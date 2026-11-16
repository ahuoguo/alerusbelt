(** Data-race freedom for concurrent probabilistic λRust.

    Port of VerusBelt's [lang/races.v].  The access relation
    [next_access_head] and the race notion are unchanged.  What changes
    is the notion of reachability and safety:
    - a [thread_step] is a step of any thread with positive probability
      (the probabilistic analogue of Iris's [erased_step]);
    - [safe_from c] says every non-value thread of every configuration
      [thread_step]-reachable from [c] is (probabilistically) reducible.
    [safe_nonracing]: safety implies data-race freedom.

    The probabilistic semantics never steps a CAS to [stuck_term] (a
    racing successful CAS has no successor), so VerusBelt's
    [head_reduce_not_to_stuck] side conditions disappear: reducibility
    alone pins down the lock states. *)
From stdpp Require Import gmap.
From Stdlib Require Import Reals Psatz.
From clutch.prob Require Import distribution.
From clutch.common Require Import con_language con_ectx_language con_ectxi_language.
From lrust.lang Require Import lang tactics.
Set Default Proof Using "Type".

Inductive access_kind : Type := ReadAcc | WriteAcc | FreeAcc.

(* This is a crucial definition; if we forget to sync it with base_step,
   the results proven here are worthless.
   AlerusBelt: CAS success/failure is decided by the structural
   [lit_eq_dec], exactly as in [head_step_prob] (the relational
   [lit_eq]/[lit_neq] overlap on dangling pointers; the probabilistic
   semantics resolves that overlap structurally). *)
Inductive next_access_head : expr → state → access_kind * order → loc → Prop :=
| Access_read ord l σ :
    next_access_head (Read ord (Lit $ LitLoc l)) σ (ReadAcc, ord) l
| Access_write ord l e σ :
    is_Some (to_val e) →
    next_access_head (Write ord (Lit $ LitLoc l) e) σ (WriteAcc, ord) l
| Access_cas_fail l st e1 lit1 e2 lit2 litl σ :
    to_val e1 = Some (LitV lit1) → to_val e2 = Some (LitV lit2) →
    lit_eq_dec lit1 litl = Some false → σ.1 !! l = Some (st, LitV litl) →
    next_access_head (CAS (Lit $ LitLoc l) e1 e2) σ (ReadAcc, ScOrd) l
| Access_cas_suc l st e1 lit1 e2 lit2 litl σ :
    to_val e1 = Some (LitV lit1) → to_val e2 = Some (LitV lit2) →
    lit_eq_dec lit1 litl = Some true → σ.1 !! l = Some (st, LitV litl) →
    next_access_head (CAS (Lit $ LitLoc l) e1 e2) σ (WriteAcc, ScOrd) l
| Access_free n l σ i :
    0 ≤ i < n →
    next_access_head (Free (Lit $ LitInt n) (Lit $ LitLoc l))
                     σ (FreeAcc, Na2Ord) (l +ₗ i).

(* Some sanity checks to make sure the definition above is not entirely insensible. *)
Goal ∀ e1 e2 e3 σ, head_reducible (CAS e1 e2 e3) σ →
                   ∃ a l, next_access_head (CAS e1 e2 e3) σ a l.
Proof.
  intros ??? σ [[[??]?] Hs]. apply head_step_prob_support in Hs.
  inversion Hs; subst;
    try match goal with
    | H : lit_eq _ ?a ?b |- _ => destruct (lit_eq_is_Some _ _ _ H) as [[] ?]
    | H : lit_neq ?a ?b |- _ => destruct (lit_neq_is_Some _ _ H) as [[] ?]
    end;
    do 2 eexists; (eapply Access_cas_fail; done) || (eapply Access_cas_suc; done).
Qed.
Goal ∀ o e σ, head_reducible (Read o e) σ →
              ∃ a l, next_access_head (Read o e) σ a l.
Proof.
  intros ?? σ [[[??]?] Hs]. apply head_step_prob_support in Hs.
  inversion Hs; do 2 eexists; eapply Access_read; done.
Qed.
Goal ∀ o e1 e2 σ, head_reducible (Write o e1 e2) σ →
              ∃ a l, next_access_head (Write o e1 e2) σ a l.
Proof.
  intros ??? σ [[[??]?] Hs]. apply head_step_prob_support in Hs.
  inversion Hs; do 2 eexists; eapply Access_write; try done; eexists; done.
Qed.
Goal ∀ e1 e2 σ, head_reducible (Free e1 e2) σ →
              ∃ a l, next_access_head (Free e1 e2) σ a l.
Proof.
  intros ?? σ [[[??]?] Hs]. apply head_step_prob_support in Hs.
  inversion Hs; do 2 eexists; eapply Access_free; done.
Qed.

Definition next_access_thread (e: expr) (σ : state)
           (a : access_kind * order) (l : loc) : Prop :=
  ∃ K e', next_access_head e' σ a l ∧ e = fill K e'.

Definition next_accesses_threadpool (el: list expr) (σ : state)
           (a1 a2 : access_kind * order) (l : loc): Prop :=
  ∃ t1 e1 t2 e2 t3, el = t1 ++ e1 :: t2 ++ e2 :: t3 ∧
                    next_access_thread e1 σ a1 l ∧ next_access_thread e2 σ a2 l.

Definition nonracing_accesses (a1 a2 : access_kind * order) : Prop :=
  match a1, a2 with
  | (_, ScOrd), (_, ScOrd) => True
  | (ReadAcc, _), (ReadAcc, _) => True
  | _, _ => False
  end.

Definition nonracing_threadpool (el : list expr) (σ : state) : Prop :=
  ∀ l a1 a2, next_accesses_threadpool el σ a1 a2 l →
             nonracing_accesses a1 a2.

(** * Probabilistic reachability and safety *)

Definition thread_step (c c' : list expr * state) : Prop :=
  ∃ t1 t2 e e' efs,
    c.1 = t1 ++ e :: t2 ∧ c'.1 = t1 ++ e' :: t2 ++ efs ∧
    (prim_step e c.2 (e', c'.2, efs) > 0)%R.

Definition safe_from (c : list expr * state) : Prop :=
  ∀ t' σ' e', rtc thread_step c (t', σ') →
              e' ∈ t' → to_val e' = None → reducible e' σ'.

Lemma next_access_head_not_val e σ a l : next_access_head e σ a l → to_val e = None.
Proof. by destruct 1. Qed.

Lemma next_access_head_reducible_ctx e σ σ' a l K :
  next_access_head e σ' a l → reducible (fill K e) σ → head_reducible e σ.
Proof.
  intros Hhead Hred. apply prim_head_reducible.
  - eapply (reducible_fill_inv (K:=fill K)), Hred. by eapply next_access_head_not_val.
  - apply ectxi_language_sub_redexes_are_values. intros [] ? ->; inversion Hhead; eauto.
Qed.

(** A positive-probability head step of [e] lifts to a [thread_step]. *)
Lemma thread_step_head t1 t2 K e σ e' σ' efs :
  (head_step_prob e σ (e', σ', efs) > 0)%R →
  thread_step (t1 ++ fill K e :: t2, σ) (t1 ++ fill K e' :: t2 ++ efs, σ').
Proof.
  intros Hs. do 5 eexists. split; [done|]. split; [done|]. simpl.
  rewrite -fill_prim_step; [by apply (head_prim_step (Λ:=lrust_ectx_lang))|].
  by eapply (val_head_stuck (Λ:=lrust_ectx_lang)).
Qed.

Lemma next_access_head_state e σ a l :
  next_access_head e σ a l → head_reducible e σ →
  match a with
  | (ReadAcc, (ScOrd | Na1Ord)) => ∃ v n, σ.1 !! l = Some (RSt n, v)
  | (ReadAcc, Na2Ord) => ∃ v n, σ.1 !! l = Some (RSt (S n), v)
  | (WriteAcc, (ScOrd | Na1Ord)) => ∃ v, σ.1 !! l = Some (RSt 0, v)
  | (WriteAcc, Na2Ord) => ∃ v, σ.1 !! l = Some (WSt, v)
  | (FreeAcc, _) => ∃ v ls, σ.1 !! l = Some (ls, v)
  end.
Proof.
  intros Ha [[[e' σ'] ef] Hstep].
  destruct Ha as [o l0 σ0|o l0 e0 σ0 He0|l0 st e1 lit1 e2 lit2 litl σ0 He1 He2 Hdec Hl
                 |l0 st e1 lit1 e2 lit2 litl σ0 He1 He2 Hdec Hl|n l0 σ0 i Hi].
  - apply head_step_prob_support in Hstep. inv_head_step; eauto.
  - apply head_step_prob_support in Hstep. destruct o; inv_head_step; eauto.
  - (* CAS failure: the probabilistic step needs a read lock state *)
    simpl in Hstep. rewrite He1 He2 Hl Hdec in Hstep.
    destruct st; [rewrite dzero_0 in Hstep; lra|eauto].
  - (* CAS success: the probabilistic step needs [RSt 0] *)
    simpl in Hstep. rewrite He1 He2 Hl Hdec in Hstep.
    destruct st as [|[|]]; try (rewrite dzero_0 in Hstep; lra). eauto.
  - apply head_step_prob_support in Hstep. inv_head_step.
    match goal with H : ∀ m, _ |- _ => destruct (H i) as [_ [[]?]] end; eauto.
Qed.

Lemma next_access_head_Na1Ord_step e1 e2 ef σ1 σ2 κ a l :
  next_access_head e1 σ1 (a, Na1Ord) l →
  head_step e1 σ1 κ e2 σ2 ef →
  next_access_head e2 σ2 (a, Na2Ord) l.
Proof.
  intros Ha Hstep. inversion Ha; subst; clear Ha; inv_head_step; constructor; by rewrite to_of_val.
Qed.

Lemma next_access_head_Na1Ord_concurent_step e1 e1' e2 e'f σ σ' κ a1 a2 l :
  next_access_head e1 σ (a1, Na1Ord) l →
  head_step e1 σ κ e1' σ' e'f →
  next_access_head e2 σ a2 l →
  next_access_head e2 σ' a2 l.
Proof.
  intros Ha1 Hstep Ha2. inversion Ha1; subst; clear Ha1; inv_head_step;
  destruct Ha2; simplify_eq; econstructor; eauto; try apply lookup_insert_eq.
Qed.

Lemma next_access_head_Free_concurent_step e1 e1' e2 e'f σ σ' κ o1 a2 l :
  next_access_head e1 σ (FreeAcc, o1) l → head_step e1 σ κ e1' σ' e'f →
  next_access_head e2 σ a2 l → (∃ κ' e2' σ'' ef, head_step e2 σ' κ' e2' σ'' ef) →
  False.
Proof.
  intros Ha1 Hstep Ha2 Hred2.
  assert (FREE : ∀ l n i, 0 ≤ i ∧ i < n → free_mem l (Z.to_nat n) σ.1 !! (l +ₗ i) = None).
  { clear. intros l n i Hi.
    replace n with (Z.of_nat (Z.to_nat n)) in Hi by (apply Z2Nat.id; lia).
    revert l i Hi. induction (Z.to_nat n) as [|? IH]=>/=l i Hi. lia.
    destruct (decide (i = 0)).
    - subst. by rewrite /shift_loc Z.add_0_r -surjective_pairing lookup_delete_eq.
    - replace i with (1+(i-1)) by lia.
      rewrite lookup_delete_ne -shift_loc_assoc ?IH //. lia.
      destruct l; intros [= ?]. lia. }
  assert (FREE' : σ'.1 !! l = None).
  { inversion Ha1; clear Ha1; inv_head_step. auto. }
  destruct Hred2 as (κ'&e2'&σ''&ef&?).
  inversion Ha2; clear Ha2; inv_head_step.
  eapply (@is_Some_None (lock_state * val)). rewrite -FREE'. naive_solver.
Qed.


Lemma safe_from_step c c' : safe_from c → rtc thread_step c c' → safe_from c'.
Proof. intros Hsafe Hc t' σ' e' Hc' ??. eapply Hsafe; [by etrans|done|done]. Qed.

Local Lemma safe_head_reducible t σ K e σ' a l :
  safe_from (t, σ) → fill K e ∈ t → next_access_head e σ' a l → head_reducible e σ.
Proof.
  intros Hsafe Hin Ha. eapply (next_access_head_reducible_ctx e σ σ' a l K); [done|].
  eapply Hsafe; [apply rtc_refl|done|]. apply fill_not_val. by eapply next_access_head_not_val.
Qed.

Theorem safe_nonracing el σ :
  safe_from (el, σ) → nonracing_threadpool el σ.
Proof.
  intros Hsafe l a1 a2 (t1&?&t2&?&t3&->&(K1&e1&Ha1&->)&(K2&e2&Ha2&->)).
  (* thread 1 steps *)
  assert (Hrede1 : head_reducible e1 σ).
  { eapply (safe_head_reducible _ _ K1); [done| |done]. set_solver+. }
  pose proof (next_access_head_state _ _ _ _ Ha1 Hrede1) as Hσe1.
  destruct Hrede1 as [[[e1' σ1'] ef1] Hstep1p].
  pose proof (head_step_prob_support _ _ _ _ _ Hstep1p) as Hstep1.
  assert (Ha1' : a1.2 = Na1Ord → next_access_head e1' σ1' (a1.1, Na2Ord) l).
  { intros. eapply next_access_head_Na1Ord_step, Hstep1.
    by destruct a1; simpl in *; subst. }
  assert (Hrtc_step1 :
    rtc thread_step (t1 ++ fill K1 e1 :: t2 ++ fill K2 e2 :: t3, σ)
        (t1 ++ fill K1 e1' :: t2 ++ fill K2 e2 :: t3 ++ ef1, σ1')).
  { eapply rtc_l, rtc_refl. rewrite (app_comm_cons t2) (app_assoc t2 (_ :: t3) ef1) -app_comm_cons.
    by apply thread_step_head. }
  assert (Hsafe1 := safe_from_step _ _ Hsafe Hrtc_step1).
  assert (Hrede1' : a1.2 = Na1Ord → head_reducible e1' σ1').
  { intros Hord. eapply (safe_head_reducible _ _ K1); [done| |by apply Ha1']. set_solver+. }
  (* thread 2 steps *)
  assert (Hrede2 : head_reducible e2 σ).
  { eapply (safe_head_reducible _ _ K2); [done| |done]. set_solver+. }
  pose proof (next_access_head_state _ _ _ _ Ha2 Hrede2) as Hσe2.
  destruct Hrede2 as [[[e2' σ2'] ef2] Hstep2p].
  pose proof (head_step_prob_support _ _ _ _ _ Hstep2p) as Hstep2.
  assert (Ha2' : a2.2 = Na1Ord → next_access_head e2' σ2' (a2.1, Na2Ord) l).
  { intros. eapply next_access_head_Na1Ord_step, Hstep2.
    by destruct a2; simpl in *; subst. }
  assert (Hrtc_step2 :
    rtc thread_step (t1 ++ fill K1 e1 :: t2 ++ fill K2 e2 :: t3, σ)
        ((t1 ++ fill K1 e1 :: t2) ++ fill K2 e2' :: t3 ++ ef2, σ2')).
  { eapply rtc_l, rtc_refl. rewrite (app_comm_cons t2) (app_assoc t1).
    by apply thread_step_head. }
  assert (Hsafe2 := safe_from_step _ _ Hsafe Hrtc_step2).
  assert (Hrede2' : a2.2 = Na1Ord → head_reducible e2' σ2').
  { intros Hord. eapply (safe_head_reducible _ _ K2); [done| |by apply Ha2']. set_solver+. }
  (* thread 2 after thread 1, and vice versa *)
  assert (Ha1'2 : a1.2 = Na1Ord → next_access_head e2 σ1' a2 l).
  { intros HNa. eapply next_access_head_Na1Ord_concurent_step=>//.
    by rewrite <-HNa, <-surjective_pairing. }
  assert (Hrede1_2 : head_reducible e2 σ1').
  { eapply (safe_head_reducible _ _ K2 e2 σ); [done| |done]. set_solver+. }
  assert (Ha2'1 : a2.2 = Na1Ord → next_access_head e1 σ2' a1 l).
  { intros HNa. eapply next_access_head_Na1Ord_concurent_step=>//.
    by rewrite <-HNa, <-surjective_pairing. }
  assert (Hrede2_1 : head_reducible e1 σ2').
  { eapply (safe_head_reducible _ _ K1 e1 σ); [done| |done]. set_solver+. }
  assert (Hσe1'1 :=
    λ Hord, next_access_head_state _ _ _ _ (Ha1' Hord) (Hrede1' Hord)).
  assert (Hσe1'2 :=
    λ Hord, next_access_head_state _ _ _ _ (Ha1'2 Hord) Hrede1_2).
  assert (Hσe2'1 :=
    λ Hord, next_access_head_state _ _ _ _ (Ha2'1 Hord) Hrede2_1).
  assert (Hσe2'2 :=
    λ Hord, next_access_head_state _ _ _ _ (Ha2' Hord) (Hrede2' Hord)).
  (* freeing races with everything *)
  assert (a1.1 = FreeAcc → False).
  { destruct a1 as [[]?]; inversion 1.
    destruct Hrede1_2 as [[[??]?] Hs%head_step_prob_support].
    eauto 10 using next_access_head_Free_concurent_step. }
  assert (a2.1 = FreeAcc → False).
  { destruct a2 as [[]?]; inversion 1.
    destruct Hrede2_1 as [[[??]?] Hs%head_step_prob_support].
    eauto 10 using next_access_head_Free_concurent_step. }
  destruct Ha1 as [[]|[]| | |], Ha2 as [[]|[]| | |]=>//=; simpl in *;
    repeat match goal with
    | H : _ = Na1Ord → _ |- _ => specialize (H (eq_refl Na1Ord)) || clear H
    | H : False |- _ => destruct H
    | H : ∃ _, _ |- _ => destruct H
    end;
    try congruence.
  (* two [Na2Ord] writes: after the first, the location is [RSt 0] and
     the second cannot step *)
  destruct Hrede1_2 as [[[??]?] Hs%head_step_prob_support].
  clear Hstep1p Hstep2p. inv_head_step.
Qed.

(** VerusBelt's [adequate_nonracing], for [safe_from]: every
    configuration reachable from a safe one is race-free. *)
Corollary safe_from_nonracing c t σ :
  safe_from c → rtc thread_step c (t, σ) → nonracing_threadpool t σ.
Proof. intros Hsafe Hrtc. apply safe_nonracing. by eapply safe_from_step. Qed.
