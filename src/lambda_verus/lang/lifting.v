(** Lifting lemmas for λRust on the concurrent probabilistic WP of
    [lrust.prob]: the [lrustGS] bundle (now with error credits and
    [HasLc] invariants), its [alerusWpGS] instance, and the primitive WP
    rules.  Proofs follow VerusBelt's; a probabilistic step is turned
    into a relational one by [head_step_prob_support] before
    [inv_head_step], and reducibility comes from
    [head_step_prob_reducible]. *)
Require Import guarding.internal.na_invariants_fork.
From guarding Require Import guard.
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From lrust.prob Require Export weakestpre lifting ectx_lifting.
From clutch.base_logic Require Export error_credits.
From lrust.lang Require Export lang heap time.
From lrust.lang Require Import tactics.
From lrust.util Require Import update non_atomic_cell_map atomic_lock_counter.
Set Default Proof Using "Type".
Import uPred.

Open Scope Z_scope.

Class lrustGS Σ := LRustGS {
  lrustGS_invGS : invGS_gen HasLc Σ;
  #[global] lrustGS_ecGS :: ecGS Σ;
  #[global] lrustGS_na_invGS :: na_invG Σ;
  #[global] lrustGS_atomic_lock_ctr_invGS :: alc_logicG Σ;
  #[global] lrustGS_gen_heapGS :: heapGS Σ;
  #[global] lrustGS_gen_timeGS :: timeGS Σ
}.


Global Program Instance lrustGS_alerusWpGS `{!lrustGS Σ} : alerusWpGS lrust_lang Σ := {
  alerusWpGS_invGS := lrustGS_invGS;
  state_interp stepcnt σ := (@heap_ctx Σ _ lrustGS_invGS lrustGS_na_invGS lrustGS_atomic_lock_ctr_invGS σ ∗ time_interp stepcnt)%I;
  fork_post _ := True%I;
  err_interp ε := ec_supply ε;
  num_laters_per_step n := (sum_advance_credits (n + 1))%nat
}.
Next Obligation.
  intros. iIntros "/= [$ H]". by iMod (time_interp_step with "H") as "$".
Qed.

Global Opaque lrustGS_invGS.

(** Reducibility from a relational step. *)
Lemma head_reducible_of_step e σ e' σ' efs :
  head_step e σ [] e' σ' efs →
  (∀ l e1 e2, e = CAS (Lit (LitLoc l)) e1 e2 → e' ≠ stuck_term) →
  head_reducible e σ.
Proof. apply head_step_prob_reducible. Qed.

Ltac solve_not_stuck := let H := fresh in intros ??? H; simplify_eq/=; try discriminate.

(** Invert a probabilistic head step into a relational one. *)
Ltac lift_step H := apply head_step_prob_support in H.

Ltac inv_lit :=
  repeat match goal with
  | H : lit_eq _ ?x ?y |- _ => inversion H; clear H; simplify_map_eq/=
  | H : lit_neq ?x ?y |- _ => inversion H; clear H; simplify_map_eq/=
  end.

Ltac inv_bin_op_eval :=
  repeat match goal with
  | H : bin_op_eval _ ?c _ _ _ |- _ => is_constructor c; inversion H; clear H; simplify_eq/=
  end.

Local Hint Extern 0 (atomic _) => solve_atomic : core.
Local Hint Extern 0 (head_reducible _ _) =>
  eapply head_reducible_of_step; [by eauto|solve_not_stuck] : core.

Local Hint Constructors head_step bin_op_eval lit_neq lit_eq : core.
Local Hint Resolve alloc_fresh : core.
Local Hint Resolve to_of_val : core.

Class AsRec (e : expr) (f : binder) (xl : list binder) (erec : expr) :=
  as_rec : e = Rec f xl erec.
Global Instance AsRec_rec f xl e : AsRec (Rec f xl e) f xl e := eq_refl.
Global Instance AsRec_rec_locked_val v f xl e :
  AsRec (of_val v) f xl e → AsRec (of_val (locked v)) f xl e.
Proof. by unlock. Qed.

Class DoSubst (x : binder) (es : expr) (e er : expr) :=
  do_subst : subst' x es e = er.
Global Hint Extern 0 (DoSubst _ _ _ _) =>
  rewrite /DoSubst; simpl_subst; reflexivity : typeclass_instances.

Class DoSubstL (xl : list binder) (esl : list expr) (e er : expr) :=
  do_subst_l : subst_l xl esl e = Some er.
Global Instance do_subst_l_nil e : DoSubstL [] [] e e.
Proof. done. Qed.
Global Instance do_subst_l_cons x xl es esl e er er' :
  DoSubstL xl esl e er' → DoSubst x es er' er →
  DoSubstL (x :: xl) (es :: esl) e er.
Proof. rewrite /DoSubstL /DoSubst /= => -> <- //. Qed.
Global Instance do_subst_vec xl (vsl : vec val (length xl)) e :
  DoSubstL xl (of_val <$> vec_to_list vsl) e (subst_v xl vsl e).
Proof. by rewrite /DoSubstL subst_v_eq. Qed.

Section lifting.
Context `{!lrustGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types e : expr.
Implicit Types ef : option expr.

Local Open Scope nat_scope.

Lemma sqr_bound (n: nat) :
    (2 ^ (S n) * 2^ (S n) ≤ (sum_advance_credits (n + 1))).
Proof.
  destruct n.
  - cbn; lia.
  - rewrite Nat.add_1_r.
    cbn [sum_advance_credits Nat.pow].
    rewrite /advance_credits.
    nia.
Qed.

Lemma Sexp_le_exp_S_lemma (n: nat) :
    (S (2 ^ (S n))) ≤ (2 ^ (S (S n))).
Proof.
    cbn.
    assert (2 ^ n ≥ 1) as H1; last by lia.
    induction n; cbn; nia.
Qed.
    
Lemma sqr_bound' (n: nat) :
    ((2 ^ (S (S n))) * ((2^ (S (S n)))) ≤ (sum_advance_credits (n + 1))).
Proof.
  destruct n.
  - cbn; lia.
  - rewrite Nat.add_1_r.
    cbn [sum_advance_credits Nat.pow].
    rewrite /advance_credits.
    nia.
Qed.

Lemma sqr_bound'' (n: nat) :
    (S (2 ^ (S n)) * (S (2^ (S n))) ≤ (sum_advance_credits (n + 1))).
Proof.
    assert (0 ≤ S (2 ^ (S n))) as H1. { nia. }
    assert (∀ x y z, 0 ≤ x → x ≤ y → y * y ≤ z → x * x ≤ z) as H. { intros. nia. }
    apply (H _ _ _ H1 (Sexp_le_exp_S_lemma n) (sqr_bound' n)).
Qed.

Lemma wp_step_fupdN_time_receipt n m E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 → ↑advN ∪ ↑timeN ⊆ E1 →
  time_ctx -∗ ⧖n -∗
    (⧗m ∧ ((|={E1∖E2,∅}=> |={∅}▷=>^(S ((n + m) * (n + m))) |={∅,E1∖E2}=> P) ∗
           WP e @ E2 {{ v, P ={E1}=∗ Φ v }})) -∗
  WP e @ E1 {{ Φ }}.
Proof.
  iIntros (???) "#TIME #Hn H".
  iApply (wp_step_fupdN (S ((n + m) * (n + m))) _ _ E2)=>//. iSplit.
  - iIntros "* [_ Ht]". iMod (time_receipt_le with "TIME Ht Hn [H]") as "[% ?]"=>//.
    + iDestruct "H" as "[$ _]".
    + iApply fupd_mask_weaken.
      2: { iIntros "_ !> !% /=". 
           have Hx := sqr_bound ns.
           nia.
      }
      set_solver.
  - iDestruct "H" as "[_ $]".
Qed.

Lemma wp_step_fupdN_time_receipt' n m E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 → ↑advN ∪ ↑timeN ⊆ E1 →
  time_ctx -∗ ⧖n -∗
    (⧗m ∧ ((|={E1∖E2,∅}=> |={∅}▷=>^((S ((S (n + m)) * S (n + m)))) |={∅,E1∖E2}=> P) ∗
           WP e @ E2 {{ v, P ={E1}=∗ Φ v }})) -∗
  WP e @ E1 {{ Φ }}.
Proof.
  iIntros (???) "#TIME #Hn H".
  iApply (wp_step_fupdN (S (((S (n + m)) * S (n + m)))) _ _ E2)=>//. iSplit.
  - iIntros "* [_ Ht]". iMod (time_receipt_le with "TIME Ht Hn [H]") as "[% ?]"=>//.
    + iDestruct "H" as "[$ _]".
    + iApply fupd_mask_weaken.
      2: { iIntros "_ !> !% /=". 
           have Hx := sqr_bound'' ns.
           nia.
      }
      set_solver.
  - iDestruct "H" as "[_ $]".
Qed.

Lemma wp_step_fupdN_persistent_time_receipt n E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 → ↑advN ∪ ↑timeN ⊆ E1 →
  time_ctx -∗ ⧖n -∗ (|={E1∖E2,∅}=> |={∅}▷=>^(S (n * n)) |={∅, E1∖E2}=> P) -∗
  WP e @ E2 {{ v, P ={E1}=∗ Φ v }} -∗
  WP e @ E1 {{ Φ }}.
Proof. 
  iIntros (???) "#TIME #Hn HP Hwp".
  iApply (wp_step_fupdN_time_receipt _ _ E1 E2 with "TIME Hn [> -]")=>//.
  iMod cumulative_time_receipt_0 as "$". iFrame. by rewrite -plus_n_O.
Qed.


Lemma wp_step_fupdN_persistent_time_receipt' n E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 → ↑advN ∪ ↑timeN ⊆ E1 →
  time_ctx -∗ ⧖n -∗ (|={E1∖E2,∅}=> |={∅}▷=>^(S ((S n) * (S n))) |={∅, E1∖E2}=> P) -∗
  WP e @ E2 {{ v, P ={E1}=∗ Φ v }} -∗
  WP e @ E1 {{ Φ }}.
Proof. 
  iIntros (???) "#TIME #Hn HP Hwp".
  iApply (wp_step_fupdN_time_receipt' _ _ E1 E2 with "TIME Hn [> -]")=>//.
  iMod cumulative_time_receipt_0 as "$". iFrame. by rewrite -plus_n_O.
Qed.

(** The time-receipt step: the inner WP runs one step-counter behind
    ([ns - 1]) and gets the credits of that counter; the surplus of the
    outer step's credits closes the time invariant.  (Upstream did this
    three times by unfolding Iris's [wp_pre]; here once, for the
    probabilistic WP, and the three rules below are instances.) *)
Lemma wp_cumulative_time_receipt_gen E e Φ d :
  TCEq (to_val e) None → ↑advN ∪ ↑timeN ⊆ E →
  time_ctx -∗ ⧖d -∗
  (⧗(d + 2) -∗ WP e @ (E∖↑advN) {{ v, Φ v }}) -∗
  WP e @ E {{ Φ }}.
Proof.
  iIntros (Hnv Hmask) "#TIME #⧖ Hwp". apply TCEq_eq in Hnv.
  rewrite !pgl_wp_unfold /pgl_wp_pre /= Hnv.
  iIntros (ns σ1 ε1) "[[Hσ Ht] Hε]".
  iMod (step_cumulative_time_receipt _ ns d with "TIME Ht ⧖")
    as "(%Hns1 & Htm1 & EnFalse & Hcum & Hclose)"; first set_solver.
  iSpecialize ("Hwp" with "Hcum").
  iMod ("Hwp" $! (ns - 1)%nat σ1 ε1 with "[$Hσ $Htm1 $Hε]") as "Hwp".
  iModIntro.
  iApply (state_step_coupl_mono with "[Hclose EnFalse] Hwp").
  iIntros (σ2 ε2) "Hwp".
  iApply (prog_coupl_mono with "[Hclose EnFalse] Hwp").
  iIntros (e3 σ3 efs ε3) "Hwp credit".
  rewrite /num_laters_per_step /=.
  iDestruct "credit" as "[Hc1 credit]".
  rewrite (sum_advance_credits_ge1 (ns + 1)); last by lia.
  iDestruct "credit" as "[credit1 credit2]".
  replace (ns + 1 - 1)%nat with ns by lia.
  iCombine "credit2 Hc1" as "credit_inner".
  replace (ns - 1 + 1)%nat with ns by lia.
  iSpecialize ("Hwp" with "credit_inner").
  simpl. iMod "Hwp". iIntros "!> !>". iMod "Hwp". iModIntro.
  iApply (step_fupdN_nmono (sum_advance_credits ns)); first lia.
  iApply (step_fupdN_wand with "Hwp"). iIntros "Hssc".
  iApply (state_step_coupl_mono with "[Hclose EnFalse credit1] Hssc").
  iIntros (σ4 ε4) ">([Hheap Ht] & Hε & Hwp_inner & Hforks)".
  replace (S (ns - 1)) with ns by lia.
  iMod ("Hclose" with "[$Ht $EnFalse credit1]") as "Ht".
  { iApply (lc_weaken with "credit1").
    replace (ns + 1)%nat with (S ns) by lia. reflexivity. }
  iModIntro. iFrame.
  iApply (pgl_wp_mask_mono with "Hwp_inner"). set_solver.
Qed.

Lemma wp_cumulative_time_receipt_linear E e Φ d :
  TCEq (to_val e) None → ↑advN ∪ ↑timeN ⊆ E →
  time_ctx -∗
  ⧖d -∗
  (⧗(S (S d)) -∗ WP e @ (E∖↑advN) {{ v, Φ v }}) -∗
  WP e @ E {{ Φ }}.
Proof.
  iIntros (??) "#TIME #⧖ Hwp".
  iApply (wp_cumulative_time_receipt_gen with "TIME ⧖"); first assumption.
  by replace (d + 2)%nat with (S (S d)) by lia.
Qed.

Lemma wp_cumulative_time_receipt2 E e Φ :
  TCEq (to_val e) None → ↑advN ∪ ↑timeN ⊆ E →
  time_ctx -∗
  (⧗2 -∗ WP e @ (E∖↑advN) {{ v, Φ v }}) -∗
  WP e @ E {{ Φ }}.
Proof.
  iIntros (??) "#TIME Hwp".
  iMod persistent_time_receipt_0 as "#⧖".
  iApply (wp_cumulative_time_receipt_gen _ _ _ 0 with "TIME ⧖"); first assumption. done.
Qed.

Lemma wp_cumulative_time_receipt1 E e Φ :
  TCEq (to_val e) None → ↑advN ∪ ↑timeN ⊆ E →
  time_ctx -∗
  (⧗1 -∗ WP e @ (E∖↑advN) {{ v, Φ v }}) -∗
  WP e @ E {{ Φ }}.
Proof.
  iIntros (??) "#TIME Hwp".
  iApply (wp_cumulative_time_receipt2 with "TIME"); first assumption.
  iIntros "⧗". replace 2%nat with (1 + 1)%nat by lia.
  iDestruct "⧗" as "[⧗ _]". by iApply "Hwp".
Qed.

Lemma wp_persistent_time_receipt n E e Φ :
  TCEq (to_val e) None → ↑advN ∪ ↑timeN ⊆ E →
  time_ctx -∗
  ⧖n -∗
  (£(advance_credits n) -∗ ⧖(S n) -∗ WP e @ (E∖↑advN) {{ v, Φ v }}) -∗
  WP e @ E {{ Φ }}.
Proof.
  intros tceq Hmask. iIntros "#TIME #⧖ Hwp".
  iApply wp_cumulative_time_receipt1; trivial.
  iIntros "⧗".
  iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ ⧖") as "[⧖S £]"; first by solve_ndisj.
  replace (n+1)%nat with (S n) by lia.
  iApply ("Hwp" with "£ ⧖S").
Qed.

(** Base axioms for core primitives of the language: Stateless reductions *)
Lemma wp_fork E e :
  {{{ ▷ WP e {{ _, True }} }}} Fork e @ E {{{ RET LitV LitPoison; True }}}.
Proof.
  iIntros (?) "?HΦ". iApply wp_lift_atomic_base_step; [done|].
  iIntros (stepcnt σ1) "[Hσ Ht] !>"; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep); lift_step Hstep; inv_head_step. iFrame.
  iMod (time_interp_step with "Ht") as "$". iIntros "credit". by iApply "HΦ".
Qed.

(** Pure reductions *)


Local Ltac solve_exec_safe :=
  intros; destruct_and?; subst;
  eapply head_reducible_of_step; [econstructor; simpl; try (eauto with lia)|solve_not_stuck].
Local Ltac solve_exec_puredet :=
  simpl; intros; destruct_and?; inv_head_step; inv_bin_op_eval; inv_lit; done.
Local Ltac solve_pure_exec :=
  intros ?; apply nsteps_once, pure_head_step_pure_step;
    constructor; [solve_exec_safe
                 | intros ?; apply head_step_prob_det; [solve_exec_safe|solve_exec_puredet]].

Global Instance pure_rec e f xl erec erec' el :
  AsRec e f xl erec →
  TCForall AsVal el →
  Closed (f :b: xl +b+ []) erec →
  DoSubstL (f :: xl) (e :: el) erec erec' →
  PureExec True 1 (App e el) erec'.
Proof.
  rewrite /AsRec /DoSubstL=> -> /TCForall_Forall Hel ??. solve_pure_exec.
  all: eapply Forall_impl; [exact Hel|]; intros e' [v <-]; rewrite to_of_val; eauto.
Qed.

Close Scope nat_scope.

Global Instance pure_le n1 n2 :
  PureExec True 1 (BinOp LeOp (Lit (LitInt n1)) (Lit (LitInt n2)))
                  (Lit (bool_decide (n1 ≤ n2))).
Proof. solve_pure_exec. Qed.

Global Instance pure_eq_int n1 n2 :
  PureExec True 1 (BinOp EqOp (Lit (LitInt n1)) (Lit (LitInt n2))) (Lit (bool_decide (n1 = n2))).
Proof. case_bool_decide; solve_pure_exec. Qed.

Global Instance pure_eq_loc_0_r l :
  PureExec True 1 (BinOp EqOp (Lit (LitLoc l)) (Lit (LitInt 0))) (Lit false).
Proof. solve_pure_exec. Qed.

Global Instance pure_eq_loc_0_l l :
  PureExec True 1 (BinOp EqOp (Lit (LitInt 0)) (Lit (LitLoc l))) (Lit false).
Proof. solve_pure_exec. Qed.

Global Instance pure_plus z1 z2 :
  PureExec True 1 (BinOp PlusOp (Lit $ LitInt z1) (Lit $ LitInt z2)) (Lit $ LitInt $ z1 + z2).
Proof. solve_pure_exec. Qed.

Global Instance pure_minus z1 z2 :
  PureExec True 1 (BinOp MinusOp (Lit $ LitInt z1) (Lit $ LitInt z2)) (Lit $ LitInt $ z1 - z2).
Proof. solve_pure_exec. Qed.

Global Instance pure_mult z1 z2 :
  PureExec True 1 (BinOp MultOp (Lit $ LitInt z1) (Lit $ LitInt z2)) (Lit $ LitInt $ z1 * z2).
Proof. solve_pure_exec. Qed.

Global Instance pure_offset l z  :
  PureExec True 1 (BinOp OffsetOp (Lit $ LitLoc l) (Lit $ LitInt z)) (Lit $ LitLoc $ l +ₗ z).
Proof. solve_pure_exec. Qed.

Global Instance pure_case i e el :
  PureExec (0 ≤ i ∧ el !! (Z.to_nat i) = Some e) 1 (Case (Lit $ LitInt i) el) e | 10.
Proof. solve_pure_exec. Qed.

Global Instance pure_if b e1 e2 :
  PureExec True 1 (If (Lit (lit_of_bool b)) e1 e2) (if b then e1 else e2) | 1.
Proof. destruct b; solve_pure_exec. Qed.

(** [wp_nd_int] removed: [NdInt] (unbounded choice) has no probabilistic
    semantics and is stuck; use [Rand]. *)

(** Heap *)
Lemma wp_alloc E (n : Z) :
  0 < n →
  {{{ True }}} Alloc (Lit $ LitInt n) @ E
  {{{ l (sz: nat), RET LitV $ LitLoc l; ⌜n = sz⌝ ∗ †l…sz ∗ l ↦∗ repeat (LitV LitPoison) sz }}}.
Proof.
  iIntros (? Φ) "_ HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (stepcnt σ1) "[Hσ Ht] !>"; iSplit; first by auto.
  iNext; iIntros (v2 σ2 efs Hstep); lift_step Hstep; inv_head_step.
  iMod (heap_alloc with "Hσ") as "[$ Hl]"; [done..|].
  iMod (time_interp_step with "Ht") as "$". iIntros "credit".
  iModIntro; iSplit=> //. iApply ("HΦ" $! _ (Z.to_nat n)). auto with lia iFrame.
Qed.

Lemma wp_free E (n:Z) l vl :
  ↑naN ⊆ E →
  n = length vl →
  {{{ ▷ l ↦∗ vl ∗ ▷ †l…(length vl) }}}
    Free (Lit $ LitInt n) (Lit $ LitLoc l) @ E
  {{{ RET LitV LitPoison; True }}}.
Proof.
  iIntros (Hmask ? Φ) "[>Hmt >Hf] HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (stepcnt σ1) "[Hσ Ht]".
  iMod (heap_free _ _ _ n with "Hσ Hmt Hf") as "(% & % & Hσ)"=>//.
  iMod (time_interp_step with "Ht") as "$".
  iModIntro; iSplit; first by auto.
  iNext; iIntros (v2 σ2 efs Hstep); lift_step Hstep; inv_head_step. iIntros "credit".
  iModIntro; iSplit=> //. iFrame. iApply "HΦ"; auto.
Qed.

Lemma wp_read_sc_guarded_cells E l c v d G :
  ↑naN ⊆ E →
  {{{ (G &&{↑naN; d}&&> l ↦[^ c] v) ∗ G ∗ £(d) }}} Read ScOrd (Lit $ LitLoc l) @ E {{{ RET v; G }}}.
Proof.
  iIntros (Hmask Φ) "[#Gv [G £]] HΦ". iApply wp_lift_base_step; auto.
  iIntros (stepcnt σ1) "[Hσ Ht]". iDestruct "Hσ" as (hF) "(Hσ & HhF & %REL & ato)".
  iMod (atomic_read with "£ [Gv] G Hσ") as (n0) "[%Heq [rim Hσ]]". { trivial. } { rewrite /heap_mapsto_cells_fancy. unfold fv2sum. iFrame "Gv". }
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit; first by eauto.
  iNext; iIntros (e2 σ2 efs Hstep); lift_step Hstep; inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iIntros "credit !>". iFrame.
  iSplit. { iPureIntro. eauto using heap_freeable_rel_stable. }
  iSplit; last done.
  (* clear dependent σ1. *)
  iApply wp_value.
  iApply ("HΦ" with "rim").
Qed.

Lemma wp_read_sc E l v :
  ↑naN ⊆ E →
  {{{ ▷ l ↦ v }}} Read ScOrd (Lit $ LitLoc l) @ E
  {{{ RET v; l ↦ v }}}.
Proof.
  iIntros (Hmask Φ) ">pt ToΦ".
  iMod lc_zero as "£0".
  iApply (wp_read_sc_guarded_cells E l [] v 0 with "[pt £0]"); trivial.
  iFrame.
  rewrite /heap_mapsto_cells_fancy /heap_mapsto /=.
  iApply guards_refl.
Qed.

Lemma wp_read_na_guarded_cells E l c G v d :
  ↑naN ⊆ E →
  {{{ (G &&{↑naN; d}&&> (l ↦[^ c] v)) ∗ G ∗ £(3*d) }}} Read Na1Ord (Lit $ LitLoc l) @ E
  {{{ RET v; G }}}.
Proof.
  iIntros (Hmask Φ) "[#Gv [G £]] HΦ". iApply wp_lift_base_step; auto.
  iIntros (stepcnt σ1) "[Hσ Ht]". iDestruct "Hσ" as (hF) "(Hσ & HhF & %REL & ato)".
  iMod (na_read_begin with "£ [Gv] G Hσ") as (n0) "[%Heq [rim Hσ]]". { trivial. } { rewrite /heap_mapsto_cells_fancy. unfold fv2sum. iFrame "Gv". } replace (n0 + 1)%nat with (S n0) by lia.
  iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit. 
    { iPureIntro. eapply head_reducible_of_step; [apply ReadNa1S; apply Heq|solve_not_stuck]. }
  iNext; iIntros (e2 σ2 efs Hstep); lift_step Hstep; inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iIntros "credit !>". iFrame.
  iSplit. { iPureIntro. eauto using heap_freeable_rel_stable. }
  iSplit; last done.
  clear dependent σ1. iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (stepcnt' σ1) "[Hσ Ht]".
  iMod (time_interp_step with "Ht") as "$".
  iDestruct "Hσ" as (hF') "(Hσ & HhF & %REL & ato)".
  iDestruct (na_read_end with "rim Hσ") as "A". { apply Hmask. }
  iMod (lc_fupd_elim_later with "credit A") as "A". iMod "A" as (n) "([%H1 %H2] & G & Hσ)".
  destruct n as [|n]; first by lia. replace (S n - 1)%nat with n by lia.
  iModIntro; iSplit.
    { iPureIntro. eapply head_reducible_of_step; [apply ReadNa2S; eauto|solve_not_stuck]. }
  iNext. iIntros (e2 σ2 efs Hstep) "credit2 !>"; lift_step Hstep; inv_head_step.
  iFrame.
  iSplit; [done|].
  iSplit. { iPureIntro. eauto using heap_freeable_rel_stable. }
  iApply "HΦ". iFrame "G".
Qed.

(* Heap-Read *)
Lemma wp_read_na_guarded_cells_0 E l c G v :
  ↑naN ⊆ E →
  {{{ (G &&{↑naN}&&> (l ↦[^ c] v)) ∗ G }}} Read Na1Ord (Lit $ LitLoc l) @ E
  {{{ RET v; G }}}.
Proof.
  iIntros (Hmask 𝛷) "[g G]". iMod (lc_zero) as "£0".
  iApply wp_read_na_guarded_cells; first trivial. iFrame "g G". done.
Qed.

Lemma wp_read_na E l v :
  ↑naN ⊆ E →
  {{{ ▷ l ↦ v }}} Read Na1Ord (Lit $ LitLoc l) @ E
  {{{ RET v; l ↦ v }}}.
Proof.
  iIntros (Hmask Φ) ">pt ToΦ".
  iMod lc_zero as "£0".
  iApply (wp_read_na_guarded_cells E l [] (l ↦ v)%I v 0 with "[pt £0]"); trivial.
  iFrame. iApply guards_refl.
Qed.

Lemma wp_read_na_guarded_cells_singleton E l c G v d :
  ↑naN ⊆ E →
  {{{ (G &&{↑naN; d}&&> (l ↦[^ c]∗ [v])) ∗ G ∗ £(3*d) }}} Read Na1Ord (Lit $ LitLoc l) @ E
  {{{ RET v; G }}}.
Proof.
  case: c=> >; last first.
  { setoid_rewrite guards_weaken_rhs_sep_l. exact: wp_read_na_guarded_cells. }
  iIntros (??) "(gd & G & £ & _) _".
  iAssert (|={E}=> False)%I with "[gd G £]" as ">[]".
  iMod (guards_open_later with "gd G") as "to"=>//.
  iMod (lc_fupd_elim_laterN with "£ to") as ">[[] _]".
Qed.

Lemma wp_read_na_guarded E l G v d :
  ↑naN ⊆ E →
  {{{ (G &&{↑naN; d}&&> (l ↦ v)) ∗ G ∗ £(3*d) }}} Read Na1Ord (Lit $ LitLoc l) @ E
  {{{ RET v; G }}}.
Proof.
  intros Hmask. have Ha := wp_read_na_guarded_cells_singleton E l [[]] G v d. simpl in Ha.
  unfold heap_mapsto_cells_val_vec in Ha. simpl in Ha. unfold heap_mapsto_fancy_vec in Ha.
  simpl in Ha. unfold heap_mapsto. setoid_rewrite bi.sep_True in Ha; last by apply _.
  apply Ha. apply Hmask.
Qed.


(* The extra +1 in £ is problematic*)
Lemma wp_write_sc_guarded E l c e v v' d G :
  ↑naN ⊆ E →
  IntoVal e v →
  {{{ (G &&{↑naN; d}&&> ((l,c) #↦_)) ∗ G ∗ (l,c) #↦ v' ∗ £(3*d+1) }}} Write ScOrd (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; (l,c) #↦ v ∗ G }}}.
Proof.
  iIntros (Hmask <- Φ) "[#guards [G [Hv £]]] HΦ".
  iApply wp_lift_base_step; auto. iIntros (stepcnt σ1) "[Hσ Ht]".
  iMod (heap_write with "£ Hσ guards G Hv") as "(% & Hσ & G & Hv')"; first by trivial.
  iApply (fupd_mask_intro _ ∅); first set_solver. iIntros "Hclose".
    iSplit. { iPureIntro. eapply head_reducible_of_step; [eapply WriteScS; eauto|solve_not_stuck]. }
  iNext; iIntros (e2 σ2 efs Hstep) "credit"; lift_step Hstep; inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iModIntro. iFrame "Hσ". iSplit; last done.
  clear dependent σ1.
  iApply wp_value.
  iApply ("HΦ" with "[$Hv' $G]").
Qed.

(* The extra £1 is the problem *)
Lemma wp_write_sc E l e v v' :
  ↑naN ⊆ E →
  IntoVal e v →
  {{{ ▷ l ↦ v' ∗ £1 }}} Write ScOrd (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; l ↦ v }}}.
Proof.
  iIntros (Hmask IntoVal Φ) "[>pt £] ToΦ".
  (* iMod lc_zero as "£0". *)
  iApply (wp_write_sc_guarded E l [] e v v' 0 (True)%I with "[pt £]"); trivial.
   - iFrame. replace ((l, []) #↦_)%I with (True : iProp Σ)%I.
     2: { unfold heap_complete_mapsto. simpl. trivial. }
     iApply guards_true.
   - iNext. iIntros "[A B]". iApply "ToΦ". rewrite heap_cloc1_mapsto_val. iFrame.
Qed. 

Lemma wp_write_na_guarded E l c e v v' d G :
  ↑naN ⊆ E →
  IntoVal e v →
  {{{ (G &&{↑naN; d}&&> ((l,c) #↦_)) ∗ G ∗ (l,c) #↦ v' ∗ £(3*d) }}} Write Na1Ord (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; (l,c) #↦ v ∗ G }}}.
Proof.
  iIntros (Hmask <- Φ) "[#guards [G [Hv £]]] HΦ".
  iApply wp_lift_base_step; auto. iIntros (stepcnt σ1) "[Hσ Ht]".
  iMod (heap_write_na with "£ Hσ guards G Hv") as "(% & Hσ & Hσclose)"; first by trivial.
  iApply (fupd_mask_intro _ ∅); first set_solver. iIntros "Hclose". iSplit.
    { iPureIntro. eapply head_reducible_of_step; [eapply WriteNa1S; done|solve_not_stuck]. }
  iNext; iIntros (e2 σ2 efs Hstep) "credit"; lift_step Hstep; inv_head_step. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iModIntro. iFrame "Hσ". iSplit; last done.
  clear dependent σ1. iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (stepcnt' σ1) "[Hσ Ht]".
  iMod ("Hσclose" with "credit Hσ") as "(%Hw & Hσ & G & Hv)". destruct Hw as [v0 Hw].
  iMod (time_interp_step with "Ht") as "$". iModIntro; iSplit.
    { iPureIntro. eapply head_reducible_of_step; [eapply WriteNa2S; done|solve_not_stuck]. }
  iNext; iIntros (e2 σ2 efs Hstep) "credit2 !>"; lift_step Hstep; inv_head_step.
  iFrame "Hσ". iSplit; [done|]. iApply "HΦ". iFrame.
Qed.

Lemma wp_write_na_guarded_0 E l cells e v v' d G :
  ↑naN ⊆ E →
  IntoVal e v →
  {{{ (G &&{↑naN; d}&&> ((l,cells) #↦_)) ∗ G ∗ (l,cells) #↦ v' ∗ £(3*d) }}} Write Na1Ord (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; (l,cells) #↦ v ∗ G }}}.
Proof.
  iIntros (Hmask Hval 𝛷) "[g G]". iMod (lc_zero) as "£0".
  iApply wp_write_na_guarded; first trivial. iFrame "g G".
Qed.

Local Open Scope nat_scope.

Lemma wp_write_na_guarded_more_credits E l c e v v' d G d' :
  ↑naN ∪ ↑timeN ⊆ E →
  IntoVal e v →
  time_ctx -∗
  {{{ (G &&{↑naN; d}&&> ((l,c) #↦_)) ∗ G ∗ (l,c) #↦ v' ∗ £(3*d) ∗ ⧖(d') }}} Write Na1Ord (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; (l,c) #↦ v ∗ G ∗ £(6*d') }}}.
Proof.
  iIntros (Hmask <-) "#TIME". iIntros (Φ). iModIntro. iIntros "[#guards [G [Hv [£ ⧖]]]] HΦ".
  iApply wp_lift_step_fupdN; first done. iIntros (stepcnt σ1) "[Hσ Ht]".
  iMod (heap_write_na with "£ Hσ guards G Hv") as "(% & Hσ & Hσclose)"; first by set_solver.
  iMod cumulative_time_receipt_0 as "⧗0".
  iMod (time_receipt_le' with "TIME Ht ⧖ ⧗0") as "[%Htimebound [Ht ⧗0]]"; first by set_solver.
  iApply (fupd_mask_intro _ ∅); first set_solver. iIntros "Hclose". iSplit.
    { iPureIntro. apply head_prim_reducible.
      eapply head_reducible_of_step; [eapply WriteNa1S; done|solve_not_stuck]. }
  iIntros (e2 σ2 efs Hstep) "credit".
  assert (head_reducible (Write Na1Ord (Lit (LitLoc l)) (of_val v)) σ1) as HR.
  { eapply head_reducible_of_step; [eapply WriteNa1S; done|solve_not_stuck]. }
  pose proof (head_reducible_prim_step (Λ:=lrust_ectx_lang) _ _ _ HR Hstep) as Hstep'.
  clear Hstep. lift_step Hstep'; inv_head_step. iModIntro. iNext. iModIntro.
  iApply (step_fupdN_intro); first by set_solver. iNext. iMod "Hclose" as "_".
  iMod (time_interp_step with "Ht") as "$". iModIntro. iFrame "Hσ". iSplit; last done.
  clear dependent σ1. iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (stepcnt' σ1) "[Hσ Ht]".
  iDestruct "credit" as "[£1 £]".
  iMod ("Hσclose" with "£1 Hσ") as "(%Hw & Hσ & G & Hv)". destruct Hw as [v1 Hw].
  iMod (time_interp_step with "Ht") as "$". iModIntro; iSplit.
    { iPureIntro. eapply head_reducible_of_step; [eapply WriteNa2S; done|solve_not_stuck]. }
  iNext; iIntros (e3 σ3 efs3 Hstep3) "credit2 !>"; lift_step Hstep3; inv_head_step.
  iFrame "Hσ". iSplit; [done|]. iApply "HΦ". iFrame.
  iApply (lc_weaken with "£").
    - rewrite Nat.add_1_r.
      cbn [sum_advance_credits].
      replace (d' + (d' + (d' + (d' + (d' + (d' + 0)))))) with (2 * (2 * d' + d'))%nat by lia.
      replace (2 ^ stepcnt + (2 ^ stepcnt + 0) + (2 ^ stepcnt + (2 ^ stepcnt + 0) + 0)) with (2 ^ (S (S stepcnt))) in Htimebound.
      2: { cbn [Nat.pow]. lia. }
      trans (2 * (2 * 2 ^ S (S stepcnt) + 2 ^ S (S stepcnt))); try lia.
      cbn [Nat.pow].
      trans (2 * (2 * 2 ^ stepcnt) * advance_credits (2 * (2 * 2 ^ stepcnt))); try lia.
      rewrite /advance_credits.
      cbn [Nat.pow].
      nia.
Qed.
  
Lemma wp_write_na E l e v v' :
  ↑naN ⊆ E →
  IntoVal e v →
  {{{ ▷ l ↦ v' }}} Write Na1Ord (Lit $ LitLoc l) e @ E
  {{{ RET LitV LitPoison; l ↦ v }}}.
Proof.
  iIntros (Hmask IntoVal Φ) ">pt ToΦ".
  iMod lc_zero as "£0".
  iApply (wp_write_na_guarded E l [] e v v' 0 (True)%I with "[pt £0]"); trivial.
   - iFrame. replace ((l, []) #↦_)%I with (True : iProp Σ)%I.
     2: { unfold heap_complete_mapsto. simpl. trivial. }
     iApply guards_true.
   - iNext. iIntros "[A B]". iApply "ToΦ". rewrite heap_cloc1_mapsto_val. iFrame.
Qed.

(* Heap-Move-Cell *)
(*
In practice, you'll usually want to use one of the "untether" lemmas directly, since these
are more flexible because they let you separate the logical step of moving the cell from
the physical steps of moving data. The proof here illustrates the concept.
Also, this matches the special case presented in the paper.
*)
Lemma wp_cell_move_na E l l' cell v' :
  ↑naN ⊆ E →
  {{{ l ↦! (FCell cell) ∗ l' ↦ v' }}} Write Na1Ord (Lit $ LitLoc l') (Read Na1Ord (Lit $ LitLoc l)) @ E
  {{{ RET LitV LitPoison; ∃ v, l ↦ v ∗ l' ↦! (FCell cell) }}}.
Proof.
  intros Hmask. iIntros (𝛷) "[pt pt'] post". iApply wp_fupd.
  (* untether the cell from the location, get a concrete value v *)
  iMod (mapsto_vec_untether1 (l, []) (FCell cell) with "pt") as (v) "[pt [retether ?]]".
  (* copy the concrete value v *)
  change (Write Na1Ord (Lit (LitLoc l')) (Read Na1Ord (Lit (LitLoc l))))
      with (fill_item (WriteRCtx Na1Ord (LitV (LitLoc l'))) (Read Na1Ord (Lit (LitLoc l)))).
  iApply wp_bind.
  iApply (wp_read_na with "pt"); first trivial. iModIntro. iIntros "pt".
  iApply (wp_write_na _ _ _ v with "pt'"); [trivial|done|].
  (* retether the cell to the new location *)
  iModIntro. iIntros "pt'".
  iMod ("retether" $! (l', []) with "[pt']") as "[? pt']". { iSplitR. { done. } 
    unfold heap_complete_mapsto_fancy, split_at_last, rev. simpl. 
    unfold heap_mapsto. iFrame "pt'".
  }
  iModIntro. iApply "post". iFrame.
Qed.

Lemma wp_cas_int_fail_guarded  E l c z1 e2 lit2 zl d G :
  ↑naN ⊆ E →
  IntoVal e2 (LitV lit2) → z1 ≠ zl →
  {{{ (G &&{↑naN; d}&&> ((l,c) #↦_)) ∗ G ∗ (l,c) #↦ LitV (LitInt zl) ∗ £(3 * d + 1) }}}
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ E
    {{{ RET LitV $ LitInt 0; G ∗ (l,c) #↦ LitV (LitInt zl) }}}.
Proof.
  iIntros (Hmask <- ? Φ) "[#guards [G [Hv £]]] HΦ".
  iApply wp_lift_base_step; auto. iIntros (stepcnt σ1) "[Hσ Ht]".
  iMod (heap_write _ _ _ (LitV $ LitInt zl) with "£ Hσ guards G Hv") as "(% & Hσ & G & Hv')"; first by trivial.
  iApply (fupd_mask_intro _ ∅); first set_solver. iIntros "Hclose". iSplit; first by eauto.
  iNext; iIntros (e2 σ2 efs Hstep) "credit"; lift_step Hstep; inv_head_step.
  - iMod "Hclose" as "_".
    iMod (time_interp_step with "Ht") as "$". iModIntro.
    rewrite insert_id => //.
    iFrame "Hσ". iSplit; last done.
    iApply wp_value.
    iApply ("HΦ" with "[$Hv' $G]").
  - rename select (lit_eq _ _ _) into Hfalse; inversion Hfalse; subst => //.
Qed.

Lemma wp_cas_int_fail E l z1 e2 lit2 zl :
  ↑naN ⊆ E →
  IntoVal e2 (LitV lit2) → z1 ≠ zl →
  {{{ ▷ l ↦ LitV (LitInt zl) ∗ £1 }}}
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ E
  {{{ RET LitV $ LitInt 0; l ↦ LitV (LitInt zl) }}}.
Proof.
  iIntros (Hmask IntoVal ? Φ) "[>pt £] ToΦ".
  (* iMod lc_zero as "£0". *)
  iApply (wp_cas_int_fail_guarded E l [] z1 e2 lit2 zl 0 True with "[pt £]"); trivial.
  -  rewrite heap_cloc1_mapsto_val. iFrame. iApply guards_true.
  - iNext. iIntros "[_ B]". iApply "ToΦ". rewrite heap_cloc1_mapsto_val. iFrame.
Qed.

Lemma wp_cas_suc_guarded  E l c lit1 e2 lit2 d G :
  ↑naN ⊆ E →
  IntoVal e2 (LitV lit2) → lit1 ≠ LitPoison →
  {{{ (G &&{↑naN; d}&&> ((l,c) #↦_)) ∗ G ∗ (l,c) #↦ LitV lit1 ∗ £(3 * d + 1) }}}
    CAS (Lit $ LitLoc l) (Lit lit1) e2 @ E
  {{{ RET LitV $ LitInt 1; G ∗ (l,c) #↦ LitV lit2 }}}.
Proof.
  iIntros (Hmask <- ? Φ) "[#guards [G [Hv £]]] HΦ".
  iApply wp_lift_base_step; auto. iIntros (stepcnt σ1) "[Hσ Ht]".
  iMod (heap_write _ _ _ (LitV lit2) with "£ Hσ guards G Hv") as "(% & Hσ & G & Hv')"; first by trivial.
  iApply (fupd_mask_intro _ ∅); first set_solver. iIntros "Hclose". iSplit. 
  { iPureIntro. eapply head_reducible_of_step;
      [eapply CasSucS => //; destruct lit1 => //|solve_not_stuck]. }
  iNext; iIntros (e2 σ2 efs Hstep) "credit"; lift_step Hstep; inv_head_step.
  - rename select (lit_neq _ _) into Hfalse; inversion Hfalse; subst => //.
  - iMod "Hclose" as "_".
    iMod (time_interp_step with "Ht") as "$". iModIntro.
    iFrame "Hσ". iSplit; last done.
    iApply wp_value.
    iApply ("HΦ" with "[$Hv' $G]").
Qed.

Lemma wp_cas_int_suc_guarded  E l c z1 e2 lit2 d G :
  ↑naN ⊆ E →
  IntoVal e2 (LitV lit2) →
  {{{ (G &&{↑naN; d}&&> ((l,c) #↦_)) ∗ G ∗ (l,c) #↦ LitV (LitInt z1) ∗ £(3 * d + 1) }}}
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ E
  {{{ RET LitV $ LitInt 1; G ∗ (l,c) #↦ LitV lit2 }}}.
Proof.
  iIntros (Hmask <- Φ) "[#guards [G [Hv £]]] HΦ".
  iApply (wp_cas_suc_guarded with "[$guards $G $Hv $£]") => //.
Qed.

Lemma wp_cas_suc E l lit1 e2 lit2 :
  ↑naN ⊆ E →
  IntoVal e2 (LitV lit2) → lit1 ≠ LitPoison →
  {{{ ▷ l ↦ LitV lit1 ∗ £1 }}}
    CAS (Lit $ LitLoc l) (Lit lit1) e2 @ E
  {{{ RET LitV (LitInt 1); l ↦ LitV lit2 }}}.
Proof.
  iIntros (? <- ? Φ) "[>Hv £] HΦ".
  iApply (wp_cas_suc_guarded E l [] lit1 _ lit2 0 True%I with "[Hv £]"); eauto => //.
  -  rewrite heap_cloc1_mapsto_val. iFrame. iApply guards_true.
  - iNext. iIntros "[_ B]". iApply "HΦ". rewrite heap_cloc1_mapsto_val. iFrame.
Qed.

Lemma wp_cas_int_suc E l z1 e2 lit2 :
  ↑naN ⊆ E →
  IntoVal e2 (LitV lit2) →
  {{{ ▷ l ↦ LitV (LitInt z1) ∗ £1 }}}
    CAS (Lit $ LitLoc l) (Lit $ LitInt z1) e2 @ E
  {{{ RET LitV (LitInt 1); l ↦ LitV lit2 }}}.
Proof.
  iIntros (Hmask IntoVal Φ) "[>pt £] ToΦ".
  iApply (wp_cas_suc with "[$]") => //.
Qed.

Lemma wp_cas_loc_suc E l l1 e2 lit2 :
  ↑naN ⊆ E →
  IntoVal e2 (LitV lit2) →
  {{{ ▷ l ↦ LitV (LitLoc l1) ∗ £1 }}}
    CAS (Lit $ LitLoc l) (Lit $ LitLoc l1) e2 @ E
  {{{ RET LitV (LitInt 1); l ↦ LitV lit2 }}}.
Proof.
  iIntros (Hmask IntoVal Φ) "[>pt £] ToΦ".
  iApply (wp_cas_suc with "[$]") => //.
Qed.

Lemma wp_eq_loc E (l1 : loc) (l2: loc) v1 v2 P Φ :
  ↑naN ⊆ E →
  (P -∗ ▷ l1 ↦ v1) →
  (P -∗ ▷ l2 ↦ v2) →
  (P -∗ ▷ Φ (LitV (bool_decide (l1 = l2)))) →
  P -∗ WP BinOp EqOp (Lit (LitLoc l1)) (Lit (LitLoc l2)) @ E {{ Φ }}.
Proof.
  iIntros (Hmask Hl1 Hl2 Hpost) "HP".
  destruct (bool_decide_reflect (l1 = l2)) as [->|].
  - iApply wp_lift_pure_det_base_step_no_fork'; [done| | |].
    { intros σ. eapply (head_reducible_of_step _ σ);
        [apply BinOpS, BinOpEqTrue, LocRefl|solve_not_stuck]. }
    { intros σ e2' σ2 efs Hs. lift_step Hs. inv_head_step; inv_bin_op_eval; inv_lit; done. }
    iAssert (▷ (WP Lit true @ E {{ v, Φ v }}))%I with "[HP]" as "X".
     + iApply wp_value. by iApply Hpost.
     + iNext. iIntros. iFrame "X".
  - iApply wp_lift_atomic_base_step_no_fork; subst=>//.
    iIntros (stepcnt σ1) "[Hσ1 Ht]".
    iMod (time_interp_step with "Ht") as "$".
    iModIntro. inv_head_step. iSplitR.
    { iPureIntro. eapply head_reducible_of_step;
        [apply BinOpS, BinOpEqFalse; constructor; done|solve_not_stuck]. }
    (* We need to do a little gymnastics here to apply Hne now and strip away a
       ▷ but also have the ↦s. *)
    iAssert ((▷ ∃ v, l1 ↦ v) ∧ (▷ ∃ v, l2 ↦ v) ∧ ▷ Φ (LitV false))%I
      with "[HP]" as "HP".
    { iSplit; last iSplit.
      + iExists _. by iApply Hl1.
      + iExists _. by iApply Hl2.
      + by iApply Hpost. }
    clear Hl1 Hl2. iNext. iIntros (e2 σ2 efs Hs) "£".
    (* Pointer equality is structural in the probabilistic semantics. *)
    apply dret_pos in Hs. simplify_eq.
    rewrite bool_decide_eq_false_2 //.
    iSplitR=>//. iDestruct "HP" as "[_ [_ $]]". done.
Qed.

(** Proof rules for working on the n-ary argument list. *)
Lemma wp_app_ind E f (el : list expr) (Ql : vec (val → iProp Σ) (length el)) vs Φ :
  AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP eQ.1 @ E {{ eQ.2 }}) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP App f (of_val <$> vs ++ vl) @ E {{ Φ }}) -∗
    WP App f ((of_val <$> vs) ++ el) @ E {{ Φ }}.
Proof.
  intros [vf <-]. revert vs Ql.
  induction el as [|e el IH]=>/= vs Ql; inv_vec Ql; simpl.
  - iIntros "_ H". iSpecialize ("H" $! [#]). rewrite !app_nil_r /=. by iApply "H".
  - iIntros (Q Ql) "[He Hl] HΦ".
    change (App (of_val vf) ((of_val <$> vs) ++ e :: el))
      with (fill_item (AppRCtx vf vs el) e).
    iApply wp_bind. iApply (wp_wand with "He"). iIntros (v) "HQ /=".
    rewrite cons_middle (assoc app) -(fmap_app _ _ [v]).
    iApply (IH _ _ with "Hl"). iIntros "* Hvl". rewrite -assoc.
    iApply ("HΦ" $! (v:::vl)). iFrame.
Qed.

Lemma wp_app_vec E f el (Ql : vec (val → iProp Σ) (length el)) Φ :
  AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP eQ.1 @ E {{ eQ.2 }}) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP App f (of_val <$> (vl : list val)) @ E {{ Φ }}) -∗
    WP App f el @ E {{ Φ }}.
Proof. iIntros (Hf). by iApply (wp_app_ind _ _ _ _ []). Qed.

Lemma wp_app (Ql : list (val → iProp Σ)) E f el Φ :
  length Ql = length el → AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP eQ.1 @ E {{ eQ.2 }}) -∗
    (∀ vl : list val, ⌜length vl = length el⌝ -∗
            ([∗ list] k ↦ vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
             WP App f (of_val <$> (vl : list val)) @ E {{ Φ }}) -∗
    WP App f el @ E {{ Φ }}.
Proof.
  iIntros (Hlen Hf) "Hel HΦ". rewrite -(vec_to_list_to_vec Ql).
  generalize (list_to_vec Ql). rewrite Hlen. clear Hlen Ql=>Ql.
  iApply (wp_app_vec with "Hel"). iIntros (vl) "Hvl".
  iApply ("HΦ" with "[%] Hvl"). by rewrite length_vec_to_list.
Qed.

Close Scope nat_scope.
 
End lifting.
