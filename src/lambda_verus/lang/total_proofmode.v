(** Proofmode wiring for [lrust_prob_lang]'s total weakest precondition.

    The [twp] counterpart of [lang/proofmode.v].  Every tactic here is its
    partial sibling with the laters removed: no [MaybeIntoLaterNEnvs]
    premise, no [iNext], and [twp_pure_step_fupd] in place of
    [wp_pure_step_later].  Surface tactics are named [twp_*] so both
    logics can be used in the same file.

    The guarded heap tactics have no counterpart; see [total_lifting.v]. *)
From iris.proofmode Require Import proofmode reduction environments coq_tactics.
From iris.proofmode Require Export proofmode.
From clutch.eris Require Export total_weakestpre.
From clutch.eris Require Import total_lifting.
From lrust.lang Require Export tactics lifting total_lifting.
From lrust.lang Require Import heap.
From lrust.util Require Import non_atomic_cell_map.
Set Default Proof Using "Type".
Import uPred.

(** The pure, value and bind tactics are stated over an arbitrary
    [erisWpGS] instance, so that they apply to [tgl_wpw W] (the
    world-satisfaction weakest precondition of [total_wsat.v]) as well as
    to the canonical one.  Only the heap tactics below need [lrustGS]. *)
Lemma tac_twp_value `{!erisWpGS lrust_prob_lang Σ} Δ s E Φ e v :
  IntoVal e v →
  envs_entails Δ (Φ v) → envs_entails Δ (WP e @ s; E [{ Φ }]).
Proof. rewrite envs_entails_unseal=> ? ->. by apply tgl_wp_value. Qed.

Ltac twp_value_head := eapply tac_twp_value; [tc_solve|reduction.pm_prettify].

Lemma tac_twp_pure `{!erisWpGS lrust_prob_lang Σ} K Δ s E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  envs_entails Δ (WP fill K e2 @ s; E [{ Φ }]) →
  envs_entails Δ (WP fill K e1 @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal=> HPE Hφ HΔ. rewrite HΔ.
  apply: twp_pure_step_fupd; [|exact Hφ]. by apply (pure_exec_ctx (fill K)).
Qed.

Tactic Notation "twp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (twp ?s ?E ?e ?Q) => reshape_expr e ltac:(fun K e' =>
    unify e' efoc;
    eapply (tac_twp_pure K);
    [simpl; tc_solve                 (* PureExec *)
    |try done                        (* the pure condition *)
    |simpl_subst; try twp_value_head (* new goal *)])
   || fail "twp_pure: cannot find" efoc "in" e "or" efoc "is not a reduct"
  | _ => fail "twp_pure: not a 'twp'"
  end.

Tactic Notation "twp_rec" := twp_pure (App _ _).
Tactic Notation "twp_lam" := twp_rec.
Tactic Notation "twp_let" := twp_lam.
Tactic Notation "twp_seq" := twp_let.
Tactic Notation "twp_op" := twp_pure (BinOp _ _ _).
Tactic Notation "twp_if" := twp_pure (If _ _ _).
Tactic Notation "twp_case" := twp_pure (Case _ _); try twp_value_head.

Lemma tac_twp_bind `{!erisWpGS lrust_prob_lang Σ} K Δ s E Φ e :
  envs_entails Δ (WP e @ s; E [{ v, WP fill K (of_val v) @ s; E [{ Φ }] }])%I →
  envs_entails Δ (WP fill K e @ s; E [{ Φ }]).
Proof. rewrite envs_entails_unseal=> ->. apply: tgl_wp_bind. Qed.

Ltac twp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => apply (tac_twp_bind K); simpl
  end.

Tactic Notation "twp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (twp ?s ?E ?e ?Q) => reshape_expr e ltac:(fun K e' =>
    match e' with
    | efoc => unify e' efoc; twp_bind_core K
    end) || fail "twp_bind: cannot find" efoc "in" e
  | _ => fail "twp_bind: not a 'twp'"
  end.

Tactic Notation "twp_apply" open_constr(lem) :=
  iPoseProofCore lem as false (fun H =>
    lazymatch goal with
    | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
      reshape_expr e ltac:(fun K e' =>
        twp_bind_core K; iApplyHyp H; simpl) ||
      lazymatch iTypeOf H with
      | Some (_,?P) => fail "twp_apply: cannot apply" P
      end
    | _ => fail "twp_apply: not a 'twp'"
    end).

(** * Heap-side tactics. *)
Section heap.
Context `{!lrustGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).

Lemma tac_twp_alloc K Δ E j1 j2 n Φ :
  (0 < n)%Z →
  (∀ l (sz : nat), n = sz → ∃ Δ',
    envs_app false (Esnoc (Esnoc Enil j1
                            (l ↦∗ repeat (LitV LitPoison) sz))
                          j2 (†l…sz)) Δ
      = Some Δ' ∧
    envs_entails Δ' (WP fill K (Lit $ LitLoc l) @ E [{ Φ }])) →
  envs_entails Δ (WP fill K (Alloc (Lit $ LitInt n)) @ E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal=> ? HΔ. rewrite -tgl_wp_bind /=.
  iIntros "Δ". iApply twp_alloc=>//. iIntros (l sz) "[%eq [† ↦]]".
  move: (HΔ l sz eq)=> [?[/envs_app_sound-> ->]]/=. iApply "Δ". iFrame.
Qed.

Lemma tac_twp_free K Δ Δ' Δ'' E i1 i2 vl (n : Z) (n' : nat) l Φ :
  ↑non_atomic_cell_map.naN ⊆ E → n = length vl →
  envs_lookup i1 Δ = Some (false, l ↦∗ vl)%I →
  envs_delete false i1 false Δ = Δ' →
  envs_lookup i2 Δ' = Some (false, †l…n')%I →
  envs_delete false i2 false Δ' = Δ'' →
  n' = length vl →
  envs_entails Δ'' (WP fill K (Lit LitPoison) @ E [{ Φ }]) →
  envs_entails Δ (WP fill K (Free (Lit $ LitInt n) (Lit $ LitLoc l)) @ E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal; intros ? -> ? <- ? <- -> HΔ. rewrite -tgl_wp_bind.
  do 2 (rewrite envs_lookup_sound //=).
  rewrite HΔ. iIntros "(↦ & † & wp)". iApply (twp_free with "[$↦ $† //]")=>//.
  by iIntros.
Qed.

Lemma tac_twp_read K Δ E i l v Φ :
  ↑naN ⊆ E →
  envs_lookup i Δ = Some (false, l ↦ v)%I →
  envs_entails Δ (WP fill K (of_val v) @ E [{ Φ }]) →
  envs_entails Δ (WP fill K (Read (Lit $ LitLoc l)) @ E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal. intros Hmask ? HΔ. rewrite -tgl_wp_bind.
  rewrite envs_lookup_split //= HΔ. iIntros "[↦ →wp]".
  by iApply (twp_read with "↦").
Qed.

Lemma tac_twp_write K Δ Δ' E i l v e v' Φ :
  IntoVal e v' → ↑non_atomic_cell_map.naN ⊆ E →
  envs_lookup i Δ = Some (false, (l ↦ v)%I) →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ = Some Δ' →
  envs_entails Δ' (WP fill K (Lit LitPoison) @ E [{ Φ }]) →
  envs_entails Δ (WP fill K (Write (Lit $ LitLoc l) e) @ E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal; intros <- ? Hi Hsimpl HΦ. rewrite -tgl_wp_bind.
  rewrite envs_simple_replace_singleton_sound //=.
  iIntros "[↦ →env]". iApply (twp_write with "↦")=>//.
  iIntros "↦". iApply HΦ. by iApply "→env".
Qed.

End heap.

Tactic Notation "twp_alloc" ident(l) "as" constr(H) constr(Hf) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (twp ?s ?E ?e ?Q) => reshape_expr e ltac:(fun K e' =>
    match e' with
    | Alloc _ => eapply (tac_twp_alloc K _ _ H Hf)
    end);
    [try fast_done                    (* 0 < n *)
    |let sz := fresh "sz" in
     let Hsz := fresh "Hsz" in
     intros l sz Hsz; eexists; split;
       [reduction.pm_reflexivity || fail "twp_alloc: name" l "not fresh"
       |simpl; try twp_value_head]]
  | _ => fail "twp_alloc: not a 'twp'"
  end.

Tactic Notation "twp_free" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (twp ?s ?E ?e ?Q) => reshape_expr e ltac:(fun K e' =>
    match e' with
    | Free _ _ => eapply (tac_twp_free K)
    end);
    [try fast_done                    (* mask *)
    |try fast_done                    (* n = length vl *)
    |let l := match goal with |- _ = Some (_, (?l ↦∗ _)%I) => l end in
     iAssumptionCore || fail "twp_free: cannot find" l "↦∗ ?"
    |reduction.pm_reflexivity
    |let l := match goal with |- _ = Some (_, (†?l…_)%I) => l end in
     iAssumptionCore || fail "twp_free: cannot find †" l "… ?"
    |reduction.pm_reflexivity
    |try fast_done                    (* n' = length vl *)
    |simpl; try twp_value_head]
  | _ => fail "twp_free: not a 'twp'"
  end.

Tactic Notation "twp_read" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (twp ?s ?E ?e ?Q) => reshape_expr e ltac:(fun K e' =>
    match e' with
    | Read _ => eapply (tac_twp_read K)
    end);
    [try fast_done                    (* mask *)
    |let l := match goal with |- _ = Some (_, (?l ↦ _)%I) => l end in
     iAssumptionCore || fail "twp_read: cannot find" l "↦ ?"
    |simpl; try twp_value_head]
  | _ => fail "twp_read: not a 'twp'"
  end.

Tactic Notation "twp_write" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (twp ?s ?E ?e ?Q) => reshape_expr e ltac:(fun K e' =>
    match e' with
    | Write _ _ => eapply (tac_twp_write K)
    end);
    [tc_solve                          (* IntoVal *)
    |try fast_done                    (* mask *)
    |let l := match goal with |- _ = Some (_, (?l ↦ _)%I) => l end in
     iAssumptionCore || fail "twp_write: cannot find" l "↦ ?"
    |reduction.pm_reflexivity
    |simpl; try first [twp_pure (Seq (Lit LitPoison) _)|twp_value_head]]
  | _ => fail "twp_write: not a 'twp'"
  end.
