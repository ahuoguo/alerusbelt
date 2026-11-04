(** * A geometric sampler, typed

  [lang/total_examples.v] verifies this program against the bare weakest
  precondition; here the derivation is a [typed_body] and the bound comes
  out of [typing_total/soundness.v].

  [geo] flips a fair coin until it comes up [0], so it is not strongly
  normalizing and no well-founded measure types it: [type_cont_wf] and
  [type_fnrec_wf], Nola's answer to the loss of Loeb induction, do not
  apply.  [type_amp] does - the loop doubles its credit on re-entry, and
  a credit cannot be doubled forever.  Neither parent can state this:
  VerusBelt's weakest precondition is partial, and Nola's conclusion
  [sn erased_step] is false for [geo]. *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.prob Require Import distribution countable_sum.
From lrust.lang Require Import notation total_proofmode.
From lrust.typing_total Require Import programs sampling recursion int inst
  soundness cont_context inv_context.
From nola.bi Require Import modw.
Import ModwNotation TglWpwNotation.
From lrust.util Require Import basic.
From lrust.typing_total Require Import ctx_wp.
(** [lrust.lang.pure_exec] last: [clutch.common.language] exports a second
  [AsVal], and once it wins the name [type_call_rec]'s [TCForall AsVal vl]
  no longer matches [pure_rec].  Same reason as [typing_total/recursion.v]. *)
From lrust.lang Require Import pure_exec.
Unset Default Proof Using.
Set Default Goal Selector "1".
Unset Suggest Proof Using.

Local Open Scope R.

(** Written as an [expr] rather than a [val]: the [val] notation wraps the
  body in [locked], which blocks the delta step that folds the recursive
  occurrence back into [geo]. *)
Definition geo : expr :=
  (rec: "f" ["_"] :=
     let: "x" := rand #2 in
     if: "x" = #0 then #0 else "f" [ #☠ ])%E.

(** The refund schedule: the good outcome costs nothing, the bad one
    carries the doubled credit, capped at [1] so that [type_rand_exp]'s
    [ε2 n ≤ 1] side condition holds however large [ε'] grows. *)
Definition geo_F (ε' : R) (n : nat) : R :=
  if (n =? 0)%nat then 0 else Rmin 1 (2 * ε').

Lemma geo_F_bounded ε' : 0 <= ε' → ∀ n, 0 <= geo_F ε' n <= 1.
Proof.
  intros Hε' n. rewrite /geo_F. case (Nat.eqb_spec n 0); intros; [lra|].
  split; [apply Rmin_glb; lra|apply Rmin_l].
Qed.

Lemma geo_F_mean ε' : 0 <= ε' →
  SeriesC (λ n : nat,
      if bool_decide (n < Z.to_nat 2)%nat
      then (1 / Z.to_nat 2) * geo_F ε' n else 0) <= ε'.
Proof.
  intros Hε'.
  rewrite (SeriesC_ext _ (λ n,
    if bool_decide (n <= 1)%nat
    then (1 / Z.to_nat 2) * geo_F ε' n else 0)); last first.
  { intros n. destruct (le_lt_dec n 1) as [Hle|Hgt].
    - rewrite !bool_decide_eq_true_2; [done|lia|simpl; lia].
    - rewrite !bool_decide_eq_false_2; [done|lia|simpl; lia]. }
  rewrite SeriesC_nat_bounded_to_foldr'. simpl. rewrite /geo_F /=.
  pose proof (Rmin_r 1 (2 * ε')). lra.
Qed.

(** The derivation.  Three typing rules and two pure steps. *)
Section geo.
  Context `{!typeG FML Σ}.

  Lemma geo_typed (ε : R) :
    0 < ε →
    ⊢ ↯ ε -∗ typed_body [] [] (InvCtx [] static AtomicClosed)
        ([] : cctx unitₛ) +[] (geo [ #☠ ]%E) (λ _ _ _, True%type).
  Proof.
    iIntros (Hε) "Hε".
    iApply (type_amp _ _ _ _ _ _ _ ε 2 with "[] Hε"); [lra|lra|].
    iIntros "!>" (ε' Hε') "#Hrec Hε".
    rewrite /geo. iApply type_call_rec. simpl_subst.
    iApply (type_rand_exp _ _ _ _ _ 2 ε' (geo_F ε') "x" with "Hε").
    all: try lia.
    all: try (by apply geo_F_bounded; lra).
    all: try (by apply geo_F_mean; lra).
    all: try apply _.
    iIntros (n Hn) "Hε". simpl_subst.
    iIntros (tid xl mask post iκs) "LFT UNIQ Eq Lq Iq Cq Tq %Htr".
    destruct n as [|n']; last (assert (n' = 0)%nat as -> by lia).
    - (* heads: the refund is [↯ 0] and the loop exits *)
      twp_op. twp_case. by rewrite /cont_postcondition.
    - (* tails: spend the doubled credit on another round *)
      twp_op. twp_case. rewrite /geo_F /=.
      destruct (Rle_dec 1 (2 * ε')) as [Hge|Hlt].
      + (* the cap bit: a full credit is absurd *)
        rewrite Rmin_left; [|lra].
        by iDestruct (ec_contradict with "Hε") as "[]".
      + rewrite Rmin_right; [|lra].
        iDestruct ("Hrec" with "Hε") as "body".
        iApply ("body" $! tid xl mask post iκs
          with "LFT UNIQ Eq Lq Iq Cq Tq [%//]").
  Qed.
End geo.

(** The sampler terminates with probability at least [1 - ε], for every
  positive [ε], and so with probability one. *)
Theorem geo_terminates {Σ} `{!verus_haltGpreS (cifOF verus_haltCON) Σ}
    (ε : R) :
  0 < ε → 1 - ε <= SeriesC (lim_exec (geo [ #☠ ]%E, ∅)).
Proof.
  move=> Hε.
  apply (verus_halt_type_soundness_credit (Σ := Σ) (𝔅 := unitₛ)
    (geo [ #☠ ]%E) (λ _ _ _, True%type) ε); [lra|done|].
  (* [exact] rather than [apply]: the soundness theorem elaborates its
     [typed_body] at [typeG_cif …], and [↯]'s [ecGS] reaches that only
     through [typeG_cif]'s definition.  [exact] checks up to conversion;
     [apply] unifies, and does not unfold it. *)
  move=> H. exact (geo_typed ε ltac:(lra)).
Qed.

Corollary geo_ast {Σ} `{!verus_haltGpreS (cifOF verus_haltCON) Σ} :
  1 <= SeriesC (lim_exec (geo [ #☠ ]%E, ∅)).
Proof.
  destruct (Rle_or_lt 1 (SeriesC (lim_exec (geo [ #☠ ]%E, ∅)))) as [?|Hlt];
    [done|exfalso].
  have Hε : 0 < (1 - SeriesC (lim_exec (geo [ #☠ ]%E, ∅))) / 2 by lra.
  pose proof (geo_terminates (Σ := Σ) _ Hε). lra.
Qed.

(** [Eq_rect_eq] and the classical axioms the reals bring, as everywhere
  else in the total stack. *)
Print Assumptions geo_terminates.
