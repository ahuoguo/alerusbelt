(** * A probabilistic assertion, typed

  [typing/examples/coin_flip.v] at [tgl_wpw], and the example
  [typing_total/error_credit.v]'s [type_rand_case] was written for: the
  credit travels *in* the typing context rather than beside it.

  The program flips a fair coin and "asserts" heads by branching to a
  read of the poison literal, which is stuck in [lrust_prob_lang].  The
  [↯_T (1/2)] it starts with is pushed entirely onto tails by the
  schedule [F], where a full credit is absurd and discharges the stuck
  branch.  The bound is tight: tails really does get stuck, with
  probability exactly [1/2].

  The derivation is a chain of [type_*] rules, as in
  [typing/examples/pcell_example.v], except for two pure steps in the
  heads branch; the note there says why they cannot be typing rules. *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.prob Require Import distribution countable_sum.
From lrust.lang Require Import notation.
From lrust.typing_total Require Import programs int bool error_credit inst
  recursion
  soundness cont_context inv_context type_context.
From lrust.util Require Import basic.
From lrust.typing_total Require Import ctx_wp.
Unset Default Proof Using.
Set Default Goal Selector "1".
Unset Suggest Proof Using.

Local Open Scope R.

Definition coin_flip : expr :=
  (let: "n" := rand #2 in if: "n" = #1 then #0 else !(#☠))%E.

(** Heads costs nothing, tails carries the whole credit. *)
Definition F (n : nat) : R := if (n =? 1)%nat then 0 else 1.

Lemma F_bounded n : 0 <= F n <= 1.
Proof. rewrite /F. case (Nat.eqb_spec n 1); intros; lra. Qed.

Lemma F_mean :
  SeriesC (λ n : nat, if bool_decide (n < Z.to_nat 2)%nat
                      then (1 / Z.to_nat 2) * F n else 0) <= 1/2.
Proof.
  rewrite (SeriesC_ext _ (λ n,
    if bool_decide (n <= 1)%nat then (1 / Z.to_nat 2) * F n else 0)); last first.
  { intros n. destruct (le_lt_dec n 1) as [Hle|Hgt].
    - rewrite !bool_decide_eq_true_2; [done|lia|simpl; lia].
    - rewrite !bool_decide_eq_false_2; [done|lia|simpl; lia]. }
  rewrite SeriesC_nat_bounded_to_foldr'. simpl. rewrite /F /=. lra.
Qed.

Section coin_flip.
  Context {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ}.

  Lemma coin_flip_typed (l : loc) :
    ⊢ typed_body [] [] (InvCtx [] static AtomicClosed) ([] : cctx unitₛ)
        +[#l ◁ error_credit_ty (1/2)] coin_flip (λ _ _ _, True%type).
  Proof.
    rewrite /coin_flip.
    iApply (type_rand_case 2 (1/2) F #l "n");
      [lia|apply F_bounded|apply F_mean|].
    iIntros (m Hm). simpl_subst.
    destruct (Nat.eqb_spec m 1) as [->|Hne].
    - (* heads: the refund is [↯_T 0] and the [if] takes the live branch.

        These two steps are the one place this file leaves the typing
        layer, and the partial [typing/examples/coin_flip.v] does the
        same.  [type_pure] reduces only a *head* redex, and here the
        comparison sits under a [Case], so no [PureExec] instance
        covers the whole expression; [type_if] cannot help either,
        because it is [b = true] that picks the branch and that fact
        lives in the context interpretation, not in the predicate
        transformer [typed_body_impl] reasons about. *)
      iIntros (tid xl mask post iκs) "_ _ _ _ _ _ _ _".
      twp_op. twp_case. by rewrite /cont_postcondition.
    - (* tails, the only other outcome: the refund is [↯_T 1], and absurd *)
      assert (m = 0)%nat as -> by lia.
      iApply type_credit_contradict_after_rand. rewrite /F /=. lra.
  Qed.
End coin_flip.

(** The [1/2] credit buys exactly the half of the execution mass that
  the stuck branch loses. *)
Theorem coin_flip_terminates {Σ}
    `{!verus_haltGpreS (cifOF verus_haltCON) Σ} :
  1 - 1/2 <= SeriesC (lim_exec (coin_flip, ∅)).
Proof.
  apply (verus_halt_type_soundness_credit (Σ := Σ) (𝔅 := unitₛ)
    coin_flip (λ _ _ _, True%type) (1/2)); [lra|done|].
  move=> H. exact (typed_body_ec_intro _ _ _ _ _ _ inhabitant
    (coin_flip_typed inhabitant)).
Qed.

Print Assumptions coin_flip_terminates.
