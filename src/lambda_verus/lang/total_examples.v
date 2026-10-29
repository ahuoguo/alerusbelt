(** A worked example for the total logic: an almost-surely-terminating
    sampler.

    [geo] flips a fair coin until it comes up [0].  It is *not* strongly
    normalizing - the all-ones execution path is infinite - so no
    well-founded measure types it, and Nola's [type_cont_wf] over Iris's
    [twp] cannot state its termination.  Under eris's [tgl_wp] it is
    routine: [ec_ind_amp] runs an ordinary Rocq induction on the number of
    times the error credit has to double before it exceeds 1, and
    [twp_rand_exp_nat] pushes the whole credit onto the branch that
    recurses.

    The conclusion, [geo_terminates], is a statement about the operational
    semantics: for every [ε > 0], [geo] converges with probability at
    least [1 - ε], i.e. with probability 1. *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.prob Require Import distribution countable_sum.
From clutch.eris Require Import total_weakestpre.
From lrust.lang Require Import lang notation heap lifting time
                               total_lifting total_error_rules
                               total_proofmode total_adequacy.
Set Default Proof Using "Type".

Local Open Scope R.

(** [rand #2] samples uniformly from [{0, 1}]. *)
(** Written as an [expr] rather than a [val]: the [val] notation wraps the
    body in [locked], which blocks the delta step that folds the recursive
    occurrence back into [geo]. *)
Definition geo : expr :=
  (rec: "f" ["_"] :=
     let: "x" := rand #2 in
     if: "x" = #0 then #0 else "f" [ #☠ ])%E.

Section geo.
  Context `{!lrustGS Σ}.

  (** The refund schedule: the good outcome costs nothing, the bad one
      carries the doubled credit, capped at 1 so the rule's [ε2 n ≤ 1]
      side condition holds however large [ε'] grows. *)
  Definition geo_F (ε' : R) (n : nat) : R :=
    if (n =? 0)%nat then 0 else Rmin 1 (2 * ε').

  Lemma geo_F_bounded ε' : 0 <= ε' → ∀ n, 0 <= geo_F ε' n <= 1.
  Proof.
    intros Hε' n. rewrite /geo_F. case (Nat.eqb_spec n 0); intros; [lra|].
    split; [apply Rmin_glb; lra|apply Rmin_l].
  Qed.

  (** Expectation: [(1/2) * 0 + (1/2) * min 1 (2ε') ≤ ε']. *)
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

  (** The spec.  No Loeb, no measure: just [ec_ind_amp]. *)
  Lemma geo_spec (ε : R) E :
    0 < ε → ↯ ε -∗ WP geo [ #☠ ] @ E [{ v, ⌜v = #0⌝ }].
  Proof.
    iIntros (Hε) "Hε".
    iApply (ec_ind_amp ε 2 _ ltac:(lra) ltac:(lra) with "[] Hε").
    iModIntro. iIntros (ε' Hε') "#Hrec Hε".
    rewrite {2}/geo. twp_rec. twp_bind (rand _)%E.
    iApply (twp_rand_exp_nat 2 ε' (geo_F ε') with "Hε").
    { lia. }
    { apply geo_F_bounded. lra. }
    { apply geo_F_mean. lra. }
    iIntros (n) "[%Hn Hε]".
    destruct n as [|n']; last (assert (n' = 0)%nat as -> by lia).
    - (* heads: the refund is [↯ 0] and the loop exits *)
      twp_let. twp_op. twp_case. by iPureIntro.
    - (* tails: spend the doubled credit on another round *)
      twp_let. twp_op. twp_case. rewrite /geo_F /=.
      destruct (Rle_dec 1 (2 * ε')) as [Hge|Hlt].
      + (* the cap bit: a full credit is absurd *)
        rewrite Rmin_left; [|lra].
        by iDestruct (ec_contradict with "Hε") as "[]".
      + rewrite Rmin_right; [|lra]. by iApply "Hrec".
  Qed.

End geo.

(** Operational conclusion: [geo] terminates with probability [1]. *)
Theorem geo_terminates `{!lrustErisGpreS Σ}
    (σ : language.state lrust_prob_lang) (ε : R) :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  0 < ε →
  1 - ε <= SeriesC (lim_exec (geo [ #☠ ]%E, σ)).
Proof.
  intros Hσ Hε.
  eapply (lrust_twp_mass_lim_exec _ _ ε 0%nat (λ v, v = #0)); [done|lra|].
  intros ?. iIntros "_ Hε". by iApply geo_spec.
Qed.

(** ** The sampler's output distribution, exactly

    [geo_terminates] says the program converges; combining it with the
    partial side says *what it converges to*.  Both halves come from the
    same [geo_spec]: a total derivation at every positive credit, which
    [tgl_wp_pgl_wp'] also reads as a partial one.

    The point is the bound.  [approx_distribution_adequacy.v]'s
    [distr_approx_tv] gives [εs + εt/2], and the slack [εt] has to be
    assumed of a partially-proved program.  Here it is discharged, and
    for an almost-surely-terminating sampler it vanishes: the total
    variation distance to the specification is [0]. *)
From clutch.prelude Require Import Series_ext.
From lrust.lang Require Import approx_distribution_adequacy
                               total_distribution_adequacy.

Set Default Proof Using "All".

Section exact.
  Context `{!lrustErisGpreS Σ}.
  Context (σ : common.language.state lrust_prob_lang).
  Hypothesis Hσ : ∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat.

  (** The partial half: [geo] returns [#0], with no error. *)
  Lemma geo_pgl : pgl (lim_exec (geo [ #☠ ]%E, σ)) (λ w, w = LitV (LitInt 0)) 0.
  Proof.
    apply pgl_epsilon_limit; [lra|]. intros ε Hε.
    rewrite /pgl. apply lim_exec_continuous_prob. intros n.
    apply (lrust_wp_pgl _ σ n ε 0%nat (λ w, w = LitV (LitInt 0)) Hσ
             ltac:(lra)).
    intros ?. iIntros "_ Hε". iApply tgl_wp_pgl_wp'.
    by iApply geo_spec.
  Qed.

  (** Hence the value distribution is exactly the Dirac at [#0]. *)
  Theorem geo_exact :
    (tv_dist (lim_exec (geo [ #☠ ]%E, σ)) (dret (LitV (LitInt 0))) <= 0)%R.
  Proof.
    eapply (distribution_adequacy_ast _ _ σ Hσ 0 0%nat).
    { apply dret_mass. }
    { (* overshoot: [geo] can only land where [dret #0] does *)
      intros P. rewrite Rplus_0_r.
      destruct (P (LitV (LitInt 0))) eqn:HP0.
      - (* the specification gives this set probability 1 *)
        rewrite (prob_dret_true _ P HP0).
        rewrite /pgl. etrans; [apply prob_le_1|lra].
      - (* [geo] almost surely avoids it, by [geo_pgl] *)
        rewrite (prob_dret_false _ P HP0).
        apply (pgl_mon_pred _ (λ w, w = LitV (LitInt 0))); [|exact geo_pgl].
        intros a ->. exact HP0. }
    intros εt Hεt ?. iIntros "_ Hε".
    iApply (tgl_wp_wand with "[Hε] []");
      [by iApply geo_spec|by iIntros (?) "_"].
  Qed.

End exact.
