(** Distributional adequacy with the termination slack discharged.

    [approx_distribution_adequacy.v] bounds the total variation distance
    between a program's value distribution and a specification
    distribution by [εs + εt/2], where

    - [εs] bounds how far the program *overshoots* [μ] on any set, and
    - [εt] bounds the mass the program loses by not terminating.

    The second hypothesis has to be *assumed* there, and that is forced:
    [pgl_wp] is a guarded fixpoint, so a program proved safe by Loeb
    induction may diverge, and nothing in a partial derivation bounds the
    lost mass.

    A total derivation bounds it.  The theorems below take a [tgl_wp]
    instead of the [εt] hypothesis, so [εt] stops being an assumption
    about the program and becomes the error credit its own termination
    proof spends.  For an almost-surely-terminating program - one that
    can be typed at *every* positive credit, as credit amplification
    allows - the slack vanishes and the bound is exactly [εs]. *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Export error_credits.
From clutch.eris Require Export total_weakestpre.
From clutch.prob Require Import distribution countable_sum graded_predicate_lifting.
From lrust.lang Require Export lang approx_distribution_adequacy
                               adequacy total_adequacy.
Set Default Proof Using "Type*".

Local Open Scope R.

Section total.
  Context `{!lrustErisGpreS Σ}.
  Context (μ : distr val).
  Context (e : common.language.expr lrust_prob_lang)
          (σ : common.language.state lrust_prob_lang).
  Hypothesis Hσ : ∀ l ls w, σ !! l = Some (ls, w) → ls = RSt 0%nat.

  (** The termination slack, now proved rather than assumed. *)
  Lemma tgl_True_of_twp (εt : R) (K : nat) :
    0 <= εt →
    (∀ `{!lrustGS Σ}, ⊢ £ K -∗ ↯ εt -∗ WP e [{ _, True }]) →
    tgl (lim_exec (e, σ)) (λ _, True) εt.
  Proof.
    intros Hεt Htwp. apply tgl_True_of_mass.
    by eapply (lrust_twp_mass_lim_exec _ _ εt K (λ _, True)).
  Qed.

  (** The approximation theorem with [εt] discharged. *)
  Theorem distribution_adequacy_total (εs εt : R) (K : nat) :
    SeriesC μ = 1 →
    0 <= εt →
    (∀ P : val → bool, pgl (lim_exec (e, σ)) (λ w, P w = false)
                           (prob μ P + εs)) →
    (∀ `{!lrustGS Σ}, ⊢ £ K -∗ ↯ εt -∗ WP e [{ _, True }]) →
    tv_dist (lim_exec (e, σ)) μ <= εs + εt / 2.
  Proof.
    intros Hμ Hεt Hpgl Htwp.
    apply distribution_adequacy_approx; [done|done|].
    by eapply tgl_True_of_twp.
  Qed.

  (** And for an almost-surely-terminating program the slack vanishes.

      The hypothesis is the shape credit amplification produces: a total
      derivation at *every* positive credit, as [ec_ind_amp] gives for a
      rejection sampler.  Compare [total_examples.v]'s [geo_terminates]
      and [total_heap_example.v]'s [hprog_terminates], both of which are
      stated exactly this way. *)
  Theorem distribution_adequacy_ast (εs : R) (K : nat) :
    SeriesC μ = 1 →
    (∀ P : val → bool, pgl (lim_exec (e, σ)) (λ w, P w = false)
                           (prob μ P + εs)) →
    (∀ εt, 0 < εt → ∀ `{!lrustGS Σ}, ⊢ £ K -∗ ↯ εt -∗ WP e [{ _, True }]) →
    tv_dist (lim_exec (e, σ)) μ <= εs.
  Proof.
    intros Hμ Hpgl Htwp.
    (* [tv_dist … ≤ εs + εt/2] for every [εt > 0], hence [≤ εs]. *)
    apply Rnot_lt_le. intros Hlt.
    set (εt := tv_dist (lim_exec (e, σ)) μ - εs).
    assert (0 < εt) as Hεt by (rewrite /εt; lra).
    assert (tv_dist (lim_exec (e, σ)) μ <= εs + εt / 2) as Hle.
    { eapply (distribution_adequacy_total εs εt K); [done|lra|done|].
      intros ?. by iApply Htwp. }
    rewrite /εt in Hle. lra.
  Qed.

End total.
