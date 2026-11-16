(** The CPP/EPT sampler specification with slack, at the typing layer,
    for concurrent prophetic λRust under every scheduler.

    This is [typing/distribution_adequacy.v]'s [ept_typed] (see there for
    the Verus signature) with one change to the [requires] clause, an
    extra [εs] of error credit,

        c@ =~= Value { car: <expectation of Err under μ> + eps }

    which the implementation may burn on whichever executions it chooses
    to sacrifice.  The guarantee weakens from "samples [μ]" to "samples
    within total variation distance [εs] of [μ]". *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.prob Require Import distribution countable_sum graded_predicate_lifting mdp.
From lrust.prob Require Import weakestpre.
From lrust.lifetime Require Import lifetime_full.
From lrust.lang Require Import adequacy approx_distribution_adequacy.
From lrust.typing Require Import type programs rand_ubig soundness
                                   distribution_adequacy.
Set Default Proof Using "Type".

Local Open Scope R.

Definition ept_typed_approx (Σ : gFunctors) (μ : distr val) (εs : R) (e : expr) : Prop :=
  ∀ (Err : val → R) (l : loc),
    (∀ v, 0 <= Err v <= 1) →
    ∀ `{!typeG Σ},
      ∃ tr : predl_trans [at_locₛ (trackedₛ unitₛ)] [at_locₛ (trackedₛ unitₛ)],
        (∀ π, tr (λ _ _ _, True) -[(l, ())] ⊤ π) ∧
        typed_instr [] [] (InvCtx [] static AtomicClosed)
          +[#l ◁ ↯_T (SeriesC (λ v, μ v * Err v) + εs)]
          e (λ v, +[#l ◁ ↯_T (Err v)]) tr.

(** Running the typed instruction as a WP. *)
Lemma ept_typed_approx_wp `{!typeG Σ}
    (μ : distr val) (εs : R) (e : expr) (Err : val → R) (l : loc) tid :
  (∀ v, 0 <= Err v <= 1) →
  ept_typed_approx Σ μ εs e →
  llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗
  invctx_interp tid ⊤ [] (InvCtx [] static AtomicClosed) -∗
  ↯ (SeriesC (λ v, μ v * Err v) + εs) -∗
  WP e {{ v, ↯ (Err v) }}.
Proof.
  intros HErr Hept.
  destruct (Hept Err l HErr _) as (tr & Htr & Hinstr).
  by apply (ept_typed_wp_gen _ _ l e tid tr).
Qed.

Section adequacy.
  Set Default Proof Using "All".
  Context `{!typePreG Σ} `{Countable sch_int_state}.
  Context (ζ : sch_int_state) (sch : scheduler (con_lang_mdp lrust_lang) sch_int_state).
  Context (μ : distr val) (εs : R) (e : expr).
  Hypothesis Hεs : 0 <= εs.
  Hypothesis Hept : ept_typed_approx Σ μ εs e.

  Lemma ept_approx_pgl_lim (P : val → bool) :
    pgl (sch_lim_exec sch (ζ, ([e], (∅, false) : state)))
        (λ w, P w = false) (prob μ P + εs).
  Proof.
    set (Err := λ w, if P w then 1 else 0).
    assert (∀ v, 0 <= Err v <= 1) as HErr.
    { intros v. rewrite /Err. case (P v); lra. }
    assert (SeriesC (λ v, μ v * Err v) = prob μ P) as Hexp.
    { rewrite /prob. apply SeriesC_ext. intros v. rewrite /Err. case (P v); lra. }
    assert (0 <= prob μ P + εs) as Hpos. { pose proof (prob_ge_0 μ P). lra. }
    rewrite /pgl. apply sch_lim_exec_continuous_prob. intros n.
    apply (type_wp_pgl ζ sch e n (prob μ P + εs) (λ w, P w = false) Hpos).
    intros Htype tid. iIntros "LFT TIME PROPH UNIQ Hinv Hcr".
    iApply (pgl_wp_wand with "[-]").
    { rewrite -Hexp.
      iApply (ept_typed_approx_wp μ εs e Err ((1%positive, 0%Z) : loc) tid HErr Hept
               with "LFT TIME PROPH UNIQ Hinv Hcr"). }
    iIntros (v) "Hcr". rewrite /Err. destruct (P v) eqn:HP.
    - iExFalso. iApply (ec_contradict with "Hcr"). lra.
    - done.
  Qed.

  Theorem type_distribution_adequacy_approx (εt : R) :
    SeriesC μ = 1 →
    tgl (sch_lim_exec sch (ζ, ([e], (∅, false) : state))) (λ _, True) εt →
    tv_dist (sch_lim_exec sch (ζ, ([e], (∅, false) : state))) μ <= εs + εt / 2.
  Proof.
    intros Hμ Hterm. apply distribution_adequacy_approx; [done| |done].
    intros P. apply ept_approx_pgl_lim.
  Qed.

  Corollary type_distribution_adequacy_slack :
    SeriesC μ = 1 →
    SeriesC (sch_lim_exec sch (ζ, ([e], (∅, false) : state))) = 1 →
    tv_dist (sch_lim_exec sch (ζ, ([e], (∅, false) : state))) μ <= εs.
  Proof.
    intros Hμ Hterm.
    cut (tv_dist (sch_lim_exec sch (ζ, ([e], (∅, false) : state))) μ <= εs + 0 / 2); [lra|].
    apply type_distribution_adequacy_approx; [done|].
    apply tgl_True_of_mass. rewrite Hterm. lra.
  Qed.
End adequacy.
