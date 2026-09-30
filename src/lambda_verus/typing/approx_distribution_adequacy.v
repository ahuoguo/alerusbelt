(** The CPP/EPT sampler specification with slack, at the typing layer.

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
From clutch.common Require Import language.
From clutch.prob Require Import distribution countable_sum graded_predicate_lifting.
From clutch.eris Require Import weakestpre.
From lrust.lifetime Require Import lifetime_full.
From lrust.lang Require Import lang lifting time approx_distribution_adequacy.
From lrust.typing Require Import type programs rand_ubig soundness
                                   distribution_adequacy.
Set Default Proof Using "Type".

Local Open Scope R.

Definition ept_typed_approx (Σ : gFunctors) (μ : distr val) (εs : R)
    (e : language.expr lrust_prob_lang) : Prop :=
  ∀ (Err : val → R) (l : loc),
    (∀ v, 0 <= Err v <= 1) →
    ∀ `{!typeG Σ, !cnaInv_logicG Σ},
      ∃ tr : predl_trans [at_locₛ (trackedₛ unitₛ)] [at_locₛ (trackedₛ unitₛ)],
        tr (λ _ _, True) -[(l, ())] ⊤ ∧
        typed_instr [] [] (InvCtx [] static AtomicClosed)
          +[#l ◁ ↯_T (SeriesC (λ v, μ v * Err v) + εs)]
          e (λ v, +[#l ◁ ↯_T (Err v)]) tr.

(** Running the typed instruction as an eris WP. *)
Lemma ept_typed_approx_wp `{!typeG Σ, !cnaInv_logicG Σ}
    (μ : distr val) (εs : R) (e : language.expr lrust_prob_lang)
    (Err : val → R) (l : loc) tid :
  (∀ v, 0 <= Err v <= 1) →
  ept_typed_approx Σ μ εs e →
  llft_ctx -∗ time_ctx -∗ uniq_ctx -∗
  invctx_interp tid ⊤ [] (InvCtx [] static AtomicClosed) -∗
  ↯ (SeriesC (λ v, μ v * Err v) + εs) -∗
  WP e {{ v, ↯ (Err v) }}.
Proof.
  iIntros (HErr Hept) "LFT TIME UNIQ Hinv Hcr".
  destruct (Hept Err l HErr _ _) as (tr & Htr & Hinstr).
  iApply fupd_pgl_wp. iMod persistent_time_receipt_0 as "#⧖0". iModIntro.
  iApply (pgl_wp_wand with "[-]").
  { iApply (Hinstr tid (λ _ _, True%type) ⊤ [] -[(l, ())]
             with "LFT TIME UNIQ [] [] Hinv [Hcr] [%//]");
      [by iApply big_sepL_nil|by iApply big_sepL_nil|].
    iSplit; last done. iExists (LitV (LitLoc l)), 0%nat.
    iSplit; first done. iFrame "⧖0". by iFrame "Hcr". }
  iIntros (v) "H". iDestruct "H" as ([[l' []] []]) "(_ & _ & [Hc _] & _)".
  by iDestruct "Hc" as (w d Hev) "[_ [$ _]]".
Qed.

Section adequacy.
  Set Default Proof Using "Type*".
  Context `{!typePreG Σ} (μ : distr val) (εs : R).
  Context (e : language.expr lrust_prob_lang) (σ : language.state lrust_prob_lang).
  Hypothesis Hεs : 0 <= εs.
  Hypothesis Hσ : ∀ l ls w, σ !! l = Some (ls, w) → ls = RSt 0%nat.
  Hypothesis Hept : ept_typed_approx Σ μ εs e.

  Lemma ept_approx_pgl_lim (P : val → bool) :
    pgl (lim_exec (e, σ)) (λ w, P w = false) (prob μ P + εs).
  Proof.
    set (Err := λ w, if P w then 1 else 0).
    assert (∀ v, 0 <= Err v <= 1) as HErr.
    { intros v. rewrite /Err. case (P v); lra. }
    assert (SeriesC (λ v, μ v * Err v) = prob μ P) as Hexp.
    { rewrite /prob. apply SeriesC_ext. intros v. rewrite /Err. case (P v); lra. }
    assert (0 <= prob μ P + εs) as Hpos. { pose proof (prob_ge_0 μ P). lra. }
    rewrite /pgl. apply lim_exec_continuous_prob. intros n.
    apply (type_wp_pgl e σ n (prob μ P + εs) (λ w, P w = false) Hσ Hpos).
    intros Htype Hcna tid. iIntros "LFT TIME UNIQ Hinv Hcr".
    iApply (pgl_wp_wand with "[-]").
    { rewrite -Hexp.
      iApply (ept_typed_approx_wp μ εs e Err ((1%positive, 0%Z) : loc) tid HErr Hept
               with "LFT TIME UNIQ Hinv Hcr"). }
    iIntros (v) "Hcr". rewrite /Err. destruct (P v) eqn:HP.
    - iExFalso. iApply (ec_contradict with "Hcr"). lra.
    - done.
  Qed.

  Theorem type_distribution_adequacy_approx (εt : R) :
    SeriesC μ = 1 →
    tgl (lim_exec (e, σ)) (λ _, True) εt →
    tv_dist (lim_exec (e, σ)) μ <= εs + εt / 2.
  Proof.
    intros Hμ Hterm. apply distribution_adequacy_approx; [done| |done].
    intros P. apply ept_approx_pgl_lim.
  Qed.

  Corollary type_distribution_adequacy_slack :
    SeriesC μ = 1 →
    SeriesC (lim_exec (e, σ)) = 1 →
    tv_dist (lim_exec (e, σ)) μ <= εs.
  Proof.
    intros Hμ Hterm.
    cut (tv_dist (lim_exec (e, σ)) μ <= εs + 0 / 2); [lra|].
    apply type_distribution_adequacy_approx; [done|].
    apply tgl_True_of_mass. rewrite Hterm. lra.
  Qed.

End adequacy.
