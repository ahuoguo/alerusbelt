(** Distribution adequacy for concurrent probabilistic λRust.

    Port of AlerusBelt's sequential [lang/distribution_adequacy.v] (after
    https://github.com/logsem/clutch/blob/cpp26-distributions-artifact/theories/eris/lib/sampling/distribution_adequacy.v)
    to schedulers: if [μ_impl] meets the expectation-preserving spec
    for [μ], then under EVERY scheduler that makes the main thread
    return almost surely, the main thread's return value is distributed
    exactly as [μ].  Termination is an external premise, as in the
    sequential version.

    The pure lemmas are unchanged; only the WP instantiation moves from
    [exec]/[lim_exec] to [sch_exec]/[sch_lim_exec]. *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.prob Require Import distribution countable_sum mdp.
From lrust.prob Require Import weakestpre.
From lrust.lang Require Import lang lifting adequacy.
Set Default Proof Using "Type".

Lemma distr_le_full_mass_eq `{Countable A} (D μ : distr A) :
  (∀ a, (D a <= μ a)%R) →
  (SeriesC D >= 1)%R →
  SeriesC μ = 1%R ∧ ∀ a, D a = μ a.
Proof.
  intros Hle Hmass.
  assert (SeriesC D <= SeriesC μ)%R as Hsum.
  { apply SeriesC_le; [|done]. intros a. split; [auto|apply Hle]. }
  pose proof (pmf_SeriesC μ) as Hμ1.
  assert (SeriesC μ = 1)%R as Hμ by lra.
  split; [exact Hμ|].
  (* The slack is nonnegative and sums to zero, hence vanishes. *)
  assert (∀ a, (0 <= μ a - D a)%R) as Hnn.
  { intros a. pose proof (Hle a). lra. }
  assert (ex_seriesC (λ a, (μ a - D a)%R)) as Hex.
  { apply (ex_seriesC_le _ μ); [|done].
    intros a. pose proof (pmf_pos D a). pose proof (Hle a). split; lra. }
  assert (SeriesC (λ a, (μ a - D a)%R) = 0%R) as Hzero.
  { rewrite SeriesC_minus; [|done|done]. pose proof (pmf_SeriesC D). lra. }
  intros a.
  pose proof (SeriesC_const0 _ Hnn (SeriesC_correct' _ _ Hzero Hex) a). lra.
Qed.

Lemma pgl_neq_pointwise `{Countable A} (D : distr A) (a : A) (r : R) :
  pgl D (λ b, a ≠ b) r → (D a <= r)%R.
Proof.
  rewrite /pgl /prob. intros Hpgl.
  rewrite (SeriesC_ext _ (λ b, if bool_decide (a = b) then D b else 0%R))
    in Hpgl; last first.
  { intros b. do 2 case_bool_decide; naive_solver. }
  rewrite (SeriesC_ext _ (λ b, if bool_decide (a = b) then D a else 0%R))
    in Hpgl; last first.
  { intros b. case_bool_decide; by subst. }
  by rewrite SeriesC_singleton' in Hpgl.
Qed.

Lemma distribution_adequacy_of_pgl `{Countable A} (μ D : distr A) :
  (∀ a, pgl D (λ b, a ≠ b) (μ a)) →
  (SeriesC D >= 1)%R →
  SeriesC μ = 1%R ∧ ∀ a, D a = μ a.
Proof.
  intros Hpgl Hmass.
  apply distr_le_full_mass_eq; [|done].
  intros a. by apply pgl_neq_pointwise.
Qed.

Section distribution_adequacy.
  Set Default Proof Using "All".

  Context (μ : distr val).
  Context (μ_impl : expr).

  Hypothesis wp_μ_adv_comp :
    ∀ `{!lrustGS Σ} (ε : R) (F : val → R) (L : R),
      (0 <= ε)%R →
      (∀ v, (0 <= F v <= L)%R) →
      SeriesC (λ v, (F v * μ v)%R) = ε →
      ⊢ ↯ ε -∗ WP μ_impl {{ v, ↯ (F v) }}.

  Lemma wp_neq `{!lrustGS Σ} (v : val) :
    ⊢ ↯ (μ v) -∗ WP μ_impl {{ w, ⌜v ≠ w⌝ }}.
  Proof.
    set (F := λ w, if bool_decide (v = w) then 1%R else 0%R).
    assert (∀ w, (0 <= F w <= 1)%R) as HDr.
    { intros w. rewrite /F. case_bool_decide; lra. }
    assert (SeriesC (λ w, (F w * μ w)%R) = μ v) as Hsum.
    { rewrite (SeriesC_ext _ (λ w, if bool_decide (w = v) then μ v else 0%R)).
      - apply SeriesC_singleton.
      - intros w. rewrite /F. do 2 case_bool_decide; subst; try done; lra. }
    iIntros "Herr".
    iApply (pgl_wp_wand with "[Herr]").
    { iApply (wp_μ_adv_comp (μ v) F 1%R (pmf_pos μ v) HDr Hsum with "Herr"). }
    iIntros (w) "Herr". rewrite /F. case_bool_decide; subst.
    - iExFalso. iApply (ec_contradict with "Herr"). lra.
    - done.
  Qed.

  Context `{!lrustGpreS Σ} `{Countable sch_int_state}.
  Context (ζ : sch_int_state) (sch : scheduler (con_lang_mdp lrust_lang) sch_int_state).

  Lemma μ_pgl (v : val) n :
    pgl (sch_exec sch n (ζ, ([μ_impl], (∅, false) : state))) (λ w, v ≠ w) (μ v).
  Proof.
    apply (lrust_wp_pgl (Σ := Σ) ζ sch _ n _ 0%nat _ (pmf_pos μ v)).
    iIntros (?) "_ _ Herr". by iApply (wp_neq with "Herr").
  Qed.

  Lemma μ_pgl_lim (v : val) :
    pgl (sch_lim_exec sch (ζ, ([μ_impl], (∅, false) : state))) (λ w, v ≠ w) (μ v).
  Proof.
    rewrite /pgl. apply sch_lim_exec_continuous_prob. intros n. apply μ_pgl.
  Qed.

  (** Every scheduler under which the main thread returns almost surely
      makes it return a [μ]-distributed value. *)
  Theorem μ_impl_is_μ :
    SeriesC (sch_lim_exec sch (ζ, ([μ_impl], (∅, false) : state))) = 1%R →
    SeriesC μ = 1%R ∧
    ∀ v, sch_lim_exec sch (ζ, ([μ_impl], (∅, false) : state)) v = μ v.
  Proof.
    intros Hterm.
    apply distribution_adequacy_of_pgl.
    - intros v. apply μ_pgl_lim.
    - apply Rle_ge, Req_le. symmetry. exact Hterm.
  Qed.

End distribution_adequacy.
