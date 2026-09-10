(** Distribution adequacy for without a total-correctness logic.

    https://github.com/logsem/clutch/blob/cpp26-distributions-artifact/theories/eris/lib/sampling/distribution_adequacy.v

   We require knowing externally [SeriesC μ = 1]. *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.common Require Import language.
From clutch.prob Require Import distribution countable_sum.
From clutch.eris Require Import weakestpre.
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
  Set Default Proof Using "Type*".

  Context (μ : distr val).
  Context (μ_impl : language.expr lrust_prob_lang).

  Hypothesis wp_μ_adv_comp :
    ∀ `{!lrustGS Σ} (ε : R) (Dr : val → R) (L : R),
      (0 <= ε)%R →
      (∀ v, (0 <= Dr v <= L)%R) →
      SeriesC (λ v, (Dr v * μ v)%R) = ε →
      ⊢ ↯ ε -∗ WP μ_impl {{ v, ↯ (Dr v) }}.

  Lemma wp_neq `{!lrustGS Σ} (v : val) :
    ⊢ ↯ (μ v) -∗ WP μ_impl {{ w, ⌜v ≠ w⌝ }}.
  Proof.
    set (Dr := λ w, if bool_decide (v = w) then 1%R else 0%R).
    assert (∀ w, (0 <= Dr w <= 1)%R) as HDr.
    { intros w. rewrite /Dr. case_bool_decide; lra. }
    assert (SeriesC (λ w, (Dr w * μ w)%R) = μ v) as Hsum.
    { rewrite (SeriesC_ext _ (λ w, if bool_decide (w = v) then μ v else 0%R)).
      - apply SeriesC_singleton.
      - intros w. rewrite /Dr. do 2 case_bool_decide; subst; try done; lra. }
    iIntros "Herr".
    iApply (pgl_wp_wand with "[Herr]").
    { iApply (wp_μ_adv_comp (μ v) Dr 1%R (pmf_pos μ v) HDr Hsum with "Herr"). }
    iIntros (w) "Herr". rewrite /Dr. case_bool_decide; subst.
    - iExFalso. iApply (ec_contradict with "Herr"). lra.
    - done.
  Qed.

  Lemma μ_pgl `{!lrustErisGpreS Σ} (σ : language.state lrust_prob_lang) (v : val) n :
    (∀ l ls w, σ !! l = Some (ls, w) → ls = RSt 0%nat) →
    pgl (exec n (μ_impl, σ)) (λ w, v ≠ w) (μ v).
  Proof.
    intros Hσ.
    apply (lrust_wp_pgl _ _ n _ 0%nat _ Hσ (pmf_pos μ v)).
    iIntros (?) "_ Herr". by iApply (wp_neq with "Herr").
  Qed.

  Lemma μ_pgl_lim `{!lrustErisGpreS Σ} (σ : language.state lrust_prob_lang) (v : val) :
    (∀ l ls w, σ !! l = Some (ls, w) → ls = RSt 0%nat) →
    pgl (lim_exec (μ_impl, σ)) (λ w, v ≠ w) (μ v).
  Proof.
    intros Hσ. rewrite /pgl.
    apply lim_exec_continuous_prob. intros n.
    by apply (μ_pgl (Σ := Σ)).
  Qed.

  Theorem μ_impl_is_μ `{!lrustErisGpreS Σ} (σ : language.state lrust_prob_lang) :
    (∀ l ls w, σ !! l = Some (ls, w) → ls = RSt 0%nat) →
    (* OBSERVE: externally we know the program returns a value with probability 1 *)
    SeriesC (lim_exec (μ_impl, σ)) = 1%R →
    SeriesC μ = 1%R ∧ ∀ v, lim_exec (μ_impl, σ) v = μ v.
  Proof.
    intros Hσ Hterm.
    apply distribution_adequacy_of_pgl.
    - intros v. by apply (μ_pgl_lim (Σ := Σ)).
    - apply Rle_ge, Req_le. symmetry. exact Hterm.
  Qed.

End distribution_adequacy.
