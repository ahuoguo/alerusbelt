(** Approximate and total-correctness distribution adequacy. *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.common Require Import language.
From clutch.prob Require Import distribution countable_sum graded_predicate_lifting.
From clutch.eris Require Import weakestpre.
From lrust.lang Require Import lang lifting adequacy distribution_adequacy.
Set Default Proof Using "Type".

Local Open Scope R.

(** * Total variation distance

    [pos_part D μ] is the part of [D - μ] where [D] overshoots.
    [Rabs (D a - μ a) = 2 * pos_part D μ a - (D a - μ a)]
*)

Section tv.
  Context `{Countable A}.
  Implicit Types D μ : distr A.

  Definition tv_dist D μ : R := SeriesC (λ a, Rabs (D a - μ a)) / 2.
  Definition sup_set D μ : A → bool := λ a, bool_decide (μ a < D a).
  Definition pos_part D μ : A → R := λ a, if sup_set D μ a then D a - μ a else 0.

  Lemma ex_seriesC_abs_diff D μ : ex_seriesC (λ a, Rabs (D a - μ a)).
  Proof.
    apply (ex_seriesC_le _ (λ a, D a + μ a));
      [|apply ex_seriesC_plus; apply pmf_ex_seriesC].
    intros a. pose proof (pmf_pos D a). pose proof (pmf_pos μ a).
    split; [apply Rabs_pos|]. apply Rabs_le. lra.
  Qed.

  Lemma ex_seriesC_diff D μ : ex_seriesC (λ a, D a - μ a).
  Proof. apply ex_seriesC_Rabs, ex_seriesC_abs_diff. Qed.

  Lemma ex_seriesC_pos_part D μ : ex_seriesC (pos_part D μ).
  Proof.
    apply (ex_seriesC_le _ D); [|apply pmf_ex_seriesC].
    intros a. pose proof (pmf_pos μ a). pose proof (pmf_pos D a).
    rewrite /pos_part /sup_set. case_bool_decide; lra.
  Qed.

  Lemma tv_dist_pos_part D μ :
    tv_dist D μ = SeriesC (pos_part D μ) + (SeriesC μ - SeriesC D) / 2.
  Proof.
    rewrite /tv_dist (SeriesC_ext _ (λ a, 2 * pos_part D μ a - (D a - μ a)));
      last first.
    { intros a. rewrite /pos_part /sup_set. case_bool_decide;
        [rewrite Rabs_right|rewrite Rabs_left1]; lra. }
    rewrite SeriesC_minus;
      [|by apply ex_seriesC_scal_l, ex_seriesC_pos_part|by apply ex_seriesC_diff].
    rewrite SeriesC_scal_l SeriesC_minus; [lra|apply pmf_ex_seriesC..].
  Qed.

  Lemma pos_part_prob D μ :
    SeriesC (pos_part D μ) = prob D (sup_set D μ) - prob μ (sup_set D μ).
  Proof.
    rewrite /prob -SeriesC_minus;
      [|by apply ex_seriesC_filter_bool_pos, pmf_ex_seriesC
       |by apply ex_seriesC_filter_bool_pos, pmf_ex_seriesC].
    apply SeriesC_ext. intros a. rewrite /pos_part. case (sup_set D μ a); lra.
  Qed.
End tv.

Theorem distr_approx_tv `{Countable A} (D μ : distr A) (εs εt : R) :
  SeriesC μ = 1 →
  (∀ P : A → bool, prob D P <= prob μ P + εs) →
  1 - εt <= SeriesC D →
  tv_dist D μ <= εs + εt / 2.
Proof.
  intros Hμ Hsets Hmass.
  pose proof (Hsets (sup_set D μ)). pose proof (pos_part_prob D μ).
  rewrite tv_dist_pos_part. lra.
Qed.

Lemma pgl_prob `{Countable A} (D : distr A) (P : A → bool) (r : R) :
  pgl D (λ a, P a = false) r → prob D P <= r.
Proof.
  rewrite /pgl /prob. intros Hpgl. etrans; [|exact Hpgl].
  apply Req_le, SeriesC_ext. intros a. destruct (P a) eqn:HP; simpl.
  - by rewrite bool_decide_eq_false_2.
  - by rewrite bool_decide_eq_true_2.
Qed.

Lemma tgl_True_of_mass `{Countable A} (D : distr A) (ε : R) :
  1 - ε <= SeriesC D → tgl D (λ _, True) ε.
Proof.
  rewrite /tgl /prob. intros Hmass. rewrite (SeriesC_ext _ D); [done|].
  intros a. by rewrite bool_decide_eq_true_2.
Qed.

Theorem distribution_adequacy_approx `{Countable A} (μ D : distr A) (εs εt : R) :
  SeriesC μ = 1 →
  (∀ P : A → bool, pgl D (λ a, P a = false) (prob μ P + εs)) →
  tgl D (λ _, True) εt →
  tv_dist D μ <= εs + εt / 2.
Proof.
  intros Hμ Hpgl Htgl.
  apply distr_approx_tv;
    [done| |by apply (tgl_termination_ineq D (λ _, True) εt)].
  intros P. by apply pgl_prob.
Qed.

(** * WP-level instantiation *)

Section approx_distribution_adequacy.
  Set Default Proof Using "Type*".

  Context (μ : distr val).
  Context (μ_impl : language.expr lrust_prob_lang).
  Context (εs : R).
  Hypothesis Hεs : 0 <= εs.

  Hypothesis wp_μ_adv_comp_slack :
    ∀ `{!lrustGS Σ} (ε : R) (F : val → R) (L : R),
      (0 <= ε)%R →
      (∀ v, (0 <= F v <= L)%R) →
      (SeriesC (λ v, (F v * μ v)%R) = ε)%R →
      ⊢ ↯ (ε + εs) -∗ WP μ_impl {{ v, ↯ (F v) }}.

  Lemma wp_not_in `{!lrustGS Σ} (P : val → bool) :
    ⊢ ↯ (prob μ P + εs) -∗ WP μ_impl {{ w, ⌜P w = false⌝ }}.
  Proof.
    set (F := λ w, if P w then 1%R else 0%R).
    assert (∀ w, (0 <= F w <= 1)%R) as HF.
    { intros w. rewrite /F. case (P w); lra. }
    assert (SeriesC (λ w, (F w * μ w)%R) = prob μ P) as Hsum.
    { rewrite /prob. apply SeriesC_ext. intros w. rewrite /F. case (P w); lra. }
    iIntros "Herr".
    iApply (pgl_wp_wand with "[Herr]").
    { iApply (wp_μ_adv_comp_slack (prob μ P) F 1%R (prob_ge_0 μ P) HF Hsum
               with "Herr"). }
    iIntros (w) "Herr". rewrite /F. destruct (P w) eqn:HP.
    - iExFalso. iApply (ec_contradict with "Herr"). lra.
    - done.
  Qed.

  Lemma μ_pgl_set_lim `{!lrustErisGpreS Σ} (σ : language.state lrust_prob_lang)
      (P : val → bool) :
    (∀ l ls w, σ !! l = Some (ls, w) → ls = RSt 0%nat) →
    pgl (lim_exec (μ_impl, σ)) (λ w, P w = false) (prob μ P + εs).
  Proof.
    intros Hσ.
    assert (0 <= prob μ P + εs)%R as Hpos. { pose proof (prob_ge_0 μ P). lra. }
    rewrite /pgl. apply lim_exec_continuous_prob. intros n.
    apply (lrust_wp_pgl _ _ n _ 0%nat _ Hσ Hpos).
    iIntros (?) "_ Herr". by iApply (wp_not_in with "Herr").
  Qed.

  Theorem μ_impl_approximates_μ `{!lrustErisGpreS Σ}
      (σ : language.state lrust_prob_lang) (εt : R) :
    (∀ l ls w, σ !! l = Some (ls, w) → ls = RSt 0%nat) →
    SeriesC μ = 1%R →
    tgl (lim_exec (μ_impl, σ)) (λ _, True) εt →
    tv_dist (lim_exec (μ_impl, σ)) μ <= εs + εt / 2.
  Proof.
    intros Hσ Hμ Hterm.
    apply distribution_adequacy_approx; [done| |done].
    intros P. by apply (μ_pgl_set_lim (Σ := Σ)).
  Qed.

End approx_distribution_adequacy.
