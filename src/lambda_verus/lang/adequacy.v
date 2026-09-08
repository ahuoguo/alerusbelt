(** Probabilistic adequacy for [lrust_prob_lang], a HasLc port on
    iris MR 1217's [fupd_finally] modality.  [lrust_wp_pgl] extracts a
    pgl bound on the value distribution [exec n] from a WP and
    [lrust_wp_safety] a stuck-freedom bound on the partial-execution
    distribution [pexec n]; both handle arbitrary
    [num_laters_per_step] (ours is [sum_advance_credits (n+1)]) by
    splitting a [£K] budget per step via [total_step_credits]. *)
From iris.proofmode Require Import base proofmode.
From iris.bi Require Import lib.fixpoint_mono.
From iris.base_logic.lib Require Import fancy_updates.
From iris.prelude Require Import options.
From iris.base_logic.lib Require Import own invariants.
From iris.algebra Require Import auth lib.mono_nat numbers dfrac_agree.
From guarding.internal Require Import na_invariants_fork.
From lrust.util Require Import non_atomic_cell_map atomic_lock_counter.
From lrust.lifetime Require Import lifetime_full.
From clutch.common Require Export language exec.
From clutch.base_logic Require Export error_credits.
From clutch.eris Require Export weakestpre.
From clutch.prob Require Export distribution graded_predicate_lifting.
From lrust.lang Require Export lang heap lifting time.
Import uPred.
Set Default Proof Using "Type".

Section adequacy.
  Context `{!erisWpGS lrust_prob_lang Σ}.

  (** Pure-monotonicity through [▷^k ◇ ⌜·⌝]. *)
  Local Lemma laterN_except_0_pure_mono k (P Q : Prop) :
    (P → Q) → ((▷^k ◇ ⌜P⌝ : iProp Σ)%I ⊢ ▷^k ◇ ⌜Q⌝).
  Proof. intros HPQ. apply bi.laterN_mono, bi.except_0_mono, bi.pure_mono, HPQ. Qed.

  (** Push [∀] through [▷^n ◇] of plain pure props (via [fupd_finally]). *)
  Lemma step_fupdN_pure_forall_intro {A} (Φ : A → Prop) n E :
    (∀ a, |={E|}=> ▷^n ◇ ⌜Φ a⌝) ⊢ |={E|}=> ▷^n ◇ ⌜∀ a, Φ a⌝ : iProp Σ.
  Proof.
    iIntros "H".
    iApply (fupd_finally_mono _ _ (▷^n ◇ ⌜∀ a, Φ a⌝)%I); last first.
    { iApply fupd_finally_forall. iIntros (a). iApply "H". }
    rewrite -laterN_forall. apply bi.laterN_mono.
    rewrite -except_0_forall. apply bi.except_0_mono.
    apply pure_forall_2.
  Qed.

  Lemma pgl_dbind' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (R : A → Prop) (T : A' → Prop) ε ε' n :
    ⌜(0 <= ε)%R⌝ -∗
    ⌜(0 <= ε')%R⌝ -∗
    ⌜pgl μ R ε⌝ -∗
    (∀ a, ⌜R a⌝ -∗ |={∅|}=> ▷^(S n) ◇ ⌜pgl (f a) T ε'⌝) -∗
    |={∅|}=> ▷^(S n) ◇ ⌜pgl (dbind f μ) T (ε + ε')%R⌝.
  Proof.
    iIntros (Hε Hε' Hpgl) "H".
    iAssert (∀ a, |={∅|}=> ▷^(S n) ◇ ⌜R a → pgl (f a) T ε'⌝)%I with "[H]" as "H".
    { iIntros (a). destruct (ExcludedMiddle (R a)) as [HR|HnR].
      - iSpecialize ("H" $! a with "[//]").
        iApply (fupd_finally_mono with "H").
        apply (laterN_except_0_pure_mono (S n)). by intros.
      - iApply fupd_finally_intro. iPureIntro. by intros. }
    iPoseProof (step_fupdN_pure_forall_intro _ (S n) ∅ with "H") as "H".
    iApply (fupd_finally_mono with "H").
    apply (laterN_except_0_pure_mono (S n)). intros Hall.
    eapply pgl_dbind; eauto.
  Qed.

  Lemma pgl_dbind_adv' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (R : A → Prop) (T : A' → Prop) ε ε' n :
    ⌜(0 <= ε)%R⌝ -∗
    ⌜exists r, forall a, (0 <= ε' a <= r)%R⌝ -∗
    ⌜pgl μ R ε⌝ -∗
    (∀ a, ⌜R a⌝ -∗ |={∅|}=> ▷^(S n) ◇ ⌜pgl (f a) T (ε' a)⌝) -∗
    |={∅|}=> ▷^(S n) ◇ ⌜pgl (dbind f μ) T (ε + SeriesC (λ a : A, (μ a * ε' a)%R))%R⌝.
  Proof.
    iIntros (Hε [r Hr] Hpgl) "H".
    iAssert (∀ a, |={∅|}=> ▷^(S n) ◇ ⌜R a → pgl (f a) T (ε' a)⌝)%I with "[H]" as "H".
    { iIntros (a). destruct (ExcludedMiddle (R a)) as [HR|HnR].
      - iSpecialize ("H" $! a with "[//]").
        iApply (fupd_finally_mono with "H").
        apply (laterN_except_0_pure_mono (S n)). by intros.
      - iApply fupd_finally_intro. iPureIntro. by intros. }
    iPoseProof (step_fupdN_pure_forall_intro _ (S n) ∅ with "H") as "H".
    iApply (fupd_finally_mono with "H").
    apply (laterN_except_0_pure_mono (S n)). intros Hall.
    eapply pgl_dbind_adv; [done|exists r; done|done|done].
  Qed.

  (** Helper: introduce a plain prop under [|={E|}=> ▷^l ◇ ·]. *)
  Local Lemma fupd_finally_plain_intro {E n} (P : iProp Σ) `{!Plain P} :
    P ⊢ |={E|}=> ▷^n ◇ P.
  Proof.
    iIntros "HP".
    iApply (fupd_finally_mono _ _ (▷^n ◇ P)%I).
    { apply bi.laterN_mono, bi.except_0_intro. }
    iApply fupd_finally_intro. by iApply plain_plainly.
  Qed.

  (** Helper: weaken [|={E1, E2}=> P] (with [P] plain) to
      [|={E1|}=> ▷^l ◇ P]. *)
  Local Lemma fupd_to_fupd_finally (l : nat) (E1 E2 : coPset) {P : iProp Σ} `{!Plain P} :
    (|={E1, E2}=> P) ⊢ |={E1|}=> ▷^l ◇ P.
  Proof.
    iIntros "H". iApply fupd_fupd_finally. iMod "H" as "HP".
    iModIntro. by iApply (fupd_finally_plain_intro P).
  Qed.

  (** Helper: push [▷^l] through [|={E|}=> ▷^k ◇ ·] (combining laters). *)
  Local Lemma laterN_fupd_finally (l : nat) {E} k (P : iProp Σ) :
    ▷^l (|={E|}=> ▷^k ◇ P) ⊢ |={E|}=> ▷^(l + k) ◇ P.
  Proof.
    induction l as [|l IH]; simpl.
    - iIntros "H". by iApply (fupd_finally_mono with "H").
    - iIntros "H". rewrite IH. rewrite fupd_finally_later.
      iApply (fupd_finally_mono with "H"). iIntros "H".
      by rewrite except_0_laterN except_0_idemp.
  Qed.

  (** Eliminate [|={E1, E2}=> P] into a fupd_finally [|={E1|}=> ▷^k ◇ Q]
      via a continuation that takes [P] (consumed at [E2]) and produces
      [|={E2|}=> ▷^(k-l') ◇ Q].  This is the workhorse for chaining the
      glm/WP step with the recursive call to [wp_refRcoupl]. *)
  Local Lemma elim_fupd_fupd_finally (k l : nat) (E1 E2 : coPset) (P Q : iProp Σ) :
    l ≤ k →
    (|={E1, E2}=> P) ∗ (∀ l', ⌜l' = l⌝ -∗ P -∗ |={E2|}=> ▷^(k - l') ◇ Q)
    ⊢ |={E1|}=> ▷^k ◇ Q.
  Proof.
    iIntros (Hlk) "[H1 H2]".
    iApply fupd_fupd_finally. iMod "H1" as "HP". iModIntro.
    iSpecialize ("H2" $! l with "[//] HP").
    iApply (fupd_finally_mono with "H2").
    replace k with (l + (k - l))%nat at 2 by lia.
    rewrite laterN_add. iIntros "H". by iApply laterN_intro.
  Qed.

  Local Definition cfgO := (prodO (exprO lrust_prob_lang) (stateO lrust_prob_lang)).

  (** [glm_erasure] in fupd_finally form, with the later-count [k]
      kept separate from the exec-offset [n] (upstream uses [S n] for
      both) so it fits the polynomial [total_step_credits] budget.
      Case 3 (state_step) is unreachable here because
      [state_idx = Empty_set] (lang.v:792-796). *)
  Lemma glm_erasure (e : language.expr lrust_prob_lang) (σ : language.state lrust_prob_lang)
      (k n : nat) φ (ε : nonnegreal) :
    1 ≤ k →
    to_val e = None →
    glm e σ ε (λ '(e2, σ2) ε',
        |={∅|}=> ▷^k ◇ ⌜pgl (exec n (e2, σ2)) φ ε'⌝)
      ⊢ |={∅|}=> ▷^k ◇ ⌜pgl (exec (S n) (e, σ)) φ ε⌝.
  Proof.
    iIntros (Hk Hv) "Hexec".
    iAssert (⌜to_val e = None⌝)%I as "-#H"; [done|]. iRevert "Hexec H".
    rewrite /glm /glm'.
    set (Φ := (λ '((e1, σ1), ε''),
                (⌜to_val e1 = None⌝ -∗
                  |={∅|}=> ▷^k ◇ ⌜pgl (exec (S n) (e1, σ1)) φ ε''⌝)%I) :
           prodO cfgO NNRO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros m ((?&?)&?) ((?&?)&?) [[[=] [=]] [=]]. by simplify_eq. }
    set (F := (glm_pre (λ '(e2, σ2) ε',
                   |={∅|}=> ▷^k ◇ ⌜pgl (exec n (e2, σ2)) φ ε'⌝)%I)).
    iPoseProof (least_fixpoint_iter F Φ with "[]") as "H"; last first.
    { iIntros "Hfix %".
      by iApply ("H" $! ((_, _)) with "Hfix"). }
    clear Hv.
    iIntros "!#" ([[e1 σ1] ε'']). rewrite /Φ/F/glm_pre.
    iIntros " [H | [ (%R & %ε1 & %ε2 & %Hred & (%r & %Hr) & %Hsum & %Hlift & H)|Hbad]] %Hv".

    (* Case 1: thin-air ε-inflation. *)
    - iApply (fupd_finally_mono _ (▷^k ◇ ⌜∀ ε' : nonnegreal,
          (ε'' < ε')%R → pgl (exec (S n) (e1, σ1)) φ ε'⌝)%I).
      { apply (laterN_except_0_pure_mono k). intros Hall.
        eapply pgl_epsilon_limit; auto.
        - apply Rle_ge, cond_nonneg.
        - intros ε' Hε'.
          apply (Hall (mknonnegreal ε' (Rle_trans _ _ _ (cond_nonneg _) (Rlt_le _ _ Hε'))) Hε'). }
      iIntros (ε' Hε').
      destruct (decide (ε' < 1)%R) as [Hε'1|Hε'1]; last first.
      { iApply fupd_finally_intro. iApply plain_plainly.
        iApply bi.laterN_intro.
        rewrite /bi_except_0. iRight. iPureIntro. apply pgl_1. lra. }
      iApply (elim_fupd_fupd_finally k 0 ∅ ∅ _
        ⌜pgl (exec (S n) (e1, σ1)) φ ε'⌝); [lia|].
      iSplitL "H"; [iApply ("H" $! ε' with "[//]")|].
      iIntros (l Hl) "Hst". assert (l = 0%nat) as -> by lia.
      rewrite Nat.sub_0_r.
      iDestruct "Hst" as "(%R' & %ε1' & %ε2' & %Hsum' & %Hlift' & Hwand')".
      rewrite -(dret_id_left' (λ _ : (), exec (S n) (e1, σ1)) tt).
      iApply (fupd_finally_mono _
        (▷^k ◇ ⌜pgl (dret tt ≫= λ _ : (), exec (S n) (e1, σ1)) φ (ε1' + ε2')⌝)%I).
      { apply (laterN_except_0_pure_mono k).
        intros Hpgl. eapply pgl_mon_grading; [|exact Hpgl]. exact Hsum'. }
      destruct k as [|k']; [lia|].
      iApply (pgl_dbind' _ (dret tt) R' (λ x, φ x) ε1' ε2' k').
      { iPureIntro. apply cond_nonneg. }
      { iPureIntro. apply cond_nonneg. }
      { iPureIntro. apply tgl_implies_pgl, Hlift'. }
      iIntros (a HRa). destruct a.
      iSpecialize ("Hwand'" with "[//]").
      iSpecialize ("Hwand'" with "[//]").
      rewrite dret_id_left.
      iApply "Hwand'".

    (* Case 2: prim_step with adv composition. *)
    - rewrite exec_Sn_not_final; [|by rewrite /is_final /= Hv].
      iApply (fupd_finally_mono _ (▷^k ◇ ⌜pgl (prim_step e1 σ1 ≫= exec n) φ
        (ε1 + SeriesC (λ ρ, (prim_step e1 σ1 ρ) * ε2 ρ))%R⌝)%I).
      { apply (laterN_except_0_pure_mono k). intros Hpgl.
        eapply pgl_mon_grading; [|exact Hpgl]. done. }
      destruct k as [|k']; [lia|].
      iApply pgl_dbind_adv'.
      { iPureIntro. apply cond_nonneg. }
      { iPureIntro. exists r. intros a. split; [apply cond_nonneg | apply Hr]. }
      { done. }
      iIntros ([e' σ'] HRes).
      iApply (elim_fupd_fupd_finally (S k') 0 ∅ ∅ _
        ⌜pgl (exec n (e', σ')) φ (ε2 (e', σ'))⌝); [lia|].
      iSplitL "H"; [iApply ("H" with "[//]")|].
      iIntros (l Hl) "Hst". assert (l = 0%nat) as -> by lia.
      rewrite Nat.sub_0_r.
      iDestruct "Hst" as "(%R' & %ε1' & %ε2' & %Hsum' & %Hlift' & Hwand')".
      rewrite -(dret_id_left' (λ _ : (), exec n (e', σ')) tt).
      iApply (fupd_finally_mono _ (▷^(S k') ◇
        ⌜pgl (dret tt ≫= λ _ : (), exec n (e', σ')) φ (ε1' + ε2')⌝)%I).
      { apply (laterN_except_0_pure_mono (S k')).
        intros Hpgl. eapply pgl_mon_grading; [|exact Hpgl]. exact Hsum'. }
      iApply (pgl_dbind' _ (dret tt) R' (λ x, φ x) ε1' ε2' k').
      { iPureIntro. apply cond_nonneg. }
      { iPureIntro. apply cond_nonneg. }
      { iPureIntro. apply tgl_implies_pgl, Hlift'. }
      iIntros (a HRa). destruct a.
      iSpecialize ("Hwand'" with "[//]").
      rewrite dret_id_left.
      iApply "Hwand'".

    (* Case 3: state_step, unreachable for [lrust_prob_lang]
       because [state_idx = Empty_set]. *)
    - iDestruct (big_orL_mono _ (λ _ _,
                   |={∅|}=> ▷^k
                     ◇ ⌜pgl (exec (S n) (e1, σ1)) φ ε''⌝)%I
                with "Hbad") as "Hbad".
      { iIntros (i α _) "_". destruct α. }
      iInduction (language.get_active σ1) as [| α] "IH"; [done|].
      destruct α.
  Qed.

  Lemma glm_erasure_safety (e : language.expr lrust_prob_lang)
      (σ : language.state lrust_prob_lang) (k n : nat) (ε : nonnegreal) :
    to_val e = None →
    glm e σ ε (λ '(e2, σ2) ε',
        |={∅|}=> ▷^k ◇ ⌜(SeriesC (iterM n prim_step_or_val (e2, σ2)) >= 1 - ε')%R⌝)
      ⊢ |={∅|}=> ▷^k ◇
          ⌜(SeriesC (iterM (S n) prim_step_or_val (e, σ)) >= 1 - ε)%R⌝.
  Proof.
    iIntros (Hv) "Hexec".
    iAssert (⌜to_val e = None⌝)%I as "-#H"; [done|]. iRevert "Hexec H".
    rewrite /glm /glm'.
    set (Φ := (λ '((e1, σ1), ε''),
                (⌜to_val e1 = None⌝ -∗
                 |={∅|}=> ▷^k ◇
                   ⌜(SeriesC (iterM (S n) prim_step_or_val (e1, σ1)) >= 1 - ε'')%R⌝)%I) :
           prodO cfgO NNRO → iPropI Σ).
    assert (NonExpansive Φ).
    { intros m ((?&?)&?) ((?&?)&?) [[[=] [=]] [=]]. by simplify_eq. }
    set (F := (glm_pre (λ '(e2, σ2) ε',
                   |={∅|}=> ▷^k ◇
                     ⌜(SeriesC (iterM n prim_step_or_val (e2, σ2)) >= 1 - ε')%R⌝)%I)).
    iPoseProof (least_fixpoint_iter F Φ with "[]") as "H"; last first.
    { iIntros "Hfix %".
      by iApply ("H" $! ((_, _)) with "Hfix"). }
    clear Hv.
    iIntros "!#" ([[e1 σ1] ε'']). rewrite /Φ/F/glm_pre.
    iIntros " [H | [ (%R & %ε1 & %ε2 & %Hred & (%r & %Hr) & %Hsum & %Hlift & H)|Hbad]] %Hv".

    (* Case 1: thin-air ε-inflation.  Take the limit ε'' + δ ↓ ε''. *)
    - iApply (fupd_finally_mono _ (▷^k ◇ ⌜(∀ ε' : nonnegreal,
          (ε'' < ε')%R →
          SeriesC (iterM (S n) prim_step_or_val (e1, σ1)) >= 1 - ε')%R⌝)%I).
      { apply (laterN_except_0_pure_mono k). intros Hall.
        apply Rle_ge, real_le_limit. intros δ Hδ.
        apply Rge_le. replace (1 - ε'' - δ)%R with (1 - (ε'' + δ))%R by lra.
        destruct ε'' as [ε'' Hε''nn]. simpl in *.
        assert (0 <= ε'' + δ)%R as Hsum_nn by lra.
        specialize (Hall (mknonnegreal (ε'' + δ) Hsum_nn)).
        simpl in Hall. apply Hall. lra. }
      iIntros (ε' Hε').
      iApply (elim_fupd_fupd_finally k 0 ∅ ∅
        (exec_stutter (λ ε0 : nonnegreal, (⌜to_val e1 = None⌝ -∗
          |={∅|}=> ▷^k ◇
            ⌜(SeriesC (iterM (S n) prim_step_or_val (e1, σ1)) >= 1 - ε0)%R⌝)%I) ε')
        ⌜(SeriesC (iterM (S n) prim_step_or_val (e1, σ1)) >= 1 - ε')%R⌝); [lia|].
      iSplitL "H"; [iApply ("H" $! ε' with "[//]")|].
      iIntros (l Hl) "Hexecs". assert (l = 0%nat) as -> by lia.
      rewrite Nat.sub_0_r.
      iDestruct (exec_stutter_compat_1 _ _ with "[] Hexecs") as "[%H'|H2]".
      { iIntros (εa εb Hle) "H %Hto".
        iSpecialize ("H" with "[//]").
        iApply (fupd_finally_mono with "H").
        apply (laterN_except_0_pure_mono k). intros Hge.
        apply Rle_ge. eapply Rle_trans; [|by apply Rge_le].
        apply Rplus_le_compat_l, Ropp_le_contravar. exact Hle. }
      + iApply fupd_finally_intro. iApply plain_plainly.
        iApply bi.laterN_intro.
        rewrite /bi_except_0. iRight. iPureIntro.
        apply Rle_ge. trans 0%R.
        { destruct ε' as [? ?]; simpl in *. lra. }
        apply SeriesC_ge_0'. intros; auto.
      + iApply ("H2" with "[//]").

    (* Case 2: prim_step with adv composition. *)
    - iApply (fupd_finally_mono _ (▷^k ◇
        ⌜(∀ ρ, R ρ → SeriesC (iterM n prim_step_or_val ρ) >= 1 - (ε2 ρ))%R⌝)%I).
      { apply (laterN_except_0_pure_mono k). intros Hall.
        apply Rle_ge. simpl.
        rewrite /dbind/dbind_pmf{1}/pmf.
        setoid_rewrite prim_step_or_val_no_val; last done.
        rewrite /pgl in Hlift. rewrite /prob in Hlift.
        rewrite distr_double_swap. setoid_rewrite SeriesC_scal_l.
        trans (1 - SeriesC
            (λ a : language.cfg lrust_prob_lang,
               if Datatypes.negb (bool_decide (R a))
               then language.prim_step e1 σ1 a else 0)
             - SeriesC (λ ρ : language.cfg lrust_prob_lang,
                          language.prim_step e1 σ1 ρ * ε2 ρ))%R.
        { simpl. simpl in *.
          (* [Hlift]/[Hsum] carry the [NNRbar_to_real ∘ Finite] coercion
             while the goal carries the plain [nonneg] one, so [lra] would
             see them as distinct atoms; restate them first. *)
          match goal with
          | |- (_ <= 1 - ?A - ?B)%R =>
              assert (A <= nonneg ε1)%R by exact Hlift;
              assert (nonneg ε1 + B <= nonneg ε'')%R by exact Hsum
          end.
          lra. }
        simpl. simpl in *.
        rewrite !Rcomplements.Rle_minus_l.
        replace 1%R with (SeriesC (language.prim_step e1 σ1)); last first.
        { apply prim_step_mass. done. }
        assert (ex_seriesC (λ a : language.cfg lrust_prob_lang,
                  (language.prim_step e1 σ1 a *
                    SeriesC (iterM n prim_step_or_val a))%R)).
        { apply pmf_ex_seriesC_mult_fn. naive_solver. }
        assert (ex_seriesC (λ ρ : language.cfg lrust_prob_lang,
                  (language.prim_step e1 σ1 ρ * ε2 ρ)%R)).
        { apply pmf_ex_seriesC_mult_fn. exists r. intros a.
          pose proof cond_nonneg (ε2 a). naive_solver. }
        eassert (ex_seriesC (λ a : language.cfg lrust_prob_lang,
                   if Datatypes.negb (bool_decide (R a))
                   then language.prim_step e1 σ1 a else 0%R)).
        { apply ex_seriesC_filter_bool_pos; auto. }
        rewrite -!SeriesC_plus; auto; last first.
        { apply ex_seriesC_plus; auto. }
        apply SeriesC_le; last first.
        { repeat apply ex_seriesC_plus; auto. }
        intros x; split; first auto.
        case_bool_decide; simpl.
        + rewrite -Rmult_plus_distr_l.
          cut (language.prim_step e1 σ1 x * 1 <=
                 language.prim_step e1 σ1 x *
                   (SeriesC (iterM n prim_step_or_val x) + ε2 x))%R.
          { rewrite Rmult_1_r. rewrite Rplus_0_r. intros; done. }
          apply Rmult_le_compat_l; auto.
          rewrite -Rcomplements.Rle_minus_l.
          apply Rge_le. naive_solver.
        + apply Rle_plus_r; first done.
          apply Rplus_le_le_0_compat; first real_solver.
          apply Rmult_le_pos; auto. }
      iIntros ([e' σ'] HR).
      iSpecialize ("H" $! e' σ' with "[//]").
      iApply (elim_fupd_fupd_finally k 0 ∅ ∅
        (exec_stutter (λ ε0 : nonnegreal,
          (|={∅|}=> ▷^k ◇
            ⌜(SeriesC (iterM n prim_step_or_val (e', σ')) >= 1 - ε0)%R⌝)%I)
          (ε2 (e', σ')))
        ⌜(SeriesC (iterM n prim_step_or_val (e', σ')) >= 1 - (ε2 (e', σ')))%R⌝); [lia|].
      iSplitL "H"; [iApply "H"|].
      iIntros (l Hl) "Hst". assert (l = 0%nat) as -> by lia.
      rewrite Nat.sub_0_r.
      iDestruct (exec_stutter_compat_1 _ _ with "[] Hst") as "[%H'|H2]".
      { iIntros (εa εb Hle) "H".
        iApply (fupd_finally_mono with "H").
        apply (laterN_except_0_pure_mono k). intros Hge.
        apply Rle_ge. eapply Rle_trans; [|by apply Rge_le].
        apply Rplus_le_compat_l, Ropp_le_contravar. exact Hle. }
      + iApply fupd_finally_intro. iApply plain_plainly.
        iApply bi.laterN_intro.
        rewrite /bi_except_0. iRight. iPureIntro.
        apply Rle_ge. trans 0%R.
        { destruct (ε2 (e', σ')) as [? ?]; simpl in *. lra. }
        apply SeriesC_ge_0'. intros; auto.
      + iApply "H2".

    (* Case 3: state_step, unreachable for [lrust_prob_lang]
       because [state_idx = Empty_set]. *)
    - iDestruct (big_orL_mono _ (λ _ _,
                   |={∅|}=> ▷^k
                     ◇ ⌜(SeriesC (iterM (S n) prim_step_or_val (e1, σ1))
                        >= 1 - ε'')%R⌝)%I
                with "Hbad") as "Hbad".
      { iIntros (i α _) "_". destruct α. }
      iInduction (language.get_active σ1) as [| α] "IH"; [done|].
      destruct α.
  Qed.


  (** Total credit budget for [n] WP steps from step counter [k], used
      as both the [£]-input and the [▷^?]-output count of
      [wp_refRcoupl]. *)
  Fixpoint total_step_credits (k n : nat) : nat :=
    match n with
    | 0%nat => 0%nat
    | S n' => S (num_laters_per_step k) + total_step_credits (S k) n'
    end.

  Lemma total_step_credits_S k n :
    total_step_credits k (S n) =
    (S (num_laters_per_step k) + total_step_credits (S k) n)%nat.
  Proof. reflexivity. Qed.

  (** Absorbs a length-[m] step-fupd chain ending in [|={∅,E}=> P],
      together with a wand out of [P], into [|={∅|}=> ▷^k ◇ Q]: the
      [m] laters from the chain land in the outer [▷^k] buffer. *)
  Local Lemma elim_step_fupdN_chain (m k : nat) (E : coPset) (P Q : iProp Σ)
      `{!Plain Q} :
    m ≤ k →
    (|={∅}▷=>^m |={∅, E}=> P) -∗
    (P -∗ |={E|}=> ▷^(k - m) ◇ Q) -∗
    |={∅|}=> ▷^k ◇ Q.
  Proof.
    iIntros (Hmk) "Hchain Hwand".
    (* Step 1: combine the chain with the wand by composing the inner
       fupd ([|={∅,E}=> P] then [P -∗ |={E|}=> ...]) into a single
       fupd_finally inside the chain. *)
    iPoseProof (step_fupdN_wand ∅ ∅ m _
      (|={∅|}=> ▷^(k - m) ◇ Q)%I with "Hchain [Hwand]") as "Hchain".
    { iIntros "Hinner".
      iApply fupd_fupd_finally. iMod "Hinner" as "HP". iModIntro.
      iApply ("Hwand" with "HP"). }
    (* Step 2: collapse the step-fupd-N chain into [|={∅|}=> ▷^m ◇ ...]. *)
    iPoseProof (step_fupdN_fupd_finally ∅ ∅ m
      (▷^(k - m) ◇ Q)%I with "Hchain") as "Hfinal".
    (* Step 3: simplify [▷^m ◇ (▷^(k-m) ◇ Q) ⊢ ▷^k ◇ Q] using
       [except_0_laterN] + [except_0_idemp] + [laterN_add].  This is
       a pure iProp entailment, so we discharge via [fupd_finally_mono]'s
       Coq-level side condition. *)
    iApply (fupd_finally_mono _ _ (▷^k ◇ Q)%I); last iApply "Hfinal".
    transitivity (▷^m (▷^(k - m) ◇ Q) : iProp Σ)%I.
    - apply bi.laterN_mono. rewrite except_0_laterN except_0_idemp //.
    - rewrite -laterN_add.
      replace (m + (k - m))%nat with k by lia.
      done.
  Qed.

  (** WP to fupd_finally adequacy, polynomial-aware: each step peels
      [S (num_laters_per_step k)] credits off the budget for the
      WP-step wand and absorbs the resulting chain's laters into the
      outer [total_step_credits k n] buffer. *)
  Theorem wp_refRcoupl k
      (ε : nonnegreal) (e : language.expr lrust_prob_lang)
      (σ : language.state lrust_prob_lang) n φ :
    £ (total_step_credits k n) ∗ state_interp k σ ∗ err_interp ε ∗
      WP e {{ v, ⌜φ v⌝ }} ⊢
    |={⊤|}=> ▷^(total_step_credits k n) ◇ ⌜pgl (exec n (e, σ)) φ ε⌝.
  Proof.
    iInduction n as [|n] "IH" forall (k e σ ε); iIntros "(Hlc & Hσ & Hε & Hwp)".
    - rewrite /exec /=.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite pgl_wp_value_fupd'.
        iApply (fupd_to_fupd_finally 0 ⊤ ⊤).
        iMod "Hwp" as "%". iModIntro.
        iPureIntro.
        apply (pgl_mon_grading _ _ 0); [apply cond_nonneg|].
        apply pgl_dret; auto.
      + iApply fupd_finally_intro. iApply plain_plainly. simpl.
        rewrite /bi_except_0. iRight.
        iPureIntro. apply pgl_dzero, Rle_ge, cond_nonneg.
    - rewrite total_step_credits_S.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        iApply (elim_fupd_fupd_finally _ 0 ⊤ ⊤ ⌜φ v⌝
          ⌜pgl (exec (S n) (of_val v, σ)) φ ε⌝); [lia|].
        rewrite pgl_wp_value_fupd'.
        iSplitL "Hwp"; [iApply "Hwp"|].
        iIntros (l' ->) "%Hφv".
        iApply fupd_finally_intro. iApply plain_plainly.
        iApply bi.laterN_intro.
        rewrite /bi_except_0. iRight. iPureIntro.
        erewrite exec_is_final; [|rewrite /= to_of_val //].
        apply (pgl_mon_grading _ _ 0); [apply cond_nonneg|].
        apply pgl_dret; auto.
      + rewrite pgl_wp_unfold /pgl_wp_pre /= Heq.
        iSpecialize ("Hwp" $! k with "[$Hσ $Hε]").
        (* Peel [S (num_laters_per_step k)] credits for this step's
           step-fupd-N chain, save [total_step_credits (S k) n] for
           the recursive call. *)
        iDestruct (lc_split (S (num_laters_per_step k))
                            (total_step_credits (S k) n) with "Hlc")
          as "[Hcred Hlc]".
        iApply (elim_fupd_fupd_finally (total_step_credits k (S n)) 0 ⊤ ∅ _
          ⌜pgl (prim_step e σ ≫= exec n) φ ε⌝); first lia.
        iSplitL "Hwp"; [iApply "Hwp"|].
        iIntros (l' ->) "Hlift".
        rewrite Nat.sub_0_r.
        iPoseProof
          (glm_mono _ (λ '(e2, σ2) ε2, |={∅|}=> ▷^(S (num_laters_per_step k)
                                                + total_step_credits (S k) n)
             ◇ ⌜pgl (exec n (e2, σ2)) φ ε2⌝)%I
            with "[%] [Hcred Hlc] Hlift") as "H".
        { apply Rle_refl. }
        { iIntros ([e' σ'] ε') "H".
          (* H : £(S np k) -∗ |={∅}▷=>^(S np k) |={∅,⊤}=>
                   state_interp (S k) σ' ∗ err ε' ∗ WP e' ... *)
          iSpecialize ("H" with "Hcred").
          (* Use [elim_step_fupdN_chain] to absorb the
             [|={∅}▷=>^(S np k)] chain into the outer buffer's first
             [S np k] laters; recurse on [|={⊤|}=> ▷^(total_step_credits (S k) n)
             ◇ ⌜pgl⌝] for the rest. *)
          iApply (elim_step_fupdN_chain (S (num_laters_per_step k))
                    _ ⊤
                    (state_interp (S k) σ' ∗ err_interp ε' ∗
                       WP e' {{ v, ⌜φ v⌝ }})%I
                    ⌜pgl (exec n (e', σ')) φ ε'⌝
                  with "H").
          { lia. }
          iIntros "(Hσ' & Hε' & Hwp')".
          replace (S (num_laters_per_step k) + total_step_credits (S k) n -
                   S (num_laters_per_step k))%nat
            with (total_step_credits (S k) n) by lia.
          iApply ("IH" $! (S k) with "[$Hlc $Hσ' $Hε' $Hwp']"). }
        replace (prim_step e σ) with (step (e, σ)) by reflexivity.
        rewrite -exec_Sn_not_final; last by rewrite /is_final /to_final /= Heq.
        (* Explicit args avoid the heavy unification cost of
           [iApply (glm_erasure with "H")]: [k]/[n] are pinned down
           rather than left as metavariables. *)
        iPoseProof
          (glm_erasure e σ
             (S (num_laters_per_step k) + total_step_credits (S k) n)
             n φ ε with "H") as "Heras".
        { lia. }
        { exact Heq. }
        iApply "Heras".
  Qed.

  (** The safety analogue of [wp_refRcoupl], and the
      polynomial-credit analogue of eris's [wp_safety_hfupd] (which
      assumes [num_laters_per_step ≡ 0], false for our schedule).
      [pexec n] loses mass exactly on stuck configurations, so the
      conclusion bounds the probability of getting stuck within [n]
      steps by [ε]. *)
  Theorem wp_refRcoupl_safety k
      (ε : nonnegreal) (e : language.expr lrust_prob_lang)
      (σ : language.state lrust_prob_lang) n φ :
    £ (total_step_credits k n) ∗ state_interp k σ ∗ err_interp ε ∗
      WP e {{ v, ⌜φ v⌝ }} ⊢
    |={⊤|}=> ▷^(total_step_credits k n) ◇
               ⌜(SeriesC (pexec n (e, σ)) >= 1 - nonneg ε)%R⌝.
  Proof.
    iInduction n as [|n] "IH" forall (k e σ ε); iIntros "(Hlc & Hσ & Hε & Hwp)".
    - iApply fupd_finally_intro. iApply plain_plainly. simpl.
      rewrite /bi_except_0. iRight. iPureIntro.
      trans 1%R; last first.
      { pose proof cond_nonneg ε. lra. }
      apply Rle_ge. rewrite dret_mass. done.
    - rewrite total_step_credits_S.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        iApply (elim_fupd_fupd_finally _ 0 ⊤ ⊤ ⌜φ v⌝
          ⌜(SeriesC (pexec (S n) (of_val v, σ)) >= 1 - nonneg ε)%R⌝); [lia|].
        rewrite pgl_wp_value_fupd'.
        iSplitL "Hwp"; [iApply "Hwp"|].
        iIntros (l' ->) "_".
        iApply fupd_finally_intro. iApply plain_plainly.
        iApply bi.laterN_intro.
        rewrite /bi_except_0. iRight. iPureIntro.
        rewrite pexec_is_final; last (rewrite /is_final /to_final /= to_of_val; by eexists).
        rewrite dret_mass.
        pose proof cond_nonneg ε. apply Rle_ge. lra.
      + rewrite pgl_wp_unfold /pgl_wp_pre /= Heq.
        iSpecialize ("Hwp" $! k with "[$Hσ $Hε]").
        iDestruct (lc_split (S (num_laters_per_step k))
                            (total_step_credits (S k) n) with "Hlc")
          as "[Hcred Hlc]".
        iApply (elim_fupd_fupd_finally (total_step_credits k (S n)) 0 ⊤ ∅ _
          ⌜(SeriesC (iterM (S n) prim_step_or_val (e, σ)) >= 1 - nonneg ε)%R⌝); first lia.
        iSplitL "Hwp"; [iApply "Hwp"|].
        iIntros (l' ->) "Hlift".
        rewrite Nat.sub_0_r.
        iPoseProof
          (glm_mono _ (λ '(e2, σ2) ε2, |={∅|}=> ▷^(S (num_laters_per_step k)
                                                + total_step_credits (S k) n)
             ◇ ⌜(SeriesC (iterM n prim_step_or_val (e2, σ2)) >= 1 - nonneg ε2)%R⌝)%I
            with "[%] [Hcred Hlc] Hlift") as "H".
        { apply Rle_refl. }
        { iIntros ([e' σ'] ε') "H".
          iSpecialize ("H" with "Hcred").
          iApply (elim_step_fupdN_chain (S (num_laters_per_step k))
                    _ ⊤
                    (state_interp (S k) σ' ∗ err_interp ε' ∗
                       WP e' {{ v, ⌜φ v⌝ }})%I
                    ⌜(SeriesC (iterM n prim_step_or_val (e', σ')) >= 1 - nonneg ε')%R⌝
                  with "H").
          { lia. }
          iIntros "(Hσ' & Hε' & Hwp')".
          replace (S (num_laters_per_step k) + total_step_credits (S k) n -
                   S (num_laters_per_step k))%nat
            with (total_step_credits (S k) n) by lia.
          iApply ("IH" $! (S k) with "[$Hlc $Hσ' $Hε' $Hwp']"). }
        iPoseProof
          (glm_erasure_safety e σ
             (S (num_laters_per_step k) + total_step_credits (S k) n)
             n ε with "H") as "Heras".
        { exact Heq. }
        iApply "Heras".
  Qed.


End adequacy.

(** [total_step_credits] with [lrustGS_erisWpGS]'s
    [sum_advance_credits (k+1)] schedule inlined, for the theorems
    below which are stated outside [Section adequacy]. *)
Fixpoint lrust_total_step_credits (k n : nat) : nat :=
  match n with
  | 0%nat => 0%nat
  | S n' => S (sum_advance_credits (k + 1)) + lrust_total_step_credits (S k) n'
  end.

(** Pre-ghost-state bundle: every inG/preG instance needed to
    allocate an [lrustGS Σ] from scratch. *)
Class lrustGpreS (Σ : gFunctors) := LrustGpreS {
  #[global] lrustGpreS_invGpreS :: invGpreS Σ;
  #[global] lrustGpreS_heap_inG :: inG Σ (authR heap.heapUR);
  #[global] lrustGpreS_heap_freeable_inG :: inG Σ (authR heap.heap_freeableUR);
  #[global] lrustGpreS_na_logicG :: na_logicG loc val Σ;
  #[global] lrustGpreS_na_invG :: na_invG Σ;
  #[global] lrustGpreS_alc_logicG :: alc_logicG Σ;
  #[global] lrustGpreS_timePreG :: timePreG Σ;
}.

(** Adds [ecGpreS] for eris's error credits. *)
Class lrustErisGpreS (Σ : gFunctors) := LrustErisGpreS {
  #[global] lrustErisGpreS_lrustGpreS :: lrustGpreS Σ;
  #[global] lrustErisGpreS_ecGpreS :: ecGpreS Σ;
}.

(** Top-level pgl adequacy, via [fupd_finally_soundness] over
    [HasLc].  [K] is the caller's later-credit budget and should be at
    least [lrust_total_step_credits 1 n]. *)
Theorem lrust_wp_pgl `{!lrustErisGpreS Σ}
    (e : language.expr lrust_prob_lang) (σ : language.state lrust_prob_lang)
    n (ε : R) (K : nat) φ :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  (0 <= ε)%R →
  (∀ `{!lrustGS Σ},
      ⊢ £ K -∗ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  pgl (exec n (e, σ)) φ ε.
Proof.
  intros Hσ Hε Hwp.
  apply (pure_soundness (PROP:=iPropI Σ)).
  apply (laterN_soundness _ (S (lrust_total_step_credits 1 n))).
  rewrite laterN_later -except_0_into_later.
  destruct (decide (ε < 1)%R) as [Hcr|Hcr]; last first.
  { iApply laterN_intro. iApply except_0_intro. iPureIntro.
    apply not_Rlt, Rge_le in Hcr.
    rewrite /pgl. intros. eapply Rle_trans; [apply prob_le_1|done]. }
  apply (fupd_finally_soundness HasLc (K + lrust_total_step_credits 1 n) ⊤).
  iIntros (Hinv) "Hlc_total".
  (* Split: K credits for the user's WP, total_step_credits for wp_refRcoupl. *)
  iDestruct (lc_split K (lrust_total_step_credits 1 n) with "Hlc_total")
    as "[H£ Hlc]".
  set ε' := mknonnegreal ε Hε.
  iMod (ec_alloc ε') as (Hec) "[Hs Hf]"; [done|].
  iMod (non_atomic_cell_map.non_atomic_map_alloc_heap σ Hσ) as (vγ) "Hvγ".
  iMod (own_alloc (● (∅ : heap.heap_freeableUR))) as (fγ) "Hfγ";
    [by apply auth_auth_valid|].
  iMod na_invariants_fork.na_alloc as (threadpool_γ) "Hpool".
  iMod atomic_lock_counter.atomic_lock_ctr_alloc as (alc_γ) "Hctr".
  iMod (own_alloc (●MN 2 ⋅ mono_nat_lb 2)) as (γglob) "[A B]";
    [by apply mono_nat_both_valid|].
  iMod (own_alloc (●MN 0)) as (γpers) "_";
    [by apply mono_nat_auth_valid|].
  iMod (own_alloc (● 0%nat)) as (γcum) "_";
    [by apply auth_auth_valid|].
  iMod (own_alloc
          (to_frac_agree (A:=leibnizO bool) (1/2) true ⋅
           to_frac_agree (A:=leibnizO bool) (1/2) true))
    as (γbool) "[Hbool _]".
  { rewrite frac_agree_op_valid Qp.half_half. split; trivial. }
  iMod (own_alloc
          (to_frac_agree (A:=leibnizO nat) (1/2) 0%nat ⋅
           to_frac_agree (A:=leibnizO nat) (1/2) 0%nat))
    as (γsum) "_".
  { rewrite frac_agree_op_valid Qp.half_half. split; trivial. }
  pose (Htime := TimeG Σ _ _ _ _ γglob γpers γcum γbool γsum).
  pose (Hheap := heap.HeapGS _ _ _ _ vγ fγ threadpool_γ alc_γ).
  pose (HlrustGS := LRustGS Σ Hinv _ _ Hheap Hec Htime).
  change ε with (nonneg ε').
  iPoseProof (wp_refRcoupl 1 ε' e σ n φ) as "H".
  iSpecialize ("H" with "[-]").
  { iFrame "Hlc".
    iSplitR "Hs H£ Hf".
    { rewrite /state_interp /=. iSplitR "A Hbool".
      - rewrite /heap.heap_ctx. iExists ∅. iFrame "Hvγ Hfγ".
        iSplit.
        { iPureIntro. rewrite /heap.heap_freeable_rel. intros blk qs Hbad.
          by rewrite lookup_empty in Hbad. }
        rewrite /heap.heap_ato_ctx. iFrame.
      - (* time_interp 1 in left disjunct (enabled true). *)
        iLeft. iFrame. iPureIntro. lia. }
    iFrame "Hs".
    iPoseProof (Hwp HlrustGS) as "Hwp'".
    iApply ("Hwp'" with "H£ Hf"). }
  iApply "H".
Qed.

(** ** Safety: the nontrivial operational consequence of a WP

    [lrust_wp_pgl] says nothing when the postcondition is [λ _, True]
    ([pgl_trivial] proves that for any distribution).  [pexec n] is a
    genuine sub-distribution whose missing mass sits exactly on stuck
    configurations, so the bounds below do carry content. *)

(** Top-level safety-mass bound from a WP; same ghost-state
    allocation and [K] convention as [lrust_wp_pgl]. *)
Theorem lrust_wp_safety `{!lrustErisGpreS Σ}
    (e : language.expr lrust_prob_lang) (σ : language.state lrust_prob_lang)
    n (ε : R) (K : nat) φ :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  (0 <= ε)%R →
  (∀ `{!lrustGS Σ},
      ⊢ £ K -∗ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  (SeriesC (pexec n (e, σ)) >= 1 - ε)%R.
Proof.
  intros Hσ Hε Hwp.
  apply (pure_soundness (PROP:=iPropI Σ)).
  apply (laterN_soundness _ (S (lrust_total_step_credits 1 n))).
  rewrite laterN_later -except_0_into_later.
  destruct (decide (ε < 1)%R) as [Hcr|Hcr]; last first.
  { iApply laterN_intro. iApply except_0_intro. iPureIntro.
    apply not_Rlt, Rge_le in Hcr.
    trans 0%R; last first.
    { lra. }
    apply Rle_ge, SeriesC_ge_0'. intros; auto. }
  apply (fupd_finally_soundness HasLc (K + lrust_total_step_credits 1 n) ⊤).
  iIntros (Hinv) "Hlc_total".
  iDestruct (lc_split K (lrust_total_step_credits 1 n) with "Hlc_total")
    as "[H£ Hlc]".
  set ε' := mknonnegreal ε Hε.
  iMod (ec_alloc ε') as (Hec) "[Hs Hf]"; [done|].
  iMod (non_atomic_cell_map.non_atomic_map_alloc_heap σ Hσ) as (vγ) "Hvγ".
  iMod (own_alloc (● (∅ : heap.heap_freeableUR))) as (fγ) "Hfγ";
    [by apply auth_auth_valid|].
  iMod na_invariants_fork.na_alloc as (threadpool_γ) "Hpool".
  iMod atomic_lock_counter.atomic_lock_ctr_alloc as (alc_γ) "Hctr".
  iMod (own_alloc (●MN 2 ⋅ mono_nat_lb 2)) as (γglob) "[A B]";
    [by apply mono_nat_both_valid|].
  iMod (own_alloc (●MN 0)) as (γpers) "_";
    [by apply mono_nat_auth_valid|].
  iMod (own_alloc (● 0%nat)) as (γcum) "_";
    [by apply auth_auth_valid|].
  iMod (own_alloc
          (to_frac_agree (A:=leibnizO bool) (1/2) true ⋅
           to_frac_agree (A:=leibnizO bool) (1/2) true))
    as (γbool) "[Hbool _]".
  { rewrite frac_agree_op_valid Qp.half_half. split; trivial. }
  iMod (own_alloc
          (to_frac_agree (A:=leibnizO nat) (1/2) 0%nat ⋅
           to_frac_agree (A:=leibnizO nat) (1/2) 0%nat))
    as (γsum) "_".
  { rewrite frac_agree_op_valid Qp.half_half. split; trivial. }
  pose (Htime := TimeG Σ _ _ _ _ γglob γpers γcum γbool γsum).
  pose (Hheap := heap.HeapGS _ _ _ _ vγ fγ threadpool_γ alc_γ).
  pose (HlrustGS := LRustGS Σ Hinv _ _ Hheap Hec Htime).
  change ε with (nonneg ε').
  iPoseProof (wp_refRcoupl_safety 1 ε' e σ n φ) as "H".
  iSpecialize ("H" with "[-]").
  { iFrame "Hlc".
    iSplitR "Hs H£ Hf".
    { rewrite /state_interp /=. iSplitR "A Hbool".
      - rewrite /heap.heap_ctx. iExists ∅. iFrame "Hvγ Hfγ".
        iSplit.
        { iPureIntro. rewrite /heap.heap_freeable_rel. intros blk qs Hbad.
          by rewrite lookup_empty in Hbad. }
        rewrite /heap.heap_ato_ctx. iFrame.
      - iLeft. iFrame. iPureIntro. lia. }
    iFrame "Hs".
    iPoseProof (Hwp HlrustGS) as "Hwp'".
    iApply ("Hwp'" with "H£ Hf"). }
  iApply "H".
Qed.

(** If a sub-distribution has full mass and [P] already carries all
    of it, then [P] holds pointwise on the support.  This is what
    turns the mass form of safety into the pointwise one. *)
Lemma probp_full_pos `{Countable A} (μ : distr A) (P : A → Prop)
    `{∀ a, Decision (P a)} :
  (SeriesC μ >= 1)%R → probp μ P = 1%R → ∀ a, (μ a > 0)%R → P a.
Proof.
  intros Hmass Hgood a Ha.
  destruct (decide (P a)) as [HP|HnP]; [exact HP|exfalso].
  pose proof (pmf_SeriesC μ) as Hle.
  pose proof (SeriesC_split_pred μ (λ x, bool_decide (P x))
                (pmf_pos μ) (pmf_ex_seriesC μ)) as Hsplit.
  rewrite /probp in Hgood.
  assert (∀ x, 0 <= (if bool_decide (P x) then 0%R else μ x))%R as Hnn.
  { intros x. case_bool_decide; [lra|auto]. }
  assert (ex_seriesC (λ x, if bool_decide (P x) then 0%R else μ x)) as Hex.
  { apply (ex_seriesC_le _ μ); [|done].
    intros x. case_bool_decide; split; auto; lra. }
  assert (SeriesC (λ x, if bool_decide (P x) then 0%R else μ x) = 0)%R
    as Hzero by lra.
  pose proof (SeriesC_const0 _ Hnn (SeriesC_correct' _ _ Hzero Hex) a) as Hpt.
  rewrite bool_decide_eq_false_2 // in Hpt. lra.
Qed.

(** The mass of [pexec (S n)] is exactly the probability that the
    [n]-step partial execution lands in a not-stuck configuration.
    Ported from eris, with [ectx_lang_mixin] replaced by the generic
    [prim_step_mass]. *)
Lemma pexec_safety_relate (e : language.expr lrust_prob_lang)
    (σ : language.state lrust_prob_lang) n :
  probp (pexec n (e, σ)) (λ ρ, is_final ρ ∨ reducible ρ) =
  SeriesC (pexec (S n) (e, σ)).
Proof.
  revert e σ.
  induction n; intros e σ.
  - simpl. rewrite pexec_O. rewrite pexec_1.
    rewrite /probp. rewrite /step_or_final.
    erewrite (SeriesC_ext _ (λ x, if bool_decide (is_final (e, σ) ∨ reducible (e, σ))
                                  then dret (e, σ) x else 0%R)); last first.
    { intros. destruct (decide (n = (e, σ))).
      - subst. done.
      - rewrite dret_0; last done. by repeat case_match. }
    case_bool_decide as H.
    + rewrite dret_mass. case_match; first by rewrite dret_mass.
      simpl. symmetry. apply (@prim_step_mass lrust_prob_lang e σ).
      destruct H as [Hfin|Hred]; last exact Hred.
      exfalso. destruct Hfin. naive_solver.
    + rewrite SeriesC_0; last done.
      case_match; first exfalso.
      * apply H. naive_solver.
      * symmetry. apply SeriesC_0.
        intros x. assert (0 <= step (e, σ) x)%R as [|] by auto; auto.
        exfalso. apply H. right. rewrite /reducible. naive_solver.
  - rewrite /probp. rewrite /probp in IHn.
    rewrite (pexec_Sn_r _ (S n)).
    rewrite dbind_mass.
    apply SeriesC_ext.
    intros [].
    case_bool_decide as H.
    + replace (SeriesC _) with 1%R; first lra.
      symmetry.
      destruct H.
      * rewrite /step_or_final. case_match; first apply dret_mass.
        exfalso. destruct H. naive_solver.
      * rewrite /step_or_final. case_match; first apply dret_mass.
        simpl. by apply (@prim_step_mass lrust_prob_lang).
    + replace (SeriesC _) with 0%R; first lra.
      symmetry.
      rewrite /step_or_final.
      case_match.
      * exfalso. naive_solver.
      * apply SeriesC_0.
        intros x. eassert (0 <= step _ x)%R as [|<-] by auto; auto.
        exfalso. apply H. right. rewrite /reducible. naive_solver.
Qed.

(** The same bound stated directly: with probability at least
    [1 - ε] the [n]-step execution is final or can take another
    step. *)
Corollary lrust_wp_safety' `{!lrustErisGpreS Σ}
    (e : language.expr lrust_prob_lang) (σ : language.state lrust_prob_lang)
    n (ε : R) (K : nat) φ :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  (0 <= ε)%R →
  (∀ `{!lrustGS Σ},
      ⊢ £ K -∗ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  (probp (pexec n (e, σ)) (λ ρ, is_final ρ ∨ reducible ρ) >= 1 - ε)%R.
Proof.
  intros Hσ Hε Hwp.
  rewrite pexec_safety_relate.
  by eapply (lrust_wp_safety _ _ _ _ K φ).
Qed.
