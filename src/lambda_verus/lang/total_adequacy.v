(** Termination adequacy for [lrust_prob_lang]'s total weakest precondition.

    Ported from [clutch.eris.total_adequacy], which is stated for
    [prob_lang].  Two simplifications fall out of our language:

    - [lrust_prob_lang] has no presampling tapes
      ([state_step_prob σ (α : Empty_set) := dzero], [get_active σ := []]),
      so [glm]'s state-step disjunct is vacuous and the 120-line
      [twp_step_fupd_tgl_state_step] together with the [erasure] argument
      disappears;
    - there is no later-credit budget to thread, so unlike the partial
      [lang/adequacy.v] there is no [total_step_credits] splitting.

    The conclusion is the one the partial logic cannot state:
    a program whose derivation spends [ε] terminates with probability at
    least [1 - ε]. *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.algebra Require Import auth lib.mono_nat numbers dfrac_agree.
From Coquelicot Require Export Lim_seq Rbar.
From clutch.common Require Export language exec.
From clutch.base_logic Require Export error_credits.
From clutch.eris Require Import weakestpre total_weakestpre.
From clutch.prob Require Import distribution graded_predicate_lifting.
From guarding.internal Require Import na_invariants_fork.
From lrust.util Require Import non_atomic_cell_map atomic_lock_counter.
From lrust.lang Require Export lang heap lifting time adequacy.
Set Default Proof Using "Type".

Import uPred.
Local Open Scope R.

Lemma twp_step_fupd_tgl_prim_step (e : language.expr lrust_prob_lang) σ (ε ε1:nonnegreal) (ε2: language.cfg lrust_prob_lang -> nonnegreal) R P:
  reducible (e, σ) ->
  (∃ r, ∀ ρ : language.cfg lrust_prob_lang, ε2 ρ <= r) ->
  ε1 + SeriesC
         (λ ρ, prim_step e σ ρ * ε2 ρ) <= ε -> pgl (prim_step e σ) R ε1 ->
  (∀ e, R e → 1 - ε2 e <= prob (lim_exec e) P) ->
  1 - ε <= SeriesC (λ a, step (e, σ) a * prob (lim_exec a) P).
Proof.
  intros Hred Hbound Hsum Hub H.
  simpl.
  assert (1 - (ε1 + SeriesC (λ ρ, prim_step e σ ρ * ε2 ρ)) <=
            SeriesC (λ a, prim_step e σ a * prob (lim_exec a) P)) as Hint; last first.
  { etrans; last exact. apply Rminus_le. lra. }
  rewrite Rcomplements.Rle_minus_l Rplus_comm Rplus_assoc.
  rewrite <-SeriesC_plus; last first.
  { eapply ex_seriesC_le; last first.
    - instantiate (1 := prim_step e σ).
      apply pmf_ex_seriesC.
    -  intros. split.
       + apply Rmult_le_pos; try done. apply prob_ge_0.
       + rewrite <-Rmult_1_r. apply Rmult_le_compat_l; first done. apply prob_le_1.
  }
  { destruct Hbound as [r ?]. eapply ex_seriesC_le; last first.
    - instantiate (1 := λ ρ, prim_step e σ ρ * r).
      apply ex_seriesC_scal_r.
      apply pmf_ex_seriesC.
    -  intros. split.
       + apply Rmult_le_pos; first done. apply cond_nonneg.
       + by apply Rmult_le_compat_l.
  }
  erewrite SeriesC_ext; last first.
  { intros n. by rewrite <-Rmult_plus_distr_l. }
  simpl in Hub, H, R. simpl.
  rewrite (SeriesC_ext _
             (λ ρ, (if bool_decide(R ρ) then prim_step e σ ρ * (ε2 ρ + prob (lim_exec ρ) P) else 0)+
                     if bool_decide (~R ρ) then prim_step e σ ρ * (ε2 ρ + prob (lim_exec ρ) P) else 0
          )); last first.
  { intros. repeat case_bool_decide; try done.
    - by rewrite Rplus_0_r.
    - by rewrite Rplus_0_l.
  }
  rewrite SeriesC_plus; last first.
  { eapply ex_seriesC_filter_pos.
    - intros. apply Rmult_le_pos; first done.
      apply Rplus_le_le_0_compat; [apply cond_nonneg|apply prob_ge_0].
    - destruct Hbound as [r?].
      eapply ex_seriesC_ext; last first.
      + eapply pmf_ex_seriesC_mult_fn. shelve.
      + intros. simpl. f_equal.
        Unshelve. exists (r+1).
        intros; split.
        * apply Rplus_le_le_0_compat; [apply cond_nonneg|apply prob_ge_0].
        * apply Rplus_le_compat; try done. apply prob_le_1.
  }
  { eapply ex_seriesC_filter_pos.
    - intros. apply Rmult_le_pos; first done.
      apply Rplus_le_le_0_compat; [apply cond_nonneg|apply prob_ge_0].
    - destruct Hbound as [r?].
      eapply ex_seriesC_ext; last first.
      + eapply pmf_ex_seriesC_mult_fn. shelve.
      + intros. simpl. f_equal.
        Unshelve. exists (r+1).
        intros; split.
        * apply Rplus_le_le_0_compat; [apply cond_nonneg|apply prob_ge_0].
        * apply Rplus_le_compat; try done. apply prob_le_1.
  }
  trans (ε1 +
  (SeriesC
     (λ x : expr * state,
        if bool_decide (R x) then prim_step e σ x else 0) +
   SeriesC
     (λ x : expr * state,
        if bool_decide (¬ R x) then prim_step e σ x * (ε2 x + prob (lim_exec x) P) else 0))).
  2:{ apply Rplus_le_compat_l. apply Rplus_le_compat_r.
      apply SeriesC_le.
      - intros. case_bool_decide; last done.
        split; [apply pmf_pos|].
        rewrite -{1}(Rmult_1_r (prim_step _ _ _)). apply Rmult_le_compat_l; [apply pmf_pos|].
        pose proof (H n H0).
        rewrite Rplus_comm. by rewrite <-Rcomplements.Rle_minus_l.
      - apply ex_seriesC_filter_pos.
        + intros. apply Rmult_le_pos; [apply pmf_pos|].
          apply Rplus_le_le_0_compat; [apply cond_nonneg|apply prob_ge_0].
        + apply pmf_ex_seriesC_mult_fn. destruct Hbound as [r?]. exists (r+1).
          intros; split.
          * apply Rplus_le_le_0_compat; [apply cond_nonneg|apply prob_ge_0].
          * apply Rplus_le_compat; try done. apply prob_le_1.
  }
  trans (ε1 +
           (SeriesC (λ x : expr * state, if bool_decide (R x) then prim_step e σ x else 0))); last first.
  { rewrite -Rplus_assoc. rewrite -{1}(Rplus_0_r (_+_)).
    apply Rplus_le_compat_l. apply SeriesC_ge_0'.
    intros. case_bool_decide; try lra.
    apply Rmult_le_pos; [apply pmf_pos|].
    apply Rplus_le_le_0_compat; [apply cond_nonneg|apply prob_ge_0].
  }
  rewrite /pgl in Hub.
  assert (prob (prim_step e σ) (∽(λ ρ, bool_decide(R ρ)))%P <= ε1).
  { etrans; last exact. apply SeriesC_le; last apply ex_seriesC_filter_bool_pos; try done.
    intros; repeat case_bool_decide; try done. simpl. done. }
  etrans.
  2: { apply Rplus_le_compat_r. exact. }
  rewrite /prob. simpl.
  rewrite <-SeriesC_plus; last first.
  - apply ex_seriesC_filter_pos; [apply pmf_pos|apply pmf_ex_seriesC].
  - eapply ex_seriesC_ext.
    + intros. by rewrite <- bool_decide_not.
    + apply ex_seriesC_filter_pos; [apply pmf_pos|apply pmf_ex_seriesC].
  - rewrite (SeriesC_ext _ (λ ρ, prim_step e σ ρ)); last first.
    { intros. case_bool_decide; simpl.
      - apply Rplus_0_l.
      - apply Rplus_0_r.
    }
    simpl. apply Req_le_sym.
    epose proof (@prim_step_mass lrust_prob_lang) as K. simpl in K.
    apply K. apply Hred.
Qed.

(** [fupd_finally] helpers.  [clutch.eris.adequacy] has these, but behind
    [Context `{!erisGS Σ}], i.e. specialised to [prob_lang]; they only need
    the invariant interface, so we restate them here. *)
(** [lrust_prob_lang] has no presampling tapes. *)
Lemma lrust_get_active_nil (σ : language.state lrust_prob_lang) :
  language.get_active σ = [].
Proof. done. Qed.

Section hfupd.
  Context `{!invGS_gen hlc Σ}.

  Lemma hfupd_intro {E} (P : iProp Σ) `{!Plain P} : P -∗ |={E|}=> P.
  Proof.
    iIntros "HP".
    iAssert (■ P)%I with "[HP]" as "#HP'"; [by iApply plain_plainly|].
    by iApply fupd_finally_intro.
  Qed.

  Lemma elim_fupd_hfupd_plain (k l : nat) (E1 E2 : coPset) (P Q : iProp Σ) :
    (l ≤ k)%nat →
    (|={E1, E2}=> P) ∗ (∀ l', ⌜l' = l⌝ -∗ P -∗ |={E2|}=> ▷^(k - l') ◇ Q)
    ⊢ |={E1|}=> ▷^k ◇ Q.
  Proof.
    iIntros (Hlk) "[H1 H2]". iMod "H1" as "HP".
    iSpecialize ("H2" $! l with "[//] HP").
    iApply (fupd_finally_mono with "H2").
    replace k with (l + (k - l))%nat at 2 by lia.
    rewrite laterN_add. iIntros "H". by iApply laterN_intro.
  Qed.
End hfupd.

Section total_adequacy.
  Context `{!erisWpGS lrust_prob_lang Σ}.

  (** Helper: lift a pure-monotone implication through [◇ ⌜·⌝]. *)
  Local Lemma except_0_pure_mono_iprop (P Q : Prop) :
    (P → Q) → ((◇ ⌜P⌝ : iProp Σ) ⊢ ◇ ⌜Q⌝).
  Proof. intros HPQ. apply bi.except_0_mono, bi.pure_mono, HPQ. Qed.

  Lemma tgl_dbind' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (R : A → Prop) (T : A' → Prop) ε ε':
    ⌜ 0 <= ε ⌝ -∗
    ⌜ 0 <= ε'⌝ -∗
    ⌜tgl μ R ε⌝ -∗
    (∀ a , ⌜R a⌝ -∗ |={∅|}=> ◇ ⌜tgl (f a) T ε'⌝) -∗
    |={∅|}=> ◇ ⌜tgl (dbind f μ) T (ε + ε')⌝ : iProp Σ.
  Proof.
    iIntros (Hε Hε' HR) "H".
    iApply (fupd_finally_mono _ (◇ ⌜∀ a, R a → tgl (f a) T ε'⌝)%I).
    { apply except_0_pure_mono_iprop. intros Hall.
      eapply tgl_dbind; eauto. }
    iIntros (a HRa). iApply ("H" with "[//]").
  Qed.

  Theorem twp_step_fupd_tgl k (e : expr) (σ : state) (ε : nonnegreal) φ  :
    state_interp k σ ∗ err_interp (ε) ∗ WP e [{ v, ⌜φ v⌝ }] ⊢
    |={⊤|}=> ◇ ⌜tgl (lim_exec (e, σ)) φ ε⌝.
  Proof.
    iIntros "(Hstate & Herr & Htwp)".
    iRevert (k σ ε) "Hstate Herr".
    pose proof (tgl_wp_ind_simple ⊤ () (λ e, ∀ (k : nat) (a : state) (a0 : nonnegreal),
                                  state_interp k a -∗ err_interp a0 -∗
                                  |={⊤|}=> ◇ ⌜tgl (lim_exec (e, a)) φ a0⌝)%I) as H.
    iApply H.
    2: { destruct twp_default. done. }
    clear H e.
    iModIntro.
    iIntros (e) "H".
    iIntros (k σ ε) "Hs Hec".
    rewrite /tgl_wp_pre.
    case_match.
    - iApply (elim_fupd_hfupd_plain 0 0 ⊤ ⊤ (⌜φ v⌝)%I
        (⌜tgl (lim_exec (e, σ)) φ ε⌝)%I); [lia|].
      iSplitL "H"; [iApply "H"|].
      iIntros (l Hl) "%Hφ". assert (l = 0%nat) as -> by lia.
      iApply hfupd_intro. rewrite /bi_except_0. iRight. iPureIntro.
      rewrite /tgl/prob.
      etrans.
      2:{ eapply SeriesC_ge_elem; last apply ex_seriesC_filter_bool_pos; try done.
          intros. case_bool_decide; try lra. apply pmf_pos. }
      erewrite (lim_exec_term 0).
      { simpl. rewrite H. rewrite dret_1_1; last done. destruct ε. simpl.
        case_bool_decide; try lra. done. }
      simpl. rewrite H. by rewrite dret_mass.
    - iSpecialize ("H" $! k σ ε with "[$]").
      iApply (elim_fupd_hfupd_plain 0 0 ⊤ ∅ _
        (⌜tgl (lim_exec (e, σ)) φ ε⌝)%I with "[$H]"); first lia.
      iIntros (l Hl) "Hglm". assert (l = 0%nat) as -> by lia.
      iRevert (H).
      iApply (glm_strong_ind
        (λ e σ ε, ⌜language.to_val e = None⌝ -∗
                  |={∅|}=> ◇ ⌜tgl (lim_exec (e, σ)) φ ε⌝)%I
        with "[][$Hglm]").
      iModIntro. clear e σ ε. iIntros (e σ ε) "H %Hval".
      iDestruct "H" as "[H|[H | H]]".
      + iApply (fupd_finally_mono _ (◇ ⌜∀ ε' : nonnegreal,
            (ε < ε') → tgl (lim_exec (e, σ)) φ ε'⌝)%I).
        { iIntros "Hgoal". iStopProof.
          apply except_0_pure_mono_iprop.
          intros Hall.
          apply tgl_epsilon_limit; [apply Rle_ge, cond_nonneg|].
          intros ε' Hε'.
          assert (0 <= ε')%R as Hε'nn.
          { apply Rgt_lt in Hε'. etrans; [|left; eauto]. apply cond_nonneg. }
          eapply (Hall (mknonnegreal ε' Hε'nn)). simpl. lra. }
        rewrite bi.pure_forall except_0_forall.
        iApply fupd_finally_forall. iIntros (ε').
        destruct (decide (ε < ε')%R) as [Hε'|Hε']; last first.
        { iApply hfupd_intro. rewrite /bi_except_0. iRight.
          iPureIntro. intros. done. }
        iSpecialize ("H" $! ε' with "[//]").
        iApply (elim_fupd_hfupd_plain 0 0 ∅ ∅
          (exec_stutter
             (λ ε'' : nonnegreal,
                ((⌜language.to_val e = None⌝ ={∅|}=∗
                  ◇ ⌜tgl (lim_exec (e, σ)) φ ε''⌝) ∧
                 glm e σ ε''
                   (λ '(e2, σ2) (ε2 : nonnegreal),
                      |={∅,⊤}=> state_interp (S k) σ2 ∗ err_interp ε2 ∗
                        ∀ (k0 : nat) (a : state) (a0 : nonnegreal),
                          state_interp k0 a -∗ err_interp a0 ={⊤|}=∗
                          ◇ ⌜tgl (lim_exec (e2, a)) φ a0⌝))%I)
             ε')
          (⌜ε < ε' → tgl (lim_exec (e, σ)) φ ε'⌝)%I); [lia|].
        iSplitL "H"; [iApply "H"|].
        iIntros (l' Hl') "Hst". assert (l' = 0%nat) as -> by lia.
        iDestruct (exec_stutter_compat_1 _ _ with "[] Hst") as "[%H'|H2]".
        { iIntros (εa εb Hle) "H". iSplit.
          - iDestruct "H" as "[H _]". iIntros "%Hto". iSpecialize ("H" with "[//]").
            iApply (fupd_finally_mono _ _ with "H").
            apply except_0_pure_mono_iprop.
            intros Hge. eapply tgl_mon_grading; eauto.
          - iDestruct "H" as "[_ H]".
            iApply (glm_mono_grading with "[%] H"). exact Hle. }
        2: { iDestruct "H2" as "[H2 _]". iSpecialize ("H2" with "[//]").
          iApply (fupd_finally_mono _ _ with "H2").
          apply except_0_pure_mono_iprop. intros; auto. }
        iApply hfupd_intro. iApply laterN_intro.
        rewrite /bi_except_0. iRight. iPureIntro.
        intros _. rewrite /tgl. intros.
        eapply Rle_trans; [|apply prob_ge_0]. lra.
      + iDestruct "H" as "(%R & %ε1 & %ε2 & %Hred & %Hbound & %Hineq & %Hub & H)".
        rewrite lim_exec_step step_or_final_no_final.
        2: { by apply reducible_not_final. }
        iAssert (∀ ρ2 : language.expr lrust_prob_lang * language.state lrust_prob_lang,
          ⌜R ρ2⌝ -∗
          |={∅|}=> ◇ ⌜tgl (lim_exec ρ2) φ (ε2 ρ2)⌝)%I with "[H]" as "H".
        { iIntros (ρ2) "%Hρ2". destruct (ρ2) as (e2&σ2).
          iApply (elim_fupd_hfupd_plain 0 0 ∅ ∅
            (exec_stutter
               (λ ε' : nonnegreal,
                  (|={∅,⊤}=> state_interp (S k) σ2 ∗ err_interp ε' ∗
                    ∀ (k0 : nat) (a : state) (a0 : nonnegreal),
                      state_interp k0 a -∗ err_interp a0 ={⊤|}=∗
                      ◇ ⌜tgl (lim_exec (e2, a)) φ a0⌝)%I)
               (ε2 (e2, σ2)))
            (⌜tgl (lim_exec (e2, σ2)) φ (ε2 (e2, σ2))⌝)%I); [lia|].
          iSplitL "H"; [iApply ("H" $! e2 σ2 Hρ2)|].
          iIntros (l1 Hl1) "Hst". assert (l1 = 0%nat) as -> by lia.
          iDestruct "Hst" as "(%R' & %ε1' & %ε2' & %Hineq' & %Hlift' & H)".
          rewrite -(dret_id_left' (λ _ : (), lim_exec (e2, σ2)) tt).
          iApply (fupd_finally_mono _ (◇ ⌜tgl (dret tt ≫= λ _ : (), lim_exec (e2, σ2)) φ (ε1' + ε2')⌝)%I).
          { apply except_0_pure_mono_iprop.
            intros Htgl. eapply tgl_mon_grading; eauto. }
          iApply (tgl_dbind' (λ _ : (), lim_exec (e2, σ2)) (dret tt) R' (λ x, φ x) ε1' ε2').
          { iPureIntro. apply cond_nonneg. }
          { iPureIntro. apply cond_nonneg. }
          { iPureIntro. exact Hlift'. }
          iIntros (a HRa). destruct a.
          iSpecialize ("H" with "[//]").
          iApply (elim_fupd_hfupd_plain 0 0 ∅ ⊤
            (state_interp (S k) σ2 ∗ err_interp ε2' ∗
              (∀ (k0 : nat) (a : state) (a0 : nonnegreal),
                state_interp k0 a -∗ err_interp a0 ={⊤|}=∗
                ◇ ⌜tgl (lim_exec (e2, a)) φ a0⌝))%I
            (⌜tgl (lim_exec (e2, σ2)) φ ε2'⌝)%I); [lia|].
          iSplitL "H"; [iApply "H"|].
          iIntros (l' Hl') "(Hσ' & Hε' & Hwp')".
          assert (l' = 0%nat) as -> by lia.
          iSpecialize ("Hwp'" $! (S k) σ2 ε2' with "Hσ' Hε'").
          iApply (fupd_finally_mono _ _ with "Hwp'").
          apply except_0_pure_mono_iprop. intros Htgl. exact Htgl. }
        rewrite {2}/tgl.
        setoid_rewrite prob_dbind.
        iApply (fupd_finally_mono _ (◇ ⌜∀ e0, R e0 → 1 - (ε2 e0) <=
                          prob (lim_exec e0) (λ x, bool_decide (φ x))⌝)%I).
        { iIntros "Hgoal". iStopProof.
          apply except_0_pure_mono_iprop. intros HR.
          by eapply twp_step_fupd_tgl_prim_step. }
        iIntros (a HRa).
        iApply (fupd_finally_mono _ _ with "(H [//])").
        apply except_0_pure_mono_iprop.
        intros. by destruct a.
      + (* [lrust_prob_lang] has no presampling tapes, so [get_active σ] is
           [[]] and this disjunct is [False]. *)
        iExFalso. iStopProof.
        rewrite lrust_get_active_nil big_orL_nil. by iIntros "[]".
  Qed.
End total_adequacy.

(** ** Top-level termination adequacy

    Same ghost-state allocation as [lang/adequacy.v]'s [lrust_wp_pgl],
    minus the [total_step_credits] budget: a total WP step mints no later
    credits, so there is nothing to split.  [K] is a *fixed, up-front*
    credit budget the caller may use to strip finitely many laters; it is
    sound for the same reason [fupd_finally_soundness] is, and it cannot
    support a loop, since each iteration would need fresh credits. *)
Theorem lrust_twp_tgl `{!lrustErisGpreS Σ}
    (e : language.expr lrust_prob_lang) (σ : language.state lrust_prob_lang)
    (ε : R) (K : nat) φ :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  (0 <= ε)%R →
  (∀ `{!lrustGS Σ}, ⊢ £ K -∗ ↯ ε -∗ WP e [{ v, ⌜φ v⌝ }]) →
  tgl (lim_exec (e, σ)) φ ε.
Proof.
  intros Hσ Hε Htwp.
  apply (pure_soundness (PROP:=iPropI Σ)).
  apply (laterN_soundness _ 1).
  rewrite laterN_later -except_0_into_later.
  destruct (decide (ε < 1)%R) as [Hcr|Hcr]; last first.
  { iApply except_0_intro. iPureIntro.
    apply not_Rlt, Rge_le in Hcr.
    rewrite /tgl. intros. eapply Rle_trans; [|apply prob_ge_0]. lra. }
  apply (fupd_finally_soundness HasLc K ⊤).
  iIntros (Hinv) "H£".
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
  iPoseProof (twp_step_fupd_tgl (Σ:=Σ) 1 e σ ε' φ) as "H".
  iSpecialize ("H" with "[-]"); last iApply "H".
  iSplitR "Hs H£ Hf"; last iFrame "Hs".
  { rewrite /state_interp /=. iSplitR "A Hbool".
    - rewrite /heap.heap_ctx. iExists ∅. iFrame "Hvγ Hfγ".
      iSplit.
      { iPureIntro. rewrite /heap.heap_freeable_rel. intros blk qs Hbad.
        by rewrite lookup_empty in Hbad. }
      rewrite /heap.heap_ato_ctx. iFrame.
    - iLeft. iFrame. iPureIntro. lia. }
  iPoseProof (Htwp HlrustGS) as "Htwp'".
  iApply ("Htwp'" with "H£ Hf").
Qed.

(** The headline: a well-specified program terminates with probability at
    least [1 - ε].  This is what the partial logic cannot state. *)
Corollary lrust_twp_mass_lim_exec `{!lrustErisGpreS Σ}
    (e : language.expr lrust_prob_lang) (σ : language.state lrust_prob_lang)
    (ε : R) (K : nat) φ :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  (0 <= ε)%R →
  (∀ `{!lrustGS Σ}, ⊢ £ K -∗ ↯ ε -∗ WP e [{ v, ⌜φ v⌝ }]) →
  (1 - ε <= SeriesC (lim_exec (e, σ)))%R.
Proof.
  intros. eapply tgl_termination_ineq. by eapply lrust_twp_tgl.
Qed.
