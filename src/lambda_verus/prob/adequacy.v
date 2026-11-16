(** Adequacy for [prob/weakestpre.v]: from a WP to a [pgl] bound on
    [sch_exec] and a mass bound on [sch_pexec], for *every* scheduler.

    Ported from clutch's [coneris/adequacy.v] in its [fupd_finally] form
    (branch [coneris-lc]); additionally threads the step counter and a
    [£ (total_step_credits k n)] budget so that arbitrary
    [num_laters_per_step] are supported, as in AlerusBelt's sequential
    [lang/adequacy.v].  The lemmas end in [|={⊤|}=> ▷^_ ◇ ⌜_⌝]; the
    language-specific theorems allocate [state_interp] and close with
    [fupd_finally_soundness]. *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.bi Require Export lib.fixpoint_mono big_op.
From iris.base_logic.lib Require Import ghost_map invariants fancy_updates.
From iris.algebra Require Import excl.
From iris.prelude Require Import options.

From clutch.prelude Require Import stdpp_ext iris_ext.
From clutch.common Require Export con_language sch_erasable.
From lrust.prob Require Import weakestpre erasure.
From clutch.prob Require Import distribution mdp.
Import uPred.
Local Open Scope R.

Section adequacy.
  Context `{!alerusWpGS Λ Σ}.
  
  Lemma step_fupd_fupdN_S n (P : iProp Σ) :  ((|={∅}▷=>^(S n) P) ⊣⊢ (|={∅}=> |={∅}▷=>^(S n) P))%I.
  Proof. iSplit; iIntros; simpl; iApply fupd_idemp; iFrame. Qed.

  (** Pure-monotonicity through [▷^k ◇ ⌜·⌝]. *)
  Local Lemma laterN_except_0_pure_mono k (P Q : Prop) :
    (P → Q) → ((▷^k ◇ ⌜P⌝ : iProp Σ)%I ⊢ ▷^k ◇ ⌜Q⌝).
  Proof. intros HPQ. apply bi.laterN_mono, bi.except_0_mono, bi.pure_mono, HPQ. Qed.

  (** Push [∀] through [|={∅}▷=>^n] of plain pure props (via [fupd_finally]). *)
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

  (** ** Compatibility shims for the old [|={l; E|}=> ▷^k ◇ P] (hfupd)
       interface, expressed in terms of the new [fupd_finally] modality
       [|={E|}=> ▷^k ◇ P].  These keep the call sites below close to their
       pre-MR-1217 form. *)

  Notation hfupd_mono := fupd_finally_mono (only parsing).

  Lemma hfupd_intro {E} (P : iProp Σ) `{!Plain P} :
    P -∗ |={E|}=> P.
  Proof.
    iIntros "HP".
    iAssert (■ P)%I with "[HP]" as "#HP'"; [by iApply plain_plainly|].
    by iApply fupd_finally_intro.
  Qed.

  Lemma hfupd_intro_pure {E n} (φ : Prop) :
    φ → ⊢ |={E|}=> ▷^n ◇ ⌜φ⌝ : iProp Σ.
  Proof.
    intros Hφ. iApply fupd_finally_intro. by iPureIntro.
  Qed.

  Lemma laterN_hfupd l {E} k (P : iProp Σ) :
    ▷^l (|={E|}=> ▷^k ◇ P) ⊢ |={E|}=> ▷^(l + k) ◇ P.
  Proof.
    induction l as [|l IH]; simpl.
    - iIntros "H". by iApply (fupd_finally_mono with "H").
    - iIntros "H". rewrite IH. rewrite fupd_finally_later.
      iApply (fupd_finally_mono with "H"). iIntros "H".
      by rewrite except_0_laterN except_0_idemp.
  Qed.

  Lemma elim_fupd_hfupd_plain (k l : nat) (E1 E2 : coPset) (P Q : iProp Σ) :
    l ≤ k →
    (|={E1, E2}=> P) ∗ (∀ l', ⌜l' = l⌝ -∗ P -∗ |={E2|}=> ▷^(k - l') ◇ Q)
    ⊢ |={E1|}=> ▷^k ◇ Q.
  Proof.
    iIntros (Hlk) "[H1 H2]". iMod "H1" as "HP".
    iSpecialize ("H2" $! l with "[//] HP").
    iApply (fupd_finally_mono with "H2").
    replace k with (l + (k - l))%nat at 2 by lia.
    rewrite laterN_add. iIntros "H". by iApply laterN_intro.
  Qed.

  Lemma fupd_plain_hfupd' (l : nat) (E1 E2 : coPset) {P : iProp Σ} `{!Plain P} :
    (|={E1, E2}=> P) ⊢ |={E1|}=> ▷^l ◇ P.
  Proof.
    iIntros "H". iMod "H" as "HP". by iApply hfupd_intro.
  Qed.

  Lemma pgl_dbind' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (T : A' → Prop) ε' n :
    ⌜ 0 <= ε' ⌝ -∗
    (∀ a , |={∅|}=> ▷^(S n) ◇ ⌜pgl (f a) T ε'⌝) -∗
    |={∅|}=> ▷^(S n) ◇ ⌜pgl (dbind f μ) T (ε')⌝ : iProp Σ.
  Proof.
    iIntros (?) "H".
    iPoseProof (step_fupdN_pure_forall_intro _ (S n) ∅ with "H") as "H".
    iApply (fupd_finally_mono with "H").
    apply (laterN_except_0_pure_mono (S n)). intros Hall.
    rewrite <-Rplus_0_l. eapply pgl_dbind; [lra|lra|intros; by apply Hall|].
    by apply pgl_trivial.
  Qed.

  Lemma pgl_dbind_adv' `{Countable A, Countable A'}
    (f : A → distr A') (μ : distr A) (T : A' → Prop) ε' n :
    ⌜ exists r, forall a, 0 <= ε' a <= r ⌝ -∗
    (∀ a , |={∅|}=> ▷^(S n) ◇ ⌜pgl (f a) T (ε' a)⌝) -∗
    |={∅|}=> ▷^(S n) ◇ ⌜pgl (dbind f μ) T ( Expval μ ε')⌝ : iProp Σ.
  Proof.
    iIntros (?) "H".
    iPoseProof (step_fupdN_pure_forall_intro _ (S n) ∅ with "H") as "H".
    iApply (fupd_finally_mono with "H").
    apply (laterN_except_0_pure_mono (S n)). intros Hall.
    rewrite <-Rplus_0_l. eapply pgl_dbind_adv; try done.
    by apply pgl_trivial.
  Qed.

  Lemma wp_adequacy_val_fupd `{Countable sch_int_state}  (ζ : sch_int_state) e es (sch: scheduler (con_lang_mdp Λ) sch_int_state) n v σ ε φ k m:
    to_val e = Some v →
    state_interp m σ ∗ err_interp ε ∗
    WP e {{ v, ⌜φ v ⌝ }} ⊢
    |={⊤|}=> ▷^(S k) ◇ ⌜pgl (sch_exec sch n (ζ, (of_val v :: es, σ))) φ ε⌝.
  Proof.
    iIntros (Hval) "(?&?&Hwp)".
    rewrite pgl_wp_unfold/pgl_wp_pre.
    iMod ("Hwp" with "[$]") as "H".
    simpl. rewrite Hval.
    iRevert (σ ε) "H".
    iApply state_step_coupl_ind.
    iModIntro.
    iIntros (??) "[%|[>(_&_&%)|[H|(%μ&%&%Herasable&%&%Hineq&H)]]]".
    - iApply (hfupd_intro_pure (n:=S k)). by apply pgl_1.
    - iApply (hfupd_intro_pure (n:=S k)).
      erewrite sch_exec_is_final; last (rewrite /= /con_lang_mdp_to_final /= to_of_val //).
      eapply pgl_mon_grading; last apply pgl_dret; auto.
    - iApply (fupd_finally_mono _ (▷^(S k) ◇ ⌜∀ ε' : R, ε' > ε → pgl (sch_exec sch n (ζ, (of_val v :: es, σ))) φ ε'⌝)%I).
      { apply (laterN_except_0_pure_mono (S k)). intros H'.
        apply pgl_epsilon_limit; last exact H'.
        by apply Rle_ge. }
      iApply (step_fupdN_pure_forall_intro _ (S k)). iIntros (ε').
      destruct (ExcludedMiddle (ε' > ε)%R) as [Hgt|Hngt]; last first.
      { iApply (hfupd_intro_pure (n:=S k)). by intros. }
      unshelve iDestruct ("H" $! (mknonnegreal ε' _) with "[]") as "[H _]".
      { pose proof cond_nonneg ε. simpl in *. lra. }
      { iPureIntro. exact Hgt. }
      iApply (fupd_finally_mono with "H").
      apply (laterN_except_0_pure_mono (S k)). by intros.
    - apply sch_erasable_sch_erasable_val in Herasable.
      erewrite <-Herasable; last done.
      iPoseProof (pgl_dbind_adv' (λ σ', sch_exec sch n (ζ, (of_val v :: es, σ'))) μ φ
                    (λ σ', nonneg (ε2 σ')) k with "[] [H]") as "H'".
      { iPureIntro. naive_solver. }
      { iIntros (a). iMod ("H" $! a) as "[H _]". iExact "H". }
      iApply (fupd_finally_mono with "H'").
      apply (laterN_except_0_pure_mono (S k)). intros H'.
      eapply pgl_mon_grading; first apply Hineq. exact H'.
  Qed.

  Lemma state_step_coupl_erasure `{Countable sch_int_state} (ζ : sch_int_state) es σ ε Z n k (sch: scheduler (con_lang_mdp Λ) sch_int_state) φ:
    state_step_coupl σ ε Z -∗
    (∀ σ2 ε2, Z σ2 ε2 -∗ |={∅|}=> ▷^(S k) ◇
                               ⌜pgl (sch_exec sch n (ζ, (es, σ2))) φ ε2⌝) -∗
    |={∅|}=> ▷^(S k) ◇ ⌜pgl (sch_exec sch n (ζ, (es, σ))) φ ε⌝.
  Proof.
    iRevert (σ ε).
    iApply state_step_coupl_ind.
    iIntros "!>" (σ ε) "[%|[?|[H|(%μ&%&%Herasable&%&%Hineq&H)]]] Hcont".
    - iApply (hfupd_intro_pure (n:=S k)). by apply pgl_1.
    - by iApply ("Hcont" with "[$]").
    - iApply (fupd_finally_mono _ (▷^(S k) ◇ ⌜∀ ε' : R, ε' > ε → (pgl (sch_exec sch n (ζ, (es, σ))) φ) ε'⌝)%I).
      { apply (laterN_except_0_pure_mono (S k)). intros H'.
        apply pgl_epsilon_limit; last exact H'.
        simpl; by apply Rle_ge. }
      iApply (step_fupdN_pure_forall_intro _ (S k)). iIntros (ε').
      destruct (ExcludedMiddle (ε' > ε)%R) as [Hgt|Hngt]; last first.
      { iApply (hfupd_intro_pure (n:=S k)). by intros. }
      unshelve iDestruct ("H" $! (mknonnegreal ε' _) with "[]") as "[H _]".
      { pose proof cond_nonneg ε. simpl in *. lra. }
      { iPureIntro. exact Hgt. }
      iPoseProof ("H" with "Hcont") as "H".
      iApply (fupd_finally_mono with "H").
      apply (laterN_except_0_pure_mono (S k)). by intros.
    - apply sch_erasable_sch_erasable_val in Herasable.
      rewrite -Herasable; last done.
      iPoseProof (pgl_dbind_adv' (λ σ', sch_exec sch n (ζ, (es, σ'))) μ φ
                    (λ σ', nonneg (ε2 σ')) k with "[] [H Hcont]") as "H'".
      { iPureIntro. naive_solver. }
      { iIntros (a). iMod ("H" $! a) as "[H _]". iApply ("H" with "Hcont"). }
      iApply (fupd_finally_mono with "H'").
      apply (laterN_except_0_pure_mono (S k)). intros H'.
      eapply pgl_mon_grading; first (simpl; apply Hineq). exact H'.
  Qed.

  Lemma state_step_coupl_erasure' `{Countable sch_int_state} (ζ : sch_int_state) (e : expr Λ) (es : list (expr Λ)) (e' : expr Λ) (σ : state Λ) ε Z n k num (sch: scheduler (con_lang_mdp Λ) sch_int_state) φ:
    ((e::es)!!num = Some e') ->
    to_val e = None ->
    to_val e' = None ->
    state_step_coupl σ ε Z -∗
    (∀ σ2 ε2, Z σ2 ε2 -∗ |={∅|}=> ▷^(S k)
                               ◇ ⌜pgl (prim_step e' σ2 ≫= λ '(e3, σ3, efs), sch_exec sch n (ζ, (<[num:=e3]> (e :: es) ++ efs, σ3))) φ ε2⌝) -∗
    |={∅|}=> ▷^(S k)
             ◇ ⌜pgl (prim_step e' σ ≫= λ '(e3, σ3, efs), sch_exec sch n (ζ, (<[num:=e3]> (e :: es) ++ efs, σ3))) φ ε⌝.
  Proof.
    intros ???.
    iRevert (σ ε).
    iApply state_step_coupl_ind.
    iIntros "!>" (σ ε) "[%|[?|[H|(%μ&%&%Herasable&%&%Hineq&H)]]] Hcont".
    - iApply (hfupd_intro_pure (n:=S k)). by apply pgl_1.
    - by iApply ("Hcont" with "[$]").
    - iApply (fupd_finally_mono _ (▷^(S k) ◇ ⌜∀ ε' : R, ε' > ε → (pgl (prim_step e' σ ≫= λ '(e3, σ3, efs), sch_exec sch n (ζ, (<[num:=e3]> (e :: es) ++ efs, σ3))) φ) ε'⌝)%I).
      { apply (laterN_except_0_pure_mono (S k)). intros H'.
        apply pgl_epsilon_limit; last exact H'.
        simpl; by apply Rle_ge. }
      iApply (step_fupdN_pure_forall_intro _ (S k)). iIntros (ε').
      destruct (ExcludedMiddle (ε' > ε)%R) as [Hgt|Hngt]; last first.
      { iApply (hfupd_intro_pure (n:=S k)). by intros. }
      unshelve iDestruct ("H" $! (mknonnegreal ε' _) with "[]") as "[H _]".
      { pose proof cond_nonneg ε. simpl in *. lra. }
      { iPureIntro. exact Hgt. }
      iPoseProof ("H" with "Hcont") as "H".
      iApply (fupd_finally_mono with "H").
      apply (laterN_except_0_pure_mono (S k)). by intros.
    - unshelve erewrite (Rcoupl_eq_elim _ _ (prim_coupl_step_prim_sch_erasable _ _ _ _ _ _ _ μ _ _ _ _ _)); [done..|].
      iPoseProof (pgl_dbind_adv'
                    (λ σ', prim_step e' σ' ≫= λ '(e3, σ3, efs), sch_exec sch n (ζ, (<[num:=e3]> (e :: es) ++ efs, σ3)))
                    μ φ (λ σ', nonneg (ε2 σ')) k with "[] [H Hcont]") as "H'".
      { iPureIntro. naive_solver. }
      { iIntros (a). iMod ("H" $! a) as "[H _]". iApply ("H" with "Hcont"). }
      iApply (fupd_finally_mono with "H'").
      apply (laterN_except_0_pure_mono (S k)). intros H'.
      eapply pgl_mon_grading; first (simpl; apply Hineq). exact H'.
  Qed.

  (** Credit / later budget for [n] scheduler steps from step counter [k]. *)
  Fixpoint total_step_credits (k n : nat) : nat :=
    match n with
    | 0%nat => 0%nat
    | S n' => S (num_laters_per_step k) + total_step_credits (S k) n'
    end.

  Lemma total_step_credits_S k n :
    total_step_credits k (S n) =
    (S (num_laters_per_step k) + total_step_credits (S k) n)%nat.
  Proof. reflexivity. Qed.

  Lemma total_step_credits_S_laters k n :
    S (total_step_credits k (S n)) =
    (S (num_laters_per_step k) + S (total_step_credits (S k) n))%nat.
  Proof. simpl. lia. Qed.

  (** The laters of a step's [|={∅}▷=>^m] chain land in the outer buffer. *)
  Lemma step_fupdN_hfupd m j (P Q : iProp Σ) :
    (|={∅}▷=>^m P) -∗ (P -∗ |={∅|}=> ▷^j ◇ Q) -∗ |={∅|}=> ▷^(m + j) ◇ Q.
  Proof.
    iInduction m as [|m] "IH"; iIntros "HP Hw"; simpl.
    - by iApply "Hw".
    - iMod "HP". iApply (laterN_hfupd 1 (m + j)). iNext. iMod "HP".
      iApply ("IH" with "HP Hw").
  Qed.

  Lemma wp_refRcoupl_hfupd `{Countable sch_int_state} (ζ : sch_int_state) (ε : nonnegreal)
    (e : expr Λ) (es : list (expr Λ)) (σ : state Λ) k n φ
    (sch: scheduler (con_lang_mdp Λ) sch_int_state) :
    £ (total_step_credits k n) ∗ state_interp k σ ∗ err_interp ε ∗
      WP e {{ v, ⌜φ v⌝ }} ∗ ([∗ list] e'∈ es, WP e' {{ fork_post }}) ⊢
    |={⊤|}=> ▷^(S (total_step_credits k n)) ◇ ⌜pgl (sch_exec sch n (ζ, (e::es, σ))) φ ε⌝.
  Proof.
    iInduction n as [|n] "IH" forall (k ζ ε e es σ); iIntros "(Hlc & Hσ & Hε & Hwp & Hwps)".
    - Local Transparent sch_exec.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        iApply (wp_adequacy_val_fupd _ _ _ _ _ _ _ _ _ 0); last iFrame.
        by rewrite to_of_val.
      + rewrite /sch_exec /=.
        iApply (hfupd_intro_pure (n:=1)). rewrite Heq.
        apply pgl_dzero, Rle_ge, cond_nonneg.
    - rewrite total_step_credits_S lc_split. iDestruct "Hlc" as "[Hlc1 Hlc]".
      replace (S (num_laters_per_step k) + total_step_credits (S k) n)%nat
        with (num_laters_per_step k + S (total_step_credits (S k) n))%nat by lia.
      rewrite sch_exec_Sn /sch_step_or_final/=.
      destruct (to_val e) eqn:Heq.
      + apply of_to_val in Heq as <-.
        rewrite dret_id_left'/=.
        iApply (wp_adequacy_val_fupd _ _ _ _ _ _ _ _ _
                  (num_laters_per_step k + S (total_step_credits (S k) n))); last iFrame.
        by rewrite to_of_val.
      + rewrite {1}/sch_step. rewrite <-dbind_assoc.
        iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
        iApply (pgl_dbind' _ _ _ _ (num_laters_per_step k + S (total_step_credits (S k) n))); first done.
        iIntros ([sch_σ sch_a]).
        simpl. rewrite Heq.
        destruct ((e::es)!!sch_a) as [chosen_e|] eqn:Hlookup; rewrite Hlookup; last first.
        { (* a thread that is out of bounds: stutter *)
          rewrite dmap_dret dret_id_left'.
          iMod (state_interp_mono with "Hσ") as "Hσ".
          iMod "Hclose" as "_".
          iApply (laterN_hfupd (S (num_laters_per_step k))). iApply laterN_intro.
          iApply ("IH" with "[-]"). iFrame.
        }
        case_match eqn:Hcheckval.
        { (* a thread that is a value: stutter *)
          rewrite dmap_dret dret_id_left'.
          iMod (state_interp_mono with "Hσ") as "Hσ".
          iMod "Hclose" as "_".
          iApply (laterN_hfupd (S (num_laters_per_step k))). iApply laterN_intro.
          iApply ("IH" with "[-]"). iFrame.
        }
        rewrite dmap_comp/dmap-dbind_assoc.
        erewrite (distr_ext _ _); last first.
        { intros x. erewrite (dbind_ext_right _ _ (λ '(_,_,_), _)); last first.
          - intros [[??]?].
            by rewrite dret_id_left/=.
          - done.
        }
        destruct sch_a as [|sch_a].
        *  (* step main thread *)
          iMod "Hclose" as "_".
          rewrite pgl_wp_unfold /pgl_wp_pre. iSimpl in "Hwp". rewrite Heq.
          iMod ("Hwp" with "[$]") as "Hlift".
          iApply (state_step_coupl_erasure' _ _ _ _ _ _ _ _
                    (num_laters_per_step k + S (total_step_credits (S k) n)) with "[$Hlift]"); [done..|].
          iIntros (σ2 ε2) "(%&%&%&%Hineq&H)".
          iApply (fupd_finally_mono _ (▷^(S (num_laters_per_step k + S (total_step_credits (S k) n))) ◇ ⌜pgl (A:=mdpstate_ret (con_lang_mdp Λ)) _ φ _⌝)%I).
          { apply (laterN_except_0_pure_mono (S _)). intros H'.
            eapply pgl_mon_grading; first (simpl; apply Hineq). exact H'. }
          replace (chosen_e) with e; last by (simpl in Hlookup; simplify_eq).
          iApply (pgl_dbind_adv' _ _ _ _ (num_laters_per_step k + S (total_step_credits (S k) n)) with "[][-]"); first (iPureIntro; naive_solver).
          iIntros ([[??]?]).
          iMod ("H" $! _ _ _ ) as "H".
          iSpecialize ("H" with "Hlc1").
          iApply (step_fupdN_hfupd (S (num_laters_per_step k)) (S (total_step_credits (S k) n)) with "H").
          iIntros "H".
          iApply (state_step_coupl_erasure _ _ _ _ _ n (total_step_credits (S k) n) with "H").
          iIntros (??) "H". iMod "H" as "(?&?&?&?)".
          iApply ("IH" with "[-]"). iFrame.
        * (* step other threads *)
          iMod "Hclose" as "_".
          simpl in Hlookup.
          apply list_elem_of_split_length in Hlookup as (l1 & l2 & -> & ->).
          iDestruct "Hwps" as "[Hl1 [Hwp' Hl2]]".
          rewrite (pgl_wp_unfold _ _ chosen_e)/pgl_wp_pre.
          iSimpl in "Hwp'".
          rewrite Hcheckval.
          iMod ("Hwp'" with "[$]") as "Hlift".
          iApply (state_step_coupl_erasure' _ e _ chosen_e _ _ _ _
                    (num_laters_per_step k + S (total_step_credits (S k) n)) with "[$]"); [|done..|].
          { simpl.
            rewrite lookup_app_r//.
            by replace (_-_)%nat with 0%nat by lia.
          }
          iIntros (σ2 ε2) "(%&%&%&%Hineq&H)".
          iApply (fupd_finally_mono _ (▷^(S (num_laters_per_step k + S (total_step_credits (S k) n))) ◇ ⌜pgl (A:=mdpstate_ret (con_lang_mdp Λ)) _ φ _⌝)%I).
          { apply (laterN_except_0_pure_mono (S _)). intros H'.
            eapply pgl_mon_grading; first (simpl; apply Hineq). exact H'. }
          iApply (pgl_dbind_adv' _ _ _ _ (num_laters_per_step k + S (total_step_credits (S k) n)) with "[][-]"); first (iPureIntro; naive_solver).
          iIntros ([[??]?]).
          iMod ("H" $! _ _ _ ) as "H".
          iSpecialize ("H" with "Hlc1").
          iApply (step_fupdN_hfupd (S (num_laters_per_step k)) (S (total_step_credits (S k) n)) with "H").
          iIntros "H".
          iApply (state_step_coupl_erasure _ _ _ _ _ n (total_step_credits (S k) n) with "H").
          iIntros (??) "H". iMod "H" as "(?&?&?&?)".
          iApply ("IH" with "[-]"). iFrame.
          rewrite insert_app_r_alt//.
          replace (_-_)%nat with 0%nat by lia.
          simpl.
          iFrame.
  Qed.

End adequacy.

(** safety *)
Definition sch_mass_1 {Λ : conLanguage} `{Countable sch_int_state} (sch: scheduler (con_lang_mdp Λ) sch_int_state) :=
  ∀ sch_cfg, SeriesC (sch sch_cfg)=1.

Section safety.
  Context `{!alerusWpGS Λ Σ}.
  
  Lemma safety_dbind_adv `{Countable A, Countable A'}(h : A → distr A')
    (μ : distr A) ε (ε2 : A → R) R :
    SeriesC μ = 1  ->
    (exists r, forall a, 0 <= ε2(a) <= r) →
    pgl μ R ε ->
    (∀ a, R a -> SeriesC (h a) >= 1 - ε2 a) →
    SeriesC (μ ≫= h) >= 1 - (ε + Expval μ ε2).
  Proof.
    intros H' H1 Hpgl H2.
    rewrite dbind_mass/Expval.
    rewrite /pgl in Hpgl.
    setoid_rewrite <-SeriesC_scal_l.
    rewrite -H'.
    trans (SeriesC μ - ( prob μ (λ a : A, Datatypes.negb (bool_decide (R a))) + SeriesC (λ a : A, μ a * ε2 a))); last lra.
    replace (SeriesC μ) with (prob μ (λ a, bool_decide (R a))+prob μ (λ a, Datatypes.negb (bool_decide (R a)))); last first.
    { rewrite /prob. rewrite -SeriesC_plus.
      - apply SeriesC_ext. intros. case_bool_decide; simpl; lra.
      - apply ex_seriesC_filter_bool_pos; auto.
      - apply ex_seriesC_filter_bool_pos; auto.
    }
    rewrite Rminus_plus_r_l.
    rewrite /prob.
    rewrite Rminus_def.
    replace (-_) with (-1 * SeriesC (λ a, μ a * ε2 a)) by lra.
    rewrite -SeriesC_scal_l -SeriesC_plus; [|by apply ex_seriesC_filter_bool_pos|by apply ex_seriesC_scal_l, pmf_ex_seriesC_mult_fn].
    apply Rle_ge.
    rewrite Rcomplements.Rminus_le_0.
    rewrite Rminus_def.
    replace (-_) with (-1 * SeriesC (λ x : A, (if bool_decide (R x) then μ x else 0) + -1 * (μ x * ε2 x))) by lra.
    rewrite -SeriesC_scal_l -SeriesC_plus; last first.
    { apply ex_seriesC_scal_l, ex_seriesC_plus; first by apply ex_seriesC_filter_bool_pos.
      apply ex_seriesC_scal_l. by apply pmf_ex_seriesC_mult_fn.
    }
    { setoid_rewrite SeriesC_scal_l. apply pmf_ex_seriesC_mult_fn. naive_solver. }
    apply SeriesC_ge_0'.
    intros a.
    rewrite SeriesC_scal_l.
    case_bool_decide.
    - trans (μ a * (1 - ε2 a) - μ a + μ a * ε2 a); first lra.
      assert (μ a * (1 - ε2 a)<= μ a * SeriesC (h a)); last lra.
      apply Rmult_le_compat_l; first done.
      apply Rge_le.
      naive_solver.
    - apply Rplus_le_le_0_compat; first real_solver.
      assert (0<=μ a) by done.
      assert (0<=ε2 a) by naive_solver.
      rewrite Rmult_plus_distr_l -Rmult_assoc.
      replace (-1*-1) with 1 by lra.
      rewrite Rmult_0_r Rplus_0_l Rmult_1_l.
      real_solver.
  Qed.

  Lemma safety_dbind_adv' `{Countable A, Countable A'}(h : A → distr A')
    (μ : distr A) ε (ε2 : A → R) k R:
    ⌜SeriesC μ = 1 ⌝ -∗
    ⌜exists r, forall a, 0 <= ε2(a) <= r⌝ -∗
               ⌜pgl μ R ε⌝ -∗
               (∀ a, ⌜R a ⌝ -∗ |={∅|}=> ▷^(S k) ◇ ⌜SeriesC (h a) >= 1 - ε2 a⌝) -∗
               |={∅|}=> ▷^(S k) ◇ ⌜SeriesC (μ ≫= h) >= 1 - (ε + Expval μ ε2)⌝ : iProp Σ.
  Proof.
    iIntros (???) "H".
    iApply (fupd_finally_mono _ (▷^(S k) ◇ ⌜∀ a, R a -> SeriesC (h a) >= 1 - ε2 a⌝)%I).
    { apply (laterN_except_0_pure_mono (S k)). intros. by eapply safety_dbind_adv. }
    iApply (step_fupdN_pure_forall_intro _ (S k)). iIntros (a).
    destruct (ExcludedMiddle (R a)) as [HR|HnR]; last first.
    { iApply (hfupd_intro_pure (n:=S k)). by intros. }
    iSpecialize ("H" $! a with "[//]").
    iApply (fupd_finally_mono with "H").
    apply (laterN_except_0_pure_mono (S k)). by intros.
  Qed.

  Lemma safety_dbind' `{Countable A, Countable A'}(h : A → distr A')
    (μ : distr A) (ε : R) k:
    ⌜0 <= ε⌝ -∗
    ⌜SeriesC μ = 1 ⌝ -∗
    (∀ a, |={∅|}=> ▷^(S k) ◇ ⌜SeriesC (h a) >= 1 - ε⌝) -∗
    |={∅|}=> ▷^(S k) ◇ ⌜SeriesC (μ ≫= h) >= 1 - ε⌝ : iProp Σ.
  Proof.
    iIntros (? Hmass) "H".
    pose (ε' (a:A):= ε).
    assert (ε=0+Expval μ ε') as K.
    { rewrite /ε'. rewrite Expval_const; last done. rewrite Hmass. simpl. lra. }
    rewrite {2}K.
    epose proof (safety_dbind_adv' h _ 0 ε' k) as hh.
    iPoseProof (hh with "[][][][H]") as "K".
    - done.
    - iPureIntro. exists ε. intros. naive_solver.
    - iPureIntro. by apply pgl_trivial.
    - iIntros. rewrite /ε'. iApply "H".
    - rewrite /ε'.
      rewrite Expval_const; last done.
      by rewrite Hmass Rmult_1_r.
  Qed.

  Lemma sch_erasable_mass `{Countable sch_int_state} (ζ : sch_int_state) (sch: scheduler (con_lang_mdp Λ) sch_int_state) (μ : distr (state Λ)) σ:
    sch_erasable (λ _ _ _ _, True) μ σ ->
    SeriesC μ = 1.
  Proof.
    intros H0.
    pose proof (H0 _ _ _ sch [] ζ 0%nat I) as H1.
    apply (f_equal (λ d : distr _, SeriesC d)) in H1. simpl in H1.
    rewrite !dmap_mass sch_pexec_O dret_mass in H1. done.
  Qed.

  
  Lemma state_step_coupl_erasure_safety `{Countable sch_int_state} (ζ : sch_int_state) es σ ε Z n k (sch: scheduler (con_lang_mdp Λ) sch_int_state):
    state_step_coupl σ ε Z -∗
    (∀ σ2 ε2, Z σ2 ε2 -∗ |={∅|}=> ▷^(S k)
                               ◇ ⌜SeriesC (sch_pexec sch n (ζ, (es, σ2))) >= 1 - ε2⌝) -∗
    |={∅|}=> ▷^(S k)
             ◇ ⌜SeriesC (sch_pexec sch n (ζ, (es, σ))) >= 1- nonneg ε⌝.
  Proof.
    iRevert (σ ε).
    iApply state_step_coupl_ind.
    iIntros "!>" (σ ε) "[%|[?|[H|(%μ&%&%Herasable&%&%&H)]]] Hcont".
    - iApply (hfupd_intro_pure (n:=S k)).
      trans 0; try lra.
      by apply Rle_ge.
    - by iApply ("Hcont" with "[$]").
    - iApply (fupd_finally_mono _ (▷^(S k) ◇ ⌜∀ ε', ε<ε'-> SeriesC (sch_pexec sch n (ζ, (es, σ))) >= 1 - ε'⌝)%I).
      { apply (laterN_except_0_pure_mono (S k)).
        intros H1.
        apply Rle_ge.
        apply Rle_plus_epsilon.
        intros eps Heps.
        assert (SeriesC (sch_pexec sch n (ζ, (es, σ))) >= 1 - (ε+eps)) as H2.
        - apply H1. lra.
        - apply Rge_le in H2. rewrite Rminus_plus_distr in H2.
          by rewrite Rcomplements.Rle_minus_l in H2.
      }
      iApply (step_fupdN_pure_forall_intro _ (S k)). iIntros (ε').
      destruct (ExcludedMiddle (ε < ε')%R) as [Hgt|Hngt]; last first.
      { iApply (hfupd_intro_pure (n:=S k)). by intros. }
      unshelve iDestruct ("H" $! (mknonnegreal ε' _) with "[]") as "[H _]".
      { pose proof cond_nonneg ε. simpl in *. lra. }
      { iPureIntro. exact Hgt. }
      iPoseProof ("H" with "Hcont") as "H".
      iApply (fupd_finally_mono with "H").
      apply (laterN_except_0_pure_mono (S k)). by intros.
    - replace (SeriesC _) with (SeriesC (μ ≫= λ σ', sch_pexec sch n (ζ, (es, σ')))); last first.
      { rewrite /sch_erasable in Herasable.
        pose proof (Herasable _ _ _ sch es ζ n I) as H4.
        assert (SeriesC (dmap
         (λ x, x.2.1)
         (μ ≫= λ σ', sch_pexec sch n (ζ, (es, σ')))) =
       SeriesC (dmap
         (λ x, x.2.1)
         (sch_pexec sch n (ζ, (es, σ))))) as H5.
        - f_equal. by rewrite H4.
        - by rewrite !dmap_mass in H5.
      }
      iApply (fupd_finally_mono _ (▷^(S k) ◇ ⌜SeriesC (μ ≫= λ σ', sch_pexec sch n (ζ, (es, σ'))) >= 1 - (0 + Expval μ ε2)⌝)%I).
      { apply (laterN_except_0_pure_mono (S k)). intros. etrans; first exact.
        apply Rle_ge.
        apply Ropp_le_cancel.
        rewrite !Ropp_minus_distr. rewrite Rplus_0_l. by apply Rplus_le_compat_r. 
      }
      iApply (safety_dbind_adv' _ _ _ _ k); [| |iPureIntro; by apply pgl_trivial|].
      { iPureIntro. by eapply (sch_erasable_mass ζ sch). }
      { iPureIntro. naive_solver. }
      iIntros (a HR).
      iMod ("H" $! a) as "[H _]".
      iApply ("H" with "Hcont").
  Qed. 

  Lemma state_step_coupl_erasure_safety' `{Countable sch_int_state} (ζ : sch_int_state) (e : expr Λ) (es : list (expr Λ)) (e' : expr Λ) (σ : state Λ) ε Z n k num (sch: scheduler (con_lang_mdp Λ) sch_int_state):
    ((e::es)!!num = Some e') ->
    to_val e = None ->
    to_val e' = None ->
    state_step_coupl σ ε Z -∗
    (∀ σ2 ε2, Z σ2 ε2 -∗ |={∅|}=> ▷^(S k)
                               ◇ ⌜SeriesC (prim_step e' σ2 ≫= λ '(e3, σ3, efs), sch_pexec sch n (ζ, (<[num:=e3]> (e :: es) ++ efs, σ3))) >=1- ε2⌝) -∗
    |={∅|}=> ▷^(S k)
             ◇ ⌜SeriesC (prim_step e' σ ≫= λ '(e3, σ3, efs), sch_pexec sch n (ζ, (<[num:=e3]> (e :: es) ++ efs, σ3))) >= 1- nonneg ε⌝.
  Proof.
    intros ???.
    iRevert (σ ε).
    iApply state_step_coupl_ind.
    iIntros "!>" (σ ε) "[%|[?|[H|(%μ&%&%Herasable&%&%&H)]]] Hcont".
    - iApply (hfupd_intro_pure (n:=S k)).
      trans 0; try lra.
      by apply Rle_ge.
    - by iApply ("Hcont" with "[$]").
    - iApply (fupd_finally_mono _
                (▷^(S k) ◇ ⌜∀ ε', ε<ε'-> SeriesC (prim_step e' σ ≫= λ '(e3, σ3, efs), sch_pexec sch n (ζ, (<[num:=e3]> (e :: es) ++ efs, σ3))) >= 1 - ε'⌝)%I).
      { apply (laterN_except_0_pure_mono (S k)).
        intros K1.
        apply Rle_ge.
        apply Rle_plus_epsilon.
        intros eps Heps.
        assert (SeriesC (prim_step e' σ ≫= λ '(e3, σ3, efs), sch_pexec sch n (ζ, (<[num:=e3]> (e :: es) ++ efs, σ3))) >= 1 - (ε+eps)) as K2.
        - apply K1. lra.
        - apply Rge_le in K2. rewrite Rminus_plus_distr in K2.
          by rewrite Rcomplements.Rle_minus_l in K2.
      }
      iApply (step_fupdN_pure_forall_intro _ (S k)). iIntros (ε').
      destruct (ExcludedMiddle (ε < ε')%R) as [Hgt|Hngt]; last first.
      { iApply (hfupd_intro_pure (n:=S k)). by intros. }
      unshelve iDestruct ("H" $! (mknonnegreal ε' _) with "[]") as "[H _]".
      { pose proof cond_nonneg ε. simpl in *. lra. }
      { iPureIntro. exact Hgt. }
      iPoseProof ("H" with "Hcont") as "H".
      iApply (fupd_finally_mono with "H").
      apply (laterN_except_0_pure_mono (S k)). by intros.
    - replace (SeriesC _) with (SeriesC (μ ≫= (λ σ', prim_step e' σ' ≫= λ '(e3, σ3, efs), sch_pexec sch n (ζ, (<[num:=e3]> (e :: es) ++ efs, σ3))))); last first.
      { (* rewrite /sch_erasable in Herasable. *)
        (* pose proof (Herasable _ _ _ sch es ζ n I) as H4. *)
        assert (SeriesC (dmap
                           (λ x, x.2.1)
                           (μ
     ≫= λ σ', prim_step e' σ'
          ≫= λ '(e3, σ3, efs), sch_pexec sch n (ζ, (<[num:=e3]> (e :: es) ++ efs, σ3)))) =
                SeriesC (dmap
                           (λ x, x.2.1)
                           (prim_step e' σ ≫= λ '(e3, σ3, efs), sch_pexec sch n (ζ, (<[num:=e3]> (e :: es) ++ efs, σ3))))) as K.
        - unshelve epose proof prim_coupl_step_prim_pexec_sch_erasable e n es σ ζ e' num μ sch _ _ _ _ as K'; try done.
          apply Rcoupl_eq_elim in K'. by rewrite K'.
        - by rewrite !dmap_mass in K.
      }
      iApply (fupd_finally_mono _ (▷^(S k) ◇ ⌜SeriesC (μ ≫= (λ σ', prim_step e' σ' ≫= λ '(e3, σ3, efs), sch_pexec sch n (ζ, (<[num:=e3]> (e :: es) ++ efs, σ3)))) >= 1 - (0 + Expval μ ε2)⌝)%I).
      { apply (laterN_except_0_pure_mono (S k)). intros. etrans; first exact.
        apply Rle_ge.
        apply Ropp_le_cancel.
        rewrite !Ropp_minus_distr. rewrite Rplus_0_l. by apply Rplus_le_compat_r.
      }
      iApply (safety_dbind_adv' _ _ _ _ k); [| |iPureIntro; by apply pgl_trivial|].
      { iPureIntro. by eapply (sch_erasable_mass ζ sch). }
      { iPureIntro. naive_solver. }
      iIntros (a HR).
      iMod ("H" $! a) as "[H _]".
      iApply ("H" with "Hcont").
  Qed.
  
  Lemma wp_safety_hfupd `{Countable sch_int_state} (ζ : sch_int_state) (ε : nonnegreal)
    (e : expr Λ) (es : list (expr Λ)) (σ : state Λ) k n φ
    (sch: scheduler (con_lang_mdp Λ) sch_int_state) :
    sch_mass_1 sch ->
    £ (total_step_credits k n) ∗ state_interp k σ ∗ err_interp ε ∗
      WP e {{ v, ⌜φ v⌝ }} ∗ ([∗ list] e'∈ es, WP e' {{ fork_post }}) ⊢
    |={⊤|}=> ▷^(S (total_step_credits k n)) ◇ ⌜SeriesC (sch_pexec sch n (ζ, (e::es, σ))) >= 1 - ε⌝.
  Proof.
    intros Hmass.
    iInduction n as [|n] "IH" forall (k ζ ε e es σ); iIntros "(Hlc & Hσ & Hε & Hwp & Hwps)".
    - iApply (hfupd_intro_pure (n:=1)).
      rewrite sch_pexec_O dret_mass.
      pose proof cond_nonneg ε. simpl. lra.
    - rewrite total_step_credits_S lc_split. iDestruct "Hlc" as "[Hlc1 Hlc]".
      replace (S (num_laters_per_step k) + total_step_credits (S k) n)%nat
        with (num_laters_per_step k + S (total_step_credits (S k) n))%nat by lia.
      rewrite sch_pexec_Sn /sch_step_or_final/=.
      case_match eqn:Hval.
      { erewrite SeriesC_ext; last (intros; by rewrite dret_id_left').
        iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
        iMod (state_interp_mono with "Hσ") as "Hσ".
          iMod "Hclose" as "_".
          iApply (laterN_hfupd (S (num_laters_per_step k))). iApply laterN_intro.
          iApply ("IH" with "[-]"). iFrame.
      }
      rewrite /sch_step. rewrite <-dbind_assoc.
      iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
      iApply (safety_dbind' _ _ _ (num_laters_per_step k + S (total_step_credits (S k) n))); [done..|].
      iIntros ([ζ' thid]).
      simpl. rewrite Hval.
      destruct ((e::es)!!thid) as [chosen_e|] eqn:Hlookup; rewrite Hlookup; last first.
      { erewrite SeriesC_ext; last first.
        - intros.
          by rewrite dmap_dret dret_id_left'.
        - iMod (state_interp_mono with "Hσ") as "Hσ".
          iMod "Hclose" as "_".
          iApply (laterN_hfupd (S (num_laters_per_step k))). iApply laterN_intro.
          iApply ("IH" with "[-]"). iFrame. }
      case_match eqn:Hcheckval.
      { erewrite SeriesC_ext; last first.
        - intros.
          by rewrite dmap_dret dret_id_left'.
        - iMod (state_interp_mono with "Hσ") as "Hσ".
          iMod "Hclose" as "_".
          iApply (laterN_hfupd (S (num_laters_per_step k))). iApply laterN_intro.
          iApply ("IH" with "[-]"). iFrame. }
      rewrite dmap_comp/dmap-dbind_assoc.
      erewrite (distr_ext _ _); last first.
      { intros x. erewrite (dbind_ext_right _ _ (λ '(_,_,_), _)); last first.
        - intros [[??]?].
          by rewrite dret_id_left/=.
        - done. }
      destruct thid as [|thid].
      + iMod "Hclose" as "_". rewrite pgl_wp_unfold/pgl_wp_pre.
        iMod ("Hwp" with "[$]") as "Hwp".
        iApply (state_step_coupl_erasure_safety' _ _ _ _ _ _ _ _ (num_laters_per_step k + S (total_step_credits (S k) n)) with "[$Hwp]"); try done.
        iIntros (σ2 ε2). simpl. rewrite Hval.
        rewrite /prog_coupl.
        iIntros "( %εb & %Hred &%Hbound & %Hineq &  Hlift)".
        assert (e = chosen_e) as ?; last simplify_eq.
        { simpl in Hlookup. by simplify_eq. }
        iApply (fupd_finally_mono _ (▷^(S (num_laters_per_step k + S (total_step_credits (S k) n))) ◇ ⌜SeriesC
           (prim_step chosen_e σ2 ≫= λ '(e3, σ3, efs), sch_pexec sch n (ζ', (e3 :: es ++ efs, σ3))) >=
                                         1 - (0 + Expval (prim_step chosen_e σ2) εb)⌝)%I).
        { apply (laterN_except_0_pure_mono (S _)). simpl in *.
          intros. etrans; first exact.
          apply Rle_ge.
          apply Ropp_le_cancel.
          rewrite !Ropp_minus_distr. rewrite Rplus_0_l. by apply Rplus_le_compat_r.
        }
        iApply (safety_dbind_adv' _ _ _ _ (num_laters_per_step k + S (total_step_credits (S k) n)) with "[][][]").
        * iPureIntro. eapply mixin_prim_step_mass; [apply con_language_mixin|done].
        * iPureIntro. naive_solver.
        * iPureIntro; by apply pgl_trivial.
        * iIntros (((e' & σ') & efs) _).
          iMod ("Hlift"$! _ _ _) as "Hlift".
          iSpecialize ("Hlift" with "Hlc1").
          iApply (step_fupdN_hfupd (S (num_laters_per_step k)) (S (total_step_credits (S k) n)) with "Hlift").
          iIntros "H".
          iApply (state_step_coupl_erasure_safety _ _ _ _ _ n (total_step_credits (S k) n) with "H").
          iIntros (??) "H". iMod "H" as "(?&?&?&?)". iApply ("IH" with "[-]"). iFrame.
      + simpl in Hlookup.
        apply list_elem_of_split_length in Hlookup as (l1 & l2 & -> & ->).
        iDestruct "Hwps" as "[Hl1 [Hwp' Hl2]]".
        rewrite (pgl_wp_unfold _ _ chosen_e)/pgl_wp_pre.
        iSimpl in "Hwp'".
        rewrite Hcheckval.
        iMod "Hclose" as "_".
        iMod ("Hwp'" with "[$]") as "Hlift".
        iApply (state_step_coupl_erasure_safety' _ _ _ _ _ _ _ _ (num_laters_per_step k + S (total_step_credits (S k) n)) with "[$]"); try done.
        { simpl. by apply list_lookup_middle. }
        iIntros (σ2 ε2). simpl. rewrite /prog_coupl.
        iIntros "( %εb & %Hred &%Hbound & %Hineq &  Hlift)".
        iApply (fupd_finally_mono _ (▷^(S (num_laters_per_step k + S (total_step_credits (S k) n))) ◇ ⌜SeriesC
           (prim_step chosen_e σ2 ≫= λ '(e3, σ3, efs),
                 sch_pexec sch n (ζ', (e :: <[length l1:=e3]> (l1 ++ chosen_e :: l2) ++ efs, σ3))) >=
                                         1 - (0 + Expval (prim_step chosen_e σ2) εb)⌝)%I).
        { apply (laterN_except_0_pure_mono (S _)). simpl in *.
          intros. etrans; first exact.
          apply Rle_ge.
          apply Ropp_le_cancel.
          rewrite !Ropp_minus_distr.
          rewrite Rplus_0_l. by apply Rplus_le_compat_r. }
        iApply (safety_dbind_adv' _ _ _ _ (num_laters_per_step k + S (total_step_credits (S k) n)) with "[][][]").
        * iPureIntro. eapply mixin_prim_step_mass; [apply con_language_mixin|done].
        * iPureIntro. naive_solver.
        * iPureIntro. by apply pgl_trivial.
        * iIntros (((e' & σ') & efs) HR).
          iMod ("Hlift" $! _ _ _) as "Hlift".
          iSpecialize ("Hlift" with "Hlc1").
          iApply (step_fupdN_hfupd (S (num_laters_per_step k)) (S (total_step_credits (S k) n)) with "Hlift").
          iIntros "H".
          iApply (state_step_coupl_erasure_safety _ _ _ _ _ n (total_step_credits (S k) n) with "H").
          iIntros (??) "H". iMod "H" as "(?&?&?&?)". iApply ("IH" with "[-]"). iFrame.
          rewrite insert_app_r_alt//.
          replace (_-_)%nat with 0%nat by lia.
          simpl. iFrame.
  Qed.

End safety.
