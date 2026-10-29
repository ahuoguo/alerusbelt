(** Error-credit rules for [lrust_prob_lang]'s total weakest precondition.

    These are the [twp] counterparts of [lang/error_rules.v].  Two things
    change and nothing else:

    - the [▷] in front of the continuation disappears from the statements,
      because [tgl_wp_pre] grants no later credits to strip it with;
    - the tail of each proof loses the [lc_succ] / [lc_fupd_elim_later] /
      [step_fupdN_intro] dance for the same reason, which makes it shorter.

    [twp_err_pos] is worth noting: thin-air error credits exist for the
    *total* WP too.  It is not credit availability that makes the partial
    logic partial. *)
Require Import guarding.internal.na_invariants_fork.
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.eris Require Import total_weakestpre total_lifting total_ectx_lifting.
From clutch.prob Require Import distribution couplings.
From clutch.prelude Require Import stdpp_ext.
From lrust.lang Require Export lifting error_rules total_lifting.
Set Default Proof Using "Type".

Local Open Scope R.

Section total_error_rules.
  Context `{!lrustGS Σ}.

  (** Error induction by increasing: the total counterpart of
      [wp_err_incr]. *)
  Lemma twp_err_incr e ε E Φ :
    to_val e = None ->
    ↯ ε ∗
      (∀ ε', ⌜ (ε < ε')%R ⌝ -∗ ↯ (ε') -∗ WP e @ E [{ Φ }] )
      ⊢ WP e @ E [{ Φ }].
  Proof.
    iIntros (?) "[Herr Hwp]".
    iApply twp_lift_step_fupd_glm; [done|].
    iIntros (ns σ1 ε2) "[Hσ1 Hε2]".
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose'".
    iApply glm_err_incr_step.
    iIntros (ε') "%Hε'".
    apply Rlt_le in Hε' as Hε''.
    pose (diff :=((ε' - ε2) Hε'')%NNR).
    destruct (decide (ε' < 1)%R); last first.
    { iApply exec_stutter_spend.
      iPureIntro. simpl in *. simpl. lra. }
    replace (ε') with (ε2 + diff)%NNR;
      last (apply nnreal_ext; rewrite /diff; simpl; lra).
    iMod (ec_supply_increase _ diff with "[$]") as "[??]".
    { rewrite /diff. simpl. simpl in *. lra. }
    iPoseProof (ec_combine with "[$]") as "Herr".
    iSpecialize ("Hwp" with "[] Herr").
    { iPureIntro. simpl in *. simpl. lra. }
    rewrite !tgl_wp_unfold /tgl_wp_pre /=.
    rewrite H.
    iMod ("Hclose'").
    iMod ("Hwp" with "[$]").
    by iApply exec_stutter_free.
  Qed.

  (** Thin-air error credits, for the total WP.  Exactly as in the partial
      case: any strictly positive amount may be conjured. *)
  Lemma twp_err_pos e E Φ :
    to_val e = None ->
    (∀ ε, ⌜ (0 < ε)%R ⌝ -∗ ↯ (ε) -∗ WP e @ E [{ Φ }] )
      ⊢ WP e @ E [{ Φ }].
  Proof.
    iIntros (?) "?".
    iMod (ec_zero) as "Herr".
    iApply (twp_err_incr with "[$]"); auto.
  Qed.

  (** Expectation-preserving [Rand]: the total counterpart of
      [wp_rand_exp_nat].  This is the rule [typing/rand_ubig.v] is built
      on, so it is what a total [type_rand_case] will need. *)
  Lemma twp_rand_exp_nat z (ε1 : R) (ε2 : nat -> R) E Φ :
    (0 < z)%Z →
    (∀ n, (0 <= ε2 n <= 1)%R) →
    (SeriesC (λ n : nat,
        if bool_decide (n < Z.to_nat z)%nat
        then (1 / Z.to_nat z) * ε2 n
        else 0)%R <= ε1)%R →
    ↯ ε1 -∗
    (∀ (n : nat), ⌜ (n < Z.to_nat z)%nat ⌝ ∗ ↯ (ε2 n) -∗
                  Φ (LitV (LitInt (Z.of_nat n)))) -∗
    WP Rand (Lit (LitInt z)) @ E [{ Φ }].
  Proof.
    iIntros (Hz Hleq Hε1) "Herr HΦ".
    assert (forall n, 0 <= ε2 n)%R as Hleq1 by (intros; apply Hleq).
    assert (forall n, ε2 n <= 1)%R as Hleq2 by (intros; apply Hleq).
    iApply twp_lift_step_fupd_glm; [done|].
    iIntros (ns σ1 ε_now) "[[Hσ Ht] Hε]".
    iApply fupd_mask_intro; [set_solver|].
    iIntros "Hclose'".
    iApply glm_adv_comp; simpl.
    iDestruct (ec_supply_ec_inv with "Hε Herr") as %(ε1' & ε3 & Hε_now & Hε1').
    set (ecfn := (λ (ρ : expr * state),
                  ε3 +
                    match ρ with
                    | (Lit (LitInt n), σ) =>
                        if bool_decide (σ = σ1)
                        then if bool_decide (0 ≤ n)%Z
                             then if bool_decide (Z.to_nat n < Z.to_nat z)%nat
                                  then mknonnegreal _ (Hleq1 (Z.to_nat n))
                                  else nnreal_zero
                             else nnreal_zero
                        else nnreal_zero
                    | _ => nnreal_zero
                    end)%NNR).
    iExists
      (λ (ρ : expr * state),
        ∃ (n : Z), (0 <= n)%Z /\ (Z.to_nat n < Z.to_nat z)%nat /\
                   ρ = (Lit (LitInt n), σ1)), nnreal_zero, ecfn.
    iSplit.
    { iPureIntro. eapply head_prim_reducible.
      by apply head_reducible_rand. }
    iSplit.
    { iPureIntro. exists (ε3 + 1)%R.
      intros (e & σ); simpl.
      apply Rplus_le_compat; [lra|].
      repeat (case_match; simpl; try lra).
      apply Hleq2. }
    iSplit.
    { iPureIntro.
      rewrite /ecfn /= Rplus_0_l.
      setoid_rewrite Rmult_plus_distr_l.
      rewrite SeriesC_plus.
      - rewrite Rplus_comm.
        subst.
        apply Rplus_le_compat.
        + etrans; eauto.
          etrans; last first.
          * apply (SeriesC_le_inj _
                     (λ ρ : expr * state,
                         let (e, σ) := ρ in
                         if bool_decide (σ = σ1) then
                           match e with
                           | Lit (LitInt n) =>
                               if bool_decide (0 ≤ n)%Z
                               then if bool_decide (Z.to_nat n < Z.to_nat z)%nat
                                    then Some (Z.to_nat n)
                                    else None
                               else None
                           | _ => None
                           end
                         else None)).
            ** intros. real_solver.
            ** intros ρ1 ρ2 m Hc1 Hc2.
               repeat (case_bool_decide || case_match); simplify_eq.
               f_equal. do 3 f_equal. apply Z2Nat.inj; auto.
            ** eapply ex_seriesC_ext;
                 last apply (ex_seriesC_nat_bounded
                              (λ n, 1 / Z.to_nat z * ε2 n) (Z.to_nat z - 1)).
               intros n. case_bool_decide as Hlt;
                 case_bool_decide as Hle; try done; lia.
          * apply SeriesC_le.
            ** intros [e σ]; split.
               *** apply Rmult_le_pos; auto.
               *** case_bool_decide; simplify_eq.
                   **** do 4 (case_match; simpl; (try (rewrite Rmult_0_r; lra))).
                        2: { rewrite Rmult_0_r.
                             rewrite (bool_decide_eq_true_2 (σ1 = σ1)); [|reflexivity].
                             cbn. lra. }
                        apply bool_decide_eq_true_1 in H1.
                        apply bool_decide_eq_true_1 in H2.
                        rewrite bool_decide_eq_true_2; last reflexivity.
                        simpl.
                        rewrite bool_decide_eq_true_2; last by lia.
                        apply Rmult_le_compat_r; [auto|].
                        rewrite (head_prim_step_eq (Λ:=lrust_prob_ectx_lang)
                                  _ _ (head_reducible_rand z _ Hz)).
                        rewrite /head_step /= bool_decide_eq_true_2 //.
                        rewrite /dmap /pmf /= /dbind_pmf /dunifP.
                        setoid_rewrite dunif_pmf.
                        replace (S (Z.to_nat z - 1)) with (Z.to_nat z) by lia.
                        rewrite SeriesC_scal_l /= /Rdiv Rmult_1_l.
                        rewrite <- Rmult_1_r.
                        apply Rmult_le_compat_l.
                        { left. apply Rinv_0_lt_compat. apply lt_0_INR. lia. }
                        rewrite /pmf /= /dret_pmf.
                        assert (Z.to_nat n < Z.to_nat z)%nat as Hbnd by lia.
                        erewrite <- (SeriesC_singleton (nat_to_fin Hbnd)).
                        apply SeriesC_le; [|apply ex_seriesC_singleton].
                        intro; split; [real_solver|].
                        case_bool_decide; try real_solver.
                        rewrite bool_decide_eq_true_2; [lra|].
                        simplify_eq. apply fin_to_nat_inj.
                        rewrite fin_to_nat_to_fin.
                        rewrite Nat2Z.id //.
                   **** rewrite (bool_decide_eq_false_2 (σ = σ1)); [|done].
                        cbn.
                        etrans; [|right; eapply Rmult_0_l].
                        apply Rmult_le_compat_r; [auto|]. right.
                        rewrite (head_prim_step_eq (Λ:=lrust_prob_ectx_lang)
                                  _ _ (head_reducible_rand z _ Hz)).
                        rewrite /head_step /= bool_decide_eq_true_2 //.
                        rewrite /dmap /pmf /= /dbind_pmf /dunifP.
                        setoid_rewrite dunif_pmf.
                        rewrite SeriesC_scal_l /= /Rdiv.
                        erewrite (SeriesC_ext _ (λ _, 0));
                          [rewrite SeriesC_0; auto; by rewrite Rmult_0_r|].
                        intro; rewrite dret_0; auto.
                        intro; simplify_eq.
            ** eapply ex_seriesC_finite_from_option.
               instantiate (1 := (λ k : nat, (Lit (LitInt (Z.of_nat k)), σ1)) <$> (seq 0%nat (Z.to_nat z))).
               intros [e σ].
               split.
               --- case_bool_decide; last first.
                   { inversion 1. done. }
                   case_match; try (by inversion 1).
                   case_match; try (by inversion 1).
                   case_bool_decide; try (by inversion 1).
                   case_bool_decide; try (by inversion 1).
                   intros _. subst.
                   eapply list_elem_of_fmap_2'; last first.
                   { repeat f_equal. instantiate (1 := Z.to_nat n). lia. }
                   rewrite elem_of_seq. lia.
               --- intros Hin. apply list_elem_of_fmap_1 in Hin.
                   destruct Hin as [k [Heq Hk]].
                   inversion Heq.
                   replace (bool_decide (_=_)) with true.
                   2: { case_bool_decide; done. }
                   replace (bool_decide _) with true.
                   2: { case_bool_decide; lia. }
                   case_match; first done.
                   apply bool_decide_eq_false_1 in H.
                   rewrite elem_of_seq in Hk.
                   exfalso.
                   apply H.
                   lia.
        + rewrite SeriesC_scal_r.
          rewrite <- Rmult_1_l.
          apply Rmult_le_compat; auto; try lra; apply cond_nonneg.
      - by apply ex_seriesC_scal_r.
      - eapply ex_seriesC_ext; last eapply ex_seriesC_list.
        intros [e σ].
        instantiate (2 := (λ k : nat, (Lit (LitInt (Z.of_nat k)), σ1)) <$> (seq 0%nat (Z.to_nat z))).
        case_bool_decide; last first.
        + repeat (case_match; try (simpl; lra)).
          exfalso. apply H. subst.
          eapply list_elem_of_fmap_2'; last first.
          { apply bool_decide_eq_true_1 in H2, H3. repeat f_equal.
            - instantiate (1 := Z.to_nat n). lia.
            - done.
          }
          rewrite elem_of_seq.
          apply bool_decide_eq_true_1 in H4.
          lia.
        + instantiate (1 :=
                         (λ '(e, s), (prim_step (Λ:=lrust_prob_ectx_lang) (Rand (Lit (LitInt z))) σ1 (e, s) *
                                        match e with
                                        | Lit (LitInt n) =>
                                            if bool_decide (s = σ1)
                                            then if bool_decide (0 ≤ n)%Z
                                                 then if bool_decide (Z.to_nat n < Z.to_nat z)%nat
                                                      then ε2 (Z.to_nat n)
                                                      else nnreal_zero
                                                 else nnreal_zero
                                            else nnreal_zero
                                        | _ => nnreal_zero
                                        end)%R)).
          simpl. repeat f_equal.
          repeat (case_match; try (simpl; lra)). }
    iSplit.
    { iPureIntro.
      eapply pgl_mon_pred; last first.
      - apply (pgl_rand_trivial z σ1 Hz).
      - intros (e2, σ2) [n Heq].
        pose proof (fin_to_nat_lt n) as Hnlt.
        exists (Z.of_nat (fin_to_nat n)).
        split; [lia|].
        split; [rewrite Nat2Z.id; done|].
        done. }
    iIntros (e2 σ2) "%H".
    destruct H as (n & Hn1 & Hn2 & Hn3); simplify_eq.
    rewrite /ecfn.
    rewrite bool_decide_eq_true_2; last done.
    rewrite bool_decide_eq_true_2; last first.
    { lia. }
    rewrite bool_decide_eq_true_2; last done.
    iMod (ec_supply_decrease with "Hε Herr") as (????) "Hε2".
    iModIntro.
    destruct (Rlt_decision (nonneg ε3 + (ε2 (Z.to_nat n)))%R 1%R) as [Hdec|Hdec]; last first.
    { apply Rnot_lt_ge, Rge_le in Hdec.
      iApply exec_stutter_spend.
      iPureIntro. simpl. lra. }
    iApply exec_stutter_free.
    iMod (ec_supply_increase ε3 (mknonnegreal _ (Hleq1 (Z.to_nat n))) with "[Hε2]")
      as "[Hε2 Hcr]".
    { simpl. lra. }
    { iApply ec_supply_eq; [|done]. simplify_eq. lra. }
    iMod "Hclose'".
    iMod (time_interp_step with "Ht") as "Ht".
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose2". iFrame "Hσ Ht Hε2".
    iMod "Hclose2".
    iApply (tgl_wp_value _ _ _ (Lit (LitInt n)) (LitV (LitInt n))); [done|].
    replace (LitV (LitInt n)) with (LitV (LitInt (Z.of_nat (Z.to_nat n)))); last first.
    { f_equal. f_equal. by rewrite Z2Nat.id. }
    iApply "HΦ". iFrame. iPureIntro. lia.
  Qed.

End total_error_rules.
