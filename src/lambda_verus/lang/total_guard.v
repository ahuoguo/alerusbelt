(** Guarded heap access in a total logic, with no later credits.

    This is the Stage-1 milestone of [PLAN-TOTAL-ERIS.md]: VerusBelt's
    [Heap-Read-Guarded] holds over eris's *total* weakest precondition.

    Compare [lifting.v]'s partial [wp_read_guarded_cell], whose precondition
    is

      (G &&{↑NllftG; d}&&> l #↦ v) ∗ G ∗ £ d

    where the [£ d] pays for the [▷^d] that opening a Leaf guard over an
    Iris invariant produces.  Under [tgl_wp] no step mints a credit, and
    minting one would be unsound ([nola/bi/paradox.v]'s [twp_loop]).  With
    Nola's later-free guard over an explicit world satisfaction there is
    nothing to pay: the guard is opened against the [W] that
    [tgl_wpw] hands over at the step, and closed again before the step
    returns.

    The world-satisfaction adequacy at the bottom is Nola's [lrust_total]
    with eris's conclusion: a program that allocates a world satisfaction
    and runs under it terminates with probability at least [1 - ε]. *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth lib.mono_nat numbers dfrac_agree.
From clutch.base_logic Require Export error_credits.
From clutch.eris Require Export total_weakestpre.
From clutch.eris Require Import total_lifting total_ectx_lifting.
From clutch.prob Require Import distribution couplings.
From clutch.prelude Require Import stdpp_ext.
From nola.bi Require Import modw guard.
From guarding.internal Require Import na_invariants_fork.
From lrust.util Require Import non_atomic_cell_map atomic_lock_counter.
From lrust.lang Require Export lang heap lifting time total_wsat total_lifting
                               error_rules total_error_rules
                               adequacy total_adequacy.
Set Default Proof Using "Type".
Import uPred.
Import ModwNotation GuardNotation TglWpwNotation.

Open Scope Z_scope.

(** [lrustGS] with the world satisfaction factored out of [state_interp].
    [ErisW emp] is the canonical instance of [lifting.v] up to [emp ∗ -]. *)
Global Program Instance lrustGS_erisWpGS' `{!lrustGS Σ} :
  erisWpGS' lrust_prob_lang Σ := {
  eris'_invGS := lrustGS_invGS;
  state_interp' n σ := (heap.heap_ctx σ ∗ time_interp n)%I;
  err_interp' ε := ec_supply ε;
  num_laters_per_step' n := sum_advance_credits (n + 1);
}.
Next Obligation.
  iIntros (Σ ? n σ) "[$ Ht]". by iMod (time_interp_step with "Ht") as "$".
Qed.

Section total_guard.
  Context `{!lrustGS Σ}.

  (** Read a location shared through a guard.  No [£], no [▷], no mask
      side condition on the guard: the world satisfaction is handed over
      by the step and handed back before it returns. *)
  Lemma twp_read_guard W E (G : iProp Σ) l v s Φ :
    ↑non_atomic_cell_map.naN ⊆ E →
    (G &&{W}&&> heap.heap_mapsto l v) -∗ G -∗ (G -∗ Φ v) -∗
    WP[W] Read (Lit (LitLoc l)) @ s; E [{ Φ }].
  Proof.
    iIntros (HE) "#Hg HG HΦ".
    iApply (twp_lift_atomic_head_step (erisWpGS0 := ErisW W)); [done|].
    iIntros (ns σ1) "[HW [Hσ Ht]]".
    iDestruct (guard_acc with "Hg HG HW") as "[Hl Hback]".
    iDestruct "Hσ" as (hF) "(Hh & Hf & %REL & ato)".
    iMod (non_atomic_cell_map.points_to_heap_reading0 with "Hl Hh")
      as "(Hl & Hh & %Hσl)"; [done|].
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. rewrite /head_reducible /= Hσl /=.
      eexists (_, _). rewrite dret_pmf_unfold bool_decide_eq_true_2 //. lra. }
    iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= Hσl in Hstep.
    apply dret_pos in Hstep as [= -> ->].
    iDestruct ("Hback" with "Hl") as "[HW HG]".
    iMod (time_interp_step with "Ht") as "Ht".
    iModIntro. iFrame "HW Ht". iSplitL "Hh Hf ato".
    { iExists hF. by iFrame. }
    rewrite /= to_of_val /=. by iApply "HΦ".
  Qed.

  (** There is deliberately no guarded *write*.  A bare guard cannot
      support one: its closer must restore exactly the proposition it
      opened, and after a write the location no longer holds [v].  This is
      what VerusBelt's points-to cell logic is for - the guard sits on the
      immutable location-to-cell link and the value is owned - and it is
      the next piece of work ([PLAN-TOTAL-ERIS.md] Stage 1). *)

End total_guard.

(** ** Heap rules over a world satisfaction

    [total_lifting.v]'s rules are pinned to the canonical [erisWpGS]
    instance, which is [ErisW emp] only up to [emp ∗ -], not definitionally.
    These are the same three proofs at [ErisW W], threading [W] through the
    step. *)
Section total_lifting_w.
  Context `{!lrustGS Σ} (W : iProp Σ).

  Lemma twpw_alloc E (n : Z) s Φ :
    (0 < n)%Z →
    (∀ (l : loc) (sz : nat), ⌜n = sz⌝ -∗ heap.heap_freeable l 1 sz -∗
       heap.heap_mapsto_vec l (repeat (LitV LitPoison) sz) -∗
       Φ (LitV (LitLoc l))) -∗
    WP[W] Alloc (Lit (LitInt n)) @ s; E [{ Φ }].
  Proof.
    iIntros (Hn) "HΦ".
    iApply (twp_lift_atomic_head_step (erisWpGS0 := ErisW W)); [done|].
    iIntros (ns σ1) "[HW [Hσ Ht]]".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. rewrite /head_reducible /=.
      rewrite bool_decide_eq_true_2 //.
      eexists (_, _). rewrite dret_pmf_unfold bool_decide_eq_true_2 //. lra. }
    iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= in Hstep.
    rewrite bool_decide_eq_true_2 in Hstep; last done.
    apply dret_pos in Hstep as [= -> ->].
    iMod (heap.heap_alloc with "Hσ") as "(Hσ & Hf & Hl)"; [exact Hn| |].
    { intros m.
      assert (fresh_loc σ1 +ₗ m = (fresh_block σ1, m)) as ->;
        [rewrite /fresh_loc /shift_loc /=; f_equal; lia|].
      apply is_fresh_block. }
    iMod (time_interp_step with "Ht") as "Ht".
    iModIntro. iFrame "HW Hσ Ht".
    iApply ("HΦ" $! _ (Z.to_nat n) with "[%] Hf Hl"). lia.
  Qed.

  Lemma twpw_read E l v s Φ :
    ↑non_atomic_cell_map.naN ⊆ E →
    heap.heap_mapsto l v -∗ (heap.heap_mapsto l v -∗ Φ v) -∗
    WP[W] Read (Lit (LitLoc l)) @ s; E [{ Φ }].
  Proof.
    iIntros (HE) "Hl HΦ".
    iApply (twp_lift_atomic_head_step (erisWpGS0 := ErisW W)); [done|].
    iIntros (ns σ1) "[HW [Hσ Ht]]".
    iDestruct "Hσ" as (hF) "(Hh & Hf & %REL & ato)".
    iMod (non_atomic_cell_map.points_to_heap_reading0 with "Hl Hh")
      as "(Hl & Hh & %Hσl)"; [done|].
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. rewrite /head_reducible /= Hσl /=.
      eexists (_, _). rewrite dret_pmf_unfold bool_decide_eq_true_2 //. lra. }
    iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= Hσl in Hstep.
    apply dret_pos in Hstep as [= -> ->].
    iMod (time_interp_step with "Ht") as "Ht".
    iModIntro. iFrame "HW Ht". iSplitL "Hh Hf ato"; [iExists hF; by iFrame|].
    rewrite /= to_of_val /=. by iApply "HΦ".
  Qed.

  Lemma twpw_write E l v e v' s Φ :
    IntoVal e v' → ↑non_atomic_cell_map.naN ⊆ E →
    heap.heap_mapsto l v -∗ (heap.heap_mapsto l v' -∗ Φ (LitV LitPoison)) -∗
    WP[W] Write (Lit (LitLoc l)) e @ s; E [{ Φ }].
  Proof.
    iIntros (<- HE) "Hl HΦ".
    iApply (twp_lift_atomic_head_step (erisWpGS0 := ErisW W)); [done|].
    iIntros (ns σ1) "[HW [Hσ Ht]]".
    iDestruct "Hσ" as (hF) "(Hh & Hf & %REL & ato)".
    iMod (non_atomic_cell_map.atomic_write _ _ _ v' with "Hl Hh")
      as "(%Hσl & Hl & Hh)"; [done|].
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. rewrite /head_reducible /=. rewrite to_of_val Hσl.
      eexists (_, _). rewrite dret_pmf_unfold bool_decide_eq_true_2 //. lra. }
    iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= to_of_val Hσl in Hstep.
    apply dret_pos in Hstep as [= -> ->].
    iMod (time_interp_step with "Ht") as "Ht".
    iModIntro. iFrame "HW Ht". iSplitL "Hh Hf ato".
    { iExists hF. iFrame.
      iPureIntro. eauto using heap.heap_freeable_rel_stable. }
    by iApply "HΦ".
  Qed.

End total_lifting_w.

(** ** The expectation-preserving [Rand] rule, over a world satisfaction

    [total_error_rules.v]'s [twp_rand_exp_nat] at [ErisW W]; the world
    satisfaction is threaded through the step untouched. *)
Section total_error_rules_w.
  Context `{!lrustGS Σ} (W : iProp Σ).
  Local Open Scope R.

  Lemma twpw_rand_exp_nat z (ε1 : R) (ε2 : nat -> R) E Φ :
    (0 < z)%Z →
    (∀ n, (0 <= ε2 n <= 1)%R) →
    (SeriesC (λ n : nat,
        if bool_decide (n < Z.to_nat z)%nat
        then (1 / Z.to_nat z) * ε2 n
        else 0)%R <= ε1)%R →
    ↯ ε1 -∗
    (∀ (n : nat), ⌜ (n < Z.to_nat z)%nat ⌝ ∗ ↯ (ε2 n) -∗
                  Φ (LitV (LitInt (Z.of_nat n)))) -∗
    WP[W] Rand (Lit (LitInt z)) @ E [{ Φ }].
  Proof.
    iIntros (Hz Hleq Hε1) "Herr HΦ".
    assert (forall n, 0 <= ε2 n)%R as Hleq1 by (intros; apply Hleq).
    assert (forall n, ε2 n <= 1)%R as Hleq2 by (intros; apply Hleq).
    iApply (twp_lift_step_fupd_glm (erisWpGS0 := ErisW W)); [done|].
    iIntros (ns σ1 ε_now) "[[HW [Hσ Ht]] Hε]".
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
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose2".
    iFrame "HW Hσ Ht Hε2".
    iMod "Hclose2".
    iApply (tgl_wp_value (erisWpGS0 := ErisW W) _ _ _
              (Lit (LitInt n)) (LitV (LitInt n))); [done|].
    replace (LitV (LitInt n)) with (LitV (LitInt (Z.of_nat (Z.to_nat n)))); last first.
    { f_equal. f_equal. by rewrite Z2Nat.id. }
    iApply "HΦ". iFrame. iPureIntro. lia.
  Qed.

End total_error_rules_w.

(** ** Termination adequacy under a world satisfaction

    Nola's [lrust_total], with eris's quantitative conclusion.  The caller
    allocates the world satisfaction after the ghost state exists, exactly
    as in [nola/verus_halt/lang/adequacy.v]. *)
Theorem lrust_twpw_mass_lim_exec `{!lrustErisGpreS Σ}
    (e : common.language.expr lrust_prob_lang)
    (σ : common.language.state lrust_prob_lang)
    (ε : R) (K : nat) :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  (0 <= ε)%R →
  (∀ `{!lrustGS Σ},
      ⊢ £ K -∗ ↯ ε -∗ |={⊤}=> ∃ W, W ∗ WP[W] e [{ _, True }]) →
  (1 - ε <= SeriesC (lim_exec (e, σ)))%R.
Proof.
  intros Hσ Hε Htwp. eapply tgl_termination_ineq.
  instantiate (1 := λ _, True).
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
  iMod (own_alloc (●MN 0)) as (γpers) "_"; [by apply mono_nat_auth_valid|].
  iMod (own_alloc (● 0%nat)) as (γcum) "_"; [by apply auth_auth_valid|].
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
  iMod (Htwp HlrustGS with "H£ Hf") as (W) "[HW Hwp]".
  change ε with (nonneg ε').
  iPoseProof (twp_step_fupd_tgl (Σ:=Σ) (erisWpGS0 := @ErisW _ Σ (@lrustGS_erisWpGS' Σ HlrustGS) W)
                1 e σ ε' (λ _, True)) as "H".
  iSpecialize ("H" with "[-]"); last iApply "H".
  iSplitR "Hs Hwp"; last first.
  { iFrame "Hs". iExact "Hwp". }
  rewrite /state_interp /=. iFrame "HW". iSplitR "A Hbool".
  - rewrite /heap.heap_ctx. iExists ∅. iFrame "Hvγ Hfγ".
    iSplit.
    { iPureIntro. rewrite /heap.heap_freeable_rel. intros blk qs Hbad.
      by rewrite lookup_empty in Hbad. }
    rewrite /heap.heap_ato_ctx. iFrame.
  - iLeft. iFrame. iPureIntro. lia.
Qed.
