(** The program logic over the later-free heap: VerusBelt's guarded heap
    rules in a total logic, with no later credits.

    The partial development ([lang/lifting.v]) sets

      num_laters_per_step n := sum_advance_credits (n + 1)

    so that the machine hands out a superlinearly growing budget of later
    credits at every step, and carries the whole time-receipt library of
    [lang/time.v] ([⧗ n], [⧖ n], [wp_cumulative_time_receipt*]) whose only
    job is to produce the credits that strip the laters a Leaf guard
    introduces when opened:

      wp_read_guarded_cell : {{{ (G &&{↑NllftG; d}&&> l #↦ v) ∗ G ∗ £ d }}} …

    Here the guard is Nola's, taken over the cell logic's world
    satisfaction [na_wsat], which the weakest precondition's own [W]
    contains ([WsatIncl W na_wsat Wr]).  There is nothing to strip:
    [num_laters_per_step' _ := 0], no time receipts, no [£].

    Statements follow [nola/verus_halt/lang/lifting.v]; the proofs are
    redone against eris's [twp_lift_atomic_head_step] and
    [lrust_prob_lang]'s [head_step_prob]. *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From clutch.base_logic Require Export error_credits.
From clutch.eris Require Export total_weakestpre.
From clutch.eris Require Import total_lifting total_ectx_lifting.
From clutch.prob Require Import distribution couplings.
From clutch.prelude Require Import stdpp_ext.
From nola.bi Require Import modw guard.
From nola.iris Require Import guard iprop.
From nola.verus_halt Require Import na_inv_fork.
From nola.verus_halt.util Require Import atomic_lock_counter.
From lrust.util Require Import total_cell_map.
From lrust.lang Require Export lang total_heap total_wsat.
From lrust.lang Require Import tactics.
Set Default Proof Using "Type".
Import uPred ModwNotation GuardNotation TglWpwNotation iPropAppNotation.

Open Scope Z_scope.

(** The ghost state of the later-free stack.  Against [lifting.v]'s
    [lrustGS] this gains the formula language [FML] with its two
    interpretations and loses [timeGS] entirely. *)
Class lrustTotGS (FML : oFunctor) (Σ : gFunctors) : Type := LRustTotGS {
  lrustTotGS_invGS : invGS_gen HasLc Σ;
  #[global] lrustTotGS_na_invGS :: na_invG Σ;
  #[global] lrustTotGS_alcGS :: alc_logicG Σ;
  #[global] lrustTotGS_heapGS :: total_heap.heapGS FML Σ;
  #[global] lrustTotGS_naSem :: NaSem FML Σ;
  #[global] lrustTotGS_heapSem :: total_heap.HeapSem FML Σ;
  #[global] lrustTotGS_ecGS :: ecGS Σ;
}.

Global Instance lrustTotGS_invGS_inst `{!lrustTotGS FML Σ} : invGS Σ
  := lrustTotGS_invGS.

(** No time receipts, so the step index is carried but unused and
    [state_interp'_mono] is trivial. *)
Global Program Instance lrustTotGS_erisWpGS' `{!lrustTotGS FML Σ} :
  erisWpGS' lrust_prob_lang Σ := {
  eris'_invGS := lrustTotGS_invGS;
  state_interp' _ σ := total_heap.heap_ctx σ;
  err_interp' ε := ec_supply ε;
  num_laters_per_step' _ := 0%nat;
}.
Next Obligation. iIntros (FML Σ ? n σ) "$". by iModIntro. Qed.

Global Opaque lrustTotGS_invGS.

Section lifting.
  Context `{!lrustTotGS FML Σ}.
  Implicit Types (W : iProp Σ) (Φ : val → iProp Σ).

  Local Lemma wsat_split {W W' Wr : iProp Σ} `{!WsatIncl W W' Wr} :
    W ⊢ W' ∗ Wr.
  Proof. by rewrite (wsat_incl W W' Wr). Qed.
  Local Lemma wsat_join {W W' Wr : iProp Σ} `{!WsatIncl W W' Wr} :
    W' -∗ Wr -∗ W.
  Proof. rewrite (wsat_incl W W' Wr). by iIntros "$$". Qed.

  (** ** Allocation and deallocation *)

  Lemma twp_alloc W s E (n : Z) Φ :
    0 < n →
    (∀ (l : loc) (sz : nat), ⌜n = sz⌝ -∗ total_heap.heap_freeable l 1 sz -∗
       total_heap.heap_mapsto_vec l (repeat (LitV LitPoison) sz) -∗
       Φ (LitV (LitLoc l))) -∗
    WP[W] Alloc (Lit (LitInt n)) @ s; E [{ Φ }].
  Proof.
    iIntros (Hn) "HΦ".
    iApply (twp_lift_atomic_head_step (erisWpGS0 := ErisW W)); [done|].
    iIntros (ns σ1) "[HW Hσ]".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. rewrite /head_reducible /=.
      rewrite bool_decide_eq_true_2 //.
      eexists (_, _). rewrite dret_pmf_unfold bool_decide_eq_true_2 //. lra. }
    iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= in Hstep.
    rewrite bool_decide_eq_true_2 in Hstep; last done.
    apply dret_pos in Hstep as [= -> ->].
    iMod (total_heap.heap_alloc with "Hσ") as "(Hσ & Hf & Hl)"; [exact Hn| |].
    { intros m.
      assert (fresh_loc σ1 +ₗ m = (fresh_block σ1, m)) as ->;
        [rewrite /fresh_loc /shift_loc /=; f_equal; lia|].
      apply is_fresh_block. }
    iModIntro. iFrame "HW Hσ".
    iApply ("HΦ" $! _ (Z.to_nat n) with "[%] Hf Hl"). lia.
  Qed.

  Lemma twp_free `{!WsatIncl W na_wsat Wr} s E (n : Z) l vl Φ :
    n = length vl →
    total_heap.heap_mapsto_vec l vl -∗
    total_heap.heap_freeable l 1 (length vl) -∗ Φ (LitV LitPoison) -∗
    WP[W] Free (Lit (LitInt n)) (Lit (LitLoc l)) @ s; E [{ Φ }].
  Proof.
    iIntros (Hn) "Hmt Hf HΦ".
    iApply (twp_lift_atomic_head_step (erisWpGS0 := ErisW W)); [done|].
    iIntros (ns σ1) "[HW Hσ]".
    iDestruct (wsat_split (W':=na_wsat) with "HW") as "[Wna Wr]".
    iMod (total_heap.heap_free _ _ _ n with "Hσ Hmt Hf Wna")
      as "(%Hpos & %Hbnd & Hσ & Wna)"; [done|].
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. rewrite /head_reducible /=. rewrite bool_decide_eq_true_2 //.
      eexists (_, _). rewrite dret_1_1 //. lra. }
    iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= in Hstep.
    rewrite bool_decide_eq_true_2 in Hstep; last done.
    apply dret_pos in Hstep as [= -> ->].
    iModIntro. iFrame "Hσ HΦ".
    iApply (wsat_join (W:=W) (W':=na_wsat) (Wr:=Wr) with "Wna Wr").
  Qed.

  (** ** Reads

      [twp_read_guarded_cells] is VerusBelt's [Heap-Read-Guarded].  Compare
      [lifting.v]'s [wp_read_guarded_cell], which additionally demands
      [£ d]. *)
  Lemma twp_read_guarded_cells `{!WsatIncl W na_wsat Wr} s E l c v
      (G : iProp Σ) Φ :
    (G &&{na_wsat}&&> total_heap.heap_mapsto_cells_fancy l c (total_heap.FVal v)) -∗ G -∗
    (G -∗ Φ v) -∗
    WP[W] Read (Lit (LitLoc l)) @ s; E [{ Φ }].
  Proof.
    iIntros "#Gv G HΦ".
    iApply (twp_lift_atomic_head_step (erisWpGS0 := ErisW W)); [done|].
    iIntros (ns σ1) "[HW Hσ]".
    iDestruct (wsat_split (W':=na_wsat) with "HW") as "[Wna Wr]".
    iDestruct "Hσ" as (hF) "(Hna & HhF & %REL & ato)".
    iDestruct (atomic_read with "Gv G Hna Wna") as (n0) "(%Heq & G & Hna & Wna)".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. rewrite /head_reducible /= Heq /=.
      eexists (_, _). rewrite dret_pmf_unfold bool_decide_eq_true_2 //. lra. }
    iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= Heq in Hstep.
    apply dret_pos in Hstep as [= -> ->].
    iModIntro. iSplitL "Wna Wr Hna HhF ato".
    { iSplitL "Wna Wr".
      { iApply (wsat_join (W:=W) (W':=na_wsat) (Wr:=Wr) with "Wna Wr"). }
      iExists hF. by iFrame. }
    rewrite /= to_of_val /=. by iApply "HΦ".
  Qed.

  Lemma twp_read `{!WsatIncl W na_wsat Wr} s E l v Φ :
    total_heap.heap_mapsto l v -∗
    (total_heap.heap_mapsto l v -∗ Φ v) -∗
    WP[W] Read (Lit (LitLoc l)) @ s; E [{ Φ }].
  Proof.
    iIntros "Hl HΦ".
    iApply (twp_read_guarded_cells s E l [] v
              (total_heap.heap_mapsto l v)%I with "[] Hl HΦ").
    iApply guard_refl.
  Qed.

  (** ** Writes

      Dual to the read.  [lifting.v]'s [wp_write_guarded] asks for
      [£ (3*d+1)]. *)
  Lemma twp_write_guarded `{!WsatIncl W na_wsat Wr} s E (l : total_heap.cloc1)
      e v v' (Gx : FML $oi Σ) Φ :
    IntoVal e v' →
    (na_sem Gx &&{na_wsat}&&> total_heap.heap_complete_mapsto l) -∗
    na_sem Gx -∗ total_heap.heap_complete_mapsto_fancy l (total_heap.FVal v) -∗
    (na_sem Gx -∗
       total_heap.heap_complete_mapsto_fancy l (total_heap.FVal v') -∗
       Φ (LitV LitPoison)) -∗
    WP[W] Write (Lit (LitLoc l.1)) e @ s; E [{ Φ }].
  Proof.
    iIntros (<-) "#Gv G Hl HΦ".
    iApply (twp_lift_atomic_head_step (erisWpGS0 := ErisW W)); [done|].
    iIntros (ns σ1) "[HW Hσ]".
    iDestruct (wsat_split (W':=na_wsat) with "HW") as "[Wna Wr]".
    iMod (total_heap.heap_write _ l v v' with "Hσ Gv G Hl Wna")
      as "(%Hσl & Hσ & G & Hl & Wna)".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. rewrite /head_reducible /=. rewrite to_of_val Hσl.
      eexists (_, _). rewrite dret_pmf_unfold bool_decide_eq_true_2 //. lra. }
    iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= to_of_val Hσl
      in Hstep.
    apply dret_pos in Hstep as [= -> ->].
    iModIntro. iSplitL "Wna Wr Hσ".
    { iSplitL "Wna Wr"; last iFrame "Hσ".
      iApply (wsat_join (W:=W) (W':=na_wsat) (Wr:=Wr) with "Wna Wr"). }
    by iApply ("HΦ" with "G Hl").
  Qed.

  (** ** Sampling

      [Rand] does not touch the heap, so the world satisfaction goes
      through untouched. *)
  Lemma twp_rand W s E (N : Z) Φ :
    (0 < N)%Z →
    (∀ (n : fin (S (Z.to_nat N - 1))),
       Φ (LitV (LitInt (Z.of_nat (fin_to_nat n))))) -∗
    WP[W] Rand (Lit (LitInt N)) @ s; E [{ Φ }].
  Proof.
    iIntros (HN) "HΦ".
    iApply (twp_lift_atomic_head_step (erisWpGS0 := ErisW W)); [done|].
    iIntros (ns σ1) "[HW Hσ]".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
    { iPureIntro. rewrite /head_reducible /=.
      rewrite bool_decide_eq_true_2 //.
      eexists (_, _). apply dmap_pos. exists 0%fin. split; first done.
      apply dunifP_pos. }
    iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= in Hstep.
    rewrite bool_decide_eq_true_2 in Hstep; last done.
    apply dmap_pos in Hstep as (n & [= -> ->] & _).
    iModIntro. iFrame "HW Hσ". by iApply "HΦ".
  Qed.

End lifting.

(** ** The expectation-preserving [Rand] rule

    [lang/error_rules.v]'s [wp_rand_exp_nat] over this stack.  The two
    language-level helpers are restated rather than imported: pulling in
    [lang/error_rules.v] would drag in the *partial* heap, whose notation
    clashes with [total_heap]'s. *)
Lemma head_reducible_rand z σ1 :
  (0 < z)%Z →
  head_reducible (Λ:=lrust_prob_ectx_lang) (Rand (Lit (LitInt z))) σ1.
Proof.
  intros Hz. rewrite /head_reducible /= bool_decide_eq_true_2 //.
  eexists (_, _). apply dmap_pos. exists 0%fin. split; first done.
  apply dunifP_pos.
Qed.

Lemma pgl_rand_trivial z σ1 :
  (0 < z)%Z →
  pgl
    (prim_step (Λ:=lrust_prob_ectx_lang) (Rand (Lit (LitInt z))) σ1)
    (λ ρ2, ∃ (n : fin (Z.to_nat z)),
        ρ2 = (Lit (LitInt (Z.of_nat (fin_to_nat n))), σ1)) 0.
Proof.
  intros Hz.
  pose proof (head_reducible_rand z σ1 Hz) as Hred.
  pose proof (head_prim_step_eq (Λ:=lrust_prob_ectx_lang) _ σ1 Hred) as Heq.
  rewrite Heq.
  rewrite /head_step /= bool_decide_eq_true_2 //.
  rewrite /dmap.
  rewrite -(Rplus_0_r 0).
  eapply (pgl_dbind _ _ _ _ _ 0); [done|done| |by apply pgl_trivial].
  intros n _. apply pgl_dret.
  pose proof (fin_to_nat_lt n) as Hn.
  assert (fin_to_nat n < Z.to_nat z)%nat as Hn' by lia.
  exists (nat_to_fin Hn'). f_equal. f_equal. f_equal.
  by rewrite fin_to_nat_to_fin.
Qed.

Section rand.
  Context `{!lrustTotGS FML Σ} (W : iProp Σ).
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
    iIntros (ns σ1 ε_now) "[[HW Hσ] Hε]".
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
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose2".
    iFrame "HW Hσ Hε2".
    iMod "Hclose2".
    iApply (tgl_wp_value' (erisWpGS0 := ErisW W) _ _ _ (LitV (LitInt n))).
    replace (LitV (LitInt n)) with (LitV (LitInt (Z.of_nat (Z.to_nat n)))); last first.
    { f_equal. f_equal. by rewrite Z2Nat.id. }
    iApply "HΦ". iFrame. iPureIntro. lia.
  Qed.

End rand.
