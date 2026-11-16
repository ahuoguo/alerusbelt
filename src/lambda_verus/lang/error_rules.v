(** Error-credit rules for concurrent probabilistic λRust.

    Counterparts of AlerusBelt's sequential [lang/error_rules.v] (which
    were proved against eris's [glm]); here they are proved against the
    [state_step_coupl] / [prog_coupl] modalities of [lrust.prob]:
    - [wp_err_incr] / [wp_err_pos] (Verus's [thin_air]) use the
      error-amplification disjunct of [state_step_coupl];
    - [wp_rand_exp_nat] (Verus's [rand_ubig]) is the expectation-preserving
      rule for [Rand], via [prog_coupl_adv_comp] on the support of the
      uniform step. *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Export error_credits.
From lrust.prob Require Import weakestpre lifting ectx_lifting.
From lrust.lang Require Export lifting.
From clutch.prob Require Import distribution.
Set Default Proof Using "Type".
Import uPred.

Local Open Scope R.

(** * The step distribution of [Rand] *)

Lemma head_reducible_rand z σ :
  (0 < z)%Z → head_reducible (Rand (Lit (LitInt z))) σ.
Proof.
  intros Hz. eapply head_reducible_of_step; [apply (RandS z 0); lia|solve_not_stuck].
Qed.

Lemma prim_step_rand z σ :
  (0 < z)%Z →
  prim_step (Rand (Lit (LitInt z))) σ =
  dmap (λ n : fin (S (Z.to_nat z - 1)),
          (Lit (LitInt (Z.of_nat (fin_to_nat n))), σ, ([] : list expr)))
       (dunifP (Z.to_nat z - 1)).
Proof.
  intros Hz.
  pose proof (head_prim_step_eq (Λ:=lrust_ectx_lang) (Rand (Lit (LitInt z))) σ
                (head_reducible_rand z σ Hz)) as Heq.
  etrans; [apply Heq|]. simpl. by rewrite bool_decide_eq_true_2.
Qed.

(** The expectation of [f] under the [Rand z] step, as a sum over the
    sampled naturals. *)
Lemma Expval_rand z σ (f : expr * state * list expr → R) :
  (0 < z)%Z → (∀ ρ, 0 <= f ρ) → (∃ r, ∀ ρ, f ρ <= r) →
  Expval (prim_step (Rand (Lit (LitInt z))) σ) f =
  SeriesC (λ n : nat, if bool_decide (n < Z.to_nat z)%nat
                      then (1 / Z.to_nat z) * f (Lit (LitInt (Z.of_nat n)), σ, [])
                      else 0).
Proof.
  intros Hz Hpos [r Hr].
  rewrite prim_step_rand //.
  rewrite Expval_dmap; [|done|].
  2: { eapply ex_expval_bounded. intros; split; [apply Hpos|apply Hr]. }
  rewrite /Expval.
  set (M := (Z.to_nat z - 1)%nat).
  assert (Z.to_nat z = S M) as HzM by (rewrite /M; lia).
  rewrite HzM.
  erewrite (SeriesC_ext (λ n : nat, if bool_decide (n < S M)%nat then _ else 0)
             (λ n : nat, if bool_decide (n ≤ M)%nat
                         then (1 / S M) * f (Lit (LitInt (Z.of_nat n)), σ, []) else 0)).
  2: { intros n. do 2 case_bool_decide; try done; lia. }
  rewrite SeriesC_nat_bounded_fin.
  apply SeriesC_ext. intros k. rewrite /dunifP dunif_pmf /= /Rdiv Rmult_1_l. done.
Qed.

(** The [Rand z] step only produces sampled literals. *)
Lemma pgl_rand_support z σ :
  (0 < z)%Z →
  pgl (prim_step (Rand (Lit (LitInt z))) σ)
      (λ ρ, ∃ k : fin (S (Z.to_nat z - 1)),
              ρ = (Lit (LitInt (Z.of_nat (fin_to_nat k))), σ, [])) 0.
Proof.
  intros Hz. rewrite prim_step_rand //.
  rewrite -(Rplus_0_r 0).
  eapply pgl_dbind; [lra|lra| |by apply pgl_trivial].
  intros k _. apply pgl_dret. by exists k.
Qed.

Section error_rules.
  Context `{!lrustGS Σ}.

  (** Error induction by increasing: [↯ ε] and the WP under any strictly
      larger budget give the WP. *)
  Lemma wp_err_incr e ε E Φ :
    to_val e = None →
    ↯ ε ∗ (∀ ε', ⌜(ε < ε')%R⌝ -∗ ↯ ε' -∗ WP e @ E {{ Φ }}) ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (?) "[Herr Hwp]".
    iApply state_step_coupl_pgl_wp.
    iIntros (n σ1 ε_now) "[Hσ Hε]".
    iDestruct (ec_supply_bound with "Hε Herr") as %Hle.
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iApply state_step_coupl_ampl. iIntros (ε') "%Hε'".
    destruct (decide (ε' < 1)%R) as [Hlt|Hge]; last first.
    { iApply state_step_coupl_ret_err_ge_1. lra. }
    iApply fupd_state_step_coupl.
    assert (0 <= ε' - ε_now)%R as Hd by lra.
    set (diff := mknonnegreal _ Hd).
    iMod (ec_supply_increase _ diff with "Hε") as "[Hε Hdiff]".
    { rewrite /diff /=. lra. }
    iDestruct (ec_combine with "[$Herr $Hdiff]") as "Herr".
    iModIntro. iApply state_step_coupl_ret.
    iMod "Hclose" as "_". iModIntro. iFrame "Hσ".
    iSplitL "Hε". { iApply (ec_supply_eq with "Hε"). rewrite /diff /=. lra. }
    iApply ("Hwp" with "[] Herr"). iPureIntro. rewrite /diff /=. lra.
  Qed.

  (** Thin-air error credits (Verus's [thin_air]). *)
  Lemma wp_err_pos e E Φ :
    to_val e = None →
    (∀ ε, ⌜(0 < ε)%R⌝ -∗ ↯ ε -∗ WP e @ E {{ Φ }}) ⊢ WP e @ E {{ Φ }}.
  Proof.
    iIntros (?) "H". iMod ec_zero as "Herr".
    iApply (wp_err_incr with "[$]"); auto.
  Qed.

  Lemma wp_err_pos_post e E Φ :
    to_val e = None →
    WP e @ E {{ Φ }} ⊢ WP e @ E {{ v, ∃ ε : R, ⌜(0 < ε)%R⌝ ∗ ↯ ε ∗ Φ v }}.
  Proof.
    iIntros (Hnv) "Hwp".
    iApply wp_err_pos; first done.
    iIntros (ε Hε) "Hcr".
    iApply (pgl_wp_wand with "Hwp").
    iIntros (v) "HΦ". iExists ε. by iFrame.
  Qed.

  (** Expectation-preserving sampling (Verus's [rand_ubig]). *)
  Lemma wp_rand_exp_nat z (ε1 : R) (ε2 : nat → R) E Φ :
    (0 < z)%Z →
    (∀ n, (0 <= ε2 n <= 1)%R) →
    (SeriesC (λ n : nat,
        if bool_decide (n < Z.to_nat z)%nat
        then (1 / Z.to_nat z) * ε2 n
        else 0)%R <= ε1)%R →
    ↯ ε1 -∗
    ▷ (∀ (n : nat), ⌜(n < Z.to_nat z)%nat⌝ ∗ ↯ (ε2 n) -∗
                    Φ (LitV (LitInt (Z.of_nat n)))) -∗
    WP Rand (Lit (LitInt z)) @ E {{ Φ }}.
  Proof.
    iIntros (Hz Hε2 Hsum) "Herr HΦ".
    rewrite pgl_wp_unfold /pgl_wp_pre /=.
    iIntros (n σ1 ε_now) "[[Hσ Ht] Hε]".
    iDestruct (ec_supply_ec_inv with "Hε Herr") as %(x1 & x3 & Hnow & Hx1).
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hclose".
    iApply state_step_coupl_ret.
    set (G := λ ρ : expr * state * list expr,
                match ρ with
                | (Lit (LitInt k), _, _) => ε2 (Z.to_nat k)
                | _ => 0
                end).
    assert (∀ ρ, 0 <= G ρ <= 1)%R as HG.
    { intros [[[] ?] ?]; simpl; try lra. case_match; try lra. apply Hε2. }
    set (F := λ ρ, (x3 + mknonnegreal (G ρ) (proj1 (HG ρ)))%NNR).
    iApply (prog_coupl_adv_comp _ _ _ ε_now).
    { iModIntro. iIntros (???) "_". iApply step_fupdN_intro; first done.
      iApply laterN_intro. by iApply state_step_coupl_ret_err_ge_1. }
    iExists (λ ρ, ∃ k : fin (S (Z.to_nat z - 1)),
                    ρ = (Lit (LitInt (Z.of_nat (fin_to_nat k))), σ1, [])),
            nnreal_zero, F.
    iSplit; [iPureIntro; apply head_prim_reducible, head_reducible_rand, Hz|].
    iSplit.
    { iPureIntro. exists (x3 + 1)%R. intros ρ. rewrite /F /=.
      pose proof (HG ρ). lra. }
    iSplit.
    { iPureIntro. simpl. rewrite Rplus_0_l.
      rewrite /F /=. rewrite Expval_plus.
      - rewrite Expval_const; [|apply cond_nonneg].
        rewrite prim_step_mass; last first.
        { apply (head_prim_reducible (Λ:=lrust_ectx_lang)), head_reducible_rand, Hz. }
        rewrite Rmult_1_r.
        rewrite (Expval_rand z σ1 G Hz); [| intros; apply HG | exists 1; intros; apply HG].
        apply (f_equal nonneg) in Hnow. simpl in Hnow.
        erewrite (SeriesC_ext _ (λ n0 : nat, if bool_decide (n0 < Z.to_nat z)%nat
                                     then 1 / Z.to_nat z * ε2 n0 else 0)).
        { lra. }
        intros k. case_bool_decide; [|done]. simpl. by rewrite Nat2Z.id.
      - eapply ex_expval_bounded. intros; split; [apply cond_nonneg|done].
      - eapply ex_expval_bounded. intros; apply HG. }
    iSplit.
    { iPureIntro. by apply pgl_rand_support. }
    iIntros (e2 σ2 efs [k Hk]). simplify_eq.
    iModIntro. iIntros "Hlc". simpl.
    iMod (ec_supply_decrease with "Hε Herr") as (x1' x3' Heq1 Heq2) "Hε".
    iModIntro. iNext.
    iMod (time_interp_step with "Ht") as "Ht". iModIntro.
    iApply step_fupdN_intro; first done. iApply laterN_intro.
    apply (f_equal nonneg) in Heq1. simpl in Heq1.
    rewrite /F /G /=.
    set (k' := Z.to_nat (Z.of_nat (fin_to_nat k))).
    assert (k' = fin_to_nat k) as Hk' by (rewrite /k'; lia).
    destruct (decide (x3 + ε2 k' < 1)%R) as [Hlt|Hge]; last first.
    { iApply state_step_coupl_ret_err_ge_1. simpl. lra. }
    iApply fupd_state_step_coupl.
    iMod (ec_supply_increase x3' (mknonnegreal (ε2 k') (proj1 (Hε2 k'))) with "Hε")
      as "[Hε Hcr]".
    { simpl. lra. }
    iModIntro. iApply state_step_coupl_ret.
    iMod "Hclose" as "_". iModIntro. iFrame "Hσ Ht".
    iSplitL "Hε". { iApply (ec_supply_eq with "Hε"). simpl. lra. }
    iSplit; [|done].
    iApply pgl_wp_value.
    iSpecialize ("HΦ" $! k' with "[Hcr]").
    { iFrame. iPureIntro. pose proof (fin_to_nat_lt k). lia. }
    rewrite /k' Z2Nat.id //; lia.
  Qed.
End error_rules.
