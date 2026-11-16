(** Base-step lifting lemmas for ectx-based languages, with Iris's names
    and shapes ([program_logic/ectx_lifting.v]); "base step" here is
    clutch's [head_step] (support of the head-step distribution). *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From clutch.common Require Export con_ectx_language.
From lrust.prob Require Export weakestpre lifting.
From iris.prelude Require Import options.

Local Open Scope R.

Section wp.
Context {Λ : conEctxLanguage} `{!alerusWpGS Λ Σ} {Hinh : Inhabited (state Λ)}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Local Hint Resolve head_prim_reducible head_reducible_prim_step : core.

Lemma wp_lift_base_step_fupd {s E Φ} e1 :
  to_val e1 = None →
  (∀ n σ1, state_interp n σ1 ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2 efs, ⌜head_step e1 σ1 (e2, σ2, efs) > 0⌝ -∗ £ 1 ={∅}=∗ ▷ |={∅,E}=>
      state_interp (S n) σ2 ∗
      WP e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupd=>//. iIntros (n σ1) "Hσ".
  iMod ("H" with "Hσ") as "[% H]"; iModIntro.
  iSplit; first by eauto. iIntros (e2 σ2 efs ?).
  iApply "H"; eauto.
Qed.

Lemma wp_lift_base_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ n σ1, state_interp n σ1 ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 (e2, σ2, efs) > 0⌝ -∗ £ 1 ={∅,E}=∗
      state_interp (S n) σ2 ∗
      WP e2 @ s; E {{ Φ }} ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_base_step_fupd; [done|]. iIntros (??) "?".
  iMod ("H" with "[$]") as "[$ H]". iIntros "!>" (e2 σ2 efs ?) "Hcred !> !>".
  by iApply ("H" with "[//] Hcred").
Qed.

Lemma wp_lift_atomic_base_step_fupd {s E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ n σ1, state_interp n σ1 ={E1}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2 efs, ⌜head_step e1 σ1 (e2, σ2, efs) > 0⌝ -∗ £ 1 ={E1}[E2]▷=∗
      state_interp (S n) σ2 ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E1 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
  iIntros (n σ1) "Hσ1". iMod ("H" with "Hσ1") as "[% H]"; iModIntro.
  iSplit; first by eauto. iIntros (e2 σ2 efs Hstep).
  iApply "H"; eauto.
Qed.

Lemma wp_lift_atomic_base_step {s E Φ} e1 :
  to_val e1 = None →
  (∀ n σ1, state_interp n σ1 ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 (e2, σ2, efs) > 0⌝ -∗ £ 1 ={E}=∗
      state_interp (S n) σ2 ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step; eauto.
  iIntros (n σ1) "Hσ1". iMod ("H" with "Hσ1") as "[% H]"; iModIntro.
  iSplit; first by eauto. iNext. iIntros (e2 σ2 efs Hstep).
  iApply "H"; eauto.
Qed.

Lemma wp_lift_atomic_base_step_no_fork_fupd {s E1 E2 Φ} e1 :
  to_val e1 = None →
  (∀ n σ1, state_interp n σ1 ={E1}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2 efs, ⌜head_step e1 σ1 (e2, σ2, efs) > 0⌝ -∗ £ 1 ={E1}[E2]▷=∗
      ⌜efs = []⌝ ∗ state_interp (S n) σ2 ∗ from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E1 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_base_step_fupd; [done|].
  iIntros (n σ1) "Hσ1". iMod ("H" $! n σ1 with "Hσ1") as "[$ H]"; iModIntro.
  iIntros (v2 σ2 efs Hstep) "Hcred".
  iMod ("H" $! v2 σ2 efs with "[# //] Hcred") as "H".
  iIntros "!> !>". iMod "H" as "(-> & ? & ?) /=". by iFrame.
Qed.

Lemma wp_lift_atomic_base_step_no_fork {s E Φ} e1 :
  to_val e1 = None →
  (∀ n σ1, state_interp n σ1 ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 (e2, σ2, efs) > 0⌝ -∗ £ 1 ={E}=∗
      ⌜efs = []⌝ ∗ state_interp (S n) σ2 ∗ from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_base_step; eauto.
  iIntros (n σ1) "Hσ1". iMod ("H" $! n σ1 with "Hσ1") as "[$ H]"; iModIntro.
  iNext; iIntros (v2 σ2 efs Hstep) "Hcred".
  iMod ("H" $! v2 σ2 efs with "[//] Hcred") as "(-> & ? & ?) /=". by iFrame.
Qed.

Lemma wp_lift_pure_det_base_step_no_fork {s E E' Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs',
    head_step e1 σ1 (e2', σ2, efs') > 0 → σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (|={E}[E']▷=> £ 1 -∗ WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -(wp_lift_pure_det_step_no_fork e1 e2); eauto.
Qed.

Lemma wp_lift_pure_det_base_step_no_fork' {s E Φ} e1 e2 :
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs',
    head_step e1 σ1 (e2', σ2, efs') > 0 → σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  ▷ (£ 1 -∗ WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -[(WP e1 @ s; _ {{ _ }})%I]wp_lift_pure_det_base_step_no_fork //.
  rewrite -step_fupd_intro //.
Qed.
End wp.
