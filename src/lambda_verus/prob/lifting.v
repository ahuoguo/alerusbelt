(** Lifting lemmas for [prob/weakestpre.v], shaped like Iris's
    [program_logic/lifting.v] (step counter, [£] per step) so that
    lambdaRust's lifting proofs port with minimal change.  Probabilistic
    steps are handled by quantifying over the support of [prim_step]. *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From iris.prelude Require Import options.
From clutch.prelude Require Import NNRbar.
From lrust.prob Require Export weakestpre.
Import uPred.

Section lifting.
  Context `{!alerusWpGS Λ Σ}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  #[local] Open Scope R.

  (** Discharges the [Z _ _ _ 1] obligation of [prog_coupl] lemmas. *)
  Local Lemma step_cont_err_1 n (Z : state Λ → nonnegreal → iProp Σ) σ :
    ⊢ £ (S (num_laters_per_step n)) -∗
      |={∅}▷=>^(S (num_laters_per_step n)) state_step_coupl σ nnreal_one Z.
  Proof.
    iIntros "_". iApply step_fupdN_intro; first done.
    iApply laterN_intro. by iApply state_step_coupl_ret_err_ge_1.
  Qed.

  Lemma wp_lift_step_fupdN E Φ e1 s :
    to_val e1 = None →
    (∀ n σ1, state_interp n σ1 ={E,∅}=∗
       ⌜reducible e1 σ1⌝ ∗
       ∀ e2 σ2 efs, ⌜prim_step e1 σ1 (e2, σ2, efs) > 0⌝ -∗
         £ (S (num_laters_per_step n)) ={∅}▷=∗^(S (num_laters_per_step n)) |={∅,E}=>
         state_interp (S n) σ2 ∗ WP e2 @ s; E {{ Φ }} ∗
         [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (H) "H". rewrite pgl_wp_unfold /pgl_wp_pre.
    iIntros (n σ1 ε) "[Hσ Hε]".
    iMod ("H" with "Hσ") as "[%Hs H]". iModIntro.
    iApply state_step_coupl_ret. rewrite H.
    iApply prog_coupl_prim_step.
    { iModIntro. iIntros (???). iApply step_cont_err_1. }
    iExists _, nnreal_zero, ε.
    iSplit; first done.
    iSplit; first (iPureIntro; simpl; lra).
    iSplit.
    { iPureIntro. eapply pgl_pos_R, pgl_trivial. simpl; lra. }
    iIntros (e2 σ2 efs (?&?)) "!> Hlc".
    iSpecialize ("H" with "[//] Hlc").
    iApply (step_fupdN_wand with "H"). iIntros "H".
    iApply state_step_coupl_ret.
    iMod "H" as "($&$&$)". by iFrame.
  Qed.

  Lemma wp_lift_step_fupd E Φ e1 s :
    to_val e1 = None →
    (∀ n σ1, state_interp n σ1 ={E,∅}=∗
       ⌜reducible e1 σ1⌝ ∗
       ∀ e2 σ2 efs, ⌜prim_step e1 σ1 (e2, σ2, efs) > 0⌝ -∗ £ 1 ={∅}=∗ ▷ |={∅,E}=>
         state_interp (S n) σ2 ∗ WP e2 @ s; E {{ Φ }} ∗
         [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "H". iApply wp_lift_step_fupdN; [done|].
    iIntros (n σ1) "Hσ". iMod ("H" with "Hσ") as "[$ H]".
    iIntros "!>" (e2 σ2 efs Hstep) "Hlc".
    iDestruct (lc_succ with "Hlc") as "[Hlc _]".
    simpl. iMod ("H" with "[//] Hlc") as "H". iIntros "!> !> !>".
    iApply step_fupdN_intro; first done. by iApply laterN_intro.
  Qed.

  Lemma wp_lift_step E Φ e1 s :
    to_val e1 = None →
    (∀ n σ1, state_interp n σ1 ={E,∅}=∗
       ⌜reducible e1 σ1⌝ ∗
       ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 (e2, σ2, efs) > 0⌝ -∗ £ 1 ={∅,E}=∗
         state_interp (S n) σ2 ∗ WP e2 @ s; E {{ Φ }} ∗
         [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "H". iApply wp_lift_step_fupd; [done|]. iIntros (??) "Hσ".
    iMod ("H" with "Hσ") as "[$ H]". iIntros "!>" (e2 σ2 efs ?) "Hlc !> !>".
    by iApply ("H" with "[//] Hlc").
  Qed.

  Lemma wp_lift_pure_step_no_fork `{!Inhabited (state Λ)} E E' Φ e1 s :
    (∀ σ1, reducible e1 σ1) →
    (∀ σ1 e2 σ2 efs, prim_step e1 σ1 (e2, σ2, efs) > 0 → σ2 = σ1 ∧ efs = []) →
    (|={E}[E']▷=> ∀ e2 σ efs, ⌜prim_step e1 σ (e2, σ, efs) > 0⌝ → £ 1 -∗
       WP e2 @ s; E {{ Φ }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (Hsafe Hstep) "H". iApply wp_lift_step.
    { specialize (Hsafe inhabitant) as [? Hs]. by eapply val_stuck. }
    iIntros (n σ1) "Hσ". iMod "H".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit; [done|].
    iNext. iIntros (e2 σ2 efs Hprim) "Hlc".
    destruct (Hstep _ _ _ _ Hprim) as [-> ->].
    iMod (state_interp_mono with "Hσ") as "Hσ".
    iMod "Hclose" as "_". iMod "H". iModIntro.
    iDestruct ("H" with "[//] Hlc") as "H". simpl. by iFrame.
  Qed.

  Lemma wp_lift_atomic_step_fupd {E1 E2 Φ} e1 s :
    to_val e1 = None →
    (∀ n σ1, state_interp n σ1 ={E1}=∗
       ⌜reducible e1 σ1⌝ ∗
       ∀ e2 σ2 efs, ⌜prim_step e1 σ1 (e2, σ2, efs) > 0⌝ -∗ £ 1 ={E1}[E2]▷=∗
         state_interp (S n) σ2 ∗ from_option Φ False (to_val e2) ∗
         [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
    ⊢ WP e1 @ s; E1 {{ Φ }}.
  Proof.
    iIntros (?) "H".
    iApply (wp_lift_step_fupd E1 _ e1)=>//; iIntros (n σ1) "Hσ1".
    iMod ("H" $! n σ1 with "Hσ1") as "[$ H]".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose" (e2 σ2 efs Hs) "Hlc". iMod "Hclose" as "_".
    iMod ("H" $! e2 σ2 with "[#] Hlc") as "H"; [done|].
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
    iMod "Hclose" as "_". iMod "H" as "($ & HQ & $)".
    destruct (to_val e2) eqn:?; last by iExFalso.
    iApply pgl_wp_value; last done. by apply of_to_val.
  Qed.

  Lemma wp_lift_atomic_step {E Φ} e1 s :
    to_val e1 = None →
    (∀ n σ1, state_interp n σ1 ={E}=∗
       ⌜reducible e1 σ1⌝ ∗
       ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 (e2, σ2, efs) > 0⌝ -∗ £ 1 ={E}=∗
         state_interp (S n) σ2 ∗ from_option Φ False (to_val e2) ∗
         [∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ fork_post }})
    ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
    iIntros (??) "?". iMod ("H" with "[$]") as "[$ H]".
    iIntros "!> *". iIntros (Hstep) "Hlc !> !>".
    by iApply ("H" with "[//] Hlc").
  Qed.

  Lemma wp_lift_pure_det_step_no_fork `{!Inhabited (state Λ)} {E E' Φ} e1 e2 s :
    (∀ σ1, reducible e1 σ1) →
    (∀ σ1 e2' σ2 efs, prim_step e1 σ1 (e2', σ2, efs) > 0 → σ2 = σ1 ∧ e2' = e2 ∧ efs = []) →
    (|={E}[E']▷=> £ 1 -∗ WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (? Hpuredet) "H". iApply (wp_lift_pure_step_no_fork E E'); try done.
    { naive_solver. }
    iApply (step_fupd_wand with "H"); iIntros "H".
    iIntros (e' σ efs (?&->&->)%Hpuredet); auto.
  Qed.

  Lemma wp_pure_step_fupd `{!Inhabited (state Λ)} E E' e1 e2 φ n Φ s :
    PureExec φ n e1 e2 →
    φ →
    (|={E}[E']▷=>^n £ n -∗ WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
    iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl.
    { iMod lc_zero as "Hz". by iApply "Hwp". }
    iApply wp_lift_pure_det_step_no_fork.
    - done.
    - intros σ1 e2' σ2 efs Hpstep.
      by injection (pmf_1_supp_eq _ _ _ (pure_step_det σ1) Hpstep).
    - iApply (step_fupd_wand with "Hwp"). iIntros "Hwp Hone".
      iApply "IH". iApply (step_fupdN_wand with "Hwp").
      iIntros "Hwp Hlc". iApply ("Hwp" with "[Hone Hlc]").
      rewrite (lc_succ n). iFrame.
  Qed.

  Lemma wp_pure_step_later `{!Inhabited (state Λ)} E e1 e2 φ n Φ s :
    PureExec φ n e1 e2 →
    φ →
    ▷^n (£ n -∗ WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    intros Hexec ?. rewrite -wp_pure_step_fupd //. clear Hexec.
    iIntros "H". by iApply step_fupdN_intro.
  Qed.

  Local Lemma step_fupdN_sep_le n m (P Q : iProp Σ) :
    n ≤ m → (|={∅}▷=>^n P) -∗ (|={∅}▷=>^m Q) -∗ |={∅}▷=>^m (P ∗ Q).
  Proof.
    iInduction n as [|n] "IH" forall (m); iIntros (Hle) "HP HQ".
    - simpl. iApply (step_fupdN_wand with "HQ"). iIntros "HQ". iFrame.
    - destruct m as [|m]; first lia. simpl.
      iMod "HP". iMod "HQ". iIntros "!> !>". iMod "HP". iMod "HQ". iModIntro.
      iApply ("IH" with "[%] HP HQ"). lia.
  Qed.

  (** Iris's [wp_step_fupdN_strong]: a caller-supplied [n]-step update is
      run alongside the next program step, provided [n] does not exceed
      that step's later budget. *)
  Lemma wp_step_fupdN_strong n s E1 E2 e P Φ :
    TCEq (to_val e) None → E2 ⊆ E1 →
    (∀ ns σ, state_interp ns σ ={E1,∅}=∗ ⌜n ≤ S (num_laters_per_step ns)⌝) ∧
    ((|={E1,E2}=> |={∅}▷=>^n |={E2,E1}=> P) ∗
      WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
    WP e @ s; E1 {{ Φ }}.
  Proof.
    destruct n as [|n].
    { iIntros (_ ?) "/= [_ [HP Hwp]]".
      iApply (pgl_wp_strong_mono with "Hwp"); [done|].
      iIntros (????) "(?&?&H)".
      iMod "HP". iMod "HP". iMod ("H" with "HP") as "HΦ".
      iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
      iApply state_step_coupl_ret. iMod "Hclose" as "_". by iFrame. }
    rewrite !pgl_wp_unfold /pgl_wp_pre /=. iIntros (-> ?) "H".
    iIntros (ns σ1 ε) "[Hσ Hε]".
    destruct (decide (n ≤ num_laters_per_step ns)) as [Hn|Hn]; first last.
    { iDestruct "H" as "[Hn _]". iMod ("Hn" with "Hσ") as %?. lia. }
    iDestruct "H" as "[_ [>HP Hwp]]". iMod ("Hwp" with "[$]") as "Hwp".
    iModIntro.
    iApply (state_step_coupl_mono with "[HP] Hwp").
    iIntros (σ2 ε2) "Hwp".
    iApply (prog_coupl_mono with "[HP] Hwp").
    iIntros (e3 σ3 efs ε3) "H Hlc".
    iPoseProof (step_fupdN_sep_le (S n) (S (num_laters_per_step ns)) with "HP (H Hlc)") as "H"; first lia.
    iApply (step_fupdN_wand with "H"). iIntros "[HP H]".
    iApply (state_step_coupl_mono with "[HP] H").
    iIntros (σ4 ε4) ">($ & $ & Hwp & $)".
    iMod "HP". iModIntro.
    iApply (pgl_wp_strong_mono with "Hwp"); [done|].
    iIntros (????) "(?&?&H)".
    iMod ("H" with "HP") as "HΦ".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iApply state_step_coupl_ret. iMod "Hclose" as "_". by iFrame.
  Qed.

  Lemma wp_step_fupdN n s E1 E2 e P Φ :
    TCEq (to_val e) None → E2 ⊆ E1 →
    (∀ ns σ, state_interp ns σ ={E1,∅}=∗ ⌜n ≤ S (num_laters_per_step ns)⌝) ∧
    ((|={E1∖E2,∅}=> |={∅}▷=>^n |={∅,E1∖E2}=> P) ∗
      WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
    WP e @ s; E1 {{ Φ }}.
  Proof.
    iIntros (??) "H". iApply (wp_step_fupdN_strong with "[H]"); [done|].
    iApply (and_mono_r with "H"). apply sep_mono_l. iIntros "HP".
    iMod fupd_mask_subseteq_emptyset_difference as "H"; [|iMod "HP"]; [set_solver|].
    iMod "H" as "_". replace (E1 ∖ (E1 ∖ E2)) with E2; last first.
    { set_unfold=>x. destruct (decide (x ∈ E2)); naive_solver. }
    iModIntro. iApply (step_fupdN_wand with "HP"). iIntros "H".
    iApply fupd_mask_frame; [|iMod "H"; iModIntro]; [set_solver|].
    by rewrite difference_empty_L (comm_L (∪)) -union_difference_L.
  Qed.

  Lemma wp_step_fupd s E1 E2 e P Φ :
    TCEq (to_val e) None → E2 ⊆ E1 →
    (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
  Proof. apply pgl_wp_step_fupd. Qed.

End lifting.
