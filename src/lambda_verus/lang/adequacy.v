(** Adequacy of the concurrent probabilistic λRust program logic.

    From a WP for [e] (given [£ K], [time_ctx] and [↯ ε]) we get, for
    every scheduler [sch] and step bound [n],
    - [lrust_wp_pgl]: [pgl (sch_exec sch n …) φ ε], and
    - [lrust_wp_safety]: the mass of non-stuck executions [sch_pexec]
      is at least [1 - ε] (for schedulers of mass 1).

    Both instantiate the generic [lrust.prob.adequacy] with λRust's ghost
    state, allocated as in VerusBelt's [lrust_adequacy], plus error
    credits.  The step budget [lrust_total_step_credits 1 n] covers
    [num_laters_per_step n = sum_advance_credits (n + 1)]. *)
Require Import guarding.internal.na_invariants_fork.
From Stdlib Require Import Reals Psatz.
From iris.algebra.lib Require Import mono_nat.
From iris.algebra Require Import numbers.
From iris.proofmode Require Import proofmode.
From lrust.prob Require Import adequacy.
From lrust.lang Require Export heap.
From lrust.lang Require Import proofmode notation.
From lrust.util Require Import non_atomic_cell_map atomic_lock_counter.
From clutch.prob Require Import distribution mdp.
Set Default Proof Using "Type".
Import uPred.

(** The invariant instance of the WP is the one [fupd_finally_soundness]
    hands us; unification has to see through the (opaque) projections. *)
Local Transparent alerusWpGS_invGS lrustGS_invGS.

Class lrustGpreS Σ := HeapGpreS {
  #[global] lrustGpreS_iris :: invGpreS Σ;
  #[global] lrustGpreS_heap :: inG Σ (authR heapUR);
  #[global] lrustGpreS_heap_freeable :: inG Σ (authR heap_freeableUR);
  #[global] lrustGpreS_heap_na_logic :: na_logicG loc val Σ;
  #[global] lrustGpreS_heap_na_inv :: na_invG Σ;
  #[global] lrustGpreS_atomic_lock_ctr :: alc_logicG Σ;
  #[global] lrustGpreS_time :: timePreG Σ;
  #[global] lrustGpreS_ec :: ecGpreS Σ;
}.

Definition lrustΣ : gFunctors :=
  #[invΣ; timeΣ; ecΣ;
    GFunctor (constRF (authR heapUR));
    GFunctor (constRF (authR heap_freeableUR));
    na_logicΣ loc val;
    alc_logicΣ;
    na_invΣ
    ].
Global Instance subG_heapPreG {Σ} : subG lrustΣ Σ → lrustGpreS Σ.
Proof. solve_inG. Qed.

(** The step budget, stated without an [lrustGS] instance. *)
Fixpoint lrust_total_step_credits (k n : nat) : nat :=
  match n with
  | 0%nat => 0%nat
  | S n' => S (sum_advance_credits (k + 1)) + lrust_total_step_credits (S k) n'
  end.

Lemma total_step_credits_lrust `{!lrustGS Σ} k n :
  total_step_credits k n = lrust_total_step_credits k n.
Proof. revert k; induction n as [|n IH]; intros k; simpl; [done|]. by rewrite IH. Qed.

Local Open Scope R.

Theorem lrust_wp_pgl `{!lrustGpreS Σ} `{Countable sch_int_state} (ζ : sch_int_state)
    (sch : scheduler (con_lang_mdp lrust_lang) sch_int_state)
    (e : expr) n (ε : R) (K : nat) φ :
  0 <= ε →
  (∀ `{!lrustGS Σ}, ⊢ £ K -∗ time_ctx -∗ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  pgl (sch_exec sch n (ζ, ([e], (∅, false)))) φ ε.
Proof.
  intros Hε Hwp.
  apply (pure_soundness (PROP:=iPropI Σ)).
  apply (laterN_soundness _ (S (S (lrust_total_step_credits 1 n)))).
  rewrite laterN_later -except_0_into_later.
  destruct (decide (ε < 1)) as [Hcr|Hcr]; last first.
  { iApply laterN_intro. iApply except_0_intro. iPureIntro.
    apply not_Rlt, Rge_le in Hcr.
    rewrite /pgl. intros. eapply Rle_trans; [apply prob_le_1|done]. }
  apply (fupd_finally_soundness HasLc
           (K + advance_credits 4 + lrust_total_step_credits 1 n) ⊤).
  iIntros (Hinv) "Hlc".
  iDestruct (lc_split with "Hlc") as "[Hlc Hsteps]".
  iDestruct (lc_split with "Hlc") as "[HK H4]".
  set ε' := mknonnegreal ε Hε.
  change ε with (nonneg ε') in Hwp |- *.
  iMod (ec_alloc ε') as (Hec) "[Hs Hf]"; [done|].
  iMod (non_atomic_map_alloc_empty) as (vγ) "Hvγ".
  iMod (own_alloc (● (∅ : heap_freeableUR))) as (fγ) "Hfγ";
    [by apply auth_auth_valid|].
  iMod (time_init with "H4") as (Htime) "[TIME Htime]"; [done|].
  iMod (na_alloc) as (atomic_poolname) "pool".
  iMod (atomic_lock_ctr_alloc) as (atomic_lock_ctr_name) "ctr".
  set (Hheap := HeapGS _ _ _ _ vγ fγ atomic_poolname atomic_lock_ctr_name).
  set (HlrustGS := LRustGS _ _ Hec _ _ Hheap Htime).
  iDestruct (Hwp HlrustGS with "HK TIME Hf") as "Hwp".
  iAssert (@state_interp lrust_lang _ (@lrustGS_alerusWpGS _ HlrustGS) 1 ((∅, false) : state))%I
    with "[Hvγ Hfγ Htime pool ctr]" as "Hσ".
  { rewrite /state_interp /=. iFrame "Htime". iExists ∅. iFrame.
    iPureIntro. intros ?? Hbad. by rewrite lookup_empty in Hbad. }
  rewrite -(total_step_credits_lrust 1 n).
  iPoseProof (wp_refRcoupl_hfupd ζ ε' e [] (∅, false) 1 n φ sch with "[-]") as "H".
  { iFrame. done. }
  iExact "H".
Qed.

Theorem lrust_wp_safety `{!lrustGpreS Σ} `{Countable sch_int_state} (ζ : sch_int_state)
    (sch : scheduler (con_lang_mdp lrust_lang) sch_int_state)
    (e : expr) n (ε : R) (K : nat) φ :
  0 <= ε →
  sch_mass_1 sch →
  (∀ `{!lrustGS Σ}, ⊢ £ K -∗ time_ctx -∗ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  SeriesC (sch_pexec sch n (ζ, ([e], (∅, false)))) >= 1 - ε.
Proof.
  intros Hε Hmass Hwp.
  apply (pure_soundness (PROP:=iPropI Σ)).
  apply (laterN_soundness _ (S (S (lrust_total_step_credits 1 n)))).
  rewrite laterN_later -except_0_into_later.
  destruct (decide (ε < 1)) as [Hcr|Hcr]; last first.
  { iApply laterN_intro. iApply except_0_intro. iPureIntro.
    trans 0; [by apply Rle_ge, SeriesC_ge_0|lra]. }
  apply (fupd_finally_soundness HasLc
           (K + advance_credits 4 + lrust_total_step_credits 1 n) ⊤).
  iIntros (Hinv) "Hlc".
  iDestruct (lc_split with "Hlc") as "[Hlc Hsteps]".
  iDestruct (lc_split with "Hlc") as "[HK H4]".
  set ε' := mknonnegreal ε Hε.
  change ε with (nonneg ε') in Hwp |- *.
  iMod (ec_alloc ε') as (Hec) "[Hs Hf]"; [done|].
  iMod (non_atomic_map_alloc_empty) as (vγ) "Hvγ".
  iMod (own_alloc (● (∅ : heap_freeableUR))) as (fγ) "Hfγ";
    [by apply auth_auth_valid|].
  iMod (time_init with "H4") as (Htime) "[TIME Htime]"; [done|].
  iMod (na_alloc) as (atomic_poolname) "pool".
  iMod (atomic_lock_ctr_alloc) as (atomic_lock_ctr_name) "ctr".
  set (Hheap := HeapGS _ _ _ _ vγ fγ atomic_poolname atomic_lock_ctr_name).
  set (HlrustGS := LRustGS _ _ Hec _ _ Hheap Htime).
  iDestruct (Hwp HlrustGS with "HK TIME Hf") as "Hwp".
  iAssert (@state_interp lrust_lang _ (@lrustGS_alerusWpGS _ HlrustGS) 1 ((∅, false) : state))%I
    with "[Hvγ Hfγ Htime pool ctr]" as "Hσ".
  { rewrite /state_interp /=. iFrame "Htime". iExists ∅. iFrame.
    iPureIntro. intros ?? Hbad. by rewrite lookup_empty in Hbad. }
  rewrite -(total_step_credits_lrust 1 n).
  iPoseProof (wp_safety_hfupd ζ ε' e [] (∅, false) 1 n φ sch Hmass with "[-]") as "H".
  { iFrame. done. }
  iExact "H".
Qed.
