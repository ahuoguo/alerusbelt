(** Distribution adequacy at the AlerusBelt typing layer. *)
From Stdlib Require Import Reals Psatz.
From iris.algebra Require Import frac dfrac_agree auth lib.mono_nat numbers.
From iris.base_logic.lib Require Import invariants own fancy_updates.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.common Require Import language exec.
From clutch.prob Require Import distribution countable_sum.
From clutch.eris Require Import weakestpre.
From guarding.internal Require Import na_invariants_fork.
From lrust.util Require Import cancellable_na_invariants cancellable
                                 non_atomic_cell_map atomic_lock_counter.
From guarding.lib Require Import fractional cancellable.
From lrust.lifetime Require Import lifetime_full.
From lrust.lang Require Import adequacy distribution_adequacy proofmode notation
                                 lang heap lifting time.
From lrust.typing Require Import type programs rand_ubig soundness.
Import uPred.
Set Default Proof Using "Type".

Local Open Scope R.

(** ** The EPT specification, as a typed instruction

    [ept_typed μ e] is the AlerusBelt model of a Verus sampler
    signature

    ```rust
      fn sample(Tracked(c): Tracked<ErrorCreditResource>,
                Ghost(Err): Ghost<spec_fn(V) -> real>)
        -> (Tracked<ErrorCreditResource>)
        requires c@ =~= Value { car: <expectation of Err under μ> },
                 forall |v| 0real <= Err(v) <= 1real,
        ensures  out@ =~= Value { car: Err(v) },
    ```

    same shape as [type_rand_ubig_instr] 
*)
Definition ept_typed (Σ : gFunctors) (μ : distr val)
    (e : language.expr lrust_prob_lang) : Prop :=
  ∀ (Err : val → R) (l : loc),
    (∀ v, 0 <= Err v <= 1) →
    ∀ `{!typeG Σ, !cnaInv_logicG Σ},
      ∃ tr : predl_trans [at_locₛ (trackedₛ unitₛ)] [at_locₛ (trackedₛ unitₛ)],
        tr (λ _ _, True) -[(l, ())] ⊤ ∧
        typed_instr [] [] (InvCtx [] static AtomicClosed)
          +[#l ◁ ↯_T (SeriesC (λ v, μ v * Err v))]
          e
          (λ v, +[#l ◁ ↯_T (Err v)])
          tr.

(** A typed spec that also returns the sampled value in its output
    tctx, matches shape of the Verus signature [-> ((v, out): (V, Tracked<ErrorCreditResource>))]
    meets [ept_typed] by dropping the head entry. *)
Lemma typed_instr_drop_head `{!typeG Σ, !cnaInv_logicG Σ} {𝔄l 𝔅 𝔅l}
    E L I (T : tctx 𝔄l) e (t : val → tctx_elt 𝔅) (T' : val → tctx 𝔅l) tr :
  typed_instr E L I T e (λ v, t v +:: T' v) tr →
  typed_instr E L I T e T' (λ post, tr (λ '(_ -:: bl), post bl)).
Proof.
  intros Hinstr tid post mask iκs xl.
  iIntros "LFT TIME E L I T %Obs".
  iApply (pgl_wp_wand with "[-]").
  { iApply (Hinstr tid (λ '(_ -:: bl), post bl) mask iκs xl
             with "LFT TIME E L I T [%]"). exact Obs. }
  iIntros (v) "H". iDestruct "H" as ([b bl]) "(L & I & [_ T] & %Obs')".
  iExists bl. by iFrame.
Qed.

(** From the typed EPT spec to an eris WP *)
Section ept_wp.
  Context `{!typeG Σ, !cnaInv_logicG Σ}.

  Lemma ept_typed_wp (μ : distr val) (e : language.expr lrust_prob_lang)
      (Err : val → R) (l : loc) tid :
    (∀ v, 0 <= Err v <= 1) →
    ept_typed Σ μ e →
    llft_ctx -∗ time_ctx -∗
    invctx_interp tid ⊤ [] (InvCtx [] static AtomicClosed) -∗
    ↯ (SeriesC (λ v, μ v * Err v)) -∗
    WP e {{ v, ↯ (Err v) }}.
  Proof.
    iIntros (HErr Hept) "LFT TIME Hinv Hcr".
    iApply fupd_pgl_wp.
    iMod persistent_time_receipt_0 as "#⧖0".
    iModIntro.
    destruct (Hept Err l HErr _ _) as (tr & Htr & Hinstr).
    iApply (pgl_wp_wand with "[-]").
    { iApply (Hinstr tid (λ _ _, True%type) ⊤ [] -[(l, ())]
               with "LFT TIME [] [] Hinv [Hcr] []").
      - iApply big_sepL_nil. done.
      - iApply big_sepL_nil. done.
      - rewrite /tctx_elt_interp /=.
        iSplit; last done.
        iExists (LitV (LitLoc l)), 0%nat.
        iSplit; first done.
        iFrame "⧖0". rewrite /ty_own /=. by iFrame "Hcr".
      - iPureIntro. exact Htr. }
    iIntros (v) "H".
    iDestruct "H" as (xl') "(_ & _ & Htctx & _)".
    destruct xl' as [[l' []] []].
    iDestruct "Htctx" as "[Hc _]".
    rewrite /tctx_elt_interp /=.
    iDestruct "Hc" as (w d Hev) "[_ [Hcr _]]".
    by rewrite /ty_own /=.
  Qed.

End ept_wp.

(** ** Typing-layer adequacy entry point

    [lrust_wp_pgl] hands the caller a bare [lrustGS Σ]; a WP coming out
    of the typing layer also needs [llft_ctx], [time_ctx] and an
    [invctx].  This allocates those too. *)
Theorem type_wp_pgl `{!typePreG Σ}
    (e : language.expr lrust_prob_lang) (σ : language.state lrust_prob_lang)
    n (ε : R) (φ : val → Prop) :
  (∀ l ls w, σ !! l = Some (ls, w) → ls = RSt 0%nat) →
  (0 <= ε) →
  (∀ `{!typeG Σ, !cnaInv_logicG Σ} (tid : thread_id),
      llft_ctx -∗ time_ctx -∗
      invctx_interp tid ⊤ [] (InvCtx [] static AtomicClosed) -∗
      ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  pgl (exec n (e, σ)) φ ε.
Proof.
  intros Hσ Hε Hwp.
  apply (pure_soundness (PROP:=iPropI Σ)).
  apply (laterN_soundness _ (S (lrust_total_step_credits 1 n))).
  rewrite laterN_later -except_0_into_later.
  destruct (decide (ε < 1)) as [Hcr|Hcr]; last first.
  { iApply laterN_intro. iApply except_0_intro. iPureIntro.
    apply not_Rlt, Rge_le in Hcr.
    rewrite /pgl. intros. eapply Rle_trans; [apply prob_le_1|done]. }
  apply (fupd_finally_soundness HasLc
           (1 + advance_credits 4 + lrust_total_step_credits 1 n) ⊤).
  iIntros (Hinv) "Hlc_total".
  iDestruct (lc_split 1
               (advance_credits 4 + lrust_total_step_credits 1 n)%nat
               with "Hlc_total") as "[H£llft Hrest]".
  iDestruct (lc_split (advance_credits 4)
               (lrust_total_step_credits 1 n)
               with "Hrest") as "[H£time Hlc]".
  iMod (ec_alloc (mknonnegreal ε Hε)) as (Hec) "[Hs Hcr]"; [done|].
  iMod (non_atomic_cell_map.non_atomic_map_alloc_heap σ Hσ) as (vγ) "Hvγ".
  iMod (own_alloc (● (∅ : heap.heap_freeableUR))) as (fγ) "Hfγ";
    [by apply auth_auth_valid|].
  iMod na_invariants_fork.na_alloc as (threadpool_γ) "Hpool".
  iMod atomic_lock_counter.atomic_lock_ctr_alloc as (alc_γ) "Hctr".
  iMod (time_init ⊤ with "H£time") as (Htime) "[#TIME Hti]"; [solve_ndisj|].
  pose (Hheap := heap.HeapGS _ _ _ _ vγ fγ threadpool_γ alc_γ).
  pose (HlrustGS := LRustGS Σ Hinv _ _ Hheap Hec Htime).
  change ε with (nonneg (mknonnegreal ε Hε)).
  iPoseProof (wp_refRcoupl 1 (mknonnegreal ε Hε) e σ n φ) as "H".
  iSpecialize ("H" with "[-]").
  { iFrame "Hlc".
    iSplitR "Hs Hcr H£llft".
    { rewrite /state_interp /=. iSplitR "Hti".
      - rewrite /heap.heap_ctx. iExists ∅. iFrame "Hvγ Hfγ".
        iSplit.
        { iPureIntro. rewrite /heap.heap_freeable_rel. intros blk qs Hbad.
          by rewrite lookup_empty in Hbad. }
        rewrite /heap.heap_ato_ctx. iFrame.
      - iApply "Hti". }
    iFrame "Hs".
    iApply fupd_pgl_wp.
    iMod (llft_alloc with "H£llft") as (Hlft) "#LFT".
    pose (Hcna := {| cnaInv_na_inv_inG := type_preG_cna_invG |}).
    iMod (@invctx_alloc Σ _ _ _ Hcna ⊤) as (tid) "Hinvctx".
    pose (Htype := @TypeG Σ HlrustGS Hlft _ _ _).
    iModIntro.
    iApply (Hwp Htype Hcna tid with "LFT TIME Hinvctx Hcr"). }
  iApply "H".
Qed.

(** The [pgl] upper bound a typed EPT spec yields: the sampler returns
    [target] with probability at most [μ target]. *)
Lemma ept_pgl_lim `{!typePreG Σ}
    (μ : distr val) (e : language.expr lrust_prob_lang)
    (σ : language.state lrust_prob_lang) (target : val) :
  (∀ l ls w, σ !! l = Some (ls, w) → ls = RSt 0%nat) →
  ept_typed Σ μ e →
  pgl (lim_exec (e, σ)) (λ w, target ≠ w) (μ target).
Proof.
  intros Hσ Hept.
  (* Instantiate the EPT spec at the indicator allocation of [target]:
     the whole budget [μ target] is refunded on the single outcome we
     want to exclude, so [↯ 1] rules it out. *)
  set (Err := λ w, if bool_decide (target = w) then 1 else 0).
  assert (∀ v, 0 <= Err v <= 1) as HErr.
  { intros v. rewrite /Err. case_bool_decide; lra. }
  assert (SeriesC (λ v, μ v * Err v) = μ target) as Hexp.
  { rewrite (SeriesC_ext _ (λ v, if bool_decide (v = target) then μ target else 0)).
    - apply SeriesC_singleton.
    - intros v. rewrite /Err. do 2 case_bool_decide; subst; try done; lra. }
  rewrite /pgl. apply lim_exec_continuous_prob. intros n.
  apply (type_wp_pgl e σ n (μ target) (λ w, target ≠ w) Hσ (pmf_pos μ target)).
  intros Htype Hcna tid.
  iIntros "LFT TIME Hinv Hcr".
  iApply (pgl_wp_wand with "[-]").
  { rewrite -Hexp.
    iApply (ept_typed_wp μ e Err ((1%positive, 0%Z) : loc) tid HErr Hept
             with "LFT TIME Hinv Hcr"). }
  iIntros (v) "Hcr". rewrite /Err. case_bool_decide; subst.
  - iExFalso. iApply (ec_contradict with "Hcr"). lra.
  - done.
Qed.

(** ** Distribution adequacy for a typed sampler

    An [ept_typed] derivation plus almost-sure termination (external,
    e.g. from Verus's [decreases] clause discharged by credit
    amplification) pins the sampler's output distribution to [μ]. *)
Theorem type_distribution_adequacy `{!typePreG Σ}
    (μ : distr val) (e : language.expr lrust_prob_lang)
    (σ : language.state lrust_prob_lang) :
  (∀ l ls w, σ !! l = Some (ls, w) → ls = RSt 0%nat) →
  ept_typed Σ μ e →
  SeriesC (lim_exec (e, σ)) = 1%R →
  SeriesC μ = 1%R ∧ ∀ v, lim_exec (e, σ) v = μ v.
Proof.
  intros Hσ Hept Hterm.
  apply distribution_adequacy_of_pgl.
  - intros target. by apply (ept_pgl_lim (Σ := Σ)).
  - apply Rle_ge, Req_le. symmetry. exact Hterm.
Qed.
