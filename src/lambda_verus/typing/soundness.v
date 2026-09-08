(** Probabilistic type soundness for [lrust_prob_lang].

    Bridges typed-program derivations to a safety bound on the mass
    of the [n]-step partial-execution distribution [pexec n].

    - [type_soundness]: the general typing-layer form, parameterised
      over [𝔅 : syn_type], a predicate transformer
      [tr : predl_trans' [] 𝔅], and a postcondition predicate
      [post : pred' (~~𝔅)].  Given a [typed_body] derivation with
      transformer [tr] and the source-level obligation
      [tr post -[] ⊤], concludes [SeriesC (pexec n (e, σ)) = 1]

    - [type_soundness_not_stuck]: the same result in probability
      form - [probp (pexec n (e, σ)) (λ ρ, is_final ρ ∨ reducible ρ)
      = 1].

    - [type_soundness_progress]: the same result *pointwise* - every
      configuration in the support of [pexec n (e, σ)] is a value or
      can take another step.  Equivalent to the mass form when there
      is no error-credit budget, and the one that reads as safety
      without knowing how [pexec] loses mass.  This is the closest
      analogue of the upstream verusbelt progress conjunct.

    - [type_soundness_val]: bridges [typed_val v ty a], the typing
      layer's notion that value [v] inhabits semantic type [ty] at
      refinement [a] - to the same conclusion for [of_val v].
      Sanity-check that the bridge exposes the typed-instr WP and
      threads it through the [typed_body] obligation.

    - [type_soundness_credit] / [type_soundness_credit_not_stuck]:
      the same, for a body that consumes an initial [↯ ε]
      error-credit budget; the bound degrades to [1 - ε].

   ** Comparison with the upstream verusbelt [type_soundness] **

    Upstream verusbelt's [soundness.v] proves an operational-safety
    theorem (see [docker-contents/clean-src/.../soundness.v]):

        Theorem type_soundness `{!typePreG Σ} (main : val) σ t c :
          (∀ `{!typeG Σ}, typed_val main main_type c) →
          rtc erased_step ([main [exit_cont]%E], (∅, false)) (t, σ) →
          nonracing_threadpool t σ ∧
          (∀ e, e ∈ t → is_Some (to_val e) ∨ reducible e σ).

    [type_soundness_progress] is the direct analogue of that progress
    conjunct: instead of quantifying over all reachable thread pools,
    it quantifies over the support of the [n]-step execution
    distribution.  [type_soundness_not_stuck] is its probabilistic
    restatement, and the only form that survives an error-credit
    budget ([type_soundness_credit_not_stuck]).

 *)

From iris.algebra Require Import frac dfrac_agree auth lib.mono_nat numbers.
From iris.base_logic.lib Require Import invariants own fancy_updates.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.common Require Import language exec.
From clutch.prob Require Import distribution.
From clutch.eris Require Import weakestpre.
From guarding.internal Require Import na_invariants_fork.
From lrust.util Require Import cancellable_na_invariants cancellable
                                 non_atomic_cell_map atomic_lock_counter.
From guarding.lib Require Import fractional cancellable.
From lrust.lifetime Require Import lifetime_full.
From lrust.lang Require Import adequacy proofmode notation lang heap lifting time.
From lrust.typing Require Import type programs rand_ubig.
Import uPred.
Set Default Proof Using "Type".

(** Pre-ghost-state bundle for [type_soundness]: extends
    [lrustErisGpreS] with the typing-layer pre-classes
    ([llft_logicGpreS], [frac_logicG], [ecInv_logicG],
    [cancellable_na_invariants.na_invG] for cnaInv_logicG, etc.). *)
Class typePreG (Σ : gFunctors) := PreTypeG {
  #[global] type_preG_lrustErisGpreS :: lrustErisGpreS Σ;
  #[global] type_preG_lftGS :: llft_logicGpreS Σ;
  #[global] type_preG_frac_logicG :: frac_logicG Σ;
  #[global] type_preG_ecInv_logicG :: ecInv_logicG Σ;
  #[global] type_preG_cna_invG :: cancellable_na_invariants.na_invG Σ;
  #[global] type_preG_agree_pairΣ :: inG Σ (dfrac_agreeR (leibnizO nat))
}.

(** Shared kernel: allocates all the ghost state, runs the
    [typed_body] derivation, and hands the resulting eris WP (with its
    credit budget, [state_interp] and error-credit supply) to an
    arbitrary adequacy consumer.  Both [wp_refRcoupl] and
    [wp_refRcoupl_safety] of [lang/adequacy.v] have that shape. *)
Local Lemma type_soundness_gen `{!typePreG Σ}
    {𝔅 : syn_type} (tr : predl_trans' [] 𝔅) (post : pred' (~~𝔅))
    (e : language.expr lrust_prob_lang) (σ : language.state lrust_prob_lang)
    (n : nat) (Ψ : Prop) :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  tr post -[] ⊤ →
  (∀ `{!typeG Σ, !cnaInv_logicG Σ},
      ⊢ typed_body (𝔄l := []) (𝔅 := 𝔅) [] []
                   (InvCtx [] static AtomicClosed) [] +[] e tr) →
  (∀ `{!lrustGS Σ},
      £ (lrust_total_step_credits 1 n) ∗ state_interp 1 σ ∗
        err_interp nnreal_zero ∗ WP e {{ _, ⌜True⌝ }}
      ⊢ |={⊤|}=> ▷^(lrust_total_step_credits 1 n) ◇ ⌜Ψ⌝) →
  Ψ.
Proof.
  intros Hσ Htr Hbody Hadq.
  apply (pure_soundness (PROP:=iPropI Σ)).
  apply (laterN_soundness _ (S (lrust_total_step_credits 1 n))).
  rewrite laterN_later -except_0_into_later.
  apply (fupd_finally_soundness HasLc
           (1 + advance_credits 4 + lrust_total_step_credits 1 n) ⊤).
  iIntros (Hinv) "Hlc_total".
  iDestruct (lc_split 1
               (advance_credits 4 + lrust_total_step_credits 1 n)%nat
               with "Hlc_total") as "[H£llft Hrest]".
  iDestruct (lc_split (advance_credits 4)
               (lrust_total_step_credits 1 n)
               with "Hrest") as "[H£time Hlc]".
  iMod (ec_alloc nnreal_zero) as (Hec) "[Hs _]"; [simpl; lra|].
  iMod (non_atomic_cell_map.non_atomic_map_alloc_heap σ Hσ) as (vγ) "Hvγ".
  iMod (own_alloc (● (∅ : heap.heap_freeableUR))) as (fγ) "Hfγ";
    [by apply auth_auth_valid|].
  iMod na_invariants_fork.na_alloc as (threadpool_γ) "Hpool".
  iMod atomic_lock_counter.atomic_lock_ctr_alloc as (alc_γ) "Hctr".
  iMod (time_init ⊤ with "H£time") as (Htime) "[#TIME Hti]"; [solve_ndisj|].
  pose (Hheap := heap.HeapGS _ _ _ _ vγ fγ threadpool_γ alc_γ).
  pose (HlrustGS := LRustGS Σ Hinv _ _ Hheap Hec Htime).
  iPoseProof (Hadq HlrustGS) as "H".
  iSpecialize ("H" with "[-]").
  { iFrame "Hlc".
    iSplitR "Hs H£llft".
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
    iPoseProof (Hbody Htype Hcna) as "Hb".
    iModIntro.
    iApply (pgl_wp_mono _ _ _ (λ _, cont_postcondition)).
    { iIntros (v) "_". iPureIntro. done. }
    iApply ("Hb" $! tid -[] ⊤ post []
              with "LFT TIME [] [] Hinvctx [] [] []").
    - iApply big_sepL_nil. done.
    - iApply big_sepL_nil. done.
    - iIntros (c Hin). by inversion Hin.
    - simpl; done.
    - iPureIntro. exact Htr. }
  iApply "H".
Qed.

(** A [typed_body] derivation entails [SeriesC (pexec n (e, σ)) = 1]:
    the [n]-step *partial* execution distribution loses mass exactly
    on stuck configurations, so full mass says the program never gets
    stuck within [n] steps. *)
Theorem type_soundness `{!typePreG Σ}
    {𝔅 : syn_type} (tr : predl_trans' [] 𝔅) (post : pred' (~~𝔅))
    (e : language.expr lrust_prob_lang) (σ : language.state lrust_prob_lang) n :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  tr post -[] ⊤ →
  (∀ `{!typeG Σ, !cnaInv_logicG Σ},
      ⊢ typed_body (𝔄l := []) (𝔅 := 𝔅) [] []
                   (InvCtx [] static AtomicClosed) [] +[] e tr) →
  SeriesC (pexec n (e, σ)) = 1%R.
Proof.
  intros Hσ Htr Hbody.
  apply Rle_antisym; [apply pmf_SeriesC|].
  cut (SeriesC (pexec n (e, σ)) >= 1 - 0)%R; [lra|].
  apply (type_soundness_gen tr post e σ n _ Hσ Htr Hbody).
  intros HlrustGS.
  exact (wp_refRcoupl_safety 1 nnreal_zero e σ n
           (λ _ : language.val lrust_prob_lang, True)).
Qed.

(** [type_soundness] in probability form: after [n] steps the program
    is a value or can take another step, with probability [1]. *)
Theorem type_soundness_not_stuck `{!typePreG Σ}
    {𝔅 : syn_type} (tr : predl_trans' [] 𝔅) (post : pred' (~~𝔅))
    (e : language.expr lrust_prob_lang) (σ : language.state lrust_prob_lang) n :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  tr post -[] ⊤ →
  (∀ `{!typeG Σ, !cnaInv_logicG Σ},
      ⊢ typed_body (𝔄l := []) (𝔅 := 𝔅) [] []
                   (InvCtx [] static AtomicClosed) [] +[] e tr) →
  probp (pexec n (e, σ)) (λ ρ, is_final ρ ∨ reducible ρ) = 1%R.
Proof.
  intros Hσ Htr Hbody.
  rewrite pexec_safety_relate.
  exact (type_soundness tr post e σ (S n) Hσ Htr Hbody).
Qed.

Theorem type_soundness_progress `{!typePreG Σ}
    {𝔅 : syn_type} (tr : predl_trans' [] 𝔅) (post : pred' (~~𝔅))
    (e : language.expr lrust_prob_lang) (σ : language.state lrust_prob_lang) n :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  tr post -[] ⊤ →
  (∀ `{!typeG Σ, !cnaInv_logicG Σ},
      ⊢ typed_body (𝔄l := []) (𝔅 := 𝔅) [] []
                   (InvCtx [] static AtomicClosed) [] +[] e tr) →
  ∀ ρ, (pexec n (e, σ) ρ > 0)%R → is_final ρ ∨ reducible ρ.
Proof.
  intros Hσ Htr Hbody.
  apply (probp_full_pos (pexec n (e, σ)) (λ ρ, is_final ρ ∨ reducible ρ)).
  - pose proof (type_soundness tr post e σ n Hσ Htr Hbody). lra.
  - exact (type_soundness_not_stuck tr post e σ n Hσ Htr Hbody).
Qed.

Theorem type_soundness_trivial `{!typePreG Σ}
    (e : language.expr lrust_prob_lang) (σ : language.state lrust_prob_lang) n :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  (∀ `{!typeG Σ, !cnaInv_logicG Σ},
      ⊢ typed_body (𝔄l := []) (𝔅 := unitₛ) [] []
                   (InvCtx [] static AtomicClosed) [] +[] e
                   (λ _ _ _, True%type)) →
  SeriesC (pexec n (e, σ)) = 1%R.
Proof.
  intros Hσ Hbody.
  apply (type_soundness (𝔅 := unitₛ) (λ _ _ _, True%type)
                        (λ _ _, True%type) e σ n Hσ);
    [done|exact Hbody].
Qed.

Theorem type_soundness_val `{!typePreG Σ}
    {𝔄 : syn_type} (v : val) (a : ~~𝔄)
    (σ : language.state lrust_prob_lang) n :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  (∀ `{!typeG Σ, !cnaInv_logicG Σ}, ∃ ty : type 𝔄, typed_val v ty a) →
  SeriesC (pexec n (of_val v, σ)) = 1%R.
Proof.
  intros Hσ Hval.
  apply (type_soundness_trivial _ σ n Hσ).
  intros HtypeG HcnaInv.
  destruct (Hval HtypeG HcnaInv) as [ty Hty].
  pose proof (Hty [] [] (InvCtx [] static AtomicClosed)) as Hinstr.
  rewrite /typed_instr_ty /typed_instr in Hinstr.
  iIntros (tid xl mask post iκs)
          "LFT TIME E_ L_ Hinv _Hcctx Htctx _".
  iApply (pgl_wp_wand with "[-]").
  - iApply (Hinstr tid (λ _ _, True%type) mask iκs xl
            with "LFT TIME E_ L_ Hinv Htctx []").
    iPureIntro. done.
  - iIntros (v') "_". done.
Qed.

(* TODO: should we add error credits as a new context *)
(** [type_soundness_gen] for a [typed_body] whose input tctx is a
    singleton [+[c ◁ ↯_T ε]] (a Verus-style
    [Tracked<ErrorCreditResource>]): [ec_alloc] supplies the [↯ ε] the
    body consumes, and the body is quantified over the loc serving as
    the credit's path-witness handle (cf. [rand_ubig.v]). *)
Local Lemma type_soundness_credit_gen `{!typePreG Σ}
    {𝔅 : syn_type}
    (tr : predl_trans' [at_locₛ (trackedₛ unitₛ)] 𝔅)
    (post : pred' (~~𝔅))
    (ε : R) (Hε_pos : (0 <= ε)%R)
    (e : language.expr lrust_prob_lang) (σ : language.state lrust_prob_lang)
    (n : nat) (Ψ : Prop) :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  (ε < 1)%R →
  (∀ l : loc, tr post -[(l, ())] ⊤) →
  (∀ `{!typeG Σ, !cnaInv_logicG Σ} (l : loc),
      ⊢ typed_body (𝔄l := [at_locₛ (trackedₛ unitₛ)]) (𝔅 := 𝔅) [] []
                   (InvCtx [] static AtomicClosed) []
                   +[#l ◁ error_credit_ty ε] e tr) →
  (∀ `{!lrustGS Σ},
      £ (lrust_total_step_credits 1 n) ∗ state_interp 1 σ ∗
        err_interp (mknonnegreal ε Hε_pos) ∗ WP e {{ _, ⌜True⌝ }}
      ⊢ |={⊤|}=> ▷^(lrust_total_step_credits 1 n) ◇ ⌜Ψ⌝) →
  Ψ.
Proof.
  intros Hσ Hε_lt1 Htr Hbody Hadq.
  apply (pure_soundness (PROP:=iPropI Σ)).
  apply (laterN_soundness _ (S (lrust_total_step_credits 1 n))).
  rewrite laterN_later -except_0_into_later.
  apply (fupd_finally_soundness HasLc
           (1 + advance_credits 4 + lrust_total_step_credits 1 n) ⊤).
  iIntros (Hinv) "Hlc_total".
  iDestruct (lc_split 1
               (advance_credits 4 + lrust_total_step_credits 1 n)%nat
               with "Hlc_total") as "[H£llft Hrest]".
  iDestruct (lc_split (advance_credits 4)
               (lrust_total_step_credits 1 n)
               with "Hrest") as "[H£time Hlc]".
  iMod (ec_alloc (mknonnegreal ε Hε_pos)) as (Hec) "[Hs Hcr]"; [done|].
  iMod (non_atomic_cell_map.non_atomic_map_alloc_heap σ Hσ) as (vγ) "Hvγ".
  iMod (own_alloc (● (∅ : heap.heap_freeableUR))) as (fγ) "Hfγ";
    [by apply auth_auth_valid|].
  iMod na_invariants_fork.na_alloc as (threadpool_γ) "Hpool".
  iMod atomic_lock_counter.atomic_lock_ctr_alloc as (alc_γ) "Hctr".
  iMod (time_init ⊤ with "H£time") as (Htime) "[#TIME Hti]"; [solve_ndisj|].
  pose (Hheap := heap.HeapGS _ _ _ _ vγ fγ threadpool_γ alc_γ).
  pose (HlrustGS := LRustGS Σ Hinv _ _ Hheap Hec Htime).
  iPoseProof (Hadq HlrustGS) as "H".
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
    iMod persistent_time_receipt_0 as "#⧖0".
    (* Pick a fictional loc for the credit's path-witness handle. *)
    pose (l_pick := ((1%positive, 0%Z) : loc)).
    iPoseProof (Hbody Htype Hcna l_pick) as "Hb".
    iModIntro.
    iApply (pgl_wp_mono _ _ _ (λ _, cont_postcondition)).
    { iIntros (v) "_". iPureIntro. done. }
    iApply ("Hb" $! tid -[(l_pick, ())] ⊤ post []
              with "LFT TIME [] [] Hinvctx [] [Hcr] []").
    - iApply big_sepL_nil. done.
    - iApply big_sepL_nil. done.
    - iIntros (c Hin). by inversion Hin.
    - rewrite /tctx_elt_interp /=.
      iSplit; last done.
      iExists (LitV (LitLoc l_pick)), 0%nat.
      iSplit; first done.
      iFrame "⧖0". rewrite /ty_own /=. by iFrame "Hcr".
    - iPureIntro. apply Htr. }
  iApply "H".
Qed.

(** The error-credit generalisation of [type_soundness]: with
    [ε = 1/2] the conclusion says the program gets stuck with
    probability at most [1/2]. *)
Theorem type_soundness_credit `{!typePreG Σ}
    {𝔅 : syn_type}
    (tr : predl_trans' [at_locₛ (trackedₛ unitₛ)] 𝔅)
    (post : pred' (~~𝔅))
    (ε : R)
    (e : language.expr lrust_prob_lang) (σ : language.state lrust_prob_lang) n :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  (0 <= ε < 1)%R →
  (∀ l : loc, tr post -[(l, ())] ⊤) →
  (∀ `{!typeG Σ, !cnaInv_logicG Σ} (l : loc),
      ⊢ typed_body (𝔄l := [at_locₛ (trackedₛ unitₛ)]) (𝔅 := 𝔅) [] []
                   (InvCtx [] static AtomicClosed) []
                   +[#l ◁ error_credit_ty ε] e tr) →
  (SeriesC (pexec n (e, σ)) >= 1 - ε)%R.
Proof.
  intros Hσ [Hε_pos Hε_lt1] Htr Hbody.
  apply (type_soundness_credit_gen tr post ε Hε_pos e σ n _
           Hσ Hε_lt1 Htr Hbody).
  intros HlrustGS.
  exact (wp_refRcoupl_safety 1 (mknonnegreal ε Hε_pos) e σ n
           (λ _ : language.val lrust_prob_lang, True)).
Qed.

(** [type_soundness_credit] in probability form: after [n] steps the
    program is a value or can take another step, with probability at
    least [1 - ε]. *)
Theorem type_soundness_credit_not_stuck `{!typePreG Σ}
    {𝔅 : syn_type}
    (tr : predl_trans' [at_locₛ (trackedₛ unitₛ)] 𝔅)
    (post : pred' (~~𝔅))
    (ε : R)
    (e : language.expr lrust_prob_lang) (σ : language.state lrust_prob_lang) n :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  (0 <= ε < 1)%R →
  (∀ l : loc, tr post -[(l, ())] ⊤) →
  (∀ `{!typeG Σ, !cnaInv_logicG Σ} (l : loc),
      ⊢ typed_body (𝔄l := [at_locₛ (trackedₛ unitₛ)]) (𝔅 := 𝔅) [] []
                   (InvCtx [] static AtomicClosed) []
                   +[#l ◁ error_credit_ty ε] e tr) →
  (probp (pexec n (e, σ)) (λ ρ, is_final ρ ∨ reducible ρ) >= 1 - ε)%R.
Proof.
  intros Hσ Hε Htr Hbody.
  rewrite pexec_safety_relate.
  apply (type_soundness_credit tr post ε e σ (S n) Hσ Hε Htr Hbody).
Qed.
