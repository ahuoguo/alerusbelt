(** Termination adequacy for the later-free stack.

    [lang/total_adequacy.v]'s [lrust_twp_tgl] runs the *partial* heap: it
    allocates [timeGS] and the superlinear later-credit budget that the
    guarded heap rules spend.  Here neither exists.  The caller instead
    supplies the formula language's two interpretations ([NaSem],
    [HeapSem]) once the ghost names are in hand, together with a world
    satisfaction containing [na_wsat] - exactly the shape of Nola's
    [lrust_total] ([nola/verus_halt/lang/adequacy.v]), with eris's
    quantitative conclusion in place of [sn erased_step]. *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import base proofmode.
From iris.algebra Require Import auth.
From clutch.base_logic Require Export error_credits.
From clutch.eris Require Import weakestpre total_weakestpre.
From clutch.prob Require Import distribution graded_predicate_lifting.
From nola.bi Require Import modw guard.
From nola.verus_halt Require Import na_inv_fork.
From nola.verus_halt.util Require Import atomic_lock_counter.
From lrust.util Require Import total_cell_map.
From lrust.lang Require Export lang total_heap total_wsat total_lifting_heap
                               total_adequacy.
Set Default Proof Using "Type".
Import uPred ModwNotation GuardNotation TglWpwNotation.

Local Open Scope R.

(** Everything needed to allocate an [lrustTotGS] from scratch. *)
Class lrustTotGpreS (FML : oFunctor) (Σ : gFunctors) : Type := LRustTotGpreS {
  #[global] lrustTotGpreS_inv :: invGpreS Σ;
  #[global] lrustTotGpreS_na_inv :: na_invG Σ;
  #[global] lrustTotGpreS_alc :: alc_logicG Σ;
  #[global] lrustTotGpreS_heap :: inG Σ (authR total_heap.heapUR);
  #[global] lrustTotGpreS_heap_freeable ::
    inG Σ (authR total_heap.heap_freeableUR);
  #[global] lrustTotGpreS_na_logic :: na_logicG loc val FML Σ;
  #[global] lrustTotGpreS_ec :: ecGpreS Σ;
}.

(** Nola's [lrustΣ], plus [ecΣ] for eris's error credits. *)
Definition lrustTotΣ FML `{!oFunctorContractive FML} : gFunctors :=
  #[invΣ; na_invΣ; alc_logicΣ;
    GFunctor (constRF (authR total_heap.heapUR));
    GFunctor (constRF (authR total_heap.heap_freeableUR));
    na_logicΣ loc val FML; ecΣ].
Global Instance subG_lrustTotGpreS {FML Σ} `{!oFunctorContractive FML} :
  subG (lrustTotΣ FML) Σ → lrustTotGpreS FML Σ.
Proof. solve_inG. Qed.

(** Allocate the heap on the empty state, with the interpretation left
    open; Nola's [heap_init]. *)
Lemma total_heap_init `{!lrustTotGpreS FML Σ, !invGS_gen HasLc Σ} :
  ⊢ |==> ∃ hGS : total_heap.heapGS FML Σ,
      ∀ naS : NaSem FML Σ, total_heap.heap_ctx ∅.
Proof.
  iMod non_atomic_map_alloc_empty_any as (vγ) "Hna".
  iMod (own_alloc (● (∅ : total_heap.heap_freeableUR))) as (fγ) "Hf";
    first by apply auth_auth_valid.
  iMod na_alloc as (tp) "Hpool".
  iMod atomic_lock_ctr_alloc as (lcγ) "Hctr". iModIntro.
  iExists (total_heap.HeapGS _ _ _ _ _ vγ fγ tp lcγ). iIntros (naS).
  iExists ∅. iFrame "Hf Hctr Hpool". iSplit; [by iApply "Hna"|].
  iPureIntro. by move=> ??.
Qed.

(** The headline for the later-free stack. *)
Theorem lrust_tot_mass_lim_exec `{!lrustTotGpreS FML Σ}
    (e : common.language.expr lrust_prob_lang) (ε : R) (K : nat) :
  (0 <= ε)%R →
  (∀ (iG : invGS_gen HasLc Σ) (hGS : total_heap.heapGS FML Σ) (eG : ecGS Σ),
     ⊢ £ K -∗ ↯ ε -∗ |={⊤}=>
       ∃ nhS : {naS : NaSem FML Σ & total_heap.HeapSem FML Σ},
         let _ : lrustTotGS FML Σ :=
           LRustTotGS FML Σ iG _ _ hGS (projT1 nhS) (projT2 nhS) eG in
         ∃ W, W ∗ WP[W] e [{ _, True }]) →
  (1 - ε <= SeriesC (lim_exec (e, ∅)))%R.
Proof.
  intros Hε Htwp. eapply tgl_termination_ineq.
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
  iMod total_heap_init as (Hheap) "Hctx".
  iMod (Htwp Hinv Hheap Hec with "H£ Hf") as ([naS hS]) "H".
  iDestruct "H" as (W) "[HW Hwp]".
  iDestruct ("Hctx" $! naS) as "Hctx".
  pose (HlrustTotGS := LRustTotGS FML Σ Hinv _ _ Hheap naS hS Hec).
  change ε with (nonneg ε').
  iPoseProof (twp_step_fupd_tgl (Σ:=Σ)
                (erisWpGS0 := @ErisW _ Σ (@lrustTotGS_erisWpGS' FML Σ HlrustTotGS) W)
                0 e ∅ ε' (λ _, True)) as "Hadq".
  iSpecialize ("Hadq" with "[-]"); last iApply "Hadq".
  iFrame "HW Hctx Hs". destruct twp_default. iExact "Hwp".
Qed.
