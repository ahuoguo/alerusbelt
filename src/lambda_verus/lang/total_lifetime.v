(** The later-free lifetime logic over eris's total weakest precondition.

    Stage 2 of [PLAN-TOTAL-ERIS.md] needed no porting.  Nola's
    [verus_halt/lifetime/] - the whole of LeLiLo rebuilt later-free, 13
    files and 10,516 lines - mentions no language and no weakest
    precondition: it is parametric in a formula language [FML], its
    interpretation [BorSem], and a world satisfaction.  So it is used as
    it stands, and all that is left is to check that it *composes* with
    the stack of [total_lifting_heap.v].

    This file is that check.  Three things:

    - [llft_wsatG] is [llft_WG ∗ shr_wsat ∗ box_wsat bor_sem ∗
      llft_inv_main], so taking the lifetime logic's ambient world [llft_WG]
      to be the cell logic's [na_wsat] puts the heap inside the lifetime
      logic's world satisfaction.  [WsatIncl llft_wsat na_wsat _] then
      holds, which is what the guarded heap rules ask for.

    - Hence [twp_read_guarded_cells] runs at [WP[llft_wsat]]: a guarded
      read under the lifetime logic's world satisfaction, with no later
      credit.

    - And a borrow still behaves: [llftl_borrow_shared] hands out a guard
      over [llft_wsatG], with no [▷], where this tree's partial
      [lifetime/lifetime_full.v] gives [&{κ} P ⊢ … ▷ P …].

    What is *not* here is a program that reads through a borrow.  That is
    not a language-level rule in this design: the lifetime logic's own
    guards live over [llft_wsatG] and carry the borrow bookkeeping, while
    a heap read consumes a guard over [na_wsat] which the *type*
    interpretation produces.  Joining them is Stage 3's business, exactly
    as in [nola/verus_halt/typing/programs.v]. *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Export error_credits.
From clutch.eris Require Export total_weakestpre.
From nola.bi Require Import modw guard.
From nola.iris Require Import sinv guard iprop.
From nola.verus_halt Require Import boxes.
From nola.verus_halt.lifetime Require Import ra inv lifetime_full.
From lrust.util Require Import total_cell_map.
From lrust.lang Require Export lang total_heap total_wsat total_lifting_heap.
Set Default Proof Using "Type".
Import ModwNotation GuardNotation TglWpwNotation iPropAppNotation.

Section compose.
  Context `{!lrustTotGS FML Σ, !llft_logicGS Σ, !LlftBorNames Σ, !boxG Σ,
            !sinvGS FML Σ, !BorSem FML Σ}.

  (** The lifetime logic's ambient world is the cell logic's: this is the
      single line that puts the heap inside the lifetime logic. *)
  Local Instance llftWG_na : LlftWG Σ :=
    LlftWGS Σ sinv_name na_wsat unit (λ _, emp)%I.

  (** [na_wsat] is then a component of the lifetime logic's world
      satisfaction, and Nola's [WsatIncl] instances find it by themselves:
      [llft_wsat = llft_wsatG ∗ llft_inv_other] and
      [llft_wsatG = na_wsat ∗ shr_wsat ∗ box_wsat bor_sem ∗ llft_inv_main].
      That is what the guarded heap rules ask for. *)

  (** A guarded heap read under the lifetime logic's world satisfaction,
      with no later credit.  Compare [lang/lifting.v]'s
      [wp_read_guarded_cell], whose precondition carries [£ d]. *)
  Lemma twp_read_guarded_llft s E l c v (G : iProp Σ) Φ :
    (G &&{na_wsat}&&> total_heap.heap_mapsto_cells_fancy l c
                        (total_heap.FVal v)) -∗ G -∗ (G -∗ Φ v) -∗
    WP[llft_wsat] Read (Lit (LitLoc l)) @ s; E [{ Φ }].
  Proof. iApply twp_read_guarded_cells. Qed.

  (** And the same for a write. *)
  Lemma twp_write_guarded_llft s E (l : total_heap.cloc1) e v v'
      (Gx : FML $oi Σ) Φ :
    IntoVal e v' →
    (na_sem Gx &&{na_wsat}&&> total_heap.heap_complete_mapsto l) -∗
    na_sem Gx -∗ total_heap.heap_complete_mapsto_fancy l (total_heap.FVal v) -∗
    (na_sem Gx -∗
       total_heap.heap_complete_mapsto_fancy l (total_heap.FVal v') -∗
       Φ (LitV LitPoison)) -∗
    WP[llft_wsat] Write (Lit (LitLoc l.1)) e @ s; E [{ Φ }].
  Proof. apply twp_write_guarded. Qed.

  (** Sampling, and the error-credit rule, under the same world. *)
  Lemma twpw_rand_exp_nat_llft z (ε1 : R) (ε2 : nat → R) E Φ :
    (0 < z)%Z →
    (∀ n, (0 <= ε2 n <= 1)%R) →
    (SeriesC (λ n : nat,
        if bool_decide (n < Z.to_nat z)%nat
        then (1 / Z.to_nat z) * ε2 n else 0)%R <= ε1)%R →
    ↯ ε1 -∗
    (∀ n : nat, ⌜(n < Z.to_nat z)%nat⌝ ∗ ↯ (ε2 n) -∗
                Φ (LitV (LitInt (Z.of_nat n)))) -∗
    WP[llft_wsat] Rand (Lit (LitInt z)) @ E [{ Φ }].
  Proof. apply twpw_rand_exp_nat. Qed.

  (** The borrow rules themselves are not restated here - they are
      imported, and restating them would only duplicate Nola.  For the
      record, these are the two that matter, and neither side is delayed:

        llftl_borrow_shared κ Px :
          bor_sem Px -∗ |=[llft_wsatG]=>
            (@[κ] &&{llft_wsatG}&&> bor_sem Px) ∗
            ([†κ] -∗ |=[llft_wsatG]=> bor_sem Px)

        llftl_bor_acc E Px κ :
          llft_ctx -∗ &{κ} Px -∗ @[κ] -∗ |=[llft_wsat]{E}=>
            bor_sem Px ∗ (∀ Qx, … -∗ bor_sem Qx -∗
                                 |=[llft_wsat]=> (&{κ} Qx) ∗ @[κ])

      against this tree's partial [lifetime/lifetime_full.v]:

        llftl_borrow : ▷ P ={E}=∗ (… &&{↑NllftG}&&> ▷ P) ∗ ([†κ] ={E}=∗ ▷ P)
        llftl_bor_acc : … ={E}=∗ (▷ P) ∗ (∀ Q, ▷ (▷ Q ∗ [†κ] ={…}=∗ ▷ P) ∗
                                               ▷ Q ={↑Nllft}=∗ (&{κ} Q) ∗ @[κ])

      Their full statements carry the semantic interfaces [StBor],
      [StBorSem], [BorStateFml] that only [typing/model.v] instantiates,
      which is why they are quoted rather than wrapped. *)

End compose.
