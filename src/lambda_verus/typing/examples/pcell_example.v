(** VerusBelt's PCell example, ported prophecy-free.

    What changed relative to upstream:

    - the predicate transformers lose their [proph_asn] argument;
    - the [&uniq] creation step ([type_uniqbor_instr], borrow.v) no
      longer constrains the value handed back when the lifetime dies, and
      [Share] ([type_share_instr]) no longer carries the
      "current = final" side condition that came from resolving the
      borrow;
    - the assignment rule has no [resolve'] premise (but does have
      [StackOkay] / [ty_size = 1] premises);
    - [type_endlft] only unblocks, it does not resolve;
    - safety is stated as [SeriesC (pexec n …) = 1] (plus the pointwise
      progress corollary) rather than [rtc erased_step] plus data-race
      freedom. *)
From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs bool own cont uninit pcell product_split borrow.
From lrust.typing Require Export soundness.
From clutch.prob Require Import distribution.
From lrust.typing.examples Require Import assert.
From lrust.lang Require Import lang notation.
Set Default Proof Using "Type".

Section pcell_example.
  Context `{!typeG Σ, !cnaInv_logicG Σ}.

  (*
  VerusBelt corresponding to the following simple Verus program:

  ```
  use vstd::prelude::*;
  use vstd::cell::pcell::*;

  verus!{

    fn pcell_example() {
        let pcell_pair = PCell::new(17);
        let pcell = pcell_pair.0;
        let Tracked(pointsto) = pcell_pair.1;

        let pcell_shr_ref = &pcell;
        let tracked pointsto_shr_ref = &pointsto;

        let intref = pcell_shr_ref.borrow(Tracked(pointsto_shr_ref));
        let x = *intref;

        assert(x == 17);
    }

  }
  ```

  The example illustrates:
    * Using PCell
    * Basic borrowing rules
    * Function call (to assert).  (The assert we use in this program is excecutable, so it's more like `assert_unchecked` than it's like the Verus specification assert.)
  *)
  
  Definition pcell_example : val :=
    fn: [] :=
      let: "p" := new [ #1 ] in   (* p : box int *)
      let: "int_init" := #17 in
      "p" <- "int_init" ;; (* write 17 *)
      let: "pcell_pair" := (PCellFromOwn ["p"]) in (* pcell_pair : box (PCell<int>, CellPointsTo) *)
      let: "pcell" := "pcell_pair" +ₗ #0 in
      let: "pointsto" := "pcell_pair" +ₗ #1 in
      
      (* There's no way to go straight to a shared borrow in VerusBelt;
         we create a unique borrow first, then turn it into a shared one. *)
      Newlft;;
      let: "pcell_uniq_ref" := UniqBor in
      let: "pcell_shr_ref" := Share in (* borrow pcell *)
      
      Newlft;;
      let: "pointsto_uniq_ref" := UniqBor in
      let: "pointsto_shr_ref" := Share in (* borrow pointsto *)
      
      (* borrow and read *)
      let: "intref" := PCellBorrow ["pcell"; "pointsto"] in
      let: "x" := !"intref" in
      
      (* compute x == 17 *)
      let: "seventeen" := #17 in
      let: "b" := ("x" = "seventeen") in
      letalloc: "b'" <- "b" in
      (* call assert *)
      let: "assert" := assert_fn in
      letcall: "assert_ret" := "assert" ["b'"] in
      
      Endlft;;
      Endlft;;
      
      (* return unit *)
      let: "r" := new [ #0] in return: ["r"].
      
  
  (* We're going to use VerusBelt to prove the `pcell_example` function
     correct with a trivial precondition, that is, we show it is always safe to execute.
     
     In the comments, we discuss how this proof corresponds to what Verus actually does.
  *)
  Lemma pcell_example_type :
    typed_val
        pcell_example
        ((fn(∅) → ()) (λ (c: ~~ ()) 𝛷 '-[] , λ mask, ∀ l, 𝛷 (l, ()) mask))
        (pcell_example, ()).
  Proof.
    unfold pcell_example. unlock.
    opose proof (@type_fn
        _ _ _ ()
        []
        ()
        ()
        ()
        (λ y: (), FP ∅ +[] () AtomicClosed)
        (λ (c: ~~ ()) 𝛷 '-[] , λ mask, ∀ l, 𝛷 (l, ()) mask)
        (_)%E
        [] _ _ _
    ) as H.
    unlock in H. apply H. clear H.
    intros c ϝ k wl.
    destruct wl. simpl_subst.
    
    (* The first part corresponds to the type-checking; this part is done by rustc. *)
    
    iApply (typed_body_impl with "[]"); last first. {
    
    iApply (type_new 1 with "[]"). { lia. } iIntros (v_p). simpl_subst.
    iApply type_int. iIntros (v_int_init). simpl_subst.
    iApply type_assign. { solve_typing. } { apply uninit_stack_okay. }
        { apply int_stack_okay. } { done. } { apply write_own; trivial. }
    iApply (type_let with "[]").
      { apply (typed_pcell_from_own _ int). }
      { solve_typing. } { reflexivity. } iIntros (v_pcell_pair). simpl_subst.
      
    iApply typed_body_tctx_incl. { apply tctx_incl_swap. }
    iApply typed_body_tctx_incl. { eapply tctx_incl_tail. apply tctx_split_own_prod. }
    iApply type_letpath. { solve_typing. } iIntros (v_pcell). simpl_subst.
    iApply type_letpath. { solve_typing. } iIntros (v_pointsto). simpl_subst.
    
    iApply (type_newlft []). iIntros (κ1).
    iApply (type_let with "[]").
      { eapply (type_uniqbor_instr _ _ _ _ _ (pcell_ty 1) κ1).
        - apply (lctx_lft_alive_local _ _ κ1 []). { apply elem_of_cons; left; trivial. } done.
        - solve_typing.
      }
      { solve_typing. } { reflexivity. }
      iIntros (v_pcell_uniq_ref). simpl_subst.
    iApply (type_let with "[]").
      { eapply (type_share_instr _ κ1 (pcell_ty 1)).
        apply (lctx_lft_alive_local _ _ κ1 []). { apply elem_of_cons; left; trivial. } done.
      }
      { solve_typing. } { reflexivity. }
      iIntros (v_pcell_shr_ref). simpl_subst.
      
    iApply (type_newlft []). iIntros (κ2).
    iApply (type_let with "[]").
      { eapply (type_uniqbor_instr _ _ _ _ _ (cell_points_to_ty int) κ2); solve_typing. }
      { solve_typing. } { reflexivity. }
      iIntros (v_pointsto_uniq_ref). simpl_subst.
    iApply (type_let with "[]").
      { eapply (type_share_instr _ κ2 (cell_points_to_ty int)). solve_typing.
       (* apply (lctx_lft_alive_local _ _ κ2 []). { apply elem_of_cons; left; trivial. } done.*)
      }
      { solve_typing. } { reflexivity. }
      iIntros (v_pointsto_shr_ref). simpl_subst.
    
    iApply (type_let with "[]").
      { eapply (typed_pcell_borrow (κ1 ⊓ κ2) v_pcell v_pointsto int). }
      { solve_typing. } { reflexivity. }
    
    iIntros (v_intref). simpl_subst.
    
    iApply (type_let with "[]").
      { eapply (type_deref_instr (𝔅 := Zₛ) _ (int)); trivial.
        * apply int_stack_okay.
        * apply (read_shr int (κ1 ⊓ κ2)). { apply int_copy. } { solve_typing. }
      }
      { solve_typing. } { reflexivity. }
      
    iIntros (v_x). simpl_subst.
    
    iApply type_int. iIntros (v17). simpl_subst.
    iApply type_int_eq. { solve_typing. } iIntros (v_eq). simpl_subst.
    iApply (type_letalloc_1 bool_ty). { solve_typing. } { done. }
    iIntros (v_b'). simpl_subst.
        
    iApply type_let. { apply assert_type. } { solve_typing. } { reflexivity. }
    iIntros (v_assert). simpl_subst.
    
    iApply (@type_letcall Σ typeG0 cnaInv_logicG0 () [boolₛ] () () _ _ _ ()
        (λ (p: ()), FP ∅ +[bool_ty] () AtomicClosed)).
      { solve_typing. } { apply lctx_ictx_alive_nil. solve_typing. }
      { solve_typing. } { solve_typing. }
    iIntros (v_assert_ret). simpl_subst.
    
    iApply (type_endlft _ _ _ κ2). {
      repeat (eapply unblock_tctx_cons_just). eapply unblock_tctx_nil.
    }
    iApply (type_endlft _ _ _ κ1). {
      repeat (eapply unblock_tctx_cons_just). eapply unblock_tctx_nil.
    }
    
    iApply (type_new_subtype () 0). { lia. } { apply uninit_unit_1. }
    iIntros (v_unit_ret). simpl_subst.
    
    iApply type_jump.
      { rewrite list_elem_of_singleton. reflexivity. }
      { solve_typing. }
      { reflexivity. }
   }
      
   Unshelve.
   2: { eapply (composeₛ empty_prod_to_unitₛ uninit0_to_unitₛ). }

   (* Now that we've type-checked it, we're effectively left with a predicate
      from the cumulative predicate transformers; it loosely corresponds to the
      weakest-precondition predicate that Verus would construct in its VC gen.
      Verus would then use Z3 to dispatch the obligations; we do it in Rocq. *)
   intros post [] mask.
   intros Ha.
   unfold trans_upper, trans_tail. simpl.
   intros l junk z ->. simpl.
   intros cell_ids m b Hm1 Hm2 m0 b0 Hm01 Hm02.
   rewrite Hm02. simpl.
   (* proof obligation 1: the two cell-id sets agree (precondition of the
      PCell borrow) *)
   split; [exact Hm2|].
   intros z0 Hz0 l2.
   (* proof obligation 2: 17 = 17, the precondition of the assert *)
   split; [done|].
   intros ret xl' Hxl' xl'0 Hxl'0 l1 junk2. apply Ha.
  Qed. (* long Qed *)
   
End pcell_example.

(** Instantiate the closed-program soundness theorem.  Upstream states
    this with [rtc erased_step] and a data-race-freedom conjunct; the eris
    port states safety as "the [n]-step partial-execution distribution
    keeps all its mass", equivalently "every reachable configuration is a
    value or reducible" (see [typing/soundness.v]). *)
Theorem pcell_example_executes_without_getting_stuck `{!typePreG Σ}
    (σ : language.state lrust_prob_lang) (n : nat) :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  SeriesC (pexec n (pcell_example [exit_cont]%E, σ)) = 1%R.
Proof.
  intros Hσ. apply (type_soundness_main _ (pcell_example, ())); [done|].
  intros typeG0 cnaInv_logicG0. apply pcell_example_type.
Qed.

Corollary pcell_example_progress `{!typePreG Σ}
    (σ : language.state lrust_prob_lang) (n : nat) :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  ∀ ρ, (pexec n (pcell_example [exit_cont]%E, σ) ρ > 0)%R →
       is_final ρ ∨ reducible ρ.
Proof.
  intros Hσ. apply (type_soundness_main_progress _ (pcell_example, ())); [done|].
  intros typeG0 cnaInv_logicG0. apply pcell_example_type.
Qed.
