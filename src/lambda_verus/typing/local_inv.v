From lrust.typing Require Export type.
From lrust.typing Require Import type_context programs programs_util_own own ghost tracked shr_bor product.
From guarding Require Import guard tactics.
From guarding.lib Require Import cancellable.
From lrust.lifetime Require Import lifetime_full.
From iris.algebra Require Import dfrac_agree.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section na_dg_agree_util.
  Context `{!typeG Σ, !cnaInv_logicG Σ}. 
  
  Local Definition dg_tok γ (k: nat) : iProp Σ :=
      own γ (to_frac_agree (A:=leibnizO (nat)) (1/2)%Qp k).
  
  Local Lemma dg_tok_alloc k :
      ⊢ |==> ∃ γ, dg_tok γ k ∗ dg_tok γ k.
  Proof.
      unfold dg_tok.
      iMod (own_alloc
          (to_frac_agree (A:=leibnizO (nat)) (1 / 2) k ⋅ to_frac_agree (A:=leibnizO (nat)) (1 / 2) k)) as (γ) "[Ho Ho2]".
        - rewrite frac_agree_op_valid. rewrite Qp.half_half. split; trivial.
        - iModIntro. iExists γ. iFrame.
  Qed.
      
  Local Lemma dg_tok_agree γ k1 k2 :
      dg_tok γ k1 -∗ dg_tok γ k2 -∗ ⌜k1 = k2⌝.
  Proof.
    unfold dg_tok. iIntros "A B". iCombine "A B" as "H".
    iDestruct (own_valid with "H") as "%v".
    iPureIntro. rewrite dfrac_agree_op_valid in v. intuition.
  Qed.
      
  Local Lemma dg_tok_update γ (k1 k2 k : nat) :
      dg_tok γ k1 -∗ dg_tok γ k2 ==∗ dg_tok γ k ∗ dg_tok γ k.
  Proof.
    unfold dg_tok. iIntros "A B". iCombine "A B" as "H". rewrite <- own_op.
    iDestruct (own_update with "H") as "H"; last by iFrame "H".
    apply frac_agree_update_2. apply Qp.half_half.
  Qed.
End na_dg_agree_util.

Section local_invariants.
  Context `{!typeG Σ, !cnaInv_logicG Σ}. 

  (*
  In Verus, the AtomicInvariant is parameterized as:

  ```
  AtomicInvariant<K, V, Pred>`
  where Pred: InvariantPredicate<K, V>
  ```

  The `K` here is given by `ℭ`, the V by `ty: type 𝔄`. The trait bound is given by the `pred`.
 
  We use `abstracted_syn_type` for the predicate since it needs to be independent of the thread id.
  *)

  Program Definition local_inv_ty {𝔄 ℭ} (ty: type 𝔄) (pred: abstracted_syn_type 𝔄 → ~~ℭ → Prop) : type (local_invₛ ℭ) := ({|
    ty_size := 0;
    ty_lfts := [];
    ty_E := [];
    ty_gho_pers x d g tid := True%I ;
    ty_gho x d g tid := match x with (N, (γ, γt, d1), c) =>
        cna_active γ
          ∗ (⌜d1 < d⌝ ∗ dg_tok γt d1)
          ∗ cna_inv γ tid N (∃ x' d' g' d1 ,
            dg_tok γt d1 ∗
            (*
            The story with the depth parameters is a little complicated here. The problem is that
            d' can increase arbitrarily when the invariant is opened and closed.
            The straightforward solution is to put £(d') credit in here. However, this would
            still be a problem for Send, since when we open the invariant to change the tid,
            we would have to use up the credits with no way to refresh them.

            Our solution is to have the credits *make up the difference* between d and d'.
            Then when we do a Send, we have to update the outer d, bringing the difference to 0.
            (Yes, this complicates the definition of Send significantly.)
            Updating the outer d requires the time credits.

            (The time credits are the important thing. We technically don't even need the £ credits, 
            since we could just generate them when we need them, at the point where we transform
            the ⧗ into ⧖.  It seems slightly simpler to have the £ credits here, though.)
            *)
            ⧖(S d' `max` g') ∗
            ⧗(d' - d1) ∗
            £(d' - d1) ∗
            ty.(ty_gho) x' d' g' tid ∗ ⌜pred (syn_abstract x') c⌝)
    end;
    ty_phys x tid := [];
  |})%I.
  Next Obligation. done. Qed. 
  Next Obligation. done. Qed. 
  Next Obligation. done. Qed. 
  Next Obligation.
    destruct x as [[N [[γ γt] d1]] c].
    iIntros (tid Hineq Hineq2) "[A [[%B B'] C]]". iFrame "A". iFrame "C". iFrame "B'".
    iSplit. { iPureIntro. lia. }
    iIntros "[A [[%B1 B1'] C]]". iFrame. done.
  Qed.
  Next Obligation. iIntros. done. Qed.
  (* [ty_guard_proph] obligation elided: prophecy stripped. *)
  Next Obligation. iIntros. done. Qed.
  
  Program Definition local_closer_ty {𝔄 ℭ} (κ: lft) (ty: type 𝔄) (pred: (abstracted_syn_type 𝔄) → ~~ℭ → Prop) : type (local_invₛ ℭ) := ({|
    ty_size := 0;
    ty_lfts := [];
    ty_E := [];
    ty_gho_pers x d g tid := True%I ;
    ty_gho x d g tid := match x with (N, (γ, γt, d1), c) =>
        dg_tok γt d1 ∗
        cna_closer κ tid N (∃ x' d' g' d1 ,
            dg_tok γt d1 ∗
            ⧖(S d' `max` g') ∗
            ⧗(d' - d1) ∗
            £(d' - d1) ∗
            ty.(ty_gho) x' d' g' tid ∗ ⌜pred (syn_abstract x') c⌝)
    end;
    ty_phys x tid := [];
  |})%I.
  Next Obligation. done. Qed. 
  Next Obligation. done. Qed. 
  Next Obligation. done. Qed. 
  Next Obligation. iIntros. iFrame. iIntros. done. Qed.
  Next Obligation. iIntros. done. Qed.
  (* [ty_guard_proph] obligation elided: prophecy stripped. *)
  Next Obligation. iIntros. done. Qed.
  
  (** [local_inv_ty_send] removed: [Send]'s [send_change_tid] field
      is elided (concurrency is not modelled). *)

  (* [local_inv_ty_resolve] removed along with [resolve]. *)

  Lemma typed_local_inv_alloc {𝔄 ℭ} (p1 p2 : path) (ty : type 𝔄) (pred: (abstracted_syn_type 𝔄) → ~~ℭ → Prop) (tyCN : type (ℭ * namespaceₛ)) E L I :
    typed_inv_instr E L I
      +[p1 ◁ own_ptr 0 (ghost_ty tyCN);
        p2 ◁ own_ptr 0 ty
       ]
      (Seq Skip Skip) I
      (const +[p2 ◁ own_ptr 0 (local_inv_ty ty pred)])
      (λ post '-[(_, (c, N)); (_, v)], λ mask, pred (syn_abstract v) c ∧ ∀ l γ, post -[(l, (N, γ, c))] mask).
  Proof.
    apply typed_instr_of_skip_own2_own. { trivial. } { trivial. }
    intros l1 l2 x1 x2 d tid post mask iκs.
    iIntros "#LFT #TIME #UNIQ #E L I1 Gho Tra %Obs #⧖ £".
    destruct x1 as [c ns].
    destruct Obs as [Sat Obs].
    iMod (dg_tok_alloc d) as (γt) "[tok1 tok2]".
    iMod (cumulative_time_receipt_0) as "⧗0".
    iMod (lc_zero) as "£0".
    iMod (cna_alloc tid ns with "[Tra tok1 ⧗0 £0]") as (γ) "[inv active]"; last first.
     - iModIntro. iExists (ns, (γ, γt, d), c). iFrame. iSplit; first by (iPureIntro; lia).
       iPureIntro. apply Obs.
     - iNext. iExists x2, d, (S d). iFrame.
       iSplit. { iApply (persistent_time_receipt_mono with "⧖"). lia. }
       replace (d - d) with 0 by lia. iFrame.
       iPureIntro. exact Sat.
  Qed.
  
  Lemma typed_local_inv_destroy {𝔄 ℭ} (p : path) (ty : type 𝔄) (pred: (abstracted_syn_type 𝔄) → ~~ℭ → Prop) E L I :
    lctx_ictx_alive E L I →
    typed_instr E L I
      +[p ◁ own_ptr 0 (local_inv_ty ty pred)]
      (Seq Skip Skip)
      (const +[p ◁ own_ptr 0 (tracked_ty ty)])
      (λ post '-[(_, (N, γ, c))], λ mask, ∀ l v, pred (syn_abstract v) c → post -[(l, v)] mask).
  Proof.
    intros Halive. apply typed_instr_of_skip_own_own_t. { trivial. } { trivial. }
    intros l [[ns [[γ γt] d0]] c] d tid iκs post mask.
    iIntros "#LFT #TIME #UNIQ #E L I (active & [%Hineq tok] & #inv) %Obs #⧖ ⧗".
    destruct I as [Il ϝ'].
    (*iAssert (∀ κ : lft, ⌜κ ∈ invctx_to_multiset Il⌝ -∗ llctx_interp L &&{ ↑NllftG }&&> @[κ])%I as "#Alive". {
      iIntros (κ) "%Hin". destruct Halive as [Halive1 Halive2].
      rewrite /invctx_to_multiset elem_of_list_to_set_disj in Hin.
      iDestruct (Halive2 _ Hin with "L E") as "X". iFrame.
    }*)
    
    iDestruct "I" as (na_mask at_mask) "[%Hm [[cna_lft #ϝincl] Irest]]".
    
    iAssert (∀ κ : lft, ⌜κ ∈ invctx_to_multiset Il ⊎ list_to_set_disj iκs⌝ -∗ llctx_interp L &&{ ↑NllftG }&&> @[κ])%I as "#Alive". {
      iIntros (κ) "%Hin". destruct Halive as [Halive1 Halive2].
      rewrite gmultiset_elem_of_disj_union in Hin.
      destruct Hin as [Hin|Hin].
        - rewrite /invctx_to_multiset elem_of_list_to_set_disj in Hin.
          iApply (Halive2 _ Hin with "L E").
        - rewrite elem_of_list_to_set_disj in Hin.
          iDestruct (Halive1 with "L E") as "#Incl".
          iDestruct (guards_transitive with "Incl ϝincl") as "Incl2".
          iApply (guards_transitive with "Incl2 []").
          iApply (lft_intersect_list_elem_of_incl _ _ Hin).
    }
        
    iMod (cna_destroy with "inv cna_lft active Alive L") as "[I [L P]]". { set_solver. }
    iMod (bi.later_exist_except_0 with "P") as (x'' d' g' d00) "[>tok2 [>⧖' [>⧗' [>£ [gho >%Hpred]]]]]".
    iMod (cumulative_persistent_time_receipt with "TIME ⧗ ⧖'") as "#⧖'". { set_solver. }
    iModIntro. iExists (S d' `max` g'), x''. 
    iFrame. iFrame "#".
    iDestruct (ty_gho_depth_mono with "gho") as "[$ _]". { lia. } { lia. }
    iSplit. { done. }
    iPureIntro. apply Obs. trivial.
  Qed.
  
  Local Lemma mask_lemma (na_mask at_mask X : coPset) :
      na_mask ∪ at_mask = ⊤ →
      X ⊆ na_mask ∩ at_mask →
      (na_mask ∖ X) ∪ at_mask = ⊤.
  Proof.
    move=> eq sub. apply leibniz_equiv, set_equiv_subseteq. split=>//. 
    rewrite -eq. etrans; [|by apply union_mono_r, difference_mono_l].
    move=> a /elem_of_union[?|?]; [|set_solver].
    case (decide (a ∈ at_mask)); set_solver.
  Qed.
  
  Lemma typed_local_inv_open {𝔄 ℭ} (p : path) (ty : type 𝔄) (pred: (abstracted_syn_type 𝔄) → ~~ℭ → Prop) E L Il ϝ 𝛼 κ :
    lctx_lft_alive E L κ →
    lctx_ictx_alive E L (InvCtx Il ϝ 𝛼) →
    typed_inv_instr E L
      (InvCtx Il ϝ 𝛼)
      +[p ◁ own_ptr 0 (tracked_ty (&shr{κ} (local_inv_ty ty pred)))]
      (Seq Skip Skip)
      (InvCtx (InvCtx_open κ :: Il) ϝ 𝛼)
      (const +[p ◁ own_ptr 0 (tracked_ty ty * local_closer_ty κ ty pred)])
      (λ post '-[(_, (_, (N, γ, c)))], λ mask, (↑N ⊆ mask) ∧ ∀ l v γ', pred (syn_abstract v) c → post -[(l, (v, (N, γ', c)))] (mask ∖ ↑N)).
  Proof.
    intros Halive HaliveI. apply typed_inv_instr_of_skip_own_own_t. { trivial. } { trivial. }
    intros l [l1 [[ns [[γ γt] d0]] c]] d tid iκs post mask.
    iIntros "#LFT #TIME #UNIQ #E L I shrgho %Obs #⧖ ⧗ £".
    iDestruct (lc_weaken (_ + _)%nat with "£") as "[£1 £2]"; first last.
    {
    destruct d as [|d]; first by done.
    iDestruct "shrgho" as "[_ [#KguardsGho _]]".
    iDestruct (Halive with "L E") as "#LguardsK".
    iDestruct (guards_transitive_right with "LguardsK KguardsGho") as "LguardsGho".
    
    leaf_open_laters "LguardsGho" with "L" as "Open". { set_solver. }
    iMod (lc_fupd_elim_laterN with "£1 Open") as "Open".
    iMod "Open" as "[[a [tok #inv]] back]".
    iMod ("back" with "[a tok]") as "L". { iFrame. iFrame "#". }
    
    leaf_hyp "KguardsGho" rhs to (cna_active γ) as "KguardsActive".
      { leaf_by_sep. iIntros "(? & ?)". iFrame. iIntros. done. }
    
    destruct Obs as [Sat Obs].
    
    iDestruct "I" as (na_mask at_mask) "[%Hm [[Ilifetimes ϝIncl] [Iown Iat]]]".
    iMod (cna_inv_acc_with_lifetime_guard with "inv Iown Ilifetimes LguardsK £2 KguardsActive L") as "[Iown [Ilifetimes [L [P Closer]]]]". { set_solver. } { set_solver. }
    
    iMod (bi.later_exist_except_0 with "P") as (x'' d' g' d1) "[>tok2 [>⧖' [>⧗' [>£ [gho >%Hpred]]]]]".
    iMod (cumulative_persistent_time_receipt with "TIME ⧗ ⧖'") as "#⧖'". { set_solver. }
    iModIntro. iExists (S d' `max` g'), (x'', (ns, (γ, γt, d1), c)). iExists (mask ∖ ↑ns).
    iFrame.
    iSplit. { iApply (persistent_time_receipt_mono with "⧖'"). lia. }
    iDestruct (ty_gho_depth_mono with "gho") as "[$ _]". { lia. } { lia. }
    iSplit. { iSplit.
      { iPureIntro. split; last by set_solver. apply mask_lemma; set_solver. }
      unfold invctx_to_multiset. simpl. rewrite gmultiset_disj_union_assoc. iFrame.
    }
    iPureIntro. apply Obs. trivial.
    }
    lia.
  Qed.
 
  Lemma typed_local_inv_close {𝔄 ℭ} (p1 p2 : path) (ty : type 𝔄) (pred: (abstracted_syn_type 𝔄) → ~~ℭ → Prop) E L Il ϝ 𝛼 κ :
    typed_inv_instr E L
      (InvCtx (InvCtx_open κ :: Il) ϝ 𝛼)
      +[p1 ◁ own_ptr 0 (tracked_ty (ty));
        p2 ◁ own_ptr 0 (tracked_ty (local_closer_ty κ ty pred))
      ]
      (Seq Skip Skip)
      (InvCtx Il ϝ 𝛼)
      (const +[])
      (λ post '-[(_, v); (_, (N, γ, c))], λ mask,
        pred (syn_abstract v) c ∧ post -[] (mask ∪ ↑N)
      ).
  Proof.
    apply typed_inv_instr_of_skip_own2_emp.
    intros l1 l2 v [[ns [[γ γt] d0]] c] d tid iκs post mask.
    iIntros "#LFT #TIME #UNIQ E L I gho1 [tok closer] %Obs #⧖ ⧗big £d".
    destruct Obs as [Sat Obs].
    iDestruct "I" as (na_mask at_mask) "[%Hm [[Ilifetimes ϝIncl] [Iown Iat]]]".
    iMod (cna_close with "closer [gho1 ⧗big £d tok] Iown Ilifetimes") as (κs') "[[%LtsEq %Hdisj] [Iown Ilifetimes]]".
     { solve_ndisj. }
     { iNext. iExists v, d, (S d). iFrame. 
        iDestruct (persistent_time_receipt_mono with "⧖") as "$"; first lia.
        iDestruct (cumulative_time_receipt_mono with "⧗big") as "$"; first lia.
        iDestruct (lc_weaken with "£d") as "$"; first lia.
        iPureIntro. exact Sat.
     }
    unfold invctx_to_multiset in LtsEq. simpl in LtsEq. 
    assert (invctx_to_multiset Il ⊎ list_to_set_disj iκs = κs') as LtsEq2 by multiset_solver.
    rewrite <- LtsEq2.
    iModIntro. iExists (mask ∪ ↑ns). iFrame.
    iSplit. { iPureIntro. split; set_solver. }
    iPureIntro. exact Obs.
  Qed.
End local_invariants.

