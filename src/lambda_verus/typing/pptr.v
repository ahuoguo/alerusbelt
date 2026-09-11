(** [PPtr] typing rules, ported to the eris WP.

    Prophecy-dependent parts are dropped
    
*)
From lrust.lang.lib Require Import memcpy.
From lrust.typing Require Export type tracked own product shr_bor uniq_bor uniq_util.
From lrust.typing Require Import uninit type_context programs freeable_util.
From guarding Require Import guard tactics.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section ptr.
  Context `{!typeG Σ}.

  Program Definition ptr_ty : type locₛ := {|
    pt_size := 1;
    pt_gho (l: ~~locₛ) _ := True%I ;
    pt_phys (l: ~~locₛ) _ := [ FVal (LitV (LitLoc l)) ] ;
  |}%I.
  Next Obligation. move=> *. trivial. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. done. Qed.
  
  Global Instance ptr_copy: Copy ptr_ty.
  Proof. split. - typeclasses eauto. - iIntros. iPureIntro. done. Qed.
  
  Lemma ptr_stack_okay : StackOkay ptr_ty.
  Proof. done. Qed.

  Global Instance ptr_send: Send ptr_ty.
  Proof.
    (* [send_change_tid] field elided: concurrency stripped. *)
    split. intros. unfold syn_abstract in H. subst x'. trivial.
  Qed.
  
  Global Instance ptr_sync: Sync ptr_ty.
  Proof. split; trivial. split; iSplit; done. Qed.
  
  (* [ptr_resolve] removed along with [resolve]. *)
End ptr.

Section points_to.
  Context `{!typeG Σ}.

  Program Definition tracked_ty_with_prop {𝔄} (ty: type 𝔄) (P : iProp Σ) : type (trackedₛ 𝔄) := {|
    ty_size := 0;
    ty_lfts := ty.(ty_lfts);
    ty_E := ty.(ty_E);
    ty_gho x d g tid := P ∗ (ty.(ty_gho) x d g tid) ;
    ty_gho_pers x d g tid := (ty.(ty_gho_pers) x d g tid) ;
    ty_phys x tid := [];
  |}%I.
  Next Obligation. intros; done. Qed.
  Next Obligation. intros; done. Qed.
  Next Obligation. intros; done. Qed.
  Next Obligation.
    intros.
    iIntros "[? gho]".
    iDestruct (ty_gho_depth_mono ty with "gho") as "[? wand]" => //. 
    iFrame.
    iIntros "[$ ?]".
    by iApply "wand".
  Qed.
  Next Obligation. intros. apply (ty_gho_pers_depth_mono ty); trivial. Qed.
  (* [ty_guard_proph] obligation elided: prophecy stripped. *)
  Next Obligation. iIntros "* [? ?]". iApply (ty_gho_pers_impl 𝔄); trivial. Qed.

  Definition points_to_ty {𝔄} ty := tracked_ty (@own_ptr _ _ 𝔄 (ty_size ty) ty).

  Global Instance tracked_ty_ne {𝔄} : NonExpansive (@tracked_ty _ _ 𝔄).
  Proof. solve_ne_type. Qed.

  Global Instance points_to_ne {𝔄} : NonExpansive (@points_to_ty 𝔄).
  Proof.
    rewrite /points_to_ty.
    move => m ty1 ty2 Eq.
    apply tracked_ty_ne.
    destruct Eq. rewrite H.
    by rewrite own.own_ne.
  Qed.

  Lemma points_to_stack_okay {𝔄} (ty: type 𝔄) : StackOkay (points_to_ty ty).
  Proof. done. Qed.

  Global Instance points_to_send {𝔄} (ty: type 𝔄) : Send ty → Send (points_to_ty  ty).
  Proof. exact _. Qed.

  Global Instance points_to_sync {𝔄} (ty: type 𝔄) : Sync ty → Sync (points_to_ty ty).
  Proof. exact _. Qed.

  (* [points_to_resolve] removed along with [resolve]. *)

  Lemma points_to_type_incl {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) ty1 ty2 :
    type_incl ty1 ty2 f -∗ type_incl (points_to_ty ty1) (points_to_ty  ty2) (tracked_mapₛ (at_loc_mapₛ f)).
  Proof.
    iIntros "Hincl".
    iApply tracked_type_incl.
    iDestruct "Hincl" as "(% & ?)".
    rewrite H.
    iApply own_type_incl.
    by iFrame.
  Qed.

  Lemma points_to_subtype {𝔄 𝔅} E L (f: 𝔄 →ₛ 𝔅) ty ty' :
    subtype E L ty ty' f → subtype E L (points_to_ty ty) (points_to_ty ty') (tracked_mapₛ (at_loc_mapₛ f)).
  Proof.
    move=> Sub. iIntros "L". iDestruct (Sub with "L") as "#Incl".
    iIntros "!> #E". iApply points_to_type_incl; by [|iApply "Incl"].
  Qed.

End points_to.

Section typing.

  Context `{!typeG Σ, !cnaInv_logicG Σ}.

  (* Not sure if this n makes sense to be an argument at the syntax level *)
  (* Notation "PPtr2Own: ptr perm" := (Skip;; ptr)%E (at level 102, ptr, perm at level 1): expr_scope. *)
  Definition PPtr2Own : val :=
    (λ: ["ptr"; "perm"], "ptr")%V.

  Lemma typed_pptr_to_own {𝔄} (perm ptr : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[ptr ◁ ptr_ty; perm ◁ own_ptr 0 (points_to_ty ty)]
    (PPtr2Own [ptr; perm]) (λ v, +[v ◁ own_ptr (ty_size ty) ty])
    (λ post '-[l; (_, (l', x))], λ mask, l = l' ∧ post -[(l, x)] mask).
  Proof.
    move => tid post mask iκs vl.
    iIntros "_ _ _ _ $ $ TY %Obs" => /=.
    destruct vl as [l [[? [l' x]] []]].
    destruct Obs as [<- Hpost].
    iDestruct "TY" as "(Hptr & Hperm & _)".
    iDestruct "Hptr" as (pl d Heval) "(#Hd & _ & %Hphys)".
    iDestruct "Hperm" as (pl' d' Heval') "(#Hd' & Hown & %Hphys')".
    simpl in Hphys, Hphys'.
    injection Hphys => ?; subst pl.
    injection Hphys' => ?; subst pl'.
    destruct d' => //=.
    iDestruct "Hown" as "(_ & _ & Hown)".
    rewrite /PPtr2Own.
    wp_bind ptr.
    iApply (pgl_wp_wand with "[]"); first by iApply wp_eval_path.
    iIntros (? ->).
    wp_bind perm.
    iApply (pgl_wp_wand with "[]"); first by iApply wp_eval_path.
    iIntros (? ->).
    wp_rec.
    iExists -[(l, x)].
    iFrame.
    rewrite /tctx_elt_interp/ty_own/=.
    iSplitL.
    - iSplit => //.
      destruct d' => //=.
      iExists _, (S (S d')).
      do 2 iSplit => //=.
      iDestruct "Hown" as "(? & ? & gho)".
      iSplitL => //.
      iFrame.
      iNext.
      iDestruct (ty.(ty_gho_depth_mono) with "gho") as "($ & ?)"; lia.
    - iPureIntro. exact Hpost.
  Qed.

  Definition PPtrFromOwn : val :=
    (λ: ["p"],
      let: "x" := new [ #1 ] in "x" <- "p";; "x")%V.

  Lemma typed_pptr_from_own {𝔄} (p : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[p ◁ own_ptr (ty_size ty) ty] (PPtrFromOwn [p])
      (λ v, +[v ◁ own_ptr 1 (prod_ty ptr_ty (points_to_ty ty))])
      (λ post '-[(l, x)], λ mask, ∀ lc, post -[(lc, (l, (l, x)))] mask).
  Proof.
    move => tid post mask iκs vl.
    iIntros "_ #TIME _ _ $ $ TY %Obs" => /=.
    destruct vl as [[l x] []].
    iDestruct "TY" as "(TY & _)".
    iDestruct "TY" as (pl d Heval) "(#Hd & Hown & %Hphys)".
    simpl in Hphys.
    injection Hphys => ?; subst pl.
    destruct d => //=.
    iDestruct "Hown" as "(Hl & Hfree & Hgho)".
    wp_bind p.
    iApply (pgl_wp_wand with "[]"); first by iApply wp_eval_path.
    iIntros (? ->).
    iApply (wp_persistent_time_receipt (S d) with "TIME Hd"); [done|solve_ndisj|].
    iIntros "£ #Hd'".
    iDestruct (lc_weaken 1 with "£") as "£1"; first (rewrite /advance_credits; lia).
    wp_rec.
    wp_bind (new _).
    iApply wp_new => //.
    iNext.
    iIntros (l') "[Hfree' Hl']".
    wp_let.
    rewrite heap_mapsto_vec_singleton.
    wp_bind (_ <- _)%E.
    iApply (wp_write _ _ _ (LitV (LitLoc l)) with "Hl'"); [solve_ndisj|].
    iNext. iIntros "Hl'". wp_seq.
    iExists -[(l', (l, (l, x)))].
    iFrame.
    rewrite /tctx_elt_interp/ty_own/=.
    iSplitL.
    - iSplit => //.
      iExists _, (S (S d)).
      do 2 iSplit => //=.
      iSplitL => //.
      rewrite -heap_mapsto_vec_singleton.
      rewrite -!(heap_mapsto_fancy_fmap_eq l').
      iFrame.
      rewrite freeable_sz_full.
      iFrame.
      iNext; iNext; iFrame.
      iDestruct (ty.(ty_gho_depth_mono) with "Hgho") as "($ & ?)"; lia.
    - iPureIntro. apply Obs.
  Qed.

  Definition PPtrBorrow : val :=
    (λ: ["ptr"; "perm_ref"], "ptr")%V.

  Lemma typed_pptr_borrow {𝔄} κ (ptr perm_ref : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[ptr ◁ ptr_ty; perm_ref ◁ shr_bor κ (points_to_ty ty)]
      (PPtrBorrow [ptr; perm_ref]) (λ v, +[v ◁ shr_bor κ ty])
      (λ post '-[l; (cl, (l', x))], λ mask,
        l = l' ∧ post -[((l, repeat [] ty.(ty_size)), x)] mask).
  Proof.
    move => tid post mask iκs vl.
    iIntros "_ #TIME _ _ $ $ TY %Obs" => /=.
    destruct vl as [l [[c [l' x]] []]].
    destruct Obs as [<- Hpost].
    iDestruct "TY" as "(Hptr & Hperm & _)".
    iDestruct "Hptr" as (pl d Heval) "(#Hd & _ & %Hphys)".
    simpl in Hphys.
    injection Hphys => ?; subst pl.
    iDestruct "Hperm" as (pl' d' Heval') "(#Hd' & Hshr & %Hphys')".
    simpl in Hphys'.
    injection Hphys' => ?; subst pl'.
    rewrite /PPtrBorrow.
    wp_bind ptr.
    iApply (pgl_wp_wand with "[]"); first by iApply wp_eval_path.
    iIntros (? ->).
    wp_bind perm_ref.
    iApply (pgl_wp_wand with "[]"); first by iApply wp_eval_path.
    iIntros (? ->).
    iApply pgl_wp_fupd.
    iApply (wp_persistent_time_receipt d' with "TIME Hd'"); [done|solve_ndisj|].
    destruct d' as [ | [ | d']] => //=; iDestruct "Hshr" as "(_ & #Hshr & #Hpers)".
    { rewrite /advance_credits /=.
      iIntros "£ #Hd''".
      iDestruct (lc_weaken 1 with "£") as "£1"; first lia.
      wp_rec.
      by iMod (lc_fupd_elim_later with "£1 Hpers"). }
    iIntros "_ #Hd''".
    wp_rec.
    iModIntro.
    iExists -[((l, repeat [] ty.(ty_size)), x)].
    rewrite /tctx_elt_interp/ty_own/=.
    iFrame.
    iSplitL.
    { rewrite /tctx_elt_interp/ty_own/=.
      iSplit => //; iExists _, (S (S (S d'))).
      iSplit => //.
      iFrame "#" => /=.
      iSplit => //.
      iSplitR; last iSplitL.
      - rewrite heap_mapsto_cells_fancy_empty.
        rewrite (ty.(ty_size_eq) x tid).
        iPoseProof (guards_weaken_rhs_sep_l with "Hshr") as "Hshr2".
        iPoseProof (lguards_weaken_later with "Hshr2") as "Hshr3".
        2: iFrame "#".
        lia.
      - iPoseProof (guards_weaken_rhs_sep_r with "Hshr") as "Hshr2".
        iPoseProof (guards_weaken_rhs_sep_r with "Hshr2") as "Hshr3".
        iPoseProof (guards_later_absorb_1 with "Hshr3") as "Hshr4".
        replace (S (S (d' + 1)) + 1) with (S (S (S (d' + 1)))) by lia.
        iClear "Hshr Hshr2 Hshr3".
        replace (S (S (S (d' + 1)))) with (S (S (S (d' + 1))) + 0) at 2 by lia.
        iApply (guards_transitive_additive with "Hshr4").
        leaf_by_sep.
        iApply ty.(ty_gho_depth_mono); lia.
      - repeat iNext.
        iApply (ty.(ty_gho_pers_depth_mono) with "Hpers") => //; lia.
    }
    iPureIntro. exact Hpost.
  Qed.

  (** [typed_pptr_mut_borrow] *)

End typing.

