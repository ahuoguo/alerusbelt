From lrust.lang.lib Require Import memcpy.
From lrust.lang Require Import heap.
From lrust.typing Require Export type own product shr_bor int bool.
From lrust.typing Require Import uninit type_context programs freeable_util.
From guarding Require Import guard tactics.
From lrust.lifetime Require Import lifetime_full.

Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section pcell.
  Context `{!typeG Σ}.

  Program Definition pcell_ty n : type (pcellₛ n) :=
    {| ty_size := n;
      ty_gho x _ _ _ := ⌜ length x = n ⌝;
      ty_gho_pers  x _ _ _ := ⌜ length x = n ⌝;
      ty_phys (cell_ids: ~~ (pcellₛ n)) _ := pad (FCell <$> cell_ids) n ;
      ty_lfts := [];
      ty_E := [];
     |}%I.
  Next Obligation. move => n v tid. by rewrite length_pad. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. move => *. iIntros "?". auto. Qed.
  Next Obligation. move => *. iIntros "?". auto. Qed.
  (* [ty_guard_proph] obligation elided: prophecy stripped. *)
  Next Obligation. move => *. by iIntros "?". Qed.
  
  Global Instance pcell_send n: Send (pcell_ty n).
  Proof.
    (* [send_change_tid] field elided: prophecy stripped. *)
    split. intros. unfold syn_abstract in H. simpl in H. rewrite H. trivial.
  Qed.
  
  Global Instance pcell_sync n: Sync (pcell_ty n).
  Proof. split; trivial. split; iSplit; done. Qed.
End pcell.

Section points_to.
  Context `{!typeG Σ}.

  Program Definition cell_points_to_ty {𝔄} (ty: type 𝔄) : type (trackedₛ (pcellₛ (ty.(ty_size)) * 𝔄)) := 
    {| ty_size := 0%nat;
      ty_lfts := ty.(ty_lfts);
      ty_E := ty.(ty_E);
      ty_gho x d g tid := 
        [S(d') := d] (cells_points_to_fancy_value_vec x.1 (ty.(ty_phys) x.2 tid))%I ∗ ▷ (ty.(ty_gho) x.2 d' g tid) ;
      ty_gho_pers x d g tid := 
        [S(d') := d] ⌜ length x.1 = ty_size ty ⌝ ∗ ▷ (ty.(ty_gho_pers) (snd x) d' g tid) ;
      ty_phys _ _ := [];
    |}%I.
  Next Obligation. move => 𝔄 tyA v tid //=. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    move => 𝔄 ty d g d' g' v tid ??//=.
    iIntros "H".
    destruct d => //=.
    destruct d' => //=; first lia.
    iDestruct "H" as "[H↦ Hgho]".
    iFrame "H↦".
    iDestruct (ty.(ty_gho_depth_mono) with "Hgho") as "[$ Hwand]" => //; first lia.
    iIntros "[$ Hgho] !>".
    by iApply "Hwand".
  Qed.
  Next Obligation.
    move => 𝔄 ty d g d' g' v tid ??//=.
    iIntros "H".
    destruct d => //=.
    destruct d' => //=; first lia.
    iDestruct "H" as "[$ H]".
    iNext.
    iDestruct (ty.(ty_gho_pers_depth_mono) _ _ d' g' with "H") as "?" => //; lia.
  Qed.
  (* [ty_guard_proph] obligation elided: prophecy stripped. *)
  Next Obligation.
    intros 𝔄 ty x d g tid. iIntros "A". destruct d as [|d']; first by done.
    iDestruct "A" as "[A1 A2]".
    iDestruct (cells_points_to_fancy_vec_length_eq with "A1") as "%".
    rewrite (ty_size_eq ty) in H.
    iSplit => //.
    iApply ty_gho_pers_impl. iFrame.
  Qed.

  Global Instance cell_points_to_send {𝔄} (ty: type 𝔄) :
      Send ty → Send (cell_points_to_ty ty).
  Proof.
    (* [send_change_tid] field elided: prophecy stripped. *)
    intros [Hphys]. split; trivial.
  Qed.
  
  Global Instance cell_points_to_sync {𝔄} (ty: type 𝔄) :
      Sync ty → Sync (cell_points_to_ty ty).
  Proof.
      move=> HSync tid tid' x d g. split => //=. split.
      + iSplit.
         - iIntros "Hgho".
           destruct d => //=.
           iDestruct "Hgho" as "(Hown&Hgho)".
           pose proof (sync_change_tid tid tid' (snd x) d g) as [-> [Hgho Hghopers]].
           iFrame "%".
           iFrame.
           iApply (Hgho with "Hgho").
         - iIntros "Hgho".
           destruct d => //=.
           iDestruct "Hgho" as "(Hown&Hgho)".
           pose proof (sync_change_tid tid tid' (snd x) d g) as [-> [Hgho Hghopers]].
           iFrame "%".
           iFrame.
           iApply (Hgho with "Hgho").
       + destruct d => //=.
         pose proof (sync_change_tid tid tid' (snd x) d g) as [_ [Hgho Hghopers]].
         rewrite Hghopers. trivial.
  Qed.

End points_to.

Section typing.

  Context `{!typeG Σ, !cnaInv_logicG Σ}.

  Definition PCellFromOwn : val :=
    (λ: ["p"], "p")%V.

  Lemma typed_pcell_from_own {𝔄} (p : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[p ◁ own_ptr (ty_size ty) ty] (PCellFromOwn [p]) (λ v, +[v ◁ own_ptr (ty_size ty) (prod_ty (pcell_ty (ty_size ty)) (cell_points_to_ty ty))]) (λ post '-[(l, x)], λ mask, ∀ (cell_ids : list positive), post -[(l, (cell_ids, (cell_ids, x)))] mask).
  Proof.
    move => tid post mask iκs vl.
    iIntros "_ #TIME _ $ $ TY %Obs" => /=.
    destruct vl as [[l x][]].
    iDestruct "TY" as "(TY & _)".
    iDestruct "TY" as (pl d Heval) "(#Hd & Hown & %Hphys)".
    simpl in Hphys.
    inversion Hphys; subst pl.
    destruct d => //=.
    iDestruct "Hown" as "(Hl & Hfree & Hgho)".
    iApply pgl_wp_fupd.
    wp_bind p.
    iApply (pgl_wp_wand with "[]"); first by iApply wp_eval_path.
    iIntros (? ->).
    iApply (wp_persistent_time_receipt _ with "TIME Hd"); [done|solve_ndisj|].
    iIntros "£ #Hd'".
    wp_rec.
    iMod (cell_alloc2 with "Hl") as "[%γs [% H↦]]".
    set cl := ((l, (λ γ, [γ]) <$> γs) : cloc).
    change l with cl.1. change (app [] <$> γs) with cl.2.
    rewrite heap_mapsto_cells_to_complete_mapsto_fancy_vec.
    iDestruct "H↦" as "[Hchain Htail]".
    rewrite heap_complete_mapsto_vec_eq.
    rewrite (ty.(ty_size_eq)) in H.
    iExists -[(l, (γs, (γs, x)))].
    iFrame.
    rewrite /tctx_elt_interp/ty_own/=.
    iSplitL.
    - iModIntro.
      iSplitL => //.
      iExists _, _.
      iFrame "Hd'".
      do 2 iSplit => //=.
      rewrite Nat.add_0_r app_nil_r pad_length'.
      2: by rewrite length_fmap -H.
      iFrame.
      iNext.
      iSplit => //.
      unfold cl.
      rewrite heap_complete_mapsto_fancy_val_vec_eq'.
      iFrame.
      iNext.
      iDestruct (ty.(ty_gho_depth_mono) with "Hgho") as "($ & ?)"; lia.
    - iPureIntro. apply Obs.
  Qed.

  Definition PCell2Own : val :=
    (λ: ["pcell"; "perm"], "pcell")%V.

  Lemma typed_pcell_to_own {𝔄} (perm pcell : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[pcell ◁ own_ptr (ty_size ty) (pcell_ty (ty_size ty)); perm ◁ own_ptr 0 (cell_points_to_ty ty)] (PCell2Own [pcell; perm]) (λ v, +[v ◁ own_ptr (ty_size ty) ty]) (λ post '-[(l, γs); (_, (γs', x))], λ mask, γs = γs' ∧ post -[(l, x)] mask).
  Proof.
    move => tid post mask iκs vl.
    iIntros "_ #TIME _ $ $ TY %Obs" => /=.
    destruct vl as [[l γs] [[l' [γs' x]] []]].
    destruct Obs as [<- Hpost].
    iDestruct "TY" as "(Hpcell & Hperm & _)".
    iDestruct "Hpcell" as (pl d Heval) "(#Hd & Hown & %Hphys)".
    iDestruct "Hperm" as (pl' d' Heval') "(#Hd' & Hown' & %Hphys')".
    simpl in Hphys, Hphys'.
    inversion Hphys; subst pl.
    inversion Hphys'; subst pl'.
    destruct d => //.
    destruct d' => //=.
    iDestruct "Hown" as "(H↦ & Hfree & >%Hlen)".
    iDestruct "Hown'" as "(_ & _ & Hown)".
    rewrite /PCell2Own.
    wp_bind pcell.
    iApply (pgl_wp_wand with "[]"); first by iApply wp_eval_path.
    iIntros (? ->).
    wp_bind perm.
    iApply (pgl_wp_wand with "[]"); first by iApply wp_eval_path.
    iIntros (? ->).
    iApply pgl_wp_fupd.
    iApply (wp_persistent_time_receipt _ with "TIME Hd"); [done|solve_ndisj|].
    iIntros "£ #Hd''".
    wp_rec.
    iDestruct "£" as "[£1 [£2 £3]]".
    destruct d' => /=.
    { by iMod (lc_fupd_elim_later with "£2 Hown"). }
    iClear "£1 £2 £3".
    rewrite pad_length'.
    2: by rewrite length_fmap.
    iDestruct "Hown" as "[H↦' Hgho]".
    rewrite -heap_complete_mapsto_fancy_val_vec_eq'.
    iExists -[(l, x)].
    iFrame.
    rewrite /tctx_elt_interp/ty_own/=.
    iSplitL.
    - iMod (heap_delete_cell with "H↦ H↦'") as "H↦".
      iModIntro.
      iSplit => //.
      iExists _, (S (S d')).
      do 2 iSplit => //=.
      iSplitL => //.
      iFrame.
      iDestruct (ty.(ty_gho_depth_mono) with "Hgho") as "($ & ?)"; lia.
    - iPureIntro. exact Hpost.
  Qed.

  Definition PCellBorrow : val :=
    (λ: ["pcell_ref"; "perm_ref"], "pcell_ref")%V.

  Lemma typed_pcell_borrow {𝔄} κ (pcell_ref perm_ref : path) (ty : type 𝔄) E L I :
    (* lctx_lft_alive E L κ → *)
    typed_instr E L I +[pcell_ref ◁ shr_bor κ (pcell_ty (ty_size ty)); perm_ref ◁ shr_bor κ (cell_points_to_ty ty)] (PCellBorrow [pcell_ref; perm_ref]) (λ v, +[v ◁ shr_bor κ ty]) (λ post '-[(l, γs); (_, (γs', x))], λ mask, γs = γs' ∧ post -[(cloc_flat_insert l γs, x)] mask).
  Proof.
    move => tid post mask iκs vl.
    iIntros "_ #TIME _ $ $ TY %Obs" => /=.
    destruct vl as [[l γs] [[l' [γs' x]] []]].
    destruct Obs as [<- Hpost].
    iDestruct "TY" as "(Hcell & Hperm & _)".
    iDestruct "Hcell" as (pl d Heval) "(#Hd & #Hshr & %Hphys)".
    simpl in Hphys.
    inversion Hphys; subst pl.
    iDestruct "Hperm" as (pl' d' Heval') "(#Hd' & Hshr' & %Hphys')".
    simpl in Hphys'.
    inversion Hphys'; subst pl'.
    (* destruct d' => //=. *)
    rewrite /PCellBorrow.
    wp_bind pcell_ref.
    iApply (pgl_wp_wand with "[]"); first by iApply wp_eval_path.
    iIntros (? ->).
    wp_bind perm_ref.
    iApply (pgl_wp_wand with "[]"); first by iApply wp_eval_path.
    iIntros (? ->).
    iApply pgl_wp_fupd.
    destruct (decide (d ≤ d')) as [Hd | Hd'].
    - iApply (wp_persistent_time_receipt _ with "TIME Hd'"); [done|solve_ndisj|].
      destruct d => //.
      iSimpl in "Hshr".
      destruct d' as [ | [ | d']] => //=.
      { iDestruct "Hshr'" as "(_ & _ & Hfalse)".
        rewrite /advance_credits /=.
        iIntros "(£ & _) #Hd''".
        wp_rec.
        by iMod (lc_fupd_elim_later with "£ Hfalse"). }
      iIntros "H£ #Hd''".
      wp_rec.
        iDestruct "Hshr'" as "(_ & #Hshr' & (H&Hpers))".
      iExists -[(cloc_flat_insert l γs, x)].
      rewrite /tctx_elt_interp/ty_own/=.
      iFrame.
      iSplitL.
      { iCombine "H Hpers" as "H".
        rewrite !Nat.add_1_r -!bi.later_laterN.
        iMod (lc_fupd_add_laterN _ _ _ (S (S d'))  with "[H£] [H]") as "H".
        { iApply (lc_weaken with "H£"). rewrite /advance_credits. nia. }
        { iIntros "!> !>". iExact "H". }
        iDestruct "H" as "[%Hlen #Hgho]".
        rewrite pad_length'.
        2: by rewrite length_fmap.
        iModIntro.
        iSplit => //.
        - iExists _, (S (S (S d'))).
          iSplit => //.
          iFrame "#" => /=.
          iSplit => //.
          iSplitR; last iSplitL.
          + iDestruct "Hshr" as "(H↦shared1 & _ & _)".
            iDestruct (guards_weaken_rhs_sep_l with "Hshr'") as "H↦shared2 ".
            iDestruct (lguards_weaken_later with "H↦shared1") as "H↦shared1'".
            1: instantiate (1 := S (S (S d'))); lia.
            iDestruct (guard_cloc_combine_fancy' with "H↦shared1' H↦shared2") as "H↦shared3".
            simpl.
            iApply (lguards_weaken_later with "H↦shared3").
            lia.
          + iDestruct (guards_weaken_rhs_sep_r with "Hshr'") as "Hghoshared".
            iDestruct (guards_later_absorb_1 with "Hghoshared") as "Hghoshared1".
            iApply (guards_transitive_left with "Hghoshared1").
            leaf_by_sep.
            iApply ty.(ty_gho_depth_mono); lia.
          + repeat iNext.
            iApply (ty.(ty_gho_pers_depth_mono) with "Hgho") => //; lia.
      }
      iPureIntro. exact Hpost.
    - iApply (wp_persistent_time_receipt _ with "TIME Hd"); [done|solve_ndisj|].
      destruct d => //.
      iSimpl in "Hshr".
      destruct d' as [ | [ | d']] => //=.
      { iDestruct "Hshr'" as "(_ & _ & Hfalse)".
        rewrite /advance_credits /=.
        iIntros "(£ & _) #Hd''".
        wp_rec.
        by iMod (lc_fupd_elim_later with "£ Hfalse"). }
      iIntros "H£ #Hd''".
      wp_rec.
        iDestruct "Hshr'" as "(_ & #Hshr' & (H&Hpers))".
      iExists -[(cloc_flat_insert l γs, x)].
      rewrite /tctx_elt_interp/ty_own/=.
      iFrame.
      iSplitL.
      { iCombine "H Hpers" as "H".
        rewrite !Nat.add_1_r -!bi.later_laterN.
        iMod (lc_fupd_add_laterN _ _ _ (S (S d'))  with "[H£] [H]") as "H".
        { iApply (lc_weaken with "H£"). rewrite /advance_credits. nia. }
        { iIntros "!> !>". iExact "H". }
        iDestruct "H" as "[%Hlen #Hgho]".
        rewrite pad_length'.
        2: by rewrite length_fmap.
        iModIntro.
        iSplit => //.
        - iExists _, (S (S d)).
          iSplit => //.
          iFrame "#" => /=.
          iSplit => //.
          iSplitR; last iSplitL.
          + iDestruct "Hshr" as "(H↦shared1 & _ & _)".
            iDestruct (guards_weaken_rhs_sep_l with "Hshr'") as "H↦shared2 ".
            iDestruct (lguards_weaken_later with "H↦shared2") as "H↦shared2'".
            1: instantiate (1 := S (S d)); lia.
            iDestruct (guard_cloc_combine_fancy' with "H↦shared1 H↦shared2'") as "H↦shared3".
            simpl.
            iApply (lguards_weaken_later with "H↦shared3").
            lia.
          + iDestruct (guards_weaken_rhs_sep_r with "Hshr'") as "Hghoshared".
            iDestruct (guards_later_absorb_1 with "Hghoshared") as "Hghoshared1".
            rewrite !Nat.add_1_r.
            iDestruct (lguards_weaken_later with "Hghoshared1") as "Hghoshared2".
            1: instantiate (1 := S (S (S d))); lia.
            iApply (guards_transitive_left with "Hghoshared2").
            leaf_by_sep.
            iApply ty.(ty_gho_depth_mono); lia.
          + repeat iNext.
            iApply (ty.(ty_gho_pers_depth_mono) with "Hgho") => //; lia.
      }
      iPureIntro. exact Hpost.
  Qed.

  (** [typed_pcell_mut_borrow]*)

End typing.

