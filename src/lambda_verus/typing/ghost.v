From lrust.typing Require Export type.
From lrust.typing Require Import programs.
From lrust.typing Require Import own.

Set Default Proof Using "Type".

Section ghost.
  Context `{!typeG Σ, !cnaInv_logicG Σ}.

  Program Definition ghost_ty {𝔄} (ty: type 𝔄) : type (ghostₛ 𝔄) := @ty_of_st _ _ (ghostₛ 𝔄)
    ({|
      st_size := 0;
      st_lfts := ty.(ty_lfts);
      st_E := [];
      st_gho x d g tid := True%I;
      st_phys x tid := [];
    |}%I : simple_type (ghostₛ 𝔄)).
  Next Obligation. move=> *. trivial. Qed.
  Next Obligation. move=> *. trivial. Qed.
  Next Obligation. move=> *. trivial. Qed.
  Next Obligation. intros. iIntros. done. Qed.
  (* [st_guard_proph] obligation elided: prophecy stripped. *)
  Next Obligation. done. Qed.
  
  Global Instance tracked_ne {𝔄} : NonExpansive (@ghost_ty 𝔄).
  Proof. solve_ne_type. Qed.

  Global Instance ghost_send {𝔄} (ty : type 𝔄) : Send (ghost_ty ty).
  Proof.
    (* [send_change_tid] field elided: concurrency stripped. *)
    intros. split; trivial.
  Qed.
  
  Global Instance ghost_sync {𝔄} (ty : type 𝔄) : Sync (ghost_ty ty).
  Proof. split; trivial. split; iSplit; done. Qed.
  
  Global Instance ghost_copy {𝔄} (ty : type 𝔄) : Copy (ghost_ty ty).
  Proof. split; try done. typeclasses eauto. Qed.

  (* [ghost_resolve] removed along with [resolve]. *)
  
  Lemma ghost_constant {𝔄} E L I (ty : type 𝔄) (c: ~~𝔄) :
    typed_instr E L I
      +[] (new [ #0 ]%E)
      (λ q, +[q ◁ own_ptr 0 (ghost_ty ty)])
      (λ post '-[], λ mask, ∀ l, post -[(l, c)] mask).
  Proof.
    move => tid post mask iκs [].
    iIntros "LFT #TIME #UNIQ E L $ TY %Obs" => /=.
    iMod (persistent_time_receipt_0) as "⧖".
    iApply (wp_persistent_time_receipt _ with "TIME ⧖"); [done|solve_ndisj|]. iIntros "_ ⧖".
    iApply wp_new=>//. iIntros "!>" (l) "(† & ↦)". iExists -[(l, c)]. iFrame. iSplitL.
    - iExists (#l). iSplit; first done. iSplit; last done.
      unfold own_ptr, ty_gho. rewrite !freeable_util.freeable_sz_full. iFrame. done.
    - iPureIntro. apply Obs.
  Qed.
  
  Lemma ghost_snapshot {𝔄} E L I p (ty : type 𝔄) :
    typed_instr E L I
      +[p ◁ ty]
      (new [ #0 ]%E)
      (λ q, +[p ◁ ty; q ◁ own_ptr 0 (ghost_ty ty)])
      (λ post '-[x], λ mask, ∀ l, post -[x; (l, x)] mask).
  Proof.
    move => tid post mask iκs [x []].
    iIntros "LFT #TIME #UNIQ E L $ [T TY] %Obs" => /=.
    iMod (persistent_time_receipt_0) as "⧖".
    iApply (wp_persistent_time_receipt _ with "TIME ⧖"); [done|solve_ndisj|]. iIntros "_ ⧖".
    iApply wp_new=>//. iIntros "!>" (l) "(† & ↦)". iExists -[x; (l, x)]. iFrame "T".
    iFrame. iSplitL.
    - iExists (#l). iSplit; first done. iSplit; last done.
      unfold own_ptr, ty_gho. rewrite !freeable_util.freeable_sz_full. iFrame. done.
    - iPureIntro. apply Obs.
  Qed.
  
  Lemma ghost_compute {𝔄 𝔅 ℭ} E L I p1 p2 (ty1 : type 𝔄) (ty2 : type 𝔅) (ty: type ℭ)
      (f : (~~𝔄) → (~~𝔅) → (~~ℭ)) :
    typed_instr E L I
      +[p1 ◁ ty1; p2 ◁ ty2]
      (new [ #0 ]%E)
      (λ q, +[p1 ◁ ty1; p2 ◁ ty2; q ◁ own_ptr 0 (ghost_ty ty)])
      (λ post '-[x; y], λ mask, ∀ l, post -[x; y; (l, f x y)] mask).
  Proof.
    move => tid post mask iκs [x [y []]].
    iIntros "LFT #TIME #UNIQ E L $ [T1 [T2 TY]] %Obs" => /=.
    iMod (persistent_time_receipt_0) as "⧖".
    iApply (wp_persistent_time_receipt _ with "TIME ⧖"); [done|solve_ndisj|]. iIntros "_ ⧖".
    iApply wp_new=>//. iIntros "!>" (l) "(† & ↦)". iExists -[x; y; (l, f x y)].
    iFrame "T1 T2". iFrame. iSplitL.
    - iExists (#l). iSplit; first done. iSplit; last done.
      unfold own_ptr, ty_gho. rewrite !freeable_util.freeable_sz_full. iFrame. done.
    - iPureIntro. apply Obs.
  Qed.
End ghost.

