(** * Raw pointers and points-to permissions

  Ported from VerusBelt ([typing/pptr.v], MIT, Hance, Elbeheiry, Matsushita,
  Dreyer).

  [tracked_ty_with_prop] carried an arbitrary [P : iProp Σ] inside the ghost
  assertion; ghost assertions are formulas here, so it carries a
  [Px : FML $oi Σ] instead.  (It is unused upstream as well.)  The receipts
  the permission operations mint and the [▷]s they strip are gone. *)

From lrust.lang.lib Require Import total_memcpy.
From lrust.typing_total Require Export type tracked own product sum uniq_bor
  uniq_util shr_bor.
From lrust.typing_total Require Import uninit type_context programs
  programs_util freeable_util lft_contexts.
From nola.verus_halt.lifetime Require Import lifetime_full.
From nola.bi Require Import guard modw.
From lrust.lang Require Import total_wsat.
Import GuardNotation ModwNotation TglWpwNotation.
(** Our [util] last, so that its [SemiIso] wins the name over Nola's; see
  [typing_total/type.v]. *)
From lrust.util Require Import basic.
(** [ctx_wp], for the [lrustTotGS] instance: this file states weakest
  preconditions.  See the head of [typing_total/ctx_wp.v]. *)
From lrust.typing_total Require Import ctx_wp.
Unset Default Proof Using.
(** [iris.prelude.options] sets [Default Goal Selector "!"], which rejects a
  bare tactic while more than one goal is focused.  It reaches a ported file
  through our imports and not through Nola's, so Nola's proofs - written
  against the default [1], "act on the first goal" - would otherwise need a
  focus fix every few lemmas.  Restoring [1] is a lint setting, not a
  soundness one. *)
Set Default Goal Selector "1".
Unset Suggest Proof Using.

Implicit Type 𝔄 𝔅: syn_type.

Section ptr.
  Context `{!typeG FML Σ}.

  Program Definition ptr_ty : type locₛ :=
    {| pt_size := 1; pt_lev := 0;
       pt_ghox (l: ~~locₛ) _ := empty_fml;
       pt_phys (l: ~~locₛ) _ := [ FVal (LitV (LitLoc l)) ];
    |}.
  Next Obligation. move=> sem H *. rewrite (empty_sem_at H). exact _. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.

  Lemma ptr_gho l d g tid : ty_gho ptr_ty l d g tid ⊣⊢ True.
  Proof. apply empty_fml_sem. Qed.
  Lemma ptr_gho_pers l d g tid : ty_gho_pers ptr_ty l d g tid ⊣⊢ True.
  Proof. apply empty_fml_sem. Qed.

  Global Instance ptr_copy: Copy ptr_ty.
  Proof. split; [apply _|]. iIntros. iPureIntro. done. Qed.

  Lemma ptr_stack_okay : StackOkay ptr_ty.
  Proof. done. Qed.

  Global Instance ptr_send: Send ptr_ty.
  Proof.
    intros. split; trivial.
    - intros. unfold syn_abstract in H. by subst x'.
    - iIntros (tid tid' x0 d g G κs) "_ _ lfts _ tok _ $ !>".
      iExists x0, 0%nat. iFrame "lfts tok".
      iSplit; [by iApply empty_fml_sem_2|done].
  Qed.

  Global Instance ptr_sync: Sync ptr_ty.
  Proof. move=> *. split; [done|]. split; reflexivity. Qed.

  (** [ptr_resolve] removed along with [resolve]: it resolves a type's
    prophecies, and there are none. *)
End ptr.

Global Hint Rewrite @ptr_gho @ptr_gho_pers : fml_sem.

Section points_to.
  Context `{!typeG FML Σ}.

  (** The original's [P] is an arbitrary [iProp Σ]; a ghost assertion is a
    formula here, so [Px] is one. *)
  Program Definition tracked_ty_with_prop {𝔄} (ty: type 𝔄) (Px : FML $oi Σ)
      : type (trackedₛ 𝔄) := {|
    ty_size := 0;
    ty_lev := 0;
    ty_lfts := ty.(ty_lfts);
    ty_E := ty.(ty_E);
    ty_ghox x d g tid := (Px ∗ ty.(ty_ghox) x d g tid)%FML;
    ty_gho_persx x d g tid := ty.(ty_gho_persx) x d g tid;
    ty_phys x tid := [];
  |}%I.
  Next Obligation. intros; done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    move=> ? ty Px sem H *. rewrite !(sep_sem_at H). iIntros "[$ gho]".
    by iApply (ty_gho_depth_mono_at ty sem H with "gho").
  Qed.
  Next Obligation.
    move=> ? ty Px sem H *. by apply (ty_gho_pers_depth_mono_at ty sem H).
  Qed.
  (** The [guard_proph] obligation is gone with the field; see [typing_total/type.v]. *)
  Next Obligation.
    move=> ? ty Px sem H *. by apply (ty_gho_pers_pers_at ty sem H).
  Qed.
  Next Obligation.
    move=> *. rewrite bor_sep_sem. iIntros "[_ gho]".
    by iApply ty_gho_pers_impl.
  Qed.

  Definition points_to_ty {𝔄} ty :=
    tracked_ty (@own_ptr _ _ _ 𝔄 (ty_size ty) ty).

  Global Instance points_to_ne {𝔄} : NonExpansive (@points_to_ty 𝔄).
  Proof.
    rewrite /points_to_ty=> m ty1 ty2 Eq. apply tracked_ne.
    destruct Eq as [Hsz ?]. rewrite Hsz. by apply own.own_ne.
  Qed.

  Lemma points_to_stack_okay {𝔄} (ty: type 𝔄) : StackOkay (points_to_ty ty).
  Proof. done. Qed.

  Global Instance points_to_send {𝔄} (ty: type 𝔄) :
    Send ty → Send (points_to_ty ty).
  Proof. exact _. Qed.

  Global Instance points_to_sync {𝔄} (ty: type 𝔄) :
    Sync ty → Sync (points_to_ty ty).
  Proof. exact _. Qed.

  (** [points_to_resolve] removed along with [resolve]: it resolves a type's
    prophecies, and there are none. *)

  Lemma points_to_type_incl {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) ty1 ty2 :
    type_incl ty1 ty2 f -∗
      type_incl (points_to_ty ty1) (points_to_ty ty2)
        (tracked_mapₛ (at_loc_mapₛ f)).
  Proof.
    iIntros "Hincl". iApply tracked_type_incl.
    iDestruct "Hincl" as "(%Hsz & ?)". rewrite Hsz.
    iApply own_type_incl. by iFrame.
  Qed.

  Lemma points_to_subtype {𝔄 𝔅} E L (f: 𝔄 →ₛ 𝔅) ty ty' :
    subtype E L ty ty' f →
    subtype E L (points_to_ty ty) (points_to_ty ty')
      (tracked_mapₛ (at_loc_mapₛ f)).
  Proof.
    move=> Sub. iIntros "L". iDestruct (Sub with "L") as "#Incl".
    iIntros "!> #E". iApply points_to_type_incl; by [|iApply "Incl"].
  Qed.
End points_to.

Section typing.
  Context `{!typeG FML Σ}.

  Definition PPtr2Own : val := (λ: ["ptr"; "perm"], "ptr")%V.

  Lemma typed_pptr_to_own {𝔄} (perm ptr : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[ptr ◁ ptr_ty; perm ◁ own_ptr 0 (points_to_ty ty)]
      (PPtr2Own [ptr; perm]) (λ v, +[v ◁ own_ptr (ty_size ty) ty])
      (λ post '-[l; (_, (l', x))], λ mask,
        l = l' ∧ post -[(l, x)] mask).
  Proof.
    move=> tid post mask iκs vπl.
    iIntros "#LFT #UNIQ #E L I TY #Obs"=>/=.
    destruct vπl as [l [[? [l' x]] []]].
    iDestruct "TY" as "(Hptr & Hperm & _)".
    iDestruct "Hptr" as (pl d Heval) "[_ %Hphys]".
    iDestruct "Hperm" as (pl' d' Heval') "[Hown %Hphys']".
    simpl in Hphys, Hphys'. injection Hphys=> ?; subst pl.
    injection Hphys'=> ?; subst pl'.
    destruct d' as [|d'];
      [by iDestruct (false_fml_sem_1 with "Hown") as "[]"|].
    rewrite own_ptr_gho /=. iDestruct "Hown" as "(_ & _ & Hown)".
    rewrite tracked_ty_gho.
    destruct d' as [|d'];
      [by iDestruct (false_fml_sem_1 with "Hown") as "[]"|].
    rewrite own_ptr_gho /=. iDestruct "Hown" as "(Hl & Hfree & Hgho)".
    iApply tgl_wpw_fupdw_nonval; [done|].
    iApply fupdw_tgl_wpw_nonval; [done|]. iIntros "W".
    iDestruct "Obs" as %HobsK0. pose proof HobsK0 as HobsK. move: HobsK0=> [<- _].
    iModIntro. iFrame "W".
    twp_bind ptr. iApply tgl_wp_wand; [by iApply twp_eval_path|].
    iIntros (?->). twp_bind perm. iApply tgl_wp_wand; [by iApply twp_eval_path|].
    iIntros (?->). twp_rec. iModIntro.
    iExists -[(l, x)]. iFrame "L I". iSplit; last first.
    { iPureIntro; move: HobsK=> Hpost. apply Hpost. }
    iSplit; [|done]. iExists (LitV (LitLoc l)), (S (S d')).
    iSplit; [done|].
    rewrite /ty_own own_ptr_gho /=. iFrame "Hl Hfree". iSplit; [|done].
    iDestruct (ty_gho_depth_mono with "Hgho") as "$"; [lia|lia].
  Qed.

  Definition PPtrFromOwn : val :=
    (λ: ["p"], let: "x" := new [ #1 ] in "x" <- "p";; "x")%V.

  Lemma typed_pptr_from_own {𝔄} (p : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[p ◁ own_ptr (ty_size ty) ty] (PPtrFromOwn [p])
      (λ v, +[v ◁ own_ptr 1 (prod_ty ptr_ty (points_to_ty ty))])
      (λ post '-[(l, x)], λ mask, ∀ lc, post -[(lc, (l, (l, x)))] mask).
  Proof.
    move=> tid post mask iκs vπl.
    iIntros "#LFT #UNIQ #E L I TY #Obs"=>/=.
    destruct vπl as [[l x] []]. iDestruct "TY" as "(TY & _)".
    iDestruct "TY" as (pl d Heval) "[Hown %Hphys]".
    simpl in Hphys. injection Hphys=> ?; subst pl.
    destruct d as [|d];
      [by iDestruct (false_fml_sem_1 with "Hown") as "[]"|].
    rewrite own_ptr_gho /=. iDestruct "Hown" as "(Hl & Hfree & Hgho)".
    twp_bind p. iApply tgl_wp_wand; [by iApply twp_eval_path|]. iIntros (?->).
    twp_rec. twp_bind (new [ #1 ])%E. iApply (twp_new 1); [lia|done|].
    iIntros (l') "[Hfree' Hl']". twp_let.
    rewrite Z2Nat.inj_pos. change (Pos.to_nat 1) with 1%nat.
    rewrite /= heap_mapsto_vec_singleton.
    twp_bind (_ <- _)%E.
    iApply (twp_write_na (W:=verus_halt_wsat) _ _ l' (LitV (LitLoc l))
      with "[Hl']"); [iFrame "Hl'"|]. iIntros "Hl'". twp_seq.
    iExists -[(l', (l, (l, x)))]. iFrame "L I". iSplit; last first.
    { iDestruct "Obs" as %Hpost; iPureIntro. apply Hpost. }
    iSplit; [|done]. iExists #l', (S (S d)). iSplit; [done|].
    rewrite /ty_own own_ptr_gho /= prod_ty_gho /= tracked_ty_gho
      own_ptr_gho /= ptr_gho.
    iSplit; [|done]. iSplitL "Hl'".
    { iEval (rewrite -heap_mapsto_vec_singleton
        -(heap_mapsto_fancy_fmap_eq l')) in "Hl'". iExact "Hl'". }
    iSplitL "Hfree'".
    { rewrite freeable_sz_full. iDestruct "Hfree'" as "[A|%E0]";
        [by iLeft|iRight; iPureIntro; lia]. }
    iSplit; [done|]. iFrame "Hl Hfree".
    iDestruct (ty_gho_depth_mono with "Hgho") as "$"; [lia|lia].
  Qed.

  Lemma cloc_mapsto_empty_cells {𝔄} (ty: type 𝔄) l x tid :
    l ↦!∗ ty_phys ty x tid ⊣⊢
      (l, repeat (@nil cell_id) (ty_size ty)) #↦!∗ ty_phys ty x tid.
  Proof.
    rewrite -(ty_size_eq ty x tid).
    exact (heap_cloc_mapsto_fancy_empty l (ty_phys ty x tid)).
  Qed.

  Lemma mapsto_empty_cells {𝔄} (ty: type 𝔄) l x tid :
    l ↦!∗ ty_phys ty x tid ⊣⊢
      ((l, repeat (@nil cell_id) (ty_size ty)).1
        ↦[^ (l, repeat (@nil cell_id) (ty_size ty)).2]!∗
          ty_phys ty x tid).
  Proof.
    rewrite -(ty_size_eq ty x tid).
    exact (heap_mapsto_cells_fancy_empty l (ty_phys ty x tid)).
  Qed.

  Definition PPtrBorrow : val := (λ: ["ptr"; "perm_ref"], "ptr")%V.

  Lemma typed_pptr_borrow {𝔄} κ (ptr perm_ref : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[ptr ◁ ptr_ty; perm_ref ◁ shr_bor κ (points_to_ty ty)]
      (PPtrBorrow [ptr; perm_ref]) (λ v, +[v ◁ shr_bor κ ty])
      (λ post '-[l; (cl, (l', x))], λ mask,
        l = l' ∧ post -[((l, repeat [] ty.(ty_size)), x)] mask).
  Proof.
    move=> tid post mask iκs vπl.
    iIntros "#LFT #UNIQ #E L I TY #Obs"=>/=.
    destruct vπl as [l [[c [l' x]] []]].
    iDestruct "TY" as "(Hptr & Hperm & _)".
    iDestruct "Hptr" as (pl d Heval) "[_ %Hphys]".
    simpl in Hphys. injection Hphys=> ?; subst pl.
    iDestruct "Hperm" as (pl' d' Heval') "[Hshr %Hphys']".
    simpl in Hphys'. injection Hphys'=> ?; subst pl'.
    iDestruct (shr_bor_gho_elim with "Hshr") as (dd gg Hdd Hgg)
      "#(_ & Hshr' & Hstp)". iClear "Hshr". iRename "Hshr'" into "Hshr".
    iApply tgl_wpw_fupdw_nonval; [done|].
    iApply fupdw_tgl_wpw_nonval; [done|]. iIntros "W".
    iDestruct "Obs" as %HobsAll. pose proof HobsAll as HobsK.
    move: HobsAll=> [<- _].
    (* Open the stored persistent part, peel the tracked owning pointer off
       it, and park what is left for the shared borrow built below. *)
    iDestruct (wsat_split (W:=verus_halt_wsat) (W':=Wguard) with "W") as "[Wg Wr]".
    iDestruct (acc_ty_gho_pers with "Hstp") as "#Acc".
    iDestruct ("Acc" with "Wg") as "[Wg #Hpers]".
    rewrite tracked_ty_gho_pers own_ptr_gho_pers.
    destruct dd as [|dd0]; [by iDestruct "Hpers" as "[]"|]. simpl.
    iMod (store_ty_gho_pers ty x dd0 gg tid with "Hpers Wg") as "[Wg #St]".
    iDestruct (wsat_join (W:=verus_halt_wsat) with "Wg Wr") as "W".
    iDestruct (dguard_rhs_sep_l with "Hshr") as "#Hshrpt".
    iDestruct (dguard_rhs_sep_r with "Hshr") as "#Hshr3".
    iDestruct (dguard_rhs_sep_r with "Hshr3") as "#Hshrgho".
    iModIntro. iFrame "W".
    twp_bind ptr. iApply tgl_wp_wand; [by iApply twp_eval_path|].
    iIntros (?->). twp_bind perm_ref.
    iApply tgl_wp_wand; [by iApply twp_eval_path|]. iIntros (?->). twp_rec.
    iModIntro. iExists -[((l, repeat [] ty.(ty_size)), x)].
    iFrame "L I". iSplit; last first.
    { iPureIntro; move: HobsK=> [_ Hpost]. apply Hpost. }
    iSplit; [|done]. iExists (LitV (LitLoc l)), (S (dd0 + gg)).
    iSplit; [done|].
    (* The shared borrow's two indices are bounded, so the pieces are put
       back at exactly the depth and guard index they were taken at. *)
    rewrite /ty_own shr_bor_gho /by_lt /by_le. iSplit; [|done].
    iExists dd0. iSplit; [iPureIntro; lia|].
    iExists gg. iSplit; [iPureIntro; lia|]. iSplit.
    { have Hpt : ∀ sem', alt_sem sem' →
        sem' (mapsto_fml l (ty_phys ty x tid)) ⊣⊢
        sem' (cells_fml (l, repeat (@nil cell_id) (ty_size ty)).1
               (l, repeat (@nil cell_id) (ty_size ty)).2 (ty_phys ty x tid)).
      { move=> sem' Hs. rewrite /mapsto_fml !(cells_sem_at Hs) ty_size_eq //. }
      iApply (dguard_rhs_iff Hpt with "Hshrpt"). }
    by iFrame "Hshrgho St".
  Qed.

  (** [PPtrMutBorrow] is gone: [typing/] does not have it. *)
  (** [typed_pptr_borrow_mut] is gone: [typing/] does not have it. *)
End typing.
