(** * Tracked types

  Ported from VerusBelt ([typing/tracked.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer).

  [Tracked<T>] is [T] with the physical contents cleared out.  Everything is
  inherited from [ty], so nothing here changes in the later-free setting. *)

From iris.proofmode Require Import proofmode.
From lrust.typing_total Require Import programs.
From lrust.typing_total Require Export type ctx.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation.
(** Our [util] last, so that its [SemiIso] wins the name over Nola's; see
  [typing_total/type.v]. *)
From lrust.util Require Import basic.
Unset Default Proof Using.
(** [iris.prelude.options] sets [Default Goal Selector "!"], which rejects a
  bare tactic while more than one goal is focused.  It reaches this file
  through our imports and not through Nola's, so Nola's proofs - written
  against the default [1], "act on the first goal" - would otherwise need a
  focus fix every few lemmas.  Restoring [1] is a lint setting, not a
  soundness one. *)
Set Default Goal Selector "1".
Unset Suggest Proof Using.

Section tracked.
  Context `{!typeG FML Σ}.

  Program Definition tracked_ty {𝔄} (ty: type 𝔄) : type (trackedₛ 𝔄) := {|
    ty_size := 0;
    ty_lev := 0;
    ty_lfts := ty.(ty_lfts);
    ty_E := ty.(ty_E);
    ty_ghox x d g tid := ty.(ty_ghox) x d g tid ;
    ty_gho_persx x d g tid := ty.(ty_gho_persx) x d g tid ;
    ty_phys x tid := [];
  |}%I.
  Next Obligation. intros; done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    intros 𝔄 ty sem H d g d' g' x tid Hd Hg.
    by apply (ty_gho_depth_mono_at ty sem H).
  Qed.
  Next Obligation.
    intros 𝔄 ty sem H d g d' g' x tid Hd Hg.
    by apply (ty_gho_pers_depth_mono_at ty sem H).
  Qed.
  (** The [guard_proph] obligation is gone with the field; see [typing_total/type.v]. *)
  Next Obligation.
    intros 𝔄 ty sem H x d g tid. apply (ty_gho_pers_pers_at ty sem H).
  Qed.
  Next Obligation. intros. apply (ty_gho_pers_impl); trivial. Qed.

  Lemma tracked_ty_gho {𝔄} (ty: type 𝔄) x d g tid :
    ty_gho (tracked_ty ty) x d g tid ⊣⊢ ty_gho ty x d g tid.
  Proof. done. Qed.
  Lemma tracked_ty_gho_pers {𝔄} (ty: type 𝔄) x d g tid :
    ty_gho_pers (tracked_ty ty) x d g tid ⊣⊢ ty_gho_pers ty x d g tid.
  Proof. done. Qed.

  Global Instance tracked_ne {𝔄} : NonExpansive (@tracked_ty 𝔄).
  Proof. solve_ne_type. Qed.

  Global Instance tracked_send {𝔄} (ty : type 𝔄) : Send ty → Send (tracked_ty ty).
  Proof. intros [Hphys Hgho]. split; trivial. Qed.

  Global Instance tracked_sync {𝔄} (ty : type 𝔄) : Sync ty → Sync (tracked_ty ty).
  Proof.
    intros Hsync tid tid' x d g.
    destruct (Hsync tid tid' x d g) as [A [B C]].
    split; [done|]. split; [exact B|exact C].
  Qed.

  Global Instance tracked_copy {𝔄} (ty : type 𝔄) : Copy ty → Copy (tracked_ty ty).
  Proof.
    intros Hcopy. destruct Hcopy. split; trivial. intros. iIntros "_".
    iPureIntro. done.
  Qed.

  (** [tracked_resolve] removed along with [resolve]: it resolves a type's
    prophecies, and there are none. *)

  (** Subtyping *)

  Lemma tracked_type_incl {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) f :
    type_incl ty ty' f ⊢ type_incl (tracked_ty ty) (tracked_ty ty') (tracked_mapₛ f).
  Proof. iIntros "(A & B & C & D & E)". iFrame. iSplit; done. Qed.

  Lemma tracked_subtype {𝔄 𝔅} E L (ty: type 𝔄) (ty': type 𝔅) f :
    subtype E L ty ty' f →
    subtype E L (tracked_ty ty) (tracked_ty ty') (tracked_mapₛ f).
  Proof.
    intros Hsub. iIntros "A". iDestruct (Hsub with "A") as "#B". iModIntro.
    iIntros "E". iApply tracked_type_incl. iApply "B". iFrame.
  Qed.

  Lemma tracked_eqtype {𝔄 𝔅} E L (ty: type 𝔄) (ty': type 𝔅) f g :
    eqtype E L ty ty' f g →
    eqtype E L (tracked_ty ty) (tracked_ty ty') (tracked_mapₛ f) (tracked_mapₛ g).
  Proof. intros [Ha Hb]. split; apply tracked_subtype; trivial. Qed.

End tracked.

Global Hint Rewrite @tracked_ty_gho @tracked_ty_gho_pers : fml_sem.

