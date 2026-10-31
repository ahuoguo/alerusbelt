(** * The base (empty) type used for fixpoints

  Ported from VerusBelt ([typing/base_type.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer). *)

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

Implicit Type 𝔄 𝔅: syn_type.

(* [base] is a version of the empty type used internally in the model, using an
  arbitrary refinement type. It is used for the base case of the fixpoint
  type. *)

Section base.
  Context `{!typeG FML Σ}.

  Program Definition base {𝔄} : type 𝔄 := {|
    ty_size := size_of 𝔄;
    ty_lev := 0;
    ty_lfts := [];
    ty_E := [];
    ty_gho_persx x d g tid := false_fml;
    ty_ghox x d g tid := false_fml;
    ty_phys x tid := @syn_phys 𝔄 x;
  |}.
  Next Obligation. intros. apply syn_phys_size_eq. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    move=> ? sem H *. rewrite (false_sem_at H). by iIntros "[]".
  Qed.
  Next Obligation.
    move=> ? sem H *. rewrite (false_sem_at H). by iIntros "[]".
  Qed.
  (** The [ty_guard_proph] obligation is gone with the field; see
    [typing_total/type.v]. *)
  Next Obligation. move=> ? sem H *. rewrite (false_sem_at H). exact _. Qed.
  Next Obligation. move=> *. rewrite false_fml_sem. by iIntros "[]". Qed.
  
  Lemma base_gho {𝔄} (x: ~~𝔄) d g tid : ty_gho base x d g tid ⊣⊢ False.
  Proof. apply false_fml_sem. Qed.
  Lemma base_gho_pers {𝔄} (x: ~~𝔄) d g tid :
    ty_gho_pers base x d g tid ⊣⊢ False.
  Proof. apply false_fml_sem. Qed.

  Global Instance base_copy {𝔄} : Copy (@base 𝔄).
  Proof.
    split=>//. { exact _. }
    move=> *. iIntros "A". by iDestruct (false_fml_sem_1 with "A") as "[]".
  Qed.

  Global Instance base_send {𝔄} : Send (@base 𝔄).
  Proof. split=>//.
     - intros. by apply syn_abstract_phys_eq.
     - move=> tid tid' x d g G κs. iIntros "_ _ _ _ _ A".
       by iDestruct (false_fml_sem_1 with "A") as "[]".
  Qed.

  Global Instance base_sync {𝔄} : Sync (@base 𝔄).
  Proof. done. Qed.

  (** [base_resolve] removed along with [resolve]. *)

  Lemma base_subtype {𝔄 𝔅} (f : 𝔄 →ₛ 𝔅) E L :
    (∀ x, ξl x = ξl ((~~!ₛ) f x)) →
    (size_of 𝔄 = size_of 𝔅) →
    (∀ x, syn_phys x = syn_phys ((~~!ₛ) f x)) →
    subtype E L (base) (base) f.
  Proof.
    move=> Eq Eq2 Eq3. iIntros "L". iModIntro. iIntros "E". iSplit; [|iSplit; [|iSplit; [|iSplit]]].
      - iPureIntro. rewrite <- ty_size_eq2. by rewrite <- ty_size_eq2.
      - iApply dincl_refl.
      - iIntros "!>" (sem Hsem ????) "A".
        rewrite (false_sem_at Hsem). by iDestruct "A" as "[]".
      - iIntros "!>" (sem Hsem ????) "A".
        rewrite (false_sem_at Hsem). by iDestruct "A" as "[]".
      - iPureIntro. simpl. intros. rewrite Eq3. trivial.
  Qed.

  Lemma base_eqtype {𝔄 𝔅} (f : 𝔄 →ₛ 𝔅) (g : 𝔅 →ₛ 𝔄) E L :
    (∀ x, ξl x = ξl ((~~!ₛ) f x)) →
    (∀ x, ξl x = ξl ((~~!ₛ) g x)) →
    (size_of 𝔄 = size_of 𝔅) →
    (∀ x, syn_phys x = syn_phys ((~~!ₛ) f x)) →
    (∀ x, syn_phys x = syn_phys ((~~!ₛ) g x)) →
    eqtype E L (base) (base) f g.
  Proof. split; exact: base_subtype. Qed.

End base.

Global Hint Rewrite @base_gho @base_gho_pers : fml_sem.

Global Hint Resolve base_subtype base_eqtype : lrust_typing.
