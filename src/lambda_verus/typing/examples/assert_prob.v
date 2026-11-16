From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.

From lrust.lang Require Import notation lifting proofmode tactics.
From lrust.typing Require Import type type_context programs cont function
                                  own bool int uninit product mod_ty.
Set Default Proof Using "Type".

Local Open Scope R.

(** [assert]: a closed value that takes a bool argument [b], returns
    [#0] on [true], and goes to UB ([!(#☠)]) on [false].  Simple
    (no fn-type wrapping) — coin_flip uses this with [wp_assert]. *)
Definition assert : val :=
  (λ: ["b"], if: "b" then #0 else !(#☠))%V.

Section assert_spec.
  Context `{!lrustGS Σ}.

  (** Combined WP spec: pay [↯ 1] on [false], nothing on [true].
      The two single-branch lemmas below are corollaries. *)
  Lemma wp_assert (b : bool) E :
    (if b then True%I else ↯ 1) ⊢ WP (assert [ #b ])%E @ E {{ _, True }}.
  Proof.
    iIntros "H". rewrite /assert. unlock.
    wp_lam. wp_if.
    destruct b.
    - by iApply pgl_wp_value.
    - iExFalso. iApply (ec_contradict with "H"). lra.
  Qed.

  Lemma wp_assert_true E :
    ⊢ WP (assert [ #true ])%E @ E {{ _, True }}.
  Proof. iApply (wp_assert true). done. Qed.

  Lemma wp_assert_false E :
    ↯ 1 ⊢ WP (assert [ #false ])%E @ E {{ _, True }}.
  Proof. iApply (wp_assert false). Qed.

End assert_spec.

(** The fn-typed assertion is upstream's [assert]/[assert_type] in
    [examples/assert.v] (typed against the prophetic function type). *)
