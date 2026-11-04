(** * Fractional deallocation permission

  Ported from VerusBelt ([typing/freeable_util.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer), itself from RustBelt.

  Pure resource arithmetic over [†{q}l…n]: no laters, no guards, nothing to
  change. *)

From iris.proofmode Require Import proofmode.
From lrust.typing_total Require Export type ctx.
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

Section freeable.
  Context `{!typeG FML Σ}.

  (** [freeable_sz] itself lives in [typing/ctx.v]: the formula language has
    to be able to express it, for [own_ptr]. *)

  Lemma freeable_sz_full n l : freeable_sz n n l ⊣⊢ †{1}l…n ∨ ⌜Z.of_nat n = 0⌝.
  Proof.
    case n=> [|n']. { iSplit; iIntros; by [iRight|]. }
    have ->: Z.of_nat (S n') = 0 ↔ False by done.
    by rewrite right_id /freeable_sz Qp.div_diag.
  Qed.

  Lemma freeable_sz_full_S n l : freeable_sz (S n) (S n) l ⊣⊢ †{1}l…(S n).
  Proof.
    rewrite freeable_sz_full. iSplit; [|iIntros; by iLeft]. by iIntros "[$|%]".
  Qed.

  Lemma freeable_sz_split n sz sz' l :
    freeable_sz n sz l ∗ freeable_sz n sz' (l +ₗ sz) ⊣⊢
    freeable_sz n (sz + sz') l.
  Proof.
    case sz; [|case sz'; [|rewrite /freeable_sz; case n]]=>/= *.
    - by rewrite left_id shift_loc_0.
    - by rewrite right_id Nat.add_0_r.
    - iSplit; by [iIntros "[??]"|iIntros].
    - rewrite heap_freeable_op_eq. f_equiv; [|done].
      by rewrite -Qp.div_add_distr pos_to_Qp_add -Nat2Pos.inj_add.
  Qed.

  Lemma freeable_sz_eq n sz sz' l :
    sz = sz' → freeable_sz n sz l -∗ freeable_sz n sz' l.
  Proof. iIntros (->) "$". Qed.

  (* Make sure 'simpl' doesn't unfold. *)
  Global Opaque freeable_sz.
End freeable.
