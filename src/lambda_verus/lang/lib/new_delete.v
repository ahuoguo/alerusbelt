From lrust.lang Require Export notation.
From lrust.lang Require Import heap proofmode.
From lrust.lang.lib Require Import memcpy.
(** [new], [delete] and the [letalloc:] notations now live beside no
    program logic at all, so that the total stack can have them without
    the partial one's [lrustGS]; see [lib/new_delete_defs.v]. *)
From lrust.lang.lib Require Export new_delete_defs.
Set Default Proof Using "Type".
Open Scope Z_scope.

Section specs.
  Context `{!lrustGS Σ}.

  Lemma wp_new E n:
    0 ≤ n →
    {{{ True }}} new [ #n ] @ E
    {{{ l, RET LitV $ LitLoc l;
        (†l…(Z.to_nat n) ∨ ⌜n = 0⌝) ∗ l ↦∗ repeat (LitV LitPoison) (Z.to_nat n) }}}.
  Proof.
    iIntros (? Φ) "_ HΦ". rewrite /new. wp_lam. wp_op; case_bool_decide.
    - wp_if. assert (n = 0) as -> by lia. iApply "HΦ".
      rewrite heap_mapsto_vec_nil. auto.
    - wp_if. wp_alloc l as "H↦" "H†"; first lia.
      iApply "HΦ". rewrite (_: Z.to_nat n = sz); [iFrame|lia].
  Qed.

  Lemma wp_delete vl (n: Z) l E :
    ↑non_atomic_cell_map.naN ⊆ E → n = length vl →
    {{{ l ↦∗ vl ∗ (†l…(length vl) ∨ ⌜n = 0⌝) }}}
      delete [ #n; #l] @ E
    {{{ RET #☠; True }}}.
  Proof.
    iIntros (?? Φ) "(H↦ & [H†|%]) HΦ";
      rewrite /delete; wp_lam; wp_op; case_bool_decide; try lia;
      wp_if; try wp_free; by iApply "HΦ".
  Qed.
End specs.
