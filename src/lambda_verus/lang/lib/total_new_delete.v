(** Total specifications for the allocation wrappers.

    The [new] and [delete] values and the [letalloc:] notations are
    language-level and come from [lang/lib/new_delete.v] unchanged; only
    the specifications are redone, over [tgl_wpw] and the later-free
    heap.  Following [nola/verus_halt/lang/lib/new_delete.v], the mask
    side condition [↑naN ⊆ E] on [wp_delete] becomes the
    world-satisfaction inclusion [WsatIncl W na_wsat Wr]. *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From nola.bi Require Import modw guard.
From lrust.util Require Import total_cell_map.
From lrust.lang Require Export notation total_heap total_wsat
                               total_lifting_heap total_proofmode.
(** [new_delete_defs], not [new_delete]: the latter carries the *partial*
    specifications, and exporting it would put the partial stack's
    [lrustGS] into scope all the way up the total typing layer.  See the
    note at the head of [lib/new_delete_defs.v] for what that cost. *)
From lrust.lang.lib Require Export new_delete_defs.
Set Default Proof Using "Type".
Import ModwNotation GuardNotation TglWpwNotation.

Open Scope Z_scope.

Section specs.
  Context `{!lrustTotGS FML Σ}.

  (** Nola's shape, written out: Nola states this as a Texan triple with
      precondition [True], and the typing layer applies it as
      [iApply twp_new; [lia|done|]] - the [done] is that [True].  The total
      stack has no Texan triples (see [lang/total_wsat.v]), so the triple
      is spelled out, which is what [iApply] sees anyway. *)
  Lemma twp_new {W s E} (n : Z) {Φ} :
    0 ≤ n →
    True -∗
    (∀ l, ((total_heap.heap_freeable l 1 (Z.to_nat n) ∨ ⌜n = 0⌝) ∗
       total_heap.heap_mapsto_vec l (repeat (LitV LitPoison) (Z.to_nat n))) -∗
       Φ (LitV (LitLoc l))) -∗
    WP[W] new [ #n ] @ s; E [{ Φ }].
  Proof.
    iIntros (Hn) "_ HΦ". rewrite /new. twp_lam. twp_op. twp_case.
    case_bool_decide as Hle.
    - assert (n = 0) as -> by lia.
      iApply (tgl_wp_value' (erisWpGS0 := ErisW W) _ _ _
                (LitV (LitLoc (42%positive, 1337)))).
      iApply "HΦ". iSplitR; [by iRight|].
      by rewrite /= total_heap.heap_mapsto_vec_nil.
    - iApply (twp_alloc W s E n); [lia|]. iIntros (l sz Hsz) "Hf Hl".
      assert (Z.to_nat n = sz) as -> by lia.
      iApply "HΦ". iFrame "Hl". by iLeft.
  Qed.

  Lemma twp_delete `{!WsatIncl W na_wsat Wr} {s E} vl (n : Z) l {Φ} :
    n = length vl →
    (total_heap.heap_mapsto_vec l vl ∗
      (total_heap.heap_freeable l 1 (length vl) ∨ ⌜n = 0⌝)) -∗
    (True -∗ Φ (LitV LitPoison)) -∗
    WP[W] delete [ #n; #l ] @ s; E [{ Φ }].
  Proof.
    iIntros (Hn) "[Hl Hf] HΦ'".
    iAssert (Φ (LitV LitPoison)) with "[HΦ']" as "HΦ"; [by iApply "HΦ'"|].
    rewrite /delete. twp_lam. twp_op. twp_case.
    case_bool_decide as Hle.
    - iApply (tgl_wp_value' (erisWpGS0 := ErisW W) _ _ _ (LitV LitPoison)).
      done.
    - iDestruct "Hf" as "[Hf|%]"; last lia.
      by iApply (twp_free with "Hl Hf HΦ").
  Qed.

End specs.
