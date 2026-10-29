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
From lrust.lang.lib Require Export new_delete.
Set Default Proof Using "Type".
Import ModwNotation GuardNotation TglWpwNotation.

Open Scope Z_scope.

Section specs.
  Context `{!lrustTotGS FML Σ}.

  Lemma twp_new W s E (n : Z) Φ :
    0 ≤ n →
    (∀ l, (total_heap.heap_freeable l 1 (Z.to_nat n) ∨ ⌜n = 0⌝) -∗
       total_heap.heap_mapsto_vec l (repeat (LitV LitPoison) (Z.to_nat n)) -∗
       Φ (LitV (LitLoc l))) -∗
    WP[W] new [ #n ] @ s; E [{ Φ }].
  Proof.
    iIntros (Hn) "HΦ". rewrite /new. twp_lam. twp_op. twp_case.
    case_bool_decide as Hle.
    - assert (n = 0) as -> by lia.
      iApply (tgl_wp_value' (erisWpGS0 := ErisW W) _ _ _
                (LitV (LitLoc (42%positive, 1337)))).
      iApply ("HΦ" with "[] []"); [by iRight|].
      by rewrite /= total_heap.heap_mapsto_vec_nil.
    - iApply (twp_alloc W s E n); [lia|]. iIntros (l sz Hsz) "Hf Hl".
      assert (Z.to_nat n = sz) as -> by lia.
      iApply ("HΦ" with "[Hf] Hl"). by iLeft.
  Qed.

  Lemma twp_delete `{!WsatIncl W na_wsat Wr} s E vl (n : Z) l Φ :
    n = length vl →
    total_heap.heap_mapsto_vec l vl -∗
    (total_heap.heap_freeable l 1 (length vl) ∨ ⌜n = 0⌝) -∗
    Φ (LitV LitPoison) -∗
    WP[W] delete [ #n; #l ] @ s; E [{ Φ }].
  Proof.
    iIntros (Hn) "Hl Hf HΦ". rewrite /delete. twp_lam. twp_op. twp_case.
    case_bool_decide as Hle.
    - iApply (tgl_wp_value' (erisWpGS0 := ErisW W) _ _ _ (LitV LitPoison)).
      done.
    - iDestruct "Hf" as "[Hf|%]"; last lia.
      by iApply (twp_free with "Hl Hf HΦ").
  Qed.

End specs.
