(** * Memory copy, later-free and total, for [lrust_prob_lang]

  Forked from [nola/verus_halt/lang/lib/memcpy.v]; the [memcpy] value and
  its notations come from [lang/lib/memcpy.v] unchanged.

  Nola's header follows.

  * Memory copy, later-free and total

  Ported from VerusBelt ([lang/lib/memcpy.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer).

  The original's [wp_memcpy_guarded] is where the time-receipt machinery is at
  its most visible: it takes [⧖d ∗ £(6*d)], splits the budget as [£(3*d+3*d)],
  feeds one half to [wp_read_na_guarded_cells] and the other to
  [wp_write_na_guarded_more_credits], and threads the leftover credits through
  a [iLöb] induction.  All of that was in service of stripping the laters the
  guards introduce.  Later-free the budget disappears, the proof becomes a
  structural induction on the length (which is what the *total* weakest
  precondition needs anyway - [iLöb] is unavailable), and the plain
  [twp_memcpy] of the unguarded case comes out as a corollary. *)

From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From nola.bi Require Import modw guard.
From lrust.util Require Import total_cell_map.
From lrust.lang Require Export notation total_heap total_wsat
                               total_lifting_heap total_proofmode.
From lrust.lang.lib Require Export memcpy.
Set Default Proof Using "Type".
Import ModwNotation GuardNotation TglWpwNotation.

Section memcpy.
  Context `{!lrustTotGS FML Σ}.

  (** Copy [n] values from a guarded source into a guarded destination.

    The destination cells are owned ([l1 #↦∗ vl1]) but their *chain* is only
    guarded, which is why [Gw] is needed as well as [Gr]. *)
  Lemma twp_memcpy_guarded_sep `{!WsatIncl W na_wsat Wr} {s E} (n : nat) :
    ∀ (l1 l2 : cloc) vl1 vl2 Gw Gr,
    length vl1 = n → length vl2 = n →
    ∀ Φ,
    l1 #↦∗ vl1 -∗
    (na_sem Gw &&{na_wsat}&&> l1 #↦∗_) -∗
    (na_sem Gr &&{na_wsat}&&> (l2.1 ↦[^ l2.2]∗ vl2)) -∗
    na_sem Gw -∗ na_sem Gr -∗
    (l1 #↦∗ vl2 -∗ na_sem Gw -∗ na_sem Gr -∗ Φ (LitV LitPoison)) -∗
    WP[W] #(l1.1) <-{n} !#(l2.1) @ s; E [{ Φ }].
  Proof.
    elim: n.
    { move=> l1 l2 vl1 vl2 Gw Gr /nil_length_inv -> /nil_length_inv ->.
      iIntros (Φ) "↦ _ _ Gw Gr →Φ". twp_rec. twp_op. twp_case.
      by iApply ("→Φ" with "↦ Gw Gr"). }
    move=> n IH [l1 cs1][l2 cs2][|v1 vl1][|v2 vl2] Gw Gr //= [len1][len2].
    iIntros (Φ) "↦ #gw #gr Gw Gr →Φ".
    destruct cs1 as [|c1 cs1]; [by iDestruct "↦" as "[]"|].
    rewrite heap_mapsto_cloc_vals_vec_cons. iDestruct "↦" as "[↦1 ↦l]".
    (* split the two guards into head and tail *)
    iDestruct (guard_rhs_sep_l (Q:=((l1, c1) #↦_)%I)
      (R:=((l1 +ₗ 1, cs1) #↦∗_)%I) with "gw") as "#gw1".
    iDestruct (guard_rhs_sep_r (Q:=((l1, c1) #↦_)%I)
      (R:=((l1 +ₗ 1, cs1) #↦∗_)%I) with "gw") as "#gw2".
    iAssert ((na_sem Gr &&{na_wsat}&&> (l2 ↦[^ hd [] cs2] v2)) ∗
             (na_sem Gr &&{na_wsat}&&>
                ((l2 +ₗ 1) ↦[^ tail cs2]∗ vl2)))%I as "[#gr1 #gr2]".
    { destruct cs2 as [|c2 cs2].
      - (* vacuous: the source chain is too short, so the guard is on [False] *)
        iSplit; by iApply (guard_false with "gr").
      - iSplit.
        + iApply (guard_rhs_sep_l (Q:=(l2 ↦[^ c2] v2)%I)
            (R:=((l2 +ₗ 1) ↦[^ cs2]∗ vl2)%I) with "gr").
        + iApply (guard_rhs_sep_r (Q:=(l2 ↦[^ c2] v2)%I)
            (R:=((l2 +ₗ 1) ↦[^ cs2]∗ vl2)%I) with "gr"). }
    twp_rec. twp_op. twp_case.
    twp_bind (!#l2)%E.
    iApply (twp_read_guarded_cells with "gr1 Gr"). iIntros "Gr".
    twp_bind (#l1 <- v2)%E.
    iApply (twp_write_guarded with "gw1 Gw ↦1"). iIntros "Gw ↦1".
    twp_seq. do 3 twp_op.
    have -> : (S n - 1)%Z = n by lia.
    iApply (IH (l1 +ₗ 1, cs1) (l2 +ₗ 1, tail cs2) vl1 vl2 Gw Gr
      ltac:(done) ltac:(done) _ with "↦l gw2 gr2 Gw Gr").
    iIntros "↦l Gw Gr". iApply ("→Φ" with "[↦1 ↦l] Gw Gr").
    rewrite heap_mapsto_cloc_vals_vec_cons. iFrame.
  Qed.

  (** The same rule under Nola's name and in Nola's bundled shape: one
      precondition, then the continuation, which is what the Texan triple
      [nola/verus_halt/lang/lib/memcpy.v] states unfolds to.  The typing
      layer applies it that way, so keeping the shape means a ported file
      does not have to be edited at the call site. *)
  Lemma twp_memcpy_guarded `{!WsatIncl W na_wsat Wr} {s E} (n : nat) :
    ∀ (l1 l2 : cloc) vl1 vl2 Gw Gr,
    length vl1 = n → length vl2 = n →
    ∀ Φ,
    (l1 #↦∗ vl1 ∗
     (na_sem Gw &&{na_wsat}&&> l1 #↦∗_) ∗
     (na_sem Gr &&{na_wsat}&&> (l2.1 ↦[^ l2.2]∗ vl2)) ∗
     na_sem Gw ∗ na_sem Gr) -∗
    ((l1 #↦∗ vl2 ∗ na_sem Gw ∗ na_sem Gr) -∗ Φ (LitV LitPoison)) -∗
    WP[W] #(l1.1) <-{n} !#(l2.1) @ s; E [{ Φ }].
  Proof.
    iIntros (?????? ?? Φ) "(↦ & #gw & #gr & Gw & Gr) →Φ".
    iApply (twp_memcpy_guarded_sep n _ _ vl1 vl2 Gw Gr
      ltac:(done) ltac:(done) _ with "↦ gw gr Gw Gr").
    iIntros "↦ Gw Gr". iApply "→Φ". iFrame.
  Qed.

  (** The unguarded copy, as in Iris's lrust *)
  Lemma twp_memcpy `{!WsatIncl W na_wsat Wr} {s E} l1 l2 vl1 vl2 (n : nat) :
    length vl1 = n → length vl2 = n →
    ∀ Φ, l1 ↦∗ vl1 -∗ l2 ↦∗ vl2 -∗
    (l1 ↦∗ vl2 -∗ l2 ↦∗ vl2 -∗ Φ (LitV LitPoison)) -∗
    WP[W] #l1 <-{n} !#l2 @ s; E [{ Φ }].
  Proof.
    move: l1 l2 vl1 vl2. elim: n.
    { move=> ?? vl1 vl2 /nil_length_inv -> /nil_length_inv ->.
      iIntros (Φ) "↦1 ↦2 →Φ". twp_rec. twp_op. twp_case.
      by iApply ("→Φ" with "↦1 ↦2"). }
    move=> n IH ??[|v1 vl1][|v2 vl2]//=[len1][len2]. iIntros (Φ) "↦1 ↦2 →Φ".
    rewrite !heap_mapsto_vec_cons. iDestruct "↦1" as "[↦1 ↦1l]".
    iDestruct "↦2" as "[↦2 ↦2l]". twp_rec. twp_op. twp_case.
    twp_bind (Read _)%E. iApply (twp_read with "↦2"). iIntros "↦2".
    twp_bind (Write _ _)%E. iApply (twp_write_plain with "↦1").
    iIntros "↦1". twp_seq.
    do 3 twp_op. have -> : (S n - 1)%Z = n by lia.
    iApply (IH _ _ vl1 vl2 ltac:(done) ltac:(done) _ with "↦1l ↦2l").
    iIntros "↦1l ↦2l". iApply ("→Φ" with "[↦1 ↦1l] [↦2 ↦2l]").
    - iFrame.
    - iFrame.
  Qed.
End memcpy.
