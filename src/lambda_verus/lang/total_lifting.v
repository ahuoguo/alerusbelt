(** Lifting lemmas for [lrust_prob_lang]'s *total* weakest precondition.

    [tgl_wp] is [bi_least_fixpoint tgl_wp_pre'], and [tgl_wp_pre] carries
    no [▷] and no [£ (S (num_laters_per_step n))]: a step hands back
    [state_interp (S n) σ2 ∗ err_interp ε2 ∗ wp] and nothing else.  So the
    partial rules of [lifting.v] port by deleting their [iNext] and their
    [time_interp_step] is still available (the step index still advances),
    but no later credits are minted.

    That is why only the *unguarded* heap rules appear here.  The guarded
    ones ([wp_read_guarded_cell], [wp_write_guarded]) demand [£d] to strip
    the [▷] a Leaf guard produces over [ownI], and under [twp] there is no
    credit to pay with.  Removing those laters is a separate piece of work;
    see [PLAN-TOTAL-ERIS.md] §3-4. *)
Require Import guarding.internal.na_invariants_fork.
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From clutch.eris Require Export total_weakestpre.
From clutch.eris Require Import total_lifting total_ectx_lifting.
From clutch.base_logic Require Export error_credits.
From clutch.prob Require Import distribution.
From lrust.lang Require Export lang time lifting.
From lrust.lang Require heap.
From lrust.util Require Import non_atomic_cell_map.
Set Default Proof Using "Type".

Open Scope Z_scope.

Section total_lifting.
  Context `{!lrustGS Σ}.

  (** [Rand]: uniform sampling over [0..N-1]. *)
  Lemma twp_rand E (N : Z) (Φ : val → iProp Σ) s :
    (0 < N)%Z →
    (∀ (n : fin (S (Z.to_nat N - 1))),
       Φ (LitV (LitInt (Z.of_nat (fin_to_nat n))))) -∗
    WP Rand (Lit (LitInt N)) @ s; E [{ Φ }].
  Proof.
    iIntros (HN) "HΦ".
    iApply twp_lift_atomic_head_step; [done|].
    iIntros (ns σ1) "[Hσ Ht]". iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose". iSplit.
    { iPureIntro. rewrite /head_reducible /=.
      rewrite bool_decide_eq_true_2 //.
      eexists (_, _). apply dmap_pos. exists 0%fin. split; first done.
      apply dunifP_pos. }
    iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= in Hstep.
    rewrite bool_decide_eq_true_2 in Hstep; last done.
    apply dmap_pos in Hstep as (n & [= -> ->] & _).
    iMod (time_interp_step with "Ht") as "Ht".
    iModIntro. iFrame "Hσ Ht". by iApply "HΦ".
  Qed.

  (** [Alloc]: fresh-block allocation. *)
  Lemma twp_alloc E (n : Z) s :
    (0 < n)%Z →
    [[{ True }]] Alloc (Lit (LitInt n)) @ s; E
    [[{ (l : loc) (sz : nat), RET LitV (LitLoc l);
        ⌜n = sz⌝ ∗ heap.heap_freeable l 1 sz ∗
        heap.heap_mapsto_vec l (repeat (LitV LitPoison) sz) }]].
  Proof.
    iIntros (Hn Φ) "_ HΦ".
    iApply twp_lift_atomic_head_step; [done|].
    iIntros (ns σ1) "[Hσ Ht]".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. rewrite /head_reducible /=.
      rewrite bool_decide_eq_true_2 //.
      eexists (_, _). rewrite dret_pmf_unfold bool_decide_eq_true_2 //. lra. }
    iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= in Hstep.
    rewrite bool_decide_eq_true_2 in Hstep; last done.
    apply dret_pos in Hstep as [= -> ->].
    iMod (heap.heap_alloc with "Hσ") as "(Hσ & Hf & Hl)"; [exact Hn| |].
    { intros m.
      assert (fresh_loc σ1 +ₗ m = (fresh_block σ1, m)) as ->;
        [rewrite /fresh_loc /shift_loc /=; f_equal; lia|].
      apply is_fresh_block. }
    iMod (time_interp_step with "Ht") as "Ht".
    iModIntro. iFrame "Hσ Ht".
    iApply ("HΦ" $! _ (Z.to_nat n)). iFrame. iPureIntro. lia.
  Qed.

  (** [Read] from a non-atomic cell at read-state 0. *)
  Lemma twp_read E l v s :
    ↑non_atomic_cell_map.naN ⊆ E →
    [[{ heap.heap_mapsto l v }]] Read (Lit (LitLoc l)) @ s; E
    [[{ RET v; heap.heap_mapsto l v }]].
  Proof.
    iIntros (HE Φ) "Hl HΦ".
    iApply twp_lift_atomic_head_step; [done|].
    iIntros (ns σ1) "[Hσ Ht]". iDestruct "Hσ" as (hF) "(Hh & Hf & %REL & ato)".
    iMod (non_atomic_cell_map.points_to_heap_reading0 with "Hl Hh")
      as "(Hl & Hh & %Hσl)"; [done|].
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. rewrite /head_reducible /= Hσl /=.
      eexists (_, _). rewrite dret_pmf_unfold bool_decide_eq_true_2 //. lra. }
    iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= Hσl in Hstep.
    apply dret_pos in Hstep as [= -> ->].
    iMod (time_interp_step with "Ht") as "Ht".
    iModIntro. iSplitL "Hh Hf ato Ht"; [iSplitR "Ht"; [iExists hF; by iFrame|by iFrame]|].
    rewrite language.to_of_val /=. by iApply ("HΦ" with "Hl").
  Qed.

  (** [Write] to a non-atomic cell at read-state 0. *)
  Lemma twp_write E l v v' s :
    ↑non_atomic_cell_map.naN ⊆ E →
    [[{ heap.heap_mapsto l v }]] Write (Lit (LitLoc l)) (of_val v') @ s; E
    [[{ RET LitV LitPoison; heap.heap_mapsto l v' }]].
  Proof.
    iIntros (HE Φ) "Hl HΦ".
    iApply twp_lift_atomic_head_step; [done|].
    iIntros (ns σ1) "[Hσ Ht]". iDestruct "Hσ" as (hF) "(Hh & Hf & %REL & ato)".
    iMod (non_atomic_cell_map.atomic_write _ _ _ v' with "Hl Hh")
      as "(%Hσl & Hl & Hh)"; [done|].
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. rewrite /head_reducible /=. rewrite to_of_val Hσl.
      eexists (_, _). rewrite dret_pmf_unfold bool_decide_eq_true_2 //. lra. }
    iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= to_of_val Hσl in Hstep.
    apply dret_pos in Hstep as [= -> ->].
    iMod (time_interp_step with "Ht") as "Ht".
    iModIntro. iSplitL "Hh Hf ato Ht".
    { iSplitR "Ht"; last by iFrame. iExists hF. iFrame.
      iPureIntro. eauto using heap.heap_freeable_rel_stable. }
    by iApply ("HΦ" with "Hl").
  Qed.

  (** [Free]. *)
  Lemma twp_free E (n : Z) l vl s :
    ↑non_atomic_cell_map.naN ⊆ E →
    n = length vl →
    [[{ heap.heap_mapsto_vec l vl ∗ heap.heap_freeable l 1 (length vl) }]]
      Free (Lit (LitInt n)) (Lit (LitLoc l)) @ s; E
    [[{ RET LitV LitPoison; True }]].
  Proof.
    iIntros (HE Hn Φ) "[Hl Hf] HΦ".
    iApply twp_lift_atomic_head_step; [done|].
    iIntros (ns σ1) "[Hσ Ht]".
    iMod (heap.heap_free with "Hσ Hl Hf") as "(%Hpos & %Hbnd & Hσ)"; [done..|].
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. rewrite /head_reducible /=. rewrite bool_decide_eq_true_2 //.
      eexists (_, _). rewrite dret_1_1 //. lra. }
    iIntros (e2 σ2 Hstep). iMod "Hclose" as "_".
    rewrite /ectx_language.head_step /= /head_step_prob /= in Hstep.
    rewrite bool_decide_eq_true_2 in Hstep; last done.
    apply dret_pos in Hstep as [= -> ->].
    iMod (time_interp_step with "Ht") as "Ht".
    iModIntro. iFrame "Hσ Ht". by iApply "HΦ".
  Qed.

End total_lifting.
