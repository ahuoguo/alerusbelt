(** End to end: a shared invariant, later-free, over eris's total weakest
    precondition.

    The program allocates a cell, publishes it into a Nola simple
    invariant, then loops on a coin flip until it comes up [0] and reads
    the cell *through a guard* on the way out.

    Three things are happening at once, and none of them works in the
    partial setting the rest of this development uses:

    - the cell is shared through an invariant that hands back its contents
      with **no [▷]** ([nola.iris.sinv]'s [sinv_tok_guard]), so the read
      needs no later credit - under [tgl_wp] there is none to be had, and
      minting one would be unsound ([nola/bi/paradox.v]'s [twp_loop]);
    - the loop is **not** strongly normalizing, so no well-founded measure
      types it; it is discharged by credit amplification ([ec_ind_amp]);
    - the conclusion is quantitative: the program converges with
      probability at least [1 - ε], for every [ε > 0].

    The invariant here stores a first-order formula ([loc * val]), so it
    does not exercise impredicativity.  The mechanism is the same one that
    carries [cif] formulas in Nola's own port; what is demonstrated is
    that it composes with eris. *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.prob Require Import distribution countable_sum.
From clutch.eris Require Import total_weakestpre.
From nola.bi Require Import modw guard.
From nola.iris Require Import sinv guard iprop.
From lrust.lang Require Import lang notation heap lifting time
                               total_lifting total_error_rules
                               total_proofmode total_wsat total_guard
                               adequacy total_adequacy.
From lrust.util Require Import non_atomic_cell_map.
Set Default Proof Using "Type".
Import ModwNotation GuardNotation TglWpwNotation iPropAppNotation.

Local Open Scope R.

(** The formula type stored in the invariant: a location and the value it
    holds.  [constOF] is contractive, so [sinvΣ] applies. *)
Definition cellF : oFunctor := constOF (leibnizO (loc * val)).

Section sem.
  Context `{!lrustGS Σ}.

  (** Its interpretation. *)
  Definition cell_sm : positive → (cellF $oi Σ) → iProp Σ :=
    λ _ p, heap.heap_mapsto p.1 p.2.

  Global Instance cell_sm_ne i : NonExpansive (cell_sm i).
  Proof. intros ? [??] [??] [=->->]. done. Qed.
End sem.

(** [rand #2] samples from [{0,1}]; the loop exits on [0]. *)
Definition shared_loop : expr :=
  (rec: "f" ["l"] :=
     let: "x" := rand #2 in
     if: "x" = #0 then !"l" else "f" ["l"])%E.

Definition shared_body : expr := ("l" <- #42 ;; shared_loop ["l"])%E.

(** [reshape_val] builds a [RecV], which carries a [Closed] side condition;
    without this instance the proofmode cannot see through the [let]. *)
Local Instance shared_body_closed : Closed ["l"] shared_body.
Proof. unfold shared_body, shared_loop, Closed. simpl. done. Qed.

Definition shared_prog : expr := (let: "l" := Alloc #1 in shared_body)%E.

Local Instance shared_loop_app_closed (l : loc) :
  Closed [] (shared_loop [ Lit (LitLoc l) ])%E.
Proof. unfold shared_loop, Closed. simpl. done. Qed.

Section proof.
  Context `{!lrustGS Σ}.

  (** The refund schedule, capped at [1] so the rule's [ε2 n ≤ 1] side
      condition survives unbounded amplification. *)
  Definition cap2 (ε' : R) (n : nat) : R :=
    if (n =? 0)%nat then 0 else Rmin 1 (2 * ε').

  Lemma cap2_bounded ε' : 0 <= ε' → ∀ n, 0 <= cap2 ε' n <= 1.
  Proof.
    intros Hε' n. rewrite /cap2. case (Nat.eqb_spec n 0); intros; [lra|].
    split; [apply Rmin_glb; lra|apply Rmin_l].
  Qed.

  Lemma cap2_mean ε' : 0 <= ε' →
    SeriesC (λ n : nat,
        if bool_decide (n < Z.to_nat 2)%nat
        then (1 / Z.to_nat 2) * cap2 ε' n else 0) <= ε'.
  Proof.
    intros Hε'.
    rewrite (SeriesC_ext _ (λ n,
      if bool_decide (n <= 1)%nat
      then (1 / Z.to_nat 2) * cap2 ε' n else 0)); last first.
    { intros n. destruct (le_lt_dec n 1) as [Hle|Hgt].
      - rewrite !bool_decide_eq_true_2; [done|lia|simpl; lia].
      - rewrite !bool_decide_eq_false_2; [done|lia|simpl; lia]. }
    rewrite SeriesC_nat_bounded_to_foldr'. simpl. rewrite /cap2 /=.
    pose proof (Rmin_r 1 (2 * ε')). lra.
  Qed.

  (** The loop: terminates with probability [1 - ε] and returns the value
      it reads through the guard. *)
  Lemma shared_loop_spec W (l : loc) (v : val) (ε : R) :
    0 < ε →
    (True &&{W}&&> heap.heap_mapsto l v) -∗ ↯ ε -∗
    WP[W] shared_loop [ #l ] [{ w, ⌜w = v⌝ }].
  Proof.
    iIntros (Hε) "#Hg Hε".
    iApply (ec_ind_amp ε 2 _ ltac:(lra) ltac:(lra) with "[] Hε").
    iModIntro. iIntros (ε' Hε') "#Hrec Hε".
    rewrite {2}/shared_loop. twp_rec. twp_bind (rand _)%E.
    iApply (twpw_rand_exp_nat W 2 ε' (cap2 ε') with "Hε").
    { lia. }
    { apply cap2_bounded. lra. }
    { apply cap2_mean. lra. }
    iIntros (n) "[%Hn Hε]".
    destruct n as [|n']; last (assert (n' = 0)%nat as -> by lia).
    - (* heads: the refund is [↯ 0]; read the cell through the guard *)
      twp_let. twp_op. twp_case.
      iApply (twp_read_guard with "Hg [//]"); [solve_ndisj|].
      by iIntros "_".
    - (* tails: spend the doubled credit on another round *)
      twp_let. twp_op. twp_case. rewrite /cap2 /=.
      destruct (Rle_dec 1 (2 * ε')) as [Hge|Hlt].
      + rewrite Rmin_left; [|lra].
        by iDestruct (ec_contradict with "Hε") as "[]".
      + rewrite Rmin_right; [|lra]. by iApply "Hrec".
  Qed.

  (** The whole program, under a [sinv] world satisfaction. *)
  Lemma shared_prog_spec `{!sinvGS cellF Σ} (ε : R) :
    0 < ε →
    sinv_wsat cell_sm -∗ ↯ ε -∗
    sinv_wsat cell_sm ∗
      WP[sinv_wsat cell_sm] shared_prog [{ w, ⌜w = #42⌝ }].
  Proof.
    iIntros (Hε) "HW Hε". iFrame "HW". rewrite /shared_prog.
    twp_apply (twpw_alloc (sinv_wsat cell_sm) ⊤ 1 _ _ ltac:(lia)).
    iIntros (l sz) "%Hsz Hf Hl".
    assert (sz = 1%nat) as -> by lia. simpl.
    rewrite heap.heap_mapsto_vec_singleton.
    twp_let. rewrite /shared_body /shared_loop. simpl_subst.
    rewrite -/shared_loop. twp_bind (Write _ _)%E.
    iApply (twpw_write with "Hl"); [solve_ndisj|]. iIntros "Hl".
    twp_seq.
    (* publish the cell into the simple invariant, later-free *)
    iApply fupdw_tgl_wpw_nonval; [done|]. iIntros "HW".
    iDestruct (sinv_tok_alloc_suspend (sm:=cell_sm) (l, #42) with "HW")
      as (I) "Halloc".
    iMod ("Halloc" $! (fresh I) with "[%]") as "[#tok Hback]";
      [apply is_fresh|].
    iDestruct ("Hback" with "Hl") as "HW". iModIntro. iFrame "HW".
    (* and read it back through the guard the token provides *)
    iApply (shared_loop_spec _ l #42 ε); [done|..]; last done.
    iApply (sinv_tok_guard (sm := cell_sm) with "tok").
  Qed.

End proof.

(** Operational conclusion. *)
Theorem shared_prog_terminates `{!lrustErisGpreS Σ, !sinvGpreS cellF Σ}
    (σ : common.language.state lrust_prob_lang) (ε : R) :
  (∀ l ls v, σ !! l = Some (ls, v) → ls = RSt 0%nat) →
  0 < ε →
  1 - ε <= SeriesC (lim_exec (shared_prog, σ)).
Proof.
  intros Hσ Hε.
  eapply (lrust_twpw_mass_lim_exec _ _ ε 0%nat); [done|lra|].
  intros HlrustGS. iIntros "_ Hε".
  iMod (sinv_wsat_alloc (FML:=cellF)) as (Hsinv) "Hmk".
  iDestruct ("Hmk" $! cell_sm with "[]") as "HW".
  { iIntros (i). iApply ne_internal_ne; apply _. }
  iDestruct (shared_prog_spec ε with "HW Hε") as "[HW Hwp]"; [done|].
  iModIntro. iExists (sinv_wsat cell_sm). iFrame "HW".
  iApply (tgl_wp_mono with "Hwp"). by iIntros (?) "_".
Qed.
