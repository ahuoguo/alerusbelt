(** The later-free stack, end to end, on VerusBelt's own heap.

    The program allocates a cell, publishes it into a simple invariant,
    then loops on a coin flip until it comes up [0] and reads the cell
    *through a guard* on the way out.

    Against [lang/total_sinv_example.v] - which did the same over the
    *partial* heap, by handing the whole points-to across the guard - this
    goes through VerusBelt's points-to cell logic: the read is
    [twp_read_guarded_cells], the counterpart of [lifting.v]'s

      wp_read_guarded_cell : {{{ (G &&{↑NllftG; d}&&> l #↦ v) ∗ G ∗ £ d }}} …

    with the [£ d] gone, because the guard carries no [▷] once its storage
    is an explicit world satisfaction rather than an Iris invariant.

    The formula language is first order ([cellfml] below), which is enough
    to instantiate [NaSem] and [HeapSem] and so to make the two classes
    non-vacuous.  Nola's own port instantiates them with [cif]; what is
    shown here is that the interfaces are inhabited and that the whole
    stack - cell logic, heap, program logic, adequacy - closes over eris's
    total weakest precondition. *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.prob Require Import distribution countable_sum.
From clutch.eris Require Import total_weakestpre.
From nola.bi Require Import modw guard.
From nola.iris Require Import sinv guard iprop.
From nola.verus_halt Require Import na_inv_fork.
From nola.verus_halt.util Require Import atomic_lock_counter.
From lrust.util Require Import total_cell_map.
(** [total_proofmode] is imported *before* [total_lifting_heap]: it pulls in
    [total_lifting], whose [twp_alloc] etc. are the partial heap's and would
    otherwise shadow this stack's. *)
From lrust.lang Require Import lang notation total_proofmode.
From lrust.lang Require Import total_heap total_wsat
                               total_lifting_heap total_heap_adequacy.
Set Default Proof Using "Type".
Import ModwNotation GuardNotation TglWpwNotation iPropAppNotation.

Local Open Scope R.

(** ** A first-order formula language for the cell logic

    [NaSem] needs a formula standing for [True] and [HeapSem] one for each
    points-to assertion; two constructors suffice. *)
Inductive cellfml :=
| CFEmpty
| CFPt (lc : loc + cell_id) (cells : list cell_id) (cv : cell_id + val).

Definition cellFML : oFunctor := constOF (leibnizO cellfml).

Section inst.
  Context `{!total_heap.heapGS cellFML Σ, !sinvGS cellFML Σ}.

  Definition cell_sem (Px : cellFML $oi Σ) : iProp Σ :=
    match Px with
    | CFEmpty => True
    | CFPt lc cells cv => lc @↦[total_heap.heap_name][^ cells] cv
    end.

  Global Instance cell_sem_ne : NonExpansive cell_sem.
  Proof. intros ? [|???] [|???] [=]; by simplify_eq. Qed.

  (** The world satisfaction the guards live over: a simple invariant
      holding points-to assertions.  This is where [sinv]'s later-freedom
      enters - [sinv_tok_acc] hands the contents back with no [▷]. *)
  Program Definition cellNaSem : NaSem cellFML Σ := {|
    na_sem := cell_sem;
    na_wsat := sinv_wsat (λ _ Px, cell_sem Px);
    na_emptyx := CFEmpty;
  |}.
  Next Obligation. done. Qed.

  Local Existing Instance cellNaSem.

  Program Definition cellHeapSem : total_heap.HeapSem cellFML Σ := {|
    total_heap.heap_fml lc cells cv := CFPt lc cells cv;
  |}.
  Next Obligation. done. Qed.

End inst.

(** ** The program *)

Definition hloop : expr :=
  (rec: "f" ["l"] :=
     let: "x" := rand #2 in
     if: "x" = #0 then !"l" else "f" ["l"])%E.

Definition hbody : expr := (hloop ["l"])%E.

Local Instance hbody_closed : Closed ["l"] hbody.
Proof. unfold hbody, hloop, Closed. simpl. done. Qed.

Definition hprog : expr := (let: "l" := Alloc #1 in hbody)%E.

Section proof.
  Context `{!lrustTotGpreS cellFML Σ, !sinvGS cellFML Σ}.
  Context (iG : invGS_gen HasLc Σ) (hGS : total_heap.heapGS cellFML Σ)
          (eG : ecGS Σ).

  (** Fixing the interpretations makes [na_wsat] reduce to the simple
      invariant's world satisfaction, so no side equation is needed. *)
  Local Instance cellTot : lrustTotGS cellFML Σ :=
    LRustTotGS cellFML Σ iG _ _ hGS cellNaSem cellHeapSem eG.

  (** Holds by [reflexivity]; stated so that proofs can fold and unfold
      the cell logic's world satisfaction where unification needs help. *)
  Lemma na_wsat_eq : na_wsat = sinv_wsat (λ _ Px, cell_sem Px).
  Proof. reflexivity. Qed.

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

  (** The loop, over the cell logic's own world satisfaction. *)
  Lemma hloop_spec (l : loc) (v : val) (ε : R) :
    0 < ε →
    (True &&{na_wsat}&&>
       total_heap.heap_mapsto_cells_fancy l [] (total_heap.FVal v)) -∗
    ↯ ε -∗ WP[na_wsat] hloop [ #l ] [{ _, True }].
  Proof.
    iIntros (Hε) "#Hg Hε".
    iApply (ec_ind_amp ε 2 _ ltac:(lra) ltac:(lra) with "[] Hε").
    iModIntro. iIntros (ε' Hε') "#Hrec Hε".
    rewrite {2}/hloop. twp_rec. twp_bind (rand _)%E.
    iApply (twpw_rand_exp_nat (lrustTotGS0 := cellTot) na_wsat 2 ε'
              (cap2 ε') ⊤ _ ltac:(lia)
              ltac:(apply cap2_bounded; lra) ltac:(apply cap2_mean; lra)
              with "Hε").
    iIntros (n) "[%Hn Hε]".
    destruct n as [|n']; last (assert (n' = 0)%nat as -> by lia).
    - (* heads: read the cell through the guard, with no credit *)
      twp_let. twp_op. twp_case. rewrite -?na_wsat_eq.
      iApply (twp_read_guarded_cells (W:=na_wsat) _ _ l [] v True%I
                with "Hg [//]").
      by iIntros "_".
    - (* tails: spend the doubled credit on another round *)
      twp_let. twp_op. twp_case. rewrite /cap2 /=.
      destruct (Rle_dec 1 (2 * ε')) as [Hge|Hlt].
      + rewrite Rmin_left; [|lra].
        by iDestruct (ec_contradict with "Hε") as "[]".
      + rewrite Rmin_right; [|lra]. by iApply "Hrec".
  Qed.

  (** The whole program. *)
  Lemma hprog_spec (ε : R) :
    0 < ε →
    na_wsat -∗ ↯ ε -∗
    na_wsat ∗ WP[na_wsat] hprog [{ _, True }].
  Proof.
    iIntros (Hε) "HW Hε". iFrame "HW". rewrite /hprog.
    twp_apply (twp_alloc na_wsat _ ⊤ 1 _ ltac:(lia)).
    iIntros (l sz) "%Hsz Hf Hl".
    assert (sz = 1%nat) as -> by lia. simpl.
    rewrite total_heap.heap_mapsto_vec_singleton.
    twp_let. rewrite /hbody /hloop. simpl_subst. rewrite -/hloop.
    (* publish the cell into the simple invariant, later-free *)
    iApply fupdw_tgl_wpw_nonval; [done|]. iIntros "HW".
    iDestruct (sinv_tok_alloc_suspend (sm:=λ _ Px, cell_sem Px)
                 (CFPt (inl l) [] (inr (LitV LitPoison))) with "HW")
      as (I) "Halloc".
    iMod ("Halloc" $! (fresh I) with "[%]") as "[#tok Hback]";
      [apply is_fresh|].
    iDestruct ("Hback" with "Hl") as "HW". iModIntro.
    iFrame "HW".
    iApply (hloop_spec l (LitV LitPoison) ε ltac:(lra) with "[] Hε").
    rewrite na_wsat_eq.
    iApply (sinv_tok_guard (sm := λ _ Px, cell_sem Px) with "tok").
  Qed.

End proof.

(** Operational conclusion: the program converges with probability [1]. *)
Theorem hprog_terminates `{!lrustTotGpreS cellFML Σ, !sinvGpreS cellFML Σ}
    (ε : R) :
  0 < ε → 1 - ε <= SeriesC (lim_exec (hprog, ∅)).
Proof.
  intros Hε.
  eapply (lrust_tot_mass_lim_exec _ ε 0%nat); [lra|].
  intros iG hGS eG. iIntros "_ Hε".
  iMod (sinv_wsat_alloc (FML:=cellFML)) as (Hsinv) "Hmk".
  iDestruct ("Hmk" $! (λ _ Px, cell_sem Px) with "[]") as "HW".
  { iIntros (i). iApply ne_internal_ne; apply _. }
  iModIntro. iExists (existT cellNaSem cellHeapSem). simpl.
  iExists (sinv_wsat (λ _ Px, cell_sem Px)).
  iApply (hprog_spec _ _ _ ε with "HW Hε"); done.
Qed.
