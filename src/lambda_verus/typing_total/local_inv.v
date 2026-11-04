(** * Local (cancellable non-atomic) invariants

  Ported from VerusBelt ([typing/local_inv.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer).

  The original's invariant body carries [⧖(S d' `max` g')], [⧗(d' - d1)] and
  [£(d' - d1)]: the credits exist to pay for the [▷]s the body is behind and
  to "make up the difference" between the outer depth [d] and the inner [d'].
  None of that exists here, so the body is just the type's ghost assertion at
  some depth, and the [dg_tok] ghost state that tracked [d1] goes with it -
  the [nat] field of the refinement stays, unused.

  Like every other ghost assertion, the type's is a *formula*; the three
  pieces of the cancellable-NA interface it names are asked for as
  [LocalInvFml]. *)

From iris.proofmode Require Import proofmode.
From lrust.typing_total Require Export type.
From lrust.typing_total Require Import type_context programs
  programs_util_own own ghost tracked shr_bor product inv_context lft_contexts.
(** Nola's [util], not ours: ours belongs to the partial
  stack and pulls in [lrust.lifetime], which makes [ra]
  resolve to that tree's. *)
From nola.verus_halt.util Require Import cancellable_na_invariants.
From nola.verus_halt.lifetime Require Import lifetime_full.
From nola.bi Require Import guard modw.
From lrust.lang Require Import total_wsat.
Import GuardNotation ModwNotation TglWpwNotation.
(** Our [util] last, so that its [SemiIso] wins the name over Nola's; see
  [typing_total/type.v]. *)
From lrust.util Require Import basic.
(** [ctx_wp], for the [lrustTotGS] instance: this file states weakest
  preconditions.  See the head of [typing_total/ctx_wp.v]. *)
From lrust.typing_total Require Import ctx_wp.
Unset Default Proof Using.
(** [iris.prelude.options] sets [Default Goal Selector "!"], which rejects a
  bare tactic while more than one goal is focused.  It reaches a ported file
  through our imports and not through Nola's, so Nola's proofs - written
  against the default [1], "act on the first goal" - would otherwise need a
  focus fix every few lemmas.  Restoring [1] is a lint setting, not a
  soundness one. *)
Set Default Goal Selector "1".
Unset Suggest Proof Using.

Implicit Type 𝔄 𝔅: syn_type.

Section local_invariants.
  Context `{!typeG FML Σ}.

  (** The three pieces of the cancellable-NA interface that a local
    invariant's ghost assertion names. *)
  Class LocalInvFml := {
    cna_active_fml : gname → FML $oi Σ;
    cna_active_fml_sem γ : bor_sem (cna_active_fml γ) ⊣⊢ cna_active γ;
    cna_inv_fml : gname → thread_id → namespace → FML $oi Σ → FML $oi Σ;
    cna_inv_fml_sem γ p N Px :
      bor_sem (cna_inv_fml γ p N Px) ⊣⊢ cna_inv γ p N Px;
    cna_otok_fml :
      gname → thread_id → namespace → lft → FML $oi Σ → FML $oi Σ;
    cna_otok_fml_sem γ p N κ Px :
      bor_sem (cna_otok_fml γ p N κ Px) ⊣⊢ cna_otok γ p N κ Px;
  }.
  Context `{!LocalInvFml}.

  #[export] Instance cna_inv_fml_persistent γ p N Px :
    Persistent (bor_sem (cna_inv_fml γ p N Px)).
  Proof. rewrite cna_inv_fml_sem. exact _. Qed.

  (** The contents of a local invariant, as a formula *)
  Definition local_inv_body {𝔄 ℭ} (ty: type 𝔄)
      (pred: abstracted_syn_type 𝔄 → ~~ℭ → Prop) (c: ~~ℭ) (tid: thread_id)
      : FML $oi Σ :=
    exs_fml (λ x' : ~~𝔄, ex_fml (λ d' : nat, ex_fml (λ g' : nat,
      (ty.(ty_ghox) x' d' g' tid ∗
        pure_fml (pred (syn_abstract x') c))%FML))).

  Lemma local_inv_body_sem {𝔄 ℭ} (ty: type 𝔄) pred (c: ~~ℭ) tid :
    bor_sem (local_inv_body ty pred c tid) ⊣⊢
      ∃ (x': ~~𝔄) (d' g': nat),
        ty_gho ty x' d' g' tid ∗ ⌜pred (syn_abstract x') c⌝.
  Proof.
    rewrite /local_inv_body exs_fml_sem. apply bi.exist_proper=> x'.
    rewrite ex_fml_sem. apply bi.exist_proper=> d'.
    rewrite ex_fml_sem. apply bi.exist_proper=> g'.
    by rewrite bor_sep_sem pure_fml_sem.
  Qed.
  Lemma local_inv_body_sem_2 {𝔄 ℭ} (ty: type 𝔄) pred (c: ~~ℭ) tid x' d' g' :
    ty_gho ty x' d' g' tid -∗ ⌜pred (syn_abstract x') c⌝ -∗
      bor_sem (local_inv_body ty pred c tid).
  Proof.
    rewrite local_inv_body_sem. iIntros "? %". iExists x', d', g'. by iFrame.
  Qed.

  Program Definition local_inv_ty {𝔄 ℭ} (ty: type 𝔄)
      (pred: abstracted_syn_type 𝔄 → ~~ℭ → Prop) : type (local_invₛ ℭ) := {|
    ty_size := 0;
    ty_lev := 0;
    ty_lfts := [];
    ty_E := [];
    ty_gho_persx x d g tid := empty_fml;
    ty_ghox x d g tid := match x with (N, (γ, γt, d1), c) =>
      (cna_active_fml γ ∗ ⌜d1 < d⌝ ∗
        cna_inv_fml γ tid N (local_inv_body ty pred c tid))%FML end;
    ty_phys x tid := [];
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    move=> ?? ty pred sem Hsm d g d' g' [[N [[γ γt] d1]] c] tid ??.
    rewrite !(sep_sem_at Hsm) !(pure_sem_at Hsm). iIntros "($ & %Hd & $)".
    iPureIntro; lia.
  Qed.
  Next Obligation. move=> ?? ty pred sem Hsm *. by iIntros "$". Qed.
  (** The [guard_proph] obligation is gone with the field; see [typing_total/type.v]. *)
  Next Obligation.
    move=> ?? ty pred sem Hsm *. rewrite (empty_sem_at Hsm). exact _.
  Qed.
  Next Obligation. move=> *. iIntros "_". by iApply empty_fml_sem_2. Qed.

  Lemma local_inv_ty_gho {𝔄 ℭ} (ty: type 𝔄) pred N γ γt d1 (c: ~~ℭ) d g tid :
    ty_gho (local_inv_ty ty pred) (N, (γ, γt, d1), c) d g tid ⊣⊢
      cna_active γ ∗ ⌜d1 < d⌝ ∗
      cna_inv γ tid N (local_inv_body ty pred c tid).
  Proof.
    rewrite /ty_gho /= !bor_sep_sem pure_fml_sem cna_active_fml_sem
      cna_inv_fml_sem //.
  Qed.
  Lemma local_inv_ty_gho_pers {𝔄 ℭ} (ty: type 𝔄) pred (x: ~~(local_invₛ ℭ))
      d g tid :
    ty_gho_pers (local_inv_ty ty pred) x d g tid ⊣⊢ True.
  Proof. apply empty_fml_sem. Qed.

  Program Definition local_closer_ty {𝔄 ℭ} (κ: lft) (ty: type 𝔄)
      (pred: abstracted_syn_type 𝔄 → ~~ℭ → Prop) : type (local_invₛ ℭ) := {|
    ty_size := 0;
    ty_lev := 0;
    ty_lfts := [];
    ty_E := [];
    ty_gho_persx x d g tid := empty_fml;
    ty_ghox x d g tid := match x with (N, (γ, γt, d1), c) =>
      cna_otok_fml γ tid N κ (local_inv_body ty pred c tid) end;
    ty_phys x tid := [];
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. move=> ??? ty pred sem Hsm *. by iIntros "$". Qed.
  Next Obligation. move=> ??? ty pred sem Hsm *. by iIntros "$". Qed.
  (** The [guard_proph] obligation is gone with the field; see [typing_total/type.v]. *)
  Next Obligation.
    move=> ??? ty pred sem Hsm *. rewrite (empty_sem_at Hsm). exact _.
  Qed.
  Next Obligation. move=> *. iIntros "_". by iApply empty_fml_sem_2. Qed.

  Lemma local_closer_ty_gho {𝔄 ℭ} κ (ty: type 𝔄) pred N γ γt d1 (c: ~~ℭ)
      d g tid :
    ty_gho (local_closer_ty κ ty pred) (N, (γ, γt, d1), c) d g tid ⊣⊢
      cna_otok γ tid N κ (local_inv_body ty pred c tid).
  Proof. apply cna_otok_fml_sem. Qed.

  (** [local_inv_ty_resolve] removed along with [resolve]: it resolves a type's
    prophecies, and there are none. *)

  (** Moving a local invariant to another thread.

    The original's depth bookkeeping - [dg_tok], the [⧗]/[£] that make up the
    difference between the outer and inner depths, and the [|={…}▷=>^d] the
    whole [Send] interface used to carry - is gone with the laters. *)
  (** [local_inv_ty_send] is gone: [typing/] does not have it. *)

  Lemma typed_local_inv_alloc {𝔄 ℭ} (p1 p2 : path) (ty : type 𝔄)
      (pred: abstracted_syn_type 𝔄 → ~~ℭ → Prop)
      (tyCN : type (ℭ * namespaceₛ)) E L I :
    typed_inv_instr E L I
      +[p1 ◁ own_ptr 0 (ghost_ty tyCN); p2 ◁ own_ptr 0 ty]
      (Seq Skip Skip) I
      (const +[p2 ◁ own_ptr 0 (local_inv_ty ty pred)])
      (λ post '-[(_, (c, N)); (_, v)], λ mask,
        pred (syn_abstract v) c ∧ ∀ l γ, post -[(l, (N, γ, c))] mask).
  Proof.
    apply typed_instr_of_skip_own2_own; [done|done|].
    move=> l1 l2 x1 x2 d tid post mask iκs.
    iIntros "#LFT #UNIQ #E L I _ Tra #Obs W".
    iDestruct "Obs" as %Sat. pose proof Sat as HobsK.
    destruct x1 as [c ns].
    destruct Sat as [Hpred _].
    iDestruct (cna_alloc (WG:=verus_halt_WGuard) (sm:=bor_sem) tid ns
      (local_inv_body ty pred c tid) with "[Tra]")
      as "A".
    { by iApply (local_inv_body_sem_2 with "Tra"). }
    iDestruct (bupdw_incl (W:=verus_halt_wsat) with "A") as "A'".
    iMod ("A'" with "W") as "(W & %γ & #inv & active)".
    iModIntro. iFrame "W L I". iExists (ns, (γ, γ, d), c).
    rewrite local_inv_ty_gho. iFrame "active inv". iSplit.
    { iPureIntro. lia. }
    iPureIntro; move: HobsK=> [_ Ha]. apply Ha.
  Qed.

  Lemma typed_local_inv_destroy {𝔄 ℭ} (p : path) (ty : type 𝔄)
      (pred: abstracted_syn_type 𝔄 → ~~ℭ → Prop) E L I :
    lctx_ictx_alive E L I →
    typed_instr E L I +[p ◁ own_ptr 0 (local_inv_ty ty pred)]
      (Seq Skip Skip) (const +[p ◁ own_ptr 0 (tracked_ty ty)])
      (λ post '-[(_, (N, γ, c))], λ mask,
        ∀ l v, pred (syn_abstract v) c → post -[(l, v)] mask).
  Proof.
    move=> Halive. apply typed_instr_of_skip_own_own_t; [done|done|].
    move=> l1 [[ns [[γ γt] d0]] c] d tid iκs post mask.
    iIntros "#LFT #UNIQ #E L I gho #Obs W".
    rewrite local_inv_ty_gho. iDestruct "gho" as "(active & %Hd0 & #inv)".
    destruct I as [Il ϝ 𝛼].
    iDestruct "I" as (na_mask at_mask) "[%Hm [[cna_lft #ϝincl] Irest]]".
    iAssert (∀ κ : lft,
      ⌜κ ∈ invctx_to_multiset Il ⊎ list_to_set_disj iκs⌝ -∗
        llctx_interp L &&{Wguard}&&> @[κ])%I as "#Alive".
    { iIntros (κ) "%Hin". destruct Halive as [Halive1 Halive2].
      rewrite gmultiset_elem_of_disj_union in Hin.
      destruct Hin as [Hin|Hin].
      - rewrite /invctx_to_multiset elem_of_list_to_set_disj in Hin.
        iApply (Halive2 _ Hin with "L E").
      - rewrite elem_of_list_to_set_disj in Hin.
        iDestruct (Halive1 with "L E") as "#Incl".
        iDestruct (fguard_here with "ϝincl") as "#ϝinclh".
        iDestruct (guard_trans with "Incl ϝinclh") as "#Incl2".
        iApply (guard_trans with "Incl2 []").
        iApply fguard_here. iApply (lft_intersect_list_elem_of_incl _ _ Hin). }
    iMod (cna_destroy with "inv cna_lft active Alive L W")
      as "(W & cna_lft & L & P)".
    rewrite local_inv_body_sem.
    iDestruct "P" as (x'' d' g') "[gho %Hpred]".
    iModIntro. iFrame "W". iExists (Nat.max d' g'), x''. iFrame "L".
    iSplitL "cna_lft Irest".
    { iExists na_mask, at_mask. by iFrame "cna_lft ϝincl Irest". }
    rewrite tracked_ty_gho. iSplitL "gho".
    { iDestruct (ty_gho_depth_mono with "gho") as "$"; lia. }
    iDestruct "Obs" as %Ha; iPureIntro. by apply Ha.
  Qed.

  Local Lemma mask_lemma (na_mask at_mask X : coPset) :
    na_mask ∪ at_mask = ⊤ → X ⊆ na_mask ∩ at_mask →
    (na_mask ∖ X) ∪ at_mask = ⊤.
  Proof.
    move=> eq sub. apply leibniz_equiv, set_equiv_subseteq. split=>//.
    rewrite -eq. etrans; [|by apply union_mono_r, difference_mono_l].
    move=> a /elem_of_union[?|?]; [|set_solver].
    case (decide (a ∈ at_mask)); set_solver.
  Qed.

  Lemma typed_local_inv_open {𝔄 ℭ} (p : path) (ty : type 𝔄)
      (pred: abstracted_syn_type 𝔄 → ~~ℭ → Prop) E L Il ϝ 𝛼 κ :
    lctx_lft_alive E L κ →
    lctx_ictx_alive E L (InvCtx Il ϝ 𝛼) →
    typed_inv_instr E L (InvCtx Il ϝ 𝛼)
      +[p ◁ own_ptr 0 (tracked_ty (&shr{κ} (local_inv_ty ty pred)))]
      (Seq Skip Skip)
      (InvCtx (InvCtx_open κ :: Il) ϝ 𝛼)
      (const +[p ◁ own_ptr 0 (tracked_ty ty * local_closer_ty κ ty pred)])
      (λ post '-[(_, (_, (N, γ, c)))], λ mask,
        ↑N ⊆ mask ∧ ∀ l v γ', pred (syn_abstract v) c →
          post -[(l, (v, (N, γ', c)))] (mask ∖ ↑N)).
  Proof.
    move=> Halive HaliveI.
    apply typed_inv_instr_of_skip_own_own_t; [done|done|].
    move=> l1 [l0 [[ns [[γ γt] d0]] c]] d tid iκs post mask.
    iIntros "#LFT #UNIQ #E L I shrgho #Obs W".
    rewrite tracked_ty_gho.
    iDestruct (shr_bor_gho_elim with "shrgho") as (dd gg Hdd Hgg)
      "#(_ & KguardsGho & _)".
    iDestruct (Halive with "L E") as "#LguardsK".
    iDestruct (dguard_rhs_sep_l with "KguardsGho") as "#KguardsActive".
    iDestruct (dguard_rhs_sep_r with "KguardsGho") as "#KguardsRest".
    iDestruct (dguard_rhs_sep_r with "KguardsRest") as "#KguardsInv".
    (* read the invariant token out of the shared reference *)
    iDestruct (dguard_alive_sem' (cna_inv_fml_sem _ _ _ _) with "KguardsInv")
      as "#KguardsInv0".
    iDestruct (guard_trans with "LguardsK KguardsInv0") as "#LguardsInv".
    iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
    iDestruct (guard_acc with "LguardsInv L Wg") as "[#inv back]".
    iDestruct ("back" with "inv") as "[Wg L]".
    iDestruct (wsat_join (W:=verus_halt_wsat) with "Wg Wr") as "W".
    iDestruct "Obs" as %HobsK0. pose proof HobsK0 as HobsK. move: HobsK0=> [Hsub _].
    iDestruct "I" as (na_mask at_mask)
      "[%Hm [[Ilifetimes #ϝIncl] [Iown Iat]]]".
    destruct Hm as [Hm1 Hm2].
    iDestruct (dguard_alive_sem' (cna_active_fml_sem _) with "KguardsActive")
      as "#KguardsActive0".
    iMod (cna_inv_acc_with_lifetime_guard with
      "inv Iown Ilifetimes LguardsK KguardsActive0 L W")
      as "(W & Iown & Ilifetimes & L & P & Closer)"; [set_solver|].
    rewrite local_inv_body_sem.
    iDestruct "P" as (x'' d' g') "[gho %Hpred]".
    iModIntro. iFrame "W".
    iExists (Nat.max d' g'), (x'', (ns, (γ, γt, d0), c)), (mask ∖ ↑ns).
    iFrame "L".
    iSplitL "Iown Ilifetimes Iat".
    { iExists (na_mask ∖ ↑ns), at_mask. iFrame "Iown Iat ϝIncl".
      iSplit.
      { iPureIntro. split; [apply mask_lemma; set_solver|set_solver]. }
      rewrite /invctx_to_multiset /= gmultiset_disj_union_assoc.
      iFrame "Ilifetimes". }
    rewrite prod_ty_gho /= tracked_ty_gho local_closer_ty_gho.
    iSplitL "gho Closer".
    { iSplitL "gho".
      - iDestruct (ty_gho_depth_mono with "gho") as "$"; lia.
      - iExact "Closer". }
    iPureIntro; move: HobsK=> [_ Ha]. by apply Ha.
  Qed.

  Lemma typed_local_inv_close {𝔄 ℭ} (p1 p2 : path) (ty : type 𝔄)
      (pred: abstracted_syn_type 𝔄 → ~~ℭ → Prop) E L Il ϝ 𝛼 κ :
    typed_inv_instr E L (InvCtx (InvCtx_open κ :: Il) ϝ 𝛼)
      +[p1 ◁ own_ptr 0 (tracked_ty ty);
        p2 ◁ own_ptr 0 (tracked_ty (local_closer_ty κ ty pred))]
      (Seq Skip Skip) (InvCtx Il ϝ 𝛼) (const +[])
      (λ post '-[(_, v); (_, (N, γ, c))], λ mask,
        pred (syn_abstract v) c ∧ post -[] (mask ∪ ↑N)).
  Proof.
    apply typed_inv_instr_of_skip_own2_emp.
    move=> l1 l2 v [[ns [[γ γt] d0]] c] d tid iκs post mask.
    iIntros "#LFT #UNIQ #E L I gho1 closer #Obs W".
    iDestruct "Obs" as %HobsAll. pose proof HobsAll as HobsK.
    move: HobsAll=> [Hpred _].
    rewrite !tracked_ty_gho local_closer_ty_gho.
    iDestruct "I" as (na_mask at_mask)
      "[%Hm [[Ilifetimes #ϝIncl] [Iown Iat]]]".
    destruct Hm as [Hm1 Hm2].
    iMod (cna_close with "closer [gho1] Iown Ilifetimes W")
      as "(W & %κs' & [%LtsEq %Hdisj] & Iown & Ilifetimes)".
    { by iApply (local_inv_body_sem_2 with "gho1"). }
    rewrite /invctx_to_multiset /= in LtsEq.
    have LtsEq2 : invctx_to_multiset Il ⊎ list_to_set_disj iκs = κs'
      by rewrite /invctx_to_multiset; multiset_solver.
    iModIntro. iFrame "W L". iExists (mask ∪ ↑ns).
    iSplitL "Iown Ilifetimes Iat".
    { iExists (na_mask ∪ ↑ns), at_mask. iFrame "Iown Iat ϝIncl".
      iSplit; [iPureIntro; split; set_solver|].
      rewrite LtsEq2. iFrame "Ilifetimes". }
    iPureIntro; move: HobsK=> [_ Ha]. apply Ha.
  Qed.
End local_invariants.
