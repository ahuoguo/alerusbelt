(** * Borrowing and dereferencing borrowed pointers

  Ported from VerusBelt ([typing/borrow.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer), itself from RustHornBelt.

  The arbitrary [Timeless G] with [G &&{↑NllftG}&&> llctx_interp L] that the
  original halves with [frac_split_guard_in_half] is an [Ltok γ L q] here,
  allocated out of [llctx_interp L] with [Ltok_alloc] and given back with
  [Ltok_withdraw]; the credits [⧗ ⧗' £] that the original's [Share] and
  [UniqBor] instructions mint go with the time receipts. *)

From iris.proofmode Require Import proofmode.
From lrust.typing_total Require Export uniq_bor shr_bor own uniq_util.
From lrust.typing_total Require Import lft_contexts type_context programs
  programs_util.
From nola.verus_halt.lifetime Require Import lifetime_full.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation.
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

Section borrow.
  Context `{!typeG FML Σ}.


  (** Creating a unique borrow out of an owning pointer.

    The original's [⧖]/[⧗]/[£] and the [▷]s they pay for are gone. *)
  Lemma type_uniqbor_instr {𝔄} E L I p n (ty: type 𝔄) κ :
    lctx_lft_alive E L κ →
    elctx_sat E L (ty_outlives_E ty κ) →
    typed_instr E L I +[p ◁ own_ptr n ty] UniqBor
      (const +[p ◁ &uniq{κ} ty;
               p ◁{κ} blocked_type_ctor _ (own_ptr n ty)])
      (λ post '-[a], λ mask,
        ∀ (m: ~~(uniq_borₛ 𝔄)) (b: ~~(blockedₛ (at_locₛ 𝔄))),
          of_cloc (uniq_bor_loc m) = a.1 →
          uniq_bor_current m = a.2 →
          post -[m; b] mask).
  Proof.
    move=> Alv Out. apply typed_instr_of_skip.
    move=> [l x] v d tid post mask iκs.
    iIntros "#LFT #UNIQ #E L I %Hp own #Obs W".
    iDestruct (Out with "L E") as "#Out".
    iDestruct (elctx_interp_ty_outlives_E with "Out") as "#Inκ".
    iDestruct "own" as "[gho %phys]".
    destruct d as [|d']; [by iDestruct (false_fml_sem_1 with "gho") as "[]"|].
    rewrite own_ptr_gho /=.
    iDestruct "gho" as "(pt & freeable & gho)".
    iDestruct (ty_gho_pers_impl with "gho") as "#Pers".
    have Hmask : (↑Nllft ∪ ↑uniqN : coPset) ⊆ ⊤ by set_solver.
    iMod (alloc_uniq_body ty x d' (S d') κ tid
      (l, repeat [] (length (ty_phys ty x tid))) ⊤ Hmask
      with "LFT UNIQ gho [pt] W")
      (* [alloc_uniq_body] no longer mints the second prophecy or the
         observation tying it to the first; see [typing_total/uniq_util.v]. *)
      as "[W (%ξi & %idx & UniqBody & Back)]".
    { by rewrite -heap_cloc_mapsto_fancy_empty. }
    iModIntro. iFrame "W L I".
    iExists -[((l, repeat [] (length (ty_phys ty x tid))), x, ξi, d', S d', idx);
               ((l, x), ξi, ξi)].
    iSplit; last first.
    (* The blocked element reuses [ξi] rather than a fresh prophecy, as in
       [typing/borrow.v], so there is no equation between the two to carry. *)
    { iDestruct "Obs" as %Hm; iPureIntro. by apply Hm. }
    iSplitL "UniqBody".
    { iExists v, (S (S d')). iSplit; [done|].
      rewrite /ty_own uniq_bor_gho. iSplitL; [|by rewrite /= -phys].
      iSplitR; [done|]. iSplitR; [iPureIntro; lia|].
      iFrame "UniqBody". iSplitR.
      { iApply dguard_cmapstoany_nil. }
      by iRight. }
    iSplit; [|done]. rewrite /tctx_elt_interp /=. iExists v.
    iSplit; [done|]. iIntros "†κ W".
    iDestruct ("Back" with "†κ") as "Back'".
    iDestruct (fupdw_incl_mask (W:=verus_halt_wsat) (E':=⊤) with "Back'")
      as "Back2"; [set_solver|].
    iMod ("Back2" with "W") as "[W Body]".
    iEval (rewrite uniq_body_fml_sem) in "Body".
    iDestruct "Body" as (x'' d'' g'') "(pc & gho2 & pt2)".
    iModIntro. iFrame "W". iExists (l, x''), (Nat.max (S d'') g'').
    destruct (Nat.max (S d'') g'') as [|d1] eqn:Hd1; [lia|].
    (* No prophecy equalizer to re-mint: [tctx_elt_interp]'s blocked case
       carries none, so the controller [pc] is simply dropped. *)
    rewrite /ty_own own_ptr_gho /=. iSplit; [|by rewrite /= -phys].
    rewrite heap_cloc_mapsto_fancy_empty !ty_size_eq.
    iFrame "pt2 freeable".
    iDestruct (ty_gho_depth_mono ty d'' g'' d1 (S d1) x'' tid with "gho2")
      as "$"; lia.
  Qed.

  (** Turning a unique borrow into a shared one.

    The original's [⧖]/[⧗]/[£] are gone, and the three guard indices it
    juggles with [leaf_goal laters to …] with them. *)
  Lemma type_share_instr {𝔄} p κ (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I +[p ◁ &uniq{κ} ty] Share (const +[p ◁ &shr{κ} ty])
      (* Nola's premise [(vπ m π).1 = (vπ m π).2] - that the borrow ends
         where it began - is prophecy-level and goes with the rest. *)
      (λ post '-[m], λ mask,
        post -[(uniq_bor_loc m, uniq_bor_current m)] mask).
  Proof.
    move=> Alv. apply typed_instr_of_skip.
    move=> [[[[[l x0] ξi] d'] g'] idx] v d tid post mask iκs.
    iIntros "#LFT #UNIQ #E L I %Hp [gho %Phys] #Obs W".
    rewrite uniq_bor_gho.
    iDestruct "gho" as "(#Incl & %Hle & UniqBody & #PtBase & #Pers)".
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct "Pers" as "[Dead|#Pers2]".
    { (* [κ] is already dead, so the lifetime context is contradictory *)
      iDestruct "Dead" as (κ') "[#Incl0 #Dead']".
      iDestruct (dincl_sem with "Incl0") as "#Incl'".
      iDestruct (guard_trans with "Alv Incl'") as "#G3".
      iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
      iDestruct (guard_acc with "G3 L Wg") as "[Alive _]".
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'"). }
    iMod (Ltok_alloc with "L W") as "[W (%γ & tok)]".
    iDestruct (dincl_incl with "Incl") as "#Incl'".
    iMod (finalize_uniq_body ty x0 ξi d' g' idx κ tid l E L γ 1 ⊤
      with "LFT UNIQ Incl' E tok UniqBody W")
      as "[W (tok & #ShrGuard)]"; [done|done|].
    iMod (Ltok_withdraw with "tok W") as "[W L]".
    (* Park the borrowed type's persistent part: the shared borrow holds it
       behind a judgment, not as a visible child. *)
    iDestruct (wsat_split (W:=verus_halt_wsat) (W':=Wguard) with "W") as "[Wg Wr]".
    iMod (store_ty_gho_pers ty x0 d' g' tid with "Pers2 Wg") as "[Wg #St]".
    iDestruct (wsat_join (W:=verus_halt_wsat) with "Wg Wr") as "W".
    iModIntro. iFrame "W L I". iExists -[(l, x0)].
    inversion Phys as [Eqv]. iSplit.
    { iSplit; [|done]. iExists v, (S (d' + g')). iSplit; [done|].
      (* Both of the shared borrow's indices are bounded, so the pieces go
         back in at exactly the depth and guard index they came out at. *)
      rewrite /ty_own shr_bor_gho /by_lt /by_le.
      iSplit; [|by rewrite -Eqv].
      iDestruct (dguard_rhs_sep_l with "ShrGuard") as "#ShrGho".
      iDestruct (dguard_rhs_sep_r with "ShrGuard") as "#ShrPt".
      iExists d'. iSplit; [iPureIntro; lia|].
      iExists g'. iSplit; [iPureIntro; lia|]. iSplit.
      { by iApply (dguard_cloc_combine_fancy with "PtBase ShrPt"). }
      by iFrame "ShrGho St". }
    (* Nola combines this with the resolution's observation; there is
       none, and the premise it discharged is gone from the statement. *)
    iDestruct "Obs" as %Himpl; iPureIntro. by apply Himpl.
  Qed.

  Lemma type_share {𝔄 𝔅l ℭl 𝔇} p κ (ty: type 𝔄) (T: tctx 𝔅l) (T' : tctx ℭl)
      trx tr e E L I (C: cctx 𝔇) :
    Closed [] e → tctx_extract_ctx E L +[p ◁ &uniq{κ} ty] T T' trx →
    lctx_lft_alive E L κ →
    typed_body E L I C (p ◁ &shr{κ} ty +:: T') e tr -∗
    typed_body E L I C T (Share;; e) (trx ∘
      (λ post '(m -:: bl), λ mask,
        tr post ((uniq_bor_loc m, uniq_bor_current m) -:: bl) mask))%type.
  Proof.
    iIntros (? Extr ?) "?".
    iApply type_seq; [by eapply type_share_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=> ??. apply Htrx. by case.
  Qed.

  (** The intermediate borrow that [tctx_reborrow_uniq] lends to [κ']: the
    old value observer paired with the new prophecy controller.  The
    original's [⧖(S d' `max` g')] inside it goes with the time receipts. *)
  Definition reborrow_mid_fml {𝔄} (x0: ~~𝔄) (ξi ζi: positive) : FML $oi Σ :=
    exs_fml (λ x' : ~~𝔄, ex_fml (λ d' : nat, ex_fml (λ g' : nat,
      (.VOx[PrVar (𝔄 ↾ prval_to_inh (vπ x0)) ξi] x' (d', g') ∗
       .PCx[PrVar (𝔄 ↾ prval_to_inh (vπ x0)) ζi] x' (vπ x') (d', g'))%FML))).

  Lemma reborrow_mid_fml_sem {𝔄} (x0: ~~𝔄) ξi ζi :
    bor_sem (reborrow_mid_fml x0 ξi ζi) ⊣⊢
      ∃ (x': ~~𝔄) (d' g': nat),
        .VO[PrVar (𝔄 ↾ prval_to_inh (vπ x0)) ξi] x' (d', g') ∗
        .PC[PrVar (𝔄 ↾ prval_to_inh (vπ x0)) ζi] x' (vπ x') (d', g').
  Proof.
    rewrite /reborrow_mid_fml exs_fml_sem. apply bi.exist_proper=> x'.
    rewrite ex_fml_sem. apply bi.exist_proper=> d'.
    rewrite ex_fml_sem. apply bi.exist_proper=> g'.
    by rewrite bor_sep_sem vo_fml_sem pc_fml_sem.
  Qed.

  (** Reborrowing a unique borrow for a shorter lifetime.

    The original's [⧖]/[⧗]/[£] and the laters they pay for are gone, and with
    them the [leaf_goal laters to …] steps; what is left is the skeleton -
    mint a fresh prophecy [ζ], reborrow the contents to [κ'], lend [κ'] the
    pair of [.VO[ξ]] and [.PC[ζ]], and merge the two borrows into one
    [uniq_body] for [ζ]. *)
  (** [tctx_reborrow_uniq] is gone: [typing/] does not have it. *)

  (** [type_deref_uniq_own_instr]'s guard source.  The original's is
    [llctx_interp L ∗ .VO[ξ] … ∗ idx_bor_tok ξidx]; here it has to be a
    formula, so the context is banked as an [Ltok] and the two pieces of
    ghost state are named by [vo_fml] and [idx_bor_tok_fml]. *)
  Definition deref_uniq_own_src (γ: gname) (ξ: proph_var)
    (x: ~~ (`ξ.(pv_ty))) (d g: nat) (idx: Idx) : FML $oi Σ :=
    (gsrc_fml (GFrac γ 1) ∗ .VOx[ξ] x (d, g) ∗ idx_bor_tok_fml idx)%FML.

  Lemma deref_uniq_own_src_sem γ ξ x d g idx :
    bor_sem (deref_uniq_own_src γ ξ x d g idx) ⊣⊢
      frac_tok γ 1 ∗ .VO[ξ] x (d, g) ∗ idx_bor_tok idx.
  Proof.
    rewrite /deref_uniq_own_src !bor_sep_sem (gsrc_fml_sem (GFrac γ 1))
      vo_fml_sem idx_bor_tok_fml_sem //.
  Qed.

  (** Dereferencing a unique borrow of an owning pointer.

    The original's [⧗]/[⧖]/[£] and the laters they strip are gone; so is the
    [llctx_interp_make_guarded] halving, replaced by one [Ltok]. *)
  (** [type_deref_uniq_own_instr] is gone: [typing/] does not have it. *)

  (** [type_deref_uniq_own] is gone: [typing/] does not have it. *)

  (** Dereferencing a shared borrow of an owning pointer.

    The original's guard source is [llctx_interp L] itself; here it has to be
    a formula, so the context is turned into an [Ltok] for the duration of
    the read and withdrawn afterwards.  Its [£] and the guard indices it
    sizes with [leaf_goal laters to …] are gone. *)
  (** [type_deref_shr_own_instr] is gone: [typing/] does not have it. *)

  (** [type_deref_shr_own] is gone: [typing/] does not have it. *)

  (** A fraction of the local context paired with a borrow token, as a
    formula.  The original's guard sources are plain [iProp]s; here every
    guard source that goes into the Points-To Cell Logic must be named. *)
  Definition frac_idx_src (γ: gname) (q: Qp) (idx: Idx) : FML $oi Σ :=
    (gsrc_fml (GFrac γ q) ∗ idx_bor_tok_fml idx)%FML.

  Lemma frac_idx_src_sem γ q idx :
    bor_sem (frac_idx_src γ q idx) ⊣⊢ frac_tok γ q ∗ idx_bor_tok idx.
  Proof.
    rewrite /frac_idx_src bor_sep_sem (gsrc_fml_sem (GFrac γ q))
      idx_bor_tok_fml_sem //.
  Qed.
  Lemma frac_idx_src_sem_1 γ q idx :
    bor_sem (frac_idx_src γ q idx) ⊢ frac_tok γ q ∗ idx_bor_tok idx.
  Proof. by rewrite frac_idx_src_sem. Qed.
  Lemma frac_idx_src_sem_2 γ q idx :
    frac_tok γ q ∗ idx_bor_tok idx ⊢ bor_sem (frac_idx_src γ q idx).
  Proof. by rewrite frac_idx_src_sem. Qed.

  (** What [type_deref_uniq_uniq_instr] leaves in the outer borrow while the
    inner one is in use: the inner borrow's value observer, the outer one's
    prophecy controller, and the inner type's persistent part. *)
  Definition deref_uniq_uniq_mid_fml {𝔄} (ty: type 𝔄) (x0: ~~ (uniq_borₛ 𝔄))
      (ξi ωi: positive) (ωidx: Idx) (κ': lft) (tid: thread_id) (l1: cloc)
      : FML $oi Σ :=
    exs_fml (λ x' : ~~𝔄, ex_fml (λ d' : nat, ex_fml (λ g' : nat,
      (.VOx[PrVar (𝔄 ↾ prval_to_inh (vπ (uniq_bor_current x0))) ωi]
         x' (d', g') ∗
       .PCx[PrVar (uniq_borₛ 𝔄 ↾ prval_to_inh (vπ x0)) ξi]
         (l1, x', ωi, d', g', ωidx)
         (@vπ (uniq_borₛ 𝔄) (l1, x', ωi, d', g', ωidx)) (S d', g') ∗
       guard_fml (alive_fml κ') (cmapstoany_fml l1) ∗
       (basically_dead_fml κ' ∨ ty.(ty_gho_persx) x' d' g' tid))%FML))).

  Lemma deref_uniq_uniq_mid_fml_sem {𝔄} (ty: type 𝔄) x0 ξi ωi ωidx κ' tid l1 :
    bor_sem (deref_uniq_uniq_mid_fml ty x0 ξi ωi ωidx κ' tid l1) ⊣⊢
      ∃ (x': ~~𝔄) (d' g': nat),
        .VO[PrVar (𝔄 ↾ prval_to_inh (vπ (uniq_bor_current x0))) ωi]
          x' (d', g') ∗
        .PC[PrVar (uniq_borₛ 𝔄 ↾ prval_to_inh (vπ x0)) ξi]
          (l1, x', ωi, d', g', ωidx)
          (@vπ (uniq_borₛ 𝔄) (l1, x', ωi, d', g', ωidx)) (S d', g') ∗
        dguard (alive_fml κ') (cmapstoany_fml l1) ∗
        (basically_dead κ' ∨ ty_gho_pers ty x' d' g' tid).
  Proof.
    rewrite /deref_uniq_uniq_mid_fml exs_fml_sem. apply bi.exist_proper=> x'.
    rewrite ex_fml_sem. apply bi.exist_proper=> d'.
    rewrite ex_fml_sem. apply bi.exist_proper=> g'.
    rewrite !bor_sep_sem vo_fml_sem pc_fml_sem or_fml_sem
      basically_dead_fml_sem //.
  Qed.

  (** Dereferencing a unique borrow of a unique borrow.

    The original's two halves of [llctx_interp L] are the two halves of one
    [Ltok]; its [⧗]/[⧖]/[£] and all the laters they strip are gone. *)
  (** [type_deref_uniq_uniq_instr] is gone: [typing/] does not have it. *)

  (** [type_deref_uniq_uniq] is gone: [typing/] does not have it. *)

  (** Dereferencing a shared borrow of a unique borrow.

    The original buys [d*(g+1)] later credits out of [⧖] to strip the [▷]s
    in front of the borrow's ghost assertion; there are none here.  What is
    left is one [guard_acc] against the local context, needed because the
    guard to [l1 #↦∗_] sits inside that ghost assertion. *)
  (** [type_deref_shr_uniq_instr] is gone: [typing/] does not have it. *)

  (** [type_deref_shr_uniq] is gone: [typing/] does not have it. *)
End borrow.
