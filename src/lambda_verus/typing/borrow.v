(** Borrowing rules.

    Prophecy-free port of [borrow.v].  Only the parts
    that do not need prophecy resolution are here:

    - [type_uniqbor_instr] creates a [&uniq{κ}] borrow out of an
      [own_ptr].  Upstream additionally minted a second prophecy variable
      [ζ] for the blocked entry and tied it to [ξ] with an equalizer; our
      blocked entry carries no equalizer (see [type_context.v]), so the
      value handed back when [κ] dies is unconstrained.
    - [type_share_instr] / [type_share] turn a [&uniq{κ}] into a
      [&shr{κ}].  Upstream's precondition [(vπ m π).1 = (vπ m π).2] came
      from resolving the borrow; with no final value there is nothing to
      say, and the proof uses [finalize_uniq_body] (the prophecy-free half
      of upstream's [resolve_uniq_body]).

    Reborrowing and the [type_deref_*] family are not ported: they rely on
    [uniq_preresolve] / [uniq_resolve]. *)
From lrust.typing Require Export uniq_bor shr_bor own uniq_util.
From lrust.typing Require Import lft_contexts type_context programs programs_util.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Section borrow.
  Context `{!typeG Σ, !cnaInv_logicG Σ}.

  Lemma type_uniqbor_instr {𝔄} E L I p n (ty: type 𝔄) κ :
    lctx_lft_alive E L κ →
    elctx_sat E L (ty_outlives_E ty κ) →
    typed_instr E L I
        +[p ◁ own_ptr n ty]
        UniqBor
        (const +[p ◁ &uniq{κ} ty; p ◁{κ} blocked_type_ctor _ (own_ptr n ty)])
      (λ post '-[a], λ mask, ∀ (m: ~~(uniq_borₛ 𝔄)) (b: ~~(blockedₛ (at_locₛ 𝔄))),
        of_cloc (uniq_bor_loc m) = a.1 →
        uniq_bor_current m = a.2 →
        post -[m; b] mask).
  Proof.
    intros Alv Out.
    apply typed_instr_of_skip.
    iIntros (x v d tid post mask iκs) "#LFT #TIME #UNIQ E L $ #P own %Obs #⧖ ⧗ ⧗' £".
    destruct x as [l x].
    iDestruct (Out with "L E") as "#Out".
    iDestruct (elctx_interp_ty_outlives_E with "Out") as "#?".
    iDestruct "own" as "[gho %phys]".
    destruct d as [|d']. { done. }
    iDestruct "gho" as "(pt & freeable & gho)".
    iDestruct (ty_gho_pers_impl _ ty with "gho") as "#Pers".
    iMod (alloc_uniq_body _ _ d' (S d') κ _ (l, repeat [] (length (ty_phys ty x tid)))
            with "LFT UNIQ [⧖] gho [pt] ⧗") as (ξi idx) "[UniqBody Back]".
      { set_solver. }
      { iApply (persistent_time_receipt_mono with "⧖"). lia. }
      { rewrite <- heap_cloc_mapsto_fancy_empty. iFrame "pt". }
    iModIntro.
    iExists -[
      ((l, repeat [] (length (ty_phys ty x tid))), x, ξi, d', S d', idx);
      ((l, x), ξi, ξi)
    ].
    iFrame "L".
    unfold tctx_interp, tctx_elt_interp.
    iSplit. {
      iSplitL "UniqBody". {
        iExists v, (S (S d')). iFrame "#". iFrame.
        iSplit; last by done. iSplit; first by iPureIntro; lia.
        rewrite <- heap_cloc_mapsto_empty. iApply guards_true.
      }
      unfold blocked_type_elim. iSplit; [|done].
      iExists v. iFrame "#". iIntros "†κ".
      iDestruct ("Back" with "†κ") as "Back". iMod (fupd_mask_mono with "Back") as "Back".
        { set_solver. }
      iMod (bi.later_exist_except_0 with "Back") as (x'') "Back".
      iMod (bi.later_exist_except_0 with "Back") as (d'') "Back".
      iMod (bi.later_exist_except_0 with "Back") as (g'') "Back".
      iDestruct "Back" as "(>⧖'' & _ & gho & >pt)".
      iModIntro. iExists (l, x''), (S d'' `max` g'').
      destruct (S d'' `max` g'') as [|d1] eqn:Hd1; first by lia.
      iFrame.
      rewrite heap_cloc_mapsto_fancy_empty. repeat rewrite ty_size_eq. iFrame.
      iSplitL. { iDestruct (ty_gho_depth_mono with "gho") as "[gho _]";
                   last by iFrame "gho". { lia. } { lia. } }
      done.
    }
    iPureIntro. by apply Obs.
  Qed.

  Lemma type_share_instr {𝔄} p κ (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I +[p ◁ &uniq{κ}ty] Share (const +[p ◁ &shr{κ} ty])
      (λ post '-[m], λ mask, post -[(uniq_bor_loc m, uniq_bor_current m)] mask).
  Proof.
    intros Alv.
    apply typed_instr_of_skip.
    intros x v d tid post mask iκs.
    iIntros "#LFT #TIME #UNIQ #E L $ #P Own %Obs ⧖ ⧗ ⧗' £".
    iDestruct (Alv with "L E") as "#Alv".
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]".
      { solve_ndisj. }
    destruct x as [[[[[l x0] ξi] d'] g'] idx].
    iDestruct "Own" as "[[#Incl [%Ineqs [UniqBody [#PtBase #Pers]]]] #Phys]".

    iDestruct "Pers" as "[Dead|Pers]". {
      iDestruct "Dead" as (κ') "[Incl' Dead']".
      iDestruct (guards_transitive with "Ghalf Alv") as "G2".
      iDestruct (guards_transitive with "G2 Incl'") as "G3".
      leaf_open "G3" with "H1" as "[Alive _]". { set_solver. }
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'").
    }

    iMod (finalize_uniq_body ty x0 ξi d' g' idx κ tid l with
            "LFT UNIQ TIME Incl E Ghalf H1 UniqBody") as "(H1 & #ShrGuard)".
      { trivial. } { set_solver. }
    iDestruct ("Halfback" with "H1 H2") as "Halfback'".
    iMod (fupd_mask_mono with "Halfback'") as "L". { set_solver. }
    iModIntro. iExists -[(l, x0)]. iFrame.
    iSplit. {
      iExists v. iSplit. { done. } iSplit; last by done.
      iSplit. {
        iApply guard_cloc_combine_fancy.
         - leaf_goal laters to (d + 1); first by lia. iFrame "PtBase".
         - leaf_goal laters to 1. { lia. } iApply (guards_weaken_rhs_sep_r with "ShrGuard").
      }
      iSplit. { leaf_goal laters to 1. { lia. }
        iApply (guards_transitive_left with "ShrGuard []").
        leaf_by_sep. iIntros "[G pt]".
        iDestruct (ty_gho_depth_mono _ _ _ d (S d) with "G") as "[G back]". { lia. } { lia. }
        iFrame "G". iIntros "G". iFrame. iApply "back". iFrame.
      }
      iNext. iApply (ty_gho_pers_depth_mono _ _ _ d (S d)); last by iFrame "Pers".
      { lia. } { lia. }
    }
    iPureIntro. by apply Obs.
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
    destruct Extr as [Htrx _]=>??. apply Htrx. by case.
  Qed.
End borrow.
