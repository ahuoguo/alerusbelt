(** * Permission cells

  Ported from VerusBelt ([typing/pcell.v], MIT, Hance, Elbeheiry, Matsushita,
  Dreyer).

  The [▷]s in front of the inner type's ghost assertion and the credits and
  time receipts that strip them are gone; the depth arithmetic that sized
  them (the [leaf_goal laters to …] steps) goes with them.  The ghost
  assertions are formulas, so the one piece of ghost state they name -
  ownership of a vector of cells - is asked for as [PcellFml]. *)

From iris.proofmode Require Import proofmode.
From lrust.lang.lib Require Import total_memcpy.
From lrust.lang Require Import total_heap.
From lrust.typing_total Require Export type own product sum shr_bor uniq_bor
  uniq_util int bool.
From lrust.typing_total Require Import uninit type_context programs
  programs_util tracked freeable_util lft_contexts ctx.
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

Section pcell.
  Context `{!typeG FML Σ}.

  (** Ownership of a vector of cells, as a formula *)
  Class PcellFml := {
    cellsvec_fml : list cell_id → list fancy_val → FML $oi Σ;
    cellsvec_fml_sem cs fv :
      bor_sem (cellsvec_fml cs fv) ⊣⊢ cs ^↦!∗ fv;
    (** The constructor means the same at every candidate interpretation;
      see [AltSem] in [typing/ctx.v]. *)
    cellsvec_sem_at {sem} : alt_sem sem → ∀ cs fv,
      sem (cellsvec_fml cs fv) ⊣⊢ cs ^↦!∗ fv;
  }.
  Context `{!PcellFml}.

  (** [guard_cloc_combine_fancy'] for stored guards *)
  Lemma dguard_cloc_combine_fancy' {Px} (l : cloc) (γs : list cell_id)
      (fv : list fancy_val) :
    dguard Px (cells_fml l.1 l.2 (FCell <$> γs)) -∗
    dguard Px (cellsvec_fml γs fv) -∗
    dguard Px (cells_fml (cloc_flat_insert l γs).1
                 (cloc_flat_insert l γs).2 fv).
  Proof.
    have ? := guard_fml_pers_at alt_here.
    iIntros "#g1 #g2". iApply dguard_of_all. iIntros (sem' Hs Hi).
    iDestruct (guard_fml_sem_into alt_here Hs Hi with "g1") as "#G1".
    iDestruct (guard_fml_sem_into alt_here Hs Hi with "g2") as "#G2".
    iDestruct (guard_rhs_iff (cells_sem_at Hs _ _ _) with "G1") as "#G1'".
    iDestruct (guard_rhs_iff (cellsvec_sem_at Hs _ _) with "G2") as "#G2'".
    have Heq : (cloc_flat_insert l γs).1 ↦[^ (cloc_flat_insert l γs).2 ]!∗ fv
      ⊣⊢ sem' (cells_fml (cloc_flat_insert l γs).1
                 (cloc_flat_insert l γs).2 fv).
    { by rewrite (cells_sem_at Hs). }
    iApply (guard_rhs_iff Heq).
    iApply (guard_cloc_combine_fancy' with "G1' G2'").
  Qed.

  Program Definition pcell_ty n : type (pcellₛ n) :=
    {| ty_size := n; ty_lev := 0;
       ty_lfts := [];
       ty_E := [];
       ty_ghox x _ _ _ := pure_fml (length x = n);
       ty_gho_persx x _ _ _ := pure_fml (length x = n);
       ty_phys (cell_ids: ~~ (pcellₛ n)) _ := pad (FCell <$> cell_ids) n;
    |}.
  Next Obligation. move=> n v tid. by rewrite length_pad. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. move=> ? sem Hsm *. by iIntros "$". Qed.
  Next Obligation. move=> ? sem Hsm *. by iIntros "$". Qed.
  (** The [guard_proph] obligation is gone with the field; see [typing_total/type.v]. *)
  Next Obligation. move=> ? sem Hsm *. rewrite (pure_sem_at Hsm). exact _. Qed.
  Next Obligation. move=> *. by iIntros "$". Qed.

  Lemma pcell_ty_gho n x d g tid :
    ty_gho (pcell_ty n) x d g tid ⊣⊢ ⌜length x = n⌝.
  Proof. apply pure_fml_sem. Qed.
  Lemma pcell_ty_gho_pers n x d g tid :
    ty_gho_pers (pcell_ty n) x d g tid ⊣⊢ ⌜length x = n⌝.
  Proof. apply pure_fml_sem. Qed.

  Global Instance pcell_send n: Send (pcell_ty n).
  Proof.
    split.
    - move=> tid tid' x x' /= ->. done.
    - move=> tid tid' x d g G κs. iIntros "_ _ lfts _ G gho $ !>".
      iExists x, 0%nat. rewrite Nat.add_0_r. by iFrame "lfts G gho".
  Qed.

  Global Instance pcell_sync n: Sync (pcell_ty n).
  Proof. move=> *. split; [done|]. split; reflexivity. Qed.
End pcell.

Global Hint Rewrite @pcell_ty_gho @pcell_ty_gho_pers : fml_sem.

Section points_to.
  Context `{!typeG FML Σ, !PcellFml}.

  Program Definition cell_points_to_ty {𝔄} (ty: type 𝔄)
      : type (trackedₛ (pcellₛ (ty.(ty_size)) * 𝔄)) :=
    {| ty_size := 0%nat; ty_lev := 0;
       ty_lfts := ty.(ty_lfts);
       ty_E := ty.(ty_E);
       ty_ghox x d g tid := [Sx(d') := d]
         (cellsvec_fml x.1 (ty.(ty_phys) x.2 tid) ∗
          ty.(ty_ghox) x.2 d' g tid)%FML;
       ty_gho_persx x d g tid := [Sx(d') := d]
         (pure_fml (length x.1 = ty_size ty) ∗
          ty.(ty_gho_persx) x.2 d' g tid)%FML;
       ty_phys _ _ := [];
    |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    move=> ? ty sem Hsm d g d' g' x tid ??.
    destruct d as [|d0]; [rewrite /= (false_sem_at Hsm); by iIntros "[]"|].
    destruct d' as [|d0']; [lia|]. rewrite /= !(sep_sem_at Hsm).
    iIntros "[$ gho]".
    iApply (ty_gho_depth_mono_at ty sem Hsm with "gho"); lia.
  Qed.
  Next Obligation.
    move=> ? ty sem Hsm d g d' g' x tid ??.
    destruct d as [|d0]; [rewrite /= (false_sem_at Hsm); by iIntros "[]"|].
    destruct d' as [|d0']; [lia|]. rewrite /= !(sep_sem_at Hsm).
    iIntros "[$ gho]".
    iApply (ty_gho_pers_depth_mono_at ty sem Hsm with "gho"); lia.
  Qed.
  (** The [guard_proph] obligation is gone with the field; see [typing_total/type.v]. *)
  Next Obligation.
    move=> ? ty sem Hsm x d g tid.
    apply (by_succx_persistent_at Hsm)=> d'.
    have ? := pure_pers_at Hsm. have ? := sep_pers_at Hsm.
    have ? := ty_gho_pers_pers_at ty sem Hsm. exact _.
  Qed.
  Next Obligation.
    move=> ? ty x d g tid. rewrite !by_succx_sem.
    destruct d as [|d']; [by iIntros "[]"|]. rewrite /= !bor_sep_sem.
    iIntros "[A1 A2]".
    iDestruct (cellsvec_fml_sem with "A1") as "A1".
    iDestruct (cells_points_to_fancy_vec_length_eq with "A1") as %Hlen.
    rewrite (ty_size_eq ty) in Hlen.
    iSplitR; [by iApply pure_fml_sem_2|].
    by iApply ty_gho_pers_impl.
  Qed.

  Lemma cell_points_to_gho {𝔄} (ty: type 𝔄) x d g tid :
    ty_gho (cell_points_to_ty ty) x d g tid ⊣⊢ [S(d') := d]
      (x.1 ^↦!∗ ty_phys ty x.2 tid ∗ ty_gho ty x.2 d' g tid).
  Proof.
    rewrite /ty_gho by_succx_sem. destruct d as [|d']; [done|].
    by rewrite /= bor_sep_sem cellsvec_fml_sem.
  Qed.
  Lemma cell_points_to_gho_pers {𝔄} (ty: type 𝔄) x d g tid :
    ty_gho_pers (cell_points_to_ty ty) x d g tid ⊣⊢ [S(d') := d]
      (⌜length x.1 = ty_size ty⌝ ∗ ty_gho_pers ty x.2 d' g tid).
  Proof.
    rewrite /ty_gho_pers by_succx_sem. destruct d as [|d']; [done|].
    by rewrite /= bor_sep_sem pure_fml_sem.
  Qed.

  Global Instance cell_points_to_send {𝔄} (ty: type 𝔄) :
    Send ty → Send (cell_points_to_ty ty).
  Proof.
    move=> [Hphys Hgho]. split; [done|].
    move=> tid tid' x d g G κs. iIntros "LFT UNIQ lfts #gs G gho W".
    rewrite cell_points_to_gho.
    destruct d as [|d]; [by iDestruct "gho" as "[]"|].
    iDestruct "gho" as "[Hown gho]".
    iMod (Hgho with "LFT UNIQ lfts gs G gho W")
      as "(W & %x' & %off & gho & %Habs & lfts & G)".
    iModIntro. iFrame "W". iExists (x.1, x'), off. iFrame "lfts G".
    rewrite cell_points_to_gho /=.
    rewrite -(Hphys tid tid' x.2 x' (eq_sym Habs)). iFrame "Hown gho".
    iPureIntro. simpl. by rewrite Habs.
  Qed.

  Global Instance cell_points_to_sync {𝔄} (ty: type 𝔄) :
    Sync ty → Sync (cell_points_to_ty ty).
  Proof.
    move=> HSync tid tid' x d g. split; [done|].
    destruct d as [|d']; [done|].
    have [Hp [Hg Hgp]] := HSync tid tid' x.2 d' g.
    split=>/=; [rewrite Hp Hg|rewrite Hgp]; done.
  Qed.
End points_to.

Section typing.
  Context `{!typeG FML Σ, !PcellFml}.

  Definition PCellFromOwn : val := (λ: ["p"], "p")%V.

  Lemma typed_pcell_from_own {𝔄} (p : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[p ◁ own_ptr (ty_size ty) ty] (PCellFromOwn [p])
      (λ v, +[v ◁ own_ptr (ty_size ty)
                 (prod_ty (pcell_ty (ty_size ty)) (cell_points_to_ty ty))])
      (λ post '-[(l, x)], λ mask, ∀ cell_ids : list positive,
        post -[(l, (cell_ids, (cell_ids, x)))] mask).
  Proof.
    move=> tid post mask iκs vπl.
    iIntros "#LFT #UNIQ #E L I TY #Obs"=>/=.
    destruct vπl as [[l x][]]. iDestruct "TY" as "(TY & _)".
    iDestruct "TY" as (pl d Heval) "[Hown %Hphys]".
    simpl in Hphys. inversion Hphys; subst pl.
    destruct d as [|d];
      [by iDestruct (false_fml_sem_1 with "Hown") as "[]"|].
    rewrite own_ptr_gho /=. iDestruct "Hown" as "(Hl & Hfree & Hgho)".
    iApply tgl_wpw_fupdw_nonval; [done|].
    twp_bind p. iApply tgl_wp_wand; [by iApply twp_eval_path|]. iIntros (?->).
    twp_rec. iIntros "W".
    iMod (cell_alloc2 with "Hl") as (γs Hlen) "H↦".
    iDestruct (bi.equiv_entails_1_1 _ _
      (heap_mapsto_cells_to_complete_mapsto_fancy_vec
         (l, (λ γ : cell_id, [γ]) <$> γs) (ty_phys ty x tid)) with "H↦")
      as "[Hchain Htail]".
    iDestruct (bi.equiv_entails_1_1 _ _ (heap_complete_mapsto_vec_eq l γs)
      with "Hchain") as "Hchain".
    iDestruct (bi.equiv_entails_1_1 _ _
      (heap_complete_mapsto_fancy_val_vec_eq' l γs (ty_phys ty x tid))
      with "Htail") as "Htail".
    rewrite ty_size_eq in Hlen.
    iModIntro. iFrame "W L I". iExists -[(l, (γs, (γs, x)))].
    iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> ? Ha. apply Ha. }
    iSplit; [|done]. iExists #l, (S (S d)). iSplit; [done|].
    rewrite /ty_own own_ptr_gho /= prod_ty_gho /= pcell_ty_gho
      cell_points_to_gho /= Nat.add_0_r app_nil_r.
    rewrite (pad_length' (FCell <$> γs) (ty_size ty));
      [|by rewrite length_fmap Hlen].
    iDestruct (ty_gho_depth_mono ty d (S d) d (S (S d)) x tid with "Hgho")
      as "Hgho"; [lia|lia|].
    iFrame "Hchain Hfree Htail Hgho". by iSplit.
  Qed.

  Definition PCell2Own : val := (λ: ["pcell"; "perm"], "pcell")%V.

  Lemma typed_pcell_to_own {𝔄} (perm pcell : path) (ty : type 𝔄) E L I :
    typed_instr E L I
      +[pcell ◁ own_ptr (ty_size ty) (pcell_ty (ty_size ty));
        perm ◁ own_ptr 0 (cell_points_to_ty ty)]
      (PCell2Own [pcell; perm]) (λ v, +[v ◁ own_ptr (ty_size ty) ty])
      (λ post '-[(l, γs); (_, (γs', x))], λ mask,
        γs = γs' ∧ post -[(l, x)] mask).
  Proof.
    move=> tid post mask iκs vπl.
    iIntros "#LFT #UNIQ #E L I TY #Obs"=>/=.
    destruct vπl as [[l γs] [[l' [γs' x]] []]].
    iDestruct "TY" as "(Hpcell & Hperm & _)".
    iDestruct "Hpcell" as (pl d Heval) "[Hown %Hphys]".
    iDestruct "Hperm" as (pl' d' Heval') "[Hown' %Hphys']".
    simpl in Hphys, Hphys'. inversion Hphys; subst pl.
    inversion Hphys'; subst pl'.
    destruct d as [|d];
      [by iDestruct (false_fml_sem_1 with "Hown") as "[]"|].
    destruct d' as [|d'];
      [by iDestruct (false_fml_sem_1 with "Hown'") as "[]"|].
    rewrite own_ptr_gho /= pcell_ty_gho.
    iDestruct "Hown" as "(H↦ & Hfree & %Hlen)".
    rewrite own_ptr_gho /=. iDestruct "Hown'" as "(_ & _ & Hown')".
    rewrite cell_points_to_gho.
    destruct d' as [|d''];
      [by iDestruct "Hown'" as "[]"|].
    iDestruct "Hown'" as "[H↦' Hgho]".
    iApply tgl_wpw_fupdw_nonval; [done|].
    twp_bind pcell. iApply tgl_wp_wand; [by iApply twp_eval_path|].
    iIntros (?->). twp_bind perm.
    iApply tgl_wp_wand; [by iApply twp_eval_path|]. iIntros (?->).
    twp_rec. iIntros "W".
    iMod (proph_obs_sat with "Obs") as %[π0 [<- _]]; [solve_ndisj|].
    rewrite (pad_length' (FCell <$> γs) (ty_size ty));
      [|by rewrite length_fmap Hlen].
    iDestruct (bi.equiv_entails_1_2 _ _
      (heap_complete_mapsto_fancy_val_vec_eq' l γs (ty_phys ty x tid))
      with "H↦'") as "H↦'".
    iMod (heap_delete_cell with "H↦ H↦'") as "H↦".
    iModIntro. iFrame "W L I". iExists -[(l, x)].
    iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> ? [_ Ha]. apply Ha. }
    iSplit; [|done]. iExists #l, (S (S d'')). iSplit; [done|].
    rewrite /ty_own own_ptr_gho /=.
    iDestruct (ty_gho_depth_mono ty d'' (S (S d'')) (S d'') (S (S d'')) x tid
      with "Hgho") as "Hgho"; [lia|lia|].
    by iFrame "H↦ Hfree Hgho".
  Qed.

  Lemma pcell_ty_gho_phys n (γs : ~~(pcellₛ n)) tid :
    length γs = n →
    ∀ (l : cloc), (l.1 ↦[^ l.2 ]!∗ ty_phys (pcell_ty n) γs tid) ⊣⊢
      (l.1 ↦[^ l.2 ]!∗ (FCell <$> γs)).
  Proof.
    move=> Hlen l. rewrite /= (pad_length' (FCell <$> γs) n) //.
    by rewrite length_fmap Hlen.
  Qed.

  Definition PCellBorrow : val := (λ: ["pcell_ref"; "perm_ref"], "pcell_ref")%V.

  (** The original splits into two symmetric branches on which of the two
    depths is larger, because it has to pick the receipt that pays for the
    [▷]s in front of the shared ghost assertions.  There are none here, so
    one branch does. *)
  Lemma typed_pcell_borrow {𝔄} κ (pcell_ref perm_ref : path) (ty : type 𝔄)
      E L I :
    typed_instr E L I
      +[pcell_ref ◁ shr_bor κ (pcell_ty (ty_size ty));
        perm_ref ◁ shr_bor κ (cell_points_to_ty ty)]
      (PCellBorrow [pcell_ref; perm_ref]) (λ v, +[v ◁ shr_bor κ ty])
      (λ post '-[(l, γs); (_, (γs', x))], λ mask,
        γs = γs' ∧ post -[(cloc_flat_insert l γs, x)] mask).
  Proof.
    move=> tid post mask iκs vπl.
    iIntros "#LFT #UNIQ #E L I TY #Obs"=>/=.
    destruct vπl as [[l γs] [[l' [γs' x]] []]].
    iDestruct "TY" as "(Hcell & Hperm & _)".
    iDestruct "Hcell" as (pl d Heval) "[Hshr %Hphys]".
    iDestruct "Hperm" as (pl' d' Heval') "[Hshr' %Hphys']".
    simpl in Hphys, Hphys'. inversion Hphys; subst pl.
    inversion Hphys'; subst pl'.
    iDestruct (shr_bor_gho_elim with "Hshr") as (dd0 gg0 Hdd0 Hgg0)
      "#(Hpt & _ & Hst0)".
    iDestruct (shr_bor_gho_elim with "Hshr'") as (dd1 gg1 Hdd1 Hgg1)
      "#(_ & Hghoshr & Hst1)".
    iApply tgl_wpw_fupdw_nonval; [done|].
    twp_bind pcell_ref. iApply tgl_wp_wand; [by iApply twp_eval_path|].
    iIntros (?->). twp_bind perm_ref.
    iApply tgl_wp_wand; [by iApply twp_eval_path|]. iIntros (?->).
    twp_rec. iIntros "W".
    iMod (proph_obs_sat with "Obs") as %[π0 [<- _]]; [solve_ndisj|].
    (* Both shared borrows keep their persistent part behind a judgment, so
       they are opened here, where the world satisfaction is at hand. *)
    iDestruct (wsat_split (W:=verus_halt_wsat) (W':=Wguard) with "W") as "[Wg Wr]".
    iDestruct (store_fml_acc with "Hst0") as "#Acc0".
    iDestruct ("Acc0" with "Wg") as "[Wg #Hlen0]".
    rewrite pure_fml_sem. iDestruct "Hlen0" as %Hlen.
    iDestruct (store_fml_acc with "Hst1") as "#Acc1".
    iDestruct ("Acc1" with "Wg") as "[Wg #Hpers0]".
    rewrite by_succx_sem.
    destruct dd1 as [|d2]; [by iDestruct "Hpers0" as "[]"|]. simpl.
    rewrite bor_sep_sem pure_fml_sem. iDestruct "Hpers0" as "[_ Hpers]".
    iMod (store_ty_gho_pers ty x d2 gg1 tid with "Hpers Wg") as "[Wg #St]".
    iDestruct (wsat_join (W:=verus_halt_wsat) with "Wg Wr") as "W".
    iDestruct (dguard_rhs_sep_l with "Hghoshr") as "#Hcells".
    iDestruct (dguard_rhs_sep_r with "Hghoshr") as "#Hgho".
    iModIntro. iFrame "W L I". iExists -[(cloc_flat_insert l γs, x)].
    iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> ? [_ Ha]. apply Ha. }
    iSplit; [|done]. iExists #l.1, (S (d2 + gg1)). iSplit; [done|].
    rewrite /ty_own. iSplit; [|done].
    iApply (shr_bor_gho_intro_st κ ty (cloc_flat_insert l γs, x) _ _ d2 gg1);
      [lia|lia| | |].
    { have Hph : ∀ sem', alt_sem sem' →
        sem' (cells_fml l.1 l.2 (ty_phys (pcell_ty (ty_size ty)) γs tid)) ⊣⊢
        sem' (cells_fml l.1 l.2 (FCell <$> γs)).
      { move=> sem' Hs. rewrite !(cells_sem_at Hs).
        apply (pcell_ty_gho_phys (ty_size ty) γs tid Hlen l). }
      iDestruct (dguard_rhs_iff Hph with "Hpt") as "#Hpt2".
      iApply (dguard_cloc_combine_fancy' with "Hpt2 Hcells"). }
    { iApply "Hgho". }
    { iApply "St". }
  Qed.

  (** The physical footprint of a permission cell, re-read as the flat
    locations the cells stand for *)
  Lemma pcell_phys_to_flat n (γs : ~~(pcellₛ n)) (cl : cloc) tid :
    length γs = n → length cl.2 = n →
    (cl.1 ↦[^ cl.2 ]!∗ ty_phys (pcell_ty n) γs tid) ⊣⊢
      cloc_flat_insert cl γs #↦∗_.
  Proof.
    move=> Hlen Hlen2. rewrite (pcell_ty_gho_phys n γs tid Hlen cl).
    rewrite heap_mapsto_cells_to_complete_mapsto_fancy_vec.
    rewrite (heap_complete_mapsto_combine γs cl); [done|].
    by rewrite Hlen2 Hlen.
  Qed.

  (** [PCellMutBorrow] is gone: [typing/] does not have it. *)

  (** As in [typed_pcell_borrow], the original's symmetric case split on which
    of the two depths is the larger only picked the time receipt that paid for
    the [▷]s in front of the shared ghost assertions; one branch does here. *)
  (** [typed_pcell_borrow_mut] is gone: [typing/] does not have it. *)

  (** ** Atomic operations on a one-cell permission cell *)

  (** The atomic operations are gone: [AtomicLoad], [AtomicStore],
    [AtomicCAS], their typing rules and the two [pcell1_*] helpers they
    alone use.  This tree's language has no concurrency, so it has no
    [GlobalLock] and no compare-and-swap, and [typing/pcell.v] carries
    none of them either. *)

End typing.
