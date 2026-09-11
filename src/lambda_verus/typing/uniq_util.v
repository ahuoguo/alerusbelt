From lrust.typing Require Export type.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section uniq_util.
  Context `{!typeG Σ}.
  
  Definition uniq_body_pers_component {𝔄} (ty: type 𝔄) (x: ~~ 𝔄) (ξi: positive) (d: nat) (g: nat) (idx: Idx)
  (κ: lft) (tid: thread_id) (l: cloc) : iProp Σ :=
    let ξ := PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi in
    &{κ, idx} (∃x' d' g', ⧖(S d' `max` g') ∗ .PC[ξ] x' (vπ x') (d', g') ∗ 
      ty.(ty_gho) x' d' g' tid ∗ l #↦!∗ ty.(ty_phys) x' tid).

  Definition uniq_body {𝔄} (ty: type 𝔄) (x: ~~ 𝔄) (ξi: positive) (d: nat) (g: nat) (idx: Idx)
      (κ: lft) (tid: thread_id) (l: cloc) : iProp Σ :=
    let ξ := PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi in
    .VO[ξ] x (d, g) ∗ ⧗1 ∗
    idx_bor_tok idx ∗
    &{κ, idx} (∃x' d' g', ⧖(S d' `max` g') ∗ .PC[ξ] x' (vπ x') (d', g') ∗ 
      ty.(ty_gho) x' d' g' tid ∗ l #↦!∗ ty.(ty_phys) x' tid).
      
  Lemma uniq_body_pers_component_impl {𝔄} (ty: type 𝔄) (x: ~~ 𝔄) (ξi: positive) (d: nat) (g: nat) (idx: Idx) (κ: lft) (tid: thread_id) (l: cloc)
    : uniq_body ty x ξi d g idx κ tid l -∗ uniq_body_pers_component ty x ξi d g idx κ tid l.
  Proof.
    unfold uniq_body. iIntros "[A [B [C D]]]". iFrame "D".
  Qed.
  
  (** [alloc_uniq_body]: upstream additionally minted a second
      prophecy [ζ] for the borrow's location-paired value and returned
      the observation [⟨π, π ζ = (l.1, π ξ)⟩]; with prophecies stripped
      both are gone. *)
  Lemma alloc_uniq_body
      {𝔄} (ty: type 𝔄) (x: ~~ 𝔄) (d: nat) (g: nat)
      (κ: lft) (tid: thread_id) (l: cloc) E
   :
    (↑Nllft ∪ ↑uniqN ⊆ E) →
    ⊢ llft_ctx -∗
      uniq_ctx -∗ ⧖(S d `max` g) -∗
      (▷ ty.(ty_gho) x d g tid) -∗
      l #↦!∗ ty.(ty_phys) x tid -∗
      ⧗1
      ={E}=∗
      ∃ ξi idx,
        let ξ := PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi in
        uniq_body ty x ξi d g idx κ tid l ∗
        ([†κ] ={↑Nllft}=∗
           ▷ ∃ x' (d' g' : nat), ⧖ (S d' `max` g') ∗
               .PC[ξ] x' (vπ x') (d', g') ∗
               ty_gho ty x' d' g' tid ∗ l #↦!∗ ty_phys ty x' tid).
  Proof.
    intros Hmask. iIntros "#LFT #UNIQ #time gho pt £".
    iMod (uniq_intro x (vπ x) (d, g) with "UNIQ") as (ξi) "[ξVo ξPc]". { set_solver. }
    set ξ := PrVar (𝔄 ↾ prval_to_inh (@vπ 𝔄 x)) ξi.
    iMod (llftl_borrow E κ (∃x' d' g', ⧖(S d' `max` g') ∗ .PC[ξ] x' (vπ x') (d', g') ∗ ty.(ty_gho) x' d' g' tid ∗ l #↦!∗ ty.(ty_phys) x' tid)%I with "LFT [gho pt ξPc]") as "[Bor Back]". { set_solver. }
    { iModIntro. iExists x, d, g. iFrame. iFrame "time". }
    iDestruct (llftl_bor_idx with "Bor") as (idx) "[Bor Tok]".
    iModIntro.
    iExists ξi, idx. iFrame.
  Qed.
 
  (*Lemma ty_share_uniq_body {𝔄} (ty: type 𝔄) vπ ξi d κ tid l κ' q E :
    ↑lftN ⊆ E → lft_ctx -∗ κ' ⊑ κ -∗ κ' ⊑ ty_lft ty -∗
    &{κ'} (uniq_body ty vπ ξi d κ tid l) -∗ q.[κ'] ={E}=∗ |={E}▷=>^(S d) |={E}=>
      &{κ'} 1:[PrVar (𝔄 ↾ prval_to_inh vπ) ξi] ∗ ty.(ty_shr) vπ d κ' tid l ∗ q.[κ'].
  Proof.
    set ξ := PrVar _ ξi. have ?: Inhabited 𝔄 := populate (vπ inhabitant).
    iIntros (?) "#LFT #In #In' Bor κ'".
    iMod (bor_sep with "LFT Bor") as "[BorVo Bor]"; [done|].
    iMod (bor_unnest with "LFT Bor") as "Bor"; [done|]. iIntros "!>!>!>".
    iMod (bor_shorten with "[] Bor") as "Bor".
    { iApply lft_incl_glb; [done|iApply lft_incl_refl]. }
    do 2 (iMod (bor_exists with "LFT Bor") as (?) "Bor"; [done|]).
    iMod (bor_sep with "LFT Bor") as "[_ Bor]"; [done|].
    iMod (bor_sep with "LFT Bor") as "[BorPc Borty]"; [done|].
    iMod (bor_combine with "LFT BorVo BorPc") as "Bor"; [done|].
    iMod (bor_acc_cons with "LFT Bor κ'") as "[[Vo Pc] ToBor]"; [done|].
    iMod (uniq_strip_later with "Vo Pc") as (<-<-) "[Vo Pc]".
    iDestruct (uniq_proph_tok with "Vo Pc") as "(Vo & ξ & ToPc)".
    iMod ("ToBor" with "[Vo ToPc] ξ") as "[Borξ κ']".
    { iIntros "!> >ξ !>!>". iFrame "Vo". by iApply "ToPc". }
    iMod (ty_share with "LFT [] Borty κ'") as "Upd"; [done..|].
    iApply (step_fupdN_wand with "Upd"). by iIntros "!> >[$$]".
  Qed.*)

  (*Lemma ty_own_proph_uniq_body {𝔄} (ty: type 𝔄) vπ ξi d κ tid l κ' q E :
    ↑lftN ⊆ E → lft_ctx -∗ κ' ⊑ κ -∗ κ' ⊑ ty_lft ty -∗
    uniq_body ty vπ ξi d κ tid l -∗ q.[κ'] ={E}=∗ |={E}▷=>^(S d) |={E}=>
      let ξ := PrVar (𝔄 ↾ prval_to_inh vπ) ξi in
      ∃ζl q', ⌜vπ ./ ζl⌝ ∗ q':+[ζl ++ [ξ]] ∗
        (q':+[ζl ++ [ξ]] ={E}=∗ uniq_body ty vπ ξi d κ tid l ∗ q.[κ']).
  Proof.
    set ξ := PrVar _ ξi. have ?: Inhabited 𝔄 := populate (vπ inhabitant).
    iIntros (?) "#LFT #Inκ #? [Vo Bor] [κ' κ'₊]".
    iMod (lft_incl_acc with "Inκ κ'") as (?) "[κ' Toκ']"; [done|].
    iMod (bor_acc with "LFT Bor κ'") as "[Big ToBor]"; [done|].
    iIntros "!>!>!>". iDestruct "Big" as (??) "(#⧖ & Pc & %vl & ↦ & ty)".
    iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
    iDestruct (uniq_proph_tok with "Vo Pc") as "(Vo & ξ & ToPc)".
    iMod (ty_own_proph with "LFT [] ty κ'₊") as "Upd"; [done..|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%&%&%& ζl & Toty) !>".
    rewrite proph_tok_singleton.
    iDestruct (proph_tok_combine with "ζl ξ") as (?) "[ζlξ Toζlξ]".
    iExists _, _. iSplit; [done|]. iIntros "{$ζlξ}ζlξ".
    iDestruct ("Toζlξ" with "ζlξ") as "[ζl ξ]".
    iMod ("Toty" with "ζl") as "[ty $]". iDestruct ("ToPc" with "ξ") as "Pc".
    iMod ("ToBor" with "[Pc ↦ ty]") as "[Bor κ']".
    { iNext. iExists _, _. iFrame "Pc ⧖". iExists _. iFrame. }
    iMod ("Toκ'" with "κ'") as "$". by iFrame.
  Qed.*)
  
  
  Lemma guards_exist_eq {A B C} (a' : A) (b' : B) (c' : C) (P Q : iProp Σ) (X : A → B → C → iProp Σ) E n1 n2 n :
    (∀ a b c , ((Q ∧ X a b c)%I ⊢ ⌜a = a' ∧ b = b' ∧ c = c'⌝)%I) →
    (n1 ≤ n) →
    (n2 ≤ n) →
    (P &&{E;n1}&&> Q) -∗
    (P &&{E;n2}&&> (∃ a b c , X a b c))
    -∗
    P &&{E;n}&&> (X a' b' c').
  Proof.
    intros Hent He1 He2. iIntros "PguardsQ PguardsBig".
    assert ((∃ (a : A) (b : B) (c : C), X a b c)
        ⊣⊢ (∃ (abc : A * B * C), X (abc.1.1) (abc.1.2) (abc.2))) as Hequiv1.
      { iSplit. { iDestruct 1 as (a b c) "X". iExists (a, b, c). iFrame. }
        iDestruct 1 as (abc) "X". iFrame. }
    assert ((∃ x : A * B * C, X x.1.1 x.1.2 x.2 ∗ ⌜x = (a', b', c')⌝) ⊣⊢ X a' b' c') as Hequiv2.
      { iSplit. { iDestruct 1 as (x) "[A %Heqs]". subst x. iFrame "A". }
        iIntros "X". iExists (a', b', c'). iFrame. done. }
    setoid_rewrite Hequiv1.
    leaf_hyp "PguardsQ" laters to n as "PguardsQ'"; first by trivial.
    leaf_hyp "PguardsBig" laters to n as "PguardsBig'"; first by trivial.
    iDestruct (guards_strengthen_exists _ _ _ (λ x, ⌜x = (a', b', c')⌝)%I with "PguardsQ' PguardsBig'") as "T".
      { intros x. simpl. iIntros "A". iDestruct (Hent with "A") as "%Heqs".
        destruct Heqs as [Heq1 [Heq2 Heq3]]. iPureIntro. subst a'. subst b'. subst c'.
        destruct x as [[a b] c]; trivial.
      }
    setoid_rewrite Hequiv2. iFrame.
  Qed.
  
  (*Lemma uniq_body_freeze {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l E G :
      ↑Nllft ⊆ E →
      llft_ctx -∗ 
      (G &&{↑NllftG}&&> @[κ]) -∗
      uniq_body ty x ξi d g idx κ tid l -∗
      G
      ={E}=∗
        G
        ∗ .VO[PrVar ( 𝔄 ↾ prval_to_inh (vπ x)) ξi] x (d, g)
        ∗ £ (2 * d * (g + 1) + 2)
        ∗ &{κ} (⧖(S d `max` g) ∗
                .PC[PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi] x (vπ x) (d, g) ∗
                ty_gho ty x d g tid ∗ l ↦∗ ty_phys ty x tid).
  Proof.
    intros Hmask. iIntros "#LFT Uniq". iDestruct "Uniq" as "(ξVo & £ & Tok & ξBor)".
    iDestruct (llftl_bor_idx_to_full with "ξBor Tok") as "ξBor".
    iMod (llftl_bor_freeze with "LFT ξBor") as (x2) "ξBor". { solve_ndisj. }
      Unshelve. 2: { split. apply x. }
    iMod (llftl_bor_freeze with "LFT ξBor") as (d2) "ξBor". { solve_ndisj. }
    iMod (llftl_bor_freeze with "LFT ξBor") as (g2) "ξBor". { solve_ndisj. }
    iModIntro. iFrame. iFrame "#".
    "ξVo" : .VO[PrVar (at_locₛ 𝔄 ↾ prval_to_inh (vπ (l1, x1))) ξi] (l1, x1) (d', g')
  "£saved" : £ (2 * d' * (g' + 1) + 2)
  "Tok" : idx_bor_tok idx
  "ξBor" : &{κ,idx}
             (∃ (x' : ~~ (`(pv_ty (PrVar (at_locₛ 𝔄 ↾ prval_to_inh (vπ (l1, x1))) ξi)))) 
                (d'0 g'0 : nat), ⧖(S d'0 `max` g'0) ∗
                .PC[PrVar (at_locₛ 𝔄 ↾ prval_to_inh (vπ (l1, x1))) ξi] x' (vπ x') (d'0, g'0) ∗
                ty_gho (own_ptr n ty) x' d'0 g'0 tid ∗ l ↦∗ ty_phys (own_ptr n ty) x' tid)*)

  
  Lemma shr_bor_from_finalized_uniq_bor {𝔄} (ty: type 𝔄) x ξi d g κ tid l F :
    ↑Nllft ⊆ F →
    llft_ctx -∗ 
    (&{κ} (⧖(S d `max` g) ∗
          .PC[PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi] x (vπ x) (d, g) ∗
          ty_gho ty x d g tid ∗ l #↦!∗ ty_phys ty x tid))
    ={F}=∗
   @[κ] &&{↑NllftG; 1}&&> (ty_gho ty x d g tid ∗ l #↦!∗ ty_phys ty x tid).
  Proof.
    intros Hmask. iIntros "#LFT Bor".
    iDestruct (llftl_bor_idx with "Bor") as (idx) "[#Bor Tok]".
    iMod (llftl_borrow_shared F κ (idx_bor_tok idx) with "Tok") as "[#Glat _]". { set_solver. }
    iDestruct (guards_remove_later_rhs with "Glat") as "G".
    iDestruct (llftl_idx_bor_guard' κ idx _ (@[κ])%I with "LFT Bor [] G") as "GBor".
      { iApply guards_refl. }
    iDestruct (guards_weaken_rhs_sep_r with "GBor") as "GBor2".
    iDestruct (guards_later_absorb_1 with "GBor2") as "GBor3".
   iModIntro.
   iDestruct (guards_weaken_rhs_sep_r with "GBor3") as "GBor4".
   iDestruct (guards_weaken_rhs_sep_r with "GBor4") as "GBor5".
   iFrame "GBor5".
  Qed.
  
  (** [resolve_uniq_body] removed: it resolved the borrow's prophecy,
      and [resolve] is stripped from this development. *)

  Lemma incl_uniq_body_pers_component {𝔄} (ty ty': type 𝔄) x ξi d g idx κ κ' tid l :
    κ' ⊑ κ -∗
    □ (∀x d tid vl, ty.(ty_gho) x d tid vl ↔ ty'.(ty_gho) x d tid vl) -∗
    (∀x tid, ⌜ ty_phys ty x tid = ty_phys ty' x tid ⌝) -∗
    uniq_body_pers_component ty x ξi d g idx κ tid l -∗ uniq_body_pers_component ty' x ξi d g idx κ' tid l.
  Proof.
    iIntros "#InLft #EqOwn %EqPhys Pc". unfold uniq_body_pers_component.
    unfold prval_to_inh.
    iApply (llftl_idx_shorten with "InLft").
    iApply llftl_idx_bor_iff; [|done]. iIntros "!>!>".
    iSplit.
      - iDestruct 1 as (x' d'' g'') "(⧖ & Pc & gho & phys)". iExists x', d'', g''.
        iFrame "⧖".
        iSplitL "Pc". { iDestruct (proph_ctrl_proper with "Pc") as "Pc"; last by iFrame "Pc".
          + trivial.
          + intros y. trivial.
          + trivial.
        }
        rewrite EqPhys. iFrame "phys".
        iApply "EqOwn". iFrame "gho".
     - iDestruct 1 as (vπ' d'' g'') "(⧖ & Pc & gho & phys)". iExists vπ', d'', g''.
        iFrame "⧖".
        iSplitL "Pc". { iDestruct (proph_ctrl_proper with "Pc") as "Pc"; last by iFrame "Pc".
          + trivial.
          + intros y. trivial.
          + trivial.
        }
        rewrite EqPhys. iFrame "phys".
        iApply "EqOwn". iFrame "gho".
  Qed.
  
  Lemma incl_uniq_body {𝔄} (ty ty': type 𝔄) x ξi d g idx κ κ' tid l :
    κ' ⊑ κ -∗
    □ (∀x d tid vl, ty.(ty_gho) x d tid vl ↔ ty'.(ty_gho) x d tid vl) -∗
    (∀x tid, ⌜ ty_phys ty x tid = ty_phys ty' x tid ⌝) -∗
    uniq_body ty x ξi d g idx κ tid l -∗ uniq_body ty' x ξi d g idx κ' tid l.
  Proof.
    iIntros "#InLft #EqOwn %EqPhys (A & B & Tok & Pc)".
    iFrame "B".
    iFrame "A". iFrame "Tok".
    iApply (incl_uniq_body_pers_component ty ty' x ξi d g idx κ κ' tid l with "InLft EqOwn");
      done.
  Qed.
  
    Lemma uniq_guards_get_guards_pt {𝔄} (ty: type 𝔄) (P Q R : iProp Σ) x d g ξi tid l :
    ((P ∗ .VO[PrVar (𝔄 ↾ prval_to_inh (@vπ 𝔄 x)) ξi] x (d, g) ∗ R) &&{ ↑NllftG }&&> (Q ∗
            ▷ ∃ x' (d' g' : nat), ⧖(S d' `max` g') ∗
                .PC[PrVar (𝔄 ↾ prval_to_inh (@vπ 𝔄 x)) ξi] x' (vπ x') (d', g') ∗ ty_gho ty x' d' g' tid ∗ l #↦!∗ ty_phys ty x' tid))
    ⊢ ((P ∗ .VO[PrVar (𝔄 ↾ prval_to_inh (@vπ 𝔄 x)) ξi] x (d, g) ∗ R) &&{ ↑NllftG; 1 }&&> l #↦!∗ ty_phys ty x tid)%I.
  Proof.
    iIntros "#G".
    iDestruct (guards_weaken_rhs_sep_r with "G") as "G2".
    iClear "G".
    iDestruct (guards_later_absorb_1 with "G2") as "G3". iClear "G2".
    iDestruct (guards_exist_eq x d g
      (P ∗ .VO[PrVar (𝔄 ↾ prval_to_inh (@vπ 𝔄 x)) ξi] x (d, g) ∗ R)%I
      (.VO[PrVar (𝔄 ↾ prval_to_inh (@vπ 𝔄 x)) ξi] x (d, g))%I
      _ _ 0 1 1
      with "[] G3") as "G4".
      - intros x0 d0 g0. iIntros "And".
        iDestruct (uniq_and_agree (PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi) with "[And]") as "%Heq".
        + iSplit. { iDestruct "And" as "[And _]". iFrame "And". }
          iDestruct "And" as "[_ (? & T & ?)]". iFrame "T".
        + iPureIntro. destruct Heq as [Heq1 Heq2]. inversion Heq2. intuition.
      - lia. - lia.
      - leaf_by_sep. iIntros "(? & ? & ?)". iFrame. iIntros. done.
      - iApply (guards_transitive_left with "G4 []").
        leaf_by_sep. iIntros "(? & ? & ? & ?)". iFrame. iIntros. done.
  Qed.
  
    
  (** [uniq_body_transform]: upstream minted a fresh prophecy [ζ] for
      the new body and *preresolved* the old [ξ] to [f (π ζ)], handing
      back the observation [⟨π, π ξ = f (π ζ)⟩] and a way to re-mint
      [.PC[ξ]] from an equalizer.  With prophecies stripped there is no
      observation to hand back; instead we simply keep the old [ξ]'s
      two agreement halves and retarget them with [uniq_update] when
      the borrow closes. *)
  Lemma uniq_body_transform {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) x x' d g ξi ξidx κ tid l l' E G
    (f: 𝔅 →ₛ 𝔄)
    :
      Timeless G →
      Inj eq eq ((!ₛ) f) →
      ↑Nllft ∪ ↑uniqN ⊆ E →
      llft_ctx -∗
      uniq_ctx -∗
      (▷ ty_gho ty x d g tid ∗ l #↦!∗ ty_phys ty x tid
        ={E}=∗ ▷ ty_gho ty' x' d g tid ∗ l' #↦!∗ ty_phys ty' x' tid ∗ 
        (∀ x'1 d1 g1 , ▷ ty_gho ty' x'1 d1 g1 tid ∗ l' #↦!∗ ty_phys ty' x'1 tid ∗ ⧖(S d1 `max` g1)
          ={↑NllftUsr}=∗ ∃ d2 g2, ▷ ty_gho ty (f ~~$ₛ x'1) d2 g2 tid ∗ l #↦!∗ ty_phys ty (f ~~$ₛ x'1) tid ∗ ⧖(S d2 `max` g2))
        ) -∗
      (G &&{↑NllftG}&&> @[κ]) -∗
      G -∗
      uniq_body ty x ξi d g ξidx κ tid l
      ={E}=∗ ∃ ζi ζidx ,
      uniq_body ty' x' ζi d g ζidx κ tid l' ∗ G.
  Proof.
    intros Htimeless Hinj Hmask. iIntros "#LFT #UNIQ wand #GuardsK G UniqBody".
    iDestruct "UniqBody" as "(ξVo & £saved & ξTok & ξBor)".
    iDestruct (llftl_bor_idx_to_full with "ξBor ξTok") as "ξBor".
    iMod (llftl_bor_acc_guarded with "LFT ξBor GuardsK G") as "[P ToBor]". { set_solver. }

    iMod (bi.later_exist_except_0 with "P") as (x1 d1 g1) "(>#⧖ & ξPc & Gho & >Pt)".

    iMod (uniq_strip_later with "ξVo ξPc") as (Hineq1 Hineq2) "[ξVo ξPc]".
    subst x1. inversion Hineq2. subst d1. subst g1.
    set ξ := PrVar (𝔄 ↾ prval_to_inh (@vπ 𝔄 x)) ξi.

    iMod (uniq_intro x' (vπ x') (d, g) with "UNIQ") as (ζi) "[ζVo ζPc]"; [set_solver|].

    iCombine "Gho Pt" as "GhoPt". iMod ("wand" with "GhoPt") as "[Gho [Pt R]]".

    iDestruct ("ToBor" with "[Pt R Gho ζPc ξVo ξPc]") as "A"; last first.
      - iMod (fupd_mask_mono with "A") as "[Bor G]". { set_solver. }
        iModIntro. iDestruct (llftl_bor_idx with "Bor") as (ζidx) "[ζBor ζTok]".
        iExists ζi. iExists ζidx. iFrame "G". iFrame "ζTok". iFrame "ζVo". iFrame "£saved".
        iFrame "ζBor".
      - iSplitR "ζPc Gho Pt". {
        iNext. iIntros "A".
        iMod (bi.later_exist_except_0 with "A") as (x1 d1 g1) "(>⧖2 & _ζPc & Gho2 & >Pt2)".
        iCombine "Gho2 Pt2 ⧖2" as "GhoPt2".
        iMod ("R" with "GhoPt2") as (d2 g2) "[Gho1 [Pt1 ⧖1]]".
        iMod (uniq_update ξ (f ~~$ₛ x1) (vπ (f ~~$ₛ x1)) (d2, g2)
                with "UNIQ ξVo ξPc") as "[_ξVo ξPc]". { solve_ndisj. }
        iModIntro. iNext. iFrame "Gho1". iFrame "Pt1". iFrame "⧖1". iFrame "ξPc".
     } {
        iFrame "ζPc". iFrame "Gho". iFrame "Pt". iFrame "⧖".
     }
  Qed.
  
  (* Verus: probably not needed *)
  Lemma split_mt_uniq_bor l' P Φ Ψ :
    (l' ↦∗: (λ vl, P ∗ [loc[l] := vl]
      ∃(d: nat) (ξi: positive), ⌜Ψ d ξi⌝ ∗ Φ l d ξi)) ⊣⊢
    P ∗ ∃(l: loc) d ξi, ⌜Ψ d ξi⌝ ∗ l' ↦ #l ∗ Φ l d ξi.
  Proof.
    iSplit.
    - iDestruct 1 as ([|[[]|][]]) "(↦ &$& big)"=>//. iDestruct "big" as (???) "?".
      iExists _, _, _. rewrite heap_mapsto_vec_singleton. by iFrame.
    - iIntros "($&%&%&%&%& ↦ &?)". iExists [_]. rewrite heap_mapsto_vec_singleton.
      iFrame "↦". iExists _, _. by iFrame.
  Qed.
  
  (* Similar to [†κ] but we can apply the basically_dead_incl rule immediately instead of
     performing an update.
     TODO should this have been the definition of [†κ'] to begin with?
     It might simplify a lot but has the disadvantage of not being timeless. *)
  Definition basically_dead (κ: lft) : iProp Σ := ∃ κ' , κ ⊑ κ' ∗ [†κ'].
  
  Definition basically_dead_incl κ κ' :
    κ' ⊑ κ -∗ basically_dead κ -∗ basically_dead κ'.
  Proof.
    iIntros "#Incl bd". iDestruct "bd" as (κ'') "[#Incl2 #Dead]".
    iExists κ''. iFrame "Dead". iApply (guards_transitive with "Incl Incl2").
  Qed.

  Lemma guard_inner_from_guard_uniq_body {𝔄} (ty: type 𝔄) x ξi d g ξidx κ tid l G n :
      llft_ctx -∗
      uniq_body_pers_component ty x ξi d g ξidx κ tid l -∗
      (G &&{↑NllftG; n}&&> uniq_body ty x ξi d g ξidx κ tid l) -∗
      (G &&{↑NllftG}&&> @[κ]) -∗
      (G &&{↑NllftG; n+1}&&> ((ty.(ty_gho) x d g tid) ∗ l #↦!∗ ty.(ty_phys) x tid)).
  Proof.
    iIntros "LFT #Bor #Guniq #Gk". unfold uniq_body.
    iDestruct (guards_weaken_rhs_sep_l with "Guniq") as "Gvo".
    iDestruct (guards_weaken_rhs_sep_r with "Guniq") as "Guniq2".
    iDestruct (guards_weaken_rhs_sep_r with "Guniq2") as "#G2".
    iDestruct (guards_weaken_rhs_sep_l with "G2") as "Gtok".
    iClear "G2". iClear "Guniq". iClear "Guniq2".
    iDestruct (llftl_idx_bor_guard' with "LFT Bor [] Gtok") as "Ginner".
      { leaf_goal laters to 0. { lia. } iFrame "Gk". }
    iDestruct (guards_weaken_rhs_sep_r with "Ginner") as "Ginner".
    iDestruct (guards_later_absorb_1 with "Ginner") as "Ginner".
    iDestruct (guards_exist_eq x d g _ _ _ _ _ _ (n+1) with "Gvo Ginner") as "G".
     - intros x0 d0 g0. iIntros "And".
        iDestruct (uniq_and_agree (PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi) with "[And]") as "%Heq".
        + iSplit. { iDestruct "And" as "[And _]". iFrame "And". }
          iDestruct "And" as "[_ (? & T & ?)]". iFrame "T".
        + iPureIntro. destruct Heq as [Heq1 Heq2]. inversion Heq2. intuition.
     - lia. - lia.
     - iApply (guards_transitive_left with "G []"). leaf_by_sep.
        iIntros "(A & B & C & D)". iFrame. iIntros. done.
  Qed.
  
  Lemma uniq_body_mono_upd {𝔄} (ty: type 𝔄) (x: ~~ 𝔄) (ξi: positive) (d g d' g': nat) (idx: Idx) (κ: lft) (tid: thread_id) (l: cloc) E G :
    Timeless G →
    ↑Nllft ∪ ↑uniqN ⊆ E →
    d ≤ d' →
    g ≤ g' →
    llft_ctx -∗
    uniq_ctx -∗
    ⧖(S d' `max` g') -∗
    (G &&{↑NllftG}&&> @[κ]) -∗
    G -∗
    uniq_body ty x ξi d g idx κ tid l ={E}=∗ 
    G ∗ uniq_body ty x ξi d' g' idx κ tid l.
  Proof.
    iIntros (Gtimeless Hmask Hle1 Hle2) "LFT UNIQ #⧖ #guards G UniqBody".
    iDestruct "UniqBody" as "(ξVo & £saved & ξTok & #ξBor)".
    iMod (llftl_bor_idx_acc_guarded with "LFT ξBor ξTok guards G") as "[Inner Back]";
        first by solve_ndisj.
        
    iMod (bi.later_exist_except_0 with "Inner") as (x'' d'' g'') "(⧖1 & ξPc & Gho & Phys)".
    iMod (uniq_strip_later with "ξVo ξPc") as "(%agree0 & %agree1 & ξVo & ξPc)".
    inversion agree1. subst x''. subst d''. subst g''.
    
    iMod (uniq_update (PrVar (𝔄 ↾ prval_to_inh (vπ x)) ξi) x _ (d', g') with "UNIQ ξVo ξPc") as "[ξVo ξPc]"; first by solve_ndisj.
    iDestruct ("Back" with "[Gho Phys ξPc]") as "B".
      { iFrame. iFrame "⧖". iDestruct (ty_gho_depth_mono with "Gho") as "[$ _]"; trivial. }
    iMod (fupd_mask_mono with "B") as "[idx G]"; first by set_solver.
    iModIntro. iFrame. iFrame "ξBor".
  Qed.
End uniq_util.
