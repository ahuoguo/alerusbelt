(** * Typing judgments for programs

  Ported from VerusBelt ([typing/programs.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer), itself from RustHornBelt.

  This is the file where the time-receipt machinery was densest, and it all
  goes.  [typed_write] used to hand back

    ∀y db', ▷ l #↦!∗: ty_own tyb' y db' (S db') tid -∗ ⧖(S db') -∗
      £(2*db'*db' + 4*db' + 2) -∗ H ={⊤}=∗ …

  - a later on the points-to, a persistent time receipt, and a *quadratic*
    later-credit budget, which the closing proof spends on
    [lc_fupd_elim_laterN] to strip the laters of a guard at index [d+1].
  [typed_read] is the same with [£(d+1)] in its precondition and a mask
  [⊤ ∖ ↑advN] carved out for the time-receipt invariant.  Later-free: no
  laters, no receipts, no credits, no [advN], and the guard carries no index.

  The weakest precondition is the *total* one over [verus_halt_wsat], and shared
  access to [L] is [Ltok γ L q] (see [nola.verus_halt.typing.ctx]). *)

From iris.proofmode Require Import environments proofmode.
From lrust.lang Require Import proofmode.
From lrust.lang.lib Require Import total_memcpy.
From lrust.typing_total Require Export type ctx lft_contexts type_context
  cont_context inv_context.
(** [ctx_wp], for the [lrustTotGS] instance: this file states weakest
  preconditions.  See the head of [typing_total/ctx_wp.v]. *)
From lrust.typing_total Require Import ctx_wp.
From nola.bi Require Import guard modw.
From nola.iris Require Import iprop.
(** Our [util] last, so that its [SemiIso] wins the name over Nola's; see
  [typing_total/type.v]. *)
From lrust.util Require Import basic.
Import GuardNotation ModwNotation TglWpwNotation iPropAppNotation.
Unset Default Proof Using.
(** [iris.prelude.options] sets [Default Goal Selector "!"], which rejects a
  bare tactic while more than one goal is focused.  It reaches this file
  through our imports and not through Nola's, so Nola's proofs - written
  against the default [1], "act on the first goal" - would otherwise need a
  focus fix every few lemmas.  Restoring [1] is a lint setting, not a
  soundness one. *)
Set Default Goal Selector "1".
Unset Suggest Proof Using.

Implicit Type (𝔄 𝔅: syn_type) (𝔄l 𝔅l: syn_typel).

Section typing.
  Context `{!typeG FML Σ}.

  (** Function Body *)
  (* This is an iProp because it is also used by the function type. *)
  (** The body's world satisfaction is a *parameter*.

    PLAN.md item 2's step 5 wants the judgment at the thesis's
    [∗_{k<j} Winv_k], and the shape of that is a world satisfaction, not
    a level: which worlds exist is [typing/level_ctx.v]'s business, and
    the only thing this file needs is that the judgment is stated over
    one of them.  [typed_body] is the instance at the ambient world, so
    every rule below - and all of [typing/] - is unchanged.

    What this buys is [ty-lev]: raising a body's execution level is
    [typed_body_at_wsat], one application of [tgl_wpw_incl_fupd], and
    nothing else.  See [typed_body_lv_le] in [typing/level_ctx.v]. *)
  Definition typed_body_at {𝔄l 𝔅} (W : iProp Σ)
    (E: elctx) (L: llctx) (I: invctx) (C: cctx 𝔅)
    (T: tctx 𝔄l) (e: expr) (tr: predl_trans' 𝔄l 𝔅) : iProp Σ :=
    ∀tid xl mask post iκs,
    llft_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
    llctx_interp L -∗ invctx_interp tid mask iκs I -∗
    cctx_interp tid iκs post C -∗ tctx_interp tid T xl -∗
      ⌜tr post xl mask⌝ -∗
      WP[W] e [{ _, cont_postcondition }].

  Definition typed_body {𝔄l 𝔅} (E: elctx) (L: llctx) (I: invctx) (C: cctx 𝔅)
    (T: tctx 𝔄l) (e: expr) (tr: predl_trans' 𝔄l 𝔅) : iProp Σ :=
    typed_body_at verus_halt_wsat E L I C T e tr.
  Global Arguments typed_body {_ _} _ _ _ _ _ _%E _%type.

  (** **** [ty-lev]

    A body proved over a smaller world satisfaction holds over a bigger
    one.  This is the thesis's [≤-→] and it is [tgl_wpw_incl_fupd] and
    nothing else, exactly as [typing/strat.v] has it. *)
  Lemma typed_body_at_wsat {𝔄l 𝔅} {W W' : iProp Σ}
      {E L} {I : invctx} {C : cctx 𝔅} {T : tctx 𝔄l} {e tr} :
    □ (W ={∅}=∗ W' ∗ (W' ={∅}=∗ W)) -∗
    typed_body_at W' E L I C T e tr -∗ typed_body_at W E L I C T e tr.
  Proof.
    iIntros "#∝ body" (tid xl mask post iκs) "A B C D E F G H".
    iApply (tgl_wpw_incl_fupd (E:=∅) with "[] [-]"); [set_solver| |].
    { iExact "∝". }
    by iApply ("body" with "A B C D E F G H").
  Qed.

  Global Instance typed_body_proper 𝔄l 𝔅 E L I C T e :
    Proper ((≡) ==> (≡)) (@typed_body 𝔄l 𝔅 E L I C T e).
  Proof.
    intros ?? EQ. unfold typed_body, typed_body_at. do 19 f_equiv. apply EQ.
  Qed.

  (** [cont_postcondition] is [True], which absorbs an update over the world
    satisfaction.  So a body's weakest precondition eats
    [|=[verus_halt_wsat]{⊤}=>] even when the expression is not known to be a
    non-value, which [fupdw_tgl_wpw_nonval] would require. *)
  Lemma fupdw_tgl_wpw_cont {e} :
    (|=[verus_halt_wsat]{⊤}=> WP[verus_halt_wsat] e [{ _, cont_postcondition }]) ⊢
      WP[verus_halt_wsat] e [{ _, cont_postcondition }].
  Proof.
    iIntros "big".
    iApply (tgl_wp_mono _ _ _ (λ _, (|=[verus_halt_wsat]{⊤}=> cont_postcondition)%I));
      [by iIntros|].
    by iApply fupdw_tgl_wpw_fupdw.
  Qed.
  Lemma typed_body_impl {𝔄l 𝔅} (tr tr': predl_trans' 𝔄l 𝔅) E L
      (I: invctx) (C: cctx 𝔅) (T: tctx 𝔄l) e :
    (∀post xl mask, tr post xl mask → tr' post xl mask) →
    typed_body E L I C T e tr' -∗ typed_body E L I C T e tr.
  Proof.
    move=> Imp. rewrite /typed_body /typed_body_at.
    iIntros "x * A B C D E F G %H".
    iApply ("x" with "A B C D E F G"). iPureIntro. by apply Imp.
  Qed.

  (** A value is typed at any transformer.  [cont_postcondition] is
    [True], so the judgment constrains termination and safety but says
    nothing about a value a program ends on - returning is a jump to a
    continuation, not the production of a value. *)
  Lemma type_value {𝔄l 𝔅} E L (I: invctx) (C: cctx 𝔅) (T: tctx 𝔄l)
      (e: expr) (v: val) `{!IntoVal e v} tr :
    ⊢ typed_body E L I C T e tr.
  Proof.
    rewrite /typed_body /typed_body_at.
    iIntros "* _ _ _ _ _ _ _ _". iApply tgl_wp_value.
    by rewrite /cont_postcondition.
  Qed.

  Lemma typed_body_vacuous {𝔄l 𝔅} E L
      (I: invctx) (C: cctx 𝔅) (T: tctx 𝔄l) e :
    ⊢ typed_body E L I C T e (λ _ _ _, False%type).
  Proof.
    rewrite /typed_body /typed_body_at.
    iIntros "* A B C D E F G %Obs". done.
  Qed.

  Lemma typed_body_tctx_incl {𝔄l 𝔅l ℭ} tr' tr (T: tctx 𝔄l) (T': tctx 𝔅l) E L
      (I: invctx) (C: cctx ℭ) e :
    tctx_incl E L T T' tr' →
    typed_body E L I C T' e tr -∗ typed_body E L I C T e (tr' ∘ tr).
  Proof.
    iIntros ([? In]) "e". iIntros (?????) "#LFT #UNIQ #E L Ic C T Obs".
    iApply fupdw_tgl_wpw_cont. iIntros "W".
    iMod (Ltok_alloc with "L W") as "[W (%γ & tok)]".
    iMod (In with "LFT UNIQ E tok T Obs W") as "[W (%&tok&T'&Obs)]".
    iMod (Ltok_withdraw with "tok W") as "[W L]". iModIntro. iFrame "W".
    iApply ("e" with "LFT UNIQ E L Ic C T' Obs").
  Qed.

  (** Instruction *)
  Definition typed_instr {𝔄l 𝔅l} (E: elctx) (L: llctx) (I: invctx)
    (T: tctx 𝔄l) (e: expr) (T': val → tctx 𝔅l) (tr: predl_trans 𝔄l 𝔅l) : Prop :=
    ∀tid post mask iκs xl, llft_ctx -∗ uniq_ctx -∗
      elctx_interp E -∗ llctx_interp L -∗ invctx_interp tid mask iκs I -∗
      tctx_interp tid T xl -∗ ⌜tr post xl mask⌝ -∗
      WP[verus_halt_wsat] e [{ v, ∃xl',
        llctx_interp L ∗ invctx_interp tid mask iκs I ∗
        tctx_interp tid (T' v) xl' ∗ ⌜post xl' mask⌝ }].
  Global Arguments typed_instr {_ _} _ _ _ _ _%E _ _%type.

  Definition typed_inv_instr {𝔄l 𝔅l} (E: elctx) (L: llctx) (I: invctx)
    (T: tctx 𝔄l) (e: expr) (I': invctx) (T': val → tctx 𝔅l)
    (tr: predl_trans 𝔄l 𝔅l) : Prop :=
    ∀tid post mask iκs xl, llft_ctx -∗ uniq_ctx -∗
      elctx_interp E -∗ llctx_interp L -∗ invctx_interp tid mask iκs I -∗
      tctx_interp tid T xl -∗ ⌜tr post xl mask⌝ -∗
      WP[verus_halt_wsat] e [{ v, ∃xl' mask',
        llctx_interp L ∗ invctx_interp tid mask' iκs I' ∗
        tctx_interp tid (T' v) xl' ∗ ⌜post xl' mask'⌝ }].

  (** Writing and Reading *)

  Definition typed_write {𝔄 𝔅 𝔄' 𝔅'} (E: elctx) (L: llctx) (ty: type 𝔄)
    (tyb: type 𝔅) (ty': type 𝔄') (tyb': type 𝔅') (gt: ~~𝔄 → ~~𝔅)
    (st: ~~𝔄 → ~~𝔅' → ~~𝔄' → Prop) : Prop :=
    tyb.(ty_size) = tyb'.(ty_size) ∧ ∀x d (v: fancy_val) tid γ q,
    llft_ctx -∗ uniq_ctx -∗ elctx_interp E -∗ Ltok γ L q -∗
    ty_own ty x d d tid [v] =[verus_halt_wsat]{⊤}=∗
      ∃(l: cloc) (d':nat) (Hx: FML $oi Σ),
      ⌜v = FVal #(l.1)⌝ ∗ ⌜d = S d'⌝ ∗ l #↦!∗: ty_own tyb (gt x) d' d tid ∗
      bor_sem Hx ∗ (bor_sem Hx &&{Wguard}&&> l #↦∗_) ∗
      ∀y db', l #↦!∗: ty_own tyb' y db' (S db') tid -∗ bor_sem Hx
        =[verus_halt_wsat]{⊤}=∗ ∃z, Ltok γ L q ∗ ⌜st x y z⌝ ∗
          ty_own ty' z (S db') (d `max` S db') tid [v].
  Global Arguments typed_write {_ _ _ _} _ _ _%T _%T _%T _%T _%type _%type.

  Definition typed_read {𝔄 𝔅 𝔄'} (E: elctx) (L: llctx) (ty: type 𝔄)
    (tyb: type 𝔅) (ty': type 𝔄') (gt: ~~𝔄 → ~~𝔅) (st: ~~𝔄 → ~~𝔄' → Prop)
    : Prop := ∀x d v tid γ q,
    llft_ctx -∗ elctx_interp E -∗ Ltok γ L q -∗
    ty_own ty x d d tid [v] =[verus_halt_wsat]{⊤}=∗
      ∃(l: cloc) (vl_concrete: list val) (vl: list fancy_val) (Hx: FML $oi Σ),
        ⌜v = FVal #(l.1)⌝ ∗ ⌜length vl_concrete = length vl⌝ ∗
        bor_sem Hx ∗ (bor_sem Hx &&{Wguard}&&> (l.1 ↦[^ l.2]∗ vl_concrete)) ∗
        (∀ l₁ c₁ , (l₁, c₁) #↦∗_ ∗ (l₁, c₁) #↦∗ vl_concrete ={∅}=∗
          (l₁, c₁) #↦∗_ ∗ (l₁, c₁) #↦!∗ vl) ∗
        ⌜StackOkay tyb → vl = fmap FVal vl_concrete⌝ ∗
        ty_own tyb (gt x) d d tid vl ∗ (bor_sem Hx =[verus_halt_wsat]{⊤}=∗
          ∃ z, ⌜st x z⌝ ∗ Ltok γ L q ∗ ty_own ty' z d d tid [v]).
  Global Arguments typed_read {_ _ _} _ _ _%T _%T _%T _ _%type.

  Definition typed_instr_ty {𝔄l 𝔅} (E: elctx) (L: llctx) (I: invctx)
    (T: tctx 𝔄l) (e: expr) (ty: type 𝔅) (tr: pred' (~~𝔅) → predl 𝔄l) : Prop :=
    typed_instr E L I T e (λ v, +[v ◁ ty]) (λ post al, tr (λ b, post -[b]) al).
  Global Arguments typed_instr_ty {_ _} _ _ _ _ _%E _%T _%type.

  Definition typed_val {𝔄} (v: val) (ty: type 𝔄) (a: ~~𝔄) : Prop :=
    ∀E L I, typed_instr_ty E L I +[] (of_val v) ty (λ post _, post a).
  Global Arguments typed_val {_} _%V _%T _%type.

  (* This lemma is helpful for specifying the predicate transformer. *)
  Lemma type_with_tr 𝔄l 𝔅 tr E L (I: invctx) (C: cctx 𝔅) (T: tctx 𝔄l) e :
    typed_body E L I C T e tr -∗ typed_body E L I C T e tr.
  Proof. iIntros. done. Qed.

  (* This lemma is helpful when switching from proving unsafe code in Iris
     back to proving it in the type system. *)
  Lemma type_type {𝔄l 𝔅} (T: tctx 𝔄l) xl mask tr E L (I: invctx) (C: cctx 𝔅)
      e tid post iκs :
    typed_body E L I C T e tr -∗
    llft_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
    llctx_interp L -∗ invctx_interp tid mask iκs I -∗
    cctx_interp tid iκs post C -∗ tctx_interp tid T xl -∗
    ⌜tr post xl mask⌝ -∗ WP[verus_halt_wsat] e [{ _, cont_postcondition }].
  Proof.
    iIntros "Bd LFT UNIQ E L I C T Obs".
    iApply ("Bd" with "LFT UNIQ E L I C T Obs").
  Qed.

  Lemma type_equivalize_lft {𝔄l 𝔅} E L I (C: cctx 𝔅) (T: tctx 𝔄l) κ κ' e tr :
    typed_body (κ ⊑ₑ κ' :: κ' ⊑ₑ κ :: E) L I C T e tr -∗
    typed_body E (κ ⊑ₗ [κ'] :: L) I C T e tr.
  Proof.
    iIntros "e" (?????) "#LFT UNIQ E [Eq L] I C T Obs".
    iApply fupdw_tgl_wpw_cont. iIntros "W".
    iMod (lctx_equalize_lft with "Eq W") as "[W [In In']]". iModIntro. iFrame "W".
    iApply ("e" with "LFT UNIQ [$E $In $In'] L I C T Obs").
  Qed.

  Lemma type_let' {𝔄l 𝔅l ℭl 𝔇} (T1: tctx 𝔄l) (T2: val → tctx 𝔅l) tr tr'
      (T: tctx ℭl) (I: invctx) (C: cctx 𝔇) xb e e' E L :
    Closed (xb :b: []) e' → typed_instr E L I T1 e T2 tr →
    (∀v: val, typed_body E L I C (T2 v h++ T) (subst' xb v e') tr') -∗
    typed_body E L I C (T1 h++ T) (let: xb := e in e')%E (λ post acl,
      let '(al, cl) := psep acl in tr (λ bl, tr' post (bl -++ cl)) al).
  Proof.
    iIntros "% %Inst e'" (? vπl2 ???). move: (papp_ex vπl2)=> [vπl[vπl'->]].
    iIntros "#LFT #UNIQ #E L I C [T1 T] %Obs". twp_bind e.
    iApply (tgl_wp_wand with "[L I T1]").
    { iApply (Inst with "LFT UNIQ E L I T1").
      iPureIntro. move: Obs. by rewrite /trans_upper papp_sepl. }
    iIntros (v) "A".
    iDestruct "A" as (xl') "(L & I & T2 & %Obs2)". twp_let. iCombine "T2 T" as "T2T".
    iApply ("e'" with "LFT UNIQ E L I C T2T").
    iPureIntro. move: Obs2. by rewrite papp_sepr.
  Qed.

  Lemma type_let'_with_inv {𝔄l 𝔅l ℭl 𝔇} (T1: tctx 𝔄l) (T2: val → tctx 𝔅l) tr tr'
      (T: tctx ℭl) (I1 I2: invctx) (C: cctx 𝔇) xb e e' E L :
    Closed (xb :b: []) e' → typed_inv_instr E L I1 T1 e I2 T2 tr →
    (∀v: val, typed_body E L I2 C (T2 v h++ T) (subst' xb v e') tr') -∗
    typed_body E L I1 C (T1 h++ T) (let: xb := e in e')%E (λ post acl,
      let '(al, cl) := psep acl in tr (λ bl, tr' post (bl -++ cl)) al).
  Proof.
    iIntros "% %Inst e'" (? vπl2 ???). move: (papp_ex vπl2)=> [vπl[vπl'->]].
    iIntros "#LFT #UNIQ #E L I C [T1 T] %Obs". twp_bind e.
    iApply (tgl_wp_wand with "[L I T1]").
    { iApply (Inst with "LFT UNIQ E L I T1").
      iPureIntro. move: Obs. by rewrite /trans_upper papp_sepl. }
    iIntros (v) "A".
    iDestruct "A" as (xl' mask') "(L & I & T2 & %Obs2)". twp_let.
    iCombine "T2 T" as "T2T".
    iApply ("e'" with "LFT UNIQ E L I C T2T").
    iPureIntro. move: Obs2. by rewrite papp_sepr.
  Qed.

  Lemma type_let {𝔄l 𝔅l ℭl 𝔇l 𝔈} (T1: tctx 𝔄l) (T2: val → tctx 𝔅l) tr tr' trx
    (T: tctx ℭl) (T': tctx 𝔇l) E L I (C: cctx 𝔈) xb e e' tr_res :
    Closed (xb :b: []) e' → typed_instr E L I T1 e T2 tr →
    tctx_extract_ctx E L T1 T T' trx → tr_res ≡ trx ∘ (trans_upper tr ∘ tr') →
    (∀v: val, typed_body E L I C (T2 v h++ T') (subst' xb v e') tr') -∗
    typed_body E L I C T (let: xb := e in e')%E tr_res.
  Proof.
    iIntros (???->) "?". iApply (typed_body_tctx_incl trx); [done|].
    by iApply type_let'.
  Qed.

  Lemma type_let_with_inv {𝔄l 𝔅l ℭl 𝔇l 𝔈} (T1: tctx 𝔄l) (T2: val → tctx 𝔅l)
    tr tr' trx (T: tctx ℭl) (T': tctx 𝔇l) E L I1 I2 (C: cctx 𝔈) xb e e' tr_res :
    Closed (xb :b: []) e' → typed_inv_instr E L I1 T1 e I2 T2 tr →
    tctx_extract_ctx E L T1 T T' trx → tr_res ≡ trx ∘ (trans_upper tr ∘ tr') →
    (∀v: val, typed_body E L I2 C (T2 v h++ T') (subst' xb v e') tr') -∗
    typed_body E L I1 C T (let: xb := e in e')%E tr_res.
  Proof.
    iIntros (???->) "?". iApply (typed_body_tctx_incl trx); [done|].
    by iApply type_let'_with_inv.
  Qed.

  Lemma type_val {𝔄 𝔅l ℭ} v (a: ~~𝔄) ty (T: tctx 𝔅l) E L (I: invctx)
      (C: cctx ℭ) xb e tr :
    Closed (xb :b: []) e → typed_val v ty a →
    (∀v': val, typed_body E L I C (v' ◁ ty +:: T) (subst' xb v' e) tr) -∗
    typed_body E L I C T (let: xb := v in e)%E (λ post bl, tr post (a -:: bl)).
  Proof.
    iIntros (? Val) "?". iApply type_let; [apply Val|solve_typing|done..].
  Qed.

  Lemma type_seq {𝔄l 𝔅l ℭl 𝔇l 𝔈} (T1: tctx 𝔄l) (T2: tctx 𝔅l)
    (T: tctx ℭl) (T': tctx 𝔇l) E L (I: invctx) (C: cctx 𝔈) e e' tr tr' trx
    tr_res :
    Closed [] e' → typed_instr E L I T1 e (const T2) tr →
    tctx_extract_ctx E L T1 T T' trx → tr_res ≡ trx ∘ (trans_upper tr ∘ tr') →
    typed_body E L I C (T2 h++ T') e' tr' -∗ typed_body E L I C T (e;; e')%E tr_res.
  Proof. iIntros. iApply (type_let _ (const T2))=>//. by iIntros. Qed.

  Lemma type_seq_with_inv {𝔄l 𝔅l ℭl 𝔇l 𝔈} (T1: tctx 𝔄l) (T2: tctx 𝔅l)
    (T: tctx ℭl) (T': tctx 𝔇l) E L (I1 I2: invctx) (C: cctx 𝔈) e e' tr tr' trx
    tr_res :
    Closed [] e' → typed_inv_instr E L I1 T1 e I2 (const T2) tr →
    tctx_extract_ctx E L T1 T T' trx → tr_res ≡ trx ∘ (trans_upper tr ∘ tr') →
    typed_body E L I2 C (T2 h++ T') e' tr' -∗
    typed_body E L I1 C T (e;; e')%E tr_res.
  Proof. iIntros. iApply (type_let_with_inv _ (const T2))=>//. by iIntros. Qed.

  Lemma type_newlft {𝔄l 𝔅} κl E L (I: invctx) (C: cctx 𝔅) (T: tctx 𝔄l) e tr :
    Closed [] e → (∀κ, typed_body E (κ ⊑ₗ κl :: L) I C T e tr) -∗
    typed_body E L I C T (Newlft;; e) tr.
  Proof.
    iIntros (?) "e %%%%% #LFT UNIQ E L I C T Obs".
    iApply fupdw_tgl_wpw_cont. iIntros "W".
    iDestruct (llftl_begin' with "LFT") as "B".
    iDestruct (bupdw_incl (W:=verus_halt_wsat) with "B") as "B'".
    iMod ("B'" with "W") as "[W (%Λ & Λ & %Hinh)]". iModIntro. iFrame "W".
    set κ' := lft_intersect_list κl. twp_seq.
    iApply ("e" $! κ' ⊓ Λ with "LFT UNIQ E [Λ $L] I C T Obs").
    rewrite /llctx_interp. iExists Λ. iFrame "Λ". by iSplit.
  Qed.

  (** The original runs [Endlft] one [Skip] at a time, because each of the
    [|={⊤}▷=>^(d*(d+1))] updates it has to discharge needs physical steps.
    Later-free the ghost work is all one update, and the three [Skip]s are
    just executed. *)
  (** Nola threads a [resolve_unblock_tctx] step through here, to resolve
    the prophecies of the types that [κ] is about to kill before unblocking
    them.  With prophecies stripped there is nothing to resolve, so this is
    [unblock_tctx] alone, exactly as in [typing/programs.v]. *)
  Lemma type_endlft {𝔄l 𝔅l ℭ} (T: tctx 𝔄l) (T': tctx 𝔅l)
      (f: plist indep_interp_of_syn_type 𝔄l →
          plist indep_interp_of_syn_type 𝔅l → Prop)
      κ κl tr e E L I (C: cctx ℭ) :
    Closed [] e → unblock_tctx E L κ T T' f →
    typed_body E L I C T' e tr -∗
    typed_body E (κ ⊑ₗ κl :: L) I C T (Endlft;; e)
      (λ post xl mask, ∀ xl', f xl xl' → tr post xl' mask)%type.
  Proof.
    iIntros (? Un) "e %tid %xl %mask %post %iκs".
    iIntros "#LFT #UNIQ #E L' I C T %Obs".
    iApply fupdw_tgl_wpw_cont. iIntros "W".
    iDestruct "L'" as "[(%κ0 & %Hκ & κ' & %ToDead) L]".
    iDestruct (llftl_end' with "LFT κ'") as "End"; [apply ToDead|].
    iDestruct (fupdw_incl_mask (W:=verus_halt_wsat) (E':=⊤) with "End") as "End'";
      [set_solver|].
    iMod ("End'" with "W") as "[W †]".
    iMod (Ltok_alloc with "L W") as "[W (%γ1 & tok)]".
    iMod (Un with "LFT E tok [†] T W") as "[W (%&tok&T'&%Hf)]".
    { simpl in *. subst. rewrite llftl_end_inter. by iRight. }
    iMod (Ltok_withdraw with "tok W") as "[W L]". iModIntro. iFrame "W".
    do 6 twp_seq.
    iApply ("e" with "LFT UNIQ E L I C T' [%]"). by apply Obs.
  Qed.

  (** [type_resolve_instr] and [type_resolve] are elided with [resolve]. *)

  Lemma type_path_instr {𝔄} p (ty: type 𝔄) E L I :
    typed_instr_ty E L I +[p ◁ ty] p ty (λ post '-[v], post v).
  Proof.
    iIntros (????[vπ[]]) "_ _ _ $$ [T _] Obs". iApply (twp_hasty with "T").
    iIntros (v d _) "?". iExists -[vπ]. do 2 (iSplit; [|done]). iExists v, d.
    rewrite eval_path_of_val. by iFrame.
  Qed.

  Lemma type_letpath {𝔄 𝔅l ℭl 𝔇} (ty: type 𝔄) (T: tctx 𝔅l) (T': tctx ℭl)
    (I: invctx) (C: cctx 𝔇) x p e trx tr E L :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p ◁ ty] T T' trx →
    (∀v: val, typed_body E L I C (v ◁ ty +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := p in e) (trx ∘ tr).
  Proof.
    iIntros (? Extr) "?". iApply type_let; [by eapply type_path_instr|done| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case.
  Qed.
  (** Assignment.

    The original splits a [£(...)] budget four ways here and spends it on
    [lc_fupd_elim_later] / [lc_step_fupdN_elim_later] to strip the laters of
    the write guard and of [resolve]'s step-taking update.  None of that is
    needed. *)
  (** Nola's statement also takes [resolve' E L tyb Φ], to resolve the
    prophecies of the value being overwritten, and its postcondition is
    [Φ (gt a) π (…)].  Stripped, as in [typing/programs.v]. *)
  Lemma type_assign_instr {𝔄 𝔅 𝔄' 𝔅'} (ty: type 𝔄) (tyb: type 𝔅)
                          (ty': type 𝔄') (tyb': type 𝔅') gt st p pb E L I :
    typed_write E L ty tyb ty' tyb' gt st →
    typed_instr E L I +[p ◁ ty; pb ◁ tyb'] (p <- pb) (λ _, +[p ◁ ty'])
      (λ post '-[a; b], λ mask, ∀ z, st a b z → post -[z] mask).
  Proof.
    iIntros ([Eq Wrt] ???? (x & y &[]))
      "#LFT #UNIQ #E L I (p & pb & _) %Obs".
    iApply tgl_wpw_fupdw_nonval; [done|].
    iApply fupdw_tgl_wpw_nonval; [done|]. iIntros "W".
    iMod (Ltok_alloc with "L W") as "[W (%γ & tok)]". iModIntro. iFrame "W".
    twp_bind p. iApply (twp_hasty with "p"). iIntros (v d Heq) "ty".
    iApply fupdw_tgl_wpw_nonval; [done|]. iIntros "W".
    iMod (Wrt with "LFT UNIQ E tok ty W") as
      "(W & %l & %d' & %Hx & %Heqv & -> & (%vl & ↦ & A) & H & #Hguards & Toty')".
    inversion Heqv. subst v.
    iDestruct "A" as "[tyb_ghos %tyb_phys]".
    assert (length vl = ty_size tyb) as Sz.
    { rewrite <- tyb_phys. apply ty_size_eq. }
    iModIntro. iFrame "W".
    twp_bind pb. iApply (twp_hasty with "pb"). iIntros (vb db ?) "tyb'".
    iApply fupdw_tgl_wpw_nonval; [done|]. iIntros "W".
    iDestruct "tyb'" as "[tyb'_gho %tyb'_phys]".
    assert (ty_size tyb' = 1) as Sz'.
    { rewrite <- (ty_size_eq _ y tid). rewrite tyb'_phys. trivial. }
    rewrite <-Eq in Sz'. rewrite <-Sz in Sz'. generalize Sz'.
    case vl=> [|?[|]]=>// ?.
    iMod (mapsto_vec_untether_singleton _ _ ⊤ ∅ with "↦")
      as (v₀ l₀ c₀) "[%Hl [↦ Retether]]". subst l. simpl.
    iModIntro. iFrame "W".
    iDestruct (guard_rhs_sep_l (Q:=((l₀, c₀) #↦_)%I) (R:=True%I)
      with "Hguards") as "#Hg".
    iApply (twp_write_na_guarded _ _ _ _ _ _ _ Hx with "[H ↦]").
    { iFrame "Hg". iFrame. }
    iIntros "[↦ H] W".
    iMod ("Toty'" $! y db with "[↦ tyb'_gho] H W")
      as "(W & %z & tok1 & %Hz & ty')".
    { iExists [FVal vb]. rewrite -heap_complete_mapsto_fancy_singleton.
      iFrame "↦". iSplitL.
      { iDestruct (ty_gho_depth_mono with "tyb'_gho") as "$".
        { lia. } { lia. } }
      done. }
    iMod (Ltok_withdraw with "tok1 W") as "[W L]". iModIntro. iFrame "W".
    iExists -[z]. iFrame "L I". iSplit.
    - rewrite right_id tctx_hasty_val'; [|done].
      iExists (S (d' `max` db)). iDestruct "ty'" as "[gho phys]". iFrame.
      iDestruct (ty_gho_depth_mono with "gho") as "$". { lia. } { lia. }
    - iPureIntro. by apply Obs.
  Qed.

  (** Dereference.

    The original takes [£(d+1)] through [typed_read] and spends it on the
    read guard's laters; [⊤ ∖ ↑advN] is the mask with the time-receipt
    invariant carved out.  Neither survives. *)
  Lemma type_deref_instr {𝔄 𝔅 𝔄'} (ty: type 𝔄) (tyb: type 𝔅) (ty': type 𝔄')
                                    gt st p E L I :
    StackOkay tyb →
    tyb.(ty_size) = 1%nat → typed_read E L ty tyb ty' gt st →
    typed_instr E L I +[p ◁ ty] (!p) (λ v, +[v ◁ tyb; p ◁ ty'])
      (λ post '-[a], λ mask, ∀ z, st a z → post -[gt a; z] mask).
  Proof.
    move=> StackOk Sz Rd. iIntros (????[x[]]) "#LFT _ #E L I [p _] %obs".
    iApply tgl_wpw_fupdw_nonval; [done|].
    iApply fupdw_tgl_wpw_nonval; [done|]. iIntros "W".
    iMod (Ltok_alloc with "L W") as "[W (%γ & tok)]". iModIntro. iFrame "W".
    twp_bind p. iApply (twp_hasty with "p"). iIntros (v d Heq) "ty".
    iApply fupdw_tgl_wpw_nonval; [done|]. iIntros "W".
    iMod (Rd with "LFT E tok ty W") as
      "(W & %l & %vl_concrete & %vl & %Hx & %Heqv & %Hleneq & Q & #QPt &
        Retether & %Conc & Own & Toty')".
    have Conc0 := Conc StackOk. subst vl.
    inversion Heqv. subst v.
    iDestruct "Own" as "[tyb_gho %tyb_phys]".
    assert (length vl_concrete = 1) as Sz1.
    { erewrite <- length_fmap. rewrite <- tyb_phys. rewrite ty_size_eq. trivial. }
    case vl_concrete as [|v[|]]=>//. iModIntro. iFrame "W".
    iApply (twp_read_na_guarded_cells_singleton _ _ _ _ _ Hx with "[Q]").
    { iFrame "QPt Q". }
    iIntros "H W".
    iMod ("Toty'" with "H W") as "(W & %z & %Hz & tok & ty')".
    iMod (Ltok_withdraw with "tok W") as "[W L]". iModIntro. iFrame "W".
    iExists -[gt x; z]. iFrame "L I". iSplit.
    - rewrite right_id tctx_hasty_val tctx_hasty_val'; [|done].
      iSplitL "tyb_gho".
      + iExists d. iFrame "tyb_gho". iPureIntro. by rewrite tyb_phys.
      + iExists d. iFrame "ty'".
    - iPureIntro. by apply obs.
  Qed.

  Lemma type_deref {𝔄 𝔅 𝔄' 𝔄l 𝔅l ℭ} (ty: type 𝔄) (tyb: type 𝔅)
                   (ty': type 𝔄') gt st
                   (T: tctx 𝔄l) (T': tctx 𝔅l) p x e trx tr E L
                   (I: invctx) (C: cctx ℭ) :
    StackOkay tyb →
    Closed (x :b: []) e → tctx_extract_ctx E L +[p ◁ ty] T T' trx →
    typed_read E L ty tyb ty' gt st → tyb.(ty_size) = 1%nat →
    (∀v: val, typed_body E L I C (v ◁ tyb +:: p ◁ ty' +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := !p in e)
      (trx ∘ (λ post '(a -:: al), λ mask,
        ∀ z, st a z → tr post (gt a -:: z -:: al) mask))%type.
  Proof.
    iIntros (?? Extr ??) "?".
    iApply type_let; [by eapply type_deref_instr|done| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case.
  Qed.

  Lemma type_assign {𝔄 𝔅 𝔄' 𝔅' 𝔄l 𝔅l ℭ} (ty: type 𝔄) (tyb: type 𝔅)
                    (ty': type 𝔄') (tyb': type 𝔅') gt st p pb E L
                    (I: invctx) (C: cctx ℭ) (T: tctx 𝔄l) (T': tctx 𝔅l) trx tr e :
    Closed [] e → tctx_extract_ctx E L +[p ◁ ty; pb ◁ tyb'] T T' trx →
    typed_write E L ty tyb ty' tyb' gt st →
    typed_body E L I C (p ◁ ty' +:: T') e tr -∗
    typed_body E L I C T (p <- pb;; e)
      (trx ∘ (λ post '(a -:: b -:: bl), λ mask,
        ∀ z, st a b z → tr post (z -:: bl) mask))%type.
  Proof.
    iIntros (? Extr ?) "?".
    iApply type_seq; [by eapply type_assign_instr|done| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case=> [?[??]].
  Qed.
  (** Memory copy.

    The original splits a six-way [£] budget here and feeds it to
    [wp_memcpy_guarded] (which itself wants [£(6*d)] and [⧖d]), to
    [lc_step_fupdN_elim_later] for [resolve], and to [lc_fupd_elim_laterN] for
    the write guard.  Later-free [twp_memcpy_guarded] needs nothing. *)
  Lemma type_memcpy_instr {𝔄 𝔄' 𝔅 𝔅' ℭ ℭ'} (tyw: type 𝔄) (tyw': type 𝔄')
        (tyr: type 𝔅) (tyr': type 𝔅') (tyb: type ℭ) (tyb': type ℭ')
        gtw stw gtr str (n: Z) pw pr E L I :
    typed_write E L tyw tyb tyw' tyb' gtw stw →
    typed_read E L tyr tyb' tyr' gtr str → n = tyb'.(ty_size) →
    typed_instr E L I +[pw ◁ tyw; pr ◁ tyr] (pw <-{n} !pr)
      (λ _, +[pw ◁ tyw'; pr ◁ tyr'])
      (λ post '-[a; b], λ mask,
        ∀ zw zr, stw a (gtr b) zw → str b zr → post -[zw; zr] mask).
  Proof.
    iIntros ([Eq Wrt] Rd ->????(xw & xr &[]))
      "/= #LFT #UNIQ #E L I (pw & pr &_) %Obs".
    iApply tgl_wpw_fupdw_nonval; [done|].
    iApply fupdw_tgl_wpw_nonval; [done|]. iIntros "W".
    iMod (Ltok_alloc with "L W") as "[W (%γ & tok)]".
    iDestruct (Ltok_split_1 with "tok") as "[t1 t2]". iModIntro. iFrame "W".
    twp_bind pw. iApply (twp_hasty with "pw"). iIntros (vw dw ?) "tyw".
    iApply fupdw_tgl_wpw_nonval; [done|]. iIntros "W".
    iMod (Wrt with "LFT UNIQ E t1 tyw W") as
      "(W & %l & %d' & %Hw & %Heqv & -> & (%vl & ↦ & Own) & Hw' & #Hwpt &
        Totyw)".
    inversion Heqv. subst vw.
    iDestruct "Own" as "[tyb_gho %tyb_phys]". iModIntro. iFrame "W".
    twp_bind pr. iApply (twp_hasty with "pr"). iIntros (vr dr ?) "tyr".
    iApply fupdw_tgl_wpw_nonval; [done|]. iIntros "W".
    iMod (Rd with "LFT E t2 tyr W") as
      "(W & %l0 & %vlb_concrete & %vlb & %Hr & %Heqv2 & %Hleneq & Hr' &
        #Hrpt' & Retether & _ & Own' & Totyr')".
    inversion Heqv2. subst vr.
    iDestruct "Own'" as "[tyb'_gho %tyb'_phys]".
    assert (length vl = ty_size tyb) as Sz.
    { rewrite <- tyb_phys. apply ty_size_eq. }
    assert (length vlb = ty_size tyb') as Sz'.
    { rewrite <- tyb'_phys. apply ty_size_eq. }
    iMod (mapsto_vec_untether _ _ ⊤ ∅ with "↦")
      as (vl_concrete) "[↦ [%Hvlen _]]".
    iModIntro. iFrame "W".
    iApply (twp_memcpy_guarded _ l l0 vl_concrete vlb_concrete
      Hw Hr with "[↦ Hw' Hr']").
    { congruence. } { congruence. }
    { iFrame "↦ Hw' Hr'". iFrame "Hwpt Hrpt'". }
    iIntros "(↦ & Hw' & Hr') W".
    destruct l as [l₁ c₁].
    iDestruct (wsat_split (W':=Wguard) with "W") as "[Wg Wr]".
    iDestruct (guard_acc with "Hwpt Hw' Wg") as "[prefix back]".
    iMod (fupd_mask_mono ∅ ⊤ with "(Retether [$prefix $↦])") as "[prefix ↦]";
      [set_solver|].
    iDestruct ("back" with "prefix") as "[Wg Hw']".
    iDestruct (wsat_join (W:=verus_halt_wsat) with "Wg Wr") as "W".
    iMod ("Totyw" $! (gtr xr) dr with "[↦ tyb'_gho] Hw' W")
      as "(W & %z & tok1 & %Hz & tyw')".
    { iExists vlb. iFrame "↦". iSplitL.
      { iDestruct (ty_gho_depth_mono with "tyb'_gho") as "$".
        { lia. } { lia. } }
      done. }
    iMod ("Totyr'" with "Hr' W") as "(W & %zr & %Hzr & tok2 & tyr')".
    iDestruct (Ltok_split_2 with "tok1 tok2") as "tok".
    iMod (Ltok_withdraw with "tok W") as "[W L]". iModIntro. iFrame "W".
    iExists -[_; _]. iFrame "L I". iSplit; [rewrite right_id|].
    - iSplitL "tyw'"; (rewrite tctx_hasty_val'; [|done]).
      + iExists (S (d' `max` dr)). iDestruct "tyw'" as "[gho phys]". iFrame.
        iDestruct (ty_gho_depth_mono with "gho") as "$". { lia. } { lia. }
      + iExists dr. iFrame "tyr'".
    - iPureIntro. by apply Obs.
  Qed.

  Lemma type_memcpy {𝔄 𝔄' 𝔅 𝔅' ℭ ℭ' 𝔄l 𝔅l 𝔇} (tyw: type 𝔄) (tyw': type 𝔄')
      (tyr: type 𝔅) (tyr': type 𝔅') (tyb: type ℭ) (tyb': type ℭ') gtw stw gtr
      str (n: Z) pw pr E L (I: invctx) (C: cctx 𝔇) (T: tctx 𝔄l)
      (T': tctx 𝔅l) e trx tr :
    Closed [] e → tctx_extract_ctx E L +[pw ◁ tyw; pr ◁ tyr] T T' trx →
    typed_write E L tyw tyb tyw' tyb' gtw stw →
    typed_read E L tyr tyb' tyr' gtr str → n = tyb'.(ty_size) →
    typed_body E L I C (pw ◁ tyw' +:: pr ◁ tyr' +:: T') e tr -∗
    typed_body E L I C T (pw <-{n} !pr;; e)
      (trx ∘ (λ post '(a -:: b -:: bl), λ mask,
        ∀ zw zr, stw a (gtr b) zw → str b zr →
          tr post (zw -:: zr -:: bl) mask))%type.
  Proof.
    iIntros (? Extr ???) "?".
    iApply type_seq; [by eapply type_memcpy_instr|done| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case=> [?[??]].
  Qed.
End typing.

Ltac via_tr_impl :=
  iStartProof;
  match goal with |- envs_entails _ (typed_body _ _ _ ?C ?T _ _) =>
    let TypeT := type of T in let TypeC := type of C in
    match eval hnf in (TypeT, TypeC) with (hlist _ ?𝔄l, list (_ ?𝔅)) =>
      iApply (typed_body_impl (𝔄l:=𝔄l) (𝔅:=𝔅)); last first
    end
  end.

Ltac via_tr_impl_with tr :=
  iStartProof;
  match goal with |- envs_entails _ (typed_body _ _ ?C ?T _ _) =>
    let TypeT := type of T in let TypeC := type of C in
    match eval hnf in (TypeT, TypeC) with (hlist _ ?𝔄l, list (_ ?𝔅)) =>
      evar (tr: predl_trans' 𝔄l 𝔅);
      iApply (typed_body_impl (𝔄l:=𝔄l) (𝔅:=𝔅) tr); last first
    end
  end.

Ltac intro_subst := iIntros (?); simpl_subst.
Ltac intro_subst_as x := iIntros (x); simpl_subst.

Global Hint Opaque typed_instr typed_write typed_read : lrust_typing.
