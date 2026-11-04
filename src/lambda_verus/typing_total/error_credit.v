(** * Error credits as a type

  The typing-layer counterpart of [↯ ε], so a credit can sit in a typing
  context.  [typing/rand_ubig.v] has the same shape:

      ↯_T ε  =  own_ptr 0 (tracked_ty (error_credit_core ε))

  Two differences, both structural.  The payload is a formula, since
  [ty_ghox] is a [cif] and not an [iProp] - which is also what lets a
  credit be stored in a borrow or an invariant.  And the handle is the
  real [own_ptr]: [typing/rand_ubig.v] needed a bespoke [own_ptr_0]
  because [typing/own.v]'s puts the pointee's ghost component behind a
  [▷], and [typing_total/own.v]'s does not. *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From lrust.typing_total Require Export inst.
From lrust.typing_total Require Import type own tracked model type_context
  programs int ctx_wp.
From lrust.lang Require Import notation total_proofmode total_lifting_heap.
From clutch.prob Require Import distribution.
From nola.bi Require Import modw.
Import ModwNotation TglWpwNotation.
Import iPropAppNotation CsemNotation.
From lrust.util Require Import basic.
Unset Default Proof Using.
Set Default Goal Selector "1".
Unset Suggest Proof Using.

Local Open Scope R.

Section error_credit.
  Context {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ}.

  (** [cif_ec]'s semantics, at a candidate and at [bor_sem]. *)
  Lemma cif_ec_sem {δ ε} :
    ⟦ cif_ec ε : cif verus_haltCON Σ ⟧ᶜ(δ) ⊣⊢ ↯ ε.
  Proof. by rewrite /cif_ec sem_cif_in. Qed.

  Lemma ec_fml_sem ε : bor_sem (cif_ec ε : cif verus_haltCON Σ) ⊣⊢ ↯ ε.
  Proof. rewrite /bor_sem /= cif_ec_sem //. Qed.

  (** The ghost-only credit: no memory, no lifetime, a formula payload. *)
  Program Definition error_credit_core (ε : R) : type unitₛ := {|
    ty_size := 0;
    ty_lev := 0;
    ty_lfts := [];
    ty_E := [];
    ty_ghox x d g tid := cif_ec ε;
    ty_gho_persx x d g tid := empty_fml;
    ty_phys x tid := [];
  |}.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. move=> ε sem Hsm *. by iIntros "$". Qed.
  Next Obligation. move=> ε sem Hsm *. by iIntros "$". Qed.
  Next Obligation.
    move=> ε sem Hsm *. rewrite (empty_sem_at Hsm). exact _.
  Qed.
  Next Obligation. move=> *. iIntros "_". by iApply empty_fml_sem_2. Qed.

  Definition error_credit_ty (ε : R) : type (at_locₛ (trackedₛ unitₛ)) :=
    own_ptr 0 (tracked_ty (error_credit_core ε)).

  (** The owning pointer's points-to and [freeable_sz] are both trivial
    at size zero, so what is left is the credit and the depth guard. *)
  Lemma error_credit_ty_gho ε x d g tid :
    ty_gho (error_credit_ty ε) x d g tid ⊣⊢
      [S(d') := d] (x.1 ↦!∗ [] ∗ freeable_sz 0 0 x.1 ∗ ↯ ε).
  Proof.
    rewrite /error_credit_ty own_ptr_gho. destruct d as [|d']=>//=.
    by rewrite /ty_gho /= cif_ec_sem.
  Qed.

  Lemma error_credit_ty_gho_S ε l u d' g tid :
    ty_gho (error_credit_ty ε) (l, u) (S d') g tid ⊣⊢ ↯ ε.
  Proof.
    rewrite error_credit_ty_gho /= heap_mapsto_fancy_vec_nil.
    iSplit; [by iIntros "(_ & _ & $)"|by iIntros "$"].
  Qed.
End error_credit.

(** As in the partial tree: [↯_T ε] is the typing layer's [↯ ε]. *)
Notation "'↯_T' ε" := (error_credit_ty ε)
  (at level 8, format "↯_T  ε") : lrust_type_scope.

(** ** Sampling, with the credit in the typing context

  [typing/rand_ubig.v]'s [type_rand_case] at [tgl_wpw].  The [Closed]
  premise is the one the partial tree takes too: [RecV] carries a
  [Closed] side condition, so without it [twp_bind] cannot see the
  [let]'s lambda as a value and never reaches the [rand]. *)
Section rand_case.
  Context {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ}.

  Lemma type_rand_case {𝔄l 𝔅} (z : Z) (ε1 : R) (ε2 : nat → R) (c : path) x e
      (T' : tctx 𝔄l) E L (I : invctx) (C : cctx 𝔅) :
    (0 < z)%Z →
    (∀ n, 0 <= ε2 n <= 1) →
    SeriesC (λ n : nat, if bool_decide (n < Z.to_nat z)%nat
                        then (1 / Z.to_nat z) * ε2 n else 0) <= ε1 →
    Closed (x :b: []) e →
    (∀ n : nat, (n < Z.to_nat z)%nat →
      ⊢ typed_body E L I C
          (#(Z.of_nat n) ◁ int +:: c ◁ error_credit_ty (ε2 n) +:: T')
          (subst' x #(Z.of_nat n) e) (λ _ _ _, True%type)) →
    ⊢ typed_body E L I C (c ◁ error_credit_ty ε1 +:: T')
        (let: x := rand #z in e) (λ _ _ _, True%type).
  Proof.
    iIntros (Hz Hb Hm Hcl Hbody).
    rewrite /typed_body /typed_body_at.
    iIntros (tid xl mask post iκs).
    destruct xl as [[lc u] cl].
    iIntros "#LFT #UNIQ #Eq Lq Iq Cq [Hcred Hrest] _".
    iDestruct "Hcred" as (v dv Hev) "[Hgho %Hphys]".
    destruct dv as [|dv'].
    { rewrite /ty_own error_credit_ty_gho /=. by iDestruct "Hgho" as "[]". }
    rewrite error_credit_ty_gho_S.
    twp_bind (rand _)%E.
    iApply (twpw_rand_exp_nat _ z ε1 ε2 _ _ Hz Hb Hm with "[Hgho]");
      [iExact "Hgho"|].
    iIntros (m) "[%Hm2 Hcr]". twp_let.
    iApply ((Hbody m Hm2) $! tid (Z.of_nat m -:: (lc, u) -:: cl) mask post iκs
      with "LFT UNIQ Eq Lq Iq Cq [Hcr Hrest]").
    - iSplitR "Hcr Hrest".
      { iExists #(Z.of_nat m), 0%nat. iSplit; [done|].
        rewrite /ty_own. iSplit; [done|done]. }
      iSplitL "Hcr".
      { iExists v, 1%nat. iSplit; [done|].
        rewrite /ty_own error_credit_ty_gho_S. by iFrame. }
      iFrame "Hrest".
    - done.
  Qed.
End rand_case.

(** [↯ 1] is false, so a branch holding one needs no typing at all.
  This is what pays for a sampler's stuck outcome.  The shape is the one
  [type_rand_case] leaves behind, as in [typing/rand_ubig.v]: the
  sampled integer first, the refund second. *)
Section contradict.
  Context {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ}.

  Lemma type_credit_contradict_after_rand {𝔄l 𝔅} (T' : tctx 𝔄l) E L
      (I : invctx) (C : cctx 𝔅) (z : Z) (p : path) (ε : R) e tr :
    1 <= ε →
    ⊢ typed_body E L I C (#z ◁ int +:: p ◁ error_credit_ty ε +:: T') e tr.
  Proof.
    iIntros (Hε). rewrite /typed_body /typed_body_at.
    iIntros (tid xl mask post iκs). destruct xl as [zv [[lc u] cl]].
    iIntros "_ _ _ _ _ _ [_ [Hcred _]] _".
    iDestruct "Hcred" as (v dv Hev) "[Hgho _]".
    destruct dv as [|dv'].
    { rewrite /ty_own error_credit_ty_gho /=. by iDestruct "Hgho" as "[]". }
    rewrite error_credit_ty_gho_S.
    iExFalso. iApply (ec_contradict with "Hgho"). lra.
  Qed.
End contradict.

(** [typing_total/soundness.v] hands over an ambient [↯ ε]; a derivation
  against [type_rand_case] wants it at a path.  The location is an
  artifact of [tctx_elt_interp], which asks every entry for a value
  witness, so any location does - nothing dereferences it. *)
Section intro.
  Context {Σ} `{!verus_haltGS (cifOF verus_haltCON) Σ}.

  Lemma typed_body_ec_intro {𝔅} E L (I : invctx) (C : cctx 𝔅) e (ε : R)
      (l : loc) :
    (⊢ typed_body E L I C +[#l ◁ error_credit_ty ε] e (λ _ _ _, True%type)) →
    ↯ ε -∗ typed_body E L I C (+[] : tctx []) e (λ _ _ _, True%type).
  Proof.
    move=> big. iIntros "Hε". rewrite /typed_body /typed_body_at.
    iIntros (tid xl mask post iκs) "LFT UNIQ Eq Lq Iq Cq _ _".
    iApply (big $! tid ((l, ()) -:: -[]) mask post iκs
      with "LFT UNIQ Eq Lq Iq Cq [Hε]"); [|done].
    iSplitL; [|done]. iExists #l, 1%nat. iSplit; [done|].
    rewrite /ty_own error_credit_ty_gho_S. by iFrame.
  Qed.
End intro.
