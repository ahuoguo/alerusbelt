(** * Error credits as a type

  The typing-layer counterpart of eris's [↯ ε], so that a credit can sit
  in a typing context like any other resource.  This tree's partial
  [typing/rand_ubig.v] does the same thing, and the shape here is its
  shape:

      ↯_T ε  =  own_ptr 0 (tracked_ty (error_credit_core ε))

  with [tracked_ty] the ghost wrapper ([typing_total/tracked.v]) and the
  owning pointer supplying the path witness that [tctx_elt_interp]
  demands - a zero-sized type cannot live at a path on its own.

  Two things are *more* grounded here than in the partial tree, and both
  for structural reasons rather than taste.

  The payload is a formula.  [ty_ghox] is a [cif], not an [iProp], so
  the credit cannot simply be written in; it is [typing_total/model.v]'s
  [cif_ec], a constructor whose selector is the amount and which has no
  children.  That is what lets [↯_T ε] be stored in a borrow, an
  invariant or the store, which an [iProp] payload never could.

  The handle is the real owning pointer.  [typing/rand_ubig.v] had to
  define a bespoke [own_ptr_0], because [typing/own.v]'s [own_ptr] wraps
  the pointee's ghost component in [▷] and an error credit must not be
  behind a later.  [typing_total/own.v]'s has no [▷] - only the depth
  guard [[Sx(d') := d]] - so [own_ptr 0] is usable as it stands. *)
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

  (** What the type holds, unfolded.  The owning pointer contributes a
    points-to over the empty list and a [freeable_sz] at size zero, both
    of which are trivial, so the content is the credit and the depth
    guard. *)
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

  This tree's [typing/rand_ubig.v]'s [type_rand_case], at [tgl_wpw]: the
  [let] binding a [rand] splits into one goal per outcome, the credit
  entry is replaced by the outcome's refund, and the sampled integer is
  pushed onto the context.  The [Closed] premise is the one the partial
  tree takes too - [lrust_prob_lang]'s [RecV] carries a [Closed] side
  condition, so without it the [let]'s lambda is not a value to
  [reshape_expr] and [twp_bind] cannot reach the [rand]. *)
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
