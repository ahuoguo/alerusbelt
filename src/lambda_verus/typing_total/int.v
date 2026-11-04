(** * The integer type

  Ported from VerusBelt ([typing/int.v], MIT, Hance, Elbeheiry, Matsushita,
  Dreyer). *)

From lrust.typing_total Require Export type ctx.
(** [ctx_wp], for the [lrustTotGS] instance: this file states weakest
  preconditions.  See the head of [typing_total/ctx_wp.v]. *)
From lrust.typing_total Require Import ctx_wp.
From lrust.typing_total Require Import bool programs.
From nola.bi Require Import guard modw.
Import GuardNotation ModwNotation TglWpwNotation.
(** Our [util] last, so that its [SemiIso] wins the name over Nola's; see
  [typing_total/type.v]. *)
From lrust.util Require Import basic.
Unset Default Proof Using.
(** [iris.prelude.options] sets [Default Goal Selector "!"], which rejects a
  bare tactic while more than one goal is focused.  It reaches this file
  through our imports and not through Nola's, so Nola's proofs - written
  against the default [1], "act on the first goal" - would otherwise need a
  focus fix every few lemmas.  Restoring [1] is a lint setting, not a
  soundness one. *)
Set Default Goal Selector "1".
Unset Suggest Proof Using.
Open Scope Z_scope.

Open Scope Z_scope.

Section int.
  Context `{!typeG FML Σ}.

  Program Definition int: type Zₛ :=
    {| pt_size := 1; pt_lev := 0;
       pt_ghox (z: ~~Zₛ) _ := empty_fml;
       pt_phys (z: ~~Zₛ) _ := [ FVal #z ];
    |}.
  Next Obligation. move=> sem H *. rewrite (empty_sem_at H). exact _. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  
  Lemma int_gho z d g tid : ty_gho int z d g tid ⊣⊢ True.
  Proof. apply empty_fml_sem. Qed.
  Lemma int_gho_pers z d g tid : ty_gho_pers int z d g tid ⊣⊢ True.
  Proof. apply empty_fml_sem. Qed.

  Global Instance int_copy: Copy int.
  Proof. split. - typeclasses eauto. - iIntros. iPureIntro. done. Qed.
  
  Lemma int_stack_okay : StackOkay int.
  Proof. done. Qed.
  
  (** Upstream ([typing/int.v]) states these two about [bool_ty], which
    [typing/bool.v] already has, so [int] is left without either.  Carried
    over as a fix rather than as written. *)
  Global Instance int_send: Send int.
  Proof.
    intros. split; trivial.
     - intros. unfold syn_abstract in H. subst x'. trivial.
     - iIntros (tid tid' x0 d g G κs) "_ _ lfts _ tok _ $ !>".
       iExists x0, 0%nat. iFrame "lfts tok".
       iSplit; [by iApply empty_fml_sem_2|done].
  Qed.

  Global Instance int_sync: Sync int.
  Proof. move=> *. split; [done|]. split; reflexivity. Qed.

  (** [int_resolve] removed along with [resolve]. *)
  
  Program Definition Z_of_boolₛ : boolₛ →ₛ Zₛ := {|
    syn_type_morphism_fn := Z_of_bool ;
    syn_type_morphism_proph_fn := Z_of_bool ;
  |}.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.

  Lemma bool_ty_to_int E L : subtype E L bool_ty int Z_of_boolₛ.
  Proof.
    apply subtype_plain_type. iIntros "*_!>_/=". iSplit; [done|].
    iSplit; [iApply dincl_refl|]. iSplit; [|done].
    iIntros (sem Hsem ??) "$". by iIntros "$".
  Qed.

  Lemma type_int_instr (z: Z) : typed_val #z int z.
  Proof.
    iIntros (????????) "_ _ _ $$ _ Obs".
    iApply tgl_wp_value. iExists -[z]. iFrame "Obs". iSplit; [|done].
    rewrite tctx_hasty_val'; [|done]. iExists 0%nat.
    iSplit; [by iApply empty_fml_sem_2|done].
  Qed.

  Lemma type_int {𝔄l 𝔅} (z: Z) (T: tctx 𝔄l) x e tr E L I (C: cctx 𝔅) :
    Closed (x :b: []) e →
    (∀v: val, typed_body E L I C (v ◁ int +:: T) (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := #z in e) (λ post al, tr post (z -:: al)).
  Proof. iIntros. iApply type_let; [apply type_int_instr|solve_typing|done..]. Qed.

  Lemma type_plus_instr E L I p1 p2 :
    typed_instr_ty E L I +[p1 ◁ int; p2 ◁ int] (p1 + p2) int
      (λ post '-[z; z'], post (z + z')).
  Proof.
    iIntros (????(z & z' &[])) "_ _ _ $$ (p1 & p2 &_) Obs".
    twp_apply (twp_hasty with "p1"). iIntros "%v %d _ [gho %phys]". inversion phys. subst v.
    twp_apply (twp_hasty with "p2"). iIntros "%v %d' _ [gho' %phys']". inversion phys'. subst v.
    twp_op. iExists -[(z + z')]. iFrame "Obs". rewrite right_id
    tctx_hasty_val'; [|done]. iExists d.
    iSplit; [by iApply empty_fml_sem_2|done].
  Qed.

  Lemma type_plus {𝔄l 𝔅l ℭ} p1 p2 x e trx tr E L I (C: cctx ℭ) (T: tctx 𝔄l) (T': tctx 𝔅l) :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p1 ◁ int; p2 ◁ int] T T' trx →
    (∀v: val, typed_body E L I C (v ◁ int +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := p1 + p2 in e)
      (trx ∘ (λ post '(z -:: z' -:: bl), tr post (z + z' -:: bl))).
  Proof.
    iIntros (? Extr) "?". iApply type_let; [by apply type_plus_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case=> [?[??]].
  Qed.

  Lemma type_minus_instr E L I p1 p2 :
    typed_instr_ty E L I +[p1 ◁ int; p2 ◁ int] (p1 - p2) int
      (λ post '-[z; z'], post (z - z')).
  Proof.
    iIntros (????(z & z' &[])) "_ _ _ $$ (p1 & p2 &_) Obs".
    twp_apply (twp_hasty with "p1"). iIntros "%v %d _ [gho %phys]". inversion phys. subst v.
    twp_apply (twp_hasty with "p2"). iIntros "%v %d' _ [gho' %phys']". inversion phys'. subst v.
    twp_op. iExists -[(z - z')]. iFrame "Obs". rewrite right_id
    tctx_hasty_val'; [|done]. iExists d.
    iSplit; [by iApply empty_fml_sem_2|done].
  Qed.

  Lemma type_minus {𝔄l 𝔅l ℭ} p1 p2 x e trx tr E L I (C: cctx ℭ) (T: tctx 𝔄l) (T': tctx 𝔅l) :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p1 ◁ int; p2 ◁ int] T T' trx →
    (∀v: val, typed_body E L I C (v ◁ int +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := p1 - p2 in e)
      (trx ∘ (λ post '(z -:: z' -:: bl), tr post (z - z' -:: bl))).
  Proof.
    iIntros (? Extr) "?". iApply type_let; [by apply type_minus_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case=> [?[??]].
  Qed.

  Lemma type_mult_instr E L I p1 p2 :
    typed_instr_ty E L I +[p1 ◁ int; p2 ◁ int] (p1 * p2) int
      (λ post '-[z; z'], post (z * z')).
  Proof.
    iIntros (????(z & z' &[])) "_ _ _ $$ (p1 & p2 &_) Obs".
    twp_apply (twp_hasty with "p1"). iIntros "%v %d _ [gho %phys]". inversion phys. subst v.
    twp_apply (twp_hasty with "p2"). iIntros "%v %d' _ [gho' %phys']". inversion phys'. subst v.
    twp_op. iExists -[(z * z')]. iFrame "Obs". rewrite right_id
    tctx_hasty_val'; [|done]. iExists d.
    iSplit; [by iApply empty_fml_sem_2|done].
  Qed.

  Lemma type_mult {𝔄l 𝔅l ℭ} p1 p2 x e trx tr E L I (C: cctx ℭ) (T: tctx 𝔄l) (T': tctx 𝔅l) :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p1 ◁ int; p2 ◁ int] T T' trx →
    (∀v: val, typed_body E L I C (v ◁ int +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := p1 * p2 in e)
      (trx ∘ (λ post '(z -:: z' -:: bl), tr post (z * z' -:: bl))).
  Proof.
    iIntros (? Extr) "?". iApply type_let; [by apply type_mult_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case=> [?[??]].
  Qed.

  Lemma type_le_instr E L I p1 p2 :
    typed_instr_ty E L I +[p1 ◁ int; p2 ◁ int] (p1 ≤ p2) bool_ty
      (λ post '-[z; z'], post (bool_decide (z ≤ z'))).
  Proof.
    iIntros (????(z & z' &[])) "_ _ _ $$ (p1 & p2 &_) Obs".
    twp_apply (twp_hasty with "p1"). iIntros "%v %d _ [gho %phys]". inversion phys. subst v.
    twp_apply (twp_hasty with "p2"). iIntros "%v %d' _ [gho' %phys']". inversion phys'. subst v.
    twp_op. iExists -[bool_decide (z ≤ z')]. iFrame "Obs". rewrite right_id
    tctx_hasty_val'; [|done]. iExists d.
    iSplit; [by iApply empty_fml_sem_2|done].
  Qed.

  Lemma type_le {𝔄l 𝔅l ℭ} p1 p2 x e trx tr E L I (C: cctx ℭ) (T: tctx 𝔄l) (T': tctx 𝔅l) :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p1 ◁ int; p2 ◁ int] T T' trx →
    (∀v: val, typed_body E L I C (v ◁ bool_ty +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := p1 ≤ p2 in e)
      (trx ∘ (λ post '(z -:: z' -:: bl), tr post (bool_decide (z ≤ z') -:: bl))).
  Proof.
    iIntros (? Extr) "?". iApply type_let; [by apply type_le_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case=> [?[??]].
  Qed.

  (** [type_nd_int_instr] / [type_nd_int] removed, as in [typing/int.v]:
      [NdInt] models unbounded non-deterministic integer choice, which is
      not a distribution over [Z] and so has no rule in a probabilistic
      weakest precondition (cf. [lang.v]).  The probabilistic replacement
      is [Rand], whose typing rule is this tree's own [typing/rand_ubig.v]
      and has no counterpart in Nola. *)

  Lemma type_int_eq_instr E L I p1 p2 :
    typed_instr_ty E L I +[p1 ◁ int; p2 ◁ int] (p1 = p2) bool_ty
      (λ post '-[z; z'], post (bool_decide (z = z'))).
  Proof.
    iIntros (????(z & z' &[])) "_ _ _ $$ (p1 & p2 &_) Obs".
    twp_apply (twp_hasty with "p1"). iIntros "%v %d _ [gho %phys]". inversion phys. subst v.
    twp_apply (twp_hasty with "p2"). iIntros "%v %d' _ [gho' %phys']". inversion phys'. subst v.
    twp_op. iExists -[bool_decide (z = z')]. iFrame "Obs". rewrite right_id
    tctx_hasty_val'; [|done]. iExists d.
    iSplit; [by iApply empty_fml_sem_2|done].
  Qed.

  Lemma type_int_eq {𝔄l 𝔅l ℭ} p1 p2 x e trx tr E L I (C: cctx ℭ) (T: tctx 𝔄l) (T': tctx 𝔅l) :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p1 ◁ int; p2 ◁ int] T T' trx →
    (∀v: val, typed_body E L I C (v ◁ bool_ty +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := p1 = p2 in e)
      (trx ∘ (λ post '(z -:: z' -:: bl), tr post (bool_decide (z = z') -:: bl))).
  Proof.
    iIntros (? Extr) "?". iApply type_let; [by apply type_int_eq_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case=> [?[??]].
  Qed.

End int.

Global Hint Rewrite @int_gho @int_gho_pers : fml_sem.

