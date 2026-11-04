(** * The Boolean type

  Ported from VerusBelt ([typing/bool.v], MIT, Hance, Elbeheiry, Matsushita,
  Dreyer). *)

From lrust.typing_total Require Export type ctx.
(** [ctx_wp], for the [lrustTotGS] instance: this file states weakest
  preconditions.  See the head of [typing_total/ctx_wp.v]. *)
From lrust.typing_total Require Import ctx_wp.
From lrust.typing_total Require Import programs.
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

Section bool.
  Context `{!typeG FML Σ}.

  Program Definition bool_ty: type boolₛ :=
    {|
      pt_size := 1;
      pt_lev := 0;
      pt_ghox (b: ~~boolₛ) _ := empty_fml ;
      pt_phys (b: ~~boolₛ) _ := [ FVal #b ] ;
    |}%I.
  Next Obligation. move=> sem H *. rewrite (empty_sem_at H). exact _. Qed.
  Next Obligation. move=> *. trivial. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. intros. done. Qed.
  
  Lemma bool_gho b d g tid : ty_gho bool_ty b d g tid ⊣⊢ True.
  Proof. apply empty_fml_sem. Qed.
  Lemma bool_gho_pers b d g tid : ty_gho_pers bool_ty b d g tid ⊣⊢ True.
  Proof. apply empty_fml_sem. Qed.

  Global Instance bool_copy: Copy bool_ty.
  Proof. split. - typeclasses eauto. - iIntros. iPureIntro. done. Qed.

  Global Instance bool_send: Send bool_ty.
  Proof.
    intros. split; trivial.
     - intros. unfold syn_abstract in H. subst x'. trivial.
     - iIntros (tid tid' x0 d g G κs) "_ _ lfts _ tok _ $ !>".
       iExists x0, 0%nat. iFrame "lfts tok".
       iSplit; [by iApply empty_fml_sem_2|done].
  Qed.
  
  Global Instance bool_sync: Sync bool_ty.
  Proof. move=> *. split; [done|]. split; reflexivity. Qed.

  (** [bool_resolve] removed along with [resolve]. *)
  
  Lemma bool_stack_okay : StackOkay bool_ty.
  Proof. done. Qed.

  Lemma type_bool_instr (b: bool) : typed_val #b bool_ty b.
  Proof.
    iIntros (????????) "_ _ _ $$ _ Obs".
    iApply tgl_wp_value. iExists -[b]. iFrame "Obs". iSplit; [|done].
    rewrite tctx_hasty_val'; [|done]. iExists 0%nat.
    iSplit; [by iApply empty_fml_sem_2|done].
  Qed.

  Lemma type_bool {𝔄l 𝔅} (b: bool) (T: tctx 𝔄l) x e tr E L (I: invctx) (C: cctx 𝔅) :
    Closed (x :b: []) e →
    (∀v: val, typed_body E L I C (v ◁ bool_ty +:: T) (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := #b in e) (λ post al, tr post (b -:: al)).
  Proof.
    iIntros. iApply type_let; [apply type_bool_instr|solve_typing|done..].
  Qed.

  (** [type_nd_bool_instr] / [type_nd_bool] removed, as in
      [typing/bool.v]: [NdBool] desugars to [#0 ≤ NdInt], so it inherits
      [NdInt]'s lack of a probabilistic WP rule (cf. [int.v]). *)

  Lemma type_if {𝔄l 𝔅l ℭ} p (T: tctx 𝔄l) (T': tctx 𝔅l) e1 e2 tr1 tr2 trx E L I (C: cctx ℭ) :
    tctx_extract_ctx E L +[p ◁ bool_ty] T T' trx →
    typed_body E L I C T' e1 tr1 -∗ typed_body E L I C T' e2 tr2 -∗
    typed_body E L I C T (if: p then e1 else e2)
      (trx ∘ (λ post '(b -:: vl), if b then tr1 post vl else tr2 post vl)).
  Proof.
    iIntros (?) "e1 e2". iApply typed_body_tctx_incl; [done|]=>/=.
    iIntros (?[b ?]???) "/= #LFT #UNIQ #E L I C [p T] %Obs".
    twp_bind p. iApply (twp_hasty with "p"). iIntros (?? _).
    iDestruct 1 as "[_true %Hphys]".
    inversion Hphys. subst v.
    destruct b; twp_case.
    - by iApply ("e1" with "LFT UNIQ E L I C T").
    - by iApply ("e2" with "LFT UNIQ E L I C T").
  Qed.
End bool.

Global Hint Rewrite @bool_gho @bool_gho_pers : fml_sem.

