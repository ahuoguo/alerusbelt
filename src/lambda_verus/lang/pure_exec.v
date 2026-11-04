(** Pure reduction for [lrust_prob_lang].

    Factored out of [lifting.v]: [PureExec], [AsRec], [AsVal] and
    [DoSubstL] are statements about the operational semantics alone, so
    the partial and total program logics share them, and neither has to
    import the other's heap.  Moved here verbatim. *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From clutch.common Require Import language ectx_language.
From clutch.prob Require Import distribution.
From lrust.lang Require Export lang.
Set Default Proof Using "Type".

Open Scope Z_scope.
Open Scope R.

(** Tactic mirroring [clutch.prob_lang.class_instances.solve_pure_exec]:
    use [case_match] + [simplify_eq] to destructure the [match]
    expressions inside [head_step_prob], then close with [dret_1_1]. *)
Local Ltac solve_exec_puredet :=
  intros σ; simpl; (repeat case_match); simplify_eq;
  rewrite dret_1_1 //.

Local Ltac solve_exec_safe :=
  intros σ; eexists (_, σ); simpl;
  (repeat case_match); simplify_eq;
  rewrite dret_1_1 //; lra.

Local Ltac solve_pure_exec :=
  intros _; apply nsteps_once;
  apply pure_head_step_pure_step;
  constructor; [solve_exec_safe | solve_exec_puredet].

(** Beta reduction: [App (Rec f xl e) (of_val <$> vs) → e[f, xl ↦ ...]]. *)
Class AsRec (e : expr) (f : binder) (xl : list binder) (erec : expr) :=
  as_rec : e = Rec f xl erec.
Global Instance AsRec_rec f xl e : AsRec (Rec f xl e) f xl e := eq_refl.
Global Instance AsRec_rec_val f xl e `{!Closed (f :b: xl +b+ []) e} :
  AsRec (of_val (RecV f xl e)) f xl e := eq_refl.
Global Instance AsRec_rec_locked_val v f xl e :
  AsRec (of_val v) f xl e → AsRec (of_val (locked v)) f xl e.
Proof. by unlock. Qed.

(** [AsVal e] says [e] is the [of_val] of some value - used in [pure_rec]
    to assert all argument expressions are values. *)
Class AsVal (e : expr) := as_val : ∃ v, of_val v = e.
Global Instance AsVal_lit l : AsVal (Lit l).
Proof. by exists (LitV l). Qed.
Global Instance AsVal_of_val v : AsVal (of_val v).
Proof. by exists v. Qed.

Class DoSubstL (xl : list binder) (esl : list expr) (e er : expr) :=
  do_subst_l : subst_l xl esl e = Some er.
Global Hint Extern 0 (DoSubstL [] [] _ _) => exact eq_refl : typeclass_instances.
Global Hint Extern 1 (DoSubstL (_ :: _) (_ :: _) _ _) =>
  rewrite /DoSubstL; cbn; reflexivity : typeclass_instances.

(** Recursive [DoSubstL] step.  Lets typeclass resolution peel a single
    [(b, e)] off the front and recurse on the remaining tail -
    crucially, the tail need not be syntactic [_ :: _], so this works
    when the tail is a [plistc binder _] / [map of_val plistc] that
    only reduces via a separate base-case instance (e.g.
    [function.do_subst_plv]). *)
Global Instance do_subst_l_cons_step (b : binder) (e : expr)
    (bl : list binder) (esl : list expr) (body result : expr) :
  DoSubstL bl esl body result →
  DoSubstL (b :: bl) (e :: esl) body (subst' b e result) | 5.
Proof. rewrite /DoSubstL /= => ->. done. Qed.

(** Companion typeclass instances for [pure_rec] resolution on
    applications of the form [(rec: f xl := e)%V (map of_val vsl)]
    where [vsl] is a *symbolic* [vec val (length xl)] (typical of
    continuation bodies in [typing/cont.v]).

    Upstream verusbelt (iris-WP) got these "for free" via
    [iris.program_logic.{language,lifting}]: the iris-side
    [Class AsVal] has [Global Instance as_vals_of_val :
    TCForall AsVal (of_val <$> vs)] (language.v:271), and iris's
    [lifting.v] provides [DoSubstL xl (of_val <$> vec_to_list vsl)
    e (subst_v xl vsl e)] as a global instance.  When ported to pgl_wp,
    we re-defined [AsVal] [DoSubstL] locally above without those companions.

    Without these instances, [wp_rec] / [wp_pure (App _ _)] fires
    [pure_rec] which then can't resolve [TCForall AsVal (map of_val
    vsl)] (Coq's typeclass search doesn't unfold [map] for symbolic
    [vsl]) and can't resolve [DoSubstL] (the default [Hint Extern]
    runs [cbn; reflexivity] which can't reduce [subst_l] on a
    symbolic vec).  The two instances + the [Closed]-by-assumption
    hint below close all three holes. *)
Global Instance TCForall_AsVal_map_of_val (vl : list val) :
  TCForall AsVal (map of_val vl).
Proof. induction vl as [|v vl IH]; constructor; [exact _|exact IH]. Qed.

Global Instance TCForall_AsVal_vec_of_val {n} (vl : vec val n) :
  TCForall AsVal (map of_val (vec_to_list vl)).
Proof. apply TCForall_AsVal_map_of_val. Qed.

Global Instance do_subst_l_rec_vec (kb : binder) (bl : list binder)
    (k : val) (vsl : vec val (length bl)) e :
  DoSubstL (kb :: bl) (of_val k :: map of_val (vec_to_list vsl)) e
           (subst' kb (of_val k) (subst_v bl vsl e)).
Proof.
  rewrite /DoSubstL /=.
  pose proof (subst_v_eq bl vsl e) as Heq.
  unfold subst_v in *. rewrite -Heq /=. done.
Qed.

(** Let typeclass search use [Closed] *hypotheses* from the proof
    context.  [pure_rec] has a [Closed (f :b: xl +b+ []) erec]
    premise; for a *symbolic* [erec] (typical of continuation
    bodies) the default [solve_closed] tactic can't fire, but the
    Coq-level [Closed] hypothesis bound at the lemma statement is
    available to [assumption]. *)
Global Hint Extern 1 (Closed _ _) => assumption : typeclass_instances.

Global Instance pure_rec e f xl erec erec' el :
  AsRec e f xl erec →
  TCForall AsVal el →
  Closed (f :b: xl +b+ []) erec →
  DoSubstL (f :: xl) (e :: el) erec erec' →
  PureExec True 1 (App e el) erec'.
Proof.
  rewrite /AsRec /DoSubstL=> -> /TCForall_Forall Hel ? Hsubst.
  assert (Hguard : Forall (λ ei, is_Some (to_val ei)) el ∧
                   Closed (f :b: xl +b+ []) erec).
  { split; [|done]. eapply Forall_impl; [exact Hel|].
    intros e' [v <-]. eexists. apply to_of_val. }
  intros _. apply nsteps_once. apply pure_head_step_pure_step.
  assert (Hgoal : ∀ σ,
    head_step_prob (App (Rec f xl erec) el) σ = dret (erec', σ)).
  { intros σ. rewrite /head_step_prob.
    rewrite (bool_decide_eq_true_2 _ Hguard). by rewrite Hsubst. }
  constructor.
  - intros σ. eexists (erec', σ).
    change (head_step_prob (App (Rec f xl erec) el) σ (erec', σ) > 0).
    rewrite Hgoal. rewrite dret_1_1 //. lra.
  - intros σ.
    change (head_step_prob (App (Rec f xl erec) el) σ (erec', σ) = 1).
    rewrite Hgoal. apply dret_1_1; reflexivity.
Qed.

Global Instance pure_le n1 n2 :
  PureExec True 1 (BinOp LeOp (Lit (LitInt n1)) (Lit (LitInt n2)))
                  (Lit (lit_of_bool (bool_decide (n1 ≤ n2)%Z))).
Proof.
  intros _. apply nsteps_once. apply pure_head_step_pure_step.
  constructor.
  - intros σ. eexists (_, σ). simpl. (repeat case_match); simplify_eq.
    rewrite dret_1_1 //. lra.
  - intros σ. simpl. (repeat case_match); simplify_eq.
    rewrite dret_1_1 //.
Qed.

Global Instance pure_eq_int z1 z2 :
  PureExec True 1 (BinOp EqOp (Lit (LitInt z1)) (Lit (LitInt z2)))
                  (Lit (lit_of_bool (bool_decide (z1 = z2)%Z))).
Proof.
  intros _. apply nsteps_once. apply pure_head_step_pure_step.
  constructor.
  - intros σ. eexists (_, σ). simpl.
    destruct z1; cbn -[bool_decide]; by rewrite dret_1_1; first lra.
  - intros σ. simpl.
    destruct z1; cbn -[bool_decide]; by rewrite dret_1_1.
Qed.

(** Pointer equality.  [bin_op_eval_fn] decides it with [lit_eq_dec],
    which never consults the heap, so unlike lambda-rust's relational
    [lit_eq] - where comparing a dangling pointer is non-deterministic -
    this is a pure step.  That is what lets [total_lifting_heap.v]'s
    [twp_eq_loc] drop the two points-to hypotheses and the world
    satisfaction that the relational version needs. *)
Global Instance pure_eq_loc (l1 l2 : loc) :
  PureExec True 1 (BinOp EqOp (Lit (LitLoc l1)) (Lit (LitLoc l2)))
                  (Lit (lit_of_bool (bool_decide (l1 = l2)))).
Proof. solve_pure_exec. Qed.

Global Instance pure_plus z1 z2 :
  PureExec True 1 (BinOp PlusOp (Lit (LitInt z1)) (Lit (LitInt z2)))
                  (Lit (LitInt (z1 + z2)%Z)).
Proof. solve_pure_exec. Qed.

Global Instance pure_minus z1 z2 :
  PureExec True 1 (BinOp MinusOp (Lit (LitInt z1)) (Lit (LitInt z2)))
                  (Lit (LitInt (z1 - z2)%Z)).
Proof. solve_pure_exec. Qed.

Global Instance pure_mult z1 z2 :
  PureExec True 1 (BinOp MultOp (Lit (LitInt z1)) (Lit (LitInt z2)))
                  (Lit (LitInt (z1 * z2)%Z)).
Proof. solve_pure_exec. Qed.

Global Instance pure_offset l z :
  PureExec True 1 (BinOp OffsetOp (Lit (LitLoc l)) (Lit (LitInt z)))
                  (Lit (LitLoc (shift_loc l z))).
Proof. solve_pure_exec. Qed.

Global Instance pure_case (i : Z) e el :
  PureExec ((0 ≤ i)%Z ∧ el !! Z.to_nat i = Some e) 1
           (Case (Lit (LitInt i)) el) e | 10.
Proof.
  intros [Hi Heq]. apply nsteps_once. apply pure_head_step_pure_step.
  constructor.
  - intros σ. eexists (e, σ). simpl.
    rewrite (bool_decide_true _ Hi) Heq. rewrite dret_1_1 //. lra.
  - intros σ. simpl. rewrite (bool_decide_true _ Hi) Heq.
    apply dret_1_1; reflexivity.
Qed.

Global Instance pure_if (b : bool) e1 e2 :
  PureExec True 1 (If (Lit (lit_of_bool b)) e1 e2) (if b then e1 else e2) | 1.
Proof.
  intros _. destruct b; (apply nsteps_once; apply pure_head_step_pure_step;
    constructor; [intros σ; eexists (_, σ); simpl; rewrite dret_1_1 //; lra
                  |intros σ; simpl; apply dret_1_1; reflexivity]).
Qed.
