(** Proofmode wiring for [lrust_prob_lang]'s total weakest precondition.

    The [twp] counterpart of [lang/proofmode.v].  Every tactic here is its
    partial sibling with the laters removed: no [MaybeIntoLaterNEnvs]
    premise, no [iNext], and [twp_pure_step_fupd] in place of
    [wp_pure_step_later].  Surface tactics are named [twp_*] so both
    logics can be used in the same file.

    The guarded heap tactics have no counterpart; see [total_lifting.v]. *)
From iris.proofmode Require Import proofmode reduction environments coq_tactics.
From iris.proofmode Require Export proofmode.
From clutch.eris Require Export total_weakestpre.
From clutch.eris Require Import total_lifting.
(** [pure_exec], not [lifting]: the partial stack's [lrustGS],
    [lrustGS_invGS_inst : invGS Σ] and [lrustGS_erisWpGS] would otherwise
    stay in scope all the way up the total typing layer, where they make
    typeclass search for the semantic interfaces of [typing_total/ctx.v]
    diverge - [typing_total/inv_context.v]'s [Context] line goes from one
    second to over two minutes with them. *)
From lrust.lang Require Export tactics pure_exec.
Set Default Proof Using "Type".
Import uPred.

(** The pure, value and bind tactics are stated over an arbitrary
    [erisWpGS] instance, so that they apply to [tgl_wpw W] (the
    world-satisfaction weakest precondition of [total_wsat.v]) as well as
    to the canonical one.  Only the heap tactics below need [lrustGS]. *)
Lemma tac_twp_value `{!erisWpGS lrust_prob_lang Σ} Δ s E Φ e v :
  IntoVal e v →
  envs_entails Δ (Φ v) → envs_entails Δ (WP e @ s; E [{ Φ }]).
Proof. rewrite envs_entails_unseal=> ? ->. by apply tgl_wp_value. Qed.

Ltac twp_value_head := eapply tac_twp_value; [tc_solve|reduction.pm_prettify].

Lemma tac_twp_pure `{!erisWpGS lrust_prob_lang Σ} K Δ s E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  envs_entails Δ (WP fill K e2 @ s; E [{ Φ }]) →
  envs_entails Δ (WP fill K e1 @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_unseal=> HPE Hφ HΔ. rewrite HΔ.
  apply: twp_pure_step_fupd; [|exact Hφ]. by apply (pure_exec_ctx (fill K)).
Qed.

Tactic Notation "twp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (twp ?s ?E ?e ?Q) => reshape_expr e ltac:(fun K e' =>
    unify e' efoc;
    eapply (tac_twp_pure K);
    [simpl; tc_solve                 (* PureExec *)
    |try done                        (* the pure condition *)
    |simpl_subst; try twp_value_head (* new goal *)])
   || fail "twp_pure: cannot find" efoc "in" e "or" efoc "is not a reduct"
  | _ => fail "twp_pure: not a 'twp'"
  end.

Tactic Notation "twp_rec" := twp_pure (App _ _).
Tactic Notation "twp_lam" := twp_rec.
Tactic Notation "twp_let" := twp_lam.
Tactic Notation "twp_seq" := twp_let.
Tactic Notation "twp_op" := twp_pure (BinOp _ _ _).
Tactic Notation "twp_if" := twp_pure (If _ _ _).
Tactic Notation "twp_case" := twp_pure (Case _ _); try twp_value_head.

Lemma tac_twp_bind `{!erisWpGS lrust_prob_lang Σ} K Δ s E Φ e :
  envs_entails Δ (WP e @ s; E [{ v, WP fill K (of_val v) @ s; E [{ Φ }] }])%I →
  envs_entails Δ (WP fill K e @ s; E [{ Φ }]).
Proof. rewrite envs_entails_unseal=> ->. apply: tgl_wp_bind. Qed.

Ltac twp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => apply (tac_twp_bind K); simpl
  end.

Tactic Notation "twp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (twp ?s ?E ?e ?Q) => reshape_expr e ltac:(fun K e' =>
    match e' with
    | efoc => unify e' efoc; twp_bind_core K
    end) || fail "twp_bind: cannot find" efoc "in" e
  | _ => fail "twp_bind: not a 'twp'"
  end.

Tactic Notation "twp_apply" open_constr(lem) :=
  iPoseProofCore lem as false (fun H =>
    lazymatch goal with
    | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
      reshape_expr e ltac:(fun K e' =>
        twp_bind_core K; iApplyHyp H; simpl) ||
      lazymatch iTypeOf H with
      | Some (_,?P) => fail "twp_apply: cannot apply" P
      end
    | _ => fail "twp_apply: not a 'twp'"
    end).

(** The heap-side tactics are deliberately absent.  They would have to
    pick one of the two heaps - [lang/heap.v]'s, used by [total_lifting.v],
    or [lang/total_heap.v]'s, used by [total_lifting_heap.v] - and
    importing this file would then shadow the other stack's rules.  Use
    [twp_apply] with the rule you mean. *)
