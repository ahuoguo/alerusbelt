(** Hint databases and [solve_typing], for the total typing layer.

    Identical to [typing/base.v] but over the total program logic's
    proofmode and allocation wrappers. *)
From Stdlib.Program Require Import Tactics.
From lrust.lang Require Export total_proofmode.
(* Last, so that we shadow the prelude's [delete]. *)
From lrust.lang.lib Require Export total_new_delete.

Open Scope Z_scope.

Create HintDb lrust_typing.
Create HintDb lrust_typing_merge.

(* First without the merging rules, then from scratch with them: the proof
   search for [tctx_extract_hasty] must succeed even if the type is an
   evar, and merging makes it diverge in that case. *)
Ltac solve_typing :=
  (typeclasses eauto with lrust_typing typeclass_instances core; fail) ||
  (typeclasses eauto with lrust_typing lrust_typing_merge typeclass_instances
     core; fail).

Global Hint Constructors Forall Forall2 list_elem_of : lrust_typing.
Global Hint Resolve submseteq_cons submseteq_inserts_l submseteq_inserts_r
  : lrust_typing.

Global Hint Extern 1 (@eq nat _ (Z.to_nat _)) =>
  (etrans; [symmetry; exact: Nat2Z.id | reflexivity]) : lrust_typing.
Global Hint Extern 1 (@eq nat (Z.to_nat _) _) =>
  (etrans; [exact: Nat2Z.id | reflexivity]) : lrust_typing.

Global Hint Resolve <- elem_of_app : lrust_typing.

(* [done] is there to handle equalities with constants *)
Global Hint Extern 100 (_ ≤ _) => simpl; first [done|lia] : lrust_typing.
Global Hint Extern 100 (@eq Z _ _) => simpl; first [done|lia] : lrust_typing.
Global Hint Extern 100 (@eq nat _ _) => simpl; first [done|lia] : lrust_typing.
