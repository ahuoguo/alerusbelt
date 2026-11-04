(** The allocation wrappers as *terms*, with no program logic.

    [new], [delete] and the [letalloc:] notations are language-level: they
    are a [val] and two pieces of notation, and nothing about them depends
    on which weakest precondition is in use.  They used to live in
    [lib/new_delete.v] beside the partial specifications, and
    [lib/total_new_delete.v] had to [Export] that file to get at them -
    which put the *partial* stack's [lrustGS] into scope all the way up the
    total typing layer.  That is not merely untidy: it made the type
    formers of [typing_total/sum.v] take over twenty minutes to elaborate
    against four seconds for the same proof in Nola's own build.  Compare
    the note in [lang/total_proofmode.v], which is the same mistake one
    level up. *)
From lrust.lang Require Export notation tactics.
From lrust.lang.lib Require Export memcpy_defs.
Set Default Proof Using "Type".
Open Scope Z_scope.

Definition new : val :=
  λ: ["n"],
    if: "n" ≤ #0 then #((42%positive, 1337):loc)
    else Alloc "n".

Definition delete : val :=
  λ: ["n"; "loc"],
    if: "n" ≤ #0 then #☠
    else Free "n" "loc".

Notation "letalloc: x <- e1 'in' e2" :=
  ((Lam [BNamed x%string%E] (Seq (Var x <- e1) e2))
    [App (of_val new) [ #(LitInt 1)]])%E
  (at level 102, x at level 1, e1, e2 at level 150) : expr_scope.

Notation "letalloc: x <-{ n } ! e1 'in' e2" :=
  ((Lam [BNamed x%string%E%E]
    (Seq (Var x <-{n%Z%E} !e1) e2))
    [App (of_val new) [ Lit (LitInt n)]])%E
  (at level 102, x at level 1, e1, e2 at level 150,
    format "letalloc:  x  <-{ n }  ! e1  'in'  e2") : expr_scope.
