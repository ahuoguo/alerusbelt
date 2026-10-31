(** [memcpy] as a *term*, with no program logic.

    Same reason as [lib/new_delete_defs.v]: the value and the two
    [<-{n} !] notations are language-level, and keeping them beside the
    partial specifications forced the total stack to [Export] the partial
    one, which put its [lrustGS] into scope all the way up the total
    typing layer. *)
From lrust.lang Require Export notation tactics.
Set Default Proof Using "Type".

Definition memcpy : val :=
  rec: "memcpy" ["dst";"len";"src"] :=
    if: "len" ≤ #0 then #☠
    else "dst" <- !"src";;
         "memcpy" ["dst" +ₗ #1 ; "len" - #1 ; "src" +ₗ #1].

Notation "e1 <-{ n } ! e2" :=
  (App (of_val memcpy) [e1%E; Lit (LitInt n); e2%E])
  (at level 80, n at next level, format "e1  <-{ n }  ! e2") : expr_scope.

Notation "e1 <-{ n ',Σ' i } ! e2" :=
  (e1%E%E <- #(LitInt i);; e1 +ₗ #(LitInt 1) <-{n} !e2)%E
  (at level 80, n, i at next level, format "e1  <-{ n ,Σ  i }  ! e2") : expr_scope.
