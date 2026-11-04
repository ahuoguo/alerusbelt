(** The typing layer's program logic.

  [verus_haltGS] fixes the ghost state; this file turns it into a
  [lrustTotGS], which is what the weakest-precondition rules of
  [lang/total_lifting_heap.v] are stated over.

  It is a file of its own rather than the last paragraph of [ctx.v]
  because [ctx.v] is imported by *every* typing file, including the ones
  that only build type formers.  With this instance in scope, elaborating
  [typing_total/sum.v]'s [xsum_ty] takes over ten minutes; without it, one
  second - and that is with every field of the record replaced by a
  constant, so it is the instance's presence in the database and not
  anything the record says.  Lowering its priority does not help: the
  search that finds it has no other solution.  Keeping it out of the way
  of the files that never state a weakest precondition is the fix.  See
  [lang/total_proofmode.v] and [lang/lib/new_delete_defs.v] for the same
  mistake made with the *partial* stack's [lrustGS]. *)
From lrust.typing_total Require Export ctx.
Unset Default Proof Using.
Set Default Goal Selector "1".
Unset Suggest Proof Using.

Section ctx_wp.
  Context `{!verus_haltGS FML Σ, !VerusHaltSem FML Σ, !HeapSem FML Σ}.

  #[export] Instance verus_halt_lrustGS : lrustTotGS FML Σ := {|
    lrustTotGS_invGS := verus_halt_invGS;
    lrustTotGS_na_invGS := na_inv_invG;
    lrustTotGS_alcGS := verus_halt_alcG;
    lrustTotGS_heapGS := verus_halt_heapGS;
    lrustTotGS_naSem := verus_halt_NaSem;
    lrustTotGS_heapSem := _;
    lrustTotGS_ecGS := _;
  |}.
End ctx_wp.

(** Let the projections reduce.  [heapGS], [na_invG] and friends are
    reachable both directly, as fields of [verus_haltGS], and through this
    instance; the two terms are convertible but not syntactically equal,
    and [iSpecialize] matches syntactically, so a heap rule stated over
    [lrustTotGS] could not be applied to a points-to produced by the
    typing layer. *)
Global Arguments verus_halt_lrustGS {_ _ _ _ _} /.
