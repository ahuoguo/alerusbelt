(** * Logical prophecy variables are compatible with error credits.

    [clutch/eris/examples/noproph.v] shows that Iris's *operational*
    prophecies are unsound with up-to-bad reasoning.  Its counterexample
    is

        let "p" := NewProph #() in let "x" := rand #99 in ResolveProph "p" "x"

    and it needs exactly two things.  (1) [wp_new_proph] returns
    [proph p pvs] where [pvs] is a concrete list, so the proof may
    case-split and read off the value [v] the resolution *will* take.
    (2) [wp_resolve_proph] then forces [pvs = (#(), v) :: pvs'], so the
    guess is guaranteed right.  Between the two, the proof spends
    [1/100] on [Err-Rand-Exp] to rule out [rand = v], and the resolve
    refutes the rest.

    VerusBelt does not use those prophecies.  Following RustHornBelt it
    uses the *logical* prophecies of [lrust.prophecy.prophecy], and
    neither ingredient exists there:

      - allocation ([proph_intro]) hands back only a fraction
        [1:[ξ]] - there is no resource naming a future value, so there
        is nothing to case-split on;
      - resolution ([proph_resolve]) lets the *prover* pick the value,
        so it can always be made to agree with whatever ran.

    Both are pure ghost updates with no [prim_step], so prophecies are
    invisible to [lim_exec] and to the credit supply.  This file states
    the three facts and closes with the AlerusBelt analogue of clutch's
    [bad], which is safe with no credits at all. *)

From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.eris Require Import weakestpre.
From lrust.prophecy Require Import prophecy.
From lrust.lang Require Import notation lifting proofmode lang.
Set Default Proof Using "Type".

(** The syntactic type of integer-valued prophecies. *)
Notation Zi := (Zₛ ↾ I : syn_typei).

Section proph_credits.
  Context `{!lrustGS Σ, !prophG Σ}.

  (** ** Allocation reveals no value

      Compare [wp_new_proph], whose postcondition is [∃ pvs p, proph p pvs]
      with [pvs] read off the world's resolution list. *)
  Lemma proph_alloc_reveals_nothing (I : gset positive) E :
    ↑prophN ⊆ E → proph_ctx ={E}=∗ ∃ i, ⌜i ∉ I⌝ ∗ 1:[PrVar Zi i].
  Proof. apply proph_intro. Qed.

  (** ** Resolution is chosen by the prover

      Compare [wp_resolve_proph], which forces the resolved value to be
      the head the world had already fixed.  Here every [z] is available,
      so the prophecy can always follow the program. *)
  Lemma proph_resolve_any E ξ (z : ξ.(pv_ty)) :
    ↑prophN ⊆ E → proph_ctx -∗ 1:[ξ] ={E}=∗ ⟨π, π ξ = z⟩.
  Proof.
    iIntros (?) "#PROPH Hξ".
    iMod (proph_resolve emp E ξ (λ _, z) [] ltac:(done) ltac:(by move=> ???)
           with "[] PROPH Hξ []") as "[$ _]"; [|done|done].
    iIntros (?) "%Hin". by apply elem_of_nil in Hin.
  Qed.

  (** ** The step the attack needs, and cannot have

      An observation [φπ] made *before* a sampling step and a resolution
      to the value [z] the step actually produced are always jointly
      satisfiable.  So no credit allocation chosen from a pre-sampling
      observation can be refuted by a post-sampling resolution, which is
      the move that closes clutch's counterexample. *)
  Lemma obs_and_resolve_consistent E ξ (φπ : proph Prop) (z : ξ.(pv_ty)) :
    ↑prophN ⊆ E →
    proph_ctx -∗ .⟨φπ⟩ -∗ 1:[ξ] ={E}=∗ ⌜∃ π₀, φπ π₀ ∧ π₀ ξ = z⌝.
  Proof.
    iIntros (?) "#PROPH #Hobs Hξ".
    iMod (proph_resolve_any with "PROPH Hξ") as "#Hz"; [done|].
    iDestruct (proph_obs_and with "Hobs Hz") as "#Hand".
    by iMod (proph_obs_sat with "PROPH Hand") as %?.
  Qed.

  (** ** clutch's [bad], with no credits

      Prophecy allocation and resolution are ghost moves, so the
      AlerusBelt analogue of [bad] is just the sampling step.  Where
      clutch derives [↯ (1/100) ⊢ WP bad {{ False }}], here the
      prophecy is simply resolved to the sampled value and the
      observation that comes back is consistent. *)
  Definition bad (N : Z) : expr := (rand #N)%E.

  Lemma bad_safe E (N : Z) (i : positive) :
    (0 < N)%Z → ↑prophN ⊆ E →
    proph_ctx -∗ 1:[PrVar Zi i] -∗
    WP bad N @ E {{ v, ∃ z : Z, ⌜v = #z⌝ ∗ ⟨π, π (PrVar Zi i) = z⟩ }}.
  Proof.
    iIntros (??) "#PROPH Hξ". rewrite /bad.
    iApply pgl_wp_fupd. iApply wp_rand; [done|]. iIntros (n).
    iMod (proph_resolve_any E (PrVar Zi i) (Z.of_nat n) with "PROPH Hξ") as "#Hz"; [done|].
    iModIntro. iExists (Z.of_nat n). by iSplit.
  Qed.
End proph_credits.
