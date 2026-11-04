(** * Sampling and credit amplification, at the typing layer

  Two rules that have no counterpart in Nola's [verus_halt/typing/],
  because Nola's weakest precondition is not probabilistic.  This tree's
  partial [typing/rand_ubig.v] has their [pgl_wp] siblings.

  [type_rand_exp] is [lang/total_lifting_heap.v]'s [twpw_rand_exp_nat]
  lifted to [typed_body]: a [let] binding a [rand] splits into one goal
  per outcome, with the error credit redistributed by a schedule whose
  mean the caller bounds.

  [type_amp] is the loop rule the probabilistic examples need.  It is
  one line, because [ec_ind_amp] is stated for an arbitrary [P : iProp Σ]
  and [typed_body] *is* an [iProp Σ].  A body that re-enters itself
  having amplified its credit by a factor [k > 1] is typed without any
  decreasing measure and without a Loeb rule, which is exactly what a
  total weakest precondition cannot otherwise do.

  Note what is deliberately absent: an error-credit *type*.  The partial
  tree carries [↯_T ε], an [own_ptr_0] over a ghost core whose [ty_gho]
  is [↯ ε], so the credit can sit in a typing context.  Here [ty_ghox] is
  a [cif] *formula* rather than an [iProp], so a credit-carrying type
  would need a new constructor in [typing_total/inst.v]'s signature.  The
  credit is threaded as an ambient [iProp] instead, which is all these
  two rules need. *)
From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.prob Require Import distribution.
From lrust.lang Require Import notation total_proofmode total_lifting_heap.
From lrust.typing_total Require Export programs.
From nola.bi Require Import modw.
Import ModwNotation TglWpwNotation.
(** Our [util] last, so that its [SemiIso] wins the name over Nola's; see
  [typing_total/type.v]. *)
From lrust.util Require Import basic.
(** [ctx_wp], for the [lrustTotGS] instance: this file states weakest
  preconditions.  See the head of [typing_total/ctx_wp.v]. *)
From lrust.typing_total Require Import ctx_wp.
Unset Default Proof Using.
(** [iris.prelude.options] sets [Default Goal Selector "!"], which rejects a
  bare tactic while more than one goal is focused.  It reaches a ported file
  through our imports and not through Nola's, so Nola's proofs - written
  against the default [1], "act on the first goal" - would otherwise need a
  focus fix every few lemmas.  Restoring [1] is a lint setting, not a
  soundness one. *)
Set Default Goal Selector "1".
Unset Suggest Proof Using.

Local Open Scope R.

Section rand_rules.
  Context `{!typeG FML Σ}.

  (** Sampling, with the credit redistributed over the outcomes.

    The schedule [ε2] must be bounded by [1] pointwise, because a credit
    above [1] is already absurd, and its mean over the [z] outcomes must
    not exceed the credit paid in - that is the expectation-preserving
    side condition of [twpw_rand_exp_nat]. *)
  Lemma type_rand_exp {𝔄l 𝔅} E L (I : invctx) (C : cctx 𝔅) (T : tctx 𝔄l)
      (z : Z) (ε1 : R) (ε2 : nat → R) (x : string) e tr :
    (0 < z)%Z → (∀ n, 0 <= ε2 n <= 1) →
    SeriesC (λ n : nat, if bool_decide (n < Z.to_nat z)%nat
                        then (1 / Z.to_nat z) * ε2 n else 0) <= ε1 →
    (** [lrust_prob_lang]'s [RecV] carries a [Closed] side condition, so
      without this the [let]'s lambda is not a value to [reshape_expr]
      and [twp_bind] cannot reach the [rand].  This tree's partial
      [typing/rand_ubig.v] takes the same premise. *)
    Closed (x :b: []) e →
    ↯ ε1 -∗
    (∀ n : nat, ⌜(n < Z.to_nat z)%nat⌝ -∗ ↯ (ε2 n) -∗
       typed_body E L I C T (subst x #(Z.of_nat n) e) tr) -∗
    typed_body E L I C T (let: x := rand #z in e) tr.
  Proof.
    iIntros (Hz Hb Hm Hcl) "Hε Hbody". rewrite /typed_body /typed_body_at.
    iIntros (tid xl mask post iκs) "LFT UNIQ Eq Lq Iq Cq Tq %Htr".
    twp_bind (rand _)%E.
    (* [iExact] rather than naming [Hε] in the spec pattern: the rule's
      [↯] is at the [ecGS] reached through [verus_halt_lrustGS] and the
      hypothesis's is at [verus_haltGS]'s own field.  The two are
      convertible but not syntactically equal, and [iSpecialize] matches
      syntactically.  See the head of [typing_total/ctx_wp.v]. *)
    iApply (twpw_rand_exp_nat _ z ε1 ε2 _ _ Hz Hb Hm with "[Hε]"); [iExact "Hε"|].
    iIntros (n) "[%Hn Hε]". twp_let.
    iAssert ⌜(n < Z.to_nat z)%nat⌝%I as "Hn'"; [done|].
    iDestruct ("Hbody" $! n with "Hn' Hε") as "body".
    iApply ("body" $! tid xl mask post iκs
      with "LFT UNIQ Eq Lq Iq Cq Tq").
    by iPureIntro.
  Qed.

  (** The loop rule.  [ec_ind_amp] at [typed_body], and nothing else. *)
  Lemma type_amp {𝔄l 𝔅} E L (I : invctx) (C : cctx 𝔅) (T : tctx 𝔄l)
      e tr (ε k : R) :
    0 < ε → 1 < k →
    □ (∀ ε' : R, ⌜0 < ε'⌝ -∗ □ (↯ (k * ε') -∗ typed_body E L I C T e tr) -∗
         ↯ ε' -∗ typed_body E L I C T e tr) -∗
    ↯ ε -∗ typed_body E L I C T e tr.
  Proof. iIntros (??). by iApply ec_ind_amp. Qed.
End rand_rules.
