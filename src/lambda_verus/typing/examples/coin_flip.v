(** Probabilistic-assertion example: flip a fair coin, "assert" it
    lands heads, with [↯_T (1/2)] error budget.

    Mirrors [veris/ub/rand_primitives.rs::flip].  In Verus:

        fn flip(Tracked(input_credit): Tracked<ErrorCreditResource>) -> (ret: u64)
            requires (ErrorCreditCarrier::Value { car: 0.5real }) == input_credit.view(),
            ensures  ret == 1,
        {
            let (val, Tracked(outcome_credit)) = rand_1_u64(...);
            proof { if (val != 1) { ec_contradict(&outcome_credit); } };
            assert(val == 1); val
        }

    Operationally the program is:

        let n = rand 2 in
        if n = 1 then 0 else !(#☠)

    The [else] branch is a load from the poison literal [#☠] — a
    *stuck* expression in [lrust_prob_lang]'s operational semantics.
    With an [↯_T (1/2)] credit in the input tctx and the per-outcome
    refund [flip_ε2 0 := 1, flip_ε2 1 := 0], the rand step pushes all
    error mass onto the tails branch, where [↯ 1] in hand suffices to
    derive [False] via [ec_contradict] and discharge the stuck WP.

    This is the full typing-layer version: the closed expression is
    given a [typed_body] derivation under input tctx
    [+[#l ◁ ↯_T (1/2)]], and bridged to an operational safety bound
    via [type_soundness_credit] (soundness.v).  The credit's path-witness
    handle [#l] (a typing-layer artifact, see [rand_ubig.v] header)
    is generated inside the soundness proof. *)

From Stdlib Require Import Reals Psatz.
From iris.proofmode Require Import proofmode.
From clutch.base_logic Require Import error_credits.
From clutch.prob Require Import distribution countable_sum mdp.
From lrust.prob Require Import adequacy.

From lrust.lang Require Import notation lifting proofmode tactics lang heap
                                 error_rules.
From lrust.typing Require Import type type_context programs rand_ubig
                                   soundness tracked function cont
                                   own bool int uninit product mod_ty.
From lrust.typing.examples Require Import assert_prob.
Set Default Proof Using "Type".

Local Open Scope R.

(** The closed expression — sample [n ∈ {0, 1}], compute [n = 1],
    then call [assert] on the result.

    [coin_flip_typed] is the WP-level proof using the simple
    value-passing [assert] (a plain lambda) via [wp_assert].
    [call_assert_via_fn_type] below demonstrates the typing-layer
    pattern from upstream verisbelt's [pcell_example.v]:
    [type_let { apply assert_type. }] introduces the fn-typed
    [assert_fn] into the tctx, and [type_letcall] invokes it on a
    boxed bool argument. *)
(** [coin_flip]: rand → conditional UB.  The [if] is inlined so the
    typing layer can case-split via [type_rand_case] and discharge
    the false branch via [type_credit_contradict]. *)
Definition coin_flip : expr :=
  (let: "n" := rand #2 in
   if: "n" = #1 then #0 else !(#☠))%E.


(** Body of [coin_flip] after the [let "n" := rand #2 in] —
    extracted so its [Closed ["n"]] instance can be registered
    once and reused. *)
Definition coin_flip_body : expr :=
  (if: "n" = #1 then #0 else !(#☠))%E.

Local Instance coin_flip_body_closed : Closed ["n"] coin_flip_body.
Proof. unfold coin_flip_body, Closed. simpl. done. Qed.

Section flip.
  Context `{!typeG Σ, !cnaInv_logicG Σ}.

  (** Per-outcome refund schedule: pay [↯ 1] on tails (unreachable
      via [ec_contradict]), [↯ 0] on heads. *)
  Definition flip_ε2 (n : nat) : R :=
    if (n =? 1)%nat then 0%R else 1%R.

  Lemma flip_ε2_bounded n : (0 <= flip_ε2 n <= 1)%R.
  Proof. rewrite /flip_ε2. case (Nat.eqb_spec n 1); intros; lra. Qed.

  Lemma flip_SeriesC_le :
    SeriesC (λ n : nat,
        if bool_decide (n < Z.to_nat 2)%nat
        then (1 / Z.to_nat 2) * flip_ε2 n
        else 0)%R
      <= 1/2.
  Proof.
    rewrite (SeriesC_ext _ (λ n,
      if bool_decide (n <= 1)%nat
      then (1 / Z.to_nat 2) * flip_ε2 n
      else 0)%R); last first.
    { intros n.
      destruct (le_lt_dec n 1) as [Hle | Hgt].
      - rewrite !bool_decide_eq_true_2; [done|lia|simpl; lia].
      - rewrite !bool_decide_eq_false_2; [done|lia|simpl; lia]. }
    rewrite SeriesC_nat_bounded_to_foldr'.
    simpl. rewrite /flip_ε2 /=. lra.
  Qed.

  (** [coin_flip_typed]: the typed_body derivation under
      [+[#l ◁ ↯_T (1/2)]].  The predicate transformer is trivial
      [(λ _ _ _, True)] — the load-bearing content is the WP, which
      consumes the credit through [wp_rand_exp_nat] and
      [ec_contradict].  The proof bypasses [type_rand_ubig_instr] +
      [type_if] + [type_int_eq] and goes directly to the WP layer
      (the typing-rule combinators are available but would require
      [typed_body_impl] gymnastics to match the trivial
      transformer; the direct WP path is cleaner here). *)
  (** [coin_flip_typed]: pcell-style end-to-end typing-layer proof.

      Uses [type_rand_case] (in [rand_ubig.v]) to case-split on the
      rand outcome [m] at the Coq level.  Each branch is then a
      separate typed_body:
      - [m = 0]: tctx has [↯_T 1] refund; discharge via
        [type_credit_contradict] (after reordering with
        [typed_body_tctx_incl]).
      - [m = 1]: tctx has [↯_T 0]; the [if] takes the true branch,
        terminate with [#0]. *)
  Lemma coin_flip_typed (l : loc) :
    ⊢ typed_body (𝔄l := [at_locₛ (trackedₛ unitₛ)]) (𝔅 := unitₛ) [] []
                 (InvCtx [] static AtomicClosed) []
                 +[#l ◁ ↯_T (1/2)] coin_flip (λ _ _ _ _, True%type).
  Proof.
    rewrite /coin_flip.
    iApply (type_rand_case 2 (1/2) flip_ε2 #l "n").
    { lia. } { apply flip_ε2_bounded. } { apply flip_SeriesC_le. }
    iIntros (m Hm).
    (* Two cases: m = 0 (false branch / UB) and m = 1 (true branch). *)
    destruct (Nat.eqb_spec m 1) as [-> | Hne].
    - (* m = 1: tctx has [↯_T (flip_ε2 1) = ↯_T 0].  The body
         simpl_subst's "n" to #1; the [if] takes the true branch,
         returning [#0]. *)
      change (flip_ε2 1) with 0%R.
      simpl_subst.
      iIntros (tid xl mask post iκs) "#LFT _ _ _ _ _ _ _ _ _".
      wp_op. wp_case. (* wp_case auto-closes at the value via wp_value_head *)
      rewrite /cont_postcondition. done.
    - (* m = 0 (the only other option since [Hm : m < 2]): the
         credit refund is [flip_ε2 0 = 1].  Apply the post-rand
         variant of [type_credit_contradict]. *)
      assert (m = 0)%nat as -> by lia.
      change (flip_ε2 0) with 1%R.
      iApply type_credit_contradict_after_rand.
  Qed.

End flip.

(** [coin_flip] gets stuck (dereferences poison) with probability at
    most [1/2], under every scheduler of mass 1: instance of
    [type_soundness_credit] with the [↯ (1/2)] budget. *)
Theorem coin_flip_safe `{!typePreG Σ} `{Countable sch_int_state}
    (ζ : sch_int_state) (sch : scheduler (con_lang_mdp lrust_lang) sch_int_state) (n : nat) :
  sch_mass_1 sch →
  (SeriesC (sch_pexec sch n (ζ, ([coin_flip], (∅, false)))) >= 1/2)%R.
Proof.
  intros Hmass.
  cut (SeriesC (sch_pexec sch n (ζ, ([coin_flip], (∅, false)))) >= 1 - 1/2)%R; [lra|].
  apply (type_soundness_credit ζ sch (𝔅 := unitₛ) (λ _ _ _ _, True%type)
           (λ _ _ _, True%type) (1/2)%R coin_flip n Hmass); [lra|done|].
  intros ? l. iApply coin_flip_typed.
Qed.

Print Assumptions coin_flip_safe.
