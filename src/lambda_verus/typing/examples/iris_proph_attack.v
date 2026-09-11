(** * Iris analog of the Verus [ProphecyGhost] unsoundness attack.

    The Verus code below proves [False] in ghost code:

    << use vstd::proph::ProphecyGhost;

       proof fn test() {
           let tracked p = ProphecyGhost::<bool>::new();
           p.resolve(!p.value());
           assert(false);   // ← contradiction!
       }
    >>

    The trick:
      - [p.value()] reads the prophesied [bool] as a Coq-level value.
      - [p.resolve(!b)] then commits the prophecy to [!b].
      - The two are (allegedly) about the same underlying value,
        so [b = !b], contradiction.

    This file works at the [proph_map] level (no [heap_lang], which
    is not in our iris pin) and shows why iris does NOT admit the
    attack: it does not offer a "peek" that reveals a prophesied
    value while retaining the [proph] resource. The only rule that
    reveals a prediction is [proph_map_resolve_proph], and it
    consumes the resource in the same breath. *)

From iris.base_logic.lib Require Import proph_map ghost_map.
From iris.proofmode Require Import proofmode.
Set Default Proof Using "Type".

Section proph_soundness.
  Context {P V : Type} `{Countable P} `{!proph_mapGS P V Σ}.
  Implicit Types p : P.
  Implicit Types v : V.

  (** ** Iris's two load-bearing prophecy rules

      From [iris.base_logic.lib.proph_map]:

      << Lemma proph_map_new_proph p ps pvs :
           p ∉ ps →
           proph_map_interp pvs ps ==∗
           proph_map_interp pvs ({[p]} ∪ ps) ∗
             proph p (proph_list_resolves pvs p).
      >>

      Allocation.  The user does NOT choose the list of future
      resolves; it is computed from the world's [pvs].  Once bound,
      the user just knows "there exists some [vs] such that
      [proph p vs]".

      << Lemma proph_map_resolve_proph p v pvs ps vs :
           proph_map_interp ((p, v) :: pvs) ps ∗ proph p vs ==∗
           ∃vs', ⌜vs = v :: vs'⌝ ∗ proph_map_interp pvs ps ∗
                 proph p vs'.
      >>

      Resolution.  To resolve, the WORLD supplies a [(p, v)] head; the
      user's [vs] is then FORCED to be [v :: vs'].  The equation
      [⌜vs = v :: vs'⌝] is what pins down the head — you cannot pick a
      different [v] than what the world's [pvs] said.

      And the exclusivity lemma that the ghost-map underlying [proph]
      gives for free:

      << Lemma proph_exclusive p vs1 vs2 :
           proph p vs1 -∗ proph p vs2 -∗ False.
      >> *)

  (** ** The attack, transliterated

      Verus does:
      << let b = p.value();         (* keeps [p], gains [bool] b *)
         p.resolve(!b);              (* consumes [p], commits [!b] *)
      >>

      In iris, "keep [p] and gain b" would be a rule of the shape

      << lethal_peek : proph p (v :: vs) -∗ ⌜v = ??? some_concrete⌝ ∗
                                            proph p (v :: vs)
      >>

      that publicises the head to the meta-logic. Iris has no such
      rule — every operation that reveals the head consumes it. *)

  Section counterfactual.
    (** We POSTULATE a lethal peek: the ability to observe the head
        of the resolve list at some concrete value [v0] chosen at
        query time, without giving up the [proph] resource. *)
    Hypothesis lethal_peek :
      ∀ p v0 vs,
        proph p (v0 :: vs) -∗
        ⌜v0 = v0⌝ ∗ proph p (v0 :: vs).
    (* ↑ the equation is trivial; the DANGEROUS content is retaining
       [proph p (v0 :: vs)] while also carrying a piece of meta-level
       information about [v0]. *)

    (** With lethal_peek in scope, we can reproduce Verus's [False].
        The attack does not need heap_lang or any WP: it is entirely
        about the interaction of [proph_exclusive] and a
        non-consuming peek. *)

    Lemma attack_derives_False p v0 vs1 vs2 :
      proph p (v0 :: vs1) -∗ proph p (v0 :: vs2) -∗ False.
    Proof.
      iIntros "H1 H2".
      by iDestruct (proph_exclusive with "H1 H2") as %[].
    Qed.

    (** Concretely: if we could BOTH peek to learn [head = v0] AND
        resolve with [head = v1 ≠ v0], we'd need two [proph] resources
        for the same [p] with different heads.  [proph_exclusive]
        forbids that. *)

    (** The subtler statement of the same point: if some hypothetical
        rule could hand us BOTH a [proph p (v_actual :: vs)] AND a
        [proph p (v_wrong :: vs)] with [v_wrong ≠ v_actual] — the
        latter modelling "I peeked and got v_wrong from the meta
        logic, but the true resolution is v_actual" — the attack
        would land via [proph_exclusive] regardless of the [v]s. *)

    Lemma peek_that_hands_back_a_second_proph_is_lethal
        p v_actual v_wrong vs :
      proph p (v_actual :: vs) -∗
      proph p (v_wrong :: vs) -∗
      False.
    Proof.
      iIntros "H1 H2".
      by iDestruct (proph_exclusive with "H1 H2") as %[].
    Qed.
    (* Iris does not have a rule that produces the second [proph].  Any
       peek that publicises the head must not hand back a fresh copy of
       [proph]; and iris rules never do. *)

  End counterfactual.

  (** ** Why the attack has no analog in real iris

      1. [proph_map_new_proph] hands you [proph p vs] where [vs] is
         determined by the world's [pvs], not by you.  You only learn
         [vs] via subsequent operations — and those operations consume
         it.

      2. [proph_map_resolve_proph] is the only rule that reveals the
         head of [vs]: it takes [proph p vs], reveals [vs = v :: vs']
         (with [v] chosen by the world's [pvs], not by you), and hands
         back [proph p vs'].  The head is NEVER revealed without
         consumption.

      3. [proph_exclusive] guarantees you cannot duplicate [proph p _]
         to keep one copy for "peeking" and use another for
         "resolving".  Ghost-map fragmentality gives this immediately.

      Verus's [ProphecyGhost::value()] violates (2) — it reveals the
      head without consuming.  That is the sole reason the Verus
      attack works and its iris analog does not. *)

End proph_soundness.

(** ** TL;DR

    Verus's [.value()] amounts to a rule that reveals the head of
    [pvs] without consuming the [proph] resource.  Iris does not
    offer such a rule and cannot: combining it with the resolve rule
    would let you produce [False] via the exact sequence of steps in
    the Verus [test]. *)
