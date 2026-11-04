(** * Soundness

  Ported from VerusBelt ([typing/soundness.v], MIT, Hance, Elbeheiry,
  Matsushita, Dreyer).

  The original proves *safety*: a well-typed program does not get stuck and
  has no data race.  Later-free the weakest precondition is total, and the
  language is probabilistic, so the same hypothesis gives the quantitative
  statement instead: a well-typed program terminates with probability one.
  That is PLAN-TOTAL-ERIS.md item 1's conclusion, and it is strictly more
  than Nola's [sn erased_step] because the steps here are sampled.

  Data races are not in the picture at all: this port has no concurrency,
  as AlerusBelt has none, so [lang/races.v] never enters the total stack.

  The ghost state is allocated in the order the port forces: the heap first
  (the language's adequacy hands it over), then the lifetime logic, and only
  then the interpretation, because [bor_sem] is [⟦⟧ᶜ(der)] and its [Csem]
  mentions the ghost state.  Compare
  [nola/examples/rust_halt/adequacy.v]'s [rust_wsat_alloc]. *)

From Stdlib Require Import Reals Psatz.
From iris.algebra Require Import gmap_view agree auth gset.
From iris.proofmode Require Import proofmode.
From clutch.prob Require Import distribution.
From lrust.lang Require Import total_adequacy total_heap_adequacy
  total_proofmode notation.
From lrust.typing_total Require Export level_ctx.
From lrust.typing_total Require Import function programs product base_type
  type_context.
From nola.bi Require Import modw.
From lrust.lang Require Import total_wsat.
Import ModwNotation TglWpwNotation iPropAppNotation.
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

(** ** Allocating the world satisfaction

  Every component is allocated before the interpretation is known, and the
  interpretation is handed in afterwards. *)
Section alloc.
  Context `{!typingC CON} {JUDG Σ}
    `{!verus_haltGpreS (cifOF CON) Σ, !invGS_gen HasLc Σ,
      !typingJ CON JUDG Σ}.

  (** The heap and the error credits are both handed in: [lrust_tot_mass_lim_exec]
    allocates them before it knows the formula language's interpretation, and
    [verus_haltGS] has to be built around the very [ecGS] the weakest
    precondition's [err_interp] is at. *)
  Lemma verus_halt_wsat_alloc (hGS : heapGS (cifOF CON) Σ) (hEc : ecGS Σ) :
    ⊢ |={⊤}=> ∃ H : verus_haltGS (cifOF CON) Σ,
      ⌜@verus_halt_invGS _ _ H = _ ∧ @verus_halt_heapGS _ _ H = hGS ∧
        @verus_halt_ecGS _ _ H = hEc⌝ ∗ uniq_ctx ∗
      (∀ (_ : Csem CON JUDG Σ) (_ : Jsem JUDG (iProp Σ))
        (_ : typingCS CON JUDG Σ) (_ : typingJS CON JUDG Σ),
        ⌜LRustTotGS (cifOF CON) Σ _
           (@lrustTotGpreS_na_inv _ _ verus_halt_preG_lrust)
           (@lrustTotGpreS_alc _ _ verus_halt_preG_lrust)
           _ verus_halt_NaSem heapSem_cif _ = verus_halt_lrustGS⌝ ∧
        verus_halt_wsat).
  Proof.
    iMod verus_halt_names_alloc as (Hllft n) "[_ W]".
    (* Nola's [uniq_init] also hands back [send_wsat], the atomic pool's
      [cna_lifetimes]; with no concurrency [send_wsat] is [True]
      ([typing_total/uniq_cmra.v]), so there is nothing to allocate. *)
    iMod (uniq_init ⊤) as (Huniq) "#UNIQ"; [done|].
    iModIntro. iExists (verus_haltGS_of Hllft hGS hEc Huniq n).
    iSplitR; [done|]. iFrame "UNIQ". iIntros (????).
    iSplit; [done|].
    (* [verus_haltGS_of] sets [verus_halt_Wx] to [emp]: this development
      is the single-level one. *)
    iSplitL; [by iApply "W"|done].
  Qed.
End alloc.

(** ** Soundness

  Two shapes, and the difference used to matter.

  [type_soundness] is about a *typing judgment* for a closed expression, as
  in [nola/examples/rust_halt/adequacy.v].  That was not a preference: [fn]
  was the one type former whose interpretation the model did not give, so
  [typed_val main main_type c] - the hypothesis VerusBelt's own theorem
  takes - had no content here.

  [type_soundness_main] below is VerusBelt's own shape, about a [main]
  *function value* that the runtime applies to a continuation.  It is
  available now because [FnFml] is inhabited ([typing_total/fn_inst.v]) and
  because [typing_total/function.v]'s [type_main_body] turns such a [main]
  into a closed [typed_body]. *)

Section soundness.
  Context `{!typingC CON} {JUDG Σ}
    `{!verus_haltGpreS (cifOF CON) Σ, !typingJ CON JUDG Σ}.

  (** A closed, semantically well-typed program whose derivation spends
    [ε] terminates with probability at least [1 - ε].

    The original ([typing/soundness.v]) can only conclude safety: its
    weakest precondition is partial, because a guard there hands out a [▷]
    that only a later credit can pay for.  Here it is total, and over a
    probabilistic language it is [tgl_wp], whose adequacy statement is a
    lower bound on the mass of [lim_exec].

    The credit is handed to the derivation as an ambient [iProp] rather
    than through the typing context.  This tree's partial
    [typing/rand_ubig.v] has an error-credit *type*, [↯_T ε]; here
    [ty_ghox] is a [cif] formula rather than an [iProp], so carrying one
    would need a new constructor in [typing_total/inst.v]'s signature.
    Nothing in [typing_total/sampling.v] needs that. *)
  Theorem type_soundness_credit {𝔅} (e : expr) (tr : predl_trans' [] 𝔅)
      (ε : R) :
    (0 <= ε)%R →
    (∀ post xl mask, tr post xl mask) →
    (∀ H : verus_haltGS (cifOF CON) Σ,
      ∃ (_ : Csem CON JUDG Σ) (_ : Jsem JUDG (iProp Σ))
        (_ : typingCS CON JUDG Σ) (_ : typingJS CON JUDG Σ),
      ⊢ ↯ ε -∗ typed_body [] [] (InvCtx [] static AtomicClosed)
          ([] : cctx 𝔅) +[] e tr) →
    1 - ε <= SeriesC (lim_exec (e, ∅)).
  Proof.
    move=> Hε Htr big.
    apply: (lrust_tot_mass_lim_exec e ε 0%nat); [done|].
    move=> iG hGS hEc. iIntros "_ Hε".
    iMod (verus_halt_wsat_alloc (invGS_gen0 := iG) hGS hEc)
      as (H) "((%eq1 & %eq2 & %eq3) & #UNIQ & →W)".
    subst. move: (big H)=> [Cs [Js [CS [JS ty]]]].
    iMod (invctx_alloc ⊤) as (tid) "I". iModIntro.
    iExists (existT verus_halt_NaSem heapSem_cif), verus_halt_wsat.
    iDestruct ("→W" $! Cs Js CS JS) as "[%Heq $]".
    cbn [projT1 projT2]. rewrite Heq.
    iPoseProof ty as "ty". iSpecialize ("ty" with "Hε").
    iApply (tgl_wp_wand with "[I ty]"); [|by iIntros (?) "_"].
    iApply ("ty" $! tid -[] ⊤ (λ _ _, True) [] with
      "[] UNIQ [] [] I [] [] []").
    all: try by rewrite /llctx_interp.
    all: try by iIntros (? ?%elem_of_nil).
    all: try (iPureIntro; apply Htr).
    all: done.
  Qed.

  (** The typing rules of [typing_total/] other than those in
    [typing_total/sampling.v] mint and spend no error credits, so for a
    derivation that does not mention them the bound is at [ε = 0] and the
    termination mass is a full one. *)
  Theorem type_soundness {𝔅} (e : expr) (tr : predl_trans' [] 𝔅) :
    (∀ post xl mask, tr post xl mask) →
    (∀ H : verus_haltGS (cifOF CON) Σ,
      ∃ (_ : Csem CON JUDG Σ) (_ : Jsem JUDG (iProp Σ))
        (_ : typingCS CON JUDG Σ) (_ : typingJS CON JUDG Σ),
      ⊢ typed_body [] [] (InvCtx [] static AtomicClosed) ([] : cctx 𝔅)
          +[] e tr) →
    1 <= SeriesC (lim_exec (e, ∅)).
  Proof.
    move=> Htr big.
    cut (1 - 0 <= SeriesC (lim_exec (e, ∅))); [lra|].
    apply (type_soundness_credit e tr 0); [lra|done|].
    move=> H. move: (big H)=> [Cs [Js [CS [JS ty]]]].
    exists Cs, Js, CS, JS. by iIntros "_".
  Qed.
End soundness.

(** ** Soundness in VerusBelt's own shape

  [main] is a function value of [typing_total/function.v]'s [main_type] - no
  arguments, a trivial specification - and the program is
  [main [exit_cont]], the application the runtime performs.  This is
  upstream's [type_soundness]/[type_soundness_closed] statement, and it
  needs [fn] interpreted, which is why the port could not state it
  before.

  The hypothesis carries an [FnFml] alongside the interpretation,
  because [main_type]'s arrow level is [fn_lv_top], which is a field of
  it.  [typing_total/fn_inst.v] supplies one. *)
Section soundness_main.
  Context `{!typingC CON} {JUDG Σ}
    `{!verus_haltGpreS (cifOF CON) Σ, !typingJ CON JUDG Σ}.

  Theorem type_soundness_main (main : val) c :
    (∀ H : verus_haltGS (cifOF CON) Σ,
      ∃ (_ : Csem CON JUDG Σ) (_ : Jsem JUDG (iProp Σ))
        (_ : typingCS CON JUDG Σ) (_ : typingJS CON JUDG Σ) (_ : FnFml),
      typed_val main main_type c) →
    1 <= SeriesC (lim_exec (main [exit_cont]%E, ∅)).
  Proof.
    move=> big.
    apply (type_soundness (𝔅:=unitₛ) _ (λ _ _ _, True%type)); [done|].
    move=> H. move: (big H)=> [Cs [Js [CS [JS [FF ty]]]]].
    exists Cs, Js, CS, JS. exact (type_main_body _ _ ty).
  Qed.
End soundness_main.

(** [Eq_rect_eq] and the classical axioms the real numbers come with: eris's
  error credits are [R]-valued, so [Classical_Prop.classic] and friends reach
  every file in the total stack.  The [main]-shaped theorem adds functional
  extensionality, which comes in through [main_type]'s result type: [unit_ty]
  is a [mod_ty] over the empty product ([typing_total/product.v]), and the
  isomorphism it carries is proved by [fun_ext].  Upstream's own [unit_ty] is
  the same. *)
Print Assumptions type_soundness.
Print Assumptions type_soundness_main.
