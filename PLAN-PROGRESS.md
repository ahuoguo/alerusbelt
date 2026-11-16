# Refork progress (AlerusBelt with concurrency + prophecies)

Working notes for executing `PLAN.md` (on branch `coneris` of the main
checkout). Update at every checkpoint.

## Layout

- `/root/alerusbelt-refork`, branch `refork`: upstream verus-belt `115a618`
  + toolchain replay. This is the tree being turned into AlerusBelt.
- `/root/clutch-coneris-lc`, branch `coneris-lc` (also on `logsem/clutch`,
  NOT pushed since): Coneris adequacy ported to `HasLc` / `fupd_finally`.
- `/root/alerusbelt` (branch `coneris`): `main` + `proph_credits.v` + plans.
  `main` = the eris (sequential) AlerusBelt; source of rand / error-credit
  typing rules / adequacy-with-`total_step_credits`.
- Switch for everything: `eval $(opam env --switch=/root/alerusbelt --set-switch)`
  (Rocq 9.1.1, iris dev 93c7df74, stdpp 1.13.0, rocq-clutch from `eris-lc-step`).
  Any `opam install` there needs `--ignore-constraints-on=rocq-stdpp`.
- Commits: never add a Claude co-author line. Do not push.

## Done

- Stage 1 (`refork` @ 0ecdc8d): upstream builds on Rocq 9.1.1 / iris dev,
  102/102 files, 0 Admitted.
- Stage 2 items 1-5 (`coneris-lc` @ 0e5622d2): `coneris/adequacy.v` in
  `fupd_finally` form; all 73 `theories/coneris` files build.

## Decision (2026-11-16): skip Stage 2 item 6 in clutch

Coneris's WP is hardcoded to `con_prob_lang` (tape-oblivious state-step
disjunct). lambdaRust has no state steps, so it needs its own WP anyway
(PLAN Stage 3 already says so). Step counter + `num_laters_per_step` +
`£` per step therefore go into a new **generic** WP in this tree:

- `src/lambda_verus/prob/weakestpre.v`: for any `conLanguage` (state steps
  ignored). Coupling = Coneris `state_step_coupl` minus the tape disjunct
  (`⌜1 ≤ ε⌝ ∨ Z σ ε ∨ ∀ ε' > ε, …`) around Coneris `prog_coupl`; each step
  gives `£ (S (nlps n)) -∗ |={∅}▷=>^(S (nlps n))`, state_interp indexed by n.
- `src/lambda_verus/prob/adequacy.v`: Coneris adequacy as ported in
  `coneris-lc`, plus `main`'s `total_step_credits` budget
  (`/root/alerusbelt/src/lambda_verus/lang/adequacy.v`); all schedulers.

## Done since

- `prob/weakestpre.v`, `prob/lifting.v`, `prob/ectx_lifting.v`,
  `prob/erasure.v`, `prob/adequacy.v` all build, 0 Admitted.
  Key lemmas: `wp_refRcoupl_hfupd`, `wp_safety_hfupd`:
  `£ (total_step_credits k n) ∗ state_interp k σ ∗ err_interp ε ∗ WP e ∗
   [∗ list] WP e' {{fork_post}} ⊢ |={⊤|}=> ▷^(S (total_step_credits k n)) ◇ ⌜…⌝`
  for every scheduler; stutter steps (value / out-of-range thread) bump
  the counter via `state_interp_mono`.
- Lifting lemmas keep Iris's names (`wp_lift_base_step`,
  `wp_lift_atomic_base_step_no_fork`, `wp_step_fupdN`, …) but quantify
  over the support `head_step e σ (e', σ', efs) > 0`.

- Stage 3 (lambdaRust on the new WP): `lang.v` (conEctxiLanguage,
  head_step_prob + support/reducible/det/atomic lemmas), `tactics.v`
  (strong atomicity proved), `time.v`, `heap.v`, `lifting.v` (all
  primitive rules incl. CAS/fork/global lock; time-receipt rules via one
  `wp_cumulative_time_receipt_gen`), `proofmode.v` (full heap tactics),
  `lib/{memcpy,new_delete,spawn}.v`, `adequacy.v` (`lrust_wp_pgl`,
  `lrust_wp_safety`, every scheduler).
  Semantic choices vs. VerusBelt: Rand added; NdInt stuck (wp_nd_int,
  type_nd_int gone, as on main); structural pointer equality; a racing
  successful CAS is stuck (instead of stepping to stuck_term) so CAS is
  strongly atomic; Free checks exact block bounds.
  `lang.v` exports `Default Goal Selector "1"` (clutch turns on "!").

- Stages 4-5: lifetime/, guarding/ unchanged; prophecy/ and all of
  typing/ build on the new WP.  Clean build 106/106, 0 Admitted.
  `typing/soundness.v` restated: for a closed well-typed `main` and every
  mass-1 scheduler, `SeriesC (sch_pexec sch n …) = 1` (no stuck mass), via
  `lrust_wp_safety` with ε = 0.  `pcell_example` instantiates it;
  `Print Assumptions`: only classical reals, extensionality, classic,
  constructive_indefinite_description.
  Fixes needed: `lang.pure.val` qualified names; `Datatypes.id` (Reals'
  `id` shadowed it — prob/weakestpre no longer re-exports Reals); uninit
  notation `↯` -> `↯ᵤ` (as on main; `↯` is error credits);
  `Unset Asymmetric Patterns` exported from lang.v (clutch sets it);
  type_nd_int / type_nd_bool removed (as on main).

- Stage 6: `lang/error_rules.v` (wp_err_incr, wp_err_pos = thin_air,
  wp_rand_exp_nat = rand_ubig, on state_step_coupl/prog_coupl);
  `typing/rand_ubig.v` (main's credit rules on the prophetic type
  record: transformers lifted in π, ε/ε2 stay meta-level);
  `typing/soundness.v: type_soundness_credit` (↯ ε in context ⇒ stuck
  mass ≤ ε for every mass-1 scheduler); `examples/coin_flip.v:
  coin_flip_safe` end to end (standard axioms only).
  Dropped from main's coin_flip: the fn-typed wrapper, the assert_fn
  letcall demo and the Abort-ed no-credit demo; `examples/assert_prob.v`
  keeps main's plain assert + wp_assert.

- Stage 7: `examples/proph_credits.v` ported; reservation API checked:
  reservations record dependencies only, never a value (3 new lemmas).
- Clean build (refork @ dc47764): 111/111, 0 Admitted.

- Distribution adequacy (main's 4 files) ported to schedulers:
  `lang/{,approx_}distribution_adequacy.v`, `typing/{,approx_}distribution_adequacy.v`.
  `type_distribution_adequacy`: an `ept_typed` sampler returns a μ-distributed
  value under EVERY scheduler that makes the main thread return a.s.
  (`sch_lim_exec`); approx: tv ≤ εs + εt/2.  `ept_typed`'s side condition on
  `tr` is now `∀ π, tr (λ _ _ _, True) -[(l,())] ⊤ π`.
  Gotcha: in a theorem under `typePreG`, `invctx_interp` inside `∀ typeG`
  resolves cnaInv via typePreG; `type_wp_pgl` pins it to the typeG's uniqG.
- Clean build: 115/115, 0 Admitted.

- Data-race freedom (2026-11-16): `lang/races.v` ported (reachability =
  `rtc thread_step`, positive-probability steps of any thread; CAS access
  kinds keyed on `lit_eq_dec`, as in `head_step_prob`).
  `lang/race_adequacy.v`: `path_sch` (deterministic scheduler replaying a
  thread path) + wrapping main as `e ;; loop` turn `lrust_wp_safety` (ε = 0)
  into `safe_from`; `lrust_wp_nonracing_safe`.  `typing/soundness.v:
  type_soundness` is upstream's statement again (nonracing ∧ no stuck
  thread in every reachable config); the mass form is `type_soundness_mass`.
  `pcell_example_executes_without_getting_stuck` restored.
- Clean build: 117/117, 0 Admitted.

- Headline example (2026-11-16): `typing/examples/headline.v`.  Typed
  program: `&mut` (prophetic uniq borrow) of a box, `rand 2` with
  `↯_T (1/2)` (credit kills n = 0), write through the borrow, `Endlft`
  (prophecy resolved, `*v` unblocked), `b := *v == 1`,
  `thread::spawn(assert(b))`, then loop.  `headline_safe`: stuck mass
  ≤ 1/2 under every mass-1 scheduler; standard axioms only.
  Library additions: `type_rand_case_tr` (rand_ubig.v: per-branch
  transformers, so prophetic knowledge survives the sample; ε stays
  meta-level), `type_endlft_unblock` (programs.v: `type_endlft` where the
  unblocked context's type list may change — upstream's `type_endlft`
  cannot use `unblock_tctx_cons_unblock`).
- Clean build: 118/118, 0 Admitted.

## Known gaps (not on the plan's critical path)

- Credit soundness only counts stuck mass until `main` returns (the
  Coneris MDP stops there); `headline` ends in a loop for this reason.
  The ε = 0 safety theorem (`race_adequacy.v`) does cover forked threads
  after `main` returns, via the `e ;; loop` wrapper; an ε > 0 version
  would need the path-scheduler argument made quantitative.
- No presampling tapes (Coneris state steps): λRust has no tapes, so the
  tape-based Coneris rules (e.g. for hash / presampled coupling proofs)
  are not available.
- Distribution adequacy takes almost-sure termination as a premise (as on
  `main`); no total-correctness / termination logic.
- No typed `join` (upstream has it commented out in typing/spawn.v).
- `coneris-lc` clutch branch (Stage 2 items 1-5) is unused by this tree.

## Deferred

## Next

8. Stage 8 done.  See "Known gaps".
