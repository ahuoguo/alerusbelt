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

## Next

1. prob/weakestpre.v (+ lifting, ectx_lifting, error rules needed by lrust)
2. prob/adequacy.v
3. Stage 3: lrust lang as conEctxiLanguage (refork lang.v + main's Rand /
   countable / distr head_step), heap, lifting, time, races, spawn.
4. Stage 4-8 per PLAN.md.
