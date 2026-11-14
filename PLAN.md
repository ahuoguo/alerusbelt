# AlerusBelt on Coneris: refork upstream VerusBelt, keep concurrency and prophecies

## Context

AlerusBelt (this repo, `main`) is VerusBelt retargeted from Iris's `wp` to
clutch/eris's `pgl_wp`, with **concurrency removed** (commits `8b45220`,
`f7a2903`, 2584 deleted lines) and **prophecies removed** (commit `5465148`,
~1350 lines). Both removals were forced by eris: eris has no concurrency, and
Iris's *operational* prophecies are unsound with error credits
([clutch `eris/examples/noproph.v`](https://github.com/logsem/clutch/blob/main/theories/eris/examples/noproph.v)).

Two things have changed.

1. **The prophecy removal was unnecessary.** `noproph.v`'s `falso` needs
   `wp_new_proph` to hand back a concrete `pvs` the proof can `destruct`, and
   `wp_resolve_proph` to force `⌜pvs = (#(), v) :: pvs'⌝`. VerusBelt's
   prophecies are RustHornBelt-style *logical* ones: `proph_tok ξ q` is a
   fraction with no value in it, `proph_resolve` lets the prover pick the
   resolved value, and `proph_obs_sat` yields only `⌜∃π₀, φπ π₀⌝`. Neither
   ingredient exists. Mechanized this session in
   `src/lambda_verus/typing/examples/proph_credits.v` (4 lemmas, all `Qed`),
   with `prophecy/{syn_type,prophecy}.v` building unchanged against eris.
2. **Coneris exists and is already installed** in the `verisbelt` switch, so
   concurrency does not have to go either.

Intended outcome: one development with lambdaRust's concurrency, VerusBelt's
prophetic mutable borrows, and Eris-style error credits, soundness proved
against Coneris's scheduler-indexed adequacy.

Decisions taken (from the questions asked while planning):
fresh clone of upstream `verus-lang/verus-belt`; no presampling tapes for
lambdaRust; full later-credit replay on Coneris.

## Upstream state

`https://github.com/verus-lang/verus-belt`, `main` @ `115a618`
(pushed 2026-11-10). Well ahead of the artifact at `e321944` in this repo:

| commit | date | content |
|---|---|---|
| `115a618` | 2026-10-25 | `prophecy.v`: resolution reservations |
| `516ed46` | 2026-10-23 | prophetic borrows library (`util/proph_bor.v`, 36 KB); unique borrows rebased on it |
| `22db381` | 2026-10-18 | `typing/proph_protocol.v`: VerusSP storage protocols with prophetic rel |
| `2a17809` | 2026-10-18 | `ra.v`: VerusRA validity made prophetic |
| `b9b14b2` | 2026-08-07 | `NllftUsr` / `NllftG` overlap |

41 `.v` files in `typing/` (~790 KB) including `spawn.v`, `atomic_inv.v`,
`programs_util_atomic.v`. Vendors Iris and stdpp pinned to
`coq >= 8.19 < 8.21~`, `coq-stdpp dev.2024-10-30` - roughly a year behind this
repo's Rocq 9.1.1 / `rocq-iris.dev` @ `93c7df74`.

Checked: upstream's reworked `prophecy.v` (~900 lines) still defines
`proph_obs φπ := ∃L, ⌜∀π, π ◁ L → φπ π⌝ ∗ [∗ list] pli ∈ L, proph_atom pli`,
`proph_tok ξ q := own proph_name (◯ line ξ (fitem q))`, and
`proph_obs_sat : proph_ctx -∗ .⟨φπ⟩ ={E}=∗ ⌜∃π₀, φπ π₀⌝`. The compatibility
argument above transfers verbatim; only the new reservation API is unexamined
(Stage 7).

## Stages

Each stage ends at a build gate. Build serially (`make -j1`); two concurrent
`rocqworker`s OOM this machine.

### Stage 0. Import upstream

Add `verus-belt` as a second remote, fetch it, branch `coneris` off
`verus-belt/main` @ `115a618`. Full upstream history, same repo, so `main`'s
already-proved error-credit typing rules stay cherry-pickable.

### Stage 1. Toolchain update on the new tree

No semantic change. Delete vendored `src/iris`, `src/stdpp` and
`docker-contents`; depend on the opam pins `main` already uses. Replay the
mechanical parts of `ddd723a` ("rm local iris and stdpp") and `2982bbd`
("update to iris 4.5.0 & rocq 9.1.1") - both are in this repo's history and
serve as the worked example. Files upstream has that `2982bbd` never saw need
doing by hand: `util/proph_bor.v`, `typing/proph_protocol.v`, and the
rewritten `typing/{ra,protocol,uniq_bor}.v`, `prophecy/prophecy.v`.

**Gate:** upstream VerusBelt builds green on Rocq 9.1.1 / Iris dev, still on
iris-WP, concurrency and prophecies intact, zero `Admitted`.

### Stage 2. Later credits for Coneris (the long pole)

`coneris/weakestpre.v:23` is `conerisWpGS_invGS :: invGS_gen HasNoLc Σ` with
no step counter; `lrustGS_invGS` is `invGS_gen HasLc Σ` because Leaf's
`guard_later_pers` needs credits. Replay the three eris commits documented in
`~/Desktop/clutch/probability/FOO27-veris/eris-lc-changes.md` on the
`eris-lc-step` branch of the clutch fork:

1. `HasNoLc` -> `HasLc` on `conerisWpGS`.
2. `state_interp : state Λ → iProp Σ` -> `nat → state Λ → iProp Σ`, plus the
   `state_interp_mono` field; thread `n` through every lift.
3. Add `num_laters_per_step : nat → nat` and produce
   `£ (S (num_laters_per_step n))` inside `prog_coupl`.

Touches `coneris/{weakestpre,adequacy,lifting,ectx_lifting,error_rules,`
`primitive_laws,wp_update,derived_laws}.v` (~4900 lines) and the coneris
examples. Expect adequacy to need the same `fupd_finally` rebase as eris
(`eris-lc-changes.md` section 4.4).

**Gate:** clutch builds; `coneris/examples` still compile; `£ 1` usable under
a coneris WP.

### Stage 3. lambdaRust as a `conLanguage`

- `head_step : expr → state → list Empty_set → expr → state → list expr → Prop`
  becomes `prim_step : expr → state → distr (expr * state * list expr)`.
  Observations are `Empty_set` and always `[]`, so they drop for free, which is
  itself the evidence that VerusBelt's prophecies are purely logical.
- Replace `NdInt` with `rand N`; lift the definition and the `bin_op_eval`
  surroundings from `main`'s `src/lambda_verus/lang/lang.v`, which already did
  exactly this.
- `state_idx := Empty_set`, `get_active σ := []`, `state_step σ α := dzero`.
  Both `ConLanguageMixin` state-step obligations
  (`mixin_state_step_not_stuck`, `mixin_state_step_mass`,
  `common/con_language.v:26,29`) are then vacuous.
- Define a lambdaRust-specific `state_step_coupl` carrying only the
  `⌜1 ≤ ε⌝`, `Z σ ε` and epsilon-increase disjuncts. This is what lets us skip
  Coneris's `con_prob_lang` specialization: the fourth disjunct is the only
  reason `coneris/weakestpre.v` hardcodes the language, via
  `sch_erasable (λ t _ _ sch, TapeOblivious t sch)` with `TapeOblivious`
  defined at `con_prob_lang/lang.v:1315`. No presampling tapes for lambdaRust;
  AlerusBelt uses none.
- `lrustGS` carries `conerisWpGS` + `ecGS` + heap + time, on `HasLc`.
- Port `lang/{heap,lifting,notation,proofmode,tactics,error_rules}.v` from
  `main` rather than from upstream: they were already converted once for eris,
  so the deltas are the `efs` thread list and the coupling-modality names.
- Keep upstream `lang/races.v` and `lang/lib/spawn.v`.

**Gate:** a standalone example proving a WP for a program that forks a thread
and samples, e.g. `Fork e ;; rand #2`.

### Stage 4. Lifetime logic and Leaf

`guarding/` (21 files) and `lifetime/` (12 files) are WP-independent ghost
theory over `fupd`. Expect no change beyond picking up the `HasLc` instance.
`util/cellmap.v` (138 KB) and `util/non_atomic_cell_map.v` (66 KB) likewise.

**Gate:** both directories build against the Stage 3 `lrustGS`.

### Stage 5. Typing layer

All 41 `typing/` files, nothing deleted. The WP swap is mechanical and already
documented for this codebase in
`~/Desktop/clutch/probability/FOO27-veris/verisbelt.md` section 1; the only new
wrinkle versus that document is that `efs` survives instead of being dropped.
`spawn.v`, `atomic_inv.v`, `programs_util_atomic.v`, `util/proph_bor.v` and
`typing/proph_protocol.v` all come along.

Order: `base`, `syn_type`, `lifetime`, `lft_contexts`, `inv_context`, `type`,
`type_context`, `cont_context`, `programs`, then the type constructors, then
`borrow`, `ra`, `protocol`, `proph_protocol`, `function`, `fixpoint`.

**Gate:** `make -j1` green, zero `Admitted`, upstream's
`typing/examples/{assert,list,pcell_example}.v` pass.

### Stage 6. Error credits in the type system

Cherry-pick from `main`: `typing/rand_ubig.v` (`error_credit_ty`,
`type_rand`, `type_credit_contradict`) and `typing/examples/coin_flip.v`.
These sit above the WP-rule names and are already proved. `error_credit_core`
there is built on the de-prophecised `type` record, so its `ty_proph` /
`ty_lev` fields need filling in for the prophetic `type`.

**Gate:** `coin_flip` retyped and its safety bound re-derived.

### Stage 7. Prophecies against error credits, checked not assumed

Port `typing/examples/proph_credits.v` (written this session) onto the new
tree and extend it to upstream's reservation API. The four existing lemmas
carry over unchanged because `proph_obs`, `proph_tok` and `proph_obs_sat` are
unchanged upstream. What is new and genuinely unexamined:

- `proph_reserve : proph_ctx -∗ 1:[ξ] -∗ q:+[ζl] ={E}=∗ proph_reserved ξ ζl ∗ q:+[ζl]`
- `proph_unreserve`, `proph_reserve_extend`, `proph_resolve_reserved`

The question is whether `proph_reserved ξ ζl` is still purely exclusive rather
than *determining*. `proph_reserved_tok_excl` and `proph_reserved_excl`
suggest it is, but this is the one place where the eris-noproph argument was
formed before the mechanism existed. Add the analogue of
`obs_and_resolve_consistent` for a reserved resolution.

**Gate:** extended `proph_credits.v` green; if a reservation does turn out to
determine, this is where it surfaces, before the soundness theorem depends on
it.

### Stage 8. Soundness

`coneris/adequacy.v:744` gives

```coq
Theorem wp_safety Σ `{conerisGpreS Σ} ... (sch : scheduler ...) `{!TapeOblivious ...} :
  0 <= ε → sch_mass_1 sch →
  (∀ `{conerisGS Σ}, ⊢ ↯ ε -∗ WP e {{ v, ⌜φ v⌝ }}) →
  SeriesC (sch_pexec sch n (ζ, ([e], σ))) >= 1 - ε.
```

With no tapes in lambdaRust, `TapeOblivious` is vacuous, so the restated
AlerusBelt Theorem 1 quantifies over **all** mass-1 schedulers. `wp_pgl_lim`
(`adequacy.v:351`) gives the limit form. Theorem 2 (the EPT / total-variation
bound) needs reworking against `sch_pexec` instead of `lim_exec`; that is new
proof work, not a port.

**Gate:** `typing/soundness.v` restated and proved; `coin_flip`'s bound
re-derived end to end.

## Risks

1. **Stage 2 is the long pole.** If Coneris's adequacy resists later credits
   the way eris's did, expect the `fupd_finally` rebase and a few days of
   plumbing. Do it first, as a spike, before any VerusBelt work.
2. **Later placement.** Coneris's single `▷` sits inside `prog_coupl` beneath
   `state_step_coupl`. Leaf's `guard_later_pers` and the lifetime logic's
   later usage must line up with that. Unverified.
3. **Stage 1 is bigger than replaying two commits.** Upstream's `ra.v`,
   `protocol.v`, `uniq_bor.v` and `prophecy.v` were rewritten after our
   `2982bbd`, and `proph_bor.v` / `proph_protocol.v` are new.
4. **Partial correctness only.** Coneris is `pgl_wp`. The `nola` branch's
   total-correctness work does not merge into this line; it stays separate.
5. **Upstream is active** (last push 2026-11-10). Pin `115a618` and rebase
   deliberately rather than tracking `main`.

## Order of work

Stage 2 spike first (clutch only, no VerusBelt in the loop), because it is the
one stage that can invalidate the plan. Then Stage 1, then 3, then the rest in
order.

## Verification

Per-stage gates above. Overall:

- `make -j1` green from a clean tree at every stage boundary.
- `grep -rn "Admitted\|Abort" src/` empty.
- Example suite: upstream's `assert.v`, `list.v`, `pcell_example.v`, plus
  `coin_flip.v` and `proph_credits.v` carried over from `main`, plus a new
  concurrency example exercising `spawn` and `rand` together.
- The headline check that the refork was worth it: a typed program that uses a
  prophetic mutable borrow, forks a thread, and spends an error credit, with
  its safety bound derived from `wp_safety`.
