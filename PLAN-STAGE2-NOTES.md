# Stage 2 working notes: later credits for Coneris

Branch: `coneris-lc` in `~/Desktop/clutch/clutch-logsem` (off `eris-lc-step` @ `1c20382d`).
Build with the **`clutch`** opam switch (same iris pin `93c7df74`, rocq 9.1.1 as
`verisbelt`; the `verisbelt` switch has OCaml 5.4.0 and chokes on the dune
`_build` tree, which was produced with 5.4.1):

    eval $(opam env --switch=clutch --set-switch)
    dune build theories/coneris/adequacy.vo

Do not use the `Makefile`: `_CoqProject` points at `_build/default/theories`,
so `make` and `dune` fight over the same targets.

## Root cause of the whole port

`invGS_gen HasNoLc` gives `BiFUpdPlainly`; `HasLc` does not. Every place
Coneris's adequacy pushed a `∀` or a pure proposition through a `fupd` relied
on it. The cure, exactly as in eris commit `58575653`, is to move from

    |={∅}=> |={∅}▷=>^n ⌜φ⌝        (needs BiFUpdPlainly)

to the `fupd_finally` modality from iris MR 1217

    |={∅|}=> ▷^(S n) ◇ ⌜φ⌝        (closed under ∀ via fupd_finally_forall)

`fupd_finally`, `fupd_finally_mono`, `fupd_finally_intro`,
`fupd_finally_forall`, `fupd_finally_soundness` are upstream iris
(`iris/base_logic/lib/fancy_updates.v`). The shims
`laterN_except_0_pure_mono`, `step_fupdN_pure_forall_intro`, `hfupd_intro`,
`hfupd_intro_pure`, `laterN_hfupd`, `elim_fupd_hfupd_plain`,
`fupd_plain_hfupd'` are *local to* `theories/eris/adequacy.v` (lines 18-33 and
79-126) and have to be copied into coneris.

## Done

- `theories/coneris/weakestpre.v:25` and `theories/coneris/primitive_laws.v:13`
  flipped `HasNoLc` -> `HasLc`. Those are the only two occurrences.
- `theories/coneris/adequacy.v`: eris's 65-line helper block spliced in after
  `Context {!conerisGS Σ}`, and `pgl_dbind'` / `pgl_dbind_adv'` rewritten in
  `fupd_finally` form. Both compile.

## Next, in order

1. `wp_adequacy_val_fupd` (now line 120). Conclusion
   `|={⊤, ∅}=> ⌜pgl ...⌝` has to become `|={⊤|}=> ▷^(S n) ◇ ⌜pgl ...⌝`.
   Two failure sites inside, both the same shape:
   `iApply (fupd_mono _ _ (⌜_⌝)%I)` followed by `iIntros (ε' ?)`. Replace with
   `fupd_finally_mono` + `laterN_except_0_pure_mono` + a
   `step_fupdN_pure_forall_intro` to get the `∀ ε0` out. Then fix its two call
   sites (lines 248 and 260).
2. `state_step_coupl_erasure` and `state_step_coupl_erasure'`: same rewrite of
   `={∅}=∗ |={∅}▷=>^n ⌜·⌝` to `|={∅|}=> ▷^(S n) ◇ ⌜·⌝`. These are the coneris
   analogues of eris's `glm_erasure`; use eris's version as the model but note
   the scheduler/`sch_erasable` premises have no eris counterpart.
3. `wp_refRcoupl_step_fupdN` -> `wp_refRcoupl_hfupd` (eris's name), then
   `wp_pgl_multi` (line ~308) swapping `step_fupdN_soundness_no_lc` for
   `pure_soundness` + `laterN_soundness` + `fupd_finally_soundness HasLc n ⊤`.
4. The safety half: `safety_dbind_adv`, `safety_dbind_adv'`, `safety_dbind'`,
   `state_step_coupl_erasure_safety`, `state_step_coupl_erasure_safety'`,
   `wp_safety_step_fupdN`, `wp_safety_multi` (second
   `step_fupdN_soundness_no_lc` at line ~722). eris's `wp_safety_hfupd` is the
   model.
5. Then the rest of coneris: `wp_update.v`, `error_rules.v`, `lifting.v`,
   `ectx_lifting.v`, `derived_laws.v`, and the examples under
   `theories/coneris/examples/`.
6. Only after that: eris commits `0be76a83` (step counter in `state_interp`)
   and `f6c13a7c` (`num_laters_per_step`). Both are mechanical
   thread-`n`-through edits, unlike step 1-5.
