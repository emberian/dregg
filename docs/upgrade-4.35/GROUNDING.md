# Lean v4.30.0 -> v4.35.0 for breadstuffs (lane `lane/lean-435`)

Goal: one toolchain across breadstuffs `metatheory/`, minidregg and Veil (`/Users/ember/src/veil`), so
they can share code and the branching-time logics (CTL, mu-calculus, LTL, the Stream omega-automata) can
run on Veil's transition systems and checkers.

## The pins

| | before | after |
|---|---|---|
| `metatheory/lean-toolchain` | `leanprover/lean4:v4.30.0` | `leanprover/lean4:v4.35.0` |
| Mathlib | `1c2b90b13009c65b090d95a83c98e248deafb6f1` | `56a005855ea17e0b0958f73ec801ae140b0a1679` (minidregg's) |
| manifest | format 1.2.0, deps inherited from Mathlib | minidregg's `lake-manifest.json` verbatim, root name `Dregg2` |
| package-store key (`lean-packages key`) | `856c40722ebb` | `d11ceef8c941` |

Mathlib 56a00585's dependency revisions (batteries 66e46918, aesop 4a174c49, Qq dce0ad79, proofwidgets
df72b022) are exactly Veil 2.0's, so a package can require both Veil and Mathlib without a version
fight. Veil itself has no Mathlib.

Other files that name the pin and move with it: `.github/workflows/ci.yml` and
`proof-integrity-canary.yml` (`MATHLIB_REV`), `dregg-lean-ffi/lean-seed.pin`,
`scripts/check-mathlib-intact.py`, `scripts/check-p3-rev-selftest.py` (its anti-false-positive anchor),
`scripts/check-p3-rev.sh` (comment).

Not moved (separate Lean roots with no Mathlib and no import of `metatheory/`; their owners move them):
`dregg-serve-spec/`, `orb/` (requires dregg-serve-spec), `orb-compiler/` (and its `Pancake/build_*.sh`
`LEAN=` defaults), `fhegg-rtl/lean/`. The seL4 PDs (`sel4/dregg-pd/*`) cross-build their own Lean
4.30 runtime archives and C from standalone files; they stay on 4.30 until that lane rebuilds them.

## What changed in Lean, 4.31 to 4.35 (what bites this tree)

Release notes: reference-manual `Manual/Releases/v4_3{1..5}_0.lean`.

- **Transparency (4.33, the big one).** `backward.isDefEq.respectTransparency.types` is on: a
  metavariable's type is compared with its value's type at *implicit* transparency. Symptoms:
  `rw`/`simp` "did not find an occurrence" with the note "target expression is not type-correct under
  the implicit transparency", `simpa`/`exact` "Type mismatch: After simplification", instances over
  type synonyms not found (4.35 #14624 does the same for instance search). Fix order (minidregg's
  playbook): unfold the definition explicitly (`simp only [f]`, `show`), mark a layout/type-family
  definition `@[reducible]`, and only where nothing else works, `set_option
  backward.isDefEq.respectTransparency false in` on that one declaration, never file-wide (Mathlib
  v4.35 does this in 1,470 files).
- **`Decidable` is now `Decidable.intro (decide : Bool) (h : decide.Reflects p)`** (4.35 #8309).
  `isTrue`/`isFalse` remain as functions and patterns. Kernel `decide` on big instances behaves
  differently (faster on well-written instances; "failed to reduce" where an instance hid its body).
  Fixes: `decide +kernel`, or a direct proof; Batteries' `DecidableEq (Except ..)` body is module-hidden.
- **Performance trap: `decide` is a structure projection now.** A pointwise equation
  `f x = decide (...)` (what `simp only [f]` or a `simpa` closing step produces) makes the kernel unfold
  the projection and whnf the `Decidable` instance over the symbolic term: Bridge.MinaVrfThreshold
  (`Int.decLe` over a degree-10 polynomial) ran 8-18 min, past 20 GB, then hit kernel deep recursion,
  and OOM-killed two whole-tree builds. Fix: a function-level `f_def` used by `rw`, then
  `of_decide_eq_true`/`decide_eq_true` (9 s). Any Bool-valued `decide` definition over big symbolic
  arithmetic can hit this.
- **Kernel recursion is bounded by `maxRecDepth`** (4.33 #13956), deterministic across hosts:
  "(kernel) deep recursion detected" needs a `set_option maxRecDepth N in` on the declaration.
- **`rw` closes more goals by `rfl`**, so a trailing `exact`/`rfl` after `rw` hits "no goals".
  `rwa .. at h` now closes the goal with `h` itself only (4.35 #14937).
- **Instances with arguments not inferable by TC synthesis are rejected**; such "instances" that are
  only ever applied explicitly become `@[reducible] def`.
- **`do` elaborator (4.32)**: needs `Pure`; `do match` arms non-dependent; `return` inside `(← do ..)`
  returns from the enclosing block.
- **`do` loop state is now a `Prod` in declaration order** (it was a reversed `MProd`). Proofs that
  `rfl`/`rw` against the old fold shape need a `List.foldl_hom` bridge (MlKemCodecSpec
  `accFold_prod`/`setFold_prod`).
- **Mathlib: `PMF.uniformOfFintype` became a deprecated alias of a `Measure`** (Mathlib 2026-10-04).
  `Dregg2/ForMathlib/UniformPMF.lean` keeps the old PMF construction as `PMF.uniformFintype` /
  `uniformFinset`; MlKemDelta and ModelBridge use it. **Statement spelling change** (same object,
  the name moved): ModelBridge `pi_uniform_singleton`, `pi_uniform_finset`, `roMeasure_accept` now name
  `PMF.uniformFintype`.
- **Core lemma renames (4.34)**: `if_pos/if_neg` -> `ite_eq_left/right`, `dif_pos/dif_neg`, `if_true`
  -> `ite_true` etc. Deprecated aliases remain (warnings only; not touched in this lane).
- **`Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`, `Lean.reduceBool` are removed**
  (4.35 #14953). `native_decide` already emitted per-theorem `<thm>._native.native_decide.ax_*` axioms in
  4.30; that is now the only form. `#assert_compiled` (Dregg2/Tactics.lean) loses its core-reduce
  branch, nothing else.
- **`==` on `UInt8/16/32/64/USize` now uses `Classical.choice`.** 4.35 core adds `Std.LinearOrderPackage`
  instances for the fixed-width integers (`Init/Data/UInt/Package.lean`); their `BEq` outranks
  `instBEqOfDecidableEq` and is built with choice, so a `[propext, Quot.sound]` pin over byte `==`
  gains `Classical.choice`. Fix: file-local `attribute [local instance high] instBEqOfDecidableEq`
  (Tree.Value, Tree.Json). The same holds for `Int`, `Fin n` and `String.Pos.Raw`
  (`Init/Data/{Int,Fin}/Package.lean`): Sat/LratCert, Datalog FixpointCert/StratifiedCert, Crypto/Deriv/
  BisimCert got the same file-local attribute (and two LratCert pins shrank to `[propext, Quot.sound]`).
  Follow-up after the upgrade lands: one `attribute [instance high] instBEqOfDecidableEq` in a base
  module (Dregg2.Tactics) restores 4.30's resolution tree-wide, then the locals go.
- `Std.Sat.CNF.Clause` is a structure now (atoms/polarities): build clauses with `Clause.ofLiterals`.
- `alias` is a keyword (4.35); `constructor` warns when several constructors fit (4.35);
  `Lean.RBMap` deprecated (unused here); `mvcgen` deprecated (unused here); `letFun` deprecated (unused).
- **Module system**: Mathlib 56a00585 is `module`-ized. Every non-module file importing it gets a
  warning per import ("designed for use with the module system"); harmless, very noisy logs.
  Module-hidden bodies mean `decide`/`rfl` cannot see through some Mathlib/Batteries definitions.
- **FFI**: `lean_initialize_runtime_module` is implicit in module initializers (4.34 #14505);
  `lean_enable_initializer_execution` returns a scalar (4.33 #14372; not called here); codegen no longer
  inspects private constructors of public types (4.33 #13679, can change a struct's C layout).
- **Lake**: `lake build --fail-fast`; `precompileImports`/`precompileLibrary`; dependencies cloned
  partially; `lake check` (+ `--paranoid`, bundled lean4lean/nanoda) as an axiom/kernel gate we can
  adopt later; manifest format 1.3.0.

## What is on the default build

`metatheory/lakefile.toml` `defaultTargets`: Dregg2 (umbrella `Dregg2.lean`, ~1,050 imports), Metatheory
(glob), Polis (glob), Market, Bfv, PicklesSynthesis, and the guard libs MinaBridgeGuards,
CommitBindsGuards, TurnAuthGuards, PicklesEmitDrivers, DivergenceToothGuards, PathOfAngelsGuards,
GameFixtureGuards, ZkmlSuiteGuards, CallTreeGuards. 2,722 `.lean` files, 1.38 M lines; 612 files use
`native_decide`, 227 files carry `#assert_compiled` pins, 39 files `#guard_msgs` over `#print axioms`.
A cold v4.35 default build is ~11,600 Lake jobs (Mathlib's included).

Gates around it (`metatheory/BUILD.md`): `make check-fast` (Mac, `lake lean` per changed file),
`make check-full` / `check-umbrella` (scripts/iter-check; per-box `packages-<key>` filled once by
`lake exe cache get`, snapshots under `~/olean-store/metatheory/<commit>`), `metatheory/scripts/automata-check.sh`
(the automata family: Datalog, Policy, Sat, Automata, Tree, Stream), `scripts/axiom-hygiene-guard.sh`,
`scripts/check-guard-modules.py` (baseline `scripts/guard-modules-baseline.txt`, red on main already).

## Native side

- Measured on 4.35 (bb2): `tree-check`, `calltree-check`, `dfa-run`, `stream-check` build and run;
  `tree-check verify` accepts the demo field certificates, and `stream-check root` prints the same
  MMR root byte for byte as the 4.30 binary. Binary size 118 MB vs 108 MB on 4.30 (Lake executables
  already linked all of Lean).
- Lean executables in the lakefile: `datalog-check`, `dfa-run`, `policyc`, `calltree-check`,
  `stream-check`, `tree-check`, `polis_governor`, the Mina emitters (`mina_*_emit`, `mina_sg_bench`),
  `emit_seam_specs`, `mina_wrap_opening_sched_emit`. Rebuilt by `lake build <exe>` on 4.35.
- `--load-dynlib`/`@[extern]`: 16 files declare externs (Exec/FFI, Blake3Compute, Ed25519Reduction,
  Storage/Deployed, ...); no lakefile `moreLeanArgs` dynlib today.
- Rust that links Lean archives: `dregg-lean-ffi` (the `libdregg_lean.a` seed + toolchain runtime,
  static or `DREGG_LEAN_LINK=shared`), which every Lean-linked crate goes through (dregg-circuit,
  grain-turn, grain-verify, exec-lean, dregg-pq, calltree, ...); plus `sdk-py`, `pg-dregg`,
  `audit-flashprove` (own `lean_initialize_runtime_module` shim). Toolchain discovery follows
  `metatheory/lean-toolchain`. The seed is content-keyed by `scripts/lean-seed-key.sh`
  (toolchain + Mathlib rev + closure), so the new pin has no published seed until one is cut;
  `fetch-lean-seed.sh` 404s and a local `scripts/bootstrap.sh` (or the seed workflow) builds one.
- **The largest native risk (measured, not guessed).** Since 4.34 (#14505) every generated module
  initializer starts by initializing Lean itself. `Lean/Compiler/LCNF/EmitC.lean` (v4.35.0, l.1018-1033):
  a module whose environment uses any module of the `Lean` package (every breadstuffs module does,
  through Mathlib) emits `lean_initialize();` at the top of `initialize_<Module>`; others emit
  `lean_initialize_runtime_module();`. Seen in this tree's IR (`ir/Dregg2/Execution.c`: `void
  lean_initialize(); ... _G_initialized = true; lean_initialize();`). `lean_initialize`
  (`src/initialize/init.cpp`) runs the whole runtime init *including `initialize_libuv`*, the C++
  util module, and `initialize_Init`, `initialize_Std` and `initialize_Lean` (the entire compiler and
  elaborator). Consequences for `dregg-lean-ffi`:
  - STATIC mode's `lean_init_st.cpp` deliberately runs the libuv-free prefix of the runtime init and
    never pulls `init_module.cpp.o`. On 4.35 the first module initializer it calls re-runs the full
    runtime init (the runtime's `g_initialized` flag was never set by the shim: double
    `initialize_alloc`/`initialize_object`) and starts the libuv thread it was written to avoid.
  - Every static link now references `lean_initialize`, so `libLean.a` is reachable from every
    module initializer: the closure-completion / reachability-GC work (tree-shake) loses most of
    its effect, and binary size and startup time grow by the compiler's.
  - The fix belongs in `dregg-lean-ffi` (not in Lean sources): in STATIC mode define our own
    idempotent `lean_initialize_runtime_module` (the libuv-free prefix, setting a flag) and
    `lean_initialize` (that, plus `initialize_Init`/`initialize_Std`; the executor never elaborates,
    which is the same argument Lean's own `LEAN_MINIMAL_CORE_INIT` build makes for `leanchecker`), so
    neither `init_module.cpp.o` nor `init.cpp.o` is pulled. SHARED mode is unaffected (the exported
    runtime init is idempotent in 4.35).
  The bundled-mimalloc TLS note in `Cargo.toml` must be re-checked against the 4.35 `libleanrt.a`.

## Who depends on the 4.30 pin today

- Every bb2 breadstuffs clone (`~/automata/bs`, `~/calltree/bs`, `~/stream/bs`, `~/mina-rescue/bs`,
  `~/sessreceipt/bs`, `~/iterspeed/bs`, `~/astra-*`, `~/iter-check/*`) and the 4.30 snapshot
  `~/olean-store/metatheory/274f65a8`; hbox `~/lanes/*`; the Mac's shared tree
  (`/Users/ember/dev/breadstuffs`, key 856c40722ebb) and `breadstuffs-codex`. A lane that merges main
  after this lands rebuilds cold once (no 4.30 olean is reusable) unless it fetches the 4.35 snapshot.
- In-flight lanes with `.lean` edits will hit the same transparency breaks in their new code; the
  fix patterns above apply.

## Built atop it: `veil-bridge/`

A separate Lake package (root `veil-bridge/`) that requires `Dregg2` by path (`../metatheory`) and Veil
2.0 at `4eaf93e9`. Its manifest is breadstuffs' package set plus Veil's (smt, Loom, VerifiedHAMT,
Lasso, lentil, cvc5, auto); the four shared packages (batteries, aesop, Qq, proofwidgets) are the same
revisions in both, which the manifest generator asserted.

- `VeilBridge.toSystem` (the shared definition, `@[reducible]`): a Veil `RelationalTransitionSystem`
  at background theory `th` as a breadstuffs `Dregg2.Execution.System` (Config = Veil state, Step =
  Veil's `next`).
- `VeilBridge.invariant_iff_AG`: a Veil invariant (every reachable state is in `P`) iff breadstuffs'
  gfp `CTL.AG P` holds at every initial state; with `reachable_of_run`/`run_of_reachable` relating
  Veil's `reachable` to `Run`. Kernel-clean (`#assert_all_clean`).
- `VeilBridge.RingCTL.single_leader_invariant_iff_AG`: Veil's tutorial ring leader election, its
  `single_leader` safety property as an `AG` statement. (Veil keeps the abstract-state
  `FieldRepresentation` instances module-local; the bridge opens them with `attribute [local instance]`.)

So every `Dregg2.Proof.CTL`/`MuCalculus` theorem applies to a Veil protocol as is; the next step is
checking CTL formulas on Veil systems (Veil's explicit-state checker for the finite instance, Lasso's
LTL->TGBA and nested DFS for the liveness side, breadstuffs' Stream omega-automata as the spec side).

Building it (bb2): Veil compiles C for its dependencies (Qq and friends), so the bridge cannot use the
read-only package store for those. `veil-bridge/.lake/packages/` holds symlinks into the store for
mathlib, Cli, importGraph, LeanSearchClient, writable copies (`cp -a`, then `chmod -R u+w`) of Qq,
batteries, aesop, proofwidgets, plausible, and Lake's own clones of Veil's packages. Then
`lake build` in `veil-bridge/` (about 1,300 Veil jobs the first time, then only the bridge). The
`../metatheory` path dependency builds into `metatheory/.lake`, so never run it while a whole-tree
build runs in the same clone.

## Package store and the switch (for the root, on merge)

The Mac store for the upgraded manifest exists and is verified:
`/Users/ember/tools/lean-packages/d11ceef8c941` (`lean-packages ensure` on this branch's
`metatheory/`; every `.olean` header matches v4.35.0). On bb2 the manifest's packages are exactly
the pool's `/srv/pool/packages-3a3779933df4` (minidregg's), which this lane's clones link to.

Switch the shared Mac tree after merging (do not run lake in it before the link is in place):

    cd /Users/ember/dev/breadstuffs
    git merge --ff-only origin/main        # or however the root lands lane/lean-435
    mv metatheory/.lake/packages metatheory/.lake/packages.v430.20261107
    ln -s /Users/ember/tools/lean-packages/d11ceef8c941 metatheory/.lake/packages
    ~/tools/lean-packages/lean-packages verify metatheory
    # the old v4.30 oleans under metatheory/.lake/build are dead; a check-fast run rebuilds what it needs.
    # (Optionally, before the first check-fast, copy a 4.35 snapshot in: scripts/iter-check fetch --box bb2.)

Every other breadstuffs clone: the same `mv`/`ln` (Mac) or link to `/srv/pool/packages-3a3779933df4`
(bb2). `scripts/iter-check` keys per-box stores by manifest key, so check-full on bb2/hbox/forge
fills `packages-d11ceef8c941` once by `lake exe cache get` (on bb2 it can instead be a symlink to
the pool's `packages-3a3779933df4`, same contents). The old key 856c40722ebb stays for lanes that have
not merged.

## Gates (status as measured)

- `scripts/check-guard-modules.py`: FAIL on the lane with 9 STALE + 3 GREW baseline rows
  (EffectActionBindingEmit/Refine, Dregg2.Claims). The identical findings come out of the merge
  base with origin/main: pre-existing, not from this upgrade.
