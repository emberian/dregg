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
- **Kernel recursion is bounded by `maxRecDepth`** (4.33 #13956), deterministic across hosts:
  "(kernel) deep recursion detected" needs a `set_option maxRecDepth N in` on the declaration.
- **`rw` closes more goals by `rfl`**, so a trailing `exact`/`rfl` after `rw` hits "no goals".
  `rwa .. at h` now closes the goal with `h` itself only (4.35 #14937).
- **Instances with arguments not inferable by TC synthesis are rejected**; such "instances" that are
  only ever applied explicitly become `@[reducible] def`.
- **`do` elaborator (4.32)**: needs `Pure`; `do match` arms non-dependent; `return` inside `(← do ..)`
  returns from the enclosing block.
- **Core lemma renames (4.34)**: `if_pos/if_neg` -> `ite_eq_left/right`, `dif_pos/dif_neg`, `if_true`
  -> `ite_true` etc. Deprecated aliases remain (warnings only; not touched in this lane).
- **`Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`, `Lean.reduceBool` are removed**
  (4.35 #14953). `native_decide` already emitted per-theorem `<thm>._native.native_decide.ax_*` axioms in
  4.30; that is now the only form. `#assert_compiled` (Dregg2/Tactics.lean) loses its core-reduce
  branch, nothing else.
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
