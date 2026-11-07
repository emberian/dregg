# AIR generator sub-lane report — 2026-11-06

Initiative register row **#1: Parser/language excellence (policy language, demos, perf, Lean-first AIR generator, build)**. Owner: Codex gpt-6-astra. Root commits; no commit or push performed by this sub-lane.

## Ready source and artifacts

- `metatheory/Dregg2/Circuit/Emit/SolvencyLeafEmit.lean`: generic bit-range generator and soundness; 30-bit two-limb solvency descriptor; integer comparison theorem from actual `Satisfied2`; fact-hash/PI equality theorem; both modular-wrap falsifiers; nonzero-borrow full descriptor inhabitant plus sound chip-table witness. **16 keystones kernel-clean**, four exact `#guard_msgs` axiom pins; no `native_decide`.
- `circuit-prove/src/solvency_leaf_adapter.rs`: remove Rust constraint builder, parse Lean artifact, generate six limbs/90bits/internal borrow, reject out-of-range host amounts before field reduction. Add production-interpreter attack tests and a real inner-STARK roundtrip with changed-PI refusal. New v2 descriptor identity; same two commitment PI slots.
- `circuit/descriptors/by-name/solvency-leaf-v2.json`: emitted by Lean, 30,012 bytes including newline, 118 columns, 106 constraints. Old shape was 51 columns/36 constraints; old `(0,2^30-1)` was falsely solvent because difference wraps below2^30.
- `zkoracle-prove/src/zk_leg.rs` and `circuit/descriptors/by-name/dfa-routing-injection.json`: replace duplicate inline Lean JSON with artifact include. Emitted JSON exactly equals prior 2901-byte literal; stale missing-challenges comment removed. Regression tests are no longer described as refinement proof.
- `metatheory/EmitByName.lean`: three imports and seven rows for these two artifacts plus tuple lane's five; pin 133→140. Route-table/weld additions are held for their separate landing.
- `docs/automata/AIR-GENERATOR-GROUNDING.md`: structural census correction, generator choices, statement limits, remaining production debt.

## Checks and limits

[MEASURED] Warm single-file Lean compile completed with exit0: `lake env lean -o .lake/build/lib/lean/Dregg2/Circuit/Emit/SolvencyLeafEmit.olean Dregg2/Circuit/Emit/SolvencyLeafEmit.lean` (log `/tmp/astra-solvency-lean11.log`). Reports 16 clean keystones; all exact axiom-message pins pass. Full honest `Satisfied2` witness and `ChipTableSoundN` witness are kernel checked.

[MEASURED] Standalone `lake env lean --run` serialization; JSON parsed and shape counts checked. Injection bytes compared exactly to captured former literal. Existing `emit_descriptors.py.parse_by_name_routing()` statically reads 140 unique rows and agrees with the pin; all 7new files exist. This does not certify provenance. Rustfmt completed on both owned Rust modules.

[PENDING] Rust integration belongs to the build-integration lane, queued for bb2 headroom. No Rust green is claimed yet. Commands:

```sh
cargo nextest run --release -p dregg-circuit-prove --lib --ignore-default-filter -E 'test(solvency_descriptor_lowers) | test(solvency_emitted_) | test(fact_arity7_chip_absorb_matches_hash_fact)'
cargo nextest run --release -p dregg-zkoracle-prove --lib --ignore-default-filter -E 'test(injection_leg_descriptor_roundtrip) | test(injection_leg_hostiles_refused) | test(table_dfa_agrees_with_the_verified_matcher)'
```

The first needs the circuit-prove dependency closure and verified Lean FFI archive. Do not substitute Rust fallback by setting `DREGG_REQUIRE_LEAN=0`. These filtered tests avoid full recursion wrapping; existing full fold tests remain available if shape integration exposes a recursion issue.

[PENDING] Fresh integrated-revision provenance stamp, sequenced with Mina rescue. The old stamp chain's immutable source snapshot cannot certify these new artifacts. No full Mac build, box job or foreign-clone write was done by this lane.

## Exact continuation

Root can commit the named source/artifact files with pending Rust status explicit, then batch filtered tests and stamp at the integrated revision. Tuple lane owns its own generator/adapters/artifacts; its 5routes are included above. Route-table/weld siblings'2newmodules/artifacts are ready for a separate EmitByName update after their closure lands.

Next concrete C9 client: DECO's three fact-opening sites plus amount-minus-one range. Tuple sibling is grounding and implementing a shared fact-opening generator. Amount domain is inclusive≤2^30 (header erroneously says<), transcript commitment currently is an existential column and not a public authenticated transcript binding. Caveat admission already has an integer `CaveatBignumCompare.borrowSub_iff` theorem; it still needs an emitted modular-to-integer bridge and consumed descriptor. zkOracle commitment is a parameterized length-specific producer, not a single static artifact. Broader debt inventory is in the grounding note. Nothing here claims C9 finished or proves Rust/STARK refinement from case tests.

## Subsequent integration update

The 21-file initial generator set landed in **a63744ae407f7adb10f839417369f264f7d55530**, whose subject belongs to the streaming lane: that concurrent commit included the staged generator files. This lane performed no git mutation. The coordinator records the actual SHA rather than rewriting shared history.

A follow-up extracts Solvency's copied generic helpers into the shared `BoundedFactEmit` owned by the DECO lane. Solvency retains 12 local keystones; the shared helper's keystones remain pinned at their own definitions. [MEASURED] Fresh Lean serialization after this refactor exactly matches the committed descriptor bytes (`cmp`, exit 0). DECO and caveat add two further consumed static producers; the four new emission rows (DECO,caveat,table route,weld route) bring the measured router count to 144. Detailed caveat proof and check results are in `CAVEAT-AIR-REPORT-2026-11-06.md`. Rust integration and fresh provenance remain the coordinator/build lane's pending checks.


## Note-spend follow-up and current debt

The shared helper/DECO/caveat/table/weld source closure landed in **bf583f317**. The next owned step replaces the two duplicated fixed note-spend Rust constructors with the already-proved Lean last-row repair. See `NOTE-SPEND-AIR-REPORT-2026-11-06.md` for exact files/checks and explicit theorem limits. This brings removed production constructors to ten; the bounded original51path census is45struct expressions in18files. The two old41site law1 baseline rows are removed, with no new allowance. `AIR-REMAINING-DEBT.md` replaces the earlier broad “parameterized” label with actual per-producer semantics and next transformations. Native tests and integrated provenance remain pending until the coordinator records their results.
