# Previous-session lane audit (2026-05-25)

Audit of the 5 lanes that ran into the 5-hour session limit. Verifies
what actually landed vs. what the wrap-up reports claimed. Pure
file-read audit — no `cargo`, no edits.

Checkpoint commits in scope: `b8c9e5b9`, `e03f9d37`, `803624dc`. Plus
the named commits that bracket them (`aba99478` storage templates,
`08bae1fd` γ.2 unilateral integration, `a541df9a` UnilateralAttestation
type, `32c876a2` RingClosureAttestation, `3d2873a5` WitnessProducer,
`c60ee82e` cross-app-e2e).

## Summary table

| Lane | Subject | Status |
| --- | --- | --- |
| 1 | Protocol categorical analysis | **FULLY-LANDED** |
| 2 | Renunciation + Refusal + OneOf | **PARTIAL-NEEDS-COMPLETION** |
| 3 | Unilateral γ.2 binding | **FULLY-LANDED** |
| 4 | Storage-templates broader migration | **MOSTLY-LANDED-MINOR-GAPS** |
| 5 | Demo interaction-pattern matrix | **FULLY-LANDED** |

## Lane 1 — Protocol categorical analysis (ae8dc377)

**Deliverable:** `PROTOCOL-CATEGORICAL-ANALYSIS.md` covering 10
enumerated surfaces (cell lifecycle, effect taxonomy, authorization,
receipt/chain, federation, capability, predicate, storage, bridge,
time).

**Status: FULLY-LANDED.**

- File present at `/Users/ember/dev/breadstuffs/PROTOCOL-CATEGORICAL-ANALYSIS.md`,
  **2,424 lines**. (Within the 1500–2500 expected band.)
- All 10 surfaces covered as §§1–10 with proper section headers.
- §11 prioritized punch list is real: 11 Tier 1 primitives, 18 Tier 2,
  Tier 3 sweep, with a "grand total" rollup at §11.4.
- §12 meta-reflection ("bias toward creation", "bias toward bilateral")
  is substantive, not filler.
- §13 references back to the prior `CROSS-CELL-CATEGORICAL-ANALYSIS.md`
  lane and explicitly *excludes* its findings from the punch list to
  avoid double-counting — exactly the interleaving discipline the audit
  brief asked us to verify.
- No obvious skipped surfaces; the only thing missing is a §11 "what
  we'd build next" prioritization across lanes, but that wasn't part of
  the brief.

**Cross-lane interleaving note:** This file landed in checkpoint
`e03f9d37` alongside Lane 2's `cell/src/facet.rs`, Lane 3's
`cell/src/unilateral.rs`, Lane 5's demo files. No content overlap; the
checkpoint is a clean multi-lane snapshot.

**Next step (if anything):** none — done. If extending, add a §14
that cross-references the inter-lane priority for the next session.

## Lane 2 — Renunciation + Refusal + OneOf (a4f1f1f9)

**Status: PARTIAL-NEEDS-COMPLETION** — types & integration shipped,
adversarial coverage **uneven**.

### Renunciation — REAL

- `RenouncedSet` enum at `cell/src/program.rs:355`.
- `StateConstraint::Renounced { sender_attr, set }` at
  `cell/src/program.rs:779`, evaluated at line 1513.
- `NonMembershipNeighborProof` in `cell/src/predicate.rs` with
  `CONSECUTIVE_TAG` discipline.
- **5 adversarial tests** in `cell/src/program.rs` (lines 2785–2941):
  legal non-membership accepts, prover-in-set rejects, forged
  consecutive-tag rejects, missing-sender-ctx rejects, public-root
  slot binding.

### Effect::Refusal — STRUCTURALLY REAL, ADVERSARIAL-COVERAGE-LIGHT

- Variant defined `turn/src/action.rs:961`, with `RefusalReason` enum
  (`Declined`, `NoAuthority`, `WindowExpired`, `Custom { reason_hash }`).
- Hashing into action commitment: `action.rs:1801`.
- Cost accounting: `executor.rs:10539`.
- Audit-slot mutation guard (refusal must not co-occur with SetState):
  `executor.rs:7235`.
- Effect-tag: `dregg_cell::EFFECT_REFUSAL` registered at
  `cell/src/lib.rs:80`.
- **GAP:** no test in `turn/src/executor.rs` or `cell/src/`
  *constructs* `Effect::Refusal` to exercise the executor pathway.
  Coverage is structural (it compiles, hashes consistently, has cost
  table entries) but not behavioral.

### Authorization::OneOf — STRUCTURALLY REAL, ADVERSARIAL-COVERAGE-LIGHT

- Variant at `turn/src/action.rs:324` (with rich rustdoc about
  rejection rules).
- Executor rejection paths at `executor.rs:5812+`: out-of-bounds
  proof_index, Unchecked at indexed slot, nested OneOf at indexed
  slot.
- Cost recursion: `executor.rs:5216`.
- Cross-cell side path: `executor.rs:6533`, `10560`.
- **GAP:** no test in `turn/src/executor.rs` constructs
  `Authorization::OneOf { .. }` to validate any of the four rejection
  paths or the happy path. The defensive `if let` cascade at line 5812
  is **executor-side dead code from a test-coverage standpoint**.

**Next step:** In `turn/src/executor.rs` test module (line 13057+),
add three tests:

1. `fn one_of_rejects_out_of_bounds_proof_index()` — construct an
   `Authorization::OneOf { candidates: vec![Signature{..}],
   proof_index: 1, .. }`, expect `ExecutorError` mentioning "out of
   bounds".
2. `fn one_of_rejects_unchecked_indexed_slot()` — `candidates:
   vec![Unchecked, Signature{..}], proof_index: 0`, expect "Unchecked"
   rejection.
3. `fn refusal_records_audit_slot_mutation()` — submit an action
   containing `Effect::Refusal { cell, refusal_reason: NoAuthority,
   .. }`, assert receipt is produced AND the audit-slot mutation guard
   at `executor.rs:7235` blocks any co-occurring SetState in the same
   action.

## Lane 3 — Unilateral γ.2 binding (af3a0785)

**Status: FULLY-LANDED.**

- `cell/src/unilateral.rs` — **165 lines** exactly as checkpoint
  reports. Four `UnilateralAttestationKind` variants
  (`SelfStateTransition`, `SelfNonceBump`, `SovereignWitness`,
  `Custom { kind_tag }`), three canonical-message helpers
  (`self_state_transition`, `self_nonce_bump`, `sovereign_witness`),
  each with `cell_id`-bound BLAKE3 preimages.
- **4 adversarial tests** in-module:
  `canonical_preimages_include_cell_id` (forged-sender block),
  `self_state_transition_is_deterministic`,
  `nonce_bump_differs_per_nonce`, `sovereign_witness_differs_per_signature`.
- **PI layout in AIR**: `circuit/src/effect_vm.rs`:
  - Slot 168 `UNILATERAL_ATTESTATIONS_COUNT` (line 1054).
  - Slots 169–172 `UNILATERAL_ATTESTATIONS_ROOT[4]` (lines 1056–1057).
  - `MAX_UNILATERAL_ATTESTATIONS = 8` (line 1062).
  - Kind discriminants `UNILATERAL_ATTESTATION_KIND_*` (lines 1067–1073).
  - Pinned with assertions at lines 6229–6231.
- **Executor + verifier integration** (commit `08bae1fd`):
  `turn/src/bilateral_schedule.rs` exports
  `unilateral_pi_tag`, `unilateral_salt`,
  `ExpectedBilateral.unilateral_attestations` map (line 370), and
  `push_unilateral` builder (line 426). `TurnExecutor::verify_bilateral_bundle`
  was split so callers can populate per-cell attestations not derivable
  from `call_forest`. `WitnessedReceipt::verify_bilateral_chain_with_schedule`
  is the receipt-side entry.
- **Bilateral-parity check:** the bilateral path
  (Transfer/Grant/Introduce) and the unilateral path share the same
  per-cell schedule fold (`per_cell_expectations`); the unilateral
  side reuses the bilateral `count + root` PI-slot pattern. Parity is
  clean.

**Next step (if anything):** add a verifier-crate JSON-fixture test
demonstrating an off-AIR bundle with non-empty `unilateral_attestations`
parses + verifies. The on-AIR path is covered; the bundle-shape doc
exists; only the cross-crate fixture is missing. Surface:
`verifier/tests/` (new file).

## Lane 4 — Storage broader migration (af64a906)

**Status: MOSTLY-LANDED-MINOR-GAPS.**

- `dregg-storage-templates/` crate exists with all 5 modules
  (`blinded_queue.rs` 608, `cap_inbox.rs` 649, `programmable_queue.rs`
  672, `pubsub_topic.rs` 520, `relay_operator.rs` 656). Each is a
  real `FactoryDescriptor` + `CellProgram::Cases` impl with slot
  layouts, transition cases, turn-builders, and inspector
  descriptors. No `todo!()`/`unimplemented!()`.
- `lib.rs` exposes `all_storage_template_descriptors()` and verifies
  five-templates-present + distinct-factory-vks + deterministic-hash.
- **Per-module unit tests:** 11 / 11 / 11 / 8 / 10 across
  cap_inbox/blinded_queue/relay_operator/programmable_queue/pubsub_topic.
  (cap_inbox+blinded+programmable+relay each have 10+ tests; pubsub
  is slightly thinner at 8.)
- **`tests/adversarial.rs`** — 611 lines, 24 `#[test]`s. Real
  adversarial scenarios with shared `strip_witness_constraints`,
  `method_meta`, `u64_field`, `blake3_field` helpers.
- **Deprecation sweep on `storage/` parallel implementations:**
  `#[deprecated]` attributes present in
  `storage/src/{operator,blinded,programmable,inbox,pubsub,relay}.rs`
  — the migration story matches what the lib.rs docstring claims.

### Gaps

- `storage/src/{atomic,dataflow,erasure,multi_asset,namespace_mount,poly_queue,quota,sharding,metering,dedup}.rs`
  are **not yet retired or templated**. The audit brief asked
  whether anything in `storage/` still hasn't been migrated — yes,
  ~10 secondary modules. Most are not in §3.1–3.5 scope of
  STORAGE-AS-CELL-PROGRAMS.md (which only enumerates five
  templates), so this is "design-scope complete, full-storage-crate
  migration incomplete."
- `pubsub_topic` has only 8 tests vs. 10–11 for siblings — could
  benefit from cursor-rewind and subscriber-fork adversarial cases.

**Next step:** triage the un-deprecated `storage/src/` modules. For
the secondaries that should ALSO be templated (atomic, multi_asset
look like natural candidates), open a follow-up lane to extend
`dregg-storage-templates/` with 2–3 more reference templates. For the
ones that are protocol-substrate (metering, dedup) — add an
`#[allow(deprecated)]` carve-out doc in `storage/src/lib.rs` so the
migration story is honest about *what isn't on the cell-programs path*.

## Lane 5 — Demo interaction-pattern matrix (a88ed83b)

**Status: FULLY-LANDED.**

- `DEMO-INTERACTION-MATRIX.md` — 208 lines. 10 numbered categories
  matching §11.x sections of the matrix. Each row has explicit
  silver/multi/xapp/imatrix coverage symbols (`OK`/`PART`/`MISS`/`XAPP`).
  "Prioritized additions" §-end lists 5 items; items 1–4 are claimed
  shipped, item 5 (sealer/unsealer) explicitly deferred.
- **Helper subcommands shipped** (`demo/two-ai-handoff/silver_helper.rs`,
  1,490 lines): `slot-caveat-suite` at line 768, `make-credential-set-auth`
  at 992, `make-introduce` at 1044. Each produces a structured artifact
  JSON (`SlotCaveatSuiteArtifact`, `CredentialSetAuthArtifact`,
  `IntroduceArtifact`).
- **`charlie.py`** (361 lines) reads each artifact and exposes
  per-variant booleans:
  `slot_caveat_suite[Variant].{positive_ok, negative_rejected}`,
  `credential_set_{reproducible, distinct_schemas, distinct_issuers}`,
  `introduce_{schedule_has_one_introduce, bilateral_verified,
  bilateral_tampered_rejected}`.
- **`run.sh`** (425 lines) has step 4b that invokes each new
  subcommand, then a summary block that adds the new assertions to
  the `add_check` table and per-variant suite case loop.
- **`expected.json`** (85 lines) lists every new boolean in
  `must_pass` / `must_not_pass`, including all 5 slot-caveat-suite
  variants × {positive, negative} = 10 assertions, plus 3
  credential-set rows, plus 3 introduce rows.
- Tampered-bundle adversarial paths land for the new Introduce
  variant (`introduce_bilateral_tampered_bundle_accepted` in
  `must_not_pass`).
- Item 4 ("make-recursive-witness") from the lane's own
  prioritization is NOT visible in run.sh; it was either descoped or
  is still in helper-only state.

**Next step:** verify item 4 status — `grep make-recursive-witness
demo/two-ai-handoff/silver_helper.rs` to see if the subcommand exists
but isn't wired into run.sh, vs. wasn't implemented at all. If
implemented, add a step-4c block to run.sh.

## Workspace health

- **Git status:** clean modulo two concurrent agents.
  - **Staged:** `Cargo.lock` (+13 lines), `cell/src/peer_exchange.rs`
    (+1 line) — likely the houyhnhnm comparison agent.
  - **Unstaged:** `TOPLEVEL-MD-INDEX.md` (+2/-1),
    `turn/src/action.rs` (+/- 21 lines, structural). The action.rs
    edit moves `Effect::ValidateHandoff` from being nested inside
    `RefusalReason` (where it was syntactically misplaced — a previous
    bug) to its proper home inside `Effect`. This is the lifecycle
    agent. **Recommend leaving alone**; the diff is correct and the
    fix unblocks `RefusalReason` from accidentally inheriting a
    handoff-cert variant.
  - **Untracked:** `houyhnhnm.total.txt` (agent output file, ignore).
- **The 5 originally-dirty files from session-start gitStatus
  (`circuit/src/lib.rs`, `intent/src/lib.rs`, `intent/src/solver.rs`,
  `turn/src/executor.rs`, `wire/src/lib.rs`, plus untracked
  `intent/src/trustless.rs`, `wire/src/hardening.rs`) are all
  committed** — they rolled into checkpoints `b8c9e5b9` / `e03f9d37`
  / `803624dc`.
- **No compile hazards detected by eyeball:**
  - 0 `todo!()` / `unimplemented!()` in
    `cell/src/`, `turn/src/`, `circuit/src/`, lane deliverable
    crates.
  - The houyhnhnm `turn/src/action.rs` edit is structurally
    legitimate (moves a struct field that was inside the wrong enum
    out into the right one — a fix, not a regression).
  - The two `#[cfg(test)]` blocks at `executor.rs:12864` and
    `:13057` both have well-formed test fns; no truncated tests
    visible.

## Top 3 highest-leverage completion tasks

These are ranked by **coverage gain per LOC** for a targeted
follow-up agent:

1. **Lane 2 adversarial-test gap — 3 executor tests for OneOf +
   Refusal.** Estimated 60–120 LOC in `turn/src/executor.rs` test
   module. Closes the only honest gap in Lane 2 and turns it from
   "structurally real" into "behaviorally proven". One-shot job for
   a focused agent.

2. **Lane 5 item 4 (`make-recursive-witness`) — finish the demo
   chain.** If the helper subcommand exists but isn't wired into
   `run.sh`, this is a 30-line addition to step 4c + 3 booleans in
   `expected.json` + 1 charlie.py field. If it doesn't exist, it's
   the next priority demo-helper subcommand (~150–300 LOC in
   silver_helper.rs). Closes the only deferred sub-item in Lane 5's
   own prioritization.

3. **Lane 4 storage-secondaries triage.** ~10 modules in
   `storage/src/` that haven't been classified as
   "to-be-templated", "protocol-substrate-keep", or "fully-retire".
   A 30-minute audit reading each module's docstring + a single-PR
   policy doc (`STORAGE-SECONDARIES-TRIAGE.md`) finishes the
   migration story honestly. Probably worth two-template
   additions for `atomic.rs` and `multi_asset.rs` if they fit the
   `FactoryDescriptor` pattern.

## Honesty calls — checkpoint-commit theater vs. real work

- **Lane 1:** real. 2,424 lines of structured analysis.
- **Lane 2:** ~70% real. Types and integration are honest; tests
  are not.
- **Lane 3:** real. PI layout + executor split + verifier wiring + 4
  unit tests + 4 commits across `a541df9a`, `08bae1fd`. Easy to
  verify because each piece is in its expected place.
- **Lane 4:** ~85% real. Five templates are substantial; the
  "broader migration" framing oversells what landed (still ~10
  storage modules in the parallel implementation).
- **Lane 5:** real. The matrix is fleshed out, the helper
  subcommands exist with structured-artifact contracts, and the
  demo wiring goes all the way through `expected.json`.

The checkpoints `e03f9d37` (4,238 lines) and `b8c9e5b9` (5,348
lines) are dominated by *real shipped code*, not auto-generated
filler — the storage-templates crate alone is ~2,600 LOC of
hand-written cell programs. Nothing reads like checkpoint theater.
