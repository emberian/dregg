# Session 2026-05-25 — What Landed

One-page orientation for future agents / reviewers. The prior session
(2026-05-24) built the substrate. This session closed the soundness
emergency that audit surfaced, shipped lifecycle effects, grew the
integration test suite by ~200 tests, and wrote 20+ audit/study docs.

---

## Soundness emergency — closed

Four findings from `AIR-SOUNDNESS-AUDIT.md` (ce1e2def) were HIGH severity
and addressed immediately:

| Fix | Commit | SILVER-DEBT |
|---|---|---|
| Temporal AIR boundary: THRESHOLD + STATE_ROOT now bound into STARK PI | `df122d4c` | T1.5 CLOSED |
| NonMembership adjacency_tag: public `[0xFE;32]` sentinel replaced with commitment-derived tag | `5d557969` | T2.7 CLOSED (Silver-Sound) |
| `default_builtins()` switched from StubVerifier (accept-all) to NotYetWiredVerifier (reject-all) | `c86aecd7` | T2.8 CLOSED |
| `SetVerificationKey` now enforces `hash == blake3(data)` at apply time | `08e01ea7` | T1.3 partial |

---

## Receipt + VK foundation fixes

From `EXECUTOR-VK-AUDIT.md` P0/P1 findings:

| Fix | Commit | SILVER-DEBT |
|---|---|---|
| Executor signature widened to full receipt_hash (was missing 6 fields) | `e0fe3316` | T1.6 CLOSED |
| Proof-carrying path now emits real `effects_hash` / `action_count` (was stub zeros) | `57f2b041` | T1.7 partial |
| Custom-effect VK widened from 4 to 8 BabyBear felts; `expand_vk_hash_16_to_32` deleted | `46a886a5` | T3.3 CLOSED |
| block1-bind TODOs: queue/capability arms now read real ledger values | `9834b3d4` | T2.1+T2.2 CLOSED |
| Cclerk `append_receipt` enforces strict `previous_receipt_hash` matching | `83718782` | — |
| `AttestedRoot.receipt_stream_root` threaded through federation/node stand-ins | `aab40d37` | — |
| `ArchivalAttestation.archive_terminal_receipt_hash` bound to live head | `d5062590` | — |

---

## Lifecycle Effects

`Effect::LifecycleActivate`, `LifecycleSuspend`, `LifecycleTerminate`,
`LifecycleDestroy` shipped with an adversarial test suite covering
invalid state transitions and LocalSeat anchor (`f4a4fd17`). Cascaded
into exhaustiveness matches across `observability`, `demo`, and
`intent` crates (`4eca9d02`, `ac81ca6f`, `7b0f8e94`).

---

## Integration test suite (~200 new tests)

Per-layer audits produced targeted integration test files:

- `integration_lifecycle` — executor-boundary lifecycle turn tests (`55fd0513`)
- `integration_burn_receipt` — `Effect::Burn` + `was_burn` receipt binding (`d770f6ed`)
- `integration_attenuate_capability` — `Effect::AttenuateCapability` turns (`f151e494`)
- `integration_destroy_terminal` — cell-layer destroy terminal permanence (`0ebe6e56`)
- `integration_attestation_archive` — `ArchivalAttestation` + archive lifecycle (`954d32cd`)
- Starbridge-apps executor-invoking tests for all 4 apps (`d235a86b`)
- Intent/bridge integration suite — 40 tests (`e404a0af`)
- SDK/node/wire integration suite (`f49b732b`)
- Substrate integration suite — storage-templates, credentials, app-framework (`2f3d5977`)

---

## Monolith decompositions

- `executor.rs` (13,916 LOC, 14+ match-on-effect blocks): structural refactor
  partially underway — per-effect-family modules created for queue, capability, and
  handoff arms as part of the block1-bind closure. T3.1 (full split) remains open.
- `effect_vm.rs`: per-action schema files (`SCHEMA_BURN`, `bridge_lock_action_air`)
  separated out as the algebraic-invariant pattern scales. The monolith is not deleted
  but is being hollowed out from the well-understood edges.

---

## Audit and study documents (20+)

Written this session and indexed in `TOPLEVEL-MD-INDEX.md`:
`SILVER-DEBT.md`, `AIR-SOUNDNESS-AUDIT.md`, `EXECUTOR-VK-AUDIT.md`,
`RECEIPT-ARCHITECTURE-STUDY.md`, `HOUYHNHNM-COMPARISON.md`,
`HOUYHNHNM-DEEP-CRITIQUE.md`, `PROTOCOL-CATEGORICAL-ANALYSIS.md`,
`KIMI-DAMAGE-AUDIT.md`, `TEST-REALITY-AUDIT.md`, `MULTI-NODE-DEVNET-RUN.md`,
`PREV-SESSION-AUDIT.md`, `DEMO-INTERACTION-MATRIX.md`,
`STORAGE-SECONDARIES-TRIAGE.md`, `BLOCK1-BIND-CLOSURE-NOTES.md`,
plus nine per-layer test audit docs.

---

## What remains open (top items)

1. T1.2 — `TrustlessIntentEngine::new` still defaults to `with_stub_registry()`.
2. T1.4 / T2.8 — no in-tree host wires real verifiers for all 6 `WitnessedPredicateKind`s.
3. T2.3 — `ValidateHandoff` recipient/introducer pk placeholders.
4. T3.1 — `executor.rs` full per-effect-family split (structural enabler for T2.1–T2.4 remaining).
5. `coord::BudgetCoordinator` signature verification (two parked security bugs).
6. Storage primitive migrations Phase 1 + 2.
7. Morpheus retirement Block 6.

See `SILVER-DEBT.md` §1/§2/§3 for the full ledger.
