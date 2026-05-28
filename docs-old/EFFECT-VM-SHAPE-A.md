# `dregg` Codebase Remediation — Master Plan

## Status (as of 2026-05-24)

The remediation plan below was written early in the season; Stages 1-3
have largely landed (see `docs-history/STAGE-3-AIR-PLAN.md` for the
completed Stage-3 work). Subsequent design has moved onto higher
layers — see `STAGE-7-GAMMA-2-PI-DESIGN.md` (bilateral PI binding),
`SOVEREIGN-WITNESS-AIR-DESIGN.md`, `VK-AS-RE-EXECUTION-RECIPE.md`,
and `NEW-WORLD.md` (the current coherent picture). Treat this file as
the *origin* of the substrate work, not the live tracker.

Audit references in this document point to the original repo-root
filenames; the audits now live under `audits/` (see
`TOPLEVEL-MD-INDEX.md`).

---

**Status:** post-design-research. The Effect VM Shape A plan absorbed enough of the
codebase's coherence problems that this file is now the master plan for moving from
"The Mess" (2-day-old Opus 4.6 generation, multiple audits with P0s, build broken)
to "actually has a hope of correct."

**Companion design docs** (all in repo root, all ~2k–7k words):
- `DESIGN-pipelined-send.md` — OCapN-style eventual-send AIR variant
- `DESIGN-commitment-framework.md` — typed `Commitment<T>` framework, dual BLAKE3+Poseidon2
- `DESIGN-receipts.md` — sovereign/federation/bridge receipts, BLS ThresholdQC, IBC-style bridge phases
- `DESIGN-max-custom-effects.md` — per-cell with AIR sum-check as soundness prereq
- `DESIGN-dsl.md` — typestate `ActionBuilder`, four-layer tower, all 42 effects reachable
- `DESIGN-captp-integration.md` — 3 new committed Merkle roots, consume-on-use handoffs

**Companion audits** (also in root): `AUDIT-cclerk.md`, `AUDIT-sdk-rest.md`, `AUDIT-node.md`,
`AUDIT-extension.md`, `AUDIT-circuit.md`, `AUDIT-wasm.md`, `AUDIT-cell.md`,
`AUDIT-turn-executor.md`, `AUDIT-dsl.md`, `REVIEW-effect-vm.md`.

---

## What "correct" means here

The codebase is supposed to deliver:

1. **Capability-secure ocap semantics** — references confer authority; no ambient authority;
   no `Authorization::Unchecked` in framework code.
2. **STARK-verifiable state transitions** — every runtime `Effect` is enforced by AIR
   constraints; the proof attests to the *actual* turn, not a fictional projection.
3. **128-bit-secure commitments** — no 31-bit truncation; typed `Commitment<T>` with
   one-way BLAKE3↔Poseidon2 binding; identical canonical bytes across producers.
4. **Receipt chains that hold** — `previous_receipt_hash` enforced (executor side DONE);
   `Turn::hash()` covers all proof fields; bridge receipts with phase-locked semantics;
   federation receipts use real BLS aggregation.
5. **DSL that exposes all of this safely** — every runtime effect has a typed builder
   method; authorization is a typestate (not a string); intent → effect lowering is
   total, deterministic, order-preserving, and lives in one module.
6. **CapTP as a real feature** — not a stub. Swiss tables and handoff approvals live
   in committed Merkle roots; the wire layer and the executor agree on what state
   exists.

---

## The Mess, inventoried

(Each entry has a corresponding fix below. Cross-refs to audit findings.)

### Build & compile
- **B-1.** Repo doesn't compile: `sdk/cipherclerk.rs:6833,6850` `receive_local_delegation`
  signature mismatch — partial revert from concurrent agents. Blocks workspace check.

### Effect VM coherence
- **E-1.** 41 runtime `Effect` variants, 24 AIR variants; projection at
  `turn/src/executor.rs:1254` collapses 31 of 41 to `NoOp`.
- **E-2.** 7 runtime variants (`CreateObligation`, `FulfillObligation`,
  `SlashObligation`, `Seal`, `Unseal`, `MakeSovereign`, `CreateCellFromFactory`) have
  working AIR variants but the projection ignores them — pure plumbing bug.
- **E-3.** 23 runtime variants lack AIR coverage: escrow ×6, bridge ×4, delegation ×3,
  CapTP intro/pipelined send, plus `SetPermissions`, `SetVerificationKey`,
  `IncrementNonce`, `CreateCell`, `RevokeCapability`, `EmitEvent`, `CreateSealPair`,
  `ExerciseViaCapability`.
- **E-4.** 5 AIR-only orphans (`Custom`, `ExportSturdyRef`, `EnlivenRef`, `DropRef`,
  `ValidateHandoff`) — no runtime emitter, two of them (`ValidateHandoff`, `EnlivenRef`)
  are tautological even as constraints.
- **E-5.** `state_commitment` PI is 1 BabyBear (~31 bits); stored as `[u8;32]` but only
  bytes 0..4 are read. Birthday at ~50k cells.
- **E-6.** Three independent commitment schemes (cell, ledger, circuit) commit to
  different subsets of authority-bearing state.
- **E-7.** `MAX_CUSTOM_EFFECTS = 4` is documentary only — no AIR sum-check binds
  `s_custom` rows to `PI[CUSTOM_EFFECT_COUNT]`; a malicious prover with its own witness
  generator can declare any count.
- **E-8.** `net_delta` PI not algebraically bound to trace balance deltas.
- **E-9.** Various tautological AIR constraints: `Seal`/`Unseal` don't update sealed
  mask; `ValidateHandoff`/`EnlivenRef` prove `hash == hash`; `DequeueMessage` uses
  enqueue hash-chain (stack semantics); `AtomicQueueTx` is a one-row stub;
  `PipelineStep.pipeline_id` unbound; `ResizeQueue` wraps on shrink; `Transfer` only
  writes to `bal_lo`; `effects_hash` synthetic-high gives ~31-bit binding.

### DSL & app framework
- **D-1.** `app-framework/src/escrow.rs:95,155,207` `EscrowManager` ships every escrow
  turn with `Authorization::Unchecked`. All 6 escrow apps structurally unauthenticated.
- **D-2.** `ActionBuilder::new` defaults to `Unchecked` with no typestate forcing
  authorization (`turn/src/builder.rs:152`).
- **D-3.** 22 of 41 runtime effect variants are unreachable through any DSL surface.
- **D-4.** Three-way fragmentation: `Turn` vs `CompoundTurn` vs `Settlement`. No
  canonical authoring path. `TrustlessIntentEngine::finalize` produces `CompoundTurn`
  with no `→Turn` translation; `RingTradeParticipant::settle_leg` is app-specific not
  framework.
- **D-5.** `apps/gallery/src/settlement.rs:92,110` declares `balance_change` deltas that
  don't match `Transfer` amounts — conservation is advisory.
- **D-6.** `intent/src/solver.rs:328-332` has `.min(x).max(x)` that collapses to `x`.
- **D-7.** `sdk/src/cipherclerk.rs:2441` `build_authorized_turn` signs with hardcoded `nonce: 0`.
- **D-8.** `intent/src/lib.rs:535-536` epoch split has 1-bit overlap.
- **D-9.** Missing `RegisterName` effect; `apps/nameservice` emits no effects at all.

### Receipts
- **R-1.** `previous_receipt_hash` was unenforced — DONE in turn-executor fix; but
  **cclerk still hardcodes `None`**, so every non-first cclerk turn now rejects.
- **R-2.** `Turn::hash()` doesn't cover `execution_proof_new_commitment`,
  `execution_proof`, `sovereign_witnesses`, `conservation_proof`,
  `custom_program_proofs` — proof swap attack possible until `Turn::hash` bumps v2→v3.
- **R-3.** `BridgeReceipt` (`cell/src/note_bridge.rs:361`) is incomplete; no phase
  structure; no replay protection; no race-condition handling.
- **R-4.** `executor_signature` never set on `TurnReceipt`.
- **R-5.** Fast-path "signatures" used to be forgeable BLAKE3-keyed hashes — DONE in
  turn-executor fix.

### CapTP
- **C-1.** Wire layer (`wire/src/server.rs:2243-2350`) mutates `CapTpState` directly,
  bypassing the executor entirely. AIR variants exist but no runtime emitter exists.
- **C-2.** No `swiss_table_root` in `CellState`, no `approved_handoffs_root` in
  federation PI, no `refcount_table_root`. Without committed roots, the AIR variants
  *cannot* be made non-tautological.

### Circuit (non-Effect-VM)
- **K-1.** Kimchi backend's native gates have no copy constraints — gadget outputs are
  not bound to binding gates (`circuit/src/backends/kimchi_native/derivation.rs:280-528`).
- **K-2.** Kimchi backend deserializes `circuit_gates_bytes` from the proof itself;
  malicious prover embeds permissive gates (`circuit/src/backends/kimchi_native/mod.rs:198-223`).
- **K-3.** `MerkleStarkAir` is `#[deprecated]` and provably unsound, but live callers
  in `circuit/src/presentation.rs:1406, 2036`, `bridge/src/mina.rs:1172`,
  `demo/src/stark_proof.rs:51`, `wire/src/bin/demo.rs:358`.

### Node / extension / WASM
- (Per their audits — `AUDIT-node.md`, `AUDIT-extension.md`, `AUDIT-wasm.md`.)
- Includes the CRITICAL `/cipherclerk/set-passphrase` on `0.0.0.0` (node), CRITICAL
  unfiltered `chrome.runtime.onMessage` listeners (extension), P0s in WASM:
  stale pkg/, `seal_intent_body` derives key from plaintext, broken
  `derive_keypair_from_mnemonic`. Many already-applied edits sitting on working tree
  from parked fix opuses.

### Storage
- **S-1.** `storage/src/blinded.rs:329` self-admits "would use Poseidon2 in a real
  system." Multiple ad-hoc commitments throughout `storage/` should migrate to typed
  `Commitment<T>`.

---

## Stage decomposition

Stages are dispatched as individual opuses. Dependency edges are explicit; everything
without an explicit edge can run in parallel.

### Phase 0 — Unblock & immediate fixes

These are dispatched in **parallel** (no cross-crate writes). Plan files for the
parked opuses already exist at `~/.claude/plans/polished-tumbling-peacock-agent-*.md`.

| Stage | Crate | Work | Est | Deps |
|-------|-------|------|-----|------|
| **0a — SDK** | `sdk/` | Resolve **B-1**. Re-apply `cipherclerk.rs`/`verify.rs`/`captp_client.rs` edits clobbered by concurrent agents. Plumb `previous_receipt_hash` through `build_authorized_turn`, queue ops, atomic ops, etc. (mandatory after R-1 / executor fix). Re-apply runtime.rs SubAgent privatization. | 2d | — |
| **0b — Cell** | `cell/` | Pop stashed canonical-commitment work; commit. Finding 2 sealing (`Cell::id`, `public_key`, `token_id`, `CellState::balance`/`nonce`/`proved_state`/`delegation_epoch` sealed via `pub(crate)` + accessors). P1-2, P1-5, P1-6, P2-1, P2-2, P2-3 from `AUDIT-cell.md`. | 2d | — |
| **0c — Node** | `node/` | Adversarial tests for the already-applied F-CRIT-1/F-CRIT-2/F-P1-1..8/F-P2-1/F-P2-7 fixes. `cargo check`, `cargo test`. Commit. | 1d | — |
| **0d — Extension** | `extension/` | Re-apply 4 missing items (P1-4 settings host-change, P2-1 `build.sh`, P2-2 sourcemap-off, P2-4 recovery clipboard). Add `extension/tests/e2e/popup-security.spec.ts` adversarial tests for the 5 popups. Rebuild `dist/` via Docker (`node:20-alpine`). | 2d | — |
| **0e — WASM** | `wasm/` | Adversarial tests for already-applied P0/P1 fixes. Consumer updates in `extension/background.js` and `site/playground/sections/*` for the new bearer-cap signature/pubkey shape. Defer `pkg/` rebuild (gated on a workspace-wide wasm32 cargo cleanup; out of scope). | 1.5d | — |
| **0f — Escrow auth** | `app-framework/` | Replace every `Authorization::Unchecked` in `app-framework/src/escrow.rs:95,155,207` with explicit `Authorizer` injected via constructor. Add CI grep-guard for `Authorization::Unchecked` in `app-framework/src/`. Update affected escrow apps. | 1d | — |
| **0g — Circuit (rescoped)** | `circuit/` | Fix **K-1** (kimchi copy constraints), **K-2** (kimchi gate-deserialization), **K-3** (`MerkleStarkAir` callers migrate to a sound variant). Do **NOT** touch Effect VM (`circuit/src/effect_vm.rs`) — that's Stage 1+. | 3d | — |

Wallclock: ~2–3 days (longest pole: extension or circuit).

### Phase 1 — Foundation

| Stage | Crates | Work | Est | Deps |
|-------|--------|------|-----|------|
| **1 — Commitment & projection foundation** | `cell/`, `circuit/`, `turn/`, `sdk/` | (a) Adopt `cell::commitment::compute_canonical_state_commitment` workspace-wide. (b) Introduce typed `Commitment<T>` / `Commitment4<T>` / `Accumulator<T>` / `MerkleRoot<T>` per `DESIGN-commitment-framework.md`. (c) Widen Effect VM PI: `OLD_COMMIT[4]`, `NEW_COMMIT[4]`, `EFFECTS_HASH[4]`, `NET_DELTA_MAG_LO`/`HI` (2 BabyBears), `NET_DELTA_SIGN`, plus `CURRENT_BLOCK_HEIGHT` (new). (d) Replace `commitment_to_babybear` / `hash_to_bb` / `field_element_to_bb` with full-width Poseidon2 hashing. (e) Add cell-state fields: `max_custom_effects: u8`, `swiss_table_root`, `refcount_table_root` (CapTP prep — values can be `Commitment::empty()` until Stages 7+). (f) Add federation-state field `approved_handoffs_root`. (g) Rewrite `convert_turn_effects_to_vm` to be **total**: every runtime variant maps. For variants not yet in AIR (the 23 from E-3), the projection emits a tagged "pending" entry that contributes to `effects_hash` but logs an error and is gated behind a workspace feature flag (production cclerk doesn't have it). Mirror in cipherclerk's `convert_effects_to_vm`. (h) Resolve `REVIEW[effect-vm-coord]` markers from turn-executor fix. | 4d | 0a, 0b |
| **2 — AIR honesty pass** | `circuit/` | Fix every existing-24 tautological/wrapping/unbound constraint. Specifically: `Seal`/`Unseal` actually update `sealed_field_mask` (now a proper trace column not packed into `reserved`); `SetField` reads the mask. `ValidateHandoff` does real Merkle membership against `approved_handoffs_root` (PI) — leaf consumed on use. `EnlivenRef` does real Merkle membership against `swiss_table_root` (PI). `DropRef` binds `holder_federation` to `refcount_table_root` key. `DequeueMessage` real FIFO with head/tail pointers. `AtomicQueueTx` decomposed into N sub-rows with per-op composition constraint. `PipelineStep.pipeline_id` bound to committed pipeline registry root. `ResizeQueue` range-checked delta. `MakeSovereign` mode_flag booleanity + once-only. `Transfer` widened to full u64 (`bal_lo` + `bal_hi`). `effects_hash` becomes Poseidon2-4 directly (drop synthetic `hi`). `custom_count` sum-check `Σ s_custom == PI[CUSTOM_EFFECT_COUNT]`. `net_delta` per-row binding to `(state_after.bal - state_before.bal)`. `CreateObligation` binds beneficiary into cap_root. | 5d | 1 |

### Phase 2 — Parallel build-out (after Stage 1)

These run in parallel after Stage 1; no shared writable region beyond their crate slice.

| Stage | Work | Est | Deps |
|-------|------|-----|------|
| **3 — Group A+B AIR variants** | `IncrementNonce`, `EmitEvent`, `SetPermissions`, `SetVerificationKey`, `RevokeCapability`, `CreateSealPair`, `Introduce`, `PipelinedSend` (per `DESIGN-pipelined-send.md` — one variant with internal branching), `PipelinedSendResolved` if needed. | 4d | 1 |
| **4 — Group C AIR variants + `ExerciseViaCapability`** | `CreateCell`, `SpawnWithDelegation`, `RefreshDelegation`, `RevokeDelegation`, `ExerciseViaCapability` (probably a 2-row variant for the c-list lookup + sub-action). | 4d | 1 |
| **5 — Group D AIR variants (escrow ×6)** | `CreateEscrow`, `ReleaseEscrow`, `RefundEscrow`, `CreateCommittedEscrow`, `ReleaseCommittedEscrow`, `RefundCommittedEscrow`. Each needs condition_hash binding, timeout vs `CURRENT_BLOCK_HEIGHT` witness, beneficiary commitment. New `escrow_root` cell-state column. | 5d | 1 |
| **6 — Group E AIR variants (bridge ×4)** | `BridgeMint`, `BridgeLock`, `BridgeFinalize`, `BridgeCancel`. Receipt format per `DESIGN-receipts.md` §5 (shared envelope + 4 phase-payloads, `bridge_id` join key, safety-margin race defense). New `bridge_state_root` if needed for in-flight bridges. | 6d | 1 |
| **7 — CapTP runtime emitters + AIR fixes** | Per `DESIGN-captp-integration.md`: 4 new runtime `Effect` variants (`ExportSturdyRef`, `EnlivenRef`, `DropRef`, `ValidateHandoff`); wire-layer alignment to go through executor not direct `CapTpState` mutation; consume-on-use for handoff certs; the 3 new Merkle roots are populated. AIR-side tautology fixes for these landed in Stage 2; this stage adds the runtime emitter side. | 5d | 1, 2 |
| **8 — DSL phased rollout** | Per `DESIGN-dsl.md` §A–G. **8a** typestate `ActionBuilder`. **8b** four-layer tower `Intent → EffectPlan → SealedTurn → Turn` with `dregg_intent::lowering`. **8c** all 42 typed `effect_*` methods. **8d** conservation derived (delete `balance_change` from user API). **8e** four auth modes first-class. **8f** app-framework `Authorizer`-required constructors. **8g** delete `CompoundTurn`/`SettlementAction`; integrate `trustless.rs`. Add `RegisterName` effect. Fix `apps/nameservice`, `apps/privacy-voting`. Closes audit findings 1, 3–9, 12–15, 18–20. | 8d | 1 |
| **9 — Receipts overhaul** | Per `DESIGN-receipts.md` §8. Bump `Turn::hash` v2→v3 covering proof fields (resolves R-2). Adopt BLS `ThresholdQC` (federation/threshold.rs) as the federation receipt QC. Full `BridgeReceipt` struct + 4 phase payloads. `executor_signature` actually set. End-to-end receipt chain crosses fed boundaries. | 5d | 1 |
| **10 — Storage Poseidon2 migration** | `storage/src/blinded.rs` + ad-hoc `storage/` commitments migrate to `Commitment<T>` typed forms. Aligns with `DESIGN-commitment-framework.md` migration plan. | 2d | 1 |

### Phase 3 — Convergence (after Phase 2)

| Stage | Work | Est | Deps |
|-------|------|-----|------|
| **11 — Integration tests** | End-to-end: a turn emitting one of each of the 42 runtime effects, proving via Effect VM, verifying. Adversarial: prover declares wrong `net_delta` → rejected. Prover swaps proof keeping signature → rejected. Bridge phase-1→3 happy path. CapTP handoff happy path + double-redeem rejected. | 3d | 3–10 |
| **12 — Doc & ship** | Update `DREGG_DESIGN.md` (currently misrepresents the system); update `docs/turn-execution-model.md`; write a short `MIGRATION.md` for app authors. | 1d | 11 |

---

## Wallclock estimate

If Phase 0 parallelizes fully: ~3d. Phase 1 sequential: ~5–6d (Stage 1 then Stage 2).
Phase 2 parallelized: ~6d (longest pole: Stage 6 bridge + Stage 8 DSL). Phase 3: ~4d.

**Total: ~18–20 days wallclock**, ~50 days of sequential opus work.

---

## Dispatch policy (lessons from prior swarms)

1. **No worktree isolation.** Branch from local HEAD, not origin/main. Per
   `~/.claude/projects/-Users-ember-dev-breadstuffs/memory/feedback-no-worktree-isolation.md`.
2. **Concurrent cargo failures**: 60s sleep + retry, not rollback.
3. **No npm direct** — Docker for any node/npm ops. Per
   `~/.claude/projects/-Users-ember-dev-breadstuffs/memory/feedback-avoid-npm-direct.md`.
4. **Plan files persist** at `~/.claude/plans/polished-tumbling-peacock-agent-*.md`.
   Redispatch agents with these as input rather than starting from scratch.
5. **Cross-crate stages get one opus** even if large. Within-crate stages can be one
   opus or a tight swarm; explicit dependency edges only.
6. **Verify-then-claim** policy (per
   `~/.claude/projects/-Users-ember-dev-breadstuffs/memory/feedback-verify-agent-claims.md`).
   Don't trust agent self-reports without spot-checking.

---

## Open decisions still needed

- **PipelinedSend replay protection v2** — `DESIGN-pipelined-send.md` defers per-promise
  sequence numbers to v2. OK?
- **Bridge committee rotation** — `DESIGN-receipts.md` proposes `committee_epoch` hook.
  Concrete rotation cadence?
- **CapTP federation boundary** — intra-fed CapTP is straightforward; inter-fed CapTP
  is essentially a bridge. Is that an explicit Stage 7b later, or do we want it in
  Stage 7 now?
- **`Permissions::open()`** — turn-executor fix marked it WONTFIX (P1-4). Confirm we
  keep this for test cells?
