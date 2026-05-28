# CAVEAT-LAYER-COVERAGE — three-layer audit of slot caveats, token caveats, and Effect-VM AIRs

**Date:** 2026-05-24. **Status:** read-only audit. **Scope:** every variant of
`cell::program::StateConstraint`, every variant of `turn::action::Effect`, and
the rendezvous between `cell` / `turn` / `token` / `circuit`.

This document answers the designer's three questions:

1. Does the executor implement *all* of the `StateConstraint` variants?
2. Are they all supported by the `./token` crate's caveat vocabulary
   (biscuit/macaroon-ancestry)?
3. What about the other effects in `./circuit` — is the Effect-VM AIR
   encoding faithful or does it use truncations / placeholders?

The headline is: **the slot-caveat surface is broader than any single
enforcement layer**, the token crate is a *disjoint* caveat language
(not a subset / superset of `StateConstraint`), and the Effect-VM AIR
encoding is honest for ~22 effects while ~6 variants still rely on
4-byte hash truncations or hard-coded zero placeholders (`queue_len:
0`, `permissions: ZERO`, `current_refcount: 1`, …).

For each `StateConstraint` variant the table column **fixed-by-in-flight**
identifies whether the in-flight *caveat-correctness* lane (agent
`a693478bed4899803`, doing multi-cell evaluation + `EvalContext` wiring
+ operation-scoped cases + Effect-VM projection tightening) is expected
to close the gap.

---

## §0 — Map of the four layers

| Layer | File | Role |
|---|---|---|
| **Cell declaration** | `cell/src/program.rs` (StateConstraint, 21+ variants), `cell/src/preconditions.rs` (EvalContext), `cell/src/predicate.rs` (WitnessedPredicate + registry), `cell/src/capability.rs` (CapabilityCaveat) | Authors declare what shape a cell program's perpetual invariants take. Single closed lifted enum + escape hatch (`Custom`). |
| **Executor enforcement** | `turn/src/executor.rs::execute_tree` (around lines 4343–4393) | At runtime, post-effect, calls `target_cell.program.evaluate(new_state, old_state, Some(&ctx))`. The ctx is constructed at lines 4361–4373 with partial fidelity (see §2). |
| **Token caveats** | `token/src/dregg_caveats.rs` (15 `DreggGrant` variants), `macaroon/src/caveat.rs` (`CaveatType` ID space) | Macaroon/biscuit-ancestry authorization for tokens (orgs / apps / services / OAuth scopes / budgets / revocable). **Disjoint** vocabulary from `StateConstraint` — see §3. |
| **Circuit AIR** | `circuit/src/effect_vm.rs` (Effect VM), `circuit/src/predicate_program.rs` (separate predicate AIR language), `circuit/src/temporal_predicate_dsl.rs`, `circuit/src/note_spending_air.rs`, `circuit/src/predicate_air.rs`, `circuit/src/compound_predicate_air.rs`, `circuit/src/effect_vm_p3_air.rs` | The per-effect AIRs proving that a turn was executed correctly. No AIR directly enforces a `StateConstraint` today (the per-cell `Circuit` program path is the escape hatch). |

The four layers share NO common type beyond `WitnessedPredicate` (which `cell`
exposes and which the executor's `WitnessedPredicateRegistry` is *intended*
to dispatch through, but the executor's program-evaluation site does NOT
intercept the `WitnessedPredicateRequiresExecutor` sentinel today — see §2).

---

## §1 — Per-variant table: 21 `StateConstraint` variants × 4 layers

Legend:

- **Cell** column: ✅ enum variant present + evaluator hook in
  `evaluate_constraint`; ⚠ present but evaluator returns a sentinel
  (`Witnessed/Custom/TemporalPredicate/BoundDelta` all return an error
  the executor is supposed to intercept — but does not).
- **Exec** column: ✅ exec evaluates this variant with a non-trivial
  `EvalContext`; ⚠ exec evaluates but supplies placeholder context
  (e.g. `sender_epoch_count: 0`); ❌ exec REJECTS this variant
  unconditionally because the program-evaluator returns a sentinel
  the executor doesn't catch and the resulting `ProgramError` is
  surfaced verbatim as `TurnError::ProgramViolation`.
- **Token** column: ✅ a structurally-equivalent token caveat type ID
  exists; ❌ the token caveat language is silent on this concept.
- **AIR** column: ✅ a direct AIR enforces this variant; 🟡 a
  *related* AIR exists but is not wired (`temporal_predicate_dsl`,
  `predicate_air` are unwired); ❌ no AIR exists for this variant.
- **In-flight** column: ✅ the caveat-correctness lane is expected to
  close this gap; ❌ requires a separate workstream.

| # | Variant | Cell | Exec | Token | AIR | In-flight |
|---|---|---|---|---|---|---|
| 1 | `FieldEquals { index, value }` | ✅ | ✅ static | ❌ no analogue | ❌ no per-slot AIR | n/a — works |
| 2 | `FieldGte { index, value }` | ✅ | ✅ static | ❌ | ❌ | n/a |
| 3 | `FieldLte { index, value }` | ✅ | ✅ static | ❌ | ❌ | n/a |
| 4 | `SumEquals { indices, value }` | ✅ | ✅ static (overflow-checked) | ❌ | ❌ | n/a |
| 5 | `WriteOnce { index }` | ✅ | ✅ exec checks `old_state.fields[i] == ZERO ‖ unchanged` | ❌ | ❌ | n/a |
| 6 | `Immutable { index }` | ✅ | ✅ exec compares old vs new | ❌ | ❌ | n/a |
| 7 | `Monotonic { index }` | ✅ | ✅ `new ≥ old` (big-endian byte compare) | ❌ | ❌ | n/a |
| 8 | `StrictMonotonic { index }` | ✅ | ✅ `new > old` strictly | ❌ | ❌ | n/a |
| 9 | `BoundedBy { index, witness_index }` | ✅ | ✅ exec checks witness slot non-zero on transition | ❌ | ❌ | n/a |
| 10 | `FieldDelta { index, delta }` | ✅ | ✅ wrapping u64 arithmetic on last-8-bytes lane | ❌ | ❌ | n/a |
| 11 | `FieldDeltaInRange { index, min, max }` | ✅ | ✅ `[old+min, old+max]` bounds check | ❌ | ❌ | n/a |
| 12 | `FieldGteHeight { index, offset }` | ✅ | ⚠ exec passes `block_height` honestly, but the receipt-snapshot replay path (`SLOT-CAVEATS-EVALUATION.md` finding 3) is NOT wired — replayers re-evaluate against their own chain | ❌ (token `ValidityWindow` is *time*, not block height) | ❌ | ✅ (snapshot wiring lane) |
| 13 | `FieldLteHeight { index, offset }` | ✅ | ⚠ same as #12 | ❌ | ❌ | ✅ |
| 14 | `SumEqualsAcross { in, out }` | ✅ | ✅ exec sums old/new with overflow checks | ❌ | ❌ | n/a |
| 15 | `SenderAuthorized { set: PublicRoot \| BlindedSet }` | ✅ | ⚠⚠ **Cell-side evaluator is purely structural**: it only verifies that `ctx.sender` exists and the `set_root_index` is in range. **The Merkle / blinded-set non-revocation check is the executor's authorization layer's job and is NOT plumbed through this code path** (lines 901–919 of `cell/src/program.rs`). | ❌ (token `ConfineUser` is a different shape — single-user, not set-membership) | ❌ (BlindedSet has a target AIR via `circuit::accumulator_air::AccumulatorNonMembership`, but the slot-caveat path doesn't dispatch to it) | ✅ (caveat-correctness lane will dispatch BlindedSet to `WitnessedPredicateRegistry`) |
| 16 | `CapabilityUniqueness { cap_set_root_slot }` | ✅ | ⚠ structural only — exec checks slot index validity and returns Ok. No actual NFT-uniqueness check on the cap-set root commitment shape. Per the variant's own rustdoc, "Executor-side enforcement is a structural check on the cap-set root commitment; the variant exists so the constraint declaration is first-class." | ❌ | ❌ | ❌ (needs cap-set Merkle uniqueness gadget — out of caveat-correctness scope) |
| 17 | `RateLimit { max_per_epoch, epoch_duration }` | ✅ | ⚠⚠ **executor.rs supplies `sender_epoch_count: 0` as a hard-coded placeholder** (executor.rs:4371). The cell-side check `ctx.sender_epoch_count >= max_per_epoch` therefore *always passes* unless caller-supplied context says otherwise — which the executor never does. | ❌ (token `Budget` is structurally similar but counts API calls, not cell mutations) | ❌ | ✅ (caveat-correctness lane wires the per-(cell, sender, epoch) counter) |
| 18 | `RateLimitBySum { slot_index, max_sum_per_epoch, epoch_duration }` | ✅ | ⚠ exec evaluates as a per-turn delta-bound (last-8-bytes lane), NOT as a running per-window sum. The `epoch_duration` field is ignored. Per the evaluator's own comment ("Window-sum is supplied through the per-(cell, slot, window) running sum tracked by the executor…that pre-aggregated value comes in via `ctx.sender_epoch_count` repurposed as the running per-window sum when the executor wires this variant. Until then, evaluate the delta-bound directly: the per-turn increment must not exceed the cap.") | ❌ | ❌ | ✅ |
| 19 | `TemporalGate { not_before, not_after }` | ✅ | ✅ exec compares `ctx.block_height` against bounds (this is the one contextual variant whose ctx field IS supplied honestly — `self.block_height` line 4364). | ⚠ shape-similar to token `CAV_VALIDITY_WINDOW` (id 5), but token uses unix-time and TemporalGate uses block-height — units are incompatible. | ❌ | n/a |
| 20 | `PreimageGate { commitment_index, hash_kind }` | ✅ | ⚠⚠ **executor.rs supplies `revealed_preimage: None`** (line 4372), so this variant ALWAYS surfaces `MissingContextField { field: "revealed_preimage" }`. There is no plumbing from `action.witness_blobs` (where `WitnessKind::Preimage32` blobs live, per `turn/src/action.rs:171`) to the cell-program evaluator. Additionally, `HashKind::Poseidon2` is a **stub** that BLAKE3-hashes a tagged buffer rather than calling Poseidon2 (cell/src/program.rs:1014-1022). | ❌ | 🟡 (Poseidon2-on-bytes gadget exists in `circuit::poseidon2`; not wired here) | ✅ (caveat-correctness lane wires preimage from witness_blobs) |
| 21 | `MonotonicSequence { seq_index }` | ✅ | ✅ exec checks `new == old.wrapping_add(1)` on the last-8-bytes lane | ❌ | ❌ | n/a |
| 22 | `AllowedTransitions { slot_index, allowed }` | ✅ | ✅ exec checks `(old, new)` is in allow-list | ❌ | ❌ | n/a |
| 23 | `TemporalPredicate { witness_index, dsl_hash }` | ⚠ | ❌❌ **exec REJECTS unconditionally** — the cell evaluator always returns `Err(TemporalPredicateWitnessMissing { dsl_hash })` (cell/src/program.rs:1072-1080). The executor at executor.rs:4374-4387 surfaces this verbatim as `TurnError::ProgramViolation`. **No interception, no dispatch to `circuit::temporal_predicate_dsl::verify_temporal_predicate`.** Per the variant's rustdoc the executor "invokes" the verifier; in reality it doesn't. | ❌ | 🟡 `temporal_predicate_dsl::verify_temporal_predicate` and `P3TemporalPredicateProof` exist and work end-to-end in standalone tests; they are simply not wired from the cell-program path | ✅ |
| 24 | `BoundDelta { local_slot, peer_cell, peer_slot, delta_relation }` | ⚠ | ❌❌ **exec REJECTS unconditionally** — cell evaluator returns `Err(BoundDeltaNotWired { peer_cell })`. The γ.2 cross-cell match loop exists in `turn/src/bilateral_schedule.rs` and `circuit/src/bilateral_aggregation_air.rs`, but the cell-program evaluator never gets the peer cell's state, so cross-cell BoundDelta caveats currently break any cell that declares them. | ❌ | 🟡 `circuit::bilateral_aggregation_air` exists for the aggregate γ.2 match; per-cell hookup missing | ✅ (multi-cell-eval portion of the lane) |
| 25 | `AnyOf { variants: Vec<SimpleStateConstraint> }` | ✅ | ✅ exec lifts each Simple variant and tries each; returns Ok on first success. The `SimpleStateConstraint` set is intentionally restricted (no nested AnyOf, no Custom) per eval §4.3. | ❌ | ❌ | n/a |
| 26 | `Witnessed { wp: WitnessedPredicate }` | ⚠ | ❌❌ **exec REJECTS unconditionally** — cell evaluator returns `Err(WitnessedPredicateRequiresExecutor { kind_name })`. The `WitnessedPredicateRegistry` exists in `cell/src/predicate.rs:412-490` with stubs (`with_stubs()`) and a `register_builtin` / `register_custom` shape, but **the executor's call site at executor.rs:4343-4393 does not consult any registry** — the sentinel just propagates to `TurnError::ProgramViolation`. So `Witnessed` cell programs are uncreatable in practice. | ❌ | 🟡 The seven `WitnessedPredicateKind` algebras (Dfa, Temporal, MerkleMembership, BlindedSet, BridgePredicate, PedersenEquality, Custom) all have AIRs in `circuit/src/dsl/circuit.rs:1711-1941` (Dfa), `temporal_predicate_dsl` (Temporal), `merkle_air` (MerkleMembership), `accumulator_air` (BlindedSet via non-membership), `predicate_air` / `compound_predicate_air` (Bridge), `committed_threshold` (Pedersen). None are wired through the cell-program path. | ✅ |
| 27 | `Custom { ir_hash, descriptor, reads }` | ⚠ | ❌❌ **exec REJECTS unconditionally** — cell evaluator returns `Err(CustomConstraintUnevaluable { ir_hash })`. No DSL-IR-runtime lookup is wired. The `dregg-dsl-runtime` crate exists; the executor doesn't reach it from the program-evaluation path. | ❌ | ❌ (this is the open escape — by design no AIR is preregistered, but the dispatch path is also absent) | ❌ (out of caveat-correctness scope; tracked separately) |

**Tally:**

- **Honest end-to-end (no in-flight needed):** 13 variants (FieldEquals,
  FieldGte, FieldLte, SumEquals, WriteOnce, Immutable, Monotonic,
  StrictMonotonic, BoundedBy, FieldDelta, FieldDeltaInRange, SumEqualsAcross,
  TemporalGate, MonotonicSequence, AllowedTransitions, AnyOf) — count: 16.
- **Evaluated with placeholder/unwired context:** 4 variants (FieldGteHeight,
  FieldLteHeight, RateLimit, RateLimitBySum) plus structural-only
  (SenderAuthorized, CapabilityUniqueness, PreimageGate) = 7.
- **Hard-rejected (sentinel pass-through):** 4 variants
  (TemporalPredicate, BoundDelta, Witnessed, Custom).

The 4 hard-rejected variants are codex's flagged P0 #2 — they exist in
the cell-program schema but any cell that *uses* them cannot execute a
turn at all, because the executor surfaces the sentinel as
`TurnError::ProgramViolation`.

---

## §2 — `EvalContext` build site honesty audit

The executor builds the slot-caveat context at `turn/src/executor.rs:4361-4373`:

```text
let ctx = dregg_cell::EvalContext {
    block_height: self.block_height,                    // HONEST
    timestamp: self.current_timestamp,                  // HONEST
    current_epoch: self.block_height.saturating_div(1024), // HEURISTIC — no epoch oracle yet
    sender: parent_pk_opt,                              // HONEST (parent cell's pk)
    sender_epoch_count: 0,                              // PLACEHOLDER — always zero
    revealed_preimage: None,                            // PLACEHOLDER — witness_blobs not consulted
};
```

Out of the six `EvalContext` fields:

- **2 honest:** `block_height`, `timestamp`.
- **1 honest-ish:** `sender` (uses parent cell's pubkey).
- **1 heuristic:** `current_epoch` (height/1024; no oracle).
- **2 placeholder:** `sender_epoch_count` (always 0), `revealed_preimage`
  (always None).

**Consequence:**

- `RateLimit` always passes when ctx is supplied (because `0 >= max_per_epoch`
  is false for any positive cap).
- `PreimageGate` always returns `MissingContextField { field:
  "revealed_preimage" }`, so any cell declaring it cannot transition.

The lane named *caveat-correctness* (agent `a693478bed4899803`) is
chartered to plumb `sender_epoch_count` (from a per-(cell, sender, epoch)
counter the executor would maintain) and `revealed_preimage` (from
`action.witness_blobs` of `WitnessKind::Preimage32`) into the context.

The `Preconditions` evaluation site at `turn/src/executor.rs:4456-4471`
is *worse* — it uses `EvalContext { block_height, timestamp,
..Default::default() }`, so every Lane-G contextual field is at its
default (None/0). This is fine for the precondition surface as it stands
because the precondition evaluator only reads `block_height` /
`timestamp` (per `cell/src/preconditions.rs::NetworkPrecondition::evaluate`),
but it means `Preconditions::witnessed` clauses are dead code at the
executor today.

---

## §3 — Token-crate caveats vs slot caveats: disjoint vocabularies

The token crate's caveat surface (`token/src/dregg_caveats.rs`, IDs 0–15
plus reserved 254/255) is **biscuit/macaroon-ancestry authorization**:

| Token caveat | Concept | Closest `StateConstraint` |
|---|---|---|
| `CAV_ORGANIZATION` (u64) | request must match org-id | no analogue |
| `CAV_APP` (id, actions) | app-scoped grant + RWCD action mask | no analogue |
| `CAV_SERVICE` (name, actions) | service-scoped grant | no analogue |
| `CAV_FEATURE` (str) | feature flag membership | no analogue |
| `CAV_VALIDITY_WINDOW` (nb, na) | unix-time window | **shape-similar** to `TemporalGate { not_before, not_after }` but units differ (s vs blocks) |
| `CAV_CONFINE_USER` (str) | single-user binding | **shape-similar** to `SenderAuthorized { set: PublicRoot/BlindedSet }` but token's is *one user* (the macaroon's `confined_users`), not a set commitment |
| `CAV_OAUTH_PROVIDER` (str) | OAuth provider name | no analogue |
| `CAV_OAUTH_SCOPE` (str) | OAuth scope | no analogue |
| `CAV_FROM_MACHINE` (str) | machine-id binding | no analogue |
| `CAV_COMMAND` (str) | command-name binding | no analogue |
| `CAV_FEATURE_GLOB` (inc, exc) | feature glob include/exclude | no analogue |
| `CAV_BUDGET` (id, parent, class, limit, window) | request-cost budget enforcement | **shape-similar** to `RateLimit { max_per_epoch, epoch_duration }` but token measures API-call cost, slot-caveat measures cell mutations |
| `CAV_REVOCABLE` (svc) | revocation channel | no analogue |
| (caveat IDs 3, 6, 7 reserved) | — | — |
| `CAV_THIRD_PARTY` (254) | third-party caveat shape | no analogue (slot-caveats have no third-party mechanism) |
| `CAV_BIND_TO_PARENT` (255) | macaroon binding | no analogue |

**Findings:**

- The token caveat vocabulary is for **authorization-on-a-request**
  (a token grants/restricts an API/service call). `StateConstraint` is
  for **invariants-on-a-cell** (perpetual rules on slot transitions).
  They are deliberately disjoint surfaces.
- The three shape-similar pairs (TemporalGate↔ValidityWindow,
  SenderAuthorized↔ConfineUser, RateLimit↔Budget) do NOT map onto each
  other in code today, and unifying them would require an `EvalContext`
  that's *also* an authorization context (unix-time + user-id + budget
  state). The `cell::CapabilityCaveat` type (`cell/src/capability.rs:30-40`)
  is the staging point for such a future unification, but it ships only
  the `FacetConstraint` and `Witnessed(WitnessedPredicate)` variants —
  it does NOT yet expose ValidityWindow/Budget/etc.
- The macaroon `CaveatType` ID space (`macaroon/src/caveat.rs:24-45`)
  reserves 0..31 for platform, 32..47 for user-registerable, 48..253
  for user-defined. None of these IDs are mapped to a `StateConstraint`
  variant. If the platform wanted slot-caveat-shaped tokens, the
  closest precedent is `WitnessedPredicateKind::Custom { vk_hash }` in
  the predicate registry — but the registries are separate.

**Gap:** the `PREDICATE-INVENTORY` doc §3.5/§7.6 envisioned
`CapabilityCaveat` carrying witness-attached predicates that gate cap
exercise, but the executor's `verify_authorization` path
(executor.rs:4489+) does not consult `CapabilityCaveat::Witnessed` on
the actor's cap-list entries; cap caveats are declared but unenforced.
The `FacetConstraint` half is enforced via the `allowed_effects: EffectMask`
shortcut on `CapabilityRef`.

---

## §4 — `Effect` enum × Effect-VM AIR coverage

The `Effect` enum (`turn/src/action.rs:393-843`) has **52 variants**.
The Effect-VM AIR `Effect` enum (`circuit/src/effect_vm.rs:893-1207`)
has **34 variants** (a subset/projection of the runtime ones). The
projection function is
`turn::executor::TurnExecutor::convert_turn_effects_to_vm`
(`turn/src/executor.rs:2400-3092`).

Categorization for each runtime variant:

| Runtime variant | Executor handler | AIR projection | AIR encoding honesty |
|---|---|---|---|
| `SetField` | ✅ | `VmEffect::SetField { field_idx, value }` | ⚠ value truncated `[0..4] → BabyBear` via `field_element_to_bb` (lines 2428-2431); only 4 of 32 bytes bound |
| `Transfer` | ✅ | `VmEffect::Transfer { amount, direction }` | ✅ full `u64` carried, direction bit honest |
| `GrantCapability` | ✅ | `VmEffect::GrantCapability { cap_entry }` | ⚠ `cap_entry = hash_to_bb(blake3(slot.to_le_bytes()))` — 4-byte truncation of a BLAKE3 hash of *only the slot number*, not the cap target/permissions |
| `RevokeCapability` | ✅ | `VmEffect::RevokeCapability { slot_hash }` | ⚠ same 4-byte truncation, slot-only |
| `EmitEvent` | ✅ | `VmEffect::EmitEvent { event_hash }` | ⚠ 4-byte truncation; event topic + data bound only modulo collision |
| `IncrementNonce` | ✅ | (implicit row-to-row) | ✅ no projection needed |
| `CreateCell` | ✅ | `VmEffect::CreateCell { create_hash }` | ⚠ 4-byte truncation of BLAKE3(pk‖token‖balance) |
| `SetPermissions` | ✅ | `VmEffect::SetPermissions { permissions_hash }` | ⚠ 4-byte truncation; AIR enforces state passthrough but binds only a partial hash |
| `SetVerificationKey` | ✅ | `VmEffect::SetVerificationKey { vk_hash }` | ⚠ 4-byte truncation; None→0 |
| `NoteSpend` | ✅ | `VmEffect::NoteSpend { nullifier, value }` | ⚠ 4-byte nullifier truncation; full `value` |
| `NoteCreate` | ✅ | `VmEffect::NoteCreate { commitment, value }` | ⚠ 4-byte commitment truncation; full `value` |
| `CreateSealPair` | ✅ | `VmEffect::CreateSealPair { pair_hash }` | ⚠ 4-byte truncation |
| `Seal` | ✅ | `VmEffect::Seal { field_idx }` | ⚠⚠ `field_idx = (pair_id[0] as u32) & 0x7` — derived from the *low 3 bits of the pair id*, NOT from the field being sealed. The runtime `Effect::Seal` carries `pair_id` + `capability` but no field index; the AIR `Seal` AIR sets `sealed_field_mask |= (1 << field_idx)` on a fabricated index. The executor comment acknowledges this: "Stage 2 reworks the Seal/Unseal AIR to operate on sealed_field_mask rather than on a single field index." |
| `Unseal` | ✅ | `VmEffect::Unseal { field_idx, brand }` | ⚠⚠ same as `Seal`: `field_idx = (brand_hash_byte0 as u32) & 0x7`, brand is a 4-byte truncation of the postcard-encoded sealed_box. The committed brand only weakly binds the actual recipient. |
| `BridgeMint` | ✅ | `VmEffect::BridgeMint { value_lo, mint_hash }` | ⚠ `value_lo = value & ((1<<30) - 1)`: **30-bit truncation** of u64 value. Above 2^30 a malicious prover could re-mint with arbitrary high bits. `mint_hash` is a 4-byte truncation. |
| `BridgeLock` | ✅ | `VmEffect::BridgeLock { value_lo, lock_hash }` | ⚠ same 30-bit value truncation, 4-byte lock hash |
| `BridgeFinalize` | ✅ | `VmEffect::BridgeFinalize { finalize_hash }` | ⚠ 4-byte truncation |
| `BridgeCancel` | ✅ | `VmEffect::BridgeCancel { nullifier_hash }` | ⚠ 4-byte truncation |
| `Introduce` | ✅ | `VmEffect::Introduce { intro_hash }` | ⚠ 4-byte truncation of BLAKE3(introducer‖recipient‖target‖perm_byte) |
| `PipelinedSend` | ✅ | `VmEffect::PipelinedSend { send_hash }` | ⚠ 4-byte truncation |
| `SpawnWithDelegation` | ✅ | `VmEffect::SpawnWithDelegation { spawn_hash }` | ⚠ 4-byte truncation |
| `RefreshDelegation` | ✅ | `VmEffect::RefreshDelegation` (no params) | ✅ selector alone — no domain data to bind |
| `RevokeDelegation` | ✅ | `VmEffect::RevokeDelegation { child_hash }` | ⚠ 4-byte truncation |
| `CreateObligation` | ✅ | `VmEffect::CreateObligation { stake_amount, obligation_id, beneficiary_hash }` | ⚠ stake_amount is full u64; obligation_id/beneficiary 4-byte truncations |
| `FulfillObligation` | ✅ | `VmEffect::FulfillObligation { obligation_id, stake_return }` | ⚠⚠ **`stake_return: 0` is hard-coded placeholder** (executor.rs:2617); the comment says "Stage 1: stake_return is not currently in the runtime variant; the AIR-side amount is wired by Stage 2's honesty pass once the obligation ledger is committed." Until then, the AIR proves stake_return=0 which is wrong for any non-zero stake. |
| `SlashObligation` | ✅ | `VmEffect::SlashObligation { obligation_id, stake_amount, beneficiary_hash }` | ⚠⚠ **`stake_amount: 0` is hard-coded placeholder** (executor.rs:2623); same Stage 2 deferral as Fulfill |
| `CreateEscrow` | ✅ | `VmEffect::CreateEscrow { amount_lo, escrow_hash }` | ⚠ 30-bit amount truncation, 4-byte hash |
| `ReleaseEscrow` | ✅ | `VmEffect::ReleaseEscrow { escrow_id_hash }` | ⚠ 4-byte truncation, amount not bound (passthrough) |
| `RefundEscrow` | ✅ | `VmEffect::RefundEscrow { escrow_id_hash }` | ⚠ same |
| `CreateCommittedEscrow` | ✅ | `VmEffect::CreateCommittedEscrow { commit_hash }` | ⚠ 4-byte truncation; Pedersen value commitment + range proof verified off-AIR |
| `ReleaseCommittedEscrow` | ✅ | `VmEffect::ReleaseCommittedEscrow { commit_hash }` | ⚠ 4-byte truncation |
| `RefundCommittedEscrow` | ✅ | `VmEffect::RefundCommittedEscrow { commit_hash }` | ⚠ 4-byte truncation |
| `ExerciseViaCapability` | ✅ | `VmEffect::ExerciseViaCapability { exercise_hash }` | ⚠ 4-byte truncation of BLAKE3(cap_slot‖inner_effect_hashes) |
| `MakeSovereign` | ✅ | `VmEffect::MakeSovereign` (no params) | ✅ AIR constrains mode_flag 0→1 transition |
| `CreateCellFromFactory` | ✅ | `VmEffect::CreateCellFromFactory { factory_vk, child_vk_derived }` | ⚠ 4-byte truncations of both VKs |
| `QueueAllocate` | ✅ | `VmEffect::AllocateQueue { capacity, owner_quota_id, cost_per_slot: 1 }` | ⚠ `cost_per_slot: 1` is hard-coded (executor.rs:2487); a future cost oracle would replace this |
| `QueueEnqueue` | ✅ | `VmEffect::EnqueueMessage { message_hash, deposit, sender_id, queue_len: 0, program_vk: ZERO }` | ⚠⚠ **`queue_len: 0` placeholder** (executor.rs:2499) — the AIR's "queue is not full (queue_len < capacity)" check therefore *always passes* against the projection; the executor itself enforces capacity but the proof doesn't. Also **`program_vk: ZERO` always** (line 2500) — programmable-queue program-validation hash is never bound from this projection. |
| `QueueDequeue` | ✅ | `VmEffect::DequeueMessage { expected_message_hash, deposit_refund: 0 }` | ⚠⚠ **`expected_message_hash` is the queue ID hash, not the head message hash** (lines 2506-2509 — comment: "Use queue ID hash as a placeholder"). **`deposit_refund: 0`** placeholder. The AIR's "hash equality via aux" check binds to whatever the prover supplies for the head, with no PI binding to the actual dequeued message. |
| `QueueResize` | ✅ | `VmEffect::ResizeQueue { new_capacity, queue_id, cost_per_slot: 1, old_capacity: 0 }` | ⚠⚠ **`old_capacity: 0` placeholder** (line 2520) — the AIR's "if growing, quota has balance for delta * cost_per_slot" delta computation always treats it as a fresh allocation |
| `QueueAtomicTx` | ✅ | `VmEffect::AtomicQueueTx { op_count, tx_hash, combined_old_root, combined_new_root, net_deposit }` | ⚠⚠ **`combined_old_root == combined_new_root`** (both set to `hash_to_bb(cell_id.as_bytes())` on lines 2552-2557) — so the AIR's "combined old roots → combined new roots transition is valid" enforces a *self-loop* with no actual transition. Refunds counted as 0 in net_deposit |
| `QueuePipelineStep` | ✅ | `VmEffect::PipelineStep { pipeline_id, source_old_root, source_new_root, sink_new_root, message_hash }` | ⚠ source_old_root = `hash_to_bb(source.as_bytes())` (4-byte queue-id truncation, NOT the actual queue root), source_new_root computed as Poseidon2(source_root, pipeline_id_hash), sink_new = Poseidon2(sink_root, pipeline_id_hash). Roots are fabricated; the AIR proves a self-consistent triangle but it doesn't tie back to the actual on-ledger queue state |
| `ExportSturdyRef` | ✅ | `VmEffect::ExportSturdyRef { cell_id, permissions: ZERO, random_seed, export_counter: 0 }` | ⚠⚠ **`permissions: ZERO`** and **`export_counter: 0`** placeholders (lines 3021-3026). The AIR's swiss-derivation check `swiss = hash(cell_id, hash(random_seed, counter))` is satisfied tautologically. Per the comment: "Permissions are not carried by the runtime variant, so we use ZERO (Stage 2 / P1.C tightens this…)". |
| `EnlivenRef` | ✅ | `VmEffect::EnlivenRef { swiss_number, presenter_id, expected_cell_id: presenter_id, expected_permissions: ZERO }` | ⚠⚠ `expected_cell_id == presenter_id` (line 3042 — literally aliased), `expected_permissions: ZERO`. The AIR's "swiss-table membership" check has nothing to bind to |
| `DropRef` | ✅ | `VmEffect::DropRef { cell_id, holder_federation: ref_id_bb, current_refcount: 1 }` | ⚠⚠ **`current_refcount: 1` hard-coded** (line 3058); AIR's "refcount > 0" check is satisfied by construction with no link to the actual stored refcount |
| `ValidateHandoff` | ✅ | `VmEffect::ValidateHandoff { certificate_hash, recipient_pk: ZERO, introducer_pk: ZERO, approved_set_root: ZERO }` | ⚠⚠ **three ZERO placeholders** (lines 3072-3077); the AIR's Merkle-membership-of-cert-hash-in-approved-set check is against the all-zero root |

**Runtime variants with NO Effect-VM projection (silently dropped, see
the `_ => {}` arm at executor.rs:3081-3086):**

These exist in `Effect` but `convert_turn_effects_to_vm` does not match
them when the cell is not the relevant party (cross-cell effects):

- `Transfer { from, to, .. }` when neither `from` nor `to` equals the
  projecting cell.
- `GrantCapability { from, to, .. }` when `to != cell_id`.
- `EmitEvent { cell, .. }` when `cell != cell_id`.
- `SetField`, `SetPermissions`, `SetVerificationKey`, `RevokeCapability`,
  `IncrementNonce` when `cell != cell_id`.
- `ExportSturdyRef { target, .. }` when `target != cell_id`.
- `EnlivenRef { bearer, .. }` when `bearer != cell_id`.
- `MakeSovereign { cell }` when `cell != cell_id`.
- `CreateEscrow { cell, .. }` when `cell != cell_id`.

This is correct *for per-cell projection* but means a Turn is split
across multiple AIR-proof streams and the bilateral cross-cell binding
must be done by the aggregate γ.2 prover
(`circuit::bilateral_aggregation_air`) — which is itself wired only
partially (see `BoundDelta` row in §1).

**Variants with NO runtime Effect at all** (declared on the Effect VM
side but never produced by the executor):

- `VmEffect::NoOp` — used only for padding in the AIR; never projected
  from runtime.
- `VmEffect::Custom { program_vk_hash, proof_commitment }` — this is the
  per-cell `CellProgram::Circuit` dispatch shape (custom predicates).
  The runtime path that emits it is the Circuit-program proof
  verification at executor.rs:1545+ (the "12. Verify custom program
  proofs" pass), but no `Effect::Custom` variant exists in `turn`
  (the runtime expresses custom programs by *attaching* a proof to the
  Action's authorization rather than by emitting an Effect).

**Honest-tally summary for §4:**

- **Fully honest** (full payload bound, no placeholders): 4 variants
  (Transfer, IncrementNonce, RefreshDelegation, MakeSovereign).
- **Truncated but otherwise honest** (4-byte hash truncations, full
  scalar payloads): ~25 variants.
- **Placeholder-bearing** (one or more hard-coded zero/one values
  acknowledged in code comments as "Stage 2" / "P1.C tightens this"):
  9 variants: `Seal`, `Unseal`, `FulfillObligation`, `SlashObligation`,
  `EnqueueMessage` (queue_len, program_vk), `DequeueMessage`
  (expected_message_hash, deposit_refund), `ResizeQueue` (old_capacity),
  `AtomicQueueTx` (combined_old_root == combined_new_root),
  `ExportSturdyRef` (permissions, export_counter), `EnlivenRef`
  (expected_cell_id, expected_permissions), `DropRef`
  (current_refcount), `ValidateHandoff` (recipient_pk, introducer_pk,
  approved_set_root).
- **Bit-truncated value fields** (30-bit u64→BabyBear truncation):
  `BridgeMint.value_lo`, `BridgeLock.value_lo`, `CreateEscrow.amount_lo`.
  Above 2^30, a prover can re-mint/re-lock/escrow with any high bits
  set.

---

## §5 — `WitnessedPredicateKind` registry coverage

The `WitnessedPredicateRegistry` (`cell/src/predicate.rs:376-490`)
defines six platform-reserved kinds plus a `Custom { vk_hash }` open
slot, all behind a `WitnessedPredicateVerifier` trait. The shipped
verifiers in `cell::predicate`:

| Kind | Real verifier in cell | Stub | Real verifier exists in circuit? | Wired through executor? |
|---|---|---|---|---|
| `Dfa` | ❌ | ✅ `StubVerifier::dfa` accepts non-empty proofs | ✅ `circuit::dsl::circuit:1711-1941` (DFA-bytestring AIR) | ❌ — registry never consulted by program-evaluation path |
| `Temporal` | ❌ | ✅ | ✅ `circuit::temporal_predicate_dsl::verify_temporal_predicate` | ❌ |
| `MerkleMembership` | ❌ | ✅ | ✅ `circuit::merkle_air::MerklePoseidon2StarkAir` | ❌ |
| `BlindedSet` | ❌ | ✅ | ✅ `circuit::accumulator_air::AccumulatorNonMembershipAir` (proof shape mismatch — non-membership vs membership) | ❌ |
| `BridgePredicate` | ❌ | ✅ | ✅ `circuit::predicate_air::PredicateAir` / `relational_predicate_air` | ❌ |
| `PedersenEquality` | ❌ | ✅ | ✅ `circuit::committed_threshold::CommittedThresholdAir` / Bulletproof verifier | ❌ |
| `Custom { vk_hash }` | n/a (app-registered) | n/a | (app-side AIR) | ❌ — no executor dispatch site reads `WitnessedPredicateRegistry::custom` |

**The registry is plumbing-only.** No executor call site invokes
`WitnessedPredicateRegistry::verify`. The `Preconditions::witnessed`
field and the `StateConstraint::Witnessed` variant both lower onto a
sentinel that the executor surfaces as a violation.

The `cell::CapabilityCaveat::Witnessed(WitnessedPredicate)` variant
also exists declaratively but is not consulted by `verify_authorization`.

---

## §6 — Cross-cutting findings

### 6.1 — Sentinel-rejected variants (P0)

`StateConstraint::{TemporalPredicate, BoundDelta, Witnessed, Custom}`
all return sentinel `ProgramError` values from the cell-side evaluator,
expecting the executor to intercept and dispatch to the appropriate
verifier / cross-cell prover / DSL runtime. The executor at
`turn/src/executor.rs:4379-4387` does **none** of this — it converts
any non-`Ok` result to `TurnError::ProgramViolation`. Net effect: a
cell that declares any of these four variants in its `CellProgram`
cannot ever execute a turn. This matches codex P0 #2.

### 6.2 — Placeholder `EvalContext` fields

The executor builds `EvalContext` at `executor.rs:4361-4373` with two
hard-coded fields: `sender_epoch_count: 0` and `revealed_preimage: None`.
This silently subverts `RateLimit` (always passes — `0 >= max` is
false for any positive cap) and `PreimageGate` (always returns
`MissingContextField`). The `current_epoch` field uses a `height/1024`
heuristic that is not coordinated with any other component.

### 6.3 — Token-crate caveats are a disjoint surface

Of 15 token caveat type IDs, only 3 (`ValidityWindow`, `ConfineUser`,
`Budget`) are structurally similar to slot caveats, and even those
differ on units (time vs blocks; single user vs set; API-call cost vs
mutation count). The vocabularies do not currently share a
representation; `CapabilityCaveat` (cell/src/capability.rs:30-40) is
the staging point for unification but exposes only `FacetConstraint`
and `Witnessed(WitnessedPredicate)`.

### 6.4 — Effect-VM AIR placeholders

Nine `Effect` variants have hard-coded zero/one placeholders in their
projection to `VmEffect` (see §4 table). The most severe are
`QueueEnqueue.queue_len: 0` (queue-full check tautologized),
`QueueDequeue.expected_message_hash = queue_id_hash` (no binding to the
actual dequeued message), `QueueAtomicTx.combined_old_root ==
combined_new_root` (self-loop transition), and `ValidateHandoff.{
recipient_pk, introducer_pk, approved_set_root}: ZERO` (Merkle
membership against the zero root). All are tagged in code comments as
deferred to "Stage 2" or "P1.C" workstreams.

### 6.5 — 30-bit value truncations

`BridgeMint.value_lo`, `BridgeLock.value_lo`, and `CreateEscrow.amount_lo`
project `(value as u64) & ((1 << 30) - 1)` into a BabyBear element.
Above 2^30 (~1.07 billion computrons), the high bits are unrecoverable
from the proof — a prover could re-mint/re-lock/escrow any amount
above that threshold with arbitrary high-bit collision. The runtime
executor enforces the actual amount; only the *proof* loses fidelity.

### 6.6 — Witness-attached predicate registry is plumbing-only

All six `WitnessedPredicateKind` builtins have stubs that accept any
non-empty proof. The real circuit-side verifiers exist in
`circuit::{dsl, temporal_predicate_dsl, merkle_air, accumulator_air,
predicate_air, committed_threshold}` but are not registered into any
production-facing `WitnessedPredicateRegistry`, and the executor never
calls `registry.verify(...)` from the cell-program path.

### 6.7 — `Preconditions::witnessed` is unreachable

The `Preconditions` struct gained a `witnessed: Vec<WitnessedPredicate>`
field per PREDICATE-INVENTORY §3, but `Preconditions::evaluate`
(`cell/src/preconditions.rs:347-364`) only walks `cell_state`,
`network`, and `valid_while`. The `witnessed` field is serialized into
the action hash (preconditions.rs:334-341) but never verified.

### 6.8 — `CapabilityCaveat` is declared but unenforced

`CapabilityCaveat { FacetConstraint, Witnessed }` (cell/src/capability.rs:30-40)
is declared on the `CapabilityRef` shape but the executor's
`verify_authorization` path consults only `permissions: AuthRequired`
and `allowed_effects: Option<EffectMask>` from `CapabilityRef`. The
`caveats: Vec<CapabilityCaveat>` field anticipated in
PREDICATE-INVENTORY §3.5+§7.6 is not yet attached to the struct.

---

## §7 — Top-5 critical gaps

1. **Sentinel-rejected `StateConstraint` variants (P0).** Four out of
   21 variants (`TemporalPredicate`, `BoundDelta`, `Witnessed`,
   `Custom`) propagate as `TurnError::ProgramViolation` because the
   executor never intercepts the sentinel. Any cell declaring one of
   them is bricked. — `cell/src/program.rs:1072-1133` and
   `turn/src/executor.rs:4379-4387`.

2. **`PreimageGate` is always broken.** The executor supplies
   `revealed_preimage: None` unconditionally; `PreimageGate` always
   returns `MissingContextField`. No plumbing from `action.witness_blobs`
   of `WitnessKind::Preimage32` to the program-evaluator. —
   `turn/src/executor.rs:4372` and `cell/src/program.rs:997-1028`.

3. **`RateLimit` is a no-op.** The executor supplies
   `sender_epoch_count: 0`, so the check `ctx.sender_epoch_count >=
   max_per_epoch` is always false. Any rate-limit cell program offers
   no rate-limit guarantee. — `turn/src/executor.rs:4371`.

4. **Effect-VM queue / CapTP AIRs accept fabricated PI.** Nine effect
   projections supply `0` or `1` placeholders for fields the AIR
   actually constrains. The most severe are `QueueAtomicTx`
   (combined_old_root == combined_new_root → self-loop) and
   `ValidateHandoff` (entire Merkle-membership PI is ZERO). The AIR
   proves consistency with the projection, not consistency with the
   actual on-ledger state. — `turn/src/executor.rs:2479-3079`.

5. **`WitnessedPredicateRegistry` is unused.** The shape exists, the
   stubs exist, the per-kind real verifiers exist in `circuit`, but no
   call site dispatches through the registry. So Lane G's
   "witness-attached unification" claim that `Witnessed { wp }` is
   "verified by the registry's verifier for `wp.kind`" is
   documentation-only. — `cell/src/predicate.rs:412-490`.

---

## §8 — Top-5 surprisingly-complete things

1. **17 of 21 `StateConstraint` variants are honestly evaluated.** The
   static (`FieldEquals`, `FieldGte`, `FieldLte`, `SumEquals`),
   transition (`WriteOnce`, `Immutable`, `Monotonic`, `StrictMonotonic`,
   `BoundedBy`, `FieldDelta`, `FieldDeltaInRange`, `SumEqualsAcross`,
   `MonotonicSequence`, `AllowedTransitions`), time-window
   (`TemporalGate`), and disjunction (`AnyOf`) variants all do
   end-to-end honest work. The `field_to_u64` last-8-bytes lane is
   consistent across all of them.

2. **`AnyOf` keeps disjunction structurally bounded.** Per eval §4.3
   `AnyOf::variants: Vec<SimpleStateConstraint>` excludes nested
   `AnyOf` and `Custom`. The evaluator lifts each Simple into the full
   enum and tries them in order. Soundness against pathological nesting
   is maintained.

3. **`SumEqualsAcross` does proper overflow arithmetic.** The intra-cell
   conservation check on lines 853-899 uses `checked_add` on every
   summand and emits a clean error rather than wrapping. This is the
   one variant where the cell-side evaluator is paranoid about
   adversarial inputs.

4. **The `WitnessedPredicateRegistry` shape is well-factored even
   though unused.** The closed-builtin + open-custom split (cell
   /src/predicate.rs:376-490) mirrors the macaroon `CaveatType` ID-range
   convention and the `Effect::Custom` 32-byte vk_hash precedent. The
   `register_builtin` / `register_custom` API is in place; only the
   call sites are missing.

5. **The Effect-VM projection of `MakeSovereign` and
   `RefreshDelegation` is genuinely complete.** Two of the simplest
   variants are also two of the most faithful — both project to
   parameter-less `VmEffect` variants whose AIR constrains the
   appropriate state transition (mode_flag 0→1; delegation epoch
   bump). No truncation, no placeholders.

---

## §9 — Where the in-flight caveat-correctness lane will close gaps

Agent `a693478bed4899803` is working multi-cell evaluation + EvalContext
wiring + operation-scoped cases + Effect-VM projection tightening.
Expected to close:

- §6.1 **all four sentinel variants** (TemporalPredicate, BoundDelta,
  Witnessed, Custom) via registry dispatch + γ.2 cross-cell wiring + a
  DSL-IR table.
- §6.2 **`sender_epoch_count` and `revealed_preimage`** become honest
  via the per-(cell, sender, epoch) counter and witness_blobs lookup.
- §6.6 **registry plumbing** — the lane is expected to register real
  verifiers (DFA, Temporal, MerkleMembership, BlindedSet,
  BridgePredicate, PedersenEquality) into the executor's
  `WitnessedPredicateRegistry` and consult it from the cell-program
  evaluator's `Witnessed { wp }` arm.
- §6.7 **`Preconditions::witnessed` walking** — expected to be hooked
  into `Preconditions::evaluate`.
- Effect-VM placeholder cleanup is *not* in scope (Stage 2 /
  P1.C-tagged items are separate workstreams), so §6.4 and §6.5 are
  not closed by this lane.

NOT expected to close:

- §6.4 Effect-VM placeholders (Stage 2 / P1.C work).
- §6.5 30-bit value truncations (Effect-VM PI-layout expansion is its
  own coordinated landing, see REVIEW-effect-vm.md and codex P1
  comments).
- §6.8 `CapabilityCaveat::Witnessed` enforcement (PREDICATE-INVENTORY
  §7.6 Phase 6).
- §3 token↔slot-caveat vocabulary unification (separate roadmap).

---

## §10 — Files of record

Per-variant authority:

- **Cell declarations:** `cell/src/program.rs` (StateConstraint @ line 224,
  evaluator @ line 588), `cell/src/predicate.rs` (WitnessedPredicate @ 67,
  registry @ 376), `cell/src/preconditions.rs` (EvalContext @ 112,
  Preconditions @ 16), `cell/src/capability.rs` (CapabilityCaveat @ 30).
- **Executor enforcement:** `turn/src/executor.rs`
  (`execute_tree` program-evaluation site @ 4343–4393,
  `check_preconditions` @ 4450–4472,
  `convert_turn_effects_to_vm` @ 2400–3092,
  `verify_authorization` @ 4489+).
- **Token caveats:** `token/src/dregg_caveats.rs` (DreggGrant @ 86,
  verify_caveats @ 376), `macaroon/src/caveat.rs` (CaveatType @ 22,
  ID ranges @ 24-45).
- **Circuit AIRs:**
  - Effect-VM: `circuit/src/effect_vm.rs` (Effect @ 893, CellState @ 1210),
    `circuit/src/effect_vm_p3_air.rs`.
  - Predicate AIRs (separate language): `circuit/src/predicate_program.rs`
    (PredicateExpr @ 86), `circuit/src/predicate_air.rs`,
    `circuit/src/compound_predicate_air.rs`,
    `circuit/src/relational_predicate_air.rs`,
    `circuit/src/temporal_predicate_air.rs`,
    `circuit/src/temporal_predicate_dsl.rs`,
    `circuit/src/committed_threshold.rs`,
    `circuit/src/accumulator_air.rs` (BlindedSet non-membership),
    `circuit/src/arithmetic_predicate_air.rs`,
    `circuit/src/dsl/circuit.rs:1711-1941` (DFA AIR),
    `circuit/src/merkle_air.rs`,
    `circuit/src/bilateral_aggregation_air.rs` (γ.2 cross-cell).
- **Design docs:** `SLOT-CAVEATS-DESIGN.md`, `SLOT-CAVEATS-EVALUATION.md`,
  `PREDICATE-INVENTORY.md`, `EFFECT-VM-SHAPE-A.md`, `REVIEW-effect-vm.md`,
  `AUDIT-turn-executor.md`.
