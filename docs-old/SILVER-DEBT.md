# SILVER-DEBT.md — dregg's canonical Silver-vs-Golden debt ledger

**Date:** 2026-05-25 (STARBRIDGE-FOLLOWUP-03 update)
**Source audits ingested:** `AIR-SOUNDNESS-AUDIT.md` (ce1e2def, 705 lines),
`EXECUTOR-VK-AUDIT.md` (793 lines), `HOUYHNHNM-DEEP-CRITIQUE.md` (1a8299eb,
1635 lines), plus a fresh sweep of `TODO[block1-bind]`, `MockProof*`,
`with_stubs`, `expand_vk_hash_16_to_32`, and 30-bit-truncation markers.
**FOLLOWUP-03:** Added thin wasm stubs for snapshot/time-travel (§5.9/5.10),
confirmed coord sig verifies landed (no new markers), injected precise
cross-ref comments at blocked sites. No debt rows added/removed (no cargo
closures of T items); §6 + §0 updated with refined cargo plan. Living
tracker status also mirrored in STARBRIDGE-PLAN.md §5.
**Companion docs:** `EXECUTOR-HONESTY-AUDIT.md` (T1-T15 threat ledger),
`CAVEAT-LAYER-COVERAGE.md` (per-variant evaluator status),
`PROTOCOL-CATEGORICAL-ANALYSIS.md` (Tier 1/2/3 punch list),
`NEW-WORLD.md` §"What's not done" (10 numbered Silver gaps).

---

## §0. Purpose

This document is **dregg's canonical Silver-vs-Golden debt ledger**.

**What it is.** A per-debt-item ledger listing every place the shipping
implementation falls short of what the docs / tagline / paper claim, and
every Silver-Sound construct awaiting its Golden-Vision algebraic lift.
Each row carries a file:line citation, a tier classification, a closure
plan, and a severity grade.

**Why it exists.** The Houyhnhnm Ch.11 deep-critique flagged this as the
sharpest single improvement: *"every priority debate becomes possible to
have"* only after this exists. Today the trust footprint is scattered
across `TODO[block1-bind]` markers, "30-bit truncation" comments,
`NotYetWiredVerifier` registrations, `EXECUTOR-HONESTY-AUDIT` open tags,
and `NEW-WORLD.md` §"What's not done" items. An external reader cannot
enumerate the *total* trust footprint without spelunking ~17,000 LOC and
seven design docs. This is the spelunking-result, written down once.

**The rule.** A new `TODO[block1-bind]` or equivalent honesty-debt
marker (`MockProof*`, `*Stub*Verifier`, `with_stubs`, `placeholder`,
`sentinel`, `expand_vk_hash_16_to_32`, `revealed_preimage: None`,
`sender_epoch_count: 0`, 30-bit value truncation, `from_parts` without
integrity check) **may not be added unless enumerated in §4 in the same
PR**. CI enforces this. Removing a marker from code requires removing
its §4 row in the same PR (forces cleanup at closure).

**Three tiers.**

- **Tier 1 — Marketing-vs-code lie.** Claim the docs/tagline make that
  the code does not honor. Severity: HIGH = blocks tagline honesty,
  MEDIUM = blocks current demo claims, LOW = blocks future claims.
- **Tier 2 — Acknowledged Silver-vs-Golden debt.** Code knowingly ships
  Silver semantics (executor re-derivation, structural check, opt-out
  fallback) with the Golden lift planned.
- **Tier 3 — Architectural debt.** Structural smells no single
  proof-system change fixes. Refactor cost: small / medium / large.

**Style.** One section per item, file:line for everything. No
moralizing. Settled design questions live in §7.

---

## §0. Recently Retired (session 2026-05-25)

Items closed during the 2026-05-25 session. Moved here from §1/§2/§3.
Commit SHAs are the primary closure evidence; re-open if a later audit
finds the marker is back.

### T1.5 — CLOSED — Temporal AIR boundary binding (2026-05-25, `df122d4c`)

`TemporalPredicateAir::boundary_constraints` previously bound only
`ACCUMULATOR` and `STEP_INDEX`. `THRESHOLD`, `VALUE`, `STATE_ROOT_INITIAL`,
`STATE_ROOT_FINAL` were plain serde fields — a prover could forge any
threshold + state-root and the wrapper accepted.

**Fix:** Boundary constraints now pin `THRESHOLD` to `PI[1]`,
`STATE_ROOT[0]` to `PI[2]`, `STATE_ROOT[N-1]` to `PI[3]`.
`verify_temporal_predicate` reconstructs PIs from caller-supplied
parameters, not from `proof.<field>`. Adversarial test confirms forged
threshold rejected.

### T1.6 — CLOSED — Executor signature covers full receipt_hash (2026-05-25, `e0fe3316`)

The v2 signed message covered only `turn_hash + pre/post_state +
timestamp + federation_id + agent`. Fields `was_encrypted`, `finality`,
`effects_hash`, `previous_receipt_hash`, `routing_directives`,
`derivation_records`, `emitted_events` were outside the signature but
inside `receipt_hash`.

**Fix:** Promoted to `executor-receipt-sig-v3:`; the signed preimage is
now the full `receipt_hash` bytes. Downstream verifiers updated. The
v2 domain separator is removed; no migration path (all receipts must be
re-signed by the live executor on resync).

### T2.1 (partial) + T2.2 — CLOSED — block1-bind queue/capability placeholders (2026-05-25, `9834b3d4`)

`convert_turn_effects_to_vm` arms for `QueueEnqueue`, `QueueDequeue`,
`QueueResize`, `QueueAtomicTx`, `ExportSturdyRef`, `EnlivenRef`, and
`DropRef` previously projected zero/synthetic placeholder values into
`VmEffect`. The proof attested vacuous queue-length, refcount, and
permissions; soundness depended entirely on the executor's `apply_effect`
cross-check.

**Fix:** All seven arms now source real ledger values — queue capacity,
head hash, combined old root, permissions mask, export counter, and
current refcount — at `convert_turn_effects_to_vm` time. Every
`TODO[block1-bind]` at these sites is removed from source.

`ValidateHandoff` recipient/introducer pk placeholders (T2.3) remain
open — a follow-on PR carries that closure.

### T2.7 — CLOSED (Silver-Sound interim) — NonMembership adjacency_tag commitment-bound (2026-05-25, `5d557969`)

`SortedNeighborNonMembershipVerifier` accepted `adjacency_tag =
[0xFE;32]` (public constant) so anyone could forge a non-membership
proof against any set by choosing `lower=0x00…, upper=0xFF…,
tag=0xFE…`.

**Fix (Silver-Sound):** `adjacency_tag` is now derived as
`BLAKE3("dregg-nonmember-adj-v1" || set_commitment || lower || upper)` —
commitment-bound per `(set, lower, upper)` triple. The public constant
is gone; the forged-tag attack is closed at the Silver level. A full
Merkle adjacency AIR proof (the Golden lift) remains on the roadmap.

### T2.8 — CLOSED — `default_builtins()` now uses `NotYetWiredVerifier` (2026-05-25, `c86aecd7`)

Previously `default_builtins()` called `Self::with_stubs()` — i.e.,
installed `StubVerifier` for every kind, which accepted any non-empty
proof bytes. An executor using `default_builtins()` silently accepted
forged `WitnessedPredicate` proofs for Dfa, Temporal, MerkleMembership,
BlindedSet, BridgePredicate, and PedersenEquality.

**Fix:** `default_builtins()` now installs `NotYetWiredVerifier` for all
six kinds. Every call to a non-wired kind returns a hard error. Honest
fail-closed posture. The registry comment documents the old permissive
behavior explicitly so future readers understand the change.

Production deployments that want real verifiers still need the planned
`dregg-witnessed-registry-default` crate (T1.4/T2.8 remains in
SILVER-DEBT as the "get real verifiers wired" story).

### T3.3 — CLOSED — Custom-effect VK widened to 8 BabyBear felts (2026-05-25, `46a886a5`)

### coord BudgetCoordinator Ed25519 sig verification — CLOSED (STARBRIDGE-FOLLOWUP-03 confirmation, 2026-05-25)
The rebalance + apply_unlock_certificate paths now perform the `verify_signature`
calls (with SECURITY comments) against registered silo pubkeys (budget.rs:482,
:756). Matches the pattern in atomic.rs. The "Forged signature (not verified...)"
test comment (now ~1189) is updated for defense-in-depth (ceiling fires first).
Gap from AUDIT-coord-crate §2/§7 + STARBRIDGE-PLAN §5.6 is closed for the
signature piece. (No new SILVER-DEBT marker row was needed as none existed
for the missing-verify itself; the tests already exercised error paths.)

`Effect::Custom { program_vk_hash }` carried only 4 BabyBear felts (16
bytes); `expand_vk_hash_16_to_32` zero-padded the upper 16 bytes. Two
VKs colliding on the low 16 bytes (~2^64 work) dispatched to the same
handler — 80-bit effective security.

**Fix:** The AIR's custom-effect PI is widened to 8 BabyBear elements
(32 bytes); `expand_vk_hash_16_to_32` is deleted from source. Security
matches the 128-bit BLAKE3 baseline everywhere else.

### T1.3 — PARTIAL — VK integrity at SetVerificationKey boundary (2026-05-25, `08e01ea7`)

The cell's `VerificationKey::from_parts` accepted arbitrary `(hash, data)`
with no `blake3(data) == hash` check. `executor.rs` called it at the
`SetVerificationKey` apply site with whatever the actor supplied.

**Fix:** `VerificationKey::from_parts_checked` added for untrusted-input
paths; `SetVerificationKey` apply now calls it and returns
`VerificationKeyIntegrityError` on mismatch. The internal
`from_parts` fast-path (for deserialization where the caller has already
validated) remains — it now carries a doc comment marking untrusted-input
sites as `#[cfg(debug_assertions)]`-assertable. The `new` constructor
still uses raw BLAKE3 (not `canonical_vk_v2`); the full v2 layered
invariant is a follow-on (see SILVER-DEBT §1 T1.3 original entry, still
tracking the `new` + v2 gap).

---

## §1. Tier 1: Marketing-vs-code lies

Each entry: the claim (with source), the code reality (with file:line),
the closure plan, the blocking severity.

### T1.1 — "proof-carrying capability mesh" tagline overstates trustless

- **Claim source.** `NEW-WORLD.md:7` — *"dregg is a proof-carrying
  capability mesh"*; also `README.md` and `paper/` framing.
- **Implied semantics.** Every authoritative state transition carries a
  proof that algebraically attests its correctness.
- **Code reality.** Three executor-trusted boundary cuts remain
  (T9 sovereign-witness Phase 2, bridge proof-to-action binding,
  `coord::BudgetCoordinator` signature gaps — `NEW-WORLD.md:235-249`);
  nine `Effect VM PI` placeholder variants (see T2.1–T2.4 below); 30-bit
  value truncation on `BridgeMint/Lock/CreateEscrow` (T2.5);
  `MockProofVerifier` still selectable in the trustless intent path
  (T1.2 below); `WitnessedProofVerifier::with_stub_registry()` is the
  *default* `TrustlessIntentEngine::new` verifier
  (`intent/src/trustless.rs:761`).
- **Severity.** HIGH — directly contradicts the tagline.
- **Closure plan.** Either narrow the tagline to *"a capability mesh
  moving toward proof-carrying; current trust assumptions in
  SILVER-DEBT.md"* (zero-cost, immediately honest) or land every Tier 1
  / Tier 2 entry below (multi-quarter). The houyhnhnm-recommended fix
  is the former during the closure work and the latter as the
  permanent state.

### T1.2 — `MockProofVerifier` in the trustless intent path

- **Claim source.** `NEW-WORLD.md:92-101` *"Trustless intent matching …
  Real STARK proofs via `dregg_circuit::multi_step_air` with
  replay-resistant `request_hash` binding."*
- **Code reality.** `intent/src/trustless.rs:682-698` —
  ```rust
  pub struct MockProofVerifier;
  impl ProofVerifier for MockProofVerifier {
      fn verify(&self, proof: &[u8], …) -> Result<(), String> {
          if proof.is_empty() { return Err("empty proof".to_string()); }
          check_submission_structure(solution, total_score, decrypted_intents)
      }
  }
  ```
  The struct is `#[deprecated]` but the engine's default
  (`TrustlessIntentEngine::new` at `intent/src/trustless.rs:761`)
  instantiates `WitnessedProofVerifier::with_stub_registry()`, which is
  the same permissive semantics under a renamed surface (any non-empty
  proof bytes pass when the submission carries no `witnessed_predicate`).
  Production posture (`WitnessedProofVerifier::strict`) exists but is
  not the default.
- **Severity.** HIGH — the *name* "trustless intent engine" is
  contradicted by the default accepting unverified proofs.
- **Closure plan.** Make `strict` the default in
  `TrustlessIntentEngine::new`; relegate `with_stub_registry()` to a
  test-only constructor (`#[cfg(test)]` or rename to
  `with_unverified_for_tests()`). Multi-step STARK fulfillment exists
  per `NEW-WORLD.md:101` — wire it as the registry's `Custom`
  verifier. Effort: small.

### T1.3 — `VerificationKey` struct has no integrity invariant

- **Claim source.** `cell/src/vk_v2.rs:213` `canonical_vk_v2` commits to
  `program_bytes || air_fingerprint || verifier_fingerprint.canonical_bytes()
  || proving_system_id` under BLAKE3 derive-key `"dregg-vk-v2"`. Test
  suite (vk_v2.rs:240-376) covers single-component sensitivity.
- **Code reality.** `cell/src/cell.rs:36-46`:
  ```rust
  impl VerificationKey {
      pub fn new(data: Vec<u8>) -> Self {
          let hash = *blake3::hash(&data).as_bytes();   // raw BLAKE3, NOT vk_v2
          VerificationKey { hash, data }
      }
      pub fn from_parts(hash: [u8; 32], data: Vec<u8>) -> Self {
          VerificationKey { hash, data }                 // no integrity check
      }
  }
  ```
  `from_parts` accepts arbitrary `(hash, data)` with no
  `blake3(data) == hash` check; `new` uses raw BLAKE3 (not the v2
  layered encoding). The two constructors are not consistent with each
  other. `turn/src/executor.rs:9678-9682` calls
  `VerificationKey::from_parts(*vk_hash, vk_hash.to_vec())` —
  populating `data` with the hash itself. `turn/src/executor.rs:7633-7649`
  `SetVerificationKey` accepts caller-supplied `VerificationKey` with no
  hash-vs-data check and no `canonical_vk_v2` derivation check.
- **Severity.** HIGH — the v2 layered encoding is unenforceable at the
  cell-state boundary. A cell can carry a `verification_key` whose hash
  is unrelated to any real (program, AIR, verifier) tuple.
- **Closure plan.** Add `VerificationKey::new_v2(components: VkComponents)`
  that calls `canonical_vk_v2`; `#[deprecated]` the raw-BLAKE3 `new`;
  remove `from_parts` from the public surface or add a debug-assertion
  enforcing `hash == canonical_vk_v2(deserialize(data))`. Reject
  `SetVerificationKey` and `CreateCellFromFactory` payloads that don't
  pass the invariant. Effort: small (one type + two effect-apply
  checks).

### T1.4 — `StateConstraint::Witnessed` was "uncreatable in practice"

- **Claim source.** `NEW-WORLD.md:46-53` *"The unifying insight is that
  dregg has **many places** where 'this thing is allowed' is expressed …
  and they all want the same predicate language. … The
  `WitnessedPredicateKindRegistry` maps `kind` to a verifier. **The same
  predicate vocabulary serves slot caveats and authorization** —
  distinguished by `input_ref`."*
- **Code reality (partially closed since `CAVEAT-LAYER-COVERAGE.md` was
  written).** The executor now carries a `witnessed_registry: Option<
  WitnessedPredicateRegistry>` field
  (`turn/src/executor.rs:898`) and defaults it to
  `WitnessedPredicateRegistry::default_builtins()` in every executor
  constructor (`turn/src/executor.rs:944,984,1020`). The cell evaluator
  still returns `ProgramError::WitnessedPredicateRequiresExecutor`
  (`cell/src/program.rs:833`), but the executor's authorization path
  intercepts and dispatches through the registry
  (`turn/src/executor.rs:5537, 6319`). **However**:
  `default_builtins()` (`cell/src/predicate.rs:646-657`) installs
  `NotYetWiredVerifier` for `Dfa`, `Temporal`, `MerkleMembership`,
  `BlindedSet`, `BridgePredicate`, `PedersenEquality` — every kind
  except `NonMembership` is *rejected by default*. The host must
  manually install real verifiers; no production host wiring is checked
  into the tree (per `cell/src/predicate.rs:628-633`: "the cell crate
  cannot depend on dregg-circuit (it would close a dependency cycle),
  so the real per-kind verifiers must be installed by the host at
  startup").
- **Severity.** MEDIUM — slot caveats and `Authorization::Custom` work
  for `NonMembership` only by default. Everything else needs out-of-tree
  registry plumbing.
- **Closure plan.** Create a `dregg-witnessed-registry-default` crate
  that depends on both `dregg-cell` and `dregg-circuit` and exposes
  `default_with_real_verifiers() -> WitnessedPredicateRegistry`
  populating each kind from its DSL backing (DFA from
  `circuit/src/dsl/circuit.rs:426`, membership from
  `dsl/membership.rs:256/312`, bridge from `bridge/src/present.rs`,
  Pedersen from `value_commitment.rs`). Every host binary
  (`dregg-node`, `dregg-cli`, `starbridge`, `app-framework::AppServer`)
  calls `set_witnessed_registry(default_with_real_verifiers())` at
  startup. Add a `WitnessedPredicateRegistry::sanity_check_no_stubs()`
  API and call it under `cfg(production)`. Effort: medium (new crate +
  ~6 verifier adapters).

### T1.5 — "Silver Vision is integration-complete" — `Temporal` boundary binding not algebraic

- **Claim source.** `NEW-WORLD.md:22` *"Silver Vision is the
  pre-algebraic form — every component integrates, every loop closes,
  every receipt is signed and replayable."* — implies Silver is
  *complete* even if pre-algebraic.
- **Code reality.** `circuit/src/temporal_predicate_dsl.rs:147-164`
  `TemporalPredicateAir::boundary_constraints` pins only `ACCUMULATOR`
  (row 0 = 1; last row = `pi[0]` = padded_len) and `STEP_INDEX` (row 0
  = 0). **`THRESHOLD`, `VALUE`, `STATE_ROOT_INITIAL`,
  `STATE_ROOT_FINAL` are NOT bound into the STARK PI.** The wrapper
  `verify_temporal_predicate` (`temporal_predicate_dsl.rs:419-457`)
  compares `proof.threshold` / `proof.initial_state_root` /
  `proof.final_state_root` as plain serde struct fields. A prover can
  forge any threshold + state-root and the wrapper still accepts
  (attack sketch: `AIR-SOUNDNESS-AUDIT.md §2.K`, lines 334-348).
- **Severity.** HIGH if `Temporal` reaches playground surfaces (intent
  matching exposes via `TemporalPredicateRequirement`).
- **Closure plan.** Extend `TemporalPredicateAir::boundary_constraints`
  to bind `VALUE`, `THRESHOLD`, `STATE_ROOT[0]`, `STATE_ROOT[N-1]`
  columns to PI slots. Rewrite `verify_temporal_predicate` to construct
  PI from caller-supplied parameters rather than from
  `proof.<field>`. The PI width changes; the wire-format
  `TemporalPredicateProof` does not need to change. Effort: medium
  (boundary constraints + PI rebuild + adversarial test).

### T1.6 — `executor signature` covers strictly less than `receipt_hash`

- **Claim source.** `turn/src/turn.rs:686-698` and the README framing of
  `canonical_executor_signed_message` as *"cryptographically binds the
  receipt to a known executor."*
- **Code reality.** `turn/src/turn.rs:686-698`:
  ```rust
  pub fn canonical_executor_signed_message(&self) -> Vec<u8> {
      const DOMAIN: &[u8] = b"executor-receipt-sig-v2:";
      // turn_hash + pre_state + post_state + timestamp + federation_id + agent
  }
  ```
  Does **not** include `was_encrypted`, `finality`, `effects_hash`,
  `previous_receipt_hash`, `routing_directives`, `derivation_records`,
  or `emitted_events` — all of which `receipt_hash`
  (`turn/src/turn.rs:586-655`) does include. A signature-only verifier
  sees a strictly weaker statement than a receipt-hash verifier.
- **Severity.** MEDIUM. `was_encrypted` is bound by `receipt_hash` so a
  full-receipt verifier catches mismatches; but downstream consumers
  documented as relying on "the narrow recoverable claim" silently lose
  the encryption-path provenance, finality status, and effects shape.
- **Closure plan.** Bump to `executor-receipt-sig-v3:` covering at
  least `was_encrypted`, `finality`, `effects_hash`,
  `previous_receipt_hash`. Update verifiers downstream. Effort: small.
  See `EXECUTOR-VK-AUDIT.md §6.5`.

### T1.7 — Atomic execution paths emit no `TurnReceipt`

- **Claim source.** `EXECUTOR-VK-AUDIT.md §2.1` central law:
  *"execute_turn(S,T) = (S',R) ⇒ verify_receipt(R, commit(S')) ∧
  R.statement == semantics(T)"*. The receipt chain is the canonical
  audit trail per `DESIGN-receipts.md`.
- **Code reality.** `turn/src/executor.rs:12319-12547`
  `execute_atomic_sovereign(&self, atomic_turn, ledger)
  -> Result<Vec<[u8; 32]>, AtomicTurnError>` — returns just the new
  commitments, **no `TurnReceipt`**.
  `turn/src/executor.rs:12572-12916` `execute_mixed_atomic` returns a
  `MixedAtomicResult { balance_deltas, commitments }` — also no
  receipt. An agent that mixes atomic and normal turns has a
  structurally incomplete audit trail; `verify_receipt_chain` cannot
  detect the gap because there is no entry to inspect.
- **Severity.** HIGH for any deployment that uses atomic paths.
- **Closure plan.** Change both signatures to return
  `Result<(TurnReceipt, …), AtomicTurnError>`. The receipt carries the
  same `effects_hash` / `pre_state` / `post_state` / `agent` discipline
  as the cleartext path. Effort: medium. See `EXECUTOR-VK-AUDIT.md §6.2`.

### T1.8 — "Federation unified" — Morpheus dead code still imported

- **Claim source.** `NEW-WORLD.md:70-71` *"`Federation` (unified after
  this season) — Subsumes the four prior disjoint concepts."*
  `FEDERATION-UNIFICATION-DESIGN.md` celebrates the collapse.
- **Code reality.** `federation/src/lib.rs:84-102` carries an explicit
  in-source comment: *"the Morpheus BFT simulator (`node.rs` +
  `transport.rs`) is **legally dead** — `dregg-blocklace` is the live
  consensus path. The simulator survives as in-crate code only because
  `teasting`, `wasm`, and `demo/sdc-consensus` still import it."* The
  simulator is re-exported as `MorpheusFederation`. ~2515 LOC of dead
  code in tree per `NEW-WORLD.md:243` (item 7).
- **Severity.** LOW (operational confusion, not soundness).
- **Closure plan.** Land Morpheus retirement Block 6: migrate
  `teasting/`, `wasm/`, `demo/sdc-consensus` off the simulator; delete
  `federation/src/node.rs` + `transport.rs`; remove the
  `MorpheusFederation` re-export. Effort: medium (3 downstream
  migrations).

### T1.9 — `BOUNDARIES.md` is "discipline" but is rustdoc convention

- **Claim source.** `NEW-WORLD.md:128-137` *"`BOUNDARIES.md` names 14
  boundaries with a unified vocabulary."* — implies enforcement.
- **Code reality.** `NEW-WORLD.md:137` itself admits: *"The doc names
  nine inconsistencies (e.g., `FieldVisibility::Committed` hides from
  external readers but NOT from the host executor; sovereign cells
  *intended* to hide from host, implementation does not yet
  algebraically enforce). The vocabulary is a *rustdoc convention*, not
  a new type system."*
- **Severity.** LOW (the vocabulary itself is valuable; the gap is
  between named discipline and enforced types).
- **Closure plan.** Either (a) tighten language in `BOUNDARIES.md` and
  marketing — say "vocabulary" not "discipline", or (b) promote each of
  the 9 inconsistencies to a type-state in cell / turn. (a) is
  zero-cost; (b) is per-inconsistency medium.

### T1.10 — `EXECUTOR-HONESTY-AUDIT` T12 "closed" omits 30-bit truncation

- **Claim source.** `EXECUTOR-HONESTY-AUDIT.md` lists T12 ("lie about
  balance deltas") as defended at AIR via
  `compute_balance_delta_from_effects` (`NEW-WORLD.md:150`).
- **Code reality.** True for BabyBear-arithmetic of the *low 30 bits*;
  the 30-bit truncation in `BridgeMint/Lock/CreateEscrow` (see T2.5
  below) means the AIR algebraically endorses a value truncated mod
  `2^30`. The honest framing: T12 is closed *modulo `2^30`*, not in
  full. The audit ledger does not say "modulo 2^30."
- **Severity.** MEDIUM — readers of the threat ledger take "closed" at
  face value.
- **Closure plan.** Update `EXECUTOR-HONESTY-AUDIT.md` to disclose the
  modulus. The proper fix is closure of T2.5 (real range proofs); the
  ledger update is a one-line documentation honesty fix in the
  meantime. Effort: trivial doc + medium code.

### T1.11 — "Slop-list deleted, apps/ remains alongside"

- **Claim source.** `NEW-WORLD.md:178` *"The slop-list (`amm`,
  `lending`, `orderbook`, `stablecoin`, `dao-treasury`,
  `prediction-market`) is already deleted."*
- **Code reality.** Six apps are indeed deleted (verified). But
  `NEW-WORLD.md:176` *"The legacy `apps/` retires as starbridge-apps
  replace each one"* — both `apps/` and `starbridge-apps/` exist in
  tree simultaneously, with no deletion date. Dual-shipping pattern.
- **Severity.** LOW (cultural / cognitive).
- **Closure plan.** Set a deletion date per legacy app; track migration
  in a single tracker line; delete on completion. Effort: per-app
  small.

### T1.12 — `StubCustomEffectVerifier` exists and ships in the platform crate

- **Claim source.** None directly; but `NEW-WORLD.md:39` describes
  Effect VM AIR as "proves the trace of an entire turn" — implying
  custom effects produce real verifiers.
- **Code reality.** `cell/src/custom_effect.rs:377-411`
  `StubCustomEffectVerifier`: same permissive shape as
  `StubVerifier` — requires non-empty proof bytes, ignores public
  inputs. No default registry installs it (an app must explicitly
  register it), so it is *less dangerous* than the WitnessedPredicate
  default of `with_stubs()`. However, the type lives in the production
  `dregg-cell` crate's public surface.
- **Severity.** LOW (unless an app's host wiring uses
  `StubCustomEffectVerifier::new(...)` in production).
- **Closure plan.** Either (a) move to a `dregg-cell-testing`
  sub-crate, or (b) rename `StubCustomEffectVerifier` →
  `DevelopmentOnlyStubCustomEffectVerifier` and add a
  `#[cfg(not(feature = "production"))]` gate. Effort: small.

---

## §2. Tier 2: Acknowledged Silver-vs-Golden debt

Each entry: the current Silver-Sound check, the missing Golden
cryptographic constraint, the AIR/STARK design sketch for closure,
severity, blocked-by relations.

### T2.1 — `QueueEnqueue` / `QueueDequeue` / `QueueResize` AIR placeholders

- **Site.** `turn/src/executor.rs:3360-3489` —
  `convert_turn_effects_to_vm` arm for
  `Effect::QueueEnqueue/Dequeue/Resize/AtomicTx`.
- **Silver check (real).** The executor's `apply_effect` enforces the
  actual queue capacity / head / arithmetic against `Ledger` state
  (`turn/src/executor.rs` queue-effect application sites).
- **Missing Golden constraint.** The AIR's PI for these arms is
  hard-coded placeholders:
  - `QueueEnqueue`: `queue_len: 0, program_vk: BabyBear::ZERO`
    (executor.rs:3384-3385).
  - `QueueDequeue`: `expected_message_hash` = domain-tagged
    `BLAKE3("DREGG_DEQUEUE_HEAD/v1" || queue_id)` (executor.rs:3409-3414);
    not anchored to the actual head.
  - `QueueResize`: `old_capacity: 0` (executor.rs:3434).
  - `QueueAtomicTx`: `combined_old_root = hash_to_bb(cell_id)`
    (executor.rs:3479); not anchored to the cell's actual queue root.
  The AIR's "queue not full" / "delta correct" / "transition real"
  constraints are satisfiable by *any* projection — the proof attests
  nothing about real queue state.
- **Closure design sketch.** Extend the runtime `Effect::Queue*`
  variants to carry the read values (queue_len, program_vk, old_capacity,
  head_hash, combined_old_root) as additional fields, and have
  `convert_turn_effects_to_vm` source them from
  `ledger.get(queue_cell).state.fields[..]`. The runtime variant change
  is back-compat (new fields are filled at the convert site, not the
  builder).
- **Severity.** MEDIUM (scope-1 Golden-only verifier accepts weaker
  statements; scope-2 inline-trace replay catches divergence).
- **Blocked by.** Nothing — ledger access is local.

### T2.2 — `ExportSturdyRef` / `EnlivenRef` / `DropRef` AIR placeholders

- **Site.** `turn/src/executor.rs:3940-4055`.
- **Silver check (real).** Executor's apply_effect verifies refcount,
  swiss-table membership, and permissions against ledger state.
- **Missing Golden constraint.** `ExportSturdyRef` projects
  `permissions: BabyBear::ZERO, export_counter: 0`
  (executor.rs:3985-3987); the AIR's swiss derivation
  `hash_2_to_1(cell_id, hash_2_to_1(random_seed, counter))` is
  self-consistent with any chosen (random_seed, counter). `EnlivenRef`
  derives `expected_cell_id` from
  `BLAKE3("DREGG_SWISS_TABLE_LOOKUP/v1" || swiss || bearer)`
  (executor.rs:4017-4020) rather than reading the *target's*
  swiss_table_root from the ledger. `DropRef` projects
  `current_refcount: 1` (executor.rs:4054); the `refcount > 0` check is
  trivially satisfied.
- **Closure design sketch.** Extend runtime variants to carry the
  permissions mask + counter + actual swiss-table-root +
  current_refcount. Source from `ledger.get(target).state.fields[5..]`.
- **Severity.** MEDIUM (capability-graph properties under-attested).
- **Blocked by.** Nothing.

### T2.3 — `ValidateHandoff` placeholder

- **Site.** `turn/src/executor.rs:4057-4100` —
  `Effect::ValidateHandoff { cert_hash }`.
- **Silver check (real).** Federation-side verification of
  `HandoffCertificate` happens out-of-AIR via the CapTP path.
- **Missing Golden constraint.** AIR derives `recipient_pk` and
  `introducer_pk` from domain-tagged hashes of `(cert_hash, cell_id)`
  (executor.rs:4088-4096) rather than from the real handoff cert.
  Partially fixed: `approved_set_root` is now sourced from the
  federation's `PI[APPROVED_HANDOFFS_BASE]` (executor.rs:4080-4087), so
  the membership constraint binds; but the recipient / introducer pks
  do not.
- **Closure design sketch.** Carry `(cert_hash, recipient_pk,
  introducer_pk)` through the runtime variant.
- **Severity.** MEDIUM.
- **Blocked by.** Nothing.

### T2.4 — Sovereign-witness transition-proof VK hash is zero sentinel

- **Site.** `turn/src/executor.rs:3089-3115`
  `SOVEREIGN_TRANSITION_PROOF_VK_HASH_BASE` written all-zeros; comment:
  *"the recursive verifier exposes a stable VK in a follow-up."*
- **Silver check (real).** Per-cell witness proofs are verified by the
  executor against a registered transition-proof verifier
  (per-deployment).
- **Missing Golden constraint.** The AIR's PI does not bind to *which*
  verifier was used. A future recursive-verifier upgrade silently
  changes what is attested.
- **Closure design sketch.** Surface the recursive verifier's VK hash
  via `circuit::recursive_witness_bundle::compute_recursive_vk_hash()`
  into the AIR's PI on the sovereign-witness boundary.
- **Severity.** MEDIUM (specific to sovereign-cell deployments).
- **Blocked by.** Recursive-verifier VK rotation story (T3.5 below).

### T2.5 — 30-bit value truncation in `BridgeMint` / `BridgeLock` / `CreateEscrow`

- **Site.** `circuit/src/effect_vm.rs:835` *"30-bit value-truncation
  fix (CAVEAT-LAYER-COVERAGE.md §6.5)"*; `circuit/src/effect_vm.rs:899-901`
  documents the fix columns `BRIDGE_MINT_VALUE_LIMBS[4]`,
  `BRIDGE_LOCK_VALUE_LIMBS[4]`, `CREATE_ESCROW_AMOUNT_LIMBS[4]`. The
  *new* (opt-in 4-limb) path is wired; **the legacy 30-bit `*_lo`
  arithmetic remains alive on the conservation lane**
  (`circuit/src/effect_vm.rs:5760-5762` — the conservation summation
  uses `value_full` correctly, but the *interior balance-delta
  arithmetic* on rows `4956 / 6707` debits `amount_lo` / `value_lo`).
  See also `circuit/src/effect_vm.rs:2305-2326` `TODO(range-checks)` /
  `TODO(underflow)`.
- **Silver check (real).** `compute_balance_delta_from_effects` in the
  executor sums `value_full` so cleartext conservation is correct.
  Cross-checked by `bridge_lock_action_air::SCHEMA_BRIDGE_LOCK`'s
  `tamper_value_above_2_pow_30_rejected` test
  (`circuit/src/bridge_lock_action_air.rs:274`) — that schema *does*
  enforce full 64-bit binding.
- **Missing Golden constraint.** A range-proof gadget enforcing
  in-circuit that `value_full` ∈ [0, 2^64) and that
  `value_lo = value_full mod 2^30` — without the gadget, a malicious
  prover can put out-of-30-bit-range `value_lo` on interior rows whose
  effect is invisible to the conservation lane.
- **Closure design sketch.** Add log-derivative lookup arguments for
  16-bit-per-limb range checks (the `TODO(range-checks)` site already
  notes "log-derivative or LogUp"). 4-limb decomposition under range
  lookups. Effort: large (~1 week, new lookup gadgets).
- **Severity.** MEDIUM (closed via the per-action `effect_action_air`
  schemas for new spends; legacy `effect_vm` interior path still
  carries the truncation).
- **Blocked by.** Lookup-argument plumbing in the underlying STARK
  backend.

### T2.6 — `recursive_witness_bundle` proves a structural-subset AIR

- **Site.** `circuit/src/recursive_witness_bundle.rs:50-58` (doc
  comment), `:354-403` (`verify_recursive_proof_variant`).
- **Silver check (real).** The recursive aggregation IS real: the inner
  STARK is cryptographically verified, the recursive VK hash is
  registry-looked-up, the PI is cross-bound to caller-supplied
  `expected_pi_u32`. Inline-trace replay (scope-2) remains
  authoritative.
- **Missing Golden constraint.** The inner AIR is `EffectVmShapeAir`
  (`circuit/src/effect_vm_p3_air.rs`), a *structural subset* of the
  full `EffectVmAir::eval_constraints`. A trace accepted by
  `EffectVmShapeAir` is not guaranteed to satisfy the full Effect VM
  constraint set.
- **Closure design sketch.** Mechanically translate every selector
  branch of `EffectVmAir::eval_constraints` into `EffectVmShapeAir::eval`.
  The doc comment at `recursive_witness_bundle.rs:60-63` calls this "a
  mechanical translation task." Effort: large (~2 weeks).
- **Severity.** LOW for Silver (inline trace authoritative); HIGH for
  any Golden-only deployment.
- **Blocked by.** Nothing structural — work is per-selector-branch
  translation.

### T2.7 — `SortedNeighborNonMembershipVerifier` adjacency tag is a public sentinel

- **Site.** `cell/src/predicate.rs:1291-1380`
  `SortedNeighborNonMembershipVerifier`; sentinel
  `NonMembershipNeighborProof::CONSECUTIVE_TAG` at
  `cell/src/predicate.rs:1288` = `[0xFE; 32]`.
- **Silver check (real).** The verifier enforces structural ordering
  `lower < candidate < upper` (byte-lex) and checks the sentinel tag.
  Per `cell/src/predicate.rs:611-615`, an `adjacency_tag` field
  *intended* to bind `(commitment, lower, upper)` is referenced in the
  doc, but the implementation at line 1349 still checks against the
  fixed `[0xFE; 32]` public constant.
- **Missing Golden constraint.** A real Merkle adjacency proof binding
  `lower` and `upper` to the set whose root is `commitment` with
  `leaf_index(upper) == leaf_index(lower) + 1`.
- **Attack with current sentinel.** Construct any `lower = 0x00…00,
  upper = 0xFF…FF, tag = 0xFE…FE`; verifier accepts non-membership
  against any set, any candidate (`AIR-SOUNDNESS-AUDIT.md §2.J`,
  lines 292-302).
- **Closure design sketch.** Either (a) replace the sentinel with a
  per-`(set, lower, upper)` adjacency commitment computed from the
  sorted set's adjacency table, or (b) compose with a real STARK
  gadget proving Merkle inclusion of both leaves at consecutive
  indices. (b) is categorically correct.
- **Severity.** HIGH (governance recusal / `Renounced` predicate
  trivially forgeable).
- **Blocked by.** Nothing for (a); (b) needs a Merkle-adjacency AIR.

### T2.8 — `default_builtins()` `NotYetWiredVerifier` rejects every non-NonMembership kind

- **Site.** `cell/src/predicate.rs:646-657`.
- **Silver check (real).** Improved from the audit's reported state:
  the registry now defaults to `NotYetWiredVerifier` (which *rejects*)
  instead of `StubVerifier` (which *accepted any non-empty bytes*).
  Honest fail-closed posture.
- **Missing Golden constraint.** No real DFA / Temporal /
  MerkleMembership / BlindedSet / BridgePredicate / PedersenEquality
  verifier is installed. Production hosts must wire one — and no
  in-tree host does.
- **Closure design sketch.** See T1.4 — `dregg-witnessed-registry-default`
  crate populating all six kinds from their DSL backings.
- **Severity.** MEDIUM (`Witnessed` slot caveats / preconditions /
  `Authorization::Custom` of every kind except `NonMembership` are
  unusable; the rejection is honest but the feature is undelivered).
- **Blocked by.** T1.4.

### T2.9 — `multi_step_air::MultiStepStarkAir` returns zero constraints

- **Site.** `circuit/src/multi_step_air.rs:167-207`. Doc comment marks
  it `DEPRECATED`; `eval_constraints` returns `BabyBear::ZERO`;
  `boundary_constraints` returns `vec![]`.
- **Silver check.** None — the AIR is empty.
- **Missing Golden constraint.** Any algebraic enforcement at all.
- **Caller.** `chunked_derivation::verify_chunked_authorization`
  (`circuit/src/chunked_derivation.rs:235, :354`) chains the deprecated
  `verify_authorization_stark`. Cross-chunk root chaining is real;
  per-chunk STARK semantics are vacuous.
- **Closure design sketch.** Delete `MultiStepStarkAir` +
  `verify_authorization_stark`; migrate
  `chunked_derivation::verify_chunked_authorization` to
  `dsl::derivation::verify_authorization_dsl`
  (`circuit/src/dsl/derivation.rs:1033`). Effort: medium.
- **Severity.** HIGH for any caller of these surfaces.
- **Blocked by.** Nothing.

### T2.10 — `RateLimit` / `PreimageGate` evaluated with hard-coded placeholder context

- **Site.** `turn/src/executor.rs:4361-4373` `EvalContext` build:
  `sender_epoch_count: 0` (placeholder), `revealed_preimage: None`
  (placeholder). Per `CAVEAT-LAYER-COVERAGE.md:127-128`.
- **Silver check.** Partial: `block_height`, `timestamp`, `sender` are
  honest; `current_epoch` is heuristic (`height/1024`).
- **Missing Golden constraint.** `RateLimit { max_per_epoch, … }` always
  passes because `0 >= max_per_epoch` is false for any positive cap.
  `PreimageGate` always errors with `MissingContextField { field:
  "revealed_preimage" }` — any cell declaring it cannot transition.
  `HashKind::Poseidon2` in `PreimageGate` is itself a stub that
  BLAKE3-hashes a tagged buffer rather than calling Poseidon2
  (`cell/src/program.rs:1014-1022`, per
  `CAVEAT-LAYER-COVERAGE.md:89`).
- **Closure design sketch.** Plumb `sender_epoch_count` from a
  per-(cell, sender, epoch) counter the executor maintains. Plumb
  `revealed_preimage` from `action.witness_blobs` of
  `WitnessKind::Preimage32`. Wire `HashKind::Poseidon2` to the real
  `circuit::poseidon2` gadget.
- **Severity.** MEDIUM (constraint variants exist in the schema as
  pure traps).
- **Blocked by.** Caveat-correctness lane (named in
  `CAVEAT-LAYER-COVERAGE.md:148`).

### T2.11 — `BoundDelta` / `TemporalPredicate` / `Witnessed` / `Custom` cell-program variants reject unconditionally

- **Site.** `cell/src/program.rs:826-833`:
  `BoundDeltaNotWired`, `TemporalPredicateWitnessMissing`,
  `WitnessedPredicateRequiresExecutor`, `CustomConstraintUnevaluable`
  — all surface to `TurnError::ProgramViolation`. Per
  `CAVEAT-LAYER-COVERAGE.md:92-96`.
- **Silver check.** Partial: `Witnessed` is now intercepted at
  executor level and dispatched through the registry (see T1.4);
  `BoundDelta`, `TemporalPredicate`, `Custom` are still unconditional
  rejects at evaluation time.
- **Missing Golden constraint.** `BoundDelta` needs the executor to
  fetch the peer cell's state and run the cross-cell match;
  `bilateral_aggregation_air` exists for the γ.2 aggregate but the
  per-cell hookup is missing. `TemporalPredicate` needs dispatch to
  `circuit::temporal_predicate_dsl::verify_temporal_predicate` (after
  T1.5 binding fix). `Custom` needs dispatch into the
  `dregg-dsl-runtime` (the crate exists; the executor never reaches
  it).
- **Closure design sketch.** Per variant: intercept at executor's
  cell-program evaluation site, dispatch through the appropriate
  verifier/runtime. Effort: per-variant medium.
- **Severity.** HIGH (declared cell programs using these variants
  cannot transition).
- **Blocked by.** T1.4 (registry default), T1.5 (Temporal binding).

### T2.12 — `note_bridge::verify_portable_note` trusts caller-vetted roots

- **Site.** `cell/src/note_bridge.rs:1181-1252`.
- **Silver check.** Destination-federation match + structural equality
  on `(merkle_root, height, note_tree_root)` against
  `trusted_roots: &[AttestedRoot]`. Caller-provided closure verifies
  the STARK.
- **Missing Golden constraint.** `AttestedRoot::is_valid_with_keys` is
  not called inside `verify_portable_note` — the verifier assumes the
  caller pre-vetted the roots. If a caller hands an unvetted attested
  root through, the verifier accepts.
- **Closure design sketch.** Replace the `iter().any(...)` structural
  match (lines 1201-1205) with `trusted_roots[i].is_valid_with_keys(
  &federation_keys)` for the matched entry. Alternatively, document
  the precondition + add a `debug_assert!`.
- **Severity.** MEDIUM.
- **Blocked by.** Nothing.

### T2.13 — `AttestedRoot::is_valid` ThresholdQC arm is structural-only

- **Site.** `types/src/lib.rs:386-394`. When `threshold_qc.is_some()`,
  `is_valid` checks `qc.0.len() >= 48` only — no cryptographic BLS
  verification.
- **Silver check.** Length check + signature validation when not using
  the BLS QC path.
- **Missing Golden constraint.** A real BLS aggregate verification when
  the QC is present.
- **Closure design sketch.** Wire `hints` crate's BLS aggregate
  verifier (already pulled in elsewhere per `types/src/lib.rs:387-388`
  comment) into this arm. Effort: medium.
- **Severity.** MEDIUM (federation contexts that rely on `is_valid`
  for BLS QCs are silently structurally-checked-only).
- **Blocked by.** `hints` integration maturity.

### T2.14 — `effect_vm` interior-row limb-range / underflow checks deferred to executor

- **Site.** `circuit/src/effect_vm.rs:2305-2328` `TODO(range-checks)`
  / `TODO(underflow)`. Also `circuit/src/effect_vm/air.rs:107-128`
  (duplicate site).
- **Silver check.** Executor-side cross-check of pre-transaction
  balance bounds rejects malformed interior limbs that violate range.
- **Missing Golden constraint.** In-circuit lookup-based range proofs
  on every limb. BabyBear subtraction wraps; underflow protection is
  executor-side only.
- **Closure design sketch.** Add log-derivative lookup arguments
  (same plumbing needed for T2.5). Effort: large.
- **Severity.** LOW (executor cross-check is exercised on every
  action); HIGH for federation-context attackers who could control
  inter-row state.
- **Blocked by.** Lookup-argument backend support.

### T2.15 — γ.2 Phase 2 joint aggregation AIR not yet landed

- **Site.** `NEW-WORLD.md:86-91`; `STAGE-7-GAMMA-2-PI-DESIGN.md`;
  `STAGE-7-GAMMA-2-PHASE-2-SKETCH.md`. Substrate
  (`plonky3_recursion_impl` generalization, "Block 1") landed; the
  joint outer AIR has not.
- **Silver check (real).** Phase 1: both sides produce independent
  proofs whose PIs cross-validate via the off-AIR
  `dregg-verifier bilateral-pair` subcommand.
- **Missing Golden constraint.** A single outer proof that verifies
  both inner proofs *and* enforces cross-cell agreement
  algebraically. Without Phase 2, multi-cell bilateral consistency is
  a verifier-side check, not an in-circuit one.
- **Closure design sketch.** Land `BilateralAggregationAir` consuming
  per-cell PIs through `circuit::recursive_witness_bundle`; gate
  acceptance on `outgoing_<kind>_root == incoming_<kind>_root`
  per-pair.
- **Severity.** LOW for Silver (verifier-side check exists);
  Golden-blocking.
- **Blocked by.** T2.6 (recursive AIR must cover full Effect VM
  constraints first).

### T2.16 — `RECURSIVE_VK_PROGRAM_BYTES` baked at compile time; no rotation

- **Site.** `circuit/src/recursive_witness_bundle.rs:105`
  `RECURSIVE_VK_PROGRAM_BYTES` is a `const`. The "registry"
  `lookup_recursive_vk` accepts one allowed value:
  `compute_recursive_vk_hash()`.
- **Silver check (real).** Single-binary recursive VK consistency: any
  binary version verifies its own proofs.
- **Missing Golden constraint.** No multi-version VK lineage. A code
  change that bumps `RECURSION_P3_REV` or alters
  `recursive_verifier_source_hash()` silently invalidates every
  existing recursive proof at the next binary run.
- **Closure design sketch.** Add `AirVersion: u32` to PI; verifiers
  carry an accepted-versions list; stored verifiers for old versions
  keep old proofs verifying. Houyhnhnm "typed upgrade function for AIR
  shape" pattern (see T3.5).
- **Severity.** MEDIUM (acceptable for single-binary deployments;
  blocks any multi-deployment federation).
- **Blocked by.** T3.5.

### T2.17 — `EncryptedTurn.turn_commitment` not bound back into receipt

- **Site.** `turn/src/encrypted.rs:71` `turn_commitment = BLAKE3(
  serde_json::to_vec(turn))`. `turn/src/turn.rs:269` `Turn::hash` is v3
  canonical layout. `receipt.turn_hash` uses `Turn::hash`;
  `turn_commitment` is nowhere in the receipt.
- **Silver check (real).** The `was_encrypted` bit is in
  `receipt_hash` (turn.rs:653) — observers know the receipt came from
  *some* encrypted envelope.
- **Missing Golden constraint.** Binding to *which* envelope a
  federation ordered. A third party can't prove "this receipt is the
  result of the envelope I observed being ordered."
- **Closure design sketch.** Add
  `TurnReceipt.encrypted_envelope_commitment: Option<[u8;32]>`;
  populated on the encrypted-turn path; included in both
  `receipt_hash` and the canonical executor signed message.
- **Severity.** MEDIUM.
- **Blocked by.** Nothing. See `EXECUTOR-VK-AUDIT.md §6.6`.

### T2.18 — Receipts are not VK-self-describing

- **Site.** `turn/src/turn.rs:580+` `TurnReceipt` has no `vk_hash` or
  `vk_set_commitment` field. `turn/src/witnessed_receipt.rs:243-264`
  `WitnessedReceipt` carries `proof_bytes`, `public_inputs`, optional
  `WitnessBundle`, but no outer VK identifier (the inner
  `RecursiveProofVariant` does carry `recursive_vk_hash`, but the
  outer Effect-VM proof has no explicit VK).
- **Silver check (real).** Verifiers infer the VK from the cell's
  stored VK at replay time.
- **Missing Golden constraint.** Without a per-receipt VK identifier,
  a long-running verifier holding a chain of historical receipts
  cannot tell which VK was in force at each step without replaying
  state. Prerequisite for any constitutional-migration story (T3.4).
- **Closure design sketch.** Add `TurnReceipt.vk_set_commitment:
  [u8;32]` commitment to the set of `(cell_id, vk_hash)` pairs the
  executor used during the turn. Include in `receipt_hash` and the
  canonical signed message.
- **Severity.** MEDIUM.
- **Blocked by.** Nothing. See `EXECUTOR-VK-AUDIT.md §6.1`.

---

## §3. Tier 3: Architectural debt

Structural smells. Refactor cost: small / medium / large / painful.

### T3.1 — `turn/src/executor.rs` is 13,916 lines with 14 `match effect` blocks

- **Site.** `turn/src/executor.rs` (13,916 lines).
  Match-on-effect blocks at lines 2555, 2659, 3301, 4151, 7237, 7400,
  10771, 10823, 10902, 10965, 11414, 11554, 11605, 11894 — *the same
  enum is re-walked at minimum 14 times* for different concerns
  (authorization, conservation, AIR projection, journal entries,
  capability check, …).
- **Design implication.** Adding a new `Effect` variant requires editing
  14 match statements in one file. A change to authorization touches
  the same file as a change to receipt shape touches the same file as
  a change to conservation rules. The "polycentric kernels" tenet from
  Ch.6 — *runtime model is polycentric, codebase is monolithic*. The
  monolith is the kernel-shaped lump.
- **Closure design sketch.** Split into
  `turn/src/effects/{transfer,capability,state,escrow,obligation,queue}.rs`
  per Houyhnhnm critique §2.4. `TurnExecutor` becomes a dispatcher;
  the 14 match-on-effect blocks collapse to one trait method per
  family. Conservation, authorization, AIR-projection move into each
  family's module. Behavior-preserving rearrangement.
- **Refactor cost.** Large (~2 weeks). High-leverage enabler for
  T2.1–T2.4 closure work (each placeholder closure becomes a PR
  against one ~500-line file instead of one ~14k-line file).

### T3.2 — Two divergent `ProofVerifier` traits

- **Sites.** `turn/src/executor.rs:315-320`
  `trait ProofVerifier { fn verify(proof, action, resource, vk: &[u8]) -> bool }`
  (returns `bool`, takes `vk: &[u8]` data — no `vk_hash`).
  `wire/src/server.rs:44-47`
  `trait ProofVerifier { fn verify(proof, action, resource) -> Result<bool, String> }`
  (no `vk` param at all).
- **Design implication.** Two traits with the same name and different
  semantics. Executor trait drops `vk_hash` entirely — an impl can
  verify against any AIR. The v2 separation between
  `(program, AIR, verifier_impl, proving_system)` is not surfaced into
  the auth-time verifier interface.
- **Closure design sketch.** Unify into one trait accepting the full
  `VkComponents` (or `(vk_hash, air_fingerprint, proving_system_id)`),
  returning `Result<(), VerifyError>`. See `EXECUTOR-VK-AUDIT.md §6.9`.
- **Refactor cost.** Medium (trait unification + impl migration).

### T3.3 — 16-byte VK hash truncation in custom-effect AIR dispatch

- **Site.** `turn/src/executor.rs:1973` calls
  `Self::expand_vk_hash_16_to_32(&vk_hash_bytes)` against PI carrying
  only 4 BabyBear elements = 16 bytes of the 32-byte VK hash.
  `executor.rs:3005-3009`:
  ```rust
  fn expand_vk_hash_16_to_32(short: &[u8; 16]) -> [u8; 32] {
      let mut result = [0u8; 32];
      result[..16].copy_from_slice(short);
      result
  }
  ```
- **Design implication.** 80-bit security in the custom-effect dispatch
  lane vs. 128-bit elsewhere. Two distinct v2 hashes whose lower
  16 bytes collide map to the same registered program (birthday-bound
  2^64).
- **Closure design sketch.** Widen the AIR's custom-effect PI to
  8 BabyBear elements (32 bytes); `expand_vk_hash_16_to_32` becomes
  unnecessary. See `EXECUTOR-VK-AUDIT.md §6.4`.
- **Refactor cost.** Medium (AIR PI layout change + executor PI
  population + tests).

### T3.4 — No upgrade-discipline for `Effect::SetVerificationKey`

- **Site.** `turn/src/action.rs:524`:
  ```rust
  SetVerificationKey {
      cell: CellId,
      new_vk: Option<dregg_cell::VerificationKey>,
  },
  ```
  `turn/src/executor.rs:7256-7261` (handler) checks only the
  `Action::SetVerificationKey` permission and swaps the hash. No
  required upgrade attestation; no proof that the new VK's program/AIR
  preserves any property of the old. No in-ledger record of which
  program the cell used to have.
- **Design implication.** A malicious or careless owner can replace a
  cell's VK with one whose AIR has totally different semantics, and
  nothing in the ledger flags this. Holders of attenuated caps issued
  against the old rules continue to hold caps "valid" against
  arbitrary new rules. This is the Houyhnhnm "code+data as one history"
  failure (Ch.5).
- **Closure design sketch.** Add `cell/src/program.rs::ProgramTransition
  { from_vk, to_vk, upgrade_witness: WitnessedPredicate,
  state_diff_kind: StateDiffKind }`. Require it on `SetVerificationKey`
  (or `StateDiffKind::Reset { explicit_drops }` for the
  no-migration case, which forces enumeration — linear-logic move).
  Hash the `ProgramTransition` into `Turn::hash`. Effort: medium.
- **Refactor cost.** Medium (new type + effect-variant change + receipt
  coverage + lineage micro-crate).

### T3.5 — No AIR-version protocol; encoder bug = catastrophe

- **Site.** No `AirVersion` in PI. `circuit/src/effect_vm.rs`'s AIR
  shape is the ground truth, *of one version*. If the AIR changes, all
  old VKs silently incompatible. `dregg-dsl-differential` tests
  *predicates* across encoders but not cell-programs.
- **Design implication.** Identity is VK-hash; VK-hash is derived from
  AIR shape; AIR shape is `const` at compile time. Houyhnhnm
  Urbit-trap: a fixed VM with no version-evolution protocol. Encoder
  bug-fixes change VKs even for the *same* program — spuriously
  breaking existing capabilities.
- **Closure design sketch.** Add `AirVersion: u32` to PI. Verifiers
  carry an accepted-versions list. New turns must use the current
  version. Stored old-verifier-binaries keep old proofs verifying. The
  upgrade function `air_v1 → air_v2` is the typed upgrade pattern.
- **Refactor cost.** Large (2 weeks for protocol + first version
  upgrade; ongoing for upgrade-function discipline). Houyhnhnm Ch.10
  diagnostic.

### T3.6 — Identity is VK-hash, not source

- **Site.** `Effect::SetVerificationKey { new_vk:
  Option<VerificationKey> }`; `FactoryDescriptor.program_vk`;
  `WitnessedPredicateKind::Custom { vk_hash }`. None reference a
  canonical source identifier.
- **Design implication.** A contract authored by a vendor that
  subsequently disappears: the federation enforces the `vk_hash`, but
  no one alive can re-derive what the program *did*. Encoder
  bug-fixes change VKs even for the same program. Houyhnhnm Ch.3 "source
  is canonical, binaries are caches" tenet inverted.
- **Closure design sketch.** Add `dregg-program-registry`: a
  content-addressed store of source programs keyed by source-hash, with
  `{source, encoder_version, derived_vk_hash}`. `FactoryDescriptor` and
  `Effect::SetVerificationKey` carry the *source-hash*; verifiers
  derive the vk-hash. Same pattern `dregg-dsl-differential` already
  uses for the predicate sub-language.
- **Refactor cost.** Large (1-2 weeks for the registry; ongoing for
  per-program-source authoring discipline).

### T3.7 — No persistence stream beyond the on-chain ledger

- **Sites.** `wire/` CapTP session state is RAM. Capability handle
  tables in `dregg-sdk` are not in any log. `intent/src/trustless.rs`
  holds in-flight ciphertexts and threshold-decryption shares in
  memory until t-of-n. Blocklace mempool is gossip-layer RAM.
  `starbridge/` browser session is WASM heap.
- **Design implication.** The WitnessedReceipt chain is *a*
  persistence layer, not *the* persistence layer. Houyhnhnm Ch.2
  fractal-persistence requirement violated everywhere outside the
  on-chain path.
- **Closure design sketch.** Pick one non-ledger layer (the trustless
  intent engine is the pragmatic candidate) and commit it to the
  WitnessedReceipt persistence stream: every ciphertext submission,
  every share contribution, every share-collection state transition
  becomes a recorded event in a per-federation event journal or a
  blocklace-meta event class.
- **Refactor cost.** Large per layer (~1 week each; ~5 layers).

### T3.8 — Threat ledger does not record sub-additive blame

- **Site.** `EXECUTOR-HONESTY-AUDIT.md` T1-T15 — single-defense-layer
  per threat. No "(could-catch)" / "(does-catch)" columns.
- **Design implication.** Post-mortems will fall into single-cause
  finger-pointing. Two parties can cooperate today to produce a receipt
  that *looks* OK and breaks an invariant with no one being blamable
  (Houyhnhnm Ch.11 sub-additive blame). The audit's central question
  ("is each threat closed?") doesn't surface the structural question
  ("what is the minimum coalition required to make this fire?").
- **Closure design sketch.** Augment `EXECUTOR-HONESTY-AUDIT.md` with
  `(could-catch)` and `(does-catch)` columns. Reformulate to "for each
  threat, what is the minimum coalition of malicious actors required
  to make it fire?". Subsequent design rule: every invariant has at
  least 2 independent defenders.
- **Refactor cost.** Small (doc edit) + ongoing audit discipline.

### T3.9 — Prover-determinism is undocumented and untested

- **Sites.** STARK backend Fiat-Shamir, recursion-layer challenges,
  Pedersen blinding factors in `value_commitment`. No
  `PROVER-DETERMINISM-AUDIT.md` exists.
- **Design implication.** A WitnessedReceipt scope-2 claim is "I
  re-executed and re-proved." If two honest re-proofs produce
  different proof bytes, the claim is not cryptographically
  bit-identical; only "the verifier accepted both." Caching proofs
  across federations becomes impossible; CRDT-shaped re-proof
  economies become impossible; proofs cannot be a primary key.
  Houyhnhnm Ch.3 "all non-determinism is eliminated or recorded"
  violated implicitly.
- **Closure design sketch.** Enumerate every RNG-consuming call site
  in `circuit/` and `turn/`; declare whether it derives from a
  Fiat-Shamir transcript or not; record where it must. CI test that
  bit-identical re-proofs from the same witness produce the same proof
  bytes for a fixed corpus.
- **Refactor cost.** Small for audit (~1 day); medium-large for
  hardening.

### T3.10 — Storage primitive migrations (Phase 1, Phase 2) pending

- **Site.** `NEW-WORLD.md:242` (item 6); `STORAGE-AS-CELL-PROGRAMS.md`.
  `storage/programmable/*` exists as a separate concept;
  ProgrammableQueue → cell-program migration not landed; CapInbox →
  cell-program migration not landed.
- **Design implication.** The thesis "storage primitives are cell-program
  patterns" is design-doc-only; the architecture is what the code
  does today. Two implementations of "storage" live in tree
  simultaneously.
- **Closure design sketch.** Land Phase 1 (Queue) + Phase 2 (Inbox)
  per the design doc; delete `storage/programmable/` once cell-program
  reference templates cover the surface.
- **Refactor cost.** Medium per phase.

### T3.11 — `coord::BudgetCoordinator` signature verification gaps

- **Site.** `NEW-WORLD.md:241` (item 5); test source has comment
  *"Forged signature not verified in rebalance yet"*. Two real
  security bugs parked.
- **Design implication.** Cross-cell budget coordination accepts
  unverified rebalance signatures today.
- **Closure design sketch.** Wire signature verification at the
  rebalance entry point; promote the test from XFAIL to expected-pass.
- **Refactor cost.** Small.

---

## §4. Enumerated honesty-debt markers (master list for CI)

One row per marker. **CI greps source for these tokens and checks the
result against this table.** A token in source not enumerated here →
build fails. A row here that no longer matches source → build fails
(forces cleanup at closure).

| file:line | marker | what's lying | tier | linked debt |
|---|---|---|---|---|
| `turn/src/executor.rs:3368` | `TODO[block1-bind]` | QueueEnqueue queue_len placeholder | 2 | T2.1 |
| `turn/src/executor.rs:3384` | `TODO[block1-bind]` (`queue_len: 0`) | AIR binds zero, not real queue length | 2 | T2.1 |
| `turn/src/executor.rs:3385` | `TODO[block1-bind]` (`program_vk: ZERO`) | AIR binds zero, not real program VK | 2 | T2.1 |
| `turn/src/executor.rs:3405` | `TODO[block1-bind]` | QueueDequeue head not anchored to actual head | 2 | T2.1 |
| `turn/src/executor.rs:3427` | `TODO[block1-bind]` | QueueResize old_capacity placeholder | 2 | T2.1 |
| `turn/src/executor.rs:3434` | `TODO[block1-bind]` (`old_capacity: 0`) | AIR binds zero | 2 | T2.1 |
| `turn/src/executor.rs:3478` | `TODO[block1-bind]` | QueueAtomicTx combined_old_root not anchored | 2 | T2.1 |
| `turn/src/executor.rs:3968` | `TODO[block1-bind]` | ExportSturdyRef permissions placeholder | 2 | T2.2 |
| `turn/src/executor.rs:4010` | `TODO[block1-bind]` | EnlivenRef expected_cell_id from synthetic hash | 2 | T2.2 |
| `turn/src/executor.rs:4042` | `TODO[block1-bind]` | DropRef current_refcount: 1 placeholder | 2 | T2.2 |
| `turn/src/executor.rs:4077` | `TODO[block1-bind]` | ValidateHandoff recipient/introducer pks synthetic | 2 | T2.3 |
| `turn/src/executor.rs:3089-3091` | `SOVEREIGN_TRANSITION_PROOF_VK_HASH_BASE` zero sentinel | sovereign transition proof VK not bound | 2 | T2.4 |
| `turn/src/executor.rs:1973, 3005` | `expand_vk_hash_16_to_32` | 80-bit VK truncation in custom-effect dispatch | 3 | T3.3 |
| `circuit/src/effect_vm.rs:2305` | `TODO(range-checks)` | balance limb range proofs deferred to executor | 2 | T2.14 |
| `circuit/src/effect_vm.rs:2326` | `TODO(underflow)` | non-negative range proof deferred | 2 | T2.14 |
| `circuit/src/effect_vm/air.rs:107` | `TODO(range-checks)` (duplicate site) | same as 2305 | 2 | T2.14 |
| `circuit/src/effect_vm/air.rs:128` | `TODO(underflow)` (duplicate site) | same as 2326 | 2 | T2.14 |
| `circuit/src/effect_vm.rs:835` | "30-bit value-truncation fix" comment | opt-in 4-limb path; legacy 30-bit `*_lo` alive on interior balance arithmetic | 2 | T2.5 |
| `circuit/src/effect_vm.rs:734` | `TODO[γ.2.1]` | γ.2 Phase 2 AIR aux columns + boundary binding pending | 2 | T2.15 |
| `circuit/src/multi_step_air.rs:167-207` | `eval_constraints` returns `BabyBear::ZERO` | deprecated stub AIR with no constraints | 2 | T2.9 |
| `circuit/src/derivation_air.rs:382` | "DEPRECATED: stub that delegates" | same pattern as multi_step_air | 2 | T2.9 |
| `intent/src/trustless.rs:682` | `MockProofVerifier` (`#[deprecated]`) | accepts any non-empty proof bytes | 1 | T1.2 |
| `intent/src/trustless.rs:761` | `WitnessedProofVerifier::with_stub_registry()` as default | non-strict default = legacy mock semantics | 1 | T1.2 |
| `cell/src/predicate.rs:646-657` | `NotYetWiredVerifier` for 6 of 7 builtin kinds | every kind except NonMembership rejects | 2 | T2.8 |
| `cell/src/predicate.rs:1288` | `CONSECUTIVE_TAG: [u8; 32] = [0xFE; 32]` | public sentinel — sorted-neighbor not commitment-bound | 2 | T2.7 |
| `cell/src/custom_effect.rs:377` | `StubCustomEffectVerifier` | accepts any non-empty proof bytes for custom effects | 1 | T1.12 |
| `cell/src/cell.rs:36-46` | `VerificationKey::new` raw BLAKE3 + `from_parts` no integrity | VK struct has no v2 invariant | 1 | T1.3 |
| `cell/src/program.rs:1014-1022` | `HashKind::Poseidon2` BLAKE3 stub | stubbed Poseidon2 in PreimageGate | 2 | T2.10 |
| `cell/src/program.rs:826` | `BoundDeltaNotWired` | cell evaluator unconditionally rejects BoundDelta | 2 | T2.11 |
| `cell/src/program.rs:828` | `TemporalPredicateWitnessMissing` | hard-reject without dispatching to verifier | 2 | T2.11 |
| `cell/src/program.rs:833` | `WitnessedPredicateRequiresExecutor` | hard-reject; executor intercepts but registry default rejects | 2 | T1.4 |
| `circuit/src/temporal_predicate_dsl.rs:147-164` | only `ACCUMULATOR`/`STEP_INDEX` boundary-bound | threshold + state-roots unbound | 1 | T1.5 |
| `turn/src/turn.rs:686-698` | `canonical_executor_signed_message` covers 6 fields | omits was_encrypted, finality, effects_hash | 1 | T1.6 |
| `turn/src/executor.rs:12319` | `execute_atomic_sovereign` returns `Vec<[u8;32]>` | no TurnReceipt emitted | 1 | T1.7 |
| `turn/src/executor.rs:12572` | `execute_mixed_atomic` returns `MixedAtomicResult` | no TurnReceipt emitted | 1 | T1.7 |
| `turn/src/executor.rs:4371` | `sender_epoch_count: 0` hard-coded | RateLimit always passes | 2 | T2.10 |
| `turn/src/executor.rs:4372` | `revealed_preimage: None` hard-coded | PreimageGate always errors | 2 | T2.10 |
| `cell/src/note_bridge.rs:1201-1205` | structural-equality `iter().any(...)` on trusted_roots | no `is_valid_with_keys` call inside verify_portable_note | 2 | T2.12 |
| `types/src/lib.rs:386-394` | `qc.0.len() >= 48` structural-only | BLS aggregate not verified when threshold_qc.is_some() | 2 | T2.13 |
| `federation/src/lib.rs:84-102` | `MorpheusFederation` "legally dead" comment | dead Morpheus simulator re-exported | 1 | T1.8 |
| `bridge/src/midnight_observer.rs:146` | "For now, it's a placeholder constant" | midnight observer commitment constant | 2 | (out-of-scope; bridge audit) |
| `bridge/src/present.rs:1320` | `BabyBear::ZERO // TODO: accept from verifier challenge` | verifier nonce always zero | 2 | (out-of-scope; bridge audit) |
| `cell/src/predicate.rs:579` | `with_stubs()` constructor | preserved permissive registry for tests | 3 (test-only) | T1.4 |
| `turn/src/executor.rs:1986` | `TODO[vk-v2]` | dispatch path resolves vk_hash via legacy lane | 3 | T3.2 |

**Provisional out-of-scope rows** (bridge / chain modules audited
separately; included so CI doesn't surface false positives until the
bridge-specific debt ledger lands): `bridge/src/present.rs:1320`,
`bridge/src/midnight_observer.rs:146`, `chain/src/bridge.rs:223`,
`circuit/src/backends/sp1.rs:*` (SP1 backend), `circuit/src/backends/mina/*`
(Mina backend). When bridge / chain / SP1 / Mina debt-ledgers land,
move rows there.

---

## §5. CI enforcement design

A tiny script — bash or rust — enforces §4 against the source tree.

**Rule.** Build two sets:
1. `MARKERS_IN_CODE` — every honesty-debt token found by `grep -rn` in
   `*.rs` under `turn/`, `cell/`, `circuit/`, `intent/`, `types/`,
   `federation/`, normalized to `(file, line, marker_kind)`.
2. `MARKERS_IN_LEDGER` — every row in §4 (parsed from this file),
   normalized to the same shape.

**Fail if:**
- `MARKERS_IN_CODE \ MARKERS_IN_LEDGER` is non-empty (new debt added
  to source without ledger entry).
- `MARKERS_IN_LEDGER \ MARKERS_IN_CODE` is non-empty (ledger row no
  longer matches source — forces cleanup).

**Token kinds** (regex patterns, line-anchored):

```
TODO\[block1-bind\]
TODO\[γ\.2\.\d+\]
TODO\[vk-v2\]
TODO\(range-checks\)
TODO\(underflow\)
MockProofVerifier            (struct definition site only)
WitnessedProofVerifier::with_stub_registry\(\)    (call sites)
NotYetWiredVerifier::         (in cell/src/predicate.rs only)
StubCustomEffectVerifier      (struct definition site only)
expand_vk_hash_16_to_32       (function defn + call sites)
SOVEREIGN_TRANSITION_PROOF_VK_HASH_BASE      (zero-sentinel constant defn)
sender_epoch_count: 0         (literal initializer)
revealed_preimage: None       (literal initializer in EvalContext build)
CONSECUTIVE_TAG: \[u8; 32\] = \[0xFE; 32\]
30-bit value-truncation fix   (comment marker for T2.5)
BoundDeltaNotWired            (variant definition)
TemporalPredicateWitnessMissing  (variant definition)
WitnessedPredicateRequiresExecutor  (variant definition)
"legally dead"                (the Morpheus marker comment)
DEPRECATED: This is a stub    (multi_step_air / derivation_air pattern)
```

**Ledger parse.** Read `SILVER-DEBT.md`; collect rows from §4's table;
for each row split `file:line | marker | …` and extract the `(file,
line)` plus `marker` kind.

**Matching.** Equality on `(file, normalized_marker)` — line numbers
drift, so `(file, marker)` is the join key; the script warns if a
ledger row's line number is more than ±5 from the source-grep hit
(soft warning, not hard fail).

**Implementation.** ~80 lines of Rust in
`xtask/src/bin/silver-debt-check.rs` (preferred — same Rust toolchain
as the rest of the workspace), or ~60 lines of bash in
`scripts/check-silver-debt.sh`. Hook into `cargo xtask ci` /
pre-commit / CI workflow. Output on failure:

```
SILVER-DEBT.md mismatch:
  + turn/src/executor.rs:9999  TODO[block1-bind]  (in code, not in ledger)
  - turn/src/executor.rs:3478  TODO[block1-bind]  (in ledger, not in code)
Fix by either:
  1. Adding a row to §4 (when introducing new honesty debt)
  2. Removing a row from §4 (when closing existing debt)
```

**Bootstrap.** Land this doc; land the script next (allowed to warn
during stabilization); flip CI to hard-fail after one cleanup cycle.

---

## §6. Closure roadmap

Reflects priorities already established in the source audits
(`HOUYHNHNM-DEEP-CRITIQUE §6` "Five sharpest"; `EXECUTOR-VK-AUDIT §7`
"Prioritized fix list"; `AIR-SOUNDNESS-AUDIT §5` "Triage";
`NEW-WORLD.md §"What's not done"`).

**Wave 1 — Honest defaults + tagline hygiene (this PR + 1 week).**
- T1.1 narrowing of tagline (zero-cost).
- T1.2 strict trustless default (small).
- T1.3 VerificationKey invariant (small).
- T1.10 EXECUTOR-HONESTY-AUDIT modulus disclosure (trivial doc).
- T3.8 add `(could-catch)` / `(does-catch)` columns to audit (small).
- This SILVER-DEBT.md + CI enforcement (§5).

**FOLLOWUP-03 (2026-05-25) addendum (no-cargo progress):** coord sig verification
confirmed landed (see Recently Retired); thin wasm stubs for snapshot/time-travel
added in wasm/ (reduces effective gap for JS surfaces per dregg excellence
scope creep); precise doc annotations injected at all §5 heavy sites with
exact PLAN/SILVER cross-refs + refined cargo order (see STARBRIDGE-PLAN §5
for the 8-step plan with crate/feature/test commands). No §4 table changes
(this session performed zero debt-marker closures).

**Wave 2 — Bind what's already in the AIR (2-4 weeks).**
- T1.5 Temporal boundary binding (medium).
- T1.6 executor-receipt-sig-v3 (small).
- T1.7 atomic-path TurnReceipt (medium).
- T2.7 SortedNeighbor adjacency commitment, (a) variant (medium).
- T2.9 delete deprecated MultiStepStarkAir; migrate chunked
  derivation (medium).
- T2.12 / T2.13 trusted-root and BLS aggregate hardening (medium).
- T1.4 + T2.8 dregg-witnessed-registry-default crate (medium).
- T2.10 EvalContext sender_epoch_count / revealed_preimage plumbing
  (caveat-correctness lane, medium).

**Wave 3 — Close the placeholders (4-6 weeks).**
- T2.1 / T2.2 / T2.3 queue + capability + handoff AIR placeholder
  closure (per-effect medium; ~10 effects).
- T2.18 vk_set_commitment in TurnReceipt (medium).
- T2.17 encrypted-envelope binding (small).
- T3.11 BudgetCoordinator signature verification (small).
- T2.16 recursive VK rotation registry (medium).
- T1.8 Morpheus retirement Block 6 (medium).
- T1.11 apps/ retirement (per-app small).

**Wave 4 — Structural refactor (2 weeks + ongoing).**
- T3.1 executor.rs split into per-effect-family modules (large but
  enabling).
- T3.2 unify ProofVerifier traits (medium).
- T3.3 widen custom-effect PI to 8 BabyBear (medium).
- T2.5 / T2.14 range proofs via lookup arguments (large — depends on
  backend support).

**Wave 5 — Golden lift (multi-quarter).**
- T2.6 EffectVmShapeAir → full Effect VM AIR (large).
- T2.15 γ.2 Phase 2 joint aggregation AIR (large).
- T3.4 / T3.5 / T3.6 program-lineage + AIR-version + source-as-canonical
  (each large; together the Houyhnhnm "type-system upgrade pattern").
- T3.7 persistence beyond ledger (large per layer; pick one).
- T3.9 prover-determinism audit + enforcement (small audit; large
  enforcement).

**Cross-cutting.** Every wave updates this doc's §4 in the same PR as
the code change (per §5 CI rule).

---

## §7. What's *not* debt

These are explicit non-debt clarifications. Items that look like
missing inverses but are *the point* of dregg's design. Future readers
should consult before opening "why doesn't dregg have …" discussions.

### N7.1 — Revocation is correctly monotone (not "missing un-revoke")

`Effect::RevokeCapability` and `Effect::RevokeDelegation` have no
inverse, and this is correct. A revocation channel that could be
*reverted* would defeat the entire purpose of revocation (a holder
relying on "this cap is revoked" cannot trust their conclusion if a
later turn re-grants). Monotonicity here is a soundness property, not
a missing-feature.
See `PROTOCOL-CATEGORICAL-ANALYSIS.md §2.3` for the full argument.

### N7.2 — Nonce is correctly monotone (not "missing nonce-reset")

`IncrementNonce` has no inverse. Nonce-reset would re-enable
already-applied turns to replay; the monotonicity is the
replay-protection invariant.

### N7.3 — Finality is correctly one-way (no "un-finalize")

`AttestedRoot.finality_round` only advances. An un-finalize would mean
attesters could withdraw their attestation; this would break the
verifier's "I have proof of finality at round R" claim.

### N7.4 — `Introduce` having no inverse is a feature, not a gap

Per `PROTOCOL-CATEGORICAL-ANALYSIS.md §2.4`: introducer cannot
*revoke an introduction* once it's been made because the introducee can
attenuate and pass on the cap to a third party. The introducer has no
authority over downstream attenuations. "Workarounds (revoke + reissue
for everyone)" are the right shape — the introducer revokes the
*specific cap* via the existing revocation channel, not the
*introduction relationship*.

### N7.5 — `dregg` deliberately resists k-ary primitives

Per `PROTOCOL-CATEGORICAL-ANALYSIS.md §12.2`: one-fed and pairwise
operations are canonical; trilateral (Introduce) is special-cased;
k-ary multilateral atomic is *intentionally* not provided. The
verifier-loop complexity and the consensus-coordination complexity
argue against k-ary primitives. Pairwise composition is expected to be
the workhorse. The only place this commitment softens is liquidity-
routing bridges (`Effect::BridgeChain` Tier 2).

### N7.6 — `WitnessedReceipt` covers ledger state only; non-ledger layers being non-persistent is not (currently) framed as debt

The houyhnhnm reading (Ch.2 fractal persistence) *would* call this debt
(see T3.7), but the audits agree that promoting non-ledger persistence
is *its own protocol design*. Until dregg picks one non-ledger layer
and commits to extending the persistence stream there, the gap is
*known and named* (in T3.7) but not framed as a soundness bug. If
dregg never adds it, the right correction is to *narrow the
persistence claim*, not to fault the system for failing to live up to
an unstated claim.

### N7.7 — `Federation` is deliberately not a `Cell`

`FEDERATION-AS-CELL.md` explores the adjunction between Federation and
Cell. The design choice not to collapse them — keeping Federation as a
specialized type with BFT consensus and BLS aggregation — is
deliberate. A future "everything is a cell" rewrite is a *different
project*; the current shape's separation is the chosen design, not
debt.

### N7.8 — `recursive_witness_bundle` PI cross-binding being *optional* is the right shape

`circuit/src/recursive_witness_bundle.rs:379-395` makes
`expected_pi_u32` cross-binding optional. Some scope-1 callers don't
have receipt-side data yet; some scope-2 callers cross-bind. Making
the cross-binding *mandatory* would break the legitimate scope-1
caller class. The "optional" surface is correct; what's debt is
ensuring scope-2 callers always supply it (per
`AIR-SOUNDNESS-AUDIT §2.G`).

### N7.9 — `WitnessedPredicate` `Custom { vk_hash }` requiring host-side registry installation is correct

The cell crate cannot depend on `dregg-circuit` (dependency cycle).
The host installing real verifiers at startup is the *right* layering.
The debt is *the absence of an in-tree default-host crate*
(T1.4 / T2.8), not the layering itself.

### N7.10 — `dregg-dsl-differential`'s 2 lint-only backends are not debt

The differential test corpus has 40 cases × 5 voting backends; 2
backends are lint-only. The lint-only role is deliberate (they validate
syntactic shape but don't produce a vote because the backend cannot
yet *generate* a proof to compare). This is the right posture during
backend stabilization; the lint-only status is documented in
`dregg-dsl-differential`'s README.

---

## Reading order

- New reader: `NEW-WORLD.md` → this doc → `EXECUTOR-HONESTY-AUDIT.md`.
- Contributor opening a PR: add/remove a §4 row in the same PR that
  adds/removes the marker. CI (§5) enforces.
- External auditor: this doc is the trust footprint; §7 settles
  pre-existing design debates; §6 gives the scheduled closure order.
