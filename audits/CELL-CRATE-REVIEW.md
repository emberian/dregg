# Cell Crate Deep Review

A read-only deep review of every file in `/Users/ember/dev/breadstuffs/cell/src/`. The cell crate is the agent-model analog of a Mina zkApp account — but it has grown to absorb the bulk of pyana's identity, capability, privacy, and cross-federation primitives. Many modules look like miniature library crates in their own right.

The crate's source-file inventory (line counts):

| File | LoC | Role |
|---|---:|---|
| `lib.rs` | 117 | module facade + public re-exports |
| `id.rs` | 5 | trivial pass-through of `pyana_types::CellId` |
| `cell.rs` | 439 | the `Cell` struct, sealing accessors, sovereign/hosted modes |
| `state.rs` | 382 | mutable per-cell state (8 fields + nonce/balance + CapTP roots) |
| `permissions.rs` | 180 | `AuthRequired` × `Action` permission matrix |
| `capability.rs` | 343 | c-list (`CapabilitySet`), `CapabilityRef`, `AttenuatedCap` |
| `delegation.rs` | 191 | snapshot+refresh E-style child delegation w/ signed c-list commitment |
| `derivation.rs` | 913 | Capability Derivation Tree (seL4-inspired, off-chain verifier structure) |
| `capability_proof.rs` | 820 | peer-to-peer signed capability exercise (sovereign-cell path) |
| `commitment.rs` | 476 | the canonical state-commitment function (audit P0-2) |
| `program.rs` | 541 | cell programs: predicate / circuit constraints on state transitions |
| `preconditions.rs` | 278 | declarative pre-state assertions used by turn actions |
| `facet.rs` | 697 | E-style faceted capabilities (effect-mask bits + extended constraints) |
| `factory.rs` | 1208 | EROS-style object factories with computable child VK |
| `ledger.rs` | 1366 | world state + Merkle tree + sovereign registrations + IVC history |
| `note.rs` | 566 | anonymous notes (Zcash-style consume-once tokens) |
| `note_bridge.rs` | 2428 | cross-federation bridge w/ 2-phase locking and 4-phase receipts |
| `nullifier_set.rs` | 441 | append-only revealed-nullifier set with non-membership proofs |
| `oblivious_transfer.rs` | 584 | 1-of-2 / 1-of-N OT (Chou-Orlandi) over Ed25519 |
| `peer_exchange.rs` | 712 | sovereign-cell signed peer-to-peer state transitions |
| `revocation_channel.rs` | 701 | opt-in synchrony primitive for instant capability revocation |
| `seal.rs` | 667 | E-style sealer/unsealer pairs (X25519 + ChaCha20-Poly1305) |
| `stealth.rs` | 547 | stealth meta-addresses for unlinkable payments (Monero/EIP-5564 style) |
| `value_commitment.rs` | 1377 | Pedersen commitments + Schnorr conservation + Bulletproofs range proofs |
| `tests.rs` | 1914 | 108 unit + integration + audit-adversarial tests |
| **Total** | **17,893** | |

The single-line `id.rs` (just `pub use pyana_types::CellId;`) is the only mostly-empty file; everything else is loaded.

---

## `lib.rs` (~117 LoC)

- **One-sentence purpose.** The module index and the public face of `pyana-cell`: declares the 24 modules and re-exports their headline types.
- **Key types/functions.** Module declarations; one giant `pub use` block.
- **Notable design choices.** Feature-gating is concentrated here: ten modules are `#[cfg(feature = "crypto")]` (capability_proof, note_bridge, oblivious_transfer, peer_exchange, seal, stealth, value_commitment). The default feature set is `crypto`, but the gating is what makes a stripped-down build (e.g. SP1 guest in `circuit/sp1-guest/`) cheap. The non-crypto skeleton is exactly what the SP1 guest's `target/debug/.fingerprint/pyana-cell-...json` shows: `"features": "[\"zkvm\"]"`, with only `cell`, `capability`, `delegation`, `derivation`, `id`, `ledger`, `note`, `nullifier_set`, `permissions`, `preconditions`, `program`, `revocation_channel`, `state` compiled.
- **Integration status.** Trivially consumed everywhere; cell is depended on by `turn`, `captp`, `intent`, `wire`, `circuit`, `app-framework` (per their Cargo.toml files). `federation` declares it but its production code doesn't import it — only `federation/tests/cross_federation_bridge_receipt.rs` does. `storage` does not depend on the cell crate at all, contrary to the designer's note's expectation.
- **What's surprising / non-obvious.** The `crypto` feature is the default, so most callers transparently get the heavy modules (bulletproofs, curve25519-dalek, ed25519, x25519, chacha20-poly1305, getrandom, merlin, zeroize). Forgetting to add `default-features = false` to a downstream `Cargo.toml` silently pulls in the entire privacy stack — including Bulletproofs/Merlin — into every build.
- **Open issues / TODOs / FIXMEs / "stub" markers.** None inline.

---

## `id.rs` (~5 LoC)

- **One-sentence purpose.** `pub use pyana_types::CellId;` — `CellId` lives in `pyana-types` but the cell crate is its primary consumer, so this file is the documentation surface for "what CellId is and how it's derived."
- **Key types/functions.** `CellId` (the re-export).
- **Notable design choices.** Keeping `CellId` in `pyana-types` lets `pyana-types` be a leaf crate every other crate (chain, federation, turn) can depend on without taking the privacy-stack transitive deps. The doc-comment notes the canonical derivation is `CellId::derive_raw(&[u8;32], &[u8;32])` via "domain-separated BLAKE3 hashing".
- **Integration status.** Every crate that touches a cell ultimately gets `CellId` through this re-export or directly from `pyana_types`. Many of the executor's signing messages embed `cell.id().as_bytes()`.
- **What's surprising / non-obvious.** The 5-line file invites the false impression that there's nothing to know. There's a quiet invariant lurking: `id == derive_raw(public_key, token_id)`, enforced only at construction time and re-checked by `Cell::verify_id_integrity` (P2-3). The crate's sealing of `Cell::id`/`public_key`/`token_id` (P0-1) and the `Ledger::update_with` closure form exist precisely because `id` could otherwise drift out of sync after deserialization or after raw mutation.
- **Open issues / TODOs / FIXMEs / "stub" markers.** None. (The invariant-restoration logic lives in `cell.rs` and `ledger.rs`.)

---

## `cell.rs` (~439 LoC)

- **One-sentence purpose.** Defines the `Cell` struct (the cell-the-noun) and its construction modes, including the sealed `pub(crate)` identity fields that audit P0-1 hardened.
- **Key types/functions.** `Cell`, `CellMode` (`Hosted` / `Sovereign`, defaulting to `Sovereign` — Phase 4), `VerificationKey`, `CellConfig` builder. Accessors: `id()`, `public_key()`, `token_id()`, `state_commitment()`, `verify_id_integrity()`. Special constructors: `remote_stub_with_id*` for placeholder cells representing remote peers whose pre-image is unknown locally.
- **Notable design choices.**
  - **Sealing**: `id`, `public_key`, `token_id` are `pub(crate)` rather than `pub`. The doc-comments include `compile_fail` doctest examples proving external mutation is rejected.
  - **`CellMode::Sovereign` is the default** — the federation stores only a 32-byte commitment; the agent must provide cell state in each turn as a witness. `new_hosted()` exists for backward compatibility.
  - **`spawn_child_with_delegation` is `pub(crate)`** (P1-5): it produces a `DelegatedRef` with an all-zero placeholder signature, so exposing it publicly would let external code mint forged delegations by skipping verification.
  - `state_commitment()` is a thin wrapper around `commitment::compute_canonical_state_commitment` — the **single source of truth** for cell commitment bytes (see commitment.rs).
- **Integration status.** Heavily consumed. `turn::executor`, `turn::tests`, `turn::fast_path`, `turn::execution_path`, `turn::turn`, `turn::journal` all manipulate `Cell` values. `circuit/benches/practical_benchmarks.rs` benches construct `Cell` and `Ledger` together.
- **What's surprising / non-obvious.**
  - The `remote_stub_with_id_pk_balance` API: a "soundness note" embedded in the doc explains it intentionally breaks the `id == derive_raw(pk, token_id)` invariant because the local node only knows the remote id. The zero-pk variant exists for gossip stubs; the pk-aware variant exists because the executor needs to *find* a delegator's stub by pk when validating bearer-cap proofs. This is one of the few places in the crate where the identity invariant is deliberately broken — and it's documented to break.
  - `CellMode` defaults to `Sovereign` for new code, but `Cell::with_balance` and `spawn_child*` use `Hosted` for backward compatibility with existing tests. A reader following the code-flow could easily expect the opposite.
- **Open issues / TODOs / FIXMEs / "stub" markers.** The `delegate: Option<CellId>` field has a doc-comment noting it is "Not yet enforced by the executor" — i.e. parent-child delegation chain walking is planned but not wired.

---

## `state.rs` (~382 LoC)

- **One-sentence purpose.** The mutable per-cell `CellState` struct: 8 generic field slots, nonce, balance, proved-state flag, delegation epoch, two CapTP Merkle roots, with the audit P0-1 sealed accessors.
- **Key types/functions.** `CellState`, `FieldVisibility` (`Public` / `Committed` / `SelectivelyDisclosable`), `PublicFieldView` (`Revealed` / `Committed` sentinel). Constants: `STATE_SLOTS = 8`, `FIELD_ZERO`. Sealed-write accessors: `set_balance`, `set_nonce`, `set_delegation_epoch` (low-level, journal-rollback only); semantic: `credit_balance`, `debit_balance`, `apply_balance_change`, `increment_nonce`, `bump_delegation_epoch`, `set_proved_state`.
- **Notable design choices.**
  - **P2-2 (overflow safety)**: `increment_nonce` and `bump_delegation_epoch` use `checked_add` and return `bool`. They are marked `#[must_use]` with a custom message — the type system makes it impossible to silently re-enable replay via nonce wraparound.
  - **P1-2 (commitment staleness)**: `get_field_public` returns a sentinel `PublicFieldView::Committed([0u8; 32])` (the zero hash) when the visibility says Committed but `commitments[index]` is `None` (because `set_field` invalidated the stale hash). Previously the function fell through to `Revealed(self.fields[index])` and silently leaked the supposedly-private value. The zero-hash means "ask the holder to re-commit."
  - **CapTP-prep fields** (`swiss_table_root`, `refcount_table_root`) are included in the canonical commitment so a cell's state commitment binds its CapTP exports.
- **Integration status.** Used everywhere; `STATE_SLOTS` is the magic number `8` referenced in turn validation, in `program::StateConstraint`, and in test fixtures.
- **What's surprising / non-obvious.** The CapTP swiss-table and refcount-table roots are wired into `compute_canonical_state_commitment` (they're declared `pub`, not `pub(crate)`) but the executor side that populates them (`Effect::ExportSturdyRef`, `Effect::EnlivenRef`, `Effect::DropRef`) lives behind Stage 7 / a feature-flagged path. So the bytes are in the commitment shape today; the gating code that mutates them is partially live.
- **Open issues / TODOs / FIXMEs / "stub" markers.** No FIXMEs, but multiple "Stage 1 / DESIGN-captp-integration.md §4" comments mark planned wiring.

---

## `permissions.rs` (~180 LoC)

- **One-sentence purpose.** The cell-level authorization matrix: each `Action` (Send, Receive, SetState, …) has an `AuthRequired` (None / Signature / Proof / Either / Impossible), and `Permissions::check` answers "does this `AuthKind` satisfy this requirement?"
- **Key types/functions.** `AuthRequired`, `AuthKind`, `Action`, `Permissions` (8-field struct with one entry per `Action`). Presets: `default_user`, `sovereign_default` (set_verification_key = Proof, for self-upgrade), `zkapp` (Proof for everything), `frozen` (Impossible for everything).
- **Notable design choices.** `is_narrower_or_equal` defines the partial order for attenuation: Impossible ≤ everything ≤ None; Signature/Proof both narrower than Either; Signature and Proof are incomparable.
- **Integration status.** Consumed by `turn::executor`, `turn::action`, `captp::handoff`, `captp::sturdy`, `captp::session`, `app-framework::captp_server`, `bridge::mina`, etc.
- **What's surprising / non-obvious.** `AuthRequired::None` is the *least* restrictive (everyone can do it), while `AuthRequired::Impossible` is the most restrictive (no one can). This is reverse-intuitive for someone reading "None = no auth" as "denies all" — it actually means "no auth required, anyone allowed." The `frozen()` preset uses `Impossible` for everything, and a `Permissions::Impossible` capability is treated as revoked in `CapabilitySet::has_access`.
- **Open issues / TODOs / FIXMEs / "stub" markers.** None.

---

## `capability.rs` (~343 LoC)

- **One-sentence purpose.** The c-list: a `CapabilitySet` holding `CapabilityRef`s, supporting attenuation (narrowing permissions) and faceting (narrowing effect kinds).
- **Key types/functions.**
  - `CapabilityRef` — a capability entry with `target: CellId`, `slot: u32`, `permissions: AuthRequired`, optional `breadstuff: [u8;32]` (token hash for revocation), optional `expires_at: u64`, optional `allowed_effects: EffectMask`.
  - `AttenuatedCap` — a slotless capability produced by `CapabilitySet::attenuate`; the slot is assigned by `insert_attenuated` in the *child's* c-list (so the child doesn't inherit the parent's slot numbering — that would leak c-list layout).
  - `CapabilitySet` — internal `Vec<CapabilityRef>` + `next_slot: u32` (checked_add — slot overflow returns `None`).
- **Notable design choices.**
  - **`Permissions::Impossible` is treated as revoked.** `has_access`, `has_access_at` ignore any cap whose permissions are `Impossible`. Combined with the `frozen()` permissions preset, this provides a "tombstone" pattern.
  - **`attenuate_faceted` enforces monotone facet narrowing.** Child `effect_mask` must be a bitwise subset of parent's; the function rejects amplification.
  - **`restore(cap: CapabilityRef)`** is the journal-rollback escape hatch for un-revoking a slot after a turn failure.
- **Integration status.** Consumed by `turn::action`, `turn::builder`, `turn::executor`, `captp::*` (sturdy refs are essentially capabilities), `app-framework::captp_server`.
- **What's surprising / non-obvious.**
  - The slot counter doesn't get reused after revocation — `revoke` just removes the entry, `next_slot` keeps climbing. This is intentional (each (cell, slot) pair must be globally unique because it's the key in `DerivationTree`), but a reader expecting "compact" slot reuse will be surprised.
  - `is_attenuation(held, granted)` is the **public** module-level helper that flips argument order: `granted.is_narrower_or_equal(held)`. Callers must be careful which arg goes where.
- **Open issues / TODOs / FIXMEs / "stub" markers.** None.

---

## `delegation.rs` (~191 LoC)

- **One-sentence purpose.** The snapshot+refresh delegation model: a child cell holds a point-in-time copy of its parent's c-list, signed by the parent.
- **Key types/functions.**
  - `DelegatedRef` — full struct with `source`, `child`, snapshot `Vec<CapabilityRef>`, `delegation_epoch`, `refreshed_at`, `max_staleness`, `clist_commitment: [u8;32]`, `parent_signature: [u8;64]`.
  - `DelegatedRef::compute_clist_commitment(serialized_clist) -> [u8;32]` — domain-separated BLAKE3 derive_key "pyana-delegation-clist-commitment-v1".
  - `DelegatedRef::signing_message(clist_commitment, epoch, child_id) -> [u8;32]`.
  - `DelegatedRef::verify_parent_signature(&self, parent_pubkey)` — Ed25519 `verify_strict`.
- **Notable design choices.**
  - **The c-list itself isn't put in the signed message** — its `clist_commitment` is. So the snapshot is bound to a fixed parent c-list state without inlining the whole list in the signature.
  - **`max_staleness == 0` means "always stale"** (always refresh). Otherwise `now - refreshed_at > max_staleness` is stale.
  - **Inline `delegation_sig_serde` module** — `serde` can't derive Serialize/Deserialize for `[u8; 64]` out of the box (>32 byte arrays). This pattern repeats across the crate (capability_proof, peer_exchange, note_bridge).
- **Integration status.** Field on `Cell`. Tested in `turn/src/tests.rs:5589` (`use pyana_cell::DelegatedRef`).
- **What's surprising / non-obvious.**
  - `Cell::spawn_child_with_delegation` produces a `DelegatedRef` with a `[0u8; 64]` placeholder signature. This is `pub(crate)` (P1-5) precisely so external code can't mint forged delegations. Callers building real delegations must use `DelegatedRef::new` and sign properly. The crate uses the placeholder pattern internally for "privileged" spawn-child flow where the signature isn't needed — but exposing it would be unsafe.
  - Verification is feature-gated (`#[cfg(feature = "crypto")]`); without the `crypto` feature, `verify_parent_signature` doesn't exist, so the no-crypto build can ingest delegations but cannot validate them.
- **Open issues / TODOs / FIXMEs / "stub" markers.** None inline.

---

## `derivation.rs` (~913 LoC)

- **One-sentence purpose.** The Capability Derivation Tree (CDT): a seL4-inspired tree tracking *where every capability came from* and supporting cascading revocation queries.
- **Key types/functions.**
  - `DerivationType` enum: `Grant`, `Introduce`, `Delegate`, `Unseal`, `Attenuate`.
  - `DerivationEdge` (source_cell, source_slot, derivation_type) with a domain-separated `hash()`.
  - `DerivationNode` — (cell, slot) keyed; optional parent `DerivationEdge`; `created_at`, `created_by_turn`.
  - `DerivationTree` — `HashMap<(CellId, u32), DerivationNode>` + children index. `record_derivation`, `ancestors`, `descendants`, `is_descendant_of`, `has_revoked_ancestor`, `derivation_path`, `path_commitment` (root-to-leaf BLAKE3 chain).
  - `DerivationRecord` — receipt-level representation, hashable for inclusion in `TurnReceipt`.
- **Notable design choices.**
  - **"NOT consulted during turn execution"** — the module doc-comment is explicit: the CDT is an off-chain/verifier-side data structure reconstructed from `DerivationRecord`s in turn receipts. Runtime revocation is handled by `RevocationChannelSet` (O(1)). The CDT lets external verifiers ask "was this cap derived from a revoked ancestor?"
  - **`revocation_hash(cell, slot)`** uses derive-key "pyana-cdt-revocation-v1", matching the nullifier-set domain separation so ZK non-membership proofs can be cross-compatible.
  - The module's ZK-integration plan (Poseidon2 Merkle proofs) is documented in detail in the module doc-comment but not yet implemented.
- **Integration status.** Consumed by `turn::turn` (`DerivationRecord`), `turn::executor`, `circuit::dsl::revocation`, and three `demo-agent/examples/` files (`cdt_revocation.rs`, `agent_network.rs`, `compute_marketplace.rs`).
- **What's surprising / non-obvious.**
  - **The CDT isn't used by the executor.** A new reader might assume cascading revocation happens at exercise time — it doesn't. Cascading revocation is verifier-side. Runtime revocation is the cheaper `RevocationChannelSet` lookup (revocation_channel.rs).
  - `derivation_path` returns leaf-to-root, including the starting node; `ancestors` returns parent-to-root, *excluding* the starting node. Easy to mix up.
- **Open issues / TODOs / FIXMEs / "stub" markers.** The ZK circuit ("not yet implemented") for proving CDT membership + non-membership against a revocation nullifier set is described at the top of the file as a planned addition. The hash-chain `path_commitment` exists as the off-chain analog.

---

## `capability_proof.rs` (~820 LoC)

- **One-sentence purpose.** A peer-to-peer proof-of-capability protocol: Alice proves she holds a cap to Bob's cell, signs over (holder commitment, target, slot, timestamp), and Bob verifies locally without contacting the federation.
- **Key types/functions.**
  - `CapabilityProof` (`holder_cell`, `holder_commitment`, `target_cell`, `permissions`, `proof_data`, `timestamp`, `signature: [u8;64]`).
  - `CapabilityProofData` — `SignedAttestation { capability_slot, expires_at }` (Phase 1, both parties online) or `StarkMembership { proof_bytes, merkle_root }` (Phase 2, ZK — holder doesn't reveal slot; **proof verification is `Err(StarkVerificationFailed)` only**, never actually verified here).
  - `PeerEffect` — the restricted subset of `turn::Effect` exercisable via a peer cap (`SetField`, `Transfer`, `IncrementNonce`, `EmitEvent`). Each maps to a required `Action`.
  - `CapabilityExerciseRequest` / `CapabilityExerciseResponse` — the wire types.
  - `VerificationContext` (Bob's view: our_cell_id, expected_holder_commitment, current_timestamp, max_proof_age_seconds, current_height).
  - `sign_capability_proof(proof, signing_key)` — Ed25519, dalek `Signer`.
  - `can_satisfy` — the permission-comparison logic (note: **reversed** from `Permissions::check` semantics — it asks whether a *cap with X permission* satisfies a *target requiring Y*).
- **Notable design choices.**
  - **Ed25519 with `verify_strict`** — rejects malleable signatures.
  - **Timestamp window is symmetric** — both `age > max` *and* `age < -max` (future-dated proofs) are rejected.
  - **`can_satisfy` is documented** but its truth table is non-obvious: `None` (no auth used to get the cap) is the *most* permissive cap (can satisfy anything), `Impossible` is the *least* (can satisfy only `None`-required targets). This is the inverse of `AuthRequired::is_narrower_or_equal` for attenuation.
- **Integration status.** **Surprisingly thin.** Outside the cell crate, only `bridge/src/mina.rs` references `CapabilityProof`. `CapabilityExerciseRequest`/`Response` don't appear anywhere else. The peer-to-peer-cap-exercise protocol is *built* but isn't wired into `turn::executor` or `captp::session` end-to-end as of this writing.
- **What's surprising / non-obvious.**
  - The `StarkMembership` variant is structurally present (Vec<u8> proof, Merkle root) but its verification path returns `CapabilityProofError::StarkVerificationFailed` everywhere — there's no actual STARK verification call. The module comment says "Future: full ZK"; today it's a typed placeholder.
  - The proof binds the *holder's* state commitment, not the *capability's* — i.e. Bob trusts that the cap-slot mentioned exists in Alice's current state, but the proof only attests to "Alice signed this at time T with her cell-id pubkey." A real production binding would require Bob to have Alice's actual state commitment up-to-date.
- **Open issues / TODOs / FIXMEs / "stub" markers.** No FIXMEs; the STARK path is documented as "Phase 2: full ZK" without a tracking marker. The `can_satisfy` truth table is fully unit-tested.

---

## `commitment.rs` (~476 LoC)

- **One-sentence purpose.** Defines the **single canonical state-commitment function** (`compute_canonical_state_commitment`) and the canonical capability-set root (`compute_canonical_capability_root`), closing audit P0-2 (three disjoint commitment schemes had drifted apart).
- **Key types/functions.**
  - `compute_canonical_state_commitment(&Cell) -> [u8; 32]` — BLAKE3 derive_key over identity, mode, full `CellState`, full `Permissions`, VK hash, capability_root, delegate, full delegation snapshot (with per-cap leaf hashing — P2-4 fix), and program.
  - `compute_canonical_capability_root(&CapabilitySet) -> [u8; 32]`.
  - `canonical_to_babybear_pi(&[u8; 32]) -> [u32; 8]` — bytes-to-felts adapter for STARK public-input binding (8 limbs × 30 bits = 240 bits of the 256-bit commitment).
  - Constants: `CANONICAL_COMMITMENT_CONTEXT` (`pyana-cell:canonical-state-commitment v1`), `CANONICAL_CAP_ROOT_CONTEXT`.
- **Notable design choices.**
  - **One function rules them all.** `Cell::state_commitment()` and `Ledger::hash_cell()` are now thin wrappers — the module's `three_commitments_agree_byte_for_byte` adversarial test asserts byte-equality.
  - **30-bit BabyBear packing**: BabyBear's modulus is `2^31 − 2^27 + 1`. Packing 30 bits per felt (8+8+8+6) gives a unique encoding with no modular-reduction collisions. The trailing `hi & 0x3F` mask drops the top 2 bits per 4-byte word; that's a 16-bit loss across 8 felts (32 bytes → 240 bits). The full hash bytes are still in `Cell::state_commitment()`; only the STARK-public-input form is truncated.
  - **Versioning policy** is documented: bumping `CANONICAL_COMMITMENT_CONTEXT` cleanly invalidates stale commitments via BLAKE3 derive-key domain separation.
- **Integration status.** The keystone. Used by:
  - `Cell::state_commitment` (cell.rs)
  - `Ledger::hash_cell` / `Ledger::hash_cell_canonical` (ledger.rs, the Merkle leaf)
  - The circuit binding is intended to constrain the STARK's `state_commit` public input equal to `canonical_to_babybear_pi(canonical_bytes)`, but per the file's own `REVIEW[circuit-fix-coordination]` markers, this binding is not yet enforced inside the circuit.
- **What's surprising / non-obvious.**
  - The doc-comment is the history of the audit: prior to this module, there were *three* incompatible commitment schemes (Cell::state_commitment, Ledger::hash_cell, circuit::compute_commitment). Two cells with identical balance/nonce/fields/cap_root but different `Permissions` collided on the circuit-side commitment. This was P0-2; the fix is here.
  - The module is **non-public-facing** as a primary API — most callers don't realize they're depending on `commitment.rs`; they call `cell.state_commitment()` and get the canonical result transparently.
- **Open issues / TODOs / FIXMEs / "stub" markers.**
  - Two `REVIEW[circuit-fix-coordination]` markers flagging that the circuit AIR's `state_commit` boundary public input still needs to be constrained equal to `canonical_to_babybear_pi(canonical_bytes)`. The cell side defines the contract; the circuit side hasn't completed the binding.

---

## `program.rs` (~541 LoC)

- **One-sentence purpose.** Cell programs: an enum of state-transition constraints (predicate or full circuit) attached to a cell so the executor can validate every state transition.
- **Key types/functions.**
  - `CellProgram::None` / `Predicate(Vec<StateConstraint>)` / `Circuit { circuit_hash }`.
  - `StateConstraint::FieldEquals` / `FieldGte` / `FieldLte` / `SumEquals` / `Immutable` / `Custom`.
  - `evaluate(new_state, old_state) -> Result<(), ProgramError>` — runs every constraint.
  - `field_from_u64` / `field_from_u64_be` — big-endian u64 helpers (`f[24..32]` = LE bytes of u64 in big-endian form).
- **Notable design choices.**
  - **Big-endian field comparison.** `field_gte` / `field_lte` use lexicographic byte comparison on `[u8; 32]`, and `field_from_u64` packs the u64 in `f[24..32]` so byte-order comparison matches numerical comparison. The adversarial test `test_field_gte_big_endian_correctness` confirms.
  - **`Immutable` fails closed when `old_state` is None and `nonce > 0`** — i.e. an executor that forgot to pass old_state cannot accidentally satisfy an immutability constraint. Only the initialization path (`nonce == 0`) is allowed without old_state.
  - **`Circuit` evaluation always returns `CircuitProofRequired`.** The local evaluation cannot prove a circuit; the executor must check the proof before calling `program.evaluate()`. This is a deliberate fail-closed: if `evaluate` is called and we hit the Circuit branch, the executor failed to enforce the proof gate.
  - **`Custom { constraint_hash }`** is "external verifier" only — local evaluation returns `CustomConstraintUnevaluable`.
- **Integration status.** `pyana-cell::CellProgram` is used by the SP1 guest (`circuit/sp1-guest/src/main.rs`), the DSL pipeline (`tests/src/dsl_pipeline.rs`, `pyana-dsl-tests/*`), the kimchi native DSL backend, the Plonky3 DSL circuit, and the effect-VM constraint module.
- **What's surprising / non-obvious.** `Predicate` constraints are checked by the executor in cleartext — they're for hosted-cell programs or sovereign cells where the agent provides the witness state. `Circuit` programs are zero-knowledge: the proof carries authorization. The two paths are not interchangeable.
- **Open issues / TODOs / FIXMEs / "stub" markers.** None inline.

---

## `preconditions.rs` (~278 LoC)

- **One-sentence purpose.** Declarative pre-state assertions a turn action can declare ("the cell's nonce must be exactly N", "field 2 must equal X", "block height must be ≥ H", "valid only during time range [a,b]").
- **Key types/functions.**
  - `Preconditions { cell_state, network, valid_while }`.
  - `CellStatePrecondition { nonce, min_nonce, min_balance, field_equals: Vec<(usize, FieldElement)>, proved_state: Option<bool> }`.
  - `NetworkPrecondition { min_height, max_height }`.
  - `TimeRange { start, end }`.
  - `EvalContext { block_height, timestamp }`.
  - `Preconditions::hash() -> [u8; 32]` — included in signing messages so a precondition is bound to a signature.
  - `evaluate` — returns `Result<(), PreconditionError>` (NonceMismatch, NonceTooLow, InsufficientBalance, FieldMismatch, HeightTooLow, HeightTooHigh, TimeOutOfRange, ProvedStateMismatch).
- **Notable design choices.**
  - **`min_nonce` exists alongside `nonce`** — the `nonce` field pins to an exact value (causes races against concurrent submitters); `min_nonce` is for monotonic "see-then-set" patterns. Both can be checked; both can be present.
  - **Empty preconditions hash to a domain-separated constant**, not zero. Prevents collision with uninitialized data.
- **Integration status.** `pyana-cell::Preconditions` is consumed by `turn::action`, `turn::builder`, `turn::preconditions`, `turn::tests`, `turn::pending`, `turn::executor`. It's a core authorization-bound primitive.
- **What's surprising / non-obvious.** The `proved_state: Option<bool>` precondition lets an action say "this only applies if the cell was recently proof-authorized" — i.e. the actor wants to chain off a previous ZK transition. This couples turn-execution to the `proved_state` flag (which `set_proved_state` in `state.rs` mutates).
- **Open issues / TODOs / FIXMEs / "stub" markers.** None.

---

## `facet.rs` (~697 LoC)

- **One-sentence purpose.** E-language **faceted capabilities**: bitmask-restricted views of an object that compose with attenuation. Plus an `ExtendedFacet` for parameterized constraints (max transfer amount, allowed targets, rate limit, budget).
- **Key types/functions.**
  - `EffectMask` (= `u32`) with 20 declared `EFFECT_*` constants (SET_FIELD, TRANSFER, GRANT_CAPABILITY, REVOKE_CAPABILITY, EMIT_EVENT, INCREMENT_NONCE, CREATE_CELL, SET_PERMISSIONS, SET_VERIFICATION_KEY, NOTE_SPEND, NOTE_CREATE, SEAL_OPS, BRIDGE_OPS, INTRODUCE, OBLIGATION_OPS, ESCROW_OPS, DELEGATION_OPS, SOVEREIGN_OPS, QUEUE_OPS, CAPTP_OPS).
  - `EFFECT_ALL = 0xFFFF_FFFF`.
  - Predefined facets: `FACET_READ_ONLY` (EmitEvent only), `FACET_TRANSFER_ONLY`, `FACET_STATE_WRITER`, `FACET_ADMIN`, `FACET_DELEGATOR`.
  - `is_facet_attenuation(parent, child)`, `is_effect_permitted(mask, effect_bit)`.
  - `FacetBuilder` — fluent allow_* builder.
  - **`ExtendedFacet`** — `{ effect_mask, constraints: Vec<FacetConstraint> }` where `FacetConstraint` is `MaxTransferAmount`, `AllowedTargets`, `RateLimit`, `Budget`. `check_effect`, `is_attenuation_of`.
  - `EffectContext` (transfer_amount, target_cell, effect_bit) is passed to the constraint check.
  - `FacetViolation` enum for errors.
- **Notable design choices.**
  - **P2-1 fix:** `is_effect_permitted(Some(0), _)` now returns `false` (deny all) instead of `true` (formerly interpreted as "unrestricted for backward compat"). Callers wanting "unrestricted" must use `None`. An attacker who could construct `allowed_effects: Some(0)` would otherwise get an unrestricted cap that *looked* heavily faceted.
  - **`is_attenuation_of` for ExtendedFacet** requires every parent constraint to be matched by a child constraint that is `is_at_least_as_tight`. Different constraint types are incomparable.
- **Integration status.**
  - **`EffectMask` / `is_effect_permitted` / `is_facet_attenuation` / predefined `FACET_*` masks** are consumed by `captp::handoff`, `captp::sturdy`, `turn::executor`, `turn::tests`.
  - **`ExtendedFacet` / `FacetConstraint` / `FacetBuilder` are NOT consumed anywhere outside the cell crate** (no external grep hit). This is a perfectly-built-but-unconsumed structure.
- **What's surprising / non-obvious.**
  - The 20 effect bits include `EFFECT_CAPTP_OPS` (bit 19), explicitly mapped to "Stage 7 / P1.A AIR-only orphan CapTP variants (selectors 14..17 in circuit/src/effect_vm.rs)" — so the bit is real but its enforcement path is partially gated.
  - `ExtendedFacet` is "ready to go" but the executor presently consumes only the bitmask form (`CapabilityRef::allowed_effects: Option<EffectMask>`) — the parameterized form has no `CapabilityRef`-style integration yet.
- **Open issues / TODOs / FIXMEs / "stub" markers.** Of all the cell modules, this is the strongest candidate for "perfectly-built-but-perfectly-unconsumed." `ExtendedFacet` ships with full tests; no caller exists.

---

## `factory.rs` (~1208 LoC)

- **One-sentence purpose.** EROS-style object factories with content-addressed constructor transparency: a `FactoryDescriptor` describes *exactly* what cells the factory can create, what capabilities it grants, what initial fields it sets, and (with `ChildVkStrategy`) what circuit each child runs.
- **Key types/functions.**
  - `FactoryDescriptor { factory_vk, child_program_vk, child_vk_strategy, allowed_cap_templates, field_constraints, default_mode, creation_budget }` with content-addressed `hash()`.
  - `ChildVkStrategy::Fixed` / `Derived { base_vk }` / `FromSet { approved_vks }` — supports static, parameterized, and allowlist child-circuit selection.
  - `CapTemplate { target: CapTarget, max_permissions, attenuatable }`, `CapTarget::{SelfCell, Specific(CellId), Any}`.
  - `FieldConstraint::{Equality, Range, NonZero}`.
  - `CapGrant`, `FactoryCreationParams`.
  - `Provenance { created_by_factory, creation_proof_hash, creation_height, derivation_param_hash }` — what gets stamped on every factory-created cell; `verify_derivation` recomputes `derive_child_vk` from `(factory_vk, param_hash)` and asserts match.
  - `FactoryRegistry` — HashMap of deployed descriptors + per-epoch creation counts for budget enforcement; `validate_and_record`.
- **Notable design choices.**
  - **`derive_child_vk(factory_vk, param_hash) = BLAKE3_derive_key("pyana-derived-child-vk-v1", factory_vk || param_hash)`** — the off-circuit version. The doc-comment says "the circuit version uses Poseidon2 over BabyBear elements," but the on-circuit binding isn't here.
  - **`creation_budget`** is per-epoch; `advance_epoch` clears prior-epoch counters (retain only current epoch).
  - **`FactoryError` variants** include `DerivedVkMismatch`, `VkNotInApprovedSet`, `ProgramMismatch`, `CapabilityOutsideTemplate`, `FieldConstraintViolation`, `BudgetExceeded`, `FactoryVkMismatch` — strong error-typed gating.
- **Integration status.** `pyana-cell::factory::*` is consumed by `wasm::privacy`, `turn::action`, `turn::executor`, `starbridge-apps::nameservice`, `sdk::cclerk`, `node::mcp`, `node::api`, `preflight::checks::cells`, `preflight::checks::sovereign`. It's wired in.
- **What's surprising / non-obvious.**
  - This is one of the few cell modules with **a real test suite that exercises every variant**: `test_derived_vk_strategy_creates_correct_vk`, `test_from_set_strategy_allows_approved_vk`, `test_budget_resets_on_epoch_advance`, `test_provenance_derivation_verification`. Compared to, say, capability_proof's stub StarkMembership path, factories are battle-ready.
  - **`is_in_approved_set` is linear (`Vec::contains`)** — not Merkle membership as the doc-comment ("order-independent Merkle tree") suggests. For small approved-set sizes this is fine; if a factory ever ships with hundreds of approved VKs, linear scan would be the bottleneck.
- **Open issues / TODOs / FIXMEs / "stub" markers.** None inline; the in-circuit Poseidon2 form is documented as "(circuit-side)" but not flagged TODO here.

---

## `ledger.rs` (~1366 LoC)

- **One-sentence purpose.** The world state: a `HashMap<CellId, Cell>` with an **incremental** binary Merkle tree, sovereign-cell registrations (bare + ephemeral with TTL), witness-freshness subscriptions, and `SovereignHistory` IVC-compressed cell history.
- **Key types/functions.**
  - `Ledger` — `cells: HashMap<CellId, Cell>`, `sovereign_commitments: HashMap<CellId, [u8;32]>`, `sovereign_registrations: HashMap<CellId, SovereignRegistration>`, `leaf_positions: BTreeMap<[u8;32], usize>`, `tree_levels: Vec<Vec<[u8;32]>>`, `root: [u8;32]`, `dirty: bool`, `witness_subscribers: HashMap<CellId, Vec<mpsc::Sender<WitnessDiff>>>`.
  - `update_with<F, R>(&mut self, id, f)` — closure-form mutation with integrity rollback (P1-6). Snapshots the cell before mutation; if `verify_id_integrity` fails afterward, restores from snapshot and returns `InvalidDelta`.
  - `apply_delta(&LedgerDelta)` — atomic: validates with cumulative balance tracking, clones, applies, then swaps in. Either fully succeeds or leaves the ledger unchanged.
  - `LedgerDelta { created: Vec<Cell>, updated: Vec<(CellId, CellStateDelta)>, computron_transfers: Vec<(CellId, CellId, u64)> }`.
  - `CellStateDelta { field_updates, nonce_increment, balance_change, permission_changes, capability_grants, capability_revocations }`.
  - `MembershipProof { cell_id, leaf_hash, path: Vec<([u8;32], Side)>, root }` with `verify()`.
  - `WitnessDiff { cell_id, old_path, new_path, new_root }` and `subscribe_witness_updates` / `notify_witness_subscribers`.
  - `SovereignRegistration { commitment, registered_at, ttl_blocks, last_activity, verification_key_hash, max_custom_effects }`.
  - `SovereignHistory { genesis_commitment, current_commitment, step_count, accumulated_hash, ivc_proof }` — `record_step` extends the hash chain (`H(old_hash || effects_hash || step_count_le)`), `attach_ivc_proof` for lazy compression.
- **Notable design choices.**
  - **Lazy tree rebuild**: mutations set `dirty = true`. `root()` rebuilds; mutations like `apply_delta` can do incremental `update_leaf` (O(log N)) when only updates/transfers happened (no structural change). The N inserts-in-a-batch case is O(N) total, not O(N²).
  - **`update_with` runs `verify_id_integrity` on exit** — P2-3 enforcement. If the closure changes `public_key` or `token_id` without updating `id`, the mutation is rejected.
  - **`hash_cell` routes through canonical** (P0-2 + P2-4). The dedicated `hash_cell_canonical(cell)` wrapper exists *only* for the tests in commitment.rs that prove byte-equality across the three commitment scheme call sites.
  - **`SovereignRegistration::max_custom_effects: Option<u8>`** — per-cell cap on `Effect::Custom` slots per turn. Defaults to `MAX_CUSTOM_EFFECTS_DEFAULT = 4`, hard cap `64`.
  - **Witness freshness via `mpsc::Sender`** — `notify_witness_subscribers` walks subscribers, retains only senders whose `send` succeeds. Dropped receivers are GC'd.
- **Integration status.** `Ledger` is consumed by `turn::economics`, `turn::executor`, `turn::fast_path`, `turn::execution_path`, `turn::tests`, `turn::eventual`, `circuit/benches/practical_benchmarks.rs`. The witness-freshness subscriber side appears to be available but unconsumed externally (no external grep for `WitnessDiff` or `subscribe_witness_updates`).
- **What's surprising / non-obvious.**
  - **Three sovereign-cell tracking maps:** `sovereign_commitments` (legacy bare), `sovereign_registrations` (ephemeral with TTL), and the cell map itself (when sovereign cells are hosted in some hybrid case). `deregister_sovereign_cell` checks both `sovereign_registrations` and `sovereign_commitments`.
  - **`SovereignHistory`** is a fully-built IVC-history primitive with `record_step` + `attach_ivc_proof` — but no external consumer (no external grep hit). The accumulated-hash chain shape is documented; the IVC proof bytes are an opaque `Option<Vec<u8>>` for later wiring.
  - The `merkle_root` helper is `#[cfg(test)]` only — production code uses the cached `tree_levels`. The standalone recompute is a test fallback for proving the cached tree matches a fresh rebuild.
  - **`update_with` snapshot-restore is panic-unsafe by docstring**: "callers that need to mutate must not panic for control flow." If the closure panics, the snapshot is *not* restored — `cell` was already mutated, and the snapshot is dropped on the panic stack-unwind.
- **Open issues / TODOs / FIXMEs / "stub" markers.** None inline. `WitnessDiff` and `SovereignHistory` are the unconsumed surfaces.

---

## `note.rs` (~566 LoC)

- **One-sentence purpose.** Anonymous notes (Zcash-style): a content-addressed `(owner, fields[8], randomness, creation_nonce)` tuple. Commitments go into the note tree; nullifiers (only the owner can compute) get published on spend.
- **Key types/functions.**
  - `Note { owner, fields, randomness, creation_nonce }`.
  - `NoteCommitment([u8; 32])` — `BLAKE3_derive_key("pyana-note commitment v1", owner || fields[0..8] || randomness || creation_nonce)`.
  - `Nullifier([u8; 32])` — `BLAKE3_derive_key("pyana-note nullifier v1", commitment || spending_key || creation_nonce)`. **Position-independent.**
  - `PositionedNote { note, commitment, tree_position }` — tree_position is metadata for Merkle proof generation, NOT for nullifier derivation.
  - `Note::poseidon2_commitment` (feature `zkvm`) — for the in-circuit note tree.
  - `NoteBatcher { pending, batch_interval_blocks, last_batch_height, max_batch_size }` — timing-correlation mitigation by batching note tree insertions.
- **Notable design choices.**
  - **Federation-independent nullifiers.** The nullifier depends only on note-intrinsic data, so the same note produces the same nullifier in every federation. This is the core property that makes cross-federation double-spend detection work without an export ceremony. The `test_nullifier_same_regardless_of_tree_position` and `test_double_spend_across_contexts` tests assert this.
  - **`creation_nonce` derived from randomness** (in `with_randomness`), domain-separated; or fully explicit via `with_nonce` for tests.
  - **BLAKE3 for cleartext use; Poseidon2 for in-circuit.** The two commitments live side by side — different domain separations, different field elements absorbed. Authoritative roles documented inline.
- **Integration status.** `Note`, `NoteCommitment`, `Nullifier` are heavily consumed by `turn::action`, `turn::builder`, `turn::executor`, `turn::tests`, `intent::sse`, `tests/src/every_variant_roundtrip.rs`, `circuit::effect_vm`. `NoteBatcher` is **unconsumed** externally.
- **What's surprising / non-obvious.**
  - The BLAKE3-vs-Poseidon2 split is documented but easy to miss: a developer wiring a new note-spending path needs to choose the right commitment for the audience (off-chain dedup ↔ BLAKE3, in-circuit Merkle proof ↔ Poseidon2). The structs are the same `Note`; only the `commitment()` vs `poseidon2_commitment()` call differs.
  - **`NoteBatcher`** has full unit tests but no external caller — yet its existence is the timing-correlation defense's API. Someone has to add it to the executor or federation sync layer for it to do anything.
  - The doc-comment of `Note::nullifier` explicitly disambiguates from the **separate** EVM-withdrawal nullifier scheme in `pyana_chain::withdraw::derive_nullifier` (different domain separation, different SP1 circuit). This kind of cross-crate guidance is exactly the "things I'd want to know if I were the designer."
- **Open issues / TODOs / FIXMEs / "stub" markers.** None.

---

## `note_bridge.rs` (~2428 LoC)

- **One-sentence purpose.** Cross-federation value transfer: a `PortableNoteProof` packages a STARK spending proof, an attested source-federation root, and a destination-federation binding so a note "burned" in Fed A can be "minted" in Fed B without a light client.
- **Key types/functions.**
  - `BridgeDestination` enum: `Evm { chain_id, contract: [u8; 20] }` / `Mina { network: String }` / `Midnight { contract_address: Vec<u8> }`.
  - `PortableNoteProof { nullifier, destination_federation, source_root: AttestedRoot, spending_proof: Vec<u8>, destination_commitment: NoteCommitment, value, asset_type }`.
  - `BridgedNullifierSet` — sorted `Vec<[u8;32]>`, `insert` rejects double-bridge.
  - **Two-phase locking bridge:** `PendingBridge { nullifier, destination_federation, value, asset_type, timeout_height, spending_proof, state: BridgeState }`. `BridgeState::{ Locked, Finalized, Cancelled }`. `PendingBridgeSet` indexes by nullifier.
  - `initiate_bridge` (Phase 1), `finalize_bridge` (Phase 3, requires `BridgeReceipt` signed by destination), `cancel_bridge` (Phase 4, requires `current_height > timeout_height`).
  - `BridgeReceipt { nullifier, destination_federation, mint_height, signature: [u8; 64] }`. `BridgeReceipt::signing_message` = `BLAKE3_derive_key("pyana-bridge-receipt-v1", nullifier || destination_federation || mint_height_le)`.
  - **Four-phase receipt envelope** (Stage 9 P3.D / DESIGN-receipts.md §5):
    - `BridgePhase::{ Locked = 1, Witnessed = 2, Finalized = 3, Refunded = 4 }` with `next_valid()`.
    - `BridgePhasePayload` per-phase data.
    - `compute_bridge_id(lock_nullifier, src_fed, dst_fed, initiating_nonce)`.
    - `BridgeReceiptEnvelope { version, phase, bridge_id, src_federation, dst_federation, block_height, previous_phase_receipt_hash, payload }` with deterministic `body_hash()`.
    - `BridgePhaseLog` — `HashMap<bridge_id, (BridgePhase, last_body_hash)>` enforcing monotone advancement and previous-hash chaining.
    - `BridgePhaseError::{ UnknownBridge, DuplicateLock, NonMonotoneAdvancement, PreviousPhaseHashMismatch, PayloadPhaseMismatch, BridgeIdMismatch }`.
  - `verify_portable_note<F>(&proof, local_federation_id, trusted_roots, verify_stark)` — verifies destination binding, trusted root, note_tree_root presence, then defers to a `verify_stark` closure passed in by the caller.
- **Notable design choices.**
  - **Destination federation in the public inputs** of the STARK proof — this is the cross-federation replay defense. The adversarial test `adversarial_cross_federation_replay` proves a proof addressed to federation A is rejected by federation B with `BridgeError::DestinationMismatch`.
  - **Two separate bridge protocols coexist.** The single-shot `BridgeReceipt` (Phase 2 mint-ack only) drives the current `finalize_bridge` flow; the four-phase `BridgeReceiptEnvelope` is the design-doc end-to-end protocol federations exchange. The module's own comment says "the envelope is NOT a drop-in replacement for BridgeReceipt in Effect::BridgeFinalize (which would require touching the Effect enum — outside this lane's write surface)."
  - **`BridgePhaseLog::admit`** is the race-condition defense: Finalize and Refund cannot both succeed for the same bridge. Whichever lands first wins; the loser fails `NonMonotoneAdvancement`. Tested in `bridge_phase_log_finalize_refund_race_resolved_by_log` (both directions).
  - The `verify_stark` closure receives `(nullifier, root, dest_fed, value, asset_type, proof_bytes)` — the caller is responsible for asserting these against the proof's actual public inputs. The doc-comment notes the closure MUST fail-closed if the AIR doesn't bind value/asset_type in PIs (the TODO is to make sure `NoteSpendingAir` does).
- **Integration status.** The single-shot `BridgeReceipt` path is consumed by `turn::executor`. The four-phase `BridgeReceiptEnvelope` and `BridgePhaseLog` are tested in `federation/tests/cross_federation_bridge_receipt.rs` but not yet consumed by production federation code.
- **What's surprising / non-obvious.**
  - The file is 2428 LoC, of which roughly the second half is tests (`mod tests` starts around line 1291). The adversarial-test suite includes cross-federation replay, double-bridge, untrusted-root, tampered-STARK-proof, value mismatch, asset-type confusion, nullifier-from-different-note, expired root, and full two-phase happy/timeout/forgery paths.
  - **`AttestedRoot`** (the source federation's attested commitment) comes from `pyana-types`, not this crate — but the bridge logic is entirely here.
  - **Two unconsumed-in-prod surfaces**: `BridgeDestination` (the multi-chain routing enum, only useful at bridge initiation) and the entire four-phase envelope (Federation-to-federation gossip body). Both are tested and ready; both await a production wiring on the federation/intent side.
- **Open issues / TODOs / FIXMEs / "stub" markers.** One inline `TODO`: "Ensure NoteSpendingAir includes value and asset_type in public inputs." This is a real, named gap.

---

## `nullifier_set.rs` (~441 LoC)

- **One-sentence purpose.** Append-only set of revealed nullifiers (with rollback hatch for journal failures). Supports O(log N) double-spend detection and non-membership proofs via adjacent-neighbor Merkle membership.
- **Key types/functions.**
  - `NullifierSet { nullifiers: BTreeSet<Nullifier> }`.
  - `insert(nullifier) -> Result<(), NoteError>` — error on double-spend.
  - `remove(nullifier)` — ONLY for journal rollback. Documented as "set is append-only outside of rollback."
  - `MerkleMembershipProof { element, index, siblings }`.
  - `NonMembershipProof { absent, left_neighbor, right_neighbor, left_membership_proof, right_membership_proof, root }` — uses adjacent-neighbor pattern: shows two consecutive nullifiers bracketing the absent value, each with Merkle membership proof, plus an adjacency check.
  - `root()` — Merkle root over sorted leaves (leaves: `BLAKE3("pyana-nullifier-leaf v1", n)`; nodes: `BLAKE3("pyana-nullifier-node v1", left || right)`).
- **Notable design choices.**
  - **`BTreeSet` for O(log N) insert + sorted iteration.** Prior code used `Vec::insert` at a binary-search position — O(N) shift on every insert. The comment is explicit.
  - **Adjacent-neighbor non-membership** requires both neighbors' indices to be consecutive (left_proof.index + 1 == right_proof.index). The `verify_non_membership` adjacency check is the critical correctness property.
- **Integration status.** Consumed by `turn::executor` (and re-exported via `pyana-cell::nullifier_set`). The Merkle membership proof side is internal to the crate; external code typically only sees `insert`/`contains`.
- **What's surprising / non-obvious.**
  - The Merkle tree is rebuilt **on every** `root()` / `prove_non_membership` call (no cached tree). That's fine at small N but quadratic-ish at large N. There's no incremental tree like `Ledger` has.
  - `remove` exists only for rollback — it's not part of the public abstract data type. Anyone calling it outside the journal-rollback path is breaking the append-only invariant.
- **Open issues / TODOs / FIXMEs / "stub" markers.** None.

---

## `seal.rs` (~667 LoC)

- **One-sentence purpose.** E-style **sealer/unsealer pairs** for partition-tolerant capability transfer: encrypt a `CapabilityRef` under a recipient's X25519 public key; only the matching unsealer secret can decrypt.
- **Key types/functions.**
  - `SealerPublic { id, sealer_public }` — serializable, safe to share.
  - `SealPair { id, sealer_public, unsealer_secret: [u8;32] }` — NOT serializable; `Drop` zeroizes the secret.
  - `SealedBox { pair_id, ephemeral_public, commitment, ciphertext, nonce: [u8;32] }`.
  - `SealPair::seal(&CapabilityRef) -> SealedBox`, `unseal(&SealedBox) -> Result<CapabilityRef, SealError>`, `verify_seal` (decrypt + commitment check without surfacing plaintext).
- **Notable design choices.**
  - **X25519 ephemeral + ChaCha20-Poly1305 + commitment.** Each seal uses a fresh ephemeral keypair → forward secrecy. The DH output goes through **BLAKE3 derive_key** as a proper KDF (eliminates DH bit bias) bound to both public keys (key-compromise impersonation resistance).
  - **Versioned plaintext serialization** (v1 implicit, v2 with `expires_at`). The deserializer handles both for backward compatibility.
  - **32-byte nonce, 12 used for AEAD.** Full 32 bytes participate in the commitment hash. Documented rationale: BLAKE3 output is uniform, ephemeral keypair is fresh per seal, so 12 bytes is sufficient; the extra 20 bytes serve the commitment binding.
  - **`SealPair::sealer_only(sealer_public)`** — a "sealer-but-not-unsealer" mode for production senders who shouldn't hold the unsealer secret.
- **Integration status.** `SealPair` / `SealedBox` are consumed by `turn::executor`, `turn::action`, `turn::builder`, `turn::journal`, `turn::conflict`, `wasm::privacy`, `tests/src/every_variant_roundtrip.rs`, `teasting/tests/cross_federation.rs`. The seal/unseal effects are real in the executor.
- **What's surprising / non-obvious.**
  - **`Drop for SealPair`** zeroizes — but `Drop for SealedBox` does NOT; the sealed box is encrypted, so the zeroization isn't needed.
  - The sealed plaintext encodes the inner `CapabilityRef`'s breadstuff + expires_at, but **does not encode `allowed_effects`** — `deserialize_capability` always sets `allowed_effects: None`. So sealing a faceted capability and unsealing it produces an *unfaceted* capability. This is a subtle pre-refactor leftover; sealing a `FACET_TRANSFER_ONLY` cap would silently widen it.
- **Open issues / TODOs / FIXMEs / "stub" markers.** No explicit TODOs. The `allowed_effects` round-trip gap is unmarked — a quiet potential authority-amplification bug if a holder ever seals a faceted cap.

---

## `stealth.rs` (~547 LoC)

- **One-sentence purpose.** **Stealth meta-addresses** (Monero / EIP-5564 style): a recipient publishes `(spend_pubkey, view_pubkey)`; a sender generates an ephemeral keypair and derives a one-time public key only the recipient can spend. Each transaction uses an unlinkable per-transaction address.
- **Key types/functions.**
  - `StealthMetaAddress { spend_pubkey: [u8;32] (Ed25519), view_pubkey: [u8;32] (X25519) }`.
  - `StealthAddress { one_time_pubkey, ephemeral_pubkey }`.
  - `StealthKeys { view_private_key, spend_private_key }` — `Drop` zeroizes both.
  - `generate_stealth_address(&self) -> (StealthAddress, [u8;32])` — sender side.
  - `StealthAddress::check_ownership(view_priv, spend_pub) -> bool` — recipient scan (constant-time comparison).
  - `StealthAddress::derive_spending_key(view_priv, spend_priv) -> [u8;32]` — recipient signing key for the one-time address (`k = shared_scalar + s mod l`).
  - `StealthAnnouncement { ephemeral_pubkey, note_commitment, view_tag: u8 }` — posted alongside a note; `view_tag` is first byte of shared secret for ~255/256 false-positive pre-filtering.
- **Notable design choices.**
  - **Mixed key types**: X25519 for DH (view), Ed25519 for point addition (one-time pubkey derivation). Two different curves used appropriately for their operation.
  - **`from_bytes_mod_order`** — the shared scalar is reduced mod l for Ed25519 safety. The shared scalar is derived via BLAKE3 keyed derivation ("pyana-stealth scalar v1") for domain separation.
  - **Constant-time equality** for ownership check (`constant_time_eq`).
  - **View key delegation pattern**: the recipient can give a scanning service the `view_private_key` without granting spending authority (view ≠ spend).
- **Integration status.** `StealthKeys`, `StealthMetaAddress`, `StealthAddress`, `StealthAnnouncement` are consumed by `wasm::privacy`, `apps/gallery/src/private_vickrey.rs`, `preflight::checks::privacy`, `sdk::cclerk`. The marketplace / gallery integration is real.
- **What's surprising / non-obvious.**
  - The same `getrandom::fill` panics on failure with `.expect("getrandom failed")` — six times in the file. This is consistent with the rest of the crate, which treats `getrandom` failure as a hard error.
  - **No tracking of view_tag false positives**: the ~255/256 pre-filter is documented but the implementation just hashes the DH and compares one byte. A scanning service still has to do the full ownership check for every match — view_tag is purely an optimization hint.
- **Open issues / TODOs / FIXMEs / "stub" markers.** None inline.

---

## `value_commitment.rs` (~1377 LoC)

- **One-sentence purpose.** **Pedersen value commitments** (over Ristretto) with Schnorr-signature conservation proofs and **Bulletproof range proofs** to prevent negative-value inflation attacks. The privacy layer for value transfer.
- **Key types/functions.**
  - Generators (BLAKE3 + Elligator2 to Ristretto): `value_generator()` = `V`, `randomness_generator()` = `R`, `asset_value_generator(asset_type)` = `V_asset` (per-asset, prevents cross-asset attacks).
  - `ValueCommitment { point: RistrettoPoint }` — `commit(v, r) = v*V + r*R` (additive/subtractive arithmetic implemented). `ValueCommitmentBytes` — serializable 32-byte compressed form.
  - `CommittedNote { asset_type, value_commitment, note_commitment }` + `CommittedNoteOpening { value, blinding, owner, asset_type, note_randomness, creation_nonce }` (private).
  - `ConservationProof { excess_commitment, nonce_commitment, response }` — Schnorr signature proving knowledge of `r_excess`.
  - `prove_conservation(inputs, outputs, excess_blinding, message)` / `verify_conservation` — verifies `sum(inputs) - sum(outputs)` is a commitment to zero (no inflation), bound to a context message.
  - `BulletproofRangeProof { proof_bytes: Vec<u8> }` — wraps `bulletproofs::RangeProof::to_bytes`. `prove_range(value, blinding)`, `verify_range(commitment)`. Implements `RangeProofTrait`.
  - `FullConservationProof { conservation, output_range_proofs: Vec<BulletproofRangeProof> }` — the production-grade combo.
  - `prove_conservation_with_range` / `verify_conservation_with_range` — Schnorr + per-output range proof.
- **Notable design choices.**
  - **Asset-type-specific generators** prevent cross-asset conservation attacks. `V_asset_a` and `V_asset_b` have unknown DL relation, so an attacker cannot forge `commit(v, r) on V_a == commit(v', r') on V_b`.
  - **Pedersen generators reused** by Bulletproofs via `PedersenGens { B: value_generator(), B_blinding: randomness_generator() }`. The Bulletproofs library calls them `B` and `B_blinding`; mapping our `V` and `R` to them keeps the schemes consistent.
  - **Adversarial test `full_conservation_negative_value_attack_fails`** is the canonical demonstration of *why* range proofs matter: an attacker who knows scalar arithmetic could commit to a "negative" value (e.g. `Scalar::from(100) - Scalar::from(1_000_100)` mod l) and produce a conservation-balancing pair, but they cannot produce a 64-bit range proof for it.
  - **Schnorr challenge** uses `blake3::new_derive_key("pyana-conservation-challenge v1")` + 64-byte wide reduction to scalar. Standard transcript pattern.
- **Integration status.** `ValueCommitment`, `ValueCommitmentBytes`, `BulletproofRangeProof`, `prove_conservation` are consumed by `turn::executor`, `turn::action`, `turn::escrow`, `turn::tests`. The committed-note executor path is wired.
- **What's surprising / non-obvious.**
  - **Bulletproof verification is per-proof**, not batched. The trait's `batch_verify` does a per-proof loop with a comment: "bulletproofs supports verify_multiple but only for aggregated proofs; independently-created proofs verify one at a time."
  - **`bulletproof_gens()` is constructed on every call** (`BulletproofGens::new(64, 1)`). The comment notes "callers doing many proofs may want to cache this" — but no caching layer exists. For a high-volume executor this could be measurable.
  - **The doc-comment is the design rationale** — it includes a longer "future migration" plan to STARK-based bit decomposition (free to batch with other STARK proofs) once the circuit integration matures. The trait abstraction (`RangeProofTrait`) makes that migration tractable.
- **Open issues / TODOs / FIXMEs / "stub" markers.** No FIXMEs. The "future: STARK-based decomposition" path is described but unmarked.

---

## `oblivious_transfer.rs` (~584 LoC)

- **One-sentence purpose.** **1-of-2 Oblivious Transfer** (Chou-Orlandi construction over Curve25519/Edwards), plus a 1-of-N extension built from `ceil(log2(N))` 1-of-2 instances.
- **Key types/functions.**
  - `OtSender { secret: Scalar, public: EdwardsPoint }`, `OtSenderSetup { sender_public }`, `OtSenderPayload { encrypted_m0, encrypted_m1 }`.
  - `OtReceiver { choice, secret, sender_public }`, `OtReceiverResponse { receiver_public }`.
  - `OtSender::new() -> (Self, OtSenderSetup)`, `OtSender::encrypt(receiver_msg, m0, m1) -> Result<OtSenderPayload, OtError>`.
  - `OtReceiver::new(choice, sender_msg) -> (Self, OtReceiverResponse)`, `OtReceiver::decrypt(payload) -> Result<Vec<u8>, OtError>`.
  - `ot_1_of_n(messages: &[&[u8]], choice: usize) -> Result<Vec<u8>, OtError>` — per-bit OT, combine keys via BLAKE3.
  - `OtError::{ InvalidSenderPublic, InvalidReceiverPublic, InvalidReceiverPoint, DecryptionFailed }`.
- **Notable design choices.**
  - **Small-order point rejection.** `OtSender::encrypt` rejects identity and small-order receiver points to prevent cofactor attacks where the DH shared secret would be trivially predictable.
  - **Edwards form (not Ristretto)** for the point arithmetic. The point addition `B = A + b_key * G` (choice=1) is straightforward on the curve; the receiver's decryption key is `b_key * A` regardless of choice (works for both branches by construction).
  - **1-of-N via bit decomposition + BLAKE3 combine.** For each bit of `choice`, run one 1-of-2 OT to obtain `key_{choice_bit_i}`; combine keys per index via `BLAKE3_derive_key("pyana-ot-combine-v1", ...)`. The receiver only has the correct keys for their choice index.
- **Integration status.** The four `Ot*` types and `ot_1_of_n` are **NOT consumed anywhere outside the cell crate**. No external grep hit. This is a perfectly-built privacy primitive with no caller.
- **What's surprising / non-obvious.**
  - The Chou-Orlandi simulation-secure UC construction is implemented in 584 lines including tests. The tests include `sender_cannot_determine_choice_from_receiver_message` (statistical), `ot_choice_0_cannot_decrypt_m1` (security), `ot_large_messages` (1KB), and `ot_randomized_100_choices`.
  - **No outer wrapper for OT-extension** (e.g. KOS/IKNP). 1-of-N is implemented as log₂(N) parallel 1-of-2s, which is fine for small N but expensive for large N. There's no comment about OT-extension as a future direction.
- **Open issues / TODOs / FIXMEs / "stub" markers.** None. The whole module is unconsumed.

---

## `peer_exchange.rs` (~712 LoC)

- **One-sentence purpose.** **Sovereign-cell peer-to-peer state exchange**: two cells maintain views of each other's state commitments, sign monotonic state transitions (Ed25519), and optionally carry a STARK proof for proof-carrying exchange.
- **Key types/functions.**
  - `PeerStateTransition { cell_id, old_commitment, new_commitment, effects_hash, timestamp, sequence, signature: [u8;64], transition_proof: Option<Vec<u8>> }`.
  - `PeerCellView { cell_id, last_known_commitment, last_sequence, last_updated }`.
  - `PeerExchange { my_cell, my_signing_key: SigningKey, my_sequence, peer_views: HashMap<CellId, PeerCellView> }`.
  - `create_transition`, `create_transition_at(timestamp)` (for wasm / deterministic tests), `verify_transition`.
  - `PeerExchangeError::{ InvalidSignature, CommitmentMismatch, SequenceGap, TimestampRegression, UnknownPeer, InvalidTransitionProof }`.
  - `verify_stark_transition` (feature `zkvm`) — deserializes the proof via `pyana_circuit::stark`, builds Stage-1 Effect VM public inputs (old/new commitments widened to 4 BabyBears via `pyana_commit::typed::canonical_32_to_felts_4`), and verifies via `EffectVmAir`.
- **Notable design choices.**
  - **Five-check verification**: signature → commitment match → sequence gap → timestamp regression → STARK proof (if present).
  - **Commitment widening.** Previously a 4-byte truncation of the 32-byte commitment gave only ~31 bits of binding. The new path uses `pyana_commit::typed::canonical_32_to_felts_4` for a 4-felt encoding (~124-bit binding). This is the Stage-1 EFFECT-VM-SHAPE-A.md uplift.
  - **`create_transition_at` exposes the timestamp** for wasm environments (no SystemTime) and deterministic replay tests. Receiver-side `TimestampRegression` check is unchanged.
- **Integration status.** `PeerExchange` is consumed by `wasm::bindings`, `wasm::runtime`, `sdk::cclerk`, `node::mcp`. This is the API JS/wasm cipherclerks see.
- **What's surprising / non-obvious.**
  - **The STARK verification path is feature-gated `#[cfg(feature = "zkvm")]`.** Without `zkvm`, the proof bytes are stored but never checked — the field is `Option<Vec<u8>>` and only the signature/commitment/sequence/timestamp checks run. This is a deliberate "signature-only" fallback.
  - **PI layout is documented inline**: `[old_commit(1), new_commit(1), net_delta_mag(1), net_delta_sign(1), effects_hash_lo(1), effects_hash_hi(1), custom_count(1), ...custom_entries(8 per)]`. The verifier *overrides* the commitment slots with verifier-derived values to catch divergence, then matches the proof's own PIs against these felts.
  - The verifier "trusts the prover's declared values" for non-commitment PIs (net_delta, effects_hash, custom_count) because the AIR's boundary + transition constraints bind them to the trace. Documented but easy to miss.
- **Open issues / TODOs / FIXMEs / "stub" markers.** None.

---

## `revocation_channel.rs` (~701 LoC)

- **One-sentence purpose.** Opt-in synchrony primitive for **instant capability revocation**: a revoker creates a `RevocationChannel`, subjects subscribe by adding the `channel_id` to their `DelegatedRef`, and the executor checks channel state on every gated exercise.
- **Key types/functions.**
  - `ChannelId = [u8; 32]` — derived as `BLAKE3("pyana-revocation-channel" || revoker || nonce_le)`.
  - `ChannelState::Active` / `Tripped { reason: [u8;32], tripped_at: u64 }`.
  - `RevocationChannel { channel_id, revoker: CellId, state, subscribers: Vec<CellId>, created_at }` with `trip`, `subscribe`/`unsubscribe`, `is_subscriber`.
  - `RevocationChannelSet { channels: HashMap<ChannelId, RevocationChannel> }` — the in-process registry. `is_channel_active`, `check_exercise_permitted(channel_id, now, last_checked_at, max_staleness)`.
  - `RevocationChannelError::{ NotAuthorized, AlreadyTripped, ChannelNotFound, ChannelAlreadyExists, ChannelTripped, StaleChannelCheck }`.
- **Notable design choices.**
  - **Fail-closed unknowns.** `is_channel_active(unknown_id)` returns `Ok(false)`; `check_exercise_permitted(unknown_id, ...)` returns `Err(ChannelTripped { tripped_at: 0 })`. An attacker referencing a never-registered or garbage-collected channel cannot bypass revocation. Tested in `test_check_exercise_channel_not_found_is_denied` and `test_is_channel_active_unknown_returns_false`.
  - **Staleness window** parameter on every check. `max_staleness == 0` means "always check" — `last_checked_at` must equal `now`. Otherwise `now - last_checked_at > max_staleness` is stale.
  - **Subscribe is idempotent.** A `subscribe(cell)` for an already-subscribed cell is a no-op.
- **Integration status.** `RevocationChannelSet`, `RevocationChannel`, `ChannelId` are consumed by `turn::error`, `turn::executor`, `turn::tests`, `discord-bot::activity_feed`, `discord-bot::discord_caps`, `trace::policy`, `trace::verify`, `wasm::runtime`.
- **What's surprising / non-obvious.**
  - **Two revocation mechanisms coexist:** the off-chain CDT (`derivation.rs::has_revoked_ancestor`) and the in-band `RevocationChannelSet`. The cell crate's design has the CDT for verifier-side cascading queries; the channel for executor-side O(1) lookups. They don't communicate — a CDT revocation doesn't trip a channel, and vice versa.
  - **The `discord-bot` consumers** suggest the channel set is wired into a live activity feed — a runtime "kill switch" for caps that humans can pull via Discord commands. Surprising to find that here, but indicative of the channel pattern's flexibility.
- **Open issues / TODOs / FIXMEs / "stub" markers.** None inline.

---

## `tests.rs` (~1914 LoC)

- **One-sentence purpose.** The crate-level integration test file: 108 tests covering `CellId`, `CellState`, `Permissions`, `Capability*`, `Cell`, `Ledger`, `LedgerDelta`, `Precondition*`, end-to-end scenarios, `FieldVisibility` progressive disclosure, and the audit-adversarial suite (P0-1, P1-2, P1-5, P1-6, P2-1, P2-2, P2-3).
- **Key types/functions.** No production types — only test functions. Helper functions `test_key(seed)`, `test_token(seed)`, `field_from_u64`.
- **Notable design choices.**
  - **The final 234-line section is the audit-adversarial test suite.** Each test cites the audit ticket number. P0-1 sealing is asserted via the `compile_fail` doctests in `cell.rs` / `state.rs` and via runtime test that `Ledger::update_with` rejects identity-breaking mutations. P2-2 nonce overflow tests verify `increment_nonce` returns false at u64::MAX. P2-3 integrity tests confirm `verify_id_integrity` flags broken cells.
  - **`integration / scenario tests`** section starting around line 1260 — multi-cell flows (transfer + grant + revoke + delegate + spawn_child).
- **Integration status.** `#[cfg(test)] mod tests;` in `lib.rs`. Tests run with `cargo test -p pyana-cell`.
- **What's surprising / non-obvious.**
  - The audit-adversarial section is one of the most useful entry points for *understanding the security invariants*. A new contributor should read it before reading any module.
  - **108 tests, but coverage is uneven by module.** `capability_proof.rs`, `seal.rs`, `peer_exchange.rs`, `oblivious_transfer.rs`, `value_commitment.rs`, `note_bridge.rs`, `stealth.rs`, `derivation.rs`, `factory.rs`, `revocation_channel.rs`, `program.rs`, `nullifier_set.rs`, `commitment.rs`, `facet.rs` all have their own `#[cfg(test)] mod tests` blocks. The crate-level `tests.rs` focuses on Cell/Ledger/CellState/Permissions/Capabilities — the foundational types — and on cross-module integration.
- **Open issues / TODOs / FIXMEs / "stub" markers.** None.

---

## Cell-crate-wide observations

### Layering — the dependency graph

The internal dependencies of cell/ form a fairly clean layered DAG. From bottom to top:

```
                       lib.rs (re-exports)
                          |
        +-----------------+-----------------+
        |                                   |
     ledger.rs                    Higher-level / standalone
        |                                modules:
        |   uses                      tests.rs
        +-> commitment.rs <--+    capability_proof.rs
        |                    |       seal.rs
        |   uses             |       peer_exchange.rs
        +-> cell.rs <--+     |       stealth.rs
        |              |     |       value_commitment.rs
        |   uses       |     |       oblivious_transfer.rs
        +-> [state, permissions, capability, delegation,
             program, facet, note, nullifier_set,
             preconditions, derivation, revocation_channel,
             factory, note_bridge]
        |
        v
       id.rs --> pyana-types::CellId
```

More specifically:

- **`id.rs`** is the leaf — just a re-export of `pyana_types::CellId`.
- **`state.rs`, `permissions.rs`, `program.rs`, `preconditions.rs`, `facet.rs`** depend only on `id.rs` (or nothing).
- **`capability.rs`** depends on `id.rs`, `permissions.rs`, `facet.rs`.
- **`delegation.rs`** depends on `id.rs`, `capability.rs`.
- **`cell.rs`** depends on `id.rs`, `state.rs`, `permissions.rs`, `capability.rs`, `delegation.rs`, `program.rs`, and **calls into** `commitment.rs` for `state_commitment()`.
- **`commitment.rs`** depends on `cell.rs`, `state.rs`, `permissions.rs`, `capability.rs`, `delegation.rs`, `program.rs` — it sits *above* the foundational types because it hashes them.
- **`ledger.rs`** depends on everything below: `cell.rs`, `state.rs`, `commitment.rs`, `permissions.rs`, `capability.rs`, `program.rs`, plus the sovereign-history side.
- **`note.rs`** is self-contained (and a Note doesn't need a Cell).
- **`nullifier_set.rs`** depends on `note.rs`.
- **`derivation.rs`** depends on `id.rs` and is otherwise self-contained.
- **`factory.rs`** depends on `id.rs`, `cell.rs`, `permissions.rs`.
- **`revocation_channel.rs`** depends on `id.rs`.
- **The crypto-feature heavy modules** (`capability_proof.rs`, `seal.rs`, `peer_exchange.rs`, `stealth.rs`, `value_commitment.rs`, `oblivious_transfer.rs`, `note_bridge.rs`) depend on the base types and pull in dalek-ecosystem crates.

The notable cycle-adjacent shape: **`cell.rs::state_commitment()` and `ledger.rs::hash_cell()` both call `commitment.rs::compute_canonical_state_commitment()`**, and `commitment.rs` calls back into `cell.rs::Cell` fields. This is a one-way data flow (`commitment.rs` reads `Cell`; `Cell::state_commitment` is a delegate), not a circular dependency.

### What's load-bearing

Five files are the heart of `cell/`:

1. **`cell.rs`** — the `Cell` struct and its sealing accessors. Every consumer of the crate touches this.
2. **`ledger.rs`** — the world state, Merkle tree, sovereign-cell registry, witness subscriptions. Every turn execution touches this.
3. **`commitment.rs`** — the *one* canonical state-commitment function. P0-2 fix; the source of truth for cross-module agreement (sovereign witness, federation Merkle leaf, STARK public input).
4. **`capability.rs`** — the c-list and attenuation/faceting logic. Every cross-cell operation traverses this.
5. **`note.rs` + `nullifier_set.rs`** — the privacy layer's foundation. Every "anonymous transfer" goes through these.

Honorable mention: **`permissions.rs`** is small but pervasive — every action goes through `Permissions::check`.

### What's unwired (perfectly-built-but-perfectly-unconsumed)

Confirmed by absent grep results outside `cell/src/`:

- **`oblivious_transfer.rs`** — `OtSender`, `OtReceiver`, `ot_1_of_n` have **zero external consumers**. A complete Chou-Orlandi implementation sits in the crate with no caller.
- **`facet::ExtendedFacet` + `FacetConstraint`** — the parameterized-facet API. The bitmask form (`EffectMask`) IS consumed; the constraint-rich form is not.
- **`note::NoteBatcher`** — the timing-correlation mitigation. Has unit tests, ready API, no caller.
- **`ledger::WitnessDiff` + `Ledger::subscribe_witness_updates` + `Ledger::notify_witness_subscribers`** — the witness-freshness mpsc subscription system. Unused outside the crate.
- **`ledger::SovereignHistory`** — IVC-compressed cell history. `record_step`, `attach_ivc_proof`, `has_ivc_proof` — all built, all unconsumed.
- **`note_bridge::BridgeDestination`** — the multi-chain routing enum (Evm/Mina/Midnight). Defined but no consumer references it.
- **`note_bridge::BridgePhase*` (the four-phase envelope path)** — `BridgeReceiptEnvelope`, `BridgePhaseLog`, `BridgePhasePayload`, `compute_bridge_id` are tested in `federation/tests/cross_federation_bridge_receipt.rs` but not used by production federation code. The single-shot `BridgeReceipt` IS used by `turn::executor`.
- **`capability_proof::*`** — `CapabilityProof`, `CapabilityExerciseRequest`, `CapabilityExerciseResponse`, `PeerEffect`, `VerificationContext`, `sign_capability_proof` — only `bridge/src/mina.rs` references `CapabilityProof`. The peer-to-peer cap exercise protocol is not yet end-to-end wired.
- **`derivation::*` (CDT) — module comment confirms** "NOT consulted during turn execution." Consumed by `turn::turn` for emitting `DerivationRecord`s in receipts, by `circuit::dsl::revocation` for ZK integration scaffolding, and by demo examples. The cascading-revocation query side has external uses; the in-circuit ZK proof path is unimplemented.

### What's vestigial

- **`Cell::remote_stub_with_id_pk_balance`** family — three constructors solving variations of the same problem ("we know the id but not the pre-image"). Documented as deliberate; suggests an evolving API where each new use case grew a new constructor rather than refactoring.
- **`Cell::spawn_child` vs `spawn_child_with_delegation`** — the former exists from before the delegation snapshot model; the latter `pub(crate)` form is the modern path. The former still exists for backward compatibility.
- **`CellMode::Hosted` as default for `Cell::with_balance` / `spawn_child*`** while `Cell::new` defaults to `Sovereign` — backward-compat split that a new reader would expect to be uniform.
- **`SealPair::sealer_only` + `from_keys` + `from_secret` + `generate`** — four constructors, of which `sealer_only` and `from_keys` are testing-leaning. Not vestigial per se, but a wider API surface than strictly needed.
- **`note_bridge.rs` having BOTH a `BridgeReceipt` AND a `BridgeReceiptEnvelope`** — the module's own comment acknowledges they coexist intentionally (the Effect enum can't be touched in this lane), but at some point one should subsume the other.
- **`STARK proof verification in `capability_proof::CapabilityProofData::StarkMembership`** — the variant exists but always returns `StarkVerificationFailed`. Either complete the ZK path or remove the variant.

### Cryptographic story

This crate stitches together a remarkable number of primitives. By purpose:

| Primitive | Implementation / library | Role |
|---|---|---|
| **BLAKE3** (`blake3`) | direct + `new_derive_key` for domain separation | Pervasive: state commitment, cap-list commitment, nullifier derivation, sealed-box commitment, KDF for X25519 outputs, view-tag derivation, all per-module hashes |
| **Ed25519** (`ed25519-dalek` with `hazmat`) | direct, `verify_strict` | Cell-level signatures (`Cell::public_key`), delegation parent signatures, capability proofs, peer-exchange state transitions, bridge receipts, also the spend keypair in stealth addresses |
| **X25519** (`x25519-dalek`) | `StaticSecret`, `PublicKey::diffie_hellman` | Sealer/unsealer pairs, stealth view-key DH, OT sender/receiver DH (in Edwards form via `curve25519-dalek`) |
| **Curve25519 (Edwards form)** (`curve25519-dalek`) | `EdwardsPoint`, `Scalar`, `from_bytes_mod_order`, `ED25519_BASEPOINT_TABLE` | Stealth address point arithmetic (k*G + S), 1-of-2 OT (Chou-Orlandi B = A + b_key*G) |
| **Ristretto** (`curve25519-dalek`) | `RistrettoPoint`, hash-to-point via `from_uniform_bytes` (Elligator2) | Pedersen value commitments (`v*V + r*R`), Schnorr conservation proof |
| **Bulletproofs** (`bulletproofs`, `merlin`) | `RangeProof::prove_single`, `verify_single`, 64-bit range | Per-output range proofs preventing negative-value inflation in Pedersen-commit transfers |
| **Schnorr signatures** | hand-rolled over Ristretto + BLAKE3 challenge | Conservation excess-blinding proof |
| **ChaCha20-Poly1305** (`chacha20poly1305`) | direct AEAD | Sealed-box encryption (cell-to-cell capability transfer), OT message encryption |
| **Poseidon2** (`pyana-circuit`) | feature-gated `zkvm`-only | Note's in-circuit commitment (`Note::poseidon2_commitment`), CDT ZK proof scaffolding (future), STARK-commitment binding (`canonical_to_babybear_pi`) |
| **Zeroize** (`zeroize`) | `Drop` impls | Secret cleanup in `SealPair`, `StealthKeys` |
| **getrandom** (`getrandom`) | `fill` | All ephemeral randomness; documented to panic on failure |

The cryptographic story is wide. The crate is essentially a curated bundle of "every primitive a privacy-respecting agent-cell platform needs," and it's well-organized: each primitive has a clear file with its own tests. The risk is **transitive bloat**: enabling the default `crypto` feature pulls in all of these crates, which is most consumers' default.

What's *not* here: no SP1/Halo2/Plonky3 inside the cell crate itself — those live in `pyana-circuit` (feature-gated `zkvm`). The crate stops at "give me the primitive bytes"; the circuit-side AIRs are downstream.

### Surprises

Things I wish I'd known before reading every file:

1. **`commitment.rs` is the keystone** — and it's the second-shortest functional file (after `id.rs`). The audit P0-2 history is critical context: before this module existed, three commitment schemes had drifted apart. The `three_commitments_agree_byte_for_byte` test is the load-bearing assertion of the entire crate.

2. **`derivation.rs` is verifier-side, NOT executor-side.** The runtime revocation answer is `revocation_channel.rs`. A reader assuming "the CDT runs every turn" will go looking for cycles that aren't there.

3. **`oblivious_transfer.rs` has no consumers.** Same for `NoteBatcher`, `SovereignHistory`, `WitnessDiff` subscriptions, `ExtendedFacet`, `BridgeDestination`, and the four-phase `BridgeReceiptEnvelope`. These are designed and tested; they are awaiting product-level wiring. The crate has been a workshop for primitives the rest of the codebase hasn't yet absorbed.

4. **`capability_proof.rs::CapabilityProofData::StarkMembership` is a typed placeholder.** Its verification always returns `StarkVerificationFailed`. Anyone reading the type and assuming a ZK proof actually verifies will be surprised.

5. **`seal.rs` quietly drops `allowed_effects` on the serialization roundtrip.** Sealing a `FACET_TRANSFER_ONLY` cap and unsealing it produces an unfaceted cap. The seal-then-grant flow on a faceted cap would silently widen authority.

6. **The crypto feature is on by default**, pulling in Bulletproofs/Merlin/dalek for every consumer that doesn't explicitly opt out. The SP1 guest in `circuit/sp1-guest/` uses only the `zkvm` feature; that build path is the minimal cell-crate dependency profile.

---

## Composition with the rest of pyana

### Composition with `turn/`

`turn::executor` is by far the heaviest cell consumer. The import at `turn/src/executor.rs:42-50`:

```rust
use pyana_cell::{
    AuthRequired, BulletproofRangeProof, Cell, CellId, CellStateDelta, Ledger, LedgerDelta,
    Preconditions, RevocationChannelSet, ValueCommitment, ValueCommitmentBytes,
    note::NoteError,
    note_bridge::{BridgedNullifierSet, PendingBridgeSet},
    nullifier_set::NullifierSet,
    preconditions::EvalContext,
    state::STATE_SLOTS,
};
```

This is the full executor inventory: the executor owns a `Ledger`, threads a `RevocationChannelSet` through capability exercise, calls `Permissions::check` and `AuthRequired::is_satisfied_by` for authorization, applies `LedgerDelta`s, tracks `NullifierSet` for double-spend, and handles the bridge state (`PendingBridgeSet`, `BridgedNullifierSet`). `program::CellProgram::evaluate` is called by the executor before commit; `preconditions::Preconditions::evaluate` before action authorization.

Concrete pointers:
- `turn::action::Effect` includes variants like `SetField`, `Transfer`, `GrantCapability`, `Introduce`, `BridgeFinalize` — these directly construct `CellStateDelta` / `LedgerDelta` and use cell types.
- `turn::executor::apply_delta` calls `ledger.apply_delta(&delta)` which runs the cumulative-balance validator.
- `turn::tests::test_full_committed_path` uses `ValueCommitment::commit`, `BulletproofRangeProof::prove_range`, `prove_conservation`.

The `Cell` struct **owns** its `CapabilitySet` and `delegation: Option<DelegatedRef>`; the executor walks the c-list when validating `ExerciseViaCapability`. `RevocationChannelSet::check_exercise_permitted` is consulted before exercising any capability whose `DelegatedRef` has an attached `channel_id`.

### Composition with `captp/`

`captp::handoff`, `captp::sturdy`, `captp::session` import only the lightweight cell types — `AuthRequired`, `EffectMask`. CapTP sturdyrefs (resumable, signed capability references for cross-network transfer) are essentially capabilities — same `AuthRequired` permission lattice, same `EffectMask` faceting. The CapTP layer is the network wire for caps; cell defines what a cap *is*.

Per `cell/src/state.rs`, two CapTP-prep fields — `swiss_table_root` and `refcount_table_root` — are baked into the canonical state commitment. The executor populates them when `Effect::ExportSturdyRef`, `Effect::EnlivenRef`, `Effect::DropRef` run (Stage 7 / P1.A — partially gated today).

### Composition with `federation/`

Federation **declares** a pyana-cell dependency but its production code does not import any cell type — only its tests do (`federation/tests/cross_federation_bridge_receipt.rs`). The bridge receipt envelope tests live there because the four-phase protocol is precisely what federations exchange end-to-end.

Federation attests roots over cell states via `pyana_types::AttestedRoot`, which is consumed by `note_bridge::PortableNoteProof`. The federation gets the *root* type from `pyana-types`; the cell crate's `Ledger` produces the root via `compute_canonical_state_commitment` per leaf.

### Composition with `circuit/`

`pyana-circuit` does not directly import `pyana-cell` (no `use pyana_cell` in `circuit/src/`). The relationship is the inverse: the cell crate has a `feature = "zkvm"` that depends on `pyana-circuit` for `Poseidon2`, `BabyBear`, `EffectVmAir`, `stark`. This is used by:

- `note.rs::Note::poseidon2_commitment` — in-circuit commitment for note tree.
- `peer_exchange.rs::PeerExchange::verify_stark_transition` — verifies a STARK proof of state transition via `EffectVmAir`.
- `commitment.rs::canonical_to_babybear_pi` — the bytes-to-felts adapter that *should* bind the STARK's `state_commit` public input. Per the file's `REVIEW[circuit-fix-coordination]` markers, the actual binding inside the circuit AIR is still pending.

The SP1 guest at `circuit/sp1-guest/src/main.rs` uses the no-crypto cell crate (`features = ["zkvm"]`) and calls `pyana_cell::preconditions::Preconditions::evaluate` and `pyana_cell::program::CellProgram::evaluate` *inside the proof* — the cell crate's preconditions and program evaluation logic is part of what the STARK proves.

### Composition with `storage/`

Storage **does not depend on the cell crate**. The designer's question framing assumed it did; in fact the storage primitives are operator-side and use `pyana_types::CellId` directly via that crate. The cell crate's `note.rs` / `nullifier_set.rs` / `note_bridge.rs` provide the *consume-once* analog of storage primitives, but they live alongside, not on top.

### Composition with `app-framework/`

`app-framework` imports lightweight cell types: `AuthRequired`, `CellId`, `state::FieldElement`. Apps (`app-framework::dispute`, `escrow`, `captp_server`) build over cell primitives but treat the cell-crate as a stable foundation rather than extending it. `app-framework::lib.rs` re-exports `pyana_cell::state::FieldElement` so app authors don't need to import the cell crate themselves for the common case.

`app-framework::captp_server` uses `AuthRequired` and `CellId` for CapTP-flavored RPC.

---

## Open questions for the designer

These are questions I cannot answer from the code alone:

1. **`oblivious_transfer.rs` has no caller.** Is it speculative (built ahead of a planned private-auction app), an experiment from a now-pivoted direction, or is wiring intentionally on hold? The Chou-Orlandi construction is a substantial implementation to leave dormant.

2. **`SovereignHistory` IVC compression has no caller, no test wiring an actual IVC proof.** What's the planned producer of `ivc_proof: Vec<u8>`? Is this Nova/SuperNova/HyperNova? The hash-chain part (`record_step`) is well-defined; the proof generation side is opaque.

3. **`note_bridge::BridgeReceiptEnvelope` (four-phase) coexists with `BridgeReceipt` (single-shot Phase 2).** The module's own comment defers the unification ("outside this lane's write surface"). Is the goal that `Effect::BridgeFinalize` will eventually consume an `Envelope` instead of a `Receipt`? If so, what's blocking?

4. **`commitment.rs` REVIEW markers**: the canonical commitment defines the contract for STARK binding via `canonical_to_babybear_pi`, but the actual constraint inside the circuit AIR is not yet enforced. Who owns the circuit-side change? Is there a tracking issue?

5. **`capability_proof::StarkMembership` is a placeholder.** When (if ever) does the ZK path land? The protocol's value proposition over `SignedAttestation` is "verifier doesn't learn the slot," which matters for true privacy — but if it's permanently deferred, the variant adds API noise.

6. **`seal.rs` deserializing strips `allowed_effects`.** This is a quiet authority-amplification surface. Is it intentional (sealed caps are always considered unfaceted), accidental (a v3 serialization is needed), or an artifact of the seal format predating facets?

7. **The `crypto` feature is on by default.** Most consumers want a slimmer build. Is the default deliberate (one less knob for app authors), or would flipping the default to no-crypto-by-default be a welcome simplification?

8. **`derivation.rs` (CDT) vs. `revocation_channel.rs` are independent.** Should a CDT revocation also trip a channel (and vice versa)? Today they're disconnected; an executor that respects channels won't honor a CDT-only revocation.

9. **The witness-freshness subscription API in `Ledger`** uses `mpsc::Sender<WitnessDiff>` — i.e. a synchronous in-process channel. Was this designed for in-process light-client use or for the federation's gossip layer? No external caller exists; the design constraint is unclear.

10. **`NoteBatcher`** has no caller. Where would it plug in — `turn::executor` after `Effect::NoteCreate`, or in the federation sync layer at block-finalization time? The choice has different privacy properties.

---

## Reading order recommendation

For a new contributor approaching `cell/`:

1. **`lib.rs`** (5 min) — get the module map.
2. **`id.rs`** (1 min) — the trivial re-export; understand it's content-addressed BLAKE3.
3. **`permissions.rs`** (10 min) — the authorization lattice. Read `AuthRequired::is_narrower_or_equal` carefully; the partial order is the basis of attenuation.
4. **`state.rs`** (15 min) — the mutable state, sealed accessors. The `FieldVisibility` and `commitments[]` interaction is worth a careful read; the P1-2 commitment-staleness sentinel is non-obvious.
5. **`capability.rs`** (15 min) — c-list, attenuation, faceting. The `AttenuatedCap` vs `CapabilityRef` distinction (slot-free vs slot-assigned) is key.
6. **`cell.rs`** (20 min) — read the doc-comments on the sealing. Note the `remote_stub_with_id*` family and read the soundness note.
7. **`commitment.rs`** (15 min) — the keystone. Read the doc-comment first (audit history). Then `compute_canonical_state_commitment` end-to-end. The `three_commitments_agree_byte_for_byte` test is the spec.
8. **`ledger.rs`** (45 min) — the longest of the core files. Skim the data layout (`Ledger` struct, sovereign maps), then read `apply_delta` and `update_with` (closure form with integrity check). The lazy-rebuild + `update_leaf` incremental path is worth understanding for performance.
9. **`tests.rs` audit-adversarial section** (30 min) — line 1678 onward. Read every test in this section; each cites the audit ticket and asserts a hardened invariant.

After this foundation, branch into specialty areas based on interest:

- **Privacy stack:** `note.rs` → `nullifier_set.rs` → `value_commitment.rs` → `stealth.rs` → `seal.rs`.
- **E-style capabilities:** `delegation.rs` → `facet.rs` → `derivation.rs` → `revocation_channel.rs`.
- **Sovereign cells & P2P:** `program.rs` → `preconditions.rs` → `peer_exchange.rs` → `capability_proof.rs`.
- **Cross-federation:** `note_bridge.rs`.
- **Objects & factories:** `factory.rs`.
- **Mostly-dormant primitives** (read last, with the question "what would consume this?" in mind): `oblivious_transfer.rs`, `SovereignHistory` (in `ledger.rs`), `NoteBatcher` (in `note.rs`), `ExtendedFacet` (in `facet.rs`), `BridgeReceiptEnvelope` chain (in `note_bridge.rs`).

For consumers who only need to *use* the crate, the public API surface is `lib.rs`'s `pub use` block — about 60 names. Most apps interact through `Cell`, `Ledger`, `CapabilityRef`, `AuthRequired`, `Preconditions`, `Permissions`, and the bridge / note types. The rest is for downstream wiring.
