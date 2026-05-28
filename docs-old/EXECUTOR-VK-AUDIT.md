# Executor + VK Silver-Vision Soundness Audit

**Date:** 2026-05-25
**Scope:** `turn/src/executor.rs`, `cell/src/vk_v2.rs`, `cell/src/commitment.rs`,
`circuit/src/recursive_witness_bundle.rs`, `turn/src/turn.rs`, `turn/src/encrypted.rs`,
`turn/src/witnessed_receipt.rs`, `types/src/lib.rs` (`AttestedRoot`).
**Method:** Read-only. No cargo runs. No code edits.

---

## §1 Audit Method + The Two Lenses

### 1.1 GPT-5.5 categorical lens

The GPT-5.5 framing recasts dregg as a category whose:

| Categorical concept     | dregg counterpart                         |
| ---                     | ---                                       |
| Object                  | `Cell` (lifecycle-bearing resource)       |
| Morphism                | `Action` (authorized transition)          |
| Tensor                  | Multi-cell `Turn` (parallel composition)  |
| Order                   | Attenuation, lifecycle monotonicity, receipt-chain prefix |
| Evidence                | `TurnReceipt` / STARK proof / `WitnessedReceipt` |
| Authorization predicate | `AuthRequired` / `WitnessedPredicate` over a proposed morphism |
| Capability              | `CapabilitySet` entry (subset of `Hom(Cell, World)`) |
| Central law             | `execute_turn(S,T) = (S',R) ⇒ verify_receipt(R, commit(S')) ∧ R.statement == semantics(T)` |

GPT's strongest charge: **no layer should reinterpret "valid."** Each
authorisation check, AIR constraint, receipt structural check, and
attested-root inclusion check should agree on the meaning of acceptance.

### 1.2 Houyhnhnm lens

| Houyhnhnm tenet                                | dregg counterpart                                   |
| ---                                            | ---                                                 |
| Code+data are one history                      | `CellProgram` is content-addressed in state         |
| Persistence is system-wide                     | Ledger journal / receipt chain                       |
| Linear-logic resource discipline               | `excess == 0`, nullifier sets, conservation proofs   |
| Determinism by construction                    | Canonical hashes, domain separation                 |
| VK-versioning matters: AIR is the bytecode of meaning | `canonical_vk_v2` 4-component commitment          |
| Every type modification ships a well-typed upgrade fn | Should: `SetVerificationKey` with migration attestation |

Both lenses ask the same question in different vocabularies: **when the
executor declares a turn valid, what exactly has it committed to having
checked, and what can downstream layers re-derive?**

---

## §2 Executor Findings — GPT's Central Law Applied

### 2.1 The cleartext `execute` path (executor.rs:4233-4935)

`execute_turn(turn, ledger) → TurnResult` is the canonical site. It
implements GPT's law in two phases:

1. **Validation Phase 0:** call-forest non-empty, expiration, agent exists,
   nonce match, fee coverage, frozen-cell check, receipt-chain
   self-binding, budget gate. (lines 4234-4356)
2. **Commit Phase 1:** fee + nonce committed unconditionally (DoS
   defense). (lines 4361-4369)
3. **Execute Phase 2:** call-forest executed against a `LedgerJournal`;
   rollback on failure. (lines 4675-4730)
4. **Conservation checks:** computrons ≤ fee, note conservation,
   `excess == 0`. (lines 4732-4814)
5. **Receipt construction:** `TurnReceipt` built with `turn_hash`,
   `forest_hash`, `pre_state_hash`, `post_state_hash`,
   `effects_hash`, derivation records, emitted events, optional
   executor signature. (lines 4869-4929)

The law's first half (`verify_receipt(R, commit(S'))`) **holds for the
cleartext path**: `post_state_hash = ledger.root()` after Phase 2; a
verifier can rebuild the post-state by replaying the journal from
`pre_state_hash` against the same turn.

The law's second half (`R.statement == semantics(T)`) **holds only
weakly**: `R.effects_hash` is `compute_effects_hash(all_effects_hashes)`,
where each `all_effects_hashes[i]` comes from `apply_effect`'s
per-effect-hash output. The receipt does NOT contain a structural
projection of `T` itself — only the `turn_hash`. So `R.statement` is
"the BLAKE3 of the turn body, plus the BLAKE3 of the per-effect outcome
hashes." It does not enumerate the effects symbolically; an
external verifier without the original `Turn` body cannot reconstruct
semantics from `R` alone.

**Score:** the central law holds *given the turn body*, but
`semantics(T)` is not algebraically captured in `R`. Silver-Vision
accepts this; Golden-Vision will need a per-receipt PI that enumerates
the effect schema.

### 2.2 The proof-carrying `execute` path (executor.rs:4378-4500)

When `turn.execution_proof` is present, the executor:

1. Verifies the STARK against `EffectVmAir` (or a custom-program
   verifier if one is registered for the cell's VK).
2. Computes a `TurnReceipt` with `effects_hash = compute_effects_hash(&[])`
   — i.e. **the receipt's effects_hash is empty** for proof-carrying
   sovereign turns. (line 4425)
3. Returns `Committed`.

This is a deliberate design choice: "the proof IS the validation" (line
4424). But the receipt's `effects_hash` field carries no information
about what the proof attested. A downstream verifier looking at the
chain sees `effects_hash = compute_effects_hash(&[])` and can derive
nothing about which effects were applied. The binding lives entirely
in `turn.execution_proof` and the AIR public inputs.

**Concern:** the receipt structurally claims "zero effects applied"
when in fact the proof attests an arbitrary state transition. This is
not *unsound* (the proof verifier won't accept an inconsistent claim)
but it violates GPT's "no layer reinterprets valid": the receipt layer
under-reports what was checked.

### 2.3 The atomic-sovereign path (executor.rs:12308-12547)

`execute_atomic_sovereign` returns `Result<Vec<[u8; 32]>, …>` — **just
the new commitments. No `TurnReceipt`.** This is a structural gap in the
receipt chain: an agent that mixes atomic and normal turns has no
unified audit trail. `execute_mixed_atomic` similarly returns a
`MixedAtomicResult` containing balance deltas and commitment vectors,
**no receipt**.

GPT's central law `execute_turn(S, T) = (S', R)` is **literally
unimplementable** for atomic paths because there is no `R`.

**Severity:** HIGH. This violates the law for an entire entry point.

### 2.4 The encrypted-turn path (executor.rs:1120-1291)

Two entry points (`execute_encrypted_turn`, `apply_encrypted_turn`)
decrypt with the executor's X25519 secret, then dispatch to `execute`.
After commit, both flip `receipt.was_encrypted = true` and re-sign.

The `was_encrypted` bit IS bound into `receipt_hash()` (turn.rs:653),
so downstream observers see "this receipt was decrypted." Good.

**BUT** `receipt.canonical_executor_signed_message` (turn.rs:686-698)
**does NOT include `was_encrypted`**. The executor signature covers
turn_hash + pre_state + post_state + timestamp + federation_id + agent —
**not** `was_encrypted`. Comment at line 1192-1196 explicitly
acknowledges this.

**Concern:** a downstream verifier that checks only the executor
signature (not the receipt hash) cannot tell whether a receipt came from
the encrypted path. This contradicts the documented intent
("…cryptographically binds the receipt to a known executor, making the
federation exit path verifiable…"). The narrow signature was designed
for forward-compatibility with downstream verifiers that don't know
about routing directives etc.; `was_encrypted` was added later but not
included in the canonical signed message.

**Additional concern:** the `EncryptedTurn.turn_commitment` (used by
federation for ordering, computed as `BLAKE3(serde_json::to_vec(turn))`)
is **NOT bound back into the receipt**. The receipt covers `turn_hash`
(canonical v3 layout) but not `turn_commitment` (JSON-serialized form).
So a third party cannot prove "this receipt came from this specific
encrypted envelope I observed being ordered" — they can only prove
"this receipt was decrypted somewhere along the way."

### 2.5 "Valid" defined consistently?

There are at least **four** authority surfaces, each with a distinct
shape:

1. **Action authorization** (`verify_authorization`, the
   `check_single_auth_requirement` switch, `verify_custom_authorization`,
   `verify_zk_proof`, `check_breadstuff`) — predicate evaluation, per-effect.
2. **Turn-level structural validity** (Phase 0 in `execute`) — nonce,
   fee, expiration, frozen cells, receipt chain head.
3. **Receipt structural validity** (`receipt_hash`, `verify_receipt_chain`
   in verify.rs) — hash continuity, state continuity, agent consistency.
4. **AttestedRoot inclusion validity** (`AttestedRoot::is_valid` in
   types/src/lib.rs:389-416) — quorum count, signature validation against
   known keys, federation_id binding.

**Disagreements:**

- The action layer accepts a turn that passes per-effect predicates;
  the AIR layer (for proof-carrying turns) attests a *projection* of
  the turn that is often a placeholder (see §5.1). Two layers disagree
  on what was checked.
- The receipt verify layer (verify.rs:117) only checks chain structure;
  it does NOT re-verify the AttestedRoot, the STARK proofs, or the
  authorization predicates. A receipt chain can be "structurally valid"
  without any of the underlying proofs being valid.
- `AttestedRoot.is_valid` validates federation signatures but does NOT
  validate that the underlying state transition makes sense. A federation
  can attest a garbage merkle_root — `is_valid` only checks the signatures
  match the bytes.

These are not soundness failures by themselves but they violate GPT's
"no layer reinterprets valid" by giving the same word four different
meanings.

### 2.6 Error-path / short-circuit audit

Spot-checks for `Ok(())` returns that should be `Err`, `?` operators
swallowing errors, `unwrap_or_default()` on critical paths:

- executor.rs:6507: `let _ = vk_hash;` — discards the vk_hash in
  `AuthRequired::Custom` fall-through. Safe: the path is reached only
  when `Authorization::Custom` was NOT supplied (handled by other
  branches), so this is a per-design rejection. OK.
- executor.rs:9678-9682: `from_parts(*vk_hash, vk_hash.to_vec())` —
  see §3.1.
- executor.rs:1923, 1996, 2009, 2474: STARK / custom-program verifier
  errors are properly bubbled up via `?` with rich error wrapping. OK.
- executor.rs:4825: `let _ = ledger.update_sovereign_commitment(cell_id, new_commitment);`
  in the sovereign-cell post-execution loop — discards the
  update-result. This is a soundness concern if `update_sovereign_commitment`
  can fail silently — e.g., if a CAS-style update existed and the
  commitment had drifted. Verified: the implementation uses an
  upsert pattern (no failure path), so this is benign. MEDIUM:
  defensive coding suggests this should be `expect`'d not discarded.
- executor.rs:4710-4714: rollback path is comprehensive — covers
  obligations, escrows, bridged nullifiers, note nullifiers,
  committed escrows. Good. (journal.rs:356-465)

### 2.7 Multi-cell atomicity / rollback

Tested by reading `journal.rs:340-465`. Rollback is replay-in-reverse
over `JournalEntry` variants. The journal covers:

- field/balance/nonce/permissions/VK/delegation/delegation_epoch
- create_cell (removes from ledger)
- capability grant/revoke
- obligation/escrow/nullifier insertions (removed on rollback)

The `LedgerJournal` is constructed at line 4679 and rolled back on
every error-exit between Phase 2 and Phase 3. Atomicity per cell is
strong. **No partial-commit window** in the cleartext path.

`execute_atomic_sovereign` is verify-all-then-commit-all-or-nothing
(lines 12372-12544). No partial-commit window.

`execute_mixed_atomic` (12561-...) appears similarly structured —
hosted side is journaled, sovereign side is verify-then-commit. The
C1 fix comment at 12555-12560 explicitly notes that hosted authorisation
is verified through the standard pipeline before any effects apply. OK.

---

## §3 VK Findings — 4-Component Commitment + Rotation

### 3.1 Is the VK actually 4-component?

`canonical_vk_v2` (cell/src/vk_v2.rs:213-223) commits to all four:

1. `program_bytes` (length-prefixed) — yes
2. `air_fingerprint` (32 fixed) — yes
3. `verifier_fingerprint.canonical_bytes()` — yes (33-byte canonical with
   variant tag, hashed to 32)
4. `proving_system_id.canonical_bytes()` (length-prefixed) — yes

The encoding is sound: BLAKE3 keyed under `"dregg-vk-v2"`, length
prefixes on variable-length fields, fixed-width fingerprints. The
test suite (vk_v2.rs:240-376) covers determinism, per-field
sensitivity, variant-tag distinction, and v1/v2 domain disjointness.
**The canonical encoder is correct.**

### 3.2 Where the 4-component story breaks down

**FINDING VK-1 (HIGH): `VerificationKey` struct ignores v2 layering.**

`cell/src/cell.rs:29-47`:
```rust
pub struct VerificationKey {
    pub hash: [u8; 32],
    pub data: Vec<u8>,
}
impl VerificationKey {
    pub fn new(data: Vec<u8>) -> Self {
        let hash = *blake3::hash(&data).as_bytes();   // ← raw blake3, NOT vk_v2
        VerificationKey { hash, data }
    }
    pub fn from_parts(hash: [u8; 32], data: Vec<u8>) -> Self {
        VerificationKey { hash, data }                 // ← no integrity check
    }
}
```

The struct stores a `(hash, data)` pair but enforces no invariant
between them. `from_parts` accepts any (hash, data) without checking
`blake3(data) == hash`, and `new(data)` uses a *raw* BLAKE3 — not the
v2 layered encoding. The two constructors are not even consistent with
each other.

`executor.rs:9678-9682` (CreateCellFromFactory):
```rust
new_cell.verification_key = Some(dregg_cell::VerificationKey::from_parts(
    *vk_hash,
    vk_hash.to_vec(), // Minimal VK data — the hash IS the identifier
));
```

The cell's stored `verification_key.hash` is whatever opaque 32-byte
value the factory descriptor produced, and `data` is set to the hash
itself. There is no in-ledger evidence that the hash was derived via
`canonical_vk_v2` over real (program_bytes, air_fingerprint,
verifier_fingerprint, proving_system_id).

`executor.rs:7633-7649` (SetVerificationKey effect):
```rust
Effect::SetVerificationKey { cell, new_vk } => {
    ...
    c.verification_key = new_vk.clone();
}
```

The caller supplies an arbitrary `VerificationKey`. Nothing checks
`new_vk.hash == blake3(new_vk.data)` and nothing checks the hash was
derived via `canonical_vk_v2`. **A cell can have a `verification_key`
whose hash claims one thing while `data` is anything.**

**FINDING VK-2 (HIGH): 16-byte truncation in custom-effect VK
dispatch.**

executor.rs:2994-2998:
```rust
fn expand_vk_hash_16_to_32(short: &[u8; 16]) -> [u8; 32] {
    let mut result = [0u8; 32];
    result[..16].copy_from_slice(short);
    result
}
```

This is called at line 1962 (`Self::expand_vk_hash_16_to_32(&vk_hash_bytes)`)
when dispatching custom-effect verifiers. The AIR's PI carries only
4 BabyBear elements = 16 bytes of the 32-byte VK hash; the executor
zero-pads the upper 16 bytes to look up the registered program.

**This is an 80-bit security level** (16 bytes), not 256. Two distinct
v2 hashes whose lower 16 bytes collide map to the same registered
program. For a 32-byte hash this is birthday-bound 2^64 collisions —
not currently exploitable, but well below the 128-bit floor the rest
of the system targets. The full 32-byte vk hash exists in the cell
state but the AIR-to-executor dispatch path narrows it.

### 3.3 Is the VK versioning consumed?

If a cell created with `VK_A` has receipts, and the AIR changes to
produce `VK_B` for the same program, do existing receipts still verify
under `VK_A` only?

- `RECURSIVE_VK_PROGRAM_BYTES` is a const string in
  `circuit/src/recursive_witness_bundle.rs:105`, and `RECURSION_P3_REV`
  is similarly const. **They are baked in at compile time.**
- `compute_recursive_vk_hash()` is recomputed on every call; there is
  no persisted registry. The "registry" is a single-entry lookup that
  compares against this freshly-computed value.
- A code change that bumps `RECURSION_P3_REV` or alters
  `recursive_verifier_source_hash()` **silently invalidates every
  existing recursive proof** at the next binary run. There is no
  migration; old proofs simply stop verifying.

This is acceptable for a single-binary deployment but is a **VK cliff**:
no rotation story, no overlap window. GPT's "this cell's constitution
permits this semantic migration" framing is entirely absent — there is
no constitutional layer.

### 3.4 Houyhnhnm: upgrade attestation

> "every type modification ships with a well-typed upgrade function."

`SetVerificationKey` (Effect) takes a new `VerificationKey` and replaces
the old. There is **no** required upgrade attestation: no proof that the
new VK's program/AIR preserves any property of the old. The auth
requirement (default `AuthRequired::Signature` from
`Permissions::default_user()`) only proves the cell's owner consented
to the swap; it does not prove the swap is semantics-preserving.

A malicious or careless owner can replace a cell's VK with one whose
AIR has totally different semantics, and nothing in the ledger flags
this. The state_commitment changes (because vk.hash is in it — see
commitment.rs:144-153), so observers know "the VK changed," but not
"to what" or "via what migration."

### 3.5 AIR fingerprint: fingerprint or label?

`dregg_circuit::air_descriptor::fingerprint` — let me verify this is
constraint-bound, not just a name.

(From `circuit/src/air_descriptor.rs` referenced at vk_v2.rs:13; not
read in full this pass.) The recursive bundle module's docs assert:
"mutating the AIR changes the hash and invalidates old recursive
proofs." This is true *if* the `AIR_DESCRIPTOR` const reflects the
actual constraint set. Spot-check: `EFFECT_VM_AIR_DESCRIPTOR` is
referenced from `crate::effect_vm::AIR_DESCRIPTOR` at line 138.
Whether changes to constraints (vs. just column layout) flow through
into the descriptor without manual update is an open question — a
descriptor that lags real constraint changes would be a fingerprint
that is actually a label.

**MEDIUM concern:** there is no auto-derived fingerprint from the
constraint AST. The descriptor is hand-maintained.

---

## §4 Cross-Layer Findings

### 4.1 Encrypted turn ↔ receipt binding

Already covered in §2.4. Summary:
- `was_encrypted` is in `receipt_hash` but NOT in the canonical
  executor-signed message.
- `EncryptedTurn.turn_commitment` (JSON-form BLAKE3) is not bound into
  the receipt at all.

### 4.2 Recursive proof ↔ inner VK binding

`verify_recursive_proof_variant` (circuit/src/recursive_witness_bundle.rs:354-403):
1. Looks up `recursive_vk_hash` in a one-entry registry
   (`lookup_recursive_vk`).
2. Checks PI width.
3. Optionally cross-binds against caller-supplied `expected_pi_u32`.
4. Verifies the recursive STARK.

The "registry" has exactly one allowed value:
`compute_recursive_vk_hash()`. So the outer proof does commit to the
inner VK — but the inner VK is *the only one that exists*.
**Multi-inner-AIR recursion is not yet a thing.** The current outer
verifier accepts only proofs over `EffectVmShapeAir`, and the recursive
bundle docs explicitly note (lines 50-58) that `EffectVmShapeAir` is a
*structural subset* of `EffectVmAir`, not a soundness equivalent.

**FINDING CL-1 (MEDIUM, documented):** the Golden-Vision recursive
proof does NOT yet prove acceptance of the full `EffectVmAir`. It
proves the trace satisfies a smaller "shape" AIR. The lane is honest
about this (the doc comment at lines 50-58 is explicit), and the
Silver-Vision inline-trace replay is still required for authoritative
checking. But a Golden-only verifier today is unsound w.r.t. the full
constraint set.

### 4.3 Federation attestation ↔ VK rotation

`AttestedRoot::signing_message` (types/src/lib.rs:432-483) commits to:
- federation_id, merkle_root, note_tree_root, nullifier_set_root
- height, timestamp, blocklace_block_id, finality_round

It does **NOT** commit to any "current VK set" or "VK rotation history."

How does this hold together? The cell's `verification_key.hash` is in
`compute_canonical_state_commitment` (commitment.rs:144-153), so a VK
rotation changes the cell's commitment, which changes the merkle_root,
which the attested root commits to. So a federation rotating a VK
**implicitly** updates its attestation by attesting a new merkle_root.

**FINDING CL-2 (LOW, indirect):** stale attested roots cannot replay
*against the current merkle tree* because the merkle_root changes.
However, if a verifier holds an old `AttestedRoot` and accepts a
receipt whose `pre_state_hash` happens to match that old root, it has
no way to know "this root is from before the VK rotation that
invalidated my AIR." The verifier has no signal that the VK semantics
have changed under it — only that the root differs.

This becomes acute when the *verifier itself* updates its AIR while
holding old roots: it would accept old proofs whose AIR no longer
matches its current verifier code. The recursive-VK registry would
catch this (unknown vk_hash → reject), but only because the registry
is single-binary-baked-in.

### 4.4 Per-receipt VK identity

The receipt does NOT carry a `vk_hash` field. So given a `TurnReceipt`
alone, a third party cannot tell which VK/AIR the executor used to
validate. They have to ask: "what was the cell's VK at that
`pre_state_hash`?" — answerable only by replaying state.

**FINDING CL-3 (MEDIUM):** receipts are not VK-self-describing. For a
proof-carrying turn, the proof bytes live in the *turn*, not the
*receipt*. A `WitnessedReceipt` (witnessed_receipt.rs:243-264) carries
`proof_bytes` + `public_inputs` + optional `witness_bundle` — but
**no `vk_hash` field at the receipt level**. The `RecursiveProofVariant`
inside the optional witness bundle does carry `recursive_vk_hash` — but
the outer Effect-VM proof has no explicit VK identifier; verifiers
infer it from the cell's stored VK at replay time.

---

## §5 The "Sloppy" Catalogue

Every place where the implementation claims more than it enforces,
with file:line.

### §5.1 AIR projects placeholders, executor enforces reality

These are explicitly marked `TODO[block1-bind]` in
`convert_turn_effects_to_vm` and the surrounding effect-translation
code. The AIR's PI is fed a constant placeholder; the executor's
`apply_effect` enforces the actual bound separately. The proof
attests a vacuous predicate ("0 < capacity") that does not bind to
the real value.

- executor.rs:3373-3374 — `QueueEnqueue { queue_len: 0, program_vk: ZERO }`.
  AIR's "queue not full" check passes against this projection; the
  executor's apply_effect enforces the actual capacity. The proof's
  attestation is vacuous w.r.t. real queue state.
- executor.rs:3401-3404 — `QueueDequeue { expected_message_hash:
  domain-tagged hash(queue_id), deposit_refund: 0 }`. Fix-in-place is
  a domain-tagged hash (not the actual head), still a placeholder per
  the comment.
- executor.rs:3423 — `QueueResize { old_capacity: 0 }`. AIR treats
  every resize as fresh allocation; executor enforces real delta.
- executor.rs:3467 — `Effect::QueueBindProgram` similar placeholder
  pattern.
- executor.rs:3957-3962 — `ExportSturdyRef { permissions: ZERO,
  export_counter: 0 }`. Runtime variant doesn't carry permissions; AIR
  is self-consistent but tautological against any prover choice.
- executor.rs:3999-4002 — `EnlivenRef { expected_cell_id:
  domain-tagged hash(swiss||bearer), expected_permissions: ZERO }`.
  Fix-in-place not anchored to real swiss-table entry.
- executor.rs:4031-4044 — `DropRef { current_refcount: 1 }`. AIR's
  `refcount > 0` check satisfied by construction with no link to
  stored refcount.
- executor.rs:4066-4068 — `ValidateHandoff { recipient_pk, introducer_pk
  = domain-tagged hashes; approved_set_root = ZERO carried via PI }`.
  Partially fixed (the approved_set_root is now sourced from
  federation PI); recipient/introducer still derived from
  domain-tagged hashes, not the real cert.

**Pattern:** the executor enforces the real predicate; the proof
attests a placeholder. A downstream replayer who trusts only the proof
(Golden-Vision scope-1) is accepting a weaker statement than the
executor enforced. This is the heart of the "claims more than it
enforces" critique.

### §5.2 VerificationKey hash/data integrity not enforced

- cell/src/cell.rs:36-46 — `VerificationKey::new` uses raw BLAKE3;
  `from_parts` accepts any hash without integrity check.
- executor.rs:9678-9682 — `from_parts(*vk_hash, vk_hash.to_vec())`
  populates `data` with `hash`; not a real VK blob.
- executor.rs:7633-7649 — `SetVerificationKey` accepts caller-supplied
  `VerificationKey` with no `hash == blake3(data)` check, no
  `canonical_vk_v2` check.

### §5.3 16-byte truncation in custom-effect dispatch

- executor.rs:2994-2998 — `expand_vk_hash_16_to_32` zero-pads upper 16
  bytes. AIR PI carries only the lower 16. Birthday bound 2^64.

### §5.4 Atomic paths emit no receipt

- executor.rs:12308-12547 — `execute_atomic_sovereign` returns
  `Vec<[u8; 32]>`.
- executor.rs:12561-12905 — `execute_mixed_atomic` returns
  `MixedAtomicResult` (commitments + deltas), no receipt.

GPT's central law has no `R` to verify against these paths.

### §5.5 Sovereign-witness transition proof VK hash is sentinel zero

- executor.rs:3089-3091 — `SOVEREIGN_TRANSITION_PROOF_VK_HASH_BASE`
  written as all-zeros sentinel.
- executor.rs:3115 — comment: "The VK hash is zero sentinel today
  (the recursive verifier exposes a stable VK in a follow-up)."

So per-cell witness proofs do not bind to a specific verifier VK in
the AIR PI; the verifier loop dispatches by other means. A future
recursive-verifier upgrade would silently change what the AIR is
attesting.

### §5.6 Executor signature canonical message is narrower than receipt hash

- turn.rs:686-698 — `canonical_executor_signed_message` covers
  turn_hash + pre + post + timestamp + federation_id + agent.
- turn.rs:586-655 — `receipt_hash` additionally covers effects_hash,
  computrons, action_count, previous_receipt_hash, routing_directives,
  introduction_exports, derivation_records, emitted_events, finality,
  was_encrypted.

A signature-only verifier sees a strictly weaker statement than a
receipt-hash verifier. Documented intent. **But** `was_encrypted`,
`finality`, and `derivation_records` are all soundness-meaningful
fields not covered by the signature. A federation that rotates exec
keys and re-signs at a higher layer can present old receipts with
mismatched `was_encrypted`/`finality` and the signature still
verifies. (Receipt hash would catch this — so callers MUST
recompute receipt_hash. But the README/doc nudges signature-only as
the "narrow recoverable claim.")

### §5.7 `let _ = result` discards on commitment update

- executor.rs:4825 — `let _ = ledger.update_sovereign_commitment(...)`
- executor.rs:2032-2039 — same pattern in `verify_and_commit_proof`.

Currently safe (upsert semantics), but defensive coding would
`expect()` not discard.

### §5.8 Two `ProofVerifier` traits with different signatures

- turn/src/executor.rs:315-320 — `trait ProofVerifier { fn verify(proof,
  action, resource, vk) -> bool }` (note: returns `bool`, no `Result`).
- wire/src/server.rs:44-47 — `trait ProofVerifier { fn verify(proof,
  action, resource) -> Result<bool, String> }` (no vk param).

The executor's trait drops `vk_hash` from the contract entirely (only
`vk: &[u8]` data is passed). An impl is free to verify against any
AIR. The v2 separation between program / AIR / verifier_impl /
proving_system is *not surfaced* into the auth-time verifier
interface. Sloppy.

### §5.9 Encrypted turn ordering hash not bound to receipt

- encrypted.rs:71 — `turn_commitment` (BLAKE3 of JSON serialization)
- turn.rs:269 — `Turn::hash` (BLAKE3 v3 of canonical layout)
- receipt.turn_hash uses `Turn::hash`. `turn_commitment` is nowhere in
  the receipt.

A third party who observed the federation ordering an encrypted
envelope cannot prove "this receipt is the result of *that* envelope"
— only "some receipt was produced from some envelope."

### §5.10 AttestedRoot does not bind VK rotation history

- types/src/lib.rs:432-483 — signing message omits any VK identifier.

Indirectly safe via merkle_root, but an out-of-band VK semantics
change (executor upgrade) is invisible to attested-root verifiers
holding stale roots.

---

## §6 Silver-Vision-Completeness Rubric

What would make the executor + VK actually Silver-complete by GPT's
standard? Specific changes:

### §6.1 Receipt should carry `vk_set_commitment`

Add `TurnReceipt.vk_set_commitment: [u8; 32]` — a commitment to the
set of (cell_id, vk_hash) pairs the executor used during this turn.
This makes the receipt *VK-self-describing*: a downstream verifier
can detect "the cell's VK at receipt time was X" without re-reading
state. The commitment becomes part of `receipt_hash` and the
canonical signed message.

### §6.2 Atomic paths return a `TurnReceipt`

Change `execute_atomic_sovereign` and `execute_mixed_atomic` to return
`Result<(TurnReceipt, …), AtomicTurnError>`. The receipt carries the
same `effects_hash` / `pre_state` / `post_state` / `agent` discipline
as the cleartext path. Without this, the receipt chain has structural
gaps and `verify_receipt_chain` can never be a complete-history check.

### §6.3 VerificationKey integrity invariant

Add `VerificationKey::new_v2(components: VkComponents) -> Self` that
calls `canonical_vk_v2` and stores `(hash, postcard(components))`.
Make the `new` (raw BLAKE3) constructor `#[deprecated]`. Make
`from_parts` either remove the public surface or add a debug-assertion
that `hash == blake3(data)` (when `data` is the canonical v2-
preimage form). At `SetVerificationKey` apply-time, reject any
`VerificationKey` that does not satisfy this invariant.

### §6.4 Fix the 16-byte truncation

Extend the AIR's custom-effect PI to carry 8 BabyBear elements (32
bytes) per VK hash instead of 4 BabyBear elements (16 bytes). The
executor's `expand_vk_hash_16_to_32` becomes unnecessary.

### §6.5 Bind `was_encrypted` and `finality` into the executor signature

`canonical_executor_signed_message` should cover every receipt field
whose value affects acceptance semantics: at minimum
`was_encrypted`, `finality`, `effects_hash`. Bump to v3 if
backwards-compat is a concern.

### §6.6 Bind `EncryptedTurn.turn_commitment` into the receipt

Add `TurnReceipt.encrypted_envelope_commitment: Option<[u8; 32]>` —
populated when the receipt was produced from an `EncryptedTurn` path.
Closes the "which envelope?" binding gap.

### §6.7 Constitutional VK migration

Define `Effect::MigrateVerificationKey { old_vk, new_vk, migration_proof }`
distinct from `SetVerificationKey`. The migration_proof attests
*semantic preservation* (e.g., "every input the old AIR accepted is
also accepted by the new AIR" or a narrower property declared by the
cell's constitution). Cell programs that disallow `SetVerificationKey`
entirely but allow `MigrateVerificationKey` with a specific proof
shape become possible.

### §6.8 Eliminate AIR placeholders

Walk every `TODO[block1-bind]` site in
`convert_turn_effects_to_vm` (executor.rs:3300-4100). For each, plumb
the real ledger value into the VM Effect, so the AIR attests the
actual predicate the executor enforces. Estimated ~10 placeholder
sites; each is a mechanical fix that requires extending the runtime
Effect variant to carry the missing field and adding ledger-read
access at the call site.

### §6.9 Single `ProofVerifier` trait surface

Unify the two `ProofVerifier` traits. The contract should take the
full `VkComponents` (or at least `(vk_hash, air_fingerprint,
proving_system_id)`) so the verifier impl can refuse to verify proofs
whose AIR doesn't match its registered binding. Today an impl is free
to do anything with `vk: &[u8]`.

### §6.10 AttestedRoot covers a VK epoch identifier

Add `AttestedRoot.vk_epoch: u64` and an associated VK-set commitment.
Stale roots from a prior epoch are rejected by current verifiers who
know which epoch they're in. Closes the "verifier upgraded under a
held root" gap.

---

## §7 Prioritized Fix List

3-5 changes that most improve correctness-confidence:

### P0: VerificationKey integrity invariant (§6.3)

**Why:** The single most exploitable gap. Today the `VerificationKey`
struct gives no guarantee that `hash == canonical_vk_v2(...)`. A
malicious or careless `SetVerificationKey` can install a VK whose hash
is unrelated to any real verifier — defeating the entire v2 layered
design. Fix: enforce the invariant at construction and at
`SetVerificationKey` apply.

**Effort:** small (constructor change + one effect-apply check).

### P0: Atomic paths emit `TurnReceipt` (§6.2)

**Why:** Without this, GPT's central law is literally unimplementable
for `execute_atomic_sovereign` / `execute_mixed_atomic`. Receipt
chains are *structurally* incomplete for any agent that uses the
atomic paths, and `verify_receipt_chain` cannot detect the gap. This
is the highest-leverage architectural gap.

**Effort:** medium (compose receipt fields from the atomic flow, add
to journal-replay equivalents).

### P1: Fix 16-byte VK truncation in custom-effect dispatch (§6.4)

**Why:** Lowering an entire authorisation lane to 80-bit security is
indefensible in a system that targets 128-bit elsewhere. The fix is
mechanical (widen the AIR PI to 8 BabyBear).

**Effort:** medium (AIR PI layout change + executor PI population
update + tests).

### P1: Receipt carries `vk_set_commitment` (§6.1)

**Why:** Today receipts are not VK-self-describing. A long-running
verifier that holds a chain of historical receipts cannot tell which
VK was in force at each step without replaying state. This is also a
prerequisite for any constitutional migration story (§6.7).

**Effort:** small-to-medium (add field, plumb through receipt hash +
signed message + verify chain).

### P2: Eliminate AIR placeholders for queue / capability operations (§6.8)

**Why:** This is GPT's "no layer reinterprets valid" concern made
concrete. The executor enforces real predicates; the AIR attests
vacuous projections; a Golden-Vision-only verifier is therefore
trusting weaker statements than the executor checked. Each fix
narrows the gap between scope-1 (proof-only) and scope-2 (replay)
verification.

**Effort:** large (~10 effects, each needing runtime-variant
extension + ledger plumbing + AIR-trace regeneration). High value but
spread across many sites.

---

## Coda: framing for the brief

The VK v2 *encoder* is sound. The *consumers* of the encoder are
inconsistent — some sites use raw blake3, some store hash without
data integrity, some pass only `vk_data` to verifiers, some discard
upper 16 bytes in the AIR. The "sloppy" charge is correct, but the
sloppiness is **not** in the canonical encoder; it is in the boundary
between cell state and AIR / verifier dispatch.

GPT's central law `execute_turn(S,T) = (S',R) ⇒ verify(R, commit(S'))`
holds on the cleartext path. On the atomic paths, there is no `R`.
On the proof-carrying path, `R.effects_hash` under-reports what was
checked. On the encrypted path, `R.was_encrypted` is bound by hash
but not by signature, and the federation's ordering-commitment is not
bound back into `R` at all.

The Silver-Vision *integration* is operationally honest about its
gaps (the explicit `TODO[block1-bind]` markers and the
`EffectVmShapeAir` "structural subset, not soundness equivalent"
docstrings). The Golden-Vision recursive lane is a documented
work-in-progress whose VK story is solid but whose AIR coverage is
not yet a soundness equivalent of the full Effect VM.
