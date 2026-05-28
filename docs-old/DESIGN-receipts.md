# DESIGN: `dregg` Receipt Formats

**Author:** receipt-design subagent
**Date:** 2026-05-23
**Status:** design — implementation tracks the migration plan in §8.
**Companion docs:** `AUDIT-turn-executor.md`, `AUDIT-circuit.md`, `REVIEW-effect-vm.md`, `DREGG_DESIGN.md`.

Receipts are the lingua franca of trust boundaries. A dregg receipt is the
artifact that lets one principal — cclerk, federation, bridge endpoint,
verifier — say to another, *"This state transition really happened, and here
is the cryptographic evidence."* They are the only object that crosses every
boundary in the system: in-circuit ↔ out-of-circuit, federation A ↔ federation
B, executor ↔ cclerk, and (via the bridge) dregg ↔ Midnight/Cardano.

This document inventories the receipt shapes currently scattered through the
codebase, lists the gaps the audits have surfaced, and proposes a single
coherent three-tier receipt design (sovereign, federation, bridge) with
explicit dual BLAKE3 + Poseidon2 encodings and an in-circuit verification
shape.

---

## 1. Current state survey

### 1.1 What exists today

#### `TurnReceipt` — the workhorse
`turn/src/turn.rs:252-298`. Issued by the executor at the end of each
`execute()` call. Single-issuer (whichever federation node ran the turn). Binds:

- `turn_hash` (BLAKE3 over `Turn`, see `Turn::hash()` at `turn.rs:133`)
- `forest_hash`, `pre_state_hash`, `post_state_hash` (all `[u8;32]`, BLAKE3-ish)
- `effects_hash` (`[u8;32]`) — currently a BLAKE3 over the runtime effects list
- `computrons_used`, `action_count`, `timestamp`, `agent`
- `previous_receipt_hash: Option<[u8;32]>` — the receipt-chain link
- `federation_id: [u8;32]` — added in `dregg-receipt-v2`, prevents cross-federation replay
- routing/introduction/derivation/event metadata
- `executor_signature: Option<Vec<u8>>` — Ed25519 over `receipt_hash()`. **Unset on every path traced.**
- `finality: Finality` — `Final` or `Tentative` (solo mode)

The canonical hash is `receipt_hash()` (`turn.rs:303-368`), versioned
`dregg-receipt-v2`, with explicit byte tags for `Option` discriminants and a
length-prefix on every variable-length field.

Verified by `verify::verify_receipt_chain` (`turn/src/verify.rs:117-181`) and
`verify_receipt_chain_with_keys` (`verify.rs:245`).

#### `BridgeReceipt` — note-bridge mint ack
`cell/src/note_bridge.rs:361-389`. Issued by the **destination** federation
in bridge Phase 2 (mint), consumed by the **source** in Phase 3 (finalize).
Binds:

- `nullifier: [u8;32]`
- `destination_federation: [u8;32]`
- `mint_height: u64`
- `signature: [u8;64]` (Ed25519 over `BLAKE3_derive_key("dregg-bridge-receipt-v1", nullifier || dest_fed || mint_height_le)`)

Verified via `verify_bridge_receipt` (`note_bridge.rs:604-628`) against a
**caller-supplied** `trusted_keys: &[[u8;32]]`. No on-chain trust root.
**Missing:** source federation id, the actual minted note commitment on the
destination side, link to the source's lock receipt, recipient binding,
amount/asset binding. This receipt cannot, by itself, answer "who got what?"
— that information lives in the `PendingBridge` record kept by the source.

`PendingBridge`/`PendingBridgeSet` (`note_bridge.rs:300-447`) carry the rest
(`destination_federation`, `value`, `asset_type`, `timeout_height`,
`spending_proof`, `state`). State transitions: `Locked → Finalized` or
`Locked → Cancelled`.

#### `TurnSign` + `TurnCertificate` — fast-path quorum
`turn/src/fast_path.rs:169-197`. Validators issue `TurnSign` (Ed25519
signature over `dregg-fast-path-sign-v2 || turn_hash`, height-tagged).
`TurnCertificate` aggregates `2f+1` `TurnSign`s + the original turn + an
optional STARK proof. Verified in `assemble_certificate` (`fast_path.rs:430`)
and `execute_certified_turn` (`fast_path.rs:468`). This is BFT consensus
output, not a receipt per se — but a `TurnReceipt` whose `finality = Final`
*should* be backed by either a certificate or a `QuorumCertificate`.

The historical P0-1 finding (BLAKE3-keyed-hash signatures) has been fixed in
the live tree — `sign_fast_path` is real Ed25519.

#### `QuorumCertificate` — consensus output
`federation/src/types.rs:181-264`. BFT certificate over a *block* (not a
turn). Carries either a `ThresholdQC` (constant-size BLS aggregate via the
`hints` crate, `federation/src/threshold.rs:64`) or a `Vec<(usize, Signature)>`
of individual Ed25519 votes. Verified via `is_valid_with_keys` or
`verify_with_committee`. Currently a *block* certificate; the per-turn
`TurnReceipt` and the block certificate are not formally chained.

#### `BlocklaceTurnReceipt`
`blocklace/src/dregg_bridge.rs:119-132`. Produced when a blocklace block
containing a turn reaches finality. Binds `block_id`, `submitter`, `seq`,
`turn_data`, `tier`, `finality_height`. **Has no signature** — it's a
local-bookkeeping record, not a receipt that crosses a trust boundary.
Confusingly named.

#### `AuditReceipt`
`audit/src/event.rs:76-95`. Issued by an audit verifier with a 4-ary Merkle
inclusion proof. Binds `event_hash`, `log_root_after`, `inclusion_proof`,
`global_index`. This is a different kind of receipt — proof of inclusion in a
log — and is mostly orthogonal to the turn/bridge story. Mentioned here for
completeness.

#### Application receipts
`apps/governed-namespace/src/storage.rs:49` (`WriteReceipt`,
`SpliceReceipt`), `apps/subscription/src/payments.rs:139` (`DebitReceipt`),
`apps/lending/src/supply.rs:137` (`SupplyReceipt`),
`apps/lending/src/liquidation.rs:34` (`LiquidationReceipt`),
`rbg/src/vfs.rs:276` (`BlobReceipt`). These are application-layer
acknowledgements consumed inside cells. Out of scope for this document.

#### `ReceiptView`
`wasm/src/bindings.rs:1026`. JS-facing facade over `TurnReceipt`. Read-only.

#### `ReceiptInfo`
`node/src/api.rs:104`. REST-API DTO. Read-only.

### 1.2 Categorized

| Receipt | Issuer | Trust boundary it crosses | Signed by | Verified against |
|---|---|---|---|---|
| `TurnReceipt` (classical) | executor (1 node) | cclerk ↔ federation | optionally Ed25519 (P3-4: usually `None`) | none enforced on-chain; off-chain `verify_receipt_chain` |
| `TurnReceipt` (sovereign / proof-carrying) | executor | trustless | STARK proof attests state transition; `executor_signature` should attest finality | STARK verifier + receipt-chain |
| `TurnReceipt` (fast-path) | executor on quorum cert | cclerk ↔ federation quorum | should chain to `TurnCertificate` 2f+1 Ed25519 | `assemble_certificate` |
| `BridgeReceipt` | destination federation | source ↔ destination | single Ed25519 over (nullifier, dest, height) | `verify_bridge_receipt` against caller-supplied keys |
| `QuorumCertificate` | block proposer + voters | federation node ↔ federation node | BLS aggregate or per-voter Ed25519 | committee key |
| `BlocklaceTurnReceipt` | local bridge | none (intra-process) | — | — |
| `AuditReceipt` | audit verifier | logger ↔ auditor | Merkle inclusion | recomputed root |

---

## 2. Identified gaps and contradictions

The audits already on disk make a sharp case that the receipt story is
broken. The key indictments, with confirmations in the live code:

**(a) `previous_receipt_hash` is enforced nowhere at write time.**
`AUDIT-turn-executor.md` P0-3: *"the executor records `turn.previous_receipt_hash`
into the emitted receipt but never compares it to the agent's last receipt
hash (which it does not store) ... The receipt-chain 'self-bound history'
property in the rustdoc is therefore unenforced at write time."* Confirmed:
`turn/src/composer.rs:337`, `turn/src/execution_path.rs:113/169/198`, and the
cipherclerk's `build_authorized_turn` (per AUDIT-cclerk) all hardcode
`previous_receipt_hash: None`. The chain *can* be reconstructed by an honest
verifier (and `verify_receipt_chain` works), but the executor accepts a turn
that claims to be genesis when it isn't.

**(b) `execution_proof_new_commitment` is not in `Turn::hash()`.**
`AUDIT-turn-executor.md` P1-1: *"the executor confirms it equals the PI in the
proof, but `Turn::hash()` (turn.rs:132-164) does NOT include `execution_proof`,
`execution_proof_cell`, or `execution_proof_new_commitment`. An attacker who
intercepts a signed Turn in flight can swap the proof and the new commitment
for a different, valid (proof, new_commitment) pair."* Confirmed at
`turn.rs:133-164`: the hash inputs are `agent | nonce | forest_hash | fee |
memo | valid_until | depends_on | previous_receipt_hash`. None of the proof
fields.

**(c) Bridge receipts don't have a defined format.**
`REVIEW-effect-vm.md` per-effect ledger, BridgeMint/Lock/Finalize/Cancel rows:
*"The effect appears in `effects_hash` and that is all. No factory-program
enforcement at the VM layer."* (Said of `CreateCellFromFactory`; the bridge
effects share the structural defect.) Confirmed: `BridgeReceipt` as defined
in `cell/src/note_bridge.rs:361` binds a nullifier + destination + height,
nothing else. It doesn't bind the source receipt that authorized the lock,
the recipient on the destination side, the asset/amount, or the
phase/protocol-version. The receipt is sufficient to ack *one* mint of *one*
nullifier; it's insufficient to chain four phases.

**(d) Receipt-chain self-binding is "load-bearing and broken or aspirational."**
`AUDIT-turn-executor.md` summary line 9: *"the fast path's 'signatures,'
`execute_mixed_atomic`'s hosted effects, the proof-carrying sovereign
commitment encoding, and the receipt-chain self-binding — are load-bearing
and broken or aspirational."* Two of these (fast-path sig P0-1, commitment
encoding P0-2) have partial fixes in the current tree; receipt-chain
self-binding does not.

**(e) `TurnReceipt.executor_signature` is never set.**
`AUDIT-turn-executor.md` P3-4: *"Receipts are never signed by the executor in
this crate; the federation-exit verifiability claim in
`verify_receipt_chain_with_keys` rests on a signature that nothing produces."*
Confirmed by grep: no executor code path sets `executor_signature: Some(...)`.

**(f) Receipt has only BLAKE3 form; in-circuit verification has no Poseidon2 form.**
A receipt's `receipt_hash()` is BLAKE3 only. When receipt R₁ is meant to be a
public input to a subsequent proof R₂ (e.g., bridge phase 3 verifying
phase 1, or an IVC step that consumes the previous step's receipt), the
verifier circuit would need to recompute BLAKE3 in-circuit (expensive,
incompatible with the rest of the BabyBear/Poseidon2 stack). No Poseidon2
form of the receipt exists.

**(g) Federation id is bound, source/destination federation ids on the bridge are not.**
`TurnReceipt.federation_id` was added to prevent cross-federation replay
(`turn.rs:267`). `BridgeReceipt` binds `destination_federation` but **not**
`source_federation`. An attacker who controls federation X can replay a
mint-receipt issued for federation A→X to claim it satisfies a bridge
initiated by federation B→X with the same nullifier (unlikely in honest
operation; possible if nullifier domain isn't federation-keyed).

---

## 3. Sovereign receipt — design

A *sovereign cell* commits to a state root; transitions are validated by a
STARK proof. The receipt for a sovereign turn must let any downstream
verifier (a) re-verify the transition without re-running it, (b) chain to
the prior sovereign receipt for replay/forking protection, and (c) feed
itself as a public input to a subsequent proof.

### 3.1 Fields

```rust
pub struct SovereignReceipt {
    // ── domain & chain ───────────────────────────────────────────────────
    /// Version tag: "dregg-sov-receipt-v1"
    pub version: u32,
    /// Federation that produced this receipt. Prevents cross-fed replay.
    pub federation_id: [u8; 32],
    /// Specific node (by Ed25519 public key) that executed it.
    pub executor_id: [u8; 32],
    /// BLAKE3 hash of the prior receipt in this cell's chain, or `None` for genesis.
    pub previous_receipt_hash: Option<[u8; 32]>,
    /// Block height of execution.
    pub block_height: u64,
    /// Monotonic nonce per `agent` cell, copied from `Turn.nonce`.
    pub nonce: u64,
    /// Cell being transitioned.
    pub cell_id: CellId,

    // ── turn binding ─────────────────────────────────────────────────────
    /// `Turn::hash()` of the executed turn (after Turn::hash is fixed per §8).
    pub turn_hash: [u8; 32],

    // ── state transition ─────────────────────────────────────────────────
    /// Pre-state commitment. Encoded as 4 Poseidon2 BabyBear elements
    /// (128-bit field-encoded commitment) packed into 32 bytes via
    /// `babybears_to_bytes32`. See §7.
    pub old_commitment: [u8; 32],
    /// Post-state commitment, same encoding.
    pub new_commitment: [u8; 32],
    /// Effect-VM `effects_hash`, encoded as 4 Poseidon2 BabyBear elements.
    pub effects_hash: [u8; 32],
    /// Net balance delta on this cell. Signed; encoded as i128 (BLAKE3 form);
    /// as `(mag_lo: BabyBear, mag_hi: BabyBear, sign: BabyBear)` in Poseidon2 form,
    /// where mag_hi*2^31 + mag_lo == abs(net_delta), sign ∈ {0,1}.
    pub net_delta: i128,

    // ── proof reference ──────────────────────────────────────────────────
    /// Hash of the STARK proof bytes (BLAKE3). Lets downstream prove the proof
    /// existed at receipt-issuance time even if the proof is GCed.
    pub proof_digest: [u8; 32],
    /// Verifier-key digest of the circuit the proof was made against. Bound
    /// into the executor's trust root: a verifier checks this VK is on its
    /// allowlist before accepting the receipt.
    pub vk_digest: [u8; 32],

    // ── executor signature ───────────────────────────────────────────────
    /// Ed25519 signature by `executor_id` over `receipt_hash_blake3()`.
    /// REQUIRED for sovereign receipts (vs. optional on the legacy `TurnReceipt`).
    pub executor_signature: [u8; 64],
}
```

### 3.2 BLAKE3 form — canonical encoding

`receipt_hash_blake3(r) = BLAKE3(domain || canonical_bytes(r_minus_sig))` where:

- `domain = "dregg-sov-receipt-v1"` (length-prefixed)
- `canonical_bytes` is a deterministic serialization. Recommended: every
  fixed-size field as raw bytes in struct-declaration order; every
  `Option<T>` as a single `0x00` tag or `0x01 || canonical(T)`; every
  variable-length field length-prefixed with a `u64_le`. No `serde`
  default-format dependence (which has historically been a footgun —
  e.g. `bincode` skipping `Option::None` differently from `Option::Some`).

This gives a single 32-byte BLAKE3 digest suitable for:

- Hashmap keys (e.g. pending-bridge registry keyed on receipt hash)
- Network message dedup
- Ed25519 signing target (`executor_signature` is over this 32-byte digest)
- Receipt-chain links (`previous_receipt_hash` is one of these)

### 3.3 Poseidon2 form — in-circuit encoding

`receipt_hash_poseidon2(r) → [BabyBear; 4]`. Computed by absorbing the same
canonical fields into a Poseidon2 sponge, in declaration order, using the
4→1 hash gadget already in `dregg_commit::hash`. Layout for a fixed-arity
absorb (each row is one Poseidon2 4→1 call):

```
row 0:  H₀ = hash_4_to_1(version_bb, fed_id_lo, fed_id_hi, exec_id_lo)
row 1:  H₁ = hash_4_to_1(H₀, exec_id_hi, prev_hash_lo, prev_hash_hi)
row 2:  H₂ = hash_4_to_1(H₁, block_height, nonce, cell_id_lo)
row 3:  H₃ = hash_4_to_1(H₂, cell_id_hi, turn_hash_lo, turn_hash_hi)
row 4:  H₄ = hash_4_to_1(H₃, old_commit[0..4])
row 5:  H₅ = hash_4_to_1(H₄, new_commit[0..4])
row 6:  H₆ = hash_4_to_1(H₅, effects_hash[0..4])
row 7:  H₇ = hash_4_to_1(H₆, net_delta_mag_lo, net_delta_mag_hi, net_delta_sign)
row 8:  H₈ = hash_4_to_1(H₇, proof_digest_lo, proof_digest_hi, vk_digest_lo)
row 9:  H₉ = hash_4_to_1(H₈, vk_digest_hi, 0, 0)  // final
```

The 32-byte BLAKE3-sized fields (`fed_id`, `exec_id`, `prev_hash`,
`cell_id`, `turn_hash`, `proof_digest`, `vk_digest`) are split into `lo`/`hi`
each consisting of 4 BabyBears (so each `[u8;32]` → 8 BabyBears via
`bytes32_to_babybear8`, which already exists at
`turn/src/executor.rs:1175`). The 32-byte *Poseidon2-natural* fields
(`old_commitment`, `new_commitment`, `effects_hash`) carry exactly 4
BabyBears already; their `[u8;32]` form is a pad-extended encoding (§7).

Output: `H₉ ∈ BabyBear⁴` (i.e. the 4-element output of the last Poseidon2
hash invocation, since `hash_4_to_1` here is the squeeze).

### 3.4 Verification

Given a `SovereignReceipt r` and the executor's federation roster
`R = (committee, validators[])`:

1. **Signature.** Recompute `h = receipt_hash_blake3(r)` (excluding signature).
   Verify `Ed25519.verify(r.executor_id, h, r.executor_signature)`. Reject
   if `r.executor_id ∉ R.validators` (executor must be a member of the
   federation it claims to speak for).
2. **VK allowlist.** Reject if `r.vk_digest ∉ R.trusted_vks`.
3. **Receipt chain.** If the verifier has the prior receipt, check that
   `r.previous_receipt_hash == Some(receipt_hash_blake3(prior))`. If the
   verifier maintains a per-cell head map, reject any non-genesis receipt
   whose prior hash does not match the stored head; reject any duplicate of
   the head (replay).
4. **State transition.** (Optional, if proof is available.) Recompute the
   STARK PI layout:
   `[old_commit_bbs..., new_commit_bbs..., effects_hash_bbs..., net_delta_mag_lo, net_delta_mag_hi, net_delta_sign, cell_id_bbs...]`
   and verify the STARK proof against `r.vk_digest`. The receipt commits to
   `proof_digest`, so the verifier can confirm the proof bytes they have
   match.
5. **Monotonicity.** `r.nonce` must be `1 +` the prior receipt's nonce for
   the same `agent`. `r.block_height` must be `>=` the prior's.

The receipt is now *usable as a public input* to a subsequent proof. Its
Poseidon2 form (`receipt_hash_poseidon2(r)`) is what a circuit consumes; its
BLAKE3 form is what off-circuit consumers consume.

---

## 4. Federation receipt — design

A *federation-executed* (non-sovereign) turn is one the federation runs in
the classical way: against actual cell state stored on federation nodes,
under BFT consensus. The receipt for such a turn must reflect that the
**federation** (not a single executor) attested to the transition, and must
be aggregable over many turns.

### 4.1 Architecture choice: aggregate vs. multi-sig

`dregg` already has two flavors of quorum proof:

- **Per-voter Ed25519**: `QuorumCertificate.votes: Vec<(usize, Signature)>`.
  Verified one by one. O(n) verifier work, O(n) certificate size.
- **Threshold BLS via `hints`**: `QuorumCertificate.aggregate_qc:
  Option<ThresholdQC>`. Constant-size aggregate. Verified once. O(1)
  verifier work.

For a federation receipt that crosses federations, **constant-size is
strongly preferred**. Verifying a federation B receipt at federation A
should not require A to know the size of B's committee. We adopt the
`ThresholdQC` flavor as the production receipt, with the per-voter form as
a fallback (mainly for solo mode and tests).

We do *not* introduce FROST. The `hints` BLS scheme is already integrated
and provides what FROST would (single signature, threshold-extractable);
adding FROST would duplicate the crypto without changing the abstraction.

### 4.2 Fields

```rust
pub struct FederationReceipt {
    /// Version tag: "dregg-fed-receipt-v1"
    pub version: u32,
    /// Federation identity (BLAKE3 over the committee's static descriptor).
    pub federation_id: [u8; 32],
    /// Committee epoch (rotates with key rotations; binds receipt to a
    /// specific verifier key).
    pub committee_epoch: u64,

    /// The receipt body that the quorum attested to.
    pub body: FederationReceiptBody,

    /// The quorum certificate over `body_hash_blake3(body)`.
    pub qc: QuorumCertificate,
}

pub struct FederationReceiptBody {
    /// BLAKE3 of the turn (post the §8 fix that includes execution_proof fields).
    pub turn_hash: [u8; 32],
    /// Block this turn was committed in.
    pub block_height: u64,
    /// Block hash (binds receipt to the canonical block).
    pub block_hash: [u8; 32],
    /// The agent cell.
    pub agent: CellId,
    /// Per-agent nonce.
    pub nonce: u64,
    /// Pre/post state hashes of the cells affected.
    /// For a federation-managed (non-sovereign) cell, these are BLAKE3 hashes
    /// of the canonical cell state, not Poseidon2.
    pub pre_state_hash: [u8; 32],
    pub post_state_hash: [u8; 32],
    /// Effects-hash (BLAKE3 of the runtime effect sequence).
    pub effects_hash: [u8; 32],
    /// `previous_receipt_hash` in this agent's chain.
    pub previous_receipt_hash: Option<[u8; 32]>,
    /// Same routing/introduction/derivation/event metadata as `TurnReceipt`.
    pub routing_directives: Vec<RoutingDirective>,
    pub introduction_exports: Vec<IntroductionExport>,
    pub derivation_records: Vec<DerivationRecord>,
    pub emitted_events: Vec<EmittedEvent>,
    pub finality: Finality,
}
```

The QC is over a 32-byte BLAKE3 of `body`, not over the whole body. This
keeps verification cheap and matches the existing `QuorumCertificate::vote_message`
shape (block hash + height + view); here the "block hash" is the
`body_hash`.

### 4.3 BLAKE3 form

`receipt_hash_blake3(r) = BLAKE3(domain || version || federation_id ||
committee_epoch || body_canonical || qc_canonical)`. `qc_canonical`
includes either the ThresholdQC bytes or the votes vector — but for
chaining purposes (`previous_receipt_hash`), we hash *only the body*,
because the QC is a property of "which validators happened to be online,"
not the state transition itself. So receipt-chain links use
`body_hash_blake3(body)`.

This is also what gets signed by `agent`'s next turn: the next turn's
`previous_receipt_hash` is `body_hash_blake3` of the previous receipt's
body, regardless of which validators signed it.

### 4.4 Poseidon2 form

A federation-managed cell's state is *not* Poseidon2 — it's a heterogeneous
runtime `Cell` struct. So `pre_state_hash` and `post_state_hash` are BLAKE3,
and they don't have a natural Poseidon2 form.

For in-circuit consumption (which is rare for federation receipts, since
they are by definition not proof-carrying), we publish a Poseidon2 hash
*of the receipt's BLAKE3 hash* — i.e. `bytes32_to_babybear8(body_hash)`
absorbed into Poseidon2 with the version tag. This is a 1-way binding: a
circuit that consumes a federation receipt cannot inspect the body, only
verify-equality against a known BLAKE3.

### 4.5 Fast path integration

The fast path (`turn/src/fast_path.rs`) collects 2f+1 `TurnSign`s into a
`TurnCertificate`. This is morally identical to a `QuorumCertificate` over
the turn hash. The integration is:

1. `TurnSign` signatures are Ed25519 over `dregg-fast-path-sign-v2 ||
   turn_hash` (already a real Ed25519 sig per the live tree; the historical
   P0-1 finding is fixed).
2. When `execute_certified_turn` succeeds, it should emit a
   `FederationReceipt` whose `qc.votes` is the set of `TurnSign`s
   (converted to `(voter_id, Signature)` pairs), with
   `qc.aggregate_qc = None`. The body uses the actual turn-execution
   results.
3. Optionally, the validator set can run BLS aggregation post-hoc to
   compact the certificate. The receipt is rewritable in the sense that
   anyone with 2f+1 individual signatures can produce the aggregate, but
   the *receipt-chain link* (which uses `body_hash_blake3`) is unchanged.
4. The `finality` field is `Final` if the certificate met the BFT threshold
   (`effective_quorum_threshold(mode, n)` from `federation`); `Tentative`
   only when in solo mode.

This addresses the unfinished half of P0-1: the fast-path was producing
real signatures but not wrapping them in a typed receipt. A
`FederationReceipt` with `qc.votes = TurnSigns` is the connecting piece.

### 4.6 Receipt-chain interaction

Federation receipts chain like sovereign receipts: each has
`previous_receipt_hash: Option<[u8; 32]>` pointing at the *body hash* of
the prior receipt. The executor enforces this (§8 P0-3 fix): a turn whose
`previous_receipt_hash != Some(stored_head_for_agent)` is rejected, except
when the agent is brand-new (no head) and the turn claims `None`.

The chain can *interleave* sovereign and federation receipts for the same
agent — an agent might issue a sovereign turn (proof-carrying, against a
sovereign-mode cell it controls) and then a federation turn (against a
hosted cell). Both link via `previous_receipt_hash` to a single per-agent
chain. The receipt format is distinguishable by version tag.

---

## 5. Bridge receipt — design (most carefully)

The bridge moves value between federations. It is the most security-
critical receipt boundary in the system because (a) the receiver federation
has *no* shared state with the sender — only the bridge protocol's
cryptographic evidence; (b) timeouts mean there is no recovery from a
mis-signed receipt; (c) replay across federations costs real money.

The current `BridgeReceipt` (note_bridge.rs:361) is one signature over
(nullifier, dest, mint_height). This is the Mint-ack message of Phase 2.
The protocol has four phases, all of which need typed receipts.

### 5.1 Bridge phases — recap

The note-bridge protocol from `cell/src/note_bridge.rs`:

- **Phase 1, Lock** (source federation): The owner of a note submits a
  "lock" turn. The note is locked (not yet burned). A `PendingBridge` is
  recorded with `state = Locked { timeout_height, destination }`.
- **Phase 2, Mint** (destination federation): The destination receives an
  attestation of the Lock and mints a corresponding note. Issues a
  mint-receipt.
- **Phase 3, Finalize** (source federation): The source verifies the
  mint-receipt and permanently nullifies the note (transition to
  `Finalized`).
- **Phase 4, Cancel** (source federation): If the timeout elapses without
  a finalize, the note is unlocked. Source-only — no destination involvement.

This is structurally close to IBC's `MsgSendPacket` /
`MsgRecvPacket` / `MsgAcknowledgePacket` / `MsgTimeoutPacket` flow
(ICS-004). IBC distinguishes:

- `PacketCommitment` — what the sending chain stores after `SendPacket`
  (a 32-byte hash of the packet's data + timeout). Counterparty proves
  inclusion of this in the sender's state.
- `PacketReceipt` — what the receiving chain stores after `RecvPacket`
  (just a presence marker: "I have seen this packet"). Prevents replay
  via a presence check, not a chain.
- `PacketAcknowledgement` — what the receiving chain stores after
  application-level handling (success/failure data). The sender proves
  inclusion of this when calling `AcknowledgePacket`.
- `TimeoutPacket` — the sender proves *non-inclusion* of a `PacketReceipt`
  on the receiver to reclaim funds.

`dregg`'s bridge is morally the same flow with two important differences:
(1) dregg federations don't have a shared light-client of each other; they
trust each other's signed receipts directly. So all four IBC commitments
collapse to *signed receipts*. (2) `dregg` wants in-circuit verification of
each phase's receipt as part of the next phase's proof — IBC verifies via
light-client Merkle inclusion proofs, dregg verifies via Poseidon2
signature recomputation in the next-phase circuit.

References: ICS-004 spec
(`https://github.com/cosmos/ibc/blob/main/spec/core/ics-004-channel-and-packet-semantics`)
defines `PacketCommitment(data, timeout) = hash(data || timeout)` and
distinguishes the three commitment types.

### 5.2 Common envelope

All four phase-receipts share an envelope. The phase number is bound,
and federation IDs are bound in both directions for replay protection:

```rust
pub struct BridgeReceiptEnvelope {
    /// Version tag: "dregg-bridge-receipt-v2"
    pub version: u32,
    /// Phase: 1=Lock, 2=Mint, 3=Finalize, 4=Cancel.
    pub phase: u8,
    /// Source federation id (always the federation that initiates).
    pub src_federation_id: [u8; 32],
    /// Destination federation id.
    pub dst_federation_id: [u8; 32],
    /// Unique bridge-instance id: BLAKE3("dregg-bridge-id-v1" || lock_nullifier
    ///   || src_fed || dst_fed || initiating_nonce). Identical across all 4
    ///   phase receipts; serves as the cross-phase join key.
    pub bridge_id: [u8; 32],
    /// Sequence within this bridge (always equal to `phase`, redundant for clarity).
    pub seq: u8,
    /// Block height on the issuing federation.
    pub block_height: u64,
    /// Issuing federation's monotonic bridge counter (replay protection within
    /// the issuing federation).
    pub issuer_nonce: u64,
    /// Hash of the *previous-phase* receipt this one is responding to.
    /// Phase 1 has `None`. Phase 2 binds Phase 1. Phase 3 binds Phase 2.
    /// Phase 4 binds Phase 1 (the locked, then-timed-out lock receipt).
    pub previous_phase_receipt_hash: Option<[u8; 32]>,
    /// Phase-specific payload.
    pub payload: BridgePhasePayload,
    /// QC over `body_hash_blake3(envelope_minus_qc)`.
    /// REQUIRED for phases 1,2,3 (cross-federation phases).
    /// Phase 4 (cancel, source-only) MAY use a single executor signature
    /// since it never leaves the source federation.
    pub qc: QuorumCertificate,
}
```

### 5.3 Phase-specific payloads

```rust
pub enum BridgePhasePayload {
    /// Phase 1 — Lock. Source federation attests that the note is locked
    /// and the bridge intent is committed.
    Lock {
        /// Nullifier of the locked note (source-side).
        nullifier: [u8; 32],
        /// Pedersen value commitment of the locked amount (hides the value
        /// from observers; revealed via the bridge program to the dst).
        value_commitment: [u8; 32],
        /// Asset type id (32-byte hash for cross-fed asset registry).
        asset_type: [u8; 32],
        /// Commitment to the expected destination recipient. The dst
        /// federation uses this to determine who to credit.
        ///   = Poseidon2(recipient_pubkey, viewing_key_hash, nonce)
        expected_recipient_commitment: [u8; 32],
        /// Source-side timeout height after which Phase 4 (cancel) is allowed.
        timeout_height: u64,
        /// The portable spending proof (what the destination needs to verify
        /// the lock is real). For dregg this is a Schnorr proof bound to
        /// the cross-federation key derivation.
        spending_proof_digest: [u8; 32],  // BLAKE3 of the proof bytes
    },
    /// Phase 2 — Mint. Destination federation attests that it received
    /// the Phase-1 receipt, verified it, and minted a corresponding note.
    Mint {
        /// The Phase-1 receipt this is responding to. Bound via
        /// `previous_phase_receipt_hash`, repeated here for explicitness.
        source_lock_receipt_hash: [u8; 32],
        /// Nullifier on the destination (chosen by destination; binds the
        /// minted note so it can be re-bridged or spent).
        mint_nullifier: [u8; 32],
        /// Commitment to the minted note (Poseidon2 leaf in dst's note tree).
        mint_commitment: [u8; 32],
        /// Insertion proof: the dst's note-tree root after insertion.
        post_insert_root: [u8; 32],
        /// Mint height on destination.
        mint_height: u64,
    },
    /// Phase 3 — Finalize. Source federation acknowledges the mint and
    /// makes the source nullifier permanent.
    Finalize {
        /// The Phase-2 receipt this finalizes. Bound via
        /// `previous_phase_receipt_hash`, repeated here.
        destination_mint_receipt_hash: [u8; 32],
        /// Permanent nullifier set root on source after this finalize.
        post_nullifier_root: [u8; 32],
        /// Confirms the original locked nullifier.
        finalized_nullifier: [u8; 32],
    },
    /// Phase 4 — Cancel. Source federation reclaims the locked note after
    /// timeout. No destination involvement.
    Cancel {
        /// The Phase-1 receipt being cancelled.
        source_lock_receipt_hash: [u8; 32],
        /// Block height at which cancellation was processed (must be > the
        /// Phase-1 timeout_height).
        cancel_height: u64,
        /// The nullifier that is being unlocked. After cancel, this nullifier
        /// returns to the spendable set.
        unlocked_nullifier: [u8; 32],
        /// Source's nullifier-set root after unlocking.
        post_unlock_root: [u8; 32],
        /// Anti-finalize binding: hash of the most recent state observed at
        /// the destination, demonstrating "as of source.cancel_height, the
        /// destination had not finalized." For the protocol below, this is
        /// optional; the canonical defense against simultaneous mint+cancel
        /// is the lock-receipt's timeout being a strict upper bound on the
        /// destination's mint deadline. (See §5.5.)
        observed_dst_height: Option<u64>,
    },
}
```

### 5.4 Phase-chain semantics

The four receipts form an authenticated state machine over a single
`bridge_id`:

```
[Phase 1: Lock] ──► [Phase 2: Mint] ──► [Phase 3: Finalize]
   on source         on destination       on source
       │
       └─► (if timeout reached, no Phase 2) ──► [Phase 4: Cancel]
                                                  on source
```

Properties:

1. **Bridge-id uniqueness.** `bridge_id` is a deterministic function of
   the Phase-1 lock's `nullifier + src + dst + nonce`. Across both
   federations, no two bridges can share an id (no two locks reuse the
   same nullifier under the source's nullifier-uniqueness invariant).
   This is the cross-federation join key.

2. **Phase-chain binding.** Each receipt's
   `previous_phase_receipt_hash` ties it to the prior phase, by
   BLAKE3 hash. Phase 2 references Phase 1; Phase 3 references Phase 2;
   Phase 4 references Phase 1. Phase 1 has `None`. This is how the
   destination "proves to the source it received and minted": its Phase
   2 receipt has `previous_phase_receipt_hash = Some(Phase1.body_hash)`,
   and the body is signed by destination's quorum. The source, in Phase
   3, runs verification:
   - QC over Phase 2 body is valid for the destination federation's
     committee (looked up by `dst_federation_id + committee_epoch`).
   - `Phase2.previous_phase_receipt_hash == Some(Phase1.body_hash)`
     where Phase 1 is the source's own stored lock receipt.
   - `Phase2.payload.source_lock_receipt_hash == Phase1.body_hash`
     (redundant binding; allows verifying without re-deserializing
     Phase 1).
   - `Phase2.bridge_id == Phase1.bridge_id`.

3. **Source proves to destination the lock is real.** Phase 2 is gated on
   the destination receiving Phase 1. Phase 1 carries the source's QC.
   The destination verifies:
   - QC over Phase 1 body is valid for source federation's committee.
   - `Phase1.payload` includes `nullifier`, `value_commitment`,
     `asset_type`, `expected_recipient_commitment`, `timeout_height`.
   - `spending_proof_digest` matches the proof the dst received OOB
     (since dregg doesn't have light-clients of source-side state, the
     full spending proof must be transmitted alongside the receipt; the
     digest binds it).
   - `Phase1.payload.timeout_height` is far enough in the future that
     the destination has time to mint, factoring in a safety margin
     `Δsafe` (see §5.5).
   - The lock has not already been finalized at the source (the
     destination can't verify this without a light-client; this is
     the synchrony assumption — see §5.5).

4. **Offline federation handling.** If destination is offline:
   - Source waits until `Phase1.payload.timeout_height`. After that, it
     issues Phase 4 (Cancel). The note is unlocked.
   - If destination later comes back online and tries to issue Phase 2,
     the source rejects it because the local `PendingBridge` is already
     in `Cancelled` state.

   If source is offline after Phase 2:
   - Destination has already minted. It does not unmint. The destination's
     view: "I have a valid mint; source has not finalized."
   - Source comes back online, sees Phase 2 receipt, issues Phase 3
     normally. As long as the source's lock-receipt is still in
     `Locked` state (i.e. cancellation has not been triggered), Phase 3
     succeeds.

5. **Replay protection across federations.**
   - Within a federation: `issuer_nonce` is a monotonic per-federation
     bridge counter. Two receipts with the same `(issuer, issuer_nonce)`
     are equal or one is invalid.
   - Across federations: `bridge_id` is unique by construction (function
     of the source nullifier). A destination cannot replay a Phase 2 from
     bridge A as Phase 2 for bridge B, because the receipt body binds the
     `bridge_id` and `nullifier`.
   - Cross-version replay: the `version` tag is a domain separator. A
     v1 receipt can never satisfy a v2 verifier even if all other bytes
     coincide.

### 5.5 Race condition: mint-and-cancel

The dangerous case is: destination mints (Phase 2) at the same time
the source cancels (Phase 4) because the destination took too long.
Without defense, the source has unlocked the note (Phase 4) **and** the
destination has minted (Phase 2) — value is created out of thin air.

**Defense (the safety-margin rule).** Phase 1's `timeout_height` and the
destination's permissible mint window are related by:

```
src_timeout_height >= src_lock_height
                      + Δproto       // network propagation budget
                      + Δmint        // dst's max mint delay
                      + Δsafe        // safety margin (≥ 1 block)
```

The destination's mint must happen *before* `src_timeout_height - Δsafe`
(in destination's clock, with a federation-clock-sync assumption). If the
destination mints later, it issues a Phase 2 that the source can prove is
**post-timeout**, and the source rejects it (Phase 3 will not be issued;
Cancel will).

The destination is responsible for not minting if it cannot meet the
deadline. A faulty/Byzantine destination that mints anyway has issued an
unenforceable receipt — the source cancels, the source's
`PendingBridgeSet` records cancellation, and any future Phase 3 attempt
from the same `bridge_id` is rejected with `BridgeError::InvalidBridgeState`.

This makes the bridge **synchronous within Δproto+Δmint+Δsafe blocks**.
For dregg's federation cadence (1s blocks typically), `Δproto = 5`,
`Δmint = 5`, `Δsafe = 5` gives a 15-block (15s) lower bound on
`timeout_height - lock_height`. The lock initiator can set higher
timeouts; lower is rejected at lock-creation time.

This is structurally similar to IBC's `timeout_timestamp` requirement —
the *send* chain commits to a deadline, and the *recv* chain must
include a `timestamp < timeout` proof or the recv is rejected.

### 5.6 BLAKE3 form

`bridge_receipt_hash_blake3(r) = BLAKE3("dregg-bridge-receipt-v2" ||
canonical_envelope_minus_qc)`. The QC is *not* included in the BLAKE3
hash for chain-link purposes — the chain link is over the *body*, so
that a re-aggregated certificate (e.g. converting per-voter votes to
ThresholdQC) does not change the chain.

### 5.7 Poseidon2 form

This is the cross-circuit binding that lets Phase 3's proof attest to
having verified Phase 2's receipt. The Poseidon2 hash absorbs:

```
H(version, phase, src_fed_lo, src_fed_hi,
  dst_fed_lo, dst_fed_hi, bridge_id_lo, bridge_id_hi,
  block_height, issuer_nonce, prev_recpt_lo, prev_recpt_hi,
  payload_poseidon_hash)
```

where `payload_poseidon_hash` is a Poseidon2 absorb of the payload's
fields in declaration order (using `bytes32_to_babybear8` for each 32-byte
field).

This is the form a Phase-3 proof circuit consumes when it wants to verify
"I am responding to *this* Phase 2 receipt." The exact in-circuit shape
follows §6.

The earlier note from the protocol review:

> `Poseidon2(src_federation_id, dst_federation_id, note_hash, phase,
>  block_height, nonce)`

is the *receipt-identity* (collision-resistant joint key), not the full
receipt content. We compute it explicitly:

```
recpt_identity = Poseidon2(version, src_fed, dst_fed, bridge_id, phase, block_height, issuer_nonce)
```

This is what an indexer would key its receipt store on. It is **not** the
content-binding hash — that is `receipt_hash_poseidon2` above.

### 5.8 QC verification at the boundary

For phases 1, 2, 3 (cross-federation), the receiving federation must
verify the QC of the issuing federation. The receiving federation looks
up the issuing federation's committee by
`(federation_id, committee_epoch)`. This lookup table is the trust root:
every federation dregg talks to must be registered with at least one
known committee descriptor (BLS group public key, or a list of validator
Ed25519 keys with the threshold).

Without a global root, federations are **bilaterally-trusted**: federation
A maintains a registry of federations it accepts bridges from, and the
committee key for each. This is a config-level decision. The receipt
format does not constrain it.

For the strongest setting: a federation-of-federations could maintain a
shared registry (a `FederationOfFederations` light-client). This is
explicit future work; the receipt format already supports it via
`committee_epoch` rotation.

---

## 6. In-circuit receipt verification

When receipt R₁ is an input to circuit R₂'s proof (e.g., bridge Phase 3
verifies Phase 1, or IVC step k verifies step k-1), the verifier circuit
needs to assert that R₁ is well-formed and that R₂'s public inputs derive
from R₁.

### 6.1 Trace columns

Add a small "receipt-verify" AIR module. For each verification of an
external receipt, the AIR allocates:

```
selector_recv_verify : 1 column, boolean
absorbed_blake_lo[8] : 8 columns (the 32-byte BLAKE3 of the receipt, split
                                  into 8 BabyBears via bytes32_to_babybear8)
poseidon_acc[4]      : 4 columns (running Poseidon2 sponge state)
field_lane[4]        : 4 columns (per-field absorb input, padded)
```

The verification works by recomputing the receipt's Poseidon2 hash
column-by-column. At each "absorb" row, the AIR enforces

```
poseidon_acc_after = Poseidon2(poseidon_acc_before, field_lane)
```

via the existing Poseidon2 gadget. At the final row, the AIR pins
`poseidon_acc == declared_receipt_poseidon_hash` as a public input.

### 6.2 AIR constraints

1. **Selector booleanity.** `selector_recv_verify * (1 - selector_recv_verify) == 0`.
2. **Sponge transition.** When `selector_recv_verify == 1`:
   `poseidon_acc_next - Poseidon2(poseidon_acc, field_lane) == 0`. This is
   a chain of `hash_4_to_1` calls just like the state-commitment tree at
   `effect_vm.rs:2266`, which is already implemented and audit-clean (per
   `AUDIT-circuit.md` §1).
3. **PI binding.** Boundary constraint: at the last absorb row,
   `poseidon_acc[0..4] == PI[RECPT_HASH_POSEIDON_0..3]`.
4. **Optional BLAKE3 binding.** When the consuming code wants to bind both
   forms, the AIR additionally exposes the BLAKE3 form as PI. This is
   *not* recomputed in-circuit (BLAKE3 in BabyBear is expensive); the
   verifier compares it post-hoc against an externally computed
   `receipt_hash_blake3`. This is acceptable because the
   `receipt_hash_blake3` and `receipt_hash_poseidon2` are computed over
   the same canonical bytes — if `poseidon2(canonical_bytes) ==
   declared_poseidon` then a verifier holding `canonical_bytes` knows
   `blake3(canonical_bytes) == declared_blake3` (both are functions of
   the same input).

### 6.3 Public-input layout (for proofs that consume a receipt)

```
PI[0..3] : poseidon_hash of the consumed receipt (4 BabyBears)
PI[4..7] : version + phase + ... receipt-identity tuple
PI[8..N] : circuit-specific PIs (state transitions, etc.)
```

### 6.4 What this enables

- **Bridge Phase 3 circuit.** Consumes the Phase-2 receipt's Poseidon2
  hash as a PI. Circuit constraints attest that the source's local
  `PendingBridge` record's `bridge_id` matches the Phase 2 receipt's
  `bridge_id`, and that the destination's mint commitment is the one
  the source's accounting expected.
- **IVC steps over a chain of `SovereignReceipt`s.** Each step's circuit
  consumes the prior receipt's Poseidon2 hash as a PI and pins the
  prior's `new_commitment` as the current's `old_commitment`. This
  closes the per-cell receipt-chain in-circuit.
- **Cross-cell atomic turns** (the `execute_atomic_sovereign` path):
  each per-cell proof attests to the sovereign receipt for that cell;
  the atomic-turn verifier collects all receipts and checks
  `Σ net_delta == 0` *in-circuit*, which closes the
  conservation-check gap that `AUDIT-circuit.md` P0-1 identified
  (net_delta currently isn't algebraically bound; if we tie the
  receipt's `net_delta` to the AIR's `aux[2]/aux[3]` as a boundary PI
  that *is* enforced, the binding is direct).

---

## 7. Dual-accumulator binding

Receipts are the canonical case for the BLAKE3/Poseidon2 dual binding.
The pattern, generalized:

1. Define one canonical byte serialization `canonical_bytes(r)` over the
   receipt struct. Deterministic, no `serde` defaults, explicit length
   prefixes, explicit `Option` tags.
2. `receipt_hash_blake3(r) = BLAKE3("dregg-<type>-receipt-v<n>" ||
   canonical_bytes(r))`. Used for hash-map keys, network dedup,
   Ed25519/BLS signing targets, and chain links (`previous_*_hash`).
3. `receipt_hash_poseidon2(r) = Poseidon2_absorb_sponge(canonical_bytes(r)
   as field_elements)`. Used for in-circuit PI binding. The field-element
   layout is fixed per receipt type (see §3.3 for sovereign).
4. The two hashes are independently collision-resistant but bind the
   *same* underlying bytes. Equality of one implies equality of the
   other (modulo collisions on whichever hash, which are computationally
   infeasible for both).

This requires a companion commitment framework. Things that need to exist
that haven't been written here (probably in a `DESIGN-commitment-framework.md`):

- A `bytes32_to_babybear8(bytes: [u8;32]) -> [BabyBear; 8]` helper.
  Already exists at `turn/src/executor.rs:1175`, but is not domain-keyed
  (i.e. the same bytes always produce the same BabyBears, regardless of
  context). For receipts, we want a *typed* version per receipt class
  that prefixes a domain tag before absorb.
- A `babybears8_to_bytes32(bbs: [BabyBear; 8]) -> [u8;32]` inverse, for
  re-extracting the BLAKE3-form for off-circuit verifiers from an
  in-circuit value.
- A canonical "absorb a struct" helper, generic over receipt types,
  whose output (Poseidon2 sponge final state) is the canonical
  Poseidon2 hash. Must agree byte-for-byte with the BLAKE3-side input.
- Test vectors that pin both hashes for known receipts, to detect drift.

The 32-byte fields that are *natively* 4-BabyBear Poseidon2 outputs
(`old_commitment`, `new_commitment`, `effects_hash`) round-trip exactly:
their `[u8;32]` form is `babybears4_to_bytes32` with the high 16 bytes
zero. The 32-byte fields that are *natively* BLAKE3 outputs
(`turn_hash`, `federation_id`, `executor_id`, `proof_digest`,
`vk_digest`) are full-entropy 32-byte values; they're absorbed as 8
BabyBears, with each BabyBear holding 31 bits of the original bytes
(8 × 31 = 248 bits, slightly less than 256; the last 8 bits are recovered
from a separate "tail" BabyBear, or accepted as a deliberate 248-bit
binding).

The audits flagged the *opposite* failure: 32-byte commitments being
read as 4 bytes (P0-2 in turn-executor, P1-1 in circuit). The fix
described above goes the other way — full 8-element encoding — which
closes both audits simultaneously.

---

## 8. Migration plan

The fixes break into four roughly-orthogonal blocks. They can be done in
any order, but the dependencies below are real.

### 8.1 Block 1 — Turn hash covers all proof fields (P1-1)

`turn/src/turn.rs:133`. Bump version tag to `dregg-turn-v3:` and include
`execution_proof`, `execution_proof_cell`, `execution_proof_new_commitment`,
`conservation_proof`, `sovereign_witnesses`, and `custom_program_proofs`
in `Turn::hash()`. The cipherclerk's `compute_turn_bytes` (AUDIT-cclerk P2-10)
must match.

**Estimated impact:** ~50 LOC change in `turn::Turn::hash()`, ~20 LOC in
cclerk, ~all tests need new turn-hashes recorded, version-tag check
prevents v2/v3 confusion at signing time.

### 8.2 Block 2 — Receipt-chain enforcement (P0-3)

`turn/src/executor.rs::execute`. Add a `last_receipt_hash: Option<[u8;
32]>` to `CellState` (per the AUDIT open question), and check at the top
of `execute()`:

```rust
let stored_head = ledger.get(&turn.agent).map(|c| c.state.last_receipt_hash);
if let Some(declared_prev) = turn.previous_receipt_hash {
    if stored_head != Some(Some(declared_prev)) {
        return Err(TurnError::ReceiptChainMismatch { /* ... */ });
    }
} else {
    // Genesis: only valid if stored_head is None (no prior receipt).
    if stored_head.is_some() && stored_head.unwrap().is_some() {
        return Err(TurnError::ReceiptChainGenesisAfterChain);
    }
}
```

On commit, set `cell.state.last_receipt_hash = Some(receipt.receipt_hash())`.

Cipherclerk changes (per AUDIT-cclerk P3-6): `build_authorized_turn`,
`allocate_queue`, `enqueue_message`, `dequeue_message`, `atomic_queue_tx`
must thread the current head through instead of hardcoding `None`.

### 8.3 Block 3 — Real executor signatures (P0-1 follow-up, P3-4)

Fast-path signatures are already real Ed25519 in the live tree. The
remaining piece is that `TurnReceipt.executor_signature` is never set.
Have `execute()` end with:

```rust
receipt.executor_signature = Some(
    self.executor_signing_key.sign(&receipt.receipt_hash()).to_bytes().to_vec()
);
```

This requires the executor to hold a signing key (currently it doesn't;
`TurnExecutor` has no signing-key field). Add:

```rust
pub struct TurnExecutor {
    // ...existing fields...
    executor_signing_key: Option<ed25519_dalek::SigningKey>,
}
```

with a setter. In production, populate from federation node config; in
tests, generate ephemeral. `verify_receipt_chain_with_keys` already
checks `executor_signature` if present, so the receiver-side code
already handles the signed case.

### 8.4 Block 4 — Bridge receipt rollout

The current `BridgeReceipt` (note_bridge.rs:361) is a Phase-2 mint-ack
only. Replace with the `BridgeReceiptEnvelope` from §5.2. Steps:

1. Add `BridgeReceiptEnvelope`, `BridgePhasePayload`, and their
   serialization to a new `bridge/src/receipt.rs` (or extend
   `cell/src/note_bridge.rs`).
2. Migrate `verify_bridge_receipt` to accept the envelope. The QC
   verification path requires looking up the issuing federation's
   committee — wire that through `TurnExecutor::trusted_federation_roots`.
3. Implement `bridge_receipt_hash_blake3` and
   `bridge_receipt_hash_poseidon2`. Test vectors first.
4. Wire receipts into all four phase entrypoints:
   - `initiate_bridge` (Phase 1) emits a `BridgeReceiptEnvelope { phase: 1, payload: Lock { .. } }`.
   - The destination's mint handler (a new entrypoint, not yet present)
     emits Phase 2.
   - `finalize_bridge` (Phase 3) verifies the incoming Phase 2 and emits
     Phase 3.
   - `cancel_bridge` (Phase 4) emits Phase 4.
5. Persist phase-receipts in a per-federation `BridgeReceiptStore`,
   keyed on `bridge_id`. The store is the source of truth for
   "which phase have we issued for this bridge."
6. Implement the in-circuit verifier (§6) as a separate AIR module
   under `circuit/src/bridge_receipt_air.rs`. Initially without IVC;
   IVC composition follows in a later block.
7. Deprecate the legacy `BridgeReceipt`. Mark `#[deprecated(note =
   "use BridgeReceiptEnvelope")]` on the old struct; keep it for one
   release to allow nodes to roll over.

### 8.5 Block 5 — Promote `TurnReceipt` to `SovereignReceipt` / `FederationReceipt` discriminated union

The current `TurnReceipt` conflates the two paths. Introduce:

```rust
pub enum Receipt {
    Sovereign(SovereignReceipt),
    Federation(FederationReceipt),
}

impl Receipt {
    pub fn body_hash_blake3(&self) -> [u8; 32] { ... }
    pub fn body_hash_poseidon2(&self) -> [BabyBear; 4] { ... }
    pub fn previous_receipt_hash(&self) -> Option<[u8; 32]> { ... }
}
```

with a shared `previous_receipt_hash` interface. The receipt chain can
interleave the two. Update `verify_receipt_chain` to handle both.

This is a significant API change. Realistically: keep `TurnReceipt` as
the storage type for now, and introduce `SovereignReceipt` /
`FederationReceipt` as projection types that `TurnReceipt` can be
converted into based on a discriminant field (e.g.,
`TurnReceipt.execution_path: ExecutionPath`). Migrate consumers
incrementally.

### 8.6 Block 6 — Replace truncating encoders

P0-2 (sovereign commitment 31-bit) and P1-1 (effects-hash truncation,
both audits). The fix is the 8-BabyBear encoding from §7. This requires
matching circuit-side changes (per `AUDIT-circuit.md` P1-1 fix
recommendation: widen the in-circuit state commitment).

Sequence:

1. Add `commitment_to_babybear8` (replaces `commitment_to_babybear`).
2. Widen the Effect VM AIR's `state_commitment` from 1 BabyBear to 4
   BabyBears (commitment tree already produces 4; the truncation
   happens at the PI boundary).
3. Widen the proof PI layout: `OLD_COMMIT[0..4]`, `NEW_COMMIT[0..4]`,
   `EFFECTS_HASH[0..4]`, `NET_DELTA_MAG[0..2]`, `NET_DELTA_SIGN`,
   `CELL_ID[0..4]` (the in-circuit encoding from §3.3).
4. Add boundary constraints binding `net_delta_mag` to
   `last_bal_lo - first_bal_lo` (closes `AUDIT-circuit.md` P0-1).
5. Update `verify_and_commit_proof` to read the wider PI.

This block depends on the circuit auditor's recommendations being
applied; it shouldn't ship without their changes.

### 8.7 Block 7 — Test vectors & cross-implementation parity

For every receipt type, produce committed test vectors:
- A canonical struct
- Its `canonical_bytes` (hex)
- Its `receipt_hash_blake3` (hex)
- Its `receipt_hash_poseidon2` (4 BabyBears, hex)

Stored under `tests/vectors/receipts/`. Used by both Rust and the
TypeScript SDK to detect drift. The TS SDK (`ts-sdk/`, `sdk-ts/`) should
implement at least the BLAKE3 form so cipherclerks can verify receipts they
receive.

---

## Closing notes

The three-receipt design is unified by a single dual-hash discipline
(BLAKE3 + Poseidon2 over identical canonical bytes), a single
chain-link discipline (`previous_*_receipt_hash` everywhere), and
explicit version tags (`dregg-<type>-receipt-vN`).

The bridge receipt is the most security-critical because it crosses
federations with no shared light-client, timeouts make recovery
impossible, and the IBC equivalent (ICS-004) is hard-fought experience
we should borrow from: split commitments from receipts from acks; bind
timeouts in the commitment; never let an ack and a timeout both
succeed.
