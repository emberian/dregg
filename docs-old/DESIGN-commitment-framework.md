# `dregg` Commitment Framework — Dual-Accumulator Design

**Status:** design proposal
**Author:** ember
**Date:** 2026-05-23
**Supersedes (partially):** the ad-hoc per-module commitment patterns in
`cell/src/commitment.rs`, `cell/src/note.rs`, `cell/src/seal.rs`,
`turn/src/turn.rs`, `turn/src/obligation.rs`, `turn/src/conditional.rs`,
`commit/src/poseidon2_tree.rs`, `storage/src/blinded.rs`,
`circuit/src/effect_vm.rs::CellState::compute_commitment`, and several callers
in `wire/`, `sdk/`, and `bridge/`.

---

## 0. The thesis

> *"…a dual-accumulator design with also BLAKE3 supported for fast
> out-of-circuit things…"*

Every authoritative content commitment in dregg SHOULD carry **two** companion
digests:

1. **`blake3: [u8; 32]`** — the canonical byte-domain commitment. Cheap,
   used everywhere outside a STARK: storage keys, gossip dedup, signatures,
   cclerk APIs, REST/JSON encodings, ledger Merkle leaves, log lines.
2. **`poseidon2: [BabyBear; 4]`** — the field-domain commitment over the
   STARK-native field (BabyBear, 31-bit). Used as AIR public inputs, in
   trace state columns, in transition constraints, in lookup arguments.

The two are bound *one-directionally* to a shared canonical byte encoding
of the underlying value. We never attempt to verify BLAKE3 inside a STARK;
instead, the prover absorbs the same canonical preimage into both hashers
and trust between the two forms is established at trusted boundary points
(cclerk sealing, executor verification of inbound capabilities, federation
ingress) where both forms are recomputed from the preimage.

This document inventories where commitments live today, defines the typed
`Commitment<T>` framework, specifies the bytes↔felts bijection, picks five
concrete migration targets, and draws the in-circuit / out-of-circuit
boundary explicitly.

---

## 1. Inventory of current commitments

### 1.1 Cell state and identity

| Commitment | Location | Domain | Shape | Has circuit form? |
| --- | --- | --- | --- | --- |
| Canonical cell state commitment | `cell/src/commitment.rs:100` (`compute_canonical_state_commitment`) | BLAKE3 derive_key `"dregg-cell:canonical-state-commitment v1"` | flat hash over tagged length-prefixed encoding | No — adapter `canonical_to_babybear_pi` (line 304) packs to 8 felts but no Poseidon2 binding exists |
| Capability set root | `cell/src/commitment.rs:277` (`compute_canonical_capability_root`) | BLAKE3 derive_key | flat hash over CapabilityRefs | Partial — circuit uses `capability_root: BabyBear` from `effect_vm.rs:645` but with no documented binding to the BLAKE3 form |
| Effect-VM cell state commitment | `circuit/src/effect_vm.rs:684` (`CellState::compute_commitment`) | Poseidon2 (`hash_4_to_1`) | 4-leaf tree of three intermediates over `(bal_lo, bal_hi, nonce, fields[0..8], capability_root)` | Yes — this **is** the circuit form, but commits to a strict subset (no identity, perms, VK) of the canonical state |
| Ledger Merkle leaf | `cell/src/ledger.rs::hash_cell_canonical` (wrapper of canonical) | BLAKE3 | flat hash | No |
| Sovereign cell registration commitment | `cell/src/ledger.rs:231` (`SovereignRegistration.commitment`) | BLAKE3 (mirrors canonical) | flat hash | No |

### 1.2 Notes (anonymous value)

| Commitment | Location | Domain | Shape | Has circuit form? |
| --- | --- | --- | --- | --- |
| Note BLAKE3 commitment | `cell/src/note.rs:162` (`Note::commitment`) | BLAKE3 derive_key `"dregg-note commitment v1"` | flat hash over `(owner ‖ fields[8] ‖ randomness ‖ creation_nonce)` | Yes — companion `poseidon2_commitment` |
| Note Poseidon2 commitment | `cell/src/note.rs:229` (`Note::poseidon2_commitment`) | Poseidon2 `hash_many` | sponge over 5 felts | **This is the existing dual-form prototype.** |
| Note BLAKE3 nullifier | `cell/src/note.rs:179` (`Note::nullifier`) | BLAKE3 derive_key `"dregg-note nullifier v1"` | flat hash over `(commitment ‖ spending_key ‖ creation_nonce)` | The circuit AIR (`note_spending_air.rs`) computes a Poseidon2 nullifier from witness columns; the two are **not** explicitly bound |
| Poseidon2 note Merkle tree | `commit/src/poseidon2_tree.rs:79` (`Poseidon2MerkleTree`) | Poseidon2 4-ary | sparse Merkle, depth 16 | Yes — primary circuit form |
| BLAKE3 4-ary tree | `commit/src/merkle.rs` (`MerkleTree`) | BLAKE3 | sparse Merkle, depth 16 | No |
| Nullifier set Merkle tree | `cell/src/nullifier_set.rs:31` | BLAKE3 sibling-path | sparse Merkle | No |

### 1.3 Turn execution / receipts / obligations

| Commitment | Location | Domain | Shape | Has circuit form? |
| --- | --- | --- | --- | --- |
| Turn hash | `turn/src/turn.rs:133` (`Turn::hash`) | BLAKE3 plain (no derive_key) | flat hash over actions+meta | No |
| Turn receipt hash | `turn/src/turn.rs:303` (`TurnReceipt::receipt_hash`) | BLAKE3 plain | hash chain via `previous_receipt_hash` | No |
| Effects hash | `turn/src/executor.rs:1606`, `executor.rs:1615` (`hash_tree_effects`) | BLAKE3 plain | DFS tree hash | Effect VM has a parallel `effects_hash` in PI computed from Poseidon2; **not bound** to BLAKE3 form |
| Forest hash | `turn/src/forest.rs` (referenced in `TurnReceipt.forest_hash`) | BLAKE3 | flat hash | No |
| Proof obligation id | `turn/src/obligation.rs:202` | BLAKE3 derive_key `"dregg-obligation-id-v1"` | flat hash | No |
| Proof obligation hash | `turn/src/obligation.rs:161` | BLAKE3 derive_key `"dregg-proof-obligation-v1"` | flat hash | No |
| Conditional turn hash | `turn/src/conditional.rs:106` | BLAKE3 derive_key `"dregg-conditional-turn-v1"` | flat hash | No |
| Proof nullifier (conditional) | `turn/src/conditional.rs:229` | BLAKE3 derive_key `"dregg-proof-nullifier-v1"` | flat hash | No |
| Conflict-set bloom commitment | `turn/src/conflict.rs:108` | BLAKE3 plain (versioned tag in body) | flat hash over bloom bytes | No |

### 1.4 Wire and bridge

| Commitment | Location | Domain | Shape | Has circuit form? |
| --- | --- | --- | --- | --- |
| Bridge receipt signing-message | `cell/src/note_bridge.rs:383` | BLAKE3 derive_key `"dregg-bridge-receipt-v1"` | flat hash | No |
| Wire authorization-request hash | `wire/src/message.rs:67` | BLAKE3 derive_key | flat hash | No |
| Federation root genesis | `wire/src/server.rs:472` | BLAKE3 plain | constant | No |
| Revocation root | `wire/src/server.rs:536` | BLAKE3 derive_key `"dregg-wire revocation-root v1"` | hash over set | Partial — `circuit/src/non_membership.rs` uses a Poseidon2 polynomial accumulator; the two roots are tracked separately |
| Peer-auth signing message | `wire/src/server.rs:869` | BLAKE3 derive_key `"dregg-wire peer-auth v1"` | flat hash | No |

### 1.5 Capabilities, sealing, delegation

| Commitment | Location | Domain | Shape | Has circuit form? |
| --- | --- | --- | --- | --- |
| Sealed-capability commitment | `cell/src/seal.rs:250` (`SealedCapability::compute_commitment`) | BLAKE3 derive_key `"dregg-seal commitment v2"` | flat hash | No |
| Macaroon caveat-chain hash | `macaroon/src/lib.rs:518` (`caveat_chain_hash`) | BLAKE3 derive_key `"dregg-proof-key-v1"` | hash chain over caveats | No |
| Macaroon proof-key derivation | `macaroon/src/lib.rs:434` | BLAKE3 KDF | derive_key | No |
| Macaroon envelope hash | `macaroon/src/lib.rs:761` (`envelope_hash`) | BLAKE3 | flat hash | No |
| Committed threshold (privacy) | `macaroon/src/lib.rs:170` | Poseidon2 | flat hash over `(threshold, blinding)` | Yes — used only in circuit |
| Capability slot fact-hash | `turn/src/executor.rs:1406` | BLAKE3 plain over `slot.to_le_bytes()` | flat hash | No |

### 1.6 Storage / queues

| Commitment | Location | Domain | Shape | Has circuit form? |
| --- | --- | --- | --- | --- |
| Blinded queue item commitment | `storage/src/blinded.rs:331` | BLAKE3 plain `"blinded-queue-commitment" ‖ item ‖ randomness` | flat hash | No — the docstring at line 329 explicitly says "in a real system this would use Poseidon2" |
| Blinded queue Merkle root | `storage/src/blinded.rs:374` | BLAKE3 binary tree | dense binary Merkle | No |
| Blinded queue nullifier | `storage/src/blinded.rs:345` | BLAKE3 plain | flat hash | No |
| Queue program vk_hash | `turn/src/queue_programs.rs:275` | BLAKE3 plain over name | flat hash | The circuit absorbs `validation_hash: BabyBear` (`queue_programs.rs:82`), an entirely different scheme |

### 1.7 Polynomial accumulators (already field-native)

| Commitment | Location | Domain | Shape |
| --- | --- | --- | --- |
| Revocation accumulator | `commit/src/accumulator.rs::PolynomialAccumulator` | BabyBear^4 | product `Π (α − h_i)` |
| Capability fact set | `commit/src/factset.rs` | BLAKE3 4-ary Merkle | sparse Merkle |
| Algebraic fact set | `commit/src/poseidon2_tree.rs::Poseidon2MerkleTree` | Poseidon2 4-ary | sparse Merkle |

### 1.8 Patterns and pathologies

Reading the inventory across the codebase, four patterns recur:

1. **Both forms exist but are not type-coupled.** Notes are the cleanest
   example — `Note::commitment()` and `Note::poseidon2_commitment()` both
   exist and are documented as the BLAKE3 and Poseidon2 forms of the same
   underlying note. But the return types are unrelated (`NoteCommitment` vs
   `BabyBear`) and there is nothing in the Rust type system that asserts
   the two were derived from the same preimage. A caller can pass the
   BLAKE3 form of note A as the "id" for the Poseidon2 form of note B.

2. **Subset commitments masquerading as state commitments.** The cell
   crate's audit P0-2 (see the module doc in `cell/src/commitment.rs:1`)
   documents the exact pathology: three different "state commitments" each
   covered a different subset of cell state, and a sovereign cell's
   circuit-side identity had no binding to its permissions or VK. The
   canonical commitment fixed the BLAKE3 side but the circuit side
   (`circuit/src/effect_vm.rs:684`) still only hashes
   `(balance, nonce, fields, cap_root)` and the binding referenced at
   `cell/src/commitment.rs:38` ("REVIEW[circuit-fix-coordination]") was
   never closed.

3. **Ad-hoc BLAKE3 with implicit domain separation.** `Turn::hash`,
   `TurnReceipt::receipt_hash`, and the various `hash_tree_effects` helpers
   use plain `blake3::Hasher::new()` and embed an in-body version tag
   (e.g., `b"dregg-receipt-v2"`). This works but is inconsistent with the
   rest of the codebase, which uses `new_derive_key("dregg-X v1")`. There
   is no central registry of domain tags.

4. **Storage-layer hashes destined to be replaced.** `storage/src/blinded.rs`
   contains TODO-shaped docstrings explicitly admitting that the BLAKE3
   commitments will become Poseidon2 in a "real system". Right now
   third-party verifiers cannot prove anything about blinded queue items
   because the commitment scheme is not in the field.

The framework below addresses all four.

---

## 2. The dual-accumulator pattern

### 2.1 Two hashes, one preimage

Every commitment in the framework has the same shape:

```
preimage  :=  canonical_bytes(T)        ← the bytes-level source of truth
blake3    :=  BLAKE3-derive_key(tag_T, canonical_bytes(T))
poseidon2 :=  Poseidon2.hash(felts_T)   where felts_T = encode_to_field(canonical_bytes(T))
```

`encode_to_field` is a fixed, public, deterministic bijection from a length-
prefixed byte string to a `Vec<BabyBear>`. The same canonical bytes feed both
sides; the two hashes are independently computed. There is **no
recompute-BLAKE3-inside-a-STARK** step.

### 2.2 Why a one-directional binding

BLAKE3 inside a STARK is prohibitively expensive: it uses a 64-byte state,
32-bit rotations, and a compression function with seven rounds of additions
and XORs. Estimates from public proofs of similar primitives (SHA-256,
BLAKE2s) put the AIR cost at hundreds of thousands of constraints per
compression block. We will not pay this cost.

Instead the binding is **established by ceremony at trusted boundaries** and
**proved in-circuit only on the Poseidon2 side**:

- The **cclerk** (or any producer of a sealed commitment) computes both
  digests from the same canonical preimage and packages them together.
  This is the only place the cross-binding is asserted; thereafter, code
  that consumes a `Commitment<T>` trusts the producer to have done this
  honestly. The honesty is enforced by the producer's signature over the
  whole structure (the cclerk signs `(blake3, poseidon2, …)` so a malicious
  producer who forged a mismatched pair would be liable).
- The **circuit** only proves statements about the Poseidon2 form. The
  BLAKE3 form is a side-channel that the verifier may hash-check
  independently if they happen to know the preimage, but no AIR ever
  asserts `blake3 = BLAKE3(preimage)`.
- The **out-of-circuit verifier** independently checks the BLAKE3 form
  (cheap, native CPU) and trusts the Poseidon2 form via the STARK.

The framework's invariant is therefore: **for any honestly produced
`Commitment<T>`, both forms commit to the same canonical bytes; for an
adversarially produced commitment, the two forms commit to (possibly)
different bytes, but the STARK proves only what the Poseidon2 form says
and the network proves only what the BLAKE3 form says.** Cross-form
divergence is detectable only by a third party who knows the preimage or
who watches the producer's signature.

### 2.3 The bytes ↔ felts encoding

`encode_to_field(bytes: &[u8]) -> Vec<BabyBear>` packs bytes into BabyBear
elements at 30 bits per limb, little-endian, with a four-byte length prefix
absorbed first. The 30-bit width matches the trick used at
`cell/src/commitment.rs:304` (`canonical_to_babybear_pi`): BabyBear's
modulus is 2³¹ − 2²⁷ + 1, and 30-bit limbs guarantee a unique
encoding without modular reduction collisions. We absorb 30 bits of
preimage per felt → ≈ 3.75 bytes per BabyBear element.

For fixed-shape preimages we DON'T use this byte-packing — instead each
field of `T` becomes its own felt (or short sequence of felts) following a
schema named in `T::poseidon2_schema()`. The byte-packing path is the
**fallback** for variable-length preimages where the schema would be
unwieldy (e.g., turn-tree effect hashes).

The two paths give two flavors of `Commitment<T>`:

- **Schema-encoded** (preferred). `T` provides a `to_felts() -> Vec<BabyBear>`
  method that emits a fixed-arity, type-aware encoding. Notes already do
  this: `(owner_lo, value, asset_type, creation_nonce_lo, randomness_lo)`.
  Schema-encoded commitments are efficient in-circuit because the AIR can
  recompute them from witness columns of known shape.
- **Bytes-packed** (fallback). `T` provides only `canonical_bytes() ->
  Vec<u8>`; the framework runs `encode_to_field(canonical_bytes)` for the
  Poseidon2 side. Useful for opaque containers like receipts or tree-shaped
  effect logs.

A `T` MAY provide both. The schema form is then the in-circuit "structured"
view and the bytes form is the "I already have a [u8;32], please give me a
field element" view (today this is `commit/src/poseidon2_tree.rs::commitment_to_field`,
line 320).

### 2.4 Domain separation

A central `commit/src/domain.rs` module will export every domain tag used
across the codebase as a `const &str`:

```rust
pub const TAG_CELL_STATE:        &str = "dregg-cell:state v2";
pub const TAG_CAPABILITY_ROOT:   &str = "dregg-cell:cap-root v2";
pub const TAG_NOTE_COMMITMENT:   &str = "dregg-note:commitment v2";
pub const TAG_NOTE_NULLIFIER:    &str = "dregg-note:nullifier v2";
pub const TAG_TURN:              &str = "dregg-turn:turn v2";
pub const TAG_RECEIPT:           &str = "dregg-turn:receipt v2";
pub const TAG_OBLIGATION:        &str = "dregg-turn:obligation v2";
pub const TAG_BRIDGE_RECEIPT:    &str = "dregg-bridge:receipt v2";
// …
```

The BLAKE3 form uses `blake3::Hasher::new_derive_key(TAG_T)`. The
Poseidon2 form mirrors the same separation by prepending
`Poseidon2.absorb(BabyBear::new(tag_hash(TAG_T)))` where `tag_hash` is a
deterministic, fixed 31-bit hash of the tag string. The same tag therefore
appears on both sides — when we bump `v2 → v3` we invalidate both forms
together.

---

## 3. The `Commitment<T>` framework

### 3.1 Core type

```rust
// commit/src/typed.rs (new)

use core::marker::PhantomData;
use dregg_circuit::field::BabyBear;

/// A typed dual-form commitment.
///
/// `T` is a zero-sized marker; the commitment binds bytes of the corresponding
/// canonical encoding to two independent hashes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Commitment<T: CommitmentSchema> {
    pub blake3:    [u8; 32],
    pub poseidon2: BabyBear,        // sponge squeeze, one felt
    _phantom:      PhantomData<fn() -> T>,
}

/// Implemented by every value that has a commitment.
///
/// `Canonical` is a self-describing byte encoding (tagged + length-prefixed)
/// and `to_felts` produces the field-element view consumed by the circuit.
pub trait CommitmentSchema: Sized + 'static {
    type Canonical: AsRef<[u8]>;
    fn canonical(&self) -> Self::Canonical;
    fn to_felts(&self) -> Vec<BabyBear>;
    const DOMAIN: &'static str;            // central registry
}

impl<T: CommitmentSchema> Commitment<T> {
    pub fn seal(value: &T) -> Self {
        let bytes = value.canonical();
        let blake3 = blake3_with_tag(T::DOMAIN, bytes.as_ref());
        let poseidon2 = poseidon2_with_tag(T::DOMAIN, &value.to_felts());
        Self { blake3, poseidon2, _phantom: PhantomData }
    }

    pub fn verify_blake3(&self, preimage_bytes: &[u8]) -> bool {
        blake3_with_tag(T::DOMAIN, preimage_bytes) == self.blake3
    }

    /// In-circuit witness handle: the producer also hands the verifier the
    /// felts they hashed. The verifier recomputes the Poseidon2 inside the
    /// AIR and checks equality against `self.poseidon2` published as a PI.
    pub fn in_circuit_pi(&self) -> BabyBear { self.poseidon2 }
}
```

A single Poseidon2 felt (~31 bits) is **not enough** for 128-bit security
on its own. Implementations that need 124-bit collision resistance squeeze
**four** BabyBear felts from the sponge (matching the BabyBear^4 quartic
extension used elsewhere in `commit/src/accumulator.rs`). The framework
provides both:

```rust
pub struct Commitment<T> { blake3: [u8; 32], poseidon2: BabyBear, … }
pub struct Commitment4<T> { blake3: [u8; 32], poseidon2: [BabyBear; 4], … }
```

`Commitment<T>` is used where the Poseidon2 form is a binding inside a
larger algebraic structure that itself has 124-bit security (e.g., a
sparse Merkle leaf where the root carries the security). `Commitment4<T>`
is used where the Poseidon2 form stands alone as an authoritative
identifier (e.g., a note commitment that is its own primary key).

### 3.2 Phantom markers

```rust
pub enum CellStateMarker {}
pub enum CapabilitySetMarker {}
pub enum NoteMarker {}
pub enum NoteNullifierMarker {}
pub enum TurnMarker {}
pub enum ReceiptMarker {}
pub enum ObligationMarker {}
pub enum BridgeReceiptMarker {}
pub enum QueueStateMarker {}
pub enum ConflictSetMarker {}
pub enum DelegationMarker {}
// …

pub type CellStateCommitment   = Commitment4<CellStateMarker>;
pub type NoteCommitment        = Commitment4<NoteMarker>;
pub type ReceiptCommitment     = Commitment4<ReceiptMarker>;
pub type ObligationCommitment  = Commitment<ObligationMarker>;
// …
```

A `NoteCommitment` cannot accidentally be passed where a `ReceiptCommitment`
is expected — the phantom marker prevents it at compile time.

### 3.3 Accumulator variants

`Commitment<T>` covers single-value commitments. For aggregates, two further
types layer on top:

```rust
/// A streaming hash-chain accumulator. Each `extend(item)` updates both
/// the BLAKE3 chain and the Poseidon2 sponge state in lock-step.
pub struct Accumulator<T: CommitmentSchema> {
    blake3_state:    blake3::Hasher,
    poseidon2_state: Poseidon2Sponge,
    n_items:         u64,
    _phantom:        PhantomData<fn() -> T>,
}

impl<T: CommitmentSchema> Accumulator<T> {
    pub fn new() -> Self { /* domain-separated init */ }
    pub fn extend(&mut self, item: &T) { /* absorb both sides */ }
    pub fn finalize(self) -> Commitment4<Vec<T>> { /* squeeze both sides */ }
}

/// A sparse 4-ary Merkle root, dual-hashed. The Poseidon2 tree
/// (`commit/src/poseidon2_tree.rs`) is the in-circuit form; the BLAKE3 tree
/// (`commit/src/merkle.rs`) is the out-of-circuit form. The MerkleRoot
/// carries both roots and a one-way binding `commitment_to_field`.
pub struct MerkleRoot<T: CommitmentSchema> {
    pub blake3_root:    [u8; 32],
    pub poseidon2_root: BabyBear,
    _phantom:           PhantomData<fn() -> T>,
}
```

A Merkle path proof similarly carries both BLAKE3 siblings and Poseidon2
siblings; verifiers select the form appropriate to their context.

### 3.4 What's NOT in the framework

We deliberately leave outside the framework:

- **Bare BLAKE3 hashes that don't carry authority.** E.g., the conflict-set
  bloom filter (`turn/src/conflict.rs`) — it's a probabilistic dedup
  filter, not a commitment to anything. Stays as bare BLAKE3.
- **KDFs (`derive_key`).** Macaroon proof-key derivation
  (`macaroon/src/lib.rs:434`) is a KDF, not a commitment. Stays as is.
- **Ed25519 / Schnorr signing messages.** Signatures are over BLAKE3
  digests of structured data; the signing-message hash function does not
  need a circuit form unless we want to verify the signature inside a
  STARK (we don't; we use `native_signature_air` for in-circuit signing).

---

## 4. In-circuit / out-of-circuit boundary

```
                       cclerk / executor
                        produces both forms
                              │
       ┌──────────────────────┴─────────────────────┐
       │                                            │
       ▼                                            ▼
  BLAKE3 form                                Poseidon2 form
  [u8; 32]                                   [BabyBear; 4]
       │                                            │
       │ used by                                    │ used by
       ▼                                            ▼
  ─ HashMap keys                              ─ AIR public inputs
  ─ storage indexes                           ─ trace state columns
  ─ wire serialization                        ─ transition constraints
  ─ gossip dedup                              ─ lookup arguments
  ─ Ed25519 signing messages                  ─ recursion (IVC)
  ─ ledger Merkle leaves (federation tree)    ─ inside STARK proofs
  ─ cclerk REST API                           ─ inside SNARK proofs (Kimchi)
  ─ log lines, audit, debugging               ─ inside lookup tables
       │                                            │
       │                                            │
       └────────────── BOTH cross ──────────────────┘
                              │
                              ▼
                   Receipt / capability /
                   sovereign-cell registration
                   (a third party may verify
                    either or both forms)
```

The **boundary** is whoever first stamps a `Commitment<T>`. That party is
trusted (or signed-and-liable) to compute both forms from the same
preimage. Once stamped:

- An out-of-circuit verifier with the preimage may check the BLAKE3 form
  directly.
- An in-circuit verifier checks the Poseidon2 form via the STARK.
- A verifier without the preimage trusts whichever side the protocol step
  in front of them carries.

**No verifier ever attempts to cross-check the two forms against each other
without re-running the preimage through both hash functions.** Cross-form
attestation is established by the producer's signature over the
`Commitment<T>` struct (which contains both digests), not by a circuit.

### 4.1 Where the boundary is concretely

| Producer | What they stamp | How they prove honesty |
| --- | --- | --- |
| Cipherclerk (`sdk/src/cipherclerk.rs`) | `Commitment4<Note>` on note creation | Ed25519 signature over `(blake3, poseidon2, owner)` |
| Executor (`turn/src/executor.rs`) | `Commitment4<Receipt>` on turn commit | Executor signature already exists (`TurnReceipt.executor_signature`); extended to cover both forms |
| Cell program (sovereign) | `Commitment4<CellState>` post-transition | STARK proof commits to Poseidon2 form via PI; ledger entry commits to BLAKE3 form via canonical commitment |
| Federation bridge (`bridge/`) | `Commitment4<BridgeReceipt>` | Threshold signature from federation quorum |
| Queue program (`turn/src/queue_programs.rs`) | `Commitment<EnqueueValidation>` | Currently only Poseidon2; gains a BLAKE3 form for log/audit |

---

## 5. Receipt-shape commitments — the hard case

Receipts (turn, sovereign, federation, bridge) **must** carry both forms
because they cross trust boundaries. A receipt is:

- accepted into a hosted-cell's call forest (consumer cares about BLAKE3 —
  fast dedup, indexing, log search);
- referenced from a `ResolutionCondition::AwaitReceipt`
  (`turn/src/pending.rs:62`) which compares `turn_hash` byte-for-byte
  (BLAKE3);
- absorbed into a recursive proof when a federation aggregates receipts
  (Poseidon2 needed because the recursion is in BabyBear);
- presented to a remote federation in `bridge/src/present.rs` (both forms
  needed: BLAKE3 for the wrapper, Poseidon2 for the bridge AIR);
- chained: `previous_receipt_hash` is currently a BLAKE3 chain
  (`TurnReceipt.previous_receipt_hash`, line 261), but if we ever recursive-
  prove a receipt chain we need a Poseidon2 chain too.

### 5.1 Design for `Commitment4<Receipt>`

```rust
pub struct ReceiptCommitment {
    pub blake3:    [u8; 32],     // existing receipt_hash, unchanged shape
    pub poseidon2: [BabyBear; 4], // squeeze of the same canonical preimage
}

impl CommitmentSchema for TurnReceipt {
    type Canonical = Vec<u8>;
    const DOMAIN: &'static str = "dregg-turn:receipt v2";

    fn canonical(&self) -> Vec<u8> {
        // exactly the current bytes hashed by receipt_hash()
        // — turn_hash || forest_hash || pre_state || post_state || …
    }

    fn to_felts(&self) -> Vec<BabyBear> {
        // schema-encoded:
        //   [turn_hash_felts(8), forest_hash_felts(8), pre_state_felt(1),
        //    post_state_felt(1), timestamp(1), effects_hash_felts(8),
        //    computrons_used(1), action_count(1), agent_felts(8),
        //    federation_felts(8), prev_receipt_felts(8)?,
        //    routing_directives_felts(*), …]
    }
}
```

`turn_hash`, `forest_hash`, `effects_hash`, `federation_id`,
`previous_receipt_hash`, `agent` are each 32-byte values. Each splits into
8 BabyBear-shaped felts via the standard 30-bit packing. **State
commitments** (`pre_state_hash`, `post_state_hash`) — once they become
`Commitment4<CellState>` per §6 — contribute their Poseidon2 form directly
(4 felts) instead of being byte-packed; this is the leverage of the typed
framework, *each nested commitment in a receipt contributes its already-
computed Poseidon2 form rather than re-hashing the BLAKE3 bytes.*

### 5.2 Why this isn't double work

You might object: "the cclerk now has to run two hash functions." Yes —
**once, at production**. Thereafter the cheap form is used in every hot
path. For comparison, the current code already runs both functions in many
places (the canonical commitment is computed via `compute_canonical_state_commitment`
*and* the circuit independently computes a Poseidon2 state commitment); we
just don't memoize the pair into a single typed value, so the binding is
silently lost at the type level.

For receipts specifically, the Poseidon2 form lets us **aggregate** receipts
via IVC (`circuit/src/ivc.rs`): a recursive prover absorbs the Poseidon2
form of receipt N into the IVC state, proves it was correctly produced from
receipt N−1, and emits a single STARK that vouches for the whole chain.
Today this is impossible because the receipt chain is BLAKE3-only.

---

## 6. Migration plan — top 5 PI-touching commitments

These five touch the Effect VM public inputs and should migrate first
because they are where the circuit-side and the executor-side already meet
and currently desynchronize.

### 6.1 Cell state commitment

- **Current.** `compute_canonical_state_commitment` (BLAKE3, full state) in
  `cell/src/commitment.rs:100`; `CellState::compute_commitment` (Poseidon2,
  subset) in `circuit/src/effect_vm.rs:684`. Adapter
  `canonical_to_babybear_pi` exists (line 304) but is unused — the
  REVIEW[circuit-fix-coordination] note from the audit was never resolved.
- **Proposed.** `Commitment4<CellState>` produced by a single function that
  hashes the same canonical preimage twice. The Poseidon2 schema absorbs
  every field the BLAKE3 form already covers (identity, mode, permissions,
  VK, capability root, delegate, delegation snapshot, program, full
  `CellState` including visibility, commitments[8], proved_state,
  delegation_epoch). The effect VM's `compute_commitment` is replaced
  with a felt-encoding of this canonical scheme.
- **Estimated LOC.** ~400 in `cell/src/commitment.rs` (extend canonical to
  produce both forms), ~200 in `circuit/src/effect_vm.rs` (replace
  `compute_commitment`), ~150 of constraint-side changes in
  `circuit/src/effect_vm.rs` to absorb the new schema, ~100 of test
  updates. **~850 LOC total.** This is the biggest migration.

### 6.2 Note commitment

- **Current.** Already a dual-form prototype: `Note::commitment` (BLAKE3)
  and `Note::poseidon2_commitment` (Poseidon2) at `cell/src/note.rs:162`
  and `:229`. The two are independently derived from the same `Note`
  fields, but the Rust types (`NoteCommitment` vs `BabyBear`) don't
  enforce the binding.
- **Proposed.** Replace `NoteCommitment(pub [u8; 32])` with
  `pub struct NoteCommitment(pub Commitment4<NoteMarker>)`. The two
  existing `commitment()` and `poseidon2_commitment()` methods stay, now
  returning views into the typed value. Callers that index storage by
  BLAKE3 (`PendingBridgeSet`, nullifier sets) keep working; callers that
  pass into circuits use the `.poseidon2` accessor.
- **Estimated LOC.** ~100 in `cell/src/note.rs`, ~50 ripple in
  `note_bridge.rs`, ~50 in `cipherclerk.rs`. **~200 LOC.** Smallest of the five
  because the dual form already exists.

### 6.3 Note nullifier

- **Current.** `Note::nullifier` (BLAKE3) at `cell/src/note.rs:179`; the
  circuit's `note_spending_air.rs` computes a Poseidon2 nullifier from
  witness columns and exposes it as a PI; the two are **not** documented
  as bound to the same preimage.
- **Proposed.** `Commitment4<NoteNullifierMarker>` derived from
  `(note_commitment.poseidon2, spending_key_felts, creation_nonce_felts)`
  on the Poseidon2 side, mirroring the existing BLAKE3 derivation. Bind
  the bridge's `PendingBridge.nullifier` lookup table to the BLAKE3 form
  and the AIR's nullifier PI to the Poseidon2 form, with a producer
  signature over the pair.
- **Estimated LOC.** ~150 in `cell/src/note.rs` + `circuit/src/note_spending_air.rs`,
  ~50 in bridge/. **~200 LOC.**

### 6.4 Effects hash

- **Current.** `hash_tree_effects` in `turn/src/executor.rs:1615` produces
  a BLAKE3 hash by DFS over the call forest. The effect VM's PI
  `effects_hash` is a Poseidon2 sum-hash computed independently in
  `circuit/src/effect_vm.rs`. These are not bound.
- **Proposed.** Define `Commitment<EffectTreeMarker>` whose preimage is the
  canonical DFS traversal of `CallTree` (already serialized to bytes for
  the BLAKE3 form). The Poseidon2 form is a schema encoding: for each
  effect, absorb its tag felt and its operand felts. Bytes form drives
  receipt chaining; Poseidon2 form drives in-circuit verification of the
  AIR's per-row effect column.
- **Estimated LOC.** ~250 in `turn/src/executor.rs` + `circuit/src/effect_vm.rs`.
  **~250 LOC.**

### 6.5 Capability set root

- **Current.** `compute_canonical_capability_root` (BLAKE3, full
  CapabilityRefs) at `cell/src/commitment.rs:277`; the circuit's
  `capability_root: BabyBear` is currently *uncomputed in the cell crate*
  (audit P0-3 note) — the circuit just absorbs whatever felt the executor
  hands it, with no binding back to the BLAKE3 form.
- **Proposed.** `MerkleRoot<CapabilityRef>` carrying both a BLAKE3 4-ary
  root (using the existing `commit/src/merkle.rs` tree) and a Poseidon2
  4-ary root (using `commit/src/poseidon2_tree.rs`). On every cell mutation
  that changes capabilities, both roots are recomputed. The PI absorbs the
  Poseidon2 root; the federation Merkle leaf absorbs the BLAKE3 root.
- **Estimated LOC.** ~300 in `cell/src/commitment.rs` and
  `cell/src/capability.rs` (new dual-tree maintenance), ~50 in circuit.
  **~350 LOC.**

**Total for migration phase 1: ~1850 LOC.** Phase 2 (obligations, bridge
receipts, sealed capabilities, queue state) is roughly the same size and
should follow immediately so we never live in a "some are typed, some
aren't" state for long.

---

## 7. Open questions

1. **Squeeze width.** Should `Commitment4<T>` squeeze 4 felts (~124-bit
   security) or 5 (~155-bit) given that recursion may want a margin? My
   current pick is 4 to match the rest of the codebase but worth checking
   against the recursion plan.
2. **Hashing receipts in the IVC step.** If we move to recursive
   aggregation of receipts, the IVC step needs the Poseidon2 form of the
   *previous* receipt as a witness column. This implies receipts are
   produced *with* their Poseidon2 form even when no immediate use exists —
   we pay an unconditional Poseidon2 cost per turn. Estimated cost: ~30
   Poseidon2 calls per receipt, ~30 µs. Acceptable.
3. **Versioning across forms.** Bumping a domain tag invalidates both
   forms. Do we ever want to bump just one? I argue no — divergence is the
   pathology we're fixing.
4. **Cipherclerk API surface.** The cipherclerk's REST/JSON layer
   (`sdk/src/client.rs`, `sdk-ts/`) currently exposes BLAKE3 hashes as hex
   strings. Should it also expose Poseidon2 forms? Probably yes, as a
   second hex string in every commitment-bearing response, so that a
   browser-side prover can construct an IVC step without round-tripping
   through the cclerk.
5. **Migration order vs. soft fork.** A bump from `v1` tags to `v2` is a
   hard invalidation. We need a migration window where the executor accepts
   both, OR we time the migration with another planned consensus break.

---

## 8. Summary

The current commitment landscape is two parallel hash universes that
silently coexist, with a few ad-hoc bridges (`commitment_to_field`,
`canonical_to_babybear_pi`) and several documented gaps (audit P0-2,
P0-3, REVIEW[circuit-fix-coordination]). The dual-accumulator framework
makes both universes first-class, types the binding, names the boundary,
and refuses to verify BLAKE3 inside a STARK. Notes are the existing
prototype; receipts are the high-value next target; cell state is the
biggest migration. After phase 1 (~1850 LOC) the Effect VM PI is fully
typed and the federation can begin recursive aggregation of receipts.

Two hashes, one preimage, one type, one boundary. That's the shape.
