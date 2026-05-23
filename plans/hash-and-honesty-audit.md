# Hash and Honesty Security Audit

Security audit of blake3/Poseidon2 usage, 32-bit collision risks, and executor trust elimination.

---

## Part 1: blake3 vs Poseidon2 Audit

### Summary of Hash Architecture

The system uses a dual-commitment model:
- **Poseidon2**: SNARK-friendly algebraic hash (BabyBear field), used in-circuit for state commitments, Merkle membership, fact hashing
- **blake3**: Fast 256-bit hash, used out-of-circuit for content addressing, Fiat-Shamir, wire protocol, domain separation

### CRITICAL: blake3 in Circuit Crate (Misuse Candidates)

#### 1. STARK Fiat-Shamir Transcript -- CORRECT

**File:** `circuit/src/stark.rs:412-465`  
**Usage:** blake3 for Fiat-Shamir transcript (challenge generation, Merkle tree for FRI commitments)  
**Verdict:** CORRECT. This is the standard construction -- blake3 is used for the OUTER STARK prover/verifier protocol (Merkle tree over evaluation domain, challenge derivation). This is NOT proven in-circuit; the STARK verifier runs the same transcript natively. No issue.

#### 2. STARK Merkle Tree (FRI) -- CORRECT

**File:** `circuit/src/stark.rs:314-336` (hash_leaf, hash_leaf_multi, hash_node)  
**Usage:** blake3 for the prover's Merkle tree over polynomial evaluations  
**Verdict:** CORRECT. This is the proof envelope (Reed-Solomon codeword commitment). The verifier recomputes these hashes natively. Not proven in-circuit.

#### 3. IVC Trace Commitment -- CORRECT (with caveat)

**File:** `circuit/src/ivc.rs:913-945, 980-985, 1051-1059, 1063-1068`  
**Usage:** blake3 for `trace_commitment` (accumulating commitment to IVC trace data) and `compute_ivc_digest` (binding IVC public data)  
**Verdict:** CORRECT. These are out-of-band binding commitments. The trace_commitment is part of the proof metadata, not a public input to the IVC STARK itself. The IVC STARK's public inputs are `[initial_root, final_root, step_count, accumulated_hash]` -- all Poseidon2.  
**Caveat:** If `trace_commitment` is ever moved INTO the IVC AIR as a constraint, it would need to be Poseidon2. Currently it's verified by the application layer (executor checks consistency).

#### 4. Binius Backend -- blake3 IN-CIRCUIT -- ARCHITECTURE SPECIFIC

**File:** `circuit/src/backends/binius.rs:133-653`  
**Usage:** Full blake3 compression function implemented as binius constraints  
**Verdict:** CORRECT for binius. Binius operates over binary fields (GF(2^n)) where blake3 IS efficient (~200 constraints vs ~250,000 in BabyBear). This is the binary-field-specific backend and is NOT used with BabyBear STARKs.

#### 5. Mina Backend Transcript -- CORRECT

**Files:** `circuit/src/backends/mina/standalone.rs:90,245,858,867`, `circuit/src/backends/mina/pickles.rs:576,585`  
**Usage:** blake3 for Fiat-Shamir in the Mina bridge  
**Verdict:** CORRECT. Same as #1 -- outer protocol transcript, not in-circuit.

#### 6. Schnorr Signature Key Derivation -- CORRECT

**File:** `circuit/src/schnorr_sig.rs:79,110,184`  
**Usage:** blake3 for key derivation (`derive_key`) and message hashing before encoding to field  
**Verdict:** CORRECT. The blake3 hash is immediately converted to 8 BabyBear elements via `encode_hash` (line 185) before use in-circuit. The circuit verifies the Schnorr equation over field elements. blake3 serves only as the pre-processing step (domain separation, deterministic nonces).

#### 7. Non-Membership SetIdentifier -- PROBLEM (low severity)

**File:** `circuit/src/non_membership.rs:59-63`
```rust
let name_hash = blake3::hash(name.as_bytes());
let domain_sep = BabyBear::new(
    u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]) % BABYBEAR_P,
);
```
**Verdict:** LOW RISK. The domain separator derived from blake3 is used as a public input to distinguish different non-membership sets. It's a SINGLE BabyBear element (31 bits) from a blake3 hash. Two different set names could collide (2^31 space). However, set names are chosen by honest operators, not adversaries. An adversary cannot force a victim to use a colliding set name.

**Recommendation:** Use `poseidon2::hash_many(&BabyBear::encode_hash(...))` for consistency, or accept the 31-bit separation as sufficient for domain tags.

#### 8. Predicate Program Attribute Hash -- MIXED (safe but inconsistent)

**File:** `circuit/src/predicate_program.rs:1877-1880`
```rust
let attr_bytes = blake3::hash(attribute.as_bytes());
let attr_bb = poseidon2::hash_many(&BabyBear::encode_hash(attr_bytes.as_bytes()));
```
**Verdict:** SAFE. blake3 is used for domain separation THEN immediately fed into Poseidon2 for the actual in-circuit hash. The Poseidon2 output is what appears in proofs. blake3 just provides the initial 256-bit expansion. This is the correct pattern.

#### 9. Binding Module -- CORRECT

**File:** `circuit/src/binding.rs:61,163,171,238`  
**Usage:** blake3 keyed hash for action binding / presentation tags, then `encode_hash` to field elements  
**Verdict:** CORRECT. The binding commitment uses blake3 for the out-of-circuit binding tag, which is then encoded as 8 BabyBear elements (248 bits) for the ActionBinding type. This is used as a public input but with FULL multi-element representation.

### CRITICAL: blake3 in Turn Crate

#### 10. Executor hash_to_bb -- PROBLEM (HIGH SEVERITY)

**File:** `turn/src/executor.rs:843-846`
```rust
fn hash_to_bb(h: &[u8; 32]) -> BabyBear {
    let val_u32 = u32::from_le_bytes([h[0], h[1], h[2], h[3]]);
    BabyBear::new(val_u32 % BABYBEAR_P)
}
```
**Usage:** Converts blake3 hashes of nullifiers, commitments, capabilities, obligation_ids, beneficiary hashes into SINGLE BabyBear elements for the Effect VM trace.

**Affected values (all become single-element IDs in-circuit):**
- `NoteSpend { nullifier: hash_to_bb(&nullifier.0) }` (line 884)
- `NoteCreate { commitment: hash_to_bb(&commitment.0) }` (line 892)
- `GrantCapability { cap_entry: hash_to_bb(cap_hash.as_bytes()) }` (line 877)
- `CreateObligation { obligation_id: hash_to_bb(...), beneficiary_hash: hash_to_bb(...) }` (lines 638-639)
- `FulfillObligation { obligation_id: hash_to_bb(obligation_id) }` (line 644)
- `SlashObligation { obligation_id: hash_to_bb(obligation_id) }` (line 650)

**Verdict:** HIGH SEVERITY. These are security-relevant identifiers proven in-circuit with only 31 bits of collision resistance. See Part 2 for full analysis.

#### 11. Executor Custom Proof Hash -- MODERATE

**File:** `turn/src/executor.rs:779-785`
```rust
fn hash_custom_proof(proof_bytes: &[u8]) -> [u8; 16] {
    let h = blake3::hash(proof_bytes);
    let bytes = h.as_bytes();
    let mut result = [0u8; 16];
    result.copy_from_slice(&bytes[..16]);
    result
}
```
**Verdict:** Uses blake3 to hash custom proof bytes, then takes 16 bytes (128 bits). This maps to 4 BabyBear elements (4 * 31 = 124 bits). Adequate for binding, but uses blake3 where the in-circuit verification could benefit from Poseidon2 consistency.

#### 12. Conditional/Obligation Hashing -- CORRECT (out-of-circuit)

**Files:** `turn/src/conditional.rs:106,229,267`, `turn/src/obligation.rs:163,203`  
**Usage:** blake3 for conditional turn hashes, proof nullifier computation, obligation IDs  
**Verdict:** CORRECT. These hashes are used for GOSSIP-LAYER identification and double-spend detection in the executor. They are NOT proven in-circuit (the executor checks them imperatively).

**Exception:** When obligation IDs are ALSO used in-circuit (via hash_to_bb), there's a consistency issue. The 32-byte blake3 obligation_id gets truncated to 31 bits for the Effect VM. See item #10.

#### 13. Turn/Forest/Routing Hashing -- CORRECT (out-of-circuit)

**Files:** `turn/src/turn.rs:135,304`, `turn/src/forest.rs:87,99,171,188,201,207`, `turn/src/routing.rs:28`  
**Usage:** blake3 for turn identification, call tree hashing, routing table  
**Verdict:** CORRECT. Purely out-of-circuit identification. Never proven.

### CRITICAL: blake3 in Cell Crate

#### 14. Cell::state_commitment() -- DUAL SYSTEM (working correctly)

**File:** `cell/src/cell.rs:239-280`
```rust
pub fn state_commitment(&self) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-cell-state-v1");
    // ... hashes id, public_key, token_id, state fields, capabilities, permissions
}
```
**Verdict:** This is the STORAGE-LAYER commitment (32 bytes, blake3). It is used for sovereign cell storage in the federation ledger.

The CIRCUIT-LAYER commitment is `CellState::compute_commitment()` in `circuit/src/effect_vm.rs:499-509` which uses `hash_4_to_1` (Poseidon2).

These are DIFFERENT commitments serving different purposes:
- blake3 `state_commitment()`: stored by federation, verified by sovereign cell witness submission
- Poseidon2 `state_commitment`: used as public input PI[0]/PI[1] in Effect VM STARK

The executor reconciles these: `commitment_to_babybear()` reads the stored [u8; 32] where the first 4 bytes encode the Poseidon2 BabyBear value. This means:

**The stored commitment IS the Poseidon2 value** (packed into [u8; 32] with zero padding). The blake3 `Cell::state_commitment()` is used only for the NON-sovereign (hosted) cell path. Sovereign cells store the Poseidon2 commitment directly.

This is confirmed at `turn/src/tests.rs:7224-7233`:
```rust
let vm_state = pyana_circuit::CellState::new(balance, nonce);
let commitment = TurnExecutor::babybear_to_commitment(vm_state.state_commitment);
```

**Verdict:** CORRECT but confusing dual system. No security issue.

#### 15. Note::commitment() vs Note::poseidon2_commitment() -- DUAL SYSTEM

**File:** `cell/src/note.rs:162-170` (blake3) vs `cell/src/note.rs:229-254` (Poseidon2)  
**Verdict:** CORRECT dual system. The blake3 commitment is for storage/gossip. The Poseidon2 commitment is for proving in the NoteSpendingAir. However, see Part 2 for the `poseidon2_commitment()` truncation issue.

### SDK/Apps blake3 Usage -- CORRECT (out-of-circuit)

**Files:** `sdk/src/client.rs:471`, `sdk/src/runtime.rs:116,417`, `sdk/src/full_turn_proof.rs:393,717`, `sdk/src/embed.rs:324,516,539`  
**Verdict:** All correct. Token ID derivation, domain hashing, proof serialization integrity, state snapshot integrity. None are proven in-circuit.

---

## Part 2: 32-bit Collision Risk Audit

### BabyBear Basics

- Field prime: p = 2^31 - 1 = 2,147,483,647
- Single element: ~31 bits of entropy
- Birthday bound: collision expected at ~2^15.5 = ~46,340 elements
- For security-relevant identifiers, 31 bits is CATASTROPHICALLY insufficient

### CRITICAL: Single-Element Identifiers in Effect VM

The Effect VM uses single BabyBear elements for:

| Identifier | Source | In-Circuit Use | Collision Impact |
|---|---|---|---|
| `nullifier` | hash_to_bb(blake3) | NoteSpend effect | **CRITICAL**: Two notes with same 31-bit nullifier = double spend undetectable |
| `commitment` | hash_to_bb(blake3) | NoteCreate effect | **HIGH**: Commitment collision = note fungibility attack |
| `cap_entry` | hash_to_bb(blake3(slot)) | GrantCapability | **MODERATE**: Capability confusion |
| `obligation_id` | hash_to_bb(blake3) | Create/Fulfill/Slash | **HIGH**: Obligation confusion = stake theft |
| `beneficiary_hash` | hash_to_bb(blake3) | CreateObligation/Slash | **HIGH**: Beneficiary confusion = stake misdirection |
| `cell_id` (ExportSturdyRef) | BabyBear | Identity binding | **CRITICAL**: Cell impersonation |
| `swiss_number` (EnlivenRef) | BabyBear | Reference validation | **HIGH**: Unauthorized access |
| `factory_vk` | BabyBear | Provenance | **MODERATE**: Factory confusion |

#### Attack Scenario: Nullifier Collision

With ~46,340 notes created, birthday paradox gives 50% chance of a nullifier collision in the 31-bit space. An adversary with a moderate-sized wallet could:
1. Create many notes, recording their blake3 nullifiers
2. Find two notes whose blake3 nullifiers share the same first 4 bytes (mod p)
3. Spend note A (nullifier recorded in-circuit as BabyBear X)
4. Claim note B's nullifier is also BabyBear X (hash_to_bb collision)
5. The in-circuit check cannot distinguish them

**Severity:** CRITICAL for high-value deployments. At 2^31 space, an adversary needs only 2^16 attempts (seconds of computation) to find a useful collision.

#### Attack Scenario: Obligation ID Collision

1. Create obligation A with hash_to_bb(id_A) = some BabyBear value V
2. Find or create obligation B with hash_to_bb(id_B) = V (same first 4 bytes mod p)
3. Fulfill obligation B using obligation A's ID in the circuit (they map to same V)
4. The Effect VM constraint `obligation_id == V` is satisfied for both

### CRITICAL: Orderbook Self-Trade Check

**File:** `apps/orderbook/src/circuit.rs:550-558`
```rust
fn id_hash_to_field(hash: &[u8; 32]) -> BabyBear {
    let truncated = u32::from_le_bytes([hash[0], hash[1], hash[2], hash[3]]);
    BabyBear::new(truncated % BABYBEAR_P)
}
```

The self-trade prevention check (`maker_id_elem != taker_id_elem`) uses a SINGLE BabyBear element per identity.

**Attack:** Two distinct users whose blake3 ID hashes share the same first 4 bytes (mod p) would be treated as the "same" user, preventing legitimate trades between them. Conversely, a wash trader could use two IDs that happen to differ in first-4-bytes but represent the same entity.

**The code acknowledges this:** "a 1-in-2^31 collision probability is negligible" -- but this is WRONG for the attack model. The adversary can generate IDs freely and test until they find a collision. Cost: ~2^16 iterations (trivial).

**Severity:** MODERATE. Not a fund-loss bug, but breaks the economic guarantee (self-trade prevention is cosmetic if collisions are cheap).

### MODERATE: Note poseidon2_commitment() Truncation

**File:** `cell/src/note.rs:233-238`
```rust
let owner = BabyBear::new_canonical(u32::from_le_bytes([
    self.owner[0], self.owner[1], self.owner[2], self.owner[3],
]));
```

The `poseidon2_commitment()` uses only the FIRST 4 BYTES of the 32-byte owner field. This gives 31 bits of owner binding in the commitment.

**Impact:** Two different owners whose public keys share the first 4 bytes (mod p) would have the same Poseidon2 note commitment. An adversary could claim ownership of someone else's note.

**However:** The NoteSpendingAir uses 8 BabyBear limbs for the spending KEY (248 bits, line 124-130), so actual spending requires the full key. The commitment collision alone doesn't enable theft -- but it DOES break the uniqueness of commitments in the note tree, potentially enabling confusion attacks.

**Severity:** MODERATE. The spending proof uses full key width, but commitment collisions could cause accounting confusion.

### GOOD: Patterns That Correctly Use Multi-Element Encoding

| Pattern | Width | Bits | Location |
|---|---|---|---|
| `BabyBear::encode_hash(&[u8; 32])` | 8 elements | ~248 bits | `circuit/src/field.rs:212` |
| `ActionBinding` | 4 elements | ~124 bits | `circuit/src/binding.rs` |
| `WideHash` (composition/revealed) | 4 elements | ~124 bits | presentation.rs |
| `spending_key` | 8 elements | ~248 bits | `circuit/src/note_spending_air.rs:130` |
| `program_vk_hash` | 4 elements | ~124 bits | `circuit/src/effect_vm.rs:357` |
| `proof_commitment` | 4 elements | ~124 bits | `circuit/src/effect_vm.rs:360` |
| `federation_root` encoding | 8 elements | ~248 bits | `sdk/src/privacy.rs:694` |
| Poseidon2MerkleTree leaves | 1 element | 31 bits | store/src/note_tree.rs |

### Required Fixes

**Priority 1 (CRITICAL):** Expand Effect VM identifiers to multi-element representation:

| Field | Current | Required | Constraint Cost |
|---|---|---|---|
| nullifier | 1 element | 4 elements (124 bits) | +3 columns, +3 boundary constraints |
| commitment | 1 element | 4 elements (124 bits) | +3 columns, +3 boundary constraints |
| obligation_id | 1 element | 4 elements (124 bits) | +3 columns per obligation effect |
| beneficiary_hash | 1 element | 4 elements (124 bits) | +3 columns per obligation effect |
| cap_entry | 1 element | 2 elements (62 bits) | +1 column (acceptable for capabilities) |

**Total trace widening:** ~20 additional columns for the Effect VM trace.

**Priority 2 (HIGH):** Fix `hash_to_bb` to `hash_to_bb4`:
```rust
fn hash_to_bb4(h: &[u8; 32]) -> [BabyBear; 4] {
    let mut result = [BabyBear::ZERO; 4];
    for i in 0..4 {
        let val = u32::from_le_bytes([h[i*4], h[i*4+1], h[i*4+2], h[i*4+3]]);
        result[i] = BabyBear::new(val % BABYBEAR_P);
    }
    result
}
```

**Priority 3 (MODERATE):** Fix `poseidon2_commitment()` owner encoding to use 8 limbs via `key_to_field_elements`, then commit with larger Poseidon2 sponge:
```rust
let owner_limbs = key_to_field_elements(&self.owner); // 8 elements
hash_many(&[owner_limbs..., value, asset_type, creation_nonce, randomness])
```

**Priority 4 (LOW):** Fix orderbook `id_hash_to_field` to use 4-element comparison. The self-trade check becomes 4 constraints (one per element) checking `maker_id[i] != taker_id[i]` for at least one i.

---

## Part 3: Executor Trust Elimination Roadmap

### Trust Assumption 1: Balance Limb Range (lo < 2^30, hi < 2^34)

**Current state:** Executor validates limbs at proof generation time (`circuit/src/effect_vm.rs:1781-1793`). NOT enforced in-circuit.

**In-circuit fix:** 16-bit lookup table range check.

```
balance_lo (30 bits) = lo_chunk_0 (15 bits) + lo_chunk_1 (15 bits) * 2^15
balance_hi (34 bits) = hi_chunk_0 (16 bits) + hi_chunk_1 (16 bits) + hi_bit (2 bits) * 2^32
```

Each chunk is checked against a 2^16 lookup table (log-derivative argument).

**Cost:**
- Lookup table: 65,536 rows (fixed, amortized across all proofs)
- Per debit row: 4 lookup queries (2 for lo, 2 for hi) = 4 additional logup columns
- Total: ~4 auxiliary columns + shared lookup table

**Implementation path:**
1. Add a `RangeCheckTable` AIR (static 2^16 table)
2. Use log-derivative (logup) bus to connect Effect VM rows to the table
3. Constrain: for every row, `lo_chunk_0 IN table AND lo_chunk_1 IN table` etc.
4. Remove executor-side check (it becomes redundant)

**Eliminates trust?** YES, fully. A malicious prover cannot use out-of-range limbs.

### Trust Assumption 2: Balance Underflow (amount <= balance)

**Current state:** Executor panics on underflow at proof generation (`circuit/src/effect_vm.rs:1836-1862`). The in-circuit defense relies on state commitment integrity (hash chain) catching wraparound indirectly.

**Residual risk:** The state commitment hash chain DOES catch inconsistency at boundaries, but on interior rows, a prover could temporarily use wrapped values. The net effect would be caught by boundary constraints ONLY IF the final balance is incorrect. A sophisticated attack: wrap on row 3, unwrap on row 5, end up with an inflated balance that still produces a "valid" commitment chain.

**Wait -- is this actually exploitable?** Let's trace:
- Row N: bal_lo = 100, amount = 200, new_bal_lo = 100 - 200 (mod p) = p - 100 = 2,147,483,547
- The constraint `new_bal_lo = old_bal_lo - amount` IS satisfied (modular arithmetic)
- The state_commitment = hash_4_to_1(new_bal_lo, ...) commits to the wrapped value
- On the NEXT row, this wrapped value is the "old_bal_lo"
- If the prover adds 300 back: new_bal_lo = (p - 100) + 300 = p + 200 = 200 (mod p)
- Final balance shows 200, which is > initial 100 + net credits 100

**But:** The boundary constraint pins the LAST row's state_commit to PI[NEW_COMMIT]. The executor verifies that the declared new_commitment actually decodes to a valid (non-wrapped) balance. So the attack is caught... but ONLY because the executor performs this check.

**In-circuit fix:** Range-check `new_bal_lo < 2^30` on EVERY row (not just boundary).

This is the SAME lookup table as Trust Assumption 1. For each debit row (Transfer out, NoteCreate, CreateObligation), constrain:
```
new_bal_lo = old_bal_lo - amount
new_bal_lo IN [0, 2^30)  (via lookup)
```

**Cost:** Same as Trust Assumption 1 (shared lookup table). The range check on `new_bal_lo` applies to all rows anyway (it's part of the state commitment validity).

**Eliminates trust?** YES, fully. Wrapping arithmetic is detectable because the wrapped value exceeds 2^30.

### Trust Assumption 3: Nullifier Uniqueness (Double-Spend Prevention)

**Current state:** The executor maintains a `NullifierSet` (`cell/src/nullifier_set.rs`) and rejects duplicate nullifiers imperatively. NOT proven in-circuit.

**In-circuit approaches:**

**Option A: Merkle non-membership proof (composition)**

The existing `AccumulatorNonRevocationAir` proves an element is NOT in a polynomial accumulator. This could be adapted:
- Public input: nullifier + accumulator_value (commitment to all previously-revealed nullifiers)
- Proof: nullifier is not a root of the accumulator polynomial
- After accepting: update accumulator with the new nullifier

**Cost:** ~64 rows per non-membership proof (already implemented as a standalone AIR)

**Integration:** Compose with Effect VM via shared public input:
- Effect VM exposes `nullifier` as a public input
- Non-membership proof exposes same `nullifier` + `accumulator_root`
- Verifier checks both proofs AND that nullifiers match AND that accumulator_root matches the federation's current accumulator

**Option B: Nullifier Merkle tree non-membership**

Use the adjacent-neighbor technique (already in `cell/src/nullifier_set.rs`) but prove it via Poseidon2 Merkle STARK.

**Option C: Polynomial accumulator inside the Effect VM (most efficient)**

Add accumulator columns to the Effect VM trace:
- `old_accumulator` (row N) -> NoteSpend -> `new_accumulator` (row N) = old * (alpha - nullifier)
- Public inputs: `initial_accumulator`, `final_accumulator`
- Verifier checks `final_accumulator` matches the federation's expected value

**Cost:** +2 auxiliary columns (old_accum, new_accum) + 1 constraint per row  
**Security:** Relies on the DLP assumption in the extension field (already used by AccumulatorNonRevocationAir)

**Recommendation:** Option C (polynomial accumulator in the Effect VM). Estimated +2 columns, +1 transition constraint.

**Eliminates trust?** YES, fully (with Option C). The accumulator update is algebraically bound.

### Trust Assumption 4: Obligation Existence for FulfillObligation

**Current state:** The executor checks that the obligation_id exists in its local obligation store (`turn/src/executor.rs:3515`). NOT proven in-circuit.

**In-circuit fix:** Merkle membership proof (obligation tree).

The system already has the pattern for this (BodyMembershipProof does exactly the same thing for fact membership). Approach:

1. Maintain a Poseidon2 Merkle tree of active obligations (keyed by obligation_id)
2. For FulfillObligation: require a Merkle membership STARK proving `obligation_id` is a leaf in the obligation tree
3. The obligation tree root is a public input to the Effect VM (or a composed proof)

**Cost:** 1 additional Poseidon2 Merkle membership STARK per FulfillObligation effect (same cost as body_membership proofs -- ~32 rows for depth-4 tree)

**Integration:** Follow the BodyMembershipProof pattern:
- Effect VM produces `obligation_id` as extractable from the trace
- Composed proof includes: membership STARK with PI = [obligation_id, obligation_tree_root]
- Verifier checks: obligation_tree_root matches federation's current obligation root

**Eliminates trust?** YES, fully. Proving membership requires the obligation to actually exist.

### Trust Assumption 5: Custom Effect External Proof Validity

**Current state:** The executor verifies custom proofs by:
1. Checking blake3(proof_bytes) matches the PI commitment (4 BabyBear elements)
2. Looking up the VK hash in its program registry
3. Calling `program.verify_transition(...)` imperatively

**The VK hash IS already a public input** (PI[7+i*8..7+i*8+4]). The proof commitment IS already a public input (PI[7+i*8+4..7+i*8+8]).

**Gap:** The verification itself (step 3) is done by the executor, not proven recursively.

**In-circuit fix (full):** Recursive STARK verification. The custom program's STARK proof is verified inside a STARK (STARK-in-STARK recursion).

This is partially implemented: `circuit/src/poseidon_stark_verifier_circuit.rs` IS a Poseidon-gate-based STARK verifier circuit. The `stark_in_pickles.rs` backend also does recursive verification.

**Cost:** ~100,000-200,000 constraints per recursive verification (estimated from `poseidon_stark.rs:1287`)

**Practical approach:** Instead of full recursion, use the existing commit-and-verify pattern:
- The Effect VM commits to (VK_hash, proof_hash) as public inputs
- A separate verifier (which CAN be another STARK or a hardware TEE) attests validity
- The attestation is bound to the proof hash

**Eliminates trust?** PARTIALLY. Full elimination requires recursive STARK verification (expensive). The commit-and-verify pattern reduces trust to the external verifier's correctness.

**Recommendation:** Phase 1: Keep current pattern (executor verifies). Phase 2: When recursive STARK is production-ready, verify custom proofs recursively.

### Trust Assumption 6: State Root Freshness

**Current state:** The executor checks that the accumulator/federation root used in proofs matches the current state (`turn/src/conditional.rs:261-263` checks `federation_root` against `trusted_roots`).

**In-circuit fix:** Bind the proof to a specific block height + root.

The system already partially does this:
- `verifier_block_height` is a public input in PresentationProof
- `not_after_height` enables expiry enforcement
- The `TrustedRoot` system provides a sliding window

**Missing piece:** The Effect VM does NOT bind to a federation state root. It only binds to the cell's own state commitment.

**Proposed enhancement:**
1. Add `federation_root` as an additional public input to the Effect VM (PI[7] or after custom effects)
2. The executor supplies the current federation root when generating the proof
3. The verifier checks: PI[federation_root] matches the root at the declared block height
4. Within the AIR: the nullifier accumulator root (from Trust Assumption 3) must equal the federation's nullifier sub-tree root

**Cost:** +1 public input element, +1 boundary constraint

**Eliminates trust?** MOSTLY. The remaining trust is: "the block height referenced is actually canonical." This is resolved by Trust Assumption 7 (consensus ordering).

### Trust Assumption 7: Execution Ordering (Turns Processed in Consensus Order)

**Current state:** The executor processes turns in the order received from the blocklace. Ordering is enforced by the consensus layer, not by proofs.

**In-circuit fix:** This is a CONSENSUS property, not a per-turn property. It CANNOT be fully proven in a single-turn STARK.

**Partial in-circuit approach:**
- The IVC chain already enforces sequential ordering: `step_count` increments and `accumulated_hash = Poseidon2(old_hash || new_root || step)`. Reordering steps requires breaking Poseidon2 preimage resistance.
- For multi-turn ordering: the blocklace finality proof (which proves a DAG of turns forms a consistent total order) is the right abstraction.

**Recommendation:**
1. The IVC chain handles sequential steps within one cell's history (ALREADY DONE)
2. Cross-cell ordering requires the blocklace finality proof (separate work item, not in-circuit per-turn)
3. The minimal trust envelope: "the blocklace finality algorithm is correct" (this is the consensus assumption, irreducible)

**Eliminates trust?** NO (irreducible consensus assumption). But the attack surface is minimized: ordering attacks require controlling the consensus/finality mechanism, not just the executor.

---

## Priority Summary

### P0 (Critical, Fix Now)

| Issue | File | Impact |
|---|---|---|
| `hash_to_bb` single-element truncation | `turn/src/executor.rs:843` | 31-bit collision on nullifiers/obligations |
| Same pattern in SDK | `sdk/src/wallet.rs:3580` | Same |
| Effect VM single-element identifiers | `circuit/src/effect_vm.rs:329-369` | All security IDs at 31-bit |

### P1 (High, Next Sprint)

| Issue | File | Impact |
|---|---|---|
| Balance limb range check (Trust #1) | `circuit/src/effect_vm.rs:804-822` | Malicious prover can use invalid limbs |
| Balance underflow (Trust #2) | `circuit/src/effect_vm.rs:824-843` | Modular wrap inflation |
| Note poseidon2_commitment owner truncation | `cell/src/note.rs:233-238` | 31-bit owner binding |
| Orderbook id_hash_to_field | `apps/orderbook/src/circuit.rs:554-558` | Wash trading possible |

### P2 (Moderate, Roadmap)

| Issue | File | Impact |
|---|---|---|
| Nullifier accumulator in-circuit (Trust #3) | n/a (new work) | Double-spend without executor |
| Obligation membership (Trust #4) | n/a (new work) | Fake fulfillment without executor |
| State root binding (Trust #6) | n/a (enhancement) | Stale state attacks |

### P3 (Low / Accepted Risk)

| Issue | File | Impact |
|---|---|---|
| Non-membership domain_sep (31-bit) | `circuit/src/non_membership.rs:59-63` | Operator-controlled, non-adversarial |
| Custom proof recursive verification (Trust #5) | Executor-verified | Expensive; keep executor for now |
| Execution ordering (Trust #7) | Consensus layer | Irreducible; blocklace handles this |

---

## Estimated Constraint Costs for Full Trust Elimination

| Fix | Additional Columns | Additional Rows | Notes |
|---|---|---|---|
| Multi-element identifiers (P0) | +20 | 0 | Trace width increase ~15% |
| Lookup table range checks (P1) | +4 logup | +65536 table rows (shared) | One-time table, amortized |
| Nullifier accumulator (P2) | +2 | 0 | Extension field multiply |
| Obligation Merkle (P2) | 0 (composed) | +32 per FulfillObligation | Separate STARK proof |
| Federation root binding (P2) | +1 PI | 0 | Trivial |
| Recursive custom verification (P3) | ~400 | ~100K rows per custom proof | Defer to Phase 3 |

**Total immediate impact (P0+P1):** ~24 additional trace columns, shared 2^16 lookup table. Proof size increase: ~15-20%. Prover time increase: ~25-30%.

---

## Appendix: Where Each blake3 Usage Maps

| Location | Type | In-Circuit? | Verdict |
|---|---|---|---|
| `circuit/src/stark.rs` (FRI Merkle) | Protocol | No | OK |
| `circuit/src/stark.rs` (Fiat-Shamir) | Protocol | No | OK |
| `circuit/src/ivc.rs` (trace commit) | Binding | No | OK |
| `circuit/src/backends/binius.rs` | Constraint | Yes (binary) | OK (binius-specific) |
| `circuit/src/schnorr_sig.rs` | Pre-processing | Partial | OK (encode_hash after) |
| `circuit/src/non_membership.rs:59` | Domain tag | Yes (1 elem) | LOW RISK |
| `circuit/src/predicate_program.rs:1877` | Pre-processing | Partial | OK (poseidon2 after) |
| `circuit/src/binding.rs` | Commitment | Yes (8 elem) | OK (full width) |
| `turn/src/executor.rs:843` | Identifier | Yes (1 elem!) | **CRITICAL** |
| `turn/src/executor.rs:779` | Proof hash | Yes (4 elem) | OK (124 bits) |
| `turn/src/executor.rs:875` | Capability | Yes (1 elem!) | **HIGH** |
| `turn/src/executor.rs:968` | Turn hash | No | OK (dead code) |
| `turn/src/conditional.rs` | Gossip | No | OK |
| `turn/src/obligation.rs` | ID derivation | No* | OK (*unless proven) |
| `turn/src/forest.rs` | Content addr | No | OK |
| `cell/src/cell.rs:239` | Storage | No | OK (dual system) |
| `cell/src/note.rs:163` | Storage | No | OK (dual system) |
| `sdk/src/embed.rs` | Integrity | No | OK |
| `sdk/src/wallet.rs:3580` | Identifier | Yes (1 elem!) | **CRITICAL** |
| `apps/orderbook/src/circuit.rs:554` | Identity | Yes (1 elem!) | **HIGH** |
