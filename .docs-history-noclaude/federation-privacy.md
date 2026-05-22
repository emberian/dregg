# Federation Privacy: Encrypted Turns for Private Ordering

## Problem Statement

Federation validators currently see ALL turn content in cleartext: the agent identity, actions, effects, targets, and balances. This is a panopticon — the ordering service knows everything about every participant's activity.

The challenge: validators must (1) order turns, (2) detect conflicts, (3) enforce conservation, and (4) verify fee sufficiency — all of which *appear* to require seeing the turn content.

This document explores mechanisms for ordering turns without revealing their content to the federation.

---

## Approach A: Commit-then-Reveal with ZK Validity Proofs

**Core idea**: Agents submit encrypted turns alongside STARK proofs that the encrypted content is valid, without revealing what it is.

### Protocol

```
┌─────────────────────────────────────────────────────────────────┐
│  SUBMIT PHASE                                                    │
│                                                                  │
│  Agent constructs:                                               │
│    1. encrypted_turn = ChaCha20-Poly1305(turn_body, agent_key)   │
│    2. turn_commitment = BLAKE3(turn_body)                        │
│    3. validity_proof = STARK proving:                             │
│       - "I know a turn T whose BLAKE3 hash = turn_commitment"    │
│       - "T.nonce = agent_cell.nonce" (replay protection)         │
│       - "agent_cell.balance >= T.fee" (can pay)                  │
│       - "T conserves value" (no creation ex nihilo)              │
│    4. conflict_set = BloomFilter(read_cells ∪ write_cells)       │
│    5. fee_commitment = Pedersen(fee, blinding)                   │
│                                                                  │
│  Submission = (encrypted_turn, turn_commitment, validity_proof,  │
│                conflict_set, fee_commitment)                      │
└─────────────────────────────────────────────────────────────────┘
           │
           ▼
┌─────────────────────────────────────────────────────────────────┐
│  ORDER PHASE (Federation consensus)                              │
│                                                                  │
│  Validators:                                                     │
│    1. Verify validity_proof (STARK verification — no decryption) │
│    2. Check conflict_set overlap between pending turns           │
│       - Non-conflicting turns: parallelize                       │
│       - Conflicting turns: serialize by submission time          │
│    3. Order turns into block by (conflict_bucket, timestamp)     │
│    4. Produce block with ordered turn_commitments                │
│                                                                  │
│  Block = { turn_commitments: Vec<[u8;32]>, ... }                │
└─────────────────────────────────────────────────────────────────┘
           │
           ▼
┌─────────────────────────────────────────────────────────────────┐
│  REVEAL + EXECUTE PHASE                                          │
│                                                                  │
│  Option 1: Agent reveals decryption key after ordering           │
│  Option 2: Threshold decryption (t-of-n validators decrypt)      │
│  Option 3: Time-locked encryption (VDF-based auto-reveal)        │
│                                                                  │
│  Validators decrypt, execute in agreed order, produce receipts.  │
│  If turn is invalid despite validity_proof: agent is slashed.    │
│  (The STARK was forged — this should be computationally          │
│  infeasible but provides economic backstop.)                     │
└─────────────────────────────────────────────────────────────────┘
```

### The Conflict Set: Key Insight

The conflict set is what makes ordering possible without seeing content. Two turns conflict if and only if they touch overlapping cells. If we can detect this overlap from commitments alone, we can order without decrypting.

**Approach A1: Bloom filter conflict sets**

```
conflict_set = BloomFilter::new(k=8, m=256)
for cell_id in turn.read_set ∪ turn.write_set:
    conflict_set.insert(cell_id)
```

Properties:
- False positives: two non-conflicting turns may appear to conflict (conservative — safe)
- No false negatives: truly conflicting turns are always detected
- Privacy: the Bloom filter reveals the *size* of the access set but not the specific cells
- Cost: O(1) conflict detection between any two turns

**Approach A2: Committed conflict sets (more private)**

```
conflict_commitment = BLAKE3(sorted(read_cells) || sorted(write_cells))
```

Problem: two turns can only be compared if they reveal their full conflict sets. A Bloom filter leaks less than explicit cell IDs but more than a single hash.

**Approach A3: Encrypted Bloom filter with homomorphic comparison**

The conflict sets are encrypted but support a "do these overlap?" query via an additively homomorphic scheme. This is the most private but requires a specific HE scheme for bit-vector inner products.

### Tradeoffs

| Property | Rating | Notes |
|----------|--------|-------|
| Privacy | HIGH | Validators never see turn content until execution |
| Complexity | VERY HIGH | Full-turn validity proof in ZK is a large circuit |
| Latency | MEDIUM | 2 phases (submit + execute) vs 1 (current) |
| Soundness | HIGH | STARK is computationally sound; economic slash as backstop |
| Conflict detection | MEDIUM | Bloom filter has false positives (reduces parallelism) |
| Proof size | MEDIUM | ~50-100 KiB per turn for the validity proof |
| Prover time | HIGH | Agents must generate STARK proofs for every turn |

### What the Validity Proof Must Cover

The `TurnValidityAir` must prove (without revealing turn content):

1. **Structural validity**: The encrypted blob decrypts to a well-formed Turn struct
2. **Nonce correctness**: `turn.nonce == agent_cell.nonce` (prevents replay)
3. **Fee sufficiency**: `agent_cell.balance >= turn.fee` (agent can pay)
4. **Conservation**: Sum of all balance deltas = 0 (no value creation)
5. **Authorization**: All actions have valid signatures/proofs (the hardest part)
6. **Conflict set honesty**: The declared conflict set genuinely covers all accessed cells

Item 5 is the hardest — proving signature verification in a STARK is expensive but tractable (Ed25519 in BabyBear STARK: ~2^20 rows). Item 6 requires the prover to commit to the access set derivation.

### Incremental Deployment

Phase 1 (this prototype): Prove items 2-3 only (nonce + fee). This is enough for a meaningful privacy improvement: the federation can order and debit fees without seeing the turn body.

Phase 2: Add conservation proof (item 4). This requires encoding the balance algebra in the AIR.

Phase 3: Add authorization proof (item 5). Requires Ed25519 verification circuit.

Phase 4: Add conflict set honesty proof (item 6). Requires encoding the CallForest traversal in the AIR.

---

## Approach B: Homomorphic State Computation

**Core idea**: Execute turns over encrypted state using Fully Homomorphic Encryption (FHE).

### How It Would Work

1. All cell state is encrypted under a federation threshold key
2. Turns operate on encrypted values: `Enc(balance) - Enc(fee)` computed homomorphically
3. Conservation is verified homomorphically: `sum(Enc(deltas)) == Enc(0)`
4. Only the agent sees their own plaintext state (via their share of the threshold key)

### Tradeoffs

| Property | Rating | Notes |
|----------|--------|-------|
| Privacy | VERY HIGH | Even execution is private |
| Complexity | EXTREME | State-of-the-art FHE research |
| Latency | VERY HIGH | FHE operations are ~10^6x slower than plaintext |
| Soundness | HIGH | Cryptographic |
| Practicality | LOW | Not viable for real-time systems in 2026 |

### Verdict

Theoretically ideal but computationally impractical. The overhead of FHE (even modern schemes like TFHE or BFV) makes this unsuitable for a system targeting sub-second turn execution. Revisit when FHE hardware accelerators mature (2028+?).

---

## Approach C: TEE-Based Private Execution

**Core idea**: Validators run in hardware enclaves (SGX, TDX, SEV-SNP). Turns are encrypted to the enclave's attestation key.

### How It Would Work

```
┌─────────────────────────────────────────────────────────────────┐
│  ENCLAVE (SGX/TDX)                                               │
│                                                                  │
│  1. Receive encrypted turn (encrypted to enclave pubkey)         │
│  2. Decrypt inside enclave                                       │
│  3. Validate + execute                                           │
│  4. Produce attested receipt (signed by enclave key)             │
│  5. Emit: receipt + post_state_root (no turn content)            │
│                                                                  │
│  Turn content NEVER leaves the enclave in plaintext              │
└─────────────────────────────────────────────────────────────────┘
```

### Tradeoffs

| Property | Rating | Notes |
|----------|--------|-------|
| Privacy | HIGH | Content stays in enclave |
| Complexity | LOW | Standard attestation patterns |
| Latency | LOW | Native execution speed inside enclave |
| Soundness | MEDIUM | Hardware trust assumption (side-channel attacks exist) |
| Decentralization | LOW | Requires specific hardware from Intel/AMD |
| Resilience | LOW | If enclave is compromised, all privacy is lost retroactively |

### Verdict

Pragmatic for a production system that needs privacy NOW, but the hardware trust assumption is philosophically at odds with pyana's "proof-carrying state" design. Good as an intermediate step while ZK circuits mature. Could be combined with Approach A: TEE for execution, ZK for ordering.

---

## Approach D: Threshold Decryption with Delayed Reveal

**Core idea**: Turns are encrypted to a threshold key shared among validators. After consensus (ordering), validators collaboratively decrypt. Historical turns remain encrypted.

### Protocol

```
Setup: Validators hold shares of a threshold decryption key (t-of-n)

Submit:  Agent encrypts turn to the threshold public key
         submission = ThresholdEnc(turn, federation_threshold_pk)

Order:   Validators order encrypted submissions by conflict_set metadata
         (requires Approach A's Bloom filter for conflict detection)

Decrypt: After block is finalized, t validators produce decryption shares
         Each validator sees the turn only AFTER ordering is locked in

Execute: Validators decrypt and execute. If invalid, agent is slashed.
         Receipt is published. Turn content is NOT stored long-term.

Forget:  After execution, validators delete plaintext turns.
         Only receipts (state transitions) are retained.
```

### Tradeoffs

| Property | Rating | Notes |
|----------|--------|-------|
| Privacy | MEDIUM-HIGH | Turns are private during ordering; revealed to t validators after |
| Complexity | MEDIUM | Threshold crypto is well-understood |
| Latency | MEDIUM | Extra round for threshold decryption |
| Soundness | HIGH | Standard threshold assumptions |
| Long-term privacy | HIGH | Historical turns can remain encrypted forever |
| Liveness | MEDIUM | Needs t validators online for decryption |

### Advantage Over Pure ZK

The threshold approach doesn't require the agent to generate a STARK proof for every turn. The tradeoff: t validators DO eventually see the turn (but only after ordering). For many threat models (MEV protection, front-running resistance), this is sufficient.

---

## Recommended Architecture: Layered Privacy

Combine approaches for defense in depth:

```
Layer 1: CONFLICT SET (Approach A, partial)
  - Bloom filter conflict set for ordering without content
  - Lightweight STARK for nonce + fee (items 2-3)
  - Federation can order and detect conflicts

Layer 2: THRESHOLD DECRYPTION (Approach D)
  - Turn body encrypted to threshold key
  - Decrypted AFTER ordering is finalized
  - Protects against MEV and front-running

Layer 3: FULL VALIDITY PROOF (Approach A, complete) [FUTURE]
  - Full STARK proving conservation + authorization
  - Eliminates need for decryption entirely
  - Agents generate proofs; federation only verifies
```

### Phase 1 (This Prototype)

Implement Layer 1:
- `EncryptedTurn` struct with encrypted body + conflict set + validity proof
- `TurnValidityAir` proving nonce correctness and fee sufficiency
- Bloom filter conflict set for ordering
- Federation orders without seeing turn content

### Phase 2 (Next)

Add Layer 2:
- Threshold key ceremony during federation genesis
- Turn encryption to threshold public key
- Decryption protocol after block finalization
- Delete-after-execute policy

### Phase 3 (Research)

Complete Layer 3:
- Full conservation proof in the validity AIR
- Ed25519 verification circuit for authorization
- Conflict set honesty proof
- Eliminate threshold decryption entirely

---

## Security Analysis

### Threat Model

| Adversary | What they learn (current) | What they learn (Phase 1) |
|-----------|--------------------------|---------------------------|
| Passive validator | Full turn content | Conflict set size + bloom filter bits |
| Active validator (Byzantine) | Full turn content + can reorder | Bloom filter + can reorder non-conflicting |
| Network observer | Encrypted QUIC payload | Encrypted QUIC payload (unchanged) |
| Historical analyst | Full chain history | Only receipts (turn bodies are ephemeral) |

### What the Bloom Filter Leaks

- **Set size**: The number of set bits reveals approximately how many cells are accessed
- **Hot cells**: If a cell appears in many Bloom filters, its hash positions become identifiable
- **Correlation**: Same agent with similar access patterns produces similar Bloom filters

Mitigation: Add random dummy bits to the Bloom filter (increases false positive rate but reduces information leakage). The validity proof must then prove "all REAL accessed cells are in the filter" without proving "all filter bits correspond to real cells."

### Slashing Conditions

If a turn passes validity_proof verification but fails execution after reveal:
1. The validity proof was forged (computationally infeasible — STARK soundness)
2. The state changed between proof generation and execution (stale nonce/balance)

Case 2 is not the agent's fault. Resolution: if execution fails due to stale state, the turn is simply dropped (not slashed). Slashing only occurs for provably forged proofs (which would require breaking BabyBear STARK soundness).

---

## Relationship to Existing Architecture

### Integration Points

- `federation/src/consensus.rs`: Block proposals carry `Vec<TurnCommitment>` instead of `Vec<TurnHash>`
- `turn/src/turn.rs`: New `EncryptedTurn` type alongside existing `Turn`
- `circuit/src/turn_validity_air.rs`: New AIR for turn validity proofs
- `turn/src/conflict.rs`: Bloom filter conflict set implementation
- `coord/`: The 2PC coordinator learns about encrypted turns

### Migration Path

1. Both `Turn` (cleartext) and `EncryptedTurn` (private) are valid block content
2. Federations opt in to privacy mode per configuration
3. Solo federations (1-node) may skip encryption (no privacy needed from yourself)
4. Cross-federation operations use threshold decryption at the boundary

### Compatibility with Existing Features

- **Budget gates (Stingray)**: The fee_commitment in the validity proof replaces the plaintext fee check. Budget debit uses the proven fee amount.
- **Conditional turns**: The condition proof can reference encrypted turns by their commitment hash.
- **Pipelines (eventual sends)**: Pipeline resolution requires decryption. Pipelines within a single encrypted turn work; cross-turn pipelines require the reveal phase.
- **Receipt chains**: Receipts are always public (they contain only state transition evidence, not turn content). Receipt chain verification is unchanged.
