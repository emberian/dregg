# Garbled Circuits and Oblivious Transfer for Two-Party Private Computation

Research document exploring how Yao's garbled circuits and oblivious transfer (OT)
can integrate with pyana to enable two-party private computation where neither
party reveals their input but both learn the result.

---

## 1. Motivation: The Gap in Pyana's Privacy Stack

Pyana's current privacy primitives cover single-party proving:

| Primitive | What it does | Limitation |
|-----------|-------------|-----------|
| `PredicateAir` | Prove `value >= threshold` without revealing value | Threshold must be public |
| Sealed secrets (X25519) | Encrypt data between parties | Receiver sees plaintext |
| Intent matching | Find counterparties without revealing capabilities | Match criteria are public or revealed to counterparty |
| IVC fold chains | Prove capability attenuation | Single-prover only |

**Missing capability**: Two-party computation where NEITHER party reveals their input.
This corresponds to Class B (private threshold), Class F (relational predicates), and
private intent matching from the predicate taxonomy in `docs/private-predicates.md`.

### Concrete use cases requiring 2PC:

1. **Private threshold comparison**: "Does my credit score meet your secret hiring bar?"
   (Class B -- verifier's threshold is secret)
2. **Private auction reserves**: "Does my bid exceed the seller's secret minimum?"
   (Neither reveals their number, both learn pass/fail)
3. **Private capability matching**: "Does my offered capability satisfy your secret
   requirement?" (Neither reveals details, both learn compatibility)
4. **Private intent negotiation**: "Is there overlap between my offer range and your
   need range?" (Millionaires' Problem variant)

---

## 2. Oblivious Transfer from X25519 (Chou-Orlandi Construction)

### 2.1 Background: 1-of-2 OT

Oblivious Transfer is the fundamental building block for two-party computation:

- **Sender** holds two messages `(m_0, m_1)`.
- **Receiver** holds a choice bit `b in {0, 1}`.
- After the protocol: Receiver learns `m_b`; Sender learns nothing about `b`.

### 2.2 The Simplest OT (Chou-Orlandi 2015)

The Chou-Orlandi protocol builds OT from a single Diffie-Hellman group -- exactly
what X25519 provides. We already have `x25519_dalek` in `tokenizer/src/encrypt.rs`.

**Protocol** (using Curve25519 notation):

```
Setup: Generator G (Curve25519 basepoint)

Sender:
  1. Generate random scalar y, compute S = yG.
  2. Send S to Receiver.

Receiver (choice bit b):
  3. Generate random scalar x.
  4. If b = 0: compute R = xG
     If b = 1: compute R = S + xG     (i.e., R = yG + xG)
  5. Send R to Sender.

Sender:
  6. Compute k_0 = H(yR) = H(xyG)         -- key for message 0
     Compute k_1 = H(y(R - S)) = H(y(R - yG))  -- key for message 1
  7. Send e_0 = Enc(k_0, m_0), e_1 = Enc(k_1, m_1)

Receiver:
  8. Compute k_b = H(xS) = H(xyG)
  9. Decrypt m_b = Dec(k_b, e_b)
     (Cannot decrypt e_{1-b} because they'd need the DH of a point they
      cannot compute without knowing y.)
```

**Why it works**:
- If `b = 0`: Receiver computed `R = xG`, so `xS = xyG = k_0`. Correct.
  Sender computed `k_1 = H(y(xG - yG)) = H(y(x-y)G)`. Receiver doesn't know `y`,
  so cannot compute this.
- If `b = 1`: Receiver computed `R = yG + xG`, so `xS = xyG = k_0`... wait, that's
  `k_0` not `k_1`. Let me correct:
  Actually `k_b = H(xS)`. If `b = 1`, `R = S + xG`, so from Sender's perspective:
  `k_1 = H(y(R - S)) = H(y * xG) = H(xyG)`. And Receiver has `xS = x(yG) = xyG`.
  So Receiver's key matches `k_1`. Correct.

**Security**:
- Receiver cannot compute `k_{1-b}` without solving CDH.
- Sender sees `R` which is uniformly random regardless of `b` (information-theoretically
  hiding the choice bit under DDH).

### 2.3 Integration with Pyana's X25519 Infrastructure

The `TokenizerKeypair` in `tokenizer/src/encrypt.rs` already wraps `x25519_dalek`:

```rust
// Existing infrastructure we can reuse:
use x25519_dalek::{PublicKey, StaticSecret};

// New OT module would live at: tokenizer/src/ot.rs or a new crate
pub struct OtSender {
    y: StaticSecret,      // sender's OT secret
    S: PublicKey,         // yG -- sent to receiver
}

pub struct OtReceiver {
    x: StaticSecret,      // receiver's OT secret
    choice: bool,         // the choice bit
}
```

**Cost per 1-of-2 OT**:
- 1 scalar multiplication (receiver computes R)
- 2 scalar multiplications (sender computes k_0, k_1)
- 2 symmetric encryptions (AES-128 or ChaCha20)
- Communication: 32 bytes (S) + 32 bytes (R) + 2 * (ciphertext_size + 16 bytes tag)

**For 31-bit values (BabyBear field elements)**: We need 31 OTs (one per bit of the
evaluator's input). Using OT extension (IKNP03), we can amortize:
- Base OTs: ~128 (using Chou-Orlandi)
- Extended OTs: 31 from those 128 base OTs via correlation-robust hashing
- Total communication for 31 OTs: ~128 * 64 bytes (base) + 31 * 256 bytes (labels) ~ 16 KB

---

## 3. Garbled Comparison Circuit for BabyBear Values

### 3.1 The Comparison Circuit

To compare two 31-bit values `a >= b`, the standard ripple-comparison circuit:

```
Input: a[30..0], b[30..0] (bit decomposition, MSB first)
Output: 1 if a >= b, else 0

For each bit position i from MSB to LSB:
  If a[i] > b[i]: result = 1 (a is larger, done)
  If a[i] < b[i]: result = 0 (b is larger, done)
  If a[i] == b[i]: continue to next bit

Equivalently as a circuit:
  carry[31] = 1  (assume equal until proven otherwise)
  For i = 30 down to 0:
    carry[i] = (a[i] AND NOT b[i]) OR (carry[i+1] AND NOT (b[i] AND NOT a[i]))
  output = carry[0]
```

**Gate count for 31-bit comparison**:
- Per bit: 2 AND gates + 1 OR gate + 2 NOT gates (NOTs are free in garbled circuits)
- Total: 31 * 3 = **93 non-free gates** (using free-XOR optimization where XOR/NOT are free)

With the free-XOR technique (Kolesnikov-Schneider 2008), XOR gates have zero
ciphertext cost. Rewriting the comparison using XOR where possible:

```
gt[i] = a[i] AND (a[i] XOR b[i])    -- a[i]=1 and b[i]=0
lt[i] = b[i] AND (a[i] XOR b[i])    -- b[i]=1 and a[i]=0
eq[i] = NOT (a[i] XOR b[i])         -- free (XOR + NOT)

carry[i] = gt[i] OR (eq[i] AND carry[i+1])
         = gt[i] XOR ((gt[i] XOR eq[i]) AND (gt[i] XOR carry[i+1]))
         -- rewritten to minimize AND gates (each AND = 1 garbled row with half-gates)
```

With **half-gates** (Zahur-Rosulek-Evans 2015), each AND gate costs **2 ciphertexts**
(2 * 128 bits = 32 bytes).

**Optimized gate count**: ~62 AND gates for 31-bit comparison (2 AND per bit).

### 3.2 Garbled Circuit Size

Using half-gates (state of the art for point-and-permute garbling):
- Each AND gate: 2 ciphertexts * 16 bytes = 32 bytes
- XOR gates: free (no ciphertext)
- NOT gates: free (flip the permutation bit)

**Total garbled circuit size for 31-bit comparison**:
- 62 AND gates * 32 bytes = **1,984 bytes (~2 KB)**
- Plus input wire labels: 31 bits * 2 labels * 16 bytes = 992 bytes
- Plus output decoding table: 32 bytes
- **Total: ~3 KB** for the garbled circuit itself

This is remarkably small -- well within a single network packet.

### 3.3 Full Communication Cost

For a single private comparison `a >= b` where Alice holds `b` (threshold) and
Bob holds `a` (value):

| Step | Direction | Size |
|------|-----------|------|
| Alice sends garbled circuit | A -> B | ~2 KB |
| Alice sends her input labels (for threshold bits) | A -> B | 31 * 16 = 496 bytes |
| OT for Bob's input labels (31 OTs) | A <-> B | ~4 KB (with OT extension) |
| Bob sends encrypted output | B -> A | 32 bytes |
| **Total** | | **~7 KB** |

Compare to the alternative approaches:
- Committed threshold (current design path): ~1 KB (just a STARK proof)
- Full MPC-in-the-head: ~50-200 KB
- Garbled circuit: **~7 KB** (sweet spot)

---

## 4. The "STARK over Garbled Evaluation" Composition Pattern

### 4.1 The Core Idea

After Bob evaluates the garbled circuit and learns the output (pass/fail), he holds:
- The garbled circuit (from Alice)
- His input wire labels (from OT)
- Each intermediate wire label (from evaluation)
- The output wire label (which decodes to 0 or 1)

**Can Bob prove to a third party that he correctly evaluated the garbled circuit and
got output=1?** Yes -- by embedding the evaluation trace in a STARK.

### 4.2 Garbled Gate Evaluation as Arithmetic Constraints

A garbled AND gate with half-gates works as follows:

```
Input labels: L_a (Alice's wire), L_b (Bob's wire)
Each label is 128 bits with a permutation bit (color bit) in the LSB.

Evaluation:
  1. Extract color bits: c_a = LSB(L_a), c_b = LSB(L_b)
  2. Compute: T_G = H(L_a, gate_id) XOR (c_a * delta_table_entry)
  3. Compute: T_E = H(L_b, gate_id) XOR (c_b * delta_table_entry)
  4. Output label: L_out = T_G XOR T_E

Where H is a circular correlation-robust hash (e.g., fixed-key AES).
```

**STARK trace for one gate evaluation**:

| Column | Description |
|--------|-------------|
| 0..7 | Input label L_a (128 bits as 8 BabyBear elements, 16 bits each) |
| 8..15 | Input label L_b (128 bits as 8 BabyBear elements) |
| 16..23 | Garbled table entry (from Alice's circuit, 128 bits) |
| 24..31 | H(L_a, gate_id) intermediate (AES evaluation) |
| 32..39 | H(L_b, gate_id) intermediate |
| 40..47 | Output label L_out (128 bits) |
| 48 | Gate ID (counter) |
| 49 | Correctness flag |

**Constraints per row**:
1. `L_out = T_G XOR T_E` (bitwise XOR as field arithmetic)
2. `T_G = H(L_a, gate_id) XOR (c_a * garbled_entry_0)` (hash correctness)
3. `T_E = H(L_b, gate_id) XOR (c_b * garbled_entry_1)` (hash correctness)
4. Output row: `output_label` matches the "1" decoding key (public input from Alice)

**The hard part**: Constraint (2) and (3) require proving correct AES/hash evaluation
inside the STARK. AES in an arithmetic circuit over BabyBear is expensive (~6000
multiplication gates per AES call, times 2 per garbled gate, times 62 gates = ~744,000
multiplications).

### 4.3 Cost Analysis: STARK over Garbled Evaluation

**Naive approach** (prove AES inside STARK):
- Trace rows: 62 gates * ~200 rows per gate (for AES constraints) = ~12,400 rows
- Trace width: ~50 columns
- Proof generation: ~2-5 seconds (dominated by AES-in-circuit)
- Proof size: ~50-100 KB (FRI-based STARK)

**Optimized approach** (algebraic hash instead of AES):

If we replace AES with Poseidon2 as the garbling hash (both parties agree on this),
the constraint cost drops dramatically:

- Poseidon2 in BabyBear: 24 rounds, ~24 multiplication constraints per hash
- Per gate: 2 Poseidon2 calls = 48 multiplications
- 62 gates: 62 * 48 = ~2,976 multiplications
- Trace rows: ~3,000 (one per multiplication step)
- Proof generation: **~100-300 ms** (comparable to existing PredicateAir proofs)
- Proof size: **~20-40 KB**

**This is the key insight**: By using a STARK-friendly hash for garbling (Poseidon2
instead of AES), we make the "STARK wrapping garbled evaluation" pattern practical.

### 4.4 The Poseidon2-Garbled Circuit Construction

Custom garbling scheme using Poseidon2 as the correlation-robust hash:

```
Garbling (Alice, the garbler):
  For each gate g with input wires (w_a, w_b) and output wire w_out:
    For each combination (c_a, c_b) in {0,1}^2:
      key = Poseidon2(L_a[c_a] || L_b[c_b] || gate_id)
      garbled_entry[c_a][c_b] = key XOR L_out[truth_table[c_a][c_b]]

Evaluation (Bob, the evaluator):
  For each gate g in topological order:
    c_a = LSB(L_a), c_b = LSB(L_b)
    key = Poseidon2(L_a || L_b || gate_id)
    L_out = garbled_entry[c_a][c_b] XOR key
```

**STARK constraint for one gate** (simplified, AND gate):

```
Public inputs: garbled_table[4][8] (4 entries * 128 bits), gate_id
Private witness: L_a, L_b (the evaluator's actual labels)

Constraint:
  1. color_a = LSB(L_a), color_b = LSB(L_b)  -- extract permutation bits
  2. idx = 2*color_a + color_b                 -- table index
  3. key = Poseidon2(L_a || L_b || gate_id)   -- hash for this gate
  4. L_out = garbled_table[idx] XOR key        -- decrypt output label
  5. Propagate L_out to next gate's input
```

The garbled table entries are **public inputs** to the STARK (Alice published the
garbled circuit). The wire labels are **private witness** (Bob's evaluation state).
The STARK proves Bob correctly followed the garbling protocol.

### 4.5 What the STARK Proves (Precisely)

The final STARK proof attests:

> "I (Bob) hold wire labels L_a[0..30] and L_b[0..30] such that:
> 1. L_b[i] were obtained via OT (bound to Alice's OT commitment)
> 2. Evaluating the garbled circuit gate-by-gate with these labels produces
>    output label L_out
> 3. L_out matches the decoding key for output=1 (published by Alice)
>
> Therefore: the computation `f(Alice's input, Bob's input) = 1`."

**Public inputs to the STARK**:
- The garbled circuit (all garbled table entries) -- committed via Poseidon2 hash
- Alice's OT public parameters (S from Chou-Orlandi)
- The output decoding key for "1"
- The circuit description (which function was computed)

**Private witness**:
- Bob's wire labels (from OT)
- All intermediate wire labels (from evaluation)
- Bob's OT secrets (proving labels came from a real OT, not fabricated)

---

## 5. Integration Points with Pyana

### 5.1 Where This Lives in the Codebase

```
tokenizer/src/ot.rs         -- Chou-Orlandi OT implementation (new)
circuit/src/garbled.rs      -- Poseidon2-based garbling scheme (new)
circuit/src/garbled_eval_air.rs  -- STARK AIR for garbled evaluation (new)
intent/src/private_match.rs -- Private intent matching via GC (new)
```

### 5.2 Integration with the Intent System

The intent system (`intent/src/lib.rs`) currently broadcasts `MatchSpec` with public
constraints. For private matching:

```rust
// Extension to PredicateRequirement in intent/src/lib.rs:
pub enum PrivatePredicateProtocol {
    /// Current: threshold is public, value is private (Class A)
    PublicThreshold { threshold: u64 },

    /// New: threshold is private, value is private (Class B)
    /// The garbled circuit approach
    GarbledComparison {
        /// Commitment to the garbled circuit: Poseidon2(all_garbled_tables)
        circuit_commitment: [u8; 32],
        /// OT sender's public parameter S = yG
        ot_sender_pubkey: [u8; 32],
        /// The circuit topology (comparison, range, custom)
        circuit_type: GarbledCircuitType,
    },
}
```

### 5.3 Integration with Sealed Secrets

The existing `SealedSecret` in `tokenizer/src/encrypt.rs` uses X25519 + ChaCha20Poly1305.
The OT protocol reuses the same X25519 infrastructure but with a different protocol
flow (the shared secret derivation follows Chou-Orlandi rather than sealed-box semantics).

Key difference:
- Sealed box: one party encrypts TO another (unidirectional)
- OT: interactive protocol where the choice bit is hidden (bidirectional)

Both use `x25519_dalek::StaticSecret` and `x25519_dalek::PublicKey`.

### 5.4 Integration with PredicateAir (Composition)

The garbled circuit output (pass/fail) can feed into the existing proof composition:

```
                    ┌─────────────────────────┐
                    │   Garbled Circuit (2PC)  │
                    │   "a >= b" over private  │
                    │   inputs from both       │
                    │   parties                │
                    └────────────┬────────────┘
                                 │ output = 1
                                 ▼
                    ┌─────────────────────────┐
                    │  GarbledEvalAir (STARK)  │
                    │  Proves correct eval     │
                    │  of garbled circuit      │
                    └────────────┬────────────┘
                                 │ proof
                                 ▼
                    ┌─────────────────────────┐
                    │  CompoundPredicateAir    │
                    │  Combines with other     │
                    │  predicates (AND/OR)     │
                    └────────────┬────────────┘
                                 │
                                 ▼
                    ┌─────────────────────────┐
                    │  BodyMembershipProof     │
                    │  Binds to token state    │
                    └─────────────────────────┘
```

### 5.5 Protocol Flow (End-to-End)

**Scenario**: Alice (verifier) wants to check if Bob's balance meets her secret
threshold, without revealing the threshold to Bob or Bob's balance to Alice.

```
Alice (garbler, holds threshold t)          Bob (evaluator, holds value v)
─────────────────────────────────           ──────────────────────────────

1. Garble comparison circuit C
   for "input_b >= t" where t is
   hardcoded into Alice's wire labels.
   
2. Publish intent:
   "I seek someone satisfying a
    private predicate. Protocol:
    GarbledComparison.
    circuit_commitment = H(C)"
                                    ──────>
                                            3. Bob sees intent, decides
                                               to engage. Sends ephemeral
                                               pubkey for OT.
                                    <──────

4. Send garbled circuit C to Bob.
   Send Alice's input labels
   (for threshold bits -- these
   encode t without revealing it).
                                    ──────>

5. OT protocol (31 rounds or batched):
   Alice is OT sender for each bit i:
     messages = (label_0[i], label_1[i])
   Bob is OT receiver with choice = v[i]
                                    <────>
                                            6. Bob now holds:
                                               - The garbled circuit C
                                               - Alice's input labels (for t)
                                               - His input labels (for v)
                                               via OT

                                            7. Evaluate C gate by gate.
                                               Learn output label.
                                               Decode: pass (v >= t) or fail.

                                            8. Generate STARK proof:
                                               GarbledEvalAir proves
                                               correct evaluation with
                                               output = 1.

                                    <──────
                                            9. Send proof to Alice (and/or
                                               publish for third-party
                                               verification).

10. Alice verifies:
    - STARK proof checks out
    - circuit_commitment matches
      her garbled circuit
    - Output decoding matches "1"
    
    Result: Alice is convinced
    Bob's value >= her threshold,
    without learning Bob's value.
```

---

## 6. Cost Analysis

### 6.1 Communication Costs

| Approach | Total bytes | Rounds | Latency |
|----------|------------|--------|---------|
| **Public threshold (current)** | ~1 KB (proof only) | 1 | 1 RTT |
| **Garbled circuit (this doc)** | ~7 KB (GC + OT + proof) | 3 | 2-3 RTT |
| **MPC-in-the-head** | ~50-200 KB | 1-2 | 1-2 RTT |
| **Generic 2PC (GMW)** | ~100+ KB | O(depth) | Many RTT |

### 6.2 Computation Costs

| Operation | Time (estimated) | Where |
|-----------|-----------------|-------|
| Garble circuit (Alice) | ~1 ms | 62 Poseidon2 calls (4 per gate) |
| OT base phase (both) | ~5 ms | 128 X25519 scalar mults |
| OT extension (both) | ~1 ms | 31 hash evaluations |
| Evaluate garbled circuit (Bob) | ~1 ms | 62 Poseidon2 calls |
| Generate STARK proof (Bob) | ~200-500 ms | GarbledEvalAir over ~3000 rows |
| Verify STARK proof (Alice/anyone) | ~10-20 ms | FRI verification |

**Total wall-clock time**: ~500 ms (dominated by STARK proof generation).

Compare to:
- Current `PredicateAir` proof generation: ~50-100 ms (but requires public threshold)
- MPC-in-the-head proof: ~2-5 seconds
- Full garbled circuit without STARK: ~10 ms (but not publicly verifiable)

### 6.3 Proof Sizes

| Approach | Proof size | Publicly verifiable? |
|----------|-----------|---------------------|
| PredicateAir (public threshold) | ~20 KB | Yes |
| GarbledEvalAir (this design) | ~30-50 KB | Yes |
| MPC-in-the-head | ~100-200 KB | Yes |
| Plain garbled circuit (no STARK) | 0 (not a proof) | No -- only Bob is convinced |

### 6.4 Security Parameters

- **Computational security**: 128-bit (from X25519 CDH assumption for OT)
- **Statistical security**: 124-bit (from BabyBear4 extension field for STARK)
- **Post-quantum status**: The STARK proof is post-quantum (hash-based). The OT
  protocol is NOT post-quantum (relies on X25519 CDH). For PQ security, the OT
  would need to be replaced with lattice-based OT (e.g., from Module-LWE).
  See `docs/pq-roadmap.md` for the broader PQ migration plan.

---

## 7. Comparison to Alternative Approaches

### 7.1 Committed-Threshold Approach (from private-predicates.md Section 4.1)

**How it works**: Alice commits to threshold `C_t = Poseidon2(t, r)`. Later, Alice
reveals `t` to Bob via a private channel. Bob generates a standard `PredicateAir`
proof. Alice verifies the proof's threshold matches her commitment.

**Advantages over garbled circuits**:
- Simpler (no OT, no garbling, no new AIR)
- Faster (standard PredicateAir proof: ~50 ms)
- Smaller proofs (~20 KB)

**Disadvantages**:
- Bob LEARNS the threshold (even temporarily). If this is unacceptable (competitive
  thresholds, auction reserves), the committed approach fails.
- No third-party verifiability without revealing the threshold eventually.

**When to use**: When the threshold can be revealed to the prover after the fact
(e.g., credit checks where the threshold is not competitively sensitive).

### 7.2 MPC-in-the-Head (Ishai et al. 2007, Banquet 2021)

**How it works**: The prover simulates a multi-party protocol "in their head,"
commits to the views of all simulated parties, and opens a random subset for
verification. If the opened views are consistent, the computation was honest.

**Advantages over garbled circuits**:
- Non-interactive (after Fiat-Shamir transform)
- No OT required
- Naturally produces STARK-compatible proofs

**Disadvantages**:
- Proof size: 5-10x larger than garbled circuit + STARK approach
- Prover time: 5-10x slower (must simulate multiple parties)
- More complex implementation (VOLE commitments, consistency checks)
- Research-grade: no production implementations for BabyBear arithmetic

**When to use**: When non-interactivity is essential (asynchronous protocols where
parties cannot be online simultaneously) or when the OT round-trip is unacceptable.

### 7.3 Homomorphic Encryption (FHE/Leveled HE)

**How it works**: Alice encrypts her threshold under FHE. Bob homomorphically
evaluates the comparison circuit on the ciphertext. The result is still encrypted;
Alice decrypts to learn pass/fail.

**Advantages**:
- Bob never sees the threshold (even encrypted wire labels leak timing)
- Supports arbitrary computation depth (with bootstrapping)

**Disadvantages**:
- Ciphertext expansion: ~1000x (a 4-byte threshold becomes ~4 KB encrypted)
- Computation: ~1000x slower than plaintext
- No obvious STARK integration (FHE ciphertexts are over different fields)
- Not post-quantum without lattice-based FHE (which we'd need anyway for PQ OT)

**When to use**: When neither party should learn anything (not even a 1-bit output)
until a trusted decryptor reveals it. Overkill for pyana's current use cases.

### 7.4 Decision Tree: "I Want Private Two-Party Computation"

```
Q: Can the threshold/predicate be revealed to the prover?
├── YES: Use committed-threshold approach (simple, fast, proven)
│         → PredicateAir with prior commitment, reveal at proof time
│
└── NO: The prover must not learn the exact predicate.
    │
    Q: Must the protocol be non-interactive?
    ├── YES: Use MPC-in-the-head
    │         → Larger proofs, slower, but single-message
    │
    └── NO: Interactive (2-3 rounds) is acceptable.
        │
        Q: Is the computation a simple comparison (>=, <=, range)?
        ├── YES: Use garbled circuits (this document)
        │         → ~7 KB communication, ~500 ms, 30-50 KB proof
        │
        └── NO: Arbitrary function (not just comparison).
            │
            Q: How complex is the function?
            ├── SMALL (<1000 gates): Garbled circuits still work
            │   → Scale linearly: 1000 gates ≈ 32 KB GC, ~2s proof
            │
            └── LARGE (>1000 gates): Consider MPC-in-the-head or
                hybrid approaches (garbled outer circuit + STARK
                inner proofs for expensive sub-computations)
```

---

## 8. Limitations and Mitigations

### 8.1 One-Time Use

Garbled circuits are inherently one-time-use. The security of Yao's protocol relies
on each garbled table entry being decryptable only once. If the same garbled circuit
is reused with different inputs, the evaluator can learn the garbler's input.

**Impact on pyana**: For repeated interactions (same threshold, many different values),
Alice must generate a fresh garbled circuit each time.

**Mitigation strategies**:

1. **Batch garbling**: Alice pre-generates N garbled circuits for the same function
   but different randomness. Cost: N * 3 KB storage. Amortizes garbling computation.

2. **Cut-and-choose for reusability**: Alice generates 2N circuits, Bob randomly
   selects N to open (verifying correctness), evaluates the remaining N. This gives
   security against a malicious garbler but still requires O(N) garbled circuits.

3. **Switch to committed-threshold after first interaction**: Once a relationship
   is established, the parties can switch to a simpler protocol where the threshold
   is revealed under NDA/contract and standard PredicateAir proofs are used going
   forward.

4. **Garbled RAM / ORAM**: For repeated evaluations of the same function with
   different inputs, garbled RAM constructions exist but are ~100x more expensive.
   Not recommended for pyana.

### 8.2 Malicious Security

The basic Yao protocol is secure against semi-honest (honest-but-curious) adversaries.
For malicious security (a cheating garbler who creates an incorrect circuit):

**Threat**: Alice garbles a circuit that always outputs "1" regardless of Bob's input.
Bob would generate a STARK proof of "correct evaluation" that verifies, but the
underlying computation is wrong.

**Mitigation**:

1. **Circuit commitment**: Alice publishes a commitment to the PLAINTEXT circuit
   (the boolean function) alongside the garbled circuit. The STARK can additionally
   prove that the garbled circuit is consistent with the committed plaintext circuit.
   Cost: +1 hash per gate in the STARK.

2. **Dual-execution**: Both parties garble the same circuit; they cross-check outputs.
   If outputs differ, someone cheated. Cost: 2x communication, 2x computation.

3. **Authenticated garbling** (Wang-Ranellucci-Katz 2017): Information-theoretic
   MACs on wire labels detect cheating. Adds ~50% communication overhead.

For pyana's use cases (where Alice's circuit commitment is public and the circuit
topology is a well-known comparison), option (1) suffices and is cheap.

### 8.3 Communication Overhead vs. Local Proofs

Current PredicateAir proofs are entirely local (Bob generates a proof offline).
Garbled circuits require interaction:

| | PredicateAir | Garbled Circuit |
|---|---|---|
| **Rounds** | 0 (offline) | 2-3 |
| **Online time** | 0 | ~50 ms (network) |
| **Offline time** | ~50 ms (proof gen) | ~500 ms (proof gen) |
| **Parties online simultaneously?** | No | Yes (for OT) |

**Mitigation**: Use the async OT variant where OT messages are queued via the
gossip layer. Bob's OT choices are sent as a sealed message; Alice's OT responses
are sent back. Total latency: 2 gossip hops (typically sub-second in federation).

### 8.4 Bit-Length Limitations

The comparison circuit is parameterized by bit width. BabyBear values are 31 bits,
so the standard circuit handles values in `[0, 2^31 - 2^27]`. For larger values
(e.g., 64-bit balances), the circuit doubles in size:

| Bit width | AND gates | GC size | OT count | Proof time |
|-----------|----------|---------|----------|-----------|
| 31 (BabyBear) | 62 | ~2 KB | 31 | ~300 ms |
| 64 | 128 | ~4 KB | 64 | ~600 ms |
| 128 | 256 | ~8 KB | 128 | ~1.2 s |
| 256 | 512 | ~16 KB | 256 | ~2.5 s |

For pyana, 31-bit (BabyBear native) is the natural choice. Values larger than
`p = 2013265921` (~2 billion) would need multi-limb representation, which the
existing `PredicateAir` bit-decomposition already handles via `PREDICATE_DIFF_BITS = 31`.

### 8.5 Post-Quantum Concerns

The OT protocol (Chou-Orlandi) relies on the CDH assumption on Curve25519.
A quantum computer breaks this. The STARK proof remains secure (hash-based).

**Migration path** (aligned with `docs/pq-roadmap.md`):
1. Replace X25519 OT with lattice-based OT (e.g., from Module-LWE)
2. The garbling scheme (Poseidon2-based) is already PQ-safe
3. The STARK proof is already PQ-safe
4. Net result: only the OT layer needs replacement for full PQ security

---

## 9. Extended Applications

### 9.1 Private Auction Reserve Prices

```
Seller (Alice): reserve price r (secret)
Bidder (Bob): bid b (secret)

Protocol:
1. Alice garbles circuit: "bid >= reserve"
2. Bob evaluates via OT with his bid
3. If output = 1: Bob knows his bid qualifies (without learning reserve)
4. If output = 0: Bob knows he's below reserve (without learning how far below)
5. Bob generates STARK proof of evaluation (for the auction contract)
```

**Advantage over sealed-bid**: In a sealed-bid auction, ALL bids are revealed at
close. With garbled circuits, losing bids are NEVER revealed. The auction contract
only needs to verify the STARK proof from the winning bidder.

### 9.2 Private Capability Matching

```
Service (Alice): requires capability set S (secret requirements)
Agent (Bob): holds capabilities C (secret)

Protocol:
1. Express "does C satisfy S?" as a boolean circuit
   (e.g., "for each required capability in S, check if C contains it")
2. Alice garbles the circuit with her requirements as input
3. Bob evaluates with his capabilities as input
4. Output: compatible (1) or incompatible (0)
5. STARK proof makes the match verifiable to the network
```

This enables the private intent matching described in `docs/private-predicates.md`
Section 5.3 without either party revealing their full capability/requirement set.

### 9.3 Private Range Overlap (Negotiation)

```
Buyer (Alice): willing to pay in range [L_a, H_a]
Seller (Bob): willing to sell in range [L_b, H_b]

Question: Is there overlap? (i.e., H_a >= L_b AND H_b >= L_a)

Protocol:
1. Alice garbles two comparison circuits:
   - Circuit 1: "Bob's lower bound <= Alice's upper bound"
   - Circuit 2: "Alice's lower bound <= Bob's upper bound"
2. Bob evaluates both via OT
3. Final AND: overlap exists iff both circuits output 1
4. Neither party learns the other's exact range
```

**Gate count**: 2 * 62 = 124 AND gates, ~4 KB garbled circuit, ~8 KB total
communication, ~600 ms proof generation.

---

## 10. Implementation Roadmap

### Phase 1: OT Primitive (1-2 weeks)

**Location**: `tokenizer/src/ot.rs` (new file)

```rust
// Core OT API:
pub struct OtSender { /* y, S = yG */ }
pub struct OtReceiver { /* x, choice bit */ }

impl OtSender {
    pub fn setup() -> (Self, OtSenderMessage1);  // S = yG
    pub fn transfer(&self, receiver_msg: &OtReceiverMessage,
                    m0: &[u8; 16], m1: &[u8; 16]) -> OtSenderMessage2;
}

impl OtReceiver {
    pub fn choose(sender_msg: &OtSenderMessage1, choice: bool) -> (Self, OtReceiverMessage);
    pub fn receive(&self, sender_msg: &OtSenderMessage2) -> [u8; 16];
}
```

Dependencies: `x25519_dalek` (already in `tokenizer/Cargo.toml`), `blake3` or
`chacha20poly1305` for key derivation.

### Phase 2: Poseidon2-Based Garbling (2-3 weeks)

**Location**: `circuit/src/garbled.rs` (new file)

```rust
pub struct GarbledCircuit {
    gates: Vec<GarbledGate>,      // Poseidon2-encrypted gate tables
    input_labels_a: Vec<[u128; 2]>,  // Garbler's input wire labels
    output_decoding: [u128; 2],    // Maps output label to 0/1
}

pub struct GarbledGate {
    table: [[BabyBear; 8]; 4],   // 4 entries, each 128 bits as 8 BabyBear
}

impl GarbledCircuit {
    /// Garble a comparison circuit for `evaluator_input >= garbler_threshold`.
    pub fn garble_comparison(threshold: u32, bits: usize) -> (Self, GarblingSecrets);

    /// Evaluate the garbled circuit given input labels.
    pub fn evaluate(&self, labels_a: &[[u8; 16]], labels_b: &[[u8; 16]]) -> EvalResult;
}
```

Dependencies: `poseidon2` (already in `circuit/src/poseidon2.rs`).

### Phase 3: GarbledEvalAir (3-4 weeks)

**Location**: `circuit/src/garbled_eval_air.rs` (new file)

This is the STARK AIR that proves correct evaluation of a Poseidon2-garbled circuit.
Reuses the existing Poseidon2 constraint infrastructure from `poseidon2_air.rs`.

Key design decisions:
- Trace width: ~50 columns (wire labels + Poseidon2 state + gate metadata)
- Trace height: `num_gates * poseidon2_rounds` (~62 * 24 = 1488 rows for comparison)
- Public inputs: garbled circuit commitment, output decoding key, circuit topology hash
- Private witness: all wire labels from evaluation

### Phase 4: Intent Integration (2-3 weeks)

**Location**: `intent/src/private_match.rs` (new file)

Wire the garbled circuit protocol into the intent matching flow:
- Extend `PredicateRequirement` with `GarbledComparison` variant
- Add OT message types to the gossip protocol
- Implement the 3-round handshake (intent -> OT -> proof)

### Phase 5: Malicious Security (4-6 weeks, optional)

Add circuit commitment verification to `GarbledEvalAir`:
- Alice publishes `circuit_hash = Poseidon2(plaintext_circuit_description)`
- The STARK additionally proves that the garbled tables are consistent with the
  committed plaintext circuit (each garbled entry decrypts to the correct output
  label per the truth table)

This prevents a malicious garbler from encoding a different function.

---

## 11. Open Questions

1. **Poseidon2 as garbling hash -- security analysis**: Standard garbled circuits
   use AES with circular correlation robustness. Poseidon2 has algebraic structure
   that AES lacks. Is this exploitable? Likely not for garbling (we only need
   one-wayness + domain separation), but needs formal analysis.

2. **OT extension compatibility**: IKNP-style OT extension uses a correlation-robust
   hash. If we use Poseidon2 here too, the entire protocol is STARK-friendly, but
   we need to verify that Poseidon2 satisfies the correlation robustness property.

3. **Proof composition**: Can the `GarbledEvalAir` proof be folded into an IVC
   chain? This would enable "prove I correctly evaluated a garbled circuit AND
   my value is bound to my committed state" in a single proof, rather than
   requiring composition of two separate proofs.

4. **Bandwidth in gossip**: The garbled circuit (~3 KB) + OT messages (~4 KB)
   flow through the gossip layer. Is this acceptable for high-frequency matching?
   For comparison, current intent messages are ~200-500 bytes.

5. **Timing side channels**: Does the OT protocol leak information through timing?
   In the Chou-Orlandi construction, both branches (b=0, b=1) perform the same
   operations, so timing should be constant. But the subsequent garbled circuit
   evaluation might have data-dependent timing if Poseidon2 is not constant-time
   in software. Need to verify `poseidon2.rs` is constant-time.

---

## 12. Summary

| Aspect | Garbled Circuits in Pyana |
|--------|--------------------------|
| **What it enables** | Two-party private computation (neither reveals input) |
| **Primary use case** | Class B predicates (private threshold comparison) |
| **Key building block** | Chou-Orlandi OT from existing X25519 infrastructure |
| **Innovation** | Poseidon2-based garbling for STARK-friendly evaluation proofs |
| **Communication** | ~7 KB per comparison (competitive with alternatives) |
| **Computation** | ~500 ms total (dominated by STARK proof generation) |
| **Proof size** | ~30-50 KB (publicly verifiable, post-quantum STARK) |
| **Security** | 128-bit computational (OT) + 124-bit statistical (STARK) |
| **PQ status** | STARK is PQ; OT needs lattice migration (per pq-roadmap.md) |
| **Limitation** | One-time use per garbled circuit; interactive (2-3 rounds) |
| **Implementation effort** | ~10-14 weeks for full stack (OT + garbling + AIR + intent) |
| **Dependencies** | x25519_dalek (have it), poseidon2 (have it), new AIR (build it) |

The garbled circuit approach fills a specific gap in pyana's privacy stack: cases
where the committed-threshold approach leaks too much (the prover would learn the
threshold) but full MPC-in-the-head is too expensive. It is the natural next step
after the existing `PredicateAir` and `CompoundPredicateAir` for two-party private
computation in the intent matching and capability verification flows.
