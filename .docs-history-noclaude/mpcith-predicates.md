# MPC-in-the-Head for Private Threshold Predicates

## Overview

This document specifies a protocol for **private threshold predicates**: proving that a
secret value satisfies a secret threshold, where neither party reveals their input to the
other. The result is a single bit (pass/fail) backed by a STARK proof.

The core insight is that MPC-in-the-Head (MPCitH) allows us to express a two-party
comparison as a STARK-friendly trace, giving us verifiability by third parties who know
neither the value nor the threshold.

---

## 1. What is MPC-in-the-Head?

MPC-in-the-Head (Ishai, Kushilevitz, Ostrovsky, Sahai 2007) is a zero-knowledge proof
paradigm where:

1. The prover **simulates** an N-party MPC protocol locally (in their head).
2. They **commit** to each simulated party's view (random tape + received messages).
3. The verifier **challenges**: "open K of the N parties' views."
4. The prover reveals those views; the verifier checks that the opened views are
   internally consistent with each other and with the protocol specification.

**Why it works**: If the prover committed honestly (ran the real protocol on the real
input), all views are consistent. If the prover cheated (used a different input), at
least one pair of views will be inconsistent. Since the prover committed before knowing
which views would be opened, they cannot "patch" inconsistencies.

**Soundness**: With N parties and K openings, the soundness error per round is
approximately `(N choose K-1) / (N choose K)`. For N=256, K=57 (Banquet parameters),
this gives ~128-bit security in a single round.

**Extensions**:
- KKW (Katz, Kolesnikov, Wang 2018): Optimized for binary circuits, uses OT-based MPC.
- Banquet (Baum et al. 2021): Uses MPC over algebraic structures (fields), STARK-friendly.
- Limbo (2023): VOLE-based commitments, fastest current construction.

---

## 2. Why MPCitH for Private Thresholds?

The comparison `value >= threshold` is a two-input function where each input belongs to a
different party:
- **Prover** holds `value` (e.g., credit score 750)
- **Verifier** holds `threshold` (e.g., hiring bar 700)

Requirements:
- Neither party learns the other's input.
- Both learn the comparison result (1 bit).
- A third-party auditor (who knows neither input) can verify the proof.

Alternatives and why MPCitH is preferred:

| Approach | Prover learns threshold? | Verifier learns value? | Third-party verifiable? | STARK-native? |
|----------|-------------------------|----------------------|------------------------|---------------|
| Committed threshold (Approach 1) | Yes (acceptable for many use cases) | No | Yes | Yes |
| Garbled circuits | No | No | No (one-time) | No |
| Bulletproofs | Yes (range revealed) | No | Yes | No (curve-based) |
| FHE comparison | No | No | Costly | No |
| **MPCitH (full)** | **No** | **No** | **Yes** | **Yes** |

MPCitH is the only approach that simultaneously achieves: no input leakage to either
party, third-party verifiability, and native STARK compatibility.

---

## 3. The Comparison Circuit: `a >= b` with Shared Inputs

### 3.1 Arithmetic Formulation

Over BabyBear (p = 2^31 - 2^27 + 1), the comparison `a >= b` is equivalent to:
- Compute `diff = a - b`
- Check that `diff` has a valid bit decomposition with the high bit (bit 30) equal to 0

This is the same technique used in `PredicateAir`, but now the inputs are shared.

### 3.2 Secret Sharing

Using additive secret sharing with N=3 parties:

```
a = a_1 + a_2 + a_3   (mod p)
b = b_1 + b_2 + b_3   (mod p)
```

The prover secret-shares their value `a` into 3 shares. The verifier's threshold `b` is
similarly shared (the verifier provides shares to the prover via the commitment protocol,
or the prover uses shares derived from the verifier's commitment).

### 3.3 Shared Subtraction

Subtraction is linear and thus free in secret-shared form:
```
diff_i = a_i - b_i   for each party i
diff = diff_1 + diff_2 + diff_3 = a - b
```

### 3.4 Shared Bit Decomposition

This is the non-trivial step. Bit decomposition is non-linear, requiring communication
between parties. The protocol:

1. Each party holds a share of `diff`.
2. Parties jointly compute shares of each bit `d_0, d_1, ..., d_30` such that
   `sum(d_k * 2^k) = diff`.
3. The bit decomposition uses a carry-propagation circuit:
   - For each bit position k, parties compute shared carries `c_k`.
   - `d_k = (diff >> k) XOR c_{k-1}` (shared XOR via degree-2 multiplication).

The MPC protocol for bit decomposition with N=3 parties requires O(30) rounds of
communication (one per bit, or O(log 30) with parallel prefix).

### 3.5 Final Check

After shared bit decomposition, the parties hold shares of bit 30 (the sign bit).
The output is: `result = 1 - d_30` (pass if high bit is 0).

---

## 4. STARK Trace Layout for MPCitH

The simulation trace captures all party states and communications:

### 4.1 Trace Columns

```
Columns 0-7:    party_1_state[8]     (party 1's internal state: shares, intermediates)
Columns 8-15:   party_2_state[8]     (party 2's internal state)
Columns 16-23:  party_3_state[8]     (party 3's internal state)
Columns 24-31:  communication[8]     (broadcast messages between parties)
Columns 32-33:  control[2]           (round counter, operation selector)
Column  34:     commitment_check     (running Poseidon2 state for view commitments)
```

Total trace width: 35 columns.

### 4.2 Trace Rows

Each row represents one round of the MPC protocol:

| Row | Operation |
|-----|-----------|
| 0 | Input sharing: commit party shares of `a` |
| 1 | Input sharing: commit party shares of `b` |
| 2 | Subtraction: compute `diff_i = a_i - b_i` per party |
| 3-33 | Bit decomposition rounds (one per bit position) |
| 34 | Output reconstruction: reveal shares of `d_30` |
| 35 | Final: compute result = 1 - d_30 |

Total: 36 rows (padded to 64 for FFT efficiency).

### 4.3 AIR Constraints

1. **Share consistency**: `party_1_state[0] + party_2_state[0] + party_3_state[0]` equals
   the committed input (for input rows).

2. **Subtraction correctness**: Each party's diff share equals their `a` share minus their
   `b` share.

3. **Communication consistency**: Messages sent by party `i` in round `r` equal messages
   received by parties `j != i` in round `r+1`.

4. **Bit extraction correctness**: The carry-propagation logic is correct at each bit
   position (degree-2 constraint per bit).

5. **High bit check**: The reconstructed bit 30 equals zero (pass) or non-zero (fail).

6. **Commitment binding**: View commitments match the opened views (Poseidon2 hashing
   of party state + communication = commitment).

---

## 5. Commitment / Opening Protocol

### 5.1 Full MPCitH Protocol (3 rounds)

**Round 1 (Prover -> Verifier)**:
1. Prover selects random tapes for all N parties.
2. Prover simulates the full MPC protocol.
3. Prover computes view commitments: `C_i = Poseidon2(tape_i, messages_i)` for each party.
4. Prover sends: `{C_1, ..., C_N, result_bit}`.

**Round 2 (Verifier -> Prover)**:
1. Verifier contributes their threshold via share distribution.
2. Verifier challenges: "open parties S = {i_1, ..., i_K}".

**Round 3 (Prover -> Verifier)**:
1. Prover reveals: `{tape_j, messages_j}` for all `j in S`.
2. Verifier checks:
   - Each opened view is consistent with the protocol.
   - Opened views are mutually consistent (messages match).
   - Commitments match: `C_j == Poseidon2(tape_j, messages_j)`.
   - The unopened parties' contributions are consistent with the result.

### 5.2 Fiat-Shamir (Non-interactive)

For STARK integration, the protocol is made non-interactive via Fiat-Shamir:
- The challenge is derived as `challenge = BLAKE3(C_1 || ... || C_N || result_bit)`.
- The entire protocol becomes a single message (the STARK proof).

### 5.3 STARK Wrapping

The STARK proof encompasses:
- **Public inputs**: `[prover_value_commitment, verifier_threshold_commitment, result_bit]`
- **Private witness**: The full MPC simulation trace (party states, random tapes, messages)
- **What the STARK proves**: "The MPC protocol was simulated honestly, the opened views
  are consistent, and the result bit correctly reflects `a >= b`."

---

## 6. Security Analysis

### 6.1 What the Verifier Learns

- The 1-bit result (pass/fail).
- The prover's value commitment (Poseidon2 hash — reveals nothing about the value).
- The STARK proof itself (zero-knowledge by the STARK's ZK property).

**The verifier does NOT learn**: the prover's actual value, beyond the binary pass/fail.

### 6.2 What the Prover Learns

- The result bit (pass/fail).
- The verifier's threshold commitment (Poseidon2 hash — reveals nothing about threshold).

**The prover does NOT learn**: the verifier's actual threshold, beyond the binary result.
(Note: the prover can binary-search the threshold by running the protocol multiple times
with different claimed values. This is inherent to any comparison protocol and can be
mitigated by rate-limiting or requiring stake per proof attempt.)

### 6.3 Soundness

- **STARK soundness**: 128-bit computational soundness (BabyBear4 extension field).
- **MPCitH soundness**: For N=256 parties with K=57 openings, `< 2^{-128}` forgery
  probability per round.
- **Combined**: A cheating prover must simultaneously break the STARK (forge an accepting
  proof for a false trace) AND produce consistent views for randomly chosen parties.

### 6.4 Zero-Knowledge

- The STARK is zero-knowledge (proven for FRI-based STARKs with sufficient blowup).
- The unopened party views reveal nothing (they are random from the verifier's perspective).
- The opened party views, combined with the STARK's ZK, leak no information beyond the
  result bit.

### 6.5 Third-Party Verification

A third party who sees only:
- `prover_value_commitment`
- `verifier_threshold_commitment`
- `result_bit`
- The STARK proof

can verify that the comparison was performed correctly. They learn nothing about the
actual values — only that the committed inputs produce the claimed result.

---

## 7. Cost Estimates

### 7.1 Trace Dimensions

| Parameter | Value |
|-----------|-------|
| Trace width | 35 columns |
| Trace rows | 64 (padded from 36) |
| Field | BabyBear (31-bit) |
| Extension degree | 4 (for 128-bit security) |

### 7.2 Proof Size

Using FRI with blowup factor 8:
- Merkle commitment: `35 * 4 * 6_levels = 840` field elements
- FRI layers: ~6 layers * 64 queries * 4 elements = 1536 field elements
- Opening proofs: 64 queries * 35 columns * log(64) = ~13,440 bytes
- **Total estimated proof size: ~20-30 KiB**

### 7.3 Proving Time

- Trace generation: ~0.1 ms (36 rows * 35 columns, simple arithmetic)
- FFT (Reed-Solomon): ~1 ms (64-point FFT over 35 columns)
- FRI commitment: ~5 ms (Merkle tree construction)
- FRI queries + openings: ~3 ms
- **Total proving time: ~10-15 ms** (comparable to existing `PredicateAir` at ~5-8 ms)

### 7.4 Verification Time

- Recompute Fiat-Shamir challenge: ~0.05 ms
- Verify FRI: ~2 ms (64 queries, 6 layers)
- Check public inputs: ~0.01 ms
- **Total verification time: ~2-3 ms**

---

## 8. Comparison to Alternatives

| System | Proof size | Proving time | Threshold hidden? | Post-quantum? | STARK-native? |
|--------|-----------|-------------|-------------------|---------------|---------------|
| PredicateAir (current) | ~8 KiB | ~5 ms | No (public input) | Yes | Yes |
| **Committed threshold** | ~10 KiB | ~7 ms | From 3rd parties only | Yes | Yes |
| Bulletproofs | ~0.7 KiB | ~30 ms | No | No | No |
| Garbled circuits | ~100 KiB | ~50 ms | Yes | No | No |
| FHE comparison | ~1 MiB | ~10 s | Yes | Yes | No |
| **Full MPCitH STARK** | ~25 KiB | ~15 ms | Yes | Yes | Yes |

The committed-threshold approach (Approach 1) is the pragmatic middle ground: it hides
the threshold from third-party verifiers while allowing the prover to learn it. For use
cases where the prover must NOT learn the threshold, the full MPCitH construction is
required.

---

## 9. Committed-Threshold Protocol (Approach 1, Implemented)

This is the immediately practical protocol, implemented in `circuit/src/committed_threshold.rs`.

### 9.1 Protocol

1. Verifier generates blinding randomness `r` and computes:
   `threshold_commitment = Poseidon2(threshold, r)`

2. Verifier sends `threshold_commitment` and `threshold` to the prover (via secure channel).

3. Prover generates a STARK proving:
   - `value >= threshold` (via bit decomposition, same as PredicateAir)
   - `Poseidon2(threshold, blinding) == threshold_commitment` (binding)
   - `value` is bound to a specific fact via `fact_commitment`

4. Public inputs: `[threshold_commitment, fact_commitment]`
   - Neither the value NOR the threshold is revealed to third parties.
   - Both are in the private witness.

5. Verifier checks: proof verifies, and `threshold_commitment` matches their secret.

### 9.2 Privacy Properties

- **Third-party verifiers** see only `threshold_commitment` and `fact_commitment`.
  They learn: "some committed value satisfies some committed threshold" (1 bit).
- **Prover** learns the threshold (acceptable for credit checks, hiring bars, etc.).
- **Verifier** learns only pass/fail (same as standard PredicateAir).

### 9.3 Advantages over Standard PredicateAir

The standard `PredicateAir` has `threshold` as a public input — anyone inspecting the
proof sees the exact threshold value. With committed-threshold:
- A lender's risk threshold stays private from auditors inspecting the proof.
- An employer's hiring bar stays private from compliance reviewers.
- The proof remains fully verifiable despite hiding both inputs.

---

## 10. Future Work: Full MPCitH Implementation

The full MPCitH construction (Approach 2) would:
1. Add a `MpcComparisonAir` with the 35-column trace layout described in Section 4.
2. Implement the carry-propagation bit decomposition as shared arithmetic.
3. Add VOLE-based commitments for party views (Limbo-style, for efficiency).
4. Integrate with the Fiat-Shamir transcript used by the existing STARK prover.

Estimated effort: 3-6 months of research + implementation.

Prerequisite: The committed-threshold protocol (Approach 1) serves all practical use
cases in the near term. Full MPCitH becomes necessary only when the prover must NOT
learn the threshold — a requirement that arises primarily in adversarial auctions and
competitive hiring markets.
