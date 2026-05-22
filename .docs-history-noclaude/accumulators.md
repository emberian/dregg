# Cryptographic Accumulators for Pyana

## Status: Design Exploration

## Problem Statement

Pyana currently proves set membership and non-membership using 4-ary Poseidon2 Merkle trees (depth 16, BabyBear field). While sound, this approach has three scaling limitations:

1. **Proof size is O(log N)**: A membership proof contains 16 levels of 3 sibling hashes each (48 field elements). For non-membership, we need TWO such paths (left and right neighbor), plus adjacency metadata -- totaling ~100 field elements per non-membership proof.

2. **Non-membership is complex**: The `non_revocation_air.rs` sorted-Merkle approach requires finding adjacent leaves in a sorted tree, proving membership of BOTH neighbors, and enforcing ordering constraints. The AIR has 12 columns and degree-4 constraints. For 8 ancestors, this is 8 * (1 + 2*4) = 72 trace rows.

3. **Dynamic updates are expensive**: When the revocation set changes (a capability is revoked), every holder with an existing non-revocation proof must obtain new Merkle paths. The federation must redistribute O(N) witnesses whenever the tree mutates.

Cryptographic accumulators can reduce some or all of these costs to O(1).

---

## Survey of Accumulator Types

### 1. RSA Accumulator

**Construction**: Given an RSA modulus N = p*q (factorization unknown), a generator g, and a set S = {e_1, ..., e_n} of prime representatives:

```
Acc = g^(e_1 * e_2 * ... * e_n) mod N
```

**Membership witness** for e_i: `w_i = g^(product of all e_j, j != i) mod N`
- Verification: `w_i^e_i == Acc mod N`
- Size: O(1) -- one RSA group element (256 bytes at 2048-bit security)

**Non-membership witness** for e (not in S): Bezout coefficients (a, d) such that `a*e + d*(product of all e_i) = 1`:
- Verification: `w^e * Acc^d == g mod N` where w = g^a
- Size: O(1)

**Applicability to pyana**:
- Excellent for revocation non-membership (O(1) witnesses, O(1) updates)
- Each capability maps to a prime via deterministic hashing (hash-to-prime)
- Updates: when e_new joins the set, `Acc_new = Acc_old^e_new`. Existing witnesses unaffected for membership; non-membership witnesses need update.

**Fatal limitation**: RSA arithmetic (2048-bit modular exponentiation) inside a BabyBear STARK is prohibitively expensive. A single 2048-bit modexp requires ~O(2048^2) = ~4M multiplications in the big-integer domain, each requiring ~65 BabyBear multiplications. Total: ~260M constraints for ONE verification. This is 3-4 orders of magnitude more expensive than our current Merkle approach.

**Verdict**: Not viable for in-circuit verification. Could work as an off-chain optimization where the accumulator is verified outside the STARK (e.g., in the on-chain verifier contract), but this breaks our "single-proof" architecture.

### 2. Bilinear Accumulator (KZG-based)

**Construction**: Given a KZG setup (tau, [g^tau^i], [h^tau^i]) and a set S = {e_1, ..., e_n}:

Define the characteristic polynomial: `f(x) = (x - e_1)(x - e_2)...(x - e_n)`

```
Acc = [f(tau)]_1 = commit_g1(f)
```

**Membership witness** for e_i: The quotient polynomial q(x) = f(x)/(x - e_i):
- `w_i = [q(tau)]_1`
- Verification: `e(w_i, [tau - e_i]_2) == e(Acc, [1]_2)`
- Size: O(1) -- one G1 point (48 bytes compressed on BLS12-381)

**Non-membership witness** for e (not in S): Polynomial division with remainder:
- `f(x) = q(x)(x - e) + f(e)` where f(e) != 0
- Witness: `(w, f(e))` where `w = [q(tau)]_1`
- Verification: `e(Acc, [1]_2) == e(w, [tau - e]_2) * e([1]_1, [1]_2)^f(e)`
- Size: O(1) -- one G1 point + one scalar

**Applicability to pyana**:
- We already have KZG infrastructure in `hints/src/kzg.rs` with BLS12-381
- We already have the Ethereum trusted setup loaded via `eth_setup()`
- The `GlobalData` structure contains `powers_of_g` and `powers_of_h` up to degree 64
- Membership/non-membership witnesses are constant-size (48 bytes each)
- Updates: Adding e_new requires recomputing `Acc_new = Acc_old * [(tau - e_new)]_1` via MSM. Existing witnesses must be updated: `w_i_new = w_i * [(tau - e_new)/(tau - e_i)]_1`. This is O(1) per witness holder if they know the update delta.

**Limitation for in-STARK use**: Pairing verification cannot be done inside a BabyBear STARK efficiently. BLS12-381 pairings require ~2M constraints in a SNARK. However, this is irrelevant for our architecture: the accumulator verification happens at the OUTER verification layer (the federation's BLS threshold signature already uses BLS12-381), not inside the STARK.

**Key insight**: We can use a hybrid architecture:
1. The STARK proves "I know my capability's derivation path" (private)
2. The accumulator proves "none of my ancestors are revoked" (verified via pairing, outside STARK)
3. The federation attests to both simultaneously

**Verdict**: Strong candidate for the revocation use case. Leverages existing infrastructure. Requires architectural change to move non-revocation from "inside STARK" to "beside STARK."

### 3. Poseidon-Field-Native Accumulator (STARK-friendly)

Since RSA and pairings are expensive inside STARKs, we need an accumulator that operates natively in BabyBear.

#### 3a. Multiplicative Hash Accumulator

**Construction**: Map each element to a field element via Poseidon2, then accumulate multiplicatively:

```
Acc = product(Poseidon2(e_i) + r) for all e_i in S
```

where r is a random challenge (bound to the set via Fiat-Shamir).

**Membership witness** for e_i: `w_i = Acc / (Poseidon2(e_i) + r)`
- Verification: `w_i * (Poseidon2(e_i) + r) == Acc`
- Size: O(1) -- one BabyBear element (4 bytes)

**Non-membership**: Not directly supported. The multiplicative accumulator over a finite field does not have a natural non-membership proof because an adversary can always compute the "witness" for a fake element by dividing Acc by the target value.

**Security issue**: In a prime field, any party who knows Acc can compute `Acc / (Poseidon2(e) + r)` for ANY e, producing a valid-looking "membership witness." This means the accumulator is NOT hiding -- it requires trust in the accumulator maintainer.

**Fix -- commitment-based approach**: The accumulator is maintained by the federation (trusted to not forge membership), and the witness is accompanied by a STARK proof of correct computation:
- Prover demonstrates inside the STARK: "I computed w = Acc / (H(my_cap) + r) using the public Acc and my private capability"
- This proves knowledge of the preimage without revealing it
- But the non-membership problem remains unsolved

**Verdict**: Useful for membership (if we trust the accumulator maintainer), not useful for non-membership. Since our primary need is non-membership (proving non-revocation), this is insufficient alone.

#### 3b. Polynomial-Evaluation Accumulator (STARK-native)

**Construction**: Represent the set as roots of a polynomial over the BabyBear extension field:

```
f(x) = (x - h_1)(x - h_2)...(x - h_n) where h_i = Poseidon2(e_i)
```

The accumulator is the polynomial's evaluation at a random point alpha (derived via Fiat-Shamir from the set commitment):

```
Acc = f(alpha) = (alpha - h_1)(alpha - h_2)...(alpha - h_n)
```

**Membership witness** for h_i: `w_i = f(alpha) / (alpha - h_i) = product(alpha - h_j, j != i)`
- Verification: `w_i * (alpha - h_i) == Acc`
- Size: O(1) -- one BabyBear element

**Non-membership witness** for h (not in S): Since f(h) != 0, compute:
- `q(x) = f(x) / (x - h)` has a remainder `f(h)`
- Witness: `(w, v)` where `w = q(alpha)` and `v = f(h)`
- Verification: `w * (alpha - h) + v == Acc` AND `v != 0`
- Size: O(1) -- two BabyBear elements

**STARK-friendliness**: Verification is a single multiplication + addition + nonzero check, all native BabyBear operations. The entire verification is ~3 constraints.

**Security analysis**:
- The Schwartz-Zippel lemma gives us security: for a polynomial of degree n over a field of size p, the probability of a false positive at a random point is n/p.
- BabyBear: p ~ 2^31. For a revocation set of size n = 2^16, the false-positive probability per random challenge is 2^16 / 2^31 = 2^{-15}.
- This is INSUFFICIENT for cryptographic security.

**Fix -- extension field**: Use BabyBear^4 (the quartic extension, ~2^124 elements):
- False-positive probability: 2^16 / 2^124 = 2^{-108}. Acceptable.
- Plonky3 already uses BabyBear^4 for FRI. Our STARK infrastructure supports it.
- Verification in-circuit: 1 extension-field multiplication (16 base multiplications) + 1 extension-field addition (4 base additions) + 1 nonzero check (~4 constraints for inverse witness).
- Total: ~25 constraints for non-membership verification. Compare to current sorted-Merkle: ~72 rows * 12 columns * several constraints = thousands of constraint evaluations.

**Update cost**: When a new element h_new is added to the set:
- `Acc_new = Acc_old * (alpha - h_new)` -- O(1)
- Existing membership witnesses: `w_i_new = w_i * (alpha - h_new)` -- O(1) per holder
- Existing non-membership witnesses: `w_new = w_old * (alpha - h_new) + v_old / (alpha - h)` -- wait, this doesn't quite work. The quotient changes.

Actually, for non-membership witnesses under update (adding h_new to S):
- New polynomial: `f_new(x) = f_old(x) * (x - h_new)`
- New non-membership of h: `f_new(h) = f_old(h) * (h - h_new)`, so `v_new = v_old * (h - h_new)`
- New quotient: `q_new(alpha) = (f_new(alpha) - f_new(h)) / (alpha - h) = (Acc_old * (alpha - h_new) - v_old * (h - h_new)) / (alpha - h)`
- This can be computed from `w_old, v_old, Acc_old, h_new, alpha, h` -- all known to the witness holder.
- Cost: O(1) per update per witness holder.

**The alpha binding problem**: alpha must be deterministically derived from the set commitment (otherwise the accumulator is malleable). Options:
1. alpha = Poseidon2(Merkle_root_of_sorted_set) -- but this recreates the Merkle tree dependency
2. alpha = Poseidon2(sequential_hash_of_all_insertions) -- append-only log commitment
3. alpha = Poseidon2(epoch_counter || federation_signature) -- epoch-based with federation attestation

Option 3 is cleanest for pyana: the federation already produces attested roots each epoch. alpha is derived from the attested state, and all witnesses are epoch-bound.

**Verdict**: Most promising for in-STARK non-membership. Requires BabyBear^4 extension field arithmetic (already available in our STARK backend). Dramatically reduces constraint count vs. sorted-Merkle.

### 4. Comparison Matrix

| Property | Sorted Merkle (current) | RSA | Bilinear (KZG) | Poly-Eval (BB^4) |
|----------|------------------------|-----|----------------|------------------|
| Membership proof size | 48 field elements | 256 bytes | 48 bytes | 4 ext. field elements (16 bytes) |
| Non-membership proof size | ~100 field elements | 512 bytes | 96 bytes | 8 ext. field elements (32 bytes) |
| In-STARK verification cost | ~2000 constraints | ~260M constraints | N/A (pairing) | ~25 constraints |
| Update (holder cost) | Re-fetch Merkle path | O(1) multiply | O(1) point mul | O(1) field ops |
| Update (federation cost) | Rebuild tree | O(1) modexp | O(1) MSM | O(1) field mul |
| Trusted setup | No | Yes (RSA modulus) | Yes (KZG tau) | No |
| Field-native | Yes (Poseidon2) | No | No | Yes (BabyBear^4) |
| Max set size | 4^16 ~ 4B | Unlimited | Degree of SRS | p/security margin |
| Security assumption | Poseidon2 collision resistance | Strong RSA | q-SDH | Schwartz-Zippel + Poseidon2 |

---

## Concrete Proposal: Polynomial-Evaluation Accumulator for Non-Revocation

### Architecture

```
                    Federation
                        |
            [Revocation set: {h_1, ..., h_n}]
            [Compute: f(x) = prod(x - h_i)]
            [Derive: alpha = Poseidon2(epoch || attested_state)]
            [Publish: Acc = f(alpha) in BabyBear^4]
                        |
                  Epoch Attestation
                   (BLS threshold sig)
                        |
        --------------------------------
        |              |               |
    Holder A       Holder B        Holder C
    [w_A, v_A]    [w_B, v_B]      [w_C, v_C]

    Non-membership witness:
      w = q(alpha)  -- quotient evaluation
      v = f(h)      -- remainder (must be nonzero)
    
    Verify: w * (alpha - h) + v == Acc AND v != 0
```

### Integration with Non-Revocation Circuit

The new `accumulator_non_revocation_air.rs` would replace `non_revocation_air.rs`:

**Current sorted-Merkle approach** (`non_revocation_air.rs`):
- Width: 12 columns
- Rows per ancestor: 1 + 2 * tree_depth = 9 (for depth 4)
- Total for 8 ancestors: 72 rows
- Constraint degree: 4
- Public inputs: revocation_set_root

**Proposed accumulator approach**:
- Width: 8 columns (in BabyBear^4, each "column" is 4 base columns)
- Rows per ancestor: 1
- Total for 8 ancestors: 8 rows
- Constraint degree: 2 (just a multiplication check)
- Public inputs: Acc (4 base field elements), alpha (4 base field elements)

**AIR layout** (base field width = 32 for 8 ext-field columns):

```
Row per ancestor:
  col  0..3:  h_i (ancestor hash in BabyBear^4)
  col  4..7:  w_i (quotient witness in BabyBear^4)
  col  8..11: v_i (remainder in BabyBear^4)
  col 12..15: alpha - h_i (precomputed difference)
  col 16..19: w_i * (alpha - h_i) (product)
  col 20..23: w_i * (alpha - h_i) + v_i (should equal Acc)
  col 24..27: v_i_inv (inverse of v_i, proves v_i != 0)
  col 28..31: v_i * v_i_inv (should equal 1)
```

**Constraints**:
1. `col[12..15] == alpha - col[0..3]` (extension field subtraction, degree 1)
2. `col[16..19] == col[4..7] * col[12..15]` (extension field multiplication, degree 2)
3. `col[20..23] == col[16..19] + col[8..11]` (extension field addition, degree 1)
4. `col[20..23] == Acc` (boundary constraint against public input)
5. `col[28..31] == col[8..11] * col[24..27]` (proves v != 0, degree 2)
6. `col[28..31] == (1, 0, 0, 0)` (boundary: product is extension-field one)

Total: 6 constraints per row, max degree 2. For 8 ancestors: 8 rows, 32 base-field columns.

Compare current: 12 columns, 72 rows, degree 4, with Poseidon2 hash computations INSIDE the constraints.

**Constraint reduction**: From ~5000 effective constraint evaluations to ~48. This is a **100x improvement** in prover work for the non-revocation sub-circuit.

### Performance Estimates

**Proof generation**:
- Current (sorted Merkle, 8 ancestors, depth 4): ~72 rows * 12 cols, plus Poseidon2 inside constraints. Estimated: 50-100ms on modern hardware.
- Proposed (poly-eval accumulator, 8 ancestors): 8 rows * 32 cols, simple field arithmetic. Estimated: 0.5-1ms. **50-100x faster.**

**Proof size**:
- Current: STARK proof over 72-row trace. FRI queries scale with trace size. Estimated: ~20-40 KB.
- Proposed: STARK proof over 8-row trace (padded to 8 or 16). Estimated: ~5-10 KB. **2-4x smaller.**

**Verification**:
- Current: STARK verification with 72-row boundary. Estimated: ~5ms.
- Proposed: STARK verification with 8-row boundary. Estimated: ~2ms. **2-3x faster.**

**Witness update (when revocation set changes)**:
- Current: Holder must re-fetch fresh Merkle paths from federation. O(log N) data transfer per ancestor.
- Proposed: Holder computes `w_new, v_new` from `w_old, v_old, h_new, alpha`. O(1) local computation. **No network round-trip needed** (only the new revoked element's hash must be broadcast).

**On-chain size** (public inputs):
- Current: 1 BabyBear element (revocation root) = 4 bytes.
- Proposed: 8 BabyBear elements (Acc + alpha) = 32 bytes. Slightly larger but still negligible.

### Epoch Transition Protocol

```
Epoch E:
  - Revocation set S_E = {h_1, ..., h_n}
  - alpha_E = Poseidon2(E || BLS_sig(S_E))
  - Acc_E = product(alpha_E - h_i) for all h_i in S_E

Epoch E+1 (h_{n+1} revoked):
  - S_{E+1} = S_E union {h_{n+1}}
  - alpha_{E+1} = Poseidon2(E+1 || BLS_sig(S_{E+1}))
  - Acc_{E+1} = product(alpha_{E+1} - h_i) for all h_i in S_{E+1}
  
  NOTE: alpha changes each epoch, so ALL witnesses must be recomputed.
  This is O(n) work for the federation (compute new Acc) and O(k) for each
  holder (where k = number of ancestors in their derivation path).
  
  Federation broadcasts: (epoch, alpha_{E+1}, Acc_{E+1}, delta = h_{n+1})
  Each holder locally recomputes their witnesses for the new alpha.
```

**Optimization -- fixed alpha with epoch commitments**:

Instead of changing alpha each epoch, fix alpha once during system setup:
- `alpha = Poseidon2("pyana-revocation-accumulator-v1")`
- `Acc_E = product(alpha - h_i)` for the current revocation set
- Federation signs `(epoch, Acc_E)` with BLS threshold

Now when h_{n+1} is added:
- `Acc_{E+1} = Acc_E * (alpha - h_{n+1})` -- O(1) federation update
- For holder with witness (w, v) for non-membership of h:
  - `v_new = v * (h - h_{n+1})` -- O(1)
  - `w_new = (Acc_{E+1} - v_new) / (alpha - h)` -- O(1) (division in BabyBear^4)
- **No re-fetch from federation needed. Holder only needs broadcast of h_{n+1}.**

This is the recommended approach: fixed alpha, incremental updates.

**Security of fixed alpha**: The adversary's goal is to find h* not in S such that `product(alpha - h_i) == w* * (alpha - h*) + v*` with v* = 0. This requires `alpha - h* | product(alpha - h_i)`, i.e., `alpha - h* = alpha - h_j` for some j, i.e., `h* = h_j` (which means h* IS in S). Contradiction. Security reduces to extension-field arithmetic -- no factoring needed.

### Migration Path

**Phase 1: Dual-proof period** (backward compatible)
- Federation publishes BOTH: Merkle root AND accumulator value
- Holders can use either proof mechanism
- New SDK versions generate accumulator witnesses
- Old SDK versions continue using Merkle paths
- Circuit supports both AIRs (selectable)

**Phase 2: Accumulator-preferred**
- Default to accumulator proofs
- Merkle proofs accepted but deprecated
- Monitor: ensure all active holders have migrated

**Phase 3: Merkle sunset**
- Remove sorted-Merkle non-membership from circuit
- Remove Merkle path distribution from federation protocol
- Merkle tree retained for audit/archival only

**Code changes required**:
1. `circuit/src/accumulator_non_revocation_air.rs` -- new AIR (replaces non_revocation_air.rs)
2. `circuit/src/extension_field.rs` -- BabyBear^4 arithmetic (may already exist via Plonky3)
3. `federation/src/revocation.rs` -- add accumulator maintenance alongside existing tree
4. `commit/src/accumulator.rs` -- accumulator data structure and witness operations
5. `wire/` -- protocol messages for accumulator updates
6. `sdk/` -- client-side witness update logic

### Integration with Existing KZG Infrastructure

While the polynomial-evaluation accumulator does NOT use pairings, there is a complementary role for the KZG infrastructure in `hints/`:

**Batch non-membership**: When a holder has k ancestors to prove non-revoked, they can batch all k checks into a single polynomial commitment:
- Define `g(x) = product(x - h_i)` for their k ancestor hashes
- Prove that `gcd(f, g) = 1` (no common roots = no revoked ancestors)
- This can be verified via a single KZG opening at a random point

This is an optimization for the outer verification layer (federation-side or on-chain), not for in-STARK use.

---

## Use Cases Beyond Revocation

### Federation Membership
- Current: Merkle tree of member public keys, O(log N) membership proof
- With accumulator: O(1) membership proof
- Less critical than revocation (membership set changes rarely, Merkle paths are cheap to redistribute)

### Capability Set
- Current: Capabilities encoded as Merkle tree leaves in the fact set
- With accumulator: O(1) proof of holding a capability
- Useful for presentations with many capabilities (reduce proof size from O(k * log N) to O(k))

### Nullifier Set
- Current: Nullifier uniqueness checked via sorted Merkle non-membership
- With accumulator: O(1) non-membership proof
- **Critical difference**: Nullifier set is append-only and grows monotonically. The accumulator value changes with every spend. All future spenders need fresh witnesses.
- For nullifiers, the current Merkle approach may be better because the tree structure enables efficient batch updates via subtree caching.

---

## Open Questions

1. **Extension field degree**: BabyBear^4 gives ~108 bits of security against Schwartz-Zippel collision. Is this sufficient, or should we use BabyBear^8 (~220 bits)? The cost doubles but security margin is much larger.

2. **Multi-epoch witness staleness**: If a holder goes offline for many epochs, their witness is outdated. They need the full list of revocations since their last sync to update. The federation could maintain a "revocation log" (append-only list of all revoked hashes) for catch-up.

3. **Soundness interaction with IVC**: If non-revocation proofs are folded into an IVC chain (via Nova/Protogalaxy), the accumulator verification constraints need to be IVC-friendly. The degree-2 constraints are ideal for folding.

4. **Prover knowledge requirement**: The prover must know their ancestors' hashes (to compute h_i) AND the accumulator witnesses (w_i, v_i). These must be stored in the wallet. Current Merkle approach requires storing O(log N) siblings; accumulator requires O(1) per ancestor. This is a storage improvement.

5. **Quantum resistance**: The polynomial-evaluation accumulator's security relies on the difficulty of finding roots of a high-degree polynomial at a specific evaluation point. This is information-theoretic (Schwartz-Zippel), not computational. It is quantum-safe.

---

## Recommendation

**Implement the polynomial-evaluation accumulator over BabyBear^4 for revocation non-membership.**

Rationale:
- 100x constraint reduction in the non-revocation sub-circuit
- O(1) witness updates (no federation round-trip on revocation set changes)
- No trusted setup required
- Field-native (no big-integer or pairing arithmetic in STARK)
- Quantum-safe security (information-theoretic bound)
- Compatible with IVC folding (degree-2 constraints)
- Straightforward migration from current sorted-Merkle approach

The KZG-based bilinear accumulator remains valuable as an OUTER verification layer (e.g., for on-chain batch verification or cross-federation attestation), leveraging the existing `hints` infrastructure. But for the in-STARK proof of non-revocation, the polynomial-evaluation approach dominates.
