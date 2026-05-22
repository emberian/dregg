# Private Predicates over Hybrid Data

Research document exploring predicate privacy combinations beyond the basic
`PredicateAir` (Phase 5: prove `value >= threshold` without revealing value).

---

## 1. Taxonomy of Predicate Privacy Combinations

Every predicate proof involves three components:
- **Data**: The value(s) being tested.
- **Predicate**: The condition being checked (threshold, set, relation).
- **Result**: Whether the predicate holds (always revealed as 1-bit: pass/fail).

The privacy of data and predicate are independent, yielding a 2x2 matrix:

| | **Public Predicate** | **Private Predicate** |
|---|---|---|
| **Public Data** | Trivial (no proof needed) | "Prove this public dataset satisfies a condition I won't reveal" |
| **Private Data** | Current `PredicateAir`: "Prove my secret value >= your public threshold" | "Prove my secret value satisfies your secret threshold" |

Two additional dimensions expand this:

- **Multi-party data**: The data belongs to a different party than the prover (cross-cell predicates).
- **Temporal data**: The predicate concerns historical state, not just the current snapshot.
- **Relational data**: The predicate involves a comparison between two private values from different parties.

### Full taxonomy (6 classes):

| Class | Data Owner | Predicate Owner | Example |
|-------|-----------|----------------|---------|
| **A. Private-over-public-predicate** | Prover | Verifier (public) | "My balance >= 1000" (current `PredicateAir`) |
| **B. Private-over-private-predicate** | Prover | Verifier (private) | "My score meets your secret hiring bar" |
| **C. Public-over-private-predicate** | Public | Prover (private) | "This public ledger satisfies a query I won't reveal" |
| **D. Cross-party predicate** | Third-party cell | Verifier | "The cell I'm interacting with has balance >= X" |
| **E. Temporal predicate** | Prover (historical) | Verifier | "My balance has been >= X for T blocks" |
| **F. Relational predicate** | Both parties | Neither (or third party) | "My balance > their balance" (neither reveals) |

---

## 2. What's Achievable Today (with PredicateAir)

The existing `PredicateAir` supports:

- **GTE / LTE / GT / LT**: Range predicates over a private value against a public threshold.
- **NEQ**: Prove non-equality via multiplicative inverse.
- **InRange**: Prove `low <= value <= high` via two range proofs.
- **Fact binding**: Every predicate proof is cryptographically bound to a specific fact in a specific token state via `fact_commitment = Poseidon2(fact_hash, state_root)`.

**Current capabilities (Class A only)**:
- The threshold is always a public input visible to the verifier.
- The private value comes from the prover's committed token state.
- Multiple independent predicates can be composed by generating multiple `PredicateProof` instances and having the verifier check all of them.

**Limitation**: No boolean logic WITHIN a single proof. The verifier must explicitly request each predicate separately, and composition is additive (AND only, via multiple proofs).

---

## 3. What's Achievable with Minor Extensions

### 3.1 Compound Predicates (Boolean Combinations)

**Goal**: Prove `(age >= 18 AND country IN {US, CA, UK}) OR (has_license AND reputation >= 100)` in a single proof.

**Approach**: Extend `PredicateAir` to a `CompoundPredicateAir` with multiple predicate rows sharing a common fact commitment.

```
Trace layout (N predicate slots + 1 boolean composition row):

Row 0..N-1: Individual predicate evaluations (reuse existing PredicateAir columns)
Row N:      Boolean composition: selector bits indicating which sub-predicates
            are active, OR/AND gates, final result bit.
```

**Circuit changes**:
- Add a `BooleanCompositionAir` that takes N boolean inputs (each from a sub-predicate's pass/fail) and evaluates an arbitrary boolean formula.
- The formula itself can be a public input (encoded as a small expression tree in field elements) or hardcoded per use case.
- AND: product of all inputs = 1.
- OR: 1 - product of (1 - input_i) = 1.
- Nested: tree of AND/OR gates with max depth ~4 (covers all practical cases).

**Difficulty**: LOW. This is pure constraint arithmetic over existing primitives. No new cryptographic assumptions.

**Cost**: +1 trace row per predicate slot. Proof generation time scales linearly with predicate count. For 4 sub-predicates: ~+80ms over baseline.

### 3.2 Membership Predicates

**Goal**: Prove `value IN {v1, v2, ..., vK}` without revealing which member matched.

**Approach**: Two options:

1. **Hash table approach** (small sets, K < 32): Commit to the set as `set_hash = Poseidon2(v1 || v2 || ... || vK)`. The circuit checks `product(value - v_i) == 0` (the value is a root of the polynomial with roots at set members). This reveals nothing about which element matched.

2. **Merkle approach** (large sets, K >= 32): Commit to the set as a Poseidon2 Merkle tree. The prover provides a Merkle membership proof for `value` in the tree. This reuses the existing `MerklePoseidon2StarkAir`.

**Difficulty**: LOW. Option 1 requires a polynomial evaluation constraint (degree K). Option 2 is already implemented.

### 3.3 Selective Disclosure + Predicates (Composition)

**Goal**: Reveal some facts in plaintext while proving predicates over others.

**Current state**: The `revealed_facts_commitment` in `PresentationWitness` already supports selective disclosure. The extension is to allow some facts to carry predicate proofs instead of plaintext reveals.

**Approach**: The verifier's request specifies per-fact: `Reveal | PredicateProof(type, threshold) | Hidden`.

```rust
enum FactDisclosure {
    Reveal,                          // Show plaintext
    Predicate(PredicateType, u64),   // Prove predicate
    Hidden,                          // Don't reveal anything
}
```

The presentation proof composition already binds fact commitments to the derivation trace. Adding predicate proofs per-fact is a matter of proof composition: the unified proof includes sub-proofs for each `Predicate` fact.

**Difficulty**: LOW-MEDIUM. Requires wiring the `PredicateAir` into the `BodyMembershipProof` composition pipeline.

---

## 4. What Requires Significant New Work

### 4.1 Private Predicates (Class B): Verifier's Threshold is Secret

**Scenario**: "Prove my credit score satisfies your hiring threshold" where the threshold is known only to the verifier.

**Challenge**: In the current `PredicateAir`, the threshold is a public input. If the threshold becomes private to the verifier, the prover cannot generate the proof (they don't know what to prove against).

**Solution 1: Oblivious Transfer + STARK** (practical, 2-round protocol)

1. Verifier commits to threshold: `C_t = Poseidon2(threshold, r_verifier)`.
2. Verifier sends `C_t` to prover (public input for both parties).
3. Prover and verifier engage in a 2-party protocol:
   - Verifier provides threshold to prover via 1-of-2 OT (prover learns threshold but verifier doesn't learn value).
   - Prover generates `PredicateProof` with the learned threshold.
   - Prover sends proof to verifier.
4. Verifier checks: proof's `threshold` matches their secret, proof verifies.

**Problem**: The prover LEARNS the threshold (even if they can't prove they learned it). This may be unacceptable for some use cases.

**Solution 2: MPC-in-the-head (VOLE-based)** (stronger, no threshold leakage)

Use the "MPC-in-the-head" paradigm (Ishai et al., extended by Baum et al. for STARKs):

1. Express the predicate as a shared circuit: prover holds `value`, verifier holds `threshold`, output is `value >= threshold`.
2. Simulate a 2-party protocol inside a STARK proof. The prover commits to their input and the "transcript" of an honest MPC execution.
3. The verifier provides their input after commitment (Fiat-Shamir or interactive).
4. The STARK proves: "the MPC was executed honestly and produced output=1."

**Compatibility with Poseidon2/BabyBear**: MPC-in-the-head naturally produces STARK-friendly proofs (the "ZKBoo" / "Limbo" / "Banquet" line of work). The bit-decomposition comparison we already use in `PredicateAir` can be shared: prover provides shares of the diff bits, verifier provides shares of the threshold.

**Difficulty**: HIGH. Requires implementing a VOLE-based commitment scheme and MPC simulation within the STARK trace. Research-grade, 3-6 months.

**Cost**: Proof generation 5-10x slower than standard predicate proof. Proof size 2-3x larger (more trace rows for MPC simulation).

### 4.2 Public Data, Private Predicate (Class C)

**Scenario**: "I want to query this public dataset but I don't want anyone to know what I'm looking for."

**Example**: A recruiter scans a public skills database: "Show me candidates where Python_experience >= 5 AND salary_expectation <= 150000" without revealing the query to the database operator.

**Approach 1: Private Information Retrieval (PIR)**

This is the classical PIR problem. The prover (database holder) has public data; the querier wants to evaluate a predicate without revealing which predicate.

For STARK-compatible PIR:
- Encode the database as a polynomial over BabyBear.
- The querier evaluates the polynomial at their secret point (the predicate parameters).
- A STARK proves the evaluation was done correctly over the committed database.

**Difficulty**: HIGH. PIR is computationally expensive. For small databases (<10K entries), it may be practical with batched FRI proofs. For large databases, this requires FHE or structured PIR.

**Approach 2: Private predicate as a committed circuit**

1. Querier commits to their predicate circuit: `C_predicate = Poseidon2(circuit_description)`.
2. Querier sends `C_predicate` to the data holder.
3. Data holder evaluates all entries against all possible predicates (or uses garbled circuits for the specific one).
4. This is essentially private function evaluation.

**Difficulty**: VERY HIGH. Requires either FHE (evaluate arbitrary predicates on encrypted data) or garbled circuits (one-time evaluation with constant round complexity).

**Practical alternative for pyana**: If the query space is small (enumerate all possible predicates), use an encrypted index:
- The database publishes Poseidon2 commitments to each entry's attributes.
- The querier locally evaluates their predicate against the commitments (if they know the data is public, they already have it).
- The privacy need is only against the database OPERATOR observing access patterns.

This reduces to Private Information Retrieval over committed data, which is feasible with our Merkle infrastructure for small databases.

### 4.3 Cross-Party Predicates (Class D)

**Scenario**: "Prove that the cell I'm interacting with has balance >= X" without that cell revealing its balance to me.

**Protocol**:

1. Cell A wants proof that Cell B satisfies `balance >= threshold`.
2. Cell B generates a `PredicateProof` with:
   - `private_value = B's balance` (B's witness)
   - `threshold` = Cell A's requested threshold (public)
   - `fact_commitment` binds to B's current state root
3. Cell B sends the proof to Cell A.
4. Cell A verifies: proof passes, fact_commitment matches B's attested state root.

**This already works with the existing `PredicateAir`!** The only requirement is that Cell B cooperates in generating the proof. The trust model is:
- Cell A trusts the STARK (mathematical guarantee).
- Cell A trusts B's state root is authentic (attested by the federation).
- Cell A does NOT need to trust B (B cannot forge a passing proof for a false statement).

**Difficulty**: LOW (already achievable). The new piece is:
- A protocol for Cell A to REQUEST a predicate proof from Cell B.
- Integration with the intent system: "I need someone whose balance >= X" becomes an intent where respondents prove the predicate.

**Non-cooperative variant** (B refuses to generate proof): Not achievable without MPC or a trusted third party. If B won't participate, no one can prove statements about B's private state.

### 4.4 Temporal Predicates (Class E)

**Scenario**: "Prove that my balance has been >= X for at least T blocks."

**Approach 1: IVC over historical state roots**

The prover demonstrates a chain of state transitions where the predicate held at every step:

```
For blocks [t-T, t-T+1, ..., t]:
  At each block i:
    - state_root_i is the attested root at block i
    - balance_i >= threshold (predicate proof against state_root_i)
    - state_root_i -> state_root_{i+1} is a valid transition (IVC step)
```

This is exactly the IVC pattern we already have (`StateTransitionAir`). The "transition function" is: "the predicate still holds in the next state."

**Cost**: Proof generation time = O(T) * per-step cost. For T=100 blocks with 10ms per step: ~1 second. With recursive composition (Phase 4 from privacy-architecture.md): constant-size proof regardless of T.

**Approach 2: Accumulator-based (amortized)**

Maintain a running accumulator that tracks "consecutive blocks where predicate P holds." The accumulator is a counter stored in the cell's state. Each block, if the predicate holds, increment; if not, reset to 0. The temporal predicate proof is then a single range check: `accumulator >= T`.

**Difficulty**: MEDIUM. Requires either:
- IVC chain of predicate proofs (approach 1): uses existing machinery but O(T) proving time.
- Accumulator in cell state (approach 2): requires the cell's program to maintain the counter (already possible with pyana programs).

**Recommended**: Approach 2 for production (accumulators are cheap). Approach 1 for historical queries where the accumulator wasn't maintained.

### 4.5 Relational Predicates (Class F)

**Scenario**: "Prove that my balance > their balance" without either party revealing their balance.

**This is the hardest class.** It fundamentally requires either:
1. A trusted third party who sees both values (defeats the purpose).
2. Secure Multi-Party Computation (MPC).
3. Fully Homomorphic Encryption (FHE).

**MPC approach (most practical)**:

1. Alice holds `a`, Bob holds `b`. They want to prove `a > b` without revealing `a` or `b` to each other.
2. Use garbled circuits (Yao's protocol) or secret sharing:
   - Alice and Bob secret-share their values: `a = a_A + a_B`, `b = b_A + b_B`.
   - They jointly evaluate the comparison circuit on shares.
   - The output (1 bit: a > b) is revealed to both.
3. To make this VERIFIABLE to a third party: wrap the MPC in a STARK.
   - The STARK proves: "the MPC protocol was executed honestly."
   - Public inputs: commitments to `a` and `b`, the result bit.
   - Private witness: the shares, the MPC transcript.

**Difficulty**: VERY HIGH. Requires:
- A 2-party comparison protocol (well-studied, e.g., Millionaires' Problem).
- Embedding the MPC transcript verification in a STARK (novel, research frontier).
- Communication rounds between parties.

**Practical alternative for pyana**:
- Each party independently proves their value to a SHARED predicate: "I have balance >= median" or "I'm in the top 10%."
- This avoids direct comparison but gives useful information.
- Or: use the cross-party predicate (Class D) with a relay — Alice proves `a >= t` to a mediator, Bob proves `b >= t` to the same mediator. The mediator learns the ordering by binary-searching `t`. This leaks to the mediator but not to Alice/Bob.

---

## 5. Integration with the Intent System

### 5.1 Current Intent Architecture

The intent system broadcasts `MatchSpec` descriptions of needed capabilities. Matching is local (privacy-preserving). Fulfillment can use STARK proofs.

The key types:
- `Intent { kind, matcher: MatchSpec, creator: CommitmentId }`
- `MatchSpec { actions, constraints, min_budget, compound }`
- `Constraint { AppId, Service, UserId, NotExpiredAt, Feature, Custom }`

### 5.2 Private Intent Matching

**Scenario**: "I need someone who satisfies predicate P, but I don't want to reveal P publicly."

Currently, intents are public (everyone sees what's needed). This is fine for capability discovery but leaks business logic.

**Design: Committed Intent with Oblivious Matching**

```
PrivateIntent {
    // Public (visible to all):
    id: [u8; 32],
    creator: CommitmentId,
    predicate_commitment: BabyBear,  // Poseidon2(predicate_description)
    expiry: u64,
    stake_proof: Option<StakeProof>,

    // Hidden (revealed only to potential satisfiers):
    encrypted_predicate: Vec<u8>,  // X25519-sealed predicate description
    // Encrypted to: the satisfier's ephemeral key (from handshake)
}
```

**Protocol**:

1. **Creator** broadcasts `PrivateIntent` with `predicate_commitment` (hides the predicate) and a public "shape hint" (e.g., "this intent concerns balance predicates" without revealing the threshold).
2. **Potential satisfiers** see the shape hint and decide whether to engage.
3. **Handshake**: Satisfier sends their ephemeral public key to Creator (via gossip or direct channel).
4. **Reveal**: Creator encrypts the predicate to the satisfier's key and sends it.
5. **Local matching**: Satisfier evaluates the predicate locally against their state.
6. **Fulfillment**: If satisfied, generates a `PredicateProof` and sends it back.

**Privacy properties**:
- The predicate is never broadcast in the clear.
- Only parties who engage in the handshake learn the predicate.
- The fulfillment proof reveals only "yes, I satisfy P" (not the value that satisfies it).
- If no one satisfies P, it expires without anyone learning P.

**Difficulty**: MEDIUM. The cryptographic pieces exist (X25519 sealed, STARK proofs). The new work is the handshake protocol and the encrypted predicate format.

### 5.3 Private Intent Matching with Private Predicates (Class B in Intent Context)

**Scenario**: "I need someone whose score >= T, but I won't tell potential satisfiers what T is either."

This is the hardest intent variant. The satisfier must prove they satisfy a predicate they don't know.

**Approach: Threshold Range Proof with Bracketing**

1. Creator publishes: "I have a threshold T in range [L, H]" (public bounds, private exact value).
2. Satisfier proves: "My value >= H" (the upper bound). This guarantees satisfaction regardless of T.
3. OR: Interactive bracketing — Creator reveals progressively tighter bounds until the satisfier can either prove satisfaction or determine they cannot.

**More sophisticated approach**: Garbled circuit-based private matching:
1. Creator garbles a circuit for `value >= threshold`.
2. Satisfier evaluates the garbled circuit with their value via Oblivious Transfer.
3. The output reveals only whether the predicate is satisfied.
4. A STARK wrapping the garbled circuit evaluation provides verifiability.

**Difficulty**: VERY HIGH. Garbled circuits + OT + STARK wrapping is novel.

### 5.4 Intent Predicate Composition

The existing `MatchSpec.compound` field already supports AND-composition of requirements. Extending to predicate proofs:

```rust
enum IntentPredicate {
    /// Current: named constraint (equality-based)
    Named(Constraint),
    /// New: range predicate over a committed attribute
    Range {
        attribute: String,      // which fact field
        predicate_type: PredicateType,
        threshold: u64,         // public threshold
    },
    /// New: membership predicate
    Membership {
        attribute: String,
        set_commitment: BabyBear,  // committed set
    },
    /// New: compound predicate with boolean logic
    Compound {
        operator: BooleanOp,    // AND / OR
        children: Vec<IntentPredicate>,
    },
}

enum BooleanOp { And, Or }
```

The matcher evaluates `IntentPredicate` locally. The fulfillment generates the appropriate combination of `PredicateProof` instances.

---

## 6. Real Use Cases

### 6.1 Sealed-Bid Auctions (Classes A + D)

**Setting**: Multiple bidders, one auctioneer. Bids are private until the auction closes.

**Current capability**: The `private_orderbook` demo already implements sealed bids with note commitments. Extension with predicates:

- **Qualification**: "Prove your deposit >= minimum_bid" (Class A, today's PredicateAir).
- **Winner determination**: Auctioneer collects predicate proofs from all bidders proving `bid >= reserve_price`, then reveals the winner.
- **Privacy**: Losing bids are never revealed. The winner reveals only their winning bid, not their maximum willingness-to-pay.

**Private reserve** (Class B extension): The reserve price is secret. Bidders prove `bid >= ?` where `?` is committed but not revealed until the auction closes. Post-close, auctioneer reveals the reserve; proofs retroactively validate qualification.

### 6.2 Credit Checks / KYC (Classes A + B)

**Setting**: A lender wants to verify a borrower's creditworthiness without learning the exact credit score.

- **Class A (today)**: "Prove credit_score >= 700" — lender sets public threshold.
- **Class B (extension)**: "Prove credit_score >= T" where T is the lender's private risk model output. The lender doesn't want competitors to know their acceptance threshold.

**Protocol with existing primitives**:
1. Borrower's credit score is a fact in their token state (attested by a credit bureau issuer).
2. Lender sends threshold to borrower (acceptable for credit checks — the threshold isn't the secret sauce, the decision logic is).
3. Borrower generates `PredicateProof(Gte, score, threshold, fact_commitment)`.
4. Lender verifies.

**With private threshold** (future):
1. Lender commits to threshold: `C = Poseidon2(threshold, blinding)`.
2. Borrower and lender engage in OT-based protocol.
3. Borrower generates proof without learning the exact threshold (only whether they passed).

### 6.3 Capability Matching in Marketplaces (Classes A + C)

**Setting**: A compute marketplace where providers prove they have resources and consumers prove they have budget, without revealing exact numbers.

- **Provider proves**: "My available GPU memory >= your requirement" (Class A).
- **Consumer proves**: "My budget >= your price" (Class A).
- **Private matching** (Class C): "I'm looking for a provider with specific capabilities but I don't want to reveal my workload characteristics" — the query itself is private.

**Intent integration**:
```
Intent {
    kind: Need,
    matcher: MatchSpec {
        constraints: [
            Custom { predicate: "gpu_memory_gte", value: "8192" },
            Custom { predicate: "bandwidth_gte", value: "1000" },
        ],
    },
}
```

Providers respond with `PredicateProof` for each constraint. The consumer's FULL requirements (which constraints and what thresholds) ARE visible in the intent. For private queries, use the `PrivateIntent` protocol from 5.2.

### 6.4 Reputation and Trust Scores (Classes A + E)

**Setting**: A decentralized marketplace where sellers must prove sustained good reputation.

- **Current reputation** (Class A): "Prove reputation >= 4.5 stars" — single predicate proof.
- **Sustained reputation** (Class E): "Prove reputation has been >= 4.0 for the last 90 days" — temporal predicate.

**Implementation with accumulators**:
- The seller's cell maintains a `reputation_streak` counter.
- Each block/epoch, if reputation >= threshold, the cell's program increments the counter.
- Temporal predicate proof = range check on the counter: `streak >= T_blocks`.

### 6.5 Multi-Party Negotiation (Class F)

**Setting**: Two companies negotiating a deal. Neither wants to reveal their budget/valuation, but they need to know if there's overlap.

- "Is my maximum_price >= their minimum_price?" — relational predicate.
- Neither party reveals their number, but both learn whether a deal is possible.

**Protocol** (practical, no full MPC):
1. Both parties commit to their values: `C_alice = Poseidon2(max_price, r_a)`, `C_bob = Poseidon2(min_price, r_b)`.
2. Use a comparison protocol (e.g., Millionaires' Problem via Paillier or via garbled circuits).
3. Output: 1 bit (deal possible / not possible).
4. For verifiability: both parties generate predicate proofs that their committed values match what was used in the comparison.

---

## 7. Mapping to Primitives

### What we have:

| Primitive | Source | Used for |
|-----------|--------|----------|
| `PredicateAir` (GTE/LTE/GT/LT/NEQ/InRange) | `circuit/src/predicate_air.rs` | Class A predicates |
| `fact_commitment` binding | `poseidon2::hash_2_to_1` | Binding proofs to specific state |
| `MerklePoseidon2StarkAir` | `circuit/src/poseidon2_air.rs` | Membership proofs (large sets) |
| `BodyMembershipProof` composition | `circuit/src/body_membership.rs` | Multi-proof verification |
| `NonRevocationAir` | `circuit/src/non_revocation_air.rs` | Non-membership proofs |
| `IvcProof` / `StateTransitionAir` | `circuit/src/ivc.rs` | Temporal chaining |
| `Intent` + `MatchSpec` + `Constraint::Custom` | `intent/src/lib.rs` | Discovery + matching |
| X25519-ChaCha20Poly1305 sealed secrets | `tokenizer/` | Encrypted communication |
| `presentation_randomness` / unlinkability | `circuit/src/presentation.rs` | Multi-show privacy |

### What we need to build:

| Primitive | Difficulty | Enables | Depends on |
|-----------|-----------|---------|-----------|
| `CompoundPredicateAir` (boolean composition) | LOW | AND/OR predicate combinations | `PredicateAir` |
| `MembershipPredicateAir` (polynomial check) | LOW | Set membership predicates | Field arithmetic |
| `IntentPredicate` type in MatchSpec | LOW | Predicate-aware intent matching | `intent` crate |
| `PrivateIntent` (committed predicate) | MEDIUM | Private intent discovery | X25519, gossip |
| Temporal predicate via IVC chain | MEDIUM | Historical state predicates | `ivc.rs` |
| Accumulator-based temporal predicate | LOW | Efficient temporal proofs | Cell programs |
| Cross-party predicate request protocol | MEDIUM | Class D (cooperative) | Gossip, intent |
| OT-based private threshold | HIGH | Class B (verifier-private predicate) | New crypto |
| MPC-in-the-head comparison | VERY HIGH | Class F (relational) | Research |
| Garbled circuit evaluation in STARK | VERY HIGH | Private function evaluation | Research |
| PIR over committed data | VERY HIGH | Class C (large databases) | FHE or structured PIR |

---

## 8. UX Considerations

### Verifier UX for Private Predicates

**Question**: "What's the UX for a verifier who wants to verify a private predicate without knowing what was proven?"

**Answer**: The verifier's experience depends on the class:

- **Class A** (today): Verifier sets the threshold, receives a proof, checks `verify_predicate(proof, threshold, commitment)`. Clear and simple.

- **Class B** (private threshold): Verifier commits to a threshold, engages in a protocol, then receives a 1-bit answer (pass/fail) plus a proof that the answer is honest. The verifier's UX is: "I set my secret bar. The system tells me pass/fail. I'm cryptographically certain the answer is correct."

- **Class D** (cross-party): Verifier broadcasts an intent with a predicate requirement. Respondents provide proofs. The verifier's UX is identical to Class A verification — they just didn't know WHO would respond.

- **Class F** (relational): Both parties see only the 1-bit comparison result. UX: "Is a deal possible? Yes/No." Both parties are certain the answer is correct without learning the other's value.

### Prover UX

The prover's experience:
1. Receive a predicate request (from an intent, a verifier, or a protocol).
2. Local evaluation: "Can I satisfy this?" (instant, no crypto).
3. If yes: generate proof (sub-second with existing STARK machinery).
4. Send proof (reveals only pass/fail + binding to state).

For compound predicates, the wallet should present: "Service X is asking you to prove: [age >= 18] AND [country in {US, CA, UK}]. Your token satisfies this. Generate proof?"

---

## 9. Security Analysis

### Soundness

All predicate proofs inherit soundness from the underlying STARK:
- A prover CANNOT forge a passing proof for a false predicate (computational soundness, 124-bit security via BabyBear4 extension).
- The `fact_commitment` prevents the prover from proving predicates about fabricated values not in their actual state.

### Zero-Knowledge

- **Class A**: Perfect ZK — verifier learns only pass/fail, not the value.
- **Class B**: Depends on protocol. OT-based: verifier learns nothing beyond pass/fail. The threshold is used but not revealed to the prover (in the ideal case).
- **Class D**: The proving cell reveals only pass/fail. The requesting cell doesn't learn the value.
- **Class E**: Temporal proofs reveal "held for >= T blocks" but not the exact duration or the exact values at each block.
- **Class F**: Each party learns only the comparison result (1 bit), not the other's value.

### Linkability

Predicate proofs should NOT be linkable across presentations. With `presentation_randomness` (Phase 2 from privacy-architecture.md), different predicate proofs from the same token use different random fact commitments, preventing correlation.

**Risk**: If the same `fact_commitment` is used across multiple predicate proofs, a verifier could correlate them. **Mitigation**: Use a blinded fact commitment: `blinded_fact_commitment = Poseidon2(fact_hash, state_root, fresh_randomness)`. The STARK proves binding to the real fact while the commitment varies per presentation.

---

## 10. Implementation Roadmap

### Phase 1: Compound Predicates (2-3 weeks)

1. Implement `CompoundPredicateAir` supporting AND/OR over up to 8 sub-predicates.
2. Add `MembershipPredicateAir` for set membership (polynomial evaluation, K <= 16).
3. Wire into the `PredicateBuilder` API from privacy-architecture.md Phase 3.
4. Tests: compound predicate generation and verification.

### Phase 2: Intent Integration (2-3 weeks)

1. Add `IntentPredicate` variant to `Constraint` enum in intent crate.
2. Extend `match_intent` to evaluate `PredicateProof`-based constraints.
3. Implement `PrivateIntent` with committed predicate and handshake protocol.
4. Tests: private intent broadcast, handshake, reveal, fulfillment with predicate proof.

### Phase 3: Cross-Party and Temporal (3-4 weeks)

1. Protocol for cross-party predicate requests (via intent system or direct message).
2. Accumulator-based temporal predicates in cell programs.
3. IVC-chain temporal proofs for historical queries.
4. Tests: cross-cell predicate proof, 100-block temporal proof.

### Phase 4: Research — Private Predicates (ongoing)

1. Prototype OT-based private threshold (Class B) using STARK-friendly OT.
2. Survey MPC-in-the-head constructions compatible with BabyBear.
3. Evaluate garbled circuit feasibility for relational predicates.
4. Publish findings and decide go/no-go for production inclusion.

---

## 11. Summary

| Class | Achievable? | Timeline | Key primitive |
|-------|------------|----------|---------------|
| A: Private data, public predicate | TODAY | Shipped | `PredicateAir` |
| A+: Compound (AND/OR) | Minor extension | 2-3 weeks | `CompoundPredicateAir` |
| A+: Membership (IN set) | Minor extension | 2-3 weeks | Polynomial / Merkle |
| B: Private threshold | Significant work | 2-3 months | OT + STARK |
| C: Private query over public data | Research | 6+ months | PIR / FHE |
| D: Cross-party (cooperative) | Moderate work | 3-4 weeks | Protocol + existing AIR |
| E: Temporal | Moderate work | 3-4 weeks | IVC / accumulators |
| F: Relational (non-cooperative) | Research | 6+ months | MPC + STARK |

The critical insight: Classes A, A+, D, and E are all achievable with the existing STARK/Poseidon2 machinery plus modest protocol extensions. Classes B, C, and F require fundamentally new cryptographic constructions (MPC, OT, PIR, FHE) — but the STARK layer can serve as the VERIFIABILITY wrapper for any of these once the underlying protocol is in place.

Pyana's architecture is well-positioned because:
1. The `PredicateAir` already handles the hard part (range proofs in BabyBear).
2. The intent system provides natural discovery for cross-party predicates.
3. The IVC machinery enables temporal predicates without new circuit designs.
4. The X25519 sealed secrets provide encrypted channels for private predicate protocols.
5. The whole stack is post-quantum safe (hash-based STARKs), unlike curve-based approaches.
