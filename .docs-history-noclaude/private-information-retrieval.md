# Private Information Retrieval over Committed Databases

## Status: Design Exploration

## Problem Statement

Pyana commits public datasets (note trees, revocation trees, capability registries, intent pools) as Poseidon2 Merkle trees over BabyBear. A querier may need to access these datasets without revealing which entry they care about:

- **Nullifier check**: "Has this specific nullifier been spent?" without revealing which nullifier.
- **Capability lookup**: "Does capability X exist in the federation registry?" without revealing X.
- **Intent discovery**: "Show me intents matching my criteria" without revealing my criteria.
- **Revocation check**: "Is this token non-revoked?" without revealing which token.

These are all instances of Private Information Retrieval (PIR): the database is public (held by a server or the federation), but the query is private.

---

## 1. PIR Taxonomy

### 1.1 Single-Server Computational PIR (cPIR)

The server holds a database D of N entries. The client wants D[i] without revealing i.

**Protocol shape**:
1. Client encodes index i into an encrypted query vector.
2. Server performs homomorphic computation over ALL entries (must touch everything to hide the access pattern).
3. Client decrypts the response to obtain D[i].

**Communication**: O(sqrt(N)) or O(N^{1/3}) depending on the scheme.
**Server computation**: O(N) -- the fundamental lower bound. The server cannot skip entries without learning which one the client wants.
**Security**: Computational (lattice-based: LWE, RLWE).

**Pyana relevance**: A federation node holds the Merkle tree; an agent wants to check a leaf without the node learning which leaf. The node is the "server."

### 1.2 Multi-Server PIR (IT-PIR)

The database is replicated across k non-colluding servers. The client sends a different (information-theoretically hiding) query to each server. No single server learns i.

**Communication**: O(N^{1/k}) per server.
**Server computation**: O(N) per server.
**Security**: Information-theoretic (unconditional) against fewer than t colluding servers.

**Pyana relevance**: If the federation has multiple independent nodes, the client can query different nodes with shares of the request. Assumes honest-majority among the queried nodes. This maps naturally to pyana's federation topology.

### 1.3 Symmetric PIR (SPIR)

Both sides have privacy:
- Client: hides which entry they want.
- Server: ensures the client learns ONLY the requested entry (not the entire database).

**Construction**: PIR + oblivious transfer (OT). The server's privacy comes from limiting what the client can extract per query.

**Pyana relevance**: When the federation wants to rate-limit queries or prevent bulk extraction of the capability registry while still allowing private lookups.

### 1.4 Verifiable PIR (vPIR)

The client can verify that the server answered honestly (returned the correct D[i], not garbage).

**Construction**: PIR + commitment to the database (Merkle root or polynomial commitment). The server provides a proof that the answer is consistent with the public commitment.

**Pyana relevance**: Critical. The federation's datasets are already committed (Poseidon2 Merkle roots are attested via BLS threshold signatures). We need the PIR answer to be provably consistent with the attested root.

### 1.5 Verifiable PIR with ZK Composition

The most powerful variant: the client proves to a THIRD party that they performed a valid PIR query and the result satisfies some predicate -- without revealing the query or the result.

**Protocol**:
1. Client PIR-queries the database (private query, gets private answer).
2. Client generates a STARK proving: "I queried the committed database, got answer A, and A satisfies predicate P."
3. Third party verifies: "someone queried the database and the result satisfies P" -- without learning the query or A.

**Pyana relevance**: "I checked the revocation tree and my token is NOT revoked" is exactly this pattern -- a verifiable PIR with a non-membership predicate. The current `NonRevocationAir` solves this, but the QUERY is not private (the federation node providing the Merkle path learns which token is being checked).

---

## 2. Computational Costs for BabyBear-Native Approaches

### 2.1 Lattice-Based cPIR (SimplePIR / DoublePIR)

**SimplePIR** (Henzinger et al. 2023):
- Database treated as a sqrt(N) x sqrt(N) matrix.
- Client sends an encrypted row selector (RLWE ciphertext).
- Server computes matrix-vector product homomorphically.
- Client decrypts to get the selected row, extracts the desired entry.

**BabyBear translation challenges**:
- SimplePIR operates over large moduli (32-64 bit integers for LWE noise).
- BabyBear is a 31-bit prime field (p = 2^31 - 2^27 + 1). LWE noise management requires careful parameter selection.
- The LWE dimension n must satisfy 128-bit security: n >= 1024 for standard parameters.
- A single LWE ciphertext: n+1 ring elements = ~4 KB.
- For a database of N = 2^20 entries (1M): sqrt(N) = 1024. Upload: 1024 ciphertexts * 4 KB = 4 MB. Download: 1024 entries.

**Server computation**:
- Matrix-vector multiply: N multiplications + N additions in the ciphertext space.
- For N = 2^20: ~4M ring operations. At ~1ns per BabyBear multiply: ~4ms raw arithmetic.
- Actual cost with ciphertext overhead (noise management): ~50-200ms for 1M entries.

**DoublePIR** (reducing communication):
- Two-dimensional encoding: N^{1/3} x N^{1/3} x N^{1/3} cube.
- Communication: O(N^{1/3}) in each direction.
- For N = 2^20: cube side = ~100. Upload: ~400 KB. Download: ~400 bytes.
- Server computation: O(N) unchanged.

**Verdict for pyana**: Feasible for databases up to ~1M entries. Communication is acceptable. Server computation is the bottleneck (O(N) per query). For the revocation tree (typically <10K entries), this is <1ms server-side. For large intent pools (100K entries), ~50ms per query.

### 2.2 Polynomial-Based PIR (BabyBear-Native)

Key insight: a database of N entries over BabyBear can be encoded as a polynomial P(x) of degree N-1 where P(omega^i) = D[i] for the N-th roots of unity omega in BabyBear.

**BabyBear's multiplicative group**:
- |F*| = p - 1 = 2^31 - 2^27 = 2^27 * (2^4 - 1) = 2^27 * 15.
- The 2-adic subgroup has order 2^27 (~134M). Supports NTTs of size up to 2^27.
- Roots of unity: omega = generator^((p-1)/N) for any N | (p-1).

**Direct polynomial evaluation PIR**:
1. Commit the database as P(x) via NTT (the coefficients are public or committed).
2. Client wants P(omega^i) without revealing i.
3. Naive approach: client sends a "blinded" evaluation point z = omega^i * r and asks for P(z). But this doesn't work -- P(z) != P(omega^i) in general.
4. Better: use LINEARITY of the evaluation map.

**Linear PIR over NTT evaluations**:
- The database in coefficient form is a vector c = [c_0, ..., c_{N-1}].
- Evaluating at omega^i computes the inner product: P(omega^i) = sum(c_j * omega^{ij}).
- The "selector vector" for position i is v_i = [1, omega^i, omega^{2i}, ..., omega^{(N-1)i}].
- PIR = compute inner product <c, v_i> without revealing v_i.
- Under Regev encryption: encrypt v_i component-wise, server computes homomorphic inner product. This is exactly SimplePIR instantiated over BabyBear!

**Cost in BabyBear**:
- N multiplications in BabyBear (one per database entry) for the inner product.
- No noise management needed if we use a field-native PIR scheme (see Section 3).
- For N = 2^16 (65K entries): 65K muls @ 1ns = 65 microseconds. Extremely fast.

**The catch**: Field-native PIR without encryption is NOT private -- the server sees v_i in the clear. We need either encryption (lattice-based, losing BabyBear-nativeness) or multi-server information-theoretic PIR (secret-sharing v_i across servers).

### 2.3 IT-PIR over BabyBear (Multi-Server, Field-Native)

With k=2 non-colluding servers:
1. Client generates random r in F^N.
2. Sends r to server 1, sends (v_i - r) to server 2.
3. Server 1 computes <c, r> = sum(c_j * r_j).
4. Server 2 computes <c, v_i - r> = sum(c_j * (v_i_j - r_j)).
5. Client adds both responses: <c, r> + <c, v_i - r> = <c, v_i> = P(omega^i).

Neither server sees v_i (only a random share of it).

**Communication**: Upload: N field elements per server = 4N bytes. Download: 1 field element per server.
**Server computation**: N multiplications + N additions = O(N) per server. In BabyBear: ~65us for N=65K.
**Security**: Unconditional against either server alone. Requires non-collusion.

**Pyana mapping**: Two federation nodes that don't share query traffic. Each sees a random-looking vector. This is extremely practical for pyana's multi-node federation architecture.

### 2.4 Summary Table

| Approach | Security | Upload | Download | Server Work (N=64K) | Field-Native? |
|----------|----------|--------|----------|---------------------|---------------|
| SimplePIR (lattice) | Computational (LWE) | ~4 MB | ~4 KB | ~50ms | No (needs 64-bit moduli) |
| DoublePIR (lattice) | Computational (RLWE) | ~400 KB | ~400 B | ~50ms | No |
| IT-PIR (2-server) | Unconditional | 256 KB per server | 4 B per server | ~65us | YES |
| IT-PIR (3-server) | Unconditional | 64 KB per server | 4 B per server | ~16us | YES |
| Polynomial KZG | Computational (q-SDH) | 48 B (one G1 point) | 48 B | ~5ms (MSM) | No (BLS12-381) |

---

## 3. KZG-Based Polynomial PIR Using Existing `hints` Infrastructure

The `hints` crate provides KZG10 over BLS12-381 with the Ethereum trusted setup (degree up to 64 currently, extensible to 4096+). This enables a particularly elegant PIR construction.

### 3.1 Construction: Private Polynomial Evaluation

**Setup** (one-time, by the federation):
1. Encode the database D[0..N-1] as a polynomial P(x) where P(omega^i) = D[i].
2. Commit: C = KZG.commit_g1(params, P) -- a single G1 point (48 bytes).
3. Publish C alongside the Poseidon2 Merkle root (dual commitment).

**Query** (per client request):
1. Client wants D[i] = P(omega^i). Defines z = omega^i (private).
2. Client sends g^z to the server (Pedersen-style committed evaluation point).
3. Server cannot extract z from g^z (discrete log).
4. Server produces a KZG opening proof at the committed point using a 2-party protocol.

**The 2-party evaluation protocol** (Caulk/Caulk+ style):

Problem: standard KZG opening requires the server to know z in the clear to compute the quotient polynomial. With committed z, we need a modified protocol:

1. Client holds z, server holds P and params.
2. Client sends E_z = g^z (commitment to the evaluation point).
3. Server precomputes: for each i in [0, N), the KZG opening proof pi_i = commit_g1(P / (x - omega^i)).
4. Client uses an oblivious selection protocol: PIR over the table of precomputed proofs.

This creates a bootstrapping problem (PIR to enable PIR). However:

**Optimization for small databases (N <= 4096)**:
- The server precomputes all N opening proofs (N * 48 bytes = ~200 KB for N=4096).
- The client retrieves the correct proof using IT-PIR over BabyBear (the proof table is the "database").
- This is a 2-level PIR: level 1 (BabyBear IT-PIR) retrieves the KZG proof; level 2 (KZG verification) provides verifiability.

### 3.2 Integration with Pyana's Hint System

The `hints/src/kzg.rs` already provides:
- `KZG10::eth_setup(max_degree)` -- load Ethereum trusted setup
- `KZG10::commit_g1(params, polynomial)` -- polynomial commitment
- `KZG10::compute_opening_proof(params, polynomial, point)` -- standard opening

**Extensions needed**:
1. **Batch precomputation**: compute all N opening proofs in O(N log N) using Feist-Khovratovich (FK) technique. Store as a lookup table.
2. **Committed evaluation**: a protocol wrapper that accepts a Pedersen-committed point and returns a proof without learning the point.
3. **Verification binding**: the KZG commitment C must be provably consistent with the Poseidon2 Merkle root (cross-commitment bridge).

### 3.3 Cross-Commitment Consistency

The database is committed TWO ways:
- Poseidon2 Merkle root R (for in-STARK membership proofs).
- KZG commitment C = [P(s)]_1 (for private evaluation / PIR).

These must be bound together. The federation attests: "R and C commit to the same dataset" via BLS threshold signature over (epoch, R, C).

A stronger binding: the client can verify consistency locally by checking that a random spot-check evaluates consistently:
- Pick random j. Get D[j] from the Merkle tree (public).
- Verify KZG opening: e(C - [D[j]]_1, [1]_2) == e(pi_j, [s - omega^j]_2). If this passes for a random j, the commitments are consistent with overwhelming probability.

### 3.4 Limitations

- **Trusted setup**: KZG requires the Ethereum SRS. For degree > 4096, we need the full Powers of Tau (available, ~150 MB for degree 2^15).
- **Not post-quantum**: BLS12-381 is broken by quantum computers. For PQ-safe PIR, use the IT-PIR approach (Section 2.3) or lattice-based cPIR.
- **Degree bound**: The database size is bounded by the SRS degree. The Ethereum ceremony supports up to degree 2^28 (~268M entries) but loading that much SRS is impractical. Practically bounded at 2^16-2^20.

---

## 4. ORAM-in-STARK Feasibility

### 4.1 Concept

Oblivious RAM (ORAM) makes every access pattern look random regardless of the actual access sequence. If the database accesses are performed via ORAM, the server learns nothing about which entries are accessed.

**Path ORAM** (the simplest practical ORAM):
- A binary tree of buckets, each holding O(log N) blocks.
- Each access reads one root-to-leaf path (O(log N) buckets) and writes back to a random path.
- A position map (client-side, O(N) entries) maps each block to its current tree path.

### 4.2 ORAM Inside a STARK

The idea: prove that an ORAM protocol was followed correctly, so a verifier trusts the result without seeing the access pattern.

**What we'd prove**:
1. "I followed Path ORAM protocol steps correctly for my query."
2. "The block I retrieved is consistent with the committed database state."
3. "I'm not cheating by accessing blocks out-of-protocol."

**Circuit cost**:
- Each ORAM access requires reading O(log N) buckets (each a Poseidon2 hash verification).
- For N = 2^16: log N = 16 levels, each with ~5 blocks per bucket.
- Per access: 16 * 5 = 80 Poseidon2 hash evaluations.
- In the current Poseidon2 AIR: ~12 rows per hash evaluation.
- Total: ~960 trace rows per ORAM access.

**Comparison to direct Merkle PIR**:
- Direct Merkle membership proof: 16 hash evaluations = ~192 trace rows.
- ORAM: ~960 rows (5x overhead for obliviousness).

### 4.3 The Position Map Problem

Path ORAM requires the client to maintain a position map of size O(N). This is:
- Stored privately by the client.
- Updated on every access.
- Recursive ORAM can reduce this to O(1) client storage, but at O(log^2 N) access cost.

For in-STARK ORAM:
- The position map becomes part of the private witness.
- Proving consistency of position map updates adds ~O(N) constraints (a full permutation check).
- This is prohibitively expensive for large databases inside a single STARK.

### 4.4 Feasibility Assessment

| Factor | Assessment |
|--------|-----------|
| Circuit overhead | 5x vs direct Merkle proof (acceptable) |
| Position map in witness | O(N) -- problematic for N > 2^14 |
| Multi-access amortization | Good (ORAM shines with multiple accesses per session) |
| Single-query case | Worse than IT-PIR or KZG-PIR in every metric |
| Implementation complexity | HIGH (ORAM state management, eviction protocols) |

**Verdict**: ORAM-in-STARK is NOT the right approach for pyana's single-query PIR needs. It becomes relevant only if a client makes MANY private queries in sequence (e.g., an agent scanning the entire intent pool privately). For that use case, ORAM amortizes to O(log N) per query after setup. But for the common case (one lookup), IT-PIR or KZG-PIR dominates.

### 4.5 When ORAM Makes Sense

- **Private batch scanning**: An agent wants to check ALL nullifiers in their wallet against the spent set without revealing which wallet they hold. This is O(K) queries for K wallet entries. ORAM amortizes well here.
- **Stateful private subscriptions**: An agent subscribes to "notify me when any of my intents are matched" without revealing which intents are theirs. The subscription service uses ORAM to access the match state privately.

---

## 5. Private Intent Discovery Protocol Design

### 5.1 The Privacy Problem in Intent Discovery

Current architecture (from `pyana-intent`):
- Intents are broadcast to the gossip pool with public `MatchSpec`.
- Potential fulfillers match locally (their capabilities stay private).
- Fulfillment uses commit-reveal (anti-frontrunning).

**Privacy gaps**:
1. The intent CREATOR's requirements are public (everyone sees what they need).
2. A potential FULFILLER browsing intents reveals access patterns to the pool operator.
3. The pool operator can build profiles of who looks at what.

Gap 1 is addressed by `PrivateIntent` (committed predicates, documented in `private-predicates.md`). Gaps 2 and 3 require PIR.

### 5.2 Protocol: PIR over the Intent Pool

**Setup**:
- The intent pool holds N intents, each with a public `intent_id` and metadata.
- The pool is committed as a Poseidon2 Merkle tree (root attested by the federation).
- Additionally, the pool is indexed by CAPABILITY TAGS: for each capability tag t, there's a list of intent IDs requiring that tag.

**Query**: "Give me intents requiring capability tag T" without revealing T.

**Design using IT-PIR (2-server)**:

The index is structured as a matrix: rows = capability tags (enumerated), columns = intent list entries.

```
Index matrix I (|Tags| x MaxIntentsPerTag):
  I[t][j] = the j-th intent_id requiring tag t, or 0 if fewer than j intents need t.

Database for PIR: treat each row as a "record" of size MaxIntentsPerTag field elements.
```

**Protocol**:
1. Client wants row t (all intents requiring capability tag T where hash(T) = t).
2. Client generates shares: r random, sends (r) to node A, sends (e_t - r) to node B.
   - e_t is the standard basis vector with 1 at position t.
3. Node A computes I^T * r (matrix-vector product), returns result_A.
4. Node B computes I^T * (e_t - r), returns result_B.
5. Client adds: result_A + result_B = I^T * e_t = row t of I = all intent IDs requiring tag t.

**Communication**:
- Upload: |Tags| field elements per server = 4 * |Tags| bytes.
- For |Tags| = 1024: 4 KB per server upload.
- Download: MaxIntentsPerTag field elements per server.
- For MaxIntentsPerTag = 64: 256 bytes per server download.

**Server computation**:
- Matrix-vector multiply: |Tags| * MaxIntentsPerTag multiplications.
- For 1024 * 64 = 65K muls: ~65 microseconds in BabyBear.

**Verification**: Client verifies the returned intent IDs exist in the attested Merkle tree by requesting standard (non-private) membership proofs for the returned IDs. The intent contents are public; only the QUERY was private.

### 5.3 Protocol: Private Intent Matching (Full Privacy)

For the case where even the INTENT CONTENTS should be private to non-matching agents:

**Encrypted Intent Pool**:
1. Each intent is encrypted under the creator's key: `E_i = Enc(intent_i, creator_key_i)`.
2. The pool stores ciphertexts.
3. A matching agent cannot decrypt intents that don't match their capabilities.

**Protocol with PIR + Predicate Evaluation**:
1. The pool maintains a PREDICATE INDEX: for each intent, a set of capability tags that would satisfy it (publicly visible as hashes).
2. The agent PIR-queries for intents matching their capability tag (private query).
3. The agent learns intent IDs, then engages in an encrypted handshake (X25519) with each intent creator to learn the full intent specification.
4. If the agent can fulfill, they proceed with commit-reveal.

**Privacy achieved**:
- Pool operator: does not learn which capability the agent has (PIR hides the query).
- Other agents: do not learn which intents the querying agent is interested in.
- Intent creator: learns that someone with a matching capability engaged, but not their identity (unless fulfillment proceeds).

### 5.4 Advanced: Keyword PIR for Intent Search

Instead of exact tag matching, support KEYWORD search over intent descriptions:

**Symmetric Keyword PIR** (Chor-Gilboa-Naor adapted):
- Each intent is tagged with multiple keywords k_1, ..., k_m.
- Client wants "all intents containing keyword K" without revealing K.
- Use an inverted index: for each possible keyword hash, the index stores the list of matching intent IDs.
- Apply IT-PIR over the inverted index.

**Cost for pyana**:
- Keyword space: 2^16 possible keyword hashes (after bucketing).
- Index size: 2^16 rows * 32 entries per row = 2M field elements = 8 MB.
- IT-PIR upload: 2^16 * 4 = 256 KB per server.
- IT-PIR download: 32 * 4 = 128 bytes per server.
- Server computation: 2M muls = ~2ms.

This is practical for intent pools up to ~100K intents with ~64K distinct keyword buckets.

### 5.5 Privacy Guarantees Summary

| Party | Learns | Does NOT learn |
|-------|--------|----------------|
| Pool operator (single node) | Query rate, response size | Which capability/keyword was queried |
| Pool operator (if both IT-PIR nodes collude) | Everything | N/A (security breaks) |
| Other agents | Nothing about the query | Query or results |
| Intent creator | Someone is interested (if handshake occurs) | Agent's identity or other capabilities |
| Federation | Query rate (metadata) | Query content |

---

## 6. Verifiable PIR Composition Pattern

### 6.1 The Pattern: Query + Prove + Show

The most powerful primitive combining PIR with STARK proofs:

```
1. QUERY:  Client privately retrieves D[i] via PIR.
2. PROVE:  Client generates a STARK proving:
           "I performed a valid retrieval from committed database C,
            the result satisfies predicate P."
3. SHOW:   Client shows the STARK proof to a third party.
           Third party verifies: "the database committed as C was queried,
           the answer satisfies P" -- without learning i or D[i].
```

### 6.2 Concrete Instance: Private Non-Revocation

**Current approach** (non-private):
1. Client asks a federation node for the Merkle non-membership witness for their token's revocation hash.
2. The federation node LEARNS which token is being checked.
3. Client generates `NonRevocationAir` proof.

**Verifiable PIR approach** (fully private):
1. Client PIR-queries the revocation tree for the neighborhood of their revocation hash (the two adjacent leaves).
2. The federation node does NOT learn which hash was queried.
3. Client locally verifies the PIR response against the attested root.
4. Client generates `NonRevocationAir` proof using the privately-obtained witnesses.
5. The STARK proof is verifiable by anyone without knowledge of the query.

**Circuit structure**:
```
VerifiablePIRNonRevocationAir:
  Private witness:
    - revocation_hash (my token's hash)
    - left_neighbor, right_neighbor (from PIR response)
    - Merkle paths for both neighbors (from PIR response)
    - PIR consistency proof (proves response matches committed database)
  
  Public inputs:
    - revocation_set_root (attested by federation)
    - accumulator_value (if using poly-eval accumulator)
  
  Constraints:
    - Standard NonRevocationAir constraints (neighbors bracket my hash)
    - PIR response consistency (the neighbors actually exist in the committed tree)
```

### 6.3 Composing with Presentation Proofs

The verifiable PIR pattern composes into the unified presentation proof (from `privacy-architecture.md`):

```
UnlinkablePresentationProof {
    1. Blinded Issuer Membership (ring proof)
    2. Fold Chain Validity (IVC)
    3. Derivation (Datalog -> ALLOW)
    4. Body Fact Membership
    5. Non-Revocation via Private Lookup  <-- PIR result feeds in here
    6. Presentation Randomization
}
```

The PIR component is invisible to verifiers. The prover obtains their witness privately, then the STARK proves everything. From the verifier's perspective, nothing changes -- they check one unified proof against public inputs.

### 6.4 General Verifiable PIR Circuit Template

```rust
/// Template for verifiable PIR in a STARK:
struct VerifiablePIRAir {
    /// The committed database root (public input).
    database_commitment: BabyBear,
    
    /// The PIR response (private witness).
    response: Vec<BabyBear>,
    
    /// Proof that response is consistent with the committed database.
    /// (Merkle path if Poseidon2, or KZG opening proof if polynomial)
    consistency_proof: ConsistencyWitness,
    
    /// The predicate to evaluate over the response (private or public).
    predicate: Predicate,
    
    /// Predicate evaluation result (public input: 1 bit).
    result: BabyBear,
}

/// Constraints:
/// 1. consistency_proof is valid (response matches database_commitment)
/// 2. predicate(response) == result
/// 3. All intermediate values are correctly computed
```

---

## 7. Concrete Recommendation: Which PIR Variant for Pyana First?

### 7.1 Decision Matrix

| Variant | Setup Cost | Per-Query Cost | PQ-Safe? | Multi-Node Req? | Impl Complexity |
|---------|-----------|---------------|----------|-----------------|-----------------|
| IT-PIR (2-server BabyBear) | None | ~65us server, 256KB upload | YES | 2 non-colluding nodes | LOW |
| IT-PIR (3-server BabyBear) | None | ~16us server, 64KB upload | YES | 3 non-colluding nodes | LOW |
| KZG-PIR (polynomial) | Precompute proofs | ~5ms server | No | 1 node | MEDIUM |
| Lattice cPIR (SimplePIR) | None | ~50ms server, 4MB upload | YES | 1 node | HIGH |
| ORAM-in-STARK | Position map | ~960 rows/query | YES | 1 node | VERY HIGH |

### 7.2 Recommendation: IT-PIR over BabyBear (2-server) as the Primary Path

**Rationale**:
1. **Field-native**: Operates entirely in BabyBear arithmetic. No foreign-field emulation, no lattice parameters, no pairings.
2. **Post-quantum safe**: Security is information-theoretic (unconditional against non-colluding servers).
3. **Trivial implementation**: Matrix-vector multiply in BabyBear. We already have the field arithmetic in `pyana-circuit`.
4. **Natural topology fit**: Pyana federations have multiple nodes. Querying two non-colluding nodes is a natural pattern. Nodes already replicate the database.
5. **Extremely fast**: Sub-millisecond server computation for databases up to 100K entries.
6. **Composable**: The PIR result feeds directly into STARK witness generation without type conversion.
7. **Low communication for practical database sizes**: 256 KB upload for 64K-entry database. Acceptable for network round-trips.

**When to use KZG-PIR instead**:
- Single-server scenarios (only one node available).
- When the database is already committed as a KZG polynomial (cross-chain bridges, Ethereum state).
- When verifiability of the PIR response is needed at the protocol level (KZG provides this "for free" via opening proofs).

### 7.3 Fallback: Lattice cPIR for Single-Server Deployments

If only one federation node is reachable (e.g., light clients behind NAT), lattice-based cPIR provides single-server privacy at the cost of larger communication and server computation. This is the fallback, not the primary path.

---

## 8. Implementation Roadmap

### Phase 1: IT-PIR Library (2-3 weeks)

**Dependencies**: `pyana-circuit::field::BabyBear` (field arithmetic).

**Deliverables**:
1. `pir/src/lib.rs` -- core PIR types and traits:
   ```rust
   pub trait PirDatabase {
       fn num_records(&self) -> usize;
       fn record_size(&self) -> usize;
       fn answer_query(&self, query: &[BabyBear]) -> Vec<BabyBear>;
   }
   
   pub trait PirClient {
       fn generate_shares(&self, index: usize, num_servers: usize) -> Vec<Vec<BabyBear>>;
       fn reconstruct(&self, responses: &[Vec<BabyBear>]) -> Vec<BabyBear>;
   }
   ```
2. `pir/src/it_pir.rs` -- 2-server and 3-server IT-PIR:
   - Query share generation (client-side).
   - Answer computation (server-side matrix-vector multiply).
   - Response reconstruction (client-side addition).
3. `pir/src/indexed.rs` -- indexed PIR for keyword/tag queries:
   - Build inverted index from intent pool.
   - PIR over the inverted index.
4. Unit tests: correctness, privacy (shares are indistinguishable from random).

### Phase 2: Intent Pool Integration (2-3 weeks)

**Dependencies**: Phase 1, `pyana-intent`, `pyana-node`.

**Deliverables**:
1. `node/src/pir_service.rs` -- node-side PIR responder:
   - Maintains PIR-ready database (matrix form) of the intent index.
   - Handles PIR query messages from clients.
   - Updates the matrix incrementally as intents are added/removed.
2. `sdk/src/private_discovery.rs` -- client-side private intent discovery:
   - Selects two non-colluding nodes (from the federation's node list).
   - Generates IT-PIR shares for the desired capability tag.
   - Sends shares to separate nodes, collects responses.
   - Reconstructs the intent ID list.
3. Integration with existing `IntentPool` gossip:
   - Nodes opt-in to PIR service (advertise capability).
   - PIR-enabled nodes maintain the index matrix alongside the gossip pool.
4. Protocol message types in `net/src/message.rs`:
   ```rust
   PirQuery { query_id: u64, shares: Vec<BabyBear> }
   PirResponse { query_id: u64, result: Vec<BabyBear> }
   ```

### Phase 3: Private Non-Revocation Witness Retrieval (3-4 weeks)

**Dependencies**: Phase 1, `pyana-circuit::non_revocation_air`, `pyana-store`.

**Deliverables**:
1. PIR-enabled revocation set query:
   - The revocation tree is indexed as a sorted array.
   - Client PIR-queries for the neighborhood (two adjacent entries bracketing their hash).
   - Requires a slightly different PIR structure: "retrieve the two entries nearest to my private value."
2. **Approximate neighbor PIR protocol**:
   - The sorted revocation set is stored as a balanced binary search tree.
   - The client performs O(log N) PIR queries, one per BST level, to binary-search for the neighborhood.
   - Each query reveals one bit of the search path -- but with IT-PIR, no single server sees any bit.
   - Total: O(log N) IT-PIR queries = O(log N * N) server work. For N = 10K, log N = 14: ~910K muls = ~1ms total.
3. Private Merkle path retrieval:
   - Once the client knows the neighborhood (from step 2), they PIR-query for the Merkle paths of the two neighbors.
   - These Merkle paths become the private witness for `NonRevocationAir`.
4. Integration with `sdk/src/verify.rs`:
   - Add `PrivateRevocationCheck` mode alongside existing `RevocationCheck`.
   - In private mode, use PIR to obtain witnesses. In standard mode, ask a single node directly.

### Phase 4: KZG-PIR for Verifiable Single-Server (4-6 weeks)

**Dependencies**: Phase 1, `hints/src/kzg.rs`, polynomial interpolation.

**Deliverables**:
1. `hints/src/polynomial_database.rs`:
   - Encode a BabyBear database as a polynomial via iNTT.
   - Commit via KZG10.
   - Precompute all opening proofs (O(N log N) via FK technique).
2. `hints/src/pir_kzg.rs`:
   - Client committed-point evaluation protocol.
   - Server-side opening proof retrieval (combined with IT-PIR for obliviousness).
   - Verification: client checks KZG opening against the committed polynomial.
3. Cross-commitment bridge:
   - Prove equivalence between Poseidon2 Merkle root and KZG polynomial commitment.
   - Federation signs both as a pair.
4. Benchmark: compare KZG-PIR vs IT-PIR for varying database sizes.

### Phase 5: Verifiable PIR Composition (6-8 weeks)

**Dependencies**: Phase 3, Phase 4, recursive proof composition from `privacy-architecture.md` Phase 4.

**Deliverables**:
1. `VerifiablePIRAir` circuit template:
   - Proves that a PIR response is consistent with a committed database.
   - Evaluates a predicate over the private response.
   - Outputs only the predicate result as a public input.
2. Integration into the unified presentation proof:
   - Non-revocation witness obtained via PIR feeds into `NonRevocationAir`.
   - The entire presentation is provably derived from the committed federation state.
   - No party (including the proof verifier) learns which specific entry was queried.
3. Composition with unlinkability (from `privacy-architecture.md`):
   - PIR queries themselves should be unlinkable across sessions.
   - Use fresh randomness for each IT-PIR share generation.
   - The STARK proof does not reveal which PIR session produced the witness.

### Dependency Graph

```
Phase 1 (IT-PIR library)
    |
    +---> Phase 2 (Intent pool integration)
    |
    +---> Phase 3 (Private non-revocation)
    |         |
    |         +---> Phase 5 (Verifiable PIR composition)
    |
    +---> Phase 4 (KZG-PIR)
              |
              +---> Phase 5
```

### Existing Primitives Leveraged

| Primitive | Location | Used by PIR for |
|-----------|----------|-----------------|
| BabyBear field arithmetic | `circuit/src/field.rs` | IT-PIR matrix multiply |
| Poseidon2 Merkle tree | `commit/src/poseidon2_tree.rs` | Database commitment, consistency proofs |
| KZG10 commitment | `hints/src/kzg.rs` | Polynomial PIR, verifiable openings |
| Ethereum trusted setup | `hints/src/trusted_setup.rs` | KZG parameters |
| NonRevocationAir | `circuit/src/non_revocation_air.rs` | PIR-enhanced non-revocation proofs |
| IntentPool gossip | `intent/src/gossip.rs` | PIR-enabled intent discovery |
| X25519 sealed secrets | `tokenizer/src/encrypt.rs` | Post-PIR handshake encryption |
| Federation BLS threshold sig | `federation/src/threshold.rs` | Attesting PIR database commitments |
| Node message protocol | `net/src/message.rs` | PIR query/response messages |

---

## 9. Security Considerations

### 9.1 Collusion Resistance

IT-PIR (2-server) breaks completely if both servers collude. Mitigations:
- **Diverse node selection**: Client picks nodes from different operators/jurisdictions.
- **Threshold PIR** (3-of-5): Use 5 servers, any 3 honest suffice. Communication increases proportionally.
- **Fallback to cPIR**: If collusion is suspected, switch to single-server lattice PIR.
- **Audit mechanism**: Nodes can be challenged (via PIR honeypots) to detect collusion.

### 9.2 Metadata Leakage

Even with perfect PIR, timing and volume metadata leak information:
- **Query timing**: The server knows WHEN a query was made, even if not WHAT was queried.
- **Response size**: Variable-length responses reveal information about the query category.
- **Mitigation**: Pad all PIR responses to fixed size. Rate-limit queries to fixed intervals. Use mix networks for delivery.

### 9.3 Intersection Attacks

If the database changes between queries, a server observing "client queried at time T1 and T2" can intersect the database diffs to narrow down which entries the client cares about.

**Mitigation**: Clients should query against a FIXED database snapshot (epoch-bound). The federation attests to epoch-consistent snapshots. All queries within an epoch operate on the same database version.

### 9.4 Post-Quantum Safety

| Component | PQ Status |
|-----------|-----------|
| IT-PIR (BabyBear) | SAFE (information-theoretic) |
| KZG-PIR (BLS12-381) | BROKEN by quantum (DLP) |
| Lattice cPIR (RLWE) | SAFE (believed quantum-resistant) |
| ORAM-in-STARK | SAFE (hash-based) |
| Poseidon2 commitments | SAFE (algebraic hash, no DLP) |
| BLS threshold attestation | BROKEN by quantum (pairing) |

For post-quantum deployments, the primary path (IT-PIR over BabyBear) is unconditionally secure. The KZG-PIR path is a convenience layer that degrades gracefully (falls back to IT-PIR if PQ migration triggers).

---

## 10. Performance Projections

### 10.1 Private Intent Discovery (Phase 2)

| Metric | Value | Notes |
|--------|-------|-------|
| Intent pool size | 50K intents | Typical large federation |
| Capability tag space | 4096 buckets | After hashing |
| IT-PIR upload | 16 KB per server | 4096 * 4 bytes |
| IT-PIR download | 256 bytes per server | 64 intents * 4 bytes |
| Server computation | ~260K muls = 260us | Per query |
| Client computation | Negligible (addition) | Reconstruction |
| End-to-end latency | ~10ms | Dominated by network RTT |
| Queries/second/node | ~3800 | Sustained throughput |

### 10.2 Private Non-Revocation (Phase 3)

| Metric | Value | Notes |
|--------|-------|-------|
| Revocation set size | 10K entries | Typical after 1 year |
| Binary search depth | 14 PIR rounds | log2(10K) |
| Per-round upload | 40 KB per server | 10K * 4 bytes |
| Per-round server work | ~10K muls = 10us | Per level |
| Total server work | 14 * 10us = 140us | All levels |
| Total upload | 14 * 80 KB = 1.1 MB | Both servers combined |
| End-to-end latency | ~50ms | 14 sequential RTTs (pipelineable) |
| With pipelining | ~15ms | Overlap queries with speculative paths |

### 10.3 KZG-PIR (Phase 4)

| Metric | Value | Notes |
|--------|-------|-------|
| Database size | 4096 entries | Limited by SRS degree |
| Precomputed proofs | 4096 * 48 B = 192 KB | One-time cost |
| Query (IT-PIR over proof table) | 16 KB upload, 48 B download | Standard IT-PIR |
| Server computation | ~4K muls + 1 MSM = ~5ms | MSM dominates |
| Client verification | 1 pairing check = ~2ms | Standard KZG verify |
| Verifiability | YES (KZG opening is a proof) | No extra STARK needed |

---

## 11. Open Research Questions

1. **Sublinear-server PIR**: Can we achieve < O(N) server work while remaining BabyBear-native? Existing sublinear PIR (e.g., Piano, Hy-PIR) uses preprocessing + binary fields. Adapting to BabyBear is unexplored.

2. **PIR over Poseidon2 Merkle trees directly**: Can the tree structure be exploited to reduce communication below the flat-database O(N) bound? Hierarchical PIR (one query per tree level) achieves O(arity * depth) communication = O(4 * 16) = 64 field elements. This is much better than O(N) but requires sequential rounds.

3. **Batch PIR**: If a client wants K entries, can they do better than K independent queries? Standard batch PIR achieves amortized O(N/K) per entry (cuckoo hashing approach). This is relevant for agents checking multiple nullifiers.

4. **Updatable PIR databases**: When the intent pool changes (intents added/removed), how to efficiently update the PIR matrix without full recomputation? Rank-1 updates to the matrix are O(N) but with small constants.

5. **PIR + accumulator synergy**: The polynomial-evaluation accumulator (from `accumulators.md`) already encodes the revocation set as a polynomial. Can we PIR-evaluate this polynomial directly, getting both privacy AND O(1) non-membership in one shot?

6. **Rate-limiting private queries**: How to prevent a malicious client from bulk-extracting the entire database via repeated PIR queries, while maintaining query privacy? The SPIR (symmetric PIR) literature addresses this via token-based rate limiting.
