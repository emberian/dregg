# Privacy Architecture: Path to Anonymous Credential Parity

## Current State Assessment

Pyana provides zero-knowledge authorization proofs where a prover demonstrates "I hold a valid attenuated capability chain from a federation-registered issuer that satisfies your request" without revealing the chain, intermediate states, or other capabilities. The proof system (BabyBear STARK + Poseidon2) covers: fold chain validity (attenuation is monotonic), multi-step Datalog derivation (ALLOW conclusion), issuer membership in the federation Merkle tree, and body fact membership (facts referenced in derivation actually exist in the committed tree). However, several properties expected of production anonymous credential systems are missing or incomplete: presentations are linkable (same `final_root` across proofs), the issuer was identifiable until recently (ring membership now in progress via `BlindedMerklePoseidon2StarkAir`), selective disclosure is commitment-bound but not cryptographically enforced at the circuit level in all paths, the fold chain is locally validated rather than STARK-proven end-to-end, and the federation sees turn content in cleartext.

---

## Target State: What "Anonymous Credential Parity" Means for Pyana

Parity with Idemix/BBS+/AnonCreds means:

1. **Unlinkable multi-show**: The same credential presented N times produces N presentations that cannot be correlated by any party (including colluding verifiers).

2. **Issuer anonymity within set**: A verifier cannot determine which federation member issued the underlying credential. (Ring membership -- in progress.)

3. **Predicate proofs over attributes**: "Prove age >= 18" or "prove balance >= X" without revealing the exact value. Arbitrary boolean combinations of such predicates.

4. **Selective disclosure with cryptographic binding**: The prover chooses which attributes to reveal; the proof cryptographically guarantees that unrevealed attributes satisfy the policy without revealing them.

5. **Revocable anonymity**: Credentials can be revoked without breaking unlinkability for non-revoked credentials.

6. **Offline verification**: All of the above must work without contacting the issuer or federation (already achieved for the STARK path).

---

## Gap Analysis

### Gap 1: Presentation Linkability (Impact: CRITICAL / Difficulty: MEDIUM)

**Problem**: `PresentationPublicInputs` exposes `initial_root` and `final_root`. These are deterministic for a given token -- any verifier receiving two proofs can check whether they share the same `final_root` and conclude they came from the same credential.

**Root cause**: The fact-set Merkle root is a static commitment. The same set of facts always produces the same root.

**What ring membership solves**: `BlindedMerklePoseidon2StarkAir` makes the *issuer leaf* unlinkable (`blinded_leaf = hash_2_to_1(leaf_hash, fresh_blinding)`). But the fold chain's `final_root` remains deterministic.

**What remains**: Even with blinded issuer membership, two presentations from the same attenuated token share the same `final_root` (public input to the derivation AIR). This is the primary linkability vector.

### Gap 2: Federation Transparency (Impact: HIGH / Difficulty: HIGH)

**Problem**: Turns submitted to the federation are in cleartext. Validators see all cell state transitions, action parameters, and delegation operations.

**Root cause**: Federation consensus requires validators to check conservation invariants, nonce ordering, and program predicates over the actual state.

### Gap 3: Fold Chain Not Fully STARK-Proven (Impact: MEDIUM / Difficulty: MEDIUM)

**Problem**: The `FoldAir` uses the constraint prover (local verification) rather than a real STARK for each fold step. The `ValidatedIvcProof` path does produce real STARKs for individual fold membership proofs and the hash chain, but the recursive composition (single proof covering fold validity + derivation + membership) is not yet operational.

**Implication**: A remote verifier trusting only the issuer membership STARK must separately trust the fold chain was honestly computed, or receive the `ValidatedIvcProof` with N per-step STARKs (proof size grows linearly in chain length).

### Gap 4: Predicate Proofs (Impact: MEDIUM / Difficulty: LOW)

**Problem**: Range proofs (prove X >= threshold) require the `CircuitLtCheck` constraint, which has landed. But there is no general "predicate proof" API that lets a credential holder prove arbitrary boolean predicates over attributes without revealing them.

**What exists**: `lt_check` and `gte_check` in the derivation AIR prove ordering relationships between variables and constants within a single derivation step.

**What is missing**: A builder API for composing predicates like "age >= 18 AND country IN {US, CA, UK} AND subscription_tier >= 2" into a single STARK proof.

### Gap 5: Selective Disclosure Not Circuit-Enforced End-to-End (Impact: MEDIUM / Difficulty: LOW)

**Problem**: `revealed_facts_commitment` is a Poseidon2 hash over the revealed fact hashes. The verifier recomputes this from plaintext facts and checks it matches the public input. This is sound. However, the binding between "these revealed facts are EXACTLY the facts that appeared in the derivation trace" relies on the derivation AIR's `body_hash` columns matching the commitment -- the current composition path does not produce a single unified proof covering both.

**What is needed**: The `BodyMembershipProof` composition (derivation STARK + per-fact membership STARKs) already solves this for body facts. Extending it to bind `revealed_facts_commitment` into the same proof composition completes the circuit.

### Gap 6: Revocation vs Unlinkability Tension (Impact: MEDIUM / Difficulty: HIGH)

**Problem**: Revocation in pyana uses the `NonRevocationAir` (sorted Merkle non-membership proof). This proves "my capability's ancestor hashes are not in the revocation tree." But if presentations are perfectly unlinkable, the revoker cannot identify which credential to add to the revocation set -- they need to know the `leaf_hash` (or some identifier) of the thing being revoked.

---

## Concrete Architecture

### Final Public Inputs (Target State)

A fully private, unlinkable presentation proof exposes:

```
PublicInputs {
    federation_root: BabyBear,       // which federation (public, shared)
    request_predicate: BabyBear,     // what is being authorized
    timestamp: BabyBear,             // freshness bound
    blinded_presentation_tag: BabyBear,  // NEW: randomized, unlinkable
    revocation_set_root: BabyBear,   // NEW: proves non-revocation
    revealed_facts_commitment: BabyBear, // zero if fully private
}
```

Removed from public inputs: `initial_root`, `final_root`. These become private witness.

The `blinded_presentation_tag` is: `Poseidon2(final_root || nonce || presentation_randomness)`. It is fresh per presentation, unlinkable, but deterministic given the token and nonce (for replay detection within a session if desired).

### Proof Structure (Target)

```
UnlinkablePresentationProof {
    // Single recursive STARK covering all sub-proofs:
    unified_proof: StarkProof,
    
    // Public inputs (everything the verifier sees):
    public_inputs: UnlinkablePublicInputs,
}
```

Internally, the unified proof composes:

```
1. Blinded Issuer Membership (ring proof)
   - Proves: "some leaf in the federation tree is my issuer"
   - Public: blinded_leaf, federation_root
   - Private: leaf_hash, blinding_factor, Merkle path

2. Fold Chain Validity (IVC)
   - Proves: "attenuation chain from issuer_root to final_root is valid"
   - Public: (NONE -- initial_root and final_root are now private)
   - Private: initial_root, final_root, all fold witnesses
   - Binding: final_root feeds into derivation as state_root

3. Derivation (multi-step Datalog -> ALLOW)
   - Proves: "the final capability set authorizes this request"
   - Public: request_predicate (what is being asked)
   - Private: state_root (= final_root), all rules, body facts, substitutions
   - Binding: state_root comes from fold chain; body facts proven in tree

4. Body Fact Membership
   - Proves: "each body fact in the derivation exists in the tree at final_root"
   - Public: (NONE -- final_root is private, fact hashes are private)
   - Private: fact hashes, Merkle paths
   - Binding: shared state_root with derivation

5. Non-Revocation
   - Proves: "my credential's ancestor hashes are not in the revocation set"
   - Public: revocation_set_root
   - Private: ancestor hashes, non-membership witnesses

6. Presentation Randomization
   - Proves: "blinded_presentation_tag is correctly derived from final_root"
   - Public: blinded_presentation_tag
   - Private: final_root, nonce, randomness
```

### Circuit Changes Required

| Component | Current State | Required Change |
|-----------|--------------|-----------------|
| `PresentationPublicInputs` | Exposes `initial_root`, `final_root` | Remove both; add `blinded_presentation_tag` |
| `PresentationAir` | Meta-AIR dispatching to sub-AIRs | Unified recursive AIR with shared private `final_root` |
| `BlindedMerklePoseidon2StarkAir` | Standalone AIR (done) | Compose into unified proof |
| `IvcAir` / `StateTransitionAir` | Hash-chain STARK (done) | Final root becomes private witness output |
| `MultiStepDerivationAir` | `initial_state_root` is public input [0] | Make it private; prove equality with IVC final_root internally |
| `NonRevocationAir` | Standalone AIR (done) | Compose into unified proof; feed ancestor hashes from fold chain |
| New: `PresentationRandomizationAir` | Does not exist | Proves `tag = Poseidon2(final_root \|\| nonce \|\| randomness)` |
| Recursive verifier | Pairs working; heterogeneous composition not yet | Required for single-proof output |

### Blinded Presentation Tag Construction

```
presentation_randomness <- random_field_element()
session_nonce <- counter or timestamp (optional, for replay detection)

blinded_presentation_tag = Poseidon2(
    final_root,
    presentation_randomness,
    session_nonce
)
```

Properties:
- **Unlinkable**: Fresh randomness per presentation means different tags each time.
- **Correct**: The STARK proves this was derived from the real `final_root` (which itself was proven valid by the fold chain).
- **Replay-resistant**: The `timestamp` public input provides time-bounding; the verifier can additionally require unique tags within a session.

---

## Migration Path

### Phase 1: Complete Issuer Unlinkability (weeks, in progress)

1. Finish integrating `BlindedMerklePoseidon2StarkAir` into `prove_stark_poseidon2()` as the default path.
2. Update `PresentationWitness` so `blinding_factor` is always non-zero in FullyPrivate mode.
3. Wire `generate_blinded_merkle_poseidon2_stark_proof()` through the bridge layer.

**Result**: Issuer is anonymous within the federation ring. Presentations from different issuers are indistinguishable. But same-token presentations remain linkable via `final_root`.

### Phase 2: Remove final_root from Public Inputs (weeks)

1. Create `PresentationRandomizationAir`: trivial AIR proving `tag = Poseidon2(root, randomness, nonce)`. Width 4, 1-2 rows.
2. Move `initial_root` and `final_root` from `PresentationPublicInputs` to private witness.
3. Add `blinded_presentation_tag` to public inputs.
4. Update the derivation AIR binding: instead of checking `derivation.state_root == public_input.final_root`, the constraint becomes `derivation.state_root == fold_chain.final_root` (internal consistency, both private).
5. Update `verify()` on `RealPresentationProof` to no longer require `final_root` in public inputs.

**Result**: Presentations are fully unlinkable. Two presentations from the same token produce different `blinded_presentation_tag` values. This is the single highest-impact change.

**Breaking change**: Verifiers can no longer cache final_root-based lookups. The revocation channel must use a different identifier (see Phase 5).

### Phase 3: Predicate Proof API (weeks)

1. Build a `PredicateBuilder` in the bridge crate:
   ```rust
   let proof = PredicateBuilder::new(token, federation_root)
       .require_gte("age", 18)
       .require_lt("debt", 10000)
       .require_membership("country", &["US", "CA", "UK"])
       .prove()?;
   ```
2. Internally, this maps to `CircuitLtCheck` / `CircuitGteCheck` / `memberof_checks` in the `DerivationWitness`.
3. The existing multi-step AIR already supports these checks -- the work is building the ergonomic API and ensuring the full composition (body membership + derivation) produces a single verifiable proof.

**Result**: Predicate proofs work over committed attributes. No new circuit machinery needed -- only API ergonomics.

### Phase 4: Unified Recursive Proof (months)

1. Extend `build_recursive_ivc_chain` (Plonky3 recursive verifier) to compose heterogeneous AIRs: fold + derivation + membership + non-revocation in a single recursive proof.
2. Alternatively: use the existing `StateTransitionAir` STARK as the outer proof and embed sub-proof verification as additional trace rows (STARK-in-STARK).
3. Target: a single `StarkProof` of ~48-80 KiB covering all components.

**Result**: Verifier checks ONE proof. No composition logic needed on the verification side. Proof size is constant regardless of chain length, predicate count, or derivation depth.

**This is the hardest phase** and depends on the recursive verifier work already in progress. It can be deferred -- the system is secure (just not optimally compact) with the multi-proof composition from Phases 1-3.

### Phase 5: Revocable Unlinkability (months)

Design: Camenisch-Lysyanskaya-style revocable anonymity adapted to STARKs.

1. At issuance, the issuer assigns a `revocation_handle = Poseidon2(issuer_secret, credential_id)`. This handle is known only to the issuer.
2. The credential holder proves non-membership of their `revocation_handle` in the revocation set -- but the handle itself is private witness (never revealed to verifiers).
3. To revoke, the issuer adds the handle to the revocation set. The next time the holder tries to prove non-revocation, their proof fails (the handle IS in the set now).
4. The `NonRevocationAir` already proves non-membership. The extension is: derive `revocation_handle` from the credential's `initial_root` (or a dedicated field) inside the circuit, then prove non-membership of that derived value.

**Key constraint**: The `revocation_handle` must be derivable by the issuer (who knows `issuer_secret` + `credential_id`) but not by verifiers (who see only blinded presentations). This maintains unlinkability for verifiers while preserving the issuer's ability to revoke.

**Circuit addition**:
```
// Inside the unified proof:
revocation_handle = Poseidon2(issuer_leaf_hash, credential_nonce)  // derived from private witness
prove_non_membership(revocation_handle, revocation_set_root)       // existing NonRevocationAir
```

The `credential_nonce` is embedded in the token at issuance and travels through the fold chain as a fact. The issuer records `(credential_id -> revocation_handle)` in their local database.

### Phase 6: Federation Privacy (future, research-grade)

Three options, ordered by feasibility:

**Option A: Encrypted Turns + State Proofs (most feasible)**
- Turns are encrypted under a federation threshold key (BLS12-381 from `hints` crate).
- Validators decrypt collectively, validate, re-encrypt results.
- Privacy: individual validators cannot reconstruct without threshold participation.
- Limitation: the validator SET still sees everything. This is privacy from external observers, not from the federation itself.

**Option B: Validium-Style Blind Ordering**
- Federation orders encrypted turn hashes without seeing content.
- Agents prove state transition validity via STARKs submitted alongside encrypted turns.
- Validators verify: (a) STARK proof of valid transition, (b) nullifier freshness (in the clear), (c) ordering consistency.
- Privacy: validators see nullifiers and proofs but NOT turn content or state.
- Cost: agents must generate a STARK for every state transition (not just authorization presentations).

**Option C: Full ZK Execution (Zcash model)**
- Every turn is a shielded transaction: validators see only proofs and nullifiers.
- Content, sender, receiver, amounts -- all hidden.
- Requires: every cell state transition to be STARK-provable (massive circuit for the full turn executor).
- This is FHE-grade difficulty adapted to STARKs. Not practical near-term.

**Recommendation**: Option B for the medium term. Pyana's existing receipt-chain model (pre/post state hashes per turn) already provides the "state transition" structure that a validity proof would cover. The `StateTransitionAir` pattern from IVC can be adapted: instead of proving fold-chain hash continuity, prove turn-execution hash continuity (`pre_state -> effects -> post_state`).

---

## Tradeoffs

### Privacy vs Performance

| Feature | Proof Gen Time | Proof Size | Privacy Gain |
|---------|---------------|-----------|--------------|
| Current (no blinding) | ~200ms | ~45 KiB | Issuer identifiable, presentations linkable |
| + Ring membership (Phase 1) | +50ms | +8 KiB | Issuer anonymous |
| + Blinded final_root (Phase 2) | +20ms | +2 KiB | Fully unlinkable |
| + Predicates (Phase 3) | +0ms (already in derivation) | +0 | Attribute predicates |
| + Unified recursive (Phase 4) | +500ms initially, amortizes | -30 KiB (constant) | Single proof, minimum leakage |
| + Revocable unlinkability (Phase 5) | +100ms (non-membership STARK) | +15 KiB | Revocable + unlinkable |
| + Federation privacy (Phase 6B) | +1-2s per turn | +80 KiB per turn | Validator-blind execution |

### Privacy vs Complexity

- **Phases 1-3**: Incremental. Each can land independently. No breaking protocol changes between agents.
- **Phase 4**: Requires recursive verifier maturity. Can be deferred indefinitely -- multi-proof composition is secure, just larger.
- **Phase 5**: Requires careful key management (issuer must track revocation handles). Protocol-level change: new field in token format.
- **Phase 6**: Research-grade. Changes the federation protocol fundamentally.

### Privacy vs Revocability

The fundamental tension: perfect unlinkability means no party can identify a specific credential holder across presentations. Revocation requires the ISSUER (but not verifiers) to identify credentials.

Pyana's resolution: the `revocation_handle` is a PRF output known only to the issuer. Verifiers never see it (it is private witness in the non-revocation proof). The issuer can revoke by handle without verifiers learning which presentations are affected. This achieves "issuer-revocable, verifier-unlinkable" -- the strongest achievable property without trusted hardware.

### Post-Quantum Safety

All additions maintain PQ safety:
- Blinding uses Poseidon2 (algebraic hash, no curves).
- Presentation randomization uses Poseidon2.
- Non-revocation uses Poseidon2 Merkle proofs.
- Predicates use BabyBear field arithmetic.
- The recursive verifier uses FRI (hash-based).

The only non-PQ component remains BLS12-381 threshold signatures in the federation layer (on the PQ migration roadmap, awaiting lattice threshold sig standardization).

---

## Comparison: Pyana vs Idemix/BBS+/AnonCreds (Target State)

| Property | Idemix | BBS+ | AnonCreds | Pyana (target) |
|----------|--------|------|-----------|----------------|
| Unlinkable multi-show | Yes | Yes | Yes | Yes (Phase 2) |
| Selective disclosure | Yes | Yes | Yes | Yes (existing + Phase 3) |
| Predicate proofs | Limited (GE only) | No | Limited | Yes, arbitrary (LT/GTE/membership) |
| Issuer anonymity | No | No | No | Yes (Phase 1, ring proof) |
| Post-quantum | No | No | No | Yes (STARK-native) |
| Offline verify | No (CRL required) | Yes | Partial | Yes (proof + attested root) |
| Proof size | ~2 KiB | ~1 KiB | ~5 KiB | ~48-80 KiB (STARK) |
| Prove time | ~50ms | ~10ms | ~100ms | ~200-500ms |
| Verify time | ~30ms | ~5ms | ~50ms | ~10ms |
| Revocable + unlinkable | Via accumulators | No (standard) | Via rev. registry | Yes (Phase 5) |
| Programmable policy | No | No | Limited Datalog | Full Datalog (32 steps, 8 body atoms) |

Pyana's tradeoff: larger proofs and slower generation in exchange for post-quantum security, programmable policy (full Datalog in-STARK), issuer anonymity, and offline verification without CRL distribution.

---

## Summary of Required Changes

| Priority | Change | Crate(s) | Breaking? |
|----------|--------|----------|-----------|
| P0 (now) | Wire blinded membership into bridge presentation | bridge, circuit | No |
| P1 (next) | Remove `initial_root`/`final_root` from public inputs | circuit, bridge, sdk | Yes (verifier API) |
| P1 (next) | Add `PresentationRandomizationAir` | circuit | No |
| P2 | `PredicateBuilder` API | bridge, sdk | No |
| P2 | Compose non-revocation into presentation | circuit, bridge | No |
| P3 | Unified recursive proof | circuit (plonky3_recursion) | No (additive) |
| P3 | Revocable unlinkability (handle derivation in-circuit) | circuit, token | Yes (token format) |
| P4 | Federation privacy (Option B: blind ordering) | federation, turn, circuit | Yes (protocol) |
