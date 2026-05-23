# Mina Bridge Design: Proof-Carrying from Day 1

## Executive Summary

Pyana and Mina share the same proof system family (Kimchi/Pickles over Pasta curves).
This means a Mina bridge can be **fully proof-carrying** without any external wrapping
service, compression, or curve mismatch workarounds. Unlike the Midnight bridge
(blocked on BLS12-381 wrapping, operating at Level 1.5 optimistic), the Mina bridge
can deliver Level 2 security immediately using existing code.

**Key insight:** Our `poseidon_stark_verifier_circuit.rs` already produces a Kimchi
proof (on Vesta) that verifies a BabyBear STARK. Wrapping that into Pickles gives us
a valid Mina-compatible recursive proof. The entire pipeline exists in code TODAY.

---

## What Mina Gets Us That Midnight Cannot

| Property | Midnight | Mina |
|----------|----------|------|
| Proof system | PLONK/BLS12-381 (different family) | Kimchi/Pasta (same family) |
| Native curve match | No (BabyBear -> BLS12-381 requires wrapping) | Yes (Pasta cycle shared) |
| STARK verification | Blocked (no BLS12-381 PLONK wrapper) | Working (`PoseidonStarkVerifierCircuit`) |
| Recursive composition | N/A (no shared recursion) | Yes (Pickles dual-curve architecture) |
| Time to production | Months (need external wrapper) | Weeks (pipeline exists) |
| Security model | Level 1.5 (optimistic + dispute) | Level 2 (computational soundness, no federation) |
| Composability | Isolated contract state | zkApp-to-zkApp recursive proofs |

---

## The STARK-in-Pickles Pipeline (Already Built)

```
Effect VM / Presentation / Authorization (BabyBear AIR)
    |
    | prove_poseidon() [poseidon_stark.rs]
    v
PoseidonStarkProof (~48 KiB, Poseidon-committed FRI)
    |
    | PoseidonStarkVerifierCircuit::prove() [poseidon_stark_verifier_circuit.rs]
    v
Kimchi proof on Vesta (~5-10 KiB, verifies the STARK)
    |
    | prove_recursive_step() [pickles.rs]
    v
PicklesRecursiveProof (constant-size, IPA accumulator forwarding)
    |
    | prove_dual_curve_step() + prove_dual_curve_wrap() [step_verifier.rs, wrap_verifier.rs]
    v
DualCurveWrapProof (Pallas proof, standalone-verifiable)
```

This is already a valid Mina proof structure. A Mina full node's verifier performs
exactly the same `batch_dlog_accumulator_check` that our `verify_standalone_dual_curve_wrap`
calls.

---

## Constraint Budget Analysis

### What Fits in a Mina Transaction?

Mina zkApp methods use Kimchi with domain sizes from 2^16 to 2^18 (typical: 2^17 = 131072 rows).
The o1js SDK auto-selects domain size based on gate count.

| Circuit | Our Gate Count | Fits in Mina? |
|---------|---------------|---------------|
| IPA verifier (standalone.rs) | ~2,686 rows (2^12) | Yes (trivially) |
| Step verifier (step_verifier.rs) | ~500 rows | Yes (trivially) |
| Wrap verifier (wrap_verifier.rs) | ~4,700 rows (2^13) | Yes (trivially) |
| STARK verifier, 1 query (poseidon_stark_verifier_circuit.rs) | ~225 rows | Yes |
| STARK verifier, 80 queries (full) | ~18,500 rows (2^15) | Yes |
| Recursive fold chain (pickles.rs) | ~30 rows per step | Yes |

**All of our circuits fit comfortably within Mina's constraint budget.**
The full 80-query STARK verifier at 18,500 rows is well under the 131,072 row
limit of a standard Mina zkApp method.

### Existing Constants (from ipa_verifier.rs)

```
IPA_ROUNDS = 15  (supports SRS up to 2^15)
ENDOMUL_ROWS_PER_SCALAR = 33
BULLET_REDUCE_ROWS_PER_ROUND = 4 * 33 + 4 = 136
Wrap verifier: 6 public inputs + 15*136 bullet_reduce + ~170 final = ~4,700 rows
```

---

## o1js Smart Contract Design

### Phase 1: State Root Verifier (the "anchor" contract)

```typescript
import { SmartContract, State, method, Proof, Field, Struct } from 'o1js';

class PyanaStateRoot extends Struct({
  root: Field,           // Poseidon hash of the pyana federation state
  epoch: Field,          // monotonic epoch counter
  proofDigest: Field,    // hash binding to the Pickles proof
}) {}

class PyanaVerifier extends SmartContract {
  @state(Field) currentRoot = State<Field>();
  @state(Field) currentEpoch = State<Field>();
  @state(Field) proofCount = State<Field>();

  /**
   * Update the pyana state root on Mina.
   *
   * The proof parameter is a Pickles-wrapped verification of:
   * 1. A BabyBear STARK (pyana Effect VM execution)
   * 2. Verified inside Kimchi (PoseidonStarkVerifierCircuit)
   * 3. Wrapped into Pickles (recursive, constant-size)
   *
   * Because we share the Pasta proof system, this proof IS a valid
   * Mina proof. The on-chain verifier just checks the recursive structure.
   */
  @method async updateRoot(
    newRoot: PyanaStateRoot,
    transitionProof: Proof<PyanaStateRoot, PyanaStateRoot>
  ) {
    // Verify the recursive proof (Pickles verification is free on Mina!)
    transitionProof.verify();

    // Check monotonic epoch
    const currentEpoch = this.currentEpoch.getAndRequireEquals();
    newRoot.epoch.assertGreaterThan(currentEpoch);

    // Check the proof binds to the new root
    transitionProof.publicOutput.root.assertEquals(newRoot.root);

    // Update state
    this.currentRoot.set(newRoot.root);
    this.currentEpoch.set(newRoot.epoch);
    this.proofCount.set(this.proofCount.getAndRequireEquals().add(1));
  }
}
```

### Phase 2: Bridge Operations

```typescript
class BridgeLock extends Struct({
  sender: Field,        // pyana capability hash (Poseidon over Fp)
  amount: Field,        // value to lock
  recipient: Field,     // Mina account hash
  nonce: Field,         // replay protection
}) {}

class PyanaMinaBridge extends SmartContract {
  @state(Field) pyanaRoot = State<Field>();
  @state(Field) lockedAmount = State<Field>();
  @state(Field) nullifierRoot = State<Field>();

  /**
   * Lock tokens from pyana onto Mina.
   *
   * Proof demonstrates:
   * 1. The lock note exists in the pyana state (Merkle membership)
   * 2. The capability authorizing the transfer is valid (Effect VM execution)
   * 3. The fold chain from issuance to this point is sound
   *
   * All verified recursively via Pickles. No federation attestation needed.
   */
  @method async lockFromPyana(
    lock: BridgeLock,
    membershipProof: Proof<BridgeLock, Field>,  // proves note in pyana state
    authorizationProof: Proof<Field, Field>,    // proves capability chain
  ) {
    membershipProof.verify();
    authorizationProof.verify();

    // Check the membership proof binds to the current pyana root
    const root = this.pyanaRoot.getAndRequireEquals();
    membershipProof.publicOutput.assertEquals(root);

    // Verify nonce hasn't been used (nullifier check)
    // ... (Merkle non-membership proof against nullifierRoot)

    // Mint/unlock the equivalent on Mina
    // ... (token transfer or account update)
  }

  /**
   * Unlock tokens back to pyana.
   *
   * Burns on Mina, emits an event that pyana's observer picks up.
   * The pyana observer then creates a provable state transition to mint.
   */
  @method async unlockToPyana(amount: Field, pyanaRecipient: Field) {
    // Verify caller owns the tokens
    // Burn them
    // Emit event for pyana observer
    this.emitEvent('unlock', { amount, recipient: pyanaRecipient });
  }
}
```

### Phase 3: Capability-Controlled Mina Accounts

```typescript
/**
 * A Mina zkApp whose state transitions REQUIRE a pyana proof.
 *
 * This is the "sovereign cell on Mina" concept: the zkApp is part of
 * pyana's governed namespace but lives on the Mina chain.
 */
class PyanaSovereignCell extends SmartContract {
  @state(Field) capabilityRoot = State<Field>();  // root of authorized caps
  @state(Field) cellState = State<Field>();       // arbitrary application state

  /**
   * Perform a state transition, authorized by a pyana capability proof.
   *
   * The proof carries the full authorization chain:
   * 1. Capability issuance (factory proof)
   * 2. Attenuation chain (fold proofs)
   * 3. Authorization evaluation (Effect VM STARK)
   * 4. STARK-in-Pickles wrapping (recursive Pasta proof)
   *
   * The Mina chain acts as a settlement layer: pyana proves authorization,
   * Mina stores and enforces the resulting state.
   */
  @method async transition(
    newState: Field,
    capabilityProof: Proof<Field, Field>,  // pyana authorization chain
  ) {
    capabilityProof.verify();

    // The proof's public output is the capability root that authorized this
    const authorizedRoot = capabilityProof.publicOutput;
    const storedRoot = this.capabilityRoot.getAndRequireEquals();
    authorizedRoot.assertEquals(storedRoot);

    // Apply the state transition
    this.cellState.set(newState);
  }
}
```

---

## CapTP Integration: Mina zkApps as Pyana Objects

### Mounting Pattern

A Mina zkApp appears in pyana's governed namespace:

```
/bridges/mina/swap        -> PyanaMinaBridge (lock/unlock operations)
/bridges/mina/anchor      -> PyanaVerifier (state root updates)
/bridges/mina/cells/0x... -> PyanaSovereignCell (application state)
```

### CapTP Session Architecture

```
pyana node                Mina bridge gateway               Mina full node
    |                           |                               |
    | CapTP.send(                |                               |
    |   target="/bridges/mina/  |                               |
    |     swap",                |                               |
    |   method="lockFromPyana", |                               |
    |   args=[proof, amount]    |                               |
    | )                         |                               |
    |                           | 1. Validate proof locally      |
    |                           | 2. Construct Mina transaction  |
    |                           | 3. Submit via GraphQL API      |
    |                           |------------------------------->|
    |                           |                               | Verify Pickles
    |                           |                               | proof on-chain
    |                           |                               | Apply state
    |                           |<-------------------------------|
    |                           |   tx_hash                     |
    |<--------------------------|                               |
    |   result: Ok(tx_hash)     |                               |
```

### Why Mina zkApps ARE Sovereign Cells

A sovereign cell has:
1. **State** (on-chain) -- zkApp has 8 state fields (Field elements, same Fp)
2. **Receives messages** -- zkApp methods are callable
3. **Produces proofs** -- every Mina state transition IS a proof
4. **Is governable** -- pyana capability proofs control access
5. **Composes recursively** -- zkApp A can verify proofs from zkApp B

This is a much richer integration than Midnight, where we can only post
attestations to a contract. On Mina, the zkApp IS the pyana object.

---

## STARK-in-Pickles Performance Analysis

### Current Numbers (from existing code)

| Stage | Time | Size | Constraint Budget |
|-------|------|------|-------------------|
| BabyBear STARK (Effect VM) | ~64 us | ~48 KiB | N/A (prover only) |
| Poseidon STARK verifier (Kimchi, 1 query) | ~1-2s | ~5-10 KiB | 225 rows |
| Poseidon STARK verifier (Kimchi, 80 queries) | ~10-30s | ~5-10 KiB | 18,500 rows |
| Pickles recursive step | ~3-5s | ~5 KiB | ~30 rows + PI |
| Pickles wrap (binding) | ~1-2s | ~5 KiB | 17 rows |
| Pickles wrap (standalone EC) | ~3-5s | ~15-20 KiB | 4,700 rows |
| **Total end-to-end** | **~15-40s** | **~5 KiB final** | **< 20K rows** |

### Is Recursive Decomposition Needed?

**No.** The full 80-query STARK verifier at 18,500 rows fits in domain 2^15 (32,768).
Mina's standard domain sizes go up to 2^18. A single zkApp method call can
verify the entire STARK proof without decomposition.

If we want faster proving (parallel), we COULD split into multiple recursion steps:
- Step 1: Verify 20 queries (4,500 rows)
- Step 2: Verify 20 more + fold step 1 (4,500 rows)
- Step 3: Verify 20 more + fold steps 1-2 (4,500 rows)
- Step 4: Verify final 20 + fold steps 1-3 (4,500 rows)

Each step proves in ~2s (domain 2^13), total ~8s parallel vs ~30s monolithic.
But this is an optimization, not a necessity.

---

## What Existing Code Bridges the Gap

### Already Working (verified by tests in the codebase)

| Component | File | Status |
|-----------|------|--------|
| Kimchi backend (Pasta curves) | `circuit/src/backends/mina/mod.rs` | Working, tested |
| Poseidon hash (same as Mina on-chain) | `poseidon_hash_4_to_1`, `poseidon_hash_bytes` | Working |
| Merkle membership circuit (Kimchi) | `build_merkle_membership_circuit` | Working, tested |
| Pickles recursive proof (assisted) | `prove_recursive_step`, `verify_recursive_proof` | Working, tested |
| Pickles dual-curve step/wrap | `prove_dual_curve_step`, `prove_dual_curve_wrap` | Working, tested |
| Standalone IPA verifier (Mina-equivalent) | `prove_standalone_recursive_step` | Working, tested |
| STARK-in-Pickles (Kimchi verifies STARK) | `PoseidonStarkVerifierCircuit::prove/verify` | Working, tested |
| Full recursive chain | `prove_full_recursive_chain` | Working, tested |
| RecursionChallenge extraction | `extract_recursion_challenge` | Working |
| GLV encoding for EndoMul | `glv_encode_for_endomul` | Working |

### Needs Implementation

| Component | Effort | Description |
|-----------|--------|-------------|
| o1js contract (TypeScript) | 2-3 days | Translate our proof types to o1js `Struct`/`Proof` |
| Proof format adapter | 1-2 days | Serialize `DualCurveWrapProof` into o1js-compatible format |
| CapTP bridge gateway | 3-5 days | Node.js service: CapTP -> Mina GraphQL submission |
| Mina event observer | 2-3 days | Mirror of `midnight_observer.rs` for Mina events |
| State root oracle | 1 day | Feed pyana state roots into `PyanaVerifier` contract |
| Integration tests | 2-3 days | End-to-end: pyana proof -> Mina chain -> verification |

---

## Implementation Timeline

### Phase 1: Proof Submission (2 weeks)

**Goal:** A pyana proof lands on Mina and is verified on-chain.

1. **Week 1:**
   - Write `PyanaVerifier` o1js contract
   - Implement proof format adapter (Rust `DualCurveWrapProof` -> o1js `Proof`)
   - Deploy to Mina devnet (Berkeley testnet)

2. **Week 2:**
   - Write bridge gateway (CapTP -> Mina tx submission)
   - End-to-end test: Effect VM STARK -> Pickles wrap -> Mina on-chain verification
   - Measure gas costs and latency

### Phase 2: Bridge Operations (2 weeks)

**Goal:** Lock/unlock/transfer with STARK proof verification.

3. **Week 3:**
   - Write `PyanaMinaBridge` contract (lock/unlock methods)
   - Implement nullifier tracking (Merkle non-membership)
   - Mina event observer for `unlockToPyana` events

4. **Week 4:**
   - Integrate with pyana's note system (`BridgeDestination::Mina`)
   - CapTP routing: `/bridges/mina/swap` namespace mount
   - Bidirectional transfer tests

### Phase 3: Sovereign Cells (2 weeks)

**Goal:** Pyana capabilities control Mina zkApp state.

5. **Week 5:**
   - `PyanaSovereignCell` o1js contract
   - Capability proof verification on Mina
   - State transition authorization via pyana Effect VM proofs

6. **Week 6:**
   - Governed namespace integration
   - Multi-cell composition (zkApp A verifies proof from zkApp B)
   - Performance optimization (parallel recursion decomposition)

### Phase 4: Composability (2 weeks)

**Goal:** Full ecosystem integration.

7. **Week 7:**
   - Mina zkApps compose with pyana proofs recursively
   - Cross-zkApp authorization (pyana proof controls multiple Mina contracts)
   - DeFi primitives: swap, lending, governed pools

8. **Week 8:**
   - Mainnet deployment preparation
   - Security audit of proof format adapter
   - Documentation and SDK for third-party developers

**Total: 8 weeks to production.**

---

## Comparison: Mina Bridge vs. Midnight Bridge

| Dimension | Midnight (current) | Mina (this design) |
|-----------|-------------------|-------------------|
| Security level | 1.5 (optimistic + dispute) | 2 (computational soundness) |
| Federation requirement | Yes (for relay) | No (proofs are self-validating) |
| Time to finality | 6h dispute window | 1 Mina block (~3 min) |
| Proof format | Attestation signature | Native Pickles recursive proof |
| Wrapping service | Needed for Level 2 | Not needed (native curves) |
| On-chain verification cost | ~920K gates (BLS12-381) | Free (Pickles recursion) |
| Composability | Isolated contract | Recursive zkApp composition |
| Existing code reuse | Bridge framework only | Full Kimchi+Pickles stack |
| Implementation effort | Months (BLS wrapper) | Weeks (format adapter only) |

**The Mina bridge is strictly superior for proof-carrying interop.** Midnight remains
useful for the Cardano ecosystem connection (via Partner Chains), but for
trustless cross-chain settlement, Mina is the natural partner.

---

## Risk Analysis

### Low Risk
- **Proof format compatibility:** Our Kimchi proofs use the same SRS structure,
  same gates, same curve parameters as Mina's. Format adapter is mechanical.
- **Constraint budget:** All circuits fit comfortably (18.5K rows << 131K limit).
- **Recursion soundness:** We already verify multi-step chains in our test suite.

### Medium Risk
- **o1js version compatibility:** o1js has breaking changes between versions.
  Need to target a specific o1js version and pin it.
- **Mina sequencer latency:** Mina blocks are ~3 minutes. Bridge operations
  inherit this latency (vs. pyana's sub-second finality).
- **SRS compatibility:** Our `new_index_for_test` uses dynamic SRS generation.
  Mina's production SRS is fixed. Need to align SRS parameters.

### High Risk (Mitigatable)
- **Pickles version mismatch:** Mina's Pickles has evolved since our fork of
  `proof-systems`. The recursion format (prev_challenges encoding, verifier
  digest) may differ between versions. Mitigation: pin to a specific Mina
  protocol version and maintain a compatibility layer.
- **o1js recursion API:** o1js's `ZkProgram` recursion API may not directly
  accept externally-generated Pickles proofs. Mitigation: may need a thin
  wrapper ZkProgram that "re-proves" the externally-generated proof, adding
  one recursion step but preserving soundness.

---

## Appendix: Proof Flow Diagram

```
                    PYANA SIDE                          MINA SIDE
                    ----------                          ---------

 [Effect VM execution]
         |
         | BabyBear STARK
         v
 [PoseidonStarkProof]
         |
         | poseidon_stark_verifier_circuit.rs
         v
 [Kimchi proof on Vesta]  -- THIS IS ALREADY A VALID --
         |                    PICKLES-COMPATIBLE PROOF
         | pickles.rs (recursive step)
         v
 [PicklesRecursiveProof]
         |
         | step_verifier.rs + wrap_verifier.rs
         v
 [DualCurveWrapProof]    -- VERIFIABLE BY MINA NODES --
         |                                              |
         | Bridge Gateway (proof format adapter)        |
         v                                              v
 [o1js-compatible proof] -----> [PyanaVerifier.updateRoot()] ----> [Mina chain state]
                                                                         |
                                                                    Verified root
                                                                    available to
                                                                    all Mina zkApps
```

---

## Appendix: o1js Proof Import Strategy

The key technical question: can o1js accept an externally-generated Pickles proof?

### Option A: Direct Import (preferred)
If o1js exposes a `Proof.fromJSON()` or similar that accepts raw Pickles proof bytes
with a matching verification key, we can directly submit our `DualCurveWrapProof`.
This requires the verification key (derived from gate layout) to match what o1js
expects.

### Option B: Re-proving Wrapper (fallback)
If direct import is not supported, we create a trivial o1js `ZkProgram`:
```typescript
const PyanaProofWrapper = ZkProgram({
  name: 'pyana-wrapper',
  publicInput: Field,   // pyana state root
  publicOutput: Field,  // verified root
  methods: {
    wrap: {
      privateInputs: [SelfProof],  // our external Pickles proof
      method(root: Field, externalProof: SelfProof<Field, Field>) {
        externalProof.verify();
        return root;
      }
    }
  }
});
```
This adds one recursion step (~3-5s) but is guaranteed to work with o1js's API.

### Option C: Native Kimchi Submission (advanced)
Submit the raw Kimchi proof directly to a Mina node via its GraphQL API,
bypassing o1js entirely. This requires constructing the transaction format
manually but avoids any o1js compatibility issues. The Mina node's verifier
operates on the same `kimchi::verifier::verify` function we already use.

---

## Conclusion

This is our FIRST production proof-carrying bridge. The Midnight path is months
away (needs BLS12-381 wrapping). The Mina path is weeks away because:

1. We share the proof system (Kimchi/Pickles/Pasta)
2. Our STARK-in-Pickles pipeline is already tested end-to-end
3. All circuits fit within Mina's constraint budget
4. No external wrapping/compression service needed
5. The bridge delivers Level 2 security (no federation trust for safety)

The implementation path is concrete, the timeline is realistic, and the existing
code provides a solid foundation. This should be our primary interop target.
