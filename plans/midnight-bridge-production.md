# Midnight Bridge Production Architecture

## Status Assessment (May 2026)

### What Has Changed Since midnight-v2.md

| Component | Then | Now |
|-----------|------|-----|
| DSL Lookup Tables | Not available | `LookupTable` in `CircuitDescriptor`, DFA routing proven |
| CapTP Effects | Untested | 4 effects proven in Effect VM (Export, Enliven, Drop, ValidateHandoff) |
| Service Mesh | Conceptual | Governed-namespace running (mount, discover, CAS, health) |
| Dispute Framework | Code only | `Disputable` trait + `dispute_dsl.rs` STARK constraints |
| Proof Composition | Single proofs | `ComposedCircuitDescriptor` with sub-proof bindings + IVC chains |
| SP1 Backend | Stub only | Full DatalogEvaluation API defined, guest program designed, ELF not compiled |
| gen_midnight.rs | Exists | Compiles IR to ZKIR v3 JSON (Require, Mutate, Match, Membership) |
| DFA Router | Absent | Wire-level DFA classification with governed route tables |
| Store-and-Forward | Absent | CapTP message queueing for offline peers |

### SP1 Ecosystem Status (external)

SP1 still wraps to **BN254/Groth16** only. No BLS12-381 output. This means:
- Path A from the original plan (SP1 direct to Midnight) remains **blocked**
- Path B (gnark BLS12-381 PLONK wrapper) is still the only route to pure Level 2
- However: the **optimistic bridge with dispute** path has become viable NOW

### Key Insight: We Don't Need Pure ZK for a Better-Than-Level-1 Bridge

The original plan framed Level 2 as "pure proof-carrying." But our dispute framework
changes the calculus. An **optimistic bridge** with **cryptographic dispute resolution**
gives us:
- Liveness equivalent to Level 1 (federation relays state)
- Safety equivalent to Level 2 (any challenger can force re-verification)
- No BLS12-381 wrapper needed (disputes happen on pyana, not Midnight)

---

## Production Architecture: Level 1.5 (Optimistic Proof-Carrying)

### Core Idea

The bridge operates optimistically:
1. **Relay** posts a pyana state claim to Midnight (federation attestation + bond)
2. **Challenge window** (configurable, e.g., 6 hours of pyana blocks)
3. **Anyone** can challenge by submitting a re-verification proof on pyana
4. If challenged and relay is wrong: relay's bond is slashed
5. If unchallenged: Midnight contract accepts the state transition

This is exactly what `app-framework/src/dispute.rs` + `dispute_dsl.rs` implement:
- `SettlementState::Pending` -> dispute window open
- `SettlementState::Disputed` -> challenger submitted counter-evidence
- `SettlementState::Finalized` -> no challenge, safe to execute
- `SettlementState::Resolved` -> dispute resolved, loser slashed

### Why This Is Strictly Better Than Level 1

| Property | Level 1 (Attestation) | Level 1.5 (Optimistic) |
|----------|----------------------|----------------------|
| Safety | 2/3 federation honest | 1 honest challenger + dispute period |
| Liveness | Federation alive | Federation alive (same) |
| Cost | Signature only | Signature + bond (refundable) |
| Fraud proof | None | Any party can generate |
| Time to finality | Instant | Dispute window (6h configurable) |

The safety improvement is significant: Level 1 requires *threshold* honesty. Level 1.5
requires *any single* honest watcher. This is the "1-of-N" security model.

---

## CapTP as Bridge Transport Layer

### Architecture

```
pyana cell  <--CapTP-->  Bridge Gateway  <--Substrate RPC-->  Midnight contract
     |                        |
     |  ExportSturdyRef       |  Store-and-Forward queue
     |  (proven in STARK)     |  (for Midnight latency)
     |                        |
     v                        v
  Effect VM proof          FederationAttestation +
  (pyana-side)             DisputeSubmission
```

### Why CapTP (not custom messages)

1. **Pipelining**: CapTP's promise pipelining lets us batch: "prove this capability,
   then bridge the result to Midnight" as a single logical operation. No round-trip
   wait between proving and bridging.

2. **Store-and-forward**: Midnight has ~20s block times vs pyana's sub-second.
   CapTP's `MessageRelay` queues bridge messages during Midnight's latency.
   The gateway holds messages until Midnight confirms inclusion.

3. **Capability-secured**: The bridge gateway IS a capability. You need a valid
   sturdy ref to use it. Governance controls who gets bridge access. No open relay.

4. **Provable session state**: CapTP effects (ExportSturdyRef, EnlivenRef, DropRef,
   ValidateHandoff) produce STARK proofs. The bridge session itself is provable.

### Implementation

```rust
// Mount the Midnight bridge as a service in the governed namespace
// Path: /bridges/midnight/mainnet
ServiceEntry {
    name: "midnight-mainnet-bridge",
    kind: ServiceKind::Custom("bridge".into()),
    sturdy_ref: "pyana://federation/bridge-gateway/midnight",
    tags: vec!["bridge", "midnight", "value-transfer", "proof-carrying"],
    ...
}
```

Discovery: `pyana namespace discover --tag bridge --tag midnight`

A client obtains a sturdy ref to the bridge gateway, enlivens it (provable via
EnlivenRef STARK), and then uses the live reference to submit bridge operations.
The bridge gateway:
1. Validates the caller's capability (permission check)
2. Queues the operation in the store-and-forward buffer
3. Batches operations for Midnight submission (gas efficiency)
4. Posts to Midnight with federation attestation + relay bond
5. Monitors the dispute window on pyana side
6. Returns result to caller via CapTP promise resolution

---

## DSL Lookups for the FRI Verifier

### Current State

The `fri_verifier_dsl.rs` prototype has 29 columns and uses `ConstraintExpr::Hash`
for Poseidon2 leaf computation. The gate count estimate is ~920K for 50 FRI queries.

### How Lookup Tables Help

The Poseidon2 S-box is `x^7 mod p` (BabyBear). Computing x^7 naively requires
3 multiplications (x^2, x^4, x^4 * x^2 * x). With a lookup table encoding
precomputed S-box values:

```rust
LookupTable {
    id: "poseidon2_sbox_babybear".into(),
    width: 2,  // (input, output)
    entries: (0..2013265921u64)  // Full BabyBear range -- impractical!
        .map(|x| vec![x as u32, pow7_babybear(x) as u32])
        .collect(),
}
```

**Problem**: The full BabyBear S-box table has 2^31 entries. This is too large.

**Solution**: Decomposition. BabyBear elements fit in 31 bits. We can:
1. Split the element into two 16-bit halves (or 8-bit bytes)
2. Use a 256-entry or 65536-entry lookup table per byte/half
3. Reconstruct via algebraic combination

For a 256-entry (8-bit) range check table:
```rust
LookupTable {
    id: "byte_range_check".into(),
    width: 1,
    entries: (0..256).map(|x| vec![x]).collect(),
}
```

This enables:
- **Range checks** for BabyBear arithmetic (mod reduction verification)
- **Byte decomposition** for efficient non-native arithmetic
- **Partial S-box tables** for the 8 bytes that hit specific round constants

### Concrete Impact on FRI Verifier

| Component | Without Lookups | With Lookups |
|-----------|----------------|--------------|
| BabyBear mod reduction | ~3 gates (decompose + range + eq) | 1 lookup (range table) |
| S-box x^7 | 3 multiplications | 1 lookup per byte (requires decomposition) |
| Merkle path bit check | decompose + constrain | 1 lookup (bit range table) |

Net effect: modest gate reduction (~15-20%) for the FRI verifier. The bigger win is
that lookups make the circuit CORRECT-BY-CONSTRUCTION for range checks, eliminating
a class of soundness bugs.

### ZKIR Mapping Question

`gen_midnight.rs` currently handles: Require, Mutate, Match, Membership.
It does NOT handle `ConstraintExpr::Lookup`. For Level 3 (shared programs), we need:

```
// gen_midnight.rs extension needed:
ConstraintExpr::Lookup { table_id, query_columns } =>
    // ZKIR v3 doesn't have native lookup tables.
    // Options:
    // A) Expand lookup into equality constraints (one per entry -- exponential blowup)
    // B) Emit as Midnight custom gate (requires Midnight protocol change)
    // C) Use polynomial evaluation: encode table as a polynomial, constrain evaluation
    //    This is what Plonk does natively (permutation argument)
```

**Verdict**: Lookups are useful on the pyana side NOW but don't directly translate
to ZKIR v3. Level 3 shared programs would need to handle lookups differently per target.
This doesn't block anything -- it's a gen_midnight.rs enhancement for later.

---

## Governed-Namespace as Bridge Registry

### Mount Structure

```
/bridges/
  midnight/
    mainnet          -> sturdy ref to mainnet bridge gateway
    testnet          -> sturdy ref to testnet bridge gateway
  evm/
    ethereum         -> sturdy ref to Ethereum bridge (SP1/Groth16)
    base             -> sturdy ref to Base L2 bridge
  internal/
    federation-a     -> inter-federation bridge
```

### Governance Model

The DFA router classifies WHO can:
- **Mount** a bridge: Only governance-approved operators (prevents rogue bridges)
- **Discover** bridges: Any cell (discovery is read-only)
- **Use** a bridge: Any cell with a valid sturdy ref (capability-secured)
- **Challenge** a bridge claim: Any cell with bonding capacity (open watchtower)

### DFA Route Table for Bridge Messages

```rust
LookupTable {
    id: "bridge_route_table".into(),
    width: 3,  // (message_type, destination_chain, handler)
    entries: vec![
        // Value transfers -> standard bridge handler
        vec![MSG_TRANSFER, CHAIN_MIDNIGHT, HANDLER_VALUE_BRIDGE],
        // Proof-carrying -> optimistic bridge handler
        vec![MSG_PROOF_CARRY, CHAIN_MIDNIGHT, HANDLER_OPTIMISTIC],
        // Capability export -> cross-chain CapTP handler
        vec![MSG_CAP_EXPORT, CHAIN_MIDNIGHT, HANDLER_CROSS_CAP],
    ],
}
```

The DFA router PROVES message classification is correct. When a bridge message
arrives, the circuit proves "this message was routed to the correct handler."
This is a cross-chain routing proof that BOTH chains can verify.

---

## Optimistic Bridge with Dispute System

### Protocol Flow

```
Timeline:
  t=0     Relay submits claim + bond to pyana dispute framework
  t=0     Simultaneously: federation attestation sent to Midnight
  t=0..T  Dispute window (T = dispute_window_blocks)
  t=T     If unchallenged: Finalized. Midnight contract executes.
          If challenged:
            - Challenger posts counter-proof (a STARK proof of invalidity)
            - Arbiter (any node that can verify STARKs) resolves
            - Loser's bond is slashed

  Midnight side:
  t=0     Receives attestation + claim
  t=T+1   Checks pyana finality (dispute resolved or window passed)
  t=T+1   Executes the bridged operation
```

### Components (all exist today)

| Component | Module | Status |
|-----------|--------|--------|
| Dispute lifecycle | `app-framework/src/dispute.rs` | Complete (Disputable trait) |
| STARK-provable disputes | `pyana-dsl-tests/src/dispute_dsl.rs` | Circuit constraints proven |
| Federation attestation | `bridge/src/midnight.rs` | Complete (25 tests) |
| Nonce/replay protection | `bridge/src/midnight.rs` NonceTracker | Complete |
| Observer | `bridge/src/midnight_observer.rs` | Mock infrastructure (7 tests) |
| Store-and-forward | `pyana-captp` store_forward module | Complete |
| Proof composition | `pyana-dsl-runtime` composition | Complete |

### What We Need to Build

1. **BridgeDisputable impl** (~200 lines): Implement `Disputable` for bridge claims.
   The claim is "pyana state X implies Midnight action Y." The evidence is a STARK
   proof that X does NOT imply Y (counterexample).

2. **Relay service** (~500 lines): A service that monitors pyana state, produces
   attestations, posts bonds, and submits to Midnight. Mount at
   `/bridges/midnight/mainnet` in the governed namespace.

3. **Watchtower** (~300 lines): Any node that monitors relay claims and challenges
   fraudulent ones. Uses the existing STARK verifier to check claims. Open to anyone
   (permissionless challenging via bonding).

4. **Midnight contract update** (~100 lines Compact): Add a `waitForDispute` guard
   that checks "pyana federation reports no active dispute for this claim." This is
   the attestation-level check on Midnight's side.

### Dispute Evidence Types

```rust
impl Disputable for BridgeClaim {
    type Claim = MidnightBridgeClaim;
    type Evidence = BridgeDisputeEvidence;

    fn validate_claim(&self, claim: &Self::Claim) -> bool {
        // Check: claim references a real pyana state transition
        // Check: the claimed Midnight action follows from that state
        true  // Optimistic: assume valid unless challenged
    }

    fn evaluate_dispute(
        &self,
        claim: &Self::Claim,
        evidence: &Self::Evidence,
    ) -> DisputeResolution {
        // Evidence is a STARK proof showing the claim is invalid.
        // Verify the STARK proof. If it verifies: challenger wins.
        // Types of invalidity:
        //   - State root mismatch (claimed state doesn't match pyana)
        //   - Logic error (state X does NOT imply action Y)
        //   - Replay (same state used twice)
        match verify_bridge_dispute_proof(&evidence.proof, &claim.pyana_state_root) {
            Ok(true) => DisputeResolution::ChallengerWins,
            _ => DisputeResolution::ClaimantWins,
        }
    }
}
```

---

## Production Deployment Phases

### Phase 1: Ship Optimistic Bridge (NOW -- 2-3 weeks)

**Goal**: Level 1.5 -- value transfer with 1-of-N security.

Tasks:
- [ ] Implement `BridgeDisputable` using existing dispute framework
- [ ] Create relay service (gateway cell in governed namespace)
- [ ] Mount at `/bridges/midnight/testnet` via governed-namespace registry
- [ ] Wire CapTP session: client -> bridge gateway -> Midnight
- [ ] Store-and-forward buffer for Midnight block time latency
- [ ] Watchtower service (separate cell that monitors and challenges)
- [ ] Integration test: full optimistic bridge lifecycle

Deliverable: A bridge where any pyana participant can challenge fraudulent relays
using STARK proofs. The relay posts a bond. Honest behavior is incentivized.

### Phase 2: Proof-Carrying Claims (4-6 weeks)

**Goal**: Relay includes an actual STARK proof with the claim, not just an attestation.

The relay submits:
- Federation attestation (for Midnight contract acceptance)
- Pyana STARK proof (for dispute resolution)
- Composed proof (Effect VM + capability chain + state transition)

Now challenges don't need to re-execute -- they just verify the attached proof.
If the proof is invalid, the challenge succeeds trivially. This collapses the
dispute to "is this proof valid?" which is objective and deterministic.

Tasks:
- [ ] Compose Effect VM proof + capability proof into bridge claim proof
- [ ] Attach composed proof to `MidnightBridgeClaim`
- [ ] Watchtower verifies proof rather than re-executing
- [ ] If proof verifies: no need for dispute window (instant finality!)
- [ ] If proof missing/invalid: fall back to dispute window

This gives us **optimistic instant finality**: if the relay includes a valid proof,
the dispute window can be skipped (the proof IS the finality). Only if the proof
is missing do we need the full dispute period.

### Phase 3: ZKIR Shared Programs (8-12 weeks)

**Goal**: Level 3 -- same predicate runs on both chains.

Tasks:
- [ ] Extend `gen_midnight.rs` to handle `ConstraintExpr::Lookup` (polynomial encoding)
- [ ] Compile a capability-check predicate to ZKIR v3
- [ ] Deploy compiled ZKIR to Midnight testnet
- [ ] End-to-end: capability proof on pyana = valid contract call on Midnight
- [ ] Shared Poseidon2 commitment binds both proofs

### Phase 4: Full Composable Cross-Chain (12+ weeks)

**Goal**: Level 4 -- proofs compose across chains.

Tasks:
- [ ] BLS12-381 compression service (gnark or future SP1 support)
- [ ] Pyana STARK verifiable directly on Midnight (in-circuit)
- [ ] Bidirectional: Midnight state proofs verifiable on pyana
- [ ] Cross-chain capability exercise: prove on pyana, spend on Midnight

---

## What to Build NEXT (the immediate action)

### Minimal Viable Level 1.5 Bridge

The smallest useful upgrade from pure attestation:

```
bridge/src/midnight_dispute.rs       -- BridgeDisputable impl (~200 lines)
bridge/src/midnight_relay.rs         -- Relay service (~500 lines)
bridge/src/midnight_watchtower.rs    -- Challenge monitor (~300 lines)
apps/midnight-bridge/src/main.rs     -- Binary that runs the gateway service
```

The relay service:
1. Holds a CapTP session to federation peers (uses existing infrastructure)
2. Monitors pyana block production for bridge-bound operations
3. Produces `FederationAttestation` (existing code in `bridge/src/midnight.rs`)
4. Submits attestation + bond via `Disputable::submit_claim`
5. After dispute window: signals Midnight contract to execute

The watchtower:
1. Monitors dispute submissions (subscribes to bridge claims)
2. For each claim: verifies the underlying pyana state transition
3. If invalid: generates a counter-proof (STARK proof of invalidity)
4. Submits challenge + counter-proof + bond
5. Collects slashed bonds when challenges succeed

### Why This Is High Quality

1. **Reuses existing infrastructure**: CapTP, dispute framework, governed namespace,
   store-and-forward, federation attestation -- all production-ready.

2. **Correct security model**: 1-of-N honest watcher (strictly better than Level 1's
   2/3 threshold). Economic incentives align via bonding/slashing.

3. **Graceful upgrade path**: Phase 2 adds proofs to claims (eliminating dispute
   windows for valid proofs). Phase 3 makes programs portable. Each phase is
   independently shippable.

4. **No external dependencies**: Does not require SP1 BLS12-381 support, Midnight
   protocol changes, or any new cryptographic primitives. Uses what we have.

5. **DFA-classified routing**: Bridge messages are classified by the same DFA router
   that handles all wire traffic. Governance controls what gets bridged.

---

## Architecture Diagram

```
                          PYANA SIDE
+------------------------------------------------------------------+
|                                                                    |
|  User Cell                     Bridge Gateway Cell                 |
|  +--------+   CapTP Session   +--------------------------+        |
|  | wallet |<----------------->| relay_service            |        |
|  | DApp   |   ExportSturdyRef | watchtower               |        |
|  +--------+   (STARK proven)  | dispute_manager          |        |
|                               | store_forward_buffer     |        |
|                               +--------------------------+        |
|                                         |                         |
|  Governed Namespace:                    | Dispute Framework        |
|  /bridges/midnight/mainnet              v                         |
|  (ServiceEntry, tags, CAS)     +------------------+               |
|                                | BridgeDisputable |               |
|                                | submit_claim()   |               |
|                                | challenge()      |               |
|                                +------------------+               |
+------------------------------------------------------------------+
                          |
                          | FederationAttestation + claim hash
                          | (Substrate RPC via observer)
                          v
                      MIDNIGHT SIDE
+------------------------------------------------------------------+
|                                                                    |
|  Bridge Contract (Compact)                                        |
|  +----------------------------------------------------+           |
|  | verifyAttestation(attestation, epoch_key)          |           |
|  | checkDisputeStatus(claim_hash) -> bool             |           |
|  | executeTransfer(recipient, amount, claim_hash)     |           |
|  +----------------------------------------------------+           |
|                                                                    |
|  State: nonce_tracker, processed_claims, bond_registry            |
|                                                                    |
+------------------------------------------------------------------+
```

---

## Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| Midnight testnet unavailable | Medium | Blocks integration testing | Use mock observer (exists) |
| Dispute window too short | Low | Challenger can't react | Configurable; start at 6h |
| Relay censorship | Low | Liveness failure | Multiple relays; permissionless |
| SP1 never ships BLS12-381 | Medium | Blocks Level 4 | gnark alternative; Level 1.5 is self-sufficient |
| ZKIR v3 breaking changes | Medium | Breaks gen_midnight.rs | Pin version; maintain compatibility |
| Economic attacks (grief) | Low | Spurious challenges waste bonds | Challenge bond > gas cost |

---

## Summary

The highest quality bridge we can realistically build NOW is **Level 1.5: Optimistic
Proof-Carrying with Dispute Resolution**. It combines:

- Federation attestations (existing, production-ready)
- Optimistic dispute framework (existing, STARK-proven)
- CapTP transport (existing, 4 effects proven)
- Governed-namespace discovery (existing, live)
- Store-and-forward for Midnight latency (existing)
- DFA routing for message classification (existing)

No new cryptographic primitives required. No external dependency on SP1 BLS12-381.
Strictly better security than Level 1 (1-of-N vs 2/3 threshold). Ships in 2-3 weeks.
Upgrades gracefully to Level 2/3/4 as external ecosystem matures.
