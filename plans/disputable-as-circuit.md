# Disputable as CellProgram: Circuit-Constrained Dispute Resolution

## Status: Design Prototype

## 1. The Dispute State Machine

The dispute cell is a sovereign cell whose state transitions are governed by
a deployed `CircuitDescriptor`. The state machine:

```
Created(0) --> Claimed(1) --> Finalized(3)
                         --> Disputed(2) --> Slashed(4)
                                        --> Finalized(3)
```

Each arc has algebraic preconditions enforceable in a STARK.

### Cell State Layout (8 fields)

| Field | Meaning                     | Type       |
|-------|-----------------------------|------------|
| 0     | state (enum 0..4)           | Selector   |
| 1     | claim_hash                  | Hash       |
| 2     | challenger_id_hash          | Hash       |
| 3     | dispute_deadline            | Value      |
| 4     | provider_stake              | Value      |
| 5     | challenger_stake            | Value      |
| 6     | resolution (0/1/2)          | Selector   |
| 7     | arbiter_commitment          | Hash       |

### Public Inputs

| PI Index | Meaning                          |
|----------|----------------------------------|
| 0        | old_state                        |
| 1        | new_state                        |
| 2        | block_height (external clock)    |
| 3        | caller_id_hash                   |
| 4        | old_claim_hash                   |
| 5        | new_claim_hash                   |
| 6        | old_deadline                     |
| 7        | new_deadline                     |
| 8        | old_provider_stake               |
| 9        | new_provider_stake               |
| 10       | old_challenger_stake             |
| 11       | new_challenger_stake             |
| 12       | old_resolution                   |
| 13       | new_resolution                   |
| 14       | arbiter_commitment               |
| 15       | arbiter_signed (0/1, verified externally) |

## 2. What CAN Be Proven In-Circuit vs Executor Support

### Provable In-Circuit (STARK constraints)

1. **State machine validity**: Only legal state transitions are allowed. If
   old_state = 0, new_state can only be 1. If old_state = 1, new_state can
   be 2 or 3. Expressed with Gated polynomial constraints.

2. **Deadline enforcement**: `block_height > deadline` for finalization.
   A range-check decomposition proves the inequality.

3. **Stake conservation**: provider_stake and challenger_stake can only change
   in prescribed ways (increase when staking, zero out when slashing/returning).

4. **Resolution binding**: field[6] can only become non-zero when state == 2.
   Resolution == 2 requires state transition to Slashed(4). Resolution == 1
   requires state transition to Finalized(3).

5. **Claim immutability**: Once set, claim_hash cannot change (equality
   constraint between old and new values).

6. **No-challenger finalization**: Claimed(1) -> Finalized(3) requires
   challenger_id_hash == 0 AND block_height > deadline.

7. **Challenger window**: Claimed(1) -> Disputed(2) requires
   block_height <= deadline AND challenger_stake > 0.

### Requires Executor Support (NOT in-circuit)

1. **Signature verification**: Verifying that the caller actually signed the
   transition. Ed25519 is ~1000 constraint rows; too expensive for the dispute
   state machine. The executor checks signatures and commits the result as
   pi[15] (arbiter_signed).

2. **Arbiter identity binding**: The executor verifies that the signer of the
   resolution matches the cell's arbiter_commitment field. The circuit just
   checks that pi[15] == 1 when resolution changes.

3. **Block height oracle**: The executor provides block_height as a public input.
   The circuit trusts this value (it cannot query the chain). The PI binding
   ensures the proof is tied to a specific block height.

4. **Cross-cell effects**: Stake lock/release/slash are effects that touch OTHER
   cells (the obligation cell, the treasury). The dispute circuit proves the
   state machine is correct; the Effect VM proves conservation across cells.

## 3. Arbiter Options and Tradeoffs

### Option A: Designated Arbiter (RECOMMENDED for v1)

The arbiter is a single cell whose public key hash is stored in field[7].
The executor verifies the arbiter's signature over the resolution message.
The circuit constrains: `pi[15] * (state_transition_to_resolved) == valid`.

**Pros**: Simple (one signature check). Fits existing executor. Low proof cost.
**Cons**: Single point of trust. Arbiter can collude.
**Circuit cost**: +1 Binary constraint (pi[15] is boolean), +1 Gated polynomial.

### Option B: Federation Consensus (N-of-M threshold)

The resolution requires N signatures from M known federation members. The
executor collects and verifies signatures, counts >= N valid ones, and sets
pi[15] = 1 if threshold met.

**Pros**: No single point of failure. Decentralized trust.
**Cons**: Executor does M signature verifications (heavy but not in-circuit).
   Requires federation membership tracking.
**Circuit cost**: Same as Option A (pi[15] is the executor's attestation).
   The DIFFERENCE is in what pi[15] MEANS -- the executor's threshold check
   is trusted, but the binding to the proof makes the result auditable.

### Option C: Cryptographic Re-execution (zkVM)

For compute disputes: the challenger provides an SP1 proof that the correct
output differs from the claimed output. The existence of a valid SP1 proof
with different output IS the resolution.

**Pros**: Fully trustless. No arbiter needed. Mathematical certainty.
**Cons**: Only works for deterministic computations. SP1 proof generation
   is expensive (minutes to hours). Not applicable to subjective disputes.
**Circuit cost**: The dispute circuit adds a constraint: resolution == 2
   requires pi[reexec_proof_valid] == 1. The executor verifies the SP1 proof.

### Option D: Hybrid/Tiered (RECOMMENDED for production)

Try cryptographic first. If the computation is re-executable, accept an SP1
proof. If not (subjective dispute, or cryptographic deadline expires), fall
back to federation consensus.

**Circuit cost**: Two resolution paths, selected by a gated constraint.
The circuit accepts EITHER path as valid.

## 4. Prototype CircuitDescriptor

### Trace Layout (12 columns)

| Col | Name                | Kind     | Description                           |
|-----|---------------------|----------|---------------------------------------|
| 0   | old_state           | Selector | Previous state (0..4)                 |
| 1   | new_state           | Selector | New state (0..4)                      |
| 2   | block_height        | Value    | Current block height                  |
| 3   | deadline            | Value    | Dispute deadline                      |
| 4   | provider_stake      | Value    | Provider stake amount                 |
| 5   | challenger_stake    | Value    | Challenger stake amount               |
| 6   | resolution          | Value    | 0=pending, 1=provider, 2=challenger   |
| 7   | arbiter_signed      | Binary   | Executor attests arbiter resolved     |
| 8   | height_gt_deadline  | Value    | block_height - deadline (range proof) |
| 9   | deadline_gt_height  | Value    | deadline - block_height (range proof) |
| 10  | no_challenger       | Binary   | 1 if challenger_stake == 0            |
| 11  | pad                 | Value    | Padding to keep width reasonable      |

### Constraint Expressions (actual ConstraintExpr declarations)

```rust
// === C1: old_state and new_state are valid enum values (0..4) ===
// old_state * (old_state - 1) * (old_state - 2) * (old_state - 3) * (old_state - 4) == 0
// Expressed as Polynomial { terms: [...] } (degree 5 -- fits max_degree 5)

// === C2: State machine transition validity ===
// Gated by old_state == 1 (Claimed) AND new_state == 3 (Finalized):
//   REQUIRE: block_height > deadline AND no_challenger == 1
//
// Encoding: (old_state)(old_state-2)(old_state-3)(old_state-4) selects old_state==1 uniquely
// but this is degree 4. Alternative: use separate binary indicator columns.
// PRACTICAL APPROACH: Use Gated constraints with binary indicator columns.

// C2a: Selector constraints (binary indicators for each state)
ConstraintExpr::Binary { col: 7 }   // arbiter_signed is boolean
ConstraintExpr::Binary { col: 10 }  // no_challenger is boolean

// C2b: Finalization path (old_state=1, new_state=3)
// When (old_state==1 AND new_state==3): height_gt_deadline >= 0 AND no_challenger == 1
// Expressed as: if this transition happens, the constraints must hold.
// Use Polynomial with selector terms.

// C3: Dispute path (old_state=1, new_state=2)
// When (old_state==1 AND new_state==2): deadline_gt_height >= 0 AND challenger_stake > 0

// C4: Slash path (old_state=2, new_state=4)
// When (old_state==2 AND new_state==4): resolution == 2 AND arbiter_signed == 1

// C5: Resolved-in-favor path (old_state=2, new_state=3)
// When (old_state==2 AND new_state==3): resolution == 1 AND arbiter_signed == 1
```

### Full CircuitDescriptor (Rust)

See `pyana-dsl-tests/src/dispute_dsl.rs` for the complete implementation.

The key insight: rather than trying to encode "if old_state == X" as a
degree-4+ polynomial selector, we use SEPARATE ROWS for each transition type,
with a `transition_type` selector column (binary). Each row proves exactly one
transition. The circuit has at most degree 3 constraints (Binary + Gated Polynomial).

## 5. Composition with Effect VM Custom Dispatch

The dispute cell's CellProgram deploys a `CircuitDescriptor` (the dispute state
machine). At runtime:

1. A participant (provider, challenger, or arbiter) submits a turn with a
   `Custom` effect targeting the dispute cell.

2. The turn includes an external proof: a STARK proof under the dispute
   CellProgram's VK hash demonstrating the state transition is valid.

3. The Effect VM processes the Custom effect row:
   - `sel_custom = 1`
   - `param[0..4]` = dispute program VK hash
   - `param[4..8]` = hash of the external dispute proof
   - State flows through unchanged in the Effect VM (Custom semantics)

4. The executor verifies the external proof against the registered CellProgram:
   ```
   registry.verify_with_program(&vk_hash, &dispute_pi, &proof_bytes)
   ```

5. The dispute_pi encodes: old_state, new_state, block_height, etc.
   The executor checks that dispute_pi is consistent with the actual cell state.

6. **Conservation**: The Effect VM handles stake lock/release separately.
   The dispute circuit proves the state machine is correct; the Effect VM proves
   value conservation. They compose:
   - Dispute circuit: "this transition is valid given these preconditions"
   - Effect VM: "the net balance change across all cells is zero"
   - Together: "the dispute resolved correctly AND no value was created/destroyed"

### Proof Composition Flow

```
Turn = [
  Effect::Custom { vk_hash: dispute_vk, proof_commit: H(dispute_proof) },
  Effect::FulfillObligation { obligation_id, stake_return },  // if finalized
  // OR
  Effect::SlashObligation { obligation_id, beneficiary },     // if slashed
]
```

The Effect VM proves the full turn (all effects together). The dispute_proof
is verified separately. The binding between them is:
- The Custom effect's VK hash matches the deployed dispute program
- The Custom effect's proof_commitment matches the actual dispute proof hash
- The Effect VM's state continuity ensures the cell state is consistent

## 6. Is This Worth It?

### What You Gain

1. **Auditability without re-execution**: Any third party can verify that a
   dispute was resolved correctly by checking the STARK proof. No need to
   replay the dispute logic or trust the executor's implementation.

2. **Upgrade safety**: If the executor implementation has a bug in dispute
   resolution, the circuit constraints serve as a safety net. An incorrect
   transition won't produce a valid proof.

3. **Composability**: Because the dispute is a standard CellProgram, it can
   be upgraded (new version deployed) without changing the executor. The
   circuit IS the specification.

4. **Federation accountability**: If the arbiter/federation signs a resolution,
   the proof binds their signature to the outcome permanently. You can audit
   "was this resolution properly authorized?" cryptographically.

5. **Deterrence**: A malicious executor that tries to resolve disputes
   incorrectly cannot produce valid proofs. The proof requirement makes
   corruption economically unviable (it's publicly detectable).

### What You Lose

1. **Proof generation cost**: Every state transition requires generating a STARK
   proof (~10-100ms for a 12-column, 2-row trace). For high-frequency disputes
   this adds latency.

2. **Complexity**: The circuit is ~50 lines of constraint declarations but
   reasoning about correctness is harder than the 20-line Rust match statement.

3. **Signature is still trusted**: The executor still verifies signatures. The
   circuit cannot verify Ed25519 efficiently. So the "provable" claim is
   conditional on the executor honestly reporting pi[15].

### Verdict

**WORTH IT for high-value disputes** (>1000 tokens at stake). The proof adds
meaningful security: an incorrect resolution is publicly detectable and cannot
be hidden. For micro-disputes (<100 tokens), the proof generation overhead
may exceed the economic value at stake.

**Recommended approach**: Make the circuit OPTIONAL. The Disputable trait
already supports different arbiter strategies. Add a new strategy variant:

```rust
ArbiterStrategy::CircuitConstrained {
    dispute_program_vk: [u8; 32],
    // Falls back to designated arbiter if proof not provided within deadline
    proof_deadline_blocks: u64,
}
```

High-value disputes require circuit proofs. Low-value disputes use the existing
executor-trusted path. This is the same "belt and suspenders" philosophy used
throughout pyana: trust but verify where it matters.

## 7. Implementation Phases

### Phase 1 (this prototype): Single-arbiter dispute circuit
- 12-column trace, degree 3
- State machine constraints (valid transitions only)
- Deadline comparison (arithmetic range proof)
- Stake non-zero checks
- arbiter_signed as external oracle (executor checks signature)

### Phase 2: Federation threshold integration
- pi[15] becomes pi[threshold_met]
- Executor collects N-of-M signatures, sets threshold_met = 1
- Circuit unchanged (still checks pi[15] == 1 for resolution)

### Phase 3: Cryptographic re-execution path
- Additional constraint path: resolution == 2 AND reexec_proof_valid == 1
- reexec_proof_valid is pi[16]: executor verifies SP1 proof externally
- Circuit accepts EITHER arbiter path OR cryptographic path

### Phase 4: Full Effect VM integration
- Dispute CellProgram deployed to ProgramRegistry
- Custom effect dispatch connects dispute state machine to Effect VM
- Conservation constraints compose with dispute state machine
- End-to-end: submit turn -> prove dispute transition -> verify at Effect VM level
