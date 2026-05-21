# Pyana Economic Model

Design document for sustainable federation economics.

---

## 1. Current State

### What Exists

**Fee handling (two-phase, Mina-style):**
- Phase 1: agent's balance is decremented by `turn.fee` and nonce incremented (never rolled back)
- Phase 2: call forest executes; if it fails, effects roll back but fee is kept
- Fees are denominated in computrons (u64)
- The fee is simply subtracted from the agent's balance -- it goes nowhere

**Turn executor costs (`ComputronCosts`):**
- `action_base: 100`, `effect_base: 50`, `transfer: 75`
- `create_cell: 500`, `proof_verify: 1000`, `signature_verify: 200`
- `per_byte: 1`

**Bounded counters (Stingray):**
- Agents' computron budgets are split into per-silo slices
- Formula: `slice = balance * (f+1) / (2f+1)` where f = Byzantine tolerance
- No coordination needed for local debits within the slice
- Rebalancing via spending certificates

**ProofObligation:**
- Obligor locks a `NoteCommitment` as stake
- If proof delivered before deadline: stake returned (Fulfilled)
- If deadline passes: stake slashed to beneficiary
- The note value is private (Poseidon2 commitment) -- no minimum enforced

**ConditionalTurn:**
- Requires `fee > 0` to prevent storage DoS
- If condition is not met before timeout: turn expires, no fee charged
- Validated: deadline cannot be more than 1000 blocks in the future

**Intent staking:**
- Gossip-propagated intents require a `StakeProof` (Poseidon2 Merkle inclusion)
- Proves note exists in the tree, does NOT verify value
- `minimum_value` field is informational only ("cannot be verified without opening the commitment")
- Nullifier tracking prevents the same stake commitment from being reused for multiple intents

**Sybil resistance:**
- One note commitment proves tree membership
- The same note can be used for unlimited intents (nullifier is per-intent-pool, not global)
- No minimum balance is enforced

### Problems

1. **Fees are burned** -- validators process turns for free
2. **No block reward** -- zero income for running a federation node
3. **ProofObligation bonds are unverifiable** -- a note with value 0 is a valid stake
4. **ConditionalTurns cost nothing on timeout** -- griefing via conditional spam
5. **Intent stake is reusable** -- one note proves unlimited identities across pools
6. **No fee market** -- all turns pay the same per-computron cost regardless of demand
7. **No validator selection economics** -- committee membership is static config

---

## 2. Proposed Model

### 2.1 Fee Distribution: Split Model

Fees are split into three destinations on every committed turn:

| Destination | Share | Rationale |
|-------------|-------|-----------|
| Block proposer | 50% | Direct incentive to process turns |
| Federation treasury | 30% | Governance-directed spending (development, bridges, audits) |
| Burned | 20% | Mild deflation, aligns all holders' interests |

**Implementation:** The executor's Phase 1 fee deduction becomes:
```
agent.balance -= fee;
proposer.balance += fee * 50 / 100;
treasury.balance += fee * 30 / 100;
// remaining 20% is destroyed (not credited anywhere)
```

The proposer is identified by the block they are assembling. The treasury is a distinguished cell whose spending requires a governance vote (quorum of current committee).

**Parameters are governance-adjustable** via a `FeePolicy` struct attested at epoch boundaries. Initial values above, with a governance vote to change them (supermajority 2/3 of committee).

### 2.2 Validator Staking (Lightweight)

Federation committees are small (3-20 nodes). Heavy PoS machinery is unnecessary. Instead:

**Deposit-based committee membership:**
- To join the committee, a node must lock a deposit note with value >= `MINIMUM_VALIDATOR_STAKE`
- Initial parameter: `MINIMUM_VALIDATOR_STAKE = 100,000 computrons`
- The deposit is proven via a range proof (see section 2.4)
- Deposit is locked for the epoch duration + unbonding period (2 epochs)

**Slash conditions (exhaustive):**
- **Equivocation**: signing two different blocks at the same height (double-vote)
- **Inactivity**: missing > 50% of consensus rounds in an epoch
- **Invalid attestation**: attesting a null/note tree root that doesn't match the actual state

**Slash amounts:**
- Equivocation: 100% of stake (this is always intentional)
- Inactivity: 5% per epoch of inactivity (graceful degradation for maintenance)
- Invalid attestation: 50% of stake

**Slashed funds** go to the federation treasury (not to the reporter -- this prevents slash-for-profit griefing between validators).

**Unbonding:**
- After announcing departure, validator stake is locked for 2 more epochs
- This ensures any pending slash evidence can be submitted
- After unbonding period: full withdrawal

### 2.3 Anti-Griefing for ConditionalTurns

**Problem:** ConditionalTurns occupy space in the pending pool until timeout. Currently they require `fee > 0` but the fee is only charged on execution -- if they timeout, the submitter pays nothing.

**Solution: Reservation deposit (partially refundable).**

```
reservation_deposit = base_deposit + per_block_rate * (timeout_height - submitted_at)
```

Parameters:
- `base_deposit = 500 computrons` (covers pool insertion overhead)
- `per_block_rate = 10 computrons/block` (storage rent for pending state)

Outcomes:
- **Condition met, turn executes**: deposit fully refunded (only execution fee charged)
- **Condition met but turn fails**: deposit refunded, execution fee charged (Phase 1)
- **Timeout (expired)**: deposit burned (20%) + sent to treasury (80%)
- **Cancelled by submitter before timeout**: deposit returned minus `base_deposit`

This makes griefing expensive: a 1000-block conditional costs `500 + 10*1000 = 10,500` if it times out.

### 2.4 Privacy-Compatible Staking via Range Proofs

**Problem:** Note values are private (Poseidon2 commitments). We need "prove my stake >= X" without revealing the exact value.

**Solution:** Add a range proof AIR circuit.

The range proof demonstrates:
1. The prover knows the opening (owner, value, asset_type, creation_nonce, randomness) of a note commitment
2. The note commitment exists in the federation's attested note tree (Merkle inclusion)
3. `value >= threshold` (range check in BabyBear arithmetic)

This composes naturally with the existing proof system:
- New AIR: `RangeProofAir` (proves `value >= min_value` for a committed note)
- Public inputs: `[note_tree_root, threshold]`
- Private witness: `[value, owner, asset_type, creation_nonce, randomness, merkle_path]`
- Constraint: `value - threshold` is non-negative in BabyBear (decompose into bit limbs, prove all are 0/1)

**For validator deposits:** prove `value >= MINIMUM_VALIDATOR_STAKE` against the current attested root.

**For ProofObligation bonds:** the beneficiary specifies a `minimum_bond` in the obligation parameters; the obligor must provide a range proof that their stake note >= `minimum_bond`.

### 2.5 Intent Marketplace Economics

**Fulfiller fees:**

When a fulfillment is accepted, the requester pays the fulfiller a `fulfillment_fee` negotiated off-protocol (embedded in the fulfillment message). This is a direct transfer between cells -- not mediated by the federation.

**Priority fee for intent visibility:**

Intents can optionally include a `priority_tip` (additional computrons locked with the intent). Higher-tip intents are propagated more eagerly by gossip relays. On fulfillment, the tip goes to the fulfiller. On expiry, the tip is returned minus a `gossip_rent` proportional to time-in-pool.

```
gossip_rent = tip * min(1.0, time_in_pool / max_expiry)
```

**Proof generation costs:**

Proof generation is local (not metered by the network). The cost is borne by the prover in CPU time. Fulfillers factor this into their `fulfillment_fee`. No on-chain "gas for proofs" -- the market prices it.

### 2.6 Sybil Resistance with Nullifier-Per-Stake

**Problem:** A single note can currently stake unlimited intents (the nullifier is pool-local). This enables one wealthy entity to flood the network with unlimited Sybil identities.

**Solution: Epoch-scoped stake nullifiers.**

Each note commitment can be used as a stake proof `K` times per epoch, where `K` is a governance parameter (initial value: `K = 5`).

**Mechanism:**
1. When a stake proof is submitted, compute: `stake_nullifier = Poseidon2(note_commitment, epoch_number, usage_counter)`
2. The federation maintains an append-only stake nullifier set per epoch
3. Each note can produce at most `K` distinct nullifiers per epoch (usage_counter in [0, K))
4. The prover includes the usage_counter in the range proof witness
5. The constraint enforces `usage_counter < K`

**Privacy properties preserved:**
- The nullifier does not reveal which note (position-independent, like spending nullifiers)
- Two nullifiers from the same note in the same epoch are unlinkable (different usage_counter)
- Cross-epoch usage is unlinkable (epoch_number changes the nullifier)

**Tradeoff:** An entity with N notes gets N*K identities per epoch. For most use cases K=5 is generous; for high-volume actors, they need proportionally more stake.

### 2.7 Fee Market (EIP-1559 Adaptation)

**Base fee adjustment (per-block):**

```
target_computrons_per_block = 1,000,000
max_computrons_per_block = 2,000,000

if actual_usage > target:
    base_fee_multiplier *= 1 + (actual_usage - target) / target * 0.125
elif actual_usage < target:
    base_fee_multiplier *= 1 - (target - actual_usage) / target * 0.125

effective_base_fee = floor(base_fee_multiplier * MINIMUM_BASE_FEE)
```

Parameters:
- `MINIMUM_BASE_FEE = 1 computron per unit` (floor -- never free)
- `MAX_BASE_FEE = 1000 computrons per unit` (ceiling -- prevents runaway)
- Adjustment speed: 12.5% per block (same as EIP-1559)

**Priority fee:**

Users specify `max_fee` and `priority_fee`. They pay `min(max_fee, base_fee + priority_fee)`. The `base_fee` portion is burned (20%) + treasury (80%). The `priority_fee` goes entirely to the block proposer.

**Relation to existing fee field:**

`turn.fee` becomes `max_fee`. Actual charge = `base_fee * computrons_used + priority_fee`. If `max_fee < base_fee * computrons_used`, the turn is rejected (cannot cover base fee).

---

## 3. Incentive Analysis

### 3.1 Nash Equilibrium for Validators

**Utility of honest validation:**
- Income: `proposer_share * avg_fees_per_block + priority_fees`
- Cost: server, bandwidth, availability

**Deviation strategies:**
- **Censor turns**: reduces fee income, also risks inactivity slash if detected
- **Include invalid turns**: other validators reject the block, proposer loses the round
- **Equivocate**: 100% stake slash -- strictly dominated by honest behavior for any positive stake
- **Go offline**: 5% slash per epoch, lost income -- dominated unless maintenance cost > income

**Equilibrium:** With the proposed parameters, honest validation is the dominant strategy whenever `annual_fee_income > server_cost + opportunity_cost_of_stake`. For a federation of 7 validators processing 100 turns/block at 1000 computrons avg fee:
- Block proposer income: ~50,000 computrons/block * 1/7 proposer frequency
- Annual: ~7,142 computrons/block-as-proposer * blocks/year
- This is viable for small federations where validators are also users/operators with aligned interests

### 3.2 Griefing Cost Analysis

**ConditionalTurn spam:**
- Cost to attacker: `500 + 10 * blocks` per conditional
- 1000 concurrent griefing conditionals for 1000 blocks each: `10,500,000 computrons`
- This is significant capital at risk for no gain (deposits are non-refundable on timeout)

**Intent spam (after Sybil fix):**
- Each note gets K=5 uses per epoch
- Flooding requires proportional stake in the note tree
- Cost: minimum note value * number_of_notes needed
- With `MINIMUM_STAKE_FOR_GOSSIP = 1000 computrons`: 500 intents requires 100 notes = 100,000 computrons locked

**Turn spam:**
- Phase 1 ensures fee is always paid
- Base fee adjustment increases cost during spam bursts
- At 2x target usage, base fee doubles within 8 blocks

### 3.3 Minimum Viable Economics

For a 5-node federation to be self-sustaining:

| Parameter | Value |
|-----------|-------|
| Server cost (per validator/month) | ~$50 (GHA free tier for non-production) |
| Minimum turns/day for break-even | 0 (free tier) to ~1000 (dedicated server) |
| Computron-to-USD exchange rate | Market-determined; not protocol-specified |
| Minimum viable fee per turn | Enough to exceed amortized server cost |

The key insight: **federations are small and purpose-built**. They don't need to compete with global L1 validator economics. A 5-node federation serving a specific application domain (agent marketplace, credential issuance, etc.) can be viable with modest throughput if operators have aligned incentives (they're also users).

---

## 4. Privacy-Compatible Staking

### 4.1 Architecture

```
Validator Deposit:
  RangeProof(value >= MINIMUM_VALIDATOR_STAKE)
  + MerkleInclusion(note_commitment in attested_tree)
  + OwnershipProof(knows spending_key for note)
  = Single STARK proof (~38 KiB)

Obligation Bond:
  RangeProof(value >= minimum_bond)
  + MerkleInclusion(note_commitment in attested_tree)
  = Single STARK proof (~38 KiB)

Intent Stake:
  MerkleInclusion(note_commitment in attested_tree)
  + NullifierComputation(note_commitment, epoch, counter < K)
  + RangeProof(value >= MINIMUM_STAKE_FOR_GOSSIP)
  = Single STARK proof (~38 KiB)
```

### 4.2 What Is Revealed

| Staking context | Public inputs | Hidden |
|-----------------|---------------|--------|
| Validator deposit | note_tree_root, threshold | exact value, note position, owner |
| Obligation bond | note_tree_root, minimum_bond | exact value, note position, owner |
| Intent stake | note_tree_root, gossip_threshold, nullifier | exact value, note position, owner, counter |

### 4.3 Slashing with Private Stakes

When a validator is slashed, the protocol needs to "take" their stake without knowing which note it is. Solution:

1. At deposit time, the validator provides a **slash commitment**: `slash_key = Poseidon2(note_commitment, "slash", randomness)`
2. The slash commitment is stored publicly in the validator registry
3. On slash, the protocol publishes the slash commitment to a "slashed set"
4. The validator's note is now encumbered: spending it requires proving non-membership in the slashed set
5. After the slash is resolved (stake transferred to treasury), the slash commitment is cleared

This means slashing is enforced at spend-time (like a lien), not at slash-time. The validator cannot move the note while slashed.

### 4.4 Unbonding Flow

```
1. Validator announces departure (publishes "unbonding" status)
2. 2 epochs pass (slash evidence window)
3. Validator proves: "my note is NOT in the slashed set AND I am past unbonding period"
4. Slash commitment is removed from validator registry
5. Note is fully spendable again
```

---

## 5. Migration Path

### Phase 1: Fee Distribution (minimal code change)

**Changes:**
- Add `FeePolicy { proposer_share: u8, treasury_share: u8, burn_share: u8 }` to federation config
- Modify executor Phase 1 to credit proposer and treasury cells
- Add distinguished `treasury_cell_id` to `TurnExecutor`
- Add `proposer_cell_id` field (set per-block by the consensus layer)

**Impact:** Low risk. Only touches the fee deduction in `executor.rs:384-387`. No changes to the proof system or consensus.

**Estimated complexity:** ~200 LOC across `turn/src/executor.rs`, `federation/src/lib.rs`, `types/src/lib.rs`.

### Phase 2: ConditionalTurn Deposits

**Changes:**
- Add `reservation_deposit` field to `ConditionalTurn`
- Add `validate_reservation_deposit()` to `conditional.rs`
- Modify `execute_conditional()` to handle deposit lifecycle (refund/burn)
- Add `base_deposit` and `per_block_rate` to `FeePolicy`

**Impact:** Medium. Touches `conditional.rs` and `executor.rs`. Requires storing deposit state for pending conditionals.

**Estimated complexity:** ~400 LOC.

### Phase 3: Range Proof AIR

**Changes:**
- New AIR in `circuit/src/range_proof_air.rs`
- Constraint: decompose `value - threshold` into BabyBear-width bit limbs, prove all bits are 0/1
- Compose with existing Merkle membership AIR for note inclusion
- New `StakeProofV2` type that includes the STARK range proof

**Impact:** High (new circuit). Requires careful security analysis of the range proof constraints. However, this is additive -- existing `StakeProof` continues to work during transition.

**Estimated complexity:** ~1500 LOC in `circuit/`, ~300 LOC in `intent/`.

### Phase 4: Fee Market

**Changes:**
- Add `BaseFeeState { multiplier: u64, last_block_usage: u64 }` to federation state
- Modify turn validation to check `max_fee >= base_fee * estimated_computrons`
- Add `priority_fee` field to `Turn`
- Adjust fee distribution to route base_fee-portion to burn/treasury and priority to proposer

**Impact:** Medium. Changes the turn structure (`turn.rs`) and validation. Backward-compatible if `priority_fee` defaults to 0 and `base_fee` starts at `MINIMUM_BASE_FEE`.

**Estimated complexity:** ~500 LOC.

### Phase 5: Epoch-Scoped Stake Nullifiers

**Changes:**
- Modify `StakeProof` to include `epoch` and `usage_counter`
- New constraint in the stake proof circuit: `usage_counter < K`
- Federation maintains per-epoch stake nullifier set (append-only)
- Modify `IntentPool::receive()` to check epoch-scoped nullifiers

**Impact:** Medium-high. Changes the stake proof format (backward-incompatible) and requires epoch awareness in the intent gossip layer.

**Estimated complexity:** ~600 LOC across `intent/`, `circuit/`, `store/`.

### Phase 6: Validator Staking and Slashing

**Changes:**
- New `ValidatorRegistry` in `federation/src/`
- Deposit/withdraw lifecycle with range proofs
- Slash commitment mechanism
- Unbonding state machine
- Slash detection (equivocation proofs, inactivity tracking)

**Impact:** High. Major new subsystem in the federation layer. Should be implemented last as it depends on Phase 3 (range proofs).

**Estimated complexity:** ~2000 LOC in `federation/`, integrated with `circuit/`.

---

## 6. Comparison to Relevant Systems

| Property | Pyana (proposed) | Cosmos/Tendermint | Mina Protocol | Ethereum L2 (Rollup) |
|----------|-----------------|-------------------|---------------|----------------------|
| **Committee size** | 3-20 (federated) | 100-175 (PoS) | ~1000 (Ouroboros) | 1 sequencer (centralized) |
| **Fee destination** | 50/30/20 split | 100% to proposer+stakers | 100% burned | 100% to sequencer |
| **Staking model** | Deposit + range proof | Delegated PoS | Delegated PoS | None (sequencer bonded) |
| **Slash conditions** | Equivocation, inactivity, bad attestation | Double-sign, downtime | Supercharged disqualification | Fraud/validity proof failure |
| **Privacy of stake** | ZK range proof (value hidden) | Fully transparent | Fully transparent | N/A |
| **Fee market** | EIP-1559 adapted | First-price auction | Fixed fees | EIP-1559 variant |
| **Anti-griefing** | Reservation deposits | Gas limits | Account creation fee | L1 calldata cost |
| **Sybil resistance** | Nullifier-per-stake-per-epoch | Minimum delegation | Minimum stake | L1 deposit |
| **Treasury** | 30% of fees | Community pool (2%) | None | Protocol-specific |
| **Validator incentive** | Fees + priority tips | Inflation + fees | Inflation + fees | MEV + fees |

### Key Differences from Each

**vs. Cosmos:** Pyana is not inflationary. No block rewards beyond fee distribution. This works because federations are small and operators have aligned interests (they're building on the platform). Cosmos needs inflation because validator sets are large and operators are pure infrastructure providers.

**vs. Mina:** Mina burns fees and relies on inflation to pay validators. Pyana's split model means validators earn from fees directly, making the system viable without inflation. Mina's staking is transparent; Pyana's is private via range proofs.

**vs. Ethereum L2s:** L2 sequencers extract all value and have no accountability. Pyana's committee is decentralized (BFT) with slashing. The tradeoff: L2s are faster (single sequencer), Pyana has higher latency but genuine decentralization within the federation.

---

## 7. Open Questions

1. **Treasury governance:** What voting mechanism controls treasury spending? Simple majority of committee? Token-weighted vote by note holders? Quadratic voting? (Deferred to governance design document.)

2. **Cross-federation fee arbitrage:** If federation A has lower fees than federation B, rational agents route through A. Is this a feature (competition) or a problem (race to bottom)?

3. **Validator rotation incentives:** When a validator's stake is small relative to others, they get fewer proposal slots. Should proposal frequency be stake-weighted or round-robin?

4. **Range proof performance:** The proposed range proof AIR adds ~2 KiB to proofs and ~100ms to generation. Is this acceptable for intent stake proofs (generated on every intent submission)?

5. **Treasury bootstrap:** Before the treasury accumulates meaningful balance, who funds the initial development? (Answer: the operators who set up the federation, same as any cooperative.)
