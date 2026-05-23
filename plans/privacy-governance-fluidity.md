# Privacy-Governance-Fluidity Analysis

How privacy and governance interact in the pyana system, what the information-theoretic limits are, and where the current implementation sits on the Pareto frontier.

## 1. Private Cell Migration

### Can a cell move between federations WITHOUT the source learning where it went?

**Yes, using the existing stealth address machinery.**

The source federation only knows that the cell departed (its commitment was zeroed or a Leave proposal passed). If the cell uses stealth addresses (`cell/src/stealth.rs`) to generate a one-time identity for the target federation, the source cannot link the departure to any arrival elsewhere.

**Current mechanism**: A sovereign cell (`cell/src/cell.rs`, `CellMode::Sovereign`) stores only a 32-byte state commitment at the federation. The cell holder can:
1. Nullify the commitment at the source (publish a "burn" transaction)
2. Generate a fresh stealth address for the target federation
3. Present a STARK proof of valid state at the target (proving the state is well-formed without revealing history)

**Gap**: No explicit "private migration" protocol exists. The note bridge (`cell/src/note_bridge.rs`) handles VALUE transfer across federations but not full cell state migration. You would need:
- A "cell exit proof" (STARK proving the cell commitment was properly retired at the source)
- A "cell entry proof" (STARK proving the new commitment derives from a valid retired state)
- The exit proof should NOT contain the target address

### Can a cell move WITHOUT the target learning its full history?

**Yes, this is already the sovereign cell model.**

A sovereign cell presents only its CURRENT state commitment to the hosting federation (`tests/src/sovereign_proof.rs`). The Effect VM proof (`circuit/src/effect_vm.rs`) proves `old_commitment -> new_commitment` validity without revealing the full state.

**Minimum disclosure for migration**:
- The target MUST learn: current state commitment (32 bytes), proof of valid state
- The target NEED NOT learn: history of transitions, prior federation membership, who issued the original token

**Key insight**: The Effect VM already proves turns without revealing cell state (lines 78-80 of `effect_vm.rs`: public inputs are `[old_commitment, new_commitment, net_delta_magnitude, net_delta_sign, effects_hash]`). The target never sees the actual state.

### Approach: intermediary relay

Use an intermediary federation as a mixing stage:
1. Cell exits source via stealth address pointing to the intermediary
2. Intermediary batches multiple cells, waits a mixing window (k-anonymity)
3. Cell exits intermediary via a DIFFERENT stealth address pointing to the true target

This provides indistinguishability among the k cells in the mixing window. The intermediary learns the correlation (source -> target) but neither source nor target learns the other.

**Better approach**: Use the handoff protocol (`captp/src/handoff.rs`) with a zero-knowledge intermediary:
- The intermediary signs a `HandoffCertificate` naming the recipient (target federation)
- The source federation never sees the certificate's `target_federation` field
- The target never sees the `introducer` (because the intermediary's identity is blinded via ring membership)

### What if the cell has PRIVATE state (encrypted notes)?

The encrypted notes travel with the cell's private state (held by the agent, not the federation). The note tree root is part of the state commitment. On migration:
- Notes remain encrypted; only the holder has the spending keys
- The note Merkle root changes only if notes are spent during the transition
- The target federation sees a new note tree root (via the state commitment) but cannot open any notes

**Remaining risk**: If the source federation previously processed NoteSpend effects, it knows WHICH nullifiers were published. These nullifiers are deterministic (derived from note content), so if the same note is later spent at the target, the source could correlate. Mitigation: re-randomize notes during migration (create new notes with the same values but fresh randomness).

## 2. Governance Privacy

### Current state: votes are public

In `blocklace/src/constitution.rs`, the `VoteTracker` stores `approvals: HashMap<BlockId, HashSet<[u8; 32]>>` — meaning every vote is attributed to a specific public key. This is by design: the causal ordering (blocklace) requires seeing who voted to verify supermajority.

### Can you have PRIVATE governance?

**Yes, using threshold decryption of vote tallies.**

The machinery already exists (`federation/src/threshold_decrypt.rs`): turns are encrypted to a threshold public key and decrypted collaboratively after ordering. Apply the same pattern to votes:

1. Each voter encrypts their vote to the federation's threshold key
2. After the voting period closes, validators collaboratively decrypt
3. Only the TALLY is published, not individual votes

**Implementation sketch**:
- `MembershipVote.approve: bool` becomes `MembershipVote.encrypted_vote: ThresholdCiphertext`
- After the voting period, validators produce `DecryptionShare`s
- The combined decryption reveals: "X approvals, Y rejections" (not WHO voted how)

**Critical limitation**: With threshold=3 and n=4, if we see 3 approvals and one known abstainer, individual votes are deducible. Private voting only provides meaningful privacy when n is large relative to the threshold.

### Ring signatures for governance

The existing presentation proof (`circuit/src/presentation.rs`) already implements ring membership with blinding:
- `blinding_factor` (line 60-66): makes presentations unlinkable
- `generate_blinded_merkle_poseidon2_stark_proof` (line 1584): proves membership without revealing WHICH member

**Applying to governance**: Instead of attributing votes, each voter produces a ring signature proving "I am ONE of the N participants" without revealing which one. The vote is a STARK proof:
- Public inputs: `[proposal_hash, approve_bit, federation_root]`
- Private witness: voter's identity, Merkle path in the participant tree

**This prevents double-voting detection** unless you add a nullifier scheme (each voter has one nullifier per proposal, published on vote, preventing duplicate voting without attribution).

### Tradeoff: transparent vs. private governance

| Property | Transparent | Private | Hybrid |
|----------|-------------|---------|--------|
| Accountability | Full | None | Partial |
| Coercion resistance | None | Full | Partial |
| Verifiability | Trivial | Complex (threshold/ZK) | Medium |
| Efficiency | O(1) per vote | O(ring_size) per vote | O(log n) |

**Recommendation**: Hybrid approach. Votes are private-by-default (ring membership proof + encrypted ballot), but voters can VOLUNTARILY reveal their vote for accountability. This gives coercion resistance (you can claim you voted either way) while allowing transparency when desired.

### Proposal privacy: blind proposals

Can you propose route changes without revealing them until passage?

**Yes, using commit-reveal**:
1. Proposer publishes `commit = blake3(proposed_routes || randomness)`
2. Voters vote on the commitment (trusting the proposer's reputation, or having received the plaintext via encrypted side-channel)
3. After passage, the proposer reveals `(proposed_routes, randomness)` and the commitment is verified

**Better**: The proposer encrypts the proposal to the federation's threshold key. After passage, validators decrypt it. This way the proposal is never revealed to non-participants, only to federation validators.

**Current gap**: `MembershipProposal::AmendRoutes` (constitution.rs line 199-207) carries the plaintext `new_routes_commitment` and `description`. These are public. Adding an encrypted proposal variant would require:
- A new proposal type: `EncryptedAmendRoutes { ciphertext: ThresholdCiphertext }`
- Validators decrypt after threshold is reached
- Apply the decrypted content

## 3. Fluid Boundaries with Privacy

### Sovereign -> Hosted: executor learns ALL cell state?

**Not necessarily.** With the Effect VM (`circuit/src/effect_vm.rs`), the executor only needs to verify the STARK proof of the state transition. The public inputs are:
- `old_commitment` (Poseidon2 hash)
- `new_commitment`
- `net_delta_magnitude` + `net_delta_sign`
- `effects_hash`

The executor never sees the actual field values, balance, or capability root. It verifies the proof and updates the commitment.

**BUT**: The executor currently needs full state for HOSTED cells (to compute the transition). The sovereign mode is exactly the privacy-preserving path. When a cell moves from sovereign to hosted, the cell owner MUST reveal state to the new host.

**Can we do better?** Three approaches:

#### A. Encrypted execution (FHE)

Execute cell programs over encrypted state. The executor processes ciphertexts without learning the plaintext.

**Feasibility**: The value commitment system (`cell/src/value_commitment.rs`) already uses Pedersen commitments (homomorphic over amounts). But arbitrary state transitions (field updates, capability grants) require fully homomorphic encryption.

**Performance**: FHE over BabyBear fields would be approximately 10^4-10^6x slower than cleartext. For a simple transfer: ~1ms cleartext vs ~10 seconds FHE. This is acceptable for high-value operations but not for routine compute.

#### B. MPC between cell owner and executor

Split the computation: the cell owner holds the state, the executor holds the routing logic. They jointly compute the transition without either learning the other's inputs.

**Existing infrastructure**: The garbled circuit system (`circuit/src/garbled.rs`, `apps/gallery/src/private_vickrey.rs`) already implements two-party computation with OT. The auctioneer evaluates a garbled circuit without learning bid values.

**Adaptation**: The cell owner garbles the state transition circuit. The executor evaluates using OT-obtained labels. Output: the executor learns only (new_commitment, effects_hash, valid_bit).

**Performance**: Garbled circuits are ~100x slower than cleartext but feasible for single turns.

#### C. Selective disclosure (the practical path)

The cell has 10 fields; the executor needs to verify only 2 of them.

**Already implemented**: The presentation proof's `revealed_facts_commitment` (presentation.rs line 47-57) implements exactly this pattern:
- The prover chooses which facts to reveal
- Revealed facts are committed via `WideHash` (124-bit binding)
- The verifier recomputes the commitment from revealed facts and checks it matches

**For cell state**: Expose a "cell state projection" where the owner reveals only the fields the executor needs (e.g., balance for a transfer) and provides a STARK proof that the unrevealed fields are consistent with the state commitment.

**This is the recommended path**: it's already working infrastructure extended to a new use case.

## 4. Information Leakage from Protocol Participation

### Gossip patterns reveal social graph

**Current mitigation**: Dandelion++ (`net/src/gossip.rs`, lines 88-117):
- Stem phase: message forwarded to exactly one random peer
- Fluff phase: normal broadcast via Plumtree
- Adaptive probability: full Dandelion++ (0.9 stem probability, ~10 hops) for networks >= 10 peers

**Gap**: Dandelion++ hides the ORIGINATOR of a message but not the INTEREST pattern. If Alice always subscribes to topic T, observers can correlate her to T's messages even without knowing she originated them.

**Recommendation**: Topic subscription mixing. Subscribe to k random decoy topics alongside real interests (k-anonymity for subscriptions). Cost: ~k extra messages per gossip round.

### Block timing reveals activity

**Gap**: When a sovereign cell produces a proof-carrying turn, the timing of that turn reveals when the agent was active. Combined with pattern analysis (e.g., "always active at 9am Pacific"), this deanonymizes.

**Mitigation**: Batched turn submission with random delays. The wallet queues turns and submits them in fixed-interval batches (e.g., every 10 minutes), adding Poisson-distributed noise to the submission time.

### CapTP session establishment reveals interest

**Gap**: `HandoffCertificate` (captp/src/handoff.rs) reveals `target_federation` and `target_cell` in plaintext. While the recipient is blinded, the CONNECTION establishment itself reveals that Alice is interested in cell X on federation Y.

**Mitigation**: Onion routing for CapTP sessions. Wrap the initial connection request in layers of encryption through intermediary federations. This is essentially Tor for capability sessions.

**Existing partial mitigation**: Swiss numbers (`HandoffCertificate.swiss`) are pre-registered and random, so the target cell ID is not directly exposed in the initial presentation. But the `target_federation` field is still cleartext.

### DFA routing: public classifier enables traffic analysis

**Current state**: The DFA route table (`wire/src/dfa_router.rs`) has a `commitment: [u8; 32]` (blake3 of the transition table). If the adversary obtains the route table (it's committed publicly via governance), they can classify any message they intercept.

**Gap**: The governance commitment (`constitution.routes_commitment`) makes the routing policy PUBLIC. Anyone who reads the constitution knows the routing rules.

**Mitigation**:
1. Encrypt the DFA tables per-federation (only validators can read them)
2. Prove correct routing in ZK: "I routed this message to the correct target" without revealing the routing table

### Timing attacks on proof generation

**Gap**: The Effect VM trace size is proportional to the number of effects in a turn. More effects = larger trace = longer proof generation. An observer timing the proof submission can estimate the turn's complexity.

**Mitigation**: Pad all proofs to a fixed trace size (the maximum supported). Current Effect VM width is 65 columns; pad the row count to a power of 2. This is already partially done (STARK proofs are padded for FRI), but the PADDING should be to a FIXED size regardless of actual effects count.

**Cost**: Proving a 1-effect turn takes the same time as proving a 16-effect turn. This is ~2-4x overhead for typical turns but eliminates the timing side channel.

## 5. Fundamental Tradeoffs

### Privacy vs. Compute

| Privacy Level | Mechanism | Overhead | Use Case |
|---|---|---|---|
| None (hosted cleartext) | Direct execution | 1x | Low-value, speed-critical |
| Commitment-based | Pedersen + conservation proof | ~5x | Value transfers |
| ZK presentation | STARK fold chain + derivation | ~50-100x | Authorization proofs |
| Encrypted execution (garbled) | 2PC garbled circuit | ~100x | High-value private compute |
| Full FHE | Lattice-based FHE | ~10^4-10^6x | Theoretical maximum privacy |

### Governance vs. Coordination

| Governance Model | Messages per Decision | Latency | Privacy |
|---|---|---|---|
| Solo (n=1) | 0 | Instant | N/A |
| Transparent voting | n messages | 1 wave | None |
| Ring-signature voting | n proofs + tally | 2-3 waves | Full voter privacy |
| Threshold-encrypted voting | n ciphertexts + threshold decrypt | 2-3 waves | Full voter privacy |

### Fluidity vs. Re-routing

| Migration Type | Messages | State Disclosed | Privacy |
|---|---|---|---|
| Hosted -> Hosted (same fed) | 1 internal | Full state | None |
| Hosted -> Sovereign | 1 exit + proof | State to self only | Full |
| Sovereign -> Sovereign (same fed) | 0 (peer exchange) | Commitment only | Full |
| Cross-federation (cleartext) | Bridge message + attestation | Full state to target | Partial |
| Cross-federation (private) | Stealth address + STARK proof | Commitment only | Full |

### Pareto Frontier

The achievable tradeoffs form three tiers:

1. **Fast path** (existing): Hosted cells with cleartext state. Zero privacy, maximum speed. Suitable for public-goods cells, governance infrastructure, routing.

2. **Standard path** (partially implemented): Sovereign cells with STARK proofs. Full privacy from the federation, moderate proof overhead (~100ms per turn). Suitable for wallets, private transfers, capability delegation.

3. **Maximum privacy path** (future): Sovereign cells + stealth addresses + Dandelion++ + padded proofs + encrypted governance. Near-total unlinkability. Overhead: ~500ms per turn, ~3x gossip bandwidth. Suitable for high-value privacy-critical applications.

## 6. Composability of Privacy Guarantees

### Private notes + public governance: does governance leak note info?

**Current leak**: The constitution stores participant public keys (`participants: Vec<[u8; 32]>`). If a note's `owner` field uses the same public key as the governance participant, spending that note (revealing the nullifier) is linkable to the governance identity.

**Fix**: Use separate key hierarchies. Governance identity keys are disjoint from note spending keys. The stealth system (`cell/src/stealth.rs`) already separates `spend_pubkey` from `view_pubkey`; extend this to have a third `governance_pubkey`.

### Private intents + public directories: does directory registration leak intent patterns?

**Current model** (intent/src/lib.rs lines 8-29):
- Intents are public (everyone sees the MatchSpec)
- Matching is private (local Datalog eval)
- Fulfillment is private (direct to creator)

**Leak**: If Alice registers her cell in a public directory with specific capabilities, and a matching intent appears, observers can correlate "Alice has capability X" with "someone fulfilled intent requiring X."

**Mitigation (already implemented)**: PIR (`intent/src/pir.rs`) for browsing intents without revealing which you're interested in. Two-server IT-PIR ensures neither server learns the queried row.

**Gap**: Intent PUBLICATION still reveals what you need. The `CommitmentId` system (anonymous creator identity) helps, but the MatchSpec content is public.

### Private cell state + public CapTP sessions: do session patterns leak state mutations?

**Leak**: If Alice establishes a CapTP session to Bob immediately after a state mutation, timing correlation reveals "Alice did something and then talked to Bob about it."

**Mitigation**: The commit-reveal fulfillment (`intent/src/commit_reveal_fulfillment.rs`) and delay pool (`intent/src/delay_pool.rs`) add temporal mixing. Sessions should also use random delay before establishment.

### Where guarantees COMPOSE cleanly

The privacy guarantees compose well in these cases:
- **Presentation proof + fold chain + Merkle membership**: All three sub-proofs are bound via the `composition_commitment` (presentation.rs line 74-87). An attacker cannot mix-and-match sub-proofs from different presentations.
- **Note spending + value conservation**: The `CommittedTurnBuilder` (`sdk/src/committed_turn.rs`) combines Pedersen commitments with Bulletproof range proofs and STARK spending proofs. The conservation proof binds all notes together.
- **Selective disclosure + authorization**: The `revealed_facts_commitment` is a public input to the STARK, cryptographically binding revealed facts to the proof. You cannot claim to have revealed different facts.

### Where guarantees BREAK DOWN

- **Governance participation + anonymous authorization**: If you vote on a proposal (public act) and then present an anonymous credential from the same federation, the timing and federation root connect the two.
- **Cross-federation bridges + privacy**: The note bridge (`cell/src/note_bridge.rs`) requires the target federation to verify a spending proof against a TRUSTED ROOT from the source. Maintaining trusted roots requires attestation messages between federations, revealing the existence of cross-federation activity.
- **DFA routing + message privacy**: The DFA commitment is public (governance-attested). Anyone with the transition table can classify intercepted messages. Private routing requires per-session encryption layers ON TOP of the DFA classification.

## 7. Top Privacy Gaps (Prioritized)

### Critical

1. **No private cell migration protocol**: Cells cannot move between federations without revealing destination to the source or history to the target. The pieces exist (stealth addresses, STARK proofs, handoff certificates) but no unified "private migration" flow connects them.

2. **Governance votes are fully public**: The `VoteTracker` stores attributed votes. There is no ring-signature or threshold-encrypted voting path. This makes federation participants vulnerable to coercion.

3. **DFA routing tables are publicly committed**: Any entity with access to the constitution can classify all wire traffic. Route governance transparency directly undermines message privacy.

### High

4. **No timing padding for proof generation**: Turn complexity is observable via proof generation time and proof size. The Effect VM traces should be padded to fixed sizes.

5. **CapTP target_federation is cleartext in HandoffCertificate**: Session establishment reveals which federation you're connecting to.

6. **Intent MatchSpecs are fully public**: Anyone monitoring gossip knows what capabilities are being sought. The commit-reveal fulfillment helps but doesn't hide the initial request.

### Medium

7. **Note nullifiers are deterministic and cross-federation portable**: A nullifier published at federation A is correlatable with the same nullifier published at federation B during a bridge. Re-randomization on migration is not implemented.

8. **Gossip topic subscriptions are observable**: Dandelion++ hides message origin but not subscription interest. Decoy subscriptions are not implemented.

9. **No constant-time operation for STARK verification**: While the STARK proof itself is non-interactive, the VERIFICATION time varies with proof size, potentially leaking information about the proven statement's complexity.

## 8. Recommended Implementation Priority

1. **Private governance (ring-signature voting)**: Extend the blinded Merkle membership proof to a "vote with ring membership" scheme. One nullifier per voter per proposal for double-vote prevention. Estimated: 2-3 weeks, uses existing STARK infrastructure.

2. **Private cell migration flow**: Define a `CellMigrationProof` circuit that combines: exit proof (commitment retired at source) + entry proof (valid state at target) + stealth addressing. Estimated: 3-4 weeks.

3. **Fixed-size proof padding**: Pad all Effect VM traces to the next supported power-of-2 regardless of actual effect count. Trivial change in `effect_vm.rs` trace generation. Estimated: 2-3 days.

4. **Encrypted CapTP target**: Wrap `target_federation` in an ephemeral Diffie-Hellman encryption layer. The handoff certificate's target is encrypted to the recipient's view key. Estimated: 1 week.

5. **Encrypted DFA routing tables**: Replace the public route commitment with a per-validator encrypted route table. Prove correct routing via STARK without revealing the table. Estimated: 4-6 weeks (most complex).
