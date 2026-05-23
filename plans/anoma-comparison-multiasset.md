# Pyana vs. Anoma: Competitive Analysis & Multi-Asset Swap Design

## Feature-by-Feature Comparison

| Dimension | Anoma | Pyana | Verdict |
|-----------|-------|-------|---------|
| **Intent architecture** | Intents are first-class: declarative partial transactions specifying desired state changes. Solvers find counterparties and compose them into balanced transactions. | Intents are Need/Offer/Query broadcast over gossip. Local Datalog-based matching. Partial fills via FillConstraints. Compound intents (multi-spec). | **Anoma is more expressive** -- their intents specify arbitrary pre/post conditions over the resource machine. Ours are capability-shaped (action + resource + constraints). But ours are *private by default* (matching is local; Anoma's solver pool is public). |
| **State model** | Transparent Resource Machine (TRM): resources are typed, linearly consumed and produced. A resource has a label, logic function, value, quantity, and data. State is a set of resources. | Shielded Note Model: notes are committed tuples (owner, fields[8], randomness, creation_nonce). Spending = revealing nullifier. Conservation via Pedersen commitments + Bulletproof range proofs. | **Pyana is more private** -- our notes are opaque by default (commitment-based), values are hidden. Anoma's TRM is transparent by default (Taiga adds shielding as an opt-in layer). Our model is Zcash-like from birth. |
| **Shielded execution** | Taiga: a shielded execution engine over the TRM. Uses Halo2 proofs. Resources can be shielded (value hidden) or transparent. Partial order between shielded and transparent. | Effect VM + Cell Programs + STARK proofs: CellProgram defines valid transitions. Circuit variant requires STARK proof for each transition. Notes are always shielded. Bridge provides Presentation Proofs. | **Comparable.** Taiga and our Effect VM serve similar roles. Our advantage: STARK-native (fast proving, post-quantum friendly). Their advantage: Halo2 is more mature for arbitrary computation, accumulation-based (no FRI overhead). |
| **Validity predicates** | Every resource type carries a "logic function" (validity predicate) that must be satisfied for the resource to be consumed/created. This is the enforcement layer. | CellProgram (Predicate variant: FieldEquals/Gte/Lte/SumEquals/Immutable; Circuit variant: arbitrary AIR). Evaluated on every state transition. | **Structurally equivalent.** Both are per-resource/per-cell transition guards. Ours support SumEquals (conservation within a cell) natively, which is nice. Anoma's are more composable (VP composition via resource logic functions that call each other). |
| **Consensus** | Typhon: heterogeneous Narwhal-based DAG consensus. Mempool is DAG; ordering is BFT with Tendermint-like finality. | Blocklace (Cordial Miners): DAG-based BFT with cordial dissemination. Equivocation detection. Finality from supermajority ack. | **Comparable.** Both use DAG-based BFT. Cordial Miners paper is newer (2024) and has cleaner liveness arguments. Typhon has more production mileage but is heavier. |
| **Multi-chain** | Anoma instances communicate via IBC (Inter-Blockchain Communication). Each Anoma instance is sovereign but IBC enables cross-chain atomic settlement with Light Client verification. | Three bridge levels: (1) Midnight (attestation/observation), (2) Mina (proof-carrying, recursive Pickles), (3) EVM (planned, attestation + SNARK). CapTP + Handoff certificates for capability delegation across trust boundaries. | **Different philosophies.** Anoma is IBC-native (Cosmos heritage). We are *proof-carrying* where possible (Mina bridge needs no trust assumptions beyond cryptography). Our CapTP layer enables cross-chain capability delegation, which Anoma lacks entirely. |
| **Solver infrastructure** | Dedicated solver role: specialized participants find matches in the intent pool, compose balanced transactions, take fees. Competitive market for solver quality. | Intent engine + local matching in wallets. No dedicated solver role yet. Fulfillment is direct (wallet-to-wallet). | **Anoma is ahead** -- their solver market creates competition for match quality. We need a solver layer (see below). |
| **Privacy in discovery** | Intents are public in the mempool. Solvers see all intents. Information leakage is significant (your trading preferences are visible). Partial mitigation via intent encryption (FHE roadmap). | Intents are public but creator is anonymous (CommitmentId). Matching is local (wallet evaluates privately). Fulfillment is direct (not broadcast). PIR module exists for private information retrieval. | **Pyana is significantly more private.** Our matching-is-local model means the counterparty search doesn't leak what you hold. Anoma's solver model requires revealing intent details to the solver. |
| **Capability security** | None. Anoma has no object-capability model. Access control is via validity predicates on resources (more like smart contract guards). | Deep: bearer capabilities (macaroons), HMAC-chain attenuation, delegation, sensitivity levels, CapTP for remote caps, handoff certificates, budget gates, revocation channels. | **Pyana is far ahead.** Object capabilities are our foundational security model. Anoma has nothing comparable -- their VPs are guards, not transferable authority. |
| **Sovereignty spectrum** | Each Anoma instance is sovereign. Cross-instance is IBC (homogeneous protocol). No partial sovereignty within an instance. | Sovereign cells with programs defining their own state transition rules. Federation hierarchy. Cells can choose their trust boundary. Factory pattern for cell templates. | **Pyana is more granular.** Sovereignty at the cell level vs. only at the chain level. A cell can define its own physics (state constraints) without launching a new chain. |

## The Algorithm: Coincidence of Wants via Directed Graph Cycle Detection

The algorithm that enables multi-asset atomic swaps without reducing to a common denominator is **Coincidence of Wants (CoW) solving via cycle detection in the intent graph**. Anoma calls this their "solver" model. The formal algorithm is:

### The Intent-Matching Graph

Model the intent pool as a directed graph G = (V, E):
- Each vertex v represents an intent: "I have asset X, I want asset Y (quantity constraints)"
- Edge (u, v) exists iff u's "have" matches v's "want" (resource compatibility)

A **valid settlement** is a set of cycles in G such that every participant in the cycle can simultaneously fulfill their counterparty's want.

### Ring Trade Detection

A **ring trade** (or "coincidence of wants cycle") is a directed cycle C = (v_1, v_2, ..., v_k, v_1) where:
- v_1 has A, wants B
- v_2 has B, wants C
- ...
- v_k has X, wants A

All k transfers execute atomically. No intermediate asset, no common denominator.

### Formal Algorithm

```
FIND_RING_TRADES(intent_pool):
  G = build_compatibility_graph(intent_pool)
  cycles = []
  for each strongly_connected_component S in G:
    if |S| > 1:
      for each simple_cycle C in S (bounded by MAX_RING_SIZE):
        if all_constraints_satisfied(C):
          if all_quantities_compatible(C):
            cycles.append(C)
  return rank_by_social_welfare(cycles)
```

The quantity compatibility check is key:
- For each edge (u, v) in the cycle, the amount u can provide must be >= the amount v requires
- With partial fills, this becomes a linear programming problem (maximize total matched volume subject to min/max fill constraints)

### Why This Doesn't Need a Common Denominator

Traditional DEXes reduce everything to a base pair (e.g., ETH/USDC) because pairwise matching in a pool requires a price. But ring trades have a different structure:

- Alice has 100 APPLES, wants BANANAS (any reasonable amount)
- Bob has 50 BANANAS, wants CHERRIES
- Carol has 200 CHERRIES, wants APPLES

No pricing needed. No AMM pool needed. Each party's subjective valuation ("I consider this trade acceptable") is sufficient. The settlement is: Alice sends APPLES to Carol, Bob sends BANANAS to Alice, Carol sends CHERRIES to Bob.

This is **exactly** what Anoma's solvers do. The algorithm they use is a variant of:
1. **Johnson's algorithm** for finding all simple cycles in a directed graph (O(|V| + |E|)(C + 1) where C is the number of cycles)
2. Bounded by a maximum ring size (typically 3-5) to keep search tractable
3. With a quantity/constraint satisfaction layer on top

The formal name from economics literature: **Shapley-Scarf Top Trading Cycles** (for indivisible goods) or more generally, **kidney exchange algorithms** (Roth et al. 2004, Nobel Prize 2012).

## How Ring Trades Would Work in Our Intent Engine

### Current State (What We Have)

Our intent engine (`intent/src/`) already has:
- `Intent { kind: Need/Offer, matcher: MatchSpec, fill_constraints }` -- intents with partial fill support
- `MatchSpec` with actions, constraints, resource patterns -- the matching language
- `match_intent()` -- local evaluation of "can I satisfy this?"
- `FillConstraints` -- min/max fill amounts, fill-or-kill
- `partial_fill.rs` -- residual intent creation, cumulative fill tracking
- `gossip.rs` -- intent propagation with stake-gated spam prevention
- `commit_reveal_fulfillment.rs` -- anti-frontrunning

### What We Need for Ring Trades

**1. Intent type extension for asset exchange:**

Currently MatchSpec is capability-shaped ("I need action X on resource Y"). For ring trades, we need:

```rust
/// An exchange intent: "I have X, I want Y"
pub struct ExchangeSpec {
    /// What I'm offering (asset type + amount range)
    pub offering: AssetOffer {
        asset_type: u64,
        min_amount: u64,
        max_amount: u64,
    },
    /// What I'm seeking (asset type + amount range)  
    pub seeking: AssetSeek {
        asset_type: u64,
        min_amount: u64,
        max_amount: u64,
    },
    /// Optional: acceptable exchange rate bounds
    /// None = accept any amount within the seeking range
    pub rate_bounds: Option<RateBounds>,
}
```

This maps directly onto graph edges: offering = outgoing label, seeking = incoming label.

**2. A Ring Solver (new module: `intent/src/ring_solver.rs`):**

```rust
pub struct RingSolver {
    /// The intent pool view (exchange intents only)
    exchange_intents: Vec<ExchangeIntent>,
    /// Maximum ring size (3-5 for tractability)
    max_ring_size: usize,
}

impl RingSolver {
    /// Find all valid ring trades in the current intent pool.
    pub fn find_rings(&self) -> Vec<RingTrade> { ... }
    
    /// Settle a ring trade atomically (produces a compound Turn).
    pub fn settle_ring(&self, ring: &RingTrade, ledger: &mut Ledger) -> Result<TurnReceipt, ...> { ... }
}
```

**3. Atomic multi-party settlement via compound turns:**

Our `Turn` already has a `CallForest` that can encode multiple actions atomically. A ring settlement is:

```rust
fn settle_ring_as_turn(ring: &RingTrade) -> Turn {
    let mut forest = CallForest::new();
    for leg in &ring.legs {
        // Each leg: transfer from sender to recipient
        forest.add_root(Action {
            target: leg.sender_cell,
            effects: vec![
                Effect::NoteSpend { /* sender's note */ },
                Effect::NoteCreate { /* recipient's note */ },
            ],
            // Conservation proof covers ALL legs simultaneously
            ...
        });
    }
    Turn {
        call_forest: forest,
        conservation_proof: ring.conservation_proof(), // multi-party conservation
        ...
    }
}
```

The key insight: our `Turn` + `CallForest` already supports atomic multi-action execution with rollback. We just need the solver logic to FIND the rings, and then settlement uses existing infrastructure.

**4. Privacy-preserving ring solver:**

The hardest part: finding rings WITHOUT revealing everyone's intentions. Options:

- **Federated solver (Anoma-style):** A designated solver node sees all exchange intents. Simple but reveals trading preferences.
- **MPC-based matching:** Use multi-party computation to find cycles without any single party seeing the full graph. Expensive but maximally private.
- **Our approach (recommended):** Use the existing gossip model (intents are already public with anonymous creators), but have matching happen at the *federation level* (not individual wallets). The federation nodes collectively run the cycle-detection algorithm on the public intent pool. This works because:
  - Exchange intents are already anonymized (CommitmentId)
  - The matching result (who is in the ring) is sent directly to participants
  - Settlement uses shielded notes (amounts hidden)
  - The public only sees "a ring trade of size K settled" (not who, not amounts)

## Multi-Chain Atomic Settlement Design

### The Problem

Can we settle a swap atomically across pyana + Mina + EVM?

Requirements:
- All legs commit or all abort (atomicity across trust boundaries)
- No single point of trust
- Compatible with shielded execution

### Approaches by Bridge Level

**Level 1 (Midnight/EVM -- attestation-based):**
- Use HTLC (Hash Time-Locked Contracts) or the observation pattern
- Atomicity via hash locks: all legs share a secret; revealing the secret on any chain lets all others claim
- Trust assumption: liveness of observers, finality of each chain
- Latency: sum of finality times (Midnight ~30s, EVM ~12min with finality, pyana ~5s)

**Level 2 (Mina -- proof-carrying):**
- Verify the pyana STARK proof on Mina via recursive wrapping (already implemented in `bridge/src/mina.rs`)
- The Mina zkApp can verify that a pyana state transition occurred without trusting any intermediary
- Atomicity: the Mina side verifies the pyana-side commitment PROOF before releasing
- This is the holy grail: **trustless atomic settlement without hash locks**

**Level 3 (CapTP -- capability-based delegation):**
- Use Handoff Certificates for cross-chain capability transfer
- The capability itself carries proof of authorization
- Settlement: "I give you a capability to claim X on chain A, you give me a capability to claim Y on chain B"
- Both capabilities expire if not claimed (timeout = abort)

### Recommended Design: Proof-Carrying HTLC Hybrid

```
Cross-Chain Atomic Settlement Protocol:

1. SETUP:
   - Alice (pyana) wants asset on Mina
   - Bob (Mina) wants asset on pyana
   - Both post exchange intents

2. COMMIT PHASE:
   Alice generates secret s, computes h = BLAKE3(s)
   Alice posts conditional turn on pyana: 
     "Transfer X to Bob's pyana-cell, conditioned on knowledge of preimage of h"
   Bob sees this (via Mina bridge relay), posts conditional zkApp transaction on Mina:
     "Transfer Y to Alice's Mina address, conditioned on knowledge of preimage of h"

3. CLAIM PHASE:
   Alice reveals s on Mina (claims Y from Bob's zkApp)
   Bob extracts s from Alice's Mina tx (visible on-chain)
   Bob reveals s on pyana (claims X from Alice's conditional turn)

4. TIMEOUT:
   If Alice doesn't reveal s within T blocks on Mina, Bob's zkApp refunds
   If Bob doesn't claim on pyana within T+delta, Alice's conditional refunds
   (Standard HTLC timeout cascade)

Enhancement for privacy:
   - Alice's pyana-side commitment uses shielded notes (amount hidden)
   - The hash h is derived from a joint computation (not just Alice's secret)
   - Bob's Mina side can verify Alice's commitment via recursive STARK proof
     (the proof proves "a note of value >= X was locked with hash h" without
     revealing the exact value)
```

### Can CapTP + Handoff Certificates Enable Cross-Chain Atomic Commitment?

Yes, with limitations:

A Handoff Certificate is a signed statement: "I authorize R to contact T with these permissions." This can encode a cross-chain claim:

```
HandoffCertificate {
    introducer: pyana_federation_key,
    recipient: bob_mina_pubkey,
    swiss_number: <pre-registered claim token>,
    permissions: "claim:asset_X:amount_100",
    expiry: block_height + 1000,
}
```

The certificate travels cross-chain (it's just bytes -- can be embedded in a Mina transaction memo). The target federation validates it on presentation. But this is unilateral (not inherently atomic). You need the HTLC/hash-lock pattern on top for true atomicity.

## Multi-Asset Fees: Can Computrons Coexist?

### Current Model

- Computrons are the universal gas token (see `turn/src/economics.rs`)
- Fee distribution: 50% proposer, 30% treasury, 20% burn
- Epoch minting with halving schedule (disinflationary)
- Storage is rented per-epoch in computrons (`storage/src/metering.rs`)
- AMM exists for token conversion (`apps/amm/`)

### The Problem with Single-Token Fees

- Requires everyone to hold computrons before they can do anything (chicken-and-egg)
- AMM liquidity may not exist for rare assets
- Users experience friction: "I have USDC but can't use the network until I swap"

### Multi-Asset Fee Design (Proposed)

**Option A: Fee abstraction via solver (Anoma's approach)**

Services accept fees in any asset. A solver converts to computrons behind the scenes:
- User submits turn with `fee_token: USDC, fee_amount: 5`
- Fee solver accepts the USDC, pays computrons to the network
- Solver takes spread as profit

Pros: UX is seamless. Cons: requires active solver market, adds latency.

**Option B: Direct multi-asset acceptance (federation policy)**

Federation nodes accept payment in a whitelist of tokens:
- Node operator configures: "I accept computrons, USDC, ETH, pyana-native at rates X, Y, Z"
- The turn's `fee` field becomes multi-typed
- Conservation law still holds (the node creates a computron-valued note from the input token, burns computrons for the fee, keeps the input token)

Pros: no middleman. Cons: nodes must price assets, adds oracle risk.

**Option C: Capability-as-fee (our native model)**

Our system already has budget gates and capability tokens. A service can require:
- "Pay me in USDC" = intent with `min_budget` in USDC-denominated notes
- The fulfillment flow already handles this: `execute_committed_fulfillment_flow` transfers notes

The key insight: **our intent engine IS a multi-asset fee system**. A service that wants payment broadcasts an Offer intent ("I offer compute, I need USDC"). A client matches it. The fulfillment flow handles settlement atomically.

### Recommendation

**Keep computrons as the NETWORK-LEVEL fee** (consensus, storage, metering). But add a **meta-transaction wrapper** that lets users pay in any asset:

```rust
pub struct MetaTransaction {
    /// The actual turn to execute
    pub inner_turn: Turn,
    /// Payment in a non-computron asset
    pub fee_payment: ShieldedNote, // the user's payment note
    /// The fee solver's signature (they front computrons)
    pub solver_signature: [u8; 64],
    /// The solver's computron payment (covers inner_turn's fee)
    pub solver_fee_turn: Turn,
}
```

This composes naturally with our existing infrastructure:
- The solver is just another intent matcher
- The fee payment uses shielded notes (privacy preserved)
- The network only sees computrons at the consensus layer (clean separation)

## What Anoma Does That We Should Steal

### 1. Composable Intent Language

Anoma intents can express arbitrary pre/post conditions over resources. Our MatchSpec is constrained to capabilities (action/resource/constraint). We should add:

```rust
// New: arbitrary state predicate intents
pub enum IntentPredicate {
    /// Existing: capability-shaped
    Capability(MatchSpec),
    /// New: exchange-shaped (for ring trades)
    Exchange(ExchangeSpec),
    /// New: arbitrary predicate over state (for composable DeFi)
    StatePredicate {
        target_cell: CellId,
        pre_condition: Vec<StateConstraint>,
        post_condition: Vec<StateConstraint>,
    },
}
```

### 2. Solver Market with MEV Redistribution

Anoma's solvers compete to find the best matches. They extract value (like MEV) but it's transparent and redistributable. We should add:

- A solver role that can submit ring settlements
- Solver staking (skin in the game)
- Solver fee = percentage of value matched (not hidden extraction)
- Commit-reveal for solver submissions (we already have this infra!)

### 3. Partial Transaction Composition

Anoma lets multiple intents compose into a single balanced transaction (inputs = outputs across all participants). Our Turn's CallForest can do this today, but we haven't built the composition UX:

```
Intent A: "I give 100 APPLES"    }
Intent B: "I give 50 BANANAS"    } → Solver composes → Single atomic Turn
Intent C: "I give 30 CHERRIES"   }   with conservation proof
```

### 4. Resource Logic Composability

Anoma's validity predicates can call each other (VP composition). Our CellPrograms are isolated per-cell. Adding inter-cell constraint references would enable richer DeFi:

```rust
// "This cell's field[0] must equal that other cell's field[2]"
StateConstraint::CrossCell { 
    other_cell: CellId, 
    this_field: u8, 
    other_field: u8, 
    relation: Relation, 
}
```

## What We Do That Anoma Doesn't

### 1. Capability Security (Fundamental)

Anoma has NO object-capability model. Their security is guards-based (validity predicates check conditions). Ours is authority-based (capabilities carry transferable, attenuatable permission). This means:

- **Delegation without the delegator's ongoing involvement**: A macaroon with caveats can be passed to a third party who can use it independently. In Anoma, you'd need to modify the resource's VP.
- **Principle of least authority**: Capabilities grant exactly what's needed, nothing more. In Anoma, a VP either passes or fails -- no granularity.
- **Revocation channels**: We can revoke a capability without touching the resource it protects.

### 2. Privacy-by-Default Discovery

Our intent matching happens LOCALLY in wallets. Anoma's happens in public solver pools. This is a fundamental architectural choice with massive privacy implications:

- In Anoma: "I want to buy ETH for USDC at price X" is visible to all solvers (front-running vector)
- In pyana: the wallet privately evaluates "can I satisfy this?" without revealing what it holds or whether it matched

### 3. Sovereignty Spectrum (Cell-Level)

Anoma instances are either sovereign or connected via IBC. There's no middle ground. Our cells can:
- Run arbitrary CellPrograms (their own physics)
- Choose trust boundaries (federation membership)
- Delegate authority selectively (via capabilities)
- Migrate between federations (note export/import via nullifiers)

### 4. Proof-Carrying Bridges (Mina)

Anoma's cross-chain story is IBC (light client verification). Our Mina bridge is proof-carrying:
- No dispute window
- No economic security assumptions
- Verification is computational, not stake-based
- Recursive composition (proof-of-proof)

### 5. ZK Authorization (STARK-native)

Our authorization is proven in ZK (multi-step AIR proves Datalog evaluation results in ALLOW without revealing which token or what delegation chain). Anoma's VPs run in cleartext (Taiga adds shielding but doesn't prove authorization decisions in ZK -- it proves resource consumption validity).

### 6. Storage Metering as a Service Market

Our storage layer is metered and rented (computrons per byte per epoch). This creates a natural market for hosting services. Anoma has no comparable model -- storage is implicit in validator state.

## Implementation Roadmap

### Phase 1: Exchange Intents (Low-hanging fruit)
- Add `ExchangeSpec` to `IntentKind` or as a new MatchSpec variant
- Extend gossip to handle exchange intents
- Two-party matching (A wants B, B wants A) using existing matcher

### Phase 2: Ring Solver
- Implement directed graph construction from exchange intents
- Johnson's algorithm (bounded by MAX_RING_SIZE=5) for cycle detection
- Quantity satisfaction LP solver for partial fills within rings
- Settle via compound Turn with multi-note conservation proof

### Phase 3: Solver Market
- Define solver role (staked participants)
- Commit-reveal for solver submissions (reuse existing infra)
- Fee structure (percentage of matched volume)
- Competition mechanism (best ring wins)

### Phase 4: Cross-Chain Ring Trades
- HTLC-based atomic settlement for ring trades spanning chains
- Proof-carrying leg for Mina side (verify pyana STARK on Mina)
- Attestation leg for Midnight/EVM side
- CapTP handoff for capability legs

### Phase 5: Multi-Asset Fees
- MetaTransaction wrapper (solver fronts computrons)
- Solver as intent matcher (exchange user-token for computrons)
- Federation-level whitelist of accepted fee tokens
- AMM integration for automatic conversion path

## Code References

| Building Block | Location | Relevance |
|---|---|---|
| Intent engine core | `intent/src/lib.rs` | Need/Offer/Query, MatchSpec, FillConstraints |
| Local matching | `intent/src/matcher.rs` | `match_intent()`, `satisfies_spec()` |
| Partial fills | `intent/src/partial_fill.rs` | Residual intents, CumulativeFillTracker |
| Fulfillment + STARK proofs | `intent/src/fulfillment.rs` | `execute_committed_fulfillment_flow()` |
| Anti-frontrunning | `intent/src/commit_reveal_fulfillment.rs` | Commit-reveal for solver fairness |
| Cell programs (validity predicates) | `cell/src/program.rs` | CellProgram, StateConstraint |
| Shielded notes | `cell/src/note.rs` | Note, NoteCommitment, Nullifier |
| Value commitments | `cell/src/value_commitment.rs` | Pedersen commitments, conservation |
| AMM with multi-hop routing | `apps/amm/src/router.rs` | `find_route()`, `execute_route()` |
| Orderbook matching | `apps/orderbook/src/matching.rs` | Price-time priority, partial fills |
| Mina bridge (proof-carrying) | `bridge/src/mina.rs` | Recursive STARK wrapping |
| Midnight bridge (attestation) | `bridge/src/midnight.rs` | Threshold attestation, observation |
| Blocklace consensus | `blocklace/src/lib.rs` | DAG blocks, cordial dissemination |
| CapTP handoff | `captp/src/handoff.rs` | Cross-chain capability transfer |
| Turn executor (atomicity) | `turn/src/executor.rs` | CallForest, rollback, conservation |
| Computron economics | `turn/src/economics.rs` | Minting, fee distribution, halving |
| Storage metering | `storage/src/metering.rs` | Per-byte-epoch rental costs |
| Compute exchange | `apps/compute-exchange/src/settlement.rs` | Atomic escrow settlement |

## Summary

**Anoma's core advantage:** Intent composability and solver infrastructure. Their intents can express any state predicate; their solvers find optimal matches in a competitive market. We should steal the concept of composable exchange intents and ring-trade solving.

**Pyana's core advantages:** Privacy (matching is local, notes are shielded), capability security (delegation, attenuation, revocation), sovereignty granularity (cell-level), and proof-carrying bridges (no trust assumptions). These are architectural choices baked into our foundations that Anoma cannot easily retrofit.

**The multi-asset swap algorithm** is cycle detection in the intent compatibility graph (Top Trading Cycles / kidney exchange / Coincidence of Wants solving). It does NOT require a common denominator because each participant specifies their own subjective "I have X, I want Y" without pricing either against a base. Our existing partial fill infrastructure (FillConstraints, residual intents, compound MatchSpecs) provides the primitives; we need the graph layer and solver role on top.

**The honest answer:** We should build a solver layer inspired by Anoma's design, but preserve our privacy advantage by keeping the matching information minimal (exchange intents reveal only asset types and quantity ranges, not identities or full portfolios).
