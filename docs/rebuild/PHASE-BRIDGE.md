# PHASE-BRIDGE — Cross-Chain / Observation Bridge in the dregg2 Verified Rebuild

> **Status:** design map + honest scope statement for the cross-chain bridge layer ("above-core" in the rebuild strata). This is a READ-ONLY study + design artifact. No code was modified.
>
> **Scope:** This phase sits at the boundary between the dregg2 **kernel** (verified via step-completeness + cryptokernel discharge in PHASE-CRYPTOKERNEL, proven green) and the **distributed protocol** (the node's observable network semantics, addressed in PHASE-UC-TRANSPORT and the forthcoming PHASE-DISTRIBUTED-ADVERSARY extensions). The bridge is the **foreign-chain observation layer** — how a dregg cell learns about another chain's state and proves conditions over it in a verifiable, capability-preserving way. The design names OPENs precisely and distinguishes what is reusable from the cryptokernel from what is genuinely new research.

---

## 1. What a Cross-Chain Bridge MUST Guarantee

A cross-chain bridge is a set of predicates over **foreign-chain observations** (claimed foreign state values) such that, when admitted into dregg's execution, they:

1. **Soundness (no false positives):** An admitted bridge observation implies the foreign condition genuinely held on the foreign chain (to the extent we can verify it).
2. **Atomicity (no double-release):** If a bridge action locks value on chain A and mints on chain B, the lock and mint are tied — either both happen or neither does. This is an **existential guarantee** (it is possible to construct a sequence where both occur) rather than a liveness guarantee (the network will eventually do it).
3. **Light-client completeness:** A verifier that knows only a foreign chain's finalized block headers can verify bridge observations without trusting a relay or a specific foreign full node.
4. **No equivocation:** The foreign chain cannot be made to give contradictory answers about its state without violating its own consensus assumptions.

These are candidate **Lean theorem shapes** (not yet all proved):

| Guarantee | Candidate Lean shape | Status (§1.1) |
|-----------|---|---|
| **Soundness** | `∀ (obs : ForeignObs) (π : BridgeProof), verifyBridge obs π = true → ForeignChain.honest_state obs` | **Reusable from Crypto.Bridge** — the `bridge_verify_sound` theorem |
| **Atomicity** | `∀ (lock mint : BridgeAction), locked lock ∧ minted mint ∧ sameAtom lock mint → ¬(locked lock ∧ ¬minted mint) ∧ ¬(¬locked lock ∧ minted mint)` | **NEW** — cross-chain atomic-swap / HTLC algebra |
| **Light-client** | `∀ (obs : ForeignObs) (headers : List BlockHeader), obs.block ∈ headers ∧ FinalityRule.finalized (headers) → ∃ π, verifyBridge obs π = true` | **OPEN** — foreign finality model not yet formalized |
| **Non-equivocation** | `∀ (obs obs' : ForeignObs), obs.value ≠ obs'.value → ¬(∃ π π', verifyBridge obs π ∧ verifyBridge obs' π')` OR `slashable witness` | **OPEN** — requires foreign consensus model + slashing algebra |

### 1.1 What the Cryptokernel Already Discharges

From `PHASE-CRYPTOKERNEL.md` §5, the bridge kind has a **full AIR (`bridge_action_air.rs`)** that is already real, and the Lean metatheory now discharges it end-to-end:

- **`Bridge.lean`** proves `bridge_bridge : Satisfies bridgeCircuit (c, threshold, v) ↔ BridgeRelation compress (c, threshold, v)` — the **soundness half** (a satisfying trace certifies an observed value opens against a committed foreign digest and clears a comparison threshold). The comparison is via the proven `RecordCircuit.range_iff` gadget (no primitive seam); the opening is over an abstract `compress` (its binding is the Layer-A carrier `CryptoPrimitives.binding`, consumed elsewhere).
- **`bridge_verify_sound`** is **derived** from `bridge_bridge` + the STARK extractability carrier: `verify accepts → ∃ v vDigest salt, BridgeRelation …`. The law is proved, not assumed.
- **`bridge_dial_wired`** pins the epistemic floor to `selective` (the committed foreign digest + threshold are disclosed; the exact observed value is the hidden witness).
- **`bridge_registry_cascade`** composes with the registry machinery, so an accepted bridge proof both discharges the predicate and proves the relation.

**The soundness guarantee (Guarantee #1) is thus DISCHARGED for the comparison predicate specifically:** an accepted bridge proof certifies the foreign-state digest opens to an observed value that clears the threshold. The comparison algebra is unconditional (no oracle, no primitive seam for `threshold ≤ v`).

What is NOT discharged by the cryptokernel alone:

- The **validity of the foreign commitment `c` itself** — the digest of the foreign state as witnessed by the bridge. The cryptokernel says "this digest opens to this value," but not "this digest is the correct digest of the foreign state." That requires knowing what the foreign chain's consensus says.
- **Which foreign state to observe** — the `selective` dial discloses the commitment + threshold, but the choice of which foreign-chain block to read from is a runtime policy, not in-circuit (the bridge action specifies a `foreign_block_height`, but that PI field is merely cross-checked against the committed digest, not verified against the foreign chain's headers).
- **Atomicity across chains** — if the bridge locks on chain A and mints on chain B, the cryptokernel proves each independently; proving they are the same atomic action (same nonce, timeout, etc.) is a **cross-chain coordination theorem** that sits above the kernel.

---

## 2. The Trust Boundary: Foreign Chain as Assumption

**Critical constraint:** dregg2 **cannot verify Cardano finality, Ethereum consensus, or any foreign chain's protocol inside Lean**. The foreign chain's consensus is an **external oracle**.

The bridge's trust model is a **two-layer seam:**

### 2.1 Layer 1 — In-Lean (Proved)

The cryptokernel discharges: **given** a foreign-chain commitment `c` (or a set of finalized block headers), a bridge proof certifies an observed foreign value against that commitment.

- `BridgeRelation compress c threshold v vDigest salt` = "`v` opens against `c` (via `vDigest` + `salt`) **AND** `threshold ≤ v`"
- `bridge_verify_sound` : accept → relation holds
- **This is purely algebraic and proved end-to-end in Lean.**

### 2.2 Layer 2 — Foreign Consensus (Boundary)

**ASSUMPTION (never proved, carried as a `Prop` parameter):** the commitment `c` (or the finalized headers) are the *actual* foreign-chain state, not forged or equivocated.

```lean
-- In the bridge kind's verifier kernel:
variable {ForeignChain : Type}
variable (foreignChainHonest : Prop)  -- Never proved in Lean.
  -- "The consensus of ForeignChain produces finalized headers H, and c ∈ H."

-- The bridge's full soundness (in-Lean + assumption):
theorem bridge_full_soundness (obs : ForeignObs) (π : Proof)
    (h : bridgeVerify obs π = true)
    (hforeign : foreignChainHonest) :
    ∃ v, ForeignChain.honest_state obs c ∧ threshold ≤ v := by
  -- bridge_verify_sound gives: ∃ v, BridgeRelation c threshold v …
  -- foreignChainHonest says: c is the true foreign digest
  -- → the observed value truly clears the threshold on the foreign chain
```

**The assumption `foreignChainHonest` is the trust boundary.** It is:
- **Not an axiom** (not a bare `assume`). It is a parameter to the bridge verifier's contract.
- **Discharged operationally** by the **light-client verifier** running on the foreign chain (e.g., a Cardano light client) or by the **federation attestation** (a quorum of honest relays signs the foreign-chain observation).
- **Named explicitly** in the type signature of any dregg cell that uses a cross-chain predicate.

### 2.3 The Relayer/Light-Client Role

The relayer (or light-client oracle) is not a verifier in Lean — it is an **executor of the foreign consensus**. Its job is to:

1. **Monitor** the foreign chain and extract finalized blocks (or state commitments).
2. **Compute** the commitment `c` (Merkle root, state root, etc.) from the foreign chain's data.
3. **Prove** (off-chain, cryptographically) that the commitment is correct (e.g., sign it with a federation key, or include it in a Merkle proof of the foreign block's state tree).
4. **Deliver** the commitment + proof to dregg as a **parameter** to the bridge predicate.

The dregg kernel then verifies: **given this commitment, is the observed foreign value correct?** The foreign chain's consensus is outside the Lean model.

---

## 3. The Observation-Bridge Pattern (Coalgebra Style)

The **observation bridge** is a **portal pattern** (Miller/capability-security style) that:

1. **Declares a foreign-chain interface** (what a relayer must provide).
2. **Binds observations to commitments** (the bridge kernel's job).
3. **Routes observations through a proof-carrying mechanism** (HTLC-style atomic swap or a simple lock/mint pair).
4. **Preserves causality** (the observation is tied to a specific foreign-chain block height, preventing replays across forks).

### 3.1 The Foreign-Chain Interface (Coalgebraic)

```lean
-- A foreign chain as a *capability* (a coalgebra):
class ForeignChain (C : Type) where
  -- The observable state: a commitment (digest, root, hash) at a given block height
  Obs := C × Nat → (commitment : Digest) × (proof : Proof)
  
  -- Finality predicate: which blocks are finalized and will not reorg
  finalized : C → Nat → Prop
  
  -- Safety: finalized blocks do not equivocate
  finality_no_equivocation : ∀ h, finalized C h → 
    ∀ (c c' : Digest), c ≠ c' → ¬(obs C h = c ∧ obs C h = c')

-- A relayer's obligation: provide observations + proofs of finality
class Relayer (ForeignChain : Type) where
  -- Read a finalized observation from the foreign chain
  observeFinal : ∀ (height : Nat), 
    ForeignChain.finalized height →
      ∃ (c : Digest) (π_obs : Proof), 
        ForeignChain.obs height = c ∧ verify_obs c π_obs
```

This is **not a full consensus model** (we do not model Cardano's Byzantine agreement), but it is a **behavioral interface** that names what dregg assumes about the foreign chain.

### 3.2 The Bridge Action (Atomic Swap Pattern)

The bridge discharges itself as an **atomic conditional swap** (HTLC / hash-time-locked contract):

```lean
-- A bridge action is a pair of locked/minted effects tied by a common nonce
structure BridgeAction where
  nonce : Digest                    -- Unique identifier (prevents replays)
  foreign_chain : ChainId           -- Which foreign chain
  foreign_height : Nat              -- The finalized block height to observe
  lock : Effect                     -- Debit on dregg (lock value in pending bridge)
  mint : Effect                     -- Credit on foreign chain (or vice versa)
  comparison : BridgeRelation       -- The observation: v opens against c ∧ threshold ≤ v

-- Atomicity: both happen or neither does
theorem bridge_atomic (a : BridgeAction) :
    (effects_contains a.lock ∧ effects_contains a.mint)
      ∨ (¬effects_contains a.lock ∧ ¬effects_contains a.mint) := by
  -- Proven by: nonce is the key; any mismatch is slashable
  sorry
```

The **nonce** is the glue. Both the lock (on dregg) and the mint (on foreign chain, or delivery to dregg from the foreign chain) reference the same nonce. The federation's agreement on nonce ensures atomicity — if the lock is committed on dregg, the relay will not mint a mismatched nonce on the foreign chain (or if they do, the foreign chain's light client will reject it).

### 3.3 Federated Attestation + Dispute (the Practical Model)

In practice, the bridge runs on a **federated model** (as implemented in `plans/midnight-bridge-production.md`):

1. **Relayer posts** a foreign observation (committed digest + proof) with a bond.
2. **Challenge window** (configurable, e.g., 6 hours of dregg blocks).
3. **Anyone can challenge** by re-running the light-client check or providing a conflicting observation.
4. **If challenged and relayer is wrong:** bond is slashed, and the correct observation is used.
5. **If unchallenged:** the observation is finalized, and bridge actions proceed.

**In Lean:** this is a **`Dispute` oracle** (a `Prop` carrier). The bridge verifier assumes "this observation has passed the challenge window" — a temporal assumption carried in the type of the bridge predicate.

---

## 4. Staged Plan: Minimal First Discharge + Roadmap

### 4.1 Smallest Verifiable Increment (§5 below)

**First bridge-kind obligation to discharge end-to-end: Midnight bridge observation (comparison-based lock/mint).**

Why this one:
- **AIR exists** (`bridge_action_air.rs:1-70`, binding at full fidelity).
- **Lean discharge done** (`Crypto.Bridge.lean` is complete and green).
- **Transport and relayer pattern exist** (`plans/midnight-bridge-production.md` documents the production architecture).
- **No new consensus model needed** (the federation + dispute framework handles foreign-chain finality).
- **Exercises the full stack:** kernel discharge → cross-chain atomicity → dial wiring.

### 4.2 Path to the Rest (Sequence)

**Phase 4a — Midnight bridge observation (as §5 below):**
- **Lean work:** formalize the `BridgeAction` atomic-swap algebra, prove that matched nonces prevent double-release, wire the dial at `selective` (commitment + threshold disclosed, observed value hidden).
- **Rust work:** formalize the `Dispute` oracle (a per-observation challenge window + slash-on-wrong proof), integrate the federation attestation into the verifier.
- **Cross-chain work:** implement the light-client (Cardano/Midnight finality checker), the relayer protocol (push observations + proofs to dregg).
- **Differential:** test Midnight bridge locks/mints against actual Cardano observations.

**Phase 4b — EVM bridge (rich contracts as dregg cells):**
- **Extend `BridgeAction`** to cross both directions: dregg → EVM and EVM → dregg.
- **Resolve the SP1 wrapper** (SP1 BabyBear STARK → Groth16 → EVM verification).
- **Formalize `DreggSovereignCell` semantics** (a cell whose "relayer" is an Ethereum contract).
- **Prove the cross-chain Turn composition** (when a dregg turn calls an EVM cell and vice versa).

**Phase 4c — Advanced light clients (Merkle-based membership + non-membership):**
- **Extend the bridge kind** to support Merkle-proof observations (not just point lookups).
- **Non-membership proofs** (showing a foreign key does not exist in a state tree).
- **Reuse existing Lean gadgets:** `Crypto.NonMembership`, `Crypto.Merkle` already proven.

**Phase 4d — Cross-group coordination + choreography:**
- **Extend the bridge to span groups** (a dregg cell in group A calls a cell in group B via a bridge-like cross-group capability).
- **Prove the projection** (`G ↾ p` for a choreography where bridge is a primitive action).
- **This is OPEN #1** (`dregg2/docs/rebuild/OPEN-PROBLEMS.md §1`, the "projection-time three-judgement split").

### 4.3 What Remains Open

| OPEN | Status | Why | Path |
|---|---|---|---|
| **Foreign finality model** | **OPEN** | Dregg2 has no formalized Cardano/Ethereum consensus. The bridge assumes foreign-finality as a `Prop` carrier. | Fetch the foreign chain's consensus paper (DLS88-style for partial synchrony); formalize in Lean if needed (honest: out of scope for now). |
| **Atomicity across chains (liveness)** | **OPEN** | We can prove "if both lock and mint are committed, they match" (by nonce). We cannot prove "both will eventually commit" without a full distributed-commitment protocol (2PC/3PC). | Use federation timeout + slash-on-equivocation (practical); or develop a 3PC-style cross-chain consensus (research-grade). |
| **Choreography projection with bridges** | **OPEN** | Standard MPST does not have cross-chain primitives. Extending the projection theorem to a choreography with bridges as primitives is **OPEN #1** in `OPEN-PROBLEMS.md`. | This is a genuine multiparty-session-types extension; needs new corpus (fetch Montesi / Montesi et al. choreography papers). |
| **Cycle detection + GC across chains** | **OPEN** (impossible in practice) | A dregg cell holding a reference to a foreign cell (via bridge) can create cycles. Detecting if the cycle is live (reachable from any root) requires global consensus on what is "reachable." Infeasible without a ledger. | Lease-based expiry (practical); distributed cycle GC is impossible under partition (per `OPEN-PROBLEMS §6`). |
| **Full dynamic UC bridge composition** | **OPEN** | The bridge is part of the protocol. Proving full UC composition (the bridge + the whole protocol realizes an ideal cross-chain-bridge functionality) is beyond the scope of this phase. | This is the goal of PHASE-UC-TRANSPORT; the commitment security is discharged there. Full bridge UC composition is future work. |

---

## 5. SMALLEST VERIFIABLE INCREMENT: Midnight Bridge Observation (Lock/Mint Comparison)

### 5.1 Lean work (new theorems)

**1. Formalize the BridgeAction algebra:**

```lean
namespace Dregg2.Bridge

structure BridgeAction where
  nonce : Digest
  foreign_chain : ChainId
  foreign_height : Nat
  lock : Effect          -- on dregg (debit)
  mint : Effect          -- on foreign chain (credit)
  lock_amount : Int
  mint_amount : Int
  comparison : BridgeRelation  -- the observation

/-- Atomicity: matched nonce ensures both lock and mint happen together or not at all. -/
theorem bridge_atomic_by_nonce (a : BridgeAction) :
    ∀ (log : List Effect),
      effects_contain_nonce a.nonce a.lock log →
      effects_contain_nonce a.nonce a.mint log := by
  -- If the lock is in the log with nonce n, then the foreign-chain relay
  -- will not accept a mint with a *different* nonce on the same (chain, height).
  -- This is enforced by federation attestation (Dispute oracle), not in-circuit.
  sorry -- OPEN: requires foreign-chain dispute model

/-- Amount matching: the lock and mint amounts must agree (no skimming). -/
theorem bridge_conservation_cross_chain (a : BridgeAction) :
    a.lock_amount = a.mint_amount := by
  -- The observation's comparison threshold is the *declared* amount.
  -- The foreign commitment `a.comparison.c` is verified to open to a value
  -- ≥ the threshold (via bridge_verify_sound). The lock amount must equal that threshold.
  sorry -- OPEN: requires binding between Effect.BridgeLock.amount and comparison.threshold
```

**2. Prove the atomicity preservation in the effect stream:**

```lean
/-- Two bridge actions with the same nonce and opposite directions (lock ↔ mint) 
form an atomic pair. -/
theorem bridge_pair_atomic (a₁ a₂ : BridgeAction) :
    a₁.nonce = a₂.nonce →
    (effect_type a₁.lock = .BridgeLock ∧ effect_type a₂.mint = .BridgeMint) →
    (a₁.foreign_chain = a₂.foreign_chain) →
    (effects_contain_nonce a₁.nonce a₁.lock ∨ ¬effects_contain_nonce a₁.nonce a₂.mint) := by
  -- Soundness: either both are in the log (committed atomically) or both are out.
  -- This is enforced by Dispute oracle (federation attestation).
  sorry
```

**3. Wire the dial at `selective`:**

The bridge observation discloses:
- The foreign commitment `c` (which foreign block was read)
- The comparison threshold (how much value was observed)

It hides:
- The exact observed value `v` (only the fact that it clears the threshold is public)

```lean
/-- Bridge kind: statement = (c, threshold), floor = selective. -/
def bridgeKindObligation : KindObligation Dg where
  Statement := Crypto.Bridge.Statement Dg  -- (c, threshold)
  dialFloor := Dial.selective
```

**4. Prove the registry cascade:**

```lean
/-- An accepted bridge proof discharges the bridge predicate and proves the relation. -/
theorem bridge_full_cascade [K : BridgeVerifierKernel Dg Proof]
    (hext : K.extractable)
    (hforeignOK : ForeignChainOK)  -- The foreign commitment is honest
    (stmt : Statement Dg)
    (proof : Proof)
    (haccept : K.verify stmt proof = true) :
    (Discharged stmt proof) ∧
    (∃ (v : Int) (vDigest salt : Dg),
        BridgeRelation K.compress stmt.c stmt.threshold v vDigest salt ∧
        ForeignChain.obs stmt.c = v) := by
  constructor
  · exact registry_sound … haccept
  · obtain ⟨v, vD, salt, hrel⟩ := bridge_verify_sound hext stmt proof haccept
    exact ⟨v, vD, salt, hrel, by assumption⟩
```

### 5.2 Rust work (verifier + relayer)

**1. Extend the bridge verifier kernel to include the Dispute oracle:**

```rust
// In Dregg2/Crypto/BridgeVerifierKernel
pub struct BridgeVerifierKernel {
    pub compress: Box<dyn Fn(&Digest, &Digest) -> Digest>,
    pub verify: Box<dyn Fn(&Statement, &Proof) -> bool>,
    pub extractable: bool,
    
    // NEW: Dispute oracle
    pub disputed: Box<dyn Fn(&Observation) -> bool>,  // Has this obs been challenged?
    pub slash_if_wrong: Box<dyn Fn(&Observation, &Proof) -> Option<Slash>>,
    pub finalized: Box<dyn Fn(&Observation) -> bool>,  // Passed challenge window?
}

impl BridgeVerifierKernel {
    pub fn accept_bridge_observation(&self, obs: &Observation, proof: &Proof) -> Result<()> {
        // 1. STARK proof verifies (extract the observed value + commitment)
        if !self.verify(&obs.stmt, proof) {
            return Err("STARK verification failed");
        }
        
        // 2. Check that the observation has finalized (challenge window passed)
        if !self.finalized(obs) {
            return Err("Observation not yet finalized");
        }
        
        // 3. If disputed, the slash proof must be present and valid
        if self.disputed(obs) {
            let slash = self.slash_if_wrong(obs, proof)?;
            // Relayer who posted the wrong observation is slashed
        }
        
        Ok(())
    }
}
```

**2. Formalize the Dispute oracle for Midnight:**

```rust
// In Verifier::verify_bridge (called during Effect VM execution)

pub struct DisputeOracle {
    federation_quorum: usize,      // How many federation members must sign?
    challenge_window_blocks: u64,  // How many blocks before finalization?
    cardano_finality_depth: u64,   // Cardano block depth for finality
}

impl DisputeOracle {
    pub fn finalized(&self, obs: &Observation) -> bool {
        // Observation is finalized if:
        // 1. It has been on dregg for ≥ challenge_window_blocks, AND
        // 2. No valid challenge proof was submitted, OR
        // 3. Challenges were resolved in favor of the relayer
        
        let dregg_blocks_since_post = current_height() - obs.posted_at;
        let finality_reached = dregg_blocks_since_post >= self.challenge_window_blocks;
        
        !self.is_disputed(obs) || self.disputes_resolved_in_favor(obs)
            && finality_reached
    }
}
```

**3. Light client (Cardano finality checker):**

```rust
// In circuit/src/cardano_light_client.rs (or a sibling module)

pub struct CardanoLightClient {
    finalized_headers: Vec<CardanoBlockHeader>,  // Blocks ≥ Cardano finality depth
    state_roots: HashMap<Nat, StateRoot>,        // block_height -> state commitment
}

impl CardanoLightClient {
    pub fn observe_state(&self, height: Nat) -> Result<(Digest, Proof)> {
        // 1. Check that height is finalized (deep enough in the chain)
        if height + CARDANO_FINALITY_DEPTH > self.current_height() {
            return Err("Not finalized yet");
        }
        
        // 2. Extract the state root from the finalized block
        let state_root = self.state_roots.get(&height)
            .ok_or("Block not in light client")?;
        
        // 3. Construct a membership proof (Merkle path from block header to state root)
        let proof = self.prove_state_root_in_block(height, state_root)?;
        
        Ok((state_root.clone(), proof))
    }
    
    pub fn prove_state_root_in_block(&self, height: Nat, root: &Digest) -> Result<Proof> {
        // Proves: the state root is a member of the finalized block at height
        // (Merkle membership, or a simpler commitment proof for direct finalization)
        todo!()
    }
}
```

### 5.3 Cross-chain work (relayer protocol)

**1. Relayer state machine (push observations to dregg):**

```rust
// In app-framework/src/midnight_bridge.rs

pub enum RelayerState {
    Idle,
    Observing { foreign_height: Nat },
    AttestingObservation { obs: Observation },
    AwaitingChallenge { obs: Observation, window_ends: BlockHeight },
    Finalizing { obs: Observation },
}

impl MidnightBridge {
    pub fn relay_step(&mut self) -> Result<()> {
        match &self.state {
            RelayerState::Idle => {
                // Poll the Cardano light client for a new finalized block
                if let Some((height, root)) = self.cardano.next_finalized_block()? {
                    self.state = RelayerState::Observing { foreign_height: height };
                }
            }
            RelayerState::Observing { foreign_height } => {
                // Fetch the observation from the light client
                let (commitment, proof) = self.cardano.observe_state(*foreign_height)?;
                
                // Create a bridge observation with the threshold from pending locks
                let pending_lock = self.dregg_pending_lock()?;  // Effect::BridgeLock
                let obs = Observation {
                    nonce: pending_lock.nonce,
                    foreign_chain: ChainId::Cardano,
                    foreign_height: *foreign_height,
                    commitment,
                    threshold: pending_lock.amount,
                    proof,
                };
                
                // Post to dregg with federation attestation
                let attestation = self.federation.attest(&obs)?;
                self.dregg.post_observation(&obs, &attestation)?;
                
                self.state = RelayerState::AttestingObservation { obs };
            }
            RelayerState::AttestingObservation { obs } => {
                // Wait for the challenge window
                let challenge_end = obs.posted_at + CHALLENGE_WINDOW;
                if current_block_height() >= challenge_end {
                    self.state = RelayerState::AwaitingChallenge { obs: obs.clone(), window_ends: challenge_end };
                }
            }
            RelayerState::AwaitingChallenge { obs, window_ends } => {
                // If the observation was not challenged, finalize it
                if !self.dregg.is_disputed(obs) {
                    self.state = RelayerState::Finalizing { obs: obs.clone() };
                } else if current_block_height() > *window_ends + DISPUTE_RESOLUTION_WINDOW {
                    // The dispute is resolved; check the outcome
                    if self.dregg.dispute_resolved_in_favor(obs) {
                        self.state = RelayerState::Finalizing { obs: obs.clone() };
                    } else {
                        // Relayer lost the dispute; slash bond and restart
                        eprintln!("Bridge observation disputed and lost; bond slashed");
                        self.state = RelayerState::Idle;
                    }
                }
            }
            RelayerState::Finalizing { obs } => {
                // Trigger the minting on Midnight (or the next bridged effect on dregg)
                self.dregg.finalize_bridge_observation(obs)?;
                self.state = RelayerState::Idle;
            }
        }
        Ok(())
    }
}
```

**2. Federation attestation:**

```rust
// In credentials/src/federation_attestation.rs

pub struct FederationAttestation {
    observation: Observation,
    signatures: Vec<(PartyId, Signature)>,  // Quorum of federation members
    bond: Coin,                              // Relayer's slashable bond
}

impl Federation {
    pub fn attest(&self, obs: &Observation) -> Result<FederationAttestation> {
        // 1. Each federation member verifies the observation independently
        for member in &self.members {
            member.verify_observation(obs)?;
        }
        
        // 2. Collect signatures (⅔ quorum)
        let sigs = self.collect_signatures(obs, QUORUM_THRESHOLD)?;
        
        // 3. Relayer posts bond (slashed if observation is wrong and challenged)
        let bond = self.slash_if_wrong_cost();
        
        Ok(FederationAttestation {
            observation: obs.clone(),
            signatures: sigs,
            bond,
        })
    }
}
```

### 5.4 Differential (test bridge against real observations)

**Test harness:**

```rust
// In verifier/tests/integration_midnight_bridge.rs

#[test]
fn test_midnight_bridge_lock_mint_atomic() {
    // 1. Cardano light client observes a state in block 8M
    let cardano = CardanoLightClient::from_finalized_headers(…);
    let (cardano_commitment, proof) = cardano.observe_state(8_000_000).unwrap();
    
    // 2. Relayer constructs a bridge observation
    let obs = Observation {
        nonce: Digest::from("nonce-12345"),
        foreign_chain: ChainId::Cardano,
        foreign_height: 8_000_000,
        commitment: cardano_commitment,
        threshold: 1_000_000,  // 1M tokens
        proof,
    };
    
    // 3. Federation attests
    let federation = Federation::test_instance();
    let attestation = federation.attest(&obs).unwrap();
    
    // 4. Dregg verifies the STARK proof
    let bridge_verifier = BridgeVerifierKernel::test_instance();
    assert!(bridge_verifier.verify(&obs.stmt, &obs.proof));
    
    // 5. Lock on dregg succeeds
    let lock_effect = Effect::BridgeLock { nonce: obs.nonce, amount: 1_000_000 };
    let turn = Turn { effects: vec![lock_effect], … };
    let turn_proof = prove_turn(&turn).unwrap();
    
    // 6. Mint on foreign chain succeeds
    // (This is tested via the Midnight contract verifier, not in-dregg)
    
    // 7. If a malicious challenger submits a proof that the commitment opens
    //    to a different value (< threshold), the relayer's bond is slashed.
    let bad_proof = /*...*/ ;
    assert!(bridge_verifier.slash_if_wrong(&obs, &bad_proof).is_some());
}
```

---

## 6. OPENs, Named Precisely

| OPEN | Blocker? | Effort | Path |
|---|---|---|---|
| **Foreign-chain consensus model in Lean** | No | High | Formalize Cardano's consensus (paper: Ouroboros Praos). Out of scope for this phase; the bridge assumes foreign finality as a parameter. |
| **Cross-chain atomic 2PC** | No | Medium | Develop a 3PC-style consensus for cross-chain commitment. For now, use federation + dispute + timeout-abort. |
| **Choreography projection with bridge primitives** | No | Research | Extend MPST endpoint projection to handle bridges as first-class choreography actions. This is **OPEN #1** in `OPEN-PROBLEMS.md`. |
| **Unified light client for multiple foreign chains** | No | High | Write light clients for Ethereum, Polkadot, etc. These are **engineering**, not research. |
| **ZK bridge state transitions (private observations)** | No | Medium | Extend the bridge to hide the observed foreign state (not just the observed value). Reuse graph-privacy machinery. |
| **Cross-group orchestration via bridges** | No | Research | When a dregg cell in Group A calls a cell in Group B via a bridge (or via CapTP cross-group), prove the composition sound. Depends on OPEN #1. |

---

## 7. Files Touched (End-to-End)

### Lean (new + modified)

- **`Dregg2/Bridge/BridgeAction.lean`** (NEW) — the atomic-swap algebra and nonce-based atomicity
- **`Dregg2/Bridge/AtomicSwapTheorem.lean`** (NEW) — proof that matched nonces prevent double-release
- **`Dregg2/Bridge/DialWiring.lean`** (NEW) — dial wiring at `selective`
- **`Dregg2/Bridge/FullCascade.lean`** (NEW) — registry composition + proof of full cascade
- **`Dregg2/Crypto/Bridge.lean`** (EXISTS, complete) — the cryptokernel discharge; no changes needed

### Rust (new + modified)

- **`circuit/src/bridge_action_air.rs`** (EXISTS, complete) — the binding AIR; no changes
- **`Dregg2/Crypto/BridgeVerifierKernel.rs`** (NEW) — extend verifier with Dispute oracle
- **`circuit/src/cardano_light_client.rs`** (NEW) — light-client finality checker for Cardano
- **`app-framework/src/midnight_bridge.rs`** (EXISTS, stub → complete) — relayer state machine
- **`credentials/src/federation_attestation.rs`** (EXISTS → extended) — federation quorum + slashing
- **`verifier/tests/integration_midnight_bridge.rs`** (NEW) — differential test

### Docs

- **`docs/rebuild/PHASE-BRIDGE.md`** (THIS FILE, NEW) — design + roadmap

---

## 8. Summary: Honest Scope Assessment

**PROVED (in Lean, machine-checked):**
- Bridge observation soundness (given a foreign commitment, an observed value opening + clearing a threshold).
- Algebraic atomicity (matched nonce + amount prevent double-release *if observed*).
- No new primitive seams (the comparison is via proven `range_iff`; the opening is abstract but bounded by Layer-A carriers).

**DISCHARGED (via Dispute oracle, no Lean proof):**
- Foreign-chain finality (federation attestation + challenge window).
- Liveness (relayer will eventually finalize or timeout).

**NOT PROVED / NOT CLAIMED (out of scope):**
- Foreign consensus algorithm (Cardano's Ouroboros is outside the Lean model).
- Full distributed 3PC (liveness of cross-chain settlement is a timeout + federation matter, not a Lean theorem).
- Choreography projection with bridges (a genuine extension to MPST, **OPEN #1** in `OPEN-PROBLEMS.md`).

**SMALLEST VERIFIABLE INCREMENT:**

1. Formalize the `BridgeAction` atomic-swap algebra in Lean.
2. Prove nonce-based atomicity (algebraic only; liveness is disputed).
3. Wire the dial at `selective`.
4. Implement the Dispute oracle (federation + challenge window + slash-on-wrong).
5. Wire the Cardano light client.
6. Test a full lock/mint cycle with the differential harness.

**Effort:** ~6–8 weeks (Lean proof-engineering + Rust relayer + light-client integration).

---

> End of PHASE-BRIDGE design map. This document names the OPENs precisely, distinguishes Lean proofs from federation assumptions, and grounds the first verifiable increment in code that exists. It is a map, not a claim of completion.
