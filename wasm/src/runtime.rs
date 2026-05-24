//! PyanaRuntime: full in-browser distributed system simulation.
//!
//! Encapsulates a complete pyana environment with:
//! - A Ledger (cells + Merkle state)
//! - A TurnExecutor
//! - A NullifierSet (note double-spend tracking)
//! - An IntentPool (simplified)
//! - A RevocationChannelSet
//! - Multiple AgentWallet instances (for multi-party simulation)
//! - Federation simulation (in-memory, no networking)

use std::collections::HashMap;

use serde::Serialize;
use zeroize::Zeroizing;

use pyana_cell::{
    AuthRequired, Cell, CellId, Ledger, Note, NoteCommitment, Nullifier, NullifierSet,
    PeerExchange, RevocationChannel, RevocationChannelSet,
};
use pyana_intent::matcher::{HeldCapability, MatchResult, Sensitivity, match_intent};
use pyana_intent::{
    ActionPattern, CommitmentId, Constraint, Intent, IntentKind, MatchSpec, VerificationMode,
};
use pyana_sdk::AgentWallet;
use pyana_turn::action::Authorization;
use pyana_turn::builder::ActionBuilder;
use pyana_turn::conditional::{ConditionalTurn, ProofCondition};
use pyana_turn::forest::CallTree;
use pyana_turn::{
    ComputronCosts, Effect, Turn, TurnBuilder, TurnExecutor, TurnReceipt, TurnResult,
};

/// Cell-ID domain shared by every wasm-sim agent. AgentWallet derives the
/// CellId deterministically as `f(public_key, domain)` so this string is part
/// of the agent's identity surface.
const WASM_SIM_DOMAIN: &str = "pyana-wasm-default-domain";

/// Fee charged on the system turn that mints a new cell from the genesis
/// agent. Must cover the computron cost of `Effect::CreateCell` (~850 with
/// default costs) plus the optional `Effect::Transfer` to fund the new cell
/// (~125 extra). 2000 leaves comfortable headroom and is debited from the
/// genesis agent's balance.
const GENESIS_MINT_FEE: u64 = 2000;

// ============================================================================
// Internal state types
// ============================================================================

/// An agent in the wasm runtime: a real `pyana_sdk::AgentWallet` plus the
/// auxiliary state we need for in-browser scenarios (cached cell_id, an
/// intent-matcher-shaped token list, a commitment id, a counter for token-id
/// generation, and a friendly name).
///
/// `held_tokens` here is the `pyana_intent::matcher::HeldCapability` shape
/// used by the intent matcher — distinct from `wallet.tokens()` which is
/// the SDK's macaroon-backed `HeldToken`. Both legitimately coexist.
pub struct SimAgent {
    pub name: String,
    pub wallet: AgentWallet,
    pub public_key: [u8; 32],
    pub cell_id: CellId,
    pub held_tokens: Vec<HeldCapability>,
    pub commitment_id: CommitmentId,
    pub token_counter: u64,
    /// Canonical `PeerExchange` session for this agent. Built once at agent
    /// creation via `AgentWallet::peer_exchange(WASM_SIM_DOMAIN)`, so the
    /// signing key used by the exchange is the wallet's real Ed25519 key —
    /// no JS-side or wasm-side reimplementation. Mutated by `register_peer`,
    /// `create_transition`, and `verify_transition`.
    pub peer_exchange: PeerExchange,
}

// Federation is now wired via the real `pyana_federation::Federation`.
//
// Previously the wasm runtime held a parallel `SimFederation` / `SimFedNode` /
// `FedEvent` set of types that didn't reflect canonical behavior. After the
// pyana-federation crate gained a `runtime` feature gate (which gates the
// tokio + crossbeam transport — the wasm-incompatible bit), the in-browser
// runtime constructs and drives the *real* `Federation` / `FederationNode`
// / `ConsensusOrchestrator` types via their sync API. The async TCP
// transport remains native-only and is not exposed here.
//
// Surface exposed to wasm: `create_federation`, `propose_block` (queue +
// run_consensus_round), `get_federation_state`, `simulate_consensus_round`.
// These delegate to the canonical types — no JS-side simulation lives here.

/// A named in-browser federation. The handle the JS UI uses to address a
/// federation is its index in `PyanaRuntime::federations`; the friendly name
/// is informational only (used by `<pyana-federation>` for display).
pub struct SimFederation {
    pub name: String,
    pub federation: pyana_federation::Federation,
    /// History of `propose_block` calls: one entry per call, each a list of
    /// token IDs that were *submitted* (not necessarily finalized — the
    /// `Federation::finalized_history` is the source of truth for what
    /// actually committed). Used by `<pyana-block>` so the inspector can
    /// surface input intent alongside the canonical `RevocationBlock`.
    pub submitted_token_ids: Vec<Vec<String>>,
}

/// A pending conditional turn.
#[derive(Clone, Debug)]
pub struct PendingConditional {
    pub id: [u8; 32],
    pub conditional: ConditionalTurn,
    pub submitted_height: u64,
}

/// Execution trace step (for step-by-step visualization).
#[derive(Clone, Debug, Serialize)]
pub struct TraceStep {
    pub action_path: Vec<usize>,
    pub target_cell: String,
    pub method: String,
    pub effects: Vec<String>,
    pub result: String,
    pub computrons_used: u64,
}

// ============================================================================
// PyanaRuntime: the core state container
// ============================================================================

/// The main runtime struct holding all simulation state.
/// NOT exposed directly via wasm_bindgen (we use an index-based handle instead).
pub struct PyanaRuntime {
    pub ledger: Ledger,
    pub executor: TurnExecutor,
    pub nullifier_set: NullifierSet,
    pub agents: Vec<SimAgent>,
    pub agent_names: HashMap<String, usize>,
    pub intents: Vec<Intent>,
    pub revocation_channels: RevocationChannelSet,
    pub conditionals: Vec<PendingConditional>,
    pub current_height: u64,
    pub current_timestamp: i64,
    pub receipts: Vec<TurnReceipt>,
    /// Real `pyana_federation::Federation` instances, addressed by index.
    /// The Studio's federation/block inspectors read through these — every
    /// hash, signature, and merkle root surfaced in the UI comes from the
    /// canonical types, not a JS-side simulation.
    pub federations: Vec<SimFederation>,
}

impl PyanaRuntime {
    pub fn new() -> Self {
        let costs = ComputronCosts::default_costs();
        let mut executor = TurnExecutor::new(costs);
        executor.set_timestamp(1000);
        executor.set_block_height(0);

        PyanaRuntime {
            ledger: Ledger::new(),
            executor,
            nullifier_set: NullifierSet::new(),
            agents: Vec::new(),
            agent_names: HashMap::new(),
            intents: Vec::new(),
            revocation_channels: RevocationChannelSet::new(),
            conditionals: Vec::new(),
            current_height: 0,
            current_timestamp: 1000,
            receipts: Vec::new(),
            federations: Vec::new(),
        }
    }

    /// Create a new federation with `num_nodes` nodes named `<name>-<idx>`.
    /// Delegates to `pyana_federation::Federation::new` — the nodes have real
    /// Ed25519 keypairs, a real Merkle revocation tree, and a real consensus
    /// state machine. Returns the new federation's index.
    pub fn create_federation(&mut self, name: &str, num_nodes: usize) -> usize {
        let node_names: Vec<String> = (0..num_nodes).map(|i| format!("{name}-{i}")).collect();
        let name_refs: Vec<&str> = node_names.iter().map(|s| s.as_str()).collect();
        let federation = pyana_federation::Federation::new(&name_refs);
        let idx = self.federations.len();
        self.federations.push(SimFederation {
            name: name.to_string(),
            federation,
            submitted_token_ids: Vec::new(),
        });
        idx
    }

    /// Submit a batch of revocation events from node 0 and immediately run a
    /// consensus round. Returns the finalized block hash and height; `None`
    /// if consensus didn't finalize (insufficient online nodes, divergence,
    /// etc.).
    ///
    /// Behavioral divergence from the deleted `SimFederation::propose_block`:
    /// the canonical `Federation::run_consensus_round` requires the leader's
    /// `pending_events` to be non-empty AND a quorum (n - floor(n/3)) of
    /// online nodes' votes — not any-N like the sim. With a single submission
    /// here (all events submitted to node 0 then drained to the leader), a
    /// freshly created federation of N >= 1 nodes will normally finalize on
    /// the first call.
    pub fn propose_block(&mut self, fed_index: usize, token_ids: Vec<String>) -> Option<[u8; 32]> {
        let fed = self.federations.get_mut(fed_index)?;
        // Submit each token-id revocation from node 0 (the initial leader).
        for tid in &token_ids {
            fed.federation.submit_revocation(0, tid);
        }
        fed.submitted_token_ids.push(token_ids);
        let (block, _qc) = fed.federation.run_consensus_round()?;
        Some(block.block_hash)
    }

    /// Run an additional consensus round (e.g. to flush any pending events
    /// submitted out-of-band). Returns the finalized block hash + height +
    /// view + event count, or `None` if the round didn't finalize.
    pub fn simulate_consensus_round(&mut self, fed_index: usize) -> Option<ConsensusRoundResult> {
        let fed = self.federations.get_mut(fed_index)?;
        let (block, qc) = fed.federation.run_consensus_round()?;
        Some(ConsensusRoundResult {
            block_hash: hex_encode_bytes(&block.block_hash),
            height: block.height,
            view: block.view,
            num_events: block.events.len(),
            proposer: block.proposer,
            qc_threshold: qc.threshold,
            qc_votes: qc.votes.len(),
        })
    }

    /// Create an agent with a name. The Ed25519 key is derived deterministically
    /// from (name, idx) so a reproducible browser session can replay an
    /// identical history. The derivation is BLAKE3-of-name-and-index for the
    /// seed; the rest of the agent — public key, cell id, signing — comes
    /// from `pyana_sdk::AgentWallet`, the same wallet used by native callers.
    /// This is not a sim-shaped reimplementation; the wallet IS the canonical
    /// implementation, just constructed with a deterministic seed for
    /// reproducibility.
    ///
    /// # Cell birth
    ///
    /// The **first** agent (idx 0) is the genesis agent: its cell is inserted
    /// directly into the ledger. This mirrors `pyana_node::genesis`'s
    /// `initial_cells` field — there must be at least one cell before any turn
    /// can run, because a turn is always issued by some existing cell.
    ///
    /// **Subsequent** agents are minted from genesis via a real turn that emits
    /// `Effect::CreateCell` (and, if `initial_balance > 0`, `Effect::Transfer`
    /// from genesis). The executor requires `CreateCell` to have `balance: 0`
    /// (see `turn::executor::Effect::CreateCell` arm), so we always pass 0 and
    /// fund the new cell with a follow-up Transfer effect within the same turn.
    pub fn create_agent(&mut self, name: &str, initial_balance: u64) -> usize {
        self.try_create_agent(name, initial_balance)
            .unwrap_or_else(|e| panic!("create_agent failed: {e}"))
    }

    /// Fallible cell-creation path. Same as [`create_agent`] but returns a
    /// String error rather than panicking, so wasm bindings can surface the
    /// error to JS rather than triggering an `unreachable` trap.
    pub fn try_create_agent(&mut self, name: &str, initial_balance: u64) -> Result<usize, String> {
        let idx = self.agents.len();

        // Deterministic Ed25519 seed.
        let mut hasher = blake3::Hasher::new_derive_key("pyana-wasm-agent-key");
        hasher.update(name.as_bytes());
        hasher.update(&(idx as u64).to_le_bytes());
        let key_hash = hasher.finalize();
        let seed_bytes: [u8; 32] = *key_hash.as_bytes();

        // CommitmentId derivation needs the raw seed; compute it before the
        // seed is moved into the wallet (where it's zeroized).
        let commitment_id = CommitmentId::derive(&seed_bytes, "pyana-wasm-commitment");

        let wallet = AgentWallet::from_key_bytes(Zeroizing::new(seed_bytes));
        let public_key = wallet.public_key().0;
        let cell_id = wallet.cell_id(WASM_SIM_DOMAIN);
        let token_id: [u8; 32] = *blake3::hash(WASM_SIM_DOMAIN.as_bytes()).as_bytes();

        if idx == 0 {
            // Genesis: insert the root cell directly. This is the same pattern
            // pyana-node uses (see node/src/genesis.rs::initial_cells).
            let cell = Cell::with_balance(public_key, token_id, initial_balance);
            self.ledger.insert_cell(cell).unwrap();
        } else {
            // Subsequent agents: mint the cell via a real turn issued by the
            // genesis agent (agent 0). This goes through the canonical
            // Effect::CreateCell + Effect::Transfer path.
            //
            // Register the SimAgent first so its CellId/wallet are visible to
            // the executor (the new cell must exist before Transfer targets
            // it — but `Effect::CreateCell` runs before `Effect::Transfer`
            // within the same action's effect list, so we're fine).
            let mut effects = vec![Effect::CreateCell {
                public_key,
                token_id,
                balance: 0,
            }];
            if initial_balance > 0 {
                effects.push(Effect::Transfer {
                    from: self.agents[0].cell_id,
                    to: cell_id,
                    amount: initial_balance,
                });
            }

            // Execute the turn signed by genesis. We must pay a fee large
            // enough to cover the turn's computrons: with default costs,
            // action_base(100) + signature_verify(200) + effect_base(50) +
            // create_cell(500) ≈ 850 for CreateCell alone, plus another
            // effect_base(50) + transfer(75) when funding. We round up to
            // GENESIS_MINT_FEE for headroom. The fee is debited from the
            // genesis cell's balance, which is why genesis should be seeded
            // with enough to cover all subsequent agent mints.
            match self.execute_turn_for_agent(0, effects, GENESIS_MINT_FEE) {
                TurnResult::Committed { .. } => {}
                other => {
                    return Err(format!(
                        "minting cell for '{name}' via Effect::CreateCell failed: {:?}",
                        other
                    ));
                }
            }
        }

        // Build the canonical `PeerExchange` for this agent using the wallet's
        // real Ed25519 signing key. `AgentWallet::peer_exchange(domain)` is
        // the SDK's factory — same code path the native API uses — so we do
        // not need a public signing-key accessor on the wallet.
        let peer_exchange = wallet.peer_exchange(WASM_SIM_DOMAIN);

        let agent = SimAgent {
            name: name.to_string(),
            wallet,
            public_key,
            cell_id,
            held_tokens: Vec::new(),
            commitment_id,
            token_counter: 0,
            peer_exchange,
        };

        self.agent_names.insert(name.to_string(), idx);
        self.agents.push(agent);
        Ok(idx)
    }

    /// Mint a cell from a raw public key (used by the wasm `create_cell` JS
    /// binding). Uses the same factory-turn mechanism as subsequent
    /// `create_agent` calls: a turn signed by the genesis agent that emits
    /// `Effect::CreateCell` + (optional) `Effect::Transfer`.
    ///
    /// Returns the new cell's `CellId`. Requires at least one prior agent
    /// (the genesis agent, idx 0) to exist as the signer.
    pub fn mint_cell_from_genesis(
        &mut self,
        owner_public_key: [u8; 32],
        initial_balance: u64,
    ) -> Result<CellId, String> {
        if self.agents.is_empty() {
            return Err(
                "wasm runtime: cannot mint cell — no genesis agent yet (call create_agent first)"
                    .to_string(),
            );
        }
        let token_id: [u8; 32] = *blake3::hash(WASM_SIM_DOMAIN.as_bytes()).as_bytes();
        let new_cell_id = CellId::derive_raw(&owner_public_key, &token_id);

        let mut effects = vec![Effect::CreateCell {
            public_key: owner_public_key,
            token_id,
            balance: 0,
        }];
        if initial_balance > 0 {
            effects.push(Effect::Transfer {
                from: self.agents[0].cell_id,
                to: new_cell_id,
                amount: initial_balance,
            });
        }

        match self.execute_turn_for_agent(0, effects, GENESIS_MINT_FEE) {
            TurnResult::Committed { .. } => Ok(new_cell_id),
            other => Err(format!(
                "wasm runtime: mint_cell_from_genesis failed: {:?}",
                other
            )),
        }
    }

    /// Mint a token for an agent (adds to their held_tokens for intent matching).
    pub fn agent_mint_token(
        &mut self,
        agent_idx: usize,
        resource: &str,
        actions: &[String],
        expiry: Option<u64>,
    ) -> usize {
        let agent = &mut self.agents[agent_idx];
        agent.token_counter += 1;
        let token_id = format!("tok_{}_{}", agent.name, agent.token_counter);

        let held = HeldCapability {
            token_id,
            actions: actions.to_vec(),
            resource: resource.to_string(),
            app_id: None,
            service: None,
            user_id: None,
            features: Vec::new(),
            oauth_provider: None,
            expiry,
            budget: None,
            sensitivity: Sensitivity::Normal,
        };

        let idx = agent.held_tokens.len();
        agent.held_tokens.push(held);
        idx
    }

    /// Grant a capability from one agent's cell to another agent's cell.
    pub fn grant_capability(
        &mut self,
        from_agent: usize,
        to_agent: usize,
        permissions: AuthRequired,
    ) -> Option<u32> {
        let from_cell_id = self.agents[from_agent].cell_id;
        let to_cell_id = self.agents[to_agent].cell_id;

        // Grant capability on the target cell (to_agent gets cap pointing to from_agent).
        let to_cell = self.ledger.get_mut(&to_cell_id)?;
        to_cell.capabilities.grant(from_cell_id, permissions)
    }

    /// Build and execute a turn using the TurnBuilder API.
    ///
    /// The legacy `TurnBuilder::action()` API stamps every action with
    /// `Authorization::Unchecked`, which gets rejected by cells with default
    /// (`Signature`-required) permissions. We post-process the built turn,
    /// walking the call forest and replacing every `Unchecked` authorization
    /// with a real Ed25519 signature from the agent's signing key. The
    /// TurnExecutor verifies these signatures against the cell's stored
    /// public key — the same code path real wallets exercise.
    pub fn execute_turn_for_agent(
        &mut self,
        agent_idx: usize,
        effects: Vec<Effect>,
        fee: u64,
    ) -> TurnResult {
        let cell_id = self.agents[agent_idx].cell_id;

        // Get current nonce.
        let nonce = self
            .ledger
            .get(&cell_id)
            .map(|c| c.state.nonce())
            .unwrap_or(0);

        let mut builder = TurnBuilder::new(cell_id, nonce);
        builder.set_fee(fee);

        {
            let mut ab = ActionBuilder::new_unchecked_for_tests(cell_id, "execute", cell_id);
            for effect in effects {
                ab = ab.effect(effect);
            }
            builder.add_action(ab.build());
        }

        let mut turn = builder.build();

        // Receipt chaining: every turn after the first from a given agent must
        // reference the previous turn's receipt hash. The executor tracks the
        // per-agent head; reuse it so callers don't have to.
        if turn.previous_receipt_hash.is_none() {
            if let Some(prev) = self.executor.get_last_receipt_hash(&cell_id) {
                turn.previous_receipt_hash = Some(prev);
            }
        }

        // Sign every Unchecked action with the agent's wallet — same code
        // path native callers exercise via `AgentWallet::sign_action`.
        let federation_id = self.executor.local_federation_id;
        let wallet = &self.agents[agent_idx].wallet;
        sign_call_forest(&mut turn, wallet, &federation_id);

        let result = self.executor.execute(&turn, &mut self.ledger);

        if let TurnResult::Committed { ref receipt, .. } = result {
            self.receipts.push(receipt.clone());
        }

        result
    }

    /// Create a note for an agent. Randomness derives deterministically from
    /// the wallet (so the same agent + same value yields the same commitment
    /// for reproducibility), via `AgentWallet::derive_symmetric_key` rather
    /// than exposing raw signing material.
    pub fn create_note(&mut self, agent_idx: usize, value: u64, asset_type: u64) -> NoteCommitment {
        let agent = &self.agents[agent_idx];
        let mut fields = [0u64; 8];
        fields[0] = asset_type;
        fields[1] = value;
        let randomness = agent
            .wallet
            .derive_symmetric_key("pyana-wasm-note-randomness");
        let note = Note::with_randomness(agent.public_key, fields, randomness);
        note.commitment()
    }

    /// Spend a note (reveal nullifier). Spending key derived from the wallet
    /// the same way `create_note` derives randomness — same deterministic
    /// key so the nullifier is reproducible.
    pub fn spend_note(
        &mut self,
        agent_idx: usize,
        value: u64,
        asset_type: u64,
    ) -> Result<Nullifier, String> {
        let agent = &self.agents[agent_idx];
        let mut fields = [0u64; 8];
        fields[0] = asset_type;
        fields[1] = value;
        let randomness = agent
            .wallet
            .derive_symmetric_key("pyana-wasm-note-randomness");
        let spending = agent
            .wallet
            .derive_symmetric_key("pyana-wasm-note-spending");
        let note = Note::with_randomness(agent.public_key, fields, randomness);
        let nullifier = note.nullifier(&spending);
        self.nullifier_set
            .insert(nullifier)
            .map_err(|e| e.to_string())?;
        Ok(nullifier)
    }

    // create_federation / propose_block / simulate_consensus_round are
    // defined above (alongside the federations field initializer) and
    // delegate to the real `pyana_federation::Federation` API.

    /// Create an intent.
    pub fn create_intent(
        &mut self,
        agent_idx: usize,
        kind: IntentKind,
        actions: Vec<ActionPattern>,
        constraints: Vec<Constraint>,
        resource_pattern: Option<String>,
        expiry: u64,
    ) -> [u8; 32] {
        let agent = &self.agents[agent_idx];
        let spec = MatchSpec {
            actions,
            constraints,
            min_budget: None,
            resource_pattern,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(kind, spec, agent.commitment_id, expiry, None);
        let id = intent.id;
        self.intents.push(intent);
        id
    }

    /// Match an intent against an agent's held tokens.
    pub fn match_intent_for_agent(&self, intent_idx: usize, agent_idx: usize) -> MatchResult {
        let intent = &self.intents[intent_idx];
        let agent = &self.agents[agent_idx];
        match_intent(
            intent,
            &agent.held_tokens,
            agent.commitment_id,
            VerificationMode::Trusted,
            self.current_timestamp as u64,
        )
    }

    /// Submit a conditional turn.
    pub fn submit_conditional(
        &mut self,
        agent_idx: usize,
        effects: Vec<Effect>,
        fee: u64,
        condition: ProofCondition,
        timeout_blocks: u64,
    ) -> [u8; 32] {
        let agent = &self.agents[agent_idx];
        let cell_id = agent.cell_id;
        let nonce = self
            .ledger
            .get(&cell_id)
            .map(|c| c.state.nonce())
            .unwrap_or(0);

        let mut builder = TurnBuilder::new(cell_id, nonce);
        builder.set_fee(fee);
        {
            let mut ab = ActionBuilder::new_unchecked_for_tests(cell_id, "conditional", cell_id);
            for effect in effects {
                ab = ab.effect(effect);
            }
            builder.add_action(ab.build());
        }
        let turn = builder.build();
        let turn_hash = turn.hash();

        let deposit_amount = pyana_turn::compute_conditional_deposit(
            self.current_height + timeout_blocks,
            self.current_height,
        );
        let conditional = ConditionalTurn {
            turn,
            condition,
            timeout_height: self.current_height + timeout_blocks,
            submitted_at: self.current_height,
            deposit_amount,
        };

        self.conditionals.push(PendingConditional {
            id: turn_hash,
            conditional,
            submitted_height: self.current_height,
        });

        turn_hash
    }

    /// Advance the block height (for timeout simulation).
    pub fn advance_height(&mut self, blocks: u64) {
        self.current_height += blocks;
        self.current_timestamp += (blocks * 12) as i64; // ~12s per block
        self.executor.set_block_height(self.current_height);
        self.executor.set_timestamp(self.current_timestamp);
    }

    /// Create a revocation channel.
    pub fn create_revocation_channel(&mut self, revoker_agent: usize) -> [u8; 32] {
        let revoker_cell_id = self.agents[revoker_agent].cell_id;
        let nonce = self.revocation_channels.len() as u64;
        let channel = RevocationChannel::new(revoker_cell_id, nonce, self.current_height);
        let channel_id = channel.channel_id;
        self.revocation_channels.register(channel).unwrap();
        channel_id
    }

    /// Trip (revoke) a channel.
    pub fn trip_channel(
        &mut self,
        channel_id: &[u8; 32],
        revoker_agent: usize,
        reason: [u8; 32],
    ) -> bool {
        let revoker_cell_id = self.agents[revoker_agent].cell_id;
        self.revocation_channels
            .trip_channel(channel_id, &revoker_cell_id, reason, self.current_height)
            .is_ok()
    }

    /// Check if a channel is active.
    pub fn is_channel_active(&self, channel_id: &[u8; 32]) -> bool {
        self.revocation_channels
            .get(channel_id)
            .map(|ch| ch.state.is_active())
            .unwrap_or(false)
    }

    // =========================================================================
    // PeerExchange (canonical sovereign-cell peer protocol)
    //
    // These methods are thin facades over `pyana_cell::PeerExchange` stored on
    // each `SimAgent`. The bindings layer doesn't reach into the agent's
    // `peer_exchange` field directly — it goes through these. All cryptography
    // and protocol logic lives inside the canonical `PeerExchange` type, no
    // reimplementation here.
    // =========================================================================

    /// Register a peer cell with an initial commitment from the agent's POV.
    /// Required before `verify_peer_transition` will accept transitions from
    /// that peer (canonical `PeerExchange::register_peer` semantics — the
    /// initial commitment is the "introduction" the two peers must agree on
    /// out-of-band).
    pub fn agent_register_peer(
        &mut self,
        agent_idx: usize,
        peer_cell_id: CellId,
        initial_commitment: [u8; 32],
    ) -> Result<(), String> {
        let agent = self
            .agents
            .get_mut(agent_idx)
            .ok_or_else(|| format!("invalid agent index: {agent_idx}"))?;
        agent
            .peer_exchange
            .register_peer(peer_cell_id, initial_commitment);
        Ok(())
    }

    /// Sign and package a state transition from this agent's exchange session.
    /// Returns the postcard-encoded `PeerStateTransition` bytes — the compact
    /// signed blob meant for the "Discord paste" UX. Mutates the agent's
    /// internal sequence counter.
    pub fn agent_create_peer_transition(
        &mut self,
        agent_idx: usize,
        old_commitment: [u8; 32],
        new_commitment: [u8; 32],
        effects_hash: [u8; 32],
    ) -> Result<Vec<u8>, String> {
        // PeerExchange's `create_transition` reads the system clock via
        // `SystemTime::now()`, which panics on wasm32-unknown-unknown. We
        // use the explicit-timestamp variant and feed it the runtime's
        // canonical clock (`current_timestamp`, in seconds — matching the
        // `i64` shape PeerExchange already uses).
        let ts = self.current_timestamp;
        let agent = self
            .agents
            .get_mut(agent_idx)
            .ok_or_else(|| format!("invalid agent index: {agent_idx}"))?;
        let transition = agent.peer_exchange.create_transition_at(
            old_commitment,
            new_commitment,
            effects_hash,
            ts,
        );
        postcard::to_stdvec(&transition)
            .map_err(|e| format!("failed to encode peer transition: {e}"))
    }

    /// Verify a transition from a peer (postcard-decoded inside). On success
    /// the agent's `peer_views` is updated to the new commitment + sequence
    /// and the updated view is returned. On failure returns the typed
    /// variant name (e.g. `"InvalidSignature"`) alongside the human-readable
    /// display so JS can switch on the variant for UX.
    pub fn agent_verify_peer_transition(
        &mut self,
        agent_idx: usize,
        transition_bytes: &[u8],
        peer_pubkey: [u8; 32],
    ) -> Result<pyana_cell::PeerCellView, (String, String)> {
        let agent = self.agents.get_mut(agent_idx).ok_or_else(|| {
            (
                "InvalidAgent".to_string(),
                format!("invalid agent index: {agent_idx}"),
            )
        })?;
        let transition: pyana_cell::PeerStateTransition = postcard::from_bytes(transition_bytes)
            .map_err(|e| {
                (
                    "DecodeError".to_string(),
                    format!("failed to decode peer transition: {e}"),
                )
            })?;
        let peer_cell_id = transition.cell_id;
        agent
            .peer_exchange
            .verify_transition(&transition, &peer_pubkey)
            .map_err(|e| (peer_exchange_error_variant(&e), e.to_string()))?;
        Ok(agent
            .peer_exchange
            .peer_view(&peer_cell_id)
            .cloned()
            .expect("verify_transition succeeded; view must exist"))
    }

    /// Get the agent's current view of a peer cell (commitment + sequence +
    /// last-updated). Returns `None` if not registered.
    pub fn agent_get_peer_view(
        &self,
        agent_idx: usize,
        peer_cell_id: CellId,
    ) -> Result<Option<pyana_cell::PeerCellView>, String> {
        let agent = self
            .agents
            .get(agent_idx)
            .ok_or_else(|| format!("invalid agent index: {agent_idx}"))?;
        Ok(agent.peer_exchange.peer_view(&peer_cell_id).cloned())
    }

    /// List all peer cell ids the agent has registered.
    pub fn agent_list_peers(&self, agent_idx: usize) -> Result<Vec<CellId>, String> {
        let agent = self
            .agents
            .get(agent_idx)
            .ok_or_else(|| format!("invalid agent index: {agent_idx}"))?;
        Ok(agent.peer_exchange.registered_peers().collect())
    }

    /// Get this agent's PeerExchange public key. Equivalent to the wallet's
    /// Ed25519 verifying key — sourced from the exchange so the binding is
    /// self-contained.
    pub fn agent_peer_pubkey(&self, agent_idx: usize) -> Result<[u8; 32], String> {
        let agent = self
            .agents
            .get(agent_idx)
            .ok_or_else(|| format!("invalid agent index: {agent_idx}"))?;
        Ok(agent.peer_exchange.public_key())
    }

    /// Read the current canonical state-commitment of a cell. Convenience
    /// for the peer-exchange flow: a sender needs the post-state commitment
    /// after running a turn, and the receiver needs an initial commitment
    /// to register the peer with. Goes through `Cell::state_commitment()`,
    /// the canonical sovereign-witness commitment function.
    pub fn cell_state_commitment(&self, cell_id: &CellId) -> Option<[u8; 32]> {
        self.ledger.get(cell_id).map(|c| c.state_commitment())
    }
}

/// Map a `PeerExchangeError` to its variant name (without payload), used by
/// the bindings to surface a typed error code to JS alongside the
/// human-readable message.
fn peer_exchange_error_variant(e: &pyana_cell::PeerExchangeError) -> String {
    use pyana_cell::PeerExchangeError as E;
    match e {
        E::InvalidSignature => "InvalidSignature",
        E::CommitmentMismatch { .. } => "CommitmentMismatch",
        E::SequenceGap { .. } => "SequenceGap",
        E::TimestampRegression => "TimestampRegression",
        E::UnknownPeer(_) => "UnknownPeer",
        E::InvalidTransitionProof(_) => "InvalidTransitionProof",
    }
    .to_string()
}

/// One-shot summary of a finalized consensus round, suitable for JS-side
/// rendering. The fields surface what's actually on the
/// `pyana_federation::RevocationBlock` + `QuorumCertificate` returned from
/// `Federation::run_consensus_round` — no inferred values.
#[derive(Clone, Debug, Serialize)]
pub struct ConsensusRoundResult {
    pub block_hash: String,
    pub height: u64,
    pub view: u64,
    pub num_events: usize,
    pub proposer: usize,
    pub qc_threshold: usize,
    pub qc_votes: usize,
}

/// Walk the turn's call forest and replace every `Authorization::Unchecked`
/// with a real Ed25519 signature via `AgentWallet::sign_action`. Existing
/// non-Unchecked authorizations are left intact so callers can pre-sign or
/// pre-prove specific actions. Uses the SDK's canonical signing path — no
/// hand-rolled cryptography.
fn sign_call_forest(turn: &mut Turn, wallet: &AgentWallet, federation_id: &[u8; 32]) {
    for tree in &mut turn.call_forest.roots {
        sign_call_tree(tree, wallet, federation_id);
    }
    // Mutating actions invalidates any cached forest hash; clear so the
    // executor recomputes from the now-signed actions.
    turn.call_forest.forest_hash = [0u8; 32];
}

fn sign_call_tree(tree: &mut CallTree, wallet: &AgentWallet, federation_id: &[u8; 32]) {
    if matches!(tree.action.authorization, Authorization::Unchecked) {
        // Clone the action because sign_action returns a fresh one; replace in place.
        tree.action = wallet.sign_action(tree.action.clone(), federation_id);
    }
    tree.hash = [0u8; 32]; // invalidate cached action hash
    for child in &mut tree.children {
        sign_call_tree(child, wallet, federation_id);
    }
}

/// Lowercase hex encode without pulling the `hex` crate (which isn't a
/// direct wasm dep). The bindings module has its own copy; this one is
/// internal to runtime so `ConsensusRoundResult` can hold a pre-encoded
/// hash string.
fn hex_encode_bytes(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        out.push(char::from_digit((b >> 4) as u32, 16).unwrap());
        out.push(char::from_digit((b & 0x0f) as u32, 16).unwrap());
    }
    out
}
