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

use serde::{Deserialize, Serialize};
use wasm_bindgen::prelude::*;

use pyana_cell::revocation_channel::ChannelState;
use pyana_cell::{
    AuthRequired, CapabilityRef, Cell, CellId, Ledger, Note, NoteCommitment, Nullifier,
    NullifierSet, Permissions, RevocationChannel, RevocationChannelSet,
};
use pyana_intent::matcher::{
    HeldCapability, MatchResult, Sensitivity, match_intent, satisfies_spec,
};
use pyana_intent::{
    ActionPattern, CommitmentId, Constraint, Intent, IntentKind, MatchSpec, VerificationMode,
};
use pyana_turn::conditional::{ConditionalTurn, ProofCondition};
use pyana_turn::{
    Action, Authorization, BudgetGate, CallForest, CallTree, ComputronCosts, DelegationMode,
    Effect, TurnBuilder, TurnExecutor, TurnReceipt, TurnResult,
};

// ============================================================================
// Internal state types
// ============================================================================

/// An agent in the simulation: identity + wallet + held tokens.
#[derive(Clone, Debug)]
pub struct SimAgent {
    pub name: String,
    pub public_key: [u8; 32],
    pub private_key: [u8; 32],
    pub cell_id: CellId,
    pub held_tokens: Vec<HeldCapability>,
    pub commitment_id: CommitmentId,
    pub token_counter: u64,
}

/// A simulated federation node.
#[derive(Clone, Debug, Serialize)]
pub struct SimFedNode {
    pub id: usize,
    pub public_key: [u8; 32],
}

/// A simulated federation.
#[derive(Clone, Debug)]
pub struct SimFederation {
    pub name: String,
    pub nodes: Vec<SimFedNode>,
    pub height: u64,
    pub events: Vec<FedEvent>,
    pub finalized_roots: Vec<[u8; 32]>,
}

/// An event in the federation's block.
#[derive(Clone, Debug, Serialize)]
pub struct FedEvent {
    pub kind: String,
    pub data: Vec<u8>,
    pub height: u64,
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
    pub federations: Vec<SimFederation>,
    pub revocation_channels: RevocationChannelSet,
    pub conditionals: Vec<PendingConditional>,
    pub current_height: u64,
    pub current_timestamp: i64,
    pub receipts: Vec<TurnReceipt>,
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
            federations: Vec::new(),
            revocation_channels: RevocationChannelSet::new(),
            conditionals: Vec::new(),
            current_height: 0,
            current_timestamp: 1000,
            receipts: Vec::new(),
        }
    }

    /// Create an agent with a name, generating keys and a cell.
    pub fn create_agent(&mut self, name: &str, initial_balance: u64) -> usize {
        let idx = self.agents.len();

        // Derive deterministic keys from name for reproducibility.
        let mut hasher = blake3::Hasher::new_derive_key("pyana-wasm-agent-key");
        hasher.update(name.as_bytes());
        hasher.update(&(idx as u64).to_le_bytes());
        let key_hash = hasher.finalize();
        let private_key: [u8; 32] = *key_hash.as_bytes();

        // Derive public key (simplified: use blake3 of private key as stand-in).
        // In a real system this would be Ed25519 derivation.
        let public_key: [u8; 32] = *blake3::hash(&private_key).as_bytes();

        // Derive token domain.
        let token_id: [u8; 32] = *blake3::hash(b"pyana-wasm-default-domain").as_bytes();

        // Create the cell in the ledger.
        let cell = Cell::with_balance(public_key, token_id, initial_balance);
        let cell_id = cell.id;
        self.ledger.insert_cell(cell).unwrap();

        // Derive commitment ID for intent matching.
        let commitment_id = CommitmentId::derive(&private_key, "pyana-wasm-commitment");

        let agent = SimAgent {
            name: name.to_string(),
            public_key,
            private_key,
            cell_id,
            held_tokens: Vec::new(),
            commitment_id,
            token_counter: 0,
        };

        self.agent_names.insert(name.to_string(), idx);
        self.agents.push(agent);
        idx
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
    pub fn execute_turn_for_agent(
        &mut self,
        agent_idx: usize,
        effects: Vec<Effect>,
        fee: u64,
    ) -> TurnResult {
        let agent = &self.agents[agent_idx];
        let cell_id = agent.cell_id;

        // Get current nonce.
        let nonce = self
            .ledger
            .get(&cell_id)
            .map(|c| c.state.nonce)
            .unwrap_or(0);

        let mut builder = TurnBuilder::new(cell_id, nonce);
        builder.set_fee(fee);

        {
            let action = builder.action(cell_id, "execute");
            for effect in effects {
                action.effect(effect);
            }
        }

        let turn = builder.build();
        let result = self.executor.execute(&turn, &mut self.ledger);

        if let TurnResult::Committed { ref receipt, .. } = result {
            self.receipts.push(receipt.clone());
        }

        result
    }

    /// Create a note for an agent.
    pub fn create_note(&mut self, agent_idx: usize, value: u64, asset_type: u64) -> NoteCommitment {
        let agent = &self.agents[agent_idx];
        let mut fields = [0u64; 8];
        fields[0] = asset_type;
        fields[1] = value;
        let note = Note::with_randomness(agent.public_key, fields, agent.private_key);
        note.commitment()
    }

    /// Spend a note (reveal nullifier).
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
        let note = Note::with_randomness(agent.public_key, fields, agent.private_key);
        let nullifier = note.nullifier(&agent.private_key);
        self.nullifier_set
            .insert(nullifier)
            .map_err(|e| e.to_string())?;
        Ok(nullifier)
    }

    /// Create a federation for simulation.
    pub fn create_federation(&mut self, name: &str, num_nodes: usize) -> usize {
        let idx = self.federations.len();
        let mut nodes = Vec::with_capacity(num_nodes);
        for i in 0..num_nodes {
            let mut hasher = blake3::Hasher::new_derive_key("pyana-wasm-fed-node");
            hasher.update(name.as_bytes());
            hasher.update(&(i as u64).to_le_bytes());
            let pk = *hasher.finalize().as_bytes();
            nodes.push(SimFedNode {
                id: i,
                public_key: pk,
            });
        }

        self.federations.push(SimFederation {
            name: name.to_string(),
            nodes,
            height: 0,
            events: Vec::new(),
            finalized_roots: Vec::new(),
        });
        idx
    }

    /// Propose a block of events to a federation.
    pub fn propose_block(&mut self, fed_idx: usize, events_data: Vec<Vec<u8>>) -> [u8; 32] {
        let fed = &mut self.federations[fed_idx];
        fed.height += 1;
        let height = fed.height;

        for data in events_data {
            fed.events.push(FedEvent {
                kind: "user_event".to_string(),
                data,
                height,
            });
        }

        // Compute block hash.
        let mut hasher = blake3::Hasher::new_derive_key("pyana-wasm-block");
        hasher.update(fed.name.as_bytes());
        hasher.update(&height.to_le_bytes());
        for ev in &fed.events {
            hasher.update(&ev.data);
        }
        let block_hash = *hasher.finalize().as_bytes();
        fed.finalized_roots.push(block_hash);
        block_hash
    }

    /// Simulate a consensus round (all nodes "vote" and finalize).
    pub fn simulate_consensus_round(&mut self, fed_idx: usize) -> ConsensusRoundResult {
        let fed = &mut self.federations[fed_idx];
        fed.height += 1;
        let height = fed.height;

        let mut hasher = blake3::Hasher::new_derive_key("pyana-wasm-consensus");
        hasher.update(fed.name.as_bytes());
        hasher.update(&height.to_le_bytes());
        let root = *hasher.finalize().as_bytes();
        fed.finalized_roots.push(root);

        ConsensusRoundResult {
            height,
            root,
            votes: fed.nodes.len(),
            quorum_reached: true,
        }
    }

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
            .map(|c| c.state.nonce)
            .unwrap_or(0);

        let mut builder = TurnBuilder::new(cell_id, nonce);
        builder.set_fee(fee);
        {
            let action = builder.action(cell_id, "conditional");
            for effect in effects {
                action.effect(effect);
            }
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
}

/// Result of a consensus round simulation.
#[derive(Clone, Debug, Serialize)]
pub struct ConsensusRoundResult {
    pub height: u64,
    pub root: [u8; 32],
    pub votes: usize,
    pub quorum_reached: bool,
}
