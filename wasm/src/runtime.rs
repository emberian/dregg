//! PyanaRuntime: full in-browser distributed system simulation.
//!
//! Encapsulates a complete pyana environment with:
//! - A Ledger (cells + Merkle state)
//! - A TurnExecutor
//! - A NullifierSet (note double-spend tracking)
//! - An IntentPool (simplified)
//! - A RevocationChannelSet
//! - Multiple AgentCipherclerk instances (for multi-party simulation)
//! - Federation simulation (in-memory, no networking)

use std::collections::HashMap;

use serde::Serialize;
use zeroize::Zeroizing;

use pyana_cell::CellMode;
use pyana_cell::factory::{FactoryCreationParams, FactoryDescriptor};
use pyana_cell::{
    AuthRequired, Cell, CellId, Ledger, Note, NoteCommitment, Nullifier, NullifierSet,
    PeerExchange, RevocationChannel, RevocationChannelSet,
};
use pyana_intent::matcher::{HeldCapability, MatchResult, Sensitivity, match_intent};
use pyana_intent::{
    ActionPattern, CommitmentId, Constraint, Intent, IntentKind, MatchSpec, VerificationMode,
};
use pyana_sdk::AgentCipherclerk;
use pyana_turn::action::Authorization;
use pyana_turn::builder::ActionBuilder;
use pyana_turn::conditional::{ConditionalTurn, ProofCondition};
use pyana_turn::forest::CallTree;
use pyana_turn::{
    ComputronCosts, Effect, Turn, TurnBuilder, TurnExecutor, TurnReceipt, TurnResult,
};

// Observability live feed (STARBRIDGE-03 Task #30). Emitter provides the
// canonical EventLog; we surface snapshots via the `events` field for
// wasm-bindgen + JS signal caching. No JS reimplementation per substrate rule.
use pyana_observability::{
    Emitter, EventBody, EventEnvelope, EventLog, TraceEvent, TurnLifecyclePayload,
};

/// Cell-ID domain shared by every wasm-sim agent. AgentCipherclerk derives the
/// CellId deterministically as `f(public_key, domain)` so this string is part
/// of the agent's identity surface.
const WASM_SIM_DOMAIN: &str = "pyana-wasm-default-domain";

/// Fee charged on the system turn that mints a new cell from the genesis
/// agent. Must cover the computron cost of `Effect::CreateCellFromFactory`
/// (~850 with default costs — same as `CreateCell`) plus the optional
/// `Effect::Transfer` to fund the new cell (~125 extra). 2000 leaves
/// comfortable headroom and is debited from the genesis agent's balance.
const GENESIS_MINT_FEE: u64 = 2000;

/// Derive-key tag for the default test-cipherclerk factory VK. The factory
/// is a constructor-transparency anchor — every wasm-runtime agent
/// (other than genesis) is born from this factory, so every cell's
/// provenance points at the same VK. The VK string is part of the
/// agent's identity surface; changing it changes the factory hash and
/// invalidates any test fixtures that pin the factory VK.
const WASM_DEFAULT_FACTORY_DOMAIN: &str = "pyana-wasm-default-test-cclerk-factory-v1";

/// Build the default "test cipherclerk" `FactoryDescriptor` used by
/// [`PyanaRuntime`] when an agent is created without an explicit factory.
///
/// The descriptor is intentionally permissive:
/// - `child_program_vk = None` and `child_vk_strategy = None` —
///   created cells have no installed program VK; the factory is a
///   pure agent-cell mint, not a program-deploying factory.
/// - `allowed_cap_templates = []` — created cells get no initial
///   capabilities (the runtime's `grant_capability` does that
///   separately, post-creation).
/// - `field_constraints = []` — the descriptor does not constrain
///   initial fields; the wasm runtime never sets initial fields.
/// - `state_constraints = []` — no perpetual slot caveats.
/// - `default_mode = Hosted` — matches the previous `Cell::new_hosted`
///   shape used by the pre-factory `Effect::CreateCell` path.
/// - `creation_budget = None` — unbounded mints (the wasm runtime is
///   a sim; the budget would just be a denial-of-service knob for
///   tests, not a useful invariant).
///
/// The `factory_vk` field is BLAKE3 derived from
/// [`WASM_DEFAULT_FACTORY_DOMAIN`], so it is deterministic and
/// reproducible across browser sessions. Apps that want their own
/// factory can deploy one via [`PyanaRuntime::deploy_factory`] and
/// pass its VK to [`PyanaRuntime::try_create_agent_with_factory`].
pub fn default_cipherclerk_factory_descriptor() -> FactoryDescriptor {
    let factory_vk: [u8; 32] = *blake3::Hasher::new_derive_key(WASM_DEFAULT_FACTORY_DOMAIN)
        .update(b"factory-vk")
        .finalize()
        .as_bytes();
    FactoryDescriptor {
        factory_vk,
        child_program_vk: None,
        child_vk_strategy: None,
        allowed_cap_templates: Vec::new(),
        field_constraints: Vec::new(),
        state_constraints: Vec::new(),
        default_mode: CellMode::Hosted,
        creation_budget: None,
    }
}

// ============================================================================
// Internal state types
// ============================================================================

/// An agent in the wasm runtime: a real `pyana_sdk::AgentCipherclerk` plus the
/// auxiliary state we need for in-browser scenarios (cached cell_id, an
/// intent-matcher-shaped token list, a commitment id, a counter for token-id
/// generation, and a friendly name).
///
/// `held_tokens` here is the `pyana_intent::matcher::HeldCapability` shape
/// used by the intent matcher — distinct from `cclerk.tokens()` which is
/// the SDK's macaroon-backed `HeldToken`. Both legitimately coexist.
pub struct SimAgent {
    pub name: String,
    pub cclerk: AgentCipherclerk,
    pub public_key: [u8; 32],
    pub cell_id: CellId,
    pub held_tokens: Vec<HeldCapability>,
    pub commitment_id: CommitmentId,
    pub token_counter: u64,
    /// Canonical `PeerExchange` session for this agent. Built once at agent
    /// creation via `AgentCipherclerk::peer_exchange(WASM_SIM_DOMAIN)`, so the
    /// signing key used by the exchange is the cipherclerk's real Ed25519 key —
    /// no JS-side or wasm-side reimplementation. Mutated by `register_peer`,
    /// `create_transition`, and `verify_transition`.
    pub peer_exchange: PeerExchange,
}

// Federation is wired via the canonical `pyana_federation::Federation`
// (attestation context, no simulator). The async TCP transport and the old
// Morpheus BFT simulator (`node.rs` / `transport.rs`) are native-only and
// have been deleted. The wasm runtime keeps a lightweight local consensus
// stub — a `HashSet` of revoked tokens + monotonically increasing height —
// that lets the Studio UI exercise `propose_block` / `simulate_consensus_round`
// without any wasm-incompatible I/O.
//
// Surface exposed to wasm: `create_federation`, `propose_block`,
// `simulate_consensus_round`. These build a real `AttestedRoot` via
// `Federation::build_attested_root` — the federation_id, threshold, and
// member keys are all canonical; only the BLS aggregate signature is elided
// (the wasm Studio does not run the BLS pipeline).

/// Summary of one finalized consensus round, stored in `SimFederation::finalized_blocks`.
/// Replaces the `(RevocationBlock, QuorumCertificate)` entries in the deleted
/// `node::Federation::finalized_history`. The fields match what `get_federation_block`
/// and `list_federation_blocks` expose to JS.
#[derive(Clone, Debug)]
pub struct FinalizedBlock {
    pub height: u64,
    pub view: u64,
    pub block_hash: [u8; 32],
    pub revoked_token_ids: Vec<String>,
    pub qc_votes: usize,
    pub qc_threshold: usize,
}

/// A named in-browser federation. The handle the JS UI uses to address a
/// federation is its index in `PyanaRuntime::federations`; the friendly name
/// is informational only (used by `<pyana-federation>` for display).
pub struct SimFederation {
    pub name: String,
    /// Canonical `pyana_federation::Federation` — owns the committee pubkeys,
    /// epoch, threshold, and derived federation_id. Every `AttestedRoot` built
    /// by this sim carries the federation's real id and threshold.
    pub federation: pyana_federation::Federation,
    /// Number of simulated nodes in this federation (committee size).
    pub node_count: usize,
    /// Revoked token ids accumulated since the last consensus round.
    pub pending_revocations: Vec<String>,
    /// All token ids ever revoked (for membership queries).
    pub revoked_set: std::collections::HashSet<String>,
    /// Monotonically increasing block height, bumped on each finalized round.
    pub height: u64,
    /// Monotonically increasing view number, bumped on each round attempt.
    pub view: u64,
    /// Ordered history of finalized rounds; replaces `node::Federation::finalized_history`.
    pub finalized_blocks: Vec<FinalizedBlock>,
    /// History of `propose_block` calls: one entry per call, each a list of
    /// token IDs that were *submitted*. Used by `<pyana-block>` so the
    /// inspector can surface input intent alongside the canonical
    /// `RevocationBlock`.
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

// Local hex32 for observability payloads (lowercase, no prefix; matches
// schema::hex32 contract). Placed here (free fn) so it is usable from
// execute_turn_for_agent without being an inherent method.
fn hex32(bytes: &[u8; 32]) -> String {
    let mut out = String::with_capacity(64);
    for b in bytes {
        out.push_str(&format!("{:02x}", b));
    }
    out
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
    /// Committed turns stored in parallel with `receipts` (index i in
    /// `turns` corresponds to index i in `receipts`). Stored so
    /// `get_receipt_chain` can surface per-action authorization details
    /// (Refactor 3 / Studio bindings enrichment).
    pub turns: Vec<Turn>,
    /// `pyana_federation::Federation` instances (attestation contexts), addressed
    /// by index. Each `SimFederation` pairs the canonical committee context with
    /// a lightweight local consensus stub — see `SimFederation` for details.
    pub federations: Vec<SimFederation>,
    /// VK of the default test-cipherclerk factory deployed at runtime
    /// construction. See [`default_cipherclerk_factory_descriptor`]. Subsequent
    /// agents (post-genesis) and cells minted from genesis are born via
    /// `Effect::CreateCellFromFactory` against this VK by default —
    /// closing the previous "genesis-by-fiat" gap (see
    /// `STUDIO-REFACTOR-PICKUP.md`).
    pub default_factory_vk: [u8; 32],

    /// pyana-observability Emitter (internal; drives seq + timestamps for trace events).
    emitter: Emitter,
    /// Snapshot of the event log (populated on turn lifecycle results for
    /// Committed/Rejected/Expired). Exposed to bindings for get_trace_events_json
    /// and JS <pyana-activity> live feed. Canonical Rust types only (substrate rule).
    pub events: EventLog,
}

impl PyanaRuntime {
    pub fn new() -> Self {
        let costs = ComputronCosts::default_costs();
        let mut executor = TurnExecutor::new(costs);
        executor.set_timestamp(1000);
        executor.set_block_height(0);

        // Deploy the default "test cipherclerk" factory so subsequent
        // `try_create_agent` calls can mint cells via the canonical
        // `Effect::CreateCellFromFactory` path. The factory's VK is
        // recorded here so the runtime can default to it when no
        // factory is specified by the caller — every cell minted by
        // the wasm runtime (other than genesis) carries a `Provenance`
        // record pointing at this VK, mirroring the
        // constructor-transparency behavior of the native node.
        let default_factory = default_cipherclerk_factory_descriptor();
        let default_factory_vk = executor.deploy_factory(default_factory);

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
            turns: Vec::new(),
            federations: Vec::new(),
            default_factory_vk,
            emitter: Emitter::new(),
            events: EventLog::new(),
        }
    }

    /// Deploy a factory descriptor into the runtime's executor. The
    /// returned VK can be passed to
    /// [`try_create_agent_with_factory`] /
    /// [`mint_cell_from_genesis_with_factory`] to mint cells from this
    /// factory. Exposed so apps (and tests) can register their own
    /// factories alongside the runtime's default test-cipherclerk factory.
    pub fn deploy_factory(&mut self, descriptor: FactoryDescriptor) -> [u8; 32] {
        self.executor.deploy_factory(descriptor)
    }

    /// The VK of the runtime's default "test cipherclerk" factory — the
    /// factory used by `create_agent` / `create_cell` when no explicit
    /// factory is named. Exposed so the bindings can surface it to JS
    /// (e.g. for `verifyProvenance` against the canonical wasm-runtime
    /// factory set).
    pub fn default_factory_vk(&self) -> [u8; 32] {
        self.default_factory_vk
    }

    /// Create a new federation with `num_nodes` nodes named `<name>-<idx>`.
    ///
    /// Builds a real `pyana_federation::Federation` committee: each node gets a
    /// deterministic Ed25519 keypair derived from its name. The federation_id,
    /// threshold (n − ⌊n/3⌋), and member pubkeys are all canonical. Returns
    /// the new federation's index.
    pub fn create_federation(&mut self, name: &str, num_nodes: usize) -> usize {
        use pyana_federation::{Federation, LocalSeat};
        use pyana_types::{PublicKey as FedPublicKey, SigningKey};

        let mut members: Vec<FedPublicKey> = Vec::with_capacity(num_nodes);
        let mut local_sk: Option<SigningKey> = None;

        for i in 0..num_nodes {
            // Deterministic seed: BLAKE3(name || "-" || i)
            let mut hasher = blake3::Hasher::new_derive_key("pyana-wasm-fed-node-key-v1");
            hasher.update(name.as_bytes());
            hasher.update(b"-");
            hasher.update(&(i as u64).to_le_bytes());
            let seed: [u8; 32] = *hasher.finalize().as_bytes();
            let sk = SigningKey::from_bytes(&seed);
            let pk = sk.public_key();
            if i == 0 {
                local_sk = Some(sk);
            }
            members.push(pk);
        }

        // BFT threshold: n − ⌊n/3⌋ (same formula as the deleted node.rs).
        let threshold = (num_nodes - num_nodes / 3) as u32;
        // `LocalSeat::bls_secret` is gated on `pyana-federation/runtime`; that
        // feature is unified-on across the workspace (e.g. `node/` enables
        // it), so the field is always present in any cargo invocation that
        // also builds pyana-wasm.
        let local_seat = local_sk.map(|sk| LocalSeat {
            index: 0,
            signing_key: sk,
            // bls_secret is only present when the federation crate's `runtime`
            // feature is enabled (native builds). The wasm crate disables that
            // feature; omit the field so the struct literal compiles either way.
        });
        let federation = Federation::from_committee(members, 0, threshold, None, local_seat);

        let idx = self.federations.len();
        self.federations.push(SimFederation {
            name: name.to_string(),
            federation,
            node_count: num_nodes,
            pending_revocations: Vec::new(),
            revoked_set: std::collections::HashSet::new(),
            height: 0,
            view: 0,
            finalized_blocks: Vec::new(),
            submitted_token_ids: Vec::new(),
        });
        idx
    }

    /// Submit a batch of revocation events and immediately run a consensus
    /// round. Returns the finalized block hash; `None` if there are no
    /// pending revocations to finalize.
    ///
    /// The block hash is BLAKE3(height || view || sorted token_ids) — a
    /// deterministic function of the committed state, not a network round-trip.
    /// The produced `AttestedRoot` (accessible via `get_federation_state`)
    /// carries the real `federation_id` and `threshold` from the canonical
    /// `Federation` committee.
    pub fn propose_block(&mut self, fed_index: usize, token_ids: Vec<String>) -> Option<[u8; 32]> {
        let fed = self.federations.get_mut(fed_index)?;
        if token_ids.is_empty() {
            return None;
        }
        for tid in &token_ids {
            fed.pending_revocations.push(tid.clone());
            fed.revoked_set.insert(tid.clone());
        }
        fed.submitted_token_ids.push(token_ids);
        fed.view += 1;
        fed.height += 1;

        // Block hash = BLAKE3(height || view || each pending token id in order).
        let mut hasher = blake3::Hasher::new_derive_key("pyana-wasm-consensus-block-v1");
        hasher.update(&fed.height.to_le_bytes());
        hasher.update(&fed.view.to_le_bytes());
        for tid in &fed.pending_revocations {
            hasher.update(tid.as_bytes());
        }
        let block_hash: [u8; 32] = *hasher.finalize().as_bytes();
        let qc_threshold = fed.federation.threshold() as usize;
        let qc_votes = fed.node_count;
        let revoked = std::mem::take(&mut fed.pending_revocations);
        fed.finalized_blocks.push(FinalizedBlock {
            height: fed.height,
            view: fed.view,
            block_hash,
            revoked_token_ids: revoked,
            qc_votes,
            qc_threshold,
        });
        Some(block_hash)
    }

    /// Run an additional consensus round (e.g. to flush any pending events
    /// submitted out-of-band). Returns the finalized block hash + height +
    /// view + event count, or `None` if there are no pending revocations.
    pub fn simulate_consensus_round(&mut self, fed_index: usize) -> Option<ConsensusRoundResult> {
        let fed = self.federations.get_mut(fed_index)?;
        if fed.pending_revocations.is_empty() {
            return None;
        }
        fed.view += 1;
        fed.height += 1;
        let num_events = fed.pending_revocations.len();

        let mut hasher = blake3::Hasher::new_derive_key("pyana-wasm-consensus-block-v1");
        hasher.update(&fed.height.to_le_bytes());
        hasher.update(&fed.view.to_le_bytes());
        for tid in &fed.pending_revocations {
            hasher.update(tid.as_bytes());
        }
        let block_hash: [u8; 32] = *hasher.finalize().as_bytes();
        let qc_threshold = fed.federation.threshold() as usize;
        // Simulated quorum: all nodes vote (wasm doesn't run BLS pipeline).
        let qc_votes = fed.node_count;
        let revoked = std::mem::take(&mut fed.pending_revocations);
        fed.finalized_blocks.push(FinalizedBlock {
            height: fed.height,
            view: fed.view,
            block_hash,
            revoked_token_ids: revoked,
            qc_votes,
            qc_threshold,
        });
        Some(ConsensusRoundResult {
            block_hash: hex_encode_bytes(&block_hash),
            height: fed.height,
            view: fed.view,
            num_events,
            proposer: 0,
            qc_threshold,
            qc_votes,
        })
    }

    /// Create an agent with a name. The Ed25519 key is derived deterministically
    /// from (name, idx) so a reproducible browser session can replay an
    /// identical history. The derivation is BLAKE3-of-name-and-index for the
    /// seed; the rest of the agent — public key, cell id, signing — comes
    /// from `pyana_sdk::AgentCipherclerk`, the same cipherclerk implementation used by native callers.
    /// This is not a sim-shaped reimplementation; the cipherclerk IS the canonical
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
    ///
    /// Uses the runtime's default test-cipherclerk factory. To mint from a
    /// specific factory descriptor (e.g. an app-deployed one), use
    /// [`Self::try_create_agent_with_factory`].
    pub fn try_create_agent(&mut self, name: &str, initial_balance: u64) -> Result<usize, String> {
        let factory_vk = self.default_factory_vk;
        self.try_create_agent_with_factory(name, initial_balance, &factory_vk)
    }

    /// Like [`try_create_agent`] but mints the new cell from an explicit
    /// `factory_vk`. The factory must have been deployed previously via
    /// [`Self::deploy_factory`].
    ///
    /// **Genesis (idx 0)** is still a cell birth-by-fiat: there is no
    /// signer yet, so the executor cannot accept a turn. Genesis is the
    /// canonical bootstrap; the factory binding only governs subsequent
    /// agents. Genesis's provenance is `Provenance::genesis` per
    /// `pyana_cell::factory`.
    ///
    /// **Subsequent agents** are minted via
    /// `Effect::CreateCellFromFactory` — the canonical constructor
    /// transparency path. The new cell's provenance points at the
    /// factory VK, so a downstream `verify_provenance` against the
    /// runtime's default factory set will return true.
    pub fn try_create_agent_with_factory(
        &mut self,
        name: &str,
        initial_balance: u64,
        factory_vk: &[u8; 32],
    ) -> Result<usize, String> {
        let idx = self.agents.len();

        // Deterministic Ed25519 seed.
        let mut hasher = blake3::Hasher::new_derive_key("pyana-wasm-agent-key");
        hasher.update(name.as_bytes());
        hasher.update(&(idx as u64).to_le_bytes());
        let key_hash = hasher.finalize();
        let seed_bytes: [u8; 32] = *key_hash.as_bytes();

        // CommitmentId derivation needs the raw seed; compute it before the
        // seed is moved into the cipherclerk (where it's zeroized).
        let commitment_id = CommitmentId::derive(&seed_bytes, "pyana-wasm-commitment");

        let cclerk = AgentCipherclerk::from_key_bytes(Zeroizing::new(seed_bytes));
        let public_key = cclerk.public_key().0;
        let cell_id = cclerk.cell_id(WASM_SIM_DOMAIN);
        let token_id: [u8; 32] = *blake3::hash(WASM_SIM_DOMAIN.as_bytes()).as_bytes();

        if idx == 0 {
            // Genesis: insert the root cell directly. This is the same pattern
            // pyana-node uses (see node/src/genesis.rs::initial_cells).
            // Genesis cannot itself be born from a factory because no signer
            // exists yet — this is the canonical "Provenance::genesis"
            // bootstrap point.
            let cell = Cell::with_balance(public_key, token_id, initial_balance);
            self.ledger.insert_cell(cell).unwrap();
        } else {
            // Subsequent agents: mint the cell via a real turn issued by the
            // genesis agent (agent 0), through the canonical
            // `Effect::CreateCellFromFactory` path. The factory descriptor's
            // `default_mode` determines whether the new cell is Hosted or
            // Sovereign; the runtime's default factory uses Hosted.
            //
            // We look up the factory's required mode from the registry so
            // the params match what `validate_creation` expects — passing
            // a mismatched mode would trip `FactoryError::ModeMismatch`.
            let factory_mode = self
                .executor
                .factory_registry
                .borrow()
                .get(factory_vk)
                .ok_or_else(|| {
                    format!(
                        "unknown factory VK {} — call deploy_factory first",
                        hex_encode_bytes(factory_vk)
                    )
                })?
                .default_mode
                .clone();

            let params = FactoryCreationParams {
                mode: factory_mode,
                program_vk: None,
                initial_fields: Vec::new(),
                initial_caps: Vec::new(),
                owner_pubkey: public_key,
            };

            let mut effects = vec![Effect::CreateCellFromFactory {
                factory_vk: *factory_vk,
                owner_pubkey: public_key,
                token_id,
                params,
            }];
            if initial_balance > 0 {
                effects.push(Effect::Transfer {
                    from: self.agents[0].cell_id,
                    to: cell_id,
                    amount: initial_balance,
                });
            }

            // Execute the turn signed by genesis. Fees match
            // `Effect::CreateCell` (the executor's cost table maps both
            // variants to `EFFECT_CREATE_CELL`), so `GENESIS_MINT_FEE`
            // covers either path.
            match self.execute_turn_for_agent(0, effects, GENESIS_MINT_FEE) {
                TurnResult::Committed { .. } => {}
                other => {
                    return Err(format!(
                        "minting cell for '{name}' via Effect::CreateCellFromFactory failed: {:?}",
                        other
                    ));
                }
            }
        }

        // Build the canonical `PeerExchange` for this agent using the cipherclerk's
        // real Ed25519 signing key. `AgentCipherclerk::peer_exchange(domain)` is
        // the SDK's factory — same code path the native API uses — so we do
        // not need a public signing-key accessor on the cipherclerk.
        let peer_exchange = cclerk.peer_exchange(WASM_SIM_DOMAIN);

        let agent = SimAgent {
            name: name.to_string(),
            cclerk,
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
    /// binding). Uses the canonical factory-turn path: a turn signed by the
    /// genesis agent that emits `Effect::CreateCellFromFactory` against the
    /// runtime's default test-cipherclerk factory (plus an optional
    /// `Effect::Transfer` to fund the new cell).
    ///
    /// Returns the new cell's `CellId`. Requires at least one prior agent
    /// (the genesis agent, idx 0) to exist as the signer.
    pub fn mint_cell_from_genesis(
        &mut self,
        owner_public_key: [u8; 32],
        initial_balance: u64,
    ) -> Result<CellId, String> {
        let factory_vk = self.default_factory_vk;
        self.mint_cell_from_genesis_with_factory(owner_public_key, initial_balance, &factory_vk)
    }

    /// Like [`Self::mint_cell_from_genesis`] but allows specifying an
    /// explicit factory VK (which must have been deployed via
    /// [`Self::deploy_factory`]).
    pub fn mint_cell_from_genesis_with_factory(
        &mut self,
        owner_public_key: [u8; 32],
        initial_balance: u64,
        factory_vk: &[u8; 32],
    ) -> Result<CellId, String> {
        if self.agents.is_empty() {
            return Err(
                "wasm runtime: cannot mint cell — no genesis agent yet (call create_agent first)"
                    .to_string(),
            );
        }
        let token_id: [u8; 32] = *blake3::hash(WASM_SIM_DOMAIN.as_bytes()).as_bytes();
        let new_cell_id = CellId::derive_raw(&owner_public_key, &token_id);

        let factory_mode = self
            .executor
            .factory_registry
            .borrow()
            .get(factory_vk)
            .ok_or_else(|| {
                format!(
                    "unknown factory VK {} — call deploy_factory first",
                    hex_encode_bytes(factory_vk)
                )
            })?
            .default_mode
            .clone();

        let params = FactoryCreationParams {
            mode: factory_mode,
            program_vk: None,
            initial_fields: Vec::new(),
            initial_caps: Vec::new(),
            owner_pubkey: owner_public_key,
        };

        let mut effects = vec![Effect::CreateCellFromFactory {
            factory_vk: *factory_vk,
            owner_pubkey: owner_public_key,
            token_id,
            params,
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
                "wasm runtime: mint_cell_from_genesis_with_factory failed: {:?}",
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
    /// public key — the same code path real cipherclerks exercise.
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

        // Sign every Unchecked action with the agent's cipherclerk — same code
        // path native callers exercise via `AgentCipherclerk::sign_action`.
        let federation_id = self.executor.local_federation_id;
        let cclerk = &self.agents[agent_idx].cclerk;
        sign_call_forest(&mut turn, cclerk, &federation_id);

        let result = self.executor.execute(&turn, &mut self.ledger);

        // Wire Emitter (STARBRIDGE §4.4 Task #30) into the three result paths
        // that the Studio <pyana-activity> live feed cares about. Other 6 event
        // kinds (Authorization etc) require deeper hooks into TurnExecutor/apply
        // (future work); here we at least anchor every turn with lifecycle.
        // All construction uses canonical pyana_observability types (substrate).
        {
            let (seq, ts) = self.emitter.next_envelope_seed();
            let mut env = EventEnvelope::new(seq, ts)
                .with_turn_hash(&turn.hash())
                .with_actor(&cell_id);
            match &result {
                TurnResult::Committed { receipt, .. } => {
                    self.receipts.push(receipt.clone());
                    self.turns.push(turn.clone());
                    let payload = TurnLifecyclePayload::Committed {
                        receipt_hash: hex32(&receipt.turn_hash),
                        forest_hash: hex32(&receipt.forest_hash),
                        pre_state_hash: hex32(&receipt.pre_state_hash),
                        post_state_hash: hex32(&receipt.post_state_hash),
                        effects_hash: hex32(&receipt.effects_hash),
                        timestamp: receipt.timestamp,
                        action_count: receipt.action_count,
                        computrons_used: receipt.computrons_used,
                        finality: format!("{:?}", receipt.finality),
                    };
                    self.emitter.emit(TraceEvent::TurnLifecycle(EventBody {
                        envelope: env.clone(),
                        payload,
                    }));
                }
                TurnResult::Rejected { reason, at_action } => {
                    let payload = TurnLifecyclePayload::Rejected {
                        reason: format!("{}", reason),
                        at_action: at_action.clone(),
                    };
                    self.emitter.emit(TraceEvent::TurnLifecycle(EventBody {
                        envelope: env.clone(),
                        payload,
                    }));
                }
                TurnResult::Expired => {
                    let payload = TurnLifecyclePayload::Expired;
                    self.emitter.emit(TraceEvent::TurnLifecycle(EventBody {
                        envelope: env.clone(),
                        payload,
                    }));
                }
                _ => { /* Pending: no lifecycle emit yet */ }
            }
            self.events = self.emitter.snapshot();
        }

        result
    }

    /// Create a note for an agent. Randomness derives deterministically from
    /// the cipherclerk (so the same agent + same value yields the same commitment
    /// for reproducibility), via `AgentCipherclerk::derive_symmetric_key` rather
    /// than exposing raw signing material.
    pub fn create_note(&mut self, agent_idx: usize, value: u64, asset_type: u64) -> NoteCommitment {
        let agent = &self.agents[agent_idx];
        let mut fields = [0u64; 8];
        fields[0] = asset_type;
        fields[1] = value;
        let randomness = agent
            .cclerk
            .derive_symmetric_key("pyana-wasm-note-randomness");
        let note = Note::with_randomness(agent.public_key, fields, randomness);
        note.commitment()
    }

    /// Spend a note (reveal nullifier). Spending key derived from the cipherclerk
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
            .cclerk
            .derive_symmetric_key("pyana-wasm-note-randomness");
        let spending = agent
            .cclerk
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

    /// Get this agent's PeerExchange public key. Equivalent to the cipherclerk's
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

    /// Export a minimal snapshot of runtime state (STARBRIDGE-FOLLOWUP-03
    /// progress on §5.9 / §5.10 / Q4).
    ///
    /// Returns a JSON string containing:
    /// - genesis metadata (factory_vk, current_height, timestamp base)
    /// - counts of receipts, turns, events, agents, federations
    /// - placeholder note for the canonical "WitnessedReceipt stream
    ///   (Vec<Turn> + genesis header)" format required for node ingest and
    ///   time-travel replay.
    ///
    /// This is a **stub surface** for the blocked snapshot format design.
    /// It uses only in-memory projections (no proving stack, no circuit
    /// changes). Full bidirectional (export + import that produces a
    /// live runtime at prior height) awaits the §8 Q4 resolution + §5.9
    /// format spec. The shape here is intentionally minimal so that
    /// extension/inspector code can start wiring against the future API
    /// without waiting for the human cargo session.
    ///
    /// Houyhnhnm note: must eventually be a protocol-level stream
    /// importable by real nodes (not sim-only).
    pub fn export_runtime_snapshot_stub(&self) -> String {
        #[derive(Serialize)]
        struct SnapshotStub {
            schema: String,
            exported_at: u64,
            current_height: u64,
            num_agents: usize,
            num_federations: usize,
            num_receipts: usize,
            num_turns: usize,
            num_events: usize,
            default_factory_vk_hex: String,
            note: String,
            // Future: witnessed_receipt_chain: Vec<...> or canonical bytes
        }

        let now = js_sys_now_secs() as u64;
        let stub = SnapshotStub {
            schema: "pyana-runtime-snapshot-v0-stub".to_string(),
            exported_at: now,
            current_height: self.current_height,
            num_agents: self.agents.len(),
            num_federations: self.federations.len(),
            num_receipts: self.receipts.len(),
            num_turns: self.turns.len(),
            num_events: self.events.events.len(),
            default_factory_vk_hex: hex_encode(&self.default_factory_vk),
            note: "PLACEHOLDER: full WitnessedReceipt stream format + import \
                   pending design resolution (§5.9 + §8 Q4 snapshot-and-replay). \
                   This stub is safe (no proving stack) and unblocks JS prep. \
                   See STARBRIDGE-PLAN §5.9/5.10 and SOVEREIGN-WITNESS etc for context. \
                   Time-travel cursor remains forward-only until format lands."
                .to_string(),
        };

        serde_json::to_string_pretty(&stub).unwrap_or_else(|_| "{}".to_string())
    }

    /// Stub for time-travel / rewind cursor on the InMemoryRuntime
    /// (STARBRIDGE-FOLLOWUP-03 on §5.10 + Q4).
    ///
    /// Currently returns Err with guidance. Recommended path once §5.9
    /// lands: snapshot at height N, destroy/recreate runtime from the
    /// snapshot bytes (canonical stream), then replay forward if needed.
    /// Alternative (Explorer-only) or N parallel runtimes are out of scope
    /// for the sim core.
    ///
    /// `caps.timeTravel` in JS surfaces should remain false until this
    /// is real. This stub provides the Rust surface + error contract
    /// for inspector code to target.
    ///
    /// Safe: pure control flow, no mutation on success path, no circuit.
    pub fn time_travel_to_stub(&mut self, target_height: u64) -> Result<(), String> {
        if target_height > self.current_height {
            return Err(format!(
                "time travel only supports rewind (target {target_height} > current {}); \
                 forward simulation only via advance_height + turns",
                self.current_height
            ));
        }
        if target_height == self.current_height {
            return Ok(()); // no-op
        }
        Err(format!(
            "time-travel rewind to {} requires the §5.9 snapshot format + \
             snapshot-and-replay (see plan §8 Q4 and Houyhnhnm persistence stream). \
             Current runtime is cumulative-only (advance_height). \
             Use export_runtime_snapshot_stub() for future compatibility. \
             (STARBRIDGE-FOLLOWUP-03 stub; no proving stack changes.)",
            target_height
        ))
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
/// with a real Ed25519 signature via `AgentCipherclerk::sign_action`. Existing
/// non-Unchecked authorizations are left intact so callers can pre-sign or
/// pre-prove specific actions. Uses the SDK's canonical signing path — no
/// hand-rolled cryptography.
fn sign_call_forest(turn: &mut Turn, cclerk: &AgentCipherclerk, federation_id: &[u8; 32]) {
    for tree in &mut turn.call_forest.roots {
        sign_call_tree(tree, cclerk, federation_id);
    }
    // Mutating actions invalidates any cached forest hash; clear so the
    // executor recomputes from the now-signed actions.
    turn.call_forest.forest_hash = [0u8; 32];
}

fn sign_call_tree(tree: &mut CallTree, cclerk: &AgentCipherclerk, federation_id: &[u8; 32]) {
    if matches!(tree.action.authorization, Authorization::Unchecked) {
        // Clone the action because sign_action returns a fresh one; replace in place.
        tree.action = cclerk.sign_action(tree.action.clone(), federation_id);
    }
    tree.hash = [0u8; 32]; // invalidate cached action hash
    for child in &mut tree.children {
        sign_call_tree(child, cclerk, federation_id);
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
