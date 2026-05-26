//! Multi-node simulation harness.
//!
//! Provides an in-process multi-node environment where federation nodes communicate
//! via direct function calls rather than real networking. This lets integration tests
//! exercise consensus, turn execution, and proof verification without any I/O.
//!
//! # Consensus engine
//!
//! `SimFederation` is now backed by `dregg_blocklace::finality::Blocklace` instances
//! (one per node) rather than the deleted `dregg_federation::node::Federation`
//! (Morpheus BFT simulator). The public API is unchanged; the internal simulation
//! follows the demo/sdk-consensus pattern: nodes propose blocks, gossip them to
//! online peers, and `tau` produces a total order.

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Arc;

use dregg_blocklace::finality::{Blocklace, Payload};
use dregg_captp::{DreggUri, FederationId as GroupId};
use dregg_cell::{AuthRequired, Ledger};
use dregg_federation::{
    Federation, FederationReceipt, FederationReceiptBody, KnownFederations, LocalSeat,
};
use dregg_turn::executor::{ComputronCosts, TurnExecutor};
use dregg_turn::{Turn, TurnReceipt, TurnResult};
use dregg_types::{AttestedRoot, CellId, PublicKey as FedPublicKey, SigningKey};
use ed25519_dalek::SigningKey as DalekSigningKey;

use crate::captp_sim::SimCapTpSession;

/// Simulated clock for deterministic time progression.
#[derive(Clone, Debug)]
pub struct SimClock {
    /// Current simulated timestamp (seconds since epoch).
    pub now: i64,
    /// Current simulated block height.
    pub block_height: u64,
}

impl SimClock {
    pub fn new() -> Self {
        Self {
            now: 1_700_000_000, // arbitrary start
            block_height: 0,
        }
    }

    /// Advance time by `seconds` and increment block height.
    pub fn advance(&mut self, seconds: i64) {
        self.now += seconds;
        self.block_height += 1;
    }

    /// Advance block height by N without changing wall-clock time.
    pub fn advance_blocks(&mut self, n: u64) {
        self.block_height += n;
    }
}

// =============================================================================
// SimNode: per-node state in the test harness
// =============================================================================

/// Per-node state: a local `finality::Blocklace` view + the set of tokens
/// this node considers revoked (updated after each finalized round).
struct SimNode {
    /// This node's Ed25519 signing key (used by the blocklace to author blocks).
    signing_key: DalekSigningKey,
    /// This node's public key as 32 bytes.
    pub_bytes: [u8; 32],
    /// Local finality blocklace view.
    blocklace: Blocklace,
    /// Revoked tokens applied to this node (updated after each consensus round).
    revoked: HashSet<String>,
    /// Pending revocations queued by `submit_revocation`; drained on
    /// `run_consensus_round`.
    pending: Vec<String>,
    /// Whether this node is currently online.
    pub is_online: bool,
    /// Last attested root (set after each finalized consensus round).
    pub attested_root: Option<AttestedRoot>,
    /// Current block height at this node.
    pub height: u64,
}

impl SimNode {
    fn new(seed: [u8; 32], quorum_threshold: usize) -> Self {
        let signing_key = DalekSigningKey::from_bytes(&seed);
        let pub_bytes = signing_key.verifying_key().to_bytes();
        let blocklace = Blocklace::new(signing_key.clone(), quorum_threshold);
        Self {
            signing_key,
            pub_bytes,
            blocklace,
            revoked: HashSet::new(),
            pending: Vec::new(),
            is_online: true,
            attested_root: None,
            height: 0,
        }
    }
}

// =============================================================================
// SimFederation
// =============================================================================

/// A simulated federation wrapping `dregg_blocklace::finality::Blocklace`
/// instances (one per node) + the canonical `dregg_federation::Federation`
/// attestation context.
pub struct SimFederation {
    /// Canonical committee context: committee pubkeys, epoch, threshold,
    /// federation_id. Used to build real `AttestedRoot` values.
    pub canonical: Federation,
    /// Per-node state (one entry per committee member).
    nodes: Vec<SimNode>,
    /// Name of this federation (informational).
    pub name: String,
    /// Current block height (bumped on each finalized round).
    height: u64,
    /// Union of all token ids ever revoked across all consensus rounds.
    /// Used by `recover_node` to replay history into the rejoining node.
    all_revoked: HashSet<String>,
}

impl SimFederation {
    /// Create a new simulated federation with `num_nodes` nodes.
    pub fn new(name: &str, num_nodes: usize) -> Self {
        // BFT threshold: n − ⌊n/3⌋ (Byzantine-fault-tolerant quorum).
        let threshold = (num_nodes - num_nodes / 3).max(1);

        let mut nodes: Vec<SimNode> = Vec::with_capacity(num_nodes);
        let mut members: Vec<FedPublicKey> = Vec::with_capacity(num_nodes);

        for i in 0..num_nodes {
            // Deterministic seed from (name, index).
            let mut hasher = blake3::Hasher::new_derive_key("dregg-teasting-sim-node-key-v1");
            hasher.update(name.as_bytes());
            hasher.update(b"-");
            hasher.update(&(i as u64).to_le_bytes());
            let seed: [u8; 32] = *hasher.finalize().as_bytes();
            let node = SimNode::new(seed, threshold);
            let pk = SigningKey::from_bytes(&seed).public_key();
            members.push(pk);
            nodes.push(node);
        }

        // Canonical federation: node 0 holds the local seat.
        // Re-derive node 0's seed to construct the LocalSeat signing key.
        let local_sk = {
            let mut hasher = blake3::Hasher::new_derive_key("dregg-teasting-sim-node-key-v1");
            hasher.update(name.as_bytes());
            hasher.update(b"-");
            hasher.update(&0u64.to_le_bytes());
            let seed: [u8; 32] = *hasher.finalize().as_bytes();
            SigningKey::from_bytes(&seed)
        };
        // `LocalSeat::bls_secret` is gated by `dregg_federation`'s `runtime`
        // feature. `dregg-teasting` depends on federation with default features
        // (which includes `runtime`), so we must include it.
        let local_seat = LocalSeat {
            index: 0,
            signing_key: local_sk,
            bls_secret: None,
        };
        let canonical =
            Federation::from_committee(members, 0, threshold as u32, None, Some(local_seat));

        Self {
            canonical,
            nodes,
            name: name.to_string(),
            height: 0,
            all_revoked: HashSet::new(),
        }
    }

    // =========================================================================
    // Consensus helpers
    // =========================================================================

    /// Submit a revocation for a token from `node_idx` (queued for the next
    /// consensus round).
    pub fn submit_revocation(&mut self, node_idx: usize, token_id: &str) {
        if node_idx < self.nodes.len() {
            self.nodes[node_idx].pending.push(token_id.to_string());
        }
    }

    /// Run one consensus round and return whether a block was finalized.
    ///
    /// Steps:
    /// 1. Each online node proposes a block carrying its pending revocations.
    /// 2. All proposed blocks are gossiped to all online peers.
    /// 3. Online nodes add enough Ack layers to complete a tau wave.
    /// 4. Ack blocks are gossiped after each layer.
    /// 5. `tau` ordering is computed on an online node's view.
    /// 6. If `tau` finalizes any blocks, their payloads are applied as
    ///    revocations to all online nodes and `attested_root` is updated.
    pub fn run_consensus_round(&mut self) -> bool {
        let num_nodes = self.nodes.len();
        let online_indices: Vec<usize> = (0..num_nodes)
            .filter(|&i| self.nodes[i].is_online)
            .collect();

        if online_indices.is_empty() {
            return false;
        }

        // Collect pending revocations and have each online node propose a block.
        let mut proposed: Vec<(usize, dregg_blocklace::finality::Block)> = Vec::new();
        for &i in &online_indices {
            let pending = std::mem::take(&mut self.nodes[i].pending);
            if !pending.is_empty() {
                let payload_bytes = pending.join("\n").into_bytes();
                let block = self.nodes[i]
                    .blocklace
                    .add_block(Payload::Data(payload_bytes));
                proposed.push((i, block));
            }
        }

        let has_existing_blocks = online_indices
            .iter()
            .any(|&i| !self.nodes[i].blocklace.is_empty());
        if proposed.is_empty() && !has_existing_blocks {
            return false;
        }

        // Gossip proposal blocks to all online peers.
        for (src, block) in &proposed {
            for &dst in &online_indices {
                if dst != *src {
                    let _ = self.nodes[dst].blocklace.receive_block(block.clone());
                }
            }
        }

        // Default tau uses wavelength=3. A data/proposal layer plus two ack
        // layers gives the wave-end blocks needed for super-ratification. If
        // this call is only advancing previously proposed data, the ack layers
        // still create the missing wave depth without duplicating payloads.
        for _ in 0..2 {
            let mut acks: Vec<(usize, dregg_blocklace::finality::Block)> = Vec::new();
            for &i in &online_indices {
                let ack = self.nodes[i].blocklace.add_block(Payload::Ack);
                acks.push((i, ack));
            }

            for (src, ack) in &acks {
                for &dst in &online_indices {
                    if dst != *src {
                        let _ = self.nodes[dst].blocklace.receive_block(ack.clone());
                    }
                }
            }
        }

        // Build the ordering blocklace from node 0's view and run `tau`.
        let leader_idx = online_indices[0];
        let participants: Vec<[u8; 32]> = self.nodes.iter().map(|node| node.pub_bytes).collect();

        let ordering_lace = build_ordering_blocklace(&self.nodes[leader_idx].blocklace);
        let finalized_ids = dregg_blocklace::ordering::tau(&ordering_lace, &participants);

        if finalized_ids.is_empty() {
            return false;
        }

        // Collect all revoked token ids from the finalized blocks' payloads.
        let mut round_revocations: Vec<String> = Vec::new();
        for bid in &finalized_ids {
            // Map ordering BlockId back to a finality block via the id map built
            // during `build_ordering_blocklace`. For simplicity we re-traverse
            // the finality lace directly.
            if let Some(b) = ordering_lace.get(bid) {
                if let Some(token_ids) = parse_data_payload(&b.payload) {
                    round_revocations.extend(token_ids);
                }
            }
        }

        self.height += 1;
        // Record all revocations in the federation-wide union set (for crash recovery replay).
        for tid in &round_revocations {
            self.all_revoked.insert(tid.clone());
        }
        let merkle_root = compute_revocation_root(&round_revocations);

        // Apply revocations to all online nodes.
        for &i in &online_indices {
            for tid in &round_revocations {
                self.nodes[i].revoked.insert(tid.clone());
            }
            self.nodes[i].height = self.height;
            // Build and store the attested root for this node.
            let block_id = finalized_ids.last().copied().unwrap_or([0u8; 32]);
            let attested = self.canonical.build_attested_root(
                merkle_root,
                None,
                None,
                self.height,
                1_700_000_000,
                block_id,
                self.height,
            );
            self.nodes[i].attested_root = Some(attested);
        }

        true
    }

    /// Check that all online nodes agree on the same revocation set.
    pub fn roots_agree(&mut self) -> bool {
        let online: Vec<&SimNode> = self.nodes.iter().filter(|n| n.is_online).collect();
        if online.is_empty() {
            return true;
        }
        let first = &online[0].revoked;
        online.iter().all(|n| &n.revoked == first)
    }

    /// Get the attested root from a specific node (if finalized).
    pub fn attested_root(&self, node_idx: usize) -> Option<&AttestedRoot> {
        self.nodes.get(node_idx)?.attested_root.as_ref()
    }

    /// Check whether a token is revoked according to a specific node.
    pub fn is_revoked(&self, node_idx: usize, token_id: &str) -> bool {
        self.nodes
            .get(node_idx)
            .map(|n| n.revoked.contains(token_id))
            .unwrap_or(false)
    }

    /// Crash a node (take offline).
    pub fn crash_node(&mut self, node_idx: usize) {
        if let Some(n) = self.nodes.get_mut(node_idx) {
            n.is_online = false;
        }
    }

    /// Recover a crashed node and replay all previously finalized revocations
    /// so the node's local state catches up to the current federation state.
    pub fn recover_node(&mut self, node_idx: usize) {
        if let Some(n) = self.nodes.get_mut(node_idx) {
            n.is_online = true;
            // Replay the full history of revocations that this node missed.
            for tid in &self.all_revoked {
                n.revoked.insert(tid.clone());
            }
            n.height = self.height;
        }
    }

    /// Number of online nodes.
    pub fn online_count(&self) -> usize {
        self.nodes.iter().filter(|n| n.is_online).count()
    }

    /// Total number of nodes.
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Return all node signing keys sorted to match the canonical member order.
    ///
    /// `Federation::from_committee` sorts members lexicographically; the
    /// per-node signing keys are originally inserted in node-index order.
    /// This method pairs each node's private key with its corresponding
    /// public key and re-orders by the canonical sorted pubkey order, so the
    /// returned `(sk, pk)` pairs are in 1-to-1 correspondence with
    /// `canonical.members()`.
    ///
    /// Used by `SimulationHarness::lift_turn_receipt` to collect
    /// threshold-many correctly-attributed vote signatures.
    pub fn all_signing_keys_canonical_order(&self) -> Vec<SigningKey> {
        // Build (pubkey_bytes, signing_key) pairs in node-index order.
        let mut pairs: Vec<([u8; 32], SigningKey)> = self
            .nodes
            .iter()
            .map(|n| {
                let sk = SigningKey::from_bytes(&n.signing_key.to_bytes());
                let pk = sk.public_key();
                (pk.0, sk)
            })
            .collect();
        // Sort by pubkey bytes — same order as Federation::from_committee sorts.
        pairs.sort_by(|(a, _), (b, _)| a.cmp(b));
        pairs.into_iter().map(|(_, sk)| sk).collect()
    }
}

// =============================================================================
// Helpers for ordering blocklace construction (mirrors demo/sdk-consensus)
// =============================================================================

/// Build an `ordering::Blocklace` from a `finality::Blocklace` view.
///
/// Mirrors `demo/sdk-consensus::build_ordering_blocklace` — the production seam
/// between the signed, equivocation-aware finality DAG and the simple ordering
/// DAG that `tau` consumes.
fn build_ordering_blocklace(finality_lace: &Blocklace) -> dregg_blocklace::Blocklace {
    let mut ordering_lace = dregg_blocklace::Blocklace::new();
    let mut f2o: HashMap<dregg_blocklace::finality::BlockId, dregg_blocklace::BlockId> =
        HashMap::new();

    // BFS from tips to collect all reachable finality blocks.
    let mut all: Vec<(
        dregg_blocklace::finality::BlockId,
        dregg_blocklace::finality::Block,
    )> = Vec::new();
    let mut frontier: Vec<dregg_blocklace::finality::BlockId> =
        finality_lace.tips().values().copied().collect();
    let mut seen = HashSet::new();

    while let Some(id) = frontier.pop() {
        if !seen.insert(id) {
            continue;
        }
        if let Some(b) = finality_lace.get(&id) {
            for p in &b.predecessors {
                frontier.push(*p);
            }
            all.push((id, b.clone()));
        }
    }

    let all_ids: HashSet<_> = all.iter().map(|(id, _)| *id).collect();
    all.sort_by(|(aid, a), (bid, b)| {
        a.seq
            .cmp(&b.seq)
            .then_with(|| a.creator.cmp(&b.creator))
            .then_with(|| aid.cmp(bid))
    });
    let mut pending: VecDeque<_> = all.into();

    while let Some((fid, block)) = pending.pop_front() {
        debug_assert!(
            block.predecessors.iter().all(|p| all_ids.contains(p)),
            "collected finality block is missing a predecessor from the reachable closure"
        );
        let ready = block.predecessors.iter().all(|p| f2o.contains_key(p));
        if !ready {
            pending.push_back((fid, block));
            if pending.iter().all(|(_, b)| {
                b.predecessors
                    .iter()
                    .any(|p| all_ids.contains(p) && !f2o.contains_key(p))
            }) {
                debug_assert!(
                    false,
                    "finality blocklace contains a predecessor cycle or missing closure"
                );
                break;
            }
            continue;
        }

        let predecessors: Vec<dregg_blocklace::BlockId> = block
            .predecessors
            .iter()
            .filter_map(|p| f2o.get(p).copied())
            .collect();
        let payload = match &block.payload {
            Payload::Data(data) => data.clone(),
            Payload::Ack => vec![],
            _ => vec![],
        };
        let ordering_block =
            dregg_blocklace::Block::new(block.creator, block.seq, predecessors, payload);
        let oid = ordering_block.id();
        let _ = ordering_lace.insert(ordering_block);
        f2o.insert(fid, oid);
    }

    ordering_lace
}

/// Parse a `Data` payload as a newline-separated list of token ids.
fn parse_data_payload(payload: &[u8]) -> Option<Vec<String>> {
    if payload.is_empty() {
        return None;
    }
    let s = std::str::from_utf8(payload).ok()?;
    let ids: Vec<String> = s
        .split('\n')
        .filter(|t| !t.is_empty())
        .map(|t| t.to_string())
        .collect();
    if ids.is_empty() { None } else { Some(ids) }
}

/// Derive a deterministic Merkle-like root from a list of revoked token ids.
/// Uses BLAKE3 chaining — sufficient for test-harness consistency checks.
fn compute_revocation_root(token_ids: &[String]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-teasting-revocation-root-v1");
    for tid in token_ids {
        hasher.update(tid.as_bytes());
        hasher.update(b"\0");
    }
    *hasher.finalize().as_bytes()
}

// =============================================================================
// SimulationHarness
// =============================================================================

/// The top-level simulation harness.
pub struct SimulationHarness {
    /// All federations in this simulation.
    pub federations: Vec<SimFederation>,
    /// Shared simulated clock.
    pub clock: SimClock,
    /// Turn executor for applying turns to ledgers.
    pub executor: TurnExecutor,
    /// Shared ledger for turn execution.
    pub ledger: Ledger,
    /// Active CapTP sessions between federations.
    /// Key is (smaller_idx, larger_idx) to avoid duplicate pairs.
    pub captp_sessions: HashMap<(usize, usize), SimCapTpSession>,
    /// Federation IDs for each federation (derived deterministically from name).
    pub federation_ids: Vec<GroupId>,
    /// Cross-federation peer registry for Seam 6 receipt-lift verification.
    ///
    /// `known_federations[i]` holds the federation registry *as seen by
    /// federation `i`*. A federation knows about itself (own entry) plus any
    /// peers that were explicitly registered via
    /// [`SimulationHarness::register_peer_federation`].
    pub known_federations: Vec<KnownFederations>,
}

impl SimulationHarness {
    /// Derive a deterministic GroupId from a federation name.
    fn derive_federation_id(name: &str) -> GroupId {
        let hash = blake3::derive_key("dregg-teasting-federation-id-v1", name.as_bytes());
        GroupId(hash)
    }

    /// Create a harness with a single federation of N nodes.
    pub fn new_federation(num_nodes: usize) -> Self {
        let fed = SimFederation::new("fed-alpha", num_nodes);
        let fed_id = Self::derive_federation_id("fed-alpha");
        // Build the own-federation entry so receipt verification works.
        let mut kf = KnownFederations::new();
        kf.register(Arc::new(fed.canonical.clone()));
        Self {
            federations: vec![fed],
            clock: SimClock::new(),
            executor: TurnExecutor::new(ComputronCosts::default_costs()),
            ledger: Ledger::new(),
            captp_sessions: HashMap::new(),
            federation_ids: vec![fed_id],
            known_federations: vec![kf],
        }
    }

    /// Create a harness with two federations for cross-federation testing.
    pub fn two_federations(nodes_a: usize, nodes_b: usize) -> Self {
        let fed_a = SimFederation::new("fed-alpha", nodes_a);
        let fed_b = SimFederation::new("fed-beta", nodes_b);
        let id_a = Self::derive_federation_id("fed-alpha");
        let id_b = Self::derive_federation_id("fed-beta");
        // Each federation's KnownFederations starts with its own entry only.
        let mut kf_a = KnownFederations::new();
        kf_a.register(Arc::new(fed_a.canonical.clone()));
        let mut kf_b = KnownFederations::new();
        kf_b.register(Arc::new(fed_b.canonical.clone()));
        Self {
            federations: vec![fed_a, fed_b],
            clock: SimClock::new(),
            executor: TurnExecutor::new(ComputronCosts::default_costs()),
            ledger: Ledger::new(),
            captp_sessions: HashMap::new(),
            federation_ids: vec![id_a, id_b],
            known_federations: vec![kf_a, kf_b],
        }
    }

    /// Advance the clock by N blocks (each block = 6 seconds).
    pub fn advance_blocks(&mut self, n: u64) {
        for _ in 0..n {
            self.clock.advance(6);
        }
    }

    /// Submit a turn and execute it against the shared ledger.
    pub fn submit_turn(&mut self, turn: &Turn) -> TurnResult {
        self.executor.set_timestamp(self.clock.now);
        self.executor.set_block_height(self.clock.block_height);
        self.executor.execute(turn, &mut self.ledger)
    }

    /// Run a consensus round on a specific federation.
    pub fn run_consensus_round(&mut self, fed_idx: usize) -> bool {
        self.federations[fed_idx].run_consensus_round()
    }

    /// Assert that all nodes in a federation agree on state.
    pub fn assert_all_nodes_agree(&mut self, fed_idx: usize) {
        assert!(
            self.federations[fed_idx].roots_agree(),
            "Federation '{}' nodes disagree on state root",
            self.federations[fed_idx].name
        );
    }

    /// Get a mutable reference to a specific federation.
    pub fn federation_mut(&mut self, idx: usize) -> &mut SimFederation {
        &mut self.federations[idx]
    }

    /// Get an immutable reference to a specific federation.
    pub fn federation(&self, idx: usize) -> &SimFederation {
        &self.federations[idx]
    }

    // =========================================================================
    // Cross-federation CapTP helpers
    // =========================================================================

    /// Connect two federations via a simulated CapTP session.
    ///
    /// Establishes a bilateral session and delivers the initial CapHello messages.
    /// Returns a mutable reference to the new session.
    ///
    /// Panics if a session already exists between these two federations.
    pub fn connect_federations(&mut self, a_idx: usize, b_idx: usize) -> &mut SimCapTpSession {
        assert_ne!(a_idx, b_idx, "cannot connect a federation to itself");
        let key = if a_idx < b_idx {
            (a_idx, b_idx)
        } else {
            (b_idx, a_idx)
        };

        assert!(
            !self.captp_sessions.contains_key(&key),
            "session already exists between federations {} and {}",
            a_idx,
            b_idx,
        );

        let fed_a_id = self.federation_ids[a_idx];
        let fed_b_id = self.federation_ids[b_idx];

        let mut session = SimCapTpSession::establish(fed_a_id, fed_b_id);
        session.current_height = self.clock.block_height;
        session.deliver_pending();

        self.captp_sessions.insert(key, session);
        self.captp_sessions.get_mut(&key).unwrap()
    }

    /// Get a mutable reference to the CapTP session between two federations.
    ///
    /// Returns `None` if no session exists between them.
    pub fn session_mut(&mut self, a_idx: usize, b_idx: usize) -> Option<&mut SimCapTpSession> {
        let key = if a_idx < b_idx {
            (a_idx, b_idx)
        } else {
            (b_idx, a_idx)
        };
        self.captp_sessions.get_mut(&key)
    }

    /// Get an immutable reference to the CapTP session between two federations.
    pub fn session(&self, a_idx: usize, b_idx: usize) -> Option<&SimCapTpSession> {
        let key = if a_idx < b_idx {
            (a_idx, b_idx)
        } else {
            (b_idx, a_idx)
        };
        self.captp_sessions.get(&key)
    }

    /// Export a cell from one federation as a sturdy ref.
    ///
    /// The federation must have a CapTP session with at least one other federation.
    /// The returned URI can be shared with any other federation.
    pub fn export_sturdy(
        &mut self,
        fed_idx: usize,
        cell_id: CellId,
        target_fed_idx: usize,
    ) -> DreggUri {
        let key = if fed_idx < target_fed_idx {
            (fed_idx, target_fed_idx)
        } else {
            (target_fed_idx, fed_idx)
        };

        let session = self
            .captp_sessions
            .get_mut(&key)
            .expect("no session between these federations");

        // Determine which side is exporting
        let fed_id = self.federation_ids[fed_idx];
        if session.fed_a_id == fed_id {
            session.export_from_a(cell_id, AuthRequired::Signature)
        } else {
            session.export_from_b(cell_id, AuthRequired::Signature)
        }
    }

    /// Enliven a sturdy ref from another federation.
    ///
    /// The caller must have a CapTP session with the federation that exported the URI.
    /// Returns the local CellId handle for the enlivened capability.
    pub fn enliven_sturdy(
        &mut self,
        fed_idx: usize,
        uri: &DreggUri,
        source_fed_idx: usize,
    ) -> Result<CellId, String> {
        let key = if fed_idx < source_fed_idx {
            (fed_idx, source_fed_idx)
        } else {
            (source_fed_idx, fed_idx)
        };

        let session = self
            .captp_sessions
            .get_mut(&key)
            .expect("no session between these federations");

        // The source federation is the one that exported the URI,
        // so we enliven "at" the source.
        let source_id = self.federation_ids[source_fed_idx];
        if session.fed_a_id == source_id {
            session.enliven_at_a(uri)
        } else {
            session.enliven_at_b(uri)
        }
    }

    /// Disconnect two federations (simulate network partition).
    pub fn disconnect_federations(&mut self, a_idx: usize, b_idx: usize) {
        let key = if a_idx < b_idx {
            (a_idx, b_idx)
        } else {
            (b_idx, a_idx)
        };
        if let Some(session) = self.captp_sessions.get_mut(&key) {
            session.disconnect();
        }
    }

    /// Get the GroupId for a federation by index.
    pub fn federation_id(&self, idx: usize) -> GroupId {
        self.federation_ids[idx]
    }

    /// Add a new federation to the harness (for multi-federation scenarios).
    pub fn add_federation(&mut self, name: &str, num_nodes: usize) -> usize {
        let idx = self.federations.len();
        let fed = SimFederation::new(name, num_nodes);
        let mut kf = KnownFederations::new();
        kf.register(Arc::new(fed.canonical.clone()));
        self.federations.push(fed);
        self.federation_ids.push(Self::derive_federation_id(name));
        self.known_federations.push(kf);
        idx
    }

    // =========================================================================
    // Seam 6 — Receipt-lift and cross-federation verification helpers
    // =========================================================================

    /// Lift a `TurnReceipt` produced by this harness's executor into a
    /// `FederationReceipt` signed by the given federation's committee seat.
    ///
    /// This is the "Turn → Federation" seam (Seam 6 from
    /// `AUDIT-protocol-composition.md`): after the executor commits a turn, the
    /// federation runs a (simulated) quorum sign and produces a typed receipt
    /// that downstream federations can verify without re-executing.
    ///
    /// In the simulation harness we use the Ed25519 `Votes` flavor,
    /// collecting exactly `threshold` signatures from the federation's node
    /// keys (sorted in canonical member order). This satisfies the `Votes`
    /// path threshold check in `FederationReceipt::verify`. In production a
    /// multi-node aggregator collects individual votes from each member and
    /// assembles the QC after quorum is reached. The receipt's `federation_id`
    /// is derived from the harness's canonical committee so
    /// `verify_cross_fed_receipt` can authenticate it.
    ///
    /// `block_id` can be any 32-byte identifier; in the harness we use the
    /// current consensus height as the mock block.
    pub fn lift_turn_receipt(
        &self,
        fed_idx: usize,
        turn_receipt: &TurnReceipt,
        nonce: u64,
        block_height: u64,
        block_id: [u8; 32],
    ) -> FederationReceipt {
        let fed = &self.federations[fed_idx];

        // Build the body that commits to all executor-observable state.
        let body = FederationReceiptBody {
            turn_hash: turn_receipt.turn_hash,
            block_height,
            block_hash: block_id,
            agent: turn_receipt.agent,
            nonce,
            pre_state_hash: turn_receipt.pre_state_hash,
            post_state_hash: turn_receipt.post_state_hash,
            effects_hash: turn_receipt.effects_hash,
            previous_receipt_hash: turn_receipt.previous_receipt_hash,
        };

        let body_hash = body.body_hash();

        // Collect threshold-many vote signatures from the federation's nodes.
        //
        // In the simulation harness all node signing keys are available
        // in-memory. We gather exactly `threshold` signatures in canonical
        // (sorted-by-pubkey) order — same order as `canonical.members()` —
        // so each (pubkey, signature) pair in `votes` correctly attributes
        // the signature to the right public key when `verify` iterates them.
        // This reflects the production scenario where the aggregator waits
        // for quorum before publishing the receipt.
        let threshold = fed.canonical.threshold_usize();
        let sorted_keys = fed.all_signing_keys_canonical_order();
        let members = fed.canonical.members();
        let mut votes: Vec<(FedPublicKey, dregg_types::Signature)> = Vec::new();
        for (sk, pk) in sorted_keys.iter().zip(members.iter()) {
            if votes.len() >= threshold {
                break;
            }
            let sig = dregg_types::sign(sk, &body_hash);
            votes.push((pk.clone(), sig));
        }

        FederationReceipt::with_vote_signatures(
            fed.canonical.id_bytes(),
            fed.canonical.epoch(),
            body,
            votes,
        )
    }

    /// Submit a turn to the shared ledger and, if it commits, immediately lift
    /// the `TurnReceipt` into a `FederationReceipt` attributed to `fed_idx`.
    ///
    /// Returns `(TurnResult, Option<FederationReceipt>)`. The `FederationReceipt`
    /// is `Some` only when the turn committed.
    pub fn submit_turn_with_lift(
        &mut self,
        turn: &Turn,
        fed_idx: usize,
    ) -> (TurnResult, Option<FederationReceipt>) {
        let result = self.submit_turn(turn);
        let block_height = self.clock.block_height;
        // Use a deterministic mock block_id: H("mock-block" || height || fed_idx).
        let block_id = {
            let mut h = blake3::Hasher::new_derive_key("dregg-teasting-mock-block-id-v1");
            h.update(&block_height.to_le_bytes());
            h.update(&(fed_idx as u64).to_le_bytes());
            *h.finalize().as_bytes()
        };
        let fed_receipt = match &result {
            TurnResult::Committed { receipt, .. } => {
                Some(self.lift_turn_receipt(fed_idx, receipt, turn.nonce, block_height, block_id))
            }
            _ => None,
        };
        (result, fed_receipt)
    }

    /// Register federation `src_idx` as a known peer in federation `dst_idx`'s
    /// `KnownFederations` registry.
    ///
    /// After this call, `dst_idx` can authenticate `FederationReceipt`s
    /// produced by `src_idx` via `verify_cross_fed_receipt`.
    ///
    /// This models the out-of-band federation-descriptor exchange that
    /// `register-federation` performs in the live node (committee pubkeys,
    /// epoch, threshold). The verifier-only entry uses the source federation's
    /// real committee pubkeys and threshold so `FederationReceipt::verify` can
    /// authenticate receipts produced by `lift_turn_receipt` (which collects
    /// threshold-many votes from the source federation's node keys).
    pub fn register_peer_federation(&mut self, src_idx: usize, dst_idx: usize) {
        assert_ne!(src_idx, dst_idx, "cannot register a federation with itself");
        let src_fed = &self.federations[src_idx];
        let verifier_only = Arc::new(Federation::verifier_only(
            src_fed.canonical.members().to_vec(),
            src_fed.canonical.epoch(),
            src_fed.canonical.threshold(),
        ));
        self.known_federations[dst_idx].register(verifier_only);
    }

    /// Verify a `FederationReceipt` claimed to have been produced by
    /// `src_fed_idx`, as observed by `dst_fed_idx`.
    ///
    /// Returns `true` iff the receipt is authentic:
    /// - `federation_id` in the receipt matches the registered src committee,
    /// - epoch matches,
    /// - at least one valid signature from a known src committee member.
    ///
    /// This is how F2 authenticates a receipt from F1 without re-executing
    /// F1's turn: it trusts F1's committee pubkeys (registered out-of-band)
    /// and verifies the Ed25519 vote signatures over the receipt body hash.
    pub fn verify_cross_fed_receipt(
        &self,
        receipt: &FederationReceipt,
        dst_fed_idx: usize,
    ) -> bool {
        self.known_federations[dst_fed_idx].verify_receipt(receipt)
    }
}
