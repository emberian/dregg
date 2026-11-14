//! # A REAL-executor in-process test NODE, exported for other crates' tests.
//!
//! [`TestNode`] is a minimal but GENUINE node: a real [`dregg_cell::Ledger`]
//! driven by the REAL [`dregg_turn::TurnExecutor`], plus the receipt chain the
//! client threads. It cannot depend on the `node` crate (that crate depends on
//! `dregg-sdk-net`, a cycle), so it re-checks a submitted turn exactly the way
//! [`node::api::post_submit_signed_turn`] does and serves — over a hand-rolled
//! HTTP/1.1 loop — the routes [`crate::node_world_sink::NodeHttpClient`] and
//! the client signer speak (`/turns/submit`, `/api/cells`, `/api/cell/{id}`,
//! `/api/receipts`, `/api/starbridge/receipts?turn_hash=`, `/status`,
//! `/api/faucet`, `/api/turn/{hash}/anchor`).
//!
//! A test that needs the node to answer WRONGLY (a lost answer, a foreign hash,
//! a failed receipt query, a rate-limited grant already in flight) sets a
//! [`SubmitFault`] or [`FaucetFault`]; every other answer stays the real one.
//!
//! The whole value is that the REFUSAL pole is a genuine authority rejection
//! (the executor's gate), not a stub: an over-reaching effect is refused BY THE
//! NODE (`accepted: false` out of `/turns/submit`), and an honest own-cell fire
//! COMMITS and lands a receipt the client reads back.
//!
//! Gated behind `test-support` so it never enters a shipped build. It carries no
//! `deos-js` dependency (executor + HTTP only), so a consuming crate can drive a
//! real node without dragging SpiderMonkey in.
//!
//! ```
//! # use dregg_sdk_net::test_support::TestNode;
//! # async fn demo(agent_pk: [u8; 32]) {
//! let (node, agent_cell) = TestNode::genesis([0u8; 32], agent_pk, 1_000_000);
//! let fed_id = node.fed_id();
//! let spawned = node.spawn().await;
//! // point a NodeWorldSink / NodeHttpClient at `spawned.base_url`, committing
//! // AS `agent_cell`, signed over `fed_id`; then read `spawned.lock().await`.
//! # let _ = (agent_cell, fed_id, spawned.base_url(), spawned.lock().await);
//! # }
//! ```

use std::sync::Arc;

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_turn::{ComputronCosts, TurnExecutor, TurnReceipt, TurnResult};
use dregg_types::CellId;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpListener;
use tokio::sync::Mutex;

use crate::node_world_sink::decode_32;

/// The token-id label an agent's default cell is derived under — the SAME label
/// [`crate::NodeWorldSink`] derives its committing cell from, so the cell the
/// node seeds is exactly the cell a client's turns bind.
pub fn default_token_id() -> [u8; 32] {
    *blake3::hash(b"default").as_bytes()
}

/// A fully-open permission set (every action [`AuthRequired::None`]) so a
/// `SetField` on a cell's own state authorizes without a grant.
pub fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

/// The minimal REAL-executor test node: a live [`Ledger`] + the receipt chain,
/// re-checking every submitted turn through the genuine [`TurnExecutor`].
pub struct TestNode {
    ledger: Ledger,
    receipts: Vec<TurnReceipt>,
    fed_id: [u8; 32],
    node_public_key: [u8; 32],
    /// Every `POST /api/faucet` body, in arrival order.
    faucet_requests: Vec<serde_json::Value>,
    /// Whether the executor admits the fee-exempt coordination class, served
    /// on `/status` as `coordination_fee_exempt`.
    coordination_fee_exempt: bool,
    submit_fault: Option<SubmitFault>,
    faucet_fault: Option<FaucetFault>,
    /// Faucet grants accepted while rate-limited, credited when the next
    /// request arrives (the in-flight grant finalizing).
    pending_grants: Vec<(CellId, u64)>,
    /// Ed25519 seeds of the committee that attests each committed receipt on
    /// `/api/turn/{hash}/anchor`. Empty: the node attests nothing and the
    /// route answers `no_attestation`.
    anchor_committee_seeds: Vec<[u8; 32]>,
}

/// A deliberately wrong answer from `POST /turns/submit` or the exact-hash
/// receipt query, for tests of what a client does with an answer it cannot
/// trust. The node's real admission is bypassed only where the fault says so.
#[derive(Clone, Debug)]
pub enum SubmitFault {
    /// Accept without executing and name a DIFFERENT turn's hash: the newest
    /// committed turn's, whose receipt is really on the chain, or a hash no
    /// turn has when the chain is empty.
    ReportsAnotherTurn,
    /// Accept without executing and name no turn at all.
    ReportsNoHash,
    /// Answer `/turns/submit` with this HTTP status and no verdict.
    HttpStatus(u16),
    /// Refuse without executing, naming the submitted turn and this reason.
    RefusesNamingTheTurn(String),
    /// Execute the turn for real, then fail every exact-hash receipt query
    /// with HTTP 500.
    ReceiptQueryFails,
}

/// A deliberately awkward answer from `POST /api/faucet`.
#[derive(Clone, Copy, Debug)]
pub enum FaucetFault {
    /// Answer a positive request "rate limited" as the node does when the
    /// cell's grant for this window is already in flight, and credit that
    /// grant when the next request (a client's balance poll) arrives.
    RateLimitedWhileGrantInFlight,
}

impl TestNode {
    /// A solo test node whose executor federation id is `blake3(node_public_key)`
    /// (the value the client resolves off `/status`), with a funded, fully-open
    /// agent cell seeded for `agent_public_key` under the default token. Returns
    /// the node and the seeded agent [`CellId`] (the cell a client's turns bind).
    pub fn genesis(
        node_public_key: [u8; 32],
        agent_public_key: [u8; 32],
        balance: i64,
    ) -> (Self, CellId) {
        let fed_id = *blake3::hash(&node_public_key).as_bytes();
        let mut node = TestNode {
            ledger: Ledger::new(),
            receipts: Vec::new(),
            fed_id,
            node_public_key,
            faucet_requests: Vec::new(),
            coordination_fee_exempt: false,
            submit_fault: None,
            faucet_fault: None,
            pending_grants: Vec::new(),
            anchor_committee_seeds: Vec::new(),
        };
        let agent = node.seed_open_cell(agent_public_key, balance);
        (node, agent)
    }

    /// Configure a committee of one whose committee-derived id is
    /// `federation_id`, the shape `dregg-node init` mints: the executor then
    /// signs under that id, and `/status` serves it as
    /// `executor_federation_id` while still saying `"solo"`.
    pub fn with_configured_committee(mut self, federation_id: [u8; 32]) -> Self {
        self.fed_id = federation_id;
        self
    }

    /// Turn on the fee-exempt coordination class: the executor admits a
    /// `fee = 0` own-cell EmitEvent-only turn up to the default ceiling, and
    /// `/status` says so.
    pub fn with_coordination_fee_exempt(mut self) -> Self {
        self.coordination_fee_exempt = true;
        self
    }

    /// Attest every committed receipt with a committee whose Ed25519 keys are
    /// derived from `seeds`, and serve the result on `/api/turn/{hash}/anchor`
    /// in the node's shape (`dregg_federation::TurnAnchorV1`, postcard-hex).
    pub fn with_anchor_committee(mut self, seeds: &[[u8; 32]]) -> Self {
        self.anchor_committee_seeds = seeds.to_vec();
        self
    }

    /// The roster [`Self::with_anchor_committee`] configured: what a checker
    /// that already trusts this committee holds.
    pub fn anchor_committee(&self) -> dregg_federation::turn_anchor::AnchorCommittee {
        dregg_federation::turn_anchor::AnchorCommittee {
            ed25519: self
                .anchor_committee_seeds
                .iter()
                .map(|seed| dregg_types::SigningKey::from_bytes(seed).public_key())
                .collect(),
            ml_dsa: Vec::new(),
            threshold: self.anchor_committee_seeds.len(),
            federation_id: dregg_types::FederationId(self.fed_id),
        }
    }

    /// Answer `/turns/submit` (or the receipt query) wrongly, as `fault` says,
    /// from now on. On a running node, call it through [`SpawnedNode::shared`]
    /// after the honest setup turns have committed.
    pub fn set_submit_fault(&mut self, fault: SubmitFault) {
        self.submit_fault = Some(fault);
    }

    /// Answer `/api/faucet` awkwardly, as `fault` says.
    pub fn with_faucet_fault(mut self, fault: FaucetFault) -> Self {
        self.faucet_fault = Some(fault);
        self
    }

    /// Seed a funded, fully-open cell for `public_key` (default token) and insert
    /// it. Returns the cell's id. For an own-cell affordance fire to commit, the
    /// agent cell must be seeded this way.
    pub fn seed_open_cell(&mut self, public_key: [u8; 32], balance: i64) -> CellId {
        let mut cell = Cell::with_balance(public_key, default_token_id(), balance);
        cell.permissions = open_permissions();
        let id = cell.id();
        self.ledger.insert_cell(cell).expect("seed cell");
        id
    }

    /// Insert an arbitrary caller-built [`Cell`] (e.g. a foreign, signature-gated
    /// cell whose set_state the agent cannot authorize — the over-reach pole).
    pub fn insert_cell(&mut self, cell: Cell) -> CellId {
        let id = cell.id();
        self.ledger.insert_cell(cell).expect("insert cell");
        id
    }

    /// The executor federation id a client signs its fire actions over:
    /// `blake3(node_public_key)`, or the configured committee's id after
    /// [`Self::with_configured_committee`].
    pub fn fed_id(&self) -> [u8; 32] {
        self.fed_id
    }

    /// The node's ledger (the committed world the client's crawl reads back).
    pub fn ledger(&self) -> &Ledger {
        &self.ledger
    }

    /// Every `POST /api/faucet` body this node received, in arrival order.
    pub fn faucet_requests(&self) -> &[serde_json::Value] {
        &self.faucet_requests
    }

    /// The receipt chain (one entry per committed turn).
    pub fn receipts(&self) -> &[TurnReceipt] {
        &self.receipts
    }

    /// `agent`'s own receipt head: the hash of the last receipt whose agent is
    /// `agent` (`None` when it has committed nothing). A submitted turn must
    /// thread exactly this as `previous_receipt_hash`, as the node's
    /// `stage_signed_turn_admission` requires; it is served on `/api/cell/{id}`
    /// as `last_receipt_hash`. The node-wide tip (`/api/receipts`' `chain_head`)
    /// is some other agent's receipt whenever another agent committed since.
    pub fn agent_receipt_head(&self, agent: &CellId) -> Option<[u8; 32]> {
        self.receipts
            .iter()
            .rev()
            .find(|r| r.agent == *agent)
            .map(|r| r.receipt_hash())
    }

    /// Take ownership of the node into a shared [`TcpListener`] serve loop on
    /// loopback, returning the [`SpawnedNode`] (its `base_url`, the accept-loop
    /// [`JoinHandle`](tokio::task::JoinHandle), and the shared node for reads).
    /// Call from within a tokio runtime.
    pub async fn spawn(self) -> SpawnedNode {
        let fed_id = self.fed_id;
        let node = Arc::new(Mutex::new(self));
        let listener = TcpListener::bind("127.0.0.1:0")
            .await
            .expect("bind test node");
        let addr = listener.local_addr().expect("test node addr");
        let base_url = format!("http://{addr}");

        let srv_node = node.clone();
        let handle = tokio::spawn(async move {
            loop {
                match listener.accept().await {
                    Ok((sock, _)) => {
                        let n = srv_node.clone();
                        tokio::spawn(handle_conn(sock, n));
                    }
                    Err(_) => break,
                }
            }
        });

        SpawnedNode {
            base_url,
            fed_id,
            node,
            handle,
        }
    }
}

/// A running [`TestNode`]: the URL a client points at, the shared node (for
/// post-fire reads), and the accept-loop handle.
pub struct SpawnedNode {
    /// The node base URL (`http://127.0.0.1:<ephemeral>`).
    pub base_url: String,
    fed_id: [u8; 32],
    node: Arc<Mutex<TestNode>>,
    handle: tokio::task::JoinHandle<()>,
}

impl SpawnedNode {
    /// The node base URL a client points at.
    pub fn base_url(&self) -> &str {
        &self.base_url
    }

    /// The executor federation id (a client signs fire actions over this).
    pub fn fed_id(&self) -> [u8; 32] {
        self.fed_id
    }

    /// A clone of the shared node handle (lock it to read the ledger/receipts).
    pub fn shared(&self) -> Arc<Mutex<TestNode>> {
        self.node.clone()
    }

    /// Lock the shared node to read its committed state (ledger, receipts) after
    /// a fire has landed.
    pub async fn lock(&self) -> tokio::sync::MutexGuard<'_, TestNode> {
        self.node.lock().await
    }

    /// Stop the accept loop (abandon in-flight connections). The node is also
    /// abandoned at process exit if this is never called.
    pub fn shutdown(self) {
        self.handle.abort();
    }
}

// ───────────────────────────── the HTTP/1.1 serve ────────────────────────────

/// Execute a submitted postcard `SignedTurn` through the REAL executor,
/// mirroring `node::api::post_submit_signed_turn`'s checks. Returns the JSON body
/// the client parses.
fn handle_submit(node: &mut TestNode, body: &[u8]) -> (u16, serde_json::Value) {
    let signed: dregg_sdk::SignedTurn = match postcard::take_from_bytes(body) {
        Ok((s, [])) => s,
        Ok((_s, remainder)) => {
            return (
                200,
                serde_json::json!({
                    "accepted": false,
                    "error": format!(
                        "trailing bytes after SignedTurn envelope: {}",
                        remainder.len()
                    ),
                }),
            );
        }
        Err(_) => {
            return (
                200,
                serde_json::json!({"accepted": false, "error": "malformed SignedTurn"}),
            );
        }
    };
    let turn_hash = signed.turn.hash();
    match node.submit_fault.clone() {
        Some(SubmitFault::ReportsAnotherTurn) => {
            let other = node
                .receipts
                .last()
                .map(|r| dregg_types::hex_encode(&r.turn_hash))
                .unwrap_or_else(|| "33".repeat(32));
            return (
                200,
                serde_json::json!({"accepted": true, "turn_hash": other}),
            );
        }
        Some(SubmitFault::ReportsNoHash) => {
            return (200, serde_json::json!({"accepted": true}));
        }
        Some(SubmitFault::HttpStatus(code)) => {
            return (code, serde_json::json!({"error": "injected status"}));
        }
        Some(SubmitFault::RefusesNamingTheTurn(reason)) => {
            return (
                200,
                serde_json::json!({
                    "accepted": false,
                    "turn_hash": dregg_types::hex_encode(&turn_hash),
                    "error": reason,
                }),
            );
        }
        Some(SubmitFault::ReceiptQueryFails) | None => {}
    }
    if !signed.signer.verify(&turn_hash, &signed.signature) {
        return (
            200,
            serde_json::json!({
                "accepted": false,
                "turn_hash": dregg_types::hex_encode(&turn_hash),
                "error": "invalid turn signature",
            }),
        );
    }
    let expected_agent = CellId::derive_raw(&signed.signer.0, &default_token_id());
    if signed.turn.agent != expected_agent {
        return (
            200,
            serde_json::json!({
                "accepted": false,
                "turn_hash": dregg_types::hex_encode(&turn_hash),
                "error": "turn agent does not match signer default cell",
            }),
        );
    }
    if signed.turn.previous_receipt_hash != node.agent_receipt_head(&signed.turn.agent) {
        return (
            200,
            serde_json::json!({
                "accepted": false,
                "turn_hash": dregg_types::hex_encode(&turn_hash),
                "error": "receipt chain mismatch",
            }),
        );
    }

    let mut costs = ComputronCosts::default();
    costs.coordination_exempt = node.coordination_fee_exempt;
    let mut executor = TurnExecutor::new(costs);
    executor.set_local_federation_id(node.fed_id);
    executor.set_timestamp(0);
    // The height a node's submit executor runs at: the attested height `/status` serves, plus
    // one (`executor_setup::BlockHeightMode::Next`). `valid_until` is checked against it.
    executor.set_block_height(node.receipts.len() as u64 + 1);
    // A fresh executor knows no agent's receipt head; the node seeds it from its chain, so an
    // agent's second turn (threading its first receipt) is admitted rather than refused as a
    // chain mismatch against `None`.
    if let Some(head) = node.agent_receipt_head(&signed.turn.agent) {
        executor.set_last_receipt_hash(signed.turn.agent, head);
    }
    match executor.execute(&signed.turn, &mut node.ledger) {
        TurnResult::Committed { receipt, .. } => {
            node.receipts.push(receipt);
            (
                200,
                serde_json::json!({
                    "accepted": true,
                    "turn_hash": dregg_types::hex_encode(&turn_hash),
                }),
            )
        }
        TurnResult::Rejected { reason, .. } => (
            200,
            serde_json::json!({
                "accepted": false,
                "turn_hash": dregg_types::hex_encode(&turn_hash),
                "error": format!("{reason}"),
            }),
        ),
        other => (
            200,
            serde_json::json!({
                "accepted": false,
                "turn_hash": dregg_types::hex_encode(&turn_hash),
                "error": format!("unexpected result: {other:?}"),
            }),
        ),
    }
}

/// `POST /api/faucet`, as a solo node answers it: record the body, then
/// materialize an absent recipient. With `public_key` the cell is bound to that
/// key (the solo node's hosted cell); without it, a zero-pk stub in the default
/// asset. A positive amount credits the recipient, as finalization does.
fn handle_faucet(node: &mut TestNode, body: &[u8]) -> serde_json::Value {
    let Ok(req) = serde_json::from_slice::<serde_json::Value>(body) else {
        return serde_json::json!({"success": false, "error": "malformed faucet request"});
    };
    node.faucet_requests.push(req.clone());
    let recipient = req["recipient"].as_str().and_then(decode_32).map(CellId);
    let amount = req["amount"].as_u64().unwrap_or(0);
    let Some(recipient) = recipient else {
        return serde_json::json!({"success": false, "error": "malformed recipient"});
    };
    if amount > 0
        && let Some(FaucetFault::RateLimitedWhileGrantInFlight) = node.faucet_fault
    {
        node.pending_grants.push((recipient, amount));
        return serde_json::json!({
            "success": false,
            "error": "rate limited: 1 request per cell per minute",
        });
    }
    if node.ledger.get(&recipient).is_none() {
        let cell = match req["public_key"].as_str().and_then(decode_32) {
            Some(pk) => Cell::with_balance(pk, default_token_id(), 0),
            None => Cell::remote_stub_with_id_pk_token_balance(
                recipient,
                [0u8; 32],
                default_token_id(),
                0,
            ),
        };
        if node.ledger.insert_cell(cell).is_err() {
            return serde_json::json!({"success": false, "error": "recipient insert refused"});
        }
    }
    if amount > 0
        && let Some(cell) = node.ledger.get_mut(&recipient)
    {
        let balance = cell.state.balance();
        cell.state.set_balance(balance + amount as i64);
    }
    let hash = dregg_types::hex_encode(blake3::hash(body).as_bytes());
    let turn_hash = (amount > 0).then(|| hash.clone());
    serde_json::json!({
        "success": true,
        "tx_hash": hash,
        "amount": amount,
        "turn_hash": turn_hash,
    })
}

fn cell_detail_json(id_hex: &str, node: &TestNode) -> serde_json::Value {
    let bytes = match decode_32(id_hex) {
        Some(b) => b,
        None => return serde_json::json!({"id": id_hex, "found": false}),
    };
    let head = node
        .agent_receipt_head(&CellId(bytes))
        .map(|h| dregg_types::hex_encode(&h));
    match node.ledger.get(&CellId(bytes)) {
        Some(cell) => serde_json::json!({
            "id": id_hex,
            "found": true,
            "last_receipt_hash": head,
            "balance": cell.state.balance(),
            "nonce": cell.state.nonce(),
            "public_key": dregg_types::hex_encode(cell.public_key()),
            "token_id": dregg_types::hex_encode(cell.token_id()),
            "delegate": cell.delegate.as_ref().map(|d| dregg_types::hex_encode(&d.0)),
            "fields": cell.state.fields.iter()
                .map(|f| dregg_types::hex_encode(f)).collect::<Vec<_>>(),
            // The c-list EDGES, serialized exactly as `node::api::get_cell_detail`
            // does — the real node's explorer surface carries them, so the crawl
            // rebuilds the true `CapabilitySet` (Pillar-2b authority fidelity).
            "capabilities": cell.capabilities.iter().cloned().collect::<Vec<_>>(),
            "capability_tombstones": cell.capabilities.tombstoned_slots().collect::<Vec<u32>>(),
        }),
        // The node serves an agent's head for a cell it does not hold too.
        None => serde_json::json!({"id": id_hex, "found": false, "last_receipt_hash": head}),
    }
}

/// `GET /api/starbridge/receipts?turn_hash=<hex>`: the whole chain filtered by
/// exact turn hash, in the node's `ReceiptInfo` shape. A solo node's receipts
/// are `tentative`.
fn exact_receipts_json(query: &str, node: &TestNode) -> serde_json::Value {
    let want = query
        .split('&')
        .find_map(|kv| kv.strip_prefix("turn_hash="))
        .unwrap_or_default();
    let last = node.receipts.len().saturating_sub(1);
    let rows: Vec<serde_json::Value> = node
        .receipts
        .iter()
        .enumerate()
        .filter(|(_, r)| dregg_types::hex_encode(&r.turn_hash).eq_ignore_ascii_case(want))
        .map(|(i, r)| {
            serde_json::json!({
                "chain_index": i as u64,
                "chain_head": i == last,
                "receipt_hash": dregg_types::hex_encode(&r.receipt_hash()),
                "turn_hash": dregg_types::hex_encode(&r.turn_hash),
                "agent": dregg_types::hex_encode(&r.agent.0),
                "finality": "tentative",
            })
        })
        .collect();
    serde_json::Value::Array(rows)
}

/// `GET /api/turn/{hash}/anchor`, as `node::api::get_turn_anchor` answers it:
/// 404 `not_committed` for a hash with no receipt, 409 `no_attestation` when
/// no committee attests, else the receipt whole under an attested root whose
/// `receipt_stream_root` is the singleton root of that receipt's hash, signed
/// by every configured committee member.
fn turn_anchor_json(hash_hex: &str, node: &TestNode) -> (u16, serde_json::Value) {
    let Some((index, receipt)) = node
        .receipts
        .iter()
        .enumerate()
        .find(|(_, r)| dregg_types::hex_encode(&r.turn_hash).eq_ignore_ascii_case(hash_hex))
    else {
        return (
            404,
            serde_json::json!({"turn_hash": hash_hex, "anchor_status": "not_committed"}),
        );
    };
    if node.anchor_committee_seeds.is_empty() {
        return (
            409,
            serde_json::json!({"turn_hash": hash_hex, "anchor_status": "no_attestation"}),
        );
    }
    let height = index as u64 + 1;
    let block_id = *blake3::hash(&height.to_le_bytes()).as_bytes();
    let mut attested = dregg_types::AttestedRoot {
        merkle_root: [0u8; 32],
        note_tree_root: None,
        nullifier_set_root: None,
        height,
        timestamp: 0,
        blocklace_block_id: Some(block_id),
        finality_round: None,
        quorum_signatures: Vec::new(),
        threshold_qc: None,
        threshold: node.anchor_committee_seeds.len(),
        federation_id: dregg_types::FederationId(node.fed_id),
        receipt_stream_root: Some(dregg_types::merkle_root_of_receipt_hashes(&[
            receipt.receipt_hash()
        ])),
        hybrid_quorum: Vec::new(),
    };
    let message = attested.signing_message();
    for seed in &node.anchor_committee_seeds {
        let key = dregg_types::SigningKey::from_bytes(seed);
        attested
            .quorum_signatures
            .push((key.public_key(), dregg_types::sign(&key, &message)));
    }
    let anchor = dregg_federation::turn_anchor::TurnAnchorV1 {
        protocol: dregg_federation::turn_anchor::TURN_ANCHOR_PROTOCOL_V1.to_string(),
        turn_hash: receipt.turn_hash,
        receipt: receipt.clone(),
        height,
        block_id,
        attested,
        served_committee: node.anchor_committee(),
    };
    let bytes = postcard::to_stdvec(&anchor).expect("encode the anchor");
    (
        200,
        serde_json::json!({
            "turn_hash": hash_hex,
            "anchor_status": "anchored",
            "anchor_hex": hex::encode(bytes),
        }),
    )
}

fn receipts_json(node: &TestNode) -> serde_json::Value {
    let last = node.receipts.len().saturating_sub(1);
    let arr: Vec<serde_json::Value> = node
        .receipts
        .iter()
        .enumerate()
        .map(|(i, r)| {
            serde_json::json!({
                "chain_index": i as u64,
                "chain_head": i == last,
                "receipt_hash": dregg_types::hex_encode(&r.receipt_hash()),
                "turn_hash": dregg_types::hex_encode(&r.turn_hash),
            })
        })
        .collect();
    serde_json::Value::Array(arr)
}

fn route(method: &str, path: &str, body: &[u8], node: &mut TestNode) -> (u16, serde_json::Value) {
    // A grant accepted while rate-limited finalizes before the next request.
    for (cell, amount) in std::mem::take(&mut node.pending_grants) {
        if let Some(c) = node.ledger.get_mut(&cell) {
            let balance = c.state.balance();
            c.state.set_balance(balance + amount as i64);
        }
    }
    if method == "POST" && path == "/turns/submit" {
        return handle_submit(node, body);
    }
    if method == "GET"
        && let Some(query) = path.strip_prefix("/api/starbridge/receipts?")
    {
        if let Some(SubmitFault::ReceiptQueryFails) = node.submit_fault {
            return (
                500,
                serde_json::json!({"error": "receipt index unavailable"}),
            );
        }
        return (200, exact_receipts_json(query, node));
    }
    if method == "GET"
        && let Some(hash) = path
            .strip_prefix("/api/turn/")
            .and_then(|rest| rest.strip_suffix("/anchor"))
    {
        return turn_anchor_json(hash, node);
    }
    let json = match (method, path) {
        ("GET", "/api/cells") => {
            let arr: Vec<serde_json::Value> = node
                .ledger
                .iter()
                .map(|(id, cell)| {
                    serde_json::json!({
                        "id": dregg_types::hex_encode(&id.0),
                        "balance": cell.state.balance(),
                        "nonce": cell.state.nonce(),
                    })
                })
                .collect();
            serde_json::Value::Array(arr)
        }
        ("GET", "/api/receipts") => receipts_json(node),
        // `executor_federation_id` is the id this node's executor verifies
        // under (`fed_id`), as the real `/status` serves
        // `federation_id_for_executor`.
        ("GET", "/status") => serde_json::json!({
            "federation_mode": "solo",
            "public_key": dregg_types::hex_encode(&node.node_public_key),
            "executor_federation_id": dregg_types::hex_encode(&node.fed_id),
            "coordination_fee_exempt": node.coordination_fee_exempt,
            "coordination_exempt_ceiling": ComputronCosts::default().coordination_exempt_ceiling,
            // One height per committed turn, as the node's attested height
            // advances only on turn-bearing finality.
            "latest_height": node.receipts.len() as u64,
        }),
        ("POST", "/api/faucet") => handle_faucet(node, body),
        ("GET", p) if p.starts_with("/api/cell/") => {
            let id_hex = p.trim_start_matches("/api/cell/");
            cell_detail_json(id_hex, node)
        }
        _ => serde_json::json!({"error": "not found"}),
    };
    (200, json)
}

/// Serve one HTTP/1.1 request on `sock` against the shared node.
async fn handle_conn(mut sock: tokio::net::TcpStream, node: Arc<Mutex<TestNode>>) {
    // Read headers (until CRLFCRLF), then Content-Length body.
    let mut buf = Vec::new();
    let mut tmp = [0u8; 4096];
    let header_end = loop {
        match sock.read(&mut tmp).await {
            Ok(0) => return,
            Ok(n) => {
                buf.extend_from_slice(&tmp[..n]);
                if let Some(pos) = find_subslice(&buf, b"\r\n\r\n") {
                    break pos;
                }
            }
            Err(_) => return,
        }
    };
    let header_str = String::from_utf8_lossy(&buf[..header_end]).to_string();
    let mut lines = header_str.split("\r\n");
    let request_line = lines.next().unwrap_or("");
    let mut parts = request_line.split_whitespace();
    let method = parts.next().unwrap_or("").to_string();
    let path = parts.next().unwrap_or("").to_string();
    let content_length = lines
        .find_map(|l| {
            let l = l.to_ascii_lowercase();
            l.strip_prefix("content-length:")
                .map(|v| v.trim().parse::<usize>().unwrap_or(0))
        })
        .unwrap_or(0);

    let mut body = buf[header_end + 4..].to_vec();
    while body.len() < content_length {
        match sock.read(&mut tmp).await {
            Ok(0) => break,
            Ok(n) => body.extend_from_slice(&tmp[..n]),
            Err(_) => break,
        }
    }

    let (code, json) = {
        let mut guard = node.lock().await;
        route(&method, &path, &body, &mut guard)
    };
    let payload = serde_json::to_vec(&json).unwrap();
    let head = format!(
        "HTTP/1.1 {code} {}\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        if code < 400 { "OK" } else { "Error" },
        payload.len()
    );
    let _ = sock.write_all(head.as_bytes()).await;
    let _ = sock.write_all(&payload).await;
    let _ = sock.flush().await;
}

fn find_subslice(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    haystack.windows(needle.len()).position(|w| w == needle)
}

/// A convenience for a foreign, signature-gated cell (the over-reach pole): a
/// funded cell for `public_key` whose `set_state` REQUIRES the owner's signature,
/// so an agent that holds neither the key nor a capability cannot write it.
pub fn signature_gated_cell(public_key: [u8; 32], balance: i64) -> Cell {
    let mut cell = Cell::with_balance(public_key, default_token_id(), balance);
    let mut perms = open_permissions();
    perms.set_state = AuthRequired::Signature;
    cell.permissions = perms;
    cell
}
