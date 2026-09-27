//! # A REAL-executor in-process test NODE, exported for other crates' tests.
//!
//! [`TestNode`] is a minimal but GENUINE node: a real [`dregg_cell::Ledger`]
//! driven by the REAL [`dregg_turn::TurnExecutor`], plus the receipt chain the
//! client threads. It cannot depend on the `node` crate (that crate depends on
//! `dregg-sdk-net`, a cycle), so it re-checks a submitted turn exactly the way
//! [`node::api::post_submit_signed_turn`] does and serves — over a hand-rolled
//! HTTP/1.1 loop — the four routes [`crate::node_world_sink::NodeHttpClient`]
//! speaks (`/turns/submit`, `/api/cells`, `/api/cell/{id}`, `/api/receipts`,
//! `/status`).
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
    /// Members of a CONFIGURED committee, as `/api/federations` counts them.
    /// `0` is the unconfigured node: its local entry lists no members and the
    /// executor signs under `blake3(node_public_key)`.
    committee_members: usize,
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
            committee_members: 0,
        };
        let agent = node.seed_open_cell(agent_public_key, balance);
        (node, agent)
    }

    /// Configure a committee of one whose committee-derived id is
    /// `federation_id`, the shape `dregg-node init` mints: the executor then
    /// signs under that id, while `/status` still says `"solo"`.
    pub fn with_configured_committee(mut self, federation_id: [u8; 32]) -> Self {
        self.fed_id = federation_id;
        self.committee_members = 1;
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

    /// The receipt chain (one entry per committed turn).
    pub fn receipts(&self) -> &[TurnReceipt] {
        &self.receipts
    }

    /// The chain-head receipt hash a fresh turn must thread (`None` when empty).
    pub fn chain_head(&self) -> Option<[u8; 32]> {
        self.receipts.last().map(|r| r.receipt_hash())
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
fn handle_submit(node: &mut TestNode, body: &[u8]) -> serde_json::Value {
    let signed: dregg_sdk::SignedTurn = match postcard::take_from_bytes(body) {
        Ok((s, [])) => s,
        Ok((_s, remainder)) => {
            return serde_json::json!({
                "accepted": false,
                "error": format!(
                    "trailing bytes after SignedTurn envelope: {}",
                    remainder.len()
                ),
            });
        }
        Err(_) => {
            return serde_json::json!({"accepted": false, "error": "malformed SignedTurn"});
        }
    };
    let turn_hash = signed.turn.hash();
    if !signed.signer.verify(&turn_hash, &signed.signature) {
        return serde_json::json!({
            "accepted": false,
            "turn_hash": dregg_types::hex_encode(&turn_hash),
            "error": "invalid turn signature",
        });
    }
    let expected_agent = CellId::derive_raw(&signed.signer.0, &default_token_id());
    if signed.turn.agent != expected_agent {
        return serde_json::json!({
            "accepted": false,
            "turn_hash": dregg_types::hex_encode(&turn_hash),
            "error": "turn agent does not match signer default cell",
        });
    }
    if signed.turn.previous_receipt_hash != node.chain_head() {
        return serde_json::json!({
            "accepted": false,
            "turn_hash": dregg_types::hex_encode(&turn_hash),
            "error": "receipt chain mismatch",
        });
    }

    let mut executor = TurnExecutor::new(ComputronCosts::default());
    executor.set_local_federation_id(node.fed_id);
    executor.set_timestamp(0);
    match executor.execute(&signed.turn, &mut node.ledger) {
        TurnResult::Committed { receipt, .. } => {
            node.receipts.push(receipt);
            serde_json::json!({
                "accepted": true,
                "turn_hash": dregg_types::hex_encode(&turn_hash),
            })
        }
        TurnResult::Rejected { reason, .. } => serde_json::json!({
            "accepted": false,
            "turn_hash": dregg_types::hex_encode(&turn_hash),
            "error": format!("{reason}"),
        }),
        other => serde_json::json!({
            "accepted": false,
            "turn_hash": dregg_types::hex_encode(&turn_hash),
            "error": format!("unexpected result: {other:?}"),
        }),
    }
}

fn cell_detail_json(id_hex: &str, node: &TestNode) -> serde_json::Value {
    let bytes = match decode_32(id_hex) {
        Some(b) => b,
        None => return serde_json::json!({"id": id_hex, "found": false}),
    };
    match node.ledger.get(&CellId(bytes)) {
        Some(cell) => serde_json::json!({
            "id": id_hex,
            "found": true,
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
        None => serde_json::json!({"id": id_hex, "found": false}),
    }
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

fn route(method: &str, path: &str, body: &[u8], node: &mut TestNode) -> serde_json::Value {
    match (method, path) {
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
        ("GET", "/status") => serde_json::json!({
            "federation_mode": "solo",
            "public_key": dregg_types::hex_encode(&node.node_public_key),
        }),
        // The node's `federation_infos` shape. An unconfigured node lists its
        // local entry with no members and an id that is NOT the executor's.
        ("GET", "/api/federations") => {
            let listed = if node.committee_members > 0 {
                node.fed_id
            } else {
                *blake3::hash(b"unconfigured local federation id").as_bytes()
            };
            serde_json::json!([{
                "id": dregg_types::hex_encode(&listed),
                "federation_id": dregg_types::hex_encode(&listed),
                "member_count": node.committee_members,
                "is_local": true,
            }])
        }
        ("POST", "/turns/submit") => handle_submit(node, body),
        ("GET", p) if p.starts_with("/api/cell/") => {
            let id_hex = p.trim_start_matches("/api/cell/");
            cell_detail_json(id_hex, node)
        }
        _ => serde_json::json!({"error": "not found"}),
    }
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

    let json = {
        let mut guard = node.lock().await;
        route(&method, &path, &body, &mut guard)
    };
    let payload = serde_json::to_vec(&json).unwrap();
    let head = format!(
        "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
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
