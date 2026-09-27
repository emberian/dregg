//! # The CLIENT-SIDE `NodeWorldSink` — inhabit a remote box's node over HTTP.
//!
//! Pillar 0 of the distributed-deos goal: a [`deos_js::WorldSink`] a remote
//! inhabitation process uses to drive a node running on ANOTHER box. It is the
//! HTTP-CLIENT half of [`node`'s in-process `NodeWorldSink`](../../node/src/deos_host.rs):
//! same trait, same semantics (which cell a turn binds, the real receipt hash a
//! commit returns), reached over the wire instead of a shared `NodeState`.
//!
//!   * **the crawl** ([`NodeHttpClient::fetch_ledger_snapshot`]) rebuilds a
//!     SNAPSHOT [`Ledger`] from `GET /api/cells` (the id list) + `GET
//!     /api/cell/{id}` (per-cell detail). This is the SAME fidelity bar the
//!     world-bridge's `WithLedger` set: it snapshots cells (public_key, token,
//!     fields, balance, nonce, delegate) — enough for the reflective crawl
//!     (`CellModel`/`reflect`) — NOT a byte-perfect `Ledger` (no sovereign
//!     commitments, no reconstructed programs; the crawl does not read them).
//!   * **the commit** ([`NodeHttpClient::submit_turn`]) builds a signed
//!     [`Turn`] the EXACT way [`crate::deos_server::fire_affordance`] does (the
//!     agent's fresh nonce off the node, the receipt-chain head threaded, the
//!     computron fee estimated, the action signed over the executor's federation
//!     id) and POSTs the postcard `SignedTurn` to `/turns/submit`. Fail-CLOSED:
//!     an HTTP error or a node refusal is `Err`, never a silent success.
//!
//! The node re-checks every effect against its verified executor's authority
//! gate, so an over-reaching effect is refused BY THE NODE (an `Err` out of
//! `fire_effects`), not by this sink — the sink carries no cap tooth (that lives
//! above it, in `deos_js::AttachedApplet`).
//!
//! The [`WorldSink`](deos_js::WorldSink) impl over this client lives behind the
//! `world-sink` feature so the base net layer stays free of the `deos-js`
//! (SpiderMonkey) dependency; the light HTTP client here carries no such dep.

use dregg_cell::state::FieldElement;
use dregg_cell::{CapabilityRef, CapabilitySet, Cell, Ledger};
use dregg_sdk::AgentCipherclerk;
use dregg_sdk::error::SdkError;
use dregg_turn::action::Effect;
use dregg_turn::{ComputronCosts, Turn, TurnExecutor};
use dregg_types::CellId;

/// The light HTTP client half — ALWAYS compiled, no `deos-js` dependency.
///
/// It speaks the node's public REST surface: the explorer reads (`/api/cells`,
/// `/api/cell/{id}`, `/api/receipts`) and the signed-turn ingress
/// (`/turns/submit`). Every method is fail-closed.
#[derive(Clone, Debug)]
pub struct NodeHttpClient {
    base_url: String,
    http: reqwest::Client,
}

impl NodeHttpClient {
    /// A client for the node reachable at `base_url` (e.g. `http://box-2.local:8080`).
    pub fn new(base_url: impl Into<String>) -> Self {
        let base_url = base_url.into().trim_end_matches('/').to_string();
        NodeHttpClient {
            base_url,
            http: reqwest::Client::new(),
        }
    }

    /// The node base URL (already trimmed of a trailing slash).
    pub fn base_url(&self) -> &str {
        &self.base_url
    }

    pub(crate) fn http_client(&self) -> &reqwest::Client {
        &self.http
    }

    // ─────────────────────────── the crawl (read) ───────────────────────────

    /// Rebuild a SNAPSHOT [`Ledger`] from the node's explorer surface: `GET
    /// /api/cells` for the id list, then `GET /api/cell/{id}` per cell for the
    /// detail. Snapshots cells only (the crawl surface `CellModel`/`reflect`
    /// walks); it does NOT reconstruct sovereign commitments or programs.
    ///
    /// Fail-closed: any HTTP/JSON error is an `Err`, so a caller never mistakes a
    /// degraded read for an empty world.
    pub async fn fetch_ledger_snapshot(&self) -> Result<Ledger, SdkError> {
        let list_url = format!("{}/api/cells", self.base_url);
        let list: serde_json::Value = self.get_json(&list_url).await?;
        let ids: Vec<String> = list
            .as_array()
            .ok_or_else(|| SdkError::Wire("/api/cells did not return an array".into()))?
            .iter()
            .filter_map(|e| e.get("id").and_then(|i| i.as_str()).map(String::from))
            .collect();

        let mut ledger = Ledger::new();
        for id in ids {
            let detail_url = format!("{}/api/cell/{}", self.base_url, id);
            let detail: serde_json::Value = self.get_json(&detail_url).await?;
            if let Some(cell) = cell_from_detail(&detail) {
                // insert_cell only re-checks id uniqueness; a detail whose fields
                // fail to rebuild a content-addressed cell is skipped (never a
                // substitute cell, never a hard fail of the whole crawl).
                let _ = ledger.insert_cell(cell);
            }
        }
        Ok(ledger)
    }

    // ────────────────────────── the commit (write) ──────────────────────────

    /// Build a signed [`Turn`] under `signer` (acting AS its own cell `agent`)
    /// carrying `effects`, named `method`, and POST it to `/turns/submit`.
    /// Returns the REAL receipt hash the node recorded for the committed turn.
    ///
    /// The flow mirrors [`crate::deos_server::fire_affordance`] exactly:
    ///   1. read `agent`'s current nonce (`GET /api/cell/{agent}`) + the node's
    ///      receipt-chain head (`GET /api/receipts`);
    ///   2. build a single-action turn (`signer.make_action` over `effects`,
    ///      signed against `federation_id`), thread the chain head as
    ///      `previous_receipt_hash`, and stamp `fee` = the estimated computron
    ///      cost (a pure function of the effects);
    ///   3. POST the postcard `SignedTurn` and read the verdict. On accept,
    ///      resolve the committed turn's `receipt_hash` off `/api/receipts`.
    ///
    /// Fail-closed: a transport error, a node rejection (`accepted != true`), or
    /// a committed turn not yet visible on `/api/receipts` all return `Err`.
    pub async fn submit_turn(
        &self,
        signer: &AgentCipherclerk,
        agent: CellId,
        method: &str,
        effects: Vec<Effect>,
        federation_id: &[u8; 32],
    ) -> Result<[u8; 32], SdkError> {
        // (1) the agent's fresh nonce + the node's chain head.
        let nonce = self.fetch_cell_nonce(&agent).await?;
        let chain_head = self.fetch_chain_head().await?;

        // (2) build + sign the single-action fire turn (the deos_server shape).
        let action = signer.make_action(agent, method, effects, federation_id);
        let mut turn: Turn = signer.make_turn_with_actions(vec![action]);
        turn.agent = agent;
        turn.nonce = nonce;
        turn.memo = Some(format!("node_world_sink_{method}"));
        turn.valid_until = Some(i64::MAX / 2);
        turn.previous_receipt_hash = chain_head;
        turn.fee = TurnExecutor::new(ComputronCosts::default()).estimate_cost(&turn);

        let signed = signer.sign_turn(&turn);
        let signed_bytes = postcard::to_stdvec(&signed)
            .map_err(|e| SdkError::Wire(format!("serialize SignedTurn: {e}")))?;

        // (3) POST the postcard SignedTurn to the signed-turn ingress.
        let url = format!("{}/turns/submit", self.base_url);
        let resp = self
            .http
            .post(&url)
            .header("Content-Type", "application/octet-stream")
            .body(signed_bytes)
            .send()
            .await
            .map_err(|e| SdkError::Wire(format!("turns/submit request failed: {e}")))?;
        if !resp.status().is_success() {
            return Err(SdkError::Wire(format!(
                "turns/submit returned status {}",
                resp.status()
            )));
        }
        let body: serde_json::Value = resp
            .json()
            .await
            .map_err(|e| SdkError::Wire(format!("parse submit response: {e}")))?;

        let accepted = body
            .get("accepted")
            .and_then(|a| a.as_bool())
            .unwrap_or(false);
        if !accepted {
            let reason = body
                .get("error")
                .and_then(|e| e.as_str())
                .unwrap_or("node refused the turn (no reason given)");
            return Err(SdkError::Wire(format!("turn refused by node: {reason}")));
        }
        let turn_hash = body
            .get("turn_hash")
            .and_then(|h| h.as_str())
            .ok_or_else(|| SdkError::Wire("accepted submit response missing turn_hash".into()))?
            .to_string();

        // Resolve the REAL receipt hash for the committed turn off /api/receipts.
        // (The submit response attests the turn hash; the sink's contract is the
        // receipt hash, the same value the in-process NodeWorldSink returns.)
        self.resolve_receipt_hash(&turn_hash).await
    }

    /// The executor's federation id — the binding a fire action is signed over.
    ///
    /// The node signs and verifies under `federation_id_for_executor`: the
    /// committee-derived `federation_id` once a committee is configured, else
    /// `blake3(node_public_key)`. A remote client cannot derive it, and
    /// `/status.federation_mode` does not decide it: that field says `"solo"`
    /// for ANY committee of one, and the chain `dregg-node init` mints is a
    /// configured committee of one. Signing such a node's actions over
    /// `blake3(public_key)` yields a signature the Rust executor never checks
    /// on an open cell, and that the verified producer's WHO leg refuses, so
    /// every turn is vetoed with no reason named.
    ///
    /// So the configured committee is read first: `GET /api/federations` lists
    /// the local federation as the `is_local` entry, and a non-empty member
    /// list means a configured committee whose `federation_id` is the id. A
    /// node with no configured committee lists its local entry with no
    /// members; it, and a node that does not serve the route, signs under
    /// `blake3(public_key)` from `/status` when it is solo.
    pub async fn fetch_executor_federation_id(&self) -> Result<[u8; 32], SdkError> {
        if let Some(id) = self.fetch_configured_local_federation_id().await? {
            return Ok(id);
        }
        let status: serde_json::Value = self.get_json(&format!("{}/status", self.base_url)).await?;
        let mode = status
            .get("federation_mode")
            .and_then(|m| m.as_str())
            .unwrap_or("solo");
        if mode != "solo" {
            return Err(SdkError::Wire(format!(
                "a {mode}-mode node lists no configured local federation on /api/federations"
            )));
        }
        let pk_hex = status
            .get("public_key")
            .and_then(|p| p.as_str())
            .ok_or_else(|| SdkError::Wire("/status missing public_key".into()))?;
        let pk = decode_32(pk_hex)
            .ok_or_else(|| SdkError::Wire("/status public_key is not 32 bytes of hex".into()))?;
        Ok(*blake3::hash(&pk).as_bytes())
    }

    /// The `federation_id` of the `is_local` entry of `GET /api/federations`
    /// when that entry has members (a configured committee). `None` when the
    /// node does not serve the route (a non-success status) or lists no
    /// configured local committee. A transport failure, or a configured entry
    /// whose id does not decode, is an `Err`: guessing the id there would sign
    /// every action over the wrong binding.
    async fn fetch_configured_local_federation_id(&self) -> Result<Option<[u8; 32]>, SdkError> {
        let url = format!("{}/api/federations", self.base_url);
        let resp = self
            .http
            .get(&url)
            .send()
            .await
            .map_err(|e| SdkError::Wire(format!("GET {url} failed: {e}")))?;
        if !resp.status().is_success() {
            return Ok(None);
        }
        let body: serde_json::Value = resp
            .json()
            .await
            .map_err(|e| SdkError::Wire(format!("parse {url}: {e}")))?;
        let Some(local) = body.as_array().and_then(|feds| {
            feds.iter()
                .find(|f| f.get("is_local").and_then(|l| l.as_bool()) == Some(true))
        }) else {
            return Ok(None);
        };
        let members = local.get("member_count").and_then(|m| m.as_u64());
        if members.unwrap_or(0) == 0 {
            return Ok(None);
        }
        let id = local
            .get("federation_id")
            .and_then(|f| f.as_str())
            .and_then(decode_32)
            .ok_or_else(|| {
                SdkError::Wire(format!(
                    "{url}: the configured local federation has no 32-byte hex federation_id"
                ))
            })?;
        Ok(Some(id))
    }

    /// `GET /api/cell/{id}` → the cell's current nonce (the executor rejects a
    /// stale nonce, so a fire must use this fresh value).
    pub async fn fetch_cell_nonce(&self, cell: &CellId) -> Result<u64, SdkError> {
        let url = format!(
            "{}/api/cell/{}",
            self.base_url,
            dregg_types::hex_encode(cell.as_bytes())
        );
        let body: serde_json::Value = self.get_json(&url).await?;
        if body.get("found").and_then(|f| f.as_bool()) != Some(true) {
            return Err(SdkError::Wire(format!(
                "agent cell {} not found on the node",
                dregg_types::hex_encode(cell.as_bytes())
            )));
        }
        Ok(body.get("nonce").and_then(|n| n.as_u64()).unwrap_or(0))
    }

    /// `GET /api/receipts` → the `receipt_hash` of the entry flagged
    /// `chain_head` (`None` when the chain is empty). The executor requires a
    /// turn to thread this head.
    pub async fn fetch_chain_head(&self) -> Result<Option<[u8; 32]>, SdkError> {
        let url = format!("{}/api/receipts", self.base_url);
        let body: serde_json::Value = self.get_json(&url).await?;
        let head_hex = body.as_array().and_then(|arr| {
            arr.iter()
                .find(|r| r.get("chain_head").and_then(|h| h.as_bool()) == Some(true))
                .and_then(|r| r.get("receipt_hash"))
                .and_then(|h| h.as_str())
        });
        match head_hex {
            Some(hex) => decode_32(hex).map(Some).ok_or_else(|| {
                SdkError::Wire("chain-head receipt_hash is not 32 hex bytes".into())
            }),
            None => Ok(None),
        }
    }

    /// `GET /api/cell/{cell}` → the receipt-chain head of `cell` acting as an
    /// AGENT (`last_receipt_hash`), or `None` when it has committed no turn.
    ///
    /// This, not [`Self::fetch_chain_head`], is the value a turn whose `agent`
    /// is `cell` must thread as `previous_receipt_hash`. The node admits a
    /// signed turn only when that field equals the agent's own head
    /// (`stage_signed_turn_admission` compares it with
    /// `agent_receipt_head_hash(turn.agent)`), and the node-wide tip is some
    /// other agent's receipt whenever another agent committed since. It is the
    /// same read as `RemoteAgent::agent_receipt_chain_head`.
    ///
    /// A cell the node does not hold is not an error: the node serves the head
    /// for a not-found cell too. See `agent_receipt_head` for what IS one.
    pub async fn fetch_agent_receipt_head(
        &self,
        cell: &CellId,
    ) -> Result<Option<[u8; 32]>, SdkError> {
        let url = format!(
            "{}/api/cell/{}",
            self.base_url,
            dregg_types::hex_encode(cell.as_bytes())
        );
        agent_receipt_head(&self.get_json(&url).await?)
    }

    /// Find the committed turn `turn_hash` on `/api/receipts` and return its
    /// `receipt_hash`. Fail-closed: a committed turn not yet visible (finality /
    /// gossip lag — the Pillar-2 handoff) is an `Err`, never a fabricated hash.
    async fn resolve_receipt_hash(&self, turn_hash: &str) -> Result<[u8; 32], SdkError> {
        let url = format!("{}/api/receipts", self.base_url);
        let body: serde_json::Value = self.get_json(&url).await?;
        let receipt_hex = body
            .as_array()
            .and_then(|arr| {
                arr.iter()
                    .find(|r| r.get("turn_hash").and_then(|t| t.as_str()) == Some(turn_hash))
                    .and_then(|r| r.get("receipt_hash"))
                    .and_then(|h| h.as_str())
            })
            .ok_or_else(|| {
                SdkError::Wire(format!(
                    "committed turn {turn_hash} not yet visible on /api/receipts \
                     (finality/gossip lag)"
                ))
            })?;
        decode_32(receipt_hex)
            .ok_or_else(|| SdkError::Wire("receipt_hash is not 32 bytes of hex".into()))
    }

    /// GET a URL and parse its JSON body, mapping every failure to `SdkError`.
    async fn get_json(&self, url: &str) -> Result<serde_json::Value, SdkError> {
        let resp = self
            .http
            .get(url)
            .send()
            .await
            .map_err(|e| SdkError::Wire(format!("GET {url} failed: {e}")))?;
        if !resp.status().is_success() {
            return Err(SdkError::Wire(format!(
                "GET {url} returned {}",
                resp.status()
            )));
        }
        resp.json()
            .await
            .map_err(|e| SdkError::Wire(format!("parse {url}: {e}")))
    }
}

/// Rebuild a [`Cell`] from a `GET /api/cell/{id}` detail JSON — the crawl-fidelity
/// snapshot (public_key, token, fields, balance, nonce, delegate). Returns `None`
/// if the detail is not a found cell or its key/token are malformed.
fn cell_from_detail(v: &serde_json::Value) -> Option<Cell> {
    if v.get("found").and_then(|f| f.as_bool()) != Some(true) {
        return None;
    }
    let public_key = decode_32(v.get("public_key")?.as_str()?)?;
    let token_id = decode_32(v.get("token_id")?.as_str()?)?;
    let balance = v.get("balance").and_then(|b| b.as_i64()).unwrap_or(0);

    let mut cell = Cell::with_balance(public_key, token_id, balance);
    if let Some(nonce) = v.get("nonce").and_then(|n| n.as_u64()) {
        cell.state.set_nonce(nonce);
    }
    if let Some(fields) = v.get("fields").and_then(|f| f.as_array()) {
        for (i, f) in fields.iter().enumerate() {
            if let Some(felt) = f.as_str().and_then(decode_32) {
                let felt: FieldElement = felt;
                cell.state.set_field(i, felt);
            }
        }
    }
    if let Some(del) = v.get("delegate").and_then(|d| d.as_str()) {
        if let Some(bytes) = decode_32(del) {
            cell.delegate = Some(CellId(bytes));
        }
    }
    // Rebuild the c-list EDGES so an authority read (`has_access`) over the
    // crawled ledger answers IDENTICALLY to a read on the origin box (Pillar-2b).
    // Without this the cell would carry the empty `CapabilitySet::with_balance`
    // starts with, and EVERY `has_access` would read uniformly FALSE — silently
    // revoking every speak-cap / marking every gadget "Discoverable" over the
    // real wire. Each edge is a full serde `CapabilityRef`; a malformed edge is
    // SKIPPED (fail-closed: never fabricate an authority we cannot decode).
    let refs: Vec<CapabilityRef> = v
        .get("capabilities")
        .and_then(|c| c.as_array())
        .map(|arr| {
            arr.iter()
                .filter_map(|e| serde_json::from_value::<CapabilityRef>(e.clone()).ok())
                .collect()
        })
        .unwrap_or_default();
    let tombstones: Vec<u32> = v
        .get("capability_tombstones")
        .and_then(|t| t.as_array())
        .map(|arr| {
            arr.iter()
                .filter_map(|e| e.as_u64().and_then(|n| u32::try_from(n).ok()))
                .collect()
        })
        .unwrap_or_default();
    if !refs.is_empty() || !tombstones.is_empty() {
        // `reconstruct` PRESERVES each cap's original slot and re-derives
        // `next_slot`/tombstones from both planes — the same c-list, not a
        // re-slotted copy.
        cell.capabilities = CapabilitySet::reconstruct(refs, tombstones);
    }
    Some(cell)
}

/// Read `last_receipt_hash` off a `GET /api/cell/{id}` body.
///
/// `null` is a real answer: the agent has no receipt yet, and its first turn
/// threads `None`. An ABSENT field is not that answer, so it is an error. Every
/// node this client talks to serializes the field, `null` included, so a body
/// without it is not a cell view, and reading it as `None` would sign a turn
/// against a head nobody reported.
fn agent_receipt_head(cell_view: &serde_json::Value) -> Result<Option<[u8; 32]>, SdkError> {
    match cell_view.get("last_receipt_hash") {
        Some(serde_json::Value::Null) => Ok(None),
        Some(serde_json::Value::String(hex)) => decode_32(hex).map(Some).ok_or_else(|| {
            SdkError::Wire(format!(
                "cell last_receipt_hash is not 32 hex bytes: {hex:?}"
            ))
        }),
        Some(other) => Err(SdkError::Wire(format!(
            "cell last_receipt_hash is not a hex string: {other}"
        ))),
        None => Err(SdkError::Wire(
            "the cell view carries no last_receipt_hash, so this agent's receipt head is unknown"
                .into(),
        )),
    }
}

/// Decode a 64-char hex string into a 32-byte array. `None` on malformed input.
pub(crate) fn decode_32(s: &str) -> Option<[u8; 32]> {
    let s = s.trim();
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(s.get(i * 2..i * 2 + 2)?, 16).ok()?;
    }
    Some(out)
}

// ───────────────────────── the WorldSink impl (feature-gated) ────────────────

#[cfg(feature = "world-sink")]
pub use sink::NodeWorldSink;

#[cfg(feature = "world-sink")]
mod sink {
    use super::*;
    use deos_js::WorldSink;

    /// A [`deos_js::WorldSink`] over a REMOTE node's HTTP API — the client half of
    /// the in-process `node::deos_host::NodeWorldSink`. `with_ledger` runs the
    /// crawl closure over a freshly-fetched snapshot ledger; `fire_effects`
    /// submits a signed turn and returns the real receipt hash.
    ///
    /// The [`WorldSink`] trait methods are synchronous, so the sink owns a
    /// current-thread tokio [`Runtime`](tokio::runtime::Runtime) it blocks the
    /// async HTTP calls on. Like the in-process sink (which requires a non-worker
    /// thread), it must be driven OFF a tokio worker thread — the remote
    /// inhabitation process is a plain program, not an async task.
    pub struct NodeWorldSink {
        client: NodeHttpClient,
        cipherclerk: AgentCipherclerk,
        agent: CellId,
        federation_id: [u8; 32],
        rt: tokio::runtime::Runtime,
    }

    impl NodeWorldSink {
        /// Attach to the node at `base_url`, committing turns AS `cipherclerk`'s
        /// default cell, signed over `federation_id` (the node's executor
        /// federation id — see [`NodeHttpClient::fetch_executor_federation_id`]).
        pub fn new(
            base_url: impl Into<String>,
            cipherclerk: AgentCipherclerk,
            federation_id: [u8; 32],
        ) -> Result<Self, SdkError> {
            let default_token_id = *blake3::hash(b"default").as_bytes();
            let agent = CellId::derive_raw(&cipherclerk.public_key().0, &default_token_id);
            let rt = tokio::runtime::Builder::new_current_thread()
                .enable_all()
                .build()
                .map_err(|e| SdkError::Wire(format!("build sink runtime: {e}")))?;
            Ok(NodeWorldSink {
                client: NodeHttpClient::new(base_url),
                cipherclerk,
                agent,
                federation_id,
                rt,
            })
        }

        /// The agent cell every turn from this sink binds (the cipherclerk's
        /// default cell).
        pub fn agent(&self) -> CellId {
            self.agent
        }

        /// The light HTTP client underneath (for direct reads).
        pub fn client(&self) -> &NodeHttpClient {
            &self.client
        }
    }

    impl WorldSink for NodeWorldSink {
        fn with_ledger(&self, f: &mut dyn FnMut(&Ledger)) {
            // Fail-soft on the read, exactly like the world-bridge crawl: a fetch
            // fault means `f` is NOT run (a degraded read of nothing — never a
            // substitute world).
            if let Ok(ledger) = self.rt.block_on(self.client.fetch_ledger_snapshot()) {
                f(&ledger);
            }
        }

        fn fire_effects(
            &mut self,
            agent: CellId,
            method: &str,
            effects: Vec<Effect>,
        ) -> Result<[u8; 32], String> {
            self.rt
                .block_on(self.client.submit_turn(
                    &self.cipherclerk,
                    agent,
                    method,
                    effects,
                    &self.federation_id,
                ))
                .map_err(|e| e.to_string())
        }

        // `mint_open_cell` keeps the trait default (an `Err`): minting an open
        // cell is a privileged host-ledger op, not reachable over the signed-turn
        // ingress — a remote client cannot mint. (The in-process host sink is the
        // one that implements it.)
    }
}

#[cfg(all(test, feature = "world-sink", feature = "test-support"))]
mod tests {
    use super::*;
    use crate::test_support::{TestNode, signature_gated_cell};

    /// BOTH poles on ONE node:
    ///   * `fire_effects` commits a SetField on the agent cell and `with_ledger`
    ///     reads the new value back (the round-trip); and
    ///   * an over-reaching effect (a SetField on a foreign signature-gated cell)
    ///     is REFUSED by the node executor — an `Err` out of `fire_effects`, not a
    ///     sink-side rejection.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn fire_and_crawl_round_trip_then_executor_refuses_overreach() {
        // The agent (the client's identity) and a FOREIGN owner whose cell the
        // agent cannot write.
        let clerk = AgentCipherclerk::new();
        let foreign = AgentCipherclerk::new();
        let agent_pk = clerk.public_key().0;
        let foreign_pk = foreign.public_key().0;

        // A distinct node identity (the executor fed id is blake3 of it) — the
        // client resolves it off `/status`, so it need not equal the agent key.
        let node_public_key = *blake3::hash(b"round-trip-test-node").as_bytes();
        let (mut node, agent) = TestNode::genesis(node_public_key, agent_pk, 1_000_000);
        let fed_id = node.fed_id();

        // A foreign cell whose set_state REQUIRES the foreign owner's signature —
        // the agent holds neither the key nor a capability, so a SetField on it is
        // an over-reach the executor refuses.
        let foreign_id = node.insert_cell(signature_gated_cell(foreign_pk, 1_000_000));

        let spawned = node.spawn().await;
        let base_url = spawned.base_url().to_string();

        // Drive the SINK off the tokio runtime (a plain OS thread): the sink owns
        // its own current-thread runtime and blocks on it, exactly as the real
        // (non-async) inhabitation process would.
        let handle = std::thread::spawn(move || {
            let mut sink = NodeWorldSink::new(base_url, clerk, fed_id).expect("build sink");
            use deos_js::WorldSink;

            // ── POLE A: commit + read-back round-trip. ──
            let slot = 3usize;
            let new_value: FieldElement = {
                let mut v = [0u8; 32];
                v[0] = 42;
                v
            };
            // Just the SetField: the executor bumps the agent nonce once per turn
            // (execute.rs:574), so no explicit IncrementNonce is needed (that would
            // double-bump).
            let rh = sink
                .fire_effects(
                    agent,
                    "set_slot",
                    vec![Effect::SetField {
                        cell: agent,
                        index: slot as u64,
                        value: new_value,
                    }],
                )
                .expect("honest SetField must commit");
            assert_ne!(
                rh, [0u8; 32],
                "committed turn must carry a real receipt hash"
            );

            // with_ledger reads the SNAPSHOT back: the new field value landed.
            let mut read_value: Option<FieldElement> = None;
            let mut read_nonce = 0u64;
            sink.with_ledger(&mut |l| {
                if let Some(cell) = l.get(&agent) {
                    read_value = Some(cell.state.fields[slot]);
                    read_nonce = cell.state.nonce();
                }
            });
            assert_eq!(
                read_value,
                Some(new_value),
                "with_ledger must read back the committed field value"
            );
            assert_eq!(
                read_nonce, 1,
                "the nonce bump must be visible in the snapshot"
            );

            // ── POLE B: the node EXECUTOR refuses an over-reach (not the sink). ──
            let refused = sink.fire_effects(
                agent,
                "steal",
                vec![Effect::SetField {
                    cell: foreign_id,
                    index: 0,
                    value: new_value,
                }],
            );
            let err = refused.expect_err("over-reaching SetField must be refused");
            assert!(
                err.contains("refused by node"),
                "refusal must come from the node executor, got: {err}"
            );

            // The refused turn left NO trace: the foreign cell is unchanged.
            let mut foreign_slot0: Option<FieldElement> = None;
            sink.with_ledger(&mut |l| {
                if let Some(c) = l.get(&foreign_id) {
                    foreign_slot0 = Some(c.state.fields[0]);
                }
            });
            assert_eq!(
                foreign_slot0,
                Some([0u8; 32]),
                "a refused over-reach must not mutate the foreign cell"
            );
        });
        handle.join().expect("sink thread");
    }

    /// PILLAR-2b over the REAL wire: a cell that HOLDS a capability to a target
    /// must read `has_access(target) == true` after being crawled through the
    /// remote explorer surface (`/api/cells` + `/api/cell/{id}`), and an UNHELD
    /// target must read `false`. This is the test that the in-process adapter
    /// dodged — it exercises the actual `fetch_ledger_snapshot` → `cell_from_detail`
    /// c-list reconstruction. Before the fix `cell_from_detail` rebuilt an EMPTY
    /// `CapabilitySet`, so BOTH poles read `false` (total silence / everything
    /// Discoverable); now the held edge crosses the wire and reconstructs.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn crawl_reconstructs_the_capability_clist_over_the_wire() {
        use crate::test_support::default_token_id;
        use dregg_cell::AuthRequired;

        // A holder cell that HOLDS a signature-gated cap to `target`; `unheld` is
        // a target the holder has NO cap to.
        let holder_pk = [7u8; 32];
        let target = CellId::derive_raw(&[9u8; 32], &default_token_id());
        let unheld = CellId::derive_raw(&[11u8; 32], &default_token_id());

        let node_public_key = *blake3::hash(b"clist-crawl-node").as_bytes();
        let (mut node, _agent) = TestNode::genesis(node_public_key, [1u8; 32], 0);

        let mut holder = Cell::with_balance(holder_pk, default_token_id(), 0);
        holder
            .capabilities
            .grant(target, AuthRequired::Signature)
            .expect("grant cap to target");
        // Sanity on the ORIGIN cell: the held cap reads reachable here.
        assert!(holder.capabilities.holds_unfrozen_ref_to(&target));
        assert!(!holder.capabilities.holds_unfrozen_ref_to(&unheld));
        let holder_id = node.insert_cell(holder);

        let spawned = node.spawn().await;
        let client = NodeHttpClient::new(spawned.base_url().to_string());

        // The CRAWL: rebuild the snapshot ledger purely from the HTTP surface.
        let ledger = client
            .fetch_ledger_snapshot()
            .await
            .expect("crawl the remote ledger");
        let crawled = ledger
            .get(&holder_id)
            .expect("holder cell is present in the crawled ledger");

        // The two poles over the REAL wire.
        assert!(
            crawled.capabilities.holds_unfrozen_ref_to(&target),
            "a HELD cap must read reachable over the crawled ledger (Pillar-2b) \
             — this was FALSE before the c-list edges crossed the wire"
        );
        assert!(
            !crawled.capabilities.holds_unfrozen_ref_to(&unheld),
            "an UNHELD cap must NOT read reachable (fail-closed, no fabricated authority)"
        );
    }
}

/// The federation-id fetch against the REAL-executor [`TestNode`]. It needs
/// only `test-support`, not the SpiderMonkey `world-sink` feature the sink
/// tests above need, so a plain `--features test-support` run reaches it.
#[cfg(all(test, feature = "test-support"))]
mod federation_id_tests {
    use super::*;
    use crate::test_support::TestNode;

    /// The federation-id fetch helper resolves a solo node's executor id
    /// (`blake3(node_public_key)`) off `/status`.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn fetch_executor_federation_id_resolves_solo_node() {
        let node_public_key = *blake3::hash(b"some-node-key").as_bytes();
        let (node, _agent) = TestNode::genesis(node_public_key, [1u8; 32], 0);
        let fed_id = node.fed_id();
        let spawned = node.spawn().await;

        let client = NodeHttpClient::new(spawned.base_url().to_string());
        let got = client
            .fetch_executor_federation_id()
            .await
            .expect("fetch fed id");
        assert_eq!(
            got, fed_id,
            "solo executor fed id = blake3(node public key)"
        );
        assert_eq!(got, *blake3::hash(&node_public_key).as_bytes());
    }

    /// A configured committee of one — the chain `dregg-node init` mints —
    /// still says `"solo"` on `/status`, but its executor signs under the
    /// committee-derived id. The fetch must return that id, not
    /// `blake3(public_key)`: a node built this way vetoed every client turn
    /// signed over the latter.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn fetch_executor_federation_id_reads_a_configured_committee_of_one() {
        let node_public_key = *blake3::hash(b"init-minted-node-key").as_bytes();
        let committee_id = *blake3::hash(b"committee-derived federation id").as_bytes();
        let (node, _agent) = TestNode::genesis(node_public_key, [1u8; 32], 0);
        let node = node.with_configured_committee(committee_id);
        let spawned = node.spawn().await;

        let client = NodeHttpClient::new(spawned.base_url().to_string());
        let got = client
            .fetch_executor_federation_id()
            .await
            .expect("fetch fed id");
        assert_eq!(got, committee_id);
        assert_eq!(got, spawned.fed_id(), "the id the executor verifies under");
        assert_ne!(got, *blake3::hash(&node_public_key).as_bytes());
    }
}

#[cfg(test)]
mod agent_receipt_head_tests {
    use super::agent_receipt_head;

    #[test]
    fn null_is_a_fresh_agent_and_hex_is_its_head() {
        let fresh = serde_json::json!({"found": true, "last_receipt_hash": null});
        assert_eq!(agent_receipt_head(&fresh).expect("null is an answer"), None);
        // A cell the node does not hold still has a head once it has acted.
        let acted = serde_json::json!({"found": false, "last_receipt_hash": "ab".repeat(32)});
        assert_eq!(agent_receipt_head(&acted).expect("hex"), Some([0xab; 32]));
    }

    #[test]
    fn an_absent_or_malformed_head_is_an_error_not_none() {
        for body in [
            serde_json::json!({"found": true, "nonce": 3}),
            serde_json::json!({"error": "not found"}),
            serde_json::json!({"last_receipt_hash": "ab".repeat(31)}),
            serde_json::json!({"last_receipt_hash": "zz".repeat(32)}),
            serde_json::json!({"last_receipt_hash": 7}),
        ] {
            assert!(
                agent_receipt_head(&body).is_err(),
                "{body} must not read as a head"
            );
        }
    }
}
