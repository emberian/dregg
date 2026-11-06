//! # `grain-session`: a stranger verifies a real Claude Code session, R0 through R3.
//!
//! Initiative 10. The ladder is not reimplemented here. R0-R2 are
//! [`grain_verify::GrainAttestation::verify_r2_for_renter`], R3's accept is the Lean
//! `Dregg2.Grain.R3Verify.r3VerifyCore` reached through [`grain_verify::r3_verify_aggregate`],
//! and the kernel turns are `grain_turn::ToolGatewayMinter`'s real executor turns. This crate is
//! the adapter between a `cv export` and that ladder, plus the checks that tie the two together:
//!
//! 1. **Projection** ([`project_exports`]): the same projection demo (b) published
//!    (`demo/datalog-governance/project_transcript.py`): per call the agent, its per-transcript
//!    sequence number, tool name, `tool_use` id, timestamp, the file path of the file tools and
//!    the spawned id of an `Agent` call. Nothing else is public. Each call additionally carries a
//!    **hiding commitment** ([`call_commit`]) to its full input and result under a per-call salt
//!    derived from a secret the session owner keeps; the owner can open any one call later
//!    without opening the rest.
//! 2. **Windows** ([`window_label`]): calls are grouped in order into windows of `W`. Each window
//!    is ONE admitted dregg-agent action whose label carries the window's Blake3-MMR root over its
//!    call leaves, so the executor turn the minter commits for it witnesses that root in
//!    `ACTION_SLOT`. Window 0's label also carries the renter's genesis nonce, so the nonce sits
//!    inside the signed chain's first receipt, not only beside it.
//! 3. **Verification** ([`verify_bundle`]): R0+R1+R2 through grain-verify; the renter statement's
//!    signature under the renter key the verifier pins; the receipts and the calls agree window
//!    by window (rewrite, reorder, truncation and an added, unreceipted call are each refused);
//!    R3 through the Lean core against the renter-countersigned 8-felt head.
//!
//! ## What a passing verify means, and what it does not
//!
//! A pass means the following. The calls shown are exactly the calls the producer committed, in that order, with none
//! dropped, added, reordered or altered. Each is bound to a committed executor turn through its window's root.
//! The renter's key acknowledged that receipt head and that aggregate head. The folded history from the
//! genesis anchor to that head verifies, decided by the Lean core under the carried
//! `EngineSound` floor.
//!
//! What it does NOT mean: that the transcript is what happened. For a replayed session, the
//! producer that wrote the transcript also minted the receipts; the verifier trusts the transcript
//! writer (live: the `cv hook receipt` commit-before-forward log), the host's R2 manifest (it is
//! the host's own list of turn hashes; nothing here re-executes or opens a turn), `EngineSound`
//! (which includes the leaf-to-executor-step correspondence, not only FRI), the verifier binary
//! and its linked Lean archive, and its own key custody and VK. The folded head is the
//! EffectVM-model head (see `grain_turn::finalize_session_threaded` for exactly what it carries;
//! the nonce counts field writes instead of turns). A host that shows two renters two histories
//! is not caught here (no witnesses). Nothing here says the model's outputs or the tools' effects
//! were true or wanted.

use std::collections::BTreeMap;
use std::path::Path;

use dregg_agent::receipt::verify_signature;
use dregg_circuit_prove::ivc_turn_chain::{RecursionVk, SEG_ANCHOR_WIDTH, WholeChainProofBytes};
use grain_verify::{GrainAttestation, GrainVerifyError, R2Verified, R3Error, R3Verified};
use serde::{Deserialize, Serialize};

#[cfg(feature = "prover")]
pub mod produce;
pub mod tamper;

/// Bundle format version.
pub const BUNDLE_VERSION: u32 = 1;
/// Domain of [`call_commit`].
pub const CALL_COMMIT_DOMAIN: &[u8] = b"dregg-cc-call-commit-v1";
/// Domain of [`call_leaf`].
pub const CALL_LEAF_DOMAIN: &[u8] = b"dregg-cc-call-leaf-v1";
/// Domain of the per-call salt derivation ([`call_salt`]).
pub const CALL_SALT_DOMAIN: &str = "dregg-cc-call-salt-v1";
/// Domain of [`RenterStatement::signing_bytes`].
pub const STATEMENT_DOMAIN: &[u8] = b"dregg-cc-session-statement-v1";
/// The tools whose file path demo (b)'s projection keeps.
pub const FILE_TOOLS: [&str; 5] = ["Read", "Write", "Edit", "MultiEdit", "NotebookEdit"];

// ─────────────────────────────────────────────────────────────────────────────
// Projection
// ─────────────────────────────────────────────────────────────────────────────

/// One tool call as published: demo (b)'s projection fields plus the hiding commitment.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CallPublic {
    /// `root` for the session itself, else the sub-agent id.
    pub agent: String,
    /// Position of the call within its transcript (0-based).
    pub seq: u64,
    /// The tool name.
    pub tool: String,
    /// The `tool_use` id.
    pub use_id: String,
    /// The message timestamp the call rode in.
    pub ts: String,
    /// The file path argument of a file tool.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub path: Option<String>,
    /// For an `Agent` call, the spawned agent id read from its result.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub spawned: Option<String>,
    /// [`call_commit`] over the full input and result (hex).
    pub commit: String,
}

/// One call with the private material its commitment covers (never published).
#[derive(Clone, Debug)]
pub struct CallPrivate {
    /// The published part (with `commit` empty until [`commit_calls`] fills it).
    pub public: CallPublic,
    /// The `tool_use` input, canonical JSON.
    pub input: String,
    /// The `tool_result` block, canonical JSON (`null` if the transcript has none).
    pub result: String,
}

/// Canonical JSON: object keys sorted at every depth, no whitespace. The commitment must not
/// depend on serde_json's map order (the workspace may enable `preserve_order`).
pub fn canonical_json(v: &serde_json::Value) -> String {
    fn go(v: &serde_json::Value, out: &mut String) {
        match v {
            serde_json::Value::Object(m) => {
                let sorted: BTreeMap<&String, &serde_json::Value> = m.iter().collect();
                out.push('{');
                for (i, (k, val)) in sorted.into_iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    out.push_str(&serde_json::to_string(k).expect("a string serializes"));
                    out.push(':');
                    go(val, out);
                }
                out.push('}');
            }
            serde_json::Value::Array(a) => {
                out.push('[');
                for (i, val) in a.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    go(val, out);
                }
                out.push(']');
            }
            other => out.push_str(&serde_json::to_string(other).expect("a scalar serializes")),
        }
    }
    let mut s = String::new();
    go(v, &mut s);
    s
}

/// The spawned agent id in an `Agent` result: the first `agentId: a<hex, 8 or more>` (the
/// python projection's `agentId: (a[0-9a-f]{8,})`, greedy).
fn spawned_id(result_text: &str) -> Option<String> {
    let mut rest = result_text;
    while let Some(i) = rest.find("agentId: a") {
        let tail = &rest[i + "agentId: ".len()..];
        let hex: String = tail[1..]
            .chars()
            .take_while(|c| c.is_ascii_digit() || ('a'..='f').contains(c))
            .collect();
        if hex.len() >= 8 {
            return Some(format!("a{hex}"));
        }
        rest = &rest[i + 1..];
    }
    None
}

/// The text of a `tool_result` block's content, as the python projection reads it.
fn result_text(block: &serde_json::Value) -> String {
    match block.get("content") {
        Some(serde_json::Value::String(s)) => s.clone(),
        Some(serde_json::Value::Array(items)) => items
            .iter()
            .filter_map(|x| x.as_object())
            .map(|x| {
                x.get("text")
                    .and_then(|t| t.as_str())
                    .unwrap_or("")
                    .to_string()
            })
            .collect::<Vec<_>>()
            .join(" "),
        _ => String::new(),
    }
}

/// Project ONE exported transcript (`cv export <id> --format json --redact`).
pub fn project_export(agent: &str, export: &serde_json::Value) -> Vec<CallPrivate> {
    let empty = Vec::new();
    let messages = export
        .get("messages")
        .and_then(|m| m.as_array())
        .unwrap_or(&empty);
    let mut results: BTreeMap<String, serde_json::Value> = BTreeMap::new();
    for m in messages {
        for p in m
            .get("content")
            .and_then(|c| c.as_array())
            .unwrap_or(&empty)
        {
            if p.get("type").and_then(|t| t.as_str()) == Some("tool_result") {
                if let Some(id) = p.get("tool_use_id").and_then(|t| t.as_str()) {
                    results.insert(id.to_string(), p.clone());
                }
            }
        }
    }
    let mut out = Vec::new();
    for m in messages {
        let ts = m
            .get("timestamp")
            .and_then(|t| t.as_str())
            .unwrap_or("")
            .to_string();
        for p in m
            .get("content")
            .and_then(|c| c.as_array())
            .unwrap_or(&empty)
        {
            if p.get("type").and_then(|t| t.as_str()) != Some("tool_use") {
                continue;
            }
            let tool = p
                .get("name")
                .and_then(|n| n.as_str())
                .unwrap_or("")
                .to_string();
            let use_id = p
                .get("id")
                .and_then(|n| n.as_str())
                .unwrap_or("")
                .to_string();
            let input = p.get("input").cloned().unwrap_or(serde_json::Value::Null);
            let path = if FILE_TOOLS.contains(&tool.as_str()) {
                input
                    .get("file_path")
                    .or_else(|| input.get("notebook_path"))
                    .and_then(|v| v.as_str())
                    .map(str::to_string)
            } else {
                None
            };
            let result = results.get(&use_id).cloned();
            let spawned = if tool == "Agent" {
                result.as_ref().and_then(|r| spawned_id(&result_text(r)))
            } else {
                None
            };
            out.push(CallPrivate {
                public: CallPublic {
                    agent: agent.to_string(),
                    seq: out.len() as u64,
                    tool,
                    use_id,
                    ts: ts.clone(),
                    path,
                    spawned,
                    commit: String::new(),
                },
                input: canonical_json(&input),
                result: canonical_json(&result.unwrap_or(serde_json::Value::Null)),
            });
        }
    }
    out
}

/// Project an export directory laid out as demo (b)'s: `root.json` and `sub/agent-<id>.json`,
/// root first, then the sub-agents in file-name order.
pub fn project_exports(dir: &Path) -> Result<Vec<CallPrivate>, String> {
    let read = |p: &Path| -> Result<serde_json::Value, String> {
        let bytes = std::fs::read(p).map_err(|e| format!("{}: {e}", p.display()))?;
        serde_json::from_slice(&bytes).map_err(|e| format!("{}: {e}", p.display()))
    };
    let mut all = project_export("root", &read(&dir.join("root.json"))?);
    let sub = dir.join("sub");
    let mut names: Vec<String> = std::fs::read_dir(&sub)
        .map_err(|e| format!("{}: {e}", sub.display()))?
        .filter_map(|e| e.ok())
        .map(|e| e.file_name().to_string_lossy().into_owned())
        .filter(|n| n.starts_with("agent-") && n.ends_with(".json"))
        .collect();
    names.sort();
    for n in names {
        let agent = &n["agent-".len()..n.len() - ".json".len()];
        all.extend(project_export(agent, &read(&sub.join(&n))?));
    }
    Ok(all)
}

// ─────────────────────────────────────────────────────────────────────────────
// Commitments, leaves, windows
// ─────────────────────────────────────────────────────────────────────────────

/// The per-call salt: keyed BLAKE3 of the owner's 32-byte secret over the call's identity. One
/// secret opens everything; revealing one salt opens one call.
pub fn call_salt(owner_secret: &[u8; 32], agent: &str, use_id: &str) -> [u8; 32] {
    let key = blake3::derive_key(CALL_SALT_DOMAIN, owner_secret);
    let mut h = blake3::Hasher::new_keyed(&key);
    h.update(&(agent.len() as u64).to_le_bytes());
    h.update(agent.as_bytes());
    h.update(&(use_id.len() as u64).to_le_bytes());
    h.update(use_id.as_bytes());
    *h.finalize().as_bytes()
}

/// The hiding commitment to one call's full input and result.
pub fn call_commit(salt: &[u8; 32], input: &str, result: &str) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(CALL_COMMIT_DOMAIN);
    h.update(salt);
    h.update(&(input.len() as u64).to_le_bytes());
    h.update(input.as_bytes());
    h.update(&(result.len() as u64).to_le_bytes());
    h.update(result.as_bytes());
    *h.finalize().as_bytes()
}

/// Fill every call's `commit` under the owner's secret.
pub fn commit_calls(calls: &mut [CallPrivate], owner_secret: &[u8; 32]) {
    for c in calls {
        let salt = call_salt(owner_secret, &c.public.agent, &c.public.use_id);
        c.public.commit = hex::encode(call_commit(&salt, &c.input, &c.result));
    }
}

fn put_str(h: &mut blake3::Hasher, s: &str) {
    h.update(&(s.len() as u64).to_le_bytes());
    h.update(s.as_bytes());
}

fn put_opt(h: &mut blake3::Hasher, s: &Option<String>) {
    match s {
        None => {
            h.update(&[0u8]);
        }
        Some(s) => {
            h.update(&[1u8]);
            put_str(h, s);
        }
    }
}

/// The MMR leaf of one published call: every published field, length-prefixed.
pub fn call_leaf(c: &CallPublic) -> Result<[u8; 32], String> {
    let commit = parse32(&c.commit).map_err(|e| format!("call {}: commit {e}", c.use_id))?;
    let mut h = blake3::Hasher::new();
    h.update(CALL_LEAF_DOMAIN);
    put_str(&mut h, &c.agent);
    h.update(&c.seq.to_le_bytes());
    put_str(&mut h, &c.tool);
    put_str(&mut h, &c.use_id);
    put_str(&mut h, &c.ts);
    put_opt(&mut h, &c.path);
    put_opt(&mut h, &c.spawned);
    h.update(&commit);
    Ok(*h.finalize().as_bytes())
}

/// The Blake3 MMR root over leaves (the same forest `grain_turn::grain_history_root` uses).
pub fn mmr_root(leaves: &[[u8; 32]]) -> [u8; 32] {
    dregg_query::Mmr::from_values(dregg_query::Blake3Mmr, leaves.to_vec()).root()
}

/// The service name of window `k` — the admitted action is `invoke:<this>`, so the minter's
/// `action_commit(label, cost)` puts it in the executor turn's `ACTION_SLOT`. Window 0 carries
/// the renter's genesis nonce.
pub fn window_service(
    k: usize,
    n_calls: usize,
    root: &[u8; 32],
    nonce: Option<&[u8; 32]>,
) -> String {
    match nonce {
        Some(n) => format!(
            "ccw:{k}:{n_calls}:{}:nonce:{}",
            hex::encode(root),
            hex::encode(n)
        ),
        None => format!("ccw:{k}:{n_calls}:{}", hex::encode(root)),
    }
}

/// The receipt `action` label window `k` must carry.
pub fn window_label(k: usize, n_calls: usize, root: &[u8; 32], nonce: Option<&[u8; 32]>) -> String {
    format!("invoke:{}", window_service(k, n_calls, root, nonce))
}

/// The windows over `n` calls of width `w`: `(start, len)` in order.
pub fn windows(n: usize, w: usize) -> Vec<(usize, usize)> {
    assert!(w > 0, "window width must be positive");
    (0..n.div_ceil(w))
        .map(|k| (k * w, w.min(n - k * w)))
        .collect()
}

/// The expected receipt labels for a call list, with the window roots.
pub fn expected_labels(
    calls: &[CallPublic],
    w: usize,
    nonce: &[u8; 32],
) -> Result<Vec<String>, String> {
    let leaves = calls.iter().map(call_leaf).collect::<Result<Vec<_>, _>>()?;
    Ok(windows(leaves.len(), w)
        .into_iter()
        .enumerate()
        .map(|(k, (s, len))| {
            let root = mmr_root(&leaves[s..s + len]);
            window_label(k, len, &root, (k == 0).then_some(nonce))
        })
        .collect())
}

// ─────────────────────────────────────────────────────────────────────────────
// The bundle
// ─────────────────────────────────────────────────────────────────────────────

/// What the renter key signs besides the R1 checkpoint: the calls, the receipt head, the R3
/// anchors and the VK, as one statement.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RenterStatement {
    /// The session id.
    pub session: String,
    /// The renter's genesis nonce.
    pub renter_nonce: [u8; 32],
    /// Number of published calls.
    pub n_calls: u64,
    /// MMR root over all call leaves.
    pub calls_root: [u8; 32],
    /// Window width.
    pub window: u64,
    /// The receipt signer (the host's receipt key).
    pub receipt_signer: [u8; 32],
    /// Number of receipts (= windows).
    pub n_receipts: u64,
    /// The receipt chain tip.
    pub receipt_head: [u8; 32],
    /// The R3 aggregate's genesis anchor (8 lanes).
    pub r3_genesis: [u32; SEG_ANCHOR_WIDTH],
    /// The R3 aggregate's committed head (8 lanes) — the anchored head the Lean core compares.
    pub r3_head: [u32; SEG_ANCHOR_WIDTH],
    /// Number of finalized legs folded.
    pub r3_legs: u32,
    /// The VK anchor the renter accepted (minted by setup, or taken from the producer).
    pub r3_vk: [u8; 32],
}

impl RenterStatement {
    /// The domain-separated bytes the renter signs.
    pub fn signing_bytes(&self) -> Vec<u8> {
        let mut v = Vec::new();
        v.extend_from_slice(STATEMENT_DOMAIN);
        v.extend_from_slice(&(self.session.len() as u64).to_le_bytes());
        v.extend_from_slice(self.session.as_bytes());
        v.extend_from_slice(&self.renter_nonce);
        v.extend_from_slice(&self.n_calls.to_le_bytes());
        v.extend_from_slice(&self.calls_root);
        v.extend_from_slice(&self.window.to_le_bytes());
        v.extend_from_slice(&self.receipt_signer);
        v.extend_from_slice(&self.n_receipts.to_le_bytes());
        v.extend_from_slice(&self.receipt_head);
        for l in self.r3_genesis.iter().chain(self.r3_head.iter()) {
            v.extend_from_slice(&l.to_le_bytes());
        }
        v.extend_from_slice(&self.r3_legs.to_le_bytes());
        v.extend_from_slice(&self.r3_vk);
        v
    }
}

/// The published bundle (`bundle.json`; the aggregate rides next to it as `aggregate.bin`).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Bundle {
    /// [`BUNDLE_VERSION`].
    pub version: u32,
    /// The session id.
    pub session: String,
    /// Window width.
    pub window: u64,
    /// Every published call, in order.
    pub calls: Vec<CallPublic>,
    /// The receipt chain with its R1 genesis pin and (once countersigned) the checkpoint.
    pub attestation: GrainAttestation,
    /// The executor's committed-turn manifest (hex) — R2's link target.
    pub manifest: Vec<String>,
    /// The statement the renter signs.
    pub statement: RenterStatement,
    /// The renter's signature over [`RenterStatement::signing_bytes`] (hex; empty until signed).
    #[serde(default)]
    pub statement_sig: String,
    /// The R3 aggregate (`WholeChainProofBytes` postcard), hex. Kept inline so one file is the bundle.
    pub aggregate: String,
    /// The head opening: the session's last committed grain cell (the executor's own `Cell`).
    pub last_cell: dregg_cell::Cell,
    /// The EffectVM model nonce the folded head carries (see `grain_turn::session_model_nonce`).
    pub model_nonce: u64,
    /// The executor's receipt-hash log for the grain cell (hex), whose prefix root the last cell
    /// binds at `HISTORY_ROOT_SLOT`.
    pub executor_receipts: Vec<String>,
}

impl Bundle {
    /// Load `bundle.json`.
    pub fn load(path: &Path) -> Result<Bundle, String> {
        let bytes = std::fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?;
        serde_json::from_slice(&bytes).map_err(|e| format!("{}: {e}", path.display()))
    }
    /// Write `bundle.json`.
    pub fn save(&self, path: &Path) -> Result<(), String> {
        let s = serde_json::to_string_pretty(self).map_err(|e| e.to_string())?;
        std::fs::write(path, s + "\n").map_err(|e| format!("{}: {e}", path.display()))
    }
}

/// The renter side: countersign the R1 checkpoint and the statement with the renter's seed. The
/// renter supplies its OWN nonce and its OWN VK anchor (from `setup`); the statement is rewritten
/// to name that VK, and signing is refused if the bundle names another nonce or its aggregate does
/// not verify against that VK. (What the renter cannot check here, it does not sign blind: the
/// receipt labels are recomputed from the calls before signing.)
pub fn countersign(
    bundle: &mut Bundle,
    renter_seed: [u8; 32],
    nonce: &[u8; 32],
    vk: &[u8; 32],
) -> Result<[u8; 32], String> {
    if &bundle.statement.renter_nonce != nonce {
        return Err("the bundle names a genesis nonce that is not yours; refusing to sign".into());
    }
    let labels = expected_labels(&bundle.calls, bundle.window as usize, nonce)?;
    let actions: Vec<&String> = bundle
        .attestation
        .report
        .receipts
        .iter()
        .map(|r| &r.action)
        .collect();
    if labels.iter().collect::<Vec<_>>() != actions {
        return Err("the receipts do not commit the calls shown; refusing to sign".into());
    }
    let agg = hex::decode(&bundle.aggregate).map_err(|e| e.to_string())?;
    dregg_circuit_prove::ivc_turn_chain::verify_whole_chain_proof_bytes(&agg, &RecursionVk(*vk))
        .map_err(|e| {
            format!("the aggregate does not verify against your VK; refusing to sign: {e}")
        })?;
    bundle.statement.r3_vk = *vk;
    let cp = bundle
        .attestation
        .checkpoint_to_countersign()
        .ok_or("the chain has no tip to countersign")?;
    let cs = grain_verify::countersign_checkpoint(renter_seed, cp);
    let signer = dregg_agent::receipt::ReceiptSigner::from_seed(renter_seed);
    bundle.statement_sig = hex::encode(signer.sign_raw(&bundle.statement.signing_bytes()));
    bundle.attestation.checkpoint = Some(cs);
    Ok(signer.public())
}

/// The grain cell's `calls_made` slot (`dregg_sdk::CALLS_MADE_SLOT`).
const CALLS_MADE: usize = 4;

/// `dregg_cell::program::field_from_u64`: big-endian in the low 8 bytes.
fn field_u64(v: u64) -> [u8; 32] {
    let mut f = [0u8; 32];
    f[24..].copy_from_slice(&v.to_be_bytes());
    f
}

/// Parse 64 hex chars.
pub fn parse32(s: &str) -> Result<[u8; 32], String> {
    let v = hex::decode(s.trim()).map_err(|e| format!("not hex: {e}"))?;
    v.try_into().map_err(|_| "not 32 bytes".to_string())
}

// ─────────────────────────────────────────────────────────────────────────────
// Verification
// ─────────────────────────────────────────────────────────────────────────────

/// Why a bundle was refused. Each variant names the rung that bit.
#[derive(Debug)]
pub enum Refusal {
    /// Malformed bundle.
    Malformed(String),
    /// The statement is not signed by the pinned renter key.
    StatementSignature,
    /// The statement names a different genesis nonce than the verifier's.
    StatementNonce,
    /// R0/R1/R2 refused (grain-verify).
    Ladder(GrainVerifyError),
    /// The renter's checkpoint does not cover the whole chain.
    CheckpointNotFinal { acknowledged: u64, shown: u64 },
    /// A statement field disagrees with what the bundle shows.
    StatementMismatch(&'static str),
    /// The number of receipts is not the number of windows the calls make.
    WindowCount { receipts: usize, windows: usize },
    /// Window `k`'s receipt does not commit the calls shown for it.
    WindowMismatch { window: usize },
    /// R3 refused (the Lean-proven decision, or its wire/link).
    R3(R3Error),
    /// The R2 links are not the manifest, in order, once each.
    LinksNotManifest,
    /// The folded head does not open to the published last cell under the manifest's turn hashes.
    HeadOpening(&'static str),
}

impl std::fmt::Display for Refusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Refusal::Malformed(e) => write!(f, "REFUSED (malformed bundle): {e}"),
            Refusal::StatementSignature => {
                write!(
                    f,
                    "REFUSED (R1): the session statement is not signed by your renter key"
                )
            }
            Refusal::StatementNonce => {
                write!(
                    f,
                    "REFUSED (R1): the statement names a genesis nonce that is not yours"
                )
            }
            Refusal::Ladder(e) => write!(f, "REFUSED (R0-R2, grain-verify): {e}"),
            Refusal::CheckpointNotFinal {
                acknowledged,
                shown,
            } => write!(
                f,
                "REFUSED (R1): your checkpoint acknowledges {acknowledged} receipts, the bundle shows {shown}"
            ),
            Refusal::StatementMismatch(w) => {
                write!(
                    f,
                    "REFUSED: the signed statement's {w} disagrees with the bundle"
                )
            }
            Refusal::WindowCount { receipts, windows } => write!(
                f,
                "REFUSED (non-omission): {receipts} receipted windows, the calls shown make {windows}"
            ),
            Refusal::WindowMismatch { window } => write!(
                f,
                "REFUSED (non-omission): window {window}'s receipt does not commit the calls shown for it \
                 (a call was rewritten, reordered, dropped or added)"
            ),
            Refusal::R3(e) => write!(f, "REFUSED (R3, Lean r3VerifyCore): {e}"),
            Refusal::LinksNotManifest => write!(
                f,
                "REFUSED (R2): the receipts' turn links are not the manifest in order, once each"
            ),
            Refusal::HeadOpening(w) => write!(f, "REFUSED (R3 head opening): {w}"),
        }
    }
}

/// What a stranger learns from a passing [`verify_bundle`].
#[derive(Debug)]
pub struct Accepted {
    /// R0-R2 (receipts, linked turns).
    pub ladder: R2Verified,
    /// Calls bound.
    pub calls: usize,
    /// Windows (receipts, executor turns).
    pub windows: usize,
    /// R3 (Lean accept).
    pub r3: R3Verified,
}

/// **The stranger's check.** `renter_pub`, `nonce` and `vk` are the stranger's own, pinned out of
/// band: the VK is one the stranger minted with `setup` (or obtained from a setup party it trusts),
/// NEVER read from the bundle. The signed statement must name the same VK.
pub fn verify_bundle(
    b: &Bundle,
    renter_pub: &[u8; 32],
    nonce: &[u8; 32],
    vk: &[u8; 32],
) -> Result<Accepted, Refusal> {
    let st = &b.statement;
    if b.version != BUNDLE_VERSION {
        return Err(Refusal::Malformed(format!(
            "bundle version {} (this verifier reads {BUNDLE_VERSION})",
            b.version
        )));
    }
    if b.session != st.session {
        return Err(Refusal::StatementMismatch("session id"));
    }
    // R1 (statement): signed by the pinned renter key, naming the pinned nonce.
    let sig = hex::decode(&b.statement_sig).map_err(|e| Refusal::Malformed(e.to_string()))?;
    if !verify_signature(renter_pub, &st.signing_bytes(), &sig) {
        return Err(Refusal::StatementSignature);
    }
    if &st.renter_nonce != nonce {
        return Err(Refusal::StatementNonce);
    }
    // R0 + R1 + R2 — grain-verify, unchanged.
    let manifest = b
        .manifest
        .iter()
        .map(|h| parse32(h))
        .collect::<Result<Vec<_>, _>>()
        .map_err(Refusal::Malformed)?;
    let ladder = b
        .attestation
        .verify_r2_for_renter(renter_pub, nonce, &manifest)
        .map_err(Refusal::Ladder)?;
    let receipts = &b.attestation.report.receipts;
    // The checkpoint is FINAL: the renter acknowledged the whole chain shown (a suffix the renter
    // never saw is not admitted silently).
    let cs = b
        .attestation
        .checkpoint
        .as_ref()
        .expect("verify_for_renter required it");
    if cs.checkpoint.num_turns != receipts.len() as u64 {
        return Err(Refusal::CheckpointNotFinal {
            acknowledged: cs.checkpoint.num_turns,
            shown: receipts.len() as u64,
        });
    }
    if st.n_receipts != receipts.len() as u64 {
        return Err(Refusal::StatementMismatch("receipt count"));
    }
    if Some(st.receipt_head) != b.attestation.tip() {
        return Err(Refusal::StatementMismatch("receipt head"));
    }
    if st.receipt_signer != b.attestation.signer() {
        return Err(Refusal::StatementMismatch("receipt signer"));
    }
    // Non-omission over the calls shown: every call is a leaf of exactly one receipted window,
    // in order; the windows are exactly the receipts.
    if st.window != b.window || b.window == 0 {
        return Err(Refusal::StatementMismatch("window width"));
    }
    let leaves = b
        .calls
        .iter()
        .map(call_leaf)
        .collect::<Result<Vec<_>, _>>()
        .map_err(Refusal::Malformed)?;
    let labels = expected_labels(&b.calls, b.window as usize, nonce).map_err(Refusal::Malformed)?;
    if labels.len() != receipts.len() {
        return Err(Refusal::WindowCount {
            receipts: receipts.len(),
            windows: labels.len(),
        });
    }
    for (k, (want, r)) in labels.iter().zip(receipts.iter()).enumerate() {
        if &r.action != want {
            return Err(Refusal::WindowMismatch { window: k });
        }
    }
    if st.n_calls != b.calls.len() as u64 {
        return Err(Refusal::StatementMismatch("call count"));
    }
    if st.calls_root != mmr_root(&leaves) {
        return Err(Refusal::StatementMismatch("calls root"));
    }
    // R3 — verify only; the accept is the Lean core's.
    let agg = hex::decode(&b.aggregate).map_err(|e| Refusal::Malformed(e.to_string()))?;
    let env = WholeChainProofBytes::from_postcard(&agg)
        .map_err(|e| Refusal::Malformed(format!("aggregate: {e}")))?;
    if env.genesis_root != st.r3_genesis {
        return Err(Refusal::StatementMismatch("R3 genesis anchor"));
    }
    if env.num_turns != st.r3_legs {
        return Err(Refusal::StatementMismatch("R3 leg count"));
    }
    if &st.r3_vk != vk {
        return Err(Refusal::StatementMismatch(
            "R3 VK (the statement names a VK that is not your anchor)",
        ));
    }
    // The JOIN between the receipts and the folded history. (1) The manifest is exactly the
    // receipts' turn links, in order, once each. (2) The aggregate's committed head opens to the
    // published last grain cell under the receipt context of exactly those turn hashes: the head
    // binds the ordered list of turns the receipts link (through its context root) and that cell's
    // fields. (3) The cell's fields say what the last window was, how many turns ran, and which
    // executor receipt history preceded it.
    let links: Vec<[u8; 32]> = receipts
        .iter()
        .map(|r| r.attestation.as_ref().and_then(|a| a.turn_receipt_hash))
        .collect::<Option<Vec<_>>>()
        .ok_or(Refusal::LinksNotManifest)?;
    let unique: std::collections::BTreeSet<_> = links.iter().collect();
    if links != manifest || unique.len() != links.len() {
        return Err(Refusal::LinksNotManifest);
    }
    let (_, model_head) = grain_turn::session_head_openings(&b.last_cell, &manifest, b.model_nonce)
        .map_err(Refusal::Malformed)?;
    if model_head != env.final_root || model_head != st.r3_head {
        return Err(Refusal::HeadOpening(
            "the aggregate's head is not the last cell under these turns",
        ));
    }
    let fields = &b.last_cell.state.fields;
    let last = receipts.last().expect("at least one window");
    if fields[grain_turn::ACTION_SLOT] != grain_turn::action_commit(&last.action, last.cost) {
        return Err(Refusal::HeadOpening(
            "the last cell's action slot is not the last window's label",
        ));
    }
    if fields[CALLS_MADE] != field_u64(receipts.len() as u64) {
        return Err(Refusal::HeadOpening(
            "the last cell's turn counter is not the number of windows",
        ));
    }
    let exec_log = b
        .executor_receipts
        .iter()
        .map(|h| parse32(h))
        .collect::<Result<Vec<_>, _>>()
        .map_err(Refusal::Malformed)?;
    if grain_turn::verify_grain_history(&b.last_cell, &exec_log)
        != grain_turn::GrainHistoryVerdict::Bound
    {
        return Err(Refusal::HeadOpening(
            "the last cell does not bind the executor receipt history",
        ));
    }
    let vk = RecursionVk(*vk);
    let r3 = grain_verify::r3_verify_aggregate(&agg, &st.r3_head, &vk).map_err(Refusal::R3)?;
    Ok(Accepted {
        ladder,
        calls: b.calls.len(),
        windows: receipts.len(),
        r3,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_json_sorts_keys_at_every_depth() {
        let v: serde_json::Value =
            serde_json::from_str(r#"{"b":1,"a":{"d":[{"z":1,"y":2}],"c":null}}"#).unwrap();
        assert_eq!(
            canonical_json(&v),
            r#"{"a":{"c":null,"d":[{"y":2,"z":1}]},"b":1}"#
        );
    }

    #[test]
    fn spawned_id_matches_the_python_regex() {
        assert_eq!(
            spawned_id("x agentId: a0123abcd y"),
            Some("a0123abcd".into())
        );
        assert_eq!(
            spawned_id("agentId: a12 agentId: aabcdef0123"),
            Some("aabcdef0123".into())
        );
        assert_eq!(spawned_id("agentId: b0123abcd"), None);
    }

    #[test]
    fn windows_partition_in_order() {
        assert_eq!(windows(5, 2), vec![(0, 2), (2, 2), (4, 1)]);
        assert_eq!(windows(4, 2), vec![(0, 2), (2, 2)]);
    }

    #[test]
    fn a_leaf_moves_with_every_published_field() {
        let c = CallPublic {
            agent: "root".into(),
            seq: 3,
            tool: "Read".into(),
            use_id: "toolu_x".into(),
            ts: "t".into(),
            path: Some("/p".into()),
            spawned: None,
            commit: hex::encode([7u8; 32]),
        };
        let base = call_leaf(&c).unwrap();
        let mut variants = Vec::new();
        let mut v = c.clone();
        v.seq = 4;
        variants.push(v);
        let mut v = c.clone();
        v.tool = "Write".into();
        variants.push(v);
        let mut v = c.clone();
        v.path = None;
        variants.push(v);
        let mut v = c.clone();
        v.spawned = Some(String::new());
        variants.push(v);
        let mut v = c.clone();
        v.commit = hex::encode([8u8; 32]);
        variants.push(v);
        for v in variants {
            assert_ne!(call_leaf(&v).unwrap(), base);
        }
    }
}
