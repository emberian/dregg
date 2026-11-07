//! The producer: replay a projected session through the REAL minter and fold it.
//!
//! Every window is one `AgentAction::Invoke` admitted by dregg-agent's run loop
//! ([`Session::run_goal_minted`]) with `grain_turn::ToolGatewayMinter` as the minter, so each
//! window is a committed `ToolGateway::invoke` executor turn whose `ACTION_SLOT` witnesses
//! `action_commit(label, cost)` — and the label carries the window's call root. The turns are
//! then finalized with `finalize_session_threaded` and folded once.

use std::collections::BTreeMap;

use dregg_agent::agent::{AgentAction, AgentSpec, PlannedBrain, ToolKit, ToolOutcome};
use dregg_agent::grant::CapGrant;
use dregg_agent::session::Session;
use dregg_circuit_prove::ivc_turn_chain::{
    WholeChainProof, WholeChainProofBytes, prove_turn_chain_recursive_without_host_gate,
};
use dregg_circuit_prove::joint_turn_aggregation::verify_descriptor_participant;
use grain_turn::{ToolGatewayMinter, finalize_session_threaded};
use grain_verify::{GenesisPin, GrainAttestation};

use crate::{
    BUNDLE_VERSION, Bundle, CallPublic, RenterStatement, call_leaf, mmr_root, window_service,
    windows,
};

/// The replay toolkit: a window "runs" by reporting its own root. Nothing executes; the calls
/// already happened, and what is committed is their record.
struct WindowToolkit;

impl ToolKit for WindowToolkit {
    fn invoke(
        &self,
        service: &str,
        _amount_cents: Option<i64>,
        _cells: &BTreeMap<String, String>,
    ) -> ToolOutcome {
        ToolOutcome::pass(format!("committed {service}"))
    }
}

/// Timings and counts of one produce run.
#[derive(Debug, Default)]
pub struct ProduceStats {
    /// Windows (= receipts = executor turns).
    pub windows: usize,
    /// Legs finalized.
    pub legs: usize,
    /// Seconds spent replaying (admission + executor turns).
    pub replay_s: f64,
    /// Seconds spent finalizing legs.
    pub finalize_s: f64,
    /// Seconds spent folding.
    pub fold_s: f64,
}

fn random32() -> [u8; 32] {
    let mut b = [0u8; 32];
    getrandom::fill(&mut b).expect("OS randomness");
    b
}

/// Replay `calls` (already committed) in windows of `w` and drive them through the real minter.
/// Returns the session's attestation (with the genesis pin), the committed-turn manifest and the
/// minter (whose records the fold reads).
pub fn replay(
    calls: &[CallPublic],
    w: usize,
    nonce: &[u8; 32],
) -> Result<(GrainAttestation, Vec<[u8; 32]>, ToolGatewayMinter), String> {
    let leaves = calls.iter().map(call_leaf).collect::<Result<Vec<_>, _>>()?;
    let wins = windows(leaves.len(), w);
    let plan: Vec<AgentAction> = wins
        .iter()
        .enumerate()
        .map(|(k, (s, len))| AgentAction::Invoke {
            service: window_service(
                k,
                *len,
                &mmr_root(&leaves[*s..s + len]),
                (k == 0).then_some(nonce),
            ),
        })
        .collect();
    let budget = plan.len() as i64;
    let spec =
        AgentSpec::new("cc-session", budget).with_grant(CapGrant::Prefix("invoke:ccw:".into()));
    // The receipt key is a fresh random secret held by this producer (the host). The renter's
    // key is never here.
    let mut sess =
        Session::open_seeded(random32(), "cc-session", spec).map_err(|e| format!("{e:?}"))?;
    // The executor signs every grain turn's receipt (a fresh host key), so the LAST receipt,
    // which no history root covers, is authenticated too.
    let mut minter = ToolGatewayMinter::open_signed("cc-session", budget, Some(random32()))
        .map_err(|e| format!("{e:?}"))?;
    let report = sess.run_goal_minted(
        "replay the recorded session",
        &mut PlannedBrain::new(plan.clone()),
        &WindowToolkit,
        Some(&mut minter),
    );
    let _ = report;
    let att = GrainAttestation::attest(&sess);
    if att.report.receipts.len() != plan.len() {
        return Err(format!(
            "replay admitted {} of {} windows (cap {} / budget {} / turn {} refused)",
            att.report.receipts.len(),
            plan.len(),
            att.report.cap_refused,
            att.report.budget_refused,
            att.report.turn_refused
        ));
    }
    let signer = att.signer();
    let att = att.with_genesis(GenesisPin {
        renter_nonce: *nonce,
        signer,
    });
    let manifest = minter.committed_turns().to_vec();
    Ok((att, manifest, minter))
}

/// Finalize the minter's turns as ONE threaded EffectVM chain and fold it.
pub fn fold(
    minter: &ToolGatewayMinter,
    stats: &mut ProduceStats,
) -> Result<WholeChainProof, String> {
    let t = std::time::Instant::now();
    let legs = finalize_session_threaded(minter.records())?;
    stats.finalize_s = t.elapsed().as_secs_f64();
    stats.legs = legs.len();
    let selectors = legs
        .iter()
        .enumerate()
        .map(|(i, l)| {
            verify_descriptor_participant(&l.participant).map_err(|e| format!("leg {i}: {e}"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let t = std::time::Instant::now();
    let proof = prove_turn_chain_recursive_without_host_gate(&legs, &selectors)
        .map_err(|e| e.to_string())?;
    stats.fold_s = t.elapsed().as_secs_f64();
    Ok(proof)
}

/// **The honest-setup anchor a stranger can mint without the session.** A content-free session
/// of `n_windows` turns through the same minter has the same leg shape (one leg per written
/// slot, the same descriptors, the same trace heights) and so the same root-circuit VK.
pub fn synthetic_setup(n_windows: usize) -> Result<[u8; 32], String> {
    let nonce = [0u8; 32];
    let calls: Vec<CallPublic> = (0..n_windows)
        .map(|i| CallPublic {
            agent: "synthetic".into(),
            seq: i as u64,
            tool: "None".into(),
            use_id: format!("s{i}"),
            ts: String::new(),
            path: None,
            spawned: None,
            commit: hex::encode([0u8; 32]),
        })
        .collect();
    let (_, _, minter) = replay(&calls, 1, &nonce)?;
    let proof = fold(&minter, &mut ProduceStats::default())?;
    Ok(proof.root_vk_fingerprint().0)
}

/// Produce the unsigned bundle: replay, fold, and the statement the renter will sign.
pub fn produce(
    session: &str,
    calls: Vec<CallPublic>,
    w: usize,
    nonce: [u8; 32],
) -> Result<(Bundle, ProduceStats), String> {
    let mut stats = ProduceStats::default();
    let t = std::time::Instant::now();
    let (att, manifest, minter) = replay(&calls, w, &nonce)?;
    stats.replay_s = t.elapsed().as_secs_f64();
    stats.windows = att.report.receipts.len();
    let proof = fold(&minter, &mut stats)?;
    let leaves = calls.iter().map(call_leaf).collect::<Result<Vec<_>, _>>()?;
    let bytes = proof.to_bytes();
    let env = WholeChainProofBytes::from_postcard(&bytes).map_err(|e| e.to_string())?;
    let statement = RenterStatement {
        session: session.to_string(),
        renter_nonce: nonce,
        n_calls: calls.len() as u64,
        calls_root: mmr_root(&leaves),
        window: w as u64,
        receipt_signer: att.signer(),
        n_receipts: att.report.receipts.len() as u64,
        receipt_head: att.tip().ok_or("empty chain")?,
        r3_genesis: env.genesis_root,
        r3_head: env.final_root,
        r3_legs: env.num_turns,
        // The producer's CLAIM. The renter replaces it with an anchor it minted (`setup`) or
        // signs it knowingly; the verifier can override it either way.
        r3_vk: proof.root_vk_fingerprint().0,
    };
    let bundle = Bundle {
        version: BUNDLE_VERSION,
        session: session.to_string(),
        window: w as u64,
        calls,
        attestation: att,
        manifest: manifest.iter().map(hex::encode).collect(),
        statement,
        statement_sig: String::new(),
        aggregate: hex::encode(&bytes),
        last_cell: minter
            .records()
            .last()
            .ok_or("no committed turn")?
            .after_cell
            .clone(),
        executor_receipts: minter.turn_receipts().to_vec(),
        executor_pubkey: minter
            .executor_pubkey()
            .ok_or("the minter signs no receipts")?,
    };
    Ok((bundle, stats))
}
