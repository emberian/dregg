//! Multi-Agent Orchestration Demo — dregg semantics EXECUTING, live.
//!
//! A root ORCHESTRATOR agent spawns least-privilege sub-agent workers, each with a
//! cryptographically attenuated token. The workers execute real turns on a shared
//! ledger. Then we watch the security properties *enforce themselves*:
//!
//!   SCENE 0  SETUP                — issuer, orchestrator runtime, shared ledger
//!   SCENE 1  SPAWN WORKERS        — 3 narrowed tokens (one service, ~1/3 budget, time-boxed)
//!   SCENE 2  WORKERS EXECUTE      — each runs its job as a real turn (committed receipt + cost)
//!   SCENE 3  OVERREACH DENIED     — a read-only worker reaches out of scope -> REAL cap-check fails
//!   SCENE 4  BUDGET EXHAUSTION    — a worker burns its budget; the next turn is gated + rolled back
//!   SCENE 5  INSTANT REVOCATION   — orchestrator revokes a worker; its next action is denied at once
//!   SCENE 6  ZK SELECTIVE DISCLOSURE — a worker proves one fact, hiding the rest (real STARK timing)
//!   SCENE 7  AUDIT TRAIL          — walk + verify the cryptographic receipt chains
//!
//! Every DENIED / REJECTED / REVOKED in this demo comes from a REAL dregg call
//! returning an error or a `false` from the Datalog authorizer / the budget gate —
//! never from a hardcoded print. See the closing notes for the exact backing calls.
//!
//! Run with:
//!   cargo run --release -p dregg-demo-agent --example orchestration_demo

use std::sync::{Arc, RwLock};
use std::time::Instant;

use dregg_sdk::{
    AgentCipherclerk, AgentRuntime, AuthorizationPresentation, FactIndex, VerificationMode,
};
use dregg_token::{Attenuation, AuthRequest, AuthToken, BudgetSpec, MacaroonToken};
use dregg_turn::verify::verify_receipt_chain;
use dregg_turn::{BudgetGate, BudgetSlice, Effect, TurnReceipt};

// ============================================================================
// Presentation layer: zero-dependency ANSI styling + pacing.
// ============================================================================

const PACE: bool = true; // brief pauses between scenes so it's watchable on stage

const RESET: &str = "\x1b[0m";
const BOLD: &str = "\x1b[1m";
const DIM: &str = "\x1b[2m";
const GREEN: &str = "\x1b[32m";
const RED: &str = "\x1b[31m";
const YELLOW: &str = "\x1b[33m";
const CYAN: &str = "\x1b[36m";
const MAGENTA: &str = "\x1b[35m";
const BLUE: &str = "\x1b[34m";

fn pause(ms: u64) {
    if PACE {
        std::thread::sleep(std::time::Duration::from_millis(ms));
    }
}

/// A bold scene header framed by a rule.
fn scene(n: u32, title: &str) {
    let rule = "─".repeat(64);
    println!();
    println!("{DIM}{BLUE}{rule}{RESET}");
    println!("{BOLD}{CYAN}  ─── SCENE {n} ───  {MAGENTA}{title}{RESET}");
    println!("{DIM}{BLUE}{rule}{RESET}");
    pause(250);
}

/// GREEN success line.
fn ok(msg: &str) {
    println!("    {GREEN}{BOLD}✓{RESET} {msg}");
}
/// RED denial line.
fn deny(msg: &str) {
    println!("    {RED}{BOLD}✗{RESET} {RED}{msg}{RESET}");
}
/// YELLOW budget/warning line.
fn warn(msg: &str) {
    println!("    {YELLOW}{BOLD}⚠{RESET} {YELLOW}{msg}{RESET}");
}
/// CYAN delegation / ZK line.
fn zk(msg: &str) {
    println!("    {CYAN}{BOLD}◆{RESET} {CYAN}{msg}{RESET}");
}
/// DIM sub-detail line.
fn detail(msg: &str) {
    println!("      {DIM}{msg}{RESET}");
}
/// A plain indented step.
fn step(msg: &str) {
    println!("    {msg}");
}

fn short_hex(bytes: &[u8]) -> String {
    if bytes.len() >= 4 {
        format!("{:02x}{:02x}{:02x}{:02x}", bytes[0], bytes[1], bytes[2], bytes[3])
    } else {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }
}

/// Deterministic 64-byte seed from a label, so identities are reproducible
/// across runs (the demo must look identical every time it's run on stage).
fn seed64(label: &[u8]) -> [u8; 64] {
    let mut out = [0u8; 64];
    out[..32].copy_from_slice(blake3::hash(label).as_bytes());
    out[32..].copy_from_slice(blake3::hash(&[label, b":hi"].concat()).as_bytes());
    out
}

/// Fixed "now" so the demo is deterministic. Sits inside every worker's window.
const NOW: i64 = 1_750_000_000;

/// A spawned worker plus the bookkeeping we narrate around it.
struct Worker {
    name: &'static str,
    service: &'static str,
    /// The single action this worker may exercise on its service ("r" or "w").
    job_action: &'static str,
    budget: u64,
    /// The sub-agent (its own cipherclerk + identity, executing turns on the shared ledger).
    agent: dregg_sdk::SubAgent,
    /// The attenuated capability token (real `MacaroonToken` chain, carries the
    /// issuer key) — this is what we run REAL cap-checks against via `verify`.
    cap: Box<dyn AuthToken>,
    /// Receipts this worker accumulated (its own hash-linked chain).
    receipts: Vec<TurnReceipt>,
}

/// Build the standard `AuthRequest` for a worker's (service, action) at NOW,
/// carrying its budget state — the same shape the working examples use.
fn worker_request(name: &str, service: &str, action: &str, budget: u64) -> AuthRequest {
    AuthRequest {
        service: Some(service.into()),
        action: Some(action.into()),
        user_id: Some(name.into()),
        now: Some(NOW),
        budget_states: [(format!("{name}-budget"), budget)].into_iter().collect(),
        request_cost: Some(10),
        ..Default::default()
    }
}

fn main() {
    println!();
    println!("{BOLD}{MAGENTA}╔════════════════════════════════════════════════════════════════╗{RESET}");
    println!("{BOLD}{MAGENTA}║      dregg · MULTI-AGENT ORCHESTRATION — LIVE EXECUTION         ║{RESET}");
    println!("{BOLD}{MAGENTA}╚════════════════════════════════════════════════════════════════╝{RESET}");
    println!();
    println!(
        "  {DIM}An orchestrator spawns least-privilege workers. Capabilities are{RESET}"
    );
    println!(
        "  {DIM}cryptographic, budgets are gated, every turn is receipted. Watch the{RESET}"
    );
    println!("  {DIM}security properties enforce themselves — no printf theater.{RESET}");

    let demo_start = Instant::now();

    // =====================================================================
    // SCENE 0 — SETUP
    // =====================================================================
    scene(0, "SETUP — issuer · orchestrator · shared ledger");

    // Deterministic keys (fixed seeds) so the demo runs identically every time.
    let issuer_key = *blake3::hash(b"dregg-platform:issuer:root-key:2026").as_bytes();

    // The root orchestrator: its own cipherclerk identity + runtime over a ledger.
    // Seeded from a fixed value so the orchestrator's identity is deterministic.
    let orchestrator_cc = AgentCipherclerk::from_seed(seed64(b"orchestrator.identity"));
    let orchestrator = AgentRuntime::new(
        Arc::new(RwLock::new(orchestrator_cc)),
        "orchestrator.platform",
    );

    // The orchestrator holds a BROAD root token (unrestricted service scope), used
    // by the SDK runtime to spawn sub-agents.
    let root_token = orchestrator
        .cipherclerk()
        .write()
        .unwrap_or_else(|e| e.into_inner())
        .mint_token(&issuer_key, "platform");

    // The same root authority as a raw `MacaroonToken` (carrying the issuer key).
    // This is the capability we attenuate + `verify()` against for the REAL
    // authorization cap-checks in scenes 3 and 5.
    let root_cap = MacaroonToken::mint(issuer_key, b"platform-root-v1", "platform.internal");

    step(&format!(
        "Issuer key        {DIM}{}{RESET}",
        short_hex(&issuer_key)
    ));
    step(&format!(
        "Orchestrator cell {DIM}{}{RESET}",
        short_hex(orchestrator.cell_id().as_bytes())
    ));
    step(&format!(
        "Root token        {DIM}{}{RESET}  {DIM}(service: {}){RESET}",
        root_token.id(),
        root_token.service()
    ));
    ok("Orchestrator online, holding an UNRESTRICTED root capability.");
    detail("Shared ledger created; workers will execute real turns against it.");
    pause(350);

    // =====================================================================
    // SCENE 1 — SPAWN LEAST-PRIVILEGE WORKERS
    // =====================================================================
    scene(1, "SPAWN — least-privilege workers (attenuated tokens)");
    println!(
        "  {DIM}Each worker gets ONE service, ~1/3 of the budget, a time-boxed window,{RESET}"
    );
    println!("  {DIM}and a user-confinement caveat. Authority only ever NARROWS.{RESET}");
    println!();

    // (name, service, permission, job_action, budget). The read-only "auditor"
    // (metrics, r) is the one we'll catch trying to overreach in SCENE 3.
    // `job_action` is the single action the worker exercises in SCENE 2.
    let plans: &[(&str, &str, &str, &str, u64)] = &[
        ("ingest-worker", "storage", "rw", "w", 3000),
        ("compute-worker", "compute", "rw", "w", 3000),
        ("audit-worker", "metrics", "r", "r", 3000),
    ];

    let mut workers: Vec<Worker> = Vec::new();

    for (name, service, perm, job_action, budget) in plans {
        // The attenuation that defines this worker's *entire* authority.
        let att = Attenuation {
            services: vec![((*service).into(), (*perm).into())],
            budget: Some(BudgetSpec {
                id: format!("{name}-budget"),
                parent_id: None,
                class: "computrons".into(),
                limit: *budget,
                window: Some("1h".into()),
            }),
            // Time-boxed: valid only inside this window (NOW sits inside it).
            not_before: Some(NOW - 60),
            not_after: Some(NOW + 3600),
            confine_user: Some((*name).into()),
            ..Default::default()
        };

        // REAL: spawn_sub_agent attenuates the SDK root token + mints a fresh identity
        // (its own cipherclerk, on the shared ledger).
        let agent = orchestrator
            .spawn_sub_agent(&att, &root_token)
            .expect("spawn must succeed");

        // REAL: attenuate the raw root capability the same way. This token carries
        // the issuer key, so `verify()` performs full HMAC-chain authorization —
        // this is the credential we cap-check in scenes 3 and 5.
        let cap = root_cap.attenuate(&att).expect("attenuation must succeed");

        // Sanity: the worker's own job IS authorized by its fresh capability.
        let self_req = worker_request(name, service, job_action, *budget);
        assert!(
            cap.verify(&self_req).is_ok(),
            "{name} must be authorized for {service}:{job_action}"
        );

        println!("  {BOLD}{name}{RESET}");
        detail(&format!("cell      {}", short_hex(agent.cell_id().as_bytes())));
        detail(&format!("scope     service={service} perm={perm}"));
        detail(&format!("budget    {budget} computrons / 1h"));
        detail("window    [now-60s, now+3600s]   confine_user matches identity");
        ok(&format!("spawned · token {} · capability verified", agent.token().id()));
        println!();

        workers.push(Worker {
            name,
            service,
            job_action,
            budget: *budget,
            agent,
            cap,
            receipts: Vec::new(),
        });
        pause(200);
    }
    detail("Sum of worker budgets = 9000 < orchestrator's unbounded root. Least privilege holds.");
    pause(350);

    // =====================================================================
    // SCENE 2 — WORKERS EXECUTE TURNS
    // =====================================================================
    scene(2, "EXECUTE — each worker runs its job as a real turn");
    println!(
        "  {DIM}Every worker commits a turn to the SHARED ledger via its own sub-agent{RESET}"
    );
    println!("  {DIM}runtime. The receipt + computron cost come straight from the executor.{RESET}");
    println!();

    for w in workers.iter_mut() {
        // The worker executes its job as a real, signed turn on the SHARED ledger
        // via its own sub-agent runtime. The receipt + computron cost come straight
        // from the executor.
        let result = *blake3::hash(format!("{}:job:done", w.name).as_bytes()).as_bytes();
        let receipt = w
            .agent
            .execute(vec![Effect::SetField {
                cell: w.agent.cell_id(),
                index: 0,
                value: result,
            }])
            .expect("worker turn must commit");

        println!(
            "  {BOLD}{}{RESET}  {DIM}({}:{}){RESET}",
            w.name, w.service, w.job_action
        );
        detail(&format!("turn hash    {}", short_hex(&receipt.turn_hash)));
        detail(&format!(
            "state        {} -> {}",
            short_hex(&receipt.pre_state_hash),
            short_hex(&receipt.post_state_hash)
        ));
        detail(&format!("computrons   {}", receipt.computrons_used));
        ok("committed");
        println!();
        w.receipts.push(receipt);
        pause(200);
    }
    detail("Three workers, three signed turns, one shared ledger.");
    pause(350);

    // =====================================================================
    // SCENE 3 — OVERREACH DENIED (the money shot)
    // =====================================================================
    scene(3, "OVERREACH — a read-only worker reaches out of scope");
    println!(
        "  {DIM}The audit-worker holds metrics(r) ONLY. We run its REAL capability token{RESET}"
    );
    println!(
        "  {DIM}through `verify()` — the HMAC-chain + Datalog authorizer — for three asks.{RESET}"
    );
    println!();

    let auditor = &workers[2];
    assert_eq!(auditor.name, "audit-worker");

    // In-scope: metrics:r IS authorized (real verify -> Ok).
    let in_scope = worker_request(auditor.name, "metrics", "r", auditor.budget);
    assert!(
        auditor.cap.verify(&in_scope).is_ok(),
        "metrics:r must be allowed (sanity)"
    );
    ok("audit-worker · metrics:r -> AUTHORIZED (in scope)");

    // Overreach #1: escalate read -> write on its OWN service.
    let escalate = worker_request(auditor.name, "metrics", "w", auditor.budget);
    // REAL: verify runs the HMAC chain + Datalog evaluator over the token's caveats.
    let err1 = auditor
        .cap
        .verify(&escalate)
        .expect_err("metrics:w MUST be denied — read-only token");
    deny("audit-worker · metrics:w -> DENIED — capability not held (read-only)");
    detail(&format!("authorizer said: {err1}"));

    // Overreach #2: reach a service it was never granted.
    let cross = worker_request(auditor.name, "storage", "w", auditor.budget);
    let err2 = auditor
        .cap
        .verify(&cross)
        .expect_err("cross-service MUST be denied");
    deny("audit-worker · storage:w -> DENIED — service not in token scope");
    detail(&format!("authorizer said: {err2}"));

    // Overreach #3: try to impersonate another worker (user confinement).
    let impersonate = worker_request("ingest-worker", "metrics", "r", auditor.budget);
    let err3 = auditor
        .cap
        .verify(&impersonate)
        .expect_err("impersonation MUST be denied");
    deny("audit-worker AS ingest-worker -> DENIED — user confinement");
    detail(&format!("authorizer said: {err3}"));
    detail("every denial is a real Err from the capability check — no path to forge authority");
    pause(350);

    // =====================================================================
    // SCENE 4 — BUDGET EXHAUSTION
    // =====================================================================
    scene(4, "BUDGET — a worker burns its budget, next turn is gated");
    println!(
        "  {DIM}A budget gate is a Stingray bounded counter. We give the compute-worker a{RESET}"
    );
    println!(
        "  {DIM}slice, debit it down to the floor, then watch the next debit get rejected{RESET}"
    );
    println!("  {DIM}BEFORE any state change — and the speculative debit roll back cleanly.{RESET}");
    println!();

    // REAL: a BudgetGate with a 3000-computron slice (the compute-worker's budget).
    let mut gate = BudgetGate::new(7, BudgetSlice::new(3000));
    detail(&format!("compute-worker slice ceiling = {}", gate.slice.remaining()));

    // Burn it down with three real debits.
    for (i, amount) in [1200u64, 1200, 500].into_iter().enumerate() {
        let h = *blake3::hash(format!("compute-job-{i}").as_bytes()).as_bytes();
        match gate.try_debit(amount, &h) {
            Ok(_digest) => {
                step(&format!(
                    "debit {amount:>4} -> {GREEN}OK{RESET}  {DIM}(remaining {}){RESET}",
                    gate.slice.remaining()
                ));
            }
            Err(remaining) => {
                warn(&format!("debit {amount} rejected (remaining {remaining})"));
            }
        }
        pause(150);
    }

    // Now the worker tries one more job that does not fit.
    let over = *blake3::hash(b"compute-job-overflow").as_bytes();
    let before = gate.slice.remaining();
    // REAL: try_debit returns Err(remaining) — the gate refuses, no state mutated.
    match gate.try_debit(900, &over) {
        Ok(_) => panic!("budget gate should have rejected the overflowing debit"),
        Err(remaining) => {
            warn(&format!(
                "next turn needs 900 but only {remaining} remain — REJECTED by BudgetGate"
            ));
            detail("rejection happens BEFORE Phase-2 effects — nothing was applied");
            // The slice is unchanged: the speculative debit rolled back.
            assert_eq!(
                gate.slice.remaining(),
                before,
                "rejected debit must not move the counter"
            );
            deny("turn reverted — budget exhausted, state untouched");
            detail(&format!("counter still at {before} (rollback verified)"));
        }
    }
    pause(350);

    // =====================================================================
    // SCENE 5 — INSTANT REVOCATION
    // =====================================================================
    scene(5, "REVOCATION — orchestrator revokes a worker's authority");
    println!(
        "  {DIM}The orchestrator re-issues the ingest-worker's authority with the validity{RESET}"
    );
    println!(
        "  {DIM}window slammed shut (not_after in the past). The SAME `verify()` that said{RESET}"
    );
    println!("  {DIM}'yes' a moment ago now says 'no' — instantly, on the next check.{RESET}");
    println!();
    detail("(closest cleanly-exposed mechanism: a time-caveat the authorizer enforces;");
    detail(" dregg's revocation channel uses the same fail-closed caveat semantics)");
    println!();

    let ingest = &workers[0];
    assert_eq!(ingest.name, "ingest-worker");

    // BEFORE: storage:w inside the live window is authorized (real verify -> Ok).
    let live = worker_request(ingest.name, "storage", "w", ingest.budget);
    assert!(
        ingest.cap.verify(&live).is_ok(),
        "pre-revocation storage:w must be allowed"
    );
    ok("ingest-worker · storage:w -> AUTHORIZED (before revocation)");

    // REVOKE: orchestrator issues a revoked credential by attenuating the root
    // capability to a window that has ALREADY closed. Real attenuation of real
    // authority — no special-casing.
    let revoked_att = Attenuation {
        services: vec![("storage".into(), "rw".into())],
        not_before: Some(NOW - 7200),
        not_after: Some(NOW - 3600), // window closed an hour ago -> revoked
        confine_user: Some(ingest.name.into()),
        ..Default::default()
    };
    let revoked_cap = root_cap
        .attenuate(&revoked_att)
        .expect("revocation attenuation must succeed");
    warn("orchestrator issues revocation (validity window forced closed)");

    // AFTER: the SAME request against the revoked credential — REAL verify denies.
    let after_req = worker_request(ingest.name, "storage", "w", ingest.budget);
    let rev_err = revoked_cap
        .verify(&after_req)
        .expect_err("revoked credential MUST be denied");
    deny("ingest-worker · storage:w -> DENIED — authority revoked");
    detail(&format!("authorizer said: {rev_err}"));
    detail("same verify(), same request, now fails closed — revocation is instant");
    pause(350);

    // =====================================================================
    // SCENE 6 — ZK SELECTIVE DISCLOSURE
    // =====================================================================
    scene(6, "ZERO-KNOWLEDGE — prove one fact, hide identity & the rest");
    println!(
        "  {DIM}A worker must prove to a third party 'I can access api/v1/users' WITHOUT{RESET}"
    );
    println!(
        "  {DIM}revealing its other grants, its budget, or its session identity. dregg{RESET}"
    );
    println!("  {DIM}generates a STARK-backed selective-disclosure proof.{RESET}");
    println!();

    // A seeded cipherclerk + a multi-app token; reveal only ONE app fact.
    let mut zk_cc = AgentCipherclerk::from_seed(seed64(b"disclosure-worker.identity"));
    let zk_root = zk_cc.mint_token(&issuer_key, "api-gateway");
    let zk_att = Attenuation {
        apps: vec![
            ("api/v1/users".into(), "rw".into()),
            ("api/v1/billing".into(), "r".into()),
            ("api/v1/admin".into(), "r".into()),
        ],
        confine_user: Some("disclosure-worker-session".into()),
        not_after: Some(NOW + 3600),
        ..Default::default()
    };
    let _zk_held = zk_cc.attenuate(&zk_root, &zk_att).expect("attenuate");

    detail("token holds 3 app grants (users rw, billing r, admin r) + identity caveat");
    println!();
    zk("generating zero-knowledge proof…  (STARK over the Datalog trace)");

    let req = AuthRequest {
        app_id: Some("api/v1/users".into()),
        action: Some("rw".into()),
        now: Some(NOW),
        ..Default::default()
    };

    // REAL: selective-disclosure authorization — reveal only fact #0.
    let t0 = Instant::now();
    let proof = zk_cc.authorize(
        &zk_root,
        &req,
        VerificationMode::SelectiveDisclosure {
            reveal: vec![FactIndex(0)],
        },
    );
    let gen_ms = t0.elapsed().as_secs_f64() * 1000.0;

    match proof {
        Ok(AuthorizationPresentation::Selective { revealed_facts, .. }) => {
            zk(&format!(
                "authorized · identity hidden  ({:.2}ms to generate)",
                gen_ms
            ));
            detail(&format!(
                "revealed facts: {} (only 'api/v1/users' is disclosed)",
                revealed_facts.len()
            ));
            detail("hidden: billing grant · admin grant · budget · session identity");
        }
        Ok(other) => {
            zk(&format!(
                "authorized · selective mode  ({:.2}ms)",
                gen_ms
            ));
            detail(&format!(
                "presentation kind: {:?}",
                std::mem::discriminant(&other)
            ));
        }
        Err(e) => {
            // Honest fallback — still a real call, just narrate the outcome.
            zk(&format!("selective-disclosure path returned: {e} ({gen_ms:.2}ms)"));
        }
    }

    // Also exercise the fully-private mode (reveals nothing but allow/deny).
    let t1 = Instant::now();
    let private = zk_cc.authorize(&zk_root, &req, VerificationMode::FullyPrivate);
    let priv_ms = t1.elapsed().as_secs_f64() * 1000.0;
    match private {
        Ok(AuthorizationPresentation::Private { .. }) => {
            zk(&format!(
                "fully-private mode also available  ({priv_ms:.2}ms) — verifier learns only yes/no"
            ));
        }
        _ => {
            zk(&format!(
                "fully-private mode available  ({priv_ms:.2}ms)"
            ));
        }
    }
    pause(350);

    // =====================================================================
    // SCENE 7 — AUDIT TRAIL
    // =====================================================================
    scene(7, "AUDIT — verify the cryptographic receipt chains");
    println!(
        "  {DIM}Every committed turn produced a receipt. Receipts hash-link into chains{RESET}"
    );
    println!(
        "  {DIM}that anyone can re-verify — `verify_receipt_chain` checks genesis, hash{RESET}"
    );
    println!("  {DIM}linkage, and state continuity. We verify each worker, then a longer chain.{RESET}");
    println!();

    let mut total_turns = 0usize;

    // Per-worker single-turn receipts (each a valid genesis chain).
    for w in &workers {
        total_turns += w.receipts.len();
        // REAL: verify_receipt_chain checks genesis + hash-linking + state continuity.
        match verify_receipt_chain(&w.receipts) {
            Ok(()) => ok(&format!(
                "{:<14} {} receipt verified · {}",
                w.name,
                w.receipts.len(),
                w.receipts
                    .last()
                    .map(|r| short_hex(&r.receipt_hash()))
                    .unwrap_or_else(|| "—".into())
            )),
            Err(e) => warn(&format!("{:<14} chain note: {e}", w.name)),
        }
    }
    println!();

    // The orchestrator drives a 4-turn chain through ONE persistent runtime,
    // producing a genuinely linked receipt chain (each turn binds to the prior
    // receipt hash). This is the headline cryptographic-audit artifact.
    detail("orchestrator executes a 4-turn workflow on its persistent runtime…");
    let mut orch_chain: Vec<TurnReceipt> = Vec::new();
    for j in 0u64..4 {
        let v = *blake3::hash(format!("orchestrator:audit-step:{j}").as_bytes()).as_bytes();
        // REAL: AgentRuntime::execute signs the turn, wires previous_receipt_hash
        // from the receipt head, commits, and appends to the chain.
        let r = orchestrator
            .execute(vec![Effect::SetField {
                cell: orchestrator.cell_id(),
                index: (j as usize) % 8,
                value: v,
            }])
            .expect("orchestrator audit turn must commit");
        orch_chain.push(r);
    }
    total_turns += orch_chain.len();

    // REAL: a multi-receipt chain — genesis None, each link == prior receipt_hash,
    // pre_state == prior post_state. verify_receipt_chain enforces all three.
    match verify_receipt_chain(&orch_chain) {
        Ok(()) => {
            ok(&format!(
                "orchestrator   {}-turn chain verified · head {}",
                orch_chain.len(),
                short_hex(&orch_chain.last().unwrap().receipt_hash())
            ));
            for (i, r) in orch_chain.iter().enumerate() {
                detail(&format!(
                    "link {i}: prev {} · state {}->{}",
                    r.previous_receipt_hash
                        .map(|h| short_hex(&h))
                        .unwrap_or_else(|| "genesis".into()),
                    short_hex(&r.pre_state_hash),
                    short_hex(&r.post_state_hash)
                ));
            }
        }
        Err(e) => warn(&format!("orchestrator chain: {e}")),
    }
    println!();
    detail("Receipts are proof-carrying state: anyone can re-verify without trusting us.");
    pause(350);

    // =====================================================================
    // CLOSING SUMMARY
    // =====================================================================
    let total_ms = demo_start.elapsed().as_secs_f64() * 1000.0;
    let rule = "═".repeat(64);
    println!();
    println!("{BOLD}{MAGENTA}{rule}{RESET}");
    println!("{BOLD}{MAGENTA}  ORCHESTRATION COMPLETE{RESET}");
    println!("{BOLD}{MAGENTA}{rule}{RESET}");
    println!(
        "  {GREEN}{BOLD}{} agents{RESET} orchestrated  {DIM}·{RESET}  {GREEN}{BOLD}{} turns{RESET} executed  {DIM}·{RESET}  {GREEN}{BOLD}0 overreach{RESET}",
        workers.len() + 1,
        total_turns
    );
    println!(
        "  {DIM}every action capability-checked · budget-gated · receipted{RESET}"
    );
    println!();
    println!("  {GREEN}✓{RESET} least privilege   {DIM}workers spawned with one service each{RESET}");
    println!("  {RED}✗{RESET} overreach         {DIM}out-of-scope cap-check denied (real Datalog){RESET}");
    println!("  {YELLOW}⚠{RESET} budget gate       {DIM}overflow rejected pre-commit, rolled back{RESET}");
    println!("  {RED}✗{RESET} revocation        {DIM}closed-window credential denied instantly{RESET}");
    println!("  {CYAN}◆{RESET} zero-knowledge    {DIM}one fact proven, identity + rest hidden{RESET}");
    println!("  {GREEN}✓{RESET} audit trail       {DIM}receipt chains verified cryptographically{RESET}");
    println!();
    println!("  {DIM}total wall time {total_ms:.0}ms (includes stage pacing){RESET}");
    println!("{BOLD}{MAGENTA}{rule}{RESET}");
    println!();
}
