//! `cross-app-helper` — drives the four anchor starbridge-apps through
//! `EmbeddedExecutor` to produce real `TurnReceipt`s for the seven-step
//! cross-app composition story.
//!
//! # Status (2026-05-25): superseded by the MCP subprocess path
//!
//! Issue #109 closed this binary's EmbeddedExecutor gap by adding
//! `cross_app_mcp.py` (path c from the issue), which spawns
//! `dregg-node mcp` as a subprocess and drives the four new MCP tools:
//!
//!   - `dregg_issue_credential`    → alice.issue receipt
//!   - `dregg_register_name`       → bob.register receipt
//!   - `dregg_register_service`    → bob.mount receipt
//!   - `dregg_publish_subscription` → carol/dan bounty-lifecycle receipts
//!
//! Each receipt now carries `effect_vm_proof_hex` (a real STARK proof
//! from `generate_effect_vm_proof`).  `verify_real.py` detects the MCP
//! path and upgrades the assertion from "no Rejected" to "all Verified".
//!
//! `run.sh` step 11 now prefers `cross_app_mcp.py` (no cargo required;
//! only needs `dregg-node` to be built) and falls back to this binary.
//!
//! # MCP subprocess pattern
//!
//! ```text
//! dregg-node mcp --data-dir ~/.dregg
//!   stdin  ← JSON-RPC 2.0 (one message per line)
//!   stdout → JSON-RPC 2.0 responses (one per line)
//!   stderr → tracing log (RUST_LOG=error for quiet mode)
//! ```
//!
//! Handshake sequence:
//! 1. Send `{"jsonrpc":"2.0","id":0,"method":"initialize","params":{...}}`
//! 2. Receive `{"jsonrpc":"2.0","id":0,"result":{...}}`
//! 3. Send `{"jsonrpc":"2.0","method":"notifications/initialized","params":{}}`
//!    (no response — notification)
//! 4. Send `tools/call` requests: `{"method":"tools/call","params":{"name":"dregg_issue_credential","arguments":{...}}}`
//! 5. Parse `result.content[0].text` (JSON string) for the tool output.
//!
//! The node starts `unlocked = true` in MCP mode so no separate
//! passphrase step is required.
//!
//! # Why this binary is kept
//!
//! - Provides a Rust integration-test path for the EmbeddedExecutor +
//!   receipt-chain layer (no running node required).
//! - Serves as a reference for the correct `build_*_action` call
//!   signatures (the MCP tools call the same builders internally).
//!
//! # What this is NOT
//!
//! - **STARK proofs:** `EmbeddedExecutor` is the app-framework's
//!   embedded path; it does not run the prover. Use `cross_app_mcp.py`
//!   for receipts with real STARK proofs.
//!
//! - **Cross-fed.** Single-federation demo; cross-federation is
//!   `SILVER-VISION-E2E-VERIFICATION.md`'s sibling lane.
//!
//! # Story arc
//!
//! 1. **alice.issue** — Alice's identity-issuer cell issues a
//!    `verified-developer-v1` credential to Bob.
//! 2. **bob.register** — Bob registers `bob.dev` in nameservice's
//!    identity-attested tier, carrying the credential proof.
//! 3. **bob.mount** — Bob registers a service entry under
//!    `governed-namespace` so `dregg://bob.dev → bob_cell`.
//! 4. **carol.post / carol.grant-publisher / carol.grant-consumer** —
//!    Carol creates a subscription cell, grants Bob consumer rights,
//!    grants her own bounty cell publisher rights.
//! 5. **dan.claim** — Dan claims the bounty (Posted → Claimed publish).
//! 6. **dan.fulfill** — Dan submits fulfillment (Claimed → Fulfilled
//!    publish).
//! 7. **carol.settle** — After the dispute window, Carol settles
//!    (Fulfilled → Settled publish).
//!
//! Each step emits `<step>.receipt.json` with the canonical
//! `TurnReceipt` shape (postcard-hex of the receipt, JSON for human
//! inspection, plus the cross-app links the next step depends on).

use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;

use serde::{Deserialize, Serialize};

use dregg_app_framework::{AgentCipherclerk, AppCipherclerk, CellId, EmbeddedExecutor};
use dregg_cell::program::AuthorizedSet;
use dregg_credentials::{AttrValue, CredentialAttributes, IssuerKeys, issue};
use dregg_turn::TurnReceipt;
use starbridge_governed_namespace::build_register_service_action;
use starbridge_identity::{
    build_issue_credential_action, kyc_schema, schema_commitment as identity_schema_commitment,
};
use starbridge_nameservice::build_register_with_credential_action;
use starbridge_subscription::{
    BountyState, bounty_state_payload_hash, build_bounty_state_publish_action,
    build_grant_consumer_action, build_grant_publisher_action, build_publish_action,
};

// ---------------------------------------------------------------------------
// On-disk artifact shape
// ---------------------------------------------------------------------------

/// What each per-step `<step>.receipt.json` contains.
///
/// Keeping this small and explicit so `verify_real.py` can read it
/// without dragging in postcard. The `receipt_bytes_hex` is the
/// canonical postcard form (what would land in a real receipt-chain on
/// disk); the human-readable fields are derived directly from the
/// receipt and replicated for fast cross-app link checks in Python.
#[derive(Serialize, Deserialize)]
struct ReceiptArtifact {
    /// Step label (e.g. "alice.issue", "bob.register").
    step: String,
    /// The agent's cell id (the executor's `cell_id()`).
    agent_cell_hex: String,
    /// Canonical receipt hash (`receipt.receipt_hash()`).
    receipt_hash_hex: String,
    /// Previous receipt hash in the agent's chain (None on genesis).
    previous_receipt_hash_hex: Option<String>,
    /// Pre / post state hashes.
    pre_state_hash_hex: String,
    post_state_hash_hex: String,
    /// effects_hash binds the action set.
    effects_hash_hex: String,
    /// action_count from the receipt.
    action_count: usize,
    /// Postcard-serialized receipt bytes, hex-encoded.
    receipt_bytes_hex: String,
    /// Emitted events from this step, in the canonical
    /// {symbol, data: [hex-32-bytes…]} shape.
    emitted_events: Vec<EventArtifact>,
    /// Step-specific cross-app link metadata (e.g. credential id,
    /// commitment values, etc.). Read by `verify_real.py` to check
    /// that the next step's input matches this step's output.
    links: HashMap<String, String>,
}

#[derive(Serialize, Deserialize)]
struct EventArtifact {
    /// The event's method symbol (e.g. "credential-issued").
    topic: String,
    /// 32-byte data fields, hex-encoded.
    data_hex: Vec<String>,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn fixture_cipherclerk(seed: u8) -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32])
}

fn fixture_executor(cipherclerk: &AppCipherclerk) -> (EmbeddedExecutor, CellId) {
    let executor = EmbeddedExecutor::new(cipherclerk, "default");
    let cell = executor.cell_id();
    (executor, cell)
}

/// Recognise a known event topic by its BLAKE3 hash. Returns the
/// canonical name if known, else the hex hash. `dregg_turn::action::symbol`
/// is `*blake3::hash(name.as_bytes()).as_bytes()` so we can recover the
/// name only by lookup. The list of names that this helper produces is
/// small and finite — the four apps' emitted-event topics.
fn topic_name(sym: &dregg_turn::action::Symbol) -> String {
    const KNOWN: &[&str] = &[
        // identity
        "credential-issued",
        "credential-revoked",
        "credential-presented",
        "presentation-verified",
        "presentation-accepted",
        "presentation-rejected",
        // nameservice
        "name-registered",
        "name-registered-attested",
        "name-renewed",
        "name-transferred",
        "name-revoked",
        "target-set",
        // governed-namespace
        "service-registered",
        "table-update-proposed",
        "table-update-voted",
        "table-update-committed",
        // subscription
        "subscription-published",
        "subscription-consumed",
        "subscription-publisher-granted",
        "subscription-consumer-granted",
    ];
    for name in KNOWN.iter().copied() {
        if dregg_turn::action::symbol(name) == *sym {
            return name.into();
        }
    }
    hex_encode(sym)
}

fn artifact_from_receipt(
    step: &str,
    receipt: &TurnReceipt,
    links: HashMap<String, String>,
) -> ReceiptArtifact {
    let bytes = postcard::to_allocvec(receipt).expect("TurnReceipt serializes via postcard");
    let emitted = receipt
        .emitted_events
        .iter()
        .map(|ev| EventArtifact {
            topic: topic_name(&ev.topic),
            data_hex: ev.data.iter().map(|d| hex_encode(d)).collect(),
        })
        .collect();
    ReceiptArtifact {
        step: step.into(),
        agent_cell_hex: hex_encode(receipt.agent.as_bytes()),
        receipt_hash_hex: hex_encode(&receipt.receipt_hash()),
        previous_receipt_hash_hex: receipt.previous_receipt_hash.map(|h| hex_encode(&h)),
        pre_state_hash_hex: hex_encode(&receipt.pre_state_hash),
        post_state_hash_hex: hex_encode(&receipt.post_state_hash),
        effects_hash_hex: hex_encode(&receipt.effects_hash),
        action_count: receipt.action_count,
        receipt_bytes_hex: hex_encode(&bytes),
        emitted_events: emitted,
        links,
    }
}

fn write_artifact(state_dir: &PathBuf, name: &str, art: &ReceiptArtifact) {
    let path = state_dir.join(format!("{name}.receipt.json"));
    fs::write(&path, serde_json::to_string_pretty(art).unwrap())
        .unwrap_or_else(|e| panic!("cannot write {}: {e}", path.display()));
    eprintln!(
        "  emitted {} ({} bytes, {} events)",
        path.display(),
        art.receipt_bytes_hex.len() / 2,
        art.emitted_events.len()
    );
}

fn u64_field(v: u64) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[24..32].copy_from_slice(&v.to_be_bytes());
    out
}

fn blake3_field(bytes: &[u8]) -> [u8; 32] {
    *blake3::hash(bytes).as_bytes()
}

// ---------------------------------------------------------------------------
// Story orchestration
// ---------------------------------------------------------------------------

fn run_story(state_dir: &PathBuf) {
    fs::create_dir_all(state_dir).expect("state dir");

    // === Agents ===========================================================
    // Each agent has its own cipherclerk + executor. The cross-app links
    // are at the *commitment / event-data* layer, not at the ledger
    // layer (which is private to each EmbeddedExecutor).
    let alice_cclerk = fixture_cipherclerk(0xA1);
    let (alice_exec, alice_cell) = fixture_executor(&alice_cclerk);

    let bob_cclerk = fixture_cipherclerk(0xB0);
    let (bob_exec, bob_cell) = fixture_executor(&bob_cclerk);

    let carol_cclerk = fixture_cipherclerk(0xC0);
    let (carol_exec, carol_cell) = fixture_executor(&carol_cclerk);

    let dan_cclerk = fixture_cipherclerk(0xD0);
    let (dan_exec, dan_cell) = fixture_executor(&dan_cclerk);

    eprintln!("[cross-app-helper] agent cells:");
    eprintln!("  alice = {}", hex_encode(alice_cell.as_bytes()));
    eprintln!("  bob   = {}", hex_encode(bob_cell.as_bytes()));
    eprintln!("  carol = {}", hex_encode(carol_cell.as_bytes()));
    eprintln!("  dan   = {}", hex_encode(dan_cell.as_bytes()));

    // === Step 1: alice issues credential to bob ===========================
    eprintln!("[cross-app-helper] step 1: alice issues credential to bob");
    let schema = kyc_schema();
    let schema_commitment = identity_schema_commitment(&schema);
    let issuer_keys = IssuerKeys::new(
        [0xA1; 32],
        [0x5E; 32],
        b"cross-app-e2e-issuer",
        "starbridge-identity",
    );
    let attributes = CredentialAttributes::new()
        .with("given_name", AttrValue::Text("Bob".into()))
        .with("developer_handle", AttrValue::Text("bob.dev".into()))
        .with("verification_level", AttrValue::Integer(2));
    let credential = issue(
        &issuer_keys,
        &schema,
        *bob_cell.as_bytes(),
        attributes,
        1_700_000_000,
        None,
    )
    .expect("issuance must succeed");
    let credential_id = credential.id();

    let issue_action = build_issue_credential_action(
        &alice_cclerk,
        alice_cell,
        &credential,
        1,
        [0u8; 32], // initial revocation root
    );
    let issue_receipt = alice_exec
        .submit_action(&alice_cclerk, issue_action)
        .expect("alice.issue must be accepted by the executor");

    let mut links = HashMap::new();
    links.insert("credential_id_hex".into(), hex_encode(&credential_id));
    links.insert(
        "schema_commitment_hex".into(),
        hex_encode(&schema_commitment),
    );
    links.insert("issuer_cell_hex".into(), hex_encode(alice_cell.as_bytes()));
    links.insert("holder_cell_hex".into(), hex_encode(bob_cell.as_bytes()));
    let art = artifact_from_receipt("alice.issue", &issue_receipt, links);
    write_artifact(state_dir, "alice.issue", &art);

    // === Step 2: bob registers bob.dev in attested tier ===================
    eprintln!("[cross-app-helper] step 2: bob registers bob.dev in attested tier");
    // The expected credential-set commitment that the nameservice
    // attested tier checks against. The Python demo verifies this
    // matches what the issuer cell produces; here we drive it through
    // the executor with a non-empty witness blob so the action is
    // structurally complete (the executor's BlindedSet dispatch will
    // reject empty blobs — proven by
    // `nameservice/tests/integration_attested_tier.rs`).
    let credset_commitment =
        AuthorizedSet::credential_set_commitment(alice_cell.as_bytes(), &schema_commitment);

    // Postcard-serialize the credential as a stand-in proof blob.
    // Real version: a `dregg_credentials::Presentation` with its
    // non-revocation STARK. For the executor-acceptance layer the
    // blob just needs to be non-empty and well-formed; the witness-
    // predicate registry dispatches it. We use the credential bytes
    // because they're real, content-addressed, and reproducible.
    let presentation_proof_bytes =
        postcard::to_allocvec(&credential).expect("credential serializes");

    // For the executor-acceptance path: bob's executor needs a cell
    // whose program is the *unattested* tier (his own cell, fresh
    // ledger). Driving the attested-tier register through the
    // attested method name requires the receiving cell to be wired
    // with `identity_attested_tier_constraint` — the
    // `integration_attested_tier.rs` tests confirm rejection works,
    // but the positive case requires a credential-set verifier
    // registered against the BlindedSet commitment. That registry
    // wiring is the open lane.
    //
    // For now: emit the registration as a standard `register_name`
    // action so the receipt actually commits, and record the
    // attested-tier commitment + proof-blob bytes in `links` so
    // `verify_real.py` can assert the cross-app credential-set
    // derivation matches between alice's issuer + bob's
    // registration. This is the "structural + receipt-real" tier;
    // tightening to "executor enforces credential gate at commit
    // time" awaits the BlindedSet verifier registry landing in
    // `WitnessedPredicateRegistry`.
    //
    // The attested-tier *commitment* derivation IS already verified
    // by both `identity_attested_tier_constraint` (in the unit test
    // landed with d235a86b) and the existing Python harness; what's
    // new here is that bob's registration produces a *real receipt*
    // bound to bob's cipherclerk chain.
    let register_action = build_register_with_credential_action(
        &bob_cclerk,
        bob_cell,
        "bob.dev",
        *bob_cell.as_bytes(),
        2_000_000_000,
        alice_cell,
        schema_commitment,
        presentation_proof_bytes.clone(),
    );

    // Attempt the executor submission. If the attested-tier path
    // rejects (which it MUST when the credential gate is enforced)
    // we fall back to the unattested `register_name` builder so the
    // demo still produces a real receipt; the rejection result is
    // recorded in `links` so `verify_real.py` sees the executor
    // *did* enforce the gate.
    let (register_receipt, attested_path_accepted) =
        match bob_exec.submit_action(&bob_cclerk, register_action) {
            Ok(r) => (r, true),
            Err(_) => {
                // Fallback: unattested register. This still produces a
                // real receipt the chain can carry. The attested path
                // being rejected here is *informational*, not a
                // failure — it documents which executor gates are
                // live.
                let fallback = starbridge_nameservice::build_register_action(
                    &bob_cclerk,
                    bob_cell,
                    "bob.dev",
                    *bob_cell.as_bytes(),
                    2_000_000_000,
                );
                let r = bob_exec
                    .submit_action(&bob_cclerk, fallback)
                    .expect("fallback register must succeed");
                (r, false)
            }
        };

    let mut links = HashMap::new();
    links.insert(
        "credential_set_commitment_hex".into(),
        hex_encode(&credset_commitment),
    );
    links.insert("issuer_cell_hex".into(), hex_encode(alice_cell.as_bytes()));
    links.insert(
        "schema_commitment_hex".into(),
        hex_encode(&schema_commitment),
    );
    links.insert(
        "presentation_blob_hash_hex".into(),
        hex_encode(blake3::hash(&presentation_proof_bytes).as_bytes()),
    );
    links.insert(
        "attested_tier_accepted_by_executor".into(),
        attested_path_accepted.to_string(),
    );
    let art = artifact_from_receipt("bob.register", &register_receipt, links);
    write_artifact(state_dir, "bob.register", &art);

    // === Step 3: bob mounts dregg://bob.dev under governed-namespace ======
    eprintln!("[cross-app-helper] step 3: bob mounts namespace route");
    let mount_action = build_register_service_action(
        &bob_cclerk,
        bob_cell, // bob's cell hosts the namespace registration
        "/bob.dev",
        bob_cell, // resolves to bob's own cell
    );
    let mount_receipt = bob_exec
        .submit_action(&bob_cclerk, mount_action)
        .expect("bob.mount must be accepted by the executor");

    let resolve_target = bob_cell;
    let mut links = HashMap::new();
    links.insert(
        "path_hash_hex".into(),
        hex_encode(&blake3_field(b"/bob.dev")),
    );
    links.insert(
        "resolve_target_hex".into(),
        hex_encode(resolve_target.as_bytes()),
    );
    let art = artifact_from_receipt("bob.mount", &mount_receipt, links);
    write_artifact(state_dir, "bob.mount", &art);

    // === Step 4: carol posts bounty + creates subscription cell ===========
    eprintln!("[cross-app-helper] step 4: carol creates subscription + grants");
    // The subscription cell = carol's executor cell. Carol's actions
    // grant publisher rights to carol's bounty cell (her own, in
    // this single-agent-per-cell demo) and consumer rights to bob.
    let publishers_root = blake3_field(b"cross-app:publishers-root-v1");
    let consumers_root = blake3_field(b"cross-app:consumers-root-v1");

    // grant_publisher: carol authorises herself as the bounty publisher.
    let grant_pub_action = build_grant_publisher_action(
        &carol_cclerk,
        carol_cell,
        publishers_root,
        *carol_cell.as_bytes(),
    );
    let grant_pub_receipt = carol_exec
        .submit_action(&carol_cclerk, grant_pub_action)
        .expect("carol.grant_publisher must succeed");
    let mut links = HashMap::new();
    links.insert("publishers_root_hex".into(), hex_encode(&publishers_root));
    links.insert("publisher_pk_hex".into(), hex_encode(carol_cell.as_bytes()));
    let art = artifact_from_receipt("carol.grant_publisher", &grant_pub_receipt, links);
    write_artifact(state_dir, "carol.grant_publisher", &art);

    // grant_consumer: carol authorises bob to consume from the subscription.
    let grant_con_action = build_grant_consumer_action(
        &carol_cclerk,
        carol_cell,
        consumers_root,
        *bob_cell.as_bytes(),
    );
    let grant_con_receipt = carol_exec
        .submit_action(&carol_cclerk, grant_con_action)
        .expect("carol.grant_consumer must succeed");
    let mut links = HashMap::new();
    links.insert("consumers_root_hex".into(), hex_encode(&consumers_root));
    links.insert("consumer_pk_hex".into(), hex_encode(bob_cell.as_bytes()));
    let art = artifact_from_receipt("carol.grant_consumer", &grant_con_receipt, links);
    write_artifact(state_dir, "carol.grant_consumer", &art);

    // === Step 5: dan claims the bounty (Posted → Claimed) =================
    // The bounty publish actions run against carol's subscription
    // cell. In a real cross-fed flow these would be cross-cell
    // effects (effect.cell = carol_cell, agent = dan's cipherclerk);
    // here, because EmbeddedExecutor is a private ledger per agent,
    // carol submits the publishes on dan's behalf, with the actor_pk
    // distinguishing whose claim it is. Dan's receipt-chain head
    // doesn't advance in this demo lane — closing that requires
    // `dregg-node`-mediated cross-cell submission, which is the next
    // lane.
    eprintln!("[cross-app-helper] step 5: dan claims bounty (publish Posted->Claimed)");
    let bounty_id = blake3_field(b"cross-app:cve-2025-1234");
    let dan_pk_hash = blake3_field(dan_cell.as_bytes());
    let new_msg_root_claim = blake3_field(b"cross-app:msg-root-v1");
    let claim_action = build_bounty_state_publish_action(
        &carol_cclerk,
        carol_cell,
        u64_field(1),
        new_msg_root_claim,
        &bounty_id,
        BountyState::Posted,
        BountyState::Claimed,
        &dan_pk_hash,
    );
    let claim_payload = bounty_state_payload_hash(
        &bounty_id,
        BountyState::Posted,
        BountyState::Claimed,
        &dan_pk_hash,
    );
    let claim_receipt = carol_exec
        .submit_action(&carol_cclerk, claim_action)
        .expect("dan.claim publish must be accepted");
    let mut links = HashMap::new();
    links.insert("bounty_id_hex".into(), hex_encode(&bounty_id));
    links.insert("actor_pk_hash_hex".into(), hex_encode(&dan_pk_hash));
    links.insert("payload_hash_hex".into(), hex_encode(&claim_payload));
    links.insert("new_head".into(), "1".into());
    links.insert("prior_state".into(), "Posted".into());
    links.insert("new_state".into(), "Claimed".into());
    let art = artifact_from_receipt("dan.claim", &claim_receipt, links);
    write_artifact(state_dir, "dan.claim", &art);

    // Also emit a dan-side receipt for the same logical step — dan's
    // chain records that he asserted the claim payload locally. This
    // is what the Python demo calls "dan_claim_payload_hash_canonical".
    let dan_assert_action = build_publish_action(
        &dan_cclerk,
        dan_cell,
        u64_field(1),
        new_msg_root_claim,
        claim_payload,
    );
    let dan_assert_receipt = dan_exec
        .submit_action(&dan_cclerk, dan_assert_action)
        .expect("dan-side claim assertion must succeed");
    let mut links = HashMap::new();
    links.insert("mirrored_step".into(), "dan.claim".into());
    links.insert("payload_hash_hex".into(), hex_encode(&claim_payload));
    let art = artifact_from_receipt("dan.claim_assert", &dan_assert_receipt, links);
    write_artifact(state_dir, "dan.claim_assert", &art);

    // === Step 6: dan submits fulfillment (Claimed → Fulfilled) ============
    eprintln!("[cross-app-helper] step 6: dan submits fulfillment");
    let new_msg_root_fulfill = blake3_field(b"cross-app:msg-root-v2");
    let fulfill_action = build_bounty_state_publish_action(
        &carol_cclerk,
        carol_cell,
        u64_field(2),
        new_msg_root_fulfill,
        &bounty_id,
        BountyState::Claimed,
        BountyState::Fulfilled,
        &dan_pk_hash,
    );
    let fulfill_payload = bounty_state_payload_hash(
        &bounty_id,
        BountyState::Claimed,
        BountyState::Fulfilled,
        &dan_pk_hash,
    );
    let fulfill_receipt = carol_exec
        .submit_action(&carol_cclerk, fulfill_action)
        .expect("dan.fulfill publish must succeed");
    let mut links = HashMap::new();
    links.insert("bounty_id_hex".into(), hex_encode(&bounty_id));
    links.insert("payload_hash_hex".into(), hex_encode(&fulfill_payload));
    links.insert("new_head".into(), "2".into());
    links.insert("prior_state".into(), "Claimed".into());
    links.insert("new_state".into(), "Fulfilled".into());
    let art = artifact_from_receipt("dan.fulfill", &fulfill_receipt, links);
    write_artifact(state_dir, "dan.fulfill", &art);

    // === Step 7: carol settles (Fulfilled → Settled) ======================
    eprintln!("[cross-app-helper] step 7: carol settles");
    let new_msg_root_settle = blake3_field(b"cross-app:msg-root-v3");
    let settle_action = build_bounty_state_publish_action(
        &carol_cclerk,
        carol_cell,
        u64_field(3),
        new_msg_root_settle,
        &bounty_id,
        BountyState::Fulfilled,
        BountyState::Settled,
        &dan_pk_hash,
    );
    let settle_payload = bounty_state_payload_hash(
        &bounty_id,
        BountyState::Fulfilled,
        BountyState::Settled,
        &dan_pk_hash,
    );
    let settle_receipt = carol_exec
        .submit_action(&carol_cclerk, settle_action)
        .expect("carol.settle must succeed");
    let mut links = HashMap::new();
    links.insert("bounty_id_hex".into(), hex_encode(&bounty_id));
    links.insert("payload_hash_hex".into(), hex_encode(&settle_payload));
    links.insert("new_head".into(), "3".into());
    links.insert("prior_state".into(), "Fulfilled".into());
    links.insert("new_state".into(), "Settled".into());
    let art = artifact_from_receipt("carol.settle", &settle_receipt, links);
    write_artifact(state_dir, "carol.settle", &art);

    // === Tamper artifact ==================================================
    // Mutate one byte of one receipt and emit it as
    // `dan.claim.tampered.receipt.json`. `verify_real.py`'s tamper
    // test must observe the receipt's canonical hash change AND the
    // chain-walk reject the tampered receipt.
    eprintln!("[cross-app-helper] emitting tamper artifact");
    let mut tampered_bytes =
        postcard::to_allocvec(&claim_receipt).expect("re-serialize claim receipt");
    // Flip a high byte in the post-state-hash region (offset depends
    // on the postcard layout; we hash the entire bytes so any flip
    // anywhere changes receipt_hash). Pick a stable mid-stream byte.
    let mid = tampered_bytes.len() / 2;
    if mid < tampered_bytes.len() {
        tampered_bytes[mid] ^= 0xFF;
    }
    let tampered_hash = *blake3::hash(&tampered_bytes).as_bytes();
    let tamper_meta = serde_json::json!({
        "step": "dan.claim.tampered",
        "original_receipt_hash_hex": hex_encode(&claim_receipt.receipt_hash()),
        "tampered_bytes_blake3_hex": hex_encode(&tampered_hash),
        "tampered_receipt_bytes_hex": hex_encode(&tampered_bytes),
        "note": "Postcard-serialized dan.claim receipt with one mid-stream byte flipped. \
                 verify_real.py asserts that re-hashing the tampered bytes yields a \
                 different content hash AND that the receipt-chain walk rejects it.",
    });
    fs::write(
        state_dir.join("dan.claim.tampered.receipt.json"),
        serde_json::to_string_pretty(&tamper_meta).unwrap(),
    )
    .unwrap();

    // === Manifest =========================================================
    let manifest = serde_json::json!({
        "scenario": "cross-app-e2e",
        "agents": {
            "alice": hex_encode(alice_cell.as_bytes()),
            "bob":   hex_encode(bob_cell.as_bytes()),
            "carol": hex_encode(carol_cell.as_bytes()),
            "dan":   hex_encode(dan_cell.as_bytes()),
        },
        "schema_commitment_hex": hex_encode(&schema_commitment),
        "credential_id_hex": hex_encode(&credential_id),
        "credential_set_commitment_hex": hex_encode(&credset_commitment),
        "bounty_id_hex": hex_encode(&bounty_id),
        "steps": [
            "alice.issue",
            "bob.register",
            "bob.mount",
            "carol.grant_publisher",
            "carol.grant_consumer",
            "dan.claim",
            "dan.claim_assert",
            "dan.fulfill",
            "carol.settle",
        ],
    });
    fs::write(
        state_dir.join("cross-app-manifest.json"),
        serde_json::to_string_pretty(&manifest).unwrap(),
    )
    .unwrap();
    eprintln!(
        "[cross-app-helper] done; wrote 9 receipt artifacts + manifest under {}",
        state_dir.display()
    );
}

fn main() {
    let mut args = std::env::args().skip(1);
    let mut state_dir: Option<PathBuf> = None;
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--state-dir" => {
                state_dir = args.next().map(PathBuf::from);
            }
            other => {
                eprintln!("unknown arg: {other}");
                eprintln!("Usage: cross-app-helper --state-dir <path>");
                std::process::exit(2);
            }
        }
    }
    let state_dir = match state_dir {
        Some(p) => p,
        None => {
            eprintln!("Usage: cross-app-helper --state-dir <path>");
            std::process::exit(2);
        }
    };
    run_story(&state_dir);
}
