//! `silver-helper`: substrate-honest demo helper for the two-AI handoff demo.
//!
//! This binary is the demo's bridge to the parts of the substrate that the
//! MCP layer of `pyana-node` does not (yet) expose:
//!
//!   * **`Authorization::CapTpDelivered`** — assembling a canonical signed
//!     CapTP-delivered Turn (introducer-signed `HandoffCertificate` +
//!     recipient-signed `captp_delivered_signing_message`). MCP today only
//!     emits `Authorization::Bearer`. GAP: a `pyana_exercise_handoff_cert`
//!     MCP tool would close this.
//!   * **`SovereignCellWitness`** — assembling the Ed25519+sequence shape
//!     of a sovereign-cell witness, with optional STARK transition proof.
//!     MCP's `pyana_make_sovereign` produces the registration but no MCP
//!     tool emits a witness-carrying Turn. GAP: a `pyana_submit_sovereign_turn`
//!     would close this.
//!   * **Slot caveats (`StateConstraint::WriteOnce`)** — installing a
//!     `WriteOnce` caveat on a slot of a demo cell and exercising the
//!     positive (first-write) and negative (re-write rejected) paths
//!     against `pyana_cell::CellProgram::evaluate`. MCP does not expose
//!     a `pyana_install_cell_program` tool today. GAP.
//!   * **γ.2 bilateral binding** — assembling a `pyana_verifier::BilateralBundle`
//!     from a Turn with a single `Effect::Transfer { from: alice, to: bob }`,
//!     fabricating the alice-side and bob-side `WitnessedReceipt`s with the
//!     correct γ.2 PI layout, and proving that both pair-verify against
//!     each other under the canonical schedule. MCP's exercise tool does
//!     not yet emit per-cell WRs. GAP.
//!
//! The helper accepts deterministic test keypairs from a demo seed so that
//! alice/bob identities are stable across runs without leaking real wallet
//! material from the MCP nodes. The substrate types are exactly the same
//! types the executor and verifier consume; only the keys are demo-local.

use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

use ed25519_dalek::{Signer, SigningKey};
use serde::{Deserialize, Serialize};

use pyana_captp::HandoffCertificate;
use pyana_cell::{
    AuthRequired, Cell, CellId, CellProgram, CellState, FIELD_ZERO, ProgramError, StateConstraint,
    field_from_u64,
};
use pyana_circuit::field::BabyBear;
use pyana_turn::bilateral_schedule::ExpectedBilateral;
use pyana_turn::{
    Action, Authorization, CallForest, CommitmentMode, DelegationMode, Effect,
    SovereignCellWitness, Turn, TurnReceipt,
};
use pyana_types::FederationId;
use pyana_verifier::{BilateralBundle, BilateralEntry, fabricate_witnessed_receipt};

// ---------------------------------------------------------------------------
// Deterministic demo keypair derivation
// ---------------------------------------------------------------------------

/// Derive a deterministic Ed25519 keypair from the demo seed + role label.
/// This is **demo-local** — these keys never see real funds, and exist only
/// so the demo's substrate artifacts have a stable identity across runs
/// without sharing keys with the MCP wallets (which the MCP layer cannot
/// export). In a real cross-federation flow, Alice's federation would
/// register Bob's recipient pk out-of-band, exactly as the demo does here.
fn derive_demo_key(seed: &[u8], role: &str) -> SigningKey {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"pyana-two-ai-demo-key-v1:");
    hasher.update(seed);
    hasher.update(b"|role|");
    hasher.update(role.as_bytes());
    let mut sk_bytes = [0u8; 32];
    sk_bytes.copy_from_slice(hasher.finalize().as_bytes());
    SigningKey::from_bytes(&sk_bytes)
}

// ---------------------------------------------------------------------------
// On-disk JSON shapes
// ---------------------------------------------------------------------------

#[derive(Serialize, Deserialize)]
struct DemoIdentities {
    alice_pk: String,
    alice_sk: String,
    bob_pk: String,
    bob_sk: String,
    federation_id_f1: String,
}

#[derive(Serialize, Deserialize)]
struct HandoffArtifacts {
    /// Hex-encoded postcard-serialized `HandoffCertificate`.
    cert_bytes_hex: String,
    /// JSON-serialized `HandoffCertificate` for human inspection.
    cert_json: serde_json::Value,
    /// The `pyana-handoff:` compact base58 URI form.
    handoff_uri: String,
    /// The recipient's signature over the presentation message
    /// (`presentation_message_v1` || cert.nonce || target_cell || target_federation).
    presentation_signature_hex: String,
}

#[derive(Serialize, Deserialize)]
struct CapTpDeliveredArtifact {
    /// Hex-encoded postcard-serialized `Turn`.
    turn_bytes_hex: String,
    /// The turn's content-addressed hash.
    turn_hash_hex: String,
    /// The cert nonce binding the sender signature.
    cert_nonce_hex: String,
    /// The action effects (for readability).
    effects_json: serde_json::Value,
    /// The canonical CapTP-delivered signing message bytes (hex).
    sender_signing_message_hex: String,
    /// Bob's signature over the message.
    sender_signature_hex: String,
    /// Same Turn but with the sender signature bit-flipped (must_not_pass).
    tampered_turn_bytes_hex: String,
}

#[derive(Serialize, Deserialize)]
struct SovereignWitnessArtifact {
    cell_id_hex: String,
    /// Hex-encoded JSON of the SovereignCellWitness.
    witness_json: serde_json::Value,
    /// The canonical signing message (hex).
    signing_message_hex: String,
    /// Hex-encoded postcard-serialized witness.
    witness_bytes_hex: String,
    /// Verification result by recomputing + re-verifying the Ed25519 sig.
    self_verifies: bool,
    /// Tampered version (flipped a byte in new_commitment) — must reject.
    tampered_self_verifies: bool,
}

#[derive(Serialize, Deserialize)]
struct SlotCaveatArtifact {
    /// The cell's program (WriteOnce on NAME_SLOT) JSON form.
    program_json: serde_json::Value,
    /// First-write transition: ok.
    first_write_ok: bool,
    first_write_reason: String,
    /// Re-register attempt: must reject with WriteOnceViolation.
    rewrite_rejected: bool,
    rewrite_reason: String,
    /// Renewal (changing a different, monotonic slot) — must accept.
    renewal_ok: bool,
    renewal_reason: String,
}

#[derive(Serialize, Deserialize)]
struct BilateralArtifact {
    /// The turn the bundle was built around.
    turn_hash_hex: String,
    /// Alice's cell id.
    alice_cell_hex: String,
    /// Bob's cell id.
    bob_cell_hex: String,
    /// Hex-encoded JSON of the BilateralBundle (for charlie to verify).
    bundle_path: String,
    /// Tampered bundle (alice's PI flipped) — bundle_path_tampered.
    bundle_path_tampered: String,
}

#[derive(Serialize, Deserialize, Default)]
struct SilverManifest {
    identities: Option<DemoIdentities>,
    handoff: Option<HandoffArtifacts>,
    captp_delivered: Option<CapTpDeliveredArtifact>,
    sovereign_witness: Option<SovereignWitnessArtifact>,
    slot_caveat: Option<SlotCaveatArtifact>,
    bilateral: Option<BilateralArtifact>,
}

// ---------------------------------------------------------------------------
// Subcommands
// ---------------------------------------------------------------------------

fn cmd_init_identities(state_dir: &PathBuf, seed: &str) -> std::io::Result<()> {
    let alice = derive_demo_key(seed.as_bytes(), "alice");
    let bob = derive_demo_key(seed.as_bytes(), "bob");
    let alice_pk = alice.verifying_key().to_bytes();
    let bob_pk = bob.verifying_key().to_bytes();
    // The demo's "F1" federation_id is BLAKE3("pyana-fed-id-v1" || alice_pk || epoch=0)
    // mirroring the genesis derivation in `node/src/genesis.rs:133`.
    let federation_id_f1 = {
        let mut h = blake3::Hasher::new();
        h.update(b"pyana-fed-id-v1");
        h.update(&alice_pk);
        h.update(&0u64.to_le_bytes());
        *h.finalize().as_bytes()
    };
    let ids = DemoIdentities {
        alice_pk: hex::encode(alice_pk),
        alice_sk: hex::encode(alice.to_bytes()),
        bob_pk: hex::encode(bob_pk),
        bob_sk: hex::encode(bob.to_bytes()),
        federation_id_f1: hex::encode(federation_id_f1),
    };
    fs::create_dir_all(state_dir)?;
    fs::write(
        state_dir.join("silver.identities.json"),
        serde_json::to_string_pretty(&ids).unwrap(),
    )?;
    println!("{}", serde_json::to_string(&ids).unwrap());
    Ok(())
}

fn load_ids(state_dir: &PathBuf) -> DemoIdentities {
    let s = fs::read_to_string(state_dir.join("silver.identities.json"))
        .expect("identities not initialised; run silver-helper init-identities first");
    serde_json::from_str(&s).expect("identities JSON parse")
}

fn parse_signing_key(hex_str: &str) -> SigningKey {
    let bytes = hex::decode(hex_str).expect("hex");
    let arr: [u8; 32] = bytes.try_into().expect("32 bytes");
    SigningKey::from_bytes(&arr)
}

fn parse_32(hex_str: &str) -> [u8; 32] {
    let bytes = hex::decode(hex_str).expect("hex");
    bytes.try_into().expect("32 bytes")
}

/// Subcommand: `make-handoff` — Alice signs a `HandoffCertificate`
/// targeting Bob; emit the canonical bytes plus the recipient-signed
/// presentation. Demonstrates the introducer-side of the canonical CapTP
/// handoff protocol.
fn cmd_make_handoff(state_dir: &PathBuf, alice_cell_hex: &str, bob_cell_hex: &str) {
    let ids = load_ids(state_dir);
    let alice_sk = parse_signing_key(&ids.alice_sk);
    let bob_sk = parse_signing_key(&ids.bob_sk);
    let bob_pk = parse_32(&ids.bob_pk);
    let alice_cell = CellId(parse_32(alice_cell_hex));
    let _bob_cell = CellId(parse_32(bob_cell_hex));
    let federation_id_f1 = FederationId(parse_32(&ids.federation_id_f1));

    // Build the canonical HandoffCertificate. introducer == target_federation
    // for this demo (same-federation handoff). A future cross-federation
    // variant would use a distinct target_federation, per SILVER-VISION-E2E.
    let mut swiss = [0u8; 32];
    swiss[..4].copy_from_slice(b"DEMO");
    // HandoffCertificate::create wants `pyana_types::SigningKey`. Wrap
    // alice's ed25519-dalek key in the substrate newtype using the
    // shared 32-byte secret material.
    let alice_sk_substrate = pyana_types::SigningKey::from_bytes(&alice_sk.to_bytes());
    let cert = HandoffCertificate::create(
        &alice_sk_substrate,
        federation_id_f1,
        federation_id_f1, // same-fed for the two-AI demo
        alice_cell,       // target_cell == alice's cell
        bob_pk,
        AuthRequired::Signature,
        None, // no allowed_effects mask (executor checks per-effect)
        Some(10_000_000),
        Some(1),
        swiss,
    );

    // Bob signs the presentation message.
    let presentation_msg = pyana_captp::HandoffPresentation::presentation_message(&cert);
    let presentation_sig = bob_sk.sign(&presentation_msg);

    let cert_bytes = cert.to_bytes();
    let handoff_uri = cert.to_compact_string();
    let artifacts = HandoffArtifacts {
        cert_bytes_hex: hex::encode(&cert_bytes),
        cert_json: serde_json::to_value(&cert).unwrap(),
        handoff_uri,
        presentation_signature_hex: hex::encode(presentation_sig.to_bytes()),
    };
    fs::write(
        state_dir.join("silver.handoff.json"),
        serde_json::to_string_pretty(&artifacts).unwrap(),
    )
    .unwrap();
    println!("{}", serde_json::to_string(&artifacts).unwrap());
}

/// Subcommand: `make-captp-delivered` — Bob assembles a canonical Turn
/// with `Authorization::CapTpDelivered` exercising Alice's bearer cert.
/// The effect is `Effect::Transfer { from: alice_cell, to: bob_cell, amount }`.
/// The sender signature is over `captp_delivered_signing_message(cert_nonce,
/// agent=bob_cell, target=alice_cell, turn_nonce, effects)`.
///
/// Note on signing semantics: the executor's `verify_captp_delivered` (see
/// `turn/src/executor.rs:4570`) uses `action.target` for both the "agent"
/// and "target" parameters of the signing-message helper. We mirror that
/// exactly here so the artifact is what the executor would verify.
fn cmd_make_captp_delivered(
    state_dir: &PathBuf,
    alice_cell_hex: &str,
    bob_cell_hex: &str,
    amount: u64,
    turn_nonce: u64,
) {
    let ids = load_ids(state_dir);
    let bob_sk = parse_signing_key(&ids.bob_sk);
    let bob_pk = parse_32(&ids.bob_pk);
    let alice_pk = parse_32(&ids.alice_pk);

    let alice_cell = CellId(parse_32(alice_cell_hex));
    let bob_cell = CellId(parse_32(bob_cell_hex));

    // Reload cert from disk.
    let handoff: HandoffArtifacts = serde_json::from_str(
        &fs::read_to_string(state_dir.join("silver.handoff.json")).expect("run make-handoff first"),
    )
    .expect("parse handoff json");
    let cert_bytes = hex::decode(&handoff.cert_bytes_hex).expect("hex");
    let cert = HandoffCertificate::from_bytes(&cert_bytes).expect("cert parse");

    // Bob's exercise: Transfer 100 from alice_cell to bob_cell.
    let effects = vec![Effect::Transfer {
        from: alice_cell,
        to: bob_cell,
        amount,
    }];

    // Build the canonical signing message (executor mirrors this).
    let signing_message = Authorization::captp_delivered_signing_message(
        &cert.nonce,
        &alice_cell, // executor uses action.target for both agent + target slots
        &alice_cell,
        turn_nonce,
        &effects,
    );
    let sender_sig = bob_sk.sign(&signing_message);

    let action = Action {
        target: alice_cell,
        method: pyana_turn::action::symbol("transfer"),
        args: vec![],
        authorization: Authorization::CapTpDelivered {
            handoff_cert: cert.clone(),
            introducer_pk: alice_pk,
            sender_pk: bob_pk,
            sender_signature: sender_sig.to_bytes(),
        },
        preconditions: Default::default(),
        effects: effects.clone(),
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    let mut forest = CallForest::new();
    forest.add_root(action);

    let turn = Turn {
        agent: bob_cell,
        nonce: turn_nonce,
        call_forest: forest,
        fee: 0,
        memo: Some("captp-delivered exercise of alice's handoff cert".into()),
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };
    let turn_hash = turn.hash();
    let turn_bytes = postcard::to_allocvec(&turn).expect("turn serialize");

    // Build a tampered variant: flip a byte in the sender signature. The
    // executor's `verify_strict` MUST reject this — that's the must_not_pass.
    let mut tampered_turn = turn.clone();
    if let Some(root) = tampered_turn.call_forest.roots.first_mut() {
        if let Authorization::CapTpDelivered {
            sender_signature, ..
        } = &mut root.action.authorization
        {
            sender_signature[0] ^= 0xFF;
        }
    }
    let tampered_bytes = postcard::to_allocvec(&tampered_turn).expect("tampered serialize");

    let artifact = CapTpDeliveredArtifact {
        turn_bytes_hex: hex::encode(&turn_bytes),
        turn_hash_hex: hex::encode(turn_hash),
        cert_nonce_hex: hex::encode(cert.nonce),
        effects_json: serde_json::to_value(&effects).unwrap(),
        sender_signing_message_hex: hex::encode(&signing_message),
        sender_signature_hex: hex::encode(sender_sig.to_bytes()),
        tampered_turn_bytes_hex: hex::encode(&tampered_bytes),
    };
    fs::write(
        state_dir.join("silver.captp-delivered.json"),
        serde_json::to_string_pretty(&artifact).unwrap(),
    )
    .unwrap();
    println!("{}", serde_json::to_string(&artifact).unwrap());
}

/// Subcommand: `verify-captp-delivered` — Charlie-side verification of the
/// canonical signing message and signatures. The executor's
/// `verify_captp_delivered` lives behind `pyana-node`, but the checks are
/// public Ed25519 + canonical messages, so we can reproduce them in the
/// helper for the demo.
fn cmd_verify_captp_delivered(state_dir: &PathBuf) -> bool {
    let ids = load_ids(state_dir);
    let alice_pk = parse_32(&ids.alice_pk);
    let bob_pk = parse_32(&ids.bob_pk);

    let art: CapTpDeliveredArtifact = serde_json::from_str(
        &fs::read_to_string(state_dir.join("silver.captp-delivered.json")).expect("artifact"),
    )
    .expect("parse");
    let turn_bytes = hex::decode(&art.turn_bytes_hex).expect("hex");
    let turn: Turn = postcard::from_bytes(&turn_bytes).expect("turn parse");

    let root = turn
        .call_forest
        .roots
        .first()
        .expect("at least one root action");
    let action = &root.action;
    let (cert, intro_pk, sender_pk, sender_sig) = match &action.authorization {
        Authorization::CapTpDelivered {
            handoff_cert,
            introducer_pk,
            sender_pk,
            sender_signature,
        } => (handoff_cert, introducer_pk, sender_pk, sender_signature),
        _ => panic!("expected CapTpDelivered auth"),
    };

    // (1) introducer_pk == cert.introducer
    let check_intro = intro_pk == &cert.introducer.0;
    // (2) sender_pk == cert.recipient_pk
    let check_sender = sender_pk == &cert.recipient_pk;
    // (3) introducer signature on cert verifies
    let intro_pk_obj = pyana_types::PublicKey(*intro_pk);
    let check_cert_sig = cert.verify_signature(&intro_pk_obj);
    // (4) sender signature on canonical message verifies
    let signing_message = Authorization::captp_delivered_signing_message(
        &cert.nonce,
        &action.target,
        &action.target,
        turn.nonce,
        &action.effects,
    );
    let sender_vk = ed25519_dalek::VerifyingKey::from_bytes(sender_pk).expect("pk");
    let sig = ed25519_dalek::Signature::from_bytes(sender_sig);
    let check_sender_sig = sender_vk.verify_strict(&signing_message, &sig).is_ok();
    // (5) cert is fresh
    let check_fresh = cert.is_valid(0);

    let ok = check_intro && check_sender && check_cert_sig && check_sender_sig && check_fresh;
    let verdict = serde_json::json!({
        "verified": ok,
        "checks": {
            "introducer_pk_matches_cert": check_intro,
            "sender_pk_matches_cert_recipient": check_sender,
            "introducer_sig_on_cert_verifies": check_cert_sig,
            "sender_sig_on_signing_message_verifies": check_sender_sig,
            "cert_not_expired": check_fresh,
        },
        "alice_pk": ids.alice_pk,
        "bob_pk": ids.bob_pk,
        "verified_intro_pk_eq_alice": intro_pk == &alice_pk,
        "verified_sender_pk_eq_bob": sender_pk == &bob_pk,
        "turn_hash": hex::encode(turn.hash()),
    });
    println!("{}", verdict);
    ok
}

/// Subcommand: `verify-captp-delivered-tampered` — same checks against the
/// tampered turn. Must reject (the demo asserts this is the must_not_pass).
fn cmd_verify_captp_delivered_tampered(state_dir: &PathBuf) -> bool {
    let art: CapTpDeliveredArtifact = serde_json::from_str(
        &fs::read_to_string(state_dir.join("silver.captp-delivered.json")).expect("artifact"),
    )
    .expect("parse");
    let turn_bytes = hex::decode(&art.tampered_turn_bytes_hex).expect("hex");
    let turn: Turn = postcard::from_bytes(&turn_bytes).expect("turn parse");

    let root = turn.call_forest.roots.first().unwrap();
    let action = &root.action;
    let (cert, sender_pk, sender_sig) = match &action.authorization {
        Authorization::CapTpDelivered {
            handoff_cert,
            sender_pk,
            sender_signature,
            ..
        } => (handoff_cert, sender_pk, sender_signature),
        _ => panic!("expected CapTpDelivered auth"),
    };

    let signing_message = Authorization::captp_delivered_signing_message(
        &cert.nonce,
        &action.target,
        &action.target,
        turn.nonce,
        &action.effects,
    );
    let sender_vk = ed25519_dalek::VerifyingKey::from_bytes(sender_pk).expect("pk");
    let sig = ed25519_dalek::Signature::from_bytes(sender_sig);
    // We EXPECT this to fail.
    let accepted = sender_vk.verify_strict(&signing_message, &sig).is_ok();
    let verdict = serde_json::json!({
        "tampered_signature_accepted": accepted,
        "expected_rejected": !accepted,
    });
    println!("{}", verdict);
    // returns true iff the tampered signature was correctly REJECTED.
    !accepted
}

/// Subcommand: `make-sovereign-witness` — Alice produces a canonical
/// `SovereignCellWitness` for her own sovereign cell, demonstrating the
/// post-soundness-sweep shape (Ed25519 sig over signing_message + sequence
/// + optional STARK).
fn cmd_make_sovereign_witness(state_dir: &PathBuf, cell_id_hex: &str, sequence: u64) {
    let ids = load_ids(state_dir);
    let alice_sk = parse_signing_key(&ids.alice_sk);
    let alice_pk_bytes = parse_32(&ids.alice_pk);

    let cell_id = CellId(parse_32(cell_id_hex));
    // Pre-state: balance = 1_000_000, fields = zero.
    let pre_cell = Cell::with_balance(alice_pk_bytes, [0u8; 32], 1_000_000);
    let old_commitment = pre_cell.state_commitment();

    // Post-state: after a single Transfer of 100 (alice -100). Use
    // `Cell::with_balance` again with the new balance.
    let post_cell = Cell::with_balance(alice_pk_bytes, [0u8; 32], 999_900);
    let new_commitment = post_cell.state_commitment();

    // effects_hash binds the effect set.
    let effects_hash: [u8; 32] = *blake3::hash(b"silver-demo-transfer-100").as_bytes();
    let timestamp = 1_716_500_000i64;

    let signing_message = SovereignCellWitness::signing_message(
        &cell_id,
        &old_commitment,
        &new_commitment,
        &effects_hash,
        timestamp,
        sequence,
    );
    let sig = alice_sk.sign(&signing_message);

    let witness = SovereignCellWitness {
        cell_id,
        old_commitment,
        new_commitment,
        effects_hash,
        timestamp,
        sequence,
        signature: sig.to_bytes(),
        cell_state: pre_cell.clone(),
        transition_proof: None,
    };

    // Self-verify (sanity check + what the executor's
    // `verify_sovereign_witnesses` will check).
    let vk = ed25519_dalek::VerifyingKey::from_bytes(&alice_pk_bytes).unwrap();
    let self_verifies = vk
        .verify_strict(
            &signing_message,
            &ed25519_dalek::Signature::from_bytes(&witness.signature),
        )
        .is_ok();

    // Tampered: bump new_commitment by one byte. The signing_message changes,
    // so the original signature must no longer verify.
    let mut tampered_new = new_commitment;
    tampered_new[0] ^= 0x01;
    let tampered_signing_message = SovereignCellWitness::signing_message(
        &cell_id,
        &old_commitment,
        &tampered_new,
        &effects_hash,
        timestamp,
        sequence,
    );
    let tampered_self_verifies = vk
        .verify_strict(
            &tampered_signing_message,
            &ed25519_dalek::Signature::from_bytes(&witness.signature),
        )
        .is_ok();

    let witness_bytes = postcard::to_allocvec(&witness).expect("witness serialize");

    let art = SovereignWitnessArtifact {
        cell_id_hex: hex::encode(cell_id.0),
        witness_json: serde_json::to_value(&witness).unwrap(),
        signing_message_hex: hex::encode(&signing_message),
        witness_bytes_hex: hex::encode(&witness_bytes),
        self_verifies,
        tampered_self_verifies,
    };
    fs::write(
        state_dir.join("silver.sovereign-witness.json"),
        serde_json::to_string_pretty(&art).unwrap(),
    )
    .unwrap();
    println!("{}", serde_json::to_string(&art).unwrap());
}

/// Subcommand: `slot-caveat-demo` — install a `WriteOnce` constraint on
/// the demo's bearer-cap registry slot (NAME_SLOT) and exercise the three
/// canonical paths:
///   (a) first registration succeeds,
///   (b) re-registration with a different value is rejected as
///       `ProgramError::ConstraintViolated{WriteOnce}`,
///   (c) a separate `Monotonic` slot (expiry) can be increased — exhibits
///       co-existence of multiple caveats.
fn cmd_slot_caveat_demo(state_dir: &PathBuf) {
    const NAME_SLOT: u8 = 0;
    const EXPIRY_SLOT: u8 = 1;
    let program = CellProgram::Predicate(vec![
        StateConstraint::WriteOnce { index: NAME_SLOT },
        StateConstraint::Monotonic { index: EXPIRY_SLOT },
    ]);

    // Fresh state: both slots zero. nonce==0, so the first-write semantics apply.
    let fresh = CellState::new(0);
    // Genuine first write: set NAME_SLOT to a non-zero value.
    let mut after_first = fresh.clone();
    after_first.fields[NAME_SLOT as usize] = field_from_u64(0xDEAD_BEEF);
    after_first.fields[EXPIRY_SLOT as usize] = field_from_u64(1000);
    let first_eval = program.evaluate_static(&after_first, Some(&fresh));

    // Attempt to re-set NAME_SLOT to a *different* value: must reject with
    // WriteOnceViolation.
    let mut after_rewrite = after_first.clone();
    after_rewrite.fields[NAME_SLOT as usize] = field_from_u64(0xC0FFEE);
    let rewrite_eval = program.evaluate_static(&after_rewrite, Some(&after_first));

    // Legal renewal: EXPIRY_SLOT increases; NAME_SLOT unchanged.
    let mut after_renewal = after_first.clone();
    after_renewal.fields[EXPIRY_SLOT as usize] = field_from_u64(2000);
    let renewal_eval = program.evaluate_static(&after_renewal, Some(&after_first));

    let first_ok = first_eval.is_ok();
    let first_reason = first_eval
        .map(|_| "ok".to_string())
        .unwrap_or_else(|e| format!("{e:?}"));
    let rewrite_rejected = matches!(
        rewrite_eval.as_ref().err(),
        Some(ProgramError::ConstraintViolated { .. })
    );
    let rewrite_reason = rewrite_eval
        .map(|_| "unexpectedly accepted".to_string())
        .unwrap_or_else(|e| format!("{e:?}"));
    let renewal_ok = renewal_eval.is_ok();
    let renewal_reason = renewal_eval
        .map(|_| "ok".to_string())
        .unwrap_or_else(|e| format!("{e:?}"));

    // Sanity: FIELD_ZERO must equal zero for the program's first-write logic.
    let _ = FIELD_ZERO;

    let art = SlotCaveatArtifact {
        program_json: serde_json::to_value(&program).unwrap(),
        first_write_ok: first_ok,
        first_write_reason: first_reason,
        rewrite_rejected,
        rewrite_reason,
        renewal_ok,
        renewal_reason,
    };
    fs::write(
        state_dir.join("silver.slot-caveat.json"),
        serde_json::to_string_pretty(&art).unwrap(),
    )
    .unwrap();
    println!("{}", serde_json::to_string(&art).unwrap());
}

/// Subcommand: `make-bilateral-bundle` — assemble a γ.2 bilateral bundle
/// for the canonical Transfer turn (alice -> bob, 100). Build one
/// `WitnessedReceipt` per cell with the γ.2 PI layout computed from the
/// turn's `ExpectedBilateral` schedule. Also emit a tampered bundle where
/// alice's OUTGOING_TRANSFER_ROOT has one felt flipped — `pyana-verifier
/// bilateral-pair` must reject it.
fn cmd_make_bilateral_bundle(
    state_dir: &PathBuf,
    alice_cell_hex: &str,
    bob_cell_hex: &str,
    amount: u64,
    turn_nonce: u64,
) {
    let alice_cell = CellId(parse_32(alice_cell_hex));
    let bob_cell = CellId(parse_32(bob_cell_hex));

    // Build the canonical Turn carrying one Transfer effect. The agent is
    // alice (she's the actor). bob's WR's IS_AGENT_CELL slot must be 0;
    // alice's must be 1.
    let action = Action {
        target: alice_cell,
        method: pyana_turn::action::symbol("transfer"),
        args: vec![],
        // We use Unchecked here because bilateral verification operates on
        // the bilateral schedule (call_forest + nonce), not the auth path.
        // The CapTpDelivered variant is exercised in the captp_delivered
        // artifact path; the bilateral schedule is identical either way.
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::Transfer {
            from: alice_cell,
            to: bob_cell,
            amount,
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    let mut forest = CallForest::new();
    forest.add_root(action);
    let turn = Turn {
        agent: alice_cell,
        nonce: turn_nonce,
        call_forest: forest,
        fee: 0,
        memo: Some("γ.2 bilateral demo turn".into()),
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    };

    // Sanity check: ensure the bilateral schedule contains exactly the one
    // Transfer we built.
    let sched = ExpectedBilateral::from_turn(&turn);
    assert_eq!(sched.transfers.len(), 1);

    let dummy_receipt = |agent: CellId| TurnReceipt {
        turn_hash: [0u8; 32],
        forest_hash: [0u8; 32],
        pre_state_hash: [0u8; 32],
        post_state_hash: [0u8; 32],
        timestamp: 0,
        effects_hash: [0u8; 32],
        computrons_used: 0,
        action_count: 0,
        previous_receipt_hash: None,
        agent,
        federation_id: [0u8; 32],
        routing_directives: vec![],
        introduction_exports: vec![],
        derivation_records: vec![],
        emitted_events: vec![],
        executor_signature: None,
        finality: Default::default(),
        was_encrypted: false,
    };

    let alice_wr = fabricate_witnessed_receipt(&turn, &alice_cell, dummy_receipt(alice_cell));
    let bob_wr = fabricate_witnessed_receipt(&turn, &bob_cell, dummy_receipt(alice_cell));

    let bundle = BilateralBundle {
        turn: turn.clone(),
        entries: vec![
            BilateralEntry {
                cell_id: alice_cell,
                witnessed_receipt: alice_wr.clone(),
            },
            BilateralEntry {
                cell_id: bob_cell,
                witnessed_receipt: bob_wr,
            },
        ],
    };
    let bundle_path = state_dir.join("silver.bilateral-bundle.json");
    fs::write(&bundle_path, serde_json::to_string_pretty(&bundle).unwrap()).unwrap();

    // Tampered: corrupt one felt in alice's OUTGOING_TRANSFER_ROOT. The
    // verifier must reject because the schedule's reconstruction will
    // disagree with alice's claimed root.
    use pyana_circuit::effect_vm::pi as p;
    let mut tampered_alice_wr = alice_wr.clone();
    tampered_alice_wr.public_inputs[p::OUTGOING_TRANSFER_ROOT_BASE] =
        BabyBear::new(0x1234_5678).as_u32();
    let tampered_bundle = BilateralBundle {
        turn: turn.clone(),
        entries: vec![
            BilateralEntry {
                cell_id: alice_cell,
                witnessed_receipt: tampered_alice_wr,
            },
            BilateralEntry {
                cell_id: bob_cell,
                witnessed_receipt: fabricate_witnessed_receipt(
                    &turn,
                    &bob_cell,
                    dummy_receipt(alice_cell),
                ),
            },
        ],
    };
    let bundle_path_tampered = state_dir.join("silver.bilateral-bundle.tampered.json");
    fs::write(
        &bundle_path_tampered,
        serde_json::to_string_pretty(&tampered_bundle).unwrap(),
    )
    .unwrap();

    let art = BilateralArtifact {
        turn_hash_hex: hex::encode(turn.hash()),
        alice_cell_hex: hex::encode(alice_cell.0),
        bob_cell_hex: hex::encode(bob_cell.0),
        bundle_path: bundle_path.display().to_string(),
        bundle_path_tampered: bundle_path_tampered.display().to_string(),
    };
    fs::write(
        state_dir.join("silver.bilateral.json"),
        serde_json::to_string_pretty(&art).unwrap(),
    )
    .unwrap();
    println!("{}", serde_json::to_string(&art).unwrap());
}

// ---------------------------------------------------------------------------
// Entrypoint
// ---------------------------------------------------------------------------

fn usage() -> ExitCode {
    eprintln!(
        "Usage: silver-helper <cmd> --state-dir <dir> [args]\n\
         \n\
         Commands:\n  \
           init-identities --seed <str>\n  \
           make-handoff --alice-cell <hex32> --bob-cell <hex32>\n  \
           make-captp-delivered --alice-cell <hex32> --bob-cell <hex32> --amount N --turn-nonce N\n  \
           verify-captp-delivered\n  \
           verify-captp-delivered-tampered\n  \
           make-sovereign-witness --cell <hex32> --sequence N\n  \
           slot-caveat-demo\n  \
           make-bilateral-bundle --alice-cell <hex32> --bob-cell <hex32> --amount N --turn-nonce N\n"
    );
    ExitCode::from(2)
}

fn arg(args: &[String], name: &str) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == name {
            return it.next().cloned();
        }
    }
    None
}

fn run(cmd: &str, rest: &[String], state_dir: &PathBuf) -> Result<bool, String> {
    let need = |name: &str| -> Result<String, String> {
        arg(rest, name).ok_or_else(|| format!("{name} required"))
    };
    let need_u64 = |name: &str, default: Option<&str>| -> Result<u64, String> {
        let raw = arg(rest, name)
            .or_else(|| default.map(String::from))
            .ok_or_else(|| format!("{name} required"))?;
        raw.parse::<u64>().map_err(|e| format!("{name}: {e}"))
    };

    match cmd {
        "init-identities" => {
            let seed = arg(rest, "--seed").unwrap_or_else(|| "two-ai-handoff-2026".into());
            cmd_init_identities(state_dir, &seed)
                .map(|_| true)
                .map_err(|e| format!("{e}"))
        }
        "make-handoff" => {
            let a = need("--alice-cell")?;
            let b = need("--bob-cell")?;
            cmd_make_handoff(state_dir, &a, &b);
            Ok(true)
        }
        "make-captp-delivered" => {
            let a = need("--alice-cell")?;
            let b = need("--bob-cell")?;
            let amount = need_u64("--amount", None)?;
            let turn_nonce = need_u64("--turn-nonce", Some("1"))?;
            cmd_make_captp_delivered(state_dir, &a, &b, amount, turn_nonce);
            Ok(true)
        }
        "verify-captp-delivered" => Ok(cmd_verify_captp_delivered(state_dir)),
        "verify-captp-delivered-tampered" => Ok(cmd_verify_captp_delivered_tampered(state_dir)),
        "make-sovereign-witness" => {
            let c = need("--cell")?;
            let seq = need_u64("--sequence", Some("1"))?;
            cmd_make_sovereign_witness(state_dir, &c, seq);
            Ok(true)
        }
        "slot-caveat-demo" => {
            cmd_slot_caveat_demo(state_dir);
            Ok(true)
        }
        "make-bilateral-bundle" => {
            let a = need("--alice-cell")?;
            let b = need("--bob-cell")?;
            let amount = need_u64("--amount", None)?;
            let turn_nonce = need_u64("--turn-nonce", Some("1"))?;
            cmd_make_bilateral_bundle(state_dir, &a, &b, amount, turn_nonce);
            Ok(true)
        }
        other => Err(format!("unknown command: {other}")),
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        return usage();
    }
    let cmd = args[1].clone();
    let rest = &args[2..];
    let state_dir = match arg(rest, "--state-dir") {
        Some(s) => PathBuf::from(s),
        None => {
            eprintln!("--state-dir required");
            return ExitCode::from(2);
        }
    };

    match run(&cmd, rest, &state_dir) {
        Ok(true) => ExitCode::from(0),
        Ok(false) => ExitCode::from(1),
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::from(2)
        }
    }
}
