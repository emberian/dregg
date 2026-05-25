//! Integration / adversarial property tests for the privacy-voting app.
//!
//! These tests target the four properties spelled out in the task brief:
//!
//! 1. Routes wired in the binary (smoke-tested via `tower::ServiceExt::oneshot`).
//! 2. Eligibility actually checks the credential.
//! 3. The vote commitment hides the vote.
//! 4. The tally is verifiable from the reveal log.
//! 5. Unlinkability: no entry on the queue carries identity bytes.

use std::collections::HashSet;

use axum::body::{Body, to_bytes};
use axum::http::{Method, Request, StatusCode};
use serde_json::{Value, json};
use tower::ServiceExt;

use pyana_app_framework::auth::AdminToken;
use pyana_sdk::wallet::{AgentCipherclerk, DelegatedToken};
use pyana_token::Attenuation;
use pyana_types::{PublicKey, Signature};

use crate::ballot::{self, BallotReveal};
use crate::eligibility::EligibilityAuthority;
use crate::proposal::{Phase, derive_proposal_id};
use crate::server::{AppState, router};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn admin_token_value() -> String {
    "test-admin-token".to_string()
}

fn make_state(issuer_pk: PublicKey) -> AppState {
    let token = AdminToken::from_value(admin_token_value());
    AppState::new(EligibilityAuthority::Single(issuer_pk), 256).with_admin_token(token)
}

fn make_app(state: AppState) -> axum::Router {
    router().with_state(state)
}

async fn post_json(app: &axum::Router, uri: &str, body: Value, admin: bool) -> (StatusCode, Value) {
    let mut req = Request::builder()
        .method(Method::POST)
        .uri(uri)
        .header("content-type", "application/json");
    if admin {
        req = req.header("authorization", format!("Bearer {}", admin_token_value()));
    }
    let req = req
        .body(Body::from(serde_json::to_vec(&body).unwrap()))
        .unwrap();
    let resp = app.clone().oneshot(req).await.unwrap();
    let status = resp.status();
    let bytes = to_bytes(resp.into_body(), usize::MAX).await.unwrap();
    let value: Value = serde_json::from_slice(&bytes)
        .unwrap_or_else(|_| Value::String(String::from_utf8_lossy(&bytes).into()));
    (status, value)
}

async fn get_json(app: &axum::Router, uri: &str) -> (StatusCode, Value) {
    let req = Request::builder()
        .method(Method::GET)
        .uri(uri)
        .body(Body::empty())
        .unwrap();
    let resp = app.clone().oneshot(req).await.unwrap();
    let status = resp.status();
    let bytes = to_bytes(resp.into_body(), usize::MAX).await.unwrap();
    let value: Value = serde_json::from_slice(&bytes)
        .unwrap_or_else(|_| Value::String(String::from_utf8_lossy(&bytes).into()));
    (status, value)
}

/// Issue a delegation envelope from `issuer` to `voter_pk` granting the
/// "vote/submit" capability. This mirrors what a real eligibility-issuer
/// service would produce.
fn issue_eligibility_credential(issuer: &mut AgentCipherclerk, voter_pk: PublicKey) -> DelegatedToken {
    let root_token = issuer.mint_token(&[0x99; 32], "vote");
    let restrictions = Attenuation {
        services: vec![("vote".into(), "submit".into())],
        ..Default::default()
    };
    issuer
        .delegate(&root_token, &voter_pk, &restrictions)
        .expect("issuer must be able to delegate")
}

// ---------------------------------------------------------------------------
// 1. Routes wired
// ---------------------------------------------------------------------------

#[tokio::test]
async fn admin_creates_and_lists_proposal() {
    let issuer = AgentCipherclerk::new();
    let state = make_state(issuer.public_key());
    let app = make_app(state);

    let (status, body) = post_json(
        &app,
        "/proposals",
        json!({
            "slug": "ratify-charter",
            "question": "Ratify the charter?",
            "options": ["yes", "no"],
        }),
        true,
    )
    .await;
    assert_eq!(status, StatusCode::CREATED, "create response body: {body}");
    let pid_hex = body["id"].as_str().unwrap().to_string();

    let (s, list) = get_json(&app, "/proposals").await;
    assert_eq!(s, StatusCode::OK);
    let arr = list.as_array().unwrap();
    assert_eq!(arr.len(), 1);
    assert_eq!(arr[0]["id"], pid_hex);
}

#[tokio::test]
async fn create_proposal_without_admin_token_rejected() {
    let issuer = AgentCipherclerk::new();
    let state = make_state(issuer.public_key());
    let app = make_app(state);
    let (status, _) = post_json(
        &app,
        "/proposals",
        json!({"slug": "x", "question": "?", "options": ["a", "b"]}),
        false,
    )
    .await;
    assert!(
        status.is_client_error(),
        "no admin token must be rejected: {status}"
    );
}

// ---------------------------------------------------------------------------
// 2. Eligibility actually checks the credential
// ---------------------------------------------------------------------------

#[tokio::test]
async fn submit_ballot_with_valid_credential_accepted() {
    let mut issuer = AgentCipherclerk::new();
    let voter = AgentCipherclerk::new();
    let state = make_state(issuer.public_key());
    let app = make_app(state);

    // Setup proposal.
    let (_, p) = post_json(
        &app,
        "/proposals",
        json!({"slug": "p1", "question": "?", "options": ["a", "b"]}),
        true,
    )
    .await;
    let pid_hex = p["id"].as_str().unwrap().to_string();
    let pid_bytes = pyana_app_framework::hex::hex_to_bytes32(&pid_hex).unwrap();

    let cred = issue_eligibility_credential(&mut issuer, voter.public_key());
    let r = [7u8; 32];
    let commitment = ballot::commit(&pid_bytes, 0, &r);

    let (status, body) = post_json(
        &app,
        "/ballots/submit",
        json!({
            "proposal_id": pid_hex,
            "commitment_hex": pyana_app_framework::hex::bytes32_to_hex(&commitment),
            "credential": cred,
        }),
        false,
    )
    .await;
    assert_eq!(status, StatusCode::OK, "submit response: {body}");
    assert_eq!(body["queued"], true);
}

#[tokio::test]
async fn submit_ballot_without_credential_rejected() {
    // Adversarial: an empty/synthesized credential must fail.
    let issuer = AgentCipherclerk::new();
    let state = make_state(issuer.public_key());
    let app = make_app(state);

    let (_, p) = post_json(
        &app,
        "/proposals",
        json!({"slug": "p2", "question": "?", "options": ["a", "b"]}),
        true,
    )
    .await;
    let pid_hex = p["id"].as_str().unwrap().to_string();

    // We cannot easily hand-craft a `DelegatedToken` from raw JSON (its
    // PublicKey/Signature fields use a length-prefixed `serde_32`/`serde_64`
    // encoding, awkward to inline). Instead, mint a real credential from an
    // UNAUTHORIZED issuer cipherclerk: this exercises the same "no credential
    // from this issuer" rejection path.
    let mut rogue_issuer = AgentCipherclerk::new();
    let voter = AgentCipherclerk::new();
    let cred = issue_eligibility_credential(&mut rogue_issuer, voter.public_key());

    let pid_bytes = pyana_app_framework::hex::hex_to_bytes32(&pid_hex).unwrap();
    let r = [1u8; 32];
    let commitment = ballot::commit(&pid_bytes, 0, &r);
    let (status, body) = post_json(
        &app,
        "/ballots/submit",
        json!({
            "proposal_id": pid_hex,
            "commitment_hex": pyana_app_framework::hex::bytes32_to_hex(&commitment),
            "credential": cred,
        }),
        false,
    )
    .await;
    assert_eq!(
        status,
        StatusCode::UNAUTHORIZED,
        "credential from wrong issuer must be 401, got {status}: {body}"
    );
}

#[tokio::test]
async fn submit_ballot_with_forged_signature_rejected() {
    // Adversarial: even with the correct delegator pubkey field, a tampered
    // signature must fail.
    let mut issuer = AgentCipherclerk::new();
    let issuer_pk = issuer.public_key();
    let voter = AgentCipherclerk::new();
    let state = make_state(issuer_pk);
    let app = make_app(state);

    let (_, p) = post_json(
        &app,
        "/proposals",
        json!({"slug": "p3", "question": "?", "options": ["a", "b"]}),
        true,
    )
    .await;
    let pid_hex = p["id"].as_str().unwrap().to_string();
    let pid_bytes = pyana_app_framework::hex::hex_to_bytes32(&pid_hex).unwrap();

    let mut cred = issue_eligibility_credential(&mut issuer, voter.public_key());
    // Tamper: random signature.
    cred.delegator_signature = Signature([0x55; 64]);

    let r = [2u8; 32];
    let commitment = ballot::commit(&pid_bytes, 0, &r);
    let (status, body) = post_json(
        &app,
        "/ballots/submit",
        json!({
            "proposal_id": pid_hex,
            "commitment_hex": pyana_app_framework::hex::bytes32_to_hex(&commitment),
            "credential": cred,
        }),
        false,
    )
    .await;
    assert_eq!(
        status,
        StatusCode::UNAUTHORIZED,
        "forged-signature credential must be 401, got {status}: {body}"
    );
}

#[tokio::test]
async fn double_submission_by_same_voter_rejected() {
    let mut issuer = AgentCipherclerk::new();
    let voter = AgentCipherclerk::new();
    let state = make_state(issuer.public_key());
    let app = make_app(state);

    let (_, p) = post_json(
        &app,
        "/proposals",
        json!({"slug": "p-dbl", "question": "?", "options": ["a", "b"]}),
        true,
    )
    .await;
    let pid_hex = p["id"].as_str().unwrap().to_string();
    let pid_bytes = pyana_app_framework::hex::hex_to_bytes32(&pid_hex).unwrap();

    let cred = issue_eligibility_credential(&mut issuer, voter.public_key());
    let r1 = [1u8; 32];
    let r2 = [2u8; 32];
    let c1 = ballot::commit(&pid_bytes, 0, &r1);
    let c2 = ballot::commit(&pid_bytes, 1, &r2);

    let (s, _) = post_json(
        &app,
        "/ballots/submit",
        json!({"proposal_id": pid_hex, "commitment_hex": pyana_app_framework::hex::bytes32_to_hex(&c1), "credential": cred.clone()}),
        false,
    )
    .await;
    assert_eq!(s, StatusCode::OK);

    let (s2, _) = post_json(
        &app,
        "/ballots/submit",
        json!({"proposal_id": pid_hex, "commitment_hex": pyana_app_framework::hex::bytes32_to_hex(&c2), "credential": cred}),
        false,
    )
    .await;
    assert_eq!(s2, StatusCode::CONFLICT, "same voter cannot submit twice");
}

// ---------------------------------------------------------------------------
// 3. The commitment hides the vote (commit phase carries no usable signal)
// ---------------------------------------------------------------------------

#[tokio::test]
async fn commitment_hides_vote() {
    // Privacy property: two voters voting the SAME option with different
    // randomness produce DIFFERENT commitments. An observer looking at the
    // queue cannot detect that two voters voted the same way.
    let pid = derive_proposal_id("hidden");
    let c1 = ballot::commit(&pid, 0, &[1u8; 32]);
    let c2 = ballot::commit(&pid, 0, &[2u8; 32]);
    assert_ne!(c1, c2);

    // And: a voter cannot mount a brute-force preimage attack to *learn* a
    // peer's vote without their randomness. This is implicit in blake3's
    // preimage resistance; we assert structurally that the only inputs are
    // (proposal_id, option, randomness), so an attacker missing randomness
    // faces 2^256 work.
    let c3 = ballot::commit(&pid, 0, &[1u8; 32]);
    assert_eq!(c1, c3, "deterministic given identical inputs");
}

// ---------------------------------------------------------------------------
// 4. The tally is verifiable
// ---------------------------------------------------------------------------

#[tokio::test]
async fn five_ballots_yield_correct_tally() {
    let mut issuer = AgentCipherclerk::new();
    let state = make_state(issuer.public_key());
    let app = make_app(state);

    let (_, p) = post_json(
        &app,
        "/proposals",
        json!({"slug": "5b", "question": "?", "options": ["yes", "no"]}),
        true,
    )
    .await;
    let pid_hex = p["id"].as_str().unwrap().to_string();
    let pid_bytes = pyana_app_framework::hex::hex_to_bytes32(&pid_hex).unwrap();

    // Five distinct voters, votes: yes, no, yes, yes, no.
    let votes = [0u32, 1, 0, 0, 1];
    let mut reveals = Vec::new();
    for (i, &opt) in votes.iter().enumerate() {
        let voter = AgentCipherclerk::new();
        let cred = issue_eligibility_credential(&mut issuer, voter.public_key());
        let r = [(i as u8 + 1) * 11u8; 32];
        let commitment = ballot::commit(&pid_bytes, opt, &r);
        let (s, _b) = post_json(
            &app,
            "/ballots/submit",
            json!({"proposal_id": pid_hex, "commitment_hex": pyana_app_framework::hex::bytes32_to_hex(&commitment), "credential": cred}),
            false,
        )
        .await;
        assert_eq!(s, StatusCode::OK, "submit {i} must succeed");
        reveals.push((commitment, opt, r));
    }

    // Advance to reveal phase.
    let (s, _) = post_json(
        &app,
        &format!("/admin/proposals/{pid_hex}/phase"),
        json!({"to": "reveal"}),
        true,
    )
    .await;
    assert_eq!(s, StatusCode::OK);

    // Reveal each.
    for (commitment, opt, r) in &reveals {
        let body = json!({
            "proposal_id": pid_hex,
            "commitment_hex": pyana_app_framework::hex::bytes32_to_hex(commitment),
            "reveal": {"option_index": opt, "randomness": r.to_vec()},
        });
        let (s, b) = post_json(&app, "/ballots/reveal", body, false).await;
        assert_eq!(s, StatusCode::OK, "reveal must accept: {b}");
    }

    // Tally.
    let (s, t) = get_json(&app, &format!("/tally/{pid_hex}")).await;
    assert_eq!(s, StatusCode::OK);
    // yes=3, no=2.
    assert_eq!(t["counts"], json!([3u64, 2u64]), "tally response: {t}");
    assert_eq!(t["reveal_count"], 5);

    // Verifiability: anyone can recompute the tally from the reveals locally.
    let mut local_log = crate::tally::RevealLog::new();
    for (commitment, opt, r) in &reveals {
        local_log.append(crate::tally::RevealedBallot {
            commitment: *commitment,
            option_index: *opt,
            randomness: *r,
        });
    }
    let counts = local_log.tally(2, &pid_bytes);
    assert_eq!(counts, vec![3, 2]);
    // And the root matches (order-sensitive; both insertion orders match).
    let local_root = local_log.merkle_root();
    let server_root = t["reveal_root"].as_str().unwrap();
    assert_eq!(
        pyana_app_framework::hex::bytes32_to_hex(&local_root),
        server_root
    );
}

#[tokio::test]
async fn reveal_with_wrong_vote_rejected() {
    // Adversarial: a voter cannot reveal a different option than they
    // committed to.
    let mut issuer = AgentCipherclerk::new();
    let voter = AgentCipherclerk::new();
    let state = make_state(issuer.public_key());
    let app = make_app(state);

    let (_, p) = post_json(
        &app,
        "/proposals",
        json!({"slug": "rwv", "question": "?", "options": ["a", "b"]}),
        true,
    )
    .await;
    let pid_hex = p["id"].as_str().unwrap().to_string();
    let pid_bytes = pyana_app_framework::hex::hex_to_bytes32(&pid_hex).unwrap();

    let cred = issue_eligibility_credential(&mut issuer, voter.public_key());
    let r = [9u8; 32];
    let commitment = ballot::commit(&pid_bytes, 0, &r);
    let (s, _) = post_json(
        &app,
        "/ballots/submit",
        json!({"proposal_id": pid_hex, "commitment_hex": pyana_app_framework::hex::bytes32_to_hex(&commitment), "credential": cred}),
        false,
    )
    .await;
    assert_eq!(s, StatusCode::OK);

    let (s, _) = post_json(
        &app,
        &format!("/admin/proposals/{pid_hex}/phase"),
        json!({"to": "reveal"}),
        true,
    )
    .await;
    assert_eq!(s, StatusCode::OK);

    // Try to claim we voted option 1 with the same randomness — must fail.
    let body = json!({
        "proposal_id": pid_hex,
        "commitment_hex": pyana_app_framework::hex::bytes32_to_hex(&commitment),
        "reveal": {"option_index": 1u32, "randomness": r.to_vec()},
    });
    let (status, _) = post_json(&app, "/ballots/reveal", body, false).await;
    assert_eq!(status, StatusCode::BAD_REQUEST);
}

// ---------------------------------------------------------------------------
// 5. Unlinkability
// ---------------------------------------------------------------------------

#[tokio::test]
async fn queue_entries_carry_no_identity_bytes() {
    // The strongest mechanical statement of unlinkability we can make in a
    // unit test: after several voters submit, the set of stored commitments
    // contains NONE of their public-key bytes as a substring of any entry,
    // and no entry equals any voter pubkey.
    let mut issuer = AgentCipherclerk::new();
    let state = make_state(issuer.public_key());
    let app = make_app(state.clone());

    let (_, p) = post_json(
        &app,
        "/proposals",
        json!({"slug": "unlink", "question": "?", "options": ["a", "b"]}),
        true,
    )
    .await;
    let pid_hex = p["id"].as_str().unwrap().to_string();
    let pid_bytes = pyana_app_framework::hex::hex_to_bytes32(&pid_hex).unwrap();

    let mut voter_pks: Vec<PublicKey> = Vec::new();
    for i in 0..4u8 {
        let voter = AgentCipherclerk::new();
        voter_pks.push(voter.public_key());
        let cred = issue_eligibility_credential(&mut issuer, voter.public_key());
        let r = [(i + 1) * 17; 32];
        let opt = (i as u32) % 2;
        let commitment = ballot::commit(&pid_bytes, opt, &r);
        let (s, _) = post_json(
            &app,
            "/ballots/submit",
            json!({"proposal_id": pid_hex, "commitment_hex": pyana_app_framework::hex::bytes32_to_hex(&commitment), "credential": cred}),
            false,
        )
        .await;
        assert_eq!(s, StatusCode::OK);
    }

    let entries = crate::server::dump_queue_entries(&state, &pid_bytes).await;
    assert_eq!(entries.len(), 4);

    let mut all_entry_bytes = Vec::new();
    for e in &entries {
        all_entry_bytes.extend_from_slice(e);
    }
    // No 32-byte entry equals any voter's public key.
    let voter_set: HashSet<[u8; 32]> = voter_pks.iter().map(|p| p.0).collect();
    for e in &entries {
        assert!(
            !voter_set.contains(e),
            "queue entry {:?} matches a voter pubkey: unlinkability broken",
            e
        );
    }
    // And the concatenated entry bytes do not contain any voter pk as a
    // contiguous substring (this is a stronger heuristic — blake3 outputs
    // should look pseudorandom and not embed inputs).
    for pk in &voter_pks {
        let needle = pk.0;
        for window in all_entry_bytes.windows(32) {
            assert_ne!(window, needle, "voter pk bytes appear in queue entries");
        }
    }
}

#[tokio::test]
async fn wrong_phase_rejects_submit_and_reveal() {
    let mut issuer = AgentCipherclerk::new();
    let voter = AgentCipherclerk::new();
    let state = make_state(issuer.public_key());
    let app = make_app(state);

    let (_, p) = post_json(
        &app,
        "/proposals",
        json!({"slug": "phase", "question": "?", "options": ["a", "b"]}),
        true,
    )
    .await;
    let pid_hex = p["id"].as_str().unwrap().to_string();
    let pid_bytes = pyana_app_framework::hex::hex_to_bytes32(&pid_hex).unwrap();

    // Advance to Reveal — now submit must fail.
    let (s, _) = post_json(
        &app,
        &format!("/admin/proposals/{pid_hex}/phase"),
        json!({"to": "reveal"}),
        true,
    )
    .await;
    assert_eq!(s, StatusCode::OK);

    let cred = issue_eligibility_credential(&mut issuer, voter.public_key());
    let r = [1u8; 32];
    let commitment = ballot::commit(&pid_bytes, 0, &r);
    let (status, _) = post_json(
        &app,
        "/ballots/submit",
        json!({"proposal_id": pid_hex, "commitment_hex": pyana_app_framework::hex::bytes32_to_hex(&commitment), "credential": cred}),
        false,
    )
    .await;
    assert_eq!(status, StatusCode::BAD_REQUEST);

    // Now close — reveal must also fail.
    let (s, _) = post_json(
        &app,
        &format!("/admin/proposals/{pid_hex}/phase"),
        json!({"to": "closed"}),
        true,
    )
    .await;
    assert_eq!(s, StatusCode::OK);
    let body = json!({
        "proposal_id": pid_hex,
        "commitment_hex": pyana_app_framework::hex::bytes32_to_hex(&commitment),
        "reveal": {"option_index": 0u32, "randomness": r.to_vec()},
    });
    let (status, _) = post_json(&app, "/ballots/reveal", body, false).await;
    assert_eq!(status, StatusCode::BAD_REQUEST);
}

// Suppress unused-import warning when `BallotReveal` is only constructed via
// json! in this file.
#[allow(dead_code)]
fn _unused_imports(_: BallotReveal, _: Phase) {}
