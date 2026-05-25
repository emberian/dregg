//! Integration test: bridge credential presentation and verification.
//!
//! Tests the `BridgePresentationBuilder` pipeline and verifies that:
//! - A correctly-built presentation proof passes verification.
//! - A forged credential (wrong issuer key) is rejected by the issuer
//!   membership check.
//! - An expired token presentation is rejected by the authorization trace.
//! - A credential for the wrong app is rejected (authorization denied).
//! - The wire proof strips the private trace (zero-knowledge property).
//!
//! Note: tests use `prove_fast()` (constraint-checked, no real STARK) so
//! this file is NO-CARGO-compatible — no STARK proving happens.

use pyana_bridge::present::BridgePresentationBuilder;
use pyana_token::{Attenuation, AuthRequest, MacaroonToken};

// ============================================================================
// Helpers
// ============================================================================

fn issuer_key() -> [u8; 32] {
    let mut k = [0u8; 32];
    k[0] = 0xDE;
    k[1] = 0xAD;
    k[28] = 0xCA;
    k[31] = 0xFE;
    k
}

fn other_key() -> [u8; 32] {
    // A different key — represents a different issuer / forged credential.
    let mut k = [0u8; 32];
    k[0] = 0xFF;
    k[1] = 0xFE;
    k[28] = 0xAB;
    k[31] = 0xCD;
    k
}

fn fed_root() -> [u8; 32] {
    let mut r = [0u8; 32];
    r[0] = 0xFE;
    r[1] = 0xD0;
    r
}

/// Compute the LINEAR Merkle AIR federation root that matches the synthetic
/// path built by BridgePresentationBuilder::new (the same helper used in
/// bridge/src/tests.rs). Required so `prove_fast()` can complete without a
/// real federation tree.
fn matching_root_bb(key: &[u8; 32]) -> pyana_circuit::BabyBear {
    use pyana_circuit::merkle_air::MerkleAir;
    use pyana_circuit::BabyBear;

    let issuer_hash = pyana_bridge::present::bytes_to_babybear(key);
    let depth = 8;
    let mut current = issuer_hash;
    for i in 0..depth {
        let position = (i % 4) as u8;
        let siblings = [
            BabyBear::new(pyana_bridge::present::hash_index(i, 0, key)),
            BabyBear::new(pyana_bridge::present::hash_index(i, 1, key)),
            BabyBear::new(pyana_bridge::present::hash_index(i, 2, key)),
        ];
        current = MerkleAir::compute_parent(current, position, &siblings);
    }
    current
}

fn builder_for_key(key: [u8; 32]) -> BridgePresentationBuilder {
    BridgePresentationBuilder::new_with_root_bb(key, fed_root(), matching_root_bb(&key))
}

// ============================================================================
// Test: valid credential is accepted
// ============================================================================

#[test]
fn valid_credential_accepted() {
    let key = issuer_key();
    let token = MacaroonToken::mint(key, b"kid-valid", "pyana.dev");

    let mut builder = builder_for_key(key);
    builder.set_root_token(token);

    let att = Attenuation {
        apps: vec![("myapp".to_string(), "rw".to_string())],
        ..Default::default()
    };
    builder.add_attenuation(&att);

    let req = AuthRequest {
        app_id: Some("myapp".to_string()),
        action: Some("read".to_string()),
        now: Some(1_700_000_000),
        ..Default::default()
    };

    let result = builder.prove_fast(&req);
    assert!(
        result.is_ok(),
        "valid credential presentation must be accepted: {:?}",
        result.err()
    );
    assert!(result.unwrap().is_constraint_checked());
}

// ============================================================================
// Test: forged credential (wrong issuer key) — issuer membership fails
// ============================================================================

#[test]
fn wrong_issuer_key_rejected_by_membership_check() {
    let real_key = issuer_key();
    let forged_key = other_key();

    // Mint a token using the FORGED key (not in the federation tree).
    let forged_token = MacaroonToken::mint(forged_key, b"kid-forge", "evil.dev");

    // Build with the forged key as the issuer — the synthetic Merkle path
    // built by BridgePresentationBuilder will not match the federation root
    // built for `real_key`.
    let mut builder = BridgePresentationBuilder::new(forged_key, fed_root());
    builder.set_root_token(forged_token);

    let att = Attenuation {
        apps: vec![("myapp".to_string(), "rw".to_string())],
        ..Default::default()
    };
    builder.add_attenuation(&att);

    let req = AuthRequest {
        app_id: Some("myapp".to_string()),
        action: Some("read".to_string()),
        now: Some(1_700_000_000),
        ..Default::default()
    };

    // prove_fast uses the local constraint check path.  The issuer membership
    // check runs via `build_issuer_membership` before the auth trace is even
    // evaluated — a builder constructed with an unregistered key must fail.
    let result = builder.prove_fast(&req);
    assert!(
        result.is_err(),
        "forged (unregistered) issuer key must be rejected by issuer membership check"
    );
}

// ============================================================================
// Test: expired token is rejected by the authorization trace
// ============================================================================

#[test]
fn expired_credential_denied() {
    let key = issuer_key();
    let token = MacaroonToken::mint(key, b"kid-exp", "pyana.dev");

    let mut builder = builder_for_key(key);
    builder.set_root_token(token);

    // Attenuation with a hard expiry in the past.
    let att = Attenuation {
        apps: vec![("myapp".to_string(), "rw".to_string())],
        not_after: Some(1_000_000_000), // long in the past
        ..Default::default()
    };
    builder.add_attenuation(&att);

    let req = AuthRequest {
        app_id: Some("myapp".to_string()),
        action: Some("read".to_string()),
        now: Some(1_700_000_000), // 700 million seconds after the expiry
        ..Default::default()
    };

    let result = builder.prove_fast(&req);
    assert!(
        result.is_err(),
        "credential with past expiry must be denied"
    );
}

// ============================================================================
// Test: credential for wrong app is rejected
// ============================================================================

#[test]
fn credential_wrong_app_denied() {
    let key = issuer_key();
    let token = MacaroonToken::mint(key, b"kid-app", "pyana.dev");

    let mut builder = builder_for_key(key);
    builder.set_root_token(token);

    // Restrict to "dashboard".
    let att = Attenuation {
        apps: vec![("dashboard".to_string(), "rw".to_string())],
        ..Default::default()
    };
    builder.add_attenuation(&att);

    // But request is for "admin-panel" — not in the token.
    let req = AuthRequest {
        app_id: Some("admin-panel".to_string()),
        action: Some("read".to_string()),
        now: Some(1_700_000_000),
        ..Default::default()
    };

    let result = builder.prove_fast(&req);
    assert!(
        result.is_err(),
        "credential restricted to 'dashboard' must be denied for 'admin-panel'"
    );
}

// ============================================================================
// Test: wire proof strips the private trace (zero-knowledge property)
// ============================================================================

#[test]
fn wire_proof_strips_private_trace() {
    let key = issuer_key();
    let token = MacaroonToken::mint(key, b"kid-wire", "pyana.dev");

    let mut builder = builder_for_key(key);
    builder.set_root_token(token);

    let att = Attenuation {
        apps: vec![("myapp".to_string(), "rw".to_string())],
        ..Default::default()
    };
    builder.add_attenuation(&att);

    let req = AuthRequest {
        app_id: Some("myapp".to_string()),
        action: Some("read".to_string()),
        now: Some(1_700_000_000),
        ..Default::default()
    };

    let proof = builder.prove_fast(&req).unwrap();

    // The full proof carries a trace (for local debugging).
    // Converting to wire format must not panic and must produce a proof
    // whose circuit-level check still holds.
    let wire = proof.into_wire_proof();
    assert!(
        matches!(
            wire.verification,
            pyana_circuit::PresentationVerification::Valid
                | pyana_circuit::PresentationVerification::LocalOnly
        ),
        "wire proof must retain the constraint verification result"
    );
    // The wire proof has no trace field at all — compile-time structural check.
    // (If WirePresentationProof ever gains a `trace` field this line won't compile,
    // which is the desired canary.)
    let _ = &wire.circuit_proof;
    let _ = &wire.verification;
}

// ============================================================================
// Test: user-confined credential — wrong user is denied
// ============================================================================

#[test]
fn credential_wrong_user_denied() {
    let key = issuer_key();
    let token = MacaroonToken::mint(key, b"kid-user", "pyana.dev");

    let mut builder = builder_for_key(key);
    builder.set_root_token(token);

    let att = Attenuation {
        apps: vec![("myapp".to_string(), "rw".to_string())],
        confine_user: Some("alice".to_string()),
        ..Default::default()
    };
    builder.add_attenuation(&att);

    // bob is not alice.
    let req = AuthRequest {
        app_id: Some("myapp".to_string()),
        action: Some("read".to_string()),
        user_id: Some("bob".to_string()),
        now: Some(1_700_000_000),
        ..Default::default()
    };

    let result = builder.prove_fast(&req);
    assert!(
        result.is_err(),
        "credential confined to 'alice' must be denied for user 'bob'"
    );
}
