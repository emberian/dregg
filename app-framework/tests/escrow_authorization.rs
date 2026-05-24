//! Adversarial test: an `EscrowManager` built with a `RejectingAuthorizer`
//! must refuse to submit any escrow turn.
//!
//! This is the regression test for the DSL audit (P0 #1) finding. Before the
//! `Authorizer` plumbing was added, `EscrowManager` produced turns with
//! `Authorization::Unchecked` no matter what — there was no path by which a
//! misconfigured caller could be loudly told "you forgot to set an
//! authorizer". After Stage 0f, the manager *must* go through the
//! authorizer, and a rejecting authorizer must cause every operation to
//! fail with `EscrowError::AuthorizationFailed`.

use pyana_app_framework::authorizer::{AuthError, RejectingAuthorizer};
use pyana_app_framework::escrow::{EscrowError, EscrowManager};
use pyana_sdk::embed::{EngineConfig, PyanaEngine};
use pyana_turn::escrow::EscrowCondition;
use pyana_types::CellId;

#[test]
fn rejecting_authorizer_blocks_create_payment_escrow() {
    let mut engine = PyanaEngine::new(EngineConfig::for_testing());
    let auth = Box::new(RejectingAuthorizer::new("no escrows allowed (test)"));
    let mut mgr = EscrowManager::new(&mut engine, auth);

    let from = CellId::from_bytes([1u8; 32]);
    let to = CellId::from_bytes([2u8; 32]);
    let condition = EscrowCondition::ProofPresented {
        verification_key: [0u8; 32],
    };

    let err = mgr
        .create_payment_escrow(from, to, 1000, condition, 100)
        .expect_err("rejecting authorizer must block escrow creation");

    match err {
        EscrowError::AuthorizationFailed(AuthError::Rejected(reason)) => {
            assert!(
                reason.contains("no escrows allowed"),
                "unexpected reject reason: {reason}"
            );
        }
        other => panic!("expected AuthorizationFailed(Rejected), got: {other:?}"),
    }
}

#[test]
fn rejecting_authorizer_blocks_release_with_proof() {
    let mut engine = PyanaEngine::new(EngineConfig::for_testing());
    let auth = Box::new(RejectingAuthorizer::default());
    let mut mgr = EscrowManager::new(&mut engine, auth);

    let escrow_id = [7u8; 32];
    let err = mgr
        .release_with_proof(escrow_id, b"any-proof")
        .expect_err("rejecting authorizer must block release");

    assert!(
        matches!(err, EscrowError::AuthorizationFailed(AuthError::Rejected(_))),
        "expected AuthorizationFailed(Rejected), got: {err:?}"
    );
}

#[test]
fn rejecting_authorizer_blocks_refund_expired() {
    let mut engine = PyanaEngine::new(EngineConfig::for_testing());
    let auth = Box::new(RejectingAuthorizer::default());
    let mut mgr = EscrowManager::new(&mut engine, auth);

    let escrow_id = [9u8; 32];
    let err = mgr
        .refund_expired(escrow_id, 1000)
        .expect_err("rejecting authorizer must block refund");

    assert!(
        matches!(err, EscrowError::AuthorizationFailed(AuthError::Rejected(_))),
        "expected AuthorizationFailed(Rejected), got: {err:?}"
    );
}
