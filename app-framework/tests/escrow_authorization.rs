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

use dregg_app_framework::authorizer::{AuthError, RejectingAuthorizer};
use dregg_app_framework::escrow::{EscrowError, EscrowManager};
use dregg_sdk::embed::{DreggEngine, EngineConfig};
use dregg_turn::escrow::EscrowCondition;
use dregg_types::CellId;

#[test]
fn rejecting_authorizer_blocks_all_escrow_operations() {
    let mut engine = DreggEngine::new(EngineConfig::for_testing());
    let auth = Box::new(RejectingAuthorizer::new("no escrows allowed (test)"));
    let mut mgr = EscrowManager::new(&mut engine, auth);

    let from = CellId::from_bytes([1u8; 32]);
    let to = CellId::from_bytes([2u8; 32]);
    let condition = EscrowCondition::ProofPresented {
        verification_key: [0u8; 32],
    };

    // create_payment_escrow
    let err = mgr
        .create_payment_escrow(from, to, 1000, condition, 100)
        .expect_err("rejecting authorizer must block escrow creation");
    assert_rejected(&err, "no escrows allowed");

    // release_with_proof
    let err = mgr
        .release_with_proof([7u8; 32], b"any-proof")
        .expect_err("rejecting authorizer must block release");
    assert_rejected(&err, "no escrows allowed");

    // refund_expired
    let err = mgr
        .refund_expired([9u8; 32], 1000)
        .expect_err("rejecting authorizer must block refund");
    assert_rejected(&err, "no escrows allowed");
}

fn assert_rejected(err: &EscrowError, reason_substring: &str) {
    match err {
        EscrowError::AuthorizationFailed(AuthError::Rejected(reason)) => {
            assert!(
                reason.contains(reason_substring),
                "unexpected reject reason: {reason}"
            );
        }
        other => panic!("expected AuthorizationFailed(Rejected), got: {other:?}"),
    }
}
