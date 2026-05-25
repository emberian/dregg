//! Cross-federation CapTP-delivered Turn integration tests.
//!
//! This is the **Silver-Vision E2E core**: Alice on F1 creates a bearer
//! cap, Bob on F2 receives via three-party handoff, Bob exercises →
//! CapTP message → Alice's executor produces a Turn with
//! `Authorization::CapTpDelivered`, the resulting WitnessedReceipt
//! scope-2 chain is verifiable across the federation boundary.
//!
//! All tests in this file currently `#[ignore]` on either:
//!   - CapTP cross-federation transport (no live wire today — exposure
//!     is via `pyana_captp::SwissTable` + `validate_handoff`, but the
//!     end-to-end CapTP→Turn pipeline is not yet wired through the
//!     teasting harness),
//!   - `Authorization::CapTpDelivered` executor dispatch with
//!     introducer + recipient signature checks,
//!   - WitnessedReceipt scope-2 chain verification across federations.
//!
//! See SILVER-VISION-E2E-VERIFICATION.md, AUDIT-federation.md §8,
//! AUTHORIZATION-CUSTOM-DESIGN.md, and demo/silver-vision-e2e/expected.json.

use pyana_captp::FederationId;
use pyana_cell::CellId;

// ---------------------------------------------------------------------------
// Federation identities used across this file
// ---------------------------------------------------------------------------

fn fed_a() -> FederationId {
    FederationId([0xA1; 32])
}

fn fed_b() -> FederationId {
    FederationId([0xB2; 32])
}

#[allow(dead_code)]
fn fed_c() -> FederationId {
    FederationId([0xC3; 32])
}

// ===========================================================================
// Happy path: Alice F1 → Bob F2 three-party handoff + CapTp-delivered turn
// ===========================================================================

/// 1. Alice on F1 owns a cell with state X.
/// 2. Alice exports a `SturdyRef` for that cell (an opaque swiss-number
///    address that names the cell + permission subset).
/// 3. Alice introduces Bob to the sturdy-ref via three-party handoff
///    (introducer = Alice, recipient = Bob, target = Alice's cell).
/// 4. Bob (on F2) presents the handoff certificate over CapTP to F1's
///    handoff verifier; F1 validates the certificate.
/// 5. Bob then exercises the cap — sends a CapTP message naming the
///    sturdy-ref.
/// 6. F1's executor receives the CapTP message and produces a Turn
///    against Alice's cell with `Authorization::CapTpDelivered`
///    carrying the introducer-signed cert + recipient sig.
/// 7. The Turn commits → executor produces a TurnReceipt → the receipt
///    is part of the scope-2 chain a fourth-party verifier can replay.
#[test]
#[ignore = "blocked on Authorization::CapTpDelivered executor dispatch + teasting cross-federation CapTP wire (AUTHORIZATION-CUSTOM-DESIGN.md, SILVER-VISION-E2E-VERIFICATION.md)"]
fn alice_f1_exports_bob_f2_exercises_captp_turn_commits() {
    let _ = fed_a();
    let _ = fed_b();
    panic!("blocked");
}

// ===========================================================================
// Adversarial: tampered introducer signature
// ===========================================================================

#[test]
#[ignore = "blocked on Authorization::CapTpDelivered executor dispatch: tamper the introducer's signature on the handoff certificate — F1's executor must reject the resulting Turn"]
fn captp_delivered_turn_tampered_introducer_sig_rejects() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on Authorization::CapTpDelivered: tamper the recipient signature (Bob's confirmation) on the handoff presentation — executor rejects"]
fn captp_delivered_turn_tampered_recipient_sig_rejects() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on Authorization::CapTpDelivered: recipient_pk in the cert disagrees with the presenter who signs the CapTP message — executor rejects (the handoff names a different recipient than the presenter)"]
fn captp_delivered_turn_recipient_pk_mismatch_rejects() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on Authorization::CapTpDelivered: replay the same handoff certificate twice across two Turns — second must reject (handoff certs are single-use per nullifier or per nonce binding)"]
fn captp_delivered_turn_handoff_cert_replay_rejects() {
    panic!("blocked");
}

// ===========================================================================
// Cross-federation replay: F1's cert replayed on F3
// ===========================================================================

#[test]
#[ignore = "blocked on Authorization::CapTpDelivered + federation_id binding (AUDIT-federation.md F1/F2): a CapTP-delivered Turn signed for federation F1 cannot be applied on F3's ledger — even if F3 has a cell with the same cell_id"]
fn captp_delivered_turn_cross_federation_replay_rejects() {
    let _ = fed_a();
    let _ = fed_c();
    panic!("blocked");
}

// ===========================================================================
// Cross-federation WitnessedReceipt scope-2 chain
// ===========================================================================

#[test]
#[ignore = "blocked on WitnessedReceipt scope-2 cross-federation chain: Dave (fourth party, no chain access) verifies the entire Alice→Bob→Carol receipt chain from receipts alone — including the CapTP-delivered Turn at the F1↔F2 boundary"]
fn dave_verifies_full_alice_bob_carol_receipt_chain_across_federations() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on WitnessedReceipt scope-2: tamper ONE receipt mid-chain — Dave's replay must detect the inconsistency"]
fn dave_detects_tampered_receipt_in_mid_chain_replay() {
    panic!("blocked");
}

#[test]
#[ignore = "blocked on WitnessedReceipt scope-2 + γ.2 trilateral binding: trilateral introduce (Alice→Bob→Carol) across three federations — Dave verifies the intro_id matches across all three per-federation receipts"]
fn dave_verifies_trilateral_intro_id_match_across_three_federations() {
    panic!("blocked");
}

// ===========================================================================
// CapTP delivery + sovereign witness composition
// ===========================================================================

#[test]
#[ignore = "blocked on Authorization::CapTpDelivered + sovereign-witness AIR teeth: Bob's F2 cell is sovereign — when Bob exercises Alice's cap, the resulting F2 turn must carry a sovereign witness for Bob's cell AND a CapTpDelivered authorization for the cross-fed reference"]
fn captp_delivered_with_sovereign_witness_on_recipient_cell() {
    panic!("blocked");
}

// ===========================================================================
// CapTP delivery + slot caveats on both sides
// ===========================================================================

#[test]
#[ignore = "blocked on Authorization::CapTpDelivered + caveat-correctness: Alice's F1 cell has RateLimit(3/epoch); Bob's F2 cell has Monotonic on a balance slot — both slot caveats must fire when Bob exercises via CapTP"]
fn captp_delivered_with_slot_caveats_on_both_cells() {
    panic!("blocked");
}

// ===========================================================================
// Three-party handoff structural sanity (testable today against
// pyana_captp::validate_handoff)
// ===========================================================================

#[test]
fn handoff_certificate_validate_via_pyana_captp_api_exists() {
    // This is a *compile-time / API-shape* sanity check: ensure the
    // function we depend on for the cross-fed integration test exists.
    // If `validate_handoff` is renamed or refactored away, this test
    // catches it before the bigger integration test silently breaks.
    let _f = pyana_captp::validate_handoff;
}

#[test]
fn cellid_and_federationid_are_distinct_types() {
    // Make sure no future refactor accidentally unifies CellId and
    // FederationId — they are disjoint trust roots. (CellId names a
    // cell inside one federation; FederationId names a federation.)
    let cell = CellId([1u8; 32]);
    let federation = fed_a();
    let _ = cell;
    let _ = federation;
}
