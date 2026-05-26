//! CapTP wire-message → runtime Effect routing (Stage 7 / P1.B).
//!
//! Per `DESIGN-captp-integration.md` §7.2 and `STAGE-7-PLUS-DESIGN.md`, every
//! CapTP wire message must lower to a turn-submitted runtime `Effect` rather
//! than directly mutating the federation's `CapTpState`. This module is the
//! load-bearing piece of that lowering: it builds the `Effect`, `Action`, and
//! `Turn` that the executor consumes.
//!
//! Today the wire layer's `process_message` (in `server.rs`) doesn't have
//! direct access to a `TurnExecutor`; the node layer is where execution
//! happens. P1.B therefore lands the **routing primitive** here and uses it
//! to record-then-mutate inside the wire handlers, so the four CapTP wire
//! messages become "construct an Effect, then apply via the federation
//! mirror." The pending-turn queue (a `Vec<Turn>` on `CapTpState`) is
//! drained by the node when it runs a turn batch.
//!
//! ### Field-shape notes
//!
//! The minimal `Effect` shapes (P1.A) carry only the load-bearing identifiers
//! (swiss number, ref id, cert hash). Richer Merkle-witness data lives in
//! the federation-mirror state (the `CapTpState`'s `swiss_table` /
//! `export_gc`) and the post-commit hook reconciles the mirror with the
//! receipt-emitted effect chain.

use pyana_captp::HandoffCertificate;
use pyana_cell::{CapabilityRef, CellId, Preconditions};
use pyana_turn::action::{Action, Authorization, CommitmentMode, DelegationMode, Effect, symbol};
use pyana_turn::forest::{CallForest, CallTree};
use pyana_turn::turn::Turn;
use pyana_types::SigningKey;
use tracing::info;

/// Build a single-action `Turn` carrying a CapTP `Effect`.
///
/// The agent is the federation gateway cell (typically the node's local
/// identity). The action's authorization is `Unchecked` for wire-layer
/// routing: the cryptographic legitimacy of the operation was already
/// established off-band (the swiss number presented, the handoff
/// signature verified, etc.). The receipt-chain and AIR proof carry the
/// state-transition evidence forward.
///
/// `nonce` should be the agent's next outer nonce; the node layer
/// supplies the right value when it drains the queue. For "preview"
/// construction at the wire layer we pass 0 — it gets overwritten before
/// the turn is signed and executed.
///
/// **NOTE**: This builder retains `Authorization::Unchecked` for the
/// CapHello / Enliven / Drop wire paths where no cert is available. The
/// executor still rejects `Unchecked`, so these paths are queued but not
/// executable until they switch to the cert-backed builder
/// (`build_captp_turn_delivered`). See AUDIT-distributed-semantics §7
/// GAP-12 and AUDIT-protocol-composition Seam 3.
pub fn build_captp_turn(agent: CellId, target: CellId, effect: Effect, nonce: u64) -> Turn {
    let action = Action {
        target,
        method: symbol("captp.route"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Preconditions::default(),
        effects: vec![effect],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    let call_forest = CallForest {
        roots: vec![CallTree::new(action)],
        forest_hash: [0u8; 32],
    };
    Turn {
        agent,
        nonce,
        call_forest,
        fee: 0,
        memo: Some("captp.route".to_string()),
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

/// Build a CapTP-routed Turn whose authorization is the verified handoff
/// delivery (Seam 3 keystone). Closes the receipt-mirror loop: every CapTP
/// PresentHandoff that the wire layer accepts produces a Turn whose
/// authorization carries the introducer-signed cert + a recipient signature
/// binding this exact Turn (cert nonce ↔ agent ↔ target ↔ turn_nonce ↔ effects).
///
/// `recipient_key` is the signing key paired with `handoff_cert.recipient_pk`.
/// In the wire-layer integration path this comes from the recipient's
/// presentation. (For an in-server test driver, the test code holds the
/// signing key and passes it here.)
pub fn build_captp_turn_delivered(
    agent: CellId,
    target: CellId,
    effect: Effect,
    nonce: u64,
    handoff_cert: HandoffCertificate,
    introducer_pk: [u8; 32],
    recipient_key: &SigningKey,
) -> Turn {
    let effects = vec![effect];
    // The agent for the signing message is the same as the action target
    // (gateway-mirrors-cell). This matches what the executor recomputes.
    let signing_msg = Authorization::captp_delivered_signing_message(
        &handoff_cert.nonce,
        &target,
        &target,
        nonce,
        &effects,
    );
    let signature = pyana_types::sign(recipient_key, &signing_msg);
    let sender_pk = handoff_cert.recipient_pk;

    let action = Action {
        target,
        method: symbol("captp.route"),
        args: vec![],
        authorization: Authorization::CapTpDelivered {
            handoff_cert,
            introducer_pk,
            sender_pk,
            sender_signature: signature.0,
        },
        preconditions: Preconditions::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    let call_forest = CallForest {
        roots: vec![CallTree::new(action)],
        forest_hash: [0u8; 32],
    };
    Turn {
        agent,
        nonce,
        call_forest,
        fee: 0,
        memo: Some("captp.route".to_string()),
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

/// Build a CapTP-routed Turn from a pre-computed sender signature.
///
/// Used by the wire-layer PresentHandoff handler when the recipient sent
/// the canonical delivery signature in the wire message. The handler does
/// not have the recipient's signing key (only the recipient does).
#[allow(clippy::too_many_arguments)]
pub fn build_captp_turn_delivered_from_parts(
    agent: CellId,
    target: CellId,
    effect: Effect,
    nonce: u64,
    handoff_cert: HandoffCertificate,
    introducer_pk: [u8; 32],
    sender_pk: [u8; 32],
    sender_signature: [u8; 64],
) -> Turn {
    // Studio trace: captp_delivered turn constructed from wire-layer parts.
    // Emitted before executor verification; the executor emits a matching authorization event on success.
    info!(kind = "authorization", auth_kind = "captp_delivered", agent = %agent, target = %target, nonce);
    let action = Action {
        target,
        method: symbol("captp.route"),
        args: vec![],
        authorization: Authorization::CapTpDelivered {
            handoff_cert,
            introducer_pk,
            sender_pk,
            sender_signature,
        },
        preconditions: Preconditions::default(),
        effects: vec![effect],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    let call_forest = CallForest {
        roots: vec![CallTree::new(action)],
        forest_hash: [0u8; 32],
    };
    Turn {
        agent,
        nonce,
        call_forest,
        fee: 0,
        memo: Some("captp.route".to_string()),
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

/// Build the `Effect::ExportSturdyRef` for a CapHello-derived export.
///
/// `permissions` is the authorization tier the bearer of the resulting
/// sturdy ref obtains on enliven (block1-bind closure
/// `ExportSturdyRef-permissions`). The apply site rejects the effect if
/// the declared tier is wider than the cell's access tier; the federation
/// mirror records this same value when the post-commit hook materialises
/// the swiss-table entry.
pub fn export_sturdy_ref_effect(
    swiss_number: [u8; 32],
    target: CellId,
    permissions: pyana_cell::permissions::AuthRequired,
) -> Effect {
    Effect::ExportSturdyRef {
        swiss_number,
        target,
        permissions,
    }
}

/// Build the `Effect::EnlivenRef` for an `EnlivenSturdyRef` wire message.
///
/// `expected_cell_id` and `expected_permissions` come from the swiss-
/// table entry the wire layer's `SwissTable::enliven` returned for
/// `swiss_number` (block1-bind closure
/// `EnlivenRef-permissions-merkle`). The apply site cross-checks the
/// bearer's c-list for a capability that covers the declared tier;
/// passing forged values that don't match the bearer's authority
/// produces an executor rejection.
pub fn enliven_ref_effect(
    swiss_number: [u8; 32],
    bearer: CellId,
    expected_cell_id: CellId,
    expected_permissions: pyana_cell::permissions::AuthRequired,
) -> Effect {
    Effect::EnlivenRef {
        swiss_number,
        bearer,
        expected_cell_id,
        expected_permissions,
    }
}

/// Build the `Effect::DropRef` for a `DropRemoteRef` wire message.
pub fn drop_ref_effect(ref_id: [u8; 32]) -> Effect {
    Effect::DropRef { ref_id }
}

/// Build the `Effect::ValidateHandoff` for a `PresentHandoff` wire message.
///
/// `recipient_pk` and `introducer_pk` MUST match the carried
/// `HandoffCertificate`'s recipient pk and the introducer's federation pk,
/// respectively. The executor's `verify_captp_delivered` rejects the action
/// if the effect-carried keys diverge from the cert (block1-bind closure
/// `ValidateHandoff-runtime-variant-extend`).
pub fn validate_handoff_effect(
    cert_hash: [u8; 32],
    recipient_pk: [u8; 32],
    introducer_pk: [u8; 32],
) -> Effect {
    Effect::ValidateHandoff {
        cert_hash,
        recipient_pk,
        introducer_pk,
    }
}

// Suppress the otherwise-unused-import lint for `CapabilityRef`. The type is
// part of the cell::* re-export contract and is held here in anticipation of
// the P1.C tightening that emits a follow-up `Effect::GrantCapability` from
// `EnlivenRef` (per `DESIGN-captp-integration.md` §3.3).
#[allow(dead_code)]
fn _unused_cap_marker(_: CapabilityRef) {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn build_captp_turn_minimal() {
        let agent = CellId::from_bytes([1u8; 32]);
        let target = CellId::from_bytes([2u8; 32]);
        let turn = build_captp_turn(agent, target, Effect::DropRef { ref_id: [3u8; 32] }, 0);
        assert_eq!(turn.agent, agent);
        assert_eq!(turn.call_forest.roots.len(), 1);
        assert_eq!(turn.call_forest.roots[0].action.target, target);
        assert!(matches!(
            turn.call_forest.roots[0].action.effects[0],
            Effect::DropRef { .. }
        ));
    }

    #[test]
    fn effect_builders_produce_expected_variants() {
        let cell = CellId::from_bytes([7u8; 32]);
        assert!(matches!(
            export_sturdy_ref_effect(
                [0u8; 32],
                cell,
                pyana_cell::permissions::AuthRequired::None
            ),
            Effect::ExportSturdyRef { .. }
        ));
        assert!(matches!(
            enliven_ref_effect(
                [0u8; 32],
                cell,
                CellId::from_bytes([8u8; 32]),
                pyana_cell::permissions::AuthRequired::None
            ),
            Effect::EnlivenRef { .. }
        ));
        assert!(matches!(drop_ref_effect([0u8; 32]), Effect::DropRef { .. }));
        assert!(matches!(
            validate_handoff_effect([0u8; 32], [1u8; 32], [2u8; 32]),
            Effect::ValidateHandoff { .. }
        ));
    }
}
