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

use pyana_cell::{CapabilityRef, CellId, Preconditions};
use pyana_turn::action::{Action, Authorization, CommitmentMode, DelegationMode, Effect, symbol};
use pyana_turn::forest::{CallForest, CallTree};
use pyana_turn::turn::Turn;

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
    }
}

/// Build the `Effect::ExportSturdyRef` for a CapHello-derived export.
pub fn export_sturdy_ref_effect(swiss_number: [u8; 32], target: CellId) -> Effect {
    Effect::ExportSturdyRef {
        swiss_number,
        target,
    }
}

/// Build the `Effect::EnlivenRef` for an `EnlivenSturdyRef` wire message.
pub fn enliven_ref_effect(swiss_number: [u8; 32], bearer: CellId) -> Effect {
    Effect::EnlivenRef {
        swiss_number,
        bearer,
    }
}

/// Build the `Effect::DropRef` for a `DropRemoteRef` wire message.
pub fn drop_ref_effect(ref_id: [u8; 32]) -> Effect {
    Effect::DropRef { ref_id }
}

/// Build the `Effect::ValidateHandoff` for a `PresentHandoff` wire message.
pub fn validate_handoff_effect(cert_hash: [u8; 32]) -> Effect {
    Effect::ValidateHandoff { cert_hash }
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
        let turn = build_captp_turn(
            agent,
            target,
            Effect::DropRef { ref_id: [3u8; 32] },
            0,
        );
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
            export_sturdy_ref_effect([0u8; 32], cell),
            Effect::ExportSturdyRef { .. }
        ));
        assert!(matches!(
            enliven_ref_effect([0u8; 32], cell),
            Effect::EnlivenRef { .. }
        ));
        assert!(matches!(drop_ref_effect([0u8; 32]), Effect::DropRef { .. }));
        assert!(matches!(
            validate_handoff_effect([0u8; 32]),
            Effect::ValidateHandoff { .. }
        ));
    }
}
