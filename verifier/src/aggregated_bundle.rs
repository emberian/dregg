//! Stage 7-γ.2 Phase 2 — verifier-side surface for the aggregated bilateral
//! bundle.
//!
//! Mirrors the Phase 1 `bilateral_pair` shape: a JSON-friendly verdict + a
//! one-shot `verify_aggregated_bundle_json` entrypoint for the CLI subcommand.
//!
//! See `STAGE-7-GAMMA-2-PHASE-2-SKETCH.md` and
//! `pyana_turn::aggregate_bilateral_prover` for the prover counterpart.

use pyana_turn::aggregate_bilateral_prover::{AggregatedBundle, verify_aggregated_bundle};
use serde::{Deserialize, Serialize};

/// Verdict from the `aggregated-bundle` verifier subcommand.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AggregatedBundleVerdict {
    /// True iff all checks passed.
    pub verified: bool,
    /// Number of cells participating in the bundle (= outer trace's active row count).
    pub n_cells: usize,
    /// Bundle epoch (= turn.nonce).
    pub bundle_epoch: u64,
    /// Federation ids participating in the bundle.
    pub federation_ids: Vec<String>,
    /// Number of bilateral effects in the canonical Turn's schedule.
    pub transfer_count: usize,
    pub grant_count: usize,
    pub introduce_count: usize,
    /// Human-readable reason; "ok" on success.
    pub reason: String,
}

/// Verify a JSON-encoded [`AggregatedBundle`].
pub fn verify_aggregated_bundle_json(json: &str) -> AggregatedBundleVerdict {
    let bundle: AggregatedBundle = match serde_json::from_str(json) {
        Ok(b) => b,
        Err(e) => {
            return AggregatedBundleVerdict {
                verified: false,
                n_cells: 0,
                bundle_epoch: 0,
                federation_ids: vec![],
                transfer_count: 0,
                grant_count: 0,
                introduce_count: 0,
                reason: format!("bundle JSON parse error: {e}"),
            };
        }
    };
    verify_aggregated_bundle_struct(&bundle)
}

/// Verify a deserialized [`AggregatedBundle`]. Pure function over the bundle.
pub fn verify_aggregated_bundle_struct(bundle: &AggregatedBundle) -> AggregatedBundleVerdict {
    let sched = pyana_turn::bilateral_schedule::ExpectedBilateral::from_turn(&bundle.turn);
    let federation_ids = bundle.federation_ids.iter().map(hex::encode).collect();
    match verify_aggregated_bundle(bundle) {
        Ok(()) => AggregatedBundleVerdict {
            verified: true,
            n_cells: bundle.participating_cells.len(),
            bundle_epoch: bundle.bundle_epoch,
            federation_ids,
            transfer_count: sched.transfers.len(),
            grant_count: sched.grants.len(),
            introduce_count: sched.introduces.len(),
            reason: "ok".into(),
        },
        Err(e) => AggregatedBundleVerdict {
            verified: false,
            n_cells: bundle.participating_cells.len(),
            bundle_epoch: bundle.bundle_epoch,
            federation_ids,
            transfer_count: sched.transfers.len(),
            grant_count: sched.grants.len(),
            introduce_count: sched.introduces.len(),
            reason: format!("{e:?}"),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_turn::aggregate_bilateral_prover::prove_aggregated_bundle;
    use pyana_turn::{ActionBuilder, TurnBuilder, WitnessedReceipt};
    use pyana_types::CellId;

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    fn dummy_receipt(agent: CellId) -> pyana_turn::TurnReceipt {
        pyana_turn::TurnReceipt {
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
        }
    }

    fn fabricate_wr(turn: &pyana_turn::Turn, cell_id: &CellId) -> WitnessedReceipt {
        crate::bilateral_pair::fabricate_witnessed_receipt(turn, cell_id, dummy_receipt(turn.agent))
    }

    #[test]
    fn cli_verdict_happy_path() {
        let alice = cid(0xA1);
        let bob = cid(0xB2);

        let mut builder = TurnBuilder::new(alice, 1);
        let action = ActionBuilder::new_unchecked_for_tests(alice, "transfer", alice)
            .effect_transfer(alice, bob, 100)
            .build();
        builder.add_action(action);
        let turn = builder.fee(0).build();

        let entries = vec![
            (alice, fabricate_wr(&turn, &alice)),
            (bob, fabricate_wr(&turn, &bob)),
        ];
        let bundle = prove_aggregated_bundle(&turn, &entries).expect("prove");
        let json = bundle.to_json().expect("serialise");

        let verdict = verify_aggregated_bundle_json(&json);
        assert!(verdict.verified, "{:?}", verdict);
        assert_eq!(verdict.n_cells, 2);
        assert_eq!(verdict.transfer_count, 1);
    }
}
