//! Witnessed receipt chains — see `WITNESSED-RECEIPT-CHAIN-DESIGN.md`.
//!
//! A [`WitnessedReceipt`] wraps an existing [`TurnReceipt`] with the material
//! needed for *scope-(2)* replay: the STARK proof bytes, the public inputs,
//! and (optionally) the full trace witness. The receipt itself is unchanged
//! — this is purely an additive on-disk / wire shape.
//!
//! # v1 design choices
//!
//! Per the design doc (§§3, 8) v1 implements:
//!
//! * Replay scope (2) — re-derive trace + verify (NOT re-execute).
//! * Storage strategy (A) — prover-local witness bundle.
//! * Structural shape (C) — [`WitnessAvailability`] is an enum so that
//!   encryption (B) and bifurcation can land additively in v2.
//!
//! The [`aggregate_membership`] field is a hook for the parallel STAGE-7-γ
//! cross-cell aggregation work; it is always `None` in v1.
//!
//! # Construction site
//!
//! The canonical construction site is wherever an Effect-VM STARK proof is
//! generated. Today that is `node/src/mcp.rs::generate_effect_vm_proof`
//! (the node's MCP tool layer) — not `turn/src/executor.rs`. The
//! [`WitnessedReceipt::from_components`] constructor below is the
//! lane-agnostic factory; this crate exposes [`TurnExecutor::wrap_witnessed`]
//! as a convenience for callers that hold both a receipt and a fresh proof.

use crate::turn::{Turn, TurnReceipt};
use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// AggregateMembership stub (STAGE-7-γ hook; populated by γ.0 when it lands)
// ---------------------------------------------------------------------------

/// Cross-cell aggregation hook. See `STAGE-7-GAMMA-AGGREGATION-DESIGN.md`.
///
/// In v1 this field is always `None` on a [`WitnessedReceipt`]. When the
/// gamma aggregator lands, an aggregated batch will populate this with an
/// inclusion proof binding this receipt's `witness_hash` into the batch
/// commitment. The struct intentionally carries the minimum interface
/// surface so γ.0 can extend it without breaking the v1 wire shape.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct AggregateMembership {
    /// Root of the aggregator's batch commitment (Poseidon2 over witness hashes).
    pub batch_root: [u8; 32],
    /// Index of this receipt's witness in the batch (0-based).
    pub leaf_index: u32,
    /// Sibling hashes along the path from leaf to root (depth-prefixed).
    #[serde(default)]
    pub merkle_siblings: Vec<[u8; 32]>,
}

// ---------------------------------------------------------------------------
// WitnessAvailability — structural shape (C)
// ---------------------------------------------------------------------------

/// How the witness bundle is made available to a future replayer.
///
/// v1 ships only [`WitnessAvailability::Inline`]: the bundle is embedded
/// verbatim in the [`WitnessedReceipt`]. Future variants will carry an
/// encrypted ciphertext (strategy B) or a public/private split (strategy C);
/// the existing enum shape ensures those land additively.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum WitnessAvailability {
    /// Full witness in-line (this WR is self-contained for replay).
    Inline,
    // EncryptedTo { recovery_pk: [u8; 32] },  // v2 (strategy B)
    // Split { public_only: bool },            // v2 (strategy C bifurcation)
}

// ---------------------------------------------------------------------------
// WitnessBundle — replay material (scope 2)
// ---------------------------------------------------------------------------

/// The replay-material bundle.
///
/// For v1 we ship the post-trace-generation form: the full trace rows as
/// canonical-BabyBear `u32` cells. This is the most direct mirror of what
/// `stark::prove` consumed; a replayer reconstructs the [`BabyBear`]
/// elements by calling `BabyBear::new_canonical(u32)`.
///
/// We deliberately do *not* ship the pre-state + effects in v1 — those
/// remain the prover's local secret and are the v2 refinement (strategy C
/// bifurcation; design doc §3).
///
/// [`BabyBear`]: pyana_circuit::field::BabyBear
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct WitnessBundle {
    /// Trace rows as canonical-BabyBear `u32` cells. Shape:
    /// `trace_rows.len() == trace_height`, each row has `EFFECT_VM_WIDTH = 105` cells.
    pub trace_rows: Vec<Vec<u32>>,
    /// How this witness is made available. Always `Inline` in v1.
    pub availability: WitnessAvailability,
}

impl WitnessBundle {
    /// Construct an inline witness bundle from the prover's in-memory trace.
    pub fn inline_from_trace(trace: &[Vec<pyana_circuit::field::BabyBear>]) -> Self {
        let trace_rows: Vec<Vec<u32>> = trace
            .iter()
            .map(|row| row.iter().map(|x| x.as_u32()).collect())
            .collect();
        Self {
            trace_rows,
            availability: WitnessAvailability::Inline,
        }
    }

    /// BLAKE3 hash of the postcard-serialized bundle. Always defined (even
    /// when `availability` is non-inline); binds the WR to a specific
    /// witness independent of disclosure.
    pub fn witness_hash(&self) -> [u8; 32] {
        let bytes = postcard::to_allocvec(self).expect("WitnessBundle is serializable");
        *blake3::hash(&bytes).as_bytes()
    }
}

// ---------------------------------------------------------------------------
// WitnessedReceipt
// ---------------------------------------------------------------------------

/// A [`TurnReceipt`] enriched with sufficient material for STARK replay.
///
/// On-disk / wire shape. In-memory the hot paths still pass plain
/// [`TurnReceipt`]; lift to `WitnessedReceipt` only at archival, audit-export,
/// or `pyana-verifier` consumption time.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WitnessedReceipt {
    /// The receipt itself. Unchanged from today, so existing chains stay valid.
    pub receipt: TurnReceipt,
    /// STARK proof bytes (`stark::proof_to_bytes` output). Verifiable
    /// stand-alone via `verifier::verify_effect_vm_proof`.
    pub proof_bytes: Vec<u8>,
    /// Public inputs as a flat `u32` vector (BabyBear canonical form).
    /// Redundant with `proof.public_inputs` but extracted for replayer
    /// convenience — avoids deserialising the proof just to read PI.
    pub public_inputs: Vec<u32>,
    /// The witness bundle. Optional at the API boundary: a receipt without
    /// a witness is still a (scope-1) verifiable artifact.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub witness_bundle: Option<WitnessBundle>,
    /// Hash of the witness bundle (committed even when the bundle itself
    /// is absent or encrypted). All-zeros when `witness_bundle` is `None`.
    pub witness_hash: [u8; 32],
    /// Cross-cell aggregation hook. See [`AggregateMembership`]. Always
    /// `None` in v1.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub aggregate_membership: Option<AggregateMembership>,
}

impl WitnessedReceipt {
    /// Build a [`WitnessedReceipt`] from raw components produced by the
    /// prove call. This is the lane-agnostic factory; both
    /// `node/src/mcp.rs::generate_effect_vm_proof` and any future
    /// per-cell prover may call into it.
    ///
    /// `trace` may be `None` for scope-(1) export (proof + PI only); pass
    /// `Some(&trace)` for scope-(2) export (the trace becomes an inline
    /// witness bundle).
    pub fn from_components(
        receipt: TurnReceipt,
        proof_bytes: Vec<u8>,
        public_inputs: Vec<u32>,
        trace: Option<&[Vec<pyana_circuit::field::BabyBear>]>,
    ) -> Self {
        let (witness_bundle, witness_hash) = match trace {
            Some(t) => {
                let wb = WitnessBundle::inline_from_trace(t);
                let h = wb.witness_hash();
                (Some(wb), h)
            }
            None => (None, [0u8; 32]),
        };
        Self {
            receipt,
            proof_bytes,
            public_inputs,
            witness_bundle,
            witness_hash,
            aggregate_membership: None,
        }
    }

    /// Stage 7-γ.2 Phase 1: verify bilateral cross-cell consistency for a
    /// bundle of WitnessedReceipts sharing one Turn.
    ///
    /// Given the turn (which carries the canonical `call_forest`) and the
    /// per-cell-id WRs that came out of executing it, this:
    ///
    /// 1. Confirms each WR's `public_inputs` carry the γ.2 layout
    ///    (length ≥ BASE_COUNT).
    /// 2. Reconstructs the expected bilateral schedule from the turn.
    /// 3. For every (cell_id, WR) pair, recomputes the expected counts
    ///    + accumulator roots and compares to the WR's PI.
    /// 4. Enforces the IS_AGENT_CELL exactly-zero-or-one rule.
    /// 5. Cross-side existence: every Transfer / Grant / Introduce in the
    ///    schedule that names any covered cell must have all its peers
    ///    covered.
    ///
    /// Returns `Ok(())` on success or a human-readable error on rejection.
    /// This is the verifier-side gate from `STAGE-7-GAMMA-2-PI-DESIGN.md` §4.
    pub fn verify_bilateral_chain(
        wrs: &[(pyana_types::CellId, &WitnessedReceipt)],
        turn: &Turn,
    ) -> Result<(), crate::error::TurnError> {
        use pyana_circuit::field::BabyBear;

        let bundle: Vec<(pyana_types::CellId, Vec<BabyBear>)> = wrs
            .iter()
            .map(|(cid, wr)| {
                let pi: Vec<BabyBear> = wr
                    .public_inputs
                    .iter()
                    .map(|&v| BabyBear::new_canonical(v))
                    .collect();
                (cid.clone(), pi)
            })
            .collect();
        crate::executor::TurnExecutor::verify_bilateral_bundle(&bundle, turn)
    }

    /// Convenience: serialize a chain (`Vec<WitnessedReceipt>`) as JSON.
    /// Used by demo / audit paths.
    pub fn chain_to_json(chain: &[Self]) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(chain)
    }

    /// Convenience: deserialize a chain from JSON.
    pub fn chain_from_json(json: &str) -> Result<Vec<Self>, serde_json::Error> {
        serde_json::from_str(json)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::turn::TurnReceipt;
    use pyana_types::CellId;

    fn dummy_receipt() -> TurnReceipt {
        TurnReceipt {
            turn_hash: [1u8; 32],
            forest_hash: [2u8; 32],
            pre_state_hash: [3u8; 32],
            post_state_hash: [4u8; 32],
            timestamp: 42,
            effects_hash: [5u8; 32],
            computrons_used: 100,
            action_count: 1,
            previous_receipt_hash: None,
            agent: CellId::from_bytes([0xAB; 32]),
            federation_id: [0u8; 32],
            routing_directives: Vec::new(),
            introduction_exports: Vec::new(),
            derivation_records: Vec::new(),
            emitted_events: Vec::new(),
            executor_signature: None,
            finality: Default::default(),
        }
    }

    #[test]
    fn from_components_without_trace_has_zero_witness_hash() {
        let wr =
            WitnessedReceipt::from_components(dummy_receipt(), vec![0u8; 4], vec![1, 2, 3], None);
        assert!(wr.witness_bundle.is_none());
        assert_eq!(wr.witness_hash, [0u8; 32]);
        assert!(wr.aggregate_membership.is_none());
    }

    #[test]
    fn from_components_with_trace_binds_witness_hash() {
        use pyana_circuit::field::BabyBear;
        let trace: Vec<Vec<BabyBear>> = (0..4)
            .map(|i| (0..3).map(|j| BabyBear::new((i * 3 + j) as u32)).collect())
            .collect();
        let wr = WitnessedReceipt::from_components(
            dummy_receipt(),
            vec![0u8; 4],
            vec![1, 2, 3],
            Some(&trace),
        );
        let wb = wr.witness_bundle.as_ref().unwrap();
        assert_eq!(wb.trace_rows.len(), 4);
        assert_eq!(wb.trace_rows[0].len(), 3);
        assert_eq!(wr.witness_hash, wb.witness_hash());
        assert_ne!(wr.witness_hash, [0u8; 32]);
    }

    #[test]
    fn json_roundtrip() {
        let wr = WitnessedReceipt::from_components(
            dummy_receipt(),
            vec![1, 2, 3, 4],
            vec![10, 20, 30],
            None,
        );
        let chain = vec![wr.clone()];
        let json = WitnessedReceipt::chain_to_json(&chain).unwrap();
        let back = WitnessedReceipt::chain_from_json(&json).unwrap();
        assert_eq!(back.len(), 1);
        assert_eq!(back[0].public_inputs, wr.public_inputs);
        assert_eq!(back[0].proof_bytes, wr.proof_bytes);
        assert_eq!(back[0].witness_hash, wr.witness_hash);
        assert_eq!(back[0].receipt.turn_hash, wr.receipt.turn_hash);
    }
}
