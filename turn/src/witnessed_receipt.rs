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
/// # Two replay modes (Silver Vision vs. Golden Vision)
///
/// The bundle carries the inline trace (Silver Vision form) and, optionally,
/// a [`RecursiveProofVariant`] (Golden Vision form). A future replayer may
/// pick either:
///
/// - **Silver Vision (Inline trace replay):** re-run `EffectVmAir::eval_constraints`
///   over every consecutive row pair of `trace_rows`. Cost grows linearly with
///   trace height; the witness payload is hundreds of KB per turn.
/// - **Golden Vision (recursive proof):** verify the single recursive STARK
///   proof in `recursive_proof`, which attests "I re-ran the AIR over the
///   inline witness data and accepted." Verifier cost is independent of trace
///   length; the proof payload is ~KB.
///
/// Both modes attest the same fact (AIR acceptance over the same trace + PI).
/// A bundle may carry either or both: a producer running with
/// `recursive_compress = true` ships both an inline trace and a recursive
/// proof; a verifier may then choose freely.
///
/// # Why an additive shape instead of a bare `enum`
///
/// The Golden Vision plan in `THOUGHTS-AND-DREAMS.md` framed the two modes as
/// two enum variants. We carry the inline trace as a required field
/// (so the existing Silver-Vision-only consumer in `node/src/mcp.rs` stays
/// untouched, per this lane's "do not touch node/" constraint) plus an
/// optional [`RecursiveProofVariant`] for the Golden Vision compression. The
/// semantic contract — "RecursiveProof attests the same acceptance as
/// re-running the AIR over the inline trace" — is preserved.
///
/// [`BabyBear`]: pyana_circuit::field::BabyBear
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct WitnessBundle {
    /// Trace rows as canonical-BabyBear `u32` cells. Shape:
    /// `trace_rows.len() == trace_height`, each row has `EFFECT_VM_WIDTH = 105` cells.
    pub trace_rows: Vec<Vec<u32>>,
    /// How this witness is made available. Always `Inline` in v1.
    pub availability: WitnessAvailability,
    /// Optional Golden Vision recursive compression. When present, a
    /// replayer may verify *this proof* in lieu of re-running the AIR over
    /// `trace_rows`. The proof attests acceptance of the same trace; an
    /// adversary cannot replace the trace and reuse the proof because the
    /// proof's own public inputs would no longer match the receipt's PI.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub recursive_proof: Option<RecursiveProofVariant>,
}

/// Golden Vision recursive compression: a single small Plonky3 recursive
/// STARK proof attesting that the inline trace satisfied the Effect VM
/// AIR's constraints.
///
/// The proof is produced by
/// `pyana_circuit::recursive_witness_bundle::RecursiveProofProducer` and
/// verified by
/// `pyana_circuit::recursive_witness_bundle::verify_recursive_proof_variant`.
/// Both sides share a registry of `recursive_vk_hash` values (VK v2
/// layered encoding) so an unknown hash → reject at registry lookup.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct RecursiveProofVariant {
    /// Postcard-encoded `BatchStarkProof<PyanaRecursionConfig>` bytes from
    /// the recursive layer.
    pub proof_bytes: Vec<u8>,
    /// Public inputs the recursive proof commits to, as canonical-BabyBear
    /// `u32` cells. Should equal `WitnessedReceipt.public_inputs` for the
    /// scope-2 replay binding to hold.
    pub public_inputs: Vec<u32>,
    /// VK v2 layered hash identifying which recursive-verifier the
    /// receiver should dispatch to. v1 supports exactly one
    /// (`EFFECT_VM_RECURSIVE_VK_HASH`); unknown hashes are rejected at
    /// the registry lookup step.
    pub recursive_vk_hash: [u8; 32],
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
            recursive_proof: None,
        }
    }

    /// Like [`inline_from_trace`] but additionally attaches a recursive
    /// compression proof. The two replay modes are then both available.
    pub fn inline_with_recursive(
        trace: &[Vec<pyana_circuit::field::BabyBear>],
        recursive: RecursiveProofVariant,
    ) -> Self {
        let mut wb = Self::inline_from_trace(trace);
        wb.recursive_proof = Some(recursive);
        wb
    }

    /// True iff this bundle carries a Golden Vision recursive proof.
    pub fn has_recursive_proof(&self) -> bool {
        self.recursive_proof.is_some()
    }

    /// BLAKE3 hash of the postcard-serialized bundle. Always defined (even
    /// when `availability` is non-inline); binds the WR to a specific
    /// witness independent of disclosure.
    ///
    /// Note: this hash covers **both** the inline trace and the optional
    /// recursive proof. If a producer ships only-inline today and decides
    /// to add a recursive proof later, the witness_hash changes — that is
    /// intentional, since the bundle has changed.
    pub fn witness_hash(&self) -> [u8; 32] {
        let bytes = postcard::to_allocvec(self).expect("WitnessBundle is serializable");
        *blake3::hash(&bytes).as_bytes()
    }
}

// ---------------------------------------------------------------------------
// Recursive compression bridge (Golden Vision)
// ---------------------------------------------------------------------------

/// Produce a [`RecursiveProofVariant`] from an inline scope-2 trace + the
/// receipt's public inputs.
///
/// Thin wrapper around
/// [`pyana_circuit::recursive_witness_bundle::RecursiveProofProducer::produce`]
/// so [`WitnessedReceipt::from_components_with_compression`] does not have
/// to thread `BabyBear` through its signature. Returns the compressed
/// variant on success; on failure returns the error string from the
/// recursion library (e.g. AIR build failure, postcard encode error).
///
/// Relies on the `recursion` feature being enabled in `pyana-circuit`
/// (which is in its default feature set). If the host disables the
/// feature, this entry point becomes a link-time error — which is the
/// honest signal: opt-in recursive compression requires the recursion
/// substrate.
fn produce_recursive_variant(
    trace: &[Vec<pyana_circuit::field::BabyBear>],
    public_inputs_u32: &[u32],
) -> Result<RecursiveProofVariant, String> {
    use pyana_circuit::field::BabyBear;
    use pyana_circuit::recursive_witness_bundle::RecursiveProofProducer;

    let pi: Vec<BabyBear> = public_inputs_u32
        .iter()
        .map(|&v| BabyBear::new_canonical(v))
        .collect();

    let out = RecursiveProofProducer::produce(trace, &pi)?;
    Ok(RecursiveProofVariant {
        proof_bytes: out.proof_bytes,
        public_inputs: public_inputs_u32.to_vec(),
        recursive_vk_hash: out.recursive_vk_hash,
    })
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
        Self::from_components_with_compression(receipt, proof_bytes, public_inputs, trace, false)
    }

    /// Like [`Self::from_components`] but with an opt-in Golden Vision
    /// recursive compression flag.
    ///
    /// When `recursive_compress` is `true` AND `trace` is `Some`, this
    /// runs `pyana_circuit::recursive_witness_bundle::RecursiveProofProducer`
    /// on the trace + public inputs and attaches a [`RecursiveProofVariant`]
    /// to the resulting [`WitnessBundle`]. The inline trace is kept
    /// alongside, so downstream replayers may pick *either* mode (re-run
    /// AIR vs. recursive verify).
    ///
    /// When `recursive_compress` is `false` (default), behaves identically
    /// to [`Self::from_components`].
    ///
    /// # Errors
    ///
    /// Recursive compression is best-effort: if the producer fails, the
    /// receipt is still returned with the inline trace attached (silver
    /// vision form) so the chain is not lost. The recursive proof is just
    /// not attached. Callers wanting hard-fail-on-compression should use
    /// [`Self::from_components_strict_recursive`].
    pub fn from_components_with_compression(
        receipt: TurnReceipt,
        proof_bytes: Vec<u8>,
        public_inputs: Vec<u32>,
        trace: Option<&[Vec<pyana_circuit::field::BabyBear>]>,
        recursive_compress: bool,
    ) -> Self {
        let (witness_bundle, witness_hash) = match trace {
            Some(t) => {
                let mut wb = WitnessBundle::inline_from_trace(t);
                if recursive_compress {
                    if let Ok(rp) = produce_recursive_variant(t, &public_inputs) {
                        wb.recursive_proof = Some(rp);
                    }
                }
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

    /// Like [`Self::from_components_with_compression`] but hard-fails if
    /// recursive compression cannot be produced. Use when the caller
    /// requires the Golden Vision form.
    pub fn from_components_strict_recursive(
        receipt: TurnReceipt,
        proof_bytes: Vec<u8>,
        public_inputs: Vec<u32>,
        trace: &[Vec<pyana_circuit::field::BabyBear>],
    ) -> Result<Self, String> {
        let rp = produce_recursive_variant(trace, &public_inputs)?;
        let wb = WitnessBundle::inline_with_recursive(trace, rp);
        let h = wb.witness_hash();
        Ok(Self {
            receipt,
            proof_bytes,
            public_inputs,
            witness_bundle: Some(wb),
            witness_hash: h,
            aggregate_membership: None,
        })
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
            was_encrypted: false,
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
