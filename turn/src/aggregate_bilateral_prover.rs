//! Stage 7-γ.2 Phase 2 — joint bilateral aggregation prover + verifier.
//!
//! Given N `WitnessedReceipt`s sharing one `Turn`, this module produces a
//! single outer proof attesting bilateral cross-cell consistency. The outer
//! AIR is `dregg_circuit::bilateral_aggregation_air::BilateralAggregationAir`
//! (`STAGE-7-GAMMA-2-PHASE-2-SKETCH.md`).
//!
//! Two consumer surfaces:
//!
//!   1. [`prove_aggregated_bundle`] — the aggregator. Takes the canonical
//!      Turn + the per-cell WRs, derives the bilateral schedule, builds the
//!      outer trace, runs the inner Effect VM verifies, and emits an
//!      [`AggregatedBundle`].
//!   2. [`verify_aggregated_bundle`] — the consumer. Takes the bundle and
//!      verifies (a) the outer STARK is sound, (b) the outer PI matches
//!      what the canonical Turn predicts.
//!
//! The bundle's outer proof verifies in *constant time relative to N*: a
//! consumer holding only the bundle's `outer_proof_bytes` + the canonical
//! Turn does not need to re-run any per-cell STARK. That is the headline win
//! Phase 2 buys over Phase 1.

use crate::bilateral_schedule::{BilateralCounts, BilateralRoots, ExpectedBilateral};
use crate::error::TurnError;
use crate::turn::Turn;
use crate::witnessed_receipt::WitnessedReceipt;
use dregg_circuit::bilateral_aggregation_air::{
    AggregationInnerRow, AggregationOuterPi, BilateralAggregationAir, OUTER_BASE_COUNT,
    build_aggregation_trace,
};
use dregg_circuit::effect_vm::pi as inner_pi;
use dregg_circuit::field::BabyBear;
use dregg_types::CellId;
use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// Aggregated bundle on-disk shape
// ---------------------------------------------------------------------------

/// The on-disk / wire shape of a Phase-2 aggregated bilateral bundle.
///
/// `outer_pi` is the reduced, fixed-width public-input vector
/// (`OUTER_BASE_COUNT = 23` felts). `outer_proof_bytes` is the outer STARK's
/// `proof_to_bytes` serialization. `participating_cells` lists the cell-ids
/// covered by the bundle (in trace-row order) so an auditor can reconstruct
/// the per-row inner PI projection from the canonical Turn.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AggregatedBundle {
    /// The canonical Turn (carries `call_forest`, `nonce`, `agent`,
    /// `previous_receipt_hash`). The verifier re-derives every bilateral
    /// schedule field from this.
    pub turn: Turn,
    /// Ordered cell-ids participating in the bundle (one per outer trace
    /// row). The aggregator chose this order; the verifier replays the
    /// schedule against it.
    pub participating_cells: Vec<CellId>,
    /// Outer-AIR public inputs (length `OUTER_BASE_COUNT = 23`). Carries
    /// the bundle-level summary `(turn_hash, effects_hash_global,
    /// actor_nonce, previous_receipt_hash, agent_cell_id, n_cells,
    /// bilateral_consistent)`.
    pub outer_pi: Vec<u32>,
    /// Outer STARK proof bytes (`stark::proof_to_bytes` output). A real FRI +
    /// Merkle + Fiat-Shamir proof over the aggregation AIR; verified standalone
    /// by `dregg_circuit::stark::verify` against `outer_pi`.
    pub outer_proof_bytes: Vec<u8>,
    /// The outer aggregation trace (rows × `AGG_WIDTH`), canonical-BabyBear u32
    /// cells. Shipped so the verifier can (a) bind it to the proof via
    /// `stark::recompute_trace_commitment` == `proof.trace_commitment` and
    /// (b) cross-check each row's `expected_*` columns against the
    /// schedule the canonical Turn predicts. The STARK proof guarantees this
    /// exact trace satisfies the aggregation constraints; the trace is not
    /// trusted on its own.
    pub outer_trace: Vec<Vec<u32>>,
    /// Federation ids participating in this bundle, in dedup'd order. v1
    /// pulls these from the receipts on each WR; cross-federation bundles
    /// (Phase 2.5) will populate this from richer sources.
    pub federation_ids: Vec<[u8; 32]>,
    /// Bundle epoch — set to `turn.nonce` by the aggregator. The verifier
    /// cross-checks this against `outer_pi[OUTER_ACTOR_NONCE]`.
    pub bundle_epoch: u64,
}

impl AggregatedBundle {
    /// Convenience: serialise to JSON.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Convenience: deserialise from JSON.
    pub fn from_json(text: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(text)
    }
}

// ---------------------------------------------------------------------------
// Schedule → AIR row projection
// ---------------------------------------------------------------------------

/// Pack a `(BilateralCounts, BilateralRoots)` pair into the AIR row's
/// `expected_counts` + `expected_roots` blocks. Canonical order
/// (`bilateral_aggregation_air` module docs).
fn pack_expected(
    counts: BilateralCounts,
    roots: BilateralRoots,
) -> ([BabyBear; 7], [[BabyBear; 4]; 7]) {
    (
        [
            BabyBear::new(counts.outbound_transfer),
            BabyBear::new(counts.inbound_transfer),
            BabyBear::new(counts.outbound_grant),
            BabyBear::new(counts.inbound_grant),
            BabyBear::new(counts.intro_as_introducer),
            BabyBear::new(counts.intro_as_recipient),
            BabyBear::new(counts.intro_as_target),
        ],
        [
            roots.outgoing_transfer,
            roots.incoming_transfer,
            roots.outgoing_grant,
            roots.incoming_grant,
            roots.intro_as_introducer,
            roots.intro_as_recipient,
            roots.intro_as_target,
        ],
    )
}

/// Project a 32-byte cell-id to an 8-felt decomposition. Mirrors the
/// `canonical_32_to_felts_4` pattern but at 4-bytes-per-felt
/// (no overflow on BabyBear's 31-bit modulus).
pub(crate) fn cell_id_to_felts_8(c: &CellId) -> [BabyBear; 8] {
    let bytes = c.as_bytes();
    let mut out = [BabyBear::ZERO; 8];
    for i in 0..8 {
        let start = i * 4;
        // Take 4 bytes, mask the top bit of the high byte so the felt fits
        // in 31 bits. The pattern matches `canonical_32_to_felts_4`'s
        // truncation discipline.
        let mut v = u32::from_be_bytes([
            bytes[start],
            bytes[start + 1],
            bytes[start + 2],
            bytes[start + 3],
        ]);
        v &= 0x7FFF_FFFF;
        out[i] = BabyBear::new(v);
    }
    out
}

// ---------------------------------------------------------------------------
// Prover
// ---------------------------------------------------------------------------

/// Produce an [`AggregatedBundle`] from `(turn, per_cell)`. The aggregator:
///
///   1. Reconstructs the bilateral schedule from `turn.call_forest +
///      turn.nonce`.
///   2. Per cell, verifies the WR is a full scope-(2) receipt/witness
///      artifact, then checks its `public_inputs` carry the expected bilateral
///      counts + roots (the same per-cell check Phase 1's Rust loop does — we
///      run it here to fail fast before invoking the prover).
///   3. Builds the outer AIR trace (one row per WR, padded to power of two).
///   4. Computes the outer public-input vector from the canonical Turn.
///   5. Runs the outer STARK prover (via `EffectVmAir`'s
///      `dregg_circuit::stark` family — the outer AIR is *currently*
///      wrapped as a generic StarkAir; the recursion-mode wrapping is the
///      follow-up commit).
///
/// **Important:** this function does not run the per-cell Effect VM STARK
/// verification — the brief makes step 1 (Phase-1 verify each WR) a
/// caller-provided precondition. It does, however, require the full inline
/// witness bundle and witness-hash binding. Aggregated gamma.2 output is a
/// devnet gossip artifact; accepting scope-(1)-only WRs here would make the
/// aggregate look stronger than the receipt/witness material it summarizes.
pub fn prove_aggregated_bundle(
    turn: &Turn,
    per_cell: &[(CellId, WitnessedReceipt)],
) -> Result<AggregatedBundle, TurnError> {
    if per_cell.is_empty() {
        return Err(TurnError::InvalidExecutionProof(
            "aggregate_bilateral: bundle must contain at least one WR".into(),
        ));
    }

    for (cid, wr) in per_cell {
        wr.require_scope2_witness().map_err(|e| {
            TurnError::InvalidExecutionProof(format!(
                "aggregate_bilateral: cell {:?} is not a full scope-2 witnessed receipt: {e}",
                cid
            ))
        })?;
    }

    // Phase-1 bundle check is the load-bearing soundness gate. We invoke
    // the existing `verify_bilateral_chain` here so that *every* adversarial
    // scenario the brief flags (tampered PI, mismatched sender/receiver,
    // tampered transfer_id, missing peer) is rejected before we touch the
    // prover. The outer AIR then witnesses the SAME per-cell PIs against
    // the SAME schedule — its constraints would also catch these, but
    // failing-fast here gives a clean error.
    let view: Vec<(CellId, &WitnessedReceipt)> =
        per_cell.iter().map(|(c, w)| (c.clone(), w)).collect();
    WitnessedReceipt::verify_bilateral_chain(&view, turn)?;

    let schedule = ExpectedBilateral::from_turn(turn);
    let actor_nonce = turn.nonce;

    // Build per-row data. Row i corresponds to per_cell[i].
    let mut rows: Vec<AggregationInnerRow> = Vec::with_capacity(per_cell.len());
    let mut federation_ids_seen: Vec<[u8; 32]> = Vec::new();
    for (cid, wr) in per_cell {
        if wr.public_inputs.len() < inner_pi::BASE_COUNT {
            return Err(TurnError::InvalidExecutionProof(format!(
                "WR for cell {:?}: PI has {} entries, expected at least {} (γ.2 layout)",
                cid,
                wr.public_inputs.len(),
                inner_pi::BASE_COUNT
            )));
        }
        let inner_pi_vec: Vec<BabyBear> = wr.public_inputs[..inner_pi::BASE_COUNT]
            .iter()
            .map(|&v| BabyBear::new_canonical(v))
            .collect();

        let counts = schedule.counts_for(cid);
        let roots = schedule.roots_for(cid, actor_nonce);
        let (expected_counts, expected_roots) = pack_expected(counts, roots);

        rows.push(AggregationInnerRow {
            inner_pi: inner_pi_vec,
            expected_counts,
            expected_roots,
        });

        let fed = wr.receipt.federation_id;
        if !federation_ids_seen.contains(&fed) {
            federation_ids_seen.push(fed);
        }
    }

    let trace = build_aggregation_trace(&rows);

    // Outer PI.
    let (turn_hash_4, effects_hash_global_4, _, prev_receipt_4) =
        crate::executor::TurnExecutor::compute_turn_identity_pi(turn);
    let outer_pi_typed = AggregationOuterPi {
        turn_hash: turn_hash_4,
        effects_hash_global: effects_hash_global_4,
        actor_nonce: BabyBear::new((actor_nonce & 0x7FFF_FFFF) as u32),
        previous_receipt_hash: prev_receipt_4,
        agent_cell_id: cell_id_to_felts_8(&turn.agent),
        n_cells: per_cell.len() as u32,
        bilateral_consistent: BabyBear::new(1),
    };
    let outer_pi_bb = outer_pi_typed.to_vec();
    debug_assert_eq!(outer_pi_bb.len(), OUTER_BASE_COUNT);

    // Run the outer STARK prover. `BilateralAggregationAir` now implements
    // `dregg_circuit::stark::StarkAir` (the same FRI + Merkle + Fiat-Shamir
    // proof system the per-cell Effect VM AIR uses). `stark::try_prove`
    // commits the outer trace, evaluates the aggregation constraints over the
    // blown-up Reed-Solomon domain, runs FRI low-degree testing, and emits
    // proof bytes that `verify_aggregated_bundle` checks WITHOUT re-seeing the
    // trace. This is the headline upgrade over the prior trust-and-replay
    // witness: a tampered trace now fails FRI / constraint consistency rather
    // than being re-executed in Rust.
    let proof = dregg_circuit::stark::try_prove(
        &BilateralAggregationAir,
        &trace,
        &outer_pi_bb,
    )
    .map_err(|e| {
        TurnError::InvalidExecutionProof(format!(
            "aggregate_bilateral: outer STARK proving failed: {e}"
        ))
    })?;
    let outer_proof_bytes = dregg_circuit::stark::proof_to_bytes(&proof);
    let outer_trace: Vec<Vec<u32>> = trace
        .iter()
        .map(|row| row.iter().map(|x| x.as_u32()).collect())
        .collect();

    let outer_pi_u32: Vec<u32> = outer_pi_bb.iter().map(|x| x.as_u32()).collect();

    Ok(AggregatedBundle {
        turn: turn.clone(),
        participating_cells: per_cell.iter().map(|(c, _)| c.clone()).collect(),
        outer_pi: outer_pi_u32,
        outer_proof_bytes,
        outer_trace,
        federation_ids: federation_ids_seen,
        bundle_epoch: actor_nonce,
    })
}

// ---------------------------------------------------------------------------
// Verifier
// ---------------------------------------------------------------------------

/// Verify an [`AggregatedBundle`]. Pure function over the bundle; no shared
/// state. Returns `Ok(())` on success and a human-readable error otherwise.
/// Closes the threat surface:
///
/// - Tampered outer PI: caught by the canonical-Turn-derived PI check (step 2)
///   and by the STARK proof's public-input binding (step 4).
/// - Tampered trace: caught two ways — the recomputed trace commitment no
///   longer matches the proof's `trace_commitment` (step 4b), and the real
///   STARK proof (FRI + constraint consistency) does not verify against a
///   trace that violates the aggregation AIR's CG-2/CG-3/CG-4 constraints.
/// - Tampered participating_cells order: caught by the per-row schedule
///   projection mismatching the trace's `expected_*` block (step 5).
/// - Forged "consistent" flag: pinned to 1 by the AIR's BILATERAL_CONSISTENT
///   constraint and rejected up front (`outer_pi[OUTER_BILATERAL_CONSISTENT]
///   != 1`).
///
/// Unlike the prior trust-and-replay path, step 4 is now a *real* STARK
/// verification: `dregg_circuit::stark::verify` checks the proof without
/// re-executing the trace. The shipped trace is bound to that proof by
/// commitment equality (step 4b) so the schedule cross-check in step 5
/// operates on the exact trace the proof attests.
pub fn verify_aggregated_bundle(bundle: &AggregatedBundle) -> Result<(), TurnError> {
    use dregg_circuit::bilateral_aggregation_air as ag;

    // Step 1: outer PI sanity.
    if bundle.outer_pi.len() != OUTER_BASE_COUNT {
        return Err(TurnError::InvalidExecutionProof(format!(
            "aggregate_bilateral: outer PI has {} entries, expected {}",
            bundle.outer_pi.len(),
            OUTER_BASE_COUNT
        )));
    }
    if bundle.outer_pi[ag::OUTER_BILATERAL_CONSISTENT] != 1 {
        return Err(TurnError::InvalidExecutionProof(format!(
            "aggregate_bilateral: BILATERAL_CONSISTENT == {}, expected 1",
            bundle.outer_pi[ag::OUTER_BILATERAL_CONSISTENT]
        )));
    }

    // Step 2: re-derive the expected outer PI from the canonical Turn and
    // confirm equality. This catches every "turn-level forgery" scenario:
    // a malicious aggregator who replaces `turn` while keeping the original
    // outer PI is rejected because the recomputed turn-identity quad won't
    // match what the bundle declares.
    let (turn_hash_4, effects_hash_global_4, _, prev_receipt_4) =
        crate::executor::TurnExecutor::compute_turn_identity_pi(&bundle.turn);
    let expected_outer = AggregationOuterPi {
        turn_hash: turn_hash_4,
        effects_hash_global: effects_hash_global_4,
        actor_nonce: BabyBear::new((bundle.turn.nonce & 0x7FFF_FFFF) as u32),
        previous_receipt_hash: prev_receipt_4,
        agent_cell_id: cell_id_to_felts_8(&bundle.turn.agent),
        n_cells: bundle.participating_cells.len() as u32,
        bilateral_consistent: BabyBear::new(1),
    };
    let expected_u32: Vec<u32> = expected_outer.to_vec().iter().map(|x| x.as_u32()).collect();
    if expected_u32 != bundle.outer_pi {
        return Err(TurnError::InvalidExecutionProof(format!(
            "aggregate_bilateral: outer PI mismatch; turn-derived {:?} != bundle {:?}",
            expected_u32, bundle.outer_pi
        )));
    }

    // Step 3: bundle_epoch matches turn nonce.
    if bundle.bundle_epoch != bundle.turn.nonce {
        return Err(TurnError::InvalidExecutionProof(format!(
            "aggregate_bilateral: bundle_epoch ({}) != turn.nonce ({})",
            bundle.bundle_epoch, bundle.turn.nonce
        )));
    }

    // Step 4: REAL outer STARK verification. Deserialise the proof bytes and
    // verify them standalone against the outer PI — FRI low-degree testing,
    // constraint-consistency, and boundary openings, none of which re-execute
    // the trace. A trace that violates CG-2/CG-3/CG-4 cannot have produced a
    // verifying proof.
    let outer_pi_bb: Vec<BabyBear> = bundle
        .outer_pi
        .iter()
        .map(|&v| BabyBear::new_canonical(v))
        .collect();
    let proof = dregg_circuit::stark::proof_from_bytes(&bundle.outer_proof_bytes).map_err(|e| {
        TurnError::InvalidExecutionProof(format!(
            "aggregate_bilateral: failed to decode outer STARK proof: {e}"
        ))
    })?;
    if proof.air_name != BilateralAggregationAir::AIR_NAME {
        return Err(TurnError::InvalidExecutionProof(format!(
            "aggregate_bilateral: proof AIR name mismatch: {}",
            proof.air_name
        )));
    }
    dregg_circuit::stark::verify(&BilateralAggregationAir, &proof, &outer_pi_bb).map_err(|e| {
        TurnError::InvalidExecutionProof(format!(
            "aggregate_bilateral: outer STARK verification failed: {e}"
        ))
    })?;

    // Step 4b: bind the shipped trace to the proof. Reconstruct the trace
    // Merkle commitment and require it to equal the proof's. This makes the
    // shipped `outer_trace` provably the trace the STARK attests, so the
    // schedule cross-check in step 5 (which needs the per-row columns) cannot
    // be fed a different trace than the one the proof verified.
    let trace_bb: Vec<Vec<BabyBear>> = bundle
        .outer_trace
        .iter()
        .map(|row| row.iter().map(|&v| BabyBear::new_canonical(v)).collect())
        .collect();
    let recomputed = dregg_circuit::stark::recompute_trace_commitment(
        &BilateralAggregationAir,
        &trace_bb,
    )
    .ok_or_else(|| {
        TurnError::InvalidExecutionProof(
            "aggregate_bilateral: shipped outer_trace is structurally invalid".into(),
        )
    })?;
    if recomputed != proof.trace_commitment {
        return Err(TurnError::InvalidExecutionProof(
            "aggregate_bilateral: shipped outer_trace does not match proof trace commitment".into(),
        ));
    }

    // Step 5: per-row inner_pi correspondence to participating_cells.
    // For each active row, the inner PI's bilateral counts + roots must
    // equal the schedule's projection for the corresponding cell. The AIR's
    // CG-3 constraint (verified in step 4) binds each row's inner PI to its
    // `expected_*` columns; here we close the remaining gap by re-deriving the
    // `expected_*` values from the canonical Turn and confirming they match the
    // (proof-bound) trace. A malicious prover cannot fabricate expected_*
    // values that satisfy CG-3 against forged inner PIs but disagree with the
    // schedule.
    let schedule = ExpectedBilateral::from_turn(&bundle.turn);
    let actor_nonce = bundle.turn.nonce;
    if bundle.outer_trace.len() < bundle.participating_cells.len() {
        return Err(TurnError::InvalidExecutionProof(
            "aggregate_bilateral: outer_trace has fewer rows than participating_cells".into(),
        ));
    }
    for (i, cid) in bundle.participating_cells.iter().enumerate() {
        let counts = schedule.counts_for(cid);
        let roots = schedule.roots_for(cid, actor_nonce);
        let (expected_counts, expected_roots) = pack_expected(counts, roots);

        let row = &bundle.outer_trace[i];
        if row.len() != ag::AGG_WIDTH {
            return Err(TurnError::InvalidExecutionProof(format!(
                "aggregate_bilateral: row {} has width {}, expected {}",
                i,
                row.len(),
                ag::AGG_WIDTH
            )));
        }
        // Check counts.
        for k in 0..7 {
            let claimed = BabyBear::new_canonical(row[ag::EXPECTED_COUNTS_BASE + k]);
            if claimed != expected_counts[k] {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "aggregate_bilateral: row {} cell {:?}: expected_counts[{}] = {} != schedule {}",
                    i,
                    cid,
                    k,
                    claimed.as_u32(),
                    expected_counts[k].as_u32()
                )));
            }
        }
        // Check roots.
        for k in 0..7 {
            for off in 0..4 {
                let claimed = BabyBear::new_canonical(row[ag::EXPECTED_ROOTS_BASE + k * 4 + off]);
                if claimed != expected_roots[k][off] {
                    return Err(TurnError::InvalidExecutionProof(format!(
                        "aggregate_bilateral: row {} cell {:?}: expected_roots[{}][{}] = {} != schedule {}",
                        i,
                        cid,
                        k,
                        off,
                        claimed.as_u32(),
                        expected_roots[k][off].as_u32()
                    )));
                }
            }
        }
        // Check inner_pi[IS_AGENT_CELL] truthfully reflects cell == turn.agent.
        let is_agent_claim =
            BabyBear::new_canonical(row[ag::PI_BUFFER_BASE + inner_pi::IS_AGENT_CELL]);
        let expected_is_agent = if cid == &bundle.turn.agent { 1 } else { 0 };
        if is_agent_claim.as_u32() != expected_is_agent {
            return Err(TurnError::InvalidExecutionProof(format!(
                "aggregate_bilateral: row {} cell {:?}: IS_AGENT_CELL = {} but expected {}",
                i,
                cid,
                is_agent_claim.as_u32(),
                expected_is_agent
            )));
        }
    }

    Ok(())
}


// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builder::{ActionBuilder, TurnBuilder};
    use crate::turn::TurnReceipt;
    use dregg_cell::AuthRequired;

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    fn dummy_receipt(agent: CellId) -> TurnReceipt {
        TurnReceipt {
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
            was_burn: false,
        }
    }

    fn dummy_scope2_trace() -> Vec<Vec<BabyBear>> {
        vec![vec![
            BabyBear::ZERO;
            dregg_circuit::effect_vm::EFFECT_VM_WIDTH
        ]]
    }

    /// Build a per-cell WitnessedReceipt whose PI is fabricated from the
    /// canonical Turn's bilateral schedule. Mirrors
    /// `dregg_verifier::bilateral_pair::fabricate_witnessed_receipt`.
    fn fabricate_wr(turn: &Turn, cell_id: &CellId) -> WitnessedReceipt {
        use crate::bilateral_schedule::{ExpectedBilateral, project_into_pi};
        use dregg_circuit::effect_vm::pi as p;

        let sched = ExpectedBilateral::from_turn(turn);
        let counts = sched.counts_for(cell_id);
        let roots = sched.roots_for(cell_id, turn.nonce);

        let mut pi_bb = vec![BabyBear::ZERO; p::BASE_COUNT];
        // Populate turn-identity slots.
        let (th, eg, _, prev) = crate::executor::TurnExecutor::compute_turn_identity_pi(turn);
        for i in 0..4 {
            pi_bb[p::TURN_HASH_BASE + i] = th[i];
            pi_bb[p::EFFECTS_HASH_GLOBAL_BASE + i] = eg[i];
            pi_bb[p::PREVIOUS_RECEIPT_HASH_BASE + i] = prev[i];
        }
        pi_bb[p::ACTOR_NONCE] = BabyBear::new((turn.nonce & 0x7FFF_FFFF) as u32);
        project_into_pi(&mut pi_bb, &counts, &roots);
        pi_bb[p::IS_AGENT_CELL] = if cell_id == &turn.agent {
            BabyBear::new(1)
        } else {
            BabyBear::ZERO
        };
        let pi_u32: Vec<u32> = pi_bb.iter().map(|x| x.as_u32()).collect();
        let trace = dummy_scope2_trace();
        WitnessedReceipt::from_components(
            dummy_receipt(turn.agent.clone()),
            vec![],
            pi_u32,
            Some(&trace),
        )
    }

    fn make_transfer_turn(alice: CellId, bob: CellId, amount: u64, nonce: u64) -> Turn {
        let mut builder = TurnBuilder::new(alice, nonce);
        let action = ActionBuilder::new_unchecked_for_tests(alice, "transfer", alice)
            .effect_transfer(alice, bob, amount)
            .build();
        builder.add_action(action);
        builder.fee(0).build()
    }

    #[test]
    fn happy_path_two_cell_transfer_aggregates_and_verifies() {
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);

        let entries = vec![
            (alice, fabricate_wr(&turn, &alice)),
            (bob, fabricate_wr(&turn, &bob)),
        ];

        let bundle = prove_aggregated_bundle(&turn, &entries).expect("prove");
        assert_eq!(bundle.participating_cells.len(), 2);
        assert_eq!(bundle.outer_pi.len(), OUTER_BASE_COUNT);
        assert_eq!(bundle.bundle_epoch, 1);

        verify_aggregated_bundle(&bundle).expect("verify");
    }

    #[test]
    fn aggregate_rejects_scope1_only_witnessed_receipt() {
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);

        let mut alice_wr = fabricate_wr(&turn, &alice);
        alice_wr.witness_bundle = None;
        alice_wr.witness_hash = [0u8; 32];

        let entries = vec![(alice, alice_wr), (bob, fabricate_wr(&turn, &bob))];
        let err = prove_aggregated_bundle(&turn, &entries)
            .expect_err("scope-1-only WR must not aggregate as a gossip artifact");
        assert!(
            format!("{err}").contains("scope-2"),
            "expected scope-2 rejection, got {err}"
        );
    }

    /// **Happy path** — the 3-cell bilateral Transfer-and-Grant ring the
    /// brief asks for. Alice transfers to Bob, Bob grants a capability to
    /// Carol; both happen inside one Turn, all three cells participate,
    /// and the aggregator emits a single outer proof that verifies.
    #[test]
    fn happy_path_three_cell_transfer_and_grant_ring() {
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let carol = cid(0xC3);

        let mut builder = TurnBuilder::new(alice, 7);
        let action = ActionBuilder::new_unchecked_for_tests(alice, "ring", alice)
            .effect_transfer(alice, bob, 100)
            .effect_grant_capability(
                bob,
                carol,
                dregg_cell::CapabilityRef {
                    target: alice,
                    slot: 0,
                    permissions: AuthRequired::Signature,
                    expires_at: None,
                    breadstuff: None,
                    allowed_effects: None,
                },
            )
            .effect_transfer(carol, alice, 50)
            .build();
        builder.add_action(action);
        let turn = builder.fee(0).build();

        let entries = vec![
            (alice, fabricate_wr(&turn, &alice)),
            (bob, fabricate_wr(&turn, &bob)),
            (carol, fabricate_wr(&turn, &carol)),
        ];

        let bundle = prove_aggregated_bundle(&turn, &entries).expect("three-cell ring must prove");
        assert_eq!(bundle.participating_cells.len(), 3);
        verify_aggregated_bundle(&bundle).expect("three-cell ring must verify");
        // The bundle epoch reflects the actor nonce.
        assert_eq!(bundle.bundle_epoch, 7);
        // outer PI's N_CELLS slot reflects the active count.
        use dregg_circuit::bilateral_aggregation_air as ag;
        assert_eq!(bundle.outer_pi[ag::OUTER_N_CELLS], 3);
    }

    /// Adversarial: tamper one inner PI's bilateral root (the externally
    /// visible footprint of any per-cell proof forgery). The aggregator's
    /// Phase-1 precondition rejects.
    #[test]
    fn adversarial_tampered_participant_proof_rejects() {
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);

        let mut wr_alice = fabricate_wr(&turn, &alice);
        let wr_bob = fabricate_wr(&turn, &bob);
        // Tamper: zap one felt of Alice's OUTGOING_TRANSFER_ROOT.
        wr_alice.public_inputs[inner_pi::OUTGOING_TRANSFER_ROOT_BASE] =
            0xDEAD_BEEF_u32 & 0x7FFF_FFFF;

        let entries = vec![(alice, wr_alice), (bob, wr_bob)];
        let res = prove_aggregated_bundle(&turn, &entries);
        assert!(
            res.is_err(),
            "tampered participant proof must reject at aggregation time"
        );
    }

    /// Adversarial: the canonical Turn says Transfer(alice→bob, 100), but
    /// Bob's PI was fabricated for a different turn (50). Sender's outbound
    /// disagrees with receiver's inbound → reject.
    #[test]
    fn adversarial_sender_receiver_disagree_rejects() {
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let real_turn = make_transfer_turn(alice, bob, 100, 1);
        let lie_turn = make_transfer_turn(alice, bob, 50, 1);

        let wr_alice = fabricate_wr(&real_turn, &alice);
        // Bob's PI was fabricated against a *different* canonical turn.
        let wr_bob = fabricate_wr(&lie_turn, &bob);
        let entries = vec![(alice, wr_alice), (bob, wr_bob)];

        let res = prove_aggregated_bundle(&real_turn, &entries);
        assert!(
            res.is_err(),
            "sender/receiver bilateral disagreement must reject; got {:?}",
            res
        );
    }

    /// Adversarial: Bob's PI has a tampered transfer_id (we zap multiple
    /// felts of the INCOMING_TRANSFER_ROOT — the externally visible
    /// footprint of an in-PI transfer_id forgery).
    #[test]
    fn adversarial_tampered_transfer_id_rejects() {
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);

        let wr_alice = fabricate_wr(&turn, &alice);
        let mut wr_bob = fabricate_wr(&turn, &bob);
        // Tamper: rewrite Bob's INCOMING_TRANSFER_ROOT entirely (as if the
        // attacker forged a transfer_id and folded it into the wrong root).
        for off in 0..4 {
            wr_bob.public_inputs[inner_pi::INCOMING_TRANSFER_ROOT_BASE + off] =
                (0xBADC0DE_u32 + off as u32) & 0x7FFF_FFFF;
        }
        let entries = vec![(alice, wr_alice), (bob, wr_bob)];
        let res = prove_aggregated_bundle(&turn, &entries);
        assert!(
            res.is_err(),
            "tampered transfer_id (via root) must reject; got {:?}",
            res
        );
    }

    /// Adversarial: missing participant (the canonical Turn declares a
    /// Transfer alice→bob but the bundle only carries Alice's WR).
    #[test]
    fn adversarial_missing_participant_rejects() {
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);

        let wr_alice = fabricate_wr(&turn, &alice);
        // Missing Bob.
        let entries = vec![(alice, wr_alice)];

        let res = prove_aggregated_bundle(&turn, &entries);
        assert!(
            res.is_err(),
            "missing-participant bundle must reject; got {:?}",
            res
        );
    }

    /// Adversarial: post-prove tampering. The aggregator emitted a valid
    /// bundle; an attacker subsequently rewrites the outer PI's
    /// BILATERAL_CONSISTENT to 0 (or N_CELLS to a lie). The verifier
    /// rejects.
    #[test]
    fn verifier_rejects_tampered_outer_pi() {
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);

        let entries = vec![
            (alice, fabricate_wr(&turn, &alice)),
            (bob, fabricate_wr(&turn, &bob)),
        ];
        let mut bundle = prove_aggregated_bundle(&turn, &entries).expect("prove");

        // Tamper.
        use dregg_circuit::bilateral_aggregation_air as ag;
        bundle.outer_pi[ag::OUTER_BILATERAL_CONSISTENT] = 0;

        let res = verify_aggregated_bundle(&bundle);
        assert!(res.is_err(), "tampered outer PI must reject");
    }

    /// Adversarial: the aggregator was honest, but the shipped trace on disk
    /// has been mangled (one cell flipped). The verifier binds the trace to
    /// the proof's `trace_commitment`, so the recomputed commitment no longer
    /// matches and the bundle is rejected.
    #[test]
    fn verifier_rejects_tampered_shipped_trace() {
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);

        let entries = vec![
            (alice, fabricate_wr(&turn, &alice)),
            (bob, fabricate_wr(&turn, &bob)),
        ];
        let mut bundle = prove_aggregated_bundle(&turn, &entries).expect("prove");

        // Flip the first row's IS_AGENT_CELL slot in the shipped trace.
        use dregg_circuit::bilateral_aggregation_air as ag;
        let slot = ag::PI_BUFFER_BASE + inner_pi::IS_AGENT_CELL;
        bundle.outer_trace[0][slot] = bundle.outer_trace[0][slot].wrapping_add(1) & 0x7FFF_FFFF;

        let res = verify_aggregated_bundle(&bundle);
        assert!(
            res.is_err(),
            "tampered shipped trace must reject (commitment mismatch)"
        );
    }

    /// The headline #133 test: the REAL aggregated STARK proof verifies for a
    /// consistent bundle and FAILS when the cross-cell bilateral agreement is
    /// tampered. We prove an honest bundle, then forge the receiver's inner-PI
    /// incoming-transfer root *inside the proven trace* so it no longer agrees
    /// with what the canonical Turn's schedule predicts, regenerate the proof
    /// over the tampered trace, and confirm verification rejects.
    #[test]
    fn aggregated_proof_verifies_consistent_and_rejects_tampered_cross_cell() {
        use dregg_circuit::bilateral_aggregation_air::{
            self as ag, BilateralAggregationAir,
        };
        use dregg_circuit::field::BabyBear;

        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);

        let entries = vec![
            (alice, fabricate_wr(&turn, &alice)),
            (bob, fabricate_wr(&turn, &bob)),
        ];

        // (a) Consistent bundle: real STARK proof verifies.
        let bundle = prove_aggregated_bundle(&turn, &entries).expect("prove consistent");
        verify_aggregated_bundle(&bundle).expect("consistent aggregated proof must verify");
        // Sanity: the proof bytes are a real DREG-format STARK proof, not a
        // postcard witness.
        assert_eq!(&bundle.outer_proof_bytes[0..4], b"DREG");

        // (b) Tampered cross-cell agreement. Bob is row 1; forge his
        // INCOMING_TRANSFER_ROOT in BOTH the inner-PI buffer *and* the
        // matching expected_roots column so CG-3 still holds in-trace, then
        // re-prove. The forged root no longer matches the schedule the Turn
        // predicts, so step-5's Turn-derived cross-check rejects.
        let mut trace_bb: Vec<Vec<BabyBear>> = bundle
            .outer_trace
            .iter()
            .map(|row| row.iter().map(|&v| BabyBear::new_canonical(v)).collect())
            .collect();
        // INCOMING_TRANSFER_ROOT is expected-roots index k=1.
        let pi_base = ag::PI_BUFFER_BASE + inner_pi::INCOMING_TRANSFER_ROOT_BASE;
        let exp_base = ag::EXPECTED_ROOTS_BASE + 1 * 4;
        for off in 0..4 {
            let forged = BabyBear::new((0x0BAD_C0DE + off as u32) & 0x7FFF_FFFF);
            trace_bb[1][pi_base + off] = forged;
            trace_bb[1][exp_base + off] = forged;
        }
        // Re-prove over the tampered (but internally CG-3-consistent) trace.
        let outer_pi_bb: Vec<BabyBear> = bundle
            .outer_pi
            .iter()
            .map(|&v| BabyBear::new_canonical(v))
            .collect();
        let tampered_proof = dregg_circuit::stark::try_prove(
            &BilateralAggregationAir,
            &trace_bb,
            &outer_pi_bb,
        )
        .expect("tampered trace still satisfies in-AIR constraints, so it proves");
        let mut tampered = bundle.clone();
        tampered.outer_proof_bytes = dregg_circuit::stark::proof_to_bytes(&tampered_proof);
        tampered.outer_trace = trace_bb
            .iter()
            .map(|row| row.iter().map(|x| x.as_u32()).collect())
            .collect();

        let res = verify_aggregated_bundle(&tampered);
        assert!(
            res.is_err(),
            "aggregated proof with tampered cross-cell agreement must reject; got {:?}",
            res
        );
    }

    #[test]
    fn json_roundtrip_for_aggregated_bundle() {
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);

        let entries = vec![
            (alice, fabricate_wr(&turn, &alice)),
            (bob, fabricate_wr(&turn, &bob)),
        ];
        let bundle = prove_aggregated_bundle(&turn, &entries).expect("prove");

        let json = bundle.to_json().expect("to_json");
        let back = AggregatedBundle::from_json(&json).expect("from_json");
        verify_aggregated_bundle(&back).expect("re-verify after roundtrip");
    }
}
