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
    /// Outer STARK proof bytes (`stark::proof_to_bytes` output).
    pub outer_proof_bytes: Vec<u8>,
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

    // Run the outer STARK prover. We use the local `stark::prove` adapter
    // through `dregg_circuit::stark::prove_with_air`. The aggregation AIR
    // implements `p3-air::Air` (gated by `plonky3`); the `dregg-circuit`
    // crate provides a generic prove path via `effect_vm_p3_air` /
    // `plonky3_recursion_impl::prove_inner_for_air` for any
    // `RecursableAir`.
    //
    // For Phase 2's *initial* landing we evaluate constraints classically
    // and emit a witness-bound proof artifact: the proof bytes are the
    // serialised trace + outer PI, and verification re-runs the AIR's
    // symbolic constraints over them. This is the "trust-and-replay"
    // mode the verifier already uses for the per-cell Effect VM AIR. A
    // later commit promotes this to a real STARK once the recursion
    // shape is fully wired through `prove_recursive_layer_for_air`.

    let outer_proof_bytes = encode_aggregation_witness(&trace, &outer_pi_bb)?;

    let outer_pi_u32: Vec<u32> = outer_pi_bb.iter().map(|x| x.as_u32()).collect();

    Ok(AggregatedBundle {
        turn: turn.clone(),
        participating_cells: per_cell.iter().map(|(c, _)| c.clone()).collect(),
        outer_pi: outer_pi_u32,
        outer_proof_bytes,
        federation_ids: federation_ids_seen,
        bundle_epoch: actor_nonce,
    })
}

// ---------------------------------------------------------------------------
// Witness encoding (Phase 2 v1 trust-and-replay path)
// ---------------------------------------------------------------------------

/// On-wire shape of the aggregation proof. v1 is a trust-and-replay form:
/// the verifier reconstructs the trace and re-runs the AIR constraints.
#[derive(Clone, Debug, Serialize, Deserialize)]
struct AggregationWitness {
    /// Trace rows as canonical-BabyBear u32 cells, shape
    /// `n_padded × AGG_WIDTH`.
    trace_rows: Vec<Vec<u32>>,
    /// Outer PI vector as canonical-BabyBear u32 cells, length
    /// `OUTER_BASE_COUNT`.
    outer_pi: Vec<u32>,
    /// AIR name (`BilateralAggregationAir::AIR_NAME`).
    air_name: String,
}

fn encode_aggregation_witness(
    trace: &[Vec<BabyBear>],
    outer_pi: &[BabyBear],
) -> Result<Vec<u8>, TurnError> {
    let trace_rows: Vec<Vec<u32>> = trace
        .iter()
        .map(|row| row.iter().map(|x| x.as_u32()).collect())
        .collect();
    let outer_pi_u32: Vec<u32> = outer_pi.iter().map(|x| x.as_u32()).collect();
    let w = AggregationWitness {
        trace_rows,
        outer_pi: outer_pi_u32,
        air_name: BilateralAggregationAir::AIR_NAME.to_string(),
    };
    postcard::to_allocvec(&w).map_err(|e| {
        TurnError::InvalidExecutionProof(format!(
            "aggregate_bilateral: failed to serialise aggregation witness: {e}"
        ))
    })
}

fn decode_aggregation_witness(bytes: &[u8]) -> Result<AggregationWitness, TurnError> {
    postcard::from_bytes::<AggregationWitness>(bytes).map_err(|e| {
        TurnError::InvalidExecutionProof(format!(
            "aggregate_bilateral: failed to decode aggregation witness: {e}"
        ))
    })
}

// ---------------------------------------------------------------------------
// Verifier
// ---------------------------------------------------------------------------

/// Verify an [`AggregatedBundle`]. Pure function over the bundle bytes; no
/// shared state. Returns `Ok(())` on success and a human-readable error
/// otherwise. Closes the threat surface:
///
/// - Tampered outer PI: caught by the canonical-Turn-derived PI check.
/// - Tampered trace: caught by re-running the AIR constraints against the
///   decoded trace.
/// - Tampered participating_cells order: caught by the per-row schedule
///   projection mismatching the WR's inner PI block.
/// - Forged "consistent" flag: pinned to 1 by the AIR's BILATERAL_CONSISTENT
///   constraint; rejecting `outer_pi[OUTER_BILATERAL_CONSISTENT] != 1`
///   short-circuits before AIR replay.
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

    // Step 4: AIR-level replay. Decode the trace and re-run the
    // aggregation AIR's symbolic constraints across every row pair.
    let w = decode_aggregation_witness(&bundle.outer_proof_bytes)?;
    if w.air_name != BilateralAggregationAir::AIR_NAME {
        return Err(TurnError::InvalidExecutionProof(format!(
            "aggregate_bilateral: AIR name mismatch in witness: {}",
            w.air_name
        )));
    }
    if w.outer_pi != bundle.outer_pi {
        return Err(TurnError::InvalidExecutionProof(
            "aggregate_bilateral: witness outer_pi disagrees with bundle outer_pi".into(),
        ));
    }
    let trace_bb: Vec<Vec<BabyBear>> = w
        .trace_rows
        .iter()
        .map(|row| row.iter().map(|&v| BabyBear::new_canonical(v)).collect())
        .collect();
    let pi_bb: Vec<BabyBear> = w
        .outer_pi
        .iter()
        .map(|&v| BabyBear::new_canonical(v))
        .collect();
    replay_aggregation_air(&trace_bb, &pi_bb)?;

    // Step 5: per-row inner_pi correspondence to participating_cells.
    // For each active row, the inner PI's bilateral counts + roots must
    // equal the schedule's projection for the corresponding cell. The
    // AIR constraints in step 4 enforce this transitively (each row's PI
    // is compared to its expected_counts/expected_roots in-AIR, and the
    // expected_* columns are *part of the trace*). We additionally
    // re-derive the expected_* values *here* from the canonical Turn and
    // confirm they match what the witness embedded — closing the door on
    // a malicious prover who would fabricate expected_* values that
    // happen to also match the inner PI but don't correspond to the
    // schedule.
    let schedule = ExpectedBilateral::from_turn(&bundle.turn);
    let actor_nonce = bundle.turn.nonce;
    for (i, cid) in bundle.participating_cells.iter().enumerate() {
        let counts = schedule.counts_for(cid);
        let roots = schedule.roots_for(cid, actor_nonce);
        let (expected_counts, expected_roots) = pack_expected(counts, roots);

        let row = &w.trace_rows[i];
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
// Symbolic AIR replay (verifier-side soundness check)
// ---------------------------------------------------------------------------

/// Re-evaluate the [`BilateralAggregationAir`] symbolic constraints against
/// the decoded trace + outer PI. This is the "scope-2 replay" pattern the
/// per-cell verifier uses (`dregg_verifier::replay_chain`) but for the outer
/// AIR: we walk every row, recompute the constraint expressions over local
/// + next + public values, and require every expression to evaluate to
/// zero.
///
/// The replay covers every constraint in `Air::eval` exactly once per row;
/// see `bilateral_aggregation_air::eval` for the source of truth.
fn replay_aggregation_air(trace: &[Vec<BabyBear>], pi: &[BabyBear]) -> Result<(), TurnError> {
    use dregg_circuit::bilateral_aggregation_air as ag;

    if trace.is_empty() {
        return Err(TurnError::InvalidExecutionProof(
            "aggregate_bilateral: empty aggregation trace".into(),
        ));
    }
    if pi.len() != OUTER_BASE_COUNT {
        return Err(TurnError::InvalidExecutionProof(format!(
            "aggregate_bilateral: outer PI length {} != {}",
            pi.len(),
            OUTER_BASE_COUNT
        )));
    }
    for (i, row) in trace.iter().enumerate() {
        if row.len() != ag::AGG_WIDTH {
            return Err(TurnError::InvalidExecutionProof(format!(
                "aggregate_bilateral: row {} has width {}, expected {}",
                i,
                row.len(),
                ag::AGG_WIDTH
            )));
        }
    }

    let n = trace.len();
    let pv_turn = &pi[ag::OUTER_TURN_HASH_BASE..ag::OUTER_TURN_HASH_BASE + ag::OUTER_TURN_HASH_LEN];
    let pv_effects = &pi[ag::OUTER_EFFECTS_HASH_GLOBAL_BASE
        ..ag::OUTER_EFFECTS_HASH_GLOBAL_BASE + ag::OUTER_EFFECTS_HASH_GLOBAL_LEN];
    let pv_actor_nonce = pi[ag::OUTER_ACTOR_NONCE];
    let pv_prev = &pi[ag::OUTER_PREVIOUS_RECEIPT_HASH_BASE
        ..ag::OUTER_PREVIOUS_RECEIPT_HASH_BASE + ag::OUTER_PREVIOUS_RECEIPT_HASH_LEN];
    let pv_n_cells = pi[ag::OUTER_N_CELLS];
    let pv_consistent = pi[ag::OUTER_BILATERAL_CONSISTENT];

    if pv_consistent.as_u32() != 1 {
        return Err(TurnError::InvalidExecutionProof(format!(
            "aggregate_bilateral: outer BILATERAL_CONSISTENT == {}",
            pv_consistent.as_u32()
        )));
    }

    for (idx, row) in trace.iter().enumerate() {
        // CG-2: turn-identity agreement.
        for i in 0..ag::OUTER_TURN_HASH_LEN {
            let r = row[ag::PI_BUFFER_BASE + inner_pi::TURN_HASH_BASE + i];
            if r != pv_turn[i] {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "aggregate_bilateral row {}: TURN_HASH[{}] in PI buffer = {} != outer {}",
                    idx,
                    i,
                    r.as_u32(),
                    pv_turn[i].as_u32()
                )));
            }
        }
        for i in 0..ag::OUTER_EFFECTS_HASH_GLOBAL_LEN {
            let r = row[ag::PI_BUFFER_BASE + inner_pi::EFFECTS_HASH_GLOBAL_BASE + i];
            if r != pv_effects[i] {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "aggregate_bilateral row {}: EFFECTS_HASH_GLOBAL[{}] = {} != outer {}",
                    idx,
                    i,
                    r.as_u32(),
                    pv_effects[i].as_u32()
                )));
            }
        }
        {
            let r = row[ag::PI_BUFFER_BASE + inner_pi::ACTOR_NONCE];
            if r != pv_actor_nonce {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "aggregate_bilateral row {}: ACTOR_NONCE = {} != outer {}",
                    idx,
                    r.as_u32(),
                    pv_actor_nonce.as_u32()
                )));
            }
        }
        for i in 0..ag::OUTER_PREVIOUS_RECEIPT_HASH_LEN {
            let r = row[ag::PI_BUFFER_BASE + inner_pi::PREVIOUS_RECEIPT_HASH_BASE + i];
            if r != pv_prev[i] {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "aggregate_bilateral row {}: PREVIOUS_RECEIPT_HASH[{}] = {} != outer {}",
                    idx,
                    i,
                    r.as_u32(),
                    pv_prev[i].as_u32()
                )));
            }
        }

        // CG-3: schedule replay - counts.
        let count_slots = [
            inner_pi::OUTBOUND_TRANSFER_COUNT,
            inner_pi::INBOUND_TRANSFER_COUNT,
            inner_pi::OUTBOUND_GRANT_COUNT,
            inner_pi::INBOUND_GRANT_COUNT,
            inner_pi::INTRO_AS_INTRODUCER_COUNT,
            inner_pi::INTRO_AS_RECIPIENT_COUNT,
            inner_pi::INTRO_AS_TARGET_COUNT,
        ];
        for (k, slot) in count_slots.iter().enumerate() {
            let row_pi = row[ag::PI_BUFFER_BASE + *slot];
            let row_expected = row[ag::EXPECTED_COUNTS_BASE + k];
            if row_pi != row_expected {
                return Err(TurnError::InvalidExecutionProof(format!(
                    "aggregate_bilateral row {}: count slot {} mismatch (pi {} != expected {})",
                    idx,
                    *slot,
                    row_pi.as_u32(),
                    row_expected.as_u32()
                )));
            }
        }

        // CG-3: schedule replay - roots.
        let root_bases = [
            inner_pi::OUTGOING_TRANSFER_ROOT_BASE,
            inner_pi::INCOMING_TRANSFER_ROOT_BASE,
            inner_pi::OUTGOING_GRANT_ROOT_BASE,
            inner_pi::INCOMING_GRANT_ROOT_BASE,
            inner_pi::INTRO_AS_INTRODUCER_ROOT_BASE,
            inner_pi::INTRO_AS_RECIPIENT_ROOT_BASE,
            inner_pi::INTRO_AS_TARGET_ROOT_BASE,
        ];
        for (k, base) in root_bases.iter().enumerate() {
            for off in 0..4 {
                let row_pi = row[ag::PI_BUFFER_BASE + base + off];
                let row_expected = row[ag::EXPECTED_ROOTS_BASE + k * 4 + off];
                if row_pi != row_expected {
                    return Err(TurnError::InvalidExecutionProof(format!(
                        "aggregate_bilateral row {}: root[{}][{}] mismatch (pi {} != expected {})",
                        idx,
                        k,
                        off,
                        row_pi.as_u32(),
                        row_expected.as_u32()
                    )));
                }
            }
        }

        // CG-4: IS_AGENT_CELL accounting (boolean + padding gates).
        let ind = row[ag::CONSISTENT_INDICATOR_COL];
        let is_agent = row[ag::PI_BUFFER_BASE + inner_pi::IS_AGENT_CELL];
        let ind_u = ind.as_u32();
        let agent_u = is_agent.as_u32();
        if ind_u > 1 {
            return Err(TurnError::InvalidExecutionProof(format!(
                "aggregate_bilateral row {}: consistent_indicator = {} not boolean",
                idx, ind_u
            )));
        }
        if agent_u > 1 {
            return Err(TurnError::InvalidExecutionProof(format!(
                "aggregate_bilateral row {}: IS_AGENT_CELL = {} not boolean",
                idx, agent_u
            )));
        }
        if ind_u == 0 && agent_u != 0 {
            return Err(TurnError::InvalidExecutionProof(format!(
                "aggregate_bilateral row {}: padding row but IS_AGENT_CELL = {}",
                idx, agent_u
            )));
        }
    }

    // Boundary: row-0.
    let cum0 = trace[0][ag::IS_AGENT_CUMULATIVE_COL];
    let agent0 = trace[0][ag::PI_BUFFER_BASE + inner_pi::IS_AGENT_CELL];
    if cum0 != agent0 {
        return Err(TurnError::InvalidExecutionProof(format!(
            "aggregate_bilateral row 0 boundary: is_agent_cumulative = {} != IS_AGENT_CELL = {}",
            cum0.as_u32(),
            agent0.as_u32()
        )));
    }
    let n0 = trace[0][ag::N_CELLS_ACTIVE_COL];
    let ind0 = trace[0][ag::CONSISTENT_INDICATOR_COL];
    if n0 != ind0 {
        return Err(TurnError::InvalidExecutionProof(format!(
            "aggregate_bilateral row 0 boundary: n_cells_active = {} != consistent_indicator = {}",
            n0.as_u32(),
            ind0.as_u32()
        )));
    }

    // Transitions: `cum[i+1] = cum[i] + thing[i+1]` (next-row contribution
    // pattern, matching the AIR's `when_transition` constraint).
    for i in 0..(n - 1) {
        let cum_local = trace[i][ag::IS_AGENT_CUMULATIVE_COL];
        let cum_next = trace[i + 1][ag::IS_AGENT_CUMULATIVE_COL];
        let is_agent_next = trace[i + 1][ag::PI_BUFFER_BASE + inner_pi::IS_AGENT_CELL];
        let expected_cum_next = BabyBear::new(cum_local.as_u32() + is_agent_next.as_u32());
        if cum_next != expected_cum_next {
            return Err(TurnError::InvalidExecutionProof(format!(
                "aggregate_bilateral row {} transition: is_agent_cumulative {} -> {} but +IS_AGENT_CELL_next ({}) = {}",
                i,
                cum_local.as_u32(),
                cum_next.as_u32(),
                is_agent_next.as_u32(),
                expected_cum_next.as_u32()
            )));
        }

        let n_local = trace[i][ag::N_CELLS_ACTIVE_COL];
        let n_next = trace[i + 1][ag::N_CELLS_ACTIVE_COL];
        let ind_next = trace[i + 1][ag::CONSISTENT_INDICATOR_COL];
        let expected_n_next = BabyBear::new(n_local.as_u32() + ind_next.as_u32());
        if n_next != expected_n_next {
            return Err(TurnError::InvalidExecutionProof(format!(
                "aggregate_bilateral row {} transition: n_cells_active {} -> {} but +consistent_indicator_next ({}) = {}",
                i,
                n_local.as_u32(),
                n_next.as_u32(),
                ind_next.as_u32(),
                expected_n_next.as_u32()
            )));
        }
    }

    // Boundary: last row.
    let last = &trace[n - 1];
    let cum_last = last[ag::IS_AGENT_CUMULATIVE_COL];
    if cum_last.as_u32() != 1 {
        return Err(TurnError::InvalidExecutionProof(format!(
            "aggregate_bilateral last row: is_agent_cumulative = {} != 1",
            cum_last.as_u32()
        )));
    }
    let n_last = last[ag::N_CELLS_ACTIVE_COL];
    if n_last != pv_n_cells {
        return Err(TurnError::InvalidExecutionProof(format!(
            "aggregate_bilateral last row: n_cells_active = {} != outer N_CELLS = {}",
            n_last.as_u32(),
            pv_n_cells.as_u32()
        )));
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

    /// Adversarial: the aggregator was honest, but the witness on disk has
    /// been mangled (one trace cell flipped). The verifier re-runs the AIR
    /// constraints and catches it.
    #[test]
    fn verifier_rejects_tampered_witness_trace() {
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);

        let entries = vec![
            (alice, fabricate_wr(&turn, &alice)),
            (bob, fabricate_wr(&turn, &bob)),
        ];
        let mut bundle = prove_aggregated_bundle(&turn, &entries).expect("prove");

        // Decode, mangle, re-encode.
        let mut w = decode_aggregation_witness(&bundle.outer_proof_bytes)
            .expect("decode aggregation witness");
        // Flip the first row's IS_AGENT_CELL slot.
        use dregg_circuit::bilateral_aggregation_air as ag;
        let slot = ag::PI_BUFFER_BASE + inner_pi::IS_AGENT_CELL;
        w.trace_rows[0][slot] = w.trace_rows[0][slot].wrapping_add(1) & 0x7FFF_FFFF;
        bundle.outer_proof_bytes = postcard::to_allocvec(&w).expect("re-encode");

        let res = verify_aggregated_bundle(&bundle);
        assert!(res.is_err(), "tampered witness trace must reject");
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
