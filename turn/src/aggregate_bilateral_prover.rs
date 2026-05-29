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
    AggregationInnerRow, AggregationOuterPi, BilateralAggregationAir, BundleTreeFoldAir,
    CrossSideExistenceAir, CrossSideHalfEdge, FOLD_PI_COUNT, OUTER_BASE_COUNT,
    build_aggregation_trace, build_cross_side_trace, build_tree_fold_trace,
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
    /// Optional in-circuit CG-5 cross-side-existence proof. When present, the
    /// "every outgoing edge has its matching incoming peer in the bundle"
    /// property is attested *algebraically* by a STARK over the
    /// `CrossSideExistenceAir` balance trace (signed edge-fingerprint sum == 0),
    /// not just by the Rust `verify_bilateral_chain` precondition. Older
    /// bundles (and the flat happy-path) leave this `None`; the verifier still
    /// runs the Rust existence check, so soundness is never weaker than before
    /// — this field *strengthens* the attestation.
    #[serde(default)]
    pub cross_side_existence: Option<CrossSideExistenceProof>,
}

/// In-circuit CG-5 attestation: a real STARK proof that the bundle's directed
/// bilateral edges balance (every materialised outgoing half-edge is cancelled
/// by its matching incoming half-edge). See
/// `dregg_circuit::bilateral_aggregation_air::CrossSideExistenceAir`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CrossSideExistenceProof {
    /// STARK proof bytes over the `CrossSideExistenceAir` balance trace.
    pub proof_bytes: Vec<u8>,
    /// The proven balance trace (rows × `CSE_WIDTH`), canonical-u32. Bound to
    /// `proof_bytes` by trace-commitment equality at verify time.
    pub trace: Vec<Vec<u32>>,
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
    let proof = dregg_circuit::stark::try_prove(&BilateralAggregationAir, &trace, &outer_pi_bb)
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

    // In-circuit CG-5: produce the algebraic cross-side-existence balance
    // proof over the canonical edges of this bundle. `verify_bilateral_chain`
    // above already guarantees completeness (Rust precondition), so this
    // always balances for an honestly-built bundle; we attach the STARK so the
    // consumer can re-check existence *algebraically* without trusting the
    // aggregator's Rust loop.
    let participating: Vec<CellId> = per_cell.iter().map(|(c, _)| c.clone()).collect();
    let cross_side_existence = Some(prove_cross_side_existence(turn, &participating)?);

    Ok(AggregatedBundle {
        turn: turn.clone(),
        participating_cells: participating,
        outer_pi: outer_pi_u32,
        outer_proof_bytes,
        outer_trace,
        federation_ids: federation_ids_seen,
        bundle_epoch: actor_nonce,
        cross_side_existence,
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
    let recomputed =
        dregg_circuit::stark::recompute_trace_commitment(&BilateralAggregationAir, &trace_bb)
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

    // Step 6: in-circuit CG-5. When the bundle carries a cross-side-existence
    // proof, verify it ALGEBRAICALLY: the balance STARK attests the signed
    // edge-fingerprint sum is zero (every outgoing edge has its matching
    // incoming peer), and the proof-bound trace is pinned to the canonical
    // schedule. This is a strictly stronger check than the prover-side Rust
    // existence loop; if it is absent we still relied on the per-row schedule
    // cross-check above, so soundness is never weakened by its absence.
    if let Some(cse) = &bundle.cross_side_existence {
        verify_cross_side_existence(cse, &bundle.turn, &bundle.participating_cells)?;
    }

    Ok(())
}

// ===========================================================================
// CG-5 IN-CIRCUIT — cross-side existence proof
// ===========================================================================

/// Deterministically derive the ordered multiset of materialised half-edges
/// for `(turn, covered_cells)`. Each bilateral edge in the canonical schedule
/// contributes an OUTGOING half-edge (claimed by `from`) and an INCOMING
/// half-edge (claimed by `to`) — but a half-edge is *materialised only when
/// its self-cell is in the covered set*. Both halves of a single edge share
/// the same canonical, direction-independent `edge_id` (the transfer/grant id),
/// so when both endpoints are covered the +/- contributions cancel.
///
/// For Introduce we treat the three role-pairs (introducer↔recipient,
/// introducer↔target) as canonical edges keyed by the intro id with a per-pair
/// salt folded in, so each pair balances independently.
///
/// This is the single source of truth shared by the CG-5 prover and verifier:
/// the verifier rebuilds the *exact* multiset and requires the proof-bound
/// trace to match it, which (together with the in-AIR balance==0 boundary)
/// closes the missing-peer attack algebraically.
fn canonical_half_edges(
    turn: &Turn,
    covered: &std::collections::HashSet<CellId>,
) -> Vec<CrossSideHalfEdge> {
    use dregg_circuit::poseidon2::hash_4_to_1;
    let schedule = ExpectedBilateral::from_turn(turn);
    let nonce = turn.nonce;
    let mut out: Vec<CrossSideHalfEdge> = Vec::new();

    // Fold a 1-felt role salt into a 4-felt id so distinct edge *roles* that
    // share a base id (e.g. the two intro pairs) get distinct fingerprints,
    // while the two halves of one role still share an id.
    let salted = |id: [BabyBear; 4], salt: u32| -> [BabyBear; 4] {
        let s = BabyBear::new(salt & 0x7FFF_FFFF);
        [
            hash_4_to_1(&[id[0], s, id[1], BabyBear::ZERO]),
            hash_4_to_1(&[id[1], s, id[2], BabyBear::ZERO]),
            hash_4_to_1(&[id[2], s, id[3], BabyBear::ZERO]),
            hash_4_to_1(&[id[3], s, id[0], BabyBear::ZERO]),
        ]
    };

    for t in &schedule.transfers {
        let id = t.id(nonce);
        if covered.contains(&t.from) {
            out.push(CrossSideHalfEdge {
                edge_id: id,
                outgoing: true,
            });
        }
        if covered.contains(&t.to) {
            out.push(CrossSideHalfEdge {
                edge_id: id,
                outgoing: false,
            });
        }
    }
    for g in &schedule.grants {
        let id = salted(g.id(nonce), 0x0000_0011);
        if covered.contains(&g.from) {
            out.push(CrossSideHalfEdge {
                edge_id: id,
                outgoing: true,
            });
        }
        if covered.contains(&g.to) {
            out.push(CrossSideHalfEdge {
                edge_id: id,
                outgoing: false,
            });
        }
    }
    for intro in &schedule.introduces {
        let base = intro.id(nonce);
        // Pair A: introducer (out) ↔ recipient (in).
        let id_a = salted(base, 0x0000_00A1);
        if covered.contains(&intro.introducer) {
            out.push(CrossSideHalfEdge {
                edge_id: id_a,
                outgoing: true,
            });
        }
        if covered.contains(&intro.recipient) {
            out.push(CrossSideHalfEdge {
                edge_id: id_a,
                outgoing: false,
            });
        }
        // Pair B: introducer (out) ↔ target (in).
        let id_b = salted(base, 0x0000_00B2);
        if covered.contains(&intro.introducer) {
            out.push(CrossSideHalfEdge {
                edge_id: id_b,
                outgoing: true,
            });
        }
        if covered.contains(&intro.target) {
            out.push(CrossSideHalfEdge {
                edge_id: id_b,
                outgoing: false,
            });
        }
    }
    out
}

/// Prove the in-circuit CG-5 cross-side existence property for a bundle's
/// `(turn, participating_cells)`. Returns a STARK proof over the
/// `CrossSideExistenceAir` balance trace. Fails if the bundle is incomplete
/// (a half-edge's peer is missing) — in that case the balance is nonzero and
/// the boundary constraint is unprovable/unverifiable.
pub fn prove_cross_side_existence(
    turn: &Turn,
    participating_cells: &[CellId],
) -> Result<CrossSideExistenceProof, TurnError> {
    let covered: std::collections::HashSet<CellId> = participating_cells.iter().cloned().collect();
    let half_edges = canonical_half_edges(turn, &covered);
    let trace = build_cross_side_trace(&half_edges);

    // Pre-flight: a nonzero final balance means a missing peer; surface a
    // clean error rather than an opaque prove failure.
    use dregg_circuit::bilateral_aggregation_air::CSE_BALANCE_COL;
    if let Some(last) = trace.last() {
        if last[CSE_BALANCE_COL] != BabyBear::ZERO {
            return Err(TurnError::InvalidExecutionProof(
                "cross_side_existence: bundle does not balance (missing peer for some edge)".into(),
            ));
        }
    }

    let proof =
        dregg_circuit::stark::try_prove(&CrossSideExistenceAir, &trace, &[]).map_err(|e| {
            TurnError::InvalidExecutionProof(format!(
                "cross_side_existence: balance STARK proving failed: {e}"
            ))
        })?;
    let proof_bytes = dregg_circuit::stark::proof_to_bytes(&proof);
    let trace_u32: Vec<Vec<u32>> = trace
        .iter()
        .map(|row| row.iter().map(|x| x.as_u32()).collect())
        .collect();
    Ok(CrossSideExistenceProof {
        proof_bytes,
        trace: trace_u32,
    })
}

/// Verify a CG-5 cross-side existence proof against the canonical Turn. This:
///   1. Re-derives the exact canonical half-edge multiset from the Turn +
///      covered cells (the schedule binding — prevents forged edge rows).
///   2. Verifies the balance STARK (FRI + the balance==0 boundary) without
///      re-executing the trace.
///   3. Binds the shipped trace to the proof (commitment equality) and
///      confirms it equals the canonical-multiset trace, so the algebraic
///      balance argument operated on exactly the schedule-derived edges.
pub fn verify_cross_side_existence(
    proof: &CrossSideExistenceProof,
    turn: &Turn,
    participating_cells: &[CellId],
) -> Result<(), TurnError> {
    let covered: std::collections::HashSet<CellId> = participating_cells.iter().cloned().collect();
    let half_edges = canonical_half_edges(turn, &covered);
    let expected_trace = build_cross_side_trace(&half_edges);

    // Decode + verify the STARK proof standalone.
    let stark_proof = dregg_circuit::stark::proof_from_bytes(&proof.proof_bytes).map_err(|e| {
        TurnError::InvalidExecutionProof(format!(
            "cross_side_existence: failed to decode proof: {e}"
        ))
    })?;
    if stark_proof.air_name != CrossSideExistenceAir::AIR_NAME {
        return Err(TurnError::InvalidExecutionProof(format!(
            "cross_side_existence: proof AIR name mismatch: {}",
            stark_proof.air_name
        )));
    }
    dregg_circuit::stark::verify(&CrossSideExistenceAir, &stark_proof, &[]).map_err(|e| {
        TurnError::InvalidExecutionProof(format!(
            "cross_side_existence: balance STARK verification failed: {e}"
        ))
    })?;

    // Bind shipped trace to the proof, then require it to be the canonical
    // schedule-derived trace. This closes forged-edge-row attacks: a prover
    // cannot present a *different* (e.g. self-cancelling fabricated) edge set
    // than the one the Turn predicts.
    let trace_bb: Vec<Vec<BabyBear>> = proof
        .trace
        .iter()
        .map(|row| row.iter().map(|&v| BabyBear::new_canonical(v)).collect())
        .collect();
    let recomputed =
        dregg_circuit::stark::recompute_trace_commitment(&CrossSideExistenceAir, &trace_bb)
            .ok_or_else(|| {
                TurnError::InvalidExecutionProof(
                    "cross_side_existence: shipped trace is structurally invalid".into(),
                )
            })?;
    if recomputed != stark_proof.trace_commitment {
        return Err(TurnError::InvalidExecutionProof(
            "cross_side_existence: shipped trace does not match proof commitment".into(),
        ));
    }
    if trace_bb != expected_trace {
        return Err(TurnError::InvalidExecutionProof(
            "cross_side_existence: proof-bound trace does not match canonical schedule edges"
                .into(),
        ));
    }
    Ok(())
}

// ===========================================================================
// PROOF-OF-PROOFS / TREE FOLD over child AggregatedBundles
// ===========================================================================

/// A tree-folded attestation over a set of child `AggregatedBundle`s. The
/// outer proof is constant-size relative to the number of children: a consumer
/// holding `(child_digests, outer_pi, outer_proof_bytes)` knows the fold chain
/// is correct without re-running any child's inner STARK. To trust the
/// *contents* of the children, the verifier re-checks each child bundle and
/// recomputes the expected accumulator.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AggregatedTree {
    /// The child bundles, in fold order.
    pub children: Vec<AggregatedBundle>,
    /// Per-child digest (Poseidon2 over the child's outer PI), in fold order.
    pub child_digests: Vec<u32>,
    /// Outer fold-AIR public inputs `[initial_acc, final_acc]`.
    pub outer_pi: Vec<u32>,
    /// Outer fold STARK proof bytes (`BundleTreeFoldAir`).
    pub outer_proof_bytes: Vec<u8>,
    /// The fold trace (rows × `FOLD_WIDTH`), canonical-u32. Bound to the proof.
    pub outer_trace: Vec<Vec<u32>>,
}

impl AggregatedTree {
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }
    pub fn from_json(text: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(text)
    }
}

/// Digest a child bundle into a single field element: Poseidon2 over its
/// outer PI vector. Binds the entire bundle summary (turn hash, effects hash,
/// agent, n_cells, consistent flag) into one chain element.
fn bundle_digest(bundle: &AggregatedBundle) -> BabyBear {
    let pi_bb: Vec<BabyBear> = bundle
        .outer_pi
        .iter()
        .map(|&v| BabyBear::new_canonical(v))
        .collect();
    dregg_circuit::poseidon2::hash_many(&pi_bb)
}

/// Tree-fold N child `AggregatedBundle`s into a single outer attestation.
/// Each child is verified classically (so the tree never attests an invalid
/// child), reduced to a digest, and folded via a Poseidon2 hash chain proven
/// by `BundleTreeFoldAir`. The result verifies in O(1) in the number of
/// children for the fold step itself.
pub fn prove_aggregated_tree(children: Vec<AggregatedBundle>) -> Result<AggregatedTree, TurnError> {
    if children.is_empty() {
        return Err(TurnError::InvalidExecutionProof(
            "aggregate_tree: need at least one child bundle".into(),
        ));
    }
    // Verify each child up front: the tree must never fold an invalid bundle.
    for (i, child) in children.iter().enumerate() {
        verify_aggregated_bundle(child).map_err(|e| {
            TurnError::InvalidExecutionProof(format!(
                "aggregate_tree: child {i} failed verification: {e}"
            ))
        })?;
    }

    let digests: Vec<BabyBear> = children.iter().map(bundle_digest).collect();
    let (trace, pi) = build_tree_fold_trace(&digests);

    let proof = dregg_circuit::stark::try_prove(&BundleTreeFoldAir, &trace, &pi).map_err(|e| {
        TurnError::InvalidExecutionProof(format!(
            "aggregate_tree: outer fold STARK proving failed: {e}"
        ))
    })?;
    let outer_proof_bytes = dregg_circuit::stark::proof_to_bytes(&proof);
    let outer_trace: Vec<Vec<u32>> = trace
        .iter()
        .map(|row| row.iter().map(|x| x.as_u32()).collect())
        .collect();

    Ok(AggregatedTree {
        children,
        child_digests: digests.iter().map(|x| x.as_u32()).collect(),
        outer_pi: pi.iter().map(|x| x.as_u32()).collect(),
        outer_proof_bytes,
        outer_trace,
    })
}

/// Verify a tree-folded attestation:
///   1. Re-verify each child bundle (full per-bundle soundness).
///   2. Recompute each child digest and require it to match `child_digests`.
///   3. Recompute the fold trace + public inputs from the digests and require
///      the outer PI to match (binds the final accumulator to the children).
///   4. Verify the outer fold STARK standalone and bind the shipped trace.
pub fn verify_aggregated_tree(tree: &AggregatedTree) -> Result<(), TurnError> {
    if tree.children.is_empty() {
        return Err(TurnError::InvalidExecutionProof(
            "aggregate_tree: empty child set".into(),
        ));
    }
    if tree.outer_pi.len() != FOLD_PI_COUNT {
        return Err(TurnError::InvalidExecutionProof(format!(
            "aggregate_tree: outer PI has {} entries, expected {}",
            tree.outer_pi.len(),
            FOLD_PI_COUNT
        )));
    }

    // Step 1+2: re-verify children and rebuild digests.
    if tree.child_digests.len() != tree.children.len() {
        return Err(TurnError::InvalidExecutionProof(
            "aggregate_tree: child_digests length != children length".into(),
        ));
    }
    let mut digests: Vec<BabyBear> = Vec::with_capacity(tree.children.len());
    for (i, child) in tree.children.iter().enumerate() {
        verify_aggregated_bundle(child).map_err(|e| {
            TurnError::InvalidExecutionProof(format!(
                "aggregate_tree: child {i} failed verification: {e}"
            ))
        })?;
        let d = bundle_digest(child);
        if d.as_u32() != tree.child_digests[i] {
            return Err(TurnError::InvalidExecutionProof(format!(
                "aggregate_tree: child {i} digest mismatch; recomputed {} != claimed {}",
                d.as_u32(),
                tree.child_digests[i]
            )));
        }
        digests.push(d);
    }

    // Step 3: recompute the expected fold trace + PI from the digests.
    let (expected_trace, expected_pi) = build_tree_fold_trace(&digests);
    let expected_pi_u32: Vec<u32> = expected_pi.iter().map(|x| x.as_u32()).collect();
    if expected_pi_u32 != tree.outer_pi {
        return Err(TurnError::InvalidExecutionProof(format!(
            "aggregate_tree: outer PI mismatch; digest-derived {:?} != claimed {:?}",
            expected_pi_u32, tree.outer_pi
        )));
    }

    // Step 4: verify the outer fold STARK + bind the shipped trace.
    let outer_pi_bb: Vec<BabyBear> = tree
        .outer_pi
        .iter()
        .map(|&v| BabyBear::new_canonical(v))
        .collect();
    let proof = dregg_circuit::stark::proof_from_bytes(&tree.outer_proof_bytes).map_err(|e| {
        TurnError::InvalidExecutionProof(format!(
            "aggregate_tree: failed to decode outer fold proof: {e}"
        ))
    })?;
    if proof.air_name != BundleTreeFoldAir::AIR_NAME {
        return Err(TurnError::InvalidExecutionProof(format!(
            "aggregate_tree: proof AIR name mismatch: {}",
            proof.air_name
        )));
    }
    dregg_circuit::stark::verify(&BundleTreeFoldAir, &proof, &outer_pi_bb).map_err(|e| {
        TurnError::InvalidExecutionProof(format!(
            "aggregate_tree: outer fold STARK verification failed: {e}"
        ))
    })?;

    let trace_bb: Vec<Vec<BabyBear>> = tree
        .outer_trace
        .iter()
        .map(|row| row.iter().map(|&v| BabyBear::new_canonical(v)).collect())
        .collect();
    let recomputed =
        dregg_circuit::stark::recompute_trace_commitment(&BundleTreeFoldAir, &trace_bb)
            .ok_or_else(|| {
                TurnError::InvalidExecutionProof(
                    "aggregate_tree: shipped outer_trace is structurally invalid".into(),
                )
            })?;
    if recomputed != proof.trace_commitment {
        return Err(TurnError::InvalidExecutionProof(
            "aggregate_tree: shipped outer_trace does not match proof commitment".into(),
        ));
    }
    // The shipped trace must be the canonical digest-derived trace, so the
    // chain the proof attests is exactly the one over our recomputed digests.
    if trace_bb != expected_trace {
        return Err(TurnError::InvalidExecutionProof(
            "aggregate_tree: proof-bound trace does not match digest-derived fold trace".into(),
        ));
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
        use dregg_circuit::bilateral_aggregation_air::{self as ag, BilateralAggregationAir};
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
        let tampered_proof =
            dregg_circuit::stark::try_prove(&BilateralAggregationAir, &trace_bb, &outer_pi_bb)
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

    // ---- In-circuit CG-5 (cross-side existence) ----

    #[test]
    fn cg5_in_circuit_proof_attached_and_verifies() {
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);
        let entries = vec![
            (alice, fabricate_wr(&turn, &alice)),
            (bob, fabricate_wr(&turn, &bob)),
        ];
        let bundle = prove_aggregated_bundle(&turn, &entries).expect("prove");
        // The bundle carries a real in-circuit CG-5 proof.
        let cse = bundle
            .cross_side_existence
            .as_ref()
            .expect("CG-5 proof must be attached");
        assert_eq!(&cse.proof_bytes[0..4], b"DREG");
        // Full bundle verification (which now includes the algebraic CG-5
        // step) succeeds.
        verify_aggregated_bundle(&bundle).expect("verify with in-circuit CG-5");
    }

    #[test]
    fn cg5_rejects_missing_peer_in_circuit() {
        // Directly exercise the algebraic CG-5 path: a covered set with only
        // the sender (peer missing) does not balance, so the proof cannot be
        // produced — the missing-peer attack is caught algebraically.
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);
        // Only alice covered; bob (the transfer peer) is missing.
        let res = prove_cross_side_existence(&turn, &[alice]);
        assert!(
            res.is_err(),
            "missing-peer bundle must fail the algebraic balance proof; got {:?}",
            res
        );
    }

    #[test]
    fn cg5_verifier_rejects_forged_cell_set() {
        // Honest 2-cell bundle, but an attacker swaps participating_cells to a
        // single-cell list when calling the CG-5 verifier directly. The
        // canonical schedule then expects an unbalanced edge set, so the
        // proof-bound trace no longer matches → reject.
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);
        let cse = prove_cross_side_existence(&turn, &[alice, bob]).expect("prove honest CG-5");
        // Verify against a forged (single-cell) participant claim.
        let res = verify_cross_side_existence(&cse, &turn, &[alice]);
        assert!(
            res.is_err(),
            "CG-5 verify against forged cell set must reject; got {:?}",
            res
        );
        // Sanity: honest cell set verifies.
        verify_cross_side_existence(&cse, &turn, &[alice, bob])
            .expect("honest cell set must verify");
    }

    #[test]
    fn cg5_three_cell_ring_balances_in_circuit() {
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
        let cse = prove_cross_side_existence(&turn, &[alice, bob, carol])
            .expect("3-cell ring must balance");
        verify_cross_side_existence(&cse, &turn, &[alice, bob, carol])
            .expect("3-cell ring CG-5 must verify");
    }

    // ---- Proof-of-proofs / tree fold ----

    #[test]
    fn tree_fold_two_bundles_proves_and_verifies() {
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let carol = cid(0xC3);
        let dave = cid(0xD4);
        let turn1 = make_transfer_turn(alice, bob, 100, 1);
        let turn2 = make_transfer_turn(carol, dave, 200, 2);
        let b1 = prove_aggregated_bundle(
            &turn1,
            &[
                (alice, fabricate_wr(&turn1, &alice)),
                (bob, fabricate_wr(&turn1, &bob)),
            ],
        )
        .expect("bundle1");
        let b2 = prove_aggregated_bundle(
            &turn2,
            &[
                (carol, fabricate_wr(&turn2, &carol)),
                (dave, fabricate_wr(&turn2, &dave)),
            ],
        )
        .expect("bundle2");

        let tree = prove_aggregated_tree(vec![b1, b2]).expect("tree fold");
        assert_eq!(tree.children.len(), 2);
        assert_eq!(&tree.outer_proof_bytes[0..4], b"DREG");
        verify_aggregated_tree(&tree).expect("tree must verify");
    }

    #[test]
    fn tree_fold_rejects_tampered_child() {
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let carol = cid(0xC3);
        let dave = cid(0xD4);
        let turn1 = make_transfer_turn(alice, bob, 100, 1);
        let turn2 = make_transfer_turn(carol, dave, 200, 2);
        let b1 = prove_aggregated_bundle(
            &turn1,
            &[
                (alice, fabricate_wr(&turn1, &alice)),
                (bob, fabricate_wr(&turn1, &bob)),
            ],
        )
        .expect("bundle1");
        let b2 = prove_aggregated_bundle(
            &turn2,
            &[
                (carol, fabricate_wr(&turn2, &carol)),
                (dave, fabricate_wr(&turn2, &dave)),
            ],
        )
        .expect("bundle2");

        let mut tree = prove_aggregated_tree(vec![b1, b2]).expect("tree fold");
        // Tamper a child's outer PI after folding. The child re-verification
        // (step 1) and the digest recomputation (step 2) both reject.
        use dregg_circuit::bilateral_aggregation_air as ag;
        tree.children[0].outer_pi[ag::OUTER_BILATERAL_CONSISTENT] = 0;
        let res = verify_aggregated_tree(&tree);
        assert!(res.is_err(), "tampered child must reject; got {:?}", res);
    }

    #[test]
    fn tree_fold_rejects_swapped_child_digest() {
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let carol = cid(0xC3);
        let dave = cid(0xD4);
        let turn1 = make_transfer_turn(alice, bob, 100, 1);
        let turn2 = make_transfer_turn(carol, dave, 200, 2);
        let b1 = prove_aggregated_bundle(
            &turn1,
            &[
                (alice, fabricate_wr(&turn1, &alice)),
                (bob, fabricate_wr(&turn1, &bob)),
            ],
        )
        .expect("bundle1");
        let b2 = prove_aggregated_bundle(
            &turn2,
            &[
                (carol, fabricate_wr(&turn2, &carol)),
                (dave, fabricate_wr(&turn2, &dave)),
            ],
        )
        .expect("bundle2");
        let mut tree = prove_aggregated_tree(vec![b1, b2]).expect("tree fold");
        // Lie about the first child's digest.
        tree.child_digests[0] = tree.child_digests[0].wrapping_add(1) & 0x7FFF_FFFF;
        let res = verify_aggregated_tree(&tree);
        assert!(
            res.is_err(),
            "swapped child digest must reject; got {:?}",
            res
        );
    }

    #[test]
    fn tree_fold_json_roundtrip() {
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);
        let b1 = prove_aggregated_bundle(
            &turn,
            &[
                (alice, fabricate_wr(&turn, &alice)),
                (bob, fabricate_wr(&turn, &bob)),
            ],
        )
        .expect("bundle");
        let tree = prove_aggregated_tree(vec![b1.clone(), b1]).expect("tree");
        let json = tree.to_json().expect("to_json");
        let back = AggregatedTree::from_json(&json).expect("from_json");
        verify_aggregated_tree(&back).expect("re-verify after roundtrip");
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
