//! Witness adapter for the Lean-authored note-spend recursion leaf.
//!
//! `NoteSpendingLeafEmit.noteSpendLeafDescFixed` supplies the consumed AIR: 149 columns,
//! seven public inputs, and 33 constraints, including six last-row boundary repairs.
//! Rust parses the artifact and builds witnesses; it does not author constraints.
//! `NoteSpendingLeafServed` composes the existing semantic bridges. Membership still
//! requires canonical values, a faithful chip table, and the explicit Merkle path shape.
//! This scalar fact-hash tree is not the deployed Faithful8 note tree.
//!
//! The witness builder produces 65 base columns and the public tuple
//! `[nullifier, merkle_root, value_lo, asset_type, destination_federation, value_hi,
//! mint_hash]`. The prover appends 12×7 Poseidon2 chip lanes.

use crate::descriptor_ir2::{EffectVmDescriptor2, parse_vm_descriptor2};
use crate::dsl::note_spending::{generate_note_spending_trace, note_spend_mint_hash_felt};
use crate::field::BabyBear;
use crate::note_spending_witness::{
    MIN_MERKLE_DEPTH, NOTE_SPENDING_WIDTH, NoteSpendingWitness, col, pi,
};
use crate::poseidon2::hash_fact;

/// The consumed serialization of `NoteSpendingLeafEmit.noteSpendLeafDescFixed`.
pub const NOTE_SPEND_LEAF_GOLDEN_JSON: &str =
    include_str!("../descriptors/by-name/note-spend-leaf.json");

/// The dispatched AIR-name of the emitted note-spend leaf descriptor.
pub const NOTE_SPEND_LEAF_NAME: &str = "note-spend-leaf::dregg-note-spending-dsl-v3";

/// The exposed claim width: the 6 note-spend PIs + the felt-domain mint_hash.
/// Lanes: `[nullifier, merkle_root, value_lo, asset_type, destination_federation, value_hi,
/// mint_hash]`.
pub const NOTE_SPEND_CLAIM_LEN: usize = 7;

/// PI slot of the felt-domain mint identity (appended after the source descriptor's 6 PIs).
pub const NOTE_SPEND_MINT_HASH_PI: usize = 6;

/// Row-0 copy of the Merkle root, pinned to `pi[1]` (`PiBinding{First}`) so the mint-hash absorb can
/// read the root on the commitment row (the canonical root carrier is the last row's `CURRENT`, also
/// pinned to `pi[1]` — both anchored to the same PI).
const MINT_ROOT_COL: usize = NOTE_SPENDING_WIDTH; // 62
/// The mint-hash chain intermediate `hash_fact(nullifier, [root, dest, asset])`.
const MINT_M1_COL: usize = NOTE_SPENDING_WIDTH + 1; // 63
/// The felt-domain mint identity, pinned to `pi[6]`.
const MINT_HASH_COL: usize = NOTE_SPENDING_WIDTH + 2; // 64
/// Base width of the extended trace (source 62 + the 3 mint columns); chip lane columns append past.
const EXT_BASE_WIDTH: usize = NOTE_SPENDING_WIDTH + 3; // 65

/// Parse the Lean-authored AIR, including the last-row boundary repair.
pub fn note_spend_leaf_descriptor() -> Result<EffectVmDescriptor2, String> {
    parse_vm_descriptor2(NOTE_SPEND_LEAF_GOLDEN_JSON)
}

/// The mint identity from a 6-slot note-spend PI vector — [`note_spend_mint_hash_felt`] over the PI
/// slots. This is the FELT-DOMAIN production commitment the executor's
/// `verify_note_spend_descriptor2` binds to; the witness reproduces it byte-for-byte as the
/// appended 7th PI.
fn mint_hash_from_pis(pis: &[BabyBear]) -> BabyBear {
    note_spend_mint_hash_felt(
        pis[pi::NULLIFIER],
        pis[pi::MERKLE_ROOT],
        pis[pi::VALUE],
        pis[pi::ASSET_TYPE],
        pis[pi::DESTINATION_FEDERATION],
        pis[pi::VALUE_HI],
    )
}

/// The HONEST 7-slot claim tuple for a witness: the source circuit's 6 PIs
/// (`generate_note_spending_trace`'s vector) + the felt-domain mint identity.
pub fn note_spend_leaf_public_inputs(witness: &NoteSpendingWitness) -> Vec<BabyBear> {
    let (_, pis) = generate_note_spending_trace(witness);
    let mint = mint_hash_from_pis(&pis);
    let mut out = pis;
    out.push(mint);
    out
}

/// **`note_spend_witness`** — build the width-65 note-spend base trace + the 7-slot claim tuple
/// `[nullifier, merkle_root, value_lo, asset_type, destination_federation, value_hi, mint_hash]` for
/// the emitted [`note_spend_leaf_descriptor`].
///
/// `witness` is the SAME [`NoteSpendingWitness`] the off-AIR `note_spending_dsl_circuit` consumes
/// (spending key, 28-limb commitment preimage, Merkle path). The Merkle depth must be
/// ≥ [`MIN_MERKLE_DEPTH`], the sibling/position lists must agree in length, and every position must
/// be `< 4`. The source trace is extended with the 3 mint columns on row 0 (Merkle/padding rows stay
/// zero — the mint sites are row-gated); the 12×7 chip-lane columns are filled by the prover's
/// `trace_with_chip_lanes`. The appended 7th PI is byte-equal to [`note_spend_mint_hash_felt`] over
/// the source PIs (the felt-domain mint identity). This builder does NOT pre-judge the spend — the
/// descriptor's pins and the Poseidon2-chip lookups do (see the module gate).
pub fn note_spend_witness(
    witness: &NoteSpendingWitness,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    let depth = witness.merkle_siblings.len();
    if depth != witness.merkle_positions.len() {
        return Err(format!(
            "note-spend siblings/positions length mismatch ({depth} vs {})",
            witness.merkle_positions.len()
        ));
    }
    if depth < MIN_MERKLE_DEPTH {
        return Err(format!(
            "note-spend Merkle depth {depth} must be ≥ MIN_MERKLE_DEPTH {MIN_MERKLE_DEPTH}"
        ));
    }
    if let Some(&p) = witness.merkle_positions.iter().find(|&&p| p >= 4) {
        return Err(format!("note-spend Merkle position {p} must be < 4"));
    }

    let (mut trace, pis) = generate_note_spending_trace(witness);
    for row in &mut trace {
        row.resize(EXT_BASE_WIDTH, BabyBear::ZERO);
    }
    let m1 = hash_fact(
        pis[pi::NULLIFIER],
        &[
            pis[pi::MERKLE_ROOT],
            pis[pi::DESTINATION_FEDERATION],
            pis[pi::ASSET_TYPE],
        ],
    );
    let mint = hash_fact(m1, &[pis[pi::VALUE], pis[pi::VALUE_HI]]);
    debug_assert_eq!(mint, mint_hash_from_pis(&pis));
    trace[0][MINT_ROOT_COL] = pis[pi::MERKLE_ROOT];
    trace[0][MINT_M1_COL] = m1;
    trace[0][MINT_HASH_COL] = mint;

    let mut full_pis = pis;
    full_pis.push(mint);
    Ok((trace, full_pis))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_by_name::descriptor_by_name;
    use crate::descriptor_ir2::{
        MemBoundaryWitness, check_descriptor2_wellformed, prove_vm_descriptor2,
        verify_vm_descriptor2,
    };
    use crate::descriptor_ir2::{TID_P2, VmConstraint2};
    use crate::lean_descriptor_air::{VmConstraint, VmRow};
    use crate::note_spending_witness::{merkle_col, test_spending_key};
    use crate::poseidon2::hash_many;
    use crate::refusal::{Outcome, classify};
    use std::panic::AssertUnwindSafe;

    /// A REAL full-width witness (raw 32-byte fields + a > 2^30 u64 value, so the high limb is live).
    /// Depth 2 → 4 trace rows (1 commitment + 2 Merkle + 1 pad), the deployed DSL circuit's own shape.
    fn make_witness(tag: u8) -> NoteSpendingWitness {
        let owner = [tag; 32];
        let nonce = [tag ^ 0x5A; 32];
        let rand = [tag ^ 0xA5; 32];
        let key = test_spending_key(tag as u32 + 0x77);
        let depth = 2;
        let mut siblings = Vec::with_capacity(depth);
        let mut positions = Vec::with_capacity(depth);
        for i in 0..depth {
            siblings.push([
                hash_many(&[BabyBear::new((i * 3 + 1) as u32), BabyBear::new(tag as u32)]),
                hash_many(&[BabyBear::new((i * 3 + 2) as u32), BabyBear::new(tag as u32)]),
                hash_many(&[BabyBear::new((i * 3 + 3) as u32), BabyBear::new(tag as u32)]),
            ]);
            positions.push((i % 4) as u8);
        }
        NoteSpendingWitness::from_note_limbs(
            &owner,
            0xDEAD_BEEF_CAFE, // > 2^30: the value_hi limb is live
            3,
            &nonce,
            &rand,
            key,
            siblings,
            positions,
        )
    }

    /// `true` iff `(trace, pis)` is REJECTED end-to-end — proving refuses OR the produced proof fails
    /// to verify against `pis`. Prove-THEN-verify is the faithful consumer-posture gate.
    fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
        match classify("rejects", || {
            let proof =
                prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
            verify_vm_descriptor2(desc, &proof, pis)
        }) {
            // The p3 debug prover's DOCUMENTED unsat verdict — a real refusal.
            // `classify` REDs on any other panic (a stray unwrap, a trace-assembly
            // debug_assert), which used to land here and read as "rejected".
            Outcome::UnsatPanic(_) => true,
            Outcome::Err(_) => true,
            Outcome::Accepted(_) => false,
        }
    }

    /// Both dispatch and the public constructor consume the repaired artifact.
    #[test]
    fn emitted_note_spend_shape_and_dispatch() {
        let built = note_spend_leaf_descriptor().expect("the emitted note-spend descriptor parses");
        assert_eq!(built.constraints.len(), 33);
        assert_eq!(
            built
                .constraints
                .iter()
                .filter(|c| matches!(
                    c,
                    VmConstraint2::Base(VmConstraint::Boundary {
                        row: VmRow::Last,
                        ..
                    })
                ))
                .count(),
            6
        );
        // Shape pins (mirror the Lean `#guard`s): width 149, 7 PIs, 12 chip lookups, 8 pins, 1 window.
        assert_eq!(built.name, NOTE_SPEND_LEAF_NAME);
        assert_eq!(built.trace_width, 149);
        assert_eq!(built.public_input_count, NOTE_SPEND_CLAIM_LEN);
        check_descriptor2_wellformed(&built).expect("the built descriptor is well-formed");
        let chips = built
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
            .count();
        assert_eq!(
            chips, 12,
            "7 commitment-chain + 2 nullifier + 1 Merkle + 2 mint fact sites"
        );
        let pins = built
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
            .count();
        assert_eq!(pins, 8, "6 source boundary pins + MINT_ROOT + MINT_HASH");
        let windows = built
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
            .count();
        assert_eq!(windows, 1, "the C7 Merkle-chain continuity");
        // The name dispatches through descriptor_by_name to the same descriptor.
        let via_dispatch = descriptor_by_name(NOTE_SPEND_LEAF_NAME).expect("dispatch");
        assert_eq!(
            via_dispatch, built,
            "descriptor_by_name resolves the note-spend leaf"
        );
    }

    /// Each repaired last-row boundary rejects its own malformed row. This checks
    /// the production expression evaluator; the whole-trace counterexample is
    /// `NoteSpendingLeafServed.served_refuses_old_forge`.
    #[test]
    fn emitted_note_spend_last_boundaries_refuse_mutants() {
        let desc = note_spend_leaf_descriptor().expect("emitted AIR");
        let boundaries: Vec<_> = desc
            .constraints
            .iter()
            .filter_map(|c| match c {
                VmConstraint2::Base(VmConstraint::Boundary {
                    row: VmRow::Last,
                    body,
                }) => Some(body),
                _ => None,
            })
            .collect();
        assert_eq!(boundaries.len(), 6);
        let row = vec![BabyBear::ZERO; desc.trace_width];
        for body in &boundaries {
            assert_eq!(
                crate::descriptor_ir2::eval_lean_expr(body, &row),
                BabyBear::ZERO
            );
        }
        for (body, (col, value)) in
            boundaries
                .iter()
                .zip([(16, 2), (5, 1), (1, 1), (19, 1), (2, 1), (4, 4)])
        {
            let mut bad = row.clone();
            bad[col] = BabyBear::new(value);
            assert_ne!(
                crate::descriptor_ir2::eval_lean_expr(body, &bad),
                BabyBear::ZERO
            );
        }
    }

    /// STEP 2 — THE POSITIVE POLE + THE PRODUCTION-COMMITMENT BYTE-MATCH: an honest REAL note-spend
    /// (spending key + 28-limb commitment + Merkle path) proves through the DISPATCHED emitted
    /// descriptor and re-verifies, AND the appended 7th PI is byte-equal to the felt-domain mint
    /// identity `note_spend_mint_hash_felt` the executor's verifier binds to.
    #[test]
    fn honest_note_spend_proves_and_verifies_via_dispatch() {
        let desc = descriptor_by_name(NOTE_SPEND_LEAF_NAME).expect("dispatch");
        let w = make_witness(0x10);
        let (trace, pis) = note_spend_witness(&w).expect("witness builds");
        assert_eq!(pis.len(), NOTE_SPEND_CLAIM_LEN);
        assert_eq!(
            pis[NOTE_SPEND_MINT_HASH_PI],
            note_spend_mint_hash_felt(pis[0], pis[1], pis[2], pis[3], pis[4], pis[5]),
            "the appended mint PI must byte-equal the production felt-domain mint identity"
        );

        let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .expect("the honest note-spend must prove through the emitted descriptor");
        verify_vm_descriptor2(&desc, &proof, &pis)
            .expect("the honest proof must re-verify against the 7-slot claim tuple");
    }

    /// STEP 3a — MUTATION CANARY (nullifier PI): a forged nullifier slot violates the boundary pin
    /// `PiBinding{First, col::NULLIFIER, pi0}` → UNSAT. Non-vacuous: the honest witness is accepted.
    #[test]
    fn forged_nullifier_pi_refuses() {
        let desc = descriptor_by_name(NOTE_SPEND_LEAF_NAME).expect("dispatch");
        let w = make_witness(0x21);
        let (trace, pis) = note_spend_witness(&w).expect("witness");
        assert!(
            !rejects(&desc, &trace, &pis),
            "honest accepted — else vacuous"
        );
        let mut forged = pis.clone();
        forged[pi::NULLIFIER] += BabyBear::ONE;
        assert!(
            rejects(&desc, &trace, &forged),
            "a forged nullifier PI must be REJECTED (nullifier binding tooth)"
        );
    }

    /// STEP 3b — MUTATION CANARY (merkle-root PI): a forged root slot violates the last-row root pin
    /// (and the MINT_ROOT pin at pi1) → UNSAT.
    #[test]
    fn forged_merkle_root_pi_refuses() {
        let desc = descriptor_by_name(NOTE_SPEND_LEAF_NAME).expect("dispatch");
        let w = make_witness(0x32);
        let (trace, pis) = note_spend_witness(&w).expect("witness");
        assert!(
            !rejects(&desc, &trace, &pis),
            "non-vacuity: honest accepted"
        );
        let mut forged = pis.clone();
        forged[pi::MERKLE_ROOT] += BabyBear::ONE;
        assert!(
            rejects(&desc, &trace, &forged),
            "a forged merkle-root PI must be REJECTED (membership root binding)"
        );
    }

    /// STEP 3c — MUTATION CANARY (mint-hash PI): a forged mint identity slot violates the pin
    /// `PiBinding{First, MINT_HASH_COL, pi6}` over the in-AIR-recomputed identity → UNSAT. This is
    /// what makes the exposed mint identity a WELD, not a prover-chosen scalar.
    #[test]
    fn forged_mint_hash_pi_refuses() {
        let desc = descriptor_by_name(NOTE_SPEND_LEAF_NAME).expect("dispatch");
        let w = make_witness(0x43);
        let (trace, pis) = note_spend_witness(&w).expect("witness");
        assert!(
            !rejects(&desc, &trace, &pis),
            "non-vacuity: honest accepted"
        );
        let mut forged = pis.clone();
        forged[NOTE_SPEND_MINT_HASH_PI] += BabyBear::ONE;
        assert!(
            rejects(&desc, &trace, &forged),
            "a forged mint-hash PI must be REJECTED (mint identity weld tooth)"
        );
    }

    /// STEP 3d — MUTATION CANARY (Merkle co-path): a tampered sibling on a Merkle row, claim tuple
    /// honest. The C6 `Poseidon2Chip` membership lookup names a parent digest no genuine permutation
    /// of the tampered inputs serves → UNSAT.
    #[test]
    fn tampered_merkle_sibling_refuses() {
        let desc = descriptor_by_name(NOTE_SPEND_LEAF_NAME).expect("dispatch");
        let w = make_witness(0x54);
        let (mut trace, pis) = note_spend_witness(&w).expect("witness");
        assert!(
            !rejects(&desc, &trace, &pis),
            "non-vacuity: honest accepted"
        );
        // Row 1 is the first Merkle row (is_merkle = 1). Tamper its SIB0 without recomputing PARENT.
        trace[1][merkle_col::SIB0] += BabyBear::ONE;
        assert!(
            rejects(&desc, &trace, &pis),
            "a forged Merkle sibling (wrong co-path) must be REJECTED (C6 chip membership lookup)"
        );
    }

    /// Malformed witnesses (length mismatch, sub-minimum depth, out-of-range position) are refused at
    /// build time.
    #[test]
    fn malformed_witness_refuses() {
        let mut w = make_witness(0x65);
        // length mismatch.
        let mut bad = w.clone();
        bad.merkle_positions.pop();
        assert!(note_spend_witness(&bad).is_err());
        // out-of-range position.
        w.merkle_positions[0] = 4;
        assert!(note_spend_witness(&w).is_err());
    }
}
