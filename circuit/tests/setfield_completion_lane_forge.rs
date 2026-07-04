//! # R1 FORGE PROBE — the setField written-slot VALUE8 completion-lane seam (audit §6 R1 / S1).
//!
//! The TRUST-BASE-CENSUS §6 R1 claims a LIVE ledgerless soundness gap: on a `setField(idx<8)` WRITE
//! turn the written field's completion lanes 1..7 (the high 224 bits of the 32-byte value) are
//! EXCEPTED from the freeze (`v3OfFrozenSetField` / `fieldsCompletionFreezesExcept slot`) AND not
//! forced to the declared value — so a ledgerless `verify_vm_descriptor2` client would accept an
//! arbitrary high-224-bit field value.
//!
//! THIS PROBE ATTACKS THAT CLAIM against the ACTUAL DEPLOYED descriptor
//! (`setFieldVmDescriptor2-{slot}R24` in `V3_STAGED_REGISTRY_TSV`), which the Lean `v3RegistryBare`
//! emits as `withSelectorGate SEL_SET_FIELD (v3OfFrozen (setFieldTickFace slot))` — the freeze-ALL
//! variant (`fieldsCompletionFreezes` = all 56 completion lanes BEFORE↔AFTER), NOT the "except"
//! variant `setFieldV3 = v3OfFrozenSetField` the census grounded on (which is defined + carries
//! keystones but is NOT wired into the deployed registry).
//!
//! Two teeth:
//!   * `honest_small_value_setfield_proves_and_verifies` — a setField whose value has ZERO high
//!     bytes (completion lanes 0 before AND after) proves + verifies (the freeze `0==0` holds).
//!   * `forged_written_slot_completion_lanes_is_unsat` — a forge that sets the written slot's
//!     completion lanes 1..7 to arbitrary nonzero (≠ the honest/pre-state 0) while keeping lane 0
//!     honest, recomputes the downstream commitment so NEW_COMMIT genuinely absorbs the forged high
//!     bytes (the wire view), and patches the post-state dpis — is UNSAT through prove/verify ALONE.
//!     If it ACCEPTS, the census R1 forge is LIVE. If it is UNSAT, the deployed freeze BINDS the
//!     written slot's completion lanes (to the pre-state) and the R1 silent-forge is closed on the
//!     deployed wire (though at the cost of the honest large-value write, a completeness seam).

use dregg_cell::{Cell, Ledger};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    AFTER_BASE, B_CHAIN_BASE, B_IROOT, B_STATE_COMMIT, NUM_PRE_LIMBS, V1_PI_COUNT,
    empty_caveat_manifest, generate_rotated_effect_vm_trace, rotated_descriptor_name_for_effect,
};
use dregg_circuit::effect_vm::{CellState, Effect, fold_bytes32_to_bb};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_many;
use dregg_turn::rotation_witness as rw;

/// The written slot under test.
const SLOT: usize = 3;
/// The first completion-lane pre-limb offset for `SLOT` (lanes 1..7 → `112 + 7·slot .. +6`).
const COMPLETION_BASE: usize = 112 + 7 * SLOT;

fn rotated_descriptor_json(name: &str) -> &'static str {
    V3_STAGED_REGISTRY_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(name) {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{name} not in V3_STAGED_REGISTRY_TSV"))
}

fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn bridge(w: &rw::RotationWitness) -> dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness {
    dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
        .expect("pre-iroot limbs")
}

/// Re-run the AFTER block's chained absorption on one row so `B_STATE_COMMIT` reflects the row's
/// current pre-limbs (incl. any forged completion lanes). Byte-identical to `fill_block`.
fn recompute_after_chain(row: &mut [BabyBear]) {
    let base = AFTER_BASE;
    let mut d = hash_many(&[row[base], row[base + 1], row[base + 2], row[base + 3]]);
    let mut chain = 0usize;
    row[base + B_CHAIN_BASE + chain] = d;
    chain += 1;
    let mut col = 4usize;
    while col < NUM_PRE_LIMBS {
        let remaining = NUM_PRE_LIMBS - col;
        if remaining >= 3 {
            d = hash_many(&[d, row[base + col], row[base + col + 1], row[base + col + 2]]);
            col += 3;
        } else {
            d = hash_many(&[d, row[base + col]]);
            col += 1;
        }
        row[base + B_CHAIN_BASE + chain] = d;
        chain += 1;
    }
    row[base + B_STATE_COMMIT] = hash_many(&[d, row[base + B_IROOT]]);
}

struct Honest {
    desc: dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    trace: Vec<Vec<BabyBear>>,
    dpis: Vec<BabyBear>,
    mem_boundary: MemBoundaryWitness,
    map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>>,
}

/// Build an honest single-effect setField trace whose written value has ZERO high bytes (so the
/// deployed completion freeze `before == after == 0` holds and the honest write proves).
fn build_honest_small() -> (Honest, BabyBear) {
    let before: i64 = 50_000;
    // A small numeric field value: only the low 4 bytes (big-endian 28..32) are set, so
    // `field_limbs8` completion lanes 1..7 are all ZERO.
    let mut field_bytes = [0u8; 32];
    field_bytes[28..32].copy_from_slice(&1_000u32.to_be_bytes());
    let new_value = fold_bytes32_to_bb(&field_bytes);

    let effect = Effect::SetField {
        field_idx: SLOT as u32,
        value: new_value,
    };
    let name = rotated_descriptor_name_for_effect(&effect).expect("setField is a cohort member");
    assert_eq!(name, "setFieldVmDescriptor2-3R24");
    let desc = parse_vm_descriptor2(rotated_descriptor_json(name)).expect("descriptor parses");

    let mut after_cell = producer_cell(before, 0);
    assert!(after_cell.state.set_field(SLOT, field_bytes), "set_field");

    let st = CellState::new(before as u64, 0);
    let effects = vec![effect];
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before, 0);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );
    let caveat = empty_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("live rotated generator must produce a setField trace + PIs");

    (
        Honest {
            desc,
            trace,
            dpis,
            mem_boundary: MemBoundaryWitness::default(),
            map_heaps: vec![],
        },
        new_value,
    )
}

fn refused(h: &Honest, trace: &[Vec<BabyBear>], dpis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(&h.desc, trace, dpis, &h.mem_boundary, &h.map_heaps)?;
        verify_vm_descriptor2(&h.desc, &proof, dpis)
    }));
    match r {
        Err(_) => true,
        Ok(res) => res.is_err(),
    }
}

#[test]
fn honest_small_value_setfield_proves_and_verifies() {
    let (h, _v) = build_honest_small();
    // Self-check: the honest AFTER completion lanes of the written slot are ZERO on every row.
    for row in &h.trace {
        for k in 0..7 {
            assert_eq!(
                row[AFTER_BASE + COMPLETION_BASE + k],
                BabyBear::ZERO,
                "honest small value: written-slot completion lane {k} must be zero"
            );
        }
    }
    let proof = prove_vm_descriptor2(&h.desc, &h.trace, &h.dpis, &h.mem_boundary, &h.map_heaps)
        .expect("HONEST small-value setField must prove against the deployed descriptor");
    verify_vm_descriptor2(&h.desc, &proof, &h.dpis)
        .expect("HONEST small-value setField proof must verify");
    eprintln!("R1 PROBE: honest small-value setField proves+verifies on the deployed descriptor.");
}

/// Build an honest single-effect setField whose written value has NONZERO high bytes (so the
/// deployed completion freeze `before(0) == after(≠0)` is VIOLATED — the completeness seam).
fn build_honest_large() -> Honest {
    let before: i64 = 50_000;
    let mut field_bytes = [0u8; 32];
    field_bytes[0] = 0xAB; // a high byte → nonzero completion lane
    field_bytes[1] = 0xCD;
    field_bytes[28..32].copy_from_slice(&1_000u32.to_be_bytes());
    let new_value = fold_bytes32_to_bb(&field_bytes);
    let effect = Effect::SetField {
        field_idx: SLOT as u32,
        value: new_value,
    };
    let name = rotated_descriptor_name_for_effect(&effect).expect("setField cohort member");
    let desc = parse_vm_descriptor2(rotated_descriptor_json(name)).expect("descriptor parses");
    let mut after_cell = producer_cell(before, 0);
    assert!(after_cell.state.set_field(SLOT, field_bytes), "set_field");
    let st = CellState::new(before as u64, 0);
    let effects = vec![effect];
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before, 0);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &[0u8; 32],
        &[0u8; 32],
        &vec![[3u8; 32]],
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &[0u8; 32],
        &[0u8; 32],
        &vec![[3u8; 32]],
        &Default::default(),
    );
    let caveat = empty_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("live rotated generator must produce a large-value setField trace + PIs");
    Honest {
        desc,
        trace,
        dpis,
        mem_boundary: MemBoundaryWitness::default(),
        map_heaps: vec![],
    }
}

/// **THE REAL RESIDUAL (a completeness seam, NOT a soundness forge).** An honest setField whose
/// written value has NONZERO high bytes CANNOT prove against the deployed freeze-ALL descriptor: the
/// completion freeze `before(0) == after(≠0)` rejects it. The written field's high 224 bits are
/// FROZEN to the pre-state, so only ≤lane-0 values are writable — a completeness limitation. The
/// proper close is the VALUE8 weld (force the written slot's 7 completion lanes to the declared
/// value8 params, replacing the freeze), which is VK-affecting and gated (ember-decision).
#[test]
fn honest_large_value_setfield_fails_the_deployed_freeze() {
    let h = build_honest_large();
    // At least one written-slot completion lane is nonzero on the active row (non-vacuity).
    let any_nonzero =
        (0..7).any(|k| h.trace[0][AFTER_BASE + COMPLETION_BASE + k] != BabyBear::ZERO);
    assert!(
        any_nonzero,
        "the large value must move ≥1 written-slot completion lane off zero"
    );
    assert!(
        refused(&h, &h.trace, &h.dpis),
        "the deployed freeze-ALL setField descriptor must REJECT an honest large-value write \
         (before==after freeze violated on the written slot's completion lanes) — the completeness \
         seam. If this proves, the freeze is absent."
    );
    eprintln!(
        "R1 RESIDUAL: an honest large-value setField FAILS the deployed freeze — the written field's \
         high bytes are frozen to the pre-state (completeness seam, not a soundness forge)."
    );
}

#[test]
fn forged_written_slot_completion_lanes_is_unsat() {
    let (h, _v) = build_honest_small();

    // Sanity: honest proves (so a reject below is the FORGE, not a broken fixture).
    let proof = prove_vm_descriptor2(&h.desc, &h.trace, &h.dpis, &h.mem_boundary, &h.map_heaps)
        .expect("honest baseline must prove");
    verify_vm_descriptor2(&h.desc, &proof, &h.dpis).expect("honest baseline must verify");

    // THE FORGE: on the active row (row 0), set the written slot's completion lanes 1..7 to
    // arbitrary NONZERO values (≠ the honest/pre-state 0), keeping lane 0 (the welded limb) honest.
    // Recompute the AFTER chain so NEW_COMMIT genuinely absorbs the forged high bytes — the exact
    // wire view a ledgerless client would accept. BEFORE stays honest (pre-state completion 0), so
    // the ONLY thing that can bite is the completion freeze `before == after`.
    let mut ftrace = h.trace.clone();
    let n = ftrace.len();
    let forged_lanes: [u32; 7] = [0xDEAD, 0xBEEF, 0x1234, 0x5678, 0x9ABC, 0xCAFE, 0xF00D];
    for k in 0..7 {
        ftrace[0][AFTER_BASE + COMPLETION_BASE + k] = BabyBear::new(forged_lanes[k]);
    }
    recompute_after_chain(&mut ftrace[0]);

    // Patch the rotated NEW_COMMIT PI (PI 43) to the forged active row's AFTER commit — the wire
    // view (the light client is handed this NEW_COMMIT). NOTE: for a single-effect trace the last
    // row's AFTER commit is the published one; here the active row IS row 0 and the padding rows
    // fold forward, so patch to whatever the last row now carries after the chain. To keep the
    // published commit consistent with the forged high bytes we mirror the forged completion lanes
    // onto every row's AFTER block and rebuild each chain, then pin PI 43 to the last row.
    for r in 1..n {
        for k in 0..7 {
            ftrace[r][AFTER_BASE + COMPLETION_BASE + k] = BabyBear::new(forged_lanes[k]);
        }
        recompute_after_chain(&mut ftrace[r]);
    }
    let mut fdpis = h.dpis.clone();
    fdpis[V1_PI_COUNT + 1] = ftrace[n - 1][AFTER_BASE + B_STATE_COMMIT];

    // Self-check (non-vacuity): the forged published commit DIFFERS from the honest one — the wire
    // genuinely carries the forged high bytes.
    assert_ne!(
        ftrace[n - 1][AFTER_BASE + B_STATE_COMMIT],
        h.trace[n - 1][AFTER_BASE + B_STATE_COMMIT],
        "the forged completion lanes must publish a DIFFERENT commit (else the forge is vacuous)"
    );

    let unsat = refused(&h, &ftrace, &fdpis);
    // Report the verdict either way — this is the R1 attack, so the truth matters, not the pass.
    if unsat {
        eprintln!(
            "R1 VERDICT: the written-slot completion-lane forge is UNSAT on the deployed descriptor \
             — the freeze-ALL setField descriptor BINDS the written slot's completion lanes \
             (before==after). The census R1 silent-forge does NOT reproduce on the deployed wire."
        );
    } else {
        eprintln!(
            "R1 VERDICT: the written-slot completion-lane forge PROVES+VERIFIES — the census R1 \
             silent-forge is LIVE on the deployed wire (the high 224 bits are unconstrained)."
        );
    }
    assert!(
        unsat,
        "R1 FORGE LIVE: a setField post-cell forged to differ ONLY in the written slot's completion \
         lanes 1..7 (high 224 bits) proves+verifies — a ledgerless client accepts an arbitrary \
         high-224-bit field value (census §6 R1 confirmed live)."
    );
}
