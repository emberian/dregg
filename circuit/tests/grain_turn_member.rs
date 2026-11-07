//! # The single-tick grain member (`grainTurnVmDescriptor2R24`, initiative 10) — prove/verify
//! against the COMMITTED bytes, and the Rust twins of the Lean refusals.
//!
//! One executor grain turn is ONE row: slots 3..=7 written, `turn.fee` debited from `bal_lo` and
//! published at `ROT_PI_COUNT`, the nonce ticked ONCE (Lean `EffectVmEmitGrainTurn`,
//! `EffectVmEmitGrainTurnRotated`). The teeth here run the real `prove_vm_descriptor2` /
//! `verify_vm_descriptor2` over the member parsed from the committed registries:
//!   * the honest turn proves and verifies (narrow V3 and the live wide member);
//!   * a row whose fee param is not the debit (the after-block carries the real post-cell) is UNSAT;
//!   * the published fee PI moved off the proven fee does not verify;
//!   * a row that ticks the nonce TWICE is UNSAT (`grainTurn_rejects_double_tick_row`);
//!   * a second active grain row is UNSAT (the window gate, `grainTurn_refuses_two_ticks`).
//!
//! Run: `cargo test -p dregg-circuit --test grain_turn_member`.

use dregg_cell::{Cell, Ledger};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    GRAIN_TURN_DESCRIPTOR_NAME, GRAIN_TURN_EXTRA_PIS, ROT_PI_COUNT, RotatedBlockWitness,
    empty_caveat_manifest, generate_rotated_effect_vm_descriptor_and_trace_wide,
    generate_rotated_effect_vm_trace, rotated_descriptor_name_for_effect,
};
use dregg_circuit::effect_vm::{
    CellState, Effect, STATE_AFTER_BASE, STATE_BEFORE_BASE, fold_bytes32_to_bb, sel, state,
};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_turn::rotation_witness as rw;

const FEE: u64 = 5_000;
const BALANCE: i64 = 100_000;

fn tsv_json(tsv: &'static str, name: &str) -> &'static str {
    tsv.lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(name) {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{name} not in tsv"))
}

fn worker(balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 0x6a;
    Cell::with_balance(pk, [0u8; 32], balance)
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
}

struct Fixture {
    st: CellState,
    effect: Effect,
    before_w: rw::RotationWitness,
    after_w: rw::RotationWitness,
}

/// An honest grain turn on a fresh worker: five 32-byte writes with nonzero high bytes (so the
/// completion lanes move), the fee debited, the nonce ticked once — the executor's per-turn
/// transition (`grain-turn/tests/ledger_head_delta.rs` measures the same shape on the executor).
fn fixture(claimed_fee: u64) -> Fixture {
    let before_cell = worker(BALANCE);
    let mut after_cell = before_cell.clone();
    let mut values = [BabyBear::ZERO; 5];
    for (k, v) in values.iter_mut().enumerate() {
        let mut bytes = [0u8; 32];
        bytes[0] = 0xA0 + k as u8;
        bytes[31] = 1 + k as u8;
        assert!(after_cell.state.set_field(3 + k, bytes));
        *v = fold_bytes32_to_bb(&bytes);
    }
    after_cell.state.set_balance(BALANCE - FEE as i64);
    after_cell.state.set_nonce(before_cell.state.nonce() + 1);
    let effect = Effect::GrainTurn {
        values,
        fee: claimed_fee,
    };
    assert_eq!(
        rotated_descriptor_name_for_effect(&effect),
        Some(GRAIN_TURN_DESCRIPTOR_NAME)
    );
    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).unwrap();
    let z8 = dregg_circuit::heap_root::empty_heap_root_8();
    let rvk = rw::empty_revoked_root_8();
    let rlog = vec![[7u8; 32]];
    let w = |c: &Cell| rw::produce(c, &ledger, &z8, &z8, &rvk, &rlog, &Default::default());
    Fixture {
        st: CellState::new(BALANCE as u64, 0),
        effect,
        before_w: w(&before_cell),
        after_w: w(&after_cell),
    }
}

fn narrow(f: &Fixture) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    generate_rotated_effect_vm_trace(
        &f.st,
        std::slice::from_ref(&f.effect),
        &bridge(&f.before_w),
        &bridge(&f.after_w),
        &empty_caveat_manifest(),
    )
    .expect("the rotated generator builds a grain row")
}

fn v3_desc() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(tsv_json(V3_STAGED_REGISTRY_TSV, GRAIN_TURN_DESCRIPTOR_NAME))
        .expect("the committed V3 grain member parses")
}

fn prove_verify(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], dpis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, dpis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, dpis)
    }));
    matches!(r, Ok(Ok(())))
}

#[test]
fn honest_grain_turn_proves_on_the_committed_v3_member() {
    let f = fixture(FEE);
    let (trace, dpis) = narrow(&f);
    let desc = v3_desc();
    assert_eq!(dpis.len(), desc.public_input_count);
    assert_eq!(dpis.len(), ROT_PI_COUNT + GRAIN_TURN_EXTRA_PIS + 4);
    assert_eq!(
        dpis[ROT_PI_COUNT],
        BabyBear::new(FEE as u32),
        "the fee is published"
    );
    assert!(
        prove_verify(&desc, &trace, &dpis),
        "the honest grain turn proves"
    );
}

#[test]
fn honest_grain_turn_proves_on_the_live_wide_member() {
    let f = fixture(FEE);
    let (desc, trace, dpis, map_heaps, mem_boundary) =
        generate_rotated_effect_vm_descriptor_and_trace_wide(
            &f.st,
            std::slice::from_ref(&f.effect),
            &bridge(&f.before_w),
            &bridge(&f.after_w),
            &empty_caveat_manifest(),
            None,
            None,
            None,
            None,
        )
        .expect("the live wide producer builds a grain leg");
    assert_eq!(dpis.len(), desc.public_input_count);
    assert_eq!(dpis[ROT_PI_COUNT], BabyBear::new(FEE as u32));
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .expect("the honest grain turn proves on the wide member");
    verify_vm_descriptor2(&desc, &proof, &dpis).expect("and verifies");
    // The published fee is bound: moved off the proven fee, the same proof does not verify.
    let mut moved = dpis.clone();
    moved[ROT_PI_COUNT] = BabyBear::new(FEE as u32 - 1);
    assert!(
        verify_vm_descriptor2(&desc, &proof, &moved).is_err(),
        "a fee PI moved off the proven debit is refused"
    );
}

#[test]
fn a_fee_that_is_not_the_debit_is_unsat() {
    // The row claims 4999 while the post-cell (the after block the welds read) carries the 5000
    // debit: the v1 after-balance and the rotated after-block disagree, and the gates refuse it.
    let f = fixture(FEE - 1);
    let (trace, dpis) = narrow(&f);
    assert_eq!(dpis[ROT_PI_COUNT], BabyBear::new(FEE as u32 - 1));
    assert!(
        !prove_verify(&v3_desc(), &trace, &dpis),
        "a row whose fee is not the debit the post-cell carries must be UNSAT"
    );
}

#[test]
fn a_double_tick_is_unsat() {
    let f = fixture(FEE);
    let (trace, dpis) = narrow(&f);
    let desc = v3_desc();
    assert!(prove_verify(&desc, &trace, &dpis), "honest baseline");
    // Row 0 ticks twice; every later row starts (and stays) at the forged nonce.
    let mut forged = trace.clone();
    let n0 = forged[0][STATE_BEFORE_BASE + state::NONCE];
    let two = n0 + BabyBear::new(2);
    forged[0][STATE_AFTER_BASE + state::NONCE] = two;
    for row in forged.iter_mut().skip(1) {
        row[STATE_BEFORE_BASE + state::NONCE] = two;
        row[STATE_AFTER_BASE + state::NONCE] = two;
    }
    assert!(
        !prove_verify(&desc, &forged, &dpis),
        "a grain row that ticks the nonce twice must be UNSAT"
    );
}

#[test]
fn a_second_active_grain_row_is_unsat() {
    let f = fixture(FEE);
    let (trace, dpis) = narrow(&f);
    let desc = v3_desc();
    // Row 1 (a pad) claims to be a second grain row: the window gate refuses it.
    let mut forged = trace.clone();
    forged[1][sel::GRAIN_TURN] = BabyBear::ONE;
    forged[1][sel::NOOP] = BabyBear::ZERO;
    assert!(
        !prove_verify(&desc, &forged, &dpis),
        "a second active grain row must be UNSAT"
    );
}
