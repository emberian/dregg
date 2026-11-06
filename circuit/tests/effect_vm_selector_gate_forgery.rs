//! # THE SELECTOR-GATE FORGERY BITE — the light-client unfoolability close for the gate-less
//! value-cohort family (setField / mint / attenuate / revokeCapability / grantCap).
//!
//! ## The forgery this closes
//!
//! The deployed sovereign verifier (`turn::executor::verify_and_commit_proof_rotated`) resolves ONE
//! rotated descriptor by `vm_effects.first()` and verifies ONE proof over a one-row-per-effect trace.
//! Before the fix, the per-slot setField descriptor (`setFieldVmDescriptor2-{0..7}R24`) and the mint /
//! attenuate / revokeCapability / grantCap members carried NO selector-binding gate. So a turn whose
//! LEAD is gate-less + a TAIL effect — e.g. `[SetField(slot0, v), Transfer(self→victim, A)]` — proved
//! under the gate-less setField LEAD descriptor while the TAIL (Transfer) row's transition was
//! UNFORCED: the prover set the tail row's balance FREELY, the commitment-integrity gates still
//! passed, and `verify_vm_descriptor2` ACCEPTED. A ledgerless light client was fooled (a silent
//! cross-effect transfer the descriptor never constrained).
//!
//! ## The close (Lean-emitted, law #1)
//!
//! Each gate-less member now appends `selectorGate <ownRuntimeSelector>` (`EffectVmEmit.§6½`,
//! `EffectVmEmitRotationV3.withSelectorGate`): the per-row body `(1 - sel[NOOP])·(1 - sel[s])` is
//! forced ZERO on every transition row, so a NON-pad row must carry the descriptor's OWN runtime
//! selector. The foreign-selector TAIL row (`sel[NOOP] = 0`, `sel[SET_FIELD] = 0`, `sel[TRANSFER] =
//! 1`) makes the body `1·1 = 1 ≠ 0` → UNSAT. The forgery is dead at `verify_vm_descriptor2` /
//! `prove_vm_descriptor2` ALONE — no ledger needed.
//!
//! ## The teeth
//!
//!   * NEGATIVE (end-to-end shape): a `[SetField(slot0, v), Transfer]` trace under the setField-0
//!     LEAD descriptor, with the Transfer tail row's balance FORGED (a free debit with no honest
//!     source) — proving REFUSES. Mirrored for mint (`[BridgeMint, Transfer]`).
//!     ⚠ Both arms are OVER-DETERMINED at HEAD and are NOT attribution: measured 2026-07-28 by
//!     removing the gate and re-proving, the forged debit ALSO violates each member's own every-row
//!     balance freeze / balance algebra and the rotated balance weld, so a gate-less clone refuses
//!     them too. They establish that the forged turn does not prove; they do not establish which
//!     constraint says so.
//!   * ATTRIBUTION (the bite, both poles): `foreign_selector_tail_is_refused_by_the_gate_alone`
//!     picks a tail the other gates ADMIT — a ZERO-amount `Transfer`, which moves no balance — so
//!     the foreign `sel[TRANSFER]` on a non-pad row is the sole defect. That trace is UNSAT under
//!     the committed member and PROVES + VERIFIES under a clone with exactly that one gate removed.
//!     One constraint is the entire difference between accept and refuse.
//!   * POSITIVE (no downgrade): an HONEST single-cohort setField turn (the homogeneous shape the
//!     deployed sovereign verify path receives — heterogeneous turns split per cohort in
//!     PATH-PRESERVE / are rejected by the rotated prover) still proves+verifies GREEN.
//!     ⚠ "Honest" is byte-position-sensitive: see [`lane0_field_bytes`]. A value written into
//!     `bytes[0..4]` is NOT an honest turn under the deployed member — the fields GENTIAN freeze
//!     makes it UNSAT — and until 2026-07-28 this file carried exactly that, so the positive
//!     control was red and both negative arms were being satisfied by the freeze rather than by
//!     the gate.
//!
//! Gated on `prover` (compiles `descriptor_ir2`). Run with
//! `cargo test -p dregg-circuit --features prover selector_gate -- --nocapture`.

// (formerly `#![cfg(feature = "prover")]` — that dregg-circuit feature is GONE; the
// descriptor-level prove/verify (`prove_vm_descriptor2`/`verify_vm_descriptor2`) is
// now unconditional in dregg-circuit, so this test compiles + runs by default.)

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, VmConstraint2, parse_vm_descriptor2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::columns::{PARAM_BASE, STATE_AFTER_BASE, param, sel, state};
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, empty_caveat_manifest, generate_rotated_effect_vm_trace,
    rotated_descriptor_name_for_effect,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint};
use dregg_circuit::refusal::{Outcome, classify};
use dregg_turn::rotation_witness as rw;

/// Resolve a rotated descriptor JSON by registry key from the committed staged TSV.
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

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("31 pre-iroot limbs")
}

/// The 32 bytes a cell field must hold for the deployed member to read `v` out of it.
///
/// ⚠ THE POSITION IS NOT `bytes[0..4]`. Since the v13 FAITHFUL FIELDS OCTET each field's 32 bytes
/// ride a full `field_limbs9` nonet, whose LANE 0 — the one welded to rotated limb `4 + slot`, the
/// one the setField write gate binds to the `VALUE` param, and the one
/// `executor::effect_vm_bridge::field_element_to_bb` projects — is `u32::from_be_bytes(b[28..32])`.
/// Lanes 1..7 are the COMPLETION lanes (rotated limbs `113 + 7·slot ..`), and the deployed member
/// FREEZES all 56 of them `before == after` (the fields GENTIAN law, `v3OfFrozen`), so a value
/// written into `bytes[0..4]` lands in lane 2 and the freeze makes the turn UNSAT. That refusal is
/// deployed behaviour, pinned by `setfield_completion_lane_forge::honest_large_value_setfield_
/// fails_the_deployed_freeze`; it is NOT the selector gate. Writing here — the same idiom as that
/// file's green honest pole — keeps every turn in this file an honest LANE-0 write, so the only
/// thing left to refuse a forgery is the gate under test.
fn lane0_field_bytes(v: u32) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[28..32].copy_from_slice(&v.to_be_bytes());
    b
}

/// The unique `selectorGate <own>` body the Lean emit appends (`EffectVmEmit.§6½`,
/// `EffectVmEmitRotationV3.withSelectorGate`): `(1 - sel[NOOP])·(1 - sel[own])`.
fn selector_gate_body(own: usize) -> LeanExpr {
    LeanExpr::mul(
        LeanExpr::add(
            LeanExpr::constant(1),
            LeanExpr::mul(LeanExpr::constant(-1), LeanExpr::var(sel::NOOP)),
        ),
        LeanExpr::add(
            LeanExpr::constant(1),
            LeanExpr::mul(LeanExpr::constant(-1), LeanExpr::var(own)),
        ),
    )
}

/// A CLONE of the committed member with its ONE appended `selectorGate` removed — i.e. the
/// PRE-CLOSE descriptor, the one the forgery in this file was written against.
///
/// This is the anti-vacuity instrument. A `prove` that errs is not by itself evidence the gate
/// bit: a malformed trace errs too, and a tooth that refuses everything reads green from the
/// negative side alone. Removing exactly the gate under test and re-proving the SAME trace
/// separates the two. The exact-count assert means a re-emit that moves the gate's shape reds
/// HERE rather than silently degrading the guard into a second copy of the tooth — and it DID:
/// the last-row hardening flag day moved every row-local body from the transition-domain `Gate`
/// onto a whole-domain `windowGate`, this matched the KIND, removed nothing, and this assert
/// fired. It now matches the BODY through `descriptor_ir2::row_local_body`, which finds it under
/// either domain.
fn without_selector_gate(desc: &EffectVmDescriptor2, own: usize) -> EffectVmDescriptor2 {
    let want = selector_gate_body(own);
    let mut out = desc.clone();
    let before = out.constraints.len();
    out.constraints
        .retain(|c| dregg_circuit::descriptor_ir2::row_local_body(c).as_deref() != Some(&want));
    assert_eq!(
        before - out.constraints.len(),
        1,
        "exactly ONE `selectorGate {own}` must be present in {} — the anti-vacuity guard is only \
         meaningful if it removes the gate under test and nothing else",
        desc.name
    );
    out
}

/// `true` iff `prove_vm_descriptor2` REFUSES (returns `Err` OR panics) on the given trace+PIs.
fn refused(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    dpis: &[BabyBear],
    mem_boundary: &MemBoundaryWitness,
    map_heaps: &[Vec<dregg_circuit::heap_root::HeapLeaf>],
) -> bool {
    match classify("refused", || {
        prove_vm_descriptor2(desc, trace, dpis, mem_boundary, map_heaps)
    }) {
        // The p3 debug prover's DOCUMENTED unsat verdict — a real refusal.
        // `classify` REDs on any other panic (a stray unwrap, a trace-assembly
        // debug_assert), which used to land here and read as "rejected".
        Outcome::UnsatPanic(_) => true,
        Outcome::Err(_) => true,
        Outcome::Accepted(_) => false,
    }
}

/// THE GRADUATION EVIDENCE for SET_FIELD (2026-11-06): EVERY per-slot member
/// `setFieldVmDescriptor2-{0..7}R24`, in BOTH the bare staged registry and the WIDE registry the
/// leg producer mints from, carries exactly ONE appended `selectorGate SET_FIELD`. The forgery
/// teeth below are measured on slot 0; this pins that the other seven slots carry the same gate,
/// so the selector can be admitted for any slot (`proof_forest::CUTOVER_READY_SELECTORS`).
#[test]
fn every_setfield_slot_member_carries_exactly_one_selector_gate() {
    let want = selector_gate_body(sel::SET_FIELD);
    for (registry, tsv) in [
        ("V3_STAGED", V3_STAGED_REGISTRY_TSV),
        (
            "WIDE",
            dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV,
        ),
    ] {
        for k in 0u32..8 {
            let wire =
                dregg_circuit::effect_vm::trace_rotated::rotated_set_field_descriptor_name(k);
            let json = tsv
                .lines()
                .find_map(|l| {
                    let mut it = l.splitn(3, '\t');
                    (it.next() == Some(wire)).then(|| {
                        let _ = it.next();
                        it.next()
                    })?
                })
                .unwrap_or_else(|| panic!("{wire} not in the {registry} registry"));
            let desc = parse_vm_descriptor2(json).expect("the member parses");
            let gates = desc
                .constraints
                .iter()
                .filter(|c| {
                    dregg_circuit::descriptor_ir2::row_local_body(c).as_deref() == Some(&want)
                })
                .count();
            assert_eq!(gates, 1, "{registry} {wire}: selectorGate SET_FIELD count");
        }
    }
}

/// THE NEGATIVE TOOTH (setField LEAD): a `[SetField(slot0, v), Transfer]` trace under the setField-0
/// LEAD descriptor — with the Transfer tail row carrying a FORGED free balance debit — is UNSAT.
/// The appended `selectorGate SET_FIELD` rejects the foreign-selector (TRANSFER) tail row.
#[test]
fn setfield_lead_with_foreign_transfer_tail_is_unsat() {
    let name = "setFieldVmDescriptor2-0R24";
    let desc = parse_vm_descriptor2(rotated_descriptor_json(name))
        .expect("setField-0 rotated descriptor parses");

    let before_balance: i64 = 100_000;
    let field_val = BabyBear::new(0xABCD);
    let st = CellState::new(before_balance as u64, 0);

    // The heterogeneous LEAD = setField(slot 0), TAIL = an outgoing Transfer (the smuggled move).
    let effects = vec![
        Effect::SetField {
            field_idx: 0,
            value: field_val,
        },
        Effect::Transfer {
            amount: 50,
            direction: 1,
        },
    ];

    // The LIVE verify path resolves the descriptor by the LEAD effect — exactly setField-0.
    assert_eq!(
        rotated_descriptor_name_for_effect(&effects[0]),
        Some(name),
        "the lead effect resolves the gate-less setField-0 descriptor (the forgery's entry)"
    );

    // Build the rotated trace + PIs through the LIVE generator (the producer the adversary controls).
    let mut ledger = Ledger::new();
    let mut after_cell = producer_cell(before_balance, 0);
    assert!(after_cell.state.set_field(0, lane0_field_bytes(0xABCD)));
    ledger.insert_cell(after_cell.clone()).unwrap();
    let before_cell = producer_cell(before_balance, 0);
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let caveat = empty_caveat_manifest();

    let (mut trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("generator builds the heterogeneous trace");

    // The TAIL (row 1) carries the foreign TRANSFER selector — the smoking gun the gate forbids.
    assert_eq!(
        trace[1][sel::TRANSFER],
        BabyBear::ONE,
        "row 1 carries the foreign TRANSFER selector"
    );
    assert_eq!(
        trace[1][sel::SET_FIELD],
        BabyBear::ZERO,
        "row 1 does NOT carry the setField selector (it is a foreign row)"
    );
    assert_eq!(
        trace[1][sel::NOOP],
        BabyBear::ZERO,
        "row 1 is NOT a NoOp pad (it is a real foreign effect)"
    );

    // The FORGERY: freely debit the tail row's after-balance (a transfer the descriptor never binds).
    trace[1][STATE_AFTER_BASE + state::BALANCE_LO] =
        trace[1][STATE_AFTER_BASE + state::BALANCE_LO] - BabyBear::new(50);
    trace[1][PARAM_BASE + param::AMOUNT] = BabyBear::new(50);
    trace[1][PARAM_BASE + param::DIRECTION] = BabyBear::ONE;

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    assert!(
        refused(&desc, &trace, &dpis, &mem_boundary, &map_heaps),
        "SOUNDNESS (light-client unfoolable): the foreign-TRANSFER tail row under the setField-0 \
         LEAD descriptor must be UNSAT — the appended `selectorGate SET_FIELD` rejects it"
    );

    // ⚠ THE REFUSAL ABOVE IS OVER-DETERMINED, and this tooth alone does not say which constraint
    // bit. Measured 2026-07-28 by removing the gate and re-proving: with `selectorGate SET_FIELD`
    // stripped the SAME trace is still UNSAT on row 1, at the member's own every-row balance freeze
    // (`after.balance_lo == before.balance_lo`) and the rotated balance weld
    // (`AFTER limb 1 == after.balance_lo`) — the free-debit half of this forgery was already closed
    // without the selector gate. So the assert above is TRUE but is NOT evidence the gate bites.
    // The attribution lives in `foreign_selector_tail_is_refused_by_the_gate_alone` below, which
    // uses a tail the other gates DO admit; keep this arm as the end-to-end shape it always was.
    eprintln!(
        "SELECTOR-GATE FORGERY BITE (setField lead): [SetField, Transfer] under setFieldVmDescriptor2-0R24 \
         is UNSAT — the foreign-selector tail row is rejected by the selector-binding gate."
    );
}

/// THE NEGATIVE TOOTH (mint LEAD): the same bite for the BridgeMint member — `[BridgeMint, Transfer]`
/// under the mint descriptor is UNSAT (the appended `selectorGate BRIDGE_MINT` rejects the tail row).
#[test]
fn mint_lead_with_foreign_transfer_tail_is_unsat() {
    let name = "mintVmDescriptor2R24";
    let desc = parse_vm_descriptor2(rotated_descriptor_json(name))
        .expect("mint rotated descriptor parses");

    let before_balance: i64 = 100_000;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![
        Effect::BridgeMint {
            value_lo: BabyBear::new(10),
            mint_hash: BabyBear::new(0x1234),
            value_full: 10,
        },
        Effect::Transfer {
            amount: 50,
            direction: 1,
        },
    ];
    assert_eq!(
        rotated_descriptor_name_for_effect(&effects[0]),
        Some(name),
        "the lead BridgeMint resolves the mint descriptor"
    );

    let mut ledger = Ledger::new();
    let after_cell = producer_cell(before_balance + 10, 0);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let before_cell = producer_cell(before_balance, 0);
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let caveat = empty_caveat_manifest();

    let (mut trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("generator builds the heterogeneous mint+transfer trace");

    assert_eq!(trace[1][sel::TRANSFER], BabyBear::ONE);
    assert_eq!(trace[1][sel::BRIDGE_MINT], BabyBear::ZERO);
    assert_eq!(trace[1][sel::NOOP], BabyBear::ZERO);

    // Forge the tail transfer's debit.
    trace[1][STATE_AFTER_BASE + state::BALANCE_LO] =
        trace[1][STATE_AFTER_BASE + state::BALANCE_LO] - BabyBear::new(50);
    trace[1][PARAM_BASE + param::AMOUNT] = BabyBear::new(50);
    trace[1][PARAM_BASE + param::DIRECTION] = BabyBear::ONE;

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    assert!(
        refused(&desc, &trace, &dpis, &mem_boundary, &map_heaps),
        "SOUNDNESS: [BridgeMint, Transfer] under the mint descriptor must be UNSAT — the appended \
         `selectorGate BRIDGE_MINT` rejects the foreign-TRANSFER tail row"
    );

    // ⚠ OVER-DETERMINED, same as the setField arm. Measured 2026-07-28: with `selectorGate
    // BRIDGE_MINT` stripped this trace is still UNSAT on row 1 — the mint member's every-row
    // balance algebra (`after.bal_lo - before.bal_lo - AMOUNT`), the `hi/lo` cross-row balance
    // continuity, and the rotated balance weld all bite on the forged debit. True assert, no
    // attribution. See `foreign_selector_tail_is_refused_by_the_gate_alone`.
    eprintln!(
        "SELECTOR-GATE FORGERY BITE (mint lead): [BridgeMint, Transfer] under mintVmDescriptor2R24 is UNSAT."
    );
}

/// THE POSITIVE TOOTH (no downgrade): an HONEST single-cohort setField turn — the homogeneous shape
/// the deployed sovereign verify path actually receives — still PROVES + VERIFIES green through the
/// gated setField-0 descriptor. The active row carries `sel[SET_FIELD] = 1` and the pads
/// `sel[NOOP] = 1`, both of which the appended gate admits.
#[test]
fn honest_homogeneous_setfield_still_proves_and_verifies() {
    let name = "setFieldVmDescriptor2-0R24";
    let desc = parse_vm_descriptor2(rotated_descriptor_json(name))
        .expect("setField-0 rotated descriptor parses");

    let before_balance: i64 = 100_000;
    let field_val = BabyBear::new(0xBEEF);
    let st = CellState::new(before_balance as u64, 0);

    // A single-cohort (homogeneous) setField turn — the ONLY shape the single-descriptor sovereign
    // verify path legitimately receives.
    let effects = vec![Effect::SetField {
        field_idx: 0,
        value: field_val,
    }];

    let mut ledger = Ledger::new();
    let mut after_cell = producer_cell(before_balance, 0);
    assert!(after_cell.state.set_field(0, lane0_field_bytes(0xBEEF)));
    ledger.insert_cell(after_cell.clone()).unwrap();
    let before_cell = producer_cell(before_balance, 0);
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
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
    .expect("generator builds the honest homogeneous setField trace");

    // The active row (0) carries the setField selector; all later rows are NoOp pads — both admitted.
    assert_eq!(
        trace[0][sel::SET_FIELD],
        BabyBear::ONE,
        "row 0 is the active setField row"
    );
    for row in trace.iter().skip(1) {
        assert_eq!(
            row[sel::NOOP],
            BabyBear::ONE,
            "every pad row carries sel[NOOP] = 1"
        );
    }

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps).expect(
        "NO DOWNGRADE: the honest homogeneous setField turn must still prove under the gate",
    );
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .expect("NO DOWNGRADE: the honest setField proof must verify under the gate");

    eprintln!(
        "SELECTOR-GATE NO-DOWNGRADE (setField): an honest single-cohort setField turn still \
         proves+verifies green through the gated setFieldVmDescriptor2-0R24."
    );
}

/// THE ATTRIBUTION TOOTH — the selector gate, and NOTHING ELSE, refuses a foreign-selector tail row.
///
/// The two forgery arms above are TRUE but over-determined: their forged free debit also violates
/// the member's own every-row balance freeze / balance algebra and the rotated balance weld, so a
/// gate-less clone refuses them too (measured 2026-07-28) and their green says nothing about the
/// gate. This arm removes the over-determination by choosing a tail the OTHER gates admit — a
/// ZERO-amount `Transfer`, which moves no balance and so trips no balance constraint — leaving the
/// foreign `sel[TRANSFER]` on a non-pad row as the sole defect. Both poles are then forced:
///
///   * REFUSED under the committed `setFieldVmDescriptor2-0R24` (the gate bites);
///   * PROVES + VERIFIES under a clone with exactly that one gate removed (nothing else objects).
///
/// The second pole is the anti-vacuity guard AND the demonstration: the ONLY difference between the
/// accepting and the refusing run is `selectorGate SET_FIELD`, so the refusal is attributable to it.
/// It is also the concrete forgery the close was written for — a tail effect riding a single-
/// descriptor cohort proof completely unconstrained, which the LEAD-resolved sovereign verify path
/// would otherwise accept.
#[test]
fn foreign_selector_tail_is_refused_by_the_gate_alone() {
    let name = "setFieldVmDescriptor2-0R24";
    let desc = parse_vm_descriptor2(rotated_descriptor_json(name))
        .expect("setField-0 rotated descriptor parses");

    let before_balance: i64 = 100_000;
    let field_val = BabyBear::new(0xBEEF);

    let st = CellState::new(before_balance as u64, 0);
    // LEAD = setField(slot 0); TAIL = a ZERO-amount Transfer. The tail moves no balance, so every
    // balance constraint that over-determined the arms above is SATISFIED here — but the row still
    // carries `sel[TRANSFER] = 1`, `sel[NOOP] = 0`, which is exactly what the gate forbids.
    let effects = vec![
        Effect::SetField {
            field_idx: 0,
            value: field_val,
        },
        Effect::Transfer {
            amount: 0,
            direction: 0,
        },
    ];
    assert_eq!(
        rotated_descriptor_name_for_effect(&effects[0]),
        Some(name),
        "the lead effect resolves the setField-0 descriptor (the LEAD-resolution the forgery rides)"
    );

    let mut ledger = Ledger::new();
    let mut after_cell = producer_cell(before_balance, 0);
    assert!(after_cell.state.set_field(0, lane0_field_bytes(0xBEEF)));
    ledger.insert_cell(after_cell.clone()).unwrap();
    let before_cell = producer_cell(before_balance, 0);
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
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
    .expect("generator builds the setField + zero-amount-transfer trace");

    // The tail row is genuinely foreign and genuinely NOT a pad — the gate's exact trigger.
    assert_eq!(
        trace[1][sel::TRANSFER],
        BabyBear::ONE,
        "row 1 carries the foreign TRANSFER selector"
    );
    assert_eq!(
        trace[1][sel::SET_FIELD],
        BabyBear::ZERO,
        "row 1 does NOT carry the descriptor's own selector"
    );
    assert_eq!(
        trace[1][sel::NOOP],
        BabyBear::ZERO,
        "row 1 is NOT a NoOp pad — the gate body is 1·1 = 1 there"
    );

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    // POLE 1 — the committed member REFUSES.
    assert!(
        refused(&desc, &trace, &dpis, &mem_boundary, &map_heaps),
        "SOUNDNESS: a foreign-selector tail row under the setField-0 LEAD descriptor must be UNSAT"
    );

    // POLE 2 — the ANTI-VACUITY / ATTRIBUTION pole. One constraint removed, the SAME trace, and it
    // proves. If this ever reds, the refusal above stopped being the gate's and the tooth is
    // measuring something else.
    let ungated = without_selector_gate(&desc, sel::SET_FIELD);
    let proof = prove_vm_descriptor2(&ungated, &trace, &dpis, &mem_boundary, &map_heaps).expect(
        "ATTRIBUTION: with `selectorGate SET_FIELD` — and only that — removed, the SAME trace MUST \
         prove; otherwise POLE 1 is some other constraint refusing and this tooth is vacuous",
    );
    verify_vm_descriptor2(&ungated, &proof, &dpis).expect(
        "ATTRIBUTION: the gate-less proof MUST verify — this is precisely the accept the gate closes",
    );

    eprintln!(
        "SELECTOR-GATE ATTRIBUTION (setField): a foreign-selector tail row is UNSAT under \
         setFieldVmDescriptor2-0R24 and PROVES+VERIFIES with that one gate removed — the refusal \
         is the gate's, not an over-determined side effect."
    );
}
