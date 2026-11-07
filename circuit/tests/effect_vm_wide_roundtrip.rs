//! # THE FAITHFUL 8-FELT WIDE ROUNDTRIPS — the cohort FANNED OUT past slice-1's transfer.
//!
//! Slice 1 proved ONE real `prove/verify_vm_descriptor2` wide roundtrip (transfer, width 816 / PI 62)
//! in `effect_vm_rotation_flip.rs`. THIS file fans the wide producers out to the rest of the
//! emit-source cohort, one real wide prove+verify roundtrip per distinct PRODUCER SHAPE:
//!
//!   * **transfer-shape** (burn) — the bare-46-PI cohort, wide member width 816 / PI 62, the same
//!     carrier shape as transfer (`generate_rotated_transfer_shape_wide`).
//!   * **grow-gate noteSpend** — limb-26 nullifier accumulator, wide width 816 / PI 63
//!     (`generate_rotated_note_spend_wide`).
//!   * **grow-gate noteCreate** — limb-27 commitments accumulator, wide width 816 / PI 63
//!     (`generate_rotated_note_create_wide`).
//!   * **grow-gate createCell** — limb-0 accounts accumulator, wide width 816 / PI 63
//!     (`generate_rotated_create_cell_wide`).
//!
//! PLUS the **EXECUTOR ANCHORING differential** (the wide analog of slice-1's G3 cell≡circuit check):
//! the wide producer's 8-felt commit (the BEFORE commit-carrier columns) byte-equals
//! `dregg_cell::commitment::compute_canonical_state_commitment_v9_felt8` for the live cell — so the
//! deployed executor (after the eventual flip) can anchor the 8 wide PIs to the trusted cell.
//!
//! ADDITIVE: the live 1-felt path / TSV / VK / executor are UNTOUCHED. The wide descriptors come from
//! the verified Lean `CapOpenEmit.v3RegistryCapOpenWide` (`WIDE_REGISTRY_STAGED_TSV`). Gated on
//! `prover`. SLOW.

// (formerly `#![cfg(feature = "prover")]` — that dregg-circuit feature is GONE; the
// descriptor-level prove/verify (`prove_vm_descriptor2`/`verify_vm_descriptor2`) is
// now unconditional in dregg-circuit, so this test compiles + runs by default.)

// ⓘ The `V9RotationContext` / `compute_canonical_state_commitment_v9_felt8` imports are GONE: the
// executor-anchoring differential reaches both through `rw::SovereignTurnCtx`, which is the only
// object in this file that names an accumulator root — and it names none of them to its callers.
use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    DFA_RC_LEN, ROT_PI_COUNT, RotatedBlockWitness, SET_FIELD_DYN_HOST_WIDTH, WIDE_COMMIT_CARRIER,
    WIDE_NUM_CARRIERS, empty_caveat_manifest, generate_rotated_create_cell_wide,
    generate_rotated_create_from_factory_wide, generate_rotated_note_create_wide,
    generate_rotated_note_spend_wide, generate_rotated_set_field_dyn_wide,
    generate_rotated_spawn_wide, generate_rotated_transfer_shape_wide,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
use dregg_turn::rotation_witness as rw;

/// Resolve a wide descriptor JSON from the wide registry TSV by member name (key column).
fn wide_json(name: &str) -> &'static str {
    WIDE_REGISTRY_STAGED_TSV
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
        .unwrap_or_else(|| panic!("{name} not in WIDE_REGISTRY_STAGED_TSV"))
}

fn wide_desc(name: &str) -> EffectVmDescriptor2 {
    parse_vm_descriptor2(wide_json(name)).unwrap_or_else(|e| panic!("{name} wide parses: {e}"))
}

/// Total columns the E1 deletion (Epoch-1 SECOND flag-day) drops for a wide member, summed from the
/// Lean-emitted single source `E1_COMPACT_TABLE` — exactly what `compact_e1_columns` drains.
fn e1_deleted_cols(key: &str) -> usize {
    dregg_circuit::effect_vm::e1_compact_generated::E1_COMPACT_TABLE
        .iter()
        .find(|(k, _)| *k == key)
        .map(|(_, iv)| iv.iter().map(|(a, b)| b - a).sum())
        .unwrap_or(0)
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
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
}

/// The columns of the BEFORE 8-felt commit carrier (carrier `WIDE_COMMIT_CARRIER`): the 8 felts the
/// wide BEFORE PIs publish on the first row. The carrier base is the HOST width (`= wide width −
/// 2·8·WIDE_NUM_CARRIERS`, where `append_wide_carriers` lays `cb_before` — the v12 carrier-material
/// widening grew `NUM_PRE_LIMBS` 88→112, so the per-block chain is 38 carriers = 304 cols, appendix
/// 608, no longer 480), which is `WIDE_BEFORE_CBASE` for the bare cohort but WIDER for the §J′
/// insert-shaped grow-gate hosts (the heap-open READ appendix). Derive it from the trace so both
/// shapes read right.
fn before_commit_8(trace: &[Vec<BabyBear>]) -> [BabyBear; 8] {
    let host_width = trace[0].len() - 2 * 8 * WIDE_NUM_CARRIERS;
    let base = host_width + 8 * WIDE_COMMIT_CARRIER;
    core::array::from_fn(|j| trace[0][base + j])
}

/// The wide member's wide-PI offset (where the 16 wide PIs START): the base PI count. Every deployed
/// member is `withDfaRcPins`-wrapped (the 4 dsl rc PIs ride LAST-pre-wide, after every per-effect
/// extra pin), so: transfer-shape = `ROT_PI_COUNT + DFA_RC_LEN` = 50; the grow-gate families carry
/// the extra grow pin PI[46] (= 51); factory additionally carries the 16 STEP-3 carrier-octet pins
/// (child_vk8 PI 47..54 + contract_hash8 PI 55..62) between the grow pin and the rc tail (= 67).
/// Matches the committed descriptor `pi_binding` order in `rotation-wide-registry-staged.tsv`.
fn assert_roundtrip(
    name: &str,
    desc: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    dpis: &[BabyBear],
    map_heaps: &[Vec<HeapLeaf>],
    wide_pi_base: usize,
) {
    // The descriptor (from the Lean-verified wide-registry TSV) is the authoritative width pin; the
    // insert-shaped grow-gate members (§J′ `effAccumInsertV3` hosts) are legitimately WIDER than the bare
    // cohort `WIDE_WIDTH` (they carry the heap-open READ appendix), exactly as heapWrite's after-spine
    // host is. So we pin the trace against the DESCRIPTOR width, not the bare-cohort constant.
    //
    // THE GENTIAN WIDE FLAG-DAY: a refuse-welded cohort member's descriptor is 3·REFUSE_STRIDE (48)
    // wider than the producer's raw wide trace — the capacity-floor refuse aux columns are PROVE-time
    // filled (`fill_refuse_aux`), NOT producer-emitted, exactly as the deployed prove wrapper does. Grow
    // + fill so the roundtrip proves the FULL welded member (an honest non-declaring turn decodes
    // `floor = 0`, so the refuse is inert and the member still proves + verifies — completeness).
    let mut t: Vec<Vec<BabyBear>> = trace.to_vec();
    if desc.trace_width > t[0].len() {
        for row in &mut t {
            row.resize(desc.trace_width, BabyBear::ZERO);
            dregg_circuit::effect_vm::bare_floor_refuse_weld::fill_refuse_aux(desc, row);
        }
    }
    assert_eq!(
        desc.trace_width,
        t[0].len(),
        "{name}: descriptor width matches (welded) trace"
    );
    assert_eq!(
        dpis.len(),
        wide_pi_base + 16,
        "{name}: base {wide_pi_base} PIs (incl. the {DFA_RC_LEN} dsl rc PIs riding last-pre-wide \
         after every per-effect extra pin — the rc-emit wrap) + 16 wide PIs"
    );
    assert_eq!(
        desc.public_input_count,
        dpis.len(),
        "{name}: descriptor PI count matches"
    );

    // The 8 BEFORE wide PIs (at wide_pi_base..+8) equal the BEFORE commit-carrier columns on row 0.
    // Read from the RAW (pre-refuse) trace: `before_commit_8` derives the carrier base as
    // `width − 2·8·WIDE_NUM_CARRIERS` (the carriers are the last `WIDE_CARRIER_APPENDIX` = 992
    // columns of the WIDE member — 960 before the nine-lane epoch); the
    // gentian refuse aux rides PAST them, so growing the trace would shift that derived base.
    let commit = before_commit_8(trace);
    for j in 0..8 {
        assert_eq!(
            dpis[wide_pi_base + j],
            commit[j],
            "{name}: wide PI {} = BEFORE 8-felt commit felt {j}",
            wide_pi_base + j
        );
    }

    let mem_boundary = MemBoundaryWitness::default();
    let proof = prove_vm_descriptor2(desc, &t, dpis, &mem_boundary, map_heaps)
        .unwrap_or_else(|e| panic!("{name}: WIDE proof must prove (816): {e}"));
    verify_vm_descriptor2(desc, &proof, dpis)
        .unwrap_or_else(|e| panic!("{name}: WIDE proof must verify: {e}"));
    eprintln!("WIDE {name}: PROVED + VERIFIED at width 816 (faithful 8-felt commit).");
}

/// **THE EXECUTOR-ANCHORING differential (wide analog of slice-1's G3 cell≡circuit check).** The
/// CELL's chip-faithful 8-felt commit — `wire_commit_8_chip` over the cell's own
/// `compute_rotated_pre_limbs(cell, ctx)` + iroot — byte-equals the CIRCUIT's published BEFORE wide
/// commit carrier, so the deployed executor (after the flip) can anchor the 8 wide PIs to the trusted
/// cell. `wire_commit_8_chip` is the byte-twin of the circuit's `fill_wide_block` (the arity-tagged
/// chip chain the wide carriers are filled with) — NOT the plain `single_perm_compress`-based
/// `wire_commit_8` the cell's `compute_canonical_state_commitment_v9_felt8` currently delegates to,
/// which DIVERGES (no chip arity tag). This differential is the spec the cell-side cutover must meet:
/// the flip repoints `_felt8` onto the chip-faithful chain so the cell anchors the deployed circuit.
/// ⚑ **THIS ANCHOR USED TO HAND-BUILD ITS OWN CONTEXT, AND IT WAS ASYMMETRIC AT HEAD.** The
/// `revoked_root` slot carried `heap_root::empty_heap_root_8()` while the PRODUCER beside it
/// (`rw::produce` in the caller) was handed `empty_revoked_root_8()`. Those were one value until
/// `b20a2c50a` rebuilt `RevokedSet` as an exact tagged-linked-leaf (`FRI2`) tree; after it the
/// cell side committed a DIFFERENT revocation set than the trace carries, which is exactly the
/// producer-vs-check asymmetry that classifies as a defect rather than an arbitrary value. It takes
/// `rw::SovereignTurnCtx` now — the same object the witnesses are minted from, with no root to name.
fn assert_executor_anchor(
    name: &str,
    cell: &Cell,
    ctx: &rw::SovereignTurnCtx,
    trace: &[Vec<BabyBear>],
) {
    // The cell's OWN pre_limbs (computed from its RecordKernelState + turn ctx, NOT the producer's
    // — the independent path the executor takes), through the CHIP-FAITHFUL wide chain.
    let cell_pre = ctx.pre_limbs(cell);
    let cell_felt8 =
        dregg_circuit::poseidon2::wire_commit_8_chip(&cell_pre, ctx.iroot().limbs()[0]);
    let circuit_carrier12 = before_commit_8(trace);
    assert_eq!(
        cell_felt8, circuit_carrier12,
        "{name}: cell chip-faithful 8-felt commit == circuit wide commit carrier (executor anchoring)"
    );
    // and it is genuinely 8 felts (NOT a 1-felt lane0 squeeze padded with zeros): at least one of
    // the felts 1..8 is non-zero for a field-bearing authority-carrying cell.
    assert!(
        circuit_carrier12[1..].iter().any(|f| *f != BabyBear::ZERO),
        "{name}: the wide commit is genuinely 8-felt-wide (lanes 1..8 not all zero)"
    );
    // POST-FLIP: the cell's `compute_canonical_state_commitment_v9_felt8` is REPOINTED (under
    // `prover`) to the CHIP chain (`wire_commit_8_chip`), so it now EQUALS the deployed circuit
    // carrier — the executor-anchoring cutover landed. (Feature unification arms `dregg-cell/prover`
    // here via `dregg-turn`.)
    let cell_felt8_deployed = ctx.commitment_felt8(cell);
    assert_eq!(
        cell_felt8_deployed, circuit_carrier12,
        "{name}: the cell `_felt8` is repointed to the chip chain and MATCHES the deployed circuit \
         carrier — the cell-side flip cutover is complete"
    );
    eprintln!(
        "WIDE {name}: executor-anchoring differential holds (cell chip-8-felt ≡ circuit commit carrier; \
         the cell `_felt8` is repointed to wire_commit_8_chip — the flip cutover is complete)."
    );
}

/// **THE EXECUTOR-ANCHORING differential for a GROW-GATE family.** The grow-gate generators OVERRIDE
/// a root limb (26 nullifier / 27 commitments / 0 cells) with the turn's openable accumulator root,
/// then recompute the block commit — so the BEFORE carrier binds the GROWN-set limbs, not the cell's
/// bare `compute_rotated_pre_limbs` (which would `hash_bytes` a [0;32] root). The executor anchors
/// the published 8-felt commit against the TRUSTED before-state limbs the kernel supplies (incl. the
/// turn's before-set root): here we read the BEFORE block's own limbs off the row (the trusted limbs
/// the executor holds) and assert `wire_commit_8_chip(limbs, iroot) == commit carrier` — the SAME chip
/// primitive the cell-side flip uses. This proves the executor's anchoring primitive reproduces the
/// circuit's published wide commit for the grow-gate shape. The plain `wire_commit_8` still DIVERGES.
fn assert_executor_anchor_grow_gate(name: &str, trace: &[Vec<BabyBear>]) {
    use dregg_circuit::effect_vm::trace_rotated::{B_IROOT, BEFORE_BASE, NUM_PRE_LIMBS};
    // E1 compaction (`compact_e1_columns`) deletes the dead v1-face aux band that sits BELOW
    // `BEFORE_BASE`, so the whole BEFORE block (its `NUM_PRE_LIMBS` pre-limbs + iroot, which S2 leaves
    // intact — S2 deletes only bands ABOVE `BEFORE_BASE`) is shifted DOWN by the count of E1-killed
    // columns strictly below `BEFORE_BASE`. Read the block at its POST-E1 base, derived from the
    // Lean-emitted single-source kill-set (`E1_COMPACT_TABLE`) — never a hardcoded pre-compaction base.
    let e1_shift: usize = dregg_circuit::effect_vm::e1_compact_generated::E1_COMPACT_TABLE
        .iter()
        .find(|(k, _)| *k == name)
        .map(|(_, iv)| {
            iv.iter()
                .filter(|(_, b)| *b <= BEFORE_BASE)
                .map(|(a, b)| b - a)
                .sum()
        })
        .unwrap_or(0);
    let base = BEFORE_BASE - e1_shift;
    // The NUM_PRE_LIMBS BEFORE pre-iroot limbs + iroot the kernel-trusted before-state supplies (the row's own
    // BEFORE block, with the grown-set root override already applied by the grow-gate generator).
    let before_limbs: Vec<BabyBear> = (0..NUM_PRE_LIMBS).map(|j| trace[0][base + j]).collect();
    let before_iroot = trace[0][base + B_IROOT];
    let anchored = dregg_circuit::poseidon2::wire_commit_8_chip(&before_limbs, before_iroot);
    let circuit_carrier12 = before_commit_8(trace);
    assert_eq!(
        anchored, circuit_carrier12,
        "{name}: wire_commit_8_chip(trusted before-limbs) == circuit wide commit carrier (grow-gate \
         executor anchoring — the published 8-felt commit binds the grown-set limbs)"
    );
    assert!(
        circuit_carrier12[1..].iter().any(|f| *f != BabyBear::ZERO),
        "{name}: the wide commit is genuinely 8-felt-wide (lanes 1..8 not all zero)"
    );
    // the plain `single_perm_compress` chain DIVERGES from the chip chain the circuit publishes.
    let plain = dregg_circuit::poseidon2::wire_commit_8(&before_limbs, before_iroot);
    assert_ne!(
        plain, circuit_carrier12,
        "{name}: the plain wire_commit_8 chain DIVERGES from the deployed circuit carrier — the \
         executor anchors via wire_commit_8_chip"
    );
    eprintln!(
        "WIDE {name}: grow-gate executor-anchoring holds (wire_commit_8_chip(trusted before-limbs) ≡ \
         circuit carrier-12; plain chain DIVERGES — flagged for the flip cutover)."
    );
}

/// **TRANSFER-SHAPE (burn) wide roundtrip.** Burn carries the bare 46-PI vector exactly as transfer;
/// its wide member is the SAME carrier shape (816 / PI 62). PROVES + VERIFIES + executor-anchors.
#[test]
fn wide_burn_transfer_shape_proves_verifies_and_executor_anchors() {
    let name = "burnVmDescriptor2R24";
    let desc = wide_desc(name);

    let before_balance: i64 = 80_000;
    let amount: u64 = 30;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Burn {
        target_hash: [BabyBear::ZERO; 8],
        amount_lo: BabyBear::new(amount as u32),
        amount_full: amount,
    }];

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance - amount as i64, 0);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
    // THE SHARED BINDING — the witnesses AND `assert_executor_anchor`'s check read one context, so
    // the producer-vs-check asymmetry the `revoked_root` slot carried has nowhere to live.
    let turn_ctx = rw::sovereign_turn_ctx(&ledger, &receipt_log, Default::default());
    let before_w = turn_ctx.witness(&before_cell);
    let after_w = turn_ctx.witness(&after_cell);

    // The deployed burn member is the AVAIL-hardened crown row: generate at ITS pad.
    let burn_pad =
        dregg_circuit::effect_vm::trace_rotated::avail_pad_for_descriptor_name(&desc.name);
    let (trace, dpis) =
        dregg_circuit::effect_vm::trace_rotated::generate_rotated_transfer_shape_wide_avail(
            burn_pad,
            &st,
            &effects,
            &bridge(&before_w),
            &bridge(&after_w),
            &empty_caveat_manifest(),
        )
        .expect("wide burn producer");
    // THE S2 DELETION (Epoch 1): the raw family trace is old-geometry; drop the dead
    // chain columns so the rows match the committed compact member.
    let mut trace = trace;
    dregg_circuit::effect_vm::trace_rotated::compact_s2_columns(&mut trace, "burnVmDescriptor2R24")
        .expect("S2 compaction must succeed on the raw wide trace");
    dregg_circuit::effect_vm::trace_rotated::compact_e1_columns(&mut trace, "burnVmDescriptor2R24")
        .expect("E1 compaction must succeed on the S2-compacted wide trace");
    // wide-PI base = ROT_PI_COUNT (46) + DFA_RC_LEN (4 dsl rc, last-pre-wide) = 50; total 66
    // = the committed burnVmDescriptor2R24 public_input_count (wide pins at PI 50..65).
    assert_roundtrip(name, &desc, &trace, &dpis, &[], ROT_PI_COUNT + DFA_RC_LEN);
    assert_executor_anchor(name, &before_cell, &turn_ctx, &trace);
}

/// **setFieldDyn wide roundtrip — the DYNAMIC overflow-field write PROVES (the residual CLOSED).**
///
/// The dynamic `SetField` (`field_idx >= 8`) routes to `setFieldDynVmDescriptor2R24`, a DISTINCT
/// V1Face geometry (host [`SET_FIELD_DYN_HOST_WIDTH`], wide member `+ 2·8·WIDE_NUM_CARRIERS`) the
/// standard generator cannot produce (it panics on `field_idx >= 8` and lays the `GRAD_ROT_WIDTH`
/// host). `generate_rotated_set_field_dyn_wide` builds it from scratch: the Blum write+read pair
/// (`addr = value = col 69`, `prev_value = col 70`, `prev_serial = col 74`, `readback = col 75`)
/// over a `MemBoundaryWitness`, the fields-root weld (col 275 == col 68), and the fifth pin
/// (→ PI[46]). This PROVES + light-client VERIFIES — no `catch_unwind`. The forge pole (a tampered
/// readback) is exercised in `vk_epoch_misc`.
#[test]
fn wide_set_field_dyn_dynamic_overflow_proves_and_verifies() {
    let name = "setFieldDynVmDescriptor2R24";
    let desc = wide_desc(name);
    assert_eq!(
        desc.trace_width,
        SET_FIELD_DYN_HOST_WIDTH + 2 * 8 * WIDE_NUM_CARRIERS + 48
            - dregg_circuit::effect_vm::s2_compact_generated::S2_DELETED_COLS
            - e1_deleted_cols(name),
        "setFieldDyn wide width = the committed narrow V1Face host + the wide-carrier appendix \
         (960) + the gentian refuse widening (48) MINUS the deleted S2 stratum (960 — the two \
         rotated 1-felt chains + their chip lanes, Epoch 1) MINUS the E1 dead v1-face bands \
         (Epoch-1 SECOND flag-day, per-member from E1_COMPACT_TABLE)"
    );
    assert_eq!(
        desc.public_input_count,
        ROT_PI_COUNT + 1 + DFA_RC_LEN + 16,
        "setFieldDyn wide carries {ROT_PI_COUNT} rotated + 1 fifth-pin + {DFA_RC_LEN} dsl rc base \
         PIs + 16 wide PIs"
    );

    let balance: i64 = 50_000;
    let st = CellState::new(balance as u64, 0);
    let mut ledger = Ledger::new();
    // A SetField bumps the nonce; the after-cell carries nonce 1.
    let before_cell = producer_cell(balance, 0);
    let after_cell = producer_cell(balance, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[5u8; 32]];
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

    // slot 3 (the overflow-memory address 0..7), previous value 0 at that address.
    let slot = 3u32;
    let prev_value = BabyBear::new(0);
    let (trace, dpis, mem_boundary) = generate_rotated_set_field_dyn_wide(
        &st,
        &bridge(&before_w),
        &bridge(&after_w),
        &empty_caveat_manifest(),
        slot,
        prev_value,
    )
    .expect("wide setFieldDyn producer");
    // THE S2 DELETION (Epoch 1): the raw family trace is old-geometry; drop the dead
    // chain columns so the rows match the committed compact member.
    let mut trace = trace;
    dregg_circuit::effect_vm::trace_rotated::compact_s2_columns(
        &mut trace,
        "setFieldDynVmDescriptor2R24",
    )
    .expect("S2 compaction must succeed on the raw wide trace");
    dregg_circuit::effect_vm::trace_rotated::compact_e1_columns(
        &mut trace,
        "setFieldDynVmDescriptor2R24",
    )
    .expect("E1 compaction must succeed on the S2-compacted wide trace");
    // Grow + fill the gentian refuse aux (prove-time filled; setFieldDyn declares no capacity ⟹ floor=0).
    let mut trace = trace;
    if desc.trace_width > trace[0].len() {
        for row in &mut trace {
            row.resize(desc.trace_width, BabyBear::ZERO);
            dregg_circuit::effect_vm::bare_floor_refuse_weld::fill_refuse_aux(&desc, row);
        }
    }
    assert_eq!(
        trace[0].len(),
        desc.trace_width,
        "setFieldDyn wide trace width matches descriptor"
    );
    assert_eq!(
        dpis.len(),
        desc.public_input_count,
        "setFieldDyn wide PI count matches descriptor"
    );

    let proof =
        prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &[]).unwrap_or_else(|e| {
            panic!(
                "setFieldDyn wide proof must prove ({}): {e}",
                desc.trace_width
            )
        });
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .unwrap_or_else(|e| panic!("setFieldDyn wide proof must verify: {e}"));
    eprintln!(
        "WIDE setFieldDyn: the DYNAMIC overflow-field write PROVED + VERIFIED at width {} (the Blum \
         write→read transport over the 1553-wide V1Face host geometry — the \
         missing-generator residual is CLOSED).",
        desc.trace_width
    );
}

/// **NOTESPEND grow-gate wide roundtrip.** The nullifier accumulator (limb 26) grow-gate; the extra
/// nullifier PI[46] + the 4 dsl rc PIs before the 16 wide PIs. PROVES + VERIFIES + anchors.
#[test]
fn wide_note_spend_grow_gate_proves_verifies_and_executor_anchors() {
    let name = "noteSpendVmDescriptor2R24";
    let desc = wide_desc(name);

    let before_balance: i64 = 90_000;
    let value: u64 = 500;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::NoteSpend {
        nullifier: BabyBear::new(0xBEEF),
        value,
    }];

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance + value as i64, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[7u8; 32]];
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

    let before_nullifiers = vec![
        HeapLeaf::entry(BabyBear::new(0x1111), BabyBear::new(1)),
        HeapLeaf::entry(BabyBear::new(0x2222), BabyBear::new(1)),
    ];
    let (trace, dpis, map_heaps) = generate_rotated_note_spend_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &empty_caveat_manifest(),
        &before_nullifiers,
        // The limb-37 `spendAncestorFreshOp`: no delegated capability; the block witnesses above
        // carry `empty_revoked_root_8()`, so the empty set is the committed revoked set.
        &dregg_circuit::effect_vm::trace_rotated::SpendRevocationWitness::undelegated(&[]),
    )
    .expect("wide noteSpend producer");
    // THE S2 DELETION (Epoch 1): the raw family trace is old-geometry; drop the dead
    // chain columns so the rows match the committed compact member.
    let mut trace = trace;
    dregg_circuit::effect_vm::trace_rotated::compact_s2_columns(
        &mut trace,
        "noteSpendVmDescriptor2R24",
    )
    .expect("S2 compaction must succeed on the raw wide trace");
    dregg_circuit::effect_vm::trace_rotated::compact_e1_columns(
        &mut trace,
        "noteSpendVmDescriptor2R24",
    )
    .expect("E1 compaction must succeed on the S2-compacted wide trace");
    // wide-PI base = ROT_PI_COUNT (46) + 1 (nullifier pin PI[46]) + DFA_RC_LEN (4 dsl rc, PI 47..50)
    // = 51; total 67 — the wide twin of the LIVE noteSpendVmDescriptor2R24 (51 PIs, rc-wrapped).
    // NOTE: the committed wide row currently says 63 (EmitWideRegistryProbe.lean builds the §J′
    // insert host from the UNWRAPPED noteSpendV3, dropping the withDfaRcPins tail the live member
    // carries) — a wide-registry emit gap, not a fixture number to copy.
    assert_roundtrip(
        name,
        &desc,
        &trace,
        &dpis,
        &map_heaps,
        ROT_PI_COUNT + 1 + DFA_RC_LEN,
    );
    assert_executor_anchor_grow_gate(name, &trace);
}

/// **NOTECREATE grow-gate wide roundtrip.** The commitments accumulator (limb 27) grow-gate; the
/// extra commitment PI[46] + the 4 dsl rc PIs before the 16 wide PIs. PROVES + VERIFIES + anchors.
#[test]
fn wide_note_create_grow_gate_proves_verifies_and_executor_anchors() {
    let name = "noteCreateVmDescriptor2R24";
    let desc = wide_desc(name);

    let before_balance: i64 = 60_000;
    let value: u64 = 250;
    let st = CellState::new(before_balance as u64, 0);
    let cm = BabyBear::new(0xC0FFEE);
    let effects = vec![Effect::NoteCreate {
        commitment: cm,
        value,
    }];

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance + value as i64, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[11u8; 32]];
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

    let before_commitments = vec![
        HeapLeaf::entry(BabyBear::new(0x111), BabyBear::new(1)),
        HeapLeaf::entry(BabyBear::new(0x222), BabyBear::new(1)),
    ];
    let (trace, dpis, map_heaps) = generate_rotated_note_create_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &empty_caveat_manifest(),
        &before_commitments,
    )
    .expect("wide noteCreate producer");
    // THE S2 DELETION (Epoch 1): the raw family trace is old-geometry; drop the dead
    // chain columns so the rows match the committed compact member.
    let mut trace = trace;
    dregg_circuit::effect_vm::trace_rotated::compact_s2_columns(
        &mut trace,
        "noteCreateVmDescriptor2R24",
    )
    .expect("S2 compaction must succeed on the raw wide trace");
    dregg_circuit::effect_vm::trace_rotated::compact_e1_columns(
        &mut trace,
        "noteCreateVmDescriptor2R24",
    )
    .expect("E1 compaction must succeed on the S2-compacted wide trace");
    // wide-PI base = ROT_PI_COUNT (46) + 1 (commitment pin PI[46]) + DFA_RC_LEN (4 dsl rc) = 51;
    // total 67 — the wide twin of the LIVE noteCreateVmDescriptor2R24 (51 PIs, rc-wrapped). The
    // committed wide row currently says 63 (the unwrapped-base wide-registry emit gap; see the
    // noteSpend note above).
    assert_roundtrip(
        name,
        &desc,
        &trace,
        &dpis,
        &map_heaps,
        ROT_PI_COUNT + 1 + DFA_RC_LEN,
    );
    assert_executor_anchor_grow_gate(name, &trace);
}

/// **CREATECELL grow-gate wide roundtrip.** The accounts accumulator (limb 0) grow-gate; the extra
/// new-cell-key PI[46] + the 4 dsl rc PIs before the 16 wide PIs. PROVES + VERIFIES + anchors.
#[test]
fn wide_create_cell_grow_gate_proves_verifies_and_executor_anchors() {
    let name = "createCellVmDescriptor2R24";
    let desc = wide_desc(name);

    let before_balance: i64 = 40_000;
    let st = CellState::new(before_balance as u64, 0);
    let new_cell_id = BabyBear::new(0xCE11);
    let effects = vec![Effect::CreateCell {
        create_hash: [new_cell_id; 8],
    }];

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[5u8; 32]];
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

    let before_accounts = vec![
        HeapLeaf::entry(BabyBear::new(0xAA01), BabyBear::new(0xAA01)),
        HeapLeaf::entry(BabyBear::new(0xAA02), BabyBear::new(0xAA02)),
    ];
    let (trace, dpis, map_heaps) = generate_rotated_create_cell_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &empty_caveat_manifest(),
        &before_accounts,
    )
    .expect("wide createCell producer");
    // THE S2 DELETION (Epoch 1): the raw family trace is old-geometry; drop the dead
    // chain columns so the rows match the committed compact member.
    let mut trace = trace;
    dregg_circuit::effect_vm::trace_rotated::compact_s2_columns(
        &mut trace,
        "createCellVmDescriptor2R24",
    )
    .expect("S2 compaction must succeed on the raw wide trace");
    dregg_circuit::effect_vm::trace_rotated::compact_e1_columns(
        &mut trace,
        "createCellVmDescriptor2R24",
    )
    .expect("E1 compaction must succeed on the S2-compacted wide trace");
    // wide-PI base = ROT_PI_COUNT (46) + 1 (new-cell-key pin PI[46]) + DFA_RC_LEN (4 dsl rc) = 51;
    // total 67 — the wide twin of the LIVE createCellVmDescriptor2R24 (51 PIs, rc-wrapped). The
    // committed wide row currently says 63 (the unwrapped-base wide-registry emit gap; see the
    // noteSpend note above).
    assert_roundtrip(
        name,
        &desc,
        &trace,
        &dpis,
        &map_heaps,
        ROT_PI_COUNT + 1 + DFA_RC_LEN,
    );
    assert_executor_anchor_grow_gate(name, &trace);
}

/// The shared birth-leg producer witnesses (a non-empty BEFORE accounts set distinct from the new-cell
/// key, so the `.absent` no-collision precondition has a bracketing witness). Mirrors the createCell
/// wide setup; the only per-effect difference is the lead effect + its new-cell key column.
fn birth_witnesses() -> (
    CellState,
    Ledger,
    rw::RotationWitness,
    rw::RotationWitness,
    Vec<HeapLeaf>,
) {
    let before_balance: i64 = 40_000;
    let st = CellState::new(before_balance as u64, 0);
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[5u8; 32]];
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
    let before_accounts = vec![
        HeapLeaf::entry(BabyBear::new(0xAA01), BabyBear::new(0xAA01)),
        HeapLeaf::entry(BabyBear::new(0xAA02), BabyBear::new(0xAA02)),
    ];
    (st, ledger, before_w, after_w, before_accounts)
}

/// **CREATECELLFROMFACTORY grow-gate wide roundtrip.** The factory twin of the createCell birth leg:
/// the born child's key rides `param1` (CHILD_VK_DERIVED), and the SAME accounts-set grow-gate (limb 0)
/// forces the genuine sorted insert against the threaded BEFORE accounts leaf set. The honest trace
/// PROVES + VERIFIES against the deployed wide `factoryVmDescriptor2R24`; the grow-gate executor anchor
/// holds.
#[test]
fn wide_factory_grow_gate_proves_verifies_and_executor_anchors() {
    let name = "factoryVmDescriptor2R24";
    let desc = wide_desc(name);
    let (st, _ledger, before_w, after_w, before_accounts) = birth_witnesses();
    let effects = vec![Effect::CreateCellFromFactory {
        factory_vk: BabyBear::new(0xFAC0),
        child_vk_derived: BabyBear::new(0xC417),
    }];
    let (trace, dpis, map_heaps) = generate_rotated_create_from_factory_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &empty_caveat_manifest(),
        &before_accounts,
    )
    .expect("wide factory producer");
    // THE S2 DELETION (Epoch 1): the raw family trace is old-geometry; drop the dead
    // chain columns so the rows match the committed compact member.
    let mut trace = trace;
    dregg_circuit::effect_vm::trace_rotated::compact_s2_columns(
        &mut trace,
        "factoryVmDescriptor2R24",
    )
    .expect("S2 compaction must succeed on the raw wide trace");
    dregg_circuit::effect_vm::trace_rotated::compact_e1_columns(
        &mut trace,
        "factoryVmDescriptor2R24",
    )
    .expect("E1 compaction must succeed on the S2-compacted wide trace");
    // wide-PI base = ROT_PI_COUNT (46) + 1 (grow pin PI[46]) + 16 (STEP-3 carrier-octet pins:
    // child_vk8 PI 47..54 + contract_hash8 PI 55..62) + DFA_RC_LEN (4 dsl rc, PI 63..66) = 67;
    // total 83 = the committed factoryVmDescriptor2R24 public_input_count (wide pins at PI 67..82).
    assert_roundtrip(
        name,
        &desc,
        &trace,
        &dpis,
        &map_heaps,
        ROT_PI_COUNT + 1 + 16 + DFA_RC_LEN,
    );
    assert_executor_anchor_grow_gate(name, &trace);
}

/// **SPAWN (birth/accounts-grow leg) grow-gate wide roundtrip.** Spawn's wide descriptor
/// (`spawnVmDescriptor2R24`) carries the accounts-set `.absent`+`.insert` grow-gate (limb 0 — the born
/// child id grown into the cells set) and NO cap-tree map_op (the parent→child cap handoff is bound by
/// the cap-open `spawnWriteCapOpenVmDescriptor2R24`, a SEPARATE path). The honest trace PROVES + VERIFIES
/// against the deployed wide `spawnVmDescriptor2R24` for the accounts-birth column.
#[test]
fn wide_spawn_grow_gate_proves_verifies_and_executor_anchors() {
    let name = "spawnVmDescriptor2R24";
    let desc = wide_desc(name);
    let (st, _ledger, before_w, after_w, before_accounts) = birth_witnesses();
    let spawn_id = BabyBear::new(0x5BA1);
    let effects = vec![Effect::SpawnWithDelegation {
        spawn_hash: [spawn_id; 8],
    }];
    let (trace, dpis, map_heaps) = generate_rotated_spawn_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &empty_caveat_manifest(),
        &before_accounts,
    )
    .expect("wide spawn (accounts birth leg) producer");
    // THE S2 DELETION (Epoch 1): the raw family trace is old-geometry; drop the dead
    // chain columns so the rows match the committed compact member.
    let mut trace = trace;
    dregg_circuit::effect_vm::trace_rotated::compact_s2_columns(
        &mut trace,
        "spawnVmDescriptor2R24",
    )
    .expect("S2 compaction must succeed on the raw wide trace");
    dregg_circuit::effect_vm::trace_rotated::compact_e1_columns(
        &mut trace,
        "spawnVmDescriptor2R24",
    )
    .expect("E1 compaction must succeed on the S2-compacted wide trace");
    // wide-PI base = ROT_PI_COUNT (46) + 1 (grow pin PI[46]) + DFA_RC_LEN (4 dsl rc, PI 47..50)
    // = 51; total 67 = the committed spawnVmDescriptor2R24 public_input_count (wide pins at 51..66).
    assert_roundtrip(
        name,
        &desc,
        &trace,
        &dpis,
        &map_heaps,
        ROT_PI_COUNT + 1 + DFA_RC_LEN,
    );
    assert_executor_anchor_grow_gate(name, &trace);
}

/// **The named wide wrappers REFUSE a mismatched lead effect** (fail-closed routing): the factory wide
/// wrapper rejects a createCell lead and vice-versa, so the dispatch lane cannot silently route the wrong
/// new-cell key column through the wrong descriptor.
#[test]
fn wide_birth_wrappers_refuse_mismatched_lead() {
    let (st, _ledger, before_w, after_w, before_accounts) = birth_witnesses();
    let cc = vec![Effect::CreateCell {
        create_hash: [BabyBear::new(0xCE11); 8],
    }];
    assert!(
        generate_rotated_create_from_factory_wide(
            &st,
            &cc,
            &bridge(&before_w),
            &bridge(&after_w),
            &empty_caveat_manifest(),
            &before_accounts,
        )
        .is_err(),
        "factory wide wrapper must refuse a createCell lead"
    );
    assert!(
        generate_rotated_spawn_wide(
            &st,
            &cc,
            &bridge(&before_w),
            &bridge(&after_w),
            &empty_caveat_manifest(),
            &before_accounts,
        )
        .is_err(),
        "spawn wide wrapper must refuse a createCell lead"
    );
}

/// **THE GEOMETRY NO-PANIC BOUNDARY TOOTH (the wide-carrier flag-day pins).**
/// `append_wide_carriers` fills BOTH wide carrier blocks up to EXACTLY the last allocated
/// byte (flush fit) and the commitment carrier is the last one. Under the RETIRED v1 declarations
/// (`WIDE_NUM_CARRIERS = 57` / commit 56 / 912-column appendix) this very call PANICKED:
/// the 60-carrier generator overran the 912-column allocation (the AFTER block's tail
/// carriers ran to `host + 935`) and collided the BEFORE block into the AFTER base. That is why
/// the four literals below exist: they are the place a `NUM_PRE_LIMBS` drift goes red at a
/// DEFINITION rather than at a mis-sized allocation three call-frames away.
#[test]
fn wide_carrier_blocks_fill_exactly_the_allocated_appendix() {
    use dregg_circuit::descriptor_ir2::chip_absorb_all_lanes;
    use dregg_circuit::effect_vm::trace_rotated::{
        AFTER_BASE, B_IROOT, BEFORE_BASE, GRAD_ROT_WIDTH, NUM_PRE_LIMBS, WIDE_CARRIER_APPENDIX,
        WIDE_CARRIER_BLOCK_SPAN, append_wide_carriers,
    };
    // The derived flag-day geometry, RE-TYPED at the KEY NONET epoch (184 -> 187 pre-limbs,
    // `76c3f7b9b`; before that 178 -> 184 at the nine-lane epoch).
    //
    //   wide_carriers_for_limbs(n) = 1 + (n-4)/3 + (n-4)%3 + 1
    //     head + 3-limb body groups + 1-limb leftovers + the final iroot carrier
    //   n = 187: body = 183, 1 + 61 + 0 + 1 = 63   (n = 184: 1 + 60 + 0 + 1 = 62; n = 178: 60)
    //   WIDE_COMMIT_CARRIER      = WIDE_NUM_CARRIERS - 1  = 62
    //   WIDE_CARRIER_BLOCK_SPAN  = 8 * 63                 = 504
    //   WIDE_CARRIER_APPENDIX    = 2 * 504                = 1008
    //
    // The whole delta is ONE carrier: 183 is 0 mod 3, so the three new pre-limbs (the carrier
    // octets' ninth lanes, 184/185/186) form exactly one more clean 3-limb body group and leave no
    // 1-limb leftover. +1 carrier -> +8 columns per block -> +16 across the two-block appendix.
    //
    // The Lean side derives 63 INDEPENDENTLY — one carrier per emitted wide-lookup spec — and
    // agrees, at every step of the chain:
    //   `EffectVmEmitRotationWide.wideNumCarriers_eq      : wideNumCarriers      = 63`
    //   `EffectVmEmitRotationWide.wideCarrierBlockSpan_eq : wideCarrierBlockSpan = 504`
    //   `EffectVmEmitRotationWide.wideAppendixSpan_eq     : wideAppendixSpan     = 1008`
    //
    // ⚠ `assert_eq!(WIDE_NUM_CARRIERS, wide_carriers_for_limbs(NUM_PRE_LIMBS))` USED TO STAND HERE
    // and has been DELETED: `trace_rotated.rs` defines `WIDE_NUM_CARRIERS` as exactly that call, so
    // the assertion was `x == x` — true at every geometry, including a wrong one. It is the same
    // tautology the cap-open geometry block was cleaned of on the same day. The literals below CAN
    // go red; that restated definition never could.
    assert_eq!(WIDE_NUM_CARRIERS, 63, "187 pre-limbs -> 63 carriers");
    assert_eq!(WIDE_COMMIT_CARRIER, 62, "the commitment carrier is 62");
    assert_eq!(WIDE_CARRIER_BLOCK_SPAN, 504);
    assert_eq!(WIDE_CARRIER_APPENDIX, 1008);

    // A base row with recognizable limb material in both rotated blocks (limbs + iroot).
    let host_width = GRAD_ROT_WIDTH;
    let mut row = vec![BabyBear::ZERO; host_width];
    for i in 0..=B_IROOT {
        row[BEFORE_BASE + i] = BabyBear::new(1_000 + i as u32);
        row[AFTER_BASE + i] = BabyBear::new(2_000 + i as u32);
    }
    let mut trace = vec![row];
    let base_pis = vec![BabyBear::ZERO; ROT_PI_COUNT + DFA_RC_LEN];
    // v1 constants make THIS call panic (index out of bounds); v2 must not.
    let dpis = append_wide_carriers(&mut trace, base_pis, host_width);
    let row = &trace[0];
    assert_eq!(
        row.len(),
        host_width + WIDE_CARRIER_APPENDIX,
        "flush allocation"
    );

    // Flush fit: the BEFORE commit carrier ends exactly at the BEFORE block's end, the AFTER
    // commit carrier exactly at the last allocated column.
    let before_commit = host_width + 8 * WIDE_COMMIT_CARRIER;
    let after_commit = host_width + WIDE_CARRIER_BLOCK_SPAN + 8 * WIDE_COMMIT_CARRIER;
    assert_eq!(before_commit + 8, host_width + WIDE_CARRIER_BLOCK_SPAN);
    assert_eq!(after_commit + 8, row.len());

    // Both blocks' LAST ALLOCATED BYTES are genuinely filled: recompute each block's chain
    // with the SAME chip-faithful derivation (an independent loop over the same shape) and
    // compare the commit carrier lane-for-lane.
    let recompute = |limb_base: usize| -> [BabyBear; 8] {
        let head = [
            row[limb_base],
            row[limb_base + 1],
            row[limb_base + 2],
            row[limb_base + 3],
        ];
        let mut d = chip_absorb_all_lanes(4, &head);
        let mut col = 4usize;
        let mut carrier = 0usize;
        while col < NUM_PRE_LIMBS {
            let mut ins = [BabyBear::ZERO; 11];
            ins[..8].copy_from_slice(&d);
            let arity = if NUM_PRE_LIMBS - col >= 3 {
                ins[8] = row[limb_base + col];
                ins[9] = row[limb_base + col + 1];
                ins[10] = row[limb_base + col + 2];
                col += 3;
                11
            } else {
                ins[8] = row[limb_base + col];
                col += 1;
                9
            };
            d = chip_absorb_all_lanes(arity, &ins);
            carrier += 1;
        }
        let mut ins = [BabyBear::ZERO; 11];
        ins[..8].copy_from_slice(&d);
        ins[8] = row[limb_base + B_IROOT];
        carrier += 1;
        assert_eq!(carrier, WIDE_COMMIT_CARRIER, "the chain ends on carrier 61");
        chip_absorb_all_lanes(11, &ins)
    };
    assert_eq!(
        &row[before_commit..before_commit + 8],
        &recompute(BEFORE_BASE)
    );
    assert_eq!(&row[after_commit..after_commit + 8], &recompute(AFTER_BASE));

    // The published 16-PI tail is exactly the two commit carriers (BEFORE first row, AFTER
    // last row), and the final allocated byte of each block is FILLED (not dead slack).
    let n = dpis.len();
    assert_eq!(&dpis[n - 16..n - 8], &row[before_commit..before_commit + 8]);
    assert_eq!(&dpis[n - 8..], &row[after_commit..after_commit + 8]);
    assert_ne!(
        row[host_width + WIDE_CARRIER_BLOCK_SPAN - 1],
        BabyBear::ZERO,
        "the BEFORE block's last allocated byte is filled"
    );
    assert_ne!(
        row[row.len() - 1],
        BabyBear::ZERO,
        "the AFTER block's last allocated byte is filled"
    );
}
