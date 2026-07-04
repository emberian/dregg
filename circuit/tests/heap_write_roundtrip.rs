//! # HEAP-WRITE producer≡descriptor ROUNDTRIP + AFTER-root 8-felt binding forge.
//!
//! ## The gap under attack (R3, v13-class)
//!
//! `heapWriteVmDescriptor2R24` is the write-bearing Class-A member. Unlike the effect-dispatched
//! cohort it has NO live selector — it is reached only through the dedicated per-family producer
//! [`generate_rotated_heap_write_wide`]. R3 flagged it as the sharpest surviving v13-class gap: a
//! DISTINCT heap-splice producer, structurally pinned only, with no end-to-end prove+verify roundtrip
//! that would catch the producer silently diverging from the committed descriptor while the drift gate
//! stays green (the v13 stale-descriptor scare class).
//!
//! The staleness risk is REAL and visible: the source carries drifted geometry comments
//! (`BEFORE_BASE // 186`, `AFTER_BASE // 237`, `read_base // 815`) whose ACTUAL runtime values are
//! 188 / 415 / 1567, and a sibling structural test (`heap_write_deployed_root_forced.rs`) hard-codes a
//! STALE `new_root` lane-0 column (307) that no longer matches the committed descriptor (443). So the
//! only trustworthy check is an EXECUTED roundtrip that binds the producer's laid columns to the
//! committed descriptor's map-op columns through an actual proof.
//!
//! ## What this file pins
//!
//!  (a) ROUNDTRIP — the wide producer's trace PROVES + light-client VERIFIES against the COMMITTED
//!      `heapWriteVmDescriptor2R24` (bare-wide, 2951/20), AND the producer's written after-root columns
//!      are byte-identical to the descriptor's `.write` map-op `new_root` columns (the anti-drift
//!      catcher). Also pins the v3-live (1567/4) committed descriptor shares those columns and the
//!      truncated producer trace proves against it — closing R3's "partial on both paths".
//!  (b) AFTER-ROOT 8-FELT FORGE — forge the `.write` `new_root` completion lanes 1..7 (cols 473..479)
//!      to garbage while keeping lane 0 (col 443) honest, recompute the after block-commit + wide
//!      carriers so the trace is fully self-consistent, and run the pure LC verify. If UNSAT, the
//!      deployed `.write` map-op binds ALL EIGHT after-root felts to the genuine sorted-Merkle splice
//!      (~124-bit), not lane-0 (~31-bit).

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MapKind, MemBoundaryWitness, VmConstraint2, chip_absorb_all_lanes,
    parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    AFTER_BASE, B_STATE_COMMIT, BEFORE_BASE, HEAP_WRITE_HOST_WIDTH, RotatedBlockWitness,
    append_wide_carriers, empty_caveat_manifest, generate_rotated_heap_write_wide,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::{V3_STAGED_REGISTRY_TSV, WIDE_REGISTRY_STAGED_TSV};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_turn::rotation_witness as rw;

const KEY: &str = "heapWriteVmDescriptor2R24";

fn registry_json(tsv: &'static str, name: &str) -> &'static str {
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
        .unwrap_or_else(|| panic!("{name} not in registry"))
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

/// The `.write` map-op's `new_root` 8-felt group COLUMNS, straight off the parsed descriptor.
fn write_new_root_cols(desc: &EffectVmDescriptor2) -> Vec<usize> {
    for c in &desc.constraints {
        if let VmConstraint2::MapOp(m) = c {
            if m.op == MapKind::Write {
                return m
                    .new_root
                    .iter()
                    .map(|e| match e {
                        LeanExpr::Var(i) => *i,
                        other => panic!("new_root lane is not a Var column: {other:?}"),
                    })
                    .collect();
            }
        }
    }
    panic!("descriptor {} has no WRITE map-op", desc.name);
}

/// `true` iff prove/verify REFUSES (Err or panic) on the given trace + PIs — the LC verdict.
fn refused(
    desc: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    dpis: &[BabyBear],
    mem_boundary: &MemBoundaryWitness,
    map_heaps: &[Vec<HeapLeaf>],
) -> bool {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, dpis, mem_boundary, map_heaps)?;
        verify_vm_descriptor2(desc, &proof, dpis)
    }));
    match r {
        Err(_) => true,
        Ok(res) => res.is_err(),
    }
}

/// Build the honest wide heap-write turn (the exact fixture `wide_new_members_cover` uses), returning
/// the producer's `(trace, dpis, map_heaps)` and the recomputed heap-address the splice opens.
fn honest_heap_write() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>, Vec<Vec<HeapLeaf>>) {
    let st = CellState::new(100, 5);
    let value_full: u64 = 30;
    let effects = vec![Effect::Mint {
        value_lo: BabyBear::new(value_full as u32),
        mint_hash: BabyBear::new(0),
        value_full,
    }];
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(100, 5);
    let after_cell = producer_cell(100 + value_full as i64, 6);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[11u8; 32]];
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

    let coll = BabyBear::new(42);
    let key = BabyBear::new(7);
    let value = BabyBear::new(123);
    let mut absorb_in = [BabyBear::new(0); 11];
    absorb_in[0] = coll;
    absorb_in[1] = key;
    let addr = chip_absorb_all_lanes(2, &absorb_in)[0];
    let heap = vec![
        HeapLeaf {
            addr,
            value: BabyBear::new(9),
        },
        HeapLeaf {
            addr: BabyBear::new(999_983),
            value: BabyBear::new(1),
        },
    ];

    let (trace, dpis, map_heaps) = generate_rotated_heap_write_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &empty_caveat_manifest(),
        coll,
        key,
        value,
        &heap,
    )
    .expect("wide heap-write generation");
    (trace, dpis, map_heaps)
}

/// **(a) ROUNDTRIP + ANTI-DRIFT.** The wide producer PROVES + light-client VERIFIES against the
/// COMMITTED `heapWriteVmDescriptor2R24`, and the columns the producer laid the after heap-root group
/// into are byte-identical to the committed descriptor's `.write` map-op `new_root` columns. This is
/// the executed check the structural teeth cannot give: a producer that laid the group at the STALE
/// (188/237-based) columns while the committed descriptor moved to 188/415 would be UNSAT here.
#[test]
fn roundtrip_wide_producer_matches_committed_descriptor() {
    let wide_desc = parse_vm_descriptor2(registry_json(WIDE_REGISTRY_STAGED_TSV, KEY))
        .expect("committed bare-wide heapWriteVmDescriptor2R24 parses");
    assert_eq!(wide_desc.trace_width, 2951, "committed bare-wide width");
    assert_eq!(wide_desc.public_input_count, 20, "committed bare-wide PIs");

    let new_root_cols = write_new_root_cols(&wide_desc);
    assert_eq!(new_root_cols.len(), 8, "after-root is an 8-felt group");
    // The committed descriptor's after-root columns, grounded (probed) at the current HEAD geometry.
    assert_eq!(
        new_root_cols,
        vec![443, 473, 474, 475, 476, 477, 478, 479],
        "committed .write new_root columns (AFTER_BASE 415 + heapRootGroupCol) — the anti-drift pin"
    );
    // The producer writes the after heap-root group at AFTER_BASE(415)+28 (lane 0) and +58..64 (lanes
    // 1..7). Assert the RUNTIME constants place lane 0 exactly at the committed lane-0 column, so the
    // producer and the frozen descriptor cannot silently diverge.
    assert_eq!(
        AFTER_BASE + 28,
        new_root_cols[0],
        "producer's after heap-root lane-0 column MUST equal the committed descriptor's new_root[0]"
    );

    let (trace, dpis, map_heaps) = honest_heap_write();
    assert_eq!(
        trace[0].len(),
        wide_desc.trace_width,
        "producer width == descriptor width"
    );
    assert_eq!(
        dpis.len(),
        wide_desc.public_input_count,
        "producer PI count == descriptor PI count"
    );

    // Non-vacuity: the producer actually laid the genuine 8-felt splice root into those columns, with
    // ≥1 nonzero completion lane (so the forge below moves a genuinely bound felt).
    let honest_root: Vec<BabyBear> = new_root_cols.iter().map(|&c| trace[0][c]).collect();
    assert!(
        (1..8).any(|l| honest_root[l] != BabyBear::ZERO),
        "the genuine 8-felt after-root has ≥1 nonzero completion lane"
    );

    let mb = MemBoundaryWitness::default();
    let proof = prove_vm_descriptor2(&wide_desc, &trace, &dpis, &mb, &map_heaps)
        .expect("ROUNDTRIP: wide heap-write producer must PROVE against the committed descriptor");
    verify_vm_descriptor2(&wide_desc, &proof, &dpis)
        .expect("ROUNDTRIP: light client must VERIFY the wide heap-write proof");
    eprintln!(
        "HEAP-WRITE ROUNDTRIP (bare-wide 2951/20): producer≡descriptor — PROVED + VERIFIED, after-root \
         group laid at the committed new_root columns {new_root_cols:?}. Coverage gap CLOSED, benign."
    );
}

/// **(a′) v3-live path.** The committed v3-live `heapWriteVmDescriptor2R24` (1567/4) shares the EXACT
/// `.write` map-op columns (root 216/246.., new_root 443/473..) with the bare-wide member — the wide is
/// the v3-live base + read appendix + wide carriers. Truncating the wide producer's trace to the
/// v3-live width (1567) and proving against the committed v3-live descriptor with the honest heap
/// witness closes R3's "partial on v3-live" leg. Reports PASS or a genuine shape MISMATCH.
#[test]
fn roundtrip_v3_live_descriptor() {
    let v3 = parse_vm_descriptor2(registry_json(V3_STAGED_REGISTRY_TSV, KEY))
        .expect("committed v3-live heapWriteVmDescriptor2R24 parses");
    assert_eq!(v3.trace_width, 1567, "committed v3-live width");
    assert_eq!(v3.public_input_count, 4, "committed v3-live PIs");
    assert_eq!(
        write_new_root_cols(&v3),
        vec![443, 473, 474, 475, 476, 477, 478, 479],
        "v3-live shares the bare-wide .write new_root columns"
    );

    let (wide_trace, wide_dpis, map_heaps) = honest_heap_write();
    // Truncate the wide producer trace to the v3-live width; use the first 4 (base) PIs.
    let trace: Vec<Vec<BabyBear>> = wide_trace
        .iter()
        .map(|r| r[..v3.trace_width].to_vec())
        .collect();
    let dpis: Vec<BabyBear> = wide_dpis[..v3.public_input_count].to_vec();
    assert_eq!(trace[0].len(), 1567);
    assert_eq!(dpis.len(), 4);

    let mb = MemBoundaryWitness::default();
    let refused_v3 = refused(&v3, &trace, &dpis, &mb, &map_heaps);
    if refused_v3 {
        eprintln!(
            "HEAP-WRITE v3-live (1567/4): the truncated producer trace does NOT prove against the \
             committed v3-live descriptor — a producer≡descriptor SHAPE MISMATCH on the v3-live leg."
        );
    } else {
        eprintln!(
            "HEAP-WRITE v3-live (1567/4): truncated producer trace PROVED + VERIFIED against the \
             committed v3-live descriptor. v3-live coverage CLOSED (shares the wide 8-felt splice)."
        );
    }
    assert!(
        !refused_v3,
        "MISMATCH: the wide producer's 1567-col prefix must satisfy the committed v3-live descriptor \
         (they share the .write map-op) — a refusal is a live v3-live producer≡descriptor divergence"
    );
}

const FORGED_LANES: [u32; 7] = [0xDEAD, 0xBEEF, 0x1234, 0x5678, 0x9ABC, 0xCAFE, 0xF00D];

/// **(b-ADV) THE ADVERSARIAL R1-TRAP CHECK — the after-root forge run against the DEPLOYED registry.**
///
/// The finder's forge `after_root_completion_lane_forge_is_unsat` runs against `WIDE_REGISTRY_STAGED_TSV`,
/// which its own doc (`effect_vm_descriptors.rs:1204`) calls "the parallel wide path BESIDE" the live
/// registry, "the live 1-felt `V3_STAGED_REGISTRY_TSV` / FP / VK are UNTOUCHED." The light client the
/// wire runs verifies against the DEPLOYED registry — `V3_STAGED_REGISTRY_TSV` (`:821`, "the live
/// 1-felt" registry). If the deployed member bound only after-root lane 0 while WIDE bound all 8, the
/// finder's UNSAT would be an R1-trap (proving 8-felt binding on an undeployed descriptor). This test
/// re-runs the identical forge against the DEPLOYED v3-live descriptor (1567/4). UNSAT here ⟹ the
/// DEPLOYED heapWrite `.write` map-op binds all 8 after-root felts — the finder's refutation holds on
/// the real light-client path, not just the staged wide twin.
#[test]
#[allow(non_snake_case)]
fn after_root_forge_is_unsat_against_DEPLOYED_v3_registry() {
    let v3 = parse_vm_descriptor2(registry_json(V3_STAGED_REGISTRY_TSV, KEY))
        .expect("committed DEPLOYED v3-live heapWriteVmDescriptor2R24 parses");
    assert_eq!(v3.trace_width, 1567, "deployed v3-live width");
    assert_eq!(v3.public_input_count, 4, "deployed v3-live PIs");
    let new_root_cols = write_new_root_cols(&v3);
    assert_eq!(
        new_root_cols,
        vec![443, 473, 474, 475, 476, 477, 478, 479],
        "deployed v3-live .write new_root columns — all 8 lanes are within the 1567 width"
    );

    let (trace, dpis, map_heaps) = honest_heap_write();
    let mb = MemBoundaryWitness::default();

    // NO DOWNGRADE: the honest truncated producer proves + verifies against the deployed descriptor.
    let htrace: Vec<Vec<BabyBear>> = trace.iter().map(|r| r[..1567].to_vec()).collect();
    let hdpis: Vec<BabyBear> = dpis[..4].to_vec();
    assert!(
        !refused(&v3, &htrace, &hdpis, &mb, &map_heaps),
        "NO DOWNGRADE: honest heap-write must prove+verify against the deployed v3 descriptor"
    );

    let honest_root: Vec<BabyBear> = new_root_cols.iter().map(|&c| trace[0][c]).collect();

    // THE FORGE (identical to the finder's, but bound for the DEPLOYED descriptor): garble after-root
    // completion lanes 1..7 on every row, keep lane 0 honest, recompute the after block-commit so only
    // the deployed .write map-op grow-gate can bite, then truncate to the deployed 1567 width + build
    // the deployed 4-PI vector (pi0 = before state-commit, pi1 = recomputed after state-commit).
    let mut ftrace = trace.clone();
    for row in ftrace.iter_mut() {
        for lane in 1..8 {
            row[new_root_cols[lane]] = BabyBear::new(FORGED_LANES[lane - 1]);
        }
    }
    assert!(
        (1..8).any(|l| ftrace[0][new_root_cols[l]] != honest_root[l]),
        "the forged high lanes differ from the genuine splice root"
    );
    dregg_circuit::effect_vm::trace_rotated::recompute_after_blocks_for_test(&mut ftrace);
    let last = ftrace.len() - 1;
    let before_sc = ftrace[0][BEFORE_BASE + B_STATE_COMMIT];
    let after_sc = ftrace[last][AFTER_BASE + B_STATE_COMMIT];
    let ftrace_v3: Vec<Vec<BabyBear>> = ftrace.iter().map(|r| r[..1567].to_vec()).collect();
    let mut fdpis = dpis[..4].to_vec();
    fdpis[0] = before_sc;
    fdpis[1] = after_sc;

    let unsat = refused(&v3, &ftrace_v3, &fdpis, &mb, &map_heaps);
    if unsat {
        eprintln!(
            "HEAP-WRITE DEPLOYED-REGISTRY VERDICT: the after-root completion-lane forge is UNSAT against \
             the DEPLOYED v3-live (1567/4) descriptor — the light client the wire runs binds ALL EIGHT \
             after-root felts. NOT an R1-trap; the finder's refutation holds on the deployed path."
        );
    } else {
        eprintln!(
            "HEAP-WRITE DEPLOYED-REGISTRY VERDICT: the forge PROVES+VERIFIES against the DEPLOYED v3-live \
             descriptor — the light client binds only after-root lane 0 (~31-bit). The finder's UNSAT \
             was an R1-TRAP (staged-wide only). LIVE 8-felt gap on the deployed heapWrite path."
        );
    }
    assert!(
        unsat,
        "R1-TRAP: the after-root forge proves+verifies against the DEPLOYED v3 registry member — the \
         deployed light-client heapWrite binds only lane-0, not the 8-felt splice. The finder tested \
         the undeployed WIDE twin."
    );
}

/// **(b) AFTER-ROOT 8-FELT BINDING FORGE.** Forge the `.write` `new_root` completion lanes 1..7 to
/// garbage on every row while keeping lane 0 honest, recompute the after block-commit chain + wide
/// carriers so the ONLY thing that can bite is the map-op grow-gate on the completion lanes, then run
/// the pure LC verify. UNSAT ⟹ the deployed `.write` map-op binds all 8 after-root felts to the
/// genuine sorted-Merkle splice (~124-bit), not lane-0.
#[test]
fn after_root_completion_lane_forge_is_unsat() {
    let wide_desc = parse_vm_descriptor2(registry_json(WIDE_REGISTRY_STAGED_TSV, KEY)).unwrap();
    let new_root_cols = write_new_root_cols(&wide_desc);

    let (trace, dpis, map_heaps) = honest_heap_write();
    let mb = MemBoundaryWitness::default();

    // POSITIVE (no downgrade): the honest turn proves + verifies.
    let honest_proof = prove_vm_descriptor2(&wide_desc, &trace, &dpis, &mb, &map_heaps)
        .expect("NO DOWNGRADE: honest wide heap-write proves");
    verify_vm_descriptor2(&wide_desc, &honest_proof, &dpis)
        .expect("NO DOWNGRADE: honest wide heap-write verifies");

    // Non-vacuity: ≥1 forged completion lane genuinely differs from the honest after-root felt.
    let honest_root: Vec<BabyBear> = new_root_cols.iter().map(|&c| trace[0][c]).collect();

    // THE FORGE: garble lanes 1..7 on every row; keep lane 0 honest. These completion lanes are the
    // after rotated block's heap-root completion limbs (58..64), so they feed the after STATE_COMMIT —
    // recompute the after block-commit + re-derive the wide carriers/PIs so the trace is fully
    // self-consistent and the map-op grow-gate is the sole possible binder.
    let mut ftrace = trace.clone();
    for row in ftrace.iter_mut() {
        for lane in 1..8 {
            row[new_root_cols[lane]] = BabyBear::new(FORGED_LANES[lane - 1]);
        }
    }
    assert_eq!(
        ftrace[0][new_root_cols[0]], trace[0][new_root_cols[0]],
        "lane 0 (the scalar heap-root limb) stays honest — only the high seven lanes are forged"
    );
    assert!(
        (1..8).any(|l| ftrace[0][new_root_cols[l]] != honest_root[l]),
        "the forged high lanes differ from the genuine splice root (the grow-gate's UNSAT precondition)"
    );

    dregg_circuit::effect_vm::trace_rotated::recompute_after_blocks_for_test(&mut ftrace);
    // Rebuild the base 4 PIs (pi1 = the recomputed after state-commit on the last row) + wide carriers.
    let last = ftrace.len() - 1;
    let mut base4 = dpis[..4].to_vec();
    base4[0] = ftrace[0][BEFORE_BASE + B_STATE_COMMIT];
    base4[1] = ftrace[last][AFTER_BASE + B_STATE_COMMIT];
    let fdpis = append_wide_carriers(&mut ftrace, base4, HEAP_WRITE_HOST_WIDTH);
    assert_eq!(fdpis.len(), 20);

    let unsat = refused(&wide_desc, &ftrace, &fdpis, &mb, &map_heaps);
    if unsat {
        eprintln!(
            "HEAP-WRITE AFTER-ROOT VERDICT: the completion-lane forge is UNSAT — the deployed .write \
             map-op binds ALL EIGHT after-root felts to the genuine sorted-Merkle splice (~124-bit). \
             The 8-felt AFTER-root binding is faithfully enforced, not lane-0."
        );
    } else {
        eprintln!(
            "HEAP-WRITE AFTER-ROOT VERDICT: the completion-lane forge PROVES+VERIFIES — the deployed \
             descriptor binds only after-root lane 0 (~31-bit). A LIVE 8-felt gap."
        );
    }
    assert!(
        unsat,
        "AFTER-ROOT FORGE: a heap-write forged to differ ONLY in the after-root's high seven \
         completion lanes proves+verifies through the deployed descriptor — the 8-felt AFTER-root is \
         NOT bound (lane-0 only). This is a live light-client soundness gap."
    );
}
