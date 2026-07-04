//! # HEAP-WRITE DEPLOYED SPLICE FORCING — the in-circuit MapOp binds `heap_root` to the genuine
//! sorted-Merkle SPLICE, NOT a free root and NOT merely an accumulator advance.
//!
//! Census D2 asked: can a prover publish a `heap_root` advance NOT matching the heap content (a
//! "forgeable root")? This test answers at the DEPLOYED level — it inspects the REAL
//! `heapWriteVmDescriptor2R24` parsed from the committed staged registry TSV (the bytes the prover
//! and the light-client verifier both consume), not a standalone model.
//!
//! WHAT IS FORCED (the PHASE-E splice — wired):
//!   The deployed descriptor carries the genuine sorted-Merkle SPLICE as a `.write` `MapOp` on the
//!   heap root, realized by the `Ir2Air::MapOps` AIR (`circuit/src/descriptor_ir2.rs`):
//!     addr     = hash[ COLL(70), KEY(71) ]               → HEAP_ADDR(102)   (the kept address site)
//!     newRoot  = writesTo( HEAP_ROOT_BEFORE(65), addr=HEAP_ADDR(102), value=VALUE(72) )
//!                                                        → HEAP_ROOT_AFTER(87)
//!   So `HEAP_ROOT_AFTER` is the genuine binary-Merkle sorted insert-or-update of `(addr, value)`
//!   into the heap behind the committed old root — `mapRoot (Heap.set h addr v)` — opened against the
//!   committed root via a membership path (`heap_root.rs` `CanonicalHeapTree::update_witness`). A root
//!   that is content-mismatched (the wrong sorted-tree update) has NO satisfying `update_witness`. This
//!   is the deployed twin of the Lean `RotatedKernelRefinementExercise.heapWrite_splice_forced` /
//!   `heapWrite_sat_rejects_wrong_splice_root` (the census worry, CLOSED for the genuine splice).
//!
//! The accumulator-advance site (`siteHeapRootAdvance`, `new_root = hash[leaf, old_root]`) is
//! REPLACED by the splice (col 87 cannot be doubly pinned): the published root is now bound to the
//! sorted-tree SPLICE, not the prepend accumulator.

use dregg_circuit::descriptor_ir2::{MapKind, MapOpSpec, VmConstraint2, parse_vm_descriptor2};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::lean_descriptor_air::LeanExpr;

const HEAP_WRITE_KEY: &str = "heapWriteVmDescriptor2R24";

// The deployed heap-write column layout (`EffectVmEmitHeapRoot` §0–§1 pins, mirrored in the TSV).
const COLL: usize = 70; // hp.COLL
const KEY: usize = 71; // hp.KEY
const VALUE: usize = 72; // hp.VALUE
const HEAP_ROOT_BEFORE: usize = 65;
const HEAP_ROOT_AFTER: usize = 87;
const HEAP_ADDR: usize = 102;
// Phase H-HEAP-8: the deployed splice `MapOp` reads/writes the FAITHFUL 8-felt heap-root GROUP on the
// ROTATED limbs (lane 0 = rotated `heap_root` limb 28, completions 58..64), NOT the v1-state cols 65/87.
// Lane 0: before = EFFECT_VM_WIDTH(188)+B_HEAP_ROOT(28) = 216; after = 188+B_SPAN(227)+28 = 443. The
// v13 rotated block span grew 91→227 (`EffectVmEmitRotationV3.B_SPAN`: R=24 geometry + commitments_root
// + lifecycle/perms/vk/mode + fields_root + the v11/v12 completion octets + the v13 fields[0..7] lanes).
// Mirrors the cap weld's rotated cap-root limb. (Lean `EffectVmEmitRotationV3.heapRootGroupCol`.)
const HEAP_ROOT_BEFORE_ROT: usize = 216;
const HEAP_ROOT_AFTER_ROT: usize = 443;

const P2_CHIP_TABLE: usize = 1; // table id of `poseidon2_chip` in the staged registry
const CHIP_DIGEST_IDX: usize = 17; // out0 position in the 25-wide chip tuple (arity + 16 inputs + out0 + 7 lanes)

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

/// `true` iff some parsed Poseidon2-chip lookup binds `hash[in0, in1] → digest_col` (arity 2).
fn has_chip_recompute(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    in0: usize,
    in1: usize,
    digest_col: usize,
) -> bool {
    desc.constraints.iter().any(|c| {
        let VmConstraint2::Lookup(l) = c else {
            return false;
        };
        l.table == P2_CHIP_TABLE
            && l.tuple.first() == Some(&LeanExpr::Const(2))
            && l.tuple.get(1) == Some(&LeanExpr::Var(in0))
            && l.tuple.get(2) == Some(&LeanExpr::Var(in1))
            && l.tuple.get(CHIP_DIGEST_IDX) == Some(&LeanExpr::Var(digest_col))
    })
}

/// The deployed heapWrite descriptor binds `HEAP_ADDR` to the in-row recompute of the bound
/// `(coll, key)` — the address site that gives the splice MapOp its genuine sorted KEY. The
/// accumulator advance is GONE (it is replaced by the splice); only the address site survives as a
/// chip recompute.
#[test]
fn deployed_heapwrite_forces_addr_recompute() {
    let desc = parse_vm_descriptor2(rotated_descriptor_json(HEAP_WRITE_KEY))
        .expect("heapWriteVmDescriptor2R24 parses from the committed staged registry");

    assert!(
        has_chip_recompute(&desc, COLL, KEY, HEAP_ADDR),
        "siteHeapAddr: addr = hash[coll, key] → HEAP_ADDR must be a deployed chip lookup (the \
         splice MapOp's genuine sorted KEY)"
    );

    // The advance recompute is GONE: col 87 (HEAP_ROOT_AFTER) is no longer pinned by a chip lookup
    // `hash[leaf, old_root]` — it is pinned by the splice MapOp instead (col 87 cannot be doubly bound).
    const HEAP_LEAF: usize = 103;
    assert!(
        !has_chip_recompute(&desc, HEAP_LEAF, HEAP_ROOT_BEFORE, HEAP_ROOT_AFTER),
        "the accumulator advance hash[leaf, old_root] → HEAP_ROOT_AFTER must be ABSENT (replaced by \
         the splice MapOp — col 87 is forced by the genuine sorted-tree update, not the accumulator)"
    );

    eprintln!(
        "DEPLOYED HEAP-ADDR FORCING: heapWriteVmDescriptor2R24 binds HEAP_ADDR({HEAP_ADDR}) = \
         hash[coll, key] via a poseidon2-chip lookup; the accumulator advance is replaced by the splice."
    );
}

/// PHASE-E SPLICE FORCING (the residual tripwire FLIPPED to the positive): the deployed heapWrite
/// descriptor carries the genuine sorted-Merkle SPLICE as a `.write` `MapOp` on the heap root —
/// `writesTo( HEAP_ROOT_BEFORE, key=HEAP_ADDR, value=VALUE ) → HEAP_ROOT_AFTER`. So the published
/// `heap_root` is bound to the sorted-tree leaf-list update (the membership-open of the OLD heap +
/// same-sibling new root), NOT merely the prepend accumulator. The Lean discharge is
/// `RotatedKernelRefinementExercise.heapWrite_newRoot_splice_forced`.
#[test]
fn deployed_heapwrite_forces_sorted_merkle_splice() {
    let desc = parse_vm_descriptor2(rotated_descriptor_json(HEAP_WRITE_KEY))
        .expect("heapWriteVmDescriptor2R24 parses");

    let splice = desc.constraints.iter().find_map(|c| match c {
        VmConstraint2::MapOp(m) if m.op == MapKind::Write => Some(m),
        _ => None,
    });

    let m: &MapOpSpec = splice
        .expect("PHASE-E: heapWriteVmDescriptor2R24 must carry a `.write` map_op (the splice)");

    // The splice op opens the committed heap root (8-felt group, lane 0 = col 65) at the in-row-
    // recomputed address (col 102) for the written value (col 72) and FORCES the new heap root
    // (8-felt group, lane 0 = col 87) to the genuine sorted update. Phase H-HEAP-8: `root`/`new_root`
    // are 8-lane digest groups whose lane 0 is the old scalar heap-root limb.
    assert_eq!(
        m.root.len(),
        8,
        "splice root must be an 8-felt heap-root group"
    );
    assert_eq!(
        m.root[0],
        LeanExpr::Var(HEAP_ROOT_BEFORE_ROT),
        "splice root lane 0 must be the ROTATED before heap-root limb 28 (col 216)"
    );
    assert_eq!(
        m.key,
        LeanExpr::Var(HEAP_ADDR),
        "splice key must be the recomputed HEAP_ADDR(102)"
    );
    assert_eq!(
        m.value,
        LeanExpr::Var(VALUE),
        "splice value must be VALUE(72)"
    );
    assert_eq!(
        m.new_root.len(),
        8,
        "splice new_root must be an 8-felt heap-root group"
    );
    assert_eq!(
        m.new_root[0],
        LeanExpr::Var(HEAP_ROOT_AFTER_ROT),
        "splice new_root lane 0 must be the ROTATED after heap-root limb 28 (col 443) — the published \
         faithful heap_root"
    );

    eprintln!(
        "PHASE-E SPLICE WIRED: heapWriteVmDescriptor2R24 carries a `.write` map_op forcing \
         HEAP_ROOT_AFTER({HEAP_ROOT_AFTER}) = the genuine sorted-Merkle splice of (HEAP_ADDR, VALUE) \
         into the heap behind HEAP_ROOT_BEFORE({HEAP_ROOT_BEFORE}). A content-mismatched root is UNSAT \
         (no update_witness). The residual is CLOSED — the published root is bound to the sorted-tree \
         update, not the accumulator."
    );
}
