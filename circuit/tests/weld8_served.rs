//! **THE 8-FELT WELDED ATTESTED AUTOMATON IS SERVED** — `dregg-attested-automaton::map-committed-weld8-v1`.
//!
//! Lean author: `metatheory/Dregg2/Circuit/Emit/AttestedAutomatonWeld8.lean` (§3 the descriptor,
//! §3.G the graduation: the two range teeth `CURRENT < 2^15`, `SYMBOL < 2` are lookups into the
//! served `range_w15` / `range_w1` tables, so the `ranges`/`hash_sites` carriers are empty). Its
//! 8-lane denotation and the forged-edge theorem are `AttestedAutomatonLanes8.lean`
//! (`Satisfied2Lanes8`, `weld8_forged_edge_refused`, `weld8_forgery_premises_inhabited`).
//!
//! What this file measures, through the DEPLOYED path (`descriptor_by_name` → `prove_vm_descriptor2`
//! → `verify_vm_descriptor2`):
//!
//! 1. the by-name descriptor passes the v2 admission gate (`check_descriptor2_wellformed`);
//! 2. an honest run of a 3-state automaton committed in the 8-felt map tree proves and verifies;
//! 3. the Lanes8 forgery shape — `forgeD` committed (every step to 0), `forgeE` run (every step to
//!    1) at that root — is REFUSED, by the producer pre-flight and, with the pre-flight bypassed, by
//!    the constraint system;
//! 4. the graduated range tooth bites in the deployed assembly: a state one past the domain
//!    (`2^15`), with a heap entry that opens honestly, is refused by the 15-bit lookup alone.
//!
//! The committed heap is the deployed indexed-Merkle tree (`CanonicalHeapTree8`), keyed by the
//! edge `2·state + symbol` and holding `step(state, symbol)`. ⚠ Key `0` is the tree's MIN-sentinel
//! address (`heap_root::SENTINEL_MIN`, value `0`), so an automaton is committable in this tree only
//! if `step(0, 0) = 0`; both automata here satisfy it (`forgeD` trivially, the counter by
//! construction). The Lean model commits a dense `2^16`-leaf heap and carries no such side
//! condition; the gap is recorded here, not closed.

use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, check_descriptor2_wellformed, prove_vm_descriptor2,
    prove_vm_descriptor2_unchecked, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{CanonicalHeapTree8, HEAP_TREE_DEPTH, HeapLeaf};
use dregg_circuit::refusal::{Refusal, must_refuse_or_unsat_panic};
use std::time::Instant;

const NAME: &str = "dregg-attested-automaton::map-committed-weld8-v1";
const WIDTH: usize = 11;
const PI_COUNT: usize = 10;
const CURRENT: usize = 0;
const SYMBOL: usize = 1;
const NEXT: usize = 2;
const ROOT0: usize = 3;

fn served() -> EffectVmDescriptor2 {
    descriptor_by_name(NAME).expect("the weld must dispatch by name")
}

/// The heap committing `step` over `states × {0, 1}`: key `2s + y ↦ step(s, y)`.
fn heap_of(states: u32, step: impl Fn(u32, u32) -> u32) -> Vec<HeapLeaf> {
    let mut leaves = Vec::new();
    for s in 0..states {
        for y in 0..2 {
            leaves.push(HeapLeaf::entry(
                BabyBear::new(2 * s + y),
                BabyBear::new(step(s, y)),
            ));
        }
    }
    leaves
}

/// One trace row per `(current, symbol, next)` triple, every row carrying the 8-lane root.
fn trace_of(rows: &[(u32, u32, u32)], root: &[BabyBear; 8]) -> Vec<Vec<BabyBear>> {
    rows.iter()
        .map(|&(c, y, n)| {
            let mut r = vec![BabyBear::ZERO; WIDTH];
            r[CURRENT] = BabyBear::new(c);
            r[SYMBOL] = BabyBear::new(y);
            r[NEXT] = BabyBear::new(n);
            r[ROOT0..ROOT0 + 8].copy_from_slice(root);
            r
        })
        .collect()
}

/// `(initial_state, final_state, root₀ … root₇)` — the descriptor's public face.
fn pis_of(rows: &[(u32, u32, u32)], root: &[BabyBear; 8]) -> Vec<BabyBear> {
    let mut p = vec![
        BabyBear::new(rows[0].0),
        BabyBear::new(rows[rows.len() - 1].2),
    ];
    p.extend_from_slice(root);
    assert_eq!(p.len(), PI_COUNT);
    p
}

/// Run `step` from `q` on `word`, as trace triples.
fn run(step: impl Fn(u32, u32) -> u32, q: u32, word: &[u32]) -> Vec<(u32, u32, u32)> {
    let mut cur = q;
    word.iter()
        .map(|&y| {
            let n = step(cur, y);
            let row = (cur, y, n);
            cur = n;
            row
        })
        .collect()
}

/// The honest automaton: count the ones mod 3 (`step(0, 0) = 0`, as the sentinel requires).
fn count_ones_mod3(s: u32, y: u32) -> u32 {
    (s + y) % 3
}

#[test]
fn weld8_is_admitted_by_the_v2_gate() {
    let d = served();
    assert_eq!(d.name, NAME);
    assert!(
        d.ranges.is_empty() && d.hash_sites.is_empty(),
        "the weld must be GRADUATED"
    );
    assert_eq!((d.trace_width, d.public_input_count), (WIDTH, PI_COUNT));
    check_descriptor2_wellformed(&d).expect("the graduated weld passes the v2 admission gate");
}

#[test]
fn weld8_honest_run_proves_and_verifies() {
    let d = served();
    let heap = heap_of(3, count_ones_mod3);
    let root = CanonicalHeapTree8::new(heap.clone(), HEAP_TREE_DEPTH)
        .root8()
        .limbs();
    let rows = run(count_ones_mod3, 0, &[1, 0, 1, 1, 0, 1, 1, 1]);
    assert_eq!(rows.len(), 8);
    let trace = trace_of(&rows, &root);
    let pis = pis_of(&rows, &root);

    let t0 = Instant::now();
    let proof = prove_vm_descriptor2(&d, &trace, &pis, &MemBoundaryWitness::default(), &[heap])
        .expect("an honest run of the committed automaton must prove");
    let prove_ms = t0.elapsed().as_millis();
    let t1 = Instant::now();
    verify_vm_descriptor2(&d, &proof, &pis).expect("the honest proof must verify");
    let verify_ms = t1.elapsed().as_millis();
    eprintln!(
        "weld8 |w|=8: prove {prove_ms} ms, verify {verify_ms} ms, {} batch instances, degree_bits {:?}",
        proof.degree_bits.len(),
        proof.degree_bits
    );

    // The public root is load-bearing: the same proof against a different lane-5 root refuses.
    let mut wrong = pis.clone();
    wrong[2 + 5] += BabyBear::ONE;
    assert!(
        verify_vm_descriptor2(&d, &proof, &wrong).is_err(),
        "a proof must not verify against a different completion lane of the public root"
    );
}

/// The Lanes8 forgery shape (`forgeD`, `forgeE`, `forgeT`): the committed automaton sends every
/// edge to 0; the trace runs the automaton that sends every edge to 1, at the committed root.
/// `forgeT` is one step from state 0 on symbol 0; here it is extended to two rows (the first
/// power-of-two height), and both rows are forged edges.
#[test]
fn weld8_forged_edge_refused() {
    let d = served();
    let forge_d = |_s: u32, _y: u32| 0u32;
    let forge_e = |_s: u32, _y: u32| 1u32;
    let heap = heap_of(2, forge_d);
    let root = CanonicalHeapTree8::new(heap.clone(), HEAP_TREE_DEPTH)
        .root8()
        .limbs();
    let rows = run(forge_e, 0, &[0, 0]);
    assert_eq!(rows, vec![(0, 0, 1), (1, 0, 1)]);
    let trace = trace_of(&rows, &root);
    let pis = pis_of(&rows, &root);

    // Leg 1: the producer pre-flight refuses (fail-closed, before the constraint system).
    let Err(pre) = prove_vm_descriptor2(
        &d,
        &trace,
        &pis,
        &MemBoundaryWitness::default(),
        std::slice::from_ref(&heap),
    ) else {
        panic!("the pre-flight must refuse a forged edge");
    };
    assert!(
        pre.contains("opens to 0, row claims 1"),
        "the pre-flight must name the forged opening: {pre}"
    );

    // Leg 2: with the pre-flight bypassed, the constraint system refuses.
    let verdict = must_refuse_or_unsat_panic("weld8 forged edge (unchecked)", || {
        let proof = prove_vm_descriptor2_unchecked(
            &d,
            &trace,
            &pis,
            &MemBoundaryWitness::default(),
            std::slice::from_ref(&heap),
        )?;
        verify_vm_descriptor2(&d, &proof, &pis)
    });
    match verdict {
        Refusal::Err(e) => eprintln!("weld8 forged edge: refused with Err: {e}"),
        Refusal::UnsatPanic(m) => eprintln!("weld8 forged edge: refused with unsat panic: {m}"),
    }
}

/// The graduated range tooth, in the deployed assembly: a row at state `2^15` whose edge DOES open
/// honestly in the committed heap (key `2^16 ↦ 0`) is refused because of the 15-bit range lookup
/// and nothing else. The Lean twin is `AttestedAutomatonWeld8.weld_range_refuses_out_of_domain`.
///
/// ⚠ Which mechanism refuses, measured: even on the unchecked rail the refusal is the range
/// table's trace filler (`row 0: range wire 0 value 32768 >= 2^15`), which declines to build limb
/// columns for an out-of-range value. That is the assembly refusing to produce the witness, not
/// the verifier refusing a hand-built one; this test does not hand-build the limb columns.
#[test]
fn weld8_range_tooth_refuses_out_of_domain_state() {
    let d = served();
    let big: u32 = 1 << 15;
    let mut heap = heap_of(1, |_s, _y| 0);
    heap.push(HeapLeaf::entry(BabyBear::new(2 * big), BabyBear::ZERO));
    let root = CanonicalHeapTree8::new(heap.clone(), HEAP_TREE_DEPTH)
        .root8()
        .limbs();
    // (2^15, 0) ↦ 0, then (0, 0) ↦ 0: both edges open in the heap; only row 0's state is out of range.
    let rows = vec![(big, 0, 0), (0, 0, 0)];
    let trace = trace_of(&rows, &root);
    let pis = pis_of(&rows, &root);
    let verdict = must_refuse_or_unsat_panic("weld8 state 2^15", || {
        let proof = prove_vm_descriptor2_unchecked(
            &d,
            &trace,
            &pis,
            &MemBoundaryWitness::default(),
            std::slice::from_ref(&heap),
        )?;
        verify_vm_descriptor2(&d, &proof, &pis)
    });
    match verdict {
        Refusal::Err(e) => eprintln!("weld8 state 2^15: refused with Err: {e}"),
        Refusal::UnsatPanic(m) => eprintln!("weld8 state 2^15: refused with unsat panic: {m}"),
    }
    // Control: the same heap and shape at an in-range state proves.
    let ok_rows = vec![(0, 0, 0), (0, 0, 0)];
    let ok_trace = trace_of(&ok_rows, &root);
    let ok_pis = pis_of(&ok_rows, &root);
    let proof = prove_vm_descriptor2(
        &d,
        &ok_trace,
        &ok_pis,
        &MemBoundaryWitness::default(),
        &[heap],
    )
    .expect("the in-range control must prove");
    verify_vm_descriptor2(&d, &proof, &ok_pis).expect("the in-range control must verify");
}
