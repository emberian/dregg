//! Demo (a), the absence receipt: ONE corpus record proved under the served table-routing family.
//!
//! The descriptor `demo/absence-receipt/record-1598.descriptor.json` is emitted by Lean
//! (`DfaRoutingTableEmit.tableRoutingDesc`, via `demo/absence-receipt/EmitRecord.lean`) from the
//! demo's absence table and corpus document 1598 (`3/c/cxr` of crates.io-index at the README's pin,
//! 2048 bytes: the first document whose length is a power of two, because the v2 assembly needs a
//! power-of-two trace height and an exact-public table pins the height to the run length): its
//! `exact_public_rows` table IS that document's run `[state, byte, next]`, so the word is public in
//! the descriptor. The by-name object `dregg-dfa-routing-table::exact-public-v1` is this family at
//! the one-row demo table; this one differs in its rows and name only.
//!
//! What it shows: the served v2 assembly proves and verifies a real record's run from the start
//! state to an accepting final state, and refuses a public input claiming a different final state.
//! What it does not show: anything about the other 99,999 documents (the Lean runner's re-execution
//! is that leg), or a private-word statement.
//!
//! Run ONLY as `cargo test -p dregg-circuit --release --test absence_receipt_record -- --nocapture`.

use std::time::Instant;

use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, TableSem, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;

const RECORD: &str = include_str!("../../demo/absence-receipt/record-1598.descriptor.json");
/// The table's start state and its accepting set's membership of the final state are checked
/// against the table by `EmitRecord.lean` (it prints `accepts`); here the PIs are the run's ends.
const START: u32 = 1;

#[test]
fn absence_record_proves_and_verifies() {
    let desc = parse_vm_descriptor2(RECORD).expect("descriptor parses");
    let rows: Vec<Vec<u32>> = match &desc.tables[0].sem {
        TableSem::ExactPublicRows { rows } => rows.clone(),
        other => panic!("expected exact_public_rows, got {other:?}"),
    };
    assert_eq!(
        rows[0][0], START,
        "the run starts at the table's start state"
    );
    for w in rows.windows(2) {
        assert_eq!(w[0][2], w[1][0], "the run is chained");
    }
    let trace: Vec<Vec<BabyBear>> = rows
        .iter()
        .map(|r| r.iter().map(|&x| BabyBear::new(x)).collect())
        .collect();
    let last = rows.last().expect("non-empty run")[2];
    let pis = vec![BabyBear::new(START), BabyBear::new(last)];
    let mem = MemBoundaryWitness::default();
    let heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    let t0 = Instant::now();
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &mem, &heaps).expect("proves");
    let prove_ms = t0.elapsed().as_secs_f64() * 1e3;
    let t1 = Instant::now();
    verify_vm_descriptor2(&desc, &proof, &pis).expect("verifies");
    let verify_ms = t1.elapsed().as_secs_f64() * 1e3;
    let proof_bytes = postcard_len(&proof);

    // Falsifier: the same proof against a public input naming a different final state.
    let wrong = vec![BabyBear::new(START), BabyBear::new(last + 1)];
    assert!(
        verify_vm_descriptor2(&desc, &proof, &wrong).is_err(),
        "a proof of this run must not verify for another final state"
    );

    println!(
        "ABSENCE-RECORD rows={} width={} constraints={} tables={} instances={} final={last} \
         prove_ms={prove_ms:.1} verify_ms={verify_ms:.1} proof_bytes={proof_bytes}",
        rows.len(),
        desc.trace_width,
        desc.constraints.len(),
        desc.tables.len(),
        proof.degree_bits.len(),
    );
}

fn postcard_len<T: serde::Serialize>(v: &T) -> usize {
    postcard::to_allocvec(v).map(|b| b.len()).unwrap_or(0)
}
