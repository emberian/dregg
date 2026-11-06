//! Demo (a), the absence receipt: ONE corpus record proved under the served table-routing family.
//!
//! The descriptor `demo/absence-receipt/record-1598.descriptor.json` is emitted by Lean
//! (`DfaRoutingTableRoute8.tableRoutingBoundDesc`, via `demo/absence-receipt/EmitRecord.lean`) from the
//! demo's absence table and corpus document 1598 (`3/c/cxr` of crates.io-index at the README's pin,
//! 2048 bytes: the first document whose length is a power of two, because the v2 assembly needs a
//! power-of-two trace height and an exact-public table pins the height to the run length): its
//! `exact_public_rows` is the public multiset of `[state, byte, next]` transitions. The shared
//! eight-lane route chain binds their order and public length, under the hash assumption. Before
//! proving, this test checks each transition and the accepting endpoint against the signed table.
//! The same proof is refused under another final state, ordered-route root, or length.
//! This is one record's served-path evidence; the other 99,999 verdicts are native re-execution.
//!
//! Run with `cargo nextest run -p dregg-circuit --release --test absence_receipt_record
//! -E 'test(absence_record_proves_and_verifies)'`.

use std::time::Instant;

use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, TableSem, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::route_chain8_witness::verify_route8_record;
use dregg_circuit::route_chain8_witness::{TABLE_ROUTE_CONFIG, extend_route8, verify_route8};

const RECORD: &str = include_str!("../../demo/absence-receipt/record-1598.descriptor.json");
const DOCUMENT: &[u8] = include_bytes!("../../demo/absence-receipt/record-1598.jsonl");
const POLICY_TABLE: &str = include_str!("../../demo/absence-receipt/absence-table.json");

#[test]
fn absence_record_proves_and_verifies() {
    let desc = parse_vm_descriptor2(RECORD).expect("descriptor parses");
    let rows: Vec<Vec<u32>> = match &desc.tables[0].sem {
        TableSem::ExactPublicRows { rows } => rows.clone(),
        other => panic!("expected exact_public_rows, got {other:?}"),
    };
    let table: serde_json::Value = serde_json::from_str(POLICY_TABLE).expect("policy table parses");
    let states = table["num_states"].as_u64().expect("state count");
    assert!(
        states > 0 && states < dregg_circuit::field::BABYBEAR_P as u64,
        "policy states have an injective field representation"
    );
    let start_nat = table["start"].as_u64().expect("start");
    assert!(start_nat < states, "policy start is a declared state");
    let start = start_nat as u32;
    let transitions = table["transitions"].as_array().expect("transitions");
    let accepting = table["accepting"].as_array().expect("accepting states");
    assert_eq!(
        rows.len(),
        DOCUMENT.len(),
        "descriptor covers the complete public record"
    );
    for (row, &byte) in rows.iter().zip(DOCUMENT) {
        assert_eq!(
            row[1], byte as u32,
            "descriptor byte agrees with the public record"
        );
        assert_eq!(row.len(), 3);
        assert!(row[1] < 256, "input symbol is a byte");
        assert_eq!(
            transitions[row[0] as usize * 256 + row[1] as usize].as_u64(),
            Some(row[2] as u64)
        );
    }
    assert_eq!(
        rows[0][0], start,
        "the run starts at the table's start state"
    );
    for w in rows.windows(2) {
        assert_eq!(w[0][2], w[1][0], "the run is chained");
    }
    let mut trace: Vec<Vec<BabyBear>> = rows
        .iter()
        .map(|r| r.iter().map(|&x| BabyBear::new(x)).collect())
        .collect();
    let last = rows.last().expect("non-empty run")[2];
    assert!(
        accepting
            .iter()
            .any(|state| state.as_u64() == Some(last as u64)),
        "the record reaches a policy-table accepting state"
    );
    let record: Vec<_> = DOCUMENT.iter().map(|&b| BabyBear::new(b as u32)).collect();
    let step = |state: BabyBear, symbol: BabyBear| -> Result<BabyBear, String> {
        let q = state.as_u32() as usize;
        let b = symbol.as_u32() as usize;
        if b >= 256 {
            return Err("record symbol is not a byte".into());
        }
        let offset = q
            .checked_mul(256)
            .and_then(|x| x.checked_add(b))
            .ok_or("table offset overflow")?;
        let next = transitions
            .get(offset)
            .and_then(serde_json::Value::as_u64)
            .ok_or("unknown table state")?;
        if next >= table["num_states"].as_u64().ok_or("missing state count")? {
            return Err("table target is out of range".into());
        }
        Ok(BabyBear::new(next as u32))
    };
    let mut pis = vec![BabyBear::new(start), BabyBear::new(last)];
    extend_route8(
        &mut trace,
        &mut pis,
        TABLE_ROUTE_CONFIG,
        [BabyBear::new(0); 8],
    )
    .expect("route witness has canonical public length");
    let mem = MemBoundaryWitness::default();
    let heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    let t0 = Instant::now();
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &mem, &heaps).expect("proves");
    let prove_ms = t0.elapsed().as_secs_f64() * 1e3;
    let t1 = Instant::now();
    verify_route8_record(
        &desc,
        &proof,
        &pis,
        TABLE_ROUTE_CONFIG,
        [BabyBear::new(0); 8],
        BabyBear::new(start),
        &record,
        step,
    )
    .expect("verifies the explicit public record with height admission");
    let verify_ms = t1.elapsed().as_secs_f64() * 1e3;
    let proof_bytes = postcard_len(&proof);

    // Falsifier: the same proof against a public input naming a different final state.
    let mut wrong = pis.clone();
    wrong[1] = BabyBear::new(last + 1);
    assert!(
        verify_vm_descriptor2(&desc, &proof, &wrong).is_err(),
        "a proof of this run must not verify for another final state"
    );

    let mut wrong_route = pis.clone();
    wrong_route[2] += BabyBear::new(1);
    assert!(
        verify_vm_descriptor2(&desc, &proof, &wrong_route).is_err(),
        "the proof must not verify for another ordered-route root"
    );
    let mut wrong_length = pis.clone();
    wrong_length[10] += BabyBear::new(1);
    assert!(
        verify_route8(&desc, &proof, &wrong_length, TABLE_ROUTE_CONFIG).is_err(),
        "the proof must not verify for another route length"
    );

    let mut wrong_record = record.clone();
    wrong_record[0] = BabyBear::new((DOCUMENT[0] ^ 1) as u32);
    assert!(
        verify_route8_record(
            &desc,
            &proof,
            &pis,
            TABLE_ROUTE_CONFIG,
            [BabyBear::new(0); 8],
            BabyBear::new(start),
            &wrong_record,
            step
        )
        .is_err(),
        "same proof and public inputs must refuse a different public record"
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
