//! Served table-routing binding: identical edge multiset and final state, distinct order.
//! Constraints are emitted by Lean; Rust only assembles witnesses and invokes the verifier.
use dregg_circuit::{
    descriptor_by_name::descriptor_by_name,
    descriptor_ir2::{
        MemBoundaryWitness, check_descriptor2_wellformed, prove_vm_descriptor2,
        prove_vm_descriptor2_unchecked, verify_vm_descriptor2,
    },
    field::BabyBear,
    refusal::must_refuse_or_unsat_panic,
    route_chain8_witness::{
        FIELD_MODULUS, TABLE_ROUTE_CONFIG, admit_route8_degree, admit_route8_length, extend_route8,
        route8_for_record, verify_route8, verify_route8_record,
    },
};
const NAME: &str = "dregg-dfa-routing-table::route8-bound-v1";
fn witness(order: [u32; 2]) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let mut trace: Vec<_> = order
        .into_iter()
        .map(|y| vec![BabyBear::new(0), BabyBear::new(y), BabyBear::new(0)])
        .collect();
    let mut pis = vec![BabyBear::new(0); 2];
    extend_route8(
        &mut trace,
        &mut pis,
        TABLE_ROUTE_CONFIG,
        [BabyBear::new(0); 8],
    )
    .unwrap();
    (trace, pis)
}
#[test]
fn table_route8_length_admission_excludes_wrap() {
    assert!(admit_route8_length(1, 1).is_ok());
    assert!(
        route8_for_record(
            TABLE_ROUTE_CONFIG,
            [BabyBear::new(0); 8],
            BabyBear::new(0),
            &[BabyBear::new(1), BabyBear::new(2)],
            |_, _| Err("unknown symbol".into())
        )
        .is_err()
    );
    let mut padded = vec![vec![BabyBear::new(0); 3]; 3];
    let original = padded.clone();
    let mut pis = vec![BabyBear::new(0); 2];
    assert!(
        extend_route8(
            &mut padded,
            &mut pis,
            TABLE_ROUTE_CONFIG,
            [BabyBear::new(0); 8]
        )
        .is_err()
    );
    assert_eq!(
        padded, original,
        "invalid height is refused before mutation"
    );
    assert_eq!(pis.len(), 2);
    assert!(admit_route8_length(FIELD_MODULUS - 1, FIELD_MODULUS - 1).is_ok());
    assert!(admit_route8_degree(1, 2).is_ok());
    for (degree, public) in [(31, 1), (usize::MAX, 1), (1, 1)] {
        assert!(admit_route8_degree(degree, public).is_err());
    }
    for (rows, public) in [
        (0, 0),
        (FIELD_MODULUS, FIELD_MODULUS),
        (FIELD_MODULUS + 1, 1),
        (2, 1),
    ] {
        assert!(admit_route8_length(rows, public).is_err());
    }
}
#[test]
fn table_route8_served_order_splice_refused() {
    let desc = descriptor_by_name(NAME).expect("bound table route dispatched");
    check_descriptor2_wellformed(&desc).expect("generated shape admitted");
    assert_eq!(
        (
            desc.trace_width,
            desc.public_input_count,
            desc.constraints.len()
        ),
        (20, 11, 32)
    );
    let (trace, pis) = witness([1, 2]);
    let (swapped, other_pis) = witness([2, 1]);
    assert_eq!(
        &pis[..2],
        &other_pis[..2],
        "unbound public endpoints are identical"
    );
    assert_ne!(
        &pis[2..10],
        &other_pis[2..10],
        "ordered eight-lane route differs"
    );
    let mem = MemBoundaryWitness::default();
    let start = std::time::Instant::now();
    let proof =
        prove_vm_descriptor2(&desc, &trace, &pis, &mem, &[]).expect("honest ordered route proves");
    let prove_ms = start.elapsed().as_secs_f64() * 1000.0;
    let start = std::time::Instant::now();
    verify_route8_record(
        &desc,
        &proof,
        &pis,
        TABLE_ROUTE_CONFIG,
        [BabyBear::new(0); 8],
        BabyBear::new(0),
        &[BabyBear::new(1), BabyBear::new(2)],
        |_, _| Ok(BabyBear::new(0)),
    )
    .expect("honest external record verifies");
    for record in [
        vec![BabyBear::new(2), BabyBear::new(1)],
        vec![BabyBear::new(1)],
    ] {
        assert!(
            verify_route8_record(
                &desc,
                &proof,
                &pis,
                TABLE_ROUTE_CONFIG,
                [BabyBear::new(0); 8],
                BabyBear::new(0),
                &record,
                |_, _| Ok(BabyBear::new(0))
            )
            .is_err(),
            "same proof and same PIs must refuse a substituted external record"
        );
    }
    let verify_ms = start.elapsed().as_secs_f64() * 1000.0;
    eprintln!(
        "TABLE-ROUTE8 rows=2 width=20 pis=11 constraints=32 wide_permutations=2 prove_ms={prove_ms:.3} verify_ms={verify_ms:.3} proof_bytes={}",
        postcard::to_allocvec(&proof).unwrap().len()
    );
    let other = prove_vm_descriptor2(&desc, &swapped, &other_pis, &mem, &[])
        .expect("other honest order proves");
    verify_route8(&desc, &other, &other_pis, TABLE_ROUTE_CONFIG)
        .expect("other honest order verifies");
    assert!(
        verify_route8(&desc, &other, &pis, TABLE_ROUTE_CONFIG).is_err(),
        "cannot substitute opposite order's proof"
    );
    for k in 2..11 {
        let mut tampered = pis.clone();
        tampered[k] += BabyBear::new(1);
        assert!(
            verify_route8(&desc, &proof, &tampered, TABLE_ROUTE_CONFIG).is_err(),
            "every route/length PI is bound"
        );
    }
    must_refuse_or_unsat_panic("table route8 opposite order at original route", || {
        let p = prove_vm_descriptor2_unchecked(&desc, &swapped, &pis, &mem, &[])?;
        verify_vm_descriptor2(&desc, &p, &pis)
    });
}
