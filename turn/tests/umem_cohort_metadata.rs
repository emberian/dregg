//! Cohort staging carries domain metadata without constructing a temporary AIR.
//! These regressions check guard ordering, boundary compatibility and admission gates;
//! they do not prove the Rust witness lowering refines the Lean memory semantics.
use dregg_cell::CellId;
use dregg_circuit::descriptor_ir2::{UMemBoundaryWitness, VmConstraint2};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_turn::umem::{
    UKey, UProjection, UVal, UmemKind, UmemOp, umem_cohort_multidomain_proving_inputs_from,
    umem_cohort_proving_inputs_from, umem_key_addr_v1, umem_proving_inputs_from_v1,
    umem_val_felt_v1,
};

fn heap_key() -> UKey {
    UKey::Field {
        cell: CellId([0x31; 32]),
        slot: 7,
    }
}

fn write(key: UKey, val: UVal) -> UmemOp {
    UmemOp {
        kind: UmemKind::Write,
        key,
        val: Some(val),
        prev_val: None,
        prev_serial: 0,
    }
}

fn same_boundary(a: &UMemBoundaryWitness, b: &UMemBoundaryWitness) {
    assert_eq!(a.addrs, b.addrs);
    assert_eq!(a.init_vals, b.init_vals);
}

#[test]
fn umem_metadata_single_domain_preserves_rows_and_boundary() {
    let key = heap_key();
    let pre = UProjection::from([(key.clone(), UVal::U64(9))]);
    let mut op = write(key.clone(), UVal::U64(10));
    op.prev_val = Some(UVal::U64(9));
    let ops = [op];
    let cohort = umem_cohort_proving_inputs_from(&pre, &ops).unwrap();
    let legacy = umem_proving_inputs_from_v1(&pre, &ops).unwrap();
    assert_eq!(cohort.domain, 1);
    assert_eq!(cohort.rows, legacy.rows);
    same_boundary(&cohort.boundary, &legacy.boundary);
    assert_eq!(cohort.boundary.addrs, vec![umem_key_addr_v1(&key)]);
    assert_eq!(
        cohort.boundary.init_vals,
        vec![Some(umem_val_felt_v1(pre.get(&key)).1)]
    );
    assert_eq!(cohort.rows.len(), 4);
    assert!(cohort.rows.iter().all(|r| r.len() == 7));
    assert_eq!(cohort.rows[0][6], BabyBear::ONE);
    assert!(
        cohort.rows[1..]
            .iter()
            .flatten()
            .all(|x| *x == BabyBear::ZERO)
    );
    assert_eq!(legacy.descriptor.trace_width, 7);
}

#[test]
fn umem_metadata_multidomain_orders_guards_independently_of_execution() {
    // Execution order is deliberately different from sorted domain/guard order.
    let ops = [
        write(UKey::Receipt(9), UVal::U64(9)),
        write(heap_key(), UVal::U64(10)),
        write(UKey::NoteNullifier([0x27; 32]), UVal::Present),
    ];
    let pre = UProjection::new();
    let cohort = umem_cohort_multidomain_proving_inputs_from(&pre, &ops).unwrap();
    let legacy = umem_proving_inputs_from_v1(&pre, &ops).unwrap();
    assert_eq!(cohort.domains, vec![1, 3, 4]);
    assert_eq!(cohort.rows, legacy.rows);
    same_boundary(&cohort.boundary, &legacy.boundary);
    assert_eq!(
        cohort
            .boundary
            .addrs
            .iter()
            .map(|(d, _)| *d)
            .collect::<Vec<_>>(),
        cohort.domains
    );
    assert_eq!(legacy.descriptor.trace_width, 9);
    assert_eq!(legacy.descriptor.constraints.len(), 3);
    for (i, constraint) in legacy.descriptor.constraints.iter().enumerate() {
        let VmConstraint2::UMemOp(op) = constraint else {
            panic!("compatibility UMem op")
        };
        assert_eq!(op.domain, cohort.domains[i]);
        assert!(matches!(&op.guard, LeanExpr::Var(col) if *col == 6 + i));
    }
    for (row, active) in cohort.rows[..3].iter().zip([2, 0, 1]) {
        for (i, v) in row[6..].iter().enumerate() {
            assert_eq!(
                *v,
                if i == active {
                    BabyBear::ONE
                } else {
                    BabyBear::ZERO
                }
            );
        }
    }
    assert!(cohort.rows[3].iter().all(|v| *v == BabyBear::ZERO));
}

#[test]
fn umem_metadata_empty_and_wrong_cohort_are_refused() {
    let pre = UProjection::new();
    assert!(
        umem_cohort_proving_inputs_from(&pre, &[])
            .unwrap_err()
            .contains("empty op trace")
    );
    assert!(
        umem_cohort_multidomain_proving_inputs_from(&pre, &[])
            .unwrap_err()
            .contains("empty op trace")
    );
    let one = [write(heap_key(), UVal::U64(1))];
    assert!(umem_cohort_proving_inputs_from(&pre, &one).is_ok());
    assert!(
        umem_cohort_multidomain_proving_inputs_from(&pre, &one)
            .unwrap_err()
            .contains("touches 1 domain")
    );
    let two = [one[0].clone(), write(UKey::Receipt(1), UVal::U64(1))];
    assert!(umem_cohort_multidomain_proving_inputs_from(&pre, &two).is_ok());
    assert!(
        umem_cohort_proving_inputs_from(&pre, &two)
            .unwrap_err()
            .contains("touches 2 domains")
    );
}

fn same_admission_refusal(pre: &UProjection, ops: &[UmemOp], reason: &str) {
    let legacy = umem_proving_inputs_from_v1(pre, ops).unwrap_err();
    assert!(legacy.contains(reason), "{legacy}");
    assert_eq!(
        umem_cohort_proving_inputs_from(pre, ops).unwrap_err(),
        legacy
    );
    assert_eq!(
        umem_cohort_multidomain_proving_inputs_from(pre, ops).unwrap_err(),
        legacy
    );
}

#[test]
fn umem_metadata_preserves_address_alias_refusal() {
    let raw = [0x42; 32];
    let honest = [write(UKey::NoteNullifier(raw), UVal::Present)];
    assert!(umem_cohort_proving_inputs_from(&UProjection::new(), &honest).is_ok());
    let aliases = [
        honest[0].clone(),
        write(UKey::BridgedNullifier(raw), UVal::Present),
    ];
    same_admission_refusal(&UProjection::new(), &aliases, "address codec collision");
}

#[test]
fn umem_metadata_preserves_value_and_prestate_alias_refusals() {
    let raw = [0x54; 32];
    for extra_domain in [false, true] {
        let mut ops = vec![write(heap_key(), UVal::Bytes32(raw))];
        if extra_domain {
            ops.push(write(UKey::Receipt(2), UVal::U64(2)));
        }
        let pre = UProjection::new();
        assert!(umem_proving_inputs_from_v1(&pre, &ops).is_ok());
        let mut bad = ops.clone();
        bad[0].prev_val = Some(UVal::UmemRef(raw));
        same_admission_refusal(&pre, &bad, "VALUE codec collision");
        let pre_alias = UProjection::from([(heap_key(), UVal::UmemRef(raw))]);
        same_admission_refusal(&pre_alias, &ops, "VALUE codec collision");
    }
}
