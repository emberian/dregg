use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};
use dregg_federation::generate_test_committee;
use hints::{PartialSignature, sign as bls_sign};

// =============================================================================
// BLS Partial Signature benchmarks
// =============================================================================

fn bench_bls_partial_sign(c: &mut Criterion) {
    let (_committee, secrets) = generate_test_committee(5, 3).unwrap();
    let msg = b"revocation-block-42";

    c.bench_function("bls_partial_sign", |b| {
        b.iter(|| {
            black_box(bls_sign(&secrets[0].secret_key, msg));
        });
    });
}

// =============================================================================
// BLS Aggregate + SNARK proof benchmarks
// =============================================================================

fn bench_bls_aggregate(c: &mut Criterion) {
    let mut group = c.benchmark_group("bls_aggregate");

    for &n in &[3, 5, 7] {
        // threshold = n (all must sign for simplicity)
        let threshold = n as u64;
        let (committee, secrets) = generate_test_committee(n, threshold).unwrap();
        let msg = b"revocation-block-aggregate-test";

        // Generate all partial signatures
        let shares: Vec<(usize, PartialSignature)> = secrets
            .iter()
            .map(|s| (s.index, committee.sign_share(s, msg)))
            .collect();

        group.bench_with_input(
            BenchmarkId::new("signers", n),
            &(committee.clone(), shares.clone(), msg.as_slice()),
            |b, (committee, shares, msg)| {
                b.iter(|| {
                    black_box(committee.aggregate(shares, msg).unwrap());
                });
            },
        );
    }

    group.finish();
}

// =============================================================================
// BLS Verify Aggregate benchmarks
// =============================================================================

fn bench_bls_verify_aggregate(c: &mut Criterion) {
    let mut group = c.benchmark_group("bls_verify_aggregate");

    for &n in &[3, 5, 7] {
        let threshold = n as u64;
        let (committee, secrets) = generate_test_committee(n, threshold).unwrap();
        let msg = b"revocation-block-verify-test";

        let shares: Vec<(usize, PartialSignature)> = secrets
            .iter()
            .map(|s| (s.index, committee.sign_share(s, msg)))
            .collect();

        let qc = committee.aggregate(&shares, msg).unwrap();

        group.bench_with_input(
            BenchmarkId::new("signers", n),
            &(committee.clone(), qc.clone(), msg.as_slice()),
            |b, (committee, qc, msg)| {
                b.iter(|| {
                    black_box(committee.verify(qc, msg).unwrap());
                });
            },
        );
    }

    group.finish();
}

// =============================================================================
// Full consensus round benchmark (in-memory)
// =============================================================================

fn bench_full_consensus_round(c: &mut Criterion) {
    let (committee, secrets) = generate_test_committee(5, 3).unwrap();
    let msg = b"full-consensus-round-test-block";

    c.bench_function("federation_full_round_5_nodes", |b| {
        b.iter(|| {
            // 1. Each node produces a partial signature
            let shares: Vec<(usize, PartialSignature)> = secrets
                .iter()
                .map(|s| (s.index, committee.sign_share(s, msg)))
                .collect();

            // 2. Aggregate into QC
            let qc = committee.aggregate(&shares, msg).unwrap();

            // 3. Verify the QC
            black_box(committee.verify(&qc, msg).unwrap());
        });
    });
}

criterion_group!(
    benches,
    bench_bls_partial_sign,
    bench_bls_aggregate,
    bench_bls_verify_aggregate,
    bench_full_consensus_round,
);
criterion_main!(benches);
