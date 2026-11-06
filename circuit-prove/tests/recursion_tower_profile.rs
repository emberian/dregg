//! # THE RECURSION TOWER, MEASURED IN EXACT COUNTS — the workload `ir2_phase_profile.rs` §0.6
//! declared out of scope.
//!
//! `notes/phase-profile.md` §0 blind spot 6: *"the recursion/leaf-wrap tower is not measured
//! here."* Four separate wins landed against the leaf prover this week and every one of them
//! deferred its real value to this tower:
//!
//! * `permEmissionNarrow` is 1.97× per chip but 1.076× on the deployed batch, *"because the chip
//!   is 13.35% of committed width there — the recursion tower is ~75% in-circuit Poseidon2, where
//!   the factor approaches 1.97×"* (`notes/narrow-witness-gen.md` §3.4);
//! * the blowup drop is prover ÷15.19 against **verifier ×2.28**, and a tower layer's job IS
//!   verifying;
//! * the `num_queries` hole is a recursion hole;
//! * hash-bound at 5.0–7.2× says hashing dominates, and this is the hash-densest workload we have.
//!
//! ## ⚑ THE INSTRUMENT, AND WHY IT IS NOT THE ONE THE BRIEF ASKED FOR
//!
//! **A permutation counter cannot see in-circuit Poseidon2 at all.** `ir2_phase_profile.rs` §D
//! counts calls to `Permutation::permute_mut`. An in-circuit permutation is not a call — it is a
//! *row of an AIR*, evaluated as field arithmetic by the same LDE/quotient machinery as every
//! other row. Pointing the §D counter at a tower layer would report that layer's **native** hashing
//! (its own Merkle commit) and would report **zero** for the thing the 75% claim is about. The two
//! populations are disjoint and a single counter conflates them by construction.
//!
//! **And the counter cannot be pointed at the tower anyway.** `prove_vm_descriptor2_for_config` is
//! generic over `SC` because the leaf's prover is. Layers 1–3 are **monomorphic**:
//! `prove_descriptor_leaf_rotated_with_config(…, config: &DreggRecursionConfig)` takes a config
//! *value*, not a config *type*, and `RecursableAir` (`plonky3_recursion_impl.rs:138-148`) welds
//! `DreggRecursionConfig` into four supertrait bounds. `impl FriRecursionConfig for
//! DreggRecursionConfig` is orphan-rule-welded to the concrete type
//! (`recursion-verify/src/config.rs:12-14`), and its `prepare_circuit_for_verification` hardcodes
//! `default_babybear_poseidon2_16()`. A counting twin is a real port, not a type parameter.
//!
//! **So the instrument here is the circuit itself.** Both exact, both contention-immune:
//!
//! 1. **The op census** — `Circuit::ops` is a `Vec<Op<EF>>` built deterministically from the child
//!    proof's shape. Counting `Op::NonPrimitiveOpWithExecutor` by `executor.op_type()` gives the
//!    **exact in-circuit Poseidon2 permutation count**, which is the quantity the 75% claim names.
//!    This is the same census `apex_shrink_trace_anatomy.rs` runs, extended with the by-type split
//!    it was missing (it printed one `NonPrimitive ops` total across poseidon2 + recompose).
//! 2. **The real table geometry** — `get_airs_and_degrees_with_prep`, the same call the prover
//!    makes, at the same `TablePacking` and `ConstraintProfile` the deployed params carry. Rows and
//!    widths are what the prover commits, not a model of them.
//!
//! From (2) the layer's **native** Poseidon2 count follows exactly from the MMCS's own definition:
//! `PaddingFreeSponge<Perm, 16, 8, 8>` absorbs `RATE = 8` base elements per permutation, so a
//! committed row of width `w` costs `⌈w/8⌉`; `TruncatedPermutation<Perm, 2, 8, 16>` is one
//! permutation per 2-to-1 node. Both are read off `recursion-verify/src/config.rs:104-105`.
//!
//! ⚠ **Wall clock is not evidence on this box** (load average 6–34 across this run, 40 login
//! sessions). No milliseconds are reported as a measurement; the two fold times printed are
//! labelled upper bounds and nothing is derived from them.
//!
//! ## Denominators — named, because a percentage without its phase set is not a measurement
//!
//! Three different denominators appear below and they differ by 20 points:
//!
//! * **`cells(main+prep)`** — every committed trace cell, preprocessed included. The honest one for
//!   "what does the prover commit", because the preprocessed columns are LDE'd and Merkle'd too.
//! * **`cells(main)`** — main trace only. What a reader who forgot the preprocessed side computes.
//! * **`rows`** — table rows, ignoring width. Meaningless for cost; included only to show how far
//!   it is from the others.
//!
//! Every share below states which.
//!
//! Run (release only):
//! ```text
//! cargo test -p dregg-circuit-prove --release --test recursion_tower_profile -- --ignored --nocapture --test-threads=1
//! ```

use std::collections::BTreeMap;
use std::time::Instant;

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    Ir2Air, MemBoundaryWitness, UMemBoundaryWitness, ir2_airs_and_common_for_config,
    parse_vm_descriptor2, prove_vm_descriptor2_for_config,
};
use dregg_circuit::effect_vm::trace_rotated::{
    GRAD_ROT_WIDTH, RotatedBlockWitness, generate_rotated_effect_vm_trace, transfer_caveat_manifest,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit_prove::dregg_outer_config::DreggOuterConfig;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, ir2_leaf_wrap_config, prove_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, create_recursion_backend,
};
use dregg_turn::rotation_witness as rw;
use dregg_turn_prover::rotation_witness::mint_rotated_participant_leg;
use p3_air::BaseAir;
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_circuit::{AluOpKind, Circuit, Op};
use p3_circuit_prover::{
    ConstraintProfile, TablePacking,
    common::{CircuitTableAir, NpoAirBuilder, NpoPreprocessor, get_airs_and_degrees_with_prep},
    expose_claim_air_builders, expose_claim_preprocessor, poseidon2_air_builders,
    poseidon2_preprocessor, recompose_air_builders, recompose_preprocessor,
};
use p3_field::extension::BinomialExtensionField;
use p3_recursion::{
    BatchOnly, RecursionInput, build_next_layer_circuit, build_next_layer_circuit_with_expose,
};

const D: usize = 4;
type EF = BinomialExtensionField<P3BabyBear, D>;

/// `PaddingFreeSponge<Perm, WIDTH=16, RATE=8, OUT=8>` — `recursion-verify/src/config.rs:104`.
/// A committed row of `w` base elements costs `⌈w/RATE⌉` permutations.
const RATE: usize = 8;

// ===========================================================================
// The census
// ===========================================================================

#[derive(Default, Debug)]
struct OpCensus {
    n_const: u64,
    n_public: u64,
    n_hint: u64,
    n_add: u64,
    n_mul: u64,
    n_bool: u64,
    n_muladd: u64,
    n_horner: u64,
    /// NPO ops keyed by `executor.op_type()` — the split `apex_shrink_trace_anatomy.rs` summed.
    npo_by_type: BTreeMap<String, u64>,
    witness_count: u32,
    public_flat_len: usize,
    private_flat_len: usize,
}

impl OpCensus {
    fn alu_total(&self) -> u64 {
        self.n_add + self.n_mul + self.n_bool + self.n_muladd + self.n_horner
    }
    fn npo_total(&self) -> u64 {
        self.npo_by_type.values().sum()
    }
    /// ⚑ The exact in-circuit Poseidon2 permutation count: NPO ops whose type is a
    /// `poseidon2_perm/*` (both the W16 FRI-transcript/Merkle permutation and the W24
    /// segment-digest one, registered at `recursion-verify/src/config.rs:262-273`).
    fn in_circuit_perms(&self) -> u64 {
        self.npo_by_type
            .iter()
            .filter(|(k, _)| k.starts_with("poseidon2_perm"))
            .map(|(_, v)| *v)
            .sum()
    }
}

fn census(circuit: &Circuit<EF>) -> OpCensus {
    let mut c = OpCensus {
        witness_count: circuit.witness_count,
        public_flat_len: circuit.public_flat_len,
        private_flat_len: circuit.private_flat_len,
        ..Default::default()
    };
    for op in &circuit.ops {
        match op {
            Op::Const { .. } => c.n_const += 1,
            Op::Public { .. } => c.n_public += 1,
            Op::Hint { .. } => c.n_hint += 1,
            Op::NonPrimitiveOpWithExecutor { executor, .. } => {
                *c.npo_by_type
                    .entry(executor.op_type().as_str().to_string())
                    .or_insert(0) += 1;
            }
            Op::Alu { kind, .. } => match kind {
                AluOpKind::Add => c.n_add += 1,
                AluOpKind::Mul => c.n_mul += 1,
                AluOpKind::BoolCheck => c.n_bool += 1,
                AluOpKind::MulAdd => c.n_muladd += 1,
                AluOpKind::HornerAcc => c.n_horner += 1,
            },
        }
    }
    c
}

fn print_census(label: &str, c: &OpCensus) {
    println!("\n─── OP CENSUS — {label} ───");
    println!("witness_count       : {}", c.witness_count);
    println!("public_flat_len     : {}", c.public_flat_len);
    println!("private_flat_len    : {}", c.private_flat_len);
    println!("Const ops           : {}", c.n_const);
    println!("Public ops          : {}", c.n_public);
    println!("Hint ops            : {}", c.n_hint);
    println!(
        "Alu ops             : {} (Add {} / Mul {} / Bool {} / MulAdd {} / HornerAcc {})",
        c.alu_total(),
        c.n_add,
        c.n_mul,
        c.n_bool,
        c.n_muladd,
        c.n_horner
    );
    println!("NonPrimitive ops    : {}", c.npo_total());
    for (k, v) in &c.npo_by_type {
        println!("    {k:<34} {v}");
    }
    println!(
        "⚑ IN-CIRCUIT POSEIDON2 PERMUTATIONS (exact): {}",
        c.in_circuit_perms()
    );
}

// ===========================================================================
// The real table geometry
// ===========================================================================

#[derive(Debug, Clone)]
struct TableShape {
    name: String,
    /// `log2(rows)`.
    degree: usize,
    main_width: usize,
    prep_width: usize,
    max_constraint_degree: Option<usize>,
}

impl TableShape {
    fn rows(&self) -> u64 {
        1u64 << self.degree
    }
    fn cells_main(&self) -> u64 {
        self.rows() * self.main_width as u64
    }
    fn cells_all(&self) -> u64 {
        self.rows() * (self.main_width + self.prep_width) as u64
    }
    /// Merkle **leaf-sponge** permutations for this matrix at `log_blowup`: one
    /// `PaddingFreeSponge` absorb of `RATE` elements per permutation, per LDE row.
    fn leaf_perms(&self, log_blowup: usize) -> u64 {
        let lde_rows = 1u64 << (self.degree + log_blowup);
        let main = (self.main_width as u64).div_ceil(RATE as u64);
        let prep = if self.prep_width > 0 {
            (self.prep_width as u64).div_ceil(RATE as u64)
        } else {
            0
        };
        lde_rows * (main + prep)
    }
}

/// `CircuitTableAir<SC, D>` is generic over the *config*, so naming its variants at two different
/// configs (BabyBear recursion, BN254 outer) needs the body monomorphised twice. A macro rather
/// than a generic fn keeps the `SymbolicExpressionExt: Algebra<..>` bound out of the signature.
macro_rules! name_shapes {
    ($airs_degrees:expr, $npo_keys_sorted:expr) => {{
        // Builders run in registration order (poseidon2, recompose, expose_claim), each over the
        // SORTED matched op types — the same iteration `get_airs_and_degrees_with_prep` performs.
        let mut dynamic_names: Vec<String> = Vec::new();
        for prefix in ["poseidon2_perm/", "recompose", "expose_claim"] {
            for k in $npo_keys_sorted.iter() {
                let k: &String = k;
                let matched = if prefix.ends_with('/') {
                    k.starts_with(prefix)
                } else {
                    k == prefix
                };
                if matched {
                    dynamic_names.push(k.clone());
                }
            }
        }
        let mut dyn_i = 0usize;
        let mut out: Vec<TableShape> = Vec::new();
        for (air, degree) in $airs_degrees.iter() {
            let (name, mw, pw, mcd) = match air {
                CircuitTableAir::Const(a) => (
                    "Const".to_string(),
                    BaseAir::<P3BabyBear>::width(a),
                    BaseAir::<P3BabyBear>::preprocessed_width(a),
                    BaseAir::<P3BabyBear>::max_constraint_degree(a),
                ),
                CircuitTableAir::Public(a) => (
                    "Public".to_string(),
                    BaseAir::<P3BabyBear>::width(a),
                    BaseAir::<P3BabyBear>::preprocessed_width(a),
                    BaseAir::<P3BabyBear>::max_constraint_degree(a),
                ),
                CircuitTableAir::Alu(a) => (
                    "Alu".to_string(),
                    BaseAir::<P3BabyBear>::width(a),
                    BaseAir::<P3BabyBear>::preprocessed_width(a),
                    BaseAir::<P3BabyBear>::max_constraint_degree(a),
                ),
                CircuitTableAir::Dynamic(a) => {
                    let n = dynamic_names
                        .get(dyn_i)
                        .cloned()
                        .unwrap_or_else(|| format!("dynamic#{dyn_i}"));
                    dyn_i += 1;
                    (
                        n,
                        BaseAir::<P3BabyBear>::width(a),
                        BaseAir::<P3BabyBear>::preprocessed_width(a),
                        BaseAir::<P3BabyBear>::max_constraint_degree(a),
                    )
                }
            };
            out.push(TableShape {
                name,
                degree: *degree,
                main_width: mw,
                prep_width: pw,
                max_constraint_degree: mcd,
            });
        }
        out
    }};
}

/// Table shapes under the BabyBear recursion config — what a leaf wrap / fold node commits.
fn shapes_recursion(circuit: &Circuit<EF>, packing: &TablePacking) -> Vec<TableShape> {
    let preprocessors: Vec<Box<dyn NpoPreprocessor<P3BabyBear>>> = vec![
        poseidon2_preprocessor::<P3BabyBear>(),
        recompose_preprocessor::<P3BabyBear>(false),
        expose_claim_preprocessor::<P3BabyBear>(),
    ];
    let air_builders: Vec<Box<dyn NpoAirBuilder<DreggRecursionConfig, D>>> = {
        let mut b = poseidon2_air_builders::<DreggRecursionConfig, D>();
        b.extend(recompose_air_builders::<DreggRecursionConfig, D>(1, false));
        b.extend(expose_claim_air_builders::<DreggRecursionConfig, D>());
        b
    };
    let (airs_degrees, _prim, npo) = get_airs_and_degrees_with_prep::<DreggRecursionConfig, EF, D>(
        circuit,
        packing,
        &preprocessors,
        &air_builders,
        ConstraintProfile::Standard,
    )
    .expect("recursion-config table-AIR extraction");
    let mut keys: Vec<String> = npo.keys().map(|k| k.as_str().to_string()).collect();
    keys.sort();
    name_shapes!(&airs_degrees, &keys)
}

/// Table shapes under the BN254 outer config — what the shrink commits.
fn shapes_outer(circuit: &Circuit<EF>, packing: &TablePacking) -> Vec<TableShape> {
    let preprocessors: Vec<Box<dyn NpoPreprocessor<P3BabyBear>>> = vec![
        poseidon2_preprocessor::<P3BabyBear>(),
        recompose_preprocessor::<P3BabyBear>(false),
        expose_claim_preprocessor::<P3BabyBear>(),
    ];
    let air_builders: Vec<Box<dyn NpoAirBuilder<DreggOuterConfig, D>>> = {
        let mut b = poseidon2_air_builders::<DreggOuterConfig, D>();
        b.extend(recompose_air_builders::<DreggOuterConfig, D>(1, false));
        b.extend(expose_claim_air_builders::<DreggOuterConfig, D>());
        b
    };
    let (airs_degrees, _prim, npo) = get_airs_and_degrees_with_prep::<DreggOuterConfig, EF, D>(
        circuit,
        packing,
        &preprocessors,
        &air_builders,
        ConstraintProfile::Standard,
    )
    .expect("outer-config table-AIR extraction");
    let mut keys: Vec<String> = npo.keys().map(|k| k.as_str().to_string()).collect();
    keys.sort();
    name_shapes!(&airs_degrees, &keys)
}

/// Print the geometry and the three denominators, then the native-hash derivation.
fn print_shapes(label: &str, shapes: &[TableShape], log_blowup: usize) {
    println!("\n─── COMMITTED GEOMETRY — {label} (mint log_blowup = {log_blowup}) ───");
    println!(
        "{:<34} {:>5} {:>10} {:>7} {:>7} {:>6} {:>14} {:>16}",
        "table", "log2", "rows", "main_w", "prep_w", "deg", "cells(m+p)", "leaf perms"
    );
    let mut cells_all = 0u64;
    let mut cells_main = 0u64;
    let mut rows_all = 0u64;
    let mut perms = 0u64;
    for s in shapes {
        println!(
            "{:<34} {:>5} {:>10} {:>7} {:>7} {:>6} {:>14} {:>16}",
            s.name,
            s.degree,
            s.rows(),
            s.main_width,
            s.prep_width,
            s.max_constraint_degree
                .map(|d| d.to_string())
                .unwrap_or_else(|| "?".into()),
            s.cells_all(),
            s.leaf_perms(log_blowup),
        );
        cells_all += s.cells_all();
        cells_main += s.cells_main();
        rows_all += s.rows();
        perms += s.leaf_perms(log_blowup);
    }
    println!(
        "degree_bits: {:?}",
        shapes.iter().map(|s| s.degree).collect::<Vec<_>>()
    );
    println!("TOTAL cells(main+prep) : {cells_all}");
    println!("TOTAL cells(main)      : {cells_main}");
    println!("TOTAL rows             : {rows_all}");
    println!("TOTAL native leaf-sponge perms @ lb{log_blowup} : {perms}");

    // Merkle 2-to-1 compressions: one `TruncatedPermutation` per internal node, per commitment.
    // Matrices sharing a height are hashed into one tree, so group by degree.
    let mut by_degree: BTreeMap<usize, ()> = BTreeMap::new();
    for s in shapes {
        by_degree.insert(s.degree, ());
    }
    let compress: u64 = by_degree
        .keys()
        .map(|d| (1u64 << (d + log_blowup)).saturating_sub(1))
        .sum();
    println!(
        "TOTAL native compress perms (2-to-1, one tree per distinct height) : {compress}  \
         [+{:.1}% on the leaf-sponge term]",
        100.0 * compress as f64 / perms.max(1) as f64
    );

    // The three shares, each with its denominator NAMED.
    for s in shapes {
        if s.name.starts_with("poseidon2_perm") {
            println!(
                "⚑ {} share — cells(main+prep) {:.2}% · cells(main) {:.2}% · rows {:.2}%",
                s.name,
                100.0 * s.cells_all() as f64 / cells_all as f64,
                100.0 * s.cells_main() as f64 / cells_main as f64,
                100.0 * s.rows() as f64 / rows_all as f64,
            );
        }
    }
    let p2_cells: u64 = shapes
        .iter()
        .filter(|s| s.name.starts_with("poseidon2_perm"))
        .map(|s| s.cells_all())
        .sum();
    let p2_cells_main: u64 = shapes
        .iter()
        .filter(|s| s.name.starts_with("poseidon2_perm"))
        .map(|s| s.cells_main())
        .sum();
    println!(
        "⚑ ALL poseidon2 tables — cells(main+prep) {:.2}% · cells(main) {:.2}%",
        100.0 * p2_cells as f64 / cells_all as f64,
        100.0 * p2_cells_main as f64 / cells_main as f64,
    );
}

// ===========================================================================
// Fixtures
// ===========================================================================

fn rotated_transfer_json() -> &'static str {
    for line in V3_STAGED_REGISTRY_TSV.lines() {
        let mut it = line.splitn(3, '\t');
        if it.next() == Some("transferVmDescriptor2R24") {
            let _name = it.next();
            return it.next().expect("json column");
        }
    }
    panic!("transferVmDescriptor2R24 not in V3_STAGED_REGISTRY_TSV");
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

/// The real deployed leaf, minted through **the same wide dispatch `mint_rotated_participant_leg`
/// runs** (`turn-prover/src/rotation_witness.rs:159`), which is the path the apex fold actually
/// takes.
///
/// ⚠ NOT `generate_rotated_effect_vm_trace` + the registry TSV, which is what
/// `rotation_batchstark_leaf_smoke.rs` uses: measured 2026-08-14 that path is RED at HEAD twice
/// over — the registry `transferVmDescriptor2R24` is `trace_width 1896` against
/// `GRAD_ROT_WIDTH = 1841` (and a source comment saying 1647), and the narrow generator emits a
/// base row of width 847 against the descriptor's `producer_owned_width` of 857, so the prover
/// refuses:
///
/// ```text
/// base row 0 width 847 is short of the PRODUCER-OWNED width 857 for descriptor
/// `dregg-effectvm-transfer-v1-avail-rot24-v3-staged-gentian-deployed-bare-refuse`
/// (trace_width 1896): columns 847..857 are filled by no prove-time weld
/// ```
///
/// `rotation_batchstark_leaf_smoke.rs` carries **no `#[ignore]` and no feature gate**. Reported,
/// not worked around.
fn rotated_transfer_workload() -> (
    dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    Vec<Vec<dregg_circuit::field::BabyBear>>,
    Vec<dregg_circuit::field::BabyBear>,
    Vec<Vec<dregg_circuit::heap_root::HeapLeaf>>,
    MemBoundaryWitness,
) {
    use dregg_circuit::effect_vm::trace_rotated::generate_rotated_effect_vm_descriptor_and_trace_wide;
    use dregg_turn::rotation_witness::{empty_revoked_root_8, produce, sender_membership_teeth};

    let before_balance: i64 = 100_000;
    let amount: u64 = 50;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance - amount as i64, 0);
    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let mk = |c: &Cell| {
        produce(
            c,
            &ledger,
            &nullifier_root,
            &commitments_root,
            &empty_revoked_root_8(),
            &receipt_log,
            &dregg_cell::commitment::RotationCarrierMaterial::default(),
        )
    };
    let before_w = mk(&before_cell);
    let after_w = mk(&after_cell);
    let bridge = |w: &rw::RotationWitness| -> RotatedBlockWitness {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("31 pre-iroot limbs")
    };
    let caveat = transfer_caveat_manifest();
    let (desc, trace, dpis, map_heaps, mem_boundary) =
        generate_rotated_effect_vm_descriptor_and_trace_wide(
            &st,
            &effects,
            &bridge(&before_w),
            &bridge(&after_w),
            &caveat,
            None,
            None,
            None,
            Some(sender_membership_teeth(&before_cell)),
        )
        .expect("the wide rotated producer dispatch");
    println!(
        "child descriptor `{}`: trace_width {} / pi_count {}   (GRAD_ROT_WIDTH constant = {}{})",
        desc.name,
        desc.trace_width,
        desc.public_input_count,
        GRAD_ROT_WIDTH,
        if desc.trace_width == GRAD_ROT_WIDTH {
            ""
        } else {
            ", ⚠ DRIFTED"
        }
    );
    (desc, trace, dpis, map_heaps, mem_boundary)
}

// ===========================================================================
// §A — LAYER 1: THE LEAF WRAP over the deployed rotated IR-v2 transfer leaf
// ===========================================================================

/// ⚑ The deployed leaf wrap, censused. This is the layer `narrow-witness-gen.md` §3.4 points at
/// when it says the tower is "~75% in-circuit Poseidon2".
#[test]
#[ignore = "MEASUREMENT: one real rotated IR-v2 prove + one leaf-wrap CIRCUIT BUILD (no wrap proving). --ignored --nocapture --test-threads=1"]
fn l1_leaf_wrap_over_the_deployed_ir2_leaf() {
    let (desc, trace, dpis, map_heaps, mem_boundary) = rotated_transfer_workload();
    let config = ir2_leaf_wrap_config();

    let t = Instant::now();
    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc,
        &trace,
        &dpis,
        &mem_boundary,
        &map_heaps,
        &UMemBoundaryWitness::default(),
        &config,
    )
    .expect("the rotated transfer leaf proves at the leaf-wrap config");
    println!(
        "[upper bound, contended box] inner IR-v2 prove: {:?}",
        t.elapsed()
    );

    // ⚑ THE CHILD'S COMMITTED GEOMETRY — the denominator `permEmissionNarrow` multiplies, and the
    // ONLY channel through which that lever reaches this layer (§1a of the note).
    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(&desc, &inner, &dpis, &config).expect("verify triple");
    println!("\n─── THE CHILD (layer 0): the rotated IR-v2 transfer batch ───");
    let mut child_cells = 0u64;
    let mut child_width = 0u64;
    let mut child_leaf_perms = 0u64;
    for (i, air) in airs.iter().enumerate() {
        let w = BaseAir::<P3BabyBear>::width(air);
        let dbits = inner.degree_bits.get(i).copied().unwrap_or(0);
        let rows = 1u64 << dbits;
        // ⌈w/8⌉ per row is the IN-CIRCUIT cost of hashing this matrix's opened leaf, per query.
        let lp = (w as u64).div_ceil(RATE as u64);
        println!(
            "  instance {i:>2}: width {w:>5}  log2 rows {dbits:>3}  rows {rows:>8}  \
             cells {:>12}  leaf-hash perms/row {lp:>4}",
            rows * w as u64
        );
        child_cells += rows * w as u64;
        child_width += w as u64;
        child_leaf_perms += lp;
    }
    println!(
        "  CHILD main traces: {} instances, Σwidth {child_width}, Σcells {child_cells}, \
         Σ⌈w/8⌉ {child_leaf_perms}",
        airs.len()
    );
    println!(
        "  ⚑ denominators for `permEmissionNarrow` at THIS child: a 386→175 chip is\n\
        \x20    Δwidth 211 / Σwidth {child_width} = {:.2}% of the child's committed width, and\n\
        \x20    Δ⌈w/8⌉ 27 / Σ⌈w/8⌉ {child_leaf_perms} = {:.2}% of its per-query in-circuit leaf hashing.",
        100.0 * 211.0 / child_width as f64,
        100.0 * 27.0 / child_leaf_perms as f64,
    );

    let input: RecursionInput<'_, DreggRecursionConfig, Ir2Air> =
        RecursionInput::NativeBatchStark {
            airs: &airs,
            proof: &inner,
            common_data: &common,
            table_public_inputs,
        };
    let backend = create_recursion_backend();
    let t = Instant::now();
    let (circuit, _vr) =
        build_next_layer_circuit_with_expose::<DreggRecursionConfig, Ir2Air, _, D>(
            &input, &config, &backend, None,
        )
        .expect("the leaf-wrap verification circuit builds");
    println!(
        "[upper bound, contended box] leaf-wrap circuit build: {:?}",
        t.elapsed()
    );

    let c = census(&circuit);
    print_census("L1 leaf wrap over the rotated IR-v2 transfer leaf", &c);

    // `ProveNextLayerParams::default()` = `TablePacking::new(1, 4)`, `ConstraintProfile::Standard` —
    // what `prove_recursion_layer_auto_with_expose` passes (`gpu_backend.rs`).
    let shapes = shapes_recursion(&circuit, &TablePacking::new(1, 4));
    // The leaf wrap MINTS at `create_recursion_config`'s log_blowup 3 (the mint/verify split).
    print_shapes(
        "L1 leaf wrap @ deployed packing p1/a4, mint lb3",
        &shapes,
        3,
    );
    // And what it cost before the split, when the child's lb 6 became the wrap's own.
    print_shapes("L1 leaf wrap @ pre-split lb6 (for contrast)", &shapes, 6);
}

/// GALOIS-LEVERS lane: the SAME wrap circuit's committed geometry across `TablePacking`
/// variants — `(alu_lanes, horner_pack_k, recompose npo_lanes)`.
///
/// The op list is built ONCE and never changes; only the table shapes move. Every point on
/// this grid is therefore a **VK rotation, not a wire change** — the same precedent class as
/// the landed reduced-opening split (`notes/sumcheck-batched-opening.md` §3): child proof
/// byte-identical, accepted predicate identical, wrap preprocessed commitment rotates.
///
/// Why this grid exists: after the reduced-opening split, the wrap's `Alu` table is dominated
/// by per-query `HornerAcc` chains over BASE-field opened values against the single ext
/// challenge α — chains that `compute_schedule` places on lane 0 at `horner_packed_steps = 2`
/// while the other `alu_lanes - 1` lanes ride along mostly idle. The cells-per-Horner-step is
/// then `(76 + 59) / 2 ≈ 67` at the deployed `p1/a4/K2`, against a linear-in-K packed-step
/// cost of `~8 main + ~7 prep` cells. The grid measures where the real minimum sits.
#[test]
#[ignore = "MEASUREMENT: one real rotated IR-v2 prove + one leaf-wrap CIRCUIT BUILD, then shape extraction per packing point. --ignored --nocapture --test-threads=1"]
fn g_packing_grid_over_the_deployed_leaf_wrap() {
    use p3_circuit::NpoTypeId;

    let (desc, trace, dpis, map_heaps, mem_boundary) = rotated_transfer_workload();
    let config = ir2_leaf_wrap_config();

    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc,
        &trace,
        &dpis,
        &mem_boundary,
        &map_heaps,
        &UMemBoundaryWitness::default(),
        &config,
    )
    .expect("the rotated transfer leaf proves at the leaf-wrap config");

    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(&desc, &inner, &dpis, &config).expect("verify triple");
    let input: RecursionInput<'_, DreggRecursionConfig, Ir2Air> =
        RecursionInput::NativeBatchStark {
            airs: &airs,
            proof: &inner,
            common_data: &common,
            table_public_inputs,
        };
    let backend = create_recursion_backend();
    let (circuit, _vr) =
        build_next_layer_circuit_with_expose::<DreggRecursionConfig, Ir2Air, _, D>(
            &input, &config, &backend, None,
        )
        .expect("the leaf-wrap verification circuit builds");

    let c = census(&circuit);
    print_census(
        "wrap over the deployed leaf — op census (packing-INVARIANT: the control)",
        &c,
    );

    // (alu_lanes, horner_pack_k, recompose_lanes). First row is the deployed control.
    let grid: &[(usize, usize, usize)] = &[
        (4, 2, 1), // deployed p1/a4/K2 — must reproduce the landed geometry exactly
        (4, 4, 1),
        (4, 8, 1),
        (2, 8, 1),
        (1, 8, 1),
        (2, 16, 1),
        (4, 16, 1),
        (4, 12, 1),
        (4, 24, 1),
        (4, 32, 1),
        (4, 64, 1),
        (8, 16, 1),
        (2, 8, 4),  // recompose lane retune on a good ALU point
        (4, 2, 4),  // recompose lane retune alone, against the deployed control
        (4, 16, 4), // the combined candidate: K16 + recompose out of the height-pin
        (4, 32, 4),
    ];

    for &(alu_lanes, horner_k, rec_lanes) in grid {
        let packing = TablePacking::new(1, alu_lanes)
            .with_horner_pack_k(horner_k)
            .with_npo_lanes(NpoTypeId::recompose(), rec_lanes);
        let shapes = shapes_recursion(&circuit, &packing);
        print_shapes(
            &format!("packing p1/a{alu_lanes}/K{horner_k}/rec{rec_lanes}"),
            &shapes,
            3,
        );
    }
}

// ===========================================================================
// §B — THE PERMUTATION COUNTER, WHERE IT DOES REACH: the child of layer 1
// ===========================================================================
//
// ⚑ The brief asked for `ir2_phase_profile.rs` §D's counter. It cannot be pointed at layers 1–3
// (§0b), but it CAN be pointed at layer 0 — the child the leaf wrap verifies — and that is the one
// place it answers a *tower* question. `blowup-drop.md` §6 prices the trade as verifier ×2.28, and
// the leaf wrap's in-circuit Poseidon2 rows are the child's verifier re-executed as constraints.
// So: count the child's NATIVE verify permutations here, and compare against the wrap's EXACT
// in-circuit permutation count from §A. If the two agree, "the wrap pays the verifier's bill"
// stops being a model and becomes a measured identity — and blowup-drop's 4,040 → 9,213 maps
// straight onto the wrap's biggest table.
//
// ⚠ The counters are PROCESS-GLOBAL (`ir2_phase_profile.rs` §D's own recorded trap: five tests
// bracketing a prove with reset/snapshot corrupted each other under default parallelism, and the
// corruption arrived as a plausible number). Run with `--test-threads=1`.

mod counting {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};

    use p3_baby_bear::{Poseidon2BabyBear, default_babybear_poseidon2_16};
    use p3_challenger::DuplexChallenger;
    use p3_commit::ExtensionMmcs;
    use p3_dft::Radix2DitParallel;
    use p3_field::Field;
    use p3_fri::{FriParameters, TwoAdicFriPcs};
    use p3_merkle_tree::MerkleTreeMmcs;
    use p3_symmetric::{
        CryptographicPermutation, PaddingFreeSponge, Permutation, TruncatedPermutation,
    };
    use p3_uni_stark::StarkConfig;

    pub static PERMS: AtomicU64 = AtomicU64::new(0);
    pub static PERMS_PACKED: AtomicU64 = AtomicU64::new(0);

    type Pack = <P3BabyBear as Field>::Packing;

    /// Verbatim `ir2_phase_profile.rs` §D: one generic impl, lane count recovered from the state's
    /// SIZE (two inherent impls do not pass coherence — `<BabyBear as Field>::Packing` is a
    /// projection rustc will not normalize far enough in an impl header).
    #[derive(Clone)]
    pub struct CountingPerm(Poseidon2BabyBear<16>);

    impl<T: Clone> Permutation<T> for CountingPerm
    where
        Poseidon2BabyBear<16>: Permutation<T>,
    {
        fn permute_mut(&self, input: &mut T) {
            let lanes = (core::mem::size_of::<T>() / (16 * core::mem::size_of::<P3BabyBear>()))
                .max(1) as u64;
            PERMS.fetch_add(lanes, Ordering::Relaxed);
            if lanes > 1 {
                PERMS_PACKED.fetch_add(1, Ordering::Relaxed);
            }
            self.0.permute_mut(input);
        }
    }
    impl<T: Clone> CryptographicPermutation<T> for CountingPerm where
        Poseidon2BabyBear<16>: CryptographicPermutation<T>
    {
    }

    type CHash = PaddingFreeSponge<CountingPerm, 16, 8, 8>;
    type CCompress = TruncatedPermutation<CountingPerm, 2, 8, 16>;
    type CValMmcs = MerkleTreeMmcs<Pack, Pack, CHash, CCompress, 2, 8>;
    type CChallengeMmcs = ExtensionMmcs<P3BabyBear, EF, CValMmcs>;
    type CPcs = TwoAdicFriPcs<P3BabyBear, Radix2DitParallel<P3BabyBear>, CValMmcs, CChallengeMmcs>;
    type CChallenger = DuplexChallenger<P3BabyBear, CountingPerm, 16, 8>;
    pub type CountingConfig = StarkConfig<CPcs, EF, CChallenger>;

    /// `max_log_arity` is a parameter here because the deployed leaf-wrap engine is **arity 2**
    /// (`INNER_FRI_MAX_LOG_ARITY = 1`, `recursion-verify/src/config.rs:81`) even though `ir2_config`
    /// — which it otherwise matches — is arity 8. §D's config hardcodes arity 8 and would be
    /// measuring the wrong engine here.
    pub fn counting_config(
        log_blowup: usize,
        max_log_arity: usize,
        num_queries: usize,
        pow: usize,
    ) -> CountingConfig {
        let perm = CountingPerm(default_babybear_poseidon2_16());
        let hash = CHash::new(perm.clone());
        let compress = CCompress::new(perm.clone());
        let val_mmcs = CValMmcs::new(hash, compress, 0);
        let fri_params = FriParameters {
            log_blowup,
            log_final_poly_len: 0,
            max_log_arity,
            num_queries,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: pow,
            mmcs: CChallengeMmcs::new(val_mmcs.clone()),
        };
        let pcs = TwoAdicFriPcs::new(Radix2DitParallel::default(), val_mmcs, fri_params);
        StarkConfig::new(pcs, CChallenger::new(perm))
    }

    pub fn reset() {
        PERMS.store(0, Ordering::Relaxed);
        PERMS_PACKED.store(0, Ordering::Relaxed);
    }
    pub fn read() -> (u64, u64) {
        (
            PERMS.load(Ordering::Relaxed),
            PERMS_PACKED.load(Ordering::Relaxed),
        )
    }
}

/// ⚑ The **rotated** transfer leaf's native prove/verify permutation split, at the engine the leaf
/// wrap actually verifies (`lb 6 / arity 2 / 19 q / pow 16`) and at the blowup drop's `(2, 57)`.
/// `blowup-drop.md` §D2 measured the UNROTATED transfer batch at arity 8; this is the deployed
/// rotated child at the deployed wrap arity, which is the number the tower's cost turns on.
#[test]
#[ignore = "MEASUREMENT: 4 real rotated IR-v2 proves under a counting config. --ignored --nocapture --test-threads=1"]
fn l0_child_prove_and_verify_permutations_at_the_wrap_engine() {
    use dregg_circuit::descriptor_ir2::verify_vm_descriptor2_with_config;

    let (desc, trace, dpis, map_heaps, mem_boundary) = rotated_transfer_workload();
    println!(
        "\n─── §B  THE CHILD'S NATIVE PERMUTATIONS (exact, contention-immune) ───\n\
         object: rotated `transferVmDescriptor2R24`, trace_width {} / pi_count {}",
        desc.trace_width, desc.public_input_count
    );
    println!(
        "\n{:<28} {:>14} {:>14} {:>14} {:>10}",
        "(lb, arity, q, pow)", "prove perms", "verify perms", "prove+verify", "packed"
    );

    // (lb, arity_bits, q, pow) — the deployed wrap engine, then the blowup drop, then each with
    // the grind removed so the drop is not read off a PoW draw (`phase-profile.md` §5).
    let points: [(usize, usize, usize, usize, &str); 4] = [
        (6, 1, 19, 16, "DEPLOYED wrap engine"),
        (6, 1, 19, 0, "deployed, grind-free"),
        (2, 1, 57, 16, "the blowup drop"),
        (2, 1, 57, 0, "the drop, grind-free"),
    ];
    for (lb, arity, q, pow, label) in points {
        let config = counting::counting_config(lb, arity, q, pow);
        counting::reset();
        let proof = prove_vm_descriptor2_for_config::<counting::CountingConfig>(
            &desc,
            &trace,
            &dpis,
            &mem_boundary,
            &map_heaps,
            &UMemBoundaryWitness::default(),
            &config,
        )
        .expect("the rotated leaf proves under the counting config");
        // ⚠ `prove_vm_descriptor2_for_config` runs its OWN self-verify (`check`), so this snapshot
        // is prove + ONE verify — the exact trap `blowup-drop.md` §D2 records. Split it by taking
        // a second verify and differencing.
        let (after_prove_plus_selfverify, packed_a) = counting::read();
        counting::reset();
        verify_vm_descriptor2_with_config(&desc, &proof, &dpis, &config)
            .expect("the rotated leaf verifies under the counting config");
        let (verify_perms, _packed_v) = counting::read();
        let prove_perms = after_prove_plus_selfverify.saturating_sub(verify_perms);
        println!(
            "{:<28} {:>14} {:>14} {:>14} {:>10}   {label}",
            format!("({lb}, {}, {q}, {pow})", 1usize << arity),
            prove_perms,
            verify_perms,
            after_prove_plus_selfverify,
            packed_a,
        );
    }
    println!(
        "\n⚠ `prove perms` is the difference of two counted quantities (prove+self-verify, minus a\n\
         second standalone verify), NOT a directly counted number. It is exact only if the\n\
         self-verify and the standalone verify do the same work — they call the same fn on the\n\
         same proof, so they do.\n\
         ⚑ The `verify perms` column is what the LEAF WRAP re-executes in-circuit. Compare it\n\
         against §A's `IN-CIRCUIT POSEIDON2 PERMUTATIONS (exact)`."
    );
}

// ===========================================================================
// §C — LAYERS 3/4: THE APEX and THE SHRINK
// ===========================================================================

// The same real 2-turn fixture `apex_shrink_trace_anatomy.rs` folds, so the two censuses are of
// the SAME object and can be compared line for line.
fn make_turn(balance: u64, nonce: u32, amount: u64) -> FinalizedTurn {
    let state = CellState::new(balance, nonce);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let before_cell = producer_cell(balance as i64, nonce as u64);
    let after_cell = producer_cell((balance as i64) - (amount as i64), nonce as u64);
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let leg = mint_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &receipt_log,
    )
    .expect("rotated leg mints");
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

fn the_chain() -> Vec<FinalizedTurn> {
    vec![make_turn(1000, 0, 7), make_turn(1000 - 7, 1, 7)]
}

/// ⚑ The apex-verifier circuit — censused at BOTH engines it can be committed under: the BabyBear
/// recursion config (what a fold node commits) and the BN254 outer config (what the shrink
/// commits). `apex_shrink_trace_anatomy.rs` reports only the latter, and only as one summed
/// `NonPrimitive ops` count.
#[test]
#[ignore = "MEASUREMENT: one real 2-turn fold + circuit build (no shrink proving). --ignored --nocapture"]
fn l3_apex_and_l4_shrink_census() {
    let t = Instant::now();
    let whole = prove_turn_chain_recursive(&the_chain()).expect("the fixed 2-turn chain folds");
    println!(
        "[upper bound, contended box] apex fold (2 turns: 2 leaves + 2 wraps + 1 fold node): {:?}",
        t.elapsed()
    );

    let inner_config = ir2_leaf_wrap_config();
    let backend = create_recursion_backend();
    let input = whole.root.into_recursion_input_pinned::<BatchOnly>(
        dregg_circuit_prove::fold_vk_pin::child_vk_commit(&whole.root, "apex")
            .expect("apex carries a preprocessed commitment"),
    );
    let t = Instant::now();
    let (circuit, _vr) = build_next_layer_circuit::<DreggRecursionConfig, BatchOnly, _, D>(
        &input,
        &inner_config,
        &backend,
    )
    .expect("apex-verifier circuit builds");
    println!(
        "[upper bound, contended box] apex-verifier circuit build: {:?}",
        t.elapsed()
    );

    let c = census(&circuit);
    print_census("L4 shrink circuit (verifies the apex)", &c);

    let packing = TablePacking::new(1, 4);
    // A fold node commits this circuit under the BabyBear recursion engine, lb 3.
    let sr = shapes_recursion(&circuit, &packing);
    print_shapes("same circuit @ BabyBear recursion engine, lb3", &sr, 3);
    // The shrink commits it under BN254. ⚠ `OUTER_FRI_LOG_BLOWUP` is **3** since the rebalance
    // (`dregg_outer_config.rs:134`); `apex_shrink_trace_anatomy.rs`'s `LOG_BLOWUP = 6` is STALE.
    let so = shapes_outer(&circuit, &packing);
    print_shapes("same circuit @ BN254 outer engine, lb3 (deployed)", &so, 3);
    print_shapes(
        "same circuit @ BN254 outer engine, lb6 (the stale constant)",
        &so,
        6,
    );
}

// ===========================================================================
// §D — THE K≠2 PROOF: packing follow-up tooth #1 (`notes/galois-levers.md` §6)
// ===========================================================================

/// ⚑ **PROVE A WRAP AT K≠2.** The grid (§A `g_packing_grid_over_the_deployed_leaf_wrap`)
/// measured `a4/K16/rec4` as the in-family minimum — wrap 40,554,496 → **28,971,008** cells,
/// ×2.011 cumulative, global max height 2¹⁸ → 2¹⁶ — **via the prover's own shape-extraction
/// call, with no proof ever minted at any K ≠ 2.** This test banks the claim: it is
/// satisfiable-and-refutable by construction (it proves or it refuses), and it carries its own
/// falsifier.
///
/// Four arms, in order, over ONE leaf prove + ONE wrap circuit build (the deployed wrap
/// pipeline exactly: circuit at `recursion_layer_over(ir2_leaf_wrap_config())` — verify the
/// lb6/19q/pow16 child in-circuit, mint at lb3/38q/pow14 — the same object
/// `prove_descriptor_leaf_rotated_with_config` hands `build_and_prove_next_layer`):
///
///   1. **control** — the packing-invariant op census must reproduce the grid's control to the
///      digit (Alu 267,526 / HornerAcc 216,330 / in-circuit perms 38,168 / recompose 160,263)
///      before any geometry or proof is read;
///   2. **geometry** — shape extraction must reproduce the measured 40,554,496 (deployed
///      `a4/K2/rec1`) and 28,971,008 (`a4/K16/rec4`) cells and the 2¹⁸ → 2¹⁶ height drop;
///   3. **prove + verify** — `prove_next_layer` at the K16/rec4 params, verified by the
///      PRODUCTION entry (`verify_recursive_batch_proof_with_config`, which reads the packing
///      off the proof); plus a deployed-packing prove of the same circuit so the VK rotation is
///      MEASURED, not asserted: both verify, and the two `recursion_vk_fingerprint`s differ.
///      Falsifier guard: the K16 proof's own embedded `table_packing` must SAY K16/rec4 — a
///      params-ignoring prover would otherwise render a default-packing proof as "K16 proved"
///      (the falsifier-that-stopped-falsifying class);
///   4. **refusal** — re-run witness generation through the same inline path, prove a CLEAN
///      baseline (validating the path and pinning its proof bytes), then corrupt ONE
///      chain-TAIL `HornerAcc` `out` cell — the committed `out_last` of its packed group
///      (⚠ a MID-chain `out` is NOT a committed cell at K-packing: `trace_to_matrix`
///      recomputes the intermediates from operands, so mutating one is a no-op the first
///      version of this test mistook for unsoundness) — in the Alu trace AND its
///      witness-bus copy, assert the mutation took, prove, assert the forged proof's bytes
///      DIFFER from the clean baseline (the mutation must reach the committed artifact or
///      no verdict exists), and require refusal at prove or at verify.
#[test]
#[ignore = "MEASUREMENT+TOOTH: one real leaf prove + one wrap circuit build + four wrap proves. --ignored --nocapture --test-threads=1"]
fn k16_wrap_proves_and_a_corrupted_trace_refuses() {
    use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
        recursion_vk_fingerprint, verify_recursive_batch_proof_with_config,
    };
    use dregg_recursion_verify::config::recursion_layer_over;
    use p3_batch_stark::ProverData;
    use p3_circuit::ops::Poseidon2Config;
    use p3_circuit::tables::WitnessTrace;
    use p3_circuit::{NpoTypeId, WitnessId};
    use p3_circuit_prover::{AirVariant, BatchStarkProver, CircuitProverData};
    use p3_field::PrimeCharacteristicRing;
    use p3_recursion::{PcsRecursionBackend, ProveNextLayerParams, VerifierCircuitResult};

    let (desc, trace, dpis, map_heaps, mem_boundary) = rotated_transfer_workload();
    let child_config = ir2_leaf_wrap_config();

    let t = Instant::now();
    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc,
        &trace,
        &dpis,
        &mem_boundary,
        &map_heaps,
        &UMemBoundaryWitness::default(),
        &child_config,
    )
    .expect("the rotated transfer leaf proves at the leaf-wrap config");
    println!("[upper bound] inner IR-v2 prove: {:?}", t.elapsed());

    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(&desc, &inner, &dpis, &child_config).expect("verify triple");
    let input: RecursionInput<'_, DreggRecursionConfig, Ir2Air> =
        RecursionInput::NativeBatchStark {
            airs: &airs,
            proof: &inner,
            common_data: &common,
            table_public_inputs,
        };
    let backend = create_recursion_backend();
    // The deployed wrap engine split: in-circuit verify at the child's mint knobs, MINT at
    // lb3/38q/pow14 — what `prove_descriptor_leaf_rotated_with_config` runs.
    let mint_config = recursion_layer_over(&child_config);
    let t = Instant::now();
    let (circuit, vr) = build_next_layer_circuit_with_expose::<DreggRecursionConfig, Ir2Air, _, D>(
        &input,
        &mint_config,
        &backend,
        None,
    )
    .expect("the leaf-wrap verification circuit builds");
    println!("[upper bound] wrap circuit build: {:?}", t.elapsed());

    // ── ARM 1: the packing-invariant control, to the digit, BEFORE anything else is read ──
    let c = census(&circuit);
    print_census("K16 tooth — packing-INVARIANT control", &c);
    assert_eq!(
        c.alu_total(),
        267_526,
        "Alu op census drifted from the grid's control"
    );
    assert_eq!(
        c.n_horner, 216_330,
        "HornerAcc census drifted from the grid's control"
    );
    assert_eq!(
        c.in_circuit_perms(),
        38_168,
        "in-circuit Poseidon2 perm census drifted from the grid's control"
    );
    assert_eq!(
        c.npo_by_type.get("recompose").copied().unwrap_or(0),
        160_263,
        "recompose census drifted from the grid's control"
    );

    // ── ARM 2: the measured geometry, reproduced by the same extraction the prover runs ──
    let deployed_packing = TablePacking::new(1, 4);
    let k16_packing = TablePacking::new(1, 4)
        .with_horner_pack_k(16)
        .with_npo_lanes(NpoTypeId::recompose(), 4);

    let shapes_dep = shapes_recursion(&circuit, &deployed_packing);
    let cells_dep: u64 = shapes_dep.iter().map(|s| s.cells_all()).sum();
    let maxdeg_dep = shapes_dep.iter().map(|s| s.degree).max().unwrap();
    let shapes_k16 = shapes_recursion(&circuit, &k16_packing);
    print_shapes(
        "a4/K16/rec4 — the grid minimum, now to be PROVEN",
        &shapes_k16,
        3,
    );
    let cells_k16: u64 = shapes_k16.iter().map(|s| s.cells_all()).sum();
    let maxdeg_k16 = shapes_k16.iter().map(|s| s.degree).max().unwrap();
    assert_eq!(
        cells_dep, 40_554_496,
        "deployed a4/K2 wrap cells drifted from the grid"
    );
    assert_eq!(
        cells_k16, 28_971_008,
        "a4/K16/rec4 wrap cells drifted from the grid"
    );
    assert_eq!(maxdeg_dep, 18, "deployed global max height should be 2^18");
    assert_eq!(maxdeg_k16, 16, "K16/rec4 global max height should be 2^16");
    let alu16 = shapes_k16
        .iter()
        .find(|s| s.name == "Alu")
        .expect("Alu table");
    assert_eq!(
        (alu16.degree, alu16.main_width, alu16.prep_width),
        (14, 216, 157),
        "the K16 Alu geometry drifted from the grid (2^14 × 216+157)"
    );
    println!(
        "geometry confirmed: deployed {cells_dep} cells (max 2^{maxdeg_dep}) → K16/rec4 \
         {cells_k16} cells (max 2^{maxdeg_k16}), ×{:.3}",
        cells_dep as f64 / cells_k16 as f64
    );

    // ── ARM 3: prove at K16/rec4, verify at the production entry; measure the VK rotation ──
    let params_k16 = ProveNextLayerParams {
        table_packing: k16_packing.clone(),
        constraint_profile: ConstraintProfile::Standard,
    };
    let t = Instant::now();
    let out_k16 = p3_recursion::prove_next_layer::<DreggRecursionConfig, Ir2Air, _, D>(
        &input,
        &circuit,
        &vr,
        &mint_config,
        &backend,
        &params_k16,
        None,
    )
    .expect("⛔ the wrap REFUSED to prove at a4/K16/rec4");
    println!("[upper bound] K16/rec4 wrap prove: {:?}", t.elapsed());

    // Falsifier guard: the proof itself must carry the K16/rec4 packing.
    assert_eq!(
        out_k16.0.table_packing.horner_packed_steps(),
        16,
        "proof does not carry K16"
    );
    assert_eq!(
        out_k16.0.table_packing.alu_lanes(),
        4,
        "proof does not carry a4"
    );
    assert_eq!(
        out_k16.0.table_packing.npo_lanes(&NpoTypeId::recompose()),
        Some(4),
        "proof does not carry rec4"
    );

    verify_recursive_batch_proof_with_config(&out_k16.0, &mint_config)
        .expect("⛔ the K16/rec4 wrap proof FAILED production verification");
    let vk_k16 = recursion_vk_fingerprint(&out_k16.0);
    println!(
        "✅ a4/K16/rec4 wrap: proved and production-verified. vk = {}",
        vk_k16.to_hex()
    );

    let t = Instant::now();
    let out_dep = p3_recursion::prove_next_layer::<DreggRecursionConfig, Ir2Air, _, D>(
        &input,
        &circuit,
        &vr,
        &mint_config,
        &backend,
        &ProveNextLayerParams::default(),
        None,
    )
    .expect("the deployed-packing control wrap proves");
    println!("[upper bound] deployed a4/K2 wrap prove: {:?}", t.elapsed());
    verify_recursive_batch_proof_with_config(&out_dep.0, &mint_config)
        .expect("the deployed-packing control proof verifies");
    let vk_dep = recursion_vk_fingerprint(&out_dep.0);
    println!(
        "deployed a4/K2 control: proved and verified. vk = {}",
        vk_dep.to_hex()
    );
    assert_ne!(
        vk_dep, vk_k16,
        "⛔ the packing retune did NOT rotate the VK — the preprocessed commitment does not \
         cover the packing, so \"VK rotation only\" is FALSE and the deployment story is wrong"
    );
    println!(
        "⚑ VK ROTATION MEASURED: deployed {} ≠ K16 {}",
        vk_dep.to_hex(),
        vk_k16.to_hex()
    );

    // ── ARM 4: the corrupted-trace refusal at the SAME geometry, mutation asserted first ──
    //
    // Inline `prove_next_layer`'s non-cached body so the traces are in hand between witness
    // generation and proving — every step below `runner.run()` is verbatim its recipe.
    //
    // ⚑ MUTATION SITE, chosen off the COMMITTED layout (`alu_air.rs::trace_to_matrix`,
    // read 2026-08-17): a `PackedHorner(first, k)` group commits the FIRST op's `a,b,c`,
    // the per-step `(a_t, c_t)` pairs, recomputed intermediate accs, and the LAST op's
    // `out` — a MID-chain `out` is NOT a committed cell (the intermediates are recomputed
    // from operands), so mutating one is a no-op on the committed artifact. The first
    // version of this test did exactly that and its "refusal" assert fired on a proof that
    // was legitimately accepted — the falsifier was dead, not the prover unsound. The
    // mutation is now a chain-TAIL `out` (last op of its chain ⇒ last op of its packed
    // group ⇒ committed and bus-carried), and the arm carries an artifact-level falsifier:
    // the corrupted proof's bytes must DIFFER from a clean same-path baseline, or the
    // mutation demonstrably never reached the commitment and the arm refuses to conclude.
    let preprocessors: Vec<Box<dyn NpoPreprocessor<P3BabyBear>>> = vec![
        poseidon2_preprocessor::<P3BabyBear>(),
        recompose_preprocessor::<P3BabyBear>(false),
        expose_claim_preprocessor::<P3BabyBear>(),
    ];
    let air_builders: Vec<Box<dyn NpoAirBuilder<DreggRecursionConfig, D>>> = {
        let mut b = poseidon2_air_builders::<DreggRecursionConfig, D>();
        b.extend(recompose_air_builders::<DreggRecursionConfig, D>(1, false));
        b.extend(expose_claim_air_builders::<DreggRecursionConfig, D>());
        b
    };
    let (airs_degrees, primitive_columns, non_primitive_columns) =
        get_airs_and_degrees_with_prep::<DreggRecursionConfig, EF, D>(
            &circuit,
            &k16_packing,
            &preprocessors,
            &air_builders,
            ConstraintProfile::Standard,
        )
        .expect("K16 table-AIR extraction for the corrupted arm");
    let (t_airs, degrees): (Vec<_>, Vec<usize>) = airs_degrees.into_iter().unzip();

    let gen_traces = || {
        let public_inputs = vr.pack_public_inputs(&input).expect("pack public inputs");
        let private_inputs = vr.pack_private_inputs(&input).expect("pack private inputs");
        let mut runner = circuit.runner();
        runner
            .set_public_inputs(&public_inputs)
            .expect("public inputs");
        runner
            .set_private_inputs(&private_inputs)
            .expect("private inputs");
        let op_ids = <_ as VerifierCircuitResult<DreggRecursionConfig, Ir2Air>>::op_ids(&vr);
        backend
            .set_private_data(&mint_config, &mut runner, op_ids, &input)
            .expect("FRI private data");
        runner.run().expect("witness generation")
    };

    // The prover for this arm — verbatim the prove_next_layer recipe at K16/rec4.
    // (`DreggRecursionConfig` is non-ZK, so ext_degrees == degrees — `prove_next_layer` adds
    // `config.is_zk()` = 0 here.)
    let prover_data = ProverData::from_airs_and_degrees(&mint_config, &t_airs, &degrees);
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);
    let mut prover = BatchStarkProver::new(mint_config.clone())
        .with_table_packing(k16_packing.clone())
        .with_alu_variant(AirVariant::Baseline);
    prover.register_poseidon2_table::<D>(Poseidon2Config::BABY_BEAR_D4_W16);
    prover.register_poseidon2_table::<D>(Poseidon2Config::BABY_BEAR_D4_W24);
    prover.register_recompose_table::<D>(false);
    prover.register_expose_claim_table::<D>();

    // Clean baseline through the SAME inline path: validates the path independently and
    // provides the proof bytes the corrupted proof must differ from.
    let clean_traces = gen_traces();
    let baseline = prover
        .prove_all_tables(&clean_traces, &circuit_prover_data)
        .expect("the clean inline-path K16 prove succeeds");
    verify_recursive_batch_proof_with_config(&baseline, &mint_config)
        .expect("the clean inline-path K16 proof verifies");
    let baseline_bytes = postcard::to_allocvec(&baseline).expect("baseline postcards");
    drop(clean_traces);

    // The mutation: one chain-TAIL HornerAcc `out`, +1, in BOTH the Alu trace and the
    // witness bus (rebuilt — `WitnessTrace` has no setter). A chain tail is the last op of
    // its packed group, so its `out` IS the committed `out_last` cell and carries the
    // group's bus `mult_out`; the packed-row chain arithmetic (and any downstream
    // consumer's bus check against the corrupted witness) must refuse it.
    let mut traces = gen_traces();
    let (mut_idx, orig_out) = {
        let alu = &traces.alu_trace;
        let n_ops = alu.op_kind.len();
        let i = (0..n_ops)
            .find(|&i| {
                alu.op_kind[i] == AluOpKind::HornerAcc
                    && (i + 1 == n_ops || alu.op_kind[i + 1] != AluOpKind::HornerAcc)
            })
            .expect("a chain-tail HornerAcc exists");
        (i, alu.values[i][3])
    };
    let delta = EF::ONE;
    let corrupted_out = orig_out + delta;
    traces.alu_trace.values[mut_idx][3] = corrupted_out;
    let out_wid: WitnessId = traces.alu_trace.indices[mut_idx][3];
    let n_wit = traces.witness_trace.num_rows();
    let mut wit_vals: Vec<EF> = (0..n_wit)
        .map(|j| {
            *traces
                .witness_trace
                .get_value(WitnessId(j as u32))
                .expect("witness value")
        })
        .collect();
    let orig_wit = wit_vals[out_wid.0 as usize];
    wit_vals[out_wid.0 as usize] = orig_wit + delta;
    traces.witness_trace = WitnessTrace::new(wit_vals);

    // ⚑ MUTATION ASSERTED BEFORE THE VERDICT IS READ (the falsifier-that-stopped-falsifying
    // class): both copies must have actually changed — and below, the proof bytes must too.
    assert_ne!(
        traces.alu_trace.values[mut_idx][3], orig_out,
        "Alu mutation did not take"
    );
    assert_eq!(traces.alu_trace.values[mut_idx][3], corrupted_out);
    assert_ne!(
        *traces
            .witness_trace
            .get_value(out_wid)
            .expect("witness value"),
        orig_wit,
        "witness-bus mutation did not take"
    );
    println!(
        "mutation asserted: chain-tail HornerAcc op #{mut_idx} out (witness id {}) += 1, in \
         Alu trace AND witness bus (successor op kind: {:?})",
        out_wid.0,
        traces.alu_trace.op_kind.get(mut_idx + 1)
    );

    let t = Instant::now();
    let prove_attempt = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prover.prove_all_tables(&traces, &circuit_prover_data)
    }));
    match prove_attempt {
        Err(panic) => {
            let msg = panic
                .downcast_ref::<String>()
                .map(String::as_str)
                .or_else(|| panic.downcast_ref::<&str>().copied())
                .unwrap_or("<non-string panic>");
            println!("✅ REFUSED at PROVE (panic) after {:?}: {msg}", t.elapsed());
        }
        Ok(Err(e)) => {
            println!("✅ REFUSED at PROVE (error) after {:?}: {e}", t.elapsed());
        }
        Ok(Ok(forged)) => {
            println!(
                "[upper bound] corrupted-trace prove completed in {:?}; the refusal must now \
                 come from the verifier",
                t.elapsed()
            );
            // The artifact-level falsifier: if the mutation never reached the committed
            // transcript, the proof is byte-identical to the clean baseline and this arm
            // has measured NOTHING — refuse to conclude rather than read the verdict.
            let forged_bytes = postcard::to_allocvec(&forged).expect("forged postcards");
            assert_ne!(
                forged_bytes, baseline_bytes,
                "⛔ the mutation did not reach the committed artifact (proof bytes identical \
                 to the clean baseline) — the falsifier is DEAD, no refusal verdict exists"
            );
            let verdict = verify_recursive_batch_proof_with_config(&forged, &mint_config);
            assert!(
                verdict.is_err(),
                "⛔⛔ THE CORRUPTED K16 TRACE VERIFIED — a committed chain-tail Horner cell \
                 was forged (proof bytes differ from clean) and the K16 packed-row chain \
                 constraint did not refuse; the geometry is UNSOUND and must not land"
            );
            println!("✅ REFUSED at VERIFY: {}", verdict.unwrap_err());
        }
    }
    println!(
        "\n⚑ K≠2 BANKED: a4/K16/rec4 proves ({cells_k16} cells, max 2^{maxdeg_k16}), the \
         production verifier accepts it, the VK rotates, and a consistent single-step Horner \
         forgery at the same geometry refuses."
    );
}

// ===========================================================================
// §UD — THE UD-100 / BLOWUP-DROP GRID OVER THE LEAF WRAP (2026-11-05)
// ===========================================================================

/// One grid point: the child is MINTED at `(lb, q, pow)` and the leaf wrap VERIFIES it at the same
/// knobs (`create_recursion_config_with_fri` sets both roles). Counts only:
///
/// * child Σcells (committed, pre-LDE) and Σcells·2^lb (the LDE the leaf prover hashes);
/// * the wrap circuit's EXACT in-circuit Poseidon2 permutation count (op census);
/// * the wrap's committed geometry at the deployed packing `p1/a4`, cells(main+prep), and its
///   native leaf-sponge permutations at the deployed wrap mint blowup 3.
///
/// No wrap is proved; no clock is evidence. The decision rule this feeds
/// (`docs/PROOF-SYSTEM-SPACE.md` U8): the blowup drop wins iff the per-turn total falls.
fn ud_grid_point<
    F: FnOnce() -> (
        dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
        Vec<Vec<dregg_circuit::field::BabyBear>>,
        Vec<dregg_circuit::field::BabyBear>,
        Vec<Vec<dregg_circuit::heap_root::HeapLeaf>>,
        MemBoundaryWitness,
    ),
>(
    child_label: &str,
    workload: F,
    lb: usize,
    q: usize,
    pow: usize,
) {
    use dregg_circuit_prove::plonky3_recursion_impl::recursive::create_recursion_config_with_fri;
    let (desc, trace, dpis, map_heaps, mem_boundary) = workload();
    let config = create_recursion_config_with_fri(lb, 0, 1, q, 0, pow);
    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc,
        &trace,
        &dpis,
        &mem_boundary,
        &map_heaps,
        &UMemBoundaryWitness::default(),
        &config,
    )
    .unwrap_or_else(|e| panic!("{child_label} proves at ({lb},{q},{pow}): {e}"));
    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(&desc, &inner, &dpis, &config).expect("verify triple");
    let mut child_cells = 0u64;
    for (i, air) in airs.iter().enumerate() {
        let w = BaseAir::<P3BabyBear>::width(air) as u64;
        let dbits = inner.degree_bits.get(i).copied().unwrap_or(0);
        child_cells += (1u64 << dbits) * w;
    }
    let input: RecursionInput<'_, DreggRecursionConfig, Ir2Air> =
        RecursionInput::NativeBatchStark {
            airs: &airs,
            proof: &inner,
            common_data: &common,
            table_public_inputs,
        };
    let backend = create_recursion_backend();
    let (circuit, _vr) =
        build_next_layer_circuit_with_expose::<DreggRecursionConfig, Ir2Air, _, D>(
            &input, &config, &backend, None,
        )
        .expect("the leaf-wrap verification circuit builds");
    let c = census(&circuit);
    let shapes = shapes_recursion(&circuit, &TablePacking::new(1, 4));
    let wrap_cells: u64 = shapes.iter().map(|s| s.cells_all()).sum();
    let wrap_rows: u64 = shapes.iter().map(|s| s.rows()).sum();
    let wrap_leaf_perms_lb3: u64 = shapes.iter().map(|s| s.leaf_perms(3)).sum();
    println!(
        "UDGRID\t{child_label}\tlb={lb}\tq={q}\tpow={pow}\tchild_cells={child_cells}\t\
         child_lde_cells={}\tqueries_in_proof={}\twrap_incircuit_p2_perms={}\t\
         wrap_alu_ops={}\twrap_cells_main_prep={wrap_cells}\twrap_rows={wrap_rows}\t\
         wrap_native_leaf_perms_lb3={wrap_leaf_perms_lb3}",
        child_cells << lb,
        q,
        c.in_circuit_perms(),
        c.alu_total(),
    );
}

/// A 2^16-row WIDE ARITHMETIC child: the sound Pasta field multiply (190 declared columns, 694
/// committed), cycled. It is row-local (no transition leg), so cycling an honest block is a valid
/// witness (`fri_blowup_global_knob_survey.rs::cycle_to`). Honest label: a stand-in for a large
/// zkML leaf's SHAPE (tall, wide, arithmetic), not a zkML descriptor.
fn wide_arith_child_2_16() -> (
    dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    Vec<Vec<dregg_circuit::field::BabyBear>>,
    Vec<dregg_circuit::field::BabyBear>,
    Vec<Vec<dregg_circuit::heap_root::HeapLeaf>>,
    MemBoundaryWitness,
) {
    const MUL_DESC_JSON: &str =
        include_str!("../../circuit/descriptors/by-name/pasta-fpmul-sound.json");
    const MUL_TRACE: &str =
        include_str!("../../circuit/tests/fixtures/pasta-fpmul-sound-trace.txt");
    let base: Vec<Vec<dregg_circuit::field::BabyBear>> = MUL_TRACE
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|t| dregg_circuit::field::BabyBear::new(t.parse::<u32>().expect("u32 cell")))
                .collect()
        })
        .collect();
    let desc = parse_vm_descriptor2(MUL_DESC_JSON).expect("fpmul parses");
    let n = 1usize << 16;
    let trace = (0..n).map(|i| base[i % base.len()].clone()).collect();
    (desc, trace, vec![], vec![], MemBoundaryWitness::default())
}

const UD_GRID: [(usize, usize, usize); 4] = [(6, 19, 16), (6, 86, 16), (2, 57, 16), (2, 148, 0)];

#[test]
#[ignore = "MEASUREMENT (counts): 4 rotated-leaf proves + 4 wrap circuit builds. --ignored --nocapture --test-threads=1"]
fn ud_grid_over_the_rotated_transfer_leaf() {
    for (lb, q, pow) in UD_GRID {
        ud_grid_point("rotated-transfer", rotated_transfer_workload, lb, q, pow);
    }
}

#[test]
#[ignore = "MEASUREMENT (counts): 4 proves of a 2^16-row x 694-wide child + 4 wrap circuit builds. --ignored --nocapture --test-threads=1"]
fn ud_grid_over_a_2_16_row_wide_child() {
    for (lb, q, pow) in UD_GRID {
        ud_grid_point("wide-arith-2^16", wide_arith_child_2_16, lb, q, pow);
    }
}
