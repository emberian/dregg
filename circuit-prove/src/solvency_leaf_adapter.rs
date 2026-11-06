//! The SOLVENCY leaf — a real reserve-covers-liabilities STARK re-proven as a
//! RECURSION-FOLDABLE IR-v2 leaf, exposing a committed solvency claim. The first
//! FINANCIAL leaf of the "everything is a leaf" moat (`docs/deos/DREGGFI-AMBITION.md`
//! §B.2 #1): a structured product is a single apex proof that folds N sub-proofs as
//! leaves, and this is the solvency face of it.
//!
//! ## What this leaf proves (the instance) — and what it does NOT (the ∀-schedule)
//!
//! The leaf proves ONE reserve state is solvent: for a hidden reserve `R` and hidden
//! liabilities `L`, `R ≥ L`, exposing the committed tuple `[reserve_commit,
//! liability_commit]` where `reserve_commit = hash_fact(R, [salt_r,0,0,0])` and
//! `liability_commit = hash_fact(L, [salt_l,0,0,0])`. This is the CIRCUIT-grade
//! instance solvency: "this reserve state covers its liabilities, and here are the
//! two commitments that bind it".
//!
//! The ∀-SCHEDULE solvency — that the reserve fund is never negative along EVERY
//! adversarial attest/reverse/spend/finalize schedule — is the Lean tower
//! `Dregg2/Verify/StripeReserve.lean` (`stripe_reserve_solvent_forever`, the
//! `escrow_solvent_forever` apex over `SSched`, `#assert_axioms`-clean). This leaf
//! does NOT re-prove that; it proves an instance the Lean invariant abstracts, and
//! composes with it by citation (the Lean theorem says the reserve state STAYS
//! solvent; this leaf says a GIVEN state IS solvent, as a foldable proof).
//!
//! ## Integer comparison, emitted from Lean
//!
//! `SolvencyLeafEmit.solvencyDescriptor` ranges reserve, liability and difference
//! as two 15-bit limbs each, and enforces a borrow chain with no final borrow.
//! Thus both amounts lie in `[0, 2^30)` and `reserve - liability = difference`
//! holds over the integers, not merely modulo BabyBear. The earlier constructor
//! ranged only the modular difference: even `(0, 2^30-1)` passed that check.
//! Arithmetic constraints bind the first row, including a one-row trace.
//! Rust parses the generated artifact and builds witnesses; it authors no gates.
//!
//! ## The claim tuple — `[reserve_commit, liability_commit]`, bound to the solvent R,L
//!
//! The two commitments are recomputed IN-AIR (two unconditional arity-7 `hash_fact`
//! chip sites over the PI-pinned commitment columns, the SAME fact-sponge carrier the
//! `note_spend_leaf_adapter` uses — KAT-pinned by `fact_arity7_chip_absorb_matches_hash_fact`)
//! and pinned to PI 0 / PI 1. Because `reserve_commit` opens to the SAME `R` the range
//! gadget compares (both read the row-0 `R` column) and likewise for `L`, the exposed
//! tuple certifies "there exist `R, L` with these commitments and `R ≥ L`". The PI
//! must equal the computed fact-hash head; an insolvent `R < L` is UNSAT.
//! The public tuple omits `R`, `L`, and salts;
//! no cryptographic hiding guarantee follows from that fact alone. Scalar fact hashes
//! retain their existing collision and blinding-space limitations.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, UMemBoundaryWitness, parse_vm_descriptor2,
    prove_vm_descriptor2_for_config,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::poseidon2::hash_fact;

use p3_recursion::{ProveNextLayerParams, RecursionOutput};

use crate::fold_vk_pin::FoldVkPins;
use crate::ivc_turn_chain::{
    prove_descriptor_leaf_rotated_with_config, prove_descriptor_leaf_with_pi_slice_expose,
};
use crate::joint_turn_aggregation::JointAggError;
use crate::plonky3_recursion_impl::recursive::DreggRecursionConfig;

/// Extension degree of the recursion config's PCS (the BabyBear-quartic stack).
const D: usize = 4;

/// Supported amount width; both reserve and liability are range-constrained in AIR.
pub const RANGE_BITS: usize = 30;

/// The exposed claim width: `[reserve_commit, liability_commit]`.
pub const SOLVENCY_CLAIM_LEN: usize = 2;

/// PI slot of the reserve commitment.
pub const RESERVE_COMMIT_PI: usize = 0;
/// PI slot of the liability commitment.
pub const LIABILITY_COMMIT_PI: usize = 1;

// ---- Trace column layout (the extended base, before the chip lane columns) ----
/// The HIDDEN reserve `R` (compared by the range gadget, opened by the commitment).
const R_COL: usize = 0;
/// The HIDDEN liabilities `L`.
const L_COL: usize = 1;
/// The HIDDEN reserve-commitment blinding salt.
const SALT_R_COL: usize = 2;
/// The HIDDEN liability-commitment blinding salt.
const SALT_L_COL: usize = 3;
/// `reserve_commit = hash_fact(R, [salt_r,0,0,0])`, pinned to PI 0.
const RESERVE_COMMIT_COL: usize = 4;
/// `liability_commit = hash_fact(L, [salt_l,0,0,0])`, pinned to PI 1.
const LIABILITY_COMMIT_COL: usize = 5;
/// `diff = R − L`, range-proven in `[0, 2^RANGE_BITS)`.
const DIFF_COL: usize = 6;
// The layout is emitted by SolvencyLeafEmit. Six little-endian 15-bit limbs
// occupy 7..13; their bit witnesses occupy 13..103; one internal borrow at 103.
const LIMB_BASE: usize = 7;
const LIMB_BITS: usize = 15;
const BIT_BASE: usize = 13;
const BORROW_COL: usize = 103;
const EXT_BASE_WIDTH: usize = 104;

fn felt(v: u64) -> BabyBear {
    BabyBear::new((v % (BABYBEAR_P as u64)) as u32)
}

/// Parse the Lean-owned, bounded-integer solvency AIR. The v2 identity marks the
/// added operand ranges and borrow constraints; old v1 proofs use a different VK.
pub fn solvency_to_descriptor2() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(include_str!(
        "../../circuit/descriptors/by-name/solvency-leaf-v2.json"
    ))
    .expect("Lean-emitted solvency descriptor decodes")
}

/// A solvency witness: the reserve `R`, liabilities `L`, and the two hidden
/// commitment salts. Honest `0 ≤ L ≤ R < 2^RANGE_BITS`.
#[derive(Clone, Debug)]
pub struct SolvencyWitness {
    /// The reserve (real collateral backing the liabilities).
    pub reserve: u64,
    /// The liabilities the reserve must cover.
    pub liability: u64,
    /// The reserve-commitment blinding salt.
    pub salt_reserve: u64,
    /// The liability-commitment blinding salt.
    pub salt_liability: u64,
}

impl SolvencyWitness {
    /// `reserve_commit = hash_fact(R, [salt_r, 0, 0, 0])`.
    pub fn reserve_commit(&self) -> BabyBear {
        hash_fact(
            felt(self.reserve),
            &[
                felt(self.salt_reserve),
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
            ],
        )
    }
    /// `liability_commit = hash_fact(L, [salt_l, 0, 0, 0])`.
    pub fn liability_commit(&self) -> BabyBear {
        hash_fact(
            felt(self.liability),
            &[
                felt(self.salt_liability),
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
            ],
        )
    }
}

/// The HONEST 2-slot claim tuple for a witness: `[reserve_commit, liability_commit]`.
pub fn solvency_leaf_public_inputs(witness: &SolvencyWitness) -> Vec<BabyBear> {
    vec![witness.reserve_commit(), witness.liability_commit()]
}

/// Build the extended base trace (2 rows: the minimal power-of-two height; every
/// constraint is row-local and holds identically on both, the row-0 pins the PIs).
/// Chip lane columns are filled by the general prover's `fill_chip_lanes`.
fn solvency_leaf_base_trace(witness: &SolvencyWitness) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let r = felt(witness.reserve);
    let l = felt(witness.liability);
    let diff = r - l; // field subtraction; honest R ≥ L gives a small non-negative diff.
    let rc = witness.reserve_commit();
    let lc = witness.liability_commit();

    let mut row = vec![BabyBear::ZERO; EXT_BASE_WIDTH];
    row[R_COL] = r;
    row[L_COL] = l;
    row[SALT_R_COL] = felt(witness.salt_reserve);
    row[SALT_L_COL] = felt(witness.salt_liability);
    row[RESERVE_COMMIT_COL] = rc;
    row[LIABILITY_COMMIT_COL] = lc;
    row[DIFF_COL] = diff;
    let mask = (1u32 << LIMB_BITS) - 1;
    let amounts = [r.as_u32(), l.as_u32(), diff.as_u32()];
    for (pair, value) in amounts.into_iter().enumerate() {
        for half in 0..2 {
            let k = 2 * pair + half;
            let limb = (value >> (half * LIMB_BITS)) & mask;
            row[LIMB_BASE + k] = BabyBear::new(limb);
            for bit in 0..LIMB_BITS {
                row[BIT_BASE + k * LIMB_BITS + bit] = BabyBear::new((limb >> bit) & 1);
            }
        }
    }
    row[BORROW_COL] = BabyBear::new(u32::from((r.as_u32() & mask) < (l.as_u32() & mask)));

    let trace = vec![row.clone(), row];
    (trace, vec![rc, lc])
}

/// The shared inner IR-v2 prove (descriptor + trace + batch mint under the recursion
/// config type).
fn prove_solvency_inner(
    witness: &SolvencyWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<
    (
        EffectVmDescriptor2,
        dregg_circuit::descriptor_ir2::Ir2BatchProof<DreggRecursionConfig>,
    ),
    String,
> {
    if public_inputs.len() != SOLVENCY_CLAIM_LEN {
        return Err(format!(
            "solvency leaf expects {SOLVENCY_CLAIM_LEN} PI slots, got {}",
            public_inputs.len()
        ));
    }
    if witness.reserve >= (1u64 << RANGE_BITS) || witness.liability >= (1u64 << RANGE_BITS) {
        return Err("solvency amounts must be below 2^30; the AIR enforces this range".into());
    }
    let desc2 = solvency_to_descriptor2();
    let (base_trace, _honest_pis) = solvency_leaf_base_trace(witness);

    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc2,
        &base_trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .map_err(|e| format!("solvency leaf inner IR-v2 prove failed: {e}"))?;
    Ok((desc2, inner))
}

/// Prove a solvency instance as a RECURSION-FOLDABLE IR-v2 leaf (no claim expose).
///
/// For an HONEST proof, `public_inputs` is [`solvency_leaf_public_inputs`]. An
/// insolvent reserve (`R < L`) or a forged commitment is UNSAT — no foldable leaf is
/// minted (the leaf-level tooth).
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_solvency_leaf(
    witness: &SolvencyWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let (desc2, inner) = prove_solvency_inner(witness, public_inputs, config)?;
    prove_descriptor_leaf_rotated_with_config(&desc2, &inner, public_inputs, config)
        .map_err(|e| format!("solvency leaf recursion wrap failed: {e}"))
}

/// Prove a solvency leaf AND RE-EXPOSE its 2-slot claim tuple `[reserve_commit,
/// liability_commit]` as an IN-CIRCUIT `expose_claim` (lanes `[0 ..
/// SOLVENCY_CLAIM_LEN)`), read from the leaf's own FRI-bound descriptor PIs — the
/// solvency analog of `note_spend_leaf_adapter::prove_note_spend_leaf_with_claim`.
/// This is the form the structured-product fold folds.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_solvency_leaf_with_claim(
    witness: &SolvencyWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let (desc2, inner) = prove_solvency_inner(witness, public_inputs, config)?;
    prove_descriptor_leaf_with_pi_slice_expose(
        &desc2,
        &inner,
        public_inputs,
        config,
        0,
        SOLVENCY_CLAIM_LEN,
    )
    .map_err(|e| format!("solvency claim leaf expose-wrap failed: {e}"))
}

/// Read the exposed 2-lane solvency claim off a leaf minted by
/// [`prove_solvency_leaf_with_claim`].
pub fn read_exposed_solvency_claim(
    output: &RecursionOutput<DreggRecursionConfig>,
) -> Option<[BabyBear; SOLVENCY_CLAIM_LEN]> {
    use p3_field::PrimeField32;
    let claims: Vec<BabyBear> = output
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")?
        .public_values
        .iter()
        .map(|&v| BabyBear::new(v.as_canonical_u32()))
        .collect();
    if claims.len() < SOLVENCY_CLAIM_LEN {
        return None;
    }
    Some(core::array::from_fn(|i| claims[i]))
}

// ============================================================================
// THE STRUCTURED-PRODUCT FOLD — "everything is a leaf"
// ============================================================================

/// The combined claim width of the marquee structured product:
/// note-spend (7 lanes) ++ solvency (2 lanes).
pub const STRUCTURED_PRODUCT_CLAIM_LEN: usize =
    crate::note_spend_leaf_adapter::NOTE_SPEND_CLAIM_LEN + SOLVENCY_CLAIM_LEN;

/// **THE PROOF-CARRYING STRUCTURED PRODUCT — ONE apex folding TWO sub-proofs as
/// leaves.** Fold a note-spend claim leaf ([`crate::note_spend_leaf_adapter::prove_note_spend_leaf_with_claim`])
/// AND a solvency claim leaf ([`prove_solvency_leaf_with_claim`]) into a SINGLE
/// recursion apex that VERIFIES BOTH leaves (the aggregation layer recursively checks
/// each child's FRI-bound proof) and EXPOSES THE COMBINED CLAIM `[…note-spend 7… ,
/// reserve_commit, liability_commit]`.
///
/// This is the structured product of `DREGGFI-AMBITION` §B.2 #1: a single apex a
/// venue verifies ONCE, on any chain, carrying both economic facts as proofs. No
/// `connect` binds the two leaves — they are INDEPENDENT financial facts (a spend and
/// a solvency), each verified on its own merits and re-exposed in the union.
///
/// **Reusable-as-a-leaf (the recursion payoff).** The output is itself a
/// claim-carrying `RecursionOutput` (it exposes an `expose_claim` table of the
/// combined tuple), so it is a valid input to another [`prove_claim_union_fold`] — a
/// structured product can be a LEG of a bigger one (a fund-of-funds). The ONE level
/// is proven here; the n-level composition is `prove_claim_union_fold` applied
/// recursively (each level folds two claim leaves into one, exposing the union).
///
/// ⚠ `config` is a FOLD config — it must verify its children at the engine those leaves were
/// MINTED at, which since the leaf-wrap mint split is `create_recursion_config`'s, not
/// `ir2_leaf_wrap_config`'s. Take it from
/// [`crate::ivc_turn_chain::turn_chain_root_config`]. (The docline here used to say
/// `ir2_leaf_wrap_config`, which was right only while a leaf inherited its child's engine.)
pub fn prove_structured_product_fold(
    note_spend_leaf: &RecursionOutput<DreggRecursionConfig>,
    solvency_leaf: &RecursionOutput<DreggRecursionConfig>,
    // ⚑ The children's VK-identity pins, threaded to the node below (`crate::fold_vk_pin`).
    pins: &FoldVkPins,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    prove_claim_union_fold(
        note_spend_leaf,
        crate::note_spend_leaf_adapter::NOTE_SPEND_CLAIM_LEN,
        solvency_leaf,
        SOLVENCY_CLAIM_LEN,
        pins,
        config,
    )
}

/// **THE GENERIC CLAIM-UNION FOLD (the composition primitive).** Fold ANY two
/// claim-carrying leaves (`left` re-exposing `≥ left_len` lanes, `right` re-exposing
/// `≥ right_len` lanes) into ONE apex that verifies both and exposes the UNION
/// `left[0..left_len] ++ right[0..right_len]`. Because the apex ITSELF carries an
/// `expose_claim` table of that union, it is a valid `left`/`right` for a further
/// fold — this is what makes structured products recursively composable ("everything
/// is a leaf"). Mirrors `note_spend_leaf_adapter::prove_note_spend_binding_node`'s
/// aggregation shape, minus the `connect` (a union, not a binding).
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_claim_union_fold(
    left_leaf: &RecursionOutput<DreggRecursionConfig>,
    left_len: usize,
    right_leaf: &RecursionOutput<DreggRecursionConfig>,
    right_len: usize,
    // ⚑ The children's VK-identity pins (`crate::fold_vk_pin`). Unpinned, each child's
    // preprocessed commitment is an unconstrained runtime public input and a same-shape /
    // different-constants child — a VALID proof of a DIFFERENT circuit — folds through.
    // ⚠ No host pre-flight compares these against the children: the refusal is the circuit's.
    pins: &FoldVkPins,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use crate::ivc_turn_chain::expose_claim_instance_index;
    use crate::plonky3_recursion_impl::recursive::create_recursion_backend;
    use p3_circuit::CircuitBuilder;
    use p3_recursion::{BatchOnly, Target, build_and_prove_aggregation_layer_with_expose};

    type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

    let left_idx = expose_claim_instance_index(&left_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason:
                "structured-product fold: left leaf carries no re-exposed claim (expose_claim) \
                     table — mint it via a *_with_claim adapter"
                    .to_string(),
        }
    })?;
    let right_idx = expose_claim_instance_index(&right_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason:
                "structured-product fold: right leaf carries no re-exposed claim (expose_claim) \
                     table — mint it via a *_with_claim adapter"
                    .to_string(),
        }
    })?;

    let left = left_leaf.into_recursion_input_pinned::<BatchOnly>(pins.left.clone());
    let right = right_leaf.into_recursion_input_pinned::<BatchOnly>(pins.right.clone());

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>],
                       _left_vk_cap: &[Target],
                       _right_vk_cap: &[Target]| {
        let lg = left_apt
            .get(left_idx)
            .expect("left leaf's re-exposed claim instance present");
        let rg = right_apt
            .get(right_idx)
            .expect("right leaf's re-exposed claim instance present");
        debug_assert!(
            lg.len() >= left_len && rg.len() >= right_len,
            "each leaf must re-expose at least its claim lanes"
        );
        // THE COMBINED CLAIM: the union of both leaves' claims, exposed as the apex's
        // public output. Both sub-proofs are recursively verified by the aggregation
        // layer, so the union is carried by a proof that checked BOTH.
        let mut combined: Vec<Target> = (0..left_len).map(|k| lg[k]).collect();
        combined.extend((0..right_len).map(|k| rg[k]));
        cb.expose_as_public_output(&combined);
    };

    build_and_prove_aggregation_layer_with_expose::<DreggRecursionConfig, BatchOnly, BatchOnly, _, D>(
        &left,
        &right,
        &crate::ivc_turn_chain::fold_layer_over_leaves(config),
        &backend,
        &params,
        None,
        Some(&expose),
    )
    .map_err(|e| JointAggError::AggregationProofInvalid {
        reason: format!("structured-product claim-union fold failed: {e:?}"),
    })
}

/// Read the combined structured-product claim (note-spend ++ solvency) off the apex
/// produced by [`prove_structured_product_fold`].
pub fn read_structured_product_claim(
    output: &RecursionOutput<DreggRecursionConfig>,
) -> Option<[BabyBear; STRUCTURED_PRODUCT_CLAIM_LEN]> {
    use p3_field::PrimeField32;
    let claims: Vec<BabyBear> = output
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")?
        .public_values
        .iter()
        .map(|&v| BabyBear::new(v.as_canonical_u32()))
        .collect();
    if claims.len() < STRUCTURED_PRODUCT_CLAIM_LEN {
        return None;
    }
    Some(core::array::from_fn(|i| claims[i]))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binding_tooth::report_refusal;
    use crate::ivc_turn_chain::ir2_leaf_wrap_config;
    use dregg_circuit::descriptor_ir2::{
        CHIP_OUT_LANES, TID_P2, VmConstraint2, chip_absorb_all_lanes,
    };
    use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};
    const SV_FACT_MARK: u32 = 0xFACF;
    use dregg_circuit::note_spending_witness::{NoteSpendingWitness, test_spending_key};
    use dregg_circuit::poseidon2::hash_many;
    use dregg_circuit::refusal::{assert_violated_constraint_not_bus, must_refuse_or_unsat_panic};

    /// THE FEASIBILITY KAT: the unconditional fact site's arity-7 absorb reproduces
    /// `hash_fact(R, [salt,0,0,0])` — the seeding equivalence the commitment openings
    /// rest on (the solvency twin of the note-spend KAT).
    #[test]
    fn fact_arity7_chip_absorb_matches_hash_fact() {
        let r = BabyBear::new(1_000_000);
        let salt = BabyBear::new(0x5EED);
        let ins = [
            r,
            salt,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::new(SV_FACT_MARK),
            BabyBear::ONE,
        ];
        assert_eq!(
            chip_absorb_all_lanes(7, &ins)[0],
            hash_fact(r, &[salt, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO]),
            "the solvency commitment fact site must reproduce hash_fact exactly"
        );
    }

    /// The descriptor lowers to the expected shape: 2 chip sites (the two openings),
    /// 90 Boolean limb gates, six reconstructions, six borrow/assembly gates, and 2 PI pins.
    #[test]
    fn solvency_descriptor_lowers() {
        let desc2 = solvency_to_descriptor2();
        assert_eq!(desc2.public_input_count, SOLVENCY_CLAIM_LEN);
        let sites = desc2
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
            .count();
        assert_eq!(sites, 2, "reserve + liability commitment openings");
        let pins = desc2
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
            .count();
        assert_eq!(pins, 2, "reserve_commit + liability_commit PI pins");
        // Lane accounting: 2 sites × 7 lanes past the extended base.
        assert_eq!(desc2.trace_width, EXT_BASE_WIDTH + 2 * (CHIP_OUT_LANES - 1));
    }

    /// Evaluate the emitted boundary gates using the production IR interpreter.
    /// The Lean theorem proves all canonical satisfying rows are solvent; these
    /// cases check the Rust witness layout and expose the old modular-wrap hole.
    #[test]
    fn solvency_emitted_integer_comparison_refuses_modular_wrap() {
        use dregg_circuit::descriptor_ir2::{check_descriptor2_wellformed, eval_lean_expr};
        let desc = solvency_to_descriptor2();
        check_descriptor2_wellformed(&desc).expect("generated AIR is executable");
        let accepted = |w: SolvencyWitness| {
            let (trace, _) = solvency_leaf_base_trace(&w);
            let gates: Vec<_> = desc
                .constraints
                .iter()
                .filter_map(|c| match c {
                    VmConstraint2::Base(VmConstraint::Boundary {
                        row: VmRow::First,
                        body,
                    }) => Some(body),
                    _ => None,
                })
                .collect();
            assert_eq!(
                gates.len(),
                102,
                "all generated arithmetic boundaries are exercised"
            );
            gates
                .iter()
                .all(|body| eval_lean_expr(body, &trace[0]) == BabyBear::ZERO)
        };
        for (r, l) in [
            (0, 0),
            (32768, 1),
            ((1 << 30) - 1, 0),
            ((1 << 30) - 1, (1 << 30) - 1),
        ] {
            assert!(accepted(solvent_witness(r, l)), "honest {r} >= {l}");
        }
        for (r, l) in [(0, (BABYBEAR_P - 1) as u64), (0, (1 << 30) - 1)] {
            let old_diff = (felt(r) - felt(l)).as_u32();
            assert!(
                r < l && old_diff < (1 << RANGE_BITS),
                "old checker admitted the attack"
            );
            assert!(
                !accepted(solvent_witness(r, l)),
                "emitted borrow chain refuses {r} < {l}"
            );
        }
        assert!(
            !accepted(solvent_witness(1 << 30, 0)),
            "operand range is enforced"
        );
    }

    /// Exercise the consumed artifact through the real inner STARK, without the
    /// unrelated recursion wrapper. A valid proof must reject changed public PIs.
    #[test]
    fn solvency_emitted_inner_roundtrip_and_forged_pi_refused() {
        use dregg_circuit::descriptor_ir2::verify_vm_descriptor2_with_config;
        let witness = solvent_witness(32768, 1);
        let pis = solvency_leaf_public_inputs(&witness);
        let config = ir2_leaf_wrap_config();
        let (desc, proof) = prove_solvency_inner(&witness, &pis, &config)
            .expect("honest borrow witness proves under emitted AIR");
        verify_vm_descriptor2_with_config(&desc, &proof, &pis, &config)
            .expect("honest emitted AIR proof verifies");
        let mut forged = pis;
        forged[RESERVE_COMMIT_PI] += BabyBear::ONE;
        assert!(verify_vm_descriptor2_with_config(&desc, &proof, &forged, &config).is_err());
        let outside = solvent_witness(1 << RANGE_BITS, 0);
        assert!(matches!(prove_solvency_inner(&outside,
            &solvency_leaf_public_inputs(&outside), &config),
            Err(e) if e.contains("amounts must be below")));
    }

    fn solvent_witness(reserve: u64, liability: u64) -> SolvencyWitness {
        SolvencyWitness {
            reserve,
            liability,
            salt_reserve: 0xBA1,
            salt_liability: 0xDEB7,
        }
    }

    /// A REAL full-width note-spend witness (mirrors the note-spend adapter's test
    /// helper): raw 32-byte fields + a > 2^30 value so the high limb is live.
    fn note_spend_witness(tag: u8) -> NoteSpendingWitness {
        let owner = [tag; 32];
        let nonce = [tag ^ 0x5A; 32];
        let rand = [tag ^ 0xA5; 32];
        let key = test_spending_key(tag as u32 + 0x77);
        let depth = 2;
        let mut siblings = Vec::with_capacity(depth);
        let mut positions = Vec::with_capacity(depth);
        for i in 0..depth {
            siblings.push([
                hash_many(&[BabyBear::new((i * 3 + 1) as u32), BabyBear::new(tag as u32)]),
                hash_many(&[BabyBear::new((i * 3 + 2) as u32), BabyBear::new(tag as u32)]),
                hash_many(&[BabyBear::new((i * 3 + 3) as u32), BabyBear::new(tag as u32)]),
            ]);
            positions.push((i % 4) as u8);
        }
        NoteSpendingWitness::from_note_limbs(
            &owner,
            0xDEAD_BEEF_CAFE,
            3,
            &nonce,
            &rand,
            key,
            siblings,
            positions,
        )
    }

    /// THE POSITIVE POLE (leaf): an honest solvent reserve (R ≥ L) proves as a
    /// foldable recursion leaf, and the exposed claim equals `[reserve_commit,
    /// liability_commit]`.
    #[test]
    fn honest_solvency_proves_as_foldable_leaf_and_exposes_claim() {
        let w = solvent_witness(1_000_000, 750_000);
        let pis = solvency_leaf_public_inputs(&w);
        assert_eq!(pis.len(), SOLVENCY_CLAIM_LEN);
        assert_eq!(pis[RESERVE_COMMIT_PI], w.reserve_commit());
        assert_eq!(pis[LIABILITY_COMMIT_PI], w.liability_commit());
        let config = ir2_leaf_wrap_config();

        let output = prove_solvency_leaf_with_claim(&w, &pis, &config)
            .expect("an honest solvent reserve must prove as a foldable claim leaf");
        let exposed =
            read_exposed_solvency_claim(&output).expect("the leaf exposes the 2-lane claim");
        assert_eq!(
            exposed.as_slice(),
            pis.as_slice(),
            "the exposed claim is the committed solvency tuple"
        );
    }

    /// THE NEGATIVE POLE (leaf, insolvency): an INSOLVENT reserve (R < L) has no
    /// satisfying assembly — `diff = R − L` is field-negative (rep > 2^30), its
    /// 30-bit reconstruction cannot equal it, the range gadget bites AT THE LEAF; no
    /// foldable leaf is minted.
    #[test]
    fn insolvent_reserve_does_not_fold() {
        // R = 500k < L = 750k: a real deficit.
        let w = solvent_witness(500_000, 750_000);
        let pis = solvency_leaf_public_inputs(&w);
        let config = ir2_leaf_wrap_config();

        let refusal = must_refuse_or_unsat_panic("an INSOLVENT reserve", || {
            prove_solvency_leaf(&w, &pis, &config)
        });
        // NAME THE REFUSAL, MEASURED FIRST (2026-08-10, --release, this exact fixture):
        //   OodEvaluationMismatch { index: Some(0) }
        // The bare `must_refuse_or_unsat_panic` here DISCARDED its result, so an FRI fault, an OOM
        // or a trace-shape error read identically to the forgery being caught. The subject is
        // a violated CONSTRAINT (`OodEvaluationMismatch` deployed / `constraints not
        // satisfied on row` in debug): the 30-bit range reconstruction of `diff = R - L` is an emitted gate.
        report_refusal("an INSOLVENT reserve", &refusal.reason());
        assert_violated_constraint_not_bus("an INSOLVENT reserve", &refusal.reason());
    }

    /// THE NEGATIVE POLE (leaf, forged commitment): a forged `reserve_commit` PI
    /// (the rest honest) is refused AT THE LEAF — the in-AIR opening plus the PI-0
    /// pin make it UNSAT, so the exposed commitment is a WELD to the compared R.
    #[test]
    fn forged_reserve_commitment_does_not_fold() {
        let w = solvent_witness(1_000_000, 750_000);
        let mut pis = solvency_leaf_public_inputs(&w);
        pis[RESERVE_COMMIT_PI] += BabyBear::ONE;
        let config = ir2_leaf_wrap_config();

        let refusal = must_refuse_or_unsat_panic("a FORGED reserve commitment", || {
            prove_solvency_leaf(&w, &pis, &config)
        });
        // NAME THE REFUSAL, MEASURED FIRST (2026-08-10, --release, this exact fixture):
        //   OodEvaluationMismatch { index: Some(0) }
        // The bare `must_refuse_or_unsat_panic` here DISCARDED its result, so an FRI fault, an OOM
        // or a trace-shape error read identically to the forgery being caught. The subject is
        // a violated CONSTRAINT (`OodEvaluationMismatch` deployed / `constraints not
        // satisfied on row` in debug): the PI-0 pin over the in-AIR opening is an emitted gate.
        report_refusal("a FORGED reserve commitment", &refusal.reason());
        assert_violated_constraint_not_bus("a FORGED reserve commitment", &refusal.reason());
    }

    /// THE STRUCTURED PRODUCT (the moat's first real financial fold): fold a REAL
    /// note-spend leaf ⊕ a REAL solvency leaf into ONE apex that verifies BOTH and
    /// exposes the combined claim `[…note-spend 7…, reserve_commit, liability_commit]`,
    /// verified ONCE.
    #[test]
    fn structured_product_folds_note_spend_and_solvency() {
        let config = ir2_leaf_wrap_config();

        // Leaf 1: the REAL foreign note-spend (spending key + Merkle + full commitment).
        let nw = note_spend_witness(0x10);
        let ns_pis = crate::note_spend_leaf_adapter::note_spend_leaf_public_inputs(&nw);
        let ns_leaf =
            crate::note_spend_leaf_adapter::prove_note_spend_leaf_with_claim(&nw, &ns_pis, &config)
                .expect("the note-spend claim leaf must mint");

        // Leaf 2: the REAL solvency instance (R ≥ L, committed).
        let sw = solvent_witness(2_000_000, 1_250_000);
        let sv_pis = solvency_leaf_public_inputs(&sw);
        let sv_leaf = prove_solvency_leaf_with_claim(&sw, &sv_pis, &config)
            .expect("the solvency claim leaf must mint");

        // THE FOLD: one apex verifying both leaves + exposing the combined claim.
        let apex = prove_structured_product_fold(
            &ns_leaf,
            &sv_leaf,
            &crate::fold_vk_pin::FoldVkPins::tracked(&ns_leaf, &sv_leaf)
                .expect("both fold children carry a preprocessed commitment"),
            &config,
        )
        .expect("the genuine structured product (note-spend ⊕ solvency) must fold + verify");

        let combined =
            read_structured_product_claim(&apex).expect("the apex exposes the combined claim");
        assert_eq!(combined.len(), STRUCTURED_PRODUCT_CLAIM_LEN);
        // The first 7 lanes are the note-spend tuple; the last 2 are the solvency
        // commitments — the whole instrument's economic facts in ONE verified apex.
        assert_eq!(
            &combined[..crate::note_spend_leaf_adapter::NOTE_SPEND_CLAIM_LEN],
            ns_pis.as_slice(),
            "the note-spend leg of the combined claim is the note-spend tuple"
        );
        assert_eq!(
            &combined[crate::note_spend_leaf_adapter::NOTE_SPEND_CLAIM_LEN..],
            sv_pis.as_slice(),
            "the solvency leg of the combined claim is the committed solvency tuple"
        );
    }
}
