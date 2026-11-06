//! IN-CIRCUIT CAVEAT ADMISSION (BIGNUM operands) — re-prove a mandate's per-trade caveat
//! admission as a RECURSION-FOLDABLE IR-v2 leaf that EVALUATES the caveat PREDICATE in the
//! AIR (not a trusted `caveatBit`), over MULTI-LIMB bignum operands (up to
//! `NUM_LIMBS * LIMB_BITS = 130` bits — u128-safe, not miniscule single-felt atoms).
//!
//! ## What this closes (the DREGGFI §7 honest edge, named in the tree)
//!
//! Today the effect-vm binds an AGGREGATE `caveatBit` / slot-caveat manifest into PI and
//! *trusts the executor's decision*: `verify_slot_caveat_manifest`
//! (`circuit/src/effect_vm/verify.rs:165`) is an OFF-AIR verifier-side re-run — a
//! re-executing validator recomputes the caveat against the state PIs, but a PURE LIGHT
//! CLIENT that only folds the per-turn recursion tree never witnesses that the admitted
//! request actually SATISFIES the caveat predicate. `Caveat.lean` says so itself
//! (`metatheory/Dregg2/Authority/Caveat.lean:57-60`, the §D6 honest framing): "the circuit
//! still binds an aggregate `caveatBit` and trusts the executor's decision; reifying a
//! caveat does not force its policy in-circuit." So "the mandate IS the proof" (DREGGFI §3
//! capability) is EXPRESSIVENESS-PROVED but VENUE-verification is executor-trusted.
//!
//! This leaf makes the DECIDABLE caveat atoms — the reified `CaveatPred` vocabulary
//! `Caveat.lean` already carries (`validUntil` expiry ceiling, `heightLt` strict height
//! ceiling) plus a value/asset SCOPE bound (the mandate `budget` + asset scope, tying to
//! `Dregg2/Agent/Mandate.lean`) — a genuine IN-CIRCUIT admission: the AIR proves each
//! `≤`/`<` by a limbwise borrow-subtraction whose difference limbs are RANGE-CHECKED, so an
//! OVER-authorized trade (past expiry, over budget, wrong asset) is UNSAT (no foldable leaf
//! minted), and a within-mandate trade folds. The admission binds to the trade: the leaf
//! re-exposes the `(trade fields ++ caveat params)` bignum limbs as a committed claim the
//! settling-venue binding node `connect`s to the deployed trade's teeth (the same
//! `expose_claim`/`connect` ABI the eight deployed carriers use,
//! `docs/deos/EFFECTVM-SIDESTRUCTURE-ABI.md`).
//!
//! ## The BIGNUM comparison mechanism (limbwise borrow-subtraction — no miniscule atoms)
//!
//! A STARK cannot assert `a ≤ b` directly, and a single BabyBear felt (`p ≈ 2³¹`) can only
//! safely range-carry ~29-bit atoms — too small for real trade values / budgets / heights.
//! So each operand is a BIGNUM of `NUM_LIMBS` limbs base `2^LIMB_BITS`. To prove `x ≤ y` the
//! AIR witnesses the schoolbook subtraction `y − x − init_borrow` limb by limb: difference
//! limbs `d_i` (each RANGE-CHECKED into `[0, 2^LIMB_BITS)`) and internal borrow bits `br_i`
//! (each BOOLEAN-constrained), pinned by the per-limb boundary relation
//! `d_i = y_i − x_i − br_i + br_{i+1}·2^LIMB_BITS`, with `br_0 = init_borrow` and the TOP
//! borrow `br_{NUM_LIMBS} = 0` PINNED. A valid witness exists IFF `y − x − init_borrow ≥ 0`.
//!   * `init_borrow = 0` realizes `x ≤ y` (inclusive — `validUntil`, `budget`);
//!   * `init_borrow = 1` realizes `x < y` (STRICT — `heightLt`; the `−1` is the incoming borrow).
//! If the caveat is VIOLATED the schoolbook subtraction underflows (needs `br_top = 1`), but
//! `br_top` is pinned `0`, so the top-limb equation forces a difference limb outside
//! `[0, 2^LIMB_BITS)` — the range lookup REFUSES it. UNSAT ⇒ no leaf. The `2·2^LIMB_BITS ≪ p`
//! headroom means every per-limb field equation has a UNIQUE integer solution (no wraparound
//! collision). This is exactly the arithmetic-vs-Caveat refinement proved in Lean over
//! UNBOUNDED `Int` (`metatheory/Dregg2/Circuit/CaveatAdmissionRefines.lean`): the limbwise
//! comparison realizes the ideal `Int` `≤`/`<` up to `130` bits, so the AIR faithfully
//! evaluates the caveat predicate, and an in-circuit-admitted request is in the token's
//! admissible set (`attenuate_narrows` / `token_discharges`).
//!
//! ## The three reified atoms (mirroring `Caveat.lean`'s `CaveatPred`) + the scope bound
//!
//!   * `validUntil t`  — admit iff `req_time  ≤ t`      (expiry CEILING, inclusive; init_borrow 0)
//!   * `heightLt   h`  — admit iff `req_height < h`      (STRICT before-block ceiling; init_borrow 1)
//!   * `budget     b`  — admit iff `trade_value ≤ b`     (the Mandate spend ceiling; init_borrow 0)
//!   * asset scope     — admit iff `trade_asset == a`    (limbwise equality, not an inequality)
//!
//! ## HONEST SCOPE (named, per the project bar — do NOT overclaim)
//!
//! This lands the DECIDABLE temporal/scope atoms IN-CIRCUIT. The caveat predicates that
//! remain EXECUTOR-TRUSTED are the un-reified ones: `Caveat.opaque` (an arbitrary `Ctx →
//! Bool` the AST cannot introspect) and `Caveat.thirdParty` (a gateway discharge). Those
//! stay off-AIR named carriers — this leaf does not force them. A mandate whose caveats are
//! all in the reified `{validUntil, heightLt, budget, asset}` vocabulary is now
//! VENUE-verifiable; a mandate carrying an `opaque` atom is still executor-trusted for that
//! atom. That slice — the decidable-caveat admission — is what this turns from
//! executor-trusted to in-circuit PROVED.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2Air, MemBoundaryWitness, UMemBoundaryWitness,
    ir2_airs_and_common_for_config, parse_vm_descriptor2, prove_vm_descriptor2_for_config,
};
use dregg_circuit::field::BabyBear;

use p3_field::PrimeField32;
use p3_recursion::{
    BatchOnly, ProveNextLayerParams, RecursionInput, RecursionOutput, Target,
    build_and_prove_aggregation_layer_with_expose, build_and_prove_next_layer_with_expose,
};
use p3_uni_stark::StarkGenericConfig;

use crate::fold_vk_pin::FoldVkPins;
use crate::ivc_turn_chain::prove_descriptor_leaf_rotated_with_config;
use crate::joint_turn_aggregation::JointAggError;
use crate::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, create_recursion_backend, recursion_layer_over,
};

type RecursionChallenge = <DreggRecursionConfig as StarkGenericConfig>::Challenge;
const D: usize = 4;

// ---- The bignum parameters ----------------------------------------------------------------
/// Bits per bignum limb. `2·2^LIMB_BITS ≪ p` (BabyBear `p ≈ 2.01e9`): the per-limb
/// subtraction field equation has a UNIQUE integer solution (no wraparound collision), and a
/// difference limb range-checked into `[0, 2^LIMB_BITS)` is a genuine `[0, 2^26)` byte-ish digit.
pub const LIMB_BITS: usize = 26;
/// Limbs per bignum operand. `NUM_LIMBS · LIMB_BITS = 130` bits ⇒ u128-safe operands (block
/// heights, times, budgets, wei-scale values) — NOT the old miniscule single-felt atom.
pub const NUM_LIMBS: usize = 5;
/// The per-limb radix `2^LIMB_BITS`, as an `i64` (fits: `2^26 = 67_108_864`).
const LIMB_BASE: i64 = 1 << LIMB_BITS;
/// The full operand bit budget (`= 130`).
pub const OPERAND_BITS: usize = NUM_LIMBS * LIMB_BITS;

/// ⚑ **BIGNUM, NOT ATOMS — AT BUILD TIME.** `OPERAND_BITS` is `NUM_LIMBS * LIMB_BITS`; if either
/// narrowed to the point where an operand fits a `u128`, this whole adapter would be paying for a
/// bignum decomposition it no longer needs *and* every caveat comparison it emits would be over a
/// domain smaller than the one callers hand it. Both operands are constants — it stood as an
/// `assert!` inside a `#[test]`.
const _: () = assert!(
    OPERAND_BITS >= 128,
    "operands must be at least u128-wide (bignum, not atoms)"
);

// ---- The 8 bignum operands (each `NUM_LIMBS` limbs, all PI-bound) --------------------------
/// The request's logical time (the `validUntil` view).
pub const OP_REQ_TIME: usize = 0;
/// The caveat's `validUntil` expiry ceiling — admit iff `req_time ≤ this`.
pub const OP_CAV_VALID_UNTIL: usize = 1;
/// The request's block height (the `heightLt` view).
pub const OP_REQ_HEIGHT: usize = 2;
/// The caveat's `heightLt` STRICT ceiling — admit iff `req_height < this`.
pub const OP_CAV_HEIGHT_LT: usize = 3;
/// The trade's value (the mandate `budget` view).
pub const OP_TRADE_VALUE: usize = 4;
/// The caveat's `budget` spend ceiling — admit iff `trade_value ≤ this`.
pub const OP_CAV_BUDGET: usize = 5;
/// The trade's asset id (the scope view).
pub const OP_TRADE_ASSET: usize = 6;
/// The caveat's scoped asset id — admit iff `trade_asset == this`.
pub const OP_CAV_ASSET: usize = 7;
/// Number of bignum operands.
pub const NUM_OPERANDS: usize = 8;

/// Number of PI slots = the committed admission-claim width: the 8 operands as limbs.
pub const CAVEAT_PI_COUNT: usize = NUM_OPERANDS * NUM_LIMBS;
/// The exposed committed-claim width (the `(trade fields ++ caveat params)` bignum limbs the
/// binding node `connect`s to the deployed trade's teeth).
pub const CAVEAT_ADMISSION_CLAIM_LEN: usize = CAVEAT_PI_COUNT;

// ---- The three comparisons (x ⩽/< y), by (x operand, y operand, strict?) -------------------
/// `(x_operand, y_operand, init_borrow)`: init_borrow 0 ⇒ `x ≤ y`; 1 ⇒ `x < y`.
const COMPARISONS: [(usize, usize, i64); 3] = [
    (OP_REQ_TIME, OP_CAV_VALID_UNTIL, 0), // validUntil: req_time ≤ cav_validUntil
    (OP_REQ_HEIGHT, OP_CAV_HEIGHT_LT, 1), // heightLt (STRICT): req_height < cav_heightLt
    (OP_TRADE_VALUE, OP_CAV_BUDGET, 0),   // budget: trade_value ≤ cav_budget
];
const NUM_COMPARISONS: usize = COMPARISONS.len();

// ---- The column layout --------------------------------------------------------------------
/// Column (and PI index) of operand `o`'s limb `j`.
const fn op_limb_col(o: usize, j: usize) -> usize {
    o * NUM_LIMBS + j
}
/// First column of the difference-limb block (after the `NUM_OPERANDS*NUM_LIMBS` operand limbs).
const DIFF_BASE: usize = NUM_OPERANDS * NUM_LIMBS;
/// Column of comparison `c`'s difference limb `j`.
const fn diff_limb_col(c: usize, j: usize) -> usize {
    DIFF_BASE + c * NUM_LIMBS + j
}
/// First column of the internal-borrow block (each comparison has `NUM_LIMBS-1` witnessed
/// borrows `br_1 .. br_{NUM_LIMBS-1}`; `br_0 = init_borrow` and `br_{NUM_LIMBS} = 0` are pinned
/// constants, not columns).
const BORROW_BASE: usize = DIFF_BASE + NUM_COMPARISONS * NUM_LIMBS;
/// Column of comparison `c`'s internal borrow `br_k` (`1 ≤ k ≤ NUM_LIMBS-1`).
const fn borrow_col(c: usize, k: usize) -> usize {
    BORROW_BASE + c * (NUM_LIMBS - 1) + (k - 1)
}
/// The base trace width.
const TRACE_WIDTH: usize = BORROW_BASE + NUM_COMPARISONS * (NUM_LIMBS - 1);

/// Split a `u128` into `NUM_LIMBS` limbs of `LIMB_BITS` bits (little-endian). The value must be
/// `< 2^OPERAND_BITS` (a `u128` always is, since `OPERAND_BITS = 130 > 128`).
fn to_limbs(v: u128) -> [u32; NUM_LIMBS] {
    let mut out = [0u32; NUM_LIMBS];
    let mask = (1u128 << LIMB_BITS) - 1;
    for (j, slot) in out.iter_mut().enumerate() {
        *slot = ((v >> (j * LIMB_BITS)) & mask) as u32;
    }
    out
}

/// A per-trade caveat-admission witness: the trade's `(time, height, value, asset)` and the
/// mandate caveat's `(validUntil, heightLt, budget, asset)`, each a `u128` bignum. Honest
/// admission requires every atom to hold; the leaf mints iff so.
#[derive(Clone, Copy, Debug)]
pub struct CaveatAdmissionWitness {
    /// The request's logical time (the `validUntil` view).
    pub req_time: u128,
    /// The caveat's expiry ceiling.
    pub cav_valid_until: u128,
    /// The request's block height (the `heightLt` view).
    pub req_height: u128,
    /// The caveat's strict height ceiling.
    pub cav_height_lt: u128,
    /// The trade's value.
    pub trade_value: u128,
    /// The caveat's spend budget.
    pub cav_budget: u128,
    /// The trade's asset id.
    pub trade_asset: u128,
    /// The caveat's scoped asset id.
    pub cav_asset: u128,
}

impl CaveatAdmissionWitness {
    /// The 8 operand values in operand-index order.
    fn operand_values(&self) -> [u128; NUM_OPERANDS] {
        [
            self.req_time,
            self.cav_valid_until,
            self.req_height,
            self.cav_height_lt,
            self.trade_value,
            self.cav_budget,
            self.trade_asset,
            self.cav_asset,
        ]
    }

    /// The `CAVEAT_PI_COUNT`-slot bignum tuple carried as the leaf's descriptor PIs (the
    /// committed admission claim `(trade fields ++ caveat params)`, operand-major limb order).
    pub fn public_inputs(&self) -> Vec<BabyBear> {
        let ops = self.operand_values();
        let mut pis = vec![BabyBear::new(0); CAVEAT_PI_COUNT];
        for (o, &v) in ops.iter().enumerate() {
            let limbs = to_limbs(v);
            for (j, &l) in limbs.iter().enumerate() {
                pis[op_limb_col(o, j)] = BabyBear::new(l);
            }
        }
        pis
    }

    /// Whether this request is WITHIN the caveat (the reference admission decision the AIR
    /// mirrors) — the twin of `CaveatPred.eval` of the reified window over UNBOUNDED `Int`. -/
    pub fn admits(&self) -> bool {
        self.req_time <= self.cav_valid_until
            && self.req_height < self.cav_height_lt
            && self.trade_value <= self.cav_budget
            && self.trade_asset == self.cav_asset
    }

    /// The base trace: one typed row (operand limbs ++ the 3 comparisons' difference limbs ++
    /// internal borrows), replicated across a power-of-two height. `WindowGate` continuity pins
    /// every column constant, so the whole tuple binds from row 0. The difference/borrow limbs
    /// are the GENUINE schoolbook subtraction of `y − x − init_borrow`: for a within-caveat
    /// comparison the top borrow is 0 and every difference limb is in range; for an
    /// OVER-authorized comparison the subtraction underflows (the honest schoolbook needs a top
    /// borrow of 1, but the AIR pins it 0), forcing a difference limb outside `[0, 2^LIMB_BITS)`
    /// — the range lookup refuses it (the tooth) — this same generation drives both poles.
    pub fn generate_trace(&self) -> Vec<Vec<BabyBear>> {
        let ops = self.operand_values();
        let op_limbs: [[u32; NUM_LIMBS]; NUM_OPERANDS] = core::array::from_fn(|o| to_limbs(ops[o]));

        let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
        // Operand limbs (PI-bound).
        for (o, limbs) in op_limbs.iter().enumerate() {
            for (j, &l) in limbs.iter().enumerate() {
                row[op_limb_col(o, j)] = BabyBear::new(l);
            }
        }
        // Per-comparison schoolbook borrow-subtraction `y − x − init_borrow`.
        for (c, &(xo, yo, init)) in COMPARISONS.iter().enumerate() {
            let x = &op_limbs[xo];
            let y = &op_limbs[yo];
            let mut borrow: i64 = init;
            for j in 0..NUM_LIMBS {
                // temp = y_j − x_j − borrow_in ; digit in [0,B), borrow_out ∈ {0,1}.
                let temp: i64 = y[j] as i64 - x[j] as i64 - borrow;
                let (digit, borrow_out) = if temp < 0 {
                    ((temp + LIMB_BASE) as u32, 1i64)
                } else {
                    (temp as u32, 0i64)
                };
                // Fill the difference limb. For a violated comparison the final `borrow_out`
                // (the top borrow) is 1, but the AIR pins it 0 — so the top-limb equation forces
                // this filled digit to be inconsistent / out of range and the leaf is UNSAT.
                row[diff_limb_col(c, j)] = BabyBear::new(digit);
                // Witness the internal borrows br_1 .. br_{NUM_LIMBS-1} (the outgoing borrow of
                // limb j is br_{j+1}; only j+1 ≤ NUM_LIMBS-1 is a column).
                if j + 1 < NUM_LIMBS {
                    row[borrow_col(c, j + 1)] = BabyBear::new(borrow_out as u32);
                }
                borrow = borrow_out;
            }
        }
        vec![row.clone(), row]
    }
}

/// Decode the Lean-authored five-limb caveat AIR. `BorrowChainEmit.bodies_sound`
/// lifts its modular equations to exact integer comparisons; `CaveatAdmissionEmit`
/// connects the actual descriptor to the public limb tuple and all four atoms.
pub fn caveat_admission_to_descriptor2() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(include_str!(
        "../../circuit/descriptors/by-name/caveat-admission-leaf.json"
    ))
    .expect("Lean-emitted caveat admission descriptor decodes")
}

/// Prove a caveat admission as a RECURSION-FOLDABLE IR-v2 leaf. `public_inputs` is the
/// `CAVEAT_PI_COUNT`-slot bignum tuple — for an honest proof it equals `witness.public_inputs()`.
///
/// THE ADMISSION TOOTH: if the request VIOLATES a caveat atom (past expiry, over budget, wrong
/// asset), the limbwise borrow-subtraction underflows and (with the top borrow pinned 0) forces a
/// difference limb outside `[0, 2^LIMB_BITS)`; the range lookup refuses it, the assembly is UNSAT,
/// and NO foldable leaf is minted. A within-caveat trade's limbs are all in range and the leaf folds.
pub fn prove_caveat_admission_leaf(
    witness: &CaveatAdmissionWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    if public_inputs.len() != CAVEAT_PI_COUNT {
        return Err(format!(
            "caveat-admission leaf expects {CAVEAT_PI_COUNT} PI slots, got {}",
            public_inputs.len()
        ));
    }
    let desc2 = caveat_admission_to_descriptor2();
    let base_trace = witness.generate_trace();

    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc2,
        &base_trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .map_err(|e| format!("caveat-admission leaf inner IR-v2 prove failed: {e}"))?;

    prove_descriptor_leaf_rotated_with_config(&desc2, &inner, public_inputs, config)
        .map_err(|e| format!("caveat-admission leaf recursion wrap failed: {e}"))
}

/// Prove the caveat admission as a foldable leaf AND re-expose its bound bignum admission claim
/// `(trade fields ++ caveat params)` (lanes `[0 .. CAVEAT_ADMISSION_CLAIM_LEN)`) as a public
/// CLAIM the settling-venue binding node `connect`s to the deployed trade's teeth.
///
/// The exposed tuple is welded to the in-circuit admission: a prover cannot expose operand limbs
/// that disagree with the tuple the leaf's range-checked comparison proves (both are the SAME
/// FRI-bound descriptor PI targets). So a fold that consumes this claim has PROOF the trade's
/// `(time, height, value, asset)` lies inside the caveat's `(validUntil, heightLt, budget, asset)`
/// — a venue-verifiable admission, not an executor-trusted bit.
pub fn prove_caveat_admission_leaf_with_claim(
    witness: &CaveatAdmissionWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    if public_inputs.len() != CAVEAT_PI_COUNT {
        return Err(format!(
            "caveat-admission claim leaf expects {CAVEAT_PI_COUNT} PI slots, got {}",
            public_inputs.len()
        ));
    }
    let desc2 = caveat_admission_to_descriptor2();
    let base_trace = witness.generate_trace();

    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc2,
        &base_trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .map_err(|e| format!("caveat-admission claim leaf inner IR-v2 prove failed: {e}"))?;

    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(&desc2, &inner, public_inputs, config)
            .map_err(|e| format!("caveat-admission claim verify-triple build failed: {e}"))?;

    let input: RecursionInput<'_, DreggRecursionConfig, Ir2Air> =
        RecursionInput::NativeBatchStark {
            airs: &airs,
            proof: &inner,
            common_data: &common,
            table_public_inputs,
        };

    let backend = create_recursion_backend();

    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       apt: &[Vec<Target>],
                       _vk_cap: &[Target]| {
        let main = apt
            .first()
            .expect("caveat-admission leaf has a main instance carrying the operand-limb PIs");
        debug_assert!(
            main.len() >= CAVEAT_ADMISSION_CLAIM_LEN,
            "main instance must carry the bignum operand PI slots"
        );
        // Re-expose the FRI-bound `(trade fields ++ caveat params)` bignum-limb lanes directly.
        let claim: Vec<Target> = (0..CAVEAT_ADMISSION_CLAIM_LEN).map(|k| main[k]).collect();
        cb.expose_as_public_output(&claim);
    };

    build_and_prove_next_layer_with_expose::<DreggRecursionConfig, Ir2Air, _, D>(
        &input,
        &recursion_layer_over(config),
        &backend,
        &ProveNextLayerParams::default(),
        Some(&expose),
    )
    .map_err(|e| format!("caveat-admission claim leaf-wrap failed: {e:?}"))
}

/// Read the bignum admission claim a [`prove_caveat_admission_leaf_with_claim`] leaf exposes.
/// Returns `None` if the proof carries no claim.
pub fn read_exposed_caveat_admission(
    output: &RecursionOutput<DreggRecursionConfig>,
) -> Option<[BabyBear; CAVEAT_ADMISSION_CLAIM_LEN]> {
    let claims: Vec<BabyBear> = output
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")?
        .public_values
        .iter()
        .map(|&v| BabyBear::new(v.as_canonical_u32()))
        .collect();
    if claims.len() < CAVEAT_ADMISSION_CLAIM_LEN {
        return None;
    }
    let mut out = [BabyBear::ZERO; CAVEAT_ADMISSION_CLAIM_LEN];
    out.copy_from_slice(&claims[0..CAVEAT_ADMISSION_CLAIM_LEN]);
    Some(out)
}

// ============================================================================
// THE CAVEAT-ADMISSION BINDING FOLD NODES (settling-venue side).
// ============================================================================

/// [`prove_caveat_admission_binding_node`]'s failure prefix, SINGLE-SOURCED so the production `format!` and a tooth's
/// `binding_tooth::assert_node_refused_by_binding_connect` expectation cannot drift apart.
/// A renamed arm that only lived as two duplicated string literals is exactly how a tooth
/// quietly degrades to "any refusal at all".
pub const CAVEAT_ADMISSION_BINDING_NODE_ARM: &str =
    "caveat-admission binding aggregation node failed";
/// [`prove_caveat_admission_binding_node_segmented`]'s failure prefix. ⚠ [`CAVEAT_ADMISSION_BINDING_NODE_ARM`] is a SUBSTRING of it, so a `contains` on the shorter
/// one does not discriminate the two nodes.
pub const CAVEAT_ADMISSION_BINDING_NODE_SEGMENTED_ARM: &str =
    "segmented caveat-admission binding aggregation node failed";

/// **THE CAVEAT-ADMISSION BINDING MECHANISM NODE.** Aggregate a deployed trade LEG leaf (which
/// must RE-EXPOSE its CLAIMED bignum `(trade fields ++ caveat params)` as an `expose_claim`) WITH
/// the re-proved caveat-admission leaf ([`prove_caveat_admission_leaf_with_claim`]), CONNECTING
/// the two tuples in-circuit and re-exposing the now-bound admission as the parent claim.
///
/// THE TOOTH: if the trade leg claims operands the admission leaf does not bind (a trade whose
/// fields the caveat gadget did not admit — or an admission for a DIFFERENT trade), the per-lane
/// `connect` is a conflict and the aggregation is UNSAT — no root. This makes a mandate breach
/// UNCONSTRUCTABLE at settlement. The twin of
/// [`crate::membership_leaf_adapter::prove_membership_binding_node`].
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_caveat_admission_binding_node(
    leg_tuple_leaf: &RecursionOutput<DreggRecursionConfig>,
    admission_leaf: &RecursionOutput<DreggRecursionConfig>,
    // ⚑ The children's VK-identity pins (`crate::fold_vk_pin`). Unpinned, each child's
    // preprocessed commitment is an unconstrained runtime public input and a same-shape /
    // different-constants child — a VALID proof of a DIFFERENT circuit — folds through.
    // ⚠ No host pre-flight compares these against the children: the refusal is the circuit's.
    pins: &FoldVkPins,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use crate::ivc_turn_chain::expose_claim_instance_index;
    use p3_circuit::CircuitBuilder;

    let leg_idx = expose_claim_instance_index(&leg_tuple_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "caveat-admission leg leaf carries no re-exposed operand tuple (expose_claim) \
                     table — it must expose the bignum (trade fields ++ caveat params)"
                .to_string(),
        }
    })?;
    let adm_idx = expose_claim_instance_index(&admission_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "caveat-admission leaf carries no exposed operand tuple (expose_claim) table \
                     — it must be minted via prove_caveat_admission_leaf_with_claim"
                .to_string(),
        }
    })?;

    let left = leg_tuple_leaf.into_recursion_input_pinned::<BatchOnly>(pins.left.clone());
    let right = admission_leaf.into_recursion_input_pinned::<BatchOnly>(pins.right.clone());

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>],
                       _left_vk_cap: &[Target],
                       _right_vk_cap: &[Target]| {
        let lg = left_apt
            .get(leg_idx)
            .expect("caveat-admission leg's re-exposed tuple instance present");
        let adm = right_apt
            .get(adm_idx)
            .expect("caveat-admission leaf's exposed tuple instance present");
        debug_assert!(
            lg.len() >= CAVEAT_ADMISSION_CLAIM_LEN && adm.len() >= CAVEAT_ADMISSION_CLAIM_LEN
        );
        // THE BINDING TOOTH, IN-CIRCUIT: the leg's CLAIMED operands must equal the admission
        // leaf's range-checked BOUND tuple, lane by lane. A trade whose teeth name operands no
        // admission leaf binds is a conflict here ⇒ UNSAT ⇒ no root.
        for k in 0..CAVEAT_ADMISSION_CLAIM_LEN {
            cb.connect(lg[k], adm[k]);
        }
        let bound: Vec<Target> = (0..CAVEAT_ADMISSION_CLAIM_LEN).map(|k| lg[k]).collect();
        cb.expose_as_public_output(&bound);
    };

    build_and_prove_aggregation_layer_with_expose::<
        DreggRecursionConfig,
        BatchOnly,
        BatchOnly,
        _,
        D,
    >(&left, &right, &crate::ivc_turn_chain::fold_layer_over_leaves(config), &backend, &params, None, Some(&expose))
    .map_err(|e| JointAggError::AggregationProofInvalid {
        reason: format!("{CAVEAT_ADMISSION_BINDING_NODE_ARM}: {e:?}"),
    })
}

/// **THE SEGMENT-PRESERVING CAVEAT-ADMISSION BINDING NODE (deployed, caller-ready — the analog
/// of [`crate::membership_leaf_adapter::prove_membership_binding_node_segmented`]).** Aggregate a
/// deployed TRADE turn's DUAL-EXPOSE effect-vm leg leaf (whose single `expose_claim` carries the
/// chain SEGMENT in lanes `[0 .. SEG_WIDTH)` and the CLAIMED bignum `(trade fields ++ caveat
/// params)` in lanes `[SEG_SPINE_WIDTH .. SEG_SPINE_WIDTH+CAVEAT_ADMISSION_CLAIM_LEN)`) WITH the re-proved
/// caveat-admission leaf ([`prove_caveat_admission_leaf_with_claim`]), and:
///
///   1. `connect`s the leg's claimed operands to the admission leaf's range-checked BOUND tuple
///      (the binding tooth — a trade the caveat gadget did NOT admit has no admission leaf to
///      bind ⇒ conflict ⇒ UNSAT ⇒ no root), and
///   2. RE-EXPOSES `[the leg's SEGMENT lanes [0 .. SEG_WIDTH) ‖ a folded vk_spine]` as the parent claim.
///
/// The output exposes an ordinary `SEG_SPINE_WIDTH`-lane `[segment ‖ vk_spine]` claim, so it folds into
/// [`crate::ivc_turn_chain::aggregate_tree`] like any other per-turn segment leaf — making the
/// caveat admission REAL for a pure light client while preserving the chain endpoints/digest.
///
/// THE NAMED BIG-BANG SEAM (honest, mirroring membership): the deployed trade leg must
/// DUAL-EXPOSE its `(trade fields ++ caveat params)` bignum limbs (lanes `[SEG_SPINE_WIDTH ..)`) at
/// fixed PI slots — the effect-vm Transfer/settle descriptor must PUBLISH the trade's `(time,
/// height, value, asset)` and the mandate caveat's `(validUntil, heightLt, budget, asset)` as
/// teeth. That PI-exposure is the VK-affecting descriptor-lane piece (the caveat twin of the
/// membership `(sender_leaf, authorized_root)` exposure); THIS node is its ready consumer. The
/// leaf + mechanism ([`prove_caveat_admission_binding_node`]) prove the fold bites today.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_caveat_admission_binding_node_segmented(
    dual_expose_leg_leaf: &RecursionOutput<DreggRecursionConfig>,
    admission_leaf: &RecursionOutput<DreggRecursionConfig>,
    // ⚑ The children's VK-identity pins (`crate::fold_vk_pin`). Unpinned, each child's
    // preprocessed commitment is an unconstrained runtime public input and a same-shape /
    // different-constants child — a VALID proof of a DIFFERENT circuit — folds through.
    // ⚠ No host pre-flight compares these against the children: the refusal is the circuit's.
    pins: &FoldVkPins,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use crate::ivc_turn_chain::{
        SEG_SPINE_WIDTH, binding_node_segment_and_spine, expose_claim_instance_index,
    };
    use p3_circuit::CircuitBuilder;

    let ev_idx = expose_claim_instance_index(&dual_expose_leg_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "dual-expose caveat leg leaf carries no expose_claim table — it must be \
                     wrapped to expose (segment ++ (trade fields ++ caveat params))"
                .to_string(),
        }
    })?;
    let adm_idx = expose_claim_instance_index(&admission_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "caveat-admission leaf carries no exposed operand tuple (expose_claim) table \
                     — it must be minted via prove_caveat_admission_leaf_with_claim"
                .to_string(),
        }
    })?;

    let left = dual_expose_leg_leaf.into_recursion_input_pinned::<BatchOnly>(pins.left.clone());
    let right = admission_leaf.into_recursion_input_pinned::<BatchOnly>(pins.right.clone());

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>],
                       left_vk_cap: &[Target],
                       right_vk_cap: &[Target]| {
        let ev = left_apt
            .get(ev_idx)
            .expect("dual-expose caveat leg's claim instance present");
        let adm = right_apt
            .get(adm_idx)
            .expect("caveat-admission leaf's exposed tuple instance present");
        debug_assert!(
            ev.len() >= SEG_SPINE_WIDTH + CAVEAT_ADMISSION_CLAIM_LEN
                && adm.len() >= CAVEAT_ADMISSION_CLAIM_LEN,
            "dual-expose claim must carry segment ++ operand tuple; admission leaf carries the tuple"
        );
        // THE BINDING TOOTH, IN-CIRCUIT: the leg's CLAIMED operands (lanes
        // [SEG_SPINE_WIDTH .. SEG_SPINE_WIDTH+CAVEAT_ADMISSION_CLAIM_LEN)) must equal the admission leaf's
        // range-checked BOUND tuple, lane by lane.
        for k in 0..CAVEAT_ADMISSION_CLAIM_LEN {
            cb.connect(ev[SEG_SPINE_WIDTH + k], adm[k]);
        }
        // RE-EXPOSE `[segment ‖ vk_spine]` as the parent claim.
        let parent = binding_node_segment_and_spine(cb, ev, left_vk_cap, right_vk_cap);
        cb.expose_as_public_output(&parent);
    };

    build_and_prove_aggregation_layer_with_expose::<
        DreggRecursionConfig,
        BatchOnly,
        BatchOnly,
        _,
        D,
    >(&left, &right, &crate::ivc_turn_chain::fold_layer_over_leaves(config), &backend, &params, None, Some(&expose))
    .map_err(|e| JointAggError::AggregationProofInvalid {
        reason: format!("{CAVEAT_ADMISSION_BINDING_NODE_SEGMENTED_ARM}: {e:?}"),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binding_tooth::{assert_node_refused_by_binding_connect, report_refusal};
    use crate::ivc_turn_chain::ir2_leaf_wrap_config;
    use dregg_circuit::descriptor_ir2::{LookupSpec, TID_RANGE, TableSem, VmConstraint2};
    use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};
    use dregg_circuit::refusal::{
        assert_violated_constraint_not_bus, must_refuse, must_refuse_or_unsat_panic,
    };

    /// A within-caveat trade: time 150 ≤ validUntil 200, height 90 < heightLt 100,
    /// value 40 ≤ budget 100, asset 7 == asset 7. Every atom holds.
    fn within_caveat() -> CaveatAdmissionWitness {
        CaveatAdmissionWitness {
            req_time: 150,
            cav_valid_until: 200,
            req_height: 90,
            cav_height_lt: 100,
            trade_value: 40,
            cav_budget: 100,
            trade_asset: 7,
            cav_asset: 7,
        }
    }

    /// A within-caveat trade whose operands are LARGE bignums — well beyond a single-felt atom
    /// (`> 2^29`): a ~1.2e18-wei value under a 2e18 budget, a ~4.3-billion block height, a
    /// 96-bit asset id. Proves the gadget is NOT miniscule-atom-bound.
    fn within_caveat_bignum() -> CaveatAdmissionWitness {
        CaveatAdmissionWitness {
            req_time: 1_700_000_000, // unix-ish seconds (> 2^30)
            cav_valid_until: 2_000_000_000,
            req_height: 4_294_967_000,              // ~2^32 block height
            cav_height_lt: 4_294_967_296,           // 2^32
            trade_value: 1_200_000_000_000_000_000, // 1.2e18 wei (> 2^59)
            cav_budget: 2_000_000_000_000_000_000,  // 2e18 wei budget
            trade_asset: (1u128 << 96) | 12345,     // a 96-bit asset id
            cav_asset: (1u128 << 96) | 12345,
        }
    }

    /// The emitted arithmetic/range checks use the production expression evaluator.
    /// These cases exercise witness layout, not a Rust-to-Lean refinement claim.
    #[test]
    fn caveat_emitted_admission_refuses_each_atom() {
        use dregg_circuit::descriptor_ir2::eval_lean_expr;
        let desc = caveat_admission_to_descriptor2();
        let accepted = |w: &CaveatAdmissionWitness| {
            let trace = w.generate_trace();
            let row = &trace[0];
            desc.constraints.iter().all(|c| match c {
                VmConstraint2::Base(VmConstraint::Boundary {
                    row: VmRow::First,
                    body,
                }) => eval_lean_expr(body, row) == BabyBear::ZERO,
                VmConstraint2::Lookup(l) if l.table == TID_RANGE => {
                    eval_lean_expr(&l.tuple[0], row).as_u32() < (1 << LIMB_BITS)
                }
                _ => true,
            })
        };
        assert!(accepted(&within_caveat()));
        assert!(accepted(&within_caveat_bignum()));
        let maximum = CaveatAdmissionWitness {
            req_time: u128::MAX,
            cav_valid_until: u128::MAX,
            req_height: u128::MAX - 1,
            cav_height_lt: u128::MAX,
            trade_value: u128::MAX,
            cav_budget: u128::MAX,
            trade_asset: u128::MAX,
            cav_asset: u128::MAX,
        };
        assert!(accepted(&maximum), "all u128 bits remain usable");
        let mut bad = within_caveat();
        bad.req_time = bad.cav_valid_until + 1;
        assert!(!accepted(&bad));
        bad = within_caveat();
        bad.req_height = bad.cav_height_lt;
        assert!(!accepted(&bad), "strict height boundary");
        bad = within_caveat();
        bad.trade_value = bad.cav_budget + 1;
        assert!(!accepted(&bad));
        bad = within_caveat();
        bad.trade_asset += 1;
        assert!(!accepted(&bad));
    }

    #[test]
    fn caveat_emitted_inner_roundtrip() {
        use dregg_circuit::descriptor_ir2::verify_vm_descriptor2_with_config;
        let witness = within_caveat_bignum();
        let desc = caveat_admission_to_descriptor2();
        let pis = witness.public_inputs();
        let config = ir2_leaf_wrap_config();
        let proof = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
            &desc,
            &witness.generate_trace(),
            &pis,
            &MemBoundaryWitness::default(),
            &[],
            &UMemBoundaryWitness::default(),
            &config,
        )
        .expect("honest bignum witness proves under Lean-emitted AIR");
        verify_vm_descriptor2_with_config(&desc, &proof, &pis, &config)
            .expect("honest bignum proof verifies");
        let mut forged = pis;
        forged[op_limb_col(OP_TRADE_ASSET, 0)] += BabyBear::ONE;
        assert!(verify_vm_descriptor2_with_config(&desc, &proof, &forged, &config).is_err());
    }

    #[test]
    fn caveat_admission_descriptor_is_wellformed() {
        let desc = caveat_admission_to_descriptor2();
        assert_eq!(desc.trace_width, TRACE_WIDTH);
        assert_eq!(desc.public_input_count, CAVEAT_PI_COUNT);
        assert_eq!(CAVEAT_PI_COUNT, NUM_OPERANDS * NUM_LIMBS);
        assert!(desc.hash_sites.is_empty());
        assert!(
            desc.ranges.is_empty(),
            "IR-v2 ranges ride the Lookup(TID_RANGE) table"
        );
        assert_eq!(desc.tables.len(), 1);
        assert_eq!(desc.tables[0].sem, TableSem::Range { bits: LIMB_BITS });
        let pi = desc
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
            .count();
        assert_eq!(pi, CAVEAT_PI_COUNT);
        let ranges = desc
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Lookup(LookupSpec { table, .. }) if *table == TID_RANGE))
            .count();
        // operand limbs + difference limbs.
        assert_eq!(ranges, (NUM_OPERANDS + NUM_COMPARISONS) * NUM_LIMBS);
        assert!(within_caveat().admits());
        assert!(within_caveat_bignum().admits());
        // (`OPERAND_BITS >= 128` is const-asserted at the constant's definition)
    }

    /// THE POSITIVE POLE: a within-caveat trade's admission proves as a foldable leaf.
    #[test]
    fn within_caveat_admission_proves_as_foldable_leaf() {
        let w = within_caveat();
        let pis = w.public_inputs();
        let config = ir2_leaf_wrap_config();
        prove_caveat_admission_leaf(&w, &pis, &config)
            .expect("a within-caveat trade must admit in-circuit (fold a leaf)");
    }

    /// THE POSITIVE POLE (BIGNUM): a within-caveat trade with LARGE (u128-scale) operands admits
    /// — the miniscule-atom ceiling is gone.
    #[test]
    fn within_caveat_bignum_admission_proves() {
        let w = within_caveat_bignum();
        let pis = w.public_inputs();
        let config = ir2_leaf_wrap_config();
        prove_caveat_admission_leaf(&w, &pis, &config)
            .expect("a within-caveat BIGNUM trade must admit in-circuit");
    }

    /// THE POSITIVE POLE (claim variant): the claim leaf folds AND re-exposes the bound bignum
    /// admission claim.
    #[test]
    fn within_caveat_claim_leaf_exposes_admission() {
        let w = within_caveat();
        let pis = w.public_inputs();
        let config = ir2_leaf_wrap_config();
        let out = prove_caveat_admission_leaf_with_claim(&w, &pis, &config)
            .expect("the claim leaf must fold for a within-caveat trade");
        let exposed = read_exposed_caveat_admission(&out).expect("an admission claim is exposed");
        assert_eq!(
            &exposed[..],
            &pis[..],
            "the exposed claim is the bound operand-limb tuple"
        );
    }

    /// Assert a witness does NOT mint a foldable leaf (the UNSAT tooth) — both a hard prover
    /// panic and a returned `Err` count as refusal; only an `Ok` is a soundness break.
    fn assert_unsat(w: &CaveatAdmissionWitness, label: &str) {
        let pis = w.public_inputs();
        let config = ir2_leaf_wrap_config();
        let what = format!("{label}: an OVER-authorized trade");
        let refusal =
            must_refuse_or_unsat_panic(&what, || prove_caveat_admission_leaf(w, &pis, &config));
        // NAME THE REFUSAL, MEASURED FIRST (2026-08-10, --release, this exact fixture):
        //   OodEvaluationMismatch { index: Some(0) }
        // The bare `must_refuse_or_unsat_panic` here DISCARDED its result, so an FRI fault, an OOM
        // or a trace-shape error read identically to the forgery being caught. The subject is
        // a violated CONSTRAINT (`OodEvaluationMismatch` deployed / `constraints not
        // satisfied on row` in debug): every caveat gate is a borrow-subtraction / limb-equality CONSTRAINT, so an over-authorized
        // trade must fail a gate, never the bus.
        report_refusal(&what, &refusal.reason());
        assert_violated_constraint_not_bus(&what, &refusal.reason());
    }

    /// THE NEGATIVE POLE — PAST EXPIRY: `req_time > validUntil`. The `validUntil` borrow-
    /// subtraction underflows (top borrow would be 1, pinned 0) ⇒ a difference limb out of range
    /// ⇒ UNSAT. Uses BIGNUM operands to show the tooth bites past a single-felt atom too.
    #[test]
    fn past_expiry_trade_is_unsat() {
        let mut w = within_caveat_bignum();
        w.req_time = w.cav_valid_until + 1; // one tick past expiry (a ~2e9 bignum)
        assert!(!w.admits());
        assert_unsat(&w, "past-expiry");
    }

    /// THE NEGATIVE POLE — OVER HEIGHT (STRICT): `req_height == heightLt` is NOT `<`. The
    /// `init_borrow = 1` subtraction underflows by exactly 1 ⇒ UNSAT (the strictness tooth).
    #[test]
    fn over_height_trade_is_unsat() {
        let mut w = within_caveat_bignum();
        w.req_height = w.cav_height_lt; // equal, not strictly less
        assert!(!w.admits());
        assert_unsat(&w, "over-height (strict boundary)");
    }

    /// THE NEGATIVE POLE — OVER BUDGET: `trade_value > budget` (a large-bignum overspend).
    /// The `budget` borrow-subtraction underflows ⇒ UNSAT. A mandate spend breach is unconstructable.
    #[test]
    fn over_budget_trade_is_unsat() {
        let mut w = within_caveat_bignum();
        w.trade_value = w.cav_budget + 1_000_000_000_000; // 1e12 wei over budget
        assert!(!w.admits());
        assert_unsat(&w, "over-budget");
    }

    /// THE NEGATIVE POLE — WRONG ASSET: `trade_asset != cav_asset`. A limbwise asset-equality
    /// boundary fails ⇒ UNSAT ⇒ no leaf.
    #[test]
    fn wrong_asset_trade_is_unsat() {
        let mut w = within_caveat_bignum();
        w.trade_asset = w.cav_asset + 1; // outside the caveat's asset scope
        assert!(!w.admits());
        assert_unsat(&w, "wrong-asset");
    }

    /// THE ADMISSION BINDS TO THE TRADE (positive): the binding node CONNECTS a trade leg's
    /// claimed operands to the admission leaf's bound tuple and folds.
    #[test]
    fn admission_binds_to_trade() {
        let w = within_caveat();
        let pis = w.public_inputs();
        let config = ir2_leaf_wrap_config();
        let leg = prove_caveat_admission_leaf_with_claim(&w, &pis, &config)
            .expect("leg tuple leaf folds");
        let adm = prove_caveat_admission_leaf_with_claim(&w, &pis, &config)
            .expect("admission leaf folds");
        prove_caveat_admission_binding_node(
            &leg,
            &adm,
            &crate::fold_vk_pin::FoldVkPins::tracked(&leg, &adm)
                .expect("both fold children carry a preprocessed commitment"),
            &config,
        )
        .expect("the admission binds to the trade (matching operands connect)");
    }

    /// THE BINDING NEGATIVE TOOTH — you cannot staple an admission for trade A onto trade B.
    /// A leg claiming trade B's operands, connected to an admission leaf that bound trade A
    /// (A ≠ B, both within-caveat but different values), is a per-lane `connect` conflict ⇒ UNSAT.
    /// This is the fold-level "mandate breach unconstructable": the admission is bound to ITS OWN
    /// trade, not transferable to a different trade the caveat did not admit under the same terms.
    #[test]
    fn forged_trade_binding_does_not_fold() {
        let config = ir2_leaf_wrap_config();
        // Trade A: value 40. Trade B: value 41 (a DIFFERENT trade, also within caveat).
        let a = within_caveat();
        let mut b = within_caveat();
        b.trade_value = 41;
        let leg_b = prove_caveat_admission_leaf_with_claim(&b, &b.public_inputs(), &config)
            .expect("leg B tuple leaf folds");
        let adm_a = prove_caveat_admission_leaf_with_claim(&a, &a.public_inputs(), &config)
            .expect("admission A leaf folds");
        let what = "an admission for trade A bound to a DIFFERENT trade B";
        let err = must_refuse(what, || {
            prove_caveat_admission_binding_node(
                &leg_b,
                &adm_a,
                &crate::fold_vk_pin::FoldVkPins::tracked(&leg_b, &adm_a)
                    .expect("both fold children carry a preprocessed commitment"),
                &config,
            )
        });
        // NAME THE REFUSAL, MEASURED FIRST (2026-08-10, --release, this exact fixture):
        //   Circuit(WitnessConflict { .. }) under `CAVEAT_ADMISSION_BINDING_NODE_ARM`
        // This tooth's subject IS the per-lane `cb.connect` between the leg's CLAIMED lanes and the
        // leaf's BOUND ones, so `binding_tooth` is the right assertion and it is exactly what the
        // discarded result used to hide: the node has PRE-CONNECT guards ("carries no expose_claim",
        // the lane-count widths) that return before a single connect exists, and until 2026-08-10 an
        // `InvalidProofShape` from a mis-derived fold engine satisfied this site identically.
        assert_node_refused_by_binding_connect(what, &err, CAVEAT_ADMISSION_BINDING_NODE_ARM);
    }
}
