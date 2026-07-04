//! Re-prove the DECO/zkTLS Stripe-payment COMMITMENT as a RECURSION-FOLDABLE IR-v2
//! leaf — the DECO carrier's G2 backing half (the 8th carrier; `docs/deos/DECO-CARRIER-PLAN.md`).
//!
//! ## What this leaf verifies IN-AIR (Option B — the bridge-style commitment fold)
//!
//! Structurally the [`crate::note_spend_leaf_adapter`] shape, but SIMPLER: a
//! Poseidon2-only commitment AIR — NO Merkle membership, NO spending-key knowledge.
//! The leaf recomputes, IN-AIR, over its PI-pinned `PaymentFacts` columns
//! (`amountCents, currency, recipient, paymentIntentId` — `Deco.lean::PaymentFacts`):
//!
//!   * gate (4) — `fieldsDigest`/the identity inner: `m1 = hash_fact(amountCents,
//!     [currency, recipient])`;
//!   * the identity: `payment_hash = hash_fact(m1, [paymentIntentId])` =
//!     [`dregg_circuit::dsl::deco_payment::deco_payment_hash_felt`] (the ONE canonical
//!     anchor, felt-domain — NEVER the executor's byte-domain BLAKE3 nullifier);
//!   * gate (3) — the transcript-commitment opening: `transcriptCommit =
//!     hash_fact(payment_hash, [salt])` (a Poseidon2 `compress` of the disclosed-field
//!     digest under the opening blinding);
//!   * gate (5) — the amount range `1 ≤ amountCents < 2^30`, by bit-decomposition of
//!     `amountCents − 1` (`Deco.lean::DecoRelation` conjunct 5, `range`).
//!
//! and exposes `payment_hash` at claim lane [`DECO_LEAF_PAYMENT_HASH_PI`]. A prover
//! cannot expose a `payment_hash` that disagrees with the facts this leaf proves: the
//! `PiBinding{First}` fact pins + the chip-recomputed `hash_fact` chain make a mismatch
//! UNSAT AT THE LEAF (the leaf-level tooth).
//!
//! ## What stays OFF-AIR (the named §8 carriers — `DECO-CARRIER-PLAN.md` §5)
//!
//! Gate (1) ed25519 server-key signature (EUF-CMA), gate (2) HMAC-SHA256 transcript
//! MAC, SHA-256, the TLS/JSON parse, Web-PKI, the DECO 3-party handshake, and Stripe's
//! `encode` schema stay OFF-AIR, executor-verified — exactly what
//! `Deco.lean::deco_binds_payment` already treats as `SK.unforgeable`/`MK.unforgeable`
//! carriers, and exactly bridge's posture (its ed25519 / nullifier-set stay off-fold).
//! This is the DEPLOYMENT of the trust factoring `Deco.lean` already proved.
//!
//! ## The deployed connect (Step 5)
//!
//! The deployed `stripeMint`/`decoMint` row publishes the SAME felt `payment_hash` at a
//! tail PI (`DECO_PAYMENT_HASH_PI`, `withPaymentHashPin`); the per-turn fold's
//! [`prove_deco_payment_binding_node_segmented`] `connect`s the leg's published identity
//! to this leaf's exposed lane — so a published payment identity no verified DECO
//! commitment backs is a `connect` conflict, UNSAT (the fold tooth).

use dregg_circuit::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, EffectVmDescriptor2, LookupSpec, MemBoundaryWitness,
    TID_P2, UMemBoundaryWitness, VmConstraint2, prove_vm_descriptor2_for_config,
};
use dregg_circuit::dsl::deco_payment::deco_payment_hash_felt;
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use dregg_circuit::poseidon2::hash_fact;

use p3_field::PrimeField32;
use p3_recursion::{ProveNextLayerParams, RecursionOutput};

use crate::ivc_turn_chain::{
    prove_descriptor_leaf_rotated_with_config, prove_descriptor_leaf_with_pi_slice_expose,
};
use crate::joint_turn_aggregation::JointAggError;
use crate::plonky3_recursion_impl::recursive::DreggRecursionConfig;

/// Extension degree of the recursion config's PCS (the BabyBear-quartic stack).
const D: usize = 4;

/// The `hash_fact` domain-separation marker (`poseidon2::hash_fact` state[5]). Kept
/// file-local; the note-spend adapter's KAT `fact_arity7_chip_absorb_matches_hash_fact`
/// pins the arity-7 chip absorb against `hash_fact` (the same chip this leaf rides).
const DECO_FACT_MARK: u32 = 0xFACF;

/// The amount-range bit-width (gate 5): `amountCents − 1 ∈ [0, 2^30)`, so
/// `1 ≤ amountCents ≤ 2^30` — matching the single-felt amount limb the anchor uses
/// (`deco_payment::AMOUNT_LIMB_BITS`).
const AMOUNT_RANGE_BITS: usize = 30;

// ---- Base trace columns (before the descriptor-driven chip lanes). ----
/// The disclosed amount (cents), PI-pinned to claim lane 0.
const COL_AMOUNT: usize = 0;
/// The ISO-4217 currency felt, PI-pinned to claim lane 1.
const COL_CURRENCY: usize = 1;
/// The recipient dregg-cell felt, PI-pinned to claim lane 2.
const COL_RECIPIENT: usize = 2;
/// The payment-intent-id felt (the replay nonce), PI-pinned to claim lane 3.
const COL_PAYMENT_INTENT: usize = 3;
/// The transcript-commitment opening blinding (`salt`, gate 3), a free witness.
const COL_SALT: usize = 4;
/// The identity inner `m1 = hash_fact(amountCents, [currency, recipient])`.
const COL_M1: usize = 5;
/// The felt payment identity `payment_hash`, PI-pinned to claim lane
/// [`DECO_LEAF_PAYMENT_HASH_PI`].
const COL_PAYMENT_HASH: usize = 6;
/// The transcript commitment `transcriptCommit = hash_fact(payment_hash, [salt])`
/// (gate 3, proven but not exposed as a claim lane).
const COL_TRANSCRIPT_COMMIT: usize = 7;
/// Base of the `AMOUNT_RANGE_BITS` boolean bit columns decomposing `amountCents − 1`.
const RANGE_BASE: usize = 8;
/// The base trace width (facts + salt + 3 digests + the range bits), before chip lanes.
const BASE_WIDTH: usize = RANGE_BASE + AMOUNT_RANGE_BITS;

/// The exposed claim width: `[amountCents, currency, recipient, paymentIntentId,
/// payment_hash]`.
pub const DECO_CLAIM_LEN: usize = 5;

/// The claim lane of the felt payment identity (the connect target — the last lane).
pub const DECO_LEAF_PAYMENT_HASH_PI: usize = 4;

/// `x − y` as a `LeanExpr` (no subtraction node: `x + (−1)·y`).
fn sub(x: LeanExpr, y: LeanExpr) -> LeanExpr {
    LeanExpr::add(x, LeanExpr::mul(LeanExpr::Const(-1), y))
}

/// Build an UNCONDITIONAL arity-7 `TID_P2` chip lookup carrying one `hash_fact` site:
/// `input_cols[0]` the predicate, `input_cols[1..]` (≤ 4) the terms. The tuple IS the
/// genuine fact absorb `[7, pred, t0..t3, 0xFACF, 1, 0…, out, lanes…]` — the same
/// arity-7 chip the note-spend leaf's `gated_fact_site` rides, minus the row-gate mux
/// (every row of this leaf is a firing row).
fn fact_site(
    output_col: usize,
    input_cols: &[usize],
    lane_base: usize,
) -> Result<VmConstraint2, String> {
    if input_cols.is_empty() || input_cols.len() > 5 {
        return Err(format!(
            "deco fact site expects 1..=5 input columns (pred + ≤4 terms), got {}",
            input_cols.len()
        ));
    }
    let mut tuple: Vec<LeanExpr> = Vec::with_capacity(CHIP_TUPLE_LEN);
    tuple.push(LeanExpr::Const(7));
    for i in 0..CHIP_RATE {
        let e = match i {
            0..=4 => match input_cols.get(i) {
                Some(&c) => LeanExpr::Var(c),
                None => LeanExpr::Const(0),
            },
            5 => LeanExpr::Const(DECO_FACT_MARK as i64),
            6 => LeanExpr::Const(1),
            _ => LeanExpr::Const(0),
        };
        tuple.push(e);
    }
    // out0: the digest lane = the site's output column (this row always fires).
    tuple.push(LeanExpr::Var(output_col));
    // lanes 1..7: the genuine permutation lanes the chip AIR EQUALITY-binds.
    for j in 0..(CHIP_OUT_LANES - 1) {
        tuple.push(LeanExpr::Var(lane_base + j));
    }
    debug_assert_eq!(tuple.len(), CHIP_TUPLE_LEN);
    Ok(VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    }))
}

/// A vanishing `Base(Gate(body))` constraint.
fn gate(body: LeanExpr) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::Gate(body))
}

/// A First-row `PiBinding` welding trace column `col` to descriptor PI `pi`.
fn first_pin(col: usize, pi: usize) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::First,
        col,
        pi_index: pi,
    })
}

/// Build the DECO commitment leaf descriptor: recompute `m1`/`payment_hash`/
/// `transcriptCommit` in-AIR (3 chip sites), enforce the amount range (gate 5), and pin
/// the four facts + the identity to the `DECO_CLAIM_LEN`-slot claim tuple.
pub fn deco_to_descriptor2() -> Result<EffectVmDescriptor2, String> {
    let mut constraints: Vec<VmConstraint2> = Vec::new();

    // The four disclosed PaymentFacts, First-row PI-pinned.
    constraints.push(first_pin(COL_AMOUNT, 0));
    constraints.push(first_pin(COL_CURRENCY, 1));
    constraints.push(first_pin(COL_RECIPIENT, 2));
    constraints.push(first_pin(COL_PAYMENT_INTENT, 3));

    // Chip sites: m1, payment_hash, transcriptCommit (7 chip lanes each, past BASE_WIDTH).
    let m1_lane = BASE_WIDTH;
    let ph_lane = BASE_WIDTH + (CHIP_OUT_LANES - 1);
    let tc_lane = BASE_WIDTH + 2 * (CHIP_OUT_LANES - 1);
    // gate (4): m1 = hash_fact(amountCents, [currency, recipient]).
    constraints.push(fact_site(
        COL_M1,
        &[COL_AMOUNT, COL_CURRENCY, COL_RECIPIENT],
        m1_lane,
    )?);
    // the identity: payment_hash = hash_fact(m1, [paymentIntentId]).
    constraints.push(fact_site(
        COL_PAYMENT_HASH,
        &[COL_M1, COL_PAYMENT_INTENT],
        ph_lane,
    )?);
    // gate (3): transcriptCommit = hash_fact(payment_hash, [salt]).
    constraints.push(fact_site(
        COL_TRANSCRIPT_COMMIT,
        &[COL_PAYMENT_HASH, COL_SALT],
        tc_lane,
    )?);
    // pin the identity to the claim lane (the connect target).
    constraints.push(first_pin(COL_PAYMENT_HASH, DECO_LEAF_PAYMENT_HASH_PI));

    // gate (5): the amount range 1 ≤ amountCents < 2^30 — bit-decompose amountCents − 1.
    // Each bit is boolean; the recomposition ties Σ bit_i·2^i to amountCents − 1.
    let mut recompose = sub(LeanExpr::Var(COL_AMOUNT), LeanExpr::Const(1));
    for i in 0..AMOUNT_RANGE_BITS {
        let bit = RANGE_BASE + i;
        // boolean: bit·(bit − 1) = 0.
        constraints.push(gate(LeanExpr::mul(
            LeanExpr::Var(bit),
            LeanExpr::add(LeanExpr::Var(bit), LeanExpr::Const(-1)),
        )));
        recompose = sub(
            recompose,
            LeanExpr::mul(LeanExpr::Const(1i64 << i), LeanExpr::Var(bit)),
        );
    }
    constraints.push(gate(recompose));

    Ok(EffectVmDescriptor2 {
        name: "deco-commitment-leaf::dregg-deco-stripe-v1".to_string(),
        trace_width: BASE_WIDTH + 3 * (CHIP_OUT_LANES - 1),
        public_input_count: DECO_CLAIM_LEN,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    })
}

/// The felt-domain witness the DECO leaf proves over — the `PaymentFacts` decomposed to
/// felts (via `deco_payment::stripe_payment_hash_felt`'s projection) plus the opening
/// `salt`. Every field is the SAME felt the deployed producer writes to the mint row.
#[derive(Clone, Copy, Debug)]
pub struct DecoLeafWitness {
    /// The disclosed amount in cents (`1 ≤ amountCents < 2^30`).
    pub amount_cents: BabyBear,
    /// The ISO-4217 currency felt.
    pub currency: BabyBear,
    /// The recipient dregg-cell felt.
    pub recipient: BabyBear,
    /// The payment-intent-id felt (the replay nonce).
    pub payment_intent: BabyBear,
    /// The transcript-commitment opening blinding.
    pub salt: BabyBear,
}

impl DecoLeafWitness {
    /// The in-AIR felt payment identity over this witness's facts.
    pub fn payment_hash(&self) -> BabyBear {
        deco_payment_hash_felt(
            self.amount_cents,
            self.currency,
            self.recipient,
            self.payment_intent,
        )
    }
}

/// The HONEST `DECO_CLAIM_LEN`-slot claim tuple for a witness:
/// `[amountCents, currency, recipient, paymentIntentId, payment_hash]`.
pub fn deco_leaf_public_inputs(witness: &DecoLeafWitness) -> Vec<BabyBear> {
    vec![
        witness.amount_cents,
        witness.currency,
        witness.recipient,
        witness.payment_intent,
        witness.payment_hash(),
    ]
}

/// Build the base trace (before chip lanes). Four identical rows (a small power-of-two
/// height; every row is a firing row, so the fact sites are consistent per row and the
/// First-row pins bind row 0). Chip lane columns are filled by the general prover's
/// descriptor-driven weld (`trace_with_chip_lanes`).
fn deco_leaf_base_trace(witness: &DecoLeafWitness) -> Vec<Vec<BabyBear>> {
    let m1 = hash_fact(witness.amount_cents, &[witness.currency, witness.recipient]);
    let payment_hash = hash_fact(m1, &[witness.payment_intent]);
    debug_assert_eq!(payment_hash, witness.payment_hash());
    let transcript_commit = hash_fact(payment_hash, &[witness.salt]);

    let amount_u = witness.amount_cents.as_u32();
    let mut row = vec![BabyBear::ZERO; BASE_WIDTH];
    row[COL_AMOUNT] = witness.amount_cents;
    row[COL_CURRENCY] = witness.currency;
    row[COL_RECIPIENT] = witness.recipient;
    row[COL_PAYMENT_INTENT] = witness.payment_intent;
    row[COL_SALT] = witness.salt;
    row[COL_M1] = m1;
    row[COL_PAYMENT_HASH] = payment_hash;
    row[COL_TRANSCRIPT_COMMIT] = transcript_commit;
    // The amount range bits: bit i of (amountCents − 1).
    let amt_minus_1 = amount_u.wrapping_sub(1);
    for i in 0..AMOUNT_RANGE_BITS {
        row[RANGE_BASE + i] = BabyBear::new((amt_minus_1 >> i) & 1);
    }
    vec![row.clone(), row.clone(), row.clone(), row]
}

/// The shared inner IR-v2 prove (descriptor + trace + batch mint under the recursion
/// config type). Passing a claim tuple that disagrees with the witnessed facts is exactly
/// a forged commitment: the `PiBinding{First}` pins + the chip-recomputed `hash_fact`
/// chain make the mismatch UNSAT — no foldable leaf is minted (the leaf-level tooth).
fn prove_deco_inner(
    witness: &DecoLeafWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<
    (
        EffectVmDescriptor2,
        dregg_circuit::descriptor_ir2::Ir2BatchProof<DreggRecursionConfig>,
    ),
    String,
> {
    if public_inputs.len() != DECO_CLAIM_LEN {
        return Err(format!(
            "deco leaf expects {DECO_CLAIM_LEN} PI slots, got {}",
            public_inputs.len()
        ));
    }
    let desc2 = deco_to_descriptor2()?;
    let base_trace = deco_leaf_base_trace(witness);
    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc2,
        &base_trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .map_err(|e| format!("deco leaf inner IR-v2 prove failed: {e}"))?;
    Ok((desc2, inner))
}

/// Prove the DECO commitment as a RECURSION-FOLDABLE IR-v2 leaf (no claim re-expose).
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_deco_leaf(
    witness: &DecoLeafWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let (desc2, inner) = prove_deco_inner(witness, public_inputs, config)?;
    prove_descriptor_leaf_rotated_with_config(&desc2, &inner, public_inputs, config)
        .map_err(|e| format!("deco leaf recursion wrap failed: {e}"))
}

/// Prove the DECO commitment leaf AND RE-EXPOSE its `DECO_CLAIM_LEN`-slot claim tuple as
/// an in-circuit `expose_claim` (lanes `[0 .. DECO_CLAIM_LEN)`), read from the leaf's own
/// FRI-bound descriptor PIs — the DECO analog of
/// [`crate::note_spend_leaf_adapter::prove_note_spend_leaf_with_claim`]. Lane
/// [`DECO_LEAF_PAYMENT_HASH_PI`] is the in-AIR-recomputed felt payment identity.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_deco_leaf_with_claim(
    witness: &DecoLeafWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let (desc2, inner) = prove_deco_inner(witness, public_inputs, config)?;
    prove_descriptor_leaf_with_pi_slice_expose(
        &desc2,
        &inner,
        public_inputs,
        config,
        0,
        DECO_CLAIM_LEN,
    )
    .map_err(|e| format!("deco claim leaf expose-wrap failed: {e}"))
}

/// **THE SEGMENT-PRESERVING DECO PAYMENT-BINDING NODE (deployed-path shape).** The DECO
/// twin of [`crate::note_spend_leaf_adapter::prove_note_spend_mint_binding_node_segmented`]:
/// the leg is a DUAL-EXPOSE leaf over the deployed `stripeMint` row — its `expose_claim` =
/// segment lanes `[0 .. SEG_WIDTH)` ++ ONE claimed lane, the published `payment_hash` PI
/// (the `withPaymentHashPin` pin, producer-filled). The sub-proof leaf is
/// [`prove_deco_leaf_with_claim`]; the node `connect`s the leg's ONE claimed lane to the
/// leaf's lane [`DECO_LEAF_PAYMENT_HASH_PI`] and re-exposes the segment so the result folds
/// into `aggregate_tree` like any per-turn segment leaf.
///
/// ONE lane binds the WHOLE tuple: the leaf's exposed lane is the `hash_fact` chain over
/// its OWN PI-pinned `(amountCents, currency, recipient, paymentIntentId)`, so under
/// Poseidon2-CR a leg identity that connects IS the identity of exactly that verified DECO
/// commitment. A leg publishing an identity no verifying DECO commitment backs is a
/// `connect` conflict ⇒ UNSAT ⇒ no root.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_deco_payment_binding_node_segmented(
    dual_expose_leg_leaf: &RecursionOutput<DreggRecursionConfig>,
    deco_leaf: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use crate::ivc_turn_chain::{SEG_WIDTH, expose_claim_instance_index};
    use crate::plonky3_recursion_impl::recursive::create_recursion_backend;
    use p3_circuit::CircuitBuilder;
    use p3_recursion::{BatchOnly, Target, build_and_prove_aggregation_layer_with_expose};

    type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

    let leg_idx = expose_claim_instance_index(&dual_expose_leg_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "dual-expose deco leg leaf carries no expose_claim table — it must \
                     re-expose (segment ++ the published payment-hash PI)"
                .to_string(),
        }
    })?;
    let cs_idx = expose_claim_instance_index(&deco_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "deco sub-proof leaf carries no exposed tuple (expose_claim) table — it \
                     must be minted via prove_deco_leaf_with_claim"
                .to_string(),
        }
    })?;

    let left = dual_expose_leg_leaf.into_recursion_input::<BatchOnly>();
    let right = deco_leaf.into_recursion_input::<BatchOnly>();

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>]| {
        let lg = left_apt
            .get(leg_idx)
            .expect("dual-expose deco leg's claim instance present");
        let cs = right_apt
            .get(cs_idx)
            .expect("deco sub-proof's exposed tuple instance present");
        debug_assert!(
            lg.len() >= SEG_WIDTH + 1 && cs.len() >= DECO_CLAIM_LEN,
            "dual-expose claim must carry segment ++ the payment-hash lane; deco leaf \
             carries the {DECO_CLAIM_LEN}-lane tuple"
        );
        // THE BINDING TOOTH, IN-CIRCUIT: the leg's published payment identity must equal the
        // deco leaf's in-AIR-recomputed identity over its genuine verified commitment.
        cb.connect(lg[SEG_WIDTH], cs[DECO_LEAF_PAYMENT_HASH_PI]);
        let seg: Vec<Target> = (0..SEG_WIDTH).map(|k| lg[k]).collect();
        cb.expose_as_public_output(&seg);
    };

    build_and_prove_aggregation_layer_with_expose::<DreggRecursionConfig, BatchOnly, BatchOnly, _, D>(
        &left,
        &right,
        config,
        &backend,
        &params,
        None,
        Some(&expose),
    )
    .map_err(|e| JointAggError::AggregationProofInvalid {
        reason: format!("segmented deco payment-binding aggregation node failed: {e:?}"),
    })
}

/// **THE UNSEGMENTED DECO PAYMENT-BINDING NODE** (a leg re-exposing its ONE claimed
/// `payment_hash` lane WITH the deco sub-proof leaf). Connects the two identities and
/// re-exposes the bound identity — the DECO twin of
/// [`crate::note_spend_leaf_adapter::prove_note_spend_binding_node`], used by the fold
/// tooth to exercise the binding without the full deployed segment geometry.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_deco_binding_node(
    leg_claim_leaf: &RecursionOutput<DreggRecursionConfig>,
    deco_leaf: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    use crate::ivc_turn_chain::expose_claim_instance_index;
    use crate::plonky3_recursion_impl::recursive::create_recursion_backend;
    use p3_circuit::CircuitBuilder;
    use p3_recursion::{BatchOnly, Target, build_and_prove_aggregation_layer_with_expose};

    type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

    let leg_idx = expose_claim_instance_index(&leg_claim_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "deco leg leaf carries no re-exposed identity (expose_claim) table".to_string(),
        }
    })?;
    let cs_idx = expose_claim_instance_index(&deco_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "deco sub-proof leaf carries no exposed tuple (expose_claim) table — it must \
                     be minted via prove_deco_leaf_with_claim"
                .to_string(),
        }
    })?;

    let left = leg_claim_leaf.into_recursion_input::<BatchOnly>();
    let right = deco_leaf.into_recursion_input::<BatchOnly>();

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>]| {
        let lg = left_apt
            .get(leg_idx)
            .expect("deco leg's re-exposed identity present");
        let cs = right_apt
            .get(cs_idx)
            .expect("deco sub-proof's exposed tuple present");
        debug_assert!(lg.len() >= 1 && cs.len() >= DECO_CLAIM_LEN);
        // The leg claims ONE lane (its published identity); connect it to the leaf's lane.
        cb.connect(lg[0], cs[DECO_LEAF_PAYMENT_HASH_PI]);
        cb.expose_as_public_output(&[lg[0]]);
    };

    build_and_prove_aggregation_layer_with_expose::<DreggRecursionConfig, BatchOnly, BatchOnly, _, D>(
        &left,
        &right,
        config,
        &backend,
        &params,
        None,
        Some(&expose),
    )
    .map_err(|e| JointAggError::AggregationProofInvalid {
        reason: format!("deco payment-binding aggregation node failed: {e:?}"),
    })
}

/// Read the exposed `DECO_CLAIM_LEN`-lane claim tuple off a leaf minted by
/// [`prove_deco_leaf_with_claim`].
pub fn read_exposed_deco_claim(
    output: &RecursionOutput<DreggRecursionConfig>,
) -> Option<[BabyBear; DECO_CLAIM_LEN]> {
    let claims: Vec<BabyBear> = output
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")?
        .public_values
        .iter()
        .map(|&v| BabyBear::new(v.as_canonical_u32()))
        .collect();
    if claims.len() < DECO_CLAIM_LEN {
        return None;
    }
    Some(core::array::from_fn(|i| claims[i]))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ivc_turn_chain::ir2_leaf_wrap_config;
    use dregg_circuit::descriptor_ir2::{VmConstraint2, chip_absorb_all_lanes};

    fn make_witness(tag: u32) -> DecoLeafWitness {
        DecoLeafWitness {
            amount_cents: BabyBear::new(2500 + tag),
            currency: BabyBear::new(840),
            recipient: BabyBear::new(0x1000 + tag),
            payment_intent: BabyBear::new(0xABCD + tag),
            salt: BabyBear::new(0x55 + tag),
        }
    }

    /// The KAT the whole fact-site carrier rests on: the arity-7 chip absorb over
    /// `[pred, t0..t3, 0xFACF, 1]` is BYTE-IDENTICAL to `hash_fact` (1- and 2-term).
    #[test]
    fn deco_fact_site_absorb_matches_hash_fact() {
        let pred = BabyBear::new(777);
        let t = [BabyBear::new(11), BabyBear::new(22)];
        let ins2 = [
            pred,
            t[0],
            t[1],
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::new(DECO_FACT_MARK),
            BabyBear::ONE,
        ];
        assert_eq!(
            chip_absorb_all_lanes(7, &ins2)[0],
            hash_fact(pred, &[t[0], t[1]])
        );
        let ins1 = [
            pred,
            t[0],
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::new(DECO_FACT_MARK),
            BabyBear::ONE,
        ];
        assert_eq!(chip_absorb_all_lanes(7, &ins1)[0], hash_fact(pred, &[t[0]]));
    }

    /// The descriptor lowers to the expected shape: 3 chip sites, DECO_CLAIM_LEN PIs,
    /// 5 First-row pins (4 facts + payment_hash), 31 range gates + a recomposition gate.
    #[test]
    fn deco_descriptor_lowers() {
        let desc = deco_to_descriptor2().expect("the deco leaf descriptor builds");
        assert_eq!(desc.public_input_count, DECO_CLAIM_LEN);
        let sites = desc
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
            .count();
        assert_eq!(sites, 3, "m1 + payment_hash + transcriptCommit");
        let pins = desc
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
            .count();
        assert_eq!(pins, 5, "4 fact pins + the payment_hash pin");
        assert_eq!(desc.trace_width, BASE_WIDTH + 3 * (CHIP_OUT_LANES - 1));
    }

    /// The host claim tuple matches the named composition (lane 4 = the anchor).
    #[test]
    fn public_inputs_match_named_identity() {
        let w = make_witness(0);
        let pis = deco_leaf_public_inputs(&w);
        assert_eq!(pis.len(), DECO_CLAIM_LEN);
        assert_eq!(pis[DECO_LEAF_PAYMENT_HASH_PI], w.payment_hash());
        assert_eq!(
            pis[DECO_LEAF_PAYMENT_HASH_PI],
            deco_payment_hash_felt(pis[0], pis[1], pis[2], pis[3]),
        );
    }

    /// THE POSITIVE POLE: an honest DECO commitment proves as a foldable recursion leaf,
    /// and the exposed claim equals the bound PIs — lane 4 the in-AIR-recomputed identity.
    #[test]
    #[ignore = "SLOW: real recursion leaf wrap (~seconds+); run with --ignored"]
    fn honest_deco_proves_as_foldable_leaf_and_exposes_claim() {
        let w = make_witness(0x10);
        let pis = deco_leaf_public_inputs(&w);
        let config = ir2_leaf_wrap_config();
        let output = prove_deco_leaf_with_claim(&w, &pis, &config)
            .expect("the honest deco commitment must prove as a foldable claim leaf");
        let exposed = read_exposed_deco_claim(&output).expect("the leaf exposes the claim");
        assert_eq!(
            exposed.as_slice(),
            pis.as_slice(),
            "exposed claim is the bound tuple"
        );
    }

    /// THE LEAF-BINDING TOOTH: a forged `payment_hash` lane (every fact honest) is refused
    /// AT THE LEAF — the in-AIR recompute (two chip sites over the PI-pinned fact columns) +
    /// the PI-4 pin make it UNSAT. What makes the exposed identity a WELD, not a scalar.
    #[test]
    #[ignore = "SLOW: real recursion leaf wrap (~seconds+); run with --ignored"]
    fn forged_payment_hash_does_not_fold() {
        let w = make_witness(0x22);
        let mut pis = deco_leaf_public_inputs(&w);
        pis[DECO_LEAF_PAYMENT_HASH_PI] += BabyBear::ONE;
        let config = ir2_leaf_wrap_config();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_deco_leaf(&w, &pis, &config)
        }));
        match result {
            Err(_) => {}
            Ok(Err(_)) => {}
            Ok(Ok(_)) => panic!("a FORGED payment_hash minted a foldable leaf — soundness OPEN"),
        }
    }

    /// THE FACT-BINDING TOOTH: a forged fact lane (tampered amount, payment_hash stale) is
    /// refused AT THE LEAF — the pinned amount no longer recomputes the pinned identity.
    #[test]
    #[ignore = "SLOW: real recursion leaf wrap (~seconds+); run with --ignored"]
    fn forged_amount_does_not_fold() {
        let w = make_witness(0x33);
        let mut pis = deco_leaf_public_inputs(&w);
        pis[COL_AMOUNT] += BabyBear::ONE; // amount changes, payment_hash lane stays
        let config = ir2_leaf_wrap_config();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_deco_leaf(&w, &pis, &config)
        }));
        match result {
            Err(_) => {}
            Ok(Err(_)) => {}
            Ok(Ok(_)) => panic!("a FORGED amount minted a foldable leaf — soundness OPEN"),
        }
    }

    /// A "leg" that publishes ONE claimed payment identity at claim position 0 — the DECO leaf
    /// of `witness` sliced to expose ONLY its `payment_hash` lane. Stands in for the deployed
    /// `stripeMint` leg's published `payment_hash` PI (which rides the big-bang descriptor
    /// regen) so the fold's `connect` tooth is exercised through the REAL recursion now.
    fn prove_deco_leg_identity(
        witness: &DecoLeafWitness,
        config: &DreggRecursionConfig,
    ) -> RecursionOutput<DreggRecursionConfig> {
        let pis = deco_leaf_public_inputs(witness);
        let (desc2, inner) = prove_deco_inner(witness, &pis, config).expect("leg inner proves");
        prove_descriptor_leaf_with_pi_slice_expose(
            &desc2,
            &inner,
            &pis,
            config,
            DECO_LEAF_PAYMENT_HASH_PI,
            1,
        )
        .expect("leg exposes its published payment identity")
    }

    /// THE FOLD-CONNECT TOOTH (POSITIVE): a leg publishing identity `A` folded WITH the DECO
    /// commitment leaf of the SAME payment `A` — the in-circuit `connect` (leg identity ==
    /// leaf's in-AIR-recomputed identity) is satisfied, so the binding node PROVES.
    #[test]
    #[ignore = "SLOW: real recursion fold (~seconds+); run with --ignored"]
    fn fold_honest_identity_connects() {
        let w = make_witness(0x40);
        let config = ir2_leaf_wrap_config();
        let leg = prove_deco_leg_identity(&w, &config);
        let backing =
            prove_deco_leaf_with_claim(&w, &deco_leaf_public_inputs(&w), &config).expect("leaf");
        prove_deco_binding_node(&leg, &backing, &config)
            .expect("honest identity: the fold connect must PROVE (leg == leaf identity)");
    }

    /// THE FOLD-CONNECT TOOTH (NEGATIVE — the anti-ghost bite): a leg publishing identity `A`
    /// folded with the DECO commitment leaf of a DIFFERENT payment `B` (A != B) — the
    /// in-circuit `connect` conflicts ⇒ UNSAT ⇒ no root. A published payment identity no
    /// verifying DECO commitment backs cannot fold (the fold twin of the Lean
    /// `forged_payment_hash_unsat_demo`).
    #[test]
    #[ignore = "SLOW: real recursion fold (~seconds+); run with --ignored"]
    fn fold_mismatched_identity_unsat() {
        let config = ir2_leaf_wrap_config();
        let leg_w = make_witness(0x41); // leg claims identity A
        let backing_w = make_witness(0x99); // backing leaf proves identity B != A
        assert_ne!(leg_w.payment_hash(), backing_w.payment_hash());
        let leg = prove_deco_leg_identity(&leg_w, &config);
        let backing =
            prove_deco_leaf_with_claim(&backing_w, &deco_leaf_public_inputs(&backing_w), &config)
                .expect("backing leaf B proves");
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_deco_binding_node(&leg, &backing, &config)
        }));
        match result {
            Err(_) => {}
            Ok(Err(_)) => {}
            Ok(Ok(_)) => panic!(
                "a leg identity backed by NO matching DECO commitment folded — the connect is OPEN"
            ),
        }
    }
}
