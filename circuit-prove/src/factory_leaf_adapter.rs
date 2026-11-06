//! Re-prove a factory-born cell's CREATION-BACKING tuple as a RECURSION-FOLDABLE IR-v2 leaf
//! (the factory analog of [`crate::sovereign_leaf_adapter`] / [`crate::custom_leaf_adapter`]).
//!
//! ## What this closes
//!
//! `Effect::CreateCellFromFactory` (`turn/src/action.rs:1218`) installs a child cell's `child_vk`,
//! capabilities, initial fields, and slot caveats via a GENERIC `EFFECT_CREATE_CELL` selector — there
//! is NO factory AIR and NO STARK constraining the creation. The off-AIR validator
//! [`dregg_cell::factory::FactoryRegistry::validate_and_record`] (`cell/src/factory.rs:917`, called at
//! `turn/src/executor/apply.rs:2360`) does ALL the work:
//!
//!   * (a) the CHILD-VK DERIVATION — `child_vk` is the descriptor's strategy-derived VK
//!     (`ChildVkStrategy::validate_child_vk`: `Fixed` exact / `Derived` `Poseidon2(factory_vk ‖
//!     param_hash)` / `FromSet` membership, `factory.rs:236`);
//!   * (b) the CAPABILITY ENVELOPE — every granted cap is within an `allowed_cap_templates` entry
//!     (`cap_within_templates`, `factory.rs:481`);
//!   * (c) the FIELD + BUDGET ENVELOPE — initial fields satisfy `field_constraints`, and the per-epoch
//!     `creation_budget` is not exhausted (`record_creation`, `factory.rs:883`).
//!
//! The executor then merely INSTALLS the validated `child_vk` / `state_constraints` as IDENTIFIERS
//! (`apply.rs:2416..2443`). A PURE LIGHT CLIENT (one that only folds the per-turn recursion tree)
//! never witnesses any of (a)/(b)/(c): the deployed `EFFECT_CREATE_CELL` row carries the prover's
//! CLAIMED `child_vk` / caps / fields with NO constraint linking them to a verifying factory
//! descriptor. The refutation [`metatheory/Dregg2/Circuit/FactoryBackingAttack.lean`]
//! (`deployed_admits_forged_child_vk`) exhibits the forged factory-born cell the deployed AIR admits.
//!
//! This module mints the BACKING tuple `(factory_vk, child_vk, derivation_digest)` as a
//! recursion-foldable IR-v2 leaf — the same `aggregate_tree` chain a light client verifies — so the
//! binding node [`prove_factory_binding_node_segmented`] (below) can `connect` it to the deployed
//! `EFFECT_CREATE_CELL` leg's claimed `child_vk` teeth, exactly as
//! `joint_turn_recursive::prove_sovereign_binding_node_segmented` connects the sovereign leg.
//!
//! ## The constraint mapping (the same TOTAL, table-free shape `sovereign_leaf_adapter` uses)
//!
//! The backing tuple is a fixed-width vector pinned at row 0 and held constant:
//!
//! | family                                                  | maps to                                              |
//! |---------------------------------------------------------|------------------------------------------------------|
//! | boundary: `row0[col c] == pi[c]` (all 24 slots)         | `Base(PiBinding{First, col=c, pi=c})` (EXACT)        |
//! | transition: `next[c] − local[c] == 0` (every column)    | `WindowGate{Nxt(c) − Loc(c), on_transition}` (EXACT) |
//!
//! Both carriers are `main`-table algebra; the descriptor declares NO tables. A prover cannot put one
//! tuple in row 0 and a different tuple in a padding row, and a tuple slot that disagrees with the
//! bound PI is UNSAT — no foldable leaf is minted.
//!
//! ## The derivation-digest boundary (NAMED honestly)
//!
//! This leaf binds the backing TUPLE in-circuit. The `derivation_digest` is a `Poseidon2` commitment
//! to the validated `caps ‖ fields ‖ budget ‖ param_hash`; the full in-AIR re-derivation of
//! `Poseidon2(factory_vk ‖ param_hash)` for `child_vk` and the Merkle-membership of
//! `allowed_cap_templates` stay OFF-AIR — the same digest-of-attestation boundary the sovereign /
//! membership carriers ride (full in-AIR derivation is the named cost, not done here). What the fold
//! WITNESSES is: the deployed factory leg's claimed `child_vk` (the teeth) equals the `child_vk` THIS
//! leaf binds, and the leaf's tuple is internally consistent (factory_vk / derivation_digest pinned).
//! The residual — re-deriving the digest from `factory_vk` + params in-circuit — is the named
//! follow-up.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2Air, MemBoundaryWitness, UMemBoundaryWitness,
    ir2_airs_and_common_for_config, prove_vm_descriptor2_for_config,
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

// ---- Backing-tuple layout (the leaf's descriptor PI slots) ----
/// The factory's own program VK digest (the deployed `FACTORY_VK` teeth).
pub const FACTORY_VK_LO: usize = 0;
/// Length of a VK digest (8 felts / ~124-bit faithful, matching the 8-felt commit width).
pub const VK_DIGEST_LEN: usize = 8;
/// The validated/derived child program VK digest (the deployed `CHILD_VK` teeth).
pub const CHILD_VK_LO: usize = FACTORY_VK_LO + VK_DIGEST_LEN;
/// The `Poseidon2` digest binding the validated derivation (`caps ‖ fields ‖ budget ‖ param_hash`).
pub const DERIVATION_DIGEST_LO: usize = CHILD_VK_LO + VK_DIGEST_LEN;
/// Length of the derivation digest (8 felts).
pub const DERIVATION_DIGEST_LEN: usize = 8;
/// Total backing-tuple width / PI count (8 + 8 + 8 = 24).
pub const FACTORY_TUPLE_WIDTH: usize = DERIVATION_DIGEST_LO + DERIVATION_DIGEST_LEN;

/// The `child_vk` claim the leaf re-exposes for the binding node to `connect` (8 felts).
pub const FACTORY_CHILD_VK_CLAIM_LEN: usize = VK_DIGEST_LEN;

/// A factory-born cell's creation-backing tuple — the SAME `(factory_vk, child_vk,
/// derivation_digest)` the off-AIR `validate_and_record` validator binds: the descriptor's
/// `factory_vk`, the strategy-derived `child_vk`, and a `Poseidon2` digest over the validated
/// caps/fields/budget/param_hash.
#[derive(Clone, Debug)]
pub struct FactoryBackingWitness {
    /// The factory's own program VK digest (the descriptor's `factory_vk`).
    pub factory_vk: [BabyBear; VK_DIGEST_LEN],
    /// The strategy-derived child program VK digest (the validated `child_vk`).
    pub child_vk: [BabyBear; VK_DIGEST_LEN],
    /// `Poseidon2(caps ‖ fields ‖ budget ‖ param_hash)` — the validated-derivation digest.
    pub derivation_digest: [BabyBear; DERIVATION_DIGEST_LEN],
}

impl FactoryBackingWitness {
    /// The 24-slot bound backing tuple carried as the leaf's descriptor PIs.
    pub fn public_inputs(&self) -> Vec<BabyBear> {
        let mut pis = vec![BabyBear::new(0); FACTORY_TUPLE_WIDTH];
        pis[FACTORY_VK_LO..FACTORY_VK_LO + VK_DIGEST_LEN].copy_from_slice(&self.factory_vk);
        pis[CHILD_VK_LO..CHILD_VK_LO + VK_DIGEST_LEN].copy_from_slice(&self.child_vk);
        pis[DERIVATION_DIGEST_LO..DERIVATION_DIGEST_LO + DERIVATION_DIGEST_LEN]
            .copy_from_slice(&self.derivation_digest);
        pis
    }

    /// The base trace: the backing tuple replicated across two rows (the `WindowGate` continuity
    /// glue pins every column constant, so one typed row padded to a power of two binds the whole
    /// tuple). Width == `FACTORY_TUPLE_WIDTH`.
    pub fn generate_trace(&self) -> Vec<Vec<BabyBear>> {
        let row = self.public_inputs();
        vec![row.clone(), row]
    }
}

/// Adapt the factory backing tuple into the IR-v2 [`EffectVmDescriptor2`]: 24 boundary pins
/// (`PiBinding{First}`, EXACT — `pi_index == col`) + 24 transition pins (`WindowGate{Nxt(c) −
/// Loc(c)}`, EXACT — every column constant across rows). Authored by Lean `TupleBindingEmit.tupleDesc`; parsing
/// fails closed if the generated artifact is invalid.
pub fn factory_backing_to_descriptor2() -> Result<EffectVmDescriptor2, String> {
    dregg_circuit::descriptor_ir2::parse_vm_descriptor2(include_str!(
        "../../circuit/descriptors/by-name/factory-backing-leaf.json"
    ))
}

/// Prove a factory backing tuple as a RECURSION-FOLDABLE IR-v2 leaf (the sovereign/bridge pattern).
/// `public_inputs` is the 24-slot bound tuple — for an HONEST proof it equals
/// `witness.public_inputs()`. Passing a DIFFERENT tuple is a forged binding (trace claims one tuple,
/// PIs another): the `PiBinding{First}` requires `row0[col] == pi[col]`, so the mismatch is UNSAT and
/// no foldable leaf is minted.
pub fn prove_factory_leaf(
    witness: &FactoryBackingWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    if public_inputs.len() != FACTORY_TUPLE_WIDTH {
        return Err(format!(
            "factory-backing leaf expects {FACTORY_TUPLE_WIDTH} PI slots, got {}",
            public_inputs.len()
        ));
    }
    let desc2 = factory_backing_to_descriptor2()?;
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
    .map_err(|e| format!("factory-backing leaf inner IR-v2 prove failed: {e}"))?;

    prove_descriptor_leaf_rotated_with_config(&desc2, &inner, public_inputs, config)
        .map_err(|e| format!("factory-backing leaf recursion wrap failed: {e}"))
}

/// Prove the factory backing tuple as a foldable leaf AND re-expose its bound 8-felt `child_vk`
/// (lanes `[CHILD_VK_LO .. CHILD_VK_LO+VK_DIGEST_LEN)`) as a public CLAIM the binding node `connect`s
/// to the deployed `EFFECT_CREATE_CELL` leg's `CHILD_VK` teeth.
///
/// Re-exposes the leaf's OWN FRI-bound descriptor PI lanes directly (the same direct-lane re-expose
/// the sovereign key-claim leaf uses), so the plain backend suffices (no `recompose/coeff` table).
/// The exposed `child_vk` is welded to the execution: a prover cannot expose a `child_vk` that
/// disagrees with the tuple the leaf proves, because both are the SAME in-circuit PI targets.
pub fn prove_factory_leaf_with_child_vk_claim(
    witness: &FactoryBackingWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    if public_inputs.len() != FACTORY_TUPLE_WIDTH {
        return Err(format!(
            "factory-backing leaf expects {FACTORY_TUPLE_WIDTH} PI slots, got {}",
            public_inputs.len()
        ));
    }
    let desc2 = factory_backing_to_descriptor2()?;
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
    .map_err(|e| format!("factory-backing child-vk-claim leaf inner IR-v2 prove failed: {e}"))?;

    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(&desc2, &inner, public_inputs, config).map_err(|e| {
            format!("factory-backing child-vk-claim verify-triple build failed: {e}")
        })?;

    let input: RecursionInput<'_, DreggRecursionConfig, Ir2Air> =
        RecursionInput::NativeBatchStark {
            airs: &airs,
            proof: &inner,
            common_data: &common,
            table_public_inputs,
        };

    // Plain backend: a direct-lane re-expose carries no decompose/coeff table.
    let backend = create_recursion_backend();

    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       apt: &[Vec<Target>],
                       _vk_cap: &[Target]| {
        let main = apt
            .first()
            .expect("factory-backing leaf has a main instance carrying the descriptor PIs");
        debug_assert!(
            main.len() >= CHILD_VK_LO + VK_DIGEST_LEN,
            "main instance must carry the child_vk PI slots"
        );
        // Re-expose the FRI-bound child_vk lanes directly (not free scalars).
        let claim: Vec<Target> = (0..VK_DIGEST_LEN).map(|k| main[CHILD_VK_LO + k]).collect();
        cb.expose_as_public_output(&claim);
    };

    build_and_prove_next_layer_with_expose::<DreggRecursionConfig, Ir2Air, _, D>(
        &input,
        &recursion_layer_over(config),
        &backend,
        &ProveNextLayerParams::default(),
        Some(&expose),
    )
    .map_err(|e| format!("factory-backing child-vk-claim leaf-wrap failed: {e:?}"))
}

/// Read the 8-felt `child_vk` a [`prove_factory_leaf_with_child_vk_claim`] leaf exposes through its
/// `expose_claim` table. Returns `None` if the proof carries no claim.
pub fn read_exposed_child_vk(
    output: &RecursionOutput<DreggRecursionConfig>,
) -> Option<[BabyBear; FACTORY_CHILD_VK_CLAIM_LEN]> {
    let claims: Vec<BabyBear> = output
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")?
        .public_values
        .iter()
        .map(|&v| BabyBear::new(v.as_canonical_u32()))
        .collect();
    if claims.len() < FACTORY_CHILD_VK_CLAIM_LEN {
        return None;
    }
    let mut out = [BabyBear::new(0); FACTORY_CHILD_VK_CLAIM_LEN];
    out.copy_from_slice(&claims[..FACTORY_CHILD_VK_CLAIM_LEN]);
    Some(out)
}

/// The binding node's failure prefix, single-sourced so the production `format!` and
/// `binding_tooth`'s arm assertion cannot drift apart.
pub const FACTORY_BINDING_NODE_SEGMENTED_ARM: &str =
    "segmented factory-binding aggregation node failed";

/// **THE SEGMENT-PRESERVING FACTORY BINDING NODE (the factory analog of
/// [`crate::joint_turn_recursive::prove_sovereign_binding_node_segmented`]).** Aggregate a factory
/// turn's DUAL-EXPOSE `EFFECT_CREATE_CELL` leg leaf (whose single `expose_claim` carries the chain
/// SEGMENT in lanes `[0 .. SEG_WIDTH)` and the CLAIMED `CHILD_VK` teeth in lanes
/// `[SEG_SPINE_WIDTH .. SEG_SPINE_WIDTH+FACTORY_CHILD_VK_CLAIM_LEN)`) WITH the re-proved factory-backing leaf
/// ([`prove_factory_leaf_with_child_vk_claim`], whose `expose_claim` is the in-circuit-bound
/// `child_vk` in lanes `[0 .. FACTORY_CHILD_VK_CLAIM_LEN)`), and:
///
///   1. `connect`s the leg's claimed `child_vk` lanes to the backing leaf's bound `child_vk` (the
///      binding tooth — a forged factory cell whose teeth name a `child_vk` no backing leaf binds is
///      a conflict ⇒ UNSAT ⇒ no root), and
///   2. RE-EXPOSES `[the leg's SEGMENT lanes [0 .. SEG_WIDTH) ‖ a folded vk_spine]` as the parent claim.
///
/// The output exposes an ordinary `SEG_SPINE_WIDTH`-lane `[segment ‖ vk_spine]` claim, so it folds into
/// [`crate::ivc_turn_chain::aggregate_tree`] like any other per-turn segment leaf. This is what makes
/// the factory backing REAL for a pure light client: the `child_vk` the deployed leg claims is bound
/// IN the deployed recursion tree the light client folds, to the backing tuple the factory leaf
/// proves, while the chain `[genesis_root, final_root, num_turns, chain_digest]` still reaches the
/// root.
///
/// THE NAMED SEAMS (honest):
///   * The deployed factory leg must DUAL-EXPOSE its `CHILD_VK` teeth (lanes `[SEG_SPINE_WIDTH ..)`).
///     Today the generic `EFFECT_CREATE_CELL` row carries the claimed `child_vk` ungated; the
///     teeth-fill on the rotated producer + the leg's dual-expose of them is **THE BIG-BANG
///     DESCRIPTOR PIECE** (a PI-exposure change, owned by the descriptor lane). This node is its
///     consumer.
///   * The node binds `child_vk` (leg (a) derivation). Connecting the `factory_vk` + the
///     `derivation_digest` (legs (b) caps + (c) field/budget) needs the leg to expose those slots
///     too — the same big-bang piece, widened. The backing leaf already binds all three in-circuit
///     (factory_vk/child_vk/derivation_digest are pinned PIs), so widening the connect is a
///     lane-count change, not new soundness machinery.
///   * The full in-AIR re-derivation `child_vk = Poseidon2(factory_vk ‖ param_hash)` + the
///     Merkle-membership of `allowed_cap_templates` stay OFF-AIR — the digest-of-attestation
///     boundary (see this module's docs).
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`]. Both children re-expose
/// FRI-bound PI lanes directly (no `recompose/coeff` table), so the plain backend suffices.
pub fn prove_factory_binding_node_segmented(
    dual_expose_leg_leaf: &RecursionOutput<DreggRecursionConfig>,
    factory_backing_leaf: &RecursionOutput<DreggRecursionConfig>,
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
            reason: "dual-expose factory leg leaf carries no expose_claim table — it must be \
                     wrapped to expose segment ++ child_vk (the EFFECT_CREATE_CELL CHILD_VK teeth)"
                .to_string(),
        }
    })?;
    let fa_idx = expose_claim_instance_index(&factory_backing_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "factory-backing leaf carries no exposed child_vk (expose_claim) table — \
                     it must be minted via prove_factory_leaf_with_child_vk_claim"
                .to_string(),
        }
    })?;

    let left = dual_expose_leg_leaf.into_recursion_input_pinned::<BatchOnly>(pins.left.clone());
    let right = factory_backing_leaf.into_recursion_input_pinned::<BatchOnly>(pins.right.clone());

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>],
                       left_vk_cap: &[Target],
                       right_vk_cap: &[Target]| {
        let ev = left_apt
            .get(ev_idx)
            .expect("dual-expose factory leg's claim instance present");
        let fa = right_apt
            .get(fa_idx)
            .expect("factory-backing leaf's exposed child_vk instance present");
        debug_assert!(
            ev.len() >= SEG_SPINE_WIDTH + FACTORY_CHILD_VK_CLAIM_LEN
                && fa.len() >= FACTORY_CHILD_VK_CLAIM_LEN,
            "dual-expose claim must carry segment ++ child_vk; backing leaf carries child_vk"
        );
        // THE BINDING TOOTH, IN-CIRCUIT: the leg's CLAIMED child_vk (lanes
        // [SEG_SPINE_WIDTH .. SEG_SPINE_WIDTH+CHILD_VK_LEN)) must equal the backing leaf's BOUND child_vk, lane by
        // lane. A factory cell whose teeth name a child_vk no backing leaf binds is a conflict here ⇒
        // UNSAT ⇒ no root.
        for k in 0..FACTORY_CHILD_VK_CLAIM_LEN {
            cb.connect(ev[SEG_SPINE_WIDTH + k], fa[k]);
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
        reason: format!("{FACTORY_BINDING_NODE_SEGMENTED_ARM}: {e:?}"),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binding_tooth::{assert_node_refused_by_binding_connect, report_refusal};
    use crate::ivc_turn_chain::{
        SEG_SPINE_WIDTH, SEG_VK_SPINE_FIRST, SEG_WIDTH, ir2_leaf_wrap_config, leaf_vk_spine_host,
        prove_descriptor_leaf_with_pi_slice_expose,
    };
    use dregg_circuit::descriptor_ir2::VmConstraint2;
    use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};
    use dregg_circuit::refusal::{assert_violated_constraint_not_bus, must_refuse};

    fn make_witness() -> FactoryBackingWitness {
        FactoryBackingWitness {
            factory_vk: core::array::from_fn(|i| BabyBear::new(100 + i as u32)),
            child_vk: core::array::from_fn(|i| BabyBear::new(200 + i as u32)),
            derivation_digest: core::array::from_fn(|i| BabyBear::new(300 + i as u32)),
        }
    }

    #[test]
    fn factory_backing_maps_to_descriptor2() {
        let desc2 = factory_backing_to_descriptor2().expect("factory maps");
        assert_eq!(desc2.trace_width, FACTORY_TUPLE_WIDTH);
        assert_eq!(desc2.public_input_count, FACTORY_TUPLE_WIDTH);
        assert!(desc2.tables.is_empty());
        assert!(desc2.hash_sites.is_empty());
        assert!(desc2.ranges.is_empty());
        assert_eq!(desc2.constraints.len(), 2 * FACTORY_TUPLE_WIDTH);
        let pi_bindings = desc2
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
            .count();
        assert_eq!(pi_bindings, FACTORY_TUPLE_WIDTH);
    }

    /// THE POSITIVE POLE: an honest backing tuple proves as a foldable recursion leaf.
    #[test]
    fn honest_factory_backing_proves_as_foldable_leaf() {
        let w = make_witness();
        let pis = w.public_inputs();
        assert_eq!(pis.len(), FACTORY_TUPLE_WIDTH);
        let config = ir2_leaf_wrap_config();
        let _output = prove_factory_leaf(&w, &pis, &config)
            .expect("the honest factory backing must prove as a foldable leaf");
    }

    /// THE POSITIVE POLE (claim variant): the child-vk-claim leaf folds AND re-exposes the bound
    /// 8-felt child_vk.
    #[test]
    fn honest_child_vk_claim_leaf_exposes_bound_child_vk() {
        let w = make_witness();
        let pis = w.public_inputs();
        let config = ir2_leaf_wrap_config();
        let output = prove_factory_leaf_with_child_vk_claim(&w, &pis, &config)
            .expect("the child-vk-claim leaf must fold");
        let exposed = read_exposed_child_vk(&output).expect("a child_vk claim is exposed");
        assert_eq!(
            exposed, w.child_vk,
            "the exposed child_vk is the bound tuple's"
        );
    }

    /// THE NEGATIVE POLE (leaf): a FORGED tuple (trace carries one child_vk, the bound PIs claim a
    /// TAMPERED one) has no satisfying assembly — `PiBinding{First}` requires `row0[col] == pi[col]`,
    /// so the mismatch is UNSAT. No foldable leaf is minted.
    #[test]
    fn forged_backing_tuple_does_not_fold() {
        let w = make_witness();
        let mut tampered = w.clone();
        tampered.child_vk[0] += BabyBear::new(1);
        let forged_pis = tampered.public_inputs();
        assert_ne!(forged_pis, w.public_inputs());
        let config = ir2_leaf_wrap_config();

        let what = "a FORGED factory backing tuple";
        let err = must_refuse(what, || prove_factory_leaf(&w, &forged_pis, &config));
        // ⚑ NAME THE VERDICT. The tooth's claim is that `PiBinding{First}` (`row0[col] == pi[col]`)
        // is UNSAT — a violated CONSTRAINT. A bare `must_refuse` was satisfied identically by the
        // leaf's own PI-count pre-flight, by the recursion wrap failing, or by an OOM.
        // `assert_violated_constraint_not_bus` is the profile-independent form: p3's
        // `constraints not satisfied on row N` under `cargo test`, the deployed verifier's
        // `OodEvaluationMismatch` under `--release`, and NEITHER bus verdict in either.
        report_refusal(what, &err);
        assert_violated_constraint_not_bus(what, &err);
    }

    /// Build a factory `EFFECT_CREATE_CELL` leg leaf that PUBLISHES
    /// `[segment ‖ vk_spine ‖ child_vk]` as a contiguous IR2 PI slice
    /// `[0 .. SEG_SPINE_WIDTH+VK_DIGEST_LEN)` and re-exposes it for the fold — a minimal stand-in
    /// for the deployed trace at the SAME dual-expose surface (the BIG-BANG descriptor piece's
    /// consumer side). The spine block carries the honest [`leaf_vk_spine_host`] value, so the row
    /// mirrors what `prove_descriptor_leaf_dual_expose_at` mints, not just its width.
    fn factory_leg_leaf(
        segment: &[BabyBear],
        claimed_child_vk: [BabyBear; VK_DIGEST_LEN],
        config: &DreggRecursionConfig,
    ) -> RecursionOutput<DreggRecursionConfig> {
        use dregg_circuit::descriptor_ir2::{
            MemBoundaryWitness, UMemBoundaryWitness, prove_vm_descriptor2_for_config,
        };
        let claim_width = SEG_SPINE_WIDTH + VK_DIGEST_LEN;
        let pi_count = claim_width;
        // Pin the contiguous claim slice [0 .. claim_width) to row 0 via PiBinding.first.
        let constraints: Vec<VmConstraint2> = (0..claim_width)
            .map(|k| {
                VmConstraint2::Base(VmConstraint::PiBinding {
                    row: VmRow::First,
                    col: k,
                    pi_index: k,
                })
            })
            .collect();
        let desc = EffectVmDescriptor2 {
            name: "EFFECT_CREATE_CELL-dual-expose-standin".to_string(),
            trace_width: claim_width,
            public_input_count: pi_count,
            challenges: 0,
            tables: vec![],
            constraints,
            hash_sites: vec![],
            ranges: vec![],
        };
        let mut row = vec![BabyBear::new(0); claim_width];
        row[..SEG_WIDTH].copy_from_slice(segment);
        row[SEG_VK_SPINE_FIRST..SEG_SPINE_WIDTH].copy_from_slice(&leaf_vk_spine_host());
        row[SEG_SPINE_WIDTH..claim_width].copy_from_slice(&claimed_child_vk);
        let trace: Vec<Vec<BabyBear>> = vec![row.clone(), row.clone()];
        let pis = row;
        let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
            &desc,
            &trace,
            &pis,
            &MemBoundaryWitness::default(),
            &[],
            &UMemBoundaryWitness::default(),
            config,
        )
        .expect("factory leg stand-in proves (the claim is internally consistent)");
        prove_descriptor_leaf_with_pi_slice_expose(&desc, &inner, &pis, config, 0, claim_width)
            .expect("factory leg leaf re-exposes [segment ‖ child_vk]")
    }

    /// Read the SEG_WIDTH-lane segment a binding node re-exposes through its `expose_claim` table.
    fn read_exposed_segment(
        output: &RecursionOutput<DreggRecursionConfig>,
    ) -> Option<Vec<BabyBear>> {
        let claims: Vec<BabyBear> = output
            .0
            .non_primitives
            .iter()
            .find(|e| e.op_type.as_str() == "expose_claim")?
            .public_values
            .iter()
            .map(|&v| BabyBear::new(v.as_canonical_u32()))
            .collect();
        if claims.len() < SEG_WIDTH {
            return None;
        }
        Some(claims[..SEG_WIDTH].to_vec())
    }

    /// THE TOOTH — POSITIVE POLE: an HONEST factory turn whose `EFFECT_CREATE_CELL` leg claims the
    /// SAME `child_vk` the backing leaf binds folds, and the node re-exposes the chain SEGMENT (the
    /// light client's segment tooth) — the aggregate is satisfiable, a pure light client accepts.
    #[test]
    fn honest_factory_turn_binds_in_the_fold() {
        let config = ir2_leaf_wrap_config();
        let w = make_witness();
        let pis = w.public_inputs();
        let segment: Vec<BabyBear> = (0..SEG_WIDTH)
            .map(|i| BabyBear::new(7000 + i as u32))
            .collect();

        let backing_leaf = prove_factory_leaf_with_child_vk_claim(&w, &pis, &config)
            .expect("the factory backing leaf folds");
        let leg_leaf = factory_leg_leaf(&segment, w.child_vk, &config); // claims the REAL child_vk

        let node = prove_factory_binding_node_segmented(
            &leg_leaf,
            &backing_leaf,
            &crate::fold_vk_pin::FoldVkPins::tracked(&leg_leaf, &backing_leaf)
                .expect("both fold children carry a preprocessed commitment"),
            &config,
        )
        .expect("an honest factory turn binds in the fold");
        let exposed = read_exposed_segment(&node).expect("the binding node re-exposes the segment");
        assert_eq!(
            exposed, segment,
            "the fold node's re-exposed segment is the leg's chain segment"
        );
    }

    /// THE TOOTH — NEGATIVE POLE (the repair BITES): a FORGED factory turn whose leg claims a
    /// `child_vk` no backing leaf binds (an arbitrary-program forgery, the
    /// `deployed_admits_forged_child_vk` shape) has NO satisfying partner in the fold: the per-lane
    /// `connect` to the backing leaf's bound child_vk is a conflict ⇒ UNSAT ⇒ no root. A pure light
    /// client cannot be fooled into accepting the forged factory cell.
    #[test]
    fn forged_child_vk_makes_aggregate_unsat() {
        let config = ir2_leaf_wrap_config();
        let w = make_witness();
        let pis = w.public_inputs();
        let segment: Vec<BabyBear> = (0..SEG_WIDTH)
            .map(|i| BabyBear::new(7000 + i as u32))
            .collect();

        let backing_leaf = prove_factory_leaf_with_child_vk_claim(&w, &pis, &config)
            .expect("the factory backing leaf folds");
        // The leg claims a child_vk that DISAGREES with the backing leaf's bound child_vk.
        let mut forged = w.child_vk;
        forged[0] += BabyBear::new(1);
        let leg_leaf = factory_leg_leaf(&segment, forged, &config);

        let what = "a FORGED child_vk (no backing leaf binds it) produced an aggregate root";
        let err = must_refuse(what, || {
            prove_factory_binding_node_segmented(
                &leg_leaf,
                &backing_leaf,
                &crate::fold_vk_pin::FoldVkPins::tracked(&leg_leaf, &backing_leaf)
                    .expect("both fold children carry a preprocessed commitment"),
                &config,
            )
        });
        // The per-lane `connect` between the leg's CLAIMED child_vk and the backing leaf's GENUINE
        // one is what must object — not a lane-count guard, not the wrap, not an OOM.
        assert_node_refused_by_binding_connect(what, &err, FACTORY_BINDING_NODE_SEGMENTED_ARM);
    }
}
