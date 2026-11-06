//! Re-prove a hatchery mint's CELL-CONTRACT attestation as a RECURSION-FOLDABLE IR-v2 leaf
//! (the hatchery analog of [`crate::sovereign_leaf_adapter`] / [`crate::custom_leaf_adapter`]),
//! plus the SEGMENT-PRESERVING binding node that welds it to the deployed mint leg's teeth.
//!
//! ## What this closes
//!
//! A hatchery [`MintedKind`](../../../sdk/src/hatchery_mint.rs) is born by a deployed
//! `CreateCellFromFactory`-shaped turn: the executor installs the kind's `state_constraints`
//! (the invariant-as-program) on the child and re-evaluates that program on every later turn
//! (`MintedKind::evaluate_transition` → `CellProgram::evaluate_with_meta`). That cell-BIRTH
//! transition is the deployed effect-vm leg. But the `HpresProof::Attested { contract_hash }`
//! *forever-crown* — the claim that the kind's invariant is backed by a machine-checked
//! `Dregg2.Verify.Contract.CellContract` (a real `step_ob` proof term, holding under EVERY
//! adversarial schedule) — is checked ENTIRELY OFF-VK:
//!
//!   * (a) the CONTRACT BACKING — the published `contract_hash` resolves to a VERIFYING
//!     `CellContract` proof (a real `step_ob`); and
//!   * (b) the INVARIANT BINDING — that proved contract certifies THIS kind's invariant, not a
//!     weaker / different one (`Hatchery.lean::forged_attestation_rejected`, the content-hash
//!     check).
//!
//! In `sdk/src/hatchery_mint.rs` the `contract_hash` is only STORED (`attest_hpres`, field
//! `HpresProof::Attested { contract_hash }`) — read by NO circuit constraint on either rung, and
//! the Lean `attested_enforces_forever` is an EXECUTOR-image carry, not a deployed-VK one. So a
//! PURE LIGHT CLIENT (one that only folds the per-turn recursion tree) witnesses neither (a) nor
//! (b): a mint carrying ANY `contract_hash` produces an attested history identical to one backed
//! by a real `CellContract` proof. The refutation
//! [`metatheory/Dregg2/Circuit/HatcheryBackingAttack.lean`]
//! (`deployed_admits_unbacked_hatchery`) exhibits the fabricated crown the deployed AIR admits.
//!
//! This module mints the attestation tuple `(contract_hash, invariant_digest)` as a
//! recursion-foldable IR-v2 leaf — the same `aggregate_tree` / chain a light client verifies —
//! so the binding node [`prove_hatchery_binding_node_segmented`] can `connect` it to the deployed
//! mint leg's claimed `contract_hash` teeth, exactly as `prove_sovereign_binding_node_segmented`
//! connects the sovereign authority leaf.
//!
//! ## The constraint mapping (the same TOTAL, table-free shape `sovereign_leaf_adapter` uses)
//!
//! The attestation tuple is a fixed-width vector pinned at row 0 and held constant:
//!
//! | family                                                  | maps to                                              |
//! |---------------------------------------------------------|------------------------------------------------------|
//! | boundary: `row0[col c] == pi[c]` (all 16 slots)         | `Base(PiBinding{First, col=c, pi=c})` (EXACT)        |
//! | transition: `next[c] − local[c] == 0` (every column)    | `WindowGate{Nxt(c) − Loc(c), on_transition}` (EXACT) |
//!
//! Both carriers are `main`-table algebra; the descriptor declares NO tables. So a prover cannot
//! put one tuple in row 0 and a different tuple in a padding row, and a tuple slot that disagrees
//! with the bound PI is UNSAT — no foldable leaf is minted.
//!
//! ## The contract-attestation boundary (NAMED honestly)
//!
//! This leaf binds the attestation TUPLE in-circuit. The re-verification that the `contract_hash`
//! actually resolves to a VERIFYING `CellContract` proof term (the full in-AIR `step_ob` recheck —
//! the hatchery analog of full in-AIR Ed25519 for the sovereign owner-sig) stays OFF-AIR: the same
//! digest-of-attestation boundary the membership / G8 / sovereign-key carriers ride. What the fold
//! WITNESSES is: the deployed mint leg's claimed `contract_hash` (the teeth) equals the tuple THIS
//! leaf binds, and the leaf's tuple is internally consistent (contract_hash + invariant_digest both
//! pinned PIs). The residual — anchoring `contract_hash` to a VERIFYING contract proof in-circuit —
//! is the named follow-up (in-AIR `CellContract` re-proof).

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2Air, MemBoundaryWitness, UMemBoundaryWitness,
    ir2_airs_and_common_for_config, prove_vm_descriptor2_for_config,
};
use dregg_circuit::field::BabyBear;

use p3_field::PrimeField32;
use p3_recursion::{
    ProveNextLayerParams, RecursionInput, RecursionOutput, Target,
    build_and_prove_next_layer_with_expose,
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

// ---- Attestation-tuple layout (the leaf's descriptor PI slots) ----
/// The proved-`CellContract` content hash — the deployed `HpresProof::Attested { contract_hash }`
/// teeth, packed as a felt digest (32 bytes → 8 felts, the faithful-commit width).
pub const CONTRACT_HASH_LO: usize = 0;
/// Length of the contract-hash digest (8 felts / ~124-bit, the faithful-commit width).
pub const CONTRACT_HASH_LEN: usize = 8;
/// The kind's invariant digest (`kind_id` / child-VK) — which invariant the crown must certify
/// (the `forged_attestation_rejected` content-hash binding).
pub const INVARIANT_DIGEST_LO: usize = CONTRACT_HASH_LO + CONTRACT_HASH_LEN;
/// Length of the invariant digest (8 felts).
pub const INVARIANT_DIGEST_LEN: usize = 8;
/// Total attestation-tuple width / PI count (8 + 8 = 16).
pub const ATTESTATION_TUPLE_WIDTH: usize = INVARIANT_DIGEST_LO + INVARIANT_DIGEST_LEN;

/// The 8-felt contract-hash claim the leaf re-exposes for the binding node to `connect`.
pub const HATCHERY_CONTRACT_CLAIM_LEN: usize = CONTRACT_HASH_LEN;

/// A hatchery mint's contract-attestation tuple — the SAME `(contract_hash, invariant_digest)` the
/// off-VK executor attestation check certifies (`HpresProof::Attested`'s `contract_hash` resolving
/// to a `CellContract` that certifies the kind's invariant, `Hatchery.lean::Attested`).
#[derive(Clone, Debug)]
pub struct HatcheryAttestationWitness {
    /// `contract_hash` — the content hash of the proved `CellContract` artifact (8-felt digest).
    pub contract_hash: [BabyBear; CONTRACT_HASH_LEN],
    /// The kind's invariant digest (`kind_id` / child-VK) the contract must certify (8-felt).
    pub invariant_digest: [BabyBear; INVARIANT_DIGEST_LEN],
}

impl HatcheryAttestationWitness {
    /// The 16-slot bound attestation tuple carried as the leaf's descriptor PIs.
    pub fn public_inputs(&self) -> Vec<BabyBear> {
        let mut pis = vec![BabyBear::new(0); ATTESTATION_TUPLE_WIDTH];
        pis[CONTRACT_HASH_LO..CONTRACT_HASH_LO + CONTRACT_HASH_LEN]
            .copy_from_slice(&self.contract_hash);
        pis[INVARIANT_DIGEST_LO..INVARIANT_DIGEST_LO + INVARIANT_DIGEST_LEN]
            .copy_from_slice(&self.invariant_digest);
        pis
    }

    /// The base trace: the attestation tuple replicated across two rows (the `WindowGate`
    /// continuity glue pins every column constant, so one typed row padded to a power of two binds
    /// the whole tuple). Width == `ATTESTATION_TUPLE_WIDTH`.
    pub fn generate_trace(&self) -> Vec<Vec<BabyBear>> {
        let row = self.public_inputs();
        vec![row.clone(), row]
    }
}

/// Adapt the contract-attestation tuple into the IR-v2 [`EffectVmDescriptor2`]: 16 boundary pins
/// (`PiBinding{First}`, EXACT — `pi_index == col`) + 16 transition pins (`WindowGate{Nxt(c) −
/// Loc(c)}`, EXACT — every column constant across rows). Authored by Lean `TupleBindingEmit.tupleDesc`;
/// parsing fails closed if the generated artifact is invalid.
pub fn hatchery_attestation_to_descriptor2() -> Result<EffectVmDescriptor2, String> {
    dregg_circuit::descriptor_ir2::parse_vm_descriptor2(include_str!(
        "../../circuit/descriptors/by-name/hatchery-attestation-leaf.json"
    ))
}

/// Prove a hatchery attestation tuple as a RECURSION-FOLDABLE IR-v2 leaf (the bridge pattern).
/// `public_inputs` is the 16-slot bound tuple — for an HONEST proof it equals
/// `witness.public_inputs()`. Passing a DIFFERENT tuple is a forged binding (trace claims one
/// tuple, PIs another): the `PiBinding{First}` requires `row0[col] == pi[col]`, so the mismatch is
/// UNSAT and no foldable leaf is minted.
pub fn prove_hatchery_leaf(
    witness: &HatcheryAttestationWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    if public_inputs.len() != ATTESTATION_TUPLE_WIDTH {
        return Err(format!(
            "hatchery-attestation leaf expects {ATTESTATION_TUPLE_WIDTH} PI slots, got {}",
            public_inputs.len()
        ));
    }
    let desc2 = hatchery_attestation_to_descriptor2()?;
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
    .map_err(|e| format!("hatchery-attestation leaf inner IR-v2 prove failed: {e}"))?;

    prove_descriptor_leaf_rotated_with_config(&desc2, &inner, public_inputs, config)
        .map_err(|e| format!("hatchery-attestation leaf recursion wrap failed: {e}"))
}

/// Prove the hatchery attestation tuple as a foldable leaf AND re-expose its bound 8-felt
/// `contract_hash` (lanes `[CONTRACT_HASH_LO .. CONTRACT_HASH_LO+CONTRACT_HASH_LEN)`) as a public
/// CLAIM the binding node `connect`s to the deployed mint leg's teeth.
///
/// This re-exposes the leaf's OWN FRI-bound descriptor PI lanes directly — the same direct-lane
/// re-expose [`crate::sovereign_leaf_adapter::prove_sovereign_leaf_with_key_claim`] uses for the
/// `key_commit` slice — so the plain backend suffices (no `recompose/coeff` table). The exposed
/// `contract_hash` is welded to the execution: a prover cannot expose a `contract_hash` that
/// disagrees with the tuple the leaf proves, because both are the SAME in-circuit PI targets.
pub fn prove_hatchery_leaf_with_contract_claim(
    witness: &HatcheryAttestationWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    if public_inputs.len() != ATTESTATION_TUPLE_WIDTH {
        return Err(format!(
            "hatchery-attestation leaf expects {ATTESTATION_TUPLE_WIDTH} PI slots, got {}",
            public_inputs.len()
        ));
    }
    let desc2 = hatchery_attestation_to_descriptor2()?;
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
    .map_err(|e| {
        format!("hatchery-attestation contract-claim leaf inner IR-v2 prove failed: {e}")
    })?;

    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(&desc2, &inner, public_inputs, config).map_err(|e| {
            format!("hatchery-attestation contract-claim verify-triple build failed: {e}")
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
            .expect("hatchery-attestation leaf has a main instance carrying the descriptor PIs");
        debug_assert!(
            main.len() >= CONTRACT_HASH_LO + CONTRACT_HASH_LEN,
            "main instance must carry the contract_hash PI slots"
        );
        // Re-expose the FRI-bound contract_hash lanes directly (not free scalars).
        let claim: Vec<Target> = (0..CONTRACT_HASH_LEN)
            .map(|k| main[CONTRACT_HASH_LO + k])
            .collect();
        cb.expose_as_public_output(&claim);
    };

    build_and_prove_next_layer_with_expose::<DreggRecursionConfig, Ir2Air, _, D>(
        &input,
        &recursion_layer_over(config),
        &backend,
        &ProveNextLayerParams::default(),
        Some(&expose),
    )
    .map_err(|e| format!("hatchery-attestation contract-claim leaf-wrap failed: {e:?}"))
}

/// Read the 8-felt `contract_hash` a [`prove_hatchery_leaf_with_contract_claim`] leaf exposes
/// through its `expose_claim` table. Returns `None` if the proof carries no claim.
pub fn read_exposed_contract_hash(
    output: &RecursionOutput<DreggRecursionConfig>,
) -> Option<[BabyBear; HATCHERY_CONTRACT_CLAIM_LEN]> {
    let claims: Vec<BabyBear> = output
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")?
        .public_values
        .iter()
        .map(|&v| BabyBear::new(v.as_canonical_u32()))
        .collect();
    if claims.len() < HATCHERY_CONTRACT_CLAIM_LEN {
        return None;
    }
    let mut out = [BabyBear::new(0); HATCHERY_CONTRACT_CLAIM_LEN];
    out.copy_from_slice(&claims[..HATCHERY_CONTRACT_CLAIM_LEN]);
    Some(out)
}

/// The binding node's failure prefix, single-sourced so the production `format!` and
/// `binding_tooth`'s arm assertion cannot drift apart.
pub const HATCHERY_BINDING_NODE_SEGMENTED_ARM: &str =
    "segmented hatchery-binding aggregation node failed";

/// **THE SEGMENT-PRESERVING HATCHERY BINDING NODE (the hatchery analog of
/// [`crate::joint_turn_recursive::prove_sovereign_binding_node_segmented`]).** Aggregate a hatchery
/// mint's DUAL-EXPOSE effect-vm leg leaf (whose single `expose_claim` carries the chain SEGMENT in
/// lanes `[0 .. SEG_WIDTH)` and the CLAIMED `contract_hash` teeth in lanes
/// `[SEG_SPINE_WIDTH .. SEG_SPINE_WIDTH+HATCHERY_CONTRACT_CLAIM_LEN)`) WITH the re-proved contract-attestation
/// leaf ([`prove_hatchery_leaf_with_contract_claim`], whose `expose_claim` is the in-circuit-bound
/// `contract_hash` in lanes `[0 .. HATCHERY_CONTRACT_CLAIM_LEN)`), and:
///
///   1. `connect`s the leg's claimed `contract_hash` lanes to the attestation leaf's bound
///      `contract_hash` (the binding tooth — a forged hatchery mint whose teeth name a
///      `contract_hash` no attestation leaf binds is a conflict ⇒ UNSAT ⇒ no root), and
///   2. RE-EXPOSES `[the leg's SEGMENT lanes [0 .. SEG_WIDTH) ‖ a folded vk_spine]` as the parent claim.
///
/// The output exposes an ordinary `SEG_SPINE_WIDTH`-lane `[segment ‖ vk_spine]` claim, so it folds into
/// [`crate::ivc_turn_chain::aggregate_tree`] like any other per-turn segment leaf. This is what
/// makes the hatchery forever-crown REAL for a pure light client: the `contract_hash` the deployed
/// leg claims is bound IN the deployed recursion tree the light client folds, to the attestation
/// tuple the hatchery leaf proves, while the chain `[genesis_root, final_root, num_turns,
/// chain_digest]` still reaches the root.
///
/// THE NAMED SEAMS (honest):
///   * **THE BIG-BANG DESCRIPTOR PIECE.** The deployed hatchery mint leg must DUAL-EXPOSE its
///     `contract_hash` teeth (lanes `[SEG_SPINE_WIDTH ..)`). Today the `contract_hash` is only STORED
///     (`hatchery_mint.rs::attest_hpres`), read by no constraint; the teeth-fill on the rotated
///     mint producer + the leg's dual-expose of them is the BIG-BANG PI-EXPOSURE change, owned by
///     the descriptor lane (the same lane the sovereign/custom teeth-fill rides). This node is its
///     consumer.
///   * The node binds `contract_hash` (the attestation digest, leg (a)). Connecting the
///     `invariant_digest` (leg (b), the `kind_id`/child-VK content binding) needs the leg to expose
///     that slot too — the same big-bang piece, widened. The attestation leaf already binds both
///     in-circuit (contract_hash/invariant_digest are pinned PIs), so widening the connect is a
///     lane-count change, not new soundness machinery.
///   * Re-verifying the `contract_hash` resolves to a VERIFYING `CellContract` proof term (the
///     in-AIR `step_ob` recheck) stays OFF-AIR — the digest-of-attestation boundary (see the module
///     docs).
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`]. Both children re-expose
/// FRI-bound PI lanes directly (no `recompose/coeff` table), so the plain backend suffices.
pub fn prove_hatchery_binding_node_segmented(
    dual_expose_leg_leaf: &RecursionOutput<DreggRecursionConfig>,
    hatchery_attestation_leaf: &RecursionOutput<DreggRecursionConfig>,
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
    use p3_recursion::{BatchOnly, build_and_prove_aggregation_layer_with_expose};

    let ev_idx = expose_claim_instance_index(&dual_expose_leg_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "dual-expose hatchery leg leaf carries no expose_claim table — it must be \
                     wrapped to expose segment ++ contract_hash (the Attested teeth)"
                .to_string(),
        }
    })?;
    let ha_idx = expose_claim_instance_index(&hatchery_attestation_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "hatchery-attestation leaf carries no exposed contract_hash (expose_claim) \
                     table — it must be minted via prove_hatchery_leaf_with_contract_claim"
                .to_string(),
        }
    })?;

    let left = dual_expose_leg_leaf.into_recursion_input_pinned::<BatchOnly>(pins.left.clone());
    let right =
        hatchery_attestation_leaf.into_recursion_input_pinned::<BatchOnly>(pins.right.clone());

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>],
                       left_vk_cap: &[Target],
                       right_vk_cap: &[Target]| {
        let ev = left_apt
            .get(ev_idx)
            .expect("dual-expose hatchery leg's claim instance present");
        let ha = right_apt
            .get(ha_idx)
            .expect("hatchery-attestation leaf's exposed contract_hash instance present");
        debug_assert!(
            ev.len() >= SEG_SPINE_WIDTH + HATCHERY_CONTRACT_CLAIM_LEN
                && ha.len() >= HATCHERY_CONTRACT_CLAIM_LEN,
            "dual-expose claim must carry segment ++ contract_hash; attestation leaf carries \
             contract_hash"
        );
        // THE BINDING TOOTH, IN-CIRCUIT: the leg's CLAIMED contract_hash (lanes
        // [SEG_SPINE_WIDTH .. SEG_SPINE_WIDTH+CLAIM_LEN)) must equal the attestation leaf's BOUND contract_hash,
        // lane by lane. A hatchery mint whose teeth name a contract_hash no attestation leaf binds
        // is a conflict here ⇒ UNSAT ⇒ no root.
        for k in 0..HATCHERY_CONTRACT_CLAIM_LEN {
            cb.connect(ev[SEG_SPINE_WIDTH + k], ha[k]);
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
        reason: format!("{HATCHERY_BINDING_NODE_SEGMENTED_ARM}: {e:?}"),
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
    use dregg_circuit::field::BABYBEAR_P;
    use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};
    use dregg_circuit::refusal::{assert_violated_constraint_not_bus, must_refuse};
    use p3_field::PrimeField32;

    fn make_witness() -> HatcheryAttestationWitness {
        HatcheryAttestationWitness {
            contract_hash: core::array::from_fn(|i| BabyBear::new(100 + i as u32)),
            invariant_digest: core::array::from_fn(|i| BabyBear::new(200 + i as u32)),
        }
    }

    #[test]
    fn hatchery_attestation_maps_to_descriptor2() {
        let desc2 = hatchery_attestation_to_descriptor2().expect("hatchery maps");
        assert_eq!(desc2.trace_width, ATTESTATION_TUPLE_WIDTH);
        assert_eq!(desc2.public_input_count, ATTESTATION_TUPLE_WIDTH);
        assert!(desc2.tables.is_empty());
        assert!(desc2.hash_sites.is_empty());
        assert!(desc2.ranges.is_empty());
        assert_eq!(desc2.constraints.len(), 2 * ATTESTATION_TUPLE_WIDTH);
        let pi_bindings = desc2
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
            .count();
        assert_eq!(pi_bindings, ATTESTATION_TUPLE_WIDTH);
    }

    /// THE POSITIVE POLE: an honest attestation tuple proves as a foldable recursion leaf.
    #[test]
    fn honest_hatchery_attestation_proves_as_foldable_leaf() {
        let w = make_witness();
        let pis = w.public_inputs();
        assert_eq!(pis.len(), ATTESTATION_TUPLE_WIDTH);
        let config = ir2_leaf_wrap_config();
        let _output = prove_hatchery_leaf(&w, &pis, &config)
            .expect("the honest hatchery attestation must prove as a foldable leaf");
    }

    /// THE POSITIVE POLE (claim variant): the contract-claim leaf folds AND re-exposes the bound
    /// 8-felt contract_hash.
    #[test]
    fn honest_claim_leaf_exposes_bound_contract_hash() {
        let w = make_witness();
        let pis = w.public_inputs();
        let config = ir2_leaf_wrap_config();
        let output = prove_hatchery_leaf_with_contract_claim(&w, &pis, &config)
            .expect("the contract-claim leaf must fold");
        let exposed =
            read_exposed_contract_hash(&output).expect("a contract_hash claim is exposed");
        assert_eq!(
            exposed, w.contract_hash,
            "the exposed contract_hash is the bound tuple's"
        );
    }

    /// THE NEGATIVE POLE (leaf-level): a FORGED tuple (trace carries one contract_hash, the bound
    /// PIs claim a TAMPERED one) has no satisfying assembly — `PiBinding{First}` requires
    /// `row0[col] == pi[col]`, so the mismatch is UNSAT. No foldable leaf is minted.
    #[test]
    fn forged_attestation_tuple_does_not_fold() {
        let w = make_witness();
        let mut tampered = w.clone();
        tampered.contract_hash[0] += BabyBear::new(1);
        tampered.invariant_digest[0] += BabyBear::new(1);
        let forged_pis = tampered.public_inputs();
        assert_ne!(forged_pis, w.public_inputs());
        let config = ir2_leaf_wrap_config();

        let what = "a FORGED hatchery attestation tuple";
        let err = must_refuse(what, || prove_hatchery_leaf(&w, &forged_pis, &config));
        // The claim is `PiBinding{First}` UNSAT — a violated CONSTRAINT in whichever profile.
        report_refusal(what, &err);
        assert_violated_constraint_not_bus(what, &err);
    }

    /// Build a minimal effect-vm leg leaf that PUBLISHES `segment ++ vk_spine ++ contract_hash` in
    /// IR2 PIs `[0 .. SEG_SPINE_WIDTH+CLAIM_LEN)` (PiBinding pins) and DUAL-EXPOSES that whole
    /// slice — a stand-in for the deployed mint leg at the SAME exposure surface the BIG-BANG
    /// descriptor piece will produce. The segment lanes are arbitrary (the fold tooth checks the
    /// contract_hash bind, not a real chain); the SPINE block is the honest
    /// [`leaf_vk_spine_host`] value, so this row mirrors what
    /// `prove_descriptor_leaf_dual_expose_at` mints rather than merely matching its width.
    fn hatchery_leg_leaf(
        segment: &[BabyBear],
        contract_hash: [BabyBear; HATCHERY_CONTRACT_CLAIM_LEN],
        config: &DreggRecursionConfig,
    ) -> RecursionOutput<DreggRecursionConfig> {
        let width = SEG_SPINE_WIDTH + HATCHERY_CONTRACT_CLAIM_LEN;
        assert_eq!(segment.len(), SEG_WIDTH);
        let constraints: Vec<VmConstraint2> = (0..width)
            .map(|k| {
                VmConstraint2::Base(VmConstraint::PiBinding {
                    row: VmRow::First,
                    col: k,
                    pi_index: k,
                })
            })
            .collect();
        let desc = EffectVmDescriptor2 {
            name: "hatchery-mint-leg-standin::seg++contract_hash".to_string(),
            trace_width: width,
            public_input_count: width,
            challenges: 0,
            tables: vec![],
            constraints,
            hash_sites: vec![],
            ranges: vec![],
        };
        let mut pis = vec![BabyBear::new(0); width];
        pis[..SEG_WIDTH].copy_from_slice(segment);
        pis[SEG_VK_SPINE_FIRST..SEG_SPINE_WIDTH].copy_from_slice(&leaf_vk_spine_host());
        pis[SEG_SPINE_WIDTH..].copy_from_slice(&contract_hash);
        let trace: Vec<Vec<BabyBear>> = vec![pis.clone(), pis.clone()];
        let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
            &desc,
            &trace,
            &pis,
            &MemBoundaryWitness::default(),
            &[],
            &UMemBoundaryWitness::default(),
            config,
        )
        .expect("hatchery leg stand-in proves (the claim is internally consistent)");
        prove_descriptor_leaf_with_pi_slice_expose(&desc, &inner, &pis, config, 0, width)
            .expect("hatchery leg leaf re-exposes segment ++ contract_hash")
    }

    /// THE TOOTH (positive pole): an HONEST hatchery mint — the leg's claimed contract_hash EQUALS
    /// the genuine contract_hash the attestation leaf binds — folds in the node, and the node
    /// re-exposes the SEGMENT (so the chain still reaches the root for a pure light client).
    #[test]
    fn honest_hatchery_mint_folds_and_lc_accepts() {
        let config = ir2_leaf_wrap_config();
        let w = make_witness();
        let pis = w.public_inputs();
        let segment: Vec<BabyBear> = (0..SEG_WIDTH)
            .map(|i| BabyBear::new(7 * i as u32 + 1))
            .collect();

        let attestation_leaf = prove_hatchery_leaf_with_contract_claim(&w, &pis, &config)
            .expect("the attestation leaf folds");
        let leg_leaf = hatchery_leg_leaf(&segment, w.contract_hash, &config); // claims the REAL hash

        let node = prove_hatchery_binding_node_segmented(
            &leg_leaf,
            &attestation_leaf,
            &crate::fold_vk_pin::FoldVkPins::tracked(&leg_leaf, &attestation_leaf)
                .expect("both fold children carry a preprocessed commitment"),
            &config,
        )
        .expect("an honest hatchery mint binds in the fold");
        // The node re-exposes `[segment ‖ vk_spine]` (the chain claim a light client folds onward,
        // plus the spine block `exposed_board_window` requires of every fold child).
        let exposed: Vec<BabyBear> = node
            .0
            .non_primitives
            .iter()
            .find(|e| e.op_type.as_str() == "expose_claim")
            .expect("the binding node re-exposes the segment")
            .public_values
            .iter()
            .map(|&v| BabyBear::new(v.as_canonical_u32()))
            .collect();
        assert_eq!(
            exposed.len(),
            SEG_SPINE_WIDTH,
            "the node re-exposes a segment AND a VK spine"
        );
        assert_eq!(
            exposed[..SEG_WIDTH],
            segment[..],
            "the re-exposed segment is the leg's bound segment"
        );
    }

    /// THE TOOTH (negative pole, the repair BITES): a FORGED hatchery mint — the leg claims a
    /// `contract_hash` NO attestation leaf binds (the fabricated forever-crown of
    /// `HatcheryBackingAttack.deployed_admits_unbacked_hatchery`) — has NO satisfying partner in the
    /// fold: the per-lane `connect` to the attestation leaf's bound contract_hash is a conflict, so
    /// the aggregate is UNSAT and no root exists. A pure light client folding this tree sees no root
    /// for the unbacked crown.
    #[test]
    fn forged_contract_hash_is_rejected_by_the_fold() {
        let config = ir2_leaf_wrap_config();
        let w = make_witness();
        let pis = w.public_inputs();
        let segment: Vec<BabyBear> = (0..SEG_WIDTH)
            .map(|i| BabyBear::new(7 * i as u32 + 1))
            .collect();

        // A contract_hash NO verifying attestation backs (lane 0 perturbed by +1 mod p).
        let mut forged = w.contract_hash;
        forged[0] = BabyBear::new((forged[0].0 + 1) % BABYBEAR_P);
        assert_ne!(forged, w.contract_hash);

        let attestation_leaf = prove_hatchery_leaf_with_contract_claim(&w, &pis, &config)
            .expect("the attestation leaf folds (it binds the REAL contract_hash)");
        let leg_leaf = hatchery_leg_leaf(&segment, forged, &config); // claims the FORGED hash

        let what = "a FORGED contract_hash (no backing attestation) produced a fold root";
        let err = must_refuse(what, || {
            prove_hatchery_binding_node_segmented(
                &leg_leaf,
                &attestation_leaf,
                &crate::fold_vk_pin::FoldVkPins::tracked(&leg_leaf, &attestation_leaf)
                    .expect("both fold children carry a preprocessed commitment"),
                &config,
            )
        });
        assert_node_refused_by_binding_connect(what, &err, HATCHERY_BINDING_NODE_SEGMENTED_ARM);
    }
}
