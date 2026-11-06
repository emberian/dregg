//! Re-prove a `SenderAuthorized` turn's set-MEMBERSHIP tuple as a RECURSION-FOLDABLE
//! IR-v2 leaf (the membership analog of [`crate::sovereign_leaf_adapter`]).
//!
//! ## What this closes
//!
//! Today a `StateConstraint::SenderAuthorized { AuthorizedSet::PublicRoot { .. } }`
//! turn's set-membership is checked ENTIRELY OFF-AIR by a re-executing validator: the
//! [`turn::executor::membership_verifier::MerkleMembershipStarkVerifier`] runs a
//! STANDALONE `dregg_circuit::dsl::membership` Poseidon2 Merkle STARK whose
//! `[leaf0..8, root0..8]` public inputs the executor pins (`membership_verifier.rs:143..158`,
//! `leaf = compress(sender_pk)`, `verify_membership_dsl(&proof, leaf, root)`).
//!
//! A PURE LIGHT CLIENT (one that only folds the per-turn recursion tree) never
//! witnesses that membership. In the deployed effect-vm AIR there is NO
//! set-membership leg — the column the effect-vm calls "membership" is the UNRELATED
//! `cap_root` (the capability-set commitment, `circuit/src/cap_root.rs`), NOT this
//! `SenderAuthorized` set. No effect-vm row publishes `(sender_leaf, authorized_root)`
//! as PIs, and no constraint links any column to a verifying Merkle path against the
//! cell's authorized-set root. So a `SenderAuthorized`-gated turn yields an
//! `AttestedHistory` BYTE-IDENTICAL to a fail-closed-default validator's: the
//! membership is RE-EXEC-ONLY. The refutation
//! [`metatheory/Dregg2/Circuit/MembershipBackingAttack.lean`]
//! (`deployed_admits_unbacked_membership`) exhibits the forged `SenderAuthorized` turn
//! the deployed AIR admits.
//!
//! This module mints the membership tuple `(sender_leaf, authorized_root)` as a
//! recursion-foldable IR-v2 leaf — the same `aggregate_tree` / chain a light client
//! verifies — so the binding node [`prove_membership_binding_node_segmented`] can
//! `connect` it to the deployed leg's published membership teeth PIs, exactly as
//! [`crate::joint_turn_recursive::prove_sovereign_binding_node_segmented`] connects the
//! sovereign authority leaf.
//!
//! ## Why the tuple-binding shape (NOT a re-proved Merkle-path STARK)
//!
//! The membership relation's load-bearing constraint is
//! [`dregg_circuit::dsl::circuit::ConstraintExpr::MerkleHash`]
//! (`circuit/src/dsl/descriptors.rs::merkle_poseidon2_descriptor` C2, the Poseidon2
//! `hash_4_to_1` parent binding). That is exactly the Poseidon2 relation
//! [`crate::custom_leaf_adapter::cellprogram_to_descriptor2`] REFUSES: the faithful
//! IR-v2 carrier routes the permutation through a chip-table lookup (`TID_P2`) that
//! requires witnessing all eight permutation lanes per site in the trace. The
//! cap-membership crown ([`dregg_circuit::dsl::cap_membership`]) does NOT help here —
//! it is itself a standalone `prove_dsl_p3` STARK whose Poseidon2 path uses
//! `Hash3Cap`, pinned OFF-AIR by `dregg_sdk::verify_full_turn_bound`, NOT a foldable
//! recursion leaf — so there is no in-circuit Merkle-opening machinery to reuse.
//!
//! So this leaf mirrors the sovereign/bridge pattern EXACTLY: it binds the membership
//! TUPLE in-circuit (the same TOTAL, table-free `PiBinding{First}` + `WindowGate` shape)
//! and re-exposes `(sender_leaf, authorized_root)` as the claim the binding node
//! `connect`s. The in-AIR Poseidon2 Merkle-path verification (that the path actually
//! hashes `sender_leaf` → `authorized_root`) is the NAMED big-bang piece — the same
//! `MerkleHash` chip-table (`TID_P2`) lookup the custom adapter names (full in-AIR
//! Poseidon2 path is the named cost, not done here). What the fold WITNESSES is: the
//! deployed leg's claimed `(sender_leaf, authorized_root)` equals the tuple THIS leaf
//! binds, and the leaf's tuple is internally consistent (both PIs pinned). The residual
//! — anchoring the tuple to a VERIFYING Merkle path in-circuit — is the named follow-up.
//!
//! ## The constraint mapping (the same TOTAL, table-free shape `sovereign_leaf_adapter` uses)
//!
//! The membership tuple is a fixed-width vector pinned at row 0 and held constant:
//!
//! | family                                                  | maps to                                              |
//! |---------------------------------------------------------|------------------------------------------------------|
//! | boundary: `row0[col c] == pi[c]` (both slots)           | `Base(PiBinding{First, col=c, pi=c})` (EXACT)        |
//! | transition: `next[c] − local[c] == 0` (every column)    | `WindowGate{Nxt(c) − Loc(c), on_transition}` (EXACT) |
//!
//! Both carriers are `main`-table algebra; the descriptor declares NO tables. So a
//! prover cannot put one tuple in row 0 and a different tuple in a padding row, and a
//! tuple slot that disagrees with the bound PI is UNSAT — no foldable leaf is minted.
//!
//! ## THE NAMED BIG-BANG PIECE (the deployed-descriptor membership-leg PI exposure)
//!
//! [`prove_membership_binding_node_segmented`] consumes a DUAL-EXPOSE leg leaf whose
//! `expose_claim` carries the chain SEGMENT in lanes `[0 .. SEG_WIDTH)` AND the claimed
//! `(sender_leaf, authorized_root)` in lanes `[SEG_SPINE_WIDTH .. SEG_SPINE_WIDTH+MEMBERSHIP_CLAIM_LEN)`.
//! Today the deployed effect-vm leg publishes NEITHER — its "membership" column is the
//! unrelated `cap_root`, and no row publishes `(sender_leaf, authorized_root)` as PIs at
//! fixed slots. **Adding that PI exposure to the deployed `SenderAuthorized` leg
//! descriptor (the leg publishing `sender_leaf` + `authorized_root` at fixed PI slots,
//! the membership twin of `prove_descriptor_leaf_dual_expose`) is the BIG-BANG
//! DESCRIPTOR PIECE — a PI-exposure change that moves the VK, owned by the descriptor
//! lane.** This node + its mechanism (and the leaf below) are READY for it; the
//! `membership_binding_mechanism` tooth proves the fold MECHANISM bites today.

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

// ---- Membership-tuple layout (the leaf's descriptor PI slots) ----
/// The `sender_leaf` slot — one felt of `compress(sender_pk)`, and the deployed leg's published
/// sender-leaf tooth. (`membership_verifier.rs:143`.)
pub const SENDER_LEAF_SLOT: usize = 0;
/// The `authorized_root` slot — one felt of the cell's `AuthorizedSet::PublicRoot`, and the
/// deployed leg's published authorized-root tooth.
pub const AUTHORIZED_ROOT_SLOT: usize = SENDER_LEAF_SLOT + 1;
/// Total membership-tuple width / PI count (1 + 1 = 2).
///
/// ⚑ **THIS IS TWO FELTS AND THE MEMBERSHIP STARK IS NOW SIXTEEN.** Until the `node8` cutover
/// this width was justified as "matching the `dregg_circuit::dsl::membership` STARK's
/// `[leaf, root]` public-input layout"; that layout is now `[leaf0..8, root0..8]`
/// (`MEMBERSHIP_4ARY_PI_COUNT = 16`), so the tuple this leaf binds carries ~31 bits of a leaf
/// and ~31 bits of a root that the STARK itself commits at full 8-felt width.
///
/// It is NOT widened here, and the reason is not taste: this width is fixed by the DEPLOYED
/// effect-vm leg's PI exposure, not by the membership family. The fold arm reads the leg's
/// claimed tuple at [`crate::ivc_turn_chain::MEMBERSHIP_CLAIM_PI_LO`] = 50 for
/// `MEMBERSHIP_CLAIM_LEN` slots; widening to 16 would run 50..66 straight through the wide
/// anchors at 52..67 on `transferV3MembershipWide`. Widening it is a Lean descriptor regen
/// (`CarrierComposed`/`EffectVmEmitRotationV3`) plus the `carrier_claim_pins_admitted` geometry
/// — and note the standing measurement recorded at that constant: the teeth pins at 50/51 do
/// not exist on the emitted bytes today, so this arm is fail-closed on every deployed leg.
pub const MEMBERSHIP_TUPLE_WIDTH: usize = AUTHORIZED_ROOT_SLOT + 1;

/// The 2-felt `(sender_leaf, authorized_root)` claim the leaf re-exposes for the
/// binding node to `connect`.
pub const MEMBERSHIP_CLAIM_LEN: usize = MEMBERSHIP_TUPLE_WIDTH;

/// A `SenderAuthorized` turn's membership tuple.
///
/// ⚑ ONE FELT EACH — see [`MEMBERSHIP_TUPLE_WIDTH`]. The off-AIR
/// `membership_verifier.rs` `MerkleMembershipStarkVerifier` now pins an 8-felt leaf and an
/// 8-felt root; this fold-side tuple is the deployed leg's 2-slot teeth exposure and is widened
/// by the descriptor regen, not here.
#[derive(Clone, Copy, Debug)]
pub struct SenderMembershipWitness {
    /// One felt of `compress(sender_pk)` — the sender leaf a verifying Merkle path proves.
    pub sender_leaf: BabyBear,
    /// One felt of the cell's `AuthorizedSet::PublicRoot` — the root the path reaches.
    pub authorized_root: BabyBear,
}

impl SenderMembershipWitness {
    /// The 2-slot bound membership tuple carried as the leaf's descriptor PIs.
    pub fn public_inputs(&self) -> Vec<BabyBear> {
        let mut pis = vec![BabyBear::new(0); MEMBERSHIP_TUPLE_WIDTH];
        pis[SENDER_LEAF_SLOT] = self.sender_leaf;
        pis[AUTHORIZED_ROOT_SLOT] = self.authorized_root;
        pis
    }

    /// The base trace: the membership tuple replicated across two rows (the
    /// `WindowGate` continuity glue pins every column constant, so one typed row
    /// padded to a power of two binds the whole tuple). Width == `MEMBERSHIP_TUPLE_WIDTH`.
    pub fn generate_trace(&self) -> Vec<Vec<BabyBear>> {
        let row = self.public_inputs();
        vec![row.clone(), row]
    }
}

/// Adapt the membership tuple into the IR-v2 [`EffectVmDescriptor2`]: 2 boundary pins
/// (`PiBinding{First}`, EXACT — `pi_index == col`) + 2 transition pins
/// (`WindowGate{Nxt(c) − Loc(c)}`, EXACT — every column constant across rows). Authored by Lean `TupleBindingEmit.tupleDesc`; parsing
/// fails closed if the generated artifact is invalid.
pub fn membership_tuple_to_descriptor2() -> Result<EffectVmDescriptor2, String> {
    dregg_circuit::descriptor_ir2::parse_vm_descriptor2(include_str!(
        "../../circuit/descriptors/by-name/membership-leaf.json"
    ))
}

/// Prove a membership tuple as a RECURSION-FOLDABLE IR-v2 leaf (the sovereign pattern).
/// `public_inputs` is the 2-slot bound tuple — for an HONEST proof it equals
/// `witness.public_inputs()`. Passing a DIFFERENT tuple is a forged binding (trace
/// claims one tuple, PIs another): the `PiBinding{First}` requires `row0[col] == pi[col]`,
/// so the mismatch is UNSAT and no foldable leaf is minted.
pub fn prove_membership_leaf(
    witness: &SenderMembershipWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    if public_inputs.len() != MEMBERSHIP_TUPLE_WIDTH {
        return Err(format!(
            "membership leaf expects {MEMBERSHIP_TUPLE_WIDTH} PI slots, got {}",
            public_inputs.len()
        ));
    }
    let desc2 = membership_tuple_to_descriptor2()?;
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
    .map_err(|e| format!("membership leaf inner IR-v2 prove failed: {e}"))?;

    prove_descriptor_leaf_rotated_with_config(&desc2, &inner, public_inputs, config)
        .map_err(|e| format!("membership leaf recursion wrap failed: {e}"))
}

/// Prove the membership tuple as a foldable leaf AND re-expose its bound 2-felt
/// `(sender_leaf, authorized_root)` (lanes `[0 .. MEMBERSHIP_CLAIM_LEN)`) as a public
/// CLAIM the binding node `connect`s to the deployed leg's claimed membership teeth.
///
/// This re-exposes the leaf's OWN FRI-bound descriptor PI lanes directly (the same
/// direct-lane re-expose [`crate::sovereign_leaf_adapter::prove_sovereign_leaf_with_key_claim`]
/// uses), so the plain backend suffices (no `recompose/coeff` table). The exposed tuple
/// is welded to the execution: a prover cannot expose a tuple that disagrees with the
/// tuple the leaf proves, because both are the SAME in-circuit PI targets.
pub fn prove_membership_leaf_with_claim(
    witness: &SenderMembershipWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    if public_inputs.len() != MEMBERSHIP_TUPLE_WIDTH {
        return Err(format!(
            "membership claim leaf expects {MEMBERSHIP_TUPLE_WIDTH} PI slots, got {}",
            public_inputs.len()
        ));
    }
    let desc2 = membership_tuple_to_descriptor2()?;
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
    .map_err(|e| format!("membership claim leaf inner IR-v2 prove failed: {e}"))?;

    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(&desc2, &inner, public_inputs, config)
            .map_err(|e| format!("membership claim verify-triple build failed: {e}"))?;

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
            .expect("membership leaf has a main instance carrying the descriptor PIs");
        debug_assert!(
            main.len() >= MEMBERSHIP_CLAIM_LEN,
            "main instance must carry the membership tuple PI slots"
        );
        // Re-expose the FRI-bound (sender_leaf, authorized_root) lanes directly.
        let claim: Vec<Target> = (0..MEMBERSHIP_CLAIM_LEN).map(|k| main[k]).collect();
        cb.expose_as_public_output(&claim);
    };

    build_and_prove_next_layer_with_expose::<DreggRecursionConfig, Ir2Air, _, D>(
        &input,
        &recursion_layer_over(config),
        &backend,
        &ProveNextLayerParams::default(),
        Some(&expose),
    )
    .map_err(|e| format!("membership claim leaf-wrap failed: {e:?}"))
}

/// Read the 2-felt `(sender_leaf, authorized_root)` a [`prove_membership_leaf_with_claim`]
/// leaf exposes through its `expose_claim` table. Returns `None` if the proof carries no claim.
pub fn read_exposed_membership(
    output: &RecursionOutput<DreggRecursionConfig>,
) -> Option<[BabyBear; MEMBERSHIP_CLAIM_LEN]> {
    let claims: Vec<BabyBear> = output
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")?
        .public_values
        .iter()
        .map(|&v| BabyBear::new(v.as_canonical_u32()))
        .collect();
    if claims.len() < MEMBERSHIP_CLAIM_LEN {
        return None;
    }
    Some([claims[SENDER_LEAF_SLOT], claims[AUTHORIZED_ROOT_SLOT]])
}

// ============================================================================
// THE MEMBERSHIP-BINDING FOLD NODES.
// ============================================================================

/// The two membership binding nodes' failure prefixes, single-sourced so the production
/// `format!` and `binding_tooth`'s arm assertion cannot drift apart. ⚠ the first is a SUBSTRING
/// of the second, so a `contains` on it does not discriminate the two nodes.
pub const MEMBERSHIP_BINDING_NODE_ARM: &str = "membership-binding aggregation node failed";

/// The segment-preserving node's prefix.
pub const MEMBERSHIP_BINDING_NODE_SEGMENTED_ARM: &str =
    "segmented membership-binding aggregation node failed";

/// **THE MEMBERSHIP-BINDING MECHANISM NODE (the minimal fold tooth — no segment).**
/// Aggregate a `SenderAuthorized` leg leaf (which must RE-EXPOSE its CLAIMED 2-slot
/// `(sender_leaf, authorized_root)` as an `expose_claim`, via
/// [`crate::ivc_turn_chain::prove_descriptor_leaf_with_pi_slice_expose`]) WITH the
/// membership leaf ([`prove_membership_leaf_with_claim`]), CONNECTING the two 2-felt
/// tuples in-circuit and re-exposing the now-bound tuple as the parent claim.
///
/// THE TOOTH: if the leg claims a tuple the membership leaf does not bind, the per-lane
/// `connect` is a conflict and the aggregation is UNSAT — no root. This is the
/// term-for-term membership twin of
/// [`crate::note_spend_leaf_adapter::prove_note_spend_binding_node`].
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_membership_binding_node(
    leg_tuple_leaf: &RecursionOutput<DreggRecursionConfig>,
    membership_leaf: &RecursionOutput<DreggRecursionConfig>,
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
            reason: "membership leg leaf carries no re-exposed tuple (expose_claim) table — it must \
                     be wrapped via prove_descriptor_leaf_with_pi_slice_expose (the (leaf, root) tuple)"
                .to_string(),
        }
    })?;
    let ms_idx = expose_claim_instance_index(&membership_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "membership leaf carries no exposed tuple (expose_claim) table — it must be \
                     minted via prove_membership_leaf_with_claim"
                .to_string(),
        }
    })?;

    let left = leg_tuple_leaf.into_recursion_input_pinned::<BatchOnly>(pins.left.clone());
    let right = membership_leaf.into_recursion_input_pinned::<BatchOnly>(pins.right.clone());

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>],
                       _left_vk_cap: &[Target],
                       _right_vk_cap: &[Target]| {
        let lg = left_apt
            .get(leg_idx)
            .expect("membership leg's re-exposed tuple instance present");
        let ms = right_apt
            .get(ms_idx)
            .expect("membership leaf's exposed tuple instance present");
        debug_assert!(lg.len() >= MEMBERSHIP_CLAIM_LEN && ms.len() >= MEMBERSHIP_CLAIM_LEN);
        // THE BINDING TOOTH, IN-CIRCUIT: the leg's CLAIMED (sender_leaf, authorized_root)
        // must equal the membership leaf's BOUND tuple, lane by lane. A forged claim no
        // membership leaf backs is a conflict here ⇒ UNSAT ⇒ no root.
        for k in 0..MEMBERSHIP_CLAIM_LEN {
            cb.connect(lg[k], ms[k]);
        }
        let bound: Vec<Target> = (0..MEMBERSHIP_CLAIM_LEN).map(|k| lg[k]).collect();
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
        reason: format!("{MEMBERSHIP_BINDING_NODE_ARM}: {e:?}"),
    })
}

/// **THE SEGMENT-PRESERVING MEMBERSHIP BINDING NODE (deployed membership-binding,
/// caller-ready — the analog of
/// [`crate::joint_turn_recursive::prove_sovereign_binding_node_segmented`]).** Aggregate
/// a `SenderAuthorized` turn's DUAL-EXPOSE effect-vm leg leaf (whose single
/// `expose_claim` carries the chain SEGMENT in lanes `[0 .. SEG_WIDTH)` and the CLAIMED
/// `(sender_leaf, authorized_root)` in lanes `[SEG_SPINE_WIDTH .. SEG_SPINE_WIDTH+MEMBERSHIP_CLAIM_LEN)`)
/// WITH the re-proved membership leaf ([`prove_membership_leaf_with_claim`], whose
/// `expose_claim` is the in-circuit-bound tuple in lanes `[0 .. MEMBERSHIP_CLAIM_LEN)`),
/// and:
///
///   1. `connect`s the leg's claimed tuple lanes to the membership leaf's bound tuple
///      (the binding tooth — a forged `SenderAuthorized` turn whose teeth name a
///      `(sender_leaf, authorized_root)` no membership leaf binds is a conflict ⇒ UNSAT
///      ⇒ no root), and
///   2. RE-EXPOSES `[the leg's SEGMENT lanes [0 .. SEG_WIDTH) ‖ a folded vk_spine]` as the parent claim.
///
/// The output exposes an ordinary `SEG_SPINE_WIDTH`-lane `[segment ‖ vk_spine]` claim, so it folds into
/// [`crate::ivc_turn_chain::aggregate_tree`] like any other per-turn segment leaf — making
/// the set-membership REAL for a pure light client while preserving the chain
/// endpoints/digest.
///
/// THE NAMED SEAMS (honest):
///   * The deployed `SenderAuthorized` leg must DUAL-EXPOSE its `(sender_leaf,
///     authorized_root)` teeth (lanes `[SEG_SPINE_WIDTH ..)`). Today the effect-vm "membership"
///     column is the unrelated `cap_root`; no row publishes these as PIs. The leg's
///     dual-expose of them is the BIG-BANG DESCRIPTOR PIECE (a PI-exposure change, owned
///     by the descriptor lane). This node is its consumer.
///   * The in-AIR Poseidon2 Merkle-path verification (that the path actually hashes
///     `sender_leaf` → `authorized_root`) stays OFF-AIR — the `MerkleHash` chip-table
///     (`TID_P2`) lookup (see this module's docs). The leaf binds the tuple in-circuit;
///     anchoring it to a verifying path is the named follow-up.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`]. Both children
/// re-expose FRI-bound PI lanes directly (no `recompose/coeff` table), so the plain
/// backend suffices.
pub fn prove_membership_binding_node_segmented(
    dual_expose_leg_leaf: &RecursionOutput<DreggRecursionConfig>,
    membership_leaf: &RecursionOutput<DreggRecursionConfig>,
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
            reason: "dual-expose membership leg leaf carries no expose_claim table — it must be \
                     wrapped to expose (segment ++ (sender_leaf, authorized_root))"
                .to_string(),
        }
    })?;
    let ms_idx = expose_claim_instance_index(&membership_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "membership leaf carries no exposed tuple (expose_claim) table — it must be \
                     minted via prove_membership_leaf_with_claim"
                .to_string(),
        }
    })?;

    let left = dual_expose_leg_leaf.into_recursion_input_pinned::<BatchOnly>(pins.left.clone());
    let right = membership_leaf.into_recursion_input_pinned::<BatchOnly>(pins.right.clone());

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>],
                       left_vk_cap: &[Target],
                       right_vk_cap: &[Target]| {
        let ev = left_apt
            .get(ev_idx)
            .expect("dual-expose membership leg's claim instance present");
        let ms = right_apt
            .get(ms_idx)
            .expect("membership leaf's exposed tuple instance present");
        debug_assert!(
            ev.len() >= SEG_SPINE_WIDTH + MEMBERSHIP_CLAIM_LEN && ms.len() >= MEMBERSHIP_CLAIM_LEN,
            "dual-expose claim must carry segment ++ tuple; membership leaf carries the tuple"
        );
        // THE BINDING TOOTH, IN-CIRCUIT: the leg's CLAIMED tuple (lanes
        // [SEG_SPINE_WIDTH .. SEG_SPINE_WIDTH+MEMBERSHIP_CLAIM_LEN)) must equal the membership leaf's
        // BOUND tuple, lane by lane. A turn whose teeth name a (sender_leaf, authorized_root)
        // no membership leaf binds is a conflict here ⇒ UNSAT ⇒ no root.
        for k in 0..MEMBERSHIP_CLAIM_LEN {
            cb.connect(ev[SEG_SPINE_WIDTH + k], ms[k]);
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
        reason: format!("{MEMBERSHIP_BINDING_NODE_SEGMENTED_ARM}: {e:?}"),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binding_tooth::report_refusal;
    use crate::ivc_turn_chain::ir2_leaf_wrap_config;
    use dregg_circuit::descriptor_ir2::VmConstraint2;
    use dregg_circuit::lean_descriptor_air::VmConstraint;
    use dregg_circuit::refusal::{assert_violated_constraint_not_bus, must_refuse};

    fn make_witness() -> SenderMembershipWitness {
        SenderMembershipWitness {
            sender_leaf: BabyBear::new(42424242),
            authorized_root: BabyBear::new(7777777),
        }
    }

    /// The mapping is total over the membership tuple and produces a table-free,
    /// four-constraint main-only descriptor (2 PiBinding{First} + 2 WindowGate).
    #[test]
    fn membership_maps_to_descriptor2() {
        let desc2 = membership_tuple_to_descriptor2().expect("membership maps");
        assert_eq!(desc2.trace_width, MEMBERSHIP_TUPLE_WIDTH);
        assert_eq!(desc2.public_input_count, MEMBERSHIP_TUPLE_WIDTH);
        assert!(desc2.tables.is_empty());
        assert!(desc2.hash_sites.is_empty());
        assert!(desc2.ranges.is_empty());
        assert_eq!(desc2.constraints.len(), 2 * MEMBERSHIP_TUPLE_WIDTH);
        let pi_bindings = desc2
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
            .count();
        assert_eq!(pi_bindings, MEMBERSHIP_TUPLE_WIDTH);
        // The PI layout is identity (`pi_index == col`).
        for (i, c) in desc2
            .constraints
            .iter()
            .filter_map(|c| match c {
                VmConstraint2::Base(VmConstraint::PiBinding { col, pi_index, .. }) => {
                    Some((*col, *pi_index))
                }
                _ => None,
            })
            .enumerate()
        {
            assert_eq!(c, (i, i), "PiBinding {i} pins col == pi_index == {i}");
        }
    }

    /// THE POSITIVE POLE: an honest membership tuple proves as a foldable recursion leaf.
    #[test]
    fn honest_membership_proves_as_foldable_leaf() {
        let w = make_witness();
        let pis = w.public_inputs();
        assert_eq!(pis.len(), MEMBERSHIP_TUPLE_WIDTH);
        let config = ir2_leaf_wrap_config();
        let _output = prove_membership_leaf(&w, &pis, &config)
            .expect("the honest membership tuple must prove as a foldable leaf");
    }

    /// THE POSITIVE POLE (claim variant): the claim leaf folds AND re-exposes the bound
    /// 2-felt `(sender_leaf, authorized_root)`.
    #[test]
    fn honest_claim_leaf_exposes_bound_tuple() {
        let w = make_witness();
        let pis = w.public_inputs();
        let config = ir2_leaf_wrap_config();
        let output =
            prove_membership_leaf_with_claim(&w, &pis, &config).expect("the claim leaf must fold");
        let exposed = read_exposed_membership(&output).expect("a membership tuple is exposed");
        assert_eq!(
            exposed,
            [w.sender_leaf, w.authorized_root],
            "the exposed tuple is the bound (sender_leaf, authorized_root)"
        );
    }

    /// THE NEGATIVE POLE: a FORGED tuple (trace carries one tuple, the bound PIs claim a
    /// TAMPERED one) has no satisfying assembly — `PiBinding{First}` requires
    /// `row0[col] == pi[col]`, so the mismatch is UNSAT. No foldable leaf is minted.
    #[test]
    fn forged_membership_tuple_does_not_fold() {
        let w = make_witness();
        let mut tampered = w;
        tampered.sender_leaf += BabyBear::new(1);
        let forged_pis = tampered.public_inputs();
        assert_ne!(forged_pis, w.public_inputs());
        let config = ir2_leaf_wrap_config();

        let what = "a FORGED membership tuple";
        let err = must_refuse(what, || prove_membership_leaf(&w, &forged_pis, &config));
        // `PiBinding{First}` UNSAT — a violated CONSTRAINT, in whichever profile this ran.
        report_refusal(what, &err);
        assert_violated_constraint_not_bus(what, &err);
    }
}
