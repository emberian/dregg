//! Re-prove the REAL foreign note-spend STARK as a RECURSION-FOLDABLE IR-v2 leaf —
//! the bridge carrier's G2 BACKING half (WELD-STATE §3 bridge row).
//!
//! ## Which STARK this re-proves (grounding)
//!
//! The STARK a bridge mint's backing rests on executor-side is the DSL note-spending
//! circuit `dregg-note-spending-dsl-v3`
//! ([`dregg_circuit::dsl::note_spending::note_spending_circuit_descriptor`], width 62,
//! 6 PIs `[nullifier, merkle_root, value_lo30, asset_type, destination_federation,
//! value_hi34]`): `turn::executor::apply::apply_bridge_mint` verifies it via
//! `verify_note_spend_descriptor2` (apply.rs:65, called at apply.rs:1913). It
//! carries the SPEND SEMANTICS — spending-key knowledge (the two-step 8-limb
//! nullifier chain C3/C4), the FULL-WIDTH 28-limb commitment binding (C2a..C2g),
//! and Merkle membership (the `hash_fact(current, [sib0..2, position])` chain C6/C7)
//! — everything the DELETED `bridge_action_witness` binding AIR did NOT have. (`SCHEMA_NOTE_SPEND` in
//! `effect_action_air.rs` is a different surface: the in-federation binding schema
//! for `Effect::NoteSpend` rows, not the bridge's foreign backing proof.)
//!
//! ## Why this module exists — folding `bridge_action_witness` was UNSOUND as a backing
//!
//! ⚑ That AIR and its fold adapter are DELETED (2026-08-07); this section records WHY, because
//! the reason is the reason this module is the backing. `bridge_leaf_adapter` folded
//! `BridgeActionAir`, a BINDING-ONLY AIR: its 26-limb tuple was a prover-chosen constant trace
//! with NO Merkle membership and NO spending-key relation, and the deployed `mint_hash` was read
//! by ZERO constraints. A leaf that re-proves only the binding AIR gives a light client a
//! tuple the prover invented — the vacuous connect the fail-open law forbids. The
//! SOUND backing leaf is THIS one: re-prove the real note-spend STARK, so the folded
//! claim is welded (through the FRI-bound descriptor PIs) to a genuine
//! key-knowledge + membership + full-width-commitment execution.
//!
//! ## The consumed Lean AIR
//!
//! `noteSpendLeafDescFixed` in `NoteSpendingLeafEmit.lean` authors the 149-column,
//! seven-PI, 33-constraint artifact. This adapter shares both descriptor parsing
//! and validated witness assembly with `dregg_circuit::note_spend_witness`.
//! Six last-row boundaries close the transition-gate gap proved in
//! `NoteSpendingLeafRung2`. `NoteSpendingLeafServed` composes the existing semantic
//! bridges, retaining explicit chip-table, canonicality and path-shape premises.
//!
//! **The fact-sponge carrier (the piece `cellprogram_to_descriptor2` refuses).** A DSL
//! `ConstraintExpr::Hash` is `hash_fact(pred, terms)`: ONE Poseidon2 permutation
//! seeded `st[0]=pred, st[1..5]=terms, st[5]=FACT_MARK(0xFACF), st[6]=1`. The chip's
//! arity-7 row seeds `st[0..7] = in0..in6` verbatim (`chip_absorb_all_lanes`, the
//! `seed456` branch), so the faithful carrier is an arity-7 chip lookup with inputs
//! `[pred, t0..t3, Const(0xFACF), Const(1)]` — byte-identical (KAT-pinned by
//! `fact_arity7_chip_absorb_matches_hash_fact`).
//!
//! **The row-gating mux.** Chip lookups fire on EVERY main row, but the note-spend
//! hash sites are row-gated (commitment-row sites via `1 − is_merkle`, the Merkle
//! site via `is_merkle`). The carrier muxes the tuple by the (Binary-pinned) selector
//! `s`: value inputs ride as `s·col`, the domain constants stay constant, and the
//! digest lane rides as `s·out + (1−s)·K₀` where `K₀ = hash_fact(0, [])`. On a firing
//! row the tuple IS the genuine site; on a non-firing row it degenerates to the
//! constant zero-fact permutation row (satisfiable by construction, binding nothing).
//! All muxed tuple entries are degree ≤ 2 (below the degree-4 `MerkleHash` exprs the
//! custom adapter already ships).
//!
//! ## The claim tuple — `(…PIs…, mint_hash)`, with mint_hash RECOMPUTED IN-CIRCUIT
//!
//! [`prove_note_spend_leaf_with_claim`] exposes all `NOTE_SPEND_CLAIM_LEN = 7` lanes
//! `[nullifier, merkle_root, value_lo, asset_type, destination_federation, value_hi,
//! mint_hash]` as its `expose_claim` (via
//! [`crate::ivc_turn_chain::prove_descriptor_leaf_with_pi_slice_expose`]). Lane 6 is
//! the FELT-DOMAIN mint identity [`note_spend_mint_hash_felt`] =
//! `hash_fact(hash_fact(nullifier, [root, dest_fed, asset]), [value_lo, value_hi])`,
//! recomputed IN-AIR by two more gated fact sites over the SAME PI-pinned row-0
//! columns and pinned to PI 6 — so a prover cannot expose a mint identity that
//! disagrees with the spend this leaf actually proves. Lane 0 (the nullifier) is the
//! double-mint guard's connect target: the deployed descriptor ALREADY commits the
//! faithful `nullifier_root` (pre-limb 26) and `pi::NOTESPEND_NULLIFIER`. (That read
//! "PI 198" until 2026-08-06 — a pre-Phase-C literal; the offset cascades from
//! `OWNER_CELL_ID_BASE + OWNER_CELL_ID_LEN`, so name the constant, never the integer.)
//!
//! ## ⚑ THE SEAM IS NOT CLOSED — the arm is BUILT, and it CANNOT FIRE (measured 2026-08-07)
//!
//! This section read "THE FORMERLY-VK-GATED SEAM — CLOSED … now CONNECTED on the
//! deployed path." That was false, and it is the sentence that sends each new reader
//! to repair a byte↔felt codec and stop. What has landed is the MECHANISM (the PI-46
//! pin, the dual-expose leg, this backing leaf, the binding node). What has NOT landed
//! is any path on which the mechanism runs. SIX independent blockers stand between HEAD
//! and "the fold arm fired on a real bridge turn"; each was read at source, and NO ONE
//! of them is repaired by fixing the other five.
//!
//! 1. **There is no production witness.** `CarrierWitness::Bridge` is constructed
//!    ONLY in tests (`circuit-prove/tests/bridge_binding_deployed_tooth.rs:309`,
//!    `tests/ivc_turn_chain_rotated.rs:509`).
//!    `joint_turn_aggregation::BridgeWitnessBundle::from_retained_bridge:452` — the
//!    one documented "THE PRODUCTION PROJECTION" — has **zero callers**. Every
//!    production leg minter hard-codes `carrier_witness: None`
//!    (`turn-prover/src/rotation_witness.rs:195`, `node/src/turn_proving.rs:2011`).
//!    Retention then **refuses** to persist a leg carrying one
//!    (`node/src/turn_proving.rs:1908`), so a wire-rehydrated turn always lands on the
//!    `None` re-exec rung. The Bridge arm at `ivc_turn_chain.rs:4438` is dead code.
//! 2. **The nullifier leg disagrees with the enforcer.** The projectors
//!    (`turn/src/executor/effect_vm_bridge.rs:406`, `sdk/src/cipherclerk.rs:6880`)
//!    build `mint_hash` from `compress(nullifier)`, while `apply_bridge_mint:2618`
//!    DECODES it (`note_spend_nullifier_felt`). Different felts ⇒ PI 46 ≠ lane 6.
//! 3. **The root leg has no honest byte↔felt map at all.** Both sides compress, so they
//!    agree with each other — but `pi[1]` is an in-AIR chain output, and `compress` is
//!    the inverse of nothing.
//! 4. **⚑ The AIR's Merkle node function is no deployed tree's.** C6 is
//!    `hash_fact(current, [sib0, sib1, sib2, position])`; the note tree that actually
//!    serves membership proofs (`Poseidon2MerkleTree`, via
//!    `persist::Poseidon2NoteTree::prove_membership`) hashes
//!    `hash_4_to_1([c0, c1, c2, c3])` — position-ORDERED children, no position felt.
//!    Different function, different arity. Stated in-tree at
//!    `commit/src/poseidon2_tree.rs:988` and `circuit/src/dsl/note_spending.rs:524`.
//!    **No membership path from the real note tree can satisfy this AIR**, at any
//!    encoding. This is the blocker that makes 2 and 3 moot, and it is why "fix the
//!    codec on both legs" cannot produce a firing arm.
//! 5. **The attested root is a THIRD tree's.** `AttestedRoot::note_tree_root` on the
//!    live path is `CanonicalFaithfulRoot::to_bytes()` — the 8-lane `Faithful8` root of
//!    `Poseidon2NoteTree16` (`node/src/blocklace_sync.rs:7355`), not the scalar tree
//!    this AIR walks, and not one felt widened.
//! 6. **Nothing produces a bridge `spending_proof`.** Every construction in the tree is
//!    `vec![]`, `vec![1,2,3,4]`, or `vec![0xDE,0xAD,0xBE,0xEF]`
//!    (`teasting/tests/cross_federation.rs:354`, `cell-crypto/src/note_bridge.rs:1483`).
//!    The BridgeMint accept path has never been exercised by a genuine note-spend STARK.
//!
//! ⚠ **What the green tooth proves.** `bridge_binding_deployed_tooth.rs`'s honest pole
//! sets the leg's PI 46 to `bundle.public_inputs[NOTE_SPEND_MINT_HASH_PI]` — the leaf's
//! OWN lane 6. It sets both sides of `connect` equal by construction and never calls
//! `bridge_mint_hash_felt`, `verify_portable_note`, or any projector. It demonstrates
//! that the binding node wires up; it is NOT evidence that a bridge turn can satisfy it.
//! (Both poles are `#[ignore]`d besides.)
//!
//! ⓘ **Where the repair actually is.** The identity is a HASH-NODE identity, so the bar
//! is collision resistance, and eight BabyBear lanes give ≈2^123.63 — which is exactly
//! what `Faithful8`/`CanonicalFaithfulRoot` already carry on the wire and what
//! `Poseidon2NoteTree16` already builds. The scalar tree this AIR walks carries ~31 bits
//! per node (≈2^15.5 birthday), so re-pointing C6 at `hash_4_to_1` would make the path
//! REACHABLE but land the source-root binding far below the repo's ~124-bit bar. The
//! on-bar target is the faithful 8-lane note-spend surface
//! (`faithful-note-spend-exact-v3`, built and staged, NOT in the deployed registry —
//! `circuit-prove/src/faithful_note_spend_exact_v3.rs:18`); the codec then falls out for
//! free as the lane-wise decode-or-refuse of `Faithful8::to_bytes32`, the direct
//! generalization of `note_spend_nullifier_felt`'s refuse-don't-reinterpret precedent.
//! That is a campaign (new claim tuple, new identity, new leaf, VK epoch, registry
//! rows), not a codec patch — and a codec patch shipped in its place would read as
//! progress while all six blockers stand.
//!
//! `apply_bridge_mint`'s `verify_note_spend_descriptor2` remains the executor enforcer.
//! This leaf is its light-client-witnessable twin — WIRED, not connected.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, UMemBoundaryWitness, prove_vm_descriptor2_for_config,
};
pub use dregg_circuit::dsl::note_spending::note_spend_mint_hash_felt;
use dregg_circuit::field::BabyBear;
pub use dregg_circuit::note_spend_witness::{
    NOTE_SPEND_CLAIM_LEN, NOTE_SPEND_MINT_HASH_PI, note_spend_leaf_public_inputs,
};
use dregg_circuit::note_spending_witness::NoteSpendingWitness;

use p3_recursion::{ProveNextLayerParams, RecursionOutput};

use crate::fold_vk_pin::FoldVkPins;
use crate::ivc_turn_chain::{
    prove_descriptor_leaf_rotated_with_config, prove_descriptor_leaf_with_pi_slice_expose,
};
use crate::joint_turn_aggregation::JointAggError;
use crate::plonky3_recursion_impl::recursive::DreggRecursionConfig;

/// Extension degree of the recursion config's PCS (the BabyBear-quartic stack).
const D: usize = 4;

/// Consume the same Lean-emitted, last-row-repaired AIR as the name-dispatched prover.
pub fn note_spend_to_descriptor2() -> Result<EffectVmDescriptor2, String> {
    dregg_circuit::note_spend_witness::note_spend_leaf_descriptor()
}

/// Prove a REAL note-spend as a RECURSION-FOLDABLE IR-v2 leaf.
///
/// `witness` is the SAME `NoteSpendingWitness` the off-AIR `note_spending_dsl_circuit`
/// consumes (spending key, 28-limb preimage, Merkle path). `public_inputs` is the
/// 7-slot claim tuple — for an HONEST proof, [`note_spend_leaf_public_inputs`].
/// Passing a DIFFERENT tuple is exactly a forged backing: the `PiBinding{First}`
/// pins + the chip-recomputed hash chain make the mismatch UNSAT, so no foldable
/// leaf is minted (the leaf-level tooth).
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_note_spend_leaf(
    witness: &NoteSpendingWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let (desc2, inner) = prove_note_spend_inner(witness, public_inputs, config)?;
    prove_descriptor_leaf_rotated_with_config(&desc2, &inner, public_inputs, config)
        .map_err(|e| format!("note-spend leaf recursion wrap failed: {e}"))
}

/// Prove a REAL note-spend leaf (as [`prove_note_spend_leaf`]) AND RE-EXPOSE its
/// 7-slot claim tuple `[nullifier, merkle_root, value_lo, asset_type,
/// destination_federation, value_hi, mint_hash]` as an IN-CIRCUIT `expose_claim`
/// (lanes `[0 .. NOTE_SPEND_CLAIM_LEN)`), read from the leaf's own FRI-bound
/// descriptor PIs.
///
/// The exposed lane 6 is the in-AIR-recomputed [`note_spend_mint_hash_felt`]; lane 0
/// is the nullifier (the double-mint guard's connect target — `NOTESPEND_NULLIFIER`
/// PI 198 + the faithful `nullifier_root` pre-limb already exist committed).
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_note_spend_leaf_with_claim(
    witness: &NoteSpendingWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let (desc2, inner) = prove_note_spend_inner(witness, public_inputs, config)?;
    prove_descriptor_leaf_with_pi_slice_expose(
        &desc2,
        &inner,
        public_inputs,
        config,
        0,
        NOTE_SPEND_CLAIM_LEN,
    )
    .map_err(|e| format!("note-spend claim leaf expose-wrap failed: {e}"))
}

/// The shared inner IR-v2 prove (emitted descriptor + validated witness + batch mint
/// under the recursion config type).
fn prove_note_spend_inner(
    witness: &NoteSpendingWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<
    (
        EffectVmDescriptor2,
        dregg_circuit::descriptor_ir2::Ir2BatchProof<DreggRecursionConfig>,
    ),
    String,
> {
    if public_inputs.len() != NOTE_SPEND_CLAIM_LEN {
        return Err(format!(
            "note-spend leaf expects {NOTE_SPEND_CLAIM_LEN} PI slots, got {}",
            public_inputs.len()
        ));
    }
    let desc2 = note_spend_to_descriptor2()?;
    let (base_trace, _honest_pis) = dregg_circuit::note_spend_witness::note_spend_witness(witness)?;

    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc2,
        &base_trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .map_err(|e| format!("note-spend leaf inner IR-v2 prove failed: {e}"))?;
    Ok((desc2, inner))
}

/// The note-spend binding node's failure prefix, single-sourced so the production `format!` and
/// `binding_tooth`'s arm assertion cannot drift apart. ⚠ it is a SUBSTRING of the segmented
/// node's prefix, so a `contains` on it does not discriminate the two.
pub const NOTE_SPEND_BINDING_NODE_ARM: &str = "note-spend binding aggregation node failed";

/// **THE NOTE-SPEND BINDING MECHANISM NODE (no segment).** Aggregate a leg leaf that
/// RE-EXPOSES its CLAIMED 7-slot tuple WITH the note-spend sub-proof leaf
/// ([`prove_note_spend_leaf_with_claim`]), CONNECTING the two tuples lane-by-lane
/// in-circuit and re-exposing the bound tuple. A leg claiming a
/// `(…, mint_hash)`/nullifier no verifying note-spend backs is a `connect` conflict
/// ⇒ UNSAT ⇒ no root.
///
/// ⚑ The DEPLOYED leg side (the `mintV3` mint_hash PI-emit + dual-expose) is the
/// named VK-gated big-bang piece (module docs); this node is its ready consumer.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_note_spend_binding_node(
    leg_claim_leaf: &RecursionOutput<DreggRecursionConfig>,
    note_spend_leaf: &RecursionOutput<DreggRecursionConfig>,
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

    let leg_idx = expose_claim_instance_index(&leg_claim_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "note-spend leg leaf carries no re-exposed tuple (expose_claim) table — it \
                     must expose the claimed 7-slot tuple"
                .to_string(),
        }
    })?;
    let cs_idx = expose_claim_instance_index(&note_spend_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "note-spend sub-proof leaf carries no exposed tuple (expose_claim) table — \
                     it must be minted via prove_note_spend_leaf_with_claim"
                .to_string(),
        }
    })?;

    let left = leg_claim_leaf.into_recursion_input_pinned::<BatchOnly>(pins.left.clone());
    let right = note_spend_leaf.into_recursion_input_pinned::<BatchOnly>(pins.right.clone());

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>],
                       _left_vk_cap: &[Target],
                       _right_vk_cap: &[Target]| {
        let lg = left_apt
            .get(leg_idx)
            .expect("note-spend leg's re-exposed tuple instance present");
        let cs = right_apt
            .get(cs_idx)
            .expect("note-spend sub-proof's exposed tuple instance present");
        debug_assert!(lg.len() >= NOTE_SPEND_CLAIM_LEN && cs.len() >= NOTE_SPEND_CLAIM_LEN);
        // THE BINDING TOOTH, IN-CIRCUIT: the leg's CLAIMED tuple must equal the
        // note-spend leaf's GENUINE bound tuple, lane by lane.
        for k in 0..NOTE_SPEND_CLAIM_LEN {
            cb.connect(lg[k], cs[k]);
        }
        let bound: Vec<Target> = (0..NOTE_SPEND_CLAIM_LEN).map(|k| lg[k]).collect();
        cb.expose_as_public_output(&bound);
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
        reason: format!("{NOTE_SPEND_BINDING_NODE_ARM}: {e:?}"),
    })
}

/// **THE SEGMENT-PRESERVING NOTE-SPEND BINDING NODE (deployed-path shape, VK-gated
/// consumer).** The leg is a
/// DUAL-EXPOSE leaf (`expose_claim` = segment lanes `[0 .. SEG_WIDTH)` ++ the claimed
/// tuple lanes `[SEG_SPINE_WIDTH ..)`), the sub-proof leaf is
/// [`prove_note_spend_leaf_with_claim`]; the node `connect`s the tuple lanes and
/// re-exposes the segment so the result folds into `aggregate_tree` like any per-turn
/// segment leaf. The dual-expose leg requires the `mintV3` PI-emit (the named
/// VK-gated seam) — this node is ready for it.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_note_spend_binding_node_segmented(
    dual_expose_leg_leaf: &RecursionOutput<DreggRecursionConfig>,
    note_spend_leaf: &RecursionOutput<DreggRecursionConfig>,
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
    use crate::plonky3_recursion_impl::recursive::create_recursion_backend;
    use p3_circuit::CircuitBuilder;
    use p3_recursion::{BatchOnly, Target, build_and_prove_aggregation_layer_with_expose};

    type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

    let leg_idx = expose_claim_instance_index(&dual_expose_leg_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "dual-expose note-spend leg leaf carries no expose_claim table — it must \
                     re-expose (segment ++ the 7-slot tuple)"
                .to_string(),
        }
    })?;
    let cs_idx = expose_claim_instance_index(&note_spend_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "note-spend sub-proof leaf carries no exposed tuple (expose_claim) table — \
                     it must be minted via prove_note_spend_leaf_with_claim"
                .to_string(),
        }
    })?;

    let left = dual_expose_leg_leaf.into_recursion_input_pinned::<BatchOnly>(pins.left.clone());
    let right = note_spend_leaf.into_recursion_input_pinned::<BatchOnly>(pins.right.clone());

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>],
                       left_vk_cap: &[Target],
                       right_vk_cap: &[Target]| {
        let lg = left_apt
            .get(leg_idx)
            .expect("dual-expose note-spend leg's claim instance present");
        let cs = right_apt
            .get(cs_idx)
            .expect("note-spend sub-proof's exposed tuple instance present");
        debug_assert!(
            lg.len() >= SEG_SPINE_WIDTH + NOTE_SPEND_CLAIM_LEN && cs.len() >= NOTE_SPEND_CLAIM_LEN,
            "dual-expose claim must carry segment ++ tuple; note-spend leaf carries the tuple"
        );
        for k in 0..NOTE_SPEND_CLAIM_LEN {
            cb.connect(lg[SEG_SPINE_WIDTH + k], cs[k]);
        }
        // RE-EXPOSE `[segment ‖ vk_spine]` as the parent claim.
        let parent = binding_node_segment_and_spine(cb, lg, left_vk_cap, right_vk_cap);
        cb.expose_as_public_output(&parent);
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
        reason: format!("segmented note-spend binding aggregation node failed: {e:?}"),
    })
}

/// **THE DEPLOYED MINT-HASH BINDING NODE (the 7th carrier's live shape).** The leg is a
/// DUAL-EXPOSE leaf over the deployed `mintVmDescriptor2R24` (`mintV3BridgeHash`): its
/// `expose_claim` = segment lanes `[0 .. SEG_WIDTH)` ++ ONE claimed lane — the published
/// mint-hash PI 46 (the STEP-1 felt-domain `note_spend_mint_hash_felt` the producer filled and
/// the pin welded to the mint row's `param0`). The sub-proof leaf is
/// [`prove_note_spend_leaf_with_claim`] (7 exposed lanes, lane [`NOTE_SPEND_MINT_HASH_PI`] the
/// in-AIR-recomputed identity over the REAL verified spend). The node `connect`s the leg's ONE
/// claimed lane to the leaf's lane 6 and re-exposes the segment.
///
/// ONE lane suffices to bind the WHOLE tuple: lane 6 is the `hash_fact` chain over the leaf's
/// OWN PI-pinned `(nullifier, root, value_lo, asset, dest_fed, value_hi)` (the in-AIR recompute
/// — `forged_mint_hash_does_not_fold`), so under Poseidon2-CR a leg identity that connects IS
/// the identity of exactly that verified spend — which nullifier, from which source root, to
/// which federation, which asset, the full u64 amount. A leg claiming a mint identity no
/// verifying note-spend backs is a `connect` conflict ⇒ UNSAT ⇒ no root.
///
/// `config` must be [`crate::ivc_turn_chain::ir2_leaf_wrap_config`].
pub fn prove_note_spend_mint_binding_node_segmented(
    dual_expose_leg_leaf: &RecursionOutput<DreggRecursionConfig>,
    note_spend_leaf: &RecursionOutput<DreggRecursionConfig>,
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
    use crate::plonky3_recursion_impl::recursive::create_recursion_backend;
    use p3_circuit::CircuitBuilder;
    use p3_recursion::{BatchOnly, Target, build_and_prove_aggregation_layer_with_expose};

    type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

    let leg_idx = expose_claim_instance_index(&dual_expose_leg_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "dual-expose bridge-mint leg leaf carries no expose_claim table — it must \
                     re-expose (segment ++ the published mint-hash PI)"
                .to_string(),
        }
    })?;
    let cs_idx = expose_claim_instance_index(&note_spend_leaf.0).ok_or_else(|| {
        JointAggError::AggregationProofInvalid {
            reason: "note-spend sub-proof leaf carries no exposed tuple (expose_claim) table — \
                     it must be minted via prove_note_spend_leaf_with_claim"
                .to_string(),
        }
    })?;

    let left = dual_expose_leg_leaf.into_recursion_input_pinned::<BatchOnly>(pins.left.clone());
    let right = note_spend_leaf.into_recursion_input_pinned::<BatchOnly>(pins.right.clone());

    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>],
                       left_vk_cap: &[Target],
                       right_vk_cap: &[Target]| {
        let lg = left_apt
            .get(leg_idx)
            .expect("dual-expose bridge-mint leg's claim instance present");
        let cs = right_apt
            .get(cs_idx)
            .expect("note-spend sub-proof's exposed tuple instance present");
        debug_assert!(
            lg.len() >= SEG_SPINE_WIDTH + 1 && cs.len() >= NOTE_SPEND_CLAIM_LEN,
            "dual-expose claim must carry segment ++ the mint-hash lane; note-spend leaf \
             carries the 7-lane tuple"
        );
        // THE BINDING TOOTH, IN-CIRCUIT: the leg's published mint identity must equal the
        // note-spend leaf's in-AIR-recomputed identity over its genuine verified spend.
        cb.connect(lg[SEG_SPINE_WIDTH], cs[NOTE_SPEND_MINT_HASH_PI]);
        // RE-EXPOSE `[segment ‖ vk_spine]` as the parent claim.
        let parent = binding_node_segment_and_spine(cb, lg, left_vk_cap, right_vk_cap);
        cb.expose_as_public_output(&parent);
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
        reason: format!("segmented bridge mint-hash binding aggregation node failed: {e:?}"),
    })
}

/// Read the exposed 7-lane claim tuple off a leaf minted by
/// [`prove_note_spend_leaf_with_claim`].
pub fn read_exposed_note_spend_claim(
    output: &RecursionOutput<DreggRecursionConfig>,
) -> Option<[BabyBear; NOTE_SPEND_CLAIM_LEN]> {
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
    if claims.len() < NOTE_SPEND_CLAIM_LEN {
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
    use dregg_circuit::note_spending_witness::{NOTE_SPENDING_WIDTH, pi};
    use dregg_circuit::poseidon2::hash_fact;
    const NS_FACT_MARK: u32 = 0xFACF;
    const EXT_BASE_WIDTH: usize = NOTE_SPENDING_WIDTH + 3;
    use dregg_circuit::note_spending_witness::test_spending_key;
    use dregg_circuit::poseidon2::hash_many;
    use dregg_circuit::refusal::{assert_violated_constraint_not_bus, must_refuse_or_unsat_panic};

    /// THE FEASIBILITY KAT: the chip's arity-7 absorb with inputs
    /// `[pred, t0..t3, 0xFACF, 1]` is BYTE-IDENTICAL to `poseidon2::hash_fact` —
    /// the seeding equivalence the whole fact-site carrier rests on. Also pins the
    /// zero-fact constant `K₀` the non-firing rows degenerate to.
    #[test]
    fn fact_arity7_chip_absorb_matches_hash_fact() {
        let pred = BabyBear::new(123_456);
        let terms = [
            BabyBear::new(7),
            BabyBear::new(88),
            BabyBear::new(999),
            BabyBear::new(1_000_000),
        ];
        let ins = [
            pred,
            terms[0],
            terms[1],
            terms[2],
            terms[3],
            BabyBear::new(NS_FACT_MARK),
            BabyBear::ONE,
        ];
        assert_eq!(
            chip_absorb_all_lanes(7, &ins)[0],
            hash_fact(pred, &terms),
            "arity-7 chip absorb must reproduce hash_fact exactly"
        );
        // Zero-padded terms (the C2g 3-term site shape).
        let ins3 = [
            pred,
            terms[0],
            terms[1],
            terms[2],
            BabyBear::ZERO,
            BabyBear::new(NS_FACT_MARK),
            BabyBear::ONE,
        ];
        assert_eq!(
            chip_absorb_all_lanes(7, &ins3)[0],
            hash_fact(pred, &[terms[0], terms[1], terms[2]]),
            "zero-padded fact absorb must match hash_fact's zero pad"
        );
        // The non-firing degenerate row: all value lanes zero.
        let ins0 = [
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::new(NS_FACT_MARK),
            BabyBear::ONE,
        ];
        assert_eq!(
            chip_absorb_all_lanes(7, &ins0)[0],
            hash_fact(BabyBear::ZERO, &[]),
            "the K₀ zero-fact constant must match the muxed-off digest lane"
        );
    }

    /// The shared emitted artifact has the expected
    /// shape: 12 chip sites (7 commitment-chain + 2 nullifier + 1 Merkle + 2 mint),
    /// the C7 WindowGate, and 8 PiBindings (6 source + MINT_ROOT + MINT_HASH).
    #[test]
    fn note_spend_descriptor_lowers() {
        let desc2 = note_spend_to_descriptor2().expect("the emitted note-spend descriptor parses");
        assert_eq!(desc2.constraints.len(), 33);
        assert_eq!(
            desc2
                .constraints
                .iter()
                .filter(|c| matches!(
                    c,
                    VmConstraint2::Base(VmConstraint::Boundary {
                        row: VmRow::Last,
                        ..
                    })
                ))
                .count(),
            6
        );
        assert_eq!(desc2.public_input_count, NOTE_SPEND_CLAIM_LEN);
        let sites = desc2
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
            .count();
        assert_eq!(sites, 12, "7 chain + 2 nullifier + 1 merkle + 2 mint sites");
        let windows = desc2
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
            .count();
        assert_eq!(windows, 1, "the C7 Merkle-chain continuity");
        let pins = desc2
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
            .count();
        assert_eq!(pins, 8, "6 source boundary pins + MINT_ROOT + MINT_HASH");
        // Lane accounting: 12 sites × 7 lanes past the 65-wide extended base.
        assert_eq!(
            desc2.trace_width,
            EXT_BASE_WIDTH + 12 * (CHIP_OUT_LANES - 1)
        );
    }

    /// A REAL full-width witness (raw 32-byte fields + a > 2^30 u64 value, so the
    /// high limb is live). Depth 2 → 4 trace rows (1 commitment + 2 Merkle + 1 pad),
    /// the one-padding-row discipline the deployed DSL circuit's own tests use.
    fn make_witness(tag: u8) -> NoteSpendingWitness {
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
            0xDEAD_BEEF_CAFE, // > 2^30: the value_hi limb is live
            3,
            &nonce,
            &rand,
            key,
            siblings,
            positions,
        )
    }

    /// THE POSITIVE POLE: an honest REAL note-spend (spending key + 28-limb
    /// commitment + Merkle path) proves as a foldable recursion leaf, and the
    /// exposed claim tuple equals the bound PIs — with lane 6 the in-AIR-recomputed
    /// felt-domain mint identity.
    #[test]
    fn honest_note_spend_proves_as_foldable_leaf_and_exposes_claim() {
        let w = make_witness(0x10);
        let pis = note_spend_leaf_public_inputs(&w);
        assert_eq!(pis.len(), NOTE_SPEND_CLAIM_LEN);
        assert_eq!(
            pis[NOTE_SPEND_MINT_HASH_PI],
            note_spend_mint_hash_felt(pis[0], pis[1], pis[2], pis[3], pis[4], pis[5]),
            "the host mint identity matches the named composition"
        );
        let config = ir2_leaf_wrap_config();

        let output = prove_note_spend_leaf_with_claim(&w, &pis, &config)
            .expect("the honest note-spend must prove as a foldable claim leaf");
        let exposed =
            read_exposed_note_spend_claim(&output).expect("the leaf exposes the 7-lane claim");
        assert_eq!(
            exposed.as_slice(),
            pis.as_slice(),
            "the exposed claim is the bound tuple"
        );
    }

    /// THE NEGATIVE POLE (tuple): a FORGED claim (tampered nullifier lane) has no
    /// satisfying assembly — the `PiBinding{First}` + the chip-bound nullifier chain
    /// refuse it AT THE LEAF; no foldable leaf is minted.
    #[test]
    fn forged_nullifier_does_not_fold() {
        let w = make_witness(0x22);
        let mut pis = note_spend_leaf_public_inputs(&w);
        pis[pi::NULLIFIER] += BabyBear::ONE;
        let config = ir2_leaf_wrap_config();

        let refusal = must_refuse_or_unsat_panic("a FORGED nullifier", || {
            prove_note_spend_leaf(&w, &pis, &config)
        });
        // NAME THE REFUSAL, MEASURED FIRST (2026-08-10, --release, this exact fixture):
        //   OodEvaluationMismatch { index: Some(0) }
        // The bare `must_refuse_or_unsat_panic` here DISCARDED its result, so an FRI fault, an OOM
        // or a trace-shape error read identically to the forgery being caught. The subject is
        // a violated CONSTRAINT (`OodEvaluationMismatch` deployed / `constraints not
        // satisfied on row` in debug): the nullifier's `PiBinding{First}` pin is an emitted gate.
        report_refusal("a FORGED nullifier", &refusal.reason());
        assert_violated_constraint_not_bus("a FORGED nullifier", &refusal.reason());
    }

    /// THE MINT-BINDING TOOTH: a forged mint_hash lane (every other PI honest) is
    /// refused AT THE LEAF — the in-AIR recompute (the two gated fact sites over the
    /// PI-pinned row-0 columns) plus the PI-6 pin make it UNSAT. This is what makes
    /// the exposed mint identity a WELD, not a prover-chosen scalar.
    #[test]
    fn forged_mint_hash_does_not_fold() {
        let w = make_witness(0x33);
        let mut pis = note_spend_leaf_public_inputs(&w);
        pis[NOTE_SPEND_MINT_HASH_PI] += BabyBear::ONE;
        let config = ir2_leaf_wrap_config();

        let refusal = must_refuse_or_unsat_panic("a FORGED mint_hash", || {
            prove_note_spend_leaf(&w, &pis, &config)
        });
        // NAME THE REFUSAL, MEASURED FIRST (2026-08-10, --release, this exact fixture):
        //   OodEvaluationMismatch { index: Some(0) }
        // The bare `must_refuse_or_unsat_panic` here DISCARDED its result, so an FRI fault, an OOM
        // or a trace-shape error read identically to the forgery being caught. The subject is
        // a violated CONSTRAINT (`OodEvaluationMismatch` deployed / `constraints not
        // satisfied on row` in debug): the PI-6 pin over the in-AIR-recomputed mint identity is an emitted gate.
        report_refusal("a FORGED mint_hash", &refusal.reason());
        assert_violated_constraint_not_bus("a FORGED mint_hash", &refusal.reason());
    }
}
