//! Re-prove a sovereign turn's AUTHORITY tuple as a RECURSION-FOLDABLE IR-v2 leaf
//! (the sovereign analog of [`crate::custom_leaf_adapter`]).
//!
//! ## What this closes
//!
//! Today a sovereign-cell turn's deployed effect-vm leg (the ROTATED proof
//! `sdk::cipherclerk::prove_sovereign_turn_rotated`) proves a state transition
//! `old_commit → new_commit` THROUGH THE EFFECTS — but the AUTHORITY that makes that
//! transition LEGITIMATE for a sovereign cell is checked ENTIRELY OFF-AIR by a
//! re-executing validator ([`turn::executor::execute`], the
//! `turn.sovereign_witnesses` loop):
//!
//!   * (a) the PRE-STATE ANCHOR — `witness.old_commitment == ledger
//!     .get_sovereign_commitment(cell)` (`execute.rs:811`);
//!   * (b) the OWNER Ed25519 SIGNATURE over `(fed, cell, old, new, effects_hash,
//!     ts, sequence)` (`execute.rs:855..886`, `verify_strict`);
//!   * (c) the REPLAY SEQUENCE — `witness.sequence == last_sovereign_witness_sequence
//!     + 1` (`execute.rs:888`, the monotonic per-cell chain-walk).
//!
//! A PURE LIGHT CLIENT (one that only folds the per-turn recursion tree) never
//! witnesses any of (a)/(b)/(c). The in-AIR teeth that COULD carry them —
//! `IS_SOVEREIGN_CELL`, `SOVEREIGN_WITNESS_KEY_COMMIT[4]`, `SOVEREIGN_WITNESS_SEQUENCE`
//! (`circuit::effect_vm::columns::aux_off`, `pi::SOVEREIGN_WITNESS_*`) — are
//! DEAD-ZERO: no producer sets `is_sovereign_cell = 1`, and no constraint links them
//! to a verifying owner signature. The refutation
//! [`metatheory/Dregg2/Circuit/SovereignBackingAttack.lean`]
//! (`deployed_admits_unbacked_sovereign`) exhibits the forged sovereign turn the
//! deployed AIR admits.
//!
//! This module mints the AUTHORITY tuple `(key_commit, sequence, anchor, new_commit)`
//! as a recursion-foldable IR-v2 leaf — the same `aggregate_tree` / chain a light
//! client verifies — so the binding node
//! [`crate::joint_turn_recursive::prove_sovereign_binding_node_segmented`] can
//! `connect` it to the deployed sovereign leg's teeth PIs, exactly as
//! `prove_custom_binding_node_segmented` connects the custom sub-proof.
//!
//! ## The constraint mapping (a TOTAL, table-free shape)
//!
//! The authority tuple is a fixed-width vector pinned at row 0 and held constant:
//!
//! | family                                                  | maps to                                              |
//! |---------------------------------------------------------|------------------------------------------------------|
//! | boundary: `row0[col c] == pi[c]` (all 21 slots)         | `Base(PiBinding{First, col=c, pi=c})` (EXACT)        |
//! | transition: `next[c] − local[c] == 0` (every column)    | `WindowGate{Nxt(c) − Loc(c), on_transition}` (EXACT) |
//!
//! Both carriers are `main`-table algebra; the descriptor declares NO tables. So a
//! prover cannot put one tuple in row 0 and a different tuple in a padding row, and a
//! tuple slot that disagrees with the bound PI is UNSAT — no foldable leaf is minted.
//!
//! ## The sig-attestation boundary (NAMED honestly)
//!
//! This leaf binds the authority TUPLE in-circuit. The Ed25519 verification that the
//! owner key (whose `Poseidon2` digest is `key_commit`) actually SIGNED that tuple
//! stays OFF-AIR — the same digest-of-attestation boundary the membership / G8
//! carriers ride (full in-AIR Ed25519 is the named cost, not done here). What the
//! fold WITNESSES is: the deployed sovereign leg's claimed `key_commit` (the teeth)
//! equals the tuple THIS leaf binds, and the leaf's tuple is internally consistent
//! (anchor/sequence/new all pinned). The residual — anchoring `key_commit` to a
//! VERIFYING signature in-circuit — is the named follow-up (in-AIR Ed25519).

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

use crate::ivc_turn_chain::prove_descriptor_leaf_rotated_with_config;
use crate::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, create_recursion_backend, recursion_layer_over,
};

type RecursionChallenge = <DreggRecursionConfig as StarkGenericConfig>::Challenge;
const D: usize = 4;

// ---- Authority-tuple layout (the leaf's descriptor PI slots) ----
/// `Poseidon2(owner_pubkey)` digest — the deployed `SOVEREIGN_WITNESS_KEY_COMMIT[4]` teeth.
pub const KEY_COMMIT_LO: usize = 0;
/// Length of the key-commit digest (4 felts).
pub const KEY_COMMIT_LEN: usize = 4;
/// Per-cell monotonic sequence — the deployed `SOVEREIGN_WITNESS_SEQUENCE` tooth.
pub const SEQUENCE_SLOT: usize = KEY_COMMIT_LO + KEY_COMMIT_LEN;
/// Pre-state anchor (`old_commitment`, the 8-felt faithful state commit). `execute.rs:811`.
pub const ANCHOR_LO: usize = SEQUENCE_SLOT + 1;
/// Length of the faithful state commitment (8 felts / ~124-bit).
pub const COMMIT_LEN: usize = 8;
/// Post-state commitment (`new_commitment`, 8-felt faithful).
pub const NEW_COMMIT_LO: usize = ANCHOR_LO + COMMIT_LEN;
/// Total authority-tuple width / PI count (4 + 1 + 8 + 8 = 21).
pub const AUTHORITY_TUPLE_WIDTH: usize = NEW_COMMIT_LO + COMMIT_LEN;

/// The 4-felt key-commit claim the leaf re-exposes for the binding node to `connect`.
pub const SOVEREIGN_KEY_CLAIM_LEN: usize = KEY_COMMIT_LEN;

/// A sovereign turn's authority tuple — the SAME `(key_commit, sequence, old, new)`
/// the off-AIR `execute.rs` sovereign-witness loop verifies (`witness.old_commitment`,
/// `witness.sequence`, the owner `public_key` digest, `witness.new_commitment`).
#[derive(Clone, Debug)]
pub struct SovereignAuthorityWitness {
    /// `Poseidon2(owner_pubkey)` — the key digest a verifying signature attests.
    pub key_commit: [BabyBear; KEY_COMMIT_LEN],
    /// The per-cell monotonic sequence (replay counter).
    pub sequence: BabyBear,
    /// The pre-state anchor — the federation's stored sovereign `old_commitment` (8-felt).
    pub anchor: [BabyBear; COMMIT_LEN],
    /// The post-state `new_commitment` (8-felt) the transition reaches.
    pub new_commit: [BabyBear; COMMIT_LEN],
}

impl SovereignAuthorityWitness {
    /// The 21-slot bound authority tuple carried as the leaf's descriptor PIs.
    pub fn public_inputs(&self) -> Vec<BabyBear> {
        let mut pis = vec![BabyBear::new(0); AUTHORITY_TUPLE_WIDTH];
        pis[KEY_COMMIT_LO..KEY_COMMIT_LO + KEY_COMMIT_LEN].copy_from_slice(&self.key_commit);
        pis[SEQUENCE_SLOT] = self.sequence;
        pis[ANCHOR_LO..ANCHOR_LO + COMMIT_LEN].copy_from_slice(&self.anchor);
        pis[NEW_COMMIT_LO..NEW_COMMIT_LO + COMMIT_LEN].copy_from_slice(&self.new_commit);
        pis
    }

    /// The base trace: the authority tuple replicated across two rows (the
    /// `WindowGate` continuity glue pins every column constant, so one typed row
    /// padded to a power of two binds the whole tuple). Width == `AUTHORITY_TUPLE_WIDTH`.
    pub fn generate_trace(&self) -> Vec<Vec<BabyBear>> {
        let row = self.public_inputs();
        vec![row.clone(), row]
    }
}

/// Adapt the sovereign authority tuple into the IR-v2 [`EffectVmDescriptor2`]: 21
/// boundary pins (`PiBinding{First}`, EXACT — `pi_index == col`) + 21 transition
/// pins (`WindowGate{Nxt(c) − Loc(c)}`, EXACT — every column constant across rows).
/// Authored by Lean `TupleBindingEmit.tupleDesc`; parsing fails closed on an invalid artifact.
pub fn sovereign_authority_to_descriptor2() -> Result<EffectVmDescriptor2, String> {
    dregg_circuit::descriptor_ir2::parse_vm_descriptor2(include_str!(
        "../../circuit/descriptors/by-name/sovereign-authority-leaf.json"
    ))
}

/// Prove a sovereign authority tuple as a RECURSION-FOLDABLE IR-v2 leaf (the bridge
/// pattern). `public_inputs` is the 21-slot bound tuple — for an HONEST proof it
/// equals `witness.public_inputs()`. Passing a DIFFERENT tuple is a forged binding
/// (trace claims one tuple, PIs another): the `PiBinding{First}` requires `row0[col]
/// == pi[col]`, so the mismatch is UNSAT and no foldable leaf is minted.
pub fn prove_sovereign_leaf(
    witness: &SovereignAuthorityWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    if public_inputs.len() != AUTHORITY_TUPLE_WIDTH {
        return Err(format!(
            "sovereign-authority leaf expects {AUTHORITY_TUPLE_WIDTH} PI slots, got {}",
            public_inputs.len()
        ));
    }
    let desc2 = sovereign_authority_to_descriptor2()?;
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
    .map_err(|e| format!("sovereign-authority leaf inner IR-v2 prove failed: {e}"))?;

    prove_descriptor_leaf_rotated_with_config(&desc2, &inner, public_inputs, config)
        .map_err(|e| format!("sovereign-authority leaf recursion wrap failed: {e}"))
}

/// Prove the sovereign authority tuple as a foldable leaf AND re-expose its bound
/// 4-felt `key_commit` (lanes `[KEY_COMMIT_LO .. KEY_COMMIT_LO+KEY_COMMIT_LEN)`) as a
/// public CLAIM the binding node `connect`s to the deployed sovereign leg's teeth.
///
/// Unlike the custom commitment expose (which decomposes one ext limb through a
/// sponge), this re-exposes the leaf's OWN FRI-bound descriptor PI lanes directly —
/// the same direct-lane re-expose [`crate::ivc_turn_chain::prove_descriptor_leaf_dual_expose`]
/// uses for the custom_proof_commitment slice — so the plain backend suffices (no
/// `recompose/coeff` table). The exposed `key_commit` is welded to the execution: a
/// prover cannot expose a `key_commit` that disagrees with the tuple the leaf proves,
/// because both are the SAME in-circuit PI targets.
pub fn prove_sovereign_leaf_with_key_claim(
    witness: &SovereignAuthorityWitness,
    public_inputs: &[BabyBear],
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    if public_inputs.len() != AUTHORITY_TUPLE_WIDTH {
        return Err(format!(
            "sovereign-authority leaf expects {AUTHORITY_TUPLE_WIDTH} PI slots, got {}",
            public_inputs.len()
        ));
    }
    let desc2 = sovereign_authority_to_descriptor2()?;
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
    .map_err(|e| format!("sovereign-authority key-claim leaf inner IR-v2 prove failed: {e}"))?;

    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(&desc2, &inner, public_inputs, config).map_err(|e| {
            format!("sovereign-authority key-claim verify-triple build failed: {e}")
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
            .expect("sovereign-authority leaf has a main instance carrying the descriptor PIs");
        debug_assert!(
            main.len() >= KEY_COMMIT_LO + KEY_COMMIT_LEN,
            "main instance must carry the key_commit PI slots"
        );
        // Re-expose the FRI-bound key_commit lanes directly (not free scalars).
        let claim: Vec<Target> = (0..KEY_COMMIT_LEN)
            .map(|k| main[KEY_COMMIT_LO + k])
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
    .map_err(|e| format!("sovereign-authority key-claim leaf-wrap failed: {e:?}"))
}

/// Read the 4-felt `key_commit` a [`prove_sovereign_leaf_with_key_claim`] leaf exposes
/// through its `expose_claim` table. Returns `None` if the proof carries no claim.
pub fn read_exposed_key_commit(
    output: &RecursionOutput<DreggRecursionConfig>,
) -> Option<[BabyBear; SOVEREIGN_KEY_CLAIM_LEN]> {
    let claims: Vec<BabyBear> = output
        .0
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")?
        .public_values
        .iter()
        .map(|&v| BabyBear::new(v.as_canonical_u32()))
        .collect();
    if claims.len() < SOVEREIGN_KEY_CLAIM_LEN {
        return None;
    }
    Some([claims[0], claims[1], claims[2], claims[3]])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binding_tooth::report_refusal;
    use crate::ivc_turn_chain::ir2_leaf_wrap_config;
    use dregg_circuit::descriptor_ir2::VmConstraint2;
    use dregg_circuit::lean_descriptor_air::VmConstraint;
    use dregg_circuit::refusal::{assert_violated_constraint_not_bus, must_refuse};

    fn make_witness() -> SovereignAuthorityWitness {
        SovereignAuthorityWitness {
            key_commit: [
                BabyBear::new(11),
                BabyBear::new(22),
                BabyBear::new(33),
                BabyBear::new(44),
            ],
            sequence: BabyBear::new(7),
            anchor: core::array::from_fn(|i| BabyBear::new(100 + i as u32)),
            new_commit: core::array::from_fn(|i| BabyBear::new(200 + i as u32)),
        }
    }

    #[test]
    fn sovereign_authority_maps_to_descriptor2() {
        let desc2 = sovereign_authority_to_descriptor2().expect("sovereign maps");
        assert_eq!(desc2.trace_width, AUTHORITY_TUPLE_WIDTH);
        assert_eq!(desc2.public_input_count, AUTHORITY_TUPLE_WIDTH);
        assert!(desc2.tables.is_empty());
        assert!(desc2.hash_sites.is_empty());
        assert!(desc2.ranges.is_empty());
        assert_eq!(desc2.constraints.len(), 2 * AUTHORITY_TUPLE_WIDTH);
        let pi_bindings = desc2
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
            .count();
        assert_eq!(pi_bindings, AUTHORITY_TUPLE_WIDTH);
    }

    /// THE POSITIVE POLE: an honest authority tuple proves as a foldable recursion leaf.
    #[test]
    fn honest_sovereign_authority_proves_as_foldable_leaf() {
        let w = make_witness();
        let pis = w.public_inputs();
        assert_eq!(pis.len(), AUTHORITY_TUPLE_WIDTH);
        let config = ir2_leaf_wrap_config();
        let _output = prove_sovereign_leaf(&w, &pis, &config)
            .expect("the honest sovereign authority must prove as a foldable leaf");
    }

    /// THE POSITIVE POLE (claim variant): the key-claim leaf folds AND re-exposes the
    /// bound 4-felt key_commit.
    #[test]
    fn honest_key_claim_leaf_exposes_bound_key_commit() {
        let w = make_witness();
        let pis = w.public_inputs();
        let config = ir2_leaf_wrap_config();
        let output = prove_sovereign_leaf_with_key_claim(&w, &pis, &config)
            .expect("the key-claim leaf must fold");
        let exposed = read_exposed_key_commit(&output).expect("a key_commit claim is exposed");
        assert_eq!(
            exposed, w.key_commit,
            "the exposed key_commit is the bound tuple's"
        );
    }

    /// THE NEGATIVE POLE: a FORGED tuple (trace carries one key_commit, the bound PIs
    /// claim a TAMPERED one) has no satisfying assembly — `PiBinding{First}` requires
    /// `row0[col] == pi[col]`, so the mismatch is UNSAT. No foldable leaf is minted.
    #[test]
    fn forged_authority_tuple_does_not_fold() {
        let w = make_witness();
        let mut tampered = w.clone();
        tampered.key_commit[0] += BabyBear::new(1);
        tampered.sequence += BabyBear::new(1);
        let forged_pis = tampered.public_inputs();
        assert_ne!(forged_pis, w.public_inputs());
        let config = ir2_leaf_wrap_config();

        let what = "a FORGED sovereign authority tuple";
        let err = must_refuse(what, || prove_sovereign_leaf(&w, &forged_pis, &config));
        // `PiBinding{First}` UNSAT — a violated CONSTRAINT, in whichever profile this ran.
        report_refusal(what, &err);
        assert_violated_constraint_not_bus(what, &err);
    }
}
