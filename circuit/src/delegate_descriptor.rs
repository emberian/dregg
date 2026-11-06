//! IR-v2 **delegation-binding** descriptor (`dregg-delegate::v2`) — the descriptor-world twin of the
//! executor's `StarkDelegation` scope-binding check.
//!
//! ## What this closes
//!
//! A `DelegationProofData::StarkDelegation` bearer proof authorizes a turn only if the STARK it
//! carries commits to the CANONICAL scope vector for the grant being exercised. The executor
//! enforces exactly that in `turn/src/action.rs::verify_stark_delegation_binding` — it recomputes the
//! expected public inputs
//!
//! ```text
//!   root_issuer_commitment (8 limbs) ‖ target (8 limbs) ‖ scope_hash (8 limbs)     [24 felts]
//! ```
//!
//! (`stark_delegation_expected_public_inputs`) and requires `proof.public_inputs[i] == expected[i]`
//! for every limb (`action.rs:672-685`). A relayed proof minted for a NARROWER grant (different
//! target/permission/expiry/federation/root-issuer) commits to a different scope vector, so the
//! elementwise check fails and the wider grant is refused.
//!
//! The StarkProof→descriptor migration re-expresses that binding as an [`EffectVmDescriptor2`]:
//! [`delegate_binding_descriptor`] pins each of the 24 scope limbs to its public input via a row-0
//! `PiBinding`, so `verify_vm_descriptor2(desc, proof, expected_scope)` succeeds iff the proof was
//! minted for exactly `expected_scope` — the IDENTICAL relay-forge check `action.rs:672-685` runs, now
//! bound in-circuit rather than by an executor-side field compare. A proof bound to scope `A` fails to
//! verify against any forged wider scope `B` (the row-0 boundary `col_i == PI_i` is UNSAT).
//!
//! ## Lean-authored tuple binding
//!
//! `TupleBindingEmit.delegateDesc` authors this descriptor; its generic
//! `tuple_semantics` theorem characterizes every emitted PI pin. The checked-in
//! artifact is serialized by `EmitByName.lean` and interpreted here. Delegation
//! binds only the first row, preserving the existing scope contract. It does not
//! assert the cap-graph effect or authorize the scope off-chain.

use crate::descriptor_ir2::EffectVmDescriptor2;
use crate::field::BabyBear;

/// Field limbs per 32-byte scope value (`root_issuer_commitment` / `target` / `scope_hash`), matching
/// `effect_vm::bytes32_to_8_limbs` (8 limbs each).
pub const SCOPE_VALUE_LIMBS: usize = 8;
/// The three 32-byte scope values bound by the delegation-binding: root_issuer, target, scope_hash.
pub const SCOPE_VALUES: usize = 3;
/// Total scope limbs bound (= trace width = public-input count).
pub const DELEGATE_SCOPE_LIMBS: usize = SCOPE_VALUE_LIMBS * SCOPE_VALUES; // 24

/// Column / PI offset of the `root_issuer_commitment` limb block.
pub const OFF_ROOT_ISSUER: usize = 0;
/// Column / PI offset of the `target` limb block.
pub const OFF_TARGET: usize = SCOPE_VALUE_LIMBS; // 8
/// Column / PI offset of the `scope_hash` limb block.
pub const OFF_SCOPE_HASH: usize = SCOPE_VALUE_LIMBS * 2; // 16

/// The `descriptor_by_name` dispatch key for the IR-v2 delegation-binding descriptor.
pub const DELEGATE_V2_NAME: &str = "dregg-delegate::v2";

/// **`delegate_binding_descriptor`** — the IR-v2 delegation scope-binding descriptor. Its `24`
/// row-0 `PiBinding`s pin each scope limb `col i` to public input `i`, so a proof verifies iff its
/// committed public inputs equal the caller's expected scope vector — the exact relay-forge check
/// `action.rs:672-685` enforces, in the descriptor world.
pub fn delegate_binding_descriptor() -> EffectVmDescriptor2 {
    crate::descriptor_ir2::parse_vm_descriptor2(include_str!(
        "../descriptors/by-name/delegate-binding-v2.json"
    ))
    .expect("Lean-emitted delegate binding descriptor must parse")
}

/// Build the delegation-binding base trace + public inputs for a scope vector.
///
/// `scope` is the 24-limb `[root_issuer(8) ‖ target(8) ‖ scope_hash(8)]` vector (the executor's
/// `stark_delegation_expected_public_inputs`). Returns a 2-row (power-of-two) trace carrying the scope
/// on every row and `pis == scope`. Proving this and verifying against a DIFFERENT scope vector fails
/// (the row-0 `PiBinding`s are UNSAT), which is the relay-forge rejection.
pub fn delegate_binding_witness(
    scope: &[BabyBear; DELEGATE_SCOPE_LIMBS],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let row = scope.to_vec();
    // Two rows (a power-of-two height); only row 0 is pinned, but replicate for a self-describing trace.
    let trace = vec![row.clone(), row];
    let pis = scope.to_vec();
    (trace, pis)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_by_name::descriptor_by_name;
    use crate::descriptor_ir2::{
        MemBoundaryWitness, check_descriptor2_wellformed, prove_vm_descriptor2,
        verify_vm_descriptor2,
    };

    /// A representative scope vector: distinct per-limb values so a single-limb forge is detectable.
    fn sample_scope() -> [BabyBear; DELEGATE_SCOPE_LIMBS] {
        core::array::from_fn(|i| BabyBear::new((i as u32 + 1) * 1_000 + 7))
    }

    /// The descriptor is well-formed and dispatches by name.
    #[test]
    fn dispatches_and_is_wellformed() {
        let desc = descriptor_by_name(DELEGATE_V2_NAME).expect("delegate v2 dispatches");
        assert_eq!(desc, delegate_binding_descriptor());
        assert_eq!(desc.trace_width, DELEGATE_SCOPE_LIMBS);
        assert_eq!(desc.public_input_count, DELEGATE_SCOPE_LIMBS);
        check_descriptor2_wellformed(&desc).expect("well-formed");
    }

    /// THE POSITIVE POLE: a delegation-binding proof bound to a scope verifies against that same
    /// scope through the dispatched descriptor.
    #[test]
    fn honest_delegation_binding_verifies() {
        let desc = descriptor_by_name(DELEGATE_V2_NAME).expect("dispatch");
        let scope = sample_scope();
        let (trace, pis) = delegate_binding_witness(&scope);
        let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .expect("honest delegation-binding must prove");
        verify_vm_descriptor2(&desc, &proof, &pis).expect("honest delegation-binding must verify");
    }

    /// THE RELAY FORGE: a proof minted for scope `A` is REJECTED when verified against a forged
    /// WIDER scope `B` (one target limb changed) — the exact `action.rs:672-685` binding failure.
    /// Non-vacuous: the honest proof is asserted to accept above and here.
    #[test]
    fn forged_wider_scope_refuses() {
        let desc = descriptor_by_name(DELEGATE_V2_NAME).expect("dispatch");
        let scope = sample_scope();
        let (trace, pis) = delegate_binding_witness(&scope);

        let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .expect("honest delegation-binding proves");
        // non-vacuity: it verifies against its own scope.
        assert!(verify_vm_descriptor2(&desc, &proof, &pis).is_ok());

        // Forge a WIDER grant: flip one target limb (relaying a narrow-target proof onto a wider one).
        let mut forged = scope;
        forged[OFF_TARGET] += BabyBear::ONE;
        assert_ne!(forged[OFF_TARGET], scope[OFF_TARGET]);
        let forged_pis: Vec<BabyBear> = forged.to_vec();
        assert!(
            verify_vm_descriptor2(&desc, &proof, &forged_pis).is_err(),
            "a proof bound to scope A must NOT verify against a forged wider scope B (relay forge)"
        );
    }

    /// EVERY scope limb is load-bearing: perturbing any one of the 24 limbs makes the bound proof
    /// reject — no limb of the (root_issuer ‖ target ‖ scope_hash) scope can be relaxed.
    #[test]
    fn every_scope_limb_is_bound() {
        let desc = delegate_binding_descriptor();
        let scope = sample_scope();
        let (trace, pis) = delegate_binding_witness(&scope);
        let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .expect("proves");
        for i in 0..DELEGATE_SCOPE_LIMBS {
            let mut forged = scope;
            forged[i] += BabyBear::ONE;
            let forged_pis: Vec<BabyBear> = forged.to_vec();
            assert!(
                verify_vm_descriptor2(&desc, &proof, &forged_pis).is_err(),
                "perturbing scope limb {i} must break the binding — that limb is not bound"
            );
        }
    }
}
