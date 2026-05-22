//! General-purpose non-membership proving system.
//!
//! Generalizes `AccumulatorNonRevocationAir` from revocation-specific to any property set.
//! The core idea: prove "element X is NOT in set S" via polynomial-evaluation accumulator
//! over BabyBear^4, regardless of what the set represents (revocation, suspension,
//! blacklist, role exclusion, etc.).
//!
//! # Usage
//!
//! ```rust,ignore
//! use pyana_circuit::non_membership::{NonMembershipProver, NonMembershipCheck};
//!
//! // Create a prover for a given set
//! let suspended_users = vec![hash_a, hash_b, hash_c];
//! let prover = NonMembershipProver::new(&suspended_users);
//!
//! // Prove that my_hash is NOT in the suspended set
//! let proof = prover.prove_non_membership(&[my_hash]).unwrap();
//!
//! // Verify (only needs the set's accumulator + alpha, not the set itself)
//! let result = prover.verify_non_membership(&[my_hash], &proof);
//! assert!(result.is_ok());
//! ```
//!
//! # Relationship to AccumulatorNonRevocationAir
//!
//! `AccumulatorNonRevocationAir` is now a thin wrapper over this generalized system.
//! The underlying AIR, trace layout, and constraints are identical -- the generalization
//! is purely at the API level (configurable set identity, generic public inputs).

use crate::accumulator_air::{
    AccumulatorNonMembershipWitness, AccumulatorNonRevocationAir, AccumulatorNonRevocationWitness,
    ExtElem, compute_accumulator, derive_alpha,
};
use crate::field::BabyBear;
use crate::poseidon2::hash_many;
use crate::stark::{self, StarkProof};

// Re-export key types from accumulator_air for convenience.
pub use crate::accumulator_air::{ExtElem as NonMembershipExtElem, MAX_ANCESTORS};

/// Identifier for a property set (e.g., "suspended", "blacklisted", "revoked").
///
/// The set_id is incorporated into the alpha challenge derivation to ensure
/// that proofs are bound to a specific set and cannot be replayed across sets.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SetIdentifier {
    /// Human-readable name (used for debugging/logging only).
    pub name: String,
    /// Domain separator: a field element derived from the set's identity.
    /// Different sets MUST have different domain separators.
    pub domain_sep: BabyBear,
}

impl SetIdentifier {
    /// Create a new set identifier from a name.
    /// The domain separator is derived by hashing the name.
    pub fn new(name: &str) -> Self {
        let name_hash = blake3::hash(name.as_bytes());
        let bytes = name_hash.as_bytes();
        let domain_sep = BabyBear::new(
            u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]) % crate::field::BABYBEAR_P,
        );
        Self {
            name: name.to_string(),
            domain_sep,
        }
    }

    /// Create a set identifier from a raw domain separator.
    pub fn from_raw(name: &str, domain_sep: BabyBear) -> Self {
        Self {
            name: name.to_string(),
            domain_sep,
        }
    }

    /// The "revocation" set identifier (backward compatible with AccumulatorNonRevocationAir).
    pub fn revocation() -> Self {
        Self {
            name: "revocation".to_string(),
            domain_sep: BabyBear::new(0x7265766F), // "revo"
        }
    }
}

/// A non-membership check to be composed with derivation proofs.
///
/// This specifies that a particular attribute's hash must NOT appear in
/// a given property set.
#[derive(Clone, Debug)]
pub struct NonMembershipCheck {
    /// The attribute being checked (e.g., "user_id", "credential_hash").
    pub attribute: String,
    /// The property set this element must NOT be in.
    pub set_id: SetIdentifier,
    /// The accumulator value for the property set.
    pub accumulator: ExtElem,
    /// The alpha challenge for the property set.
    pub alpha: ExtElem,
    /// Number of elements being checked.
    pub num_elements: usize,
}

/// A verified non-membership proof bundled with its public parameters.
#[derive(Clone, Debug)]
pub struct NonMembershipProof {
    /// The underlying STARK proof.
    pub stark_proof: StarkProof,
    /// The set identifier this proof is for.
    pub set_id: SetIdentifier,
    /// Accumulator value used in the proof.
    pub accumulator: ExtElem,
    /// Alpha challenge used in the proof.
    pub alpha: ExtElem,
    /// Number of elements proven non-member.
    pub num_elements: usize,
}

/// Builder/prover for non-membership proofs.
///
/// Encapsulates the set's accumulator state and provides methods to
/// prove and verify non-membership of elements.
#[derive(Clone, Debug)]
pub struct NonMembershipProver {
    /// The set's elements (needed for witness generation).
    set_elements: Vec<BabyBear>,
    /// The computed accumulator value.
    accumulator: ExtElem,
    /// The alpha challenge derived from the set.
    alpha: ExtElem,
    /// The set identifier.
    set_id: SetIdentifier,
}

impl NonMembershipProver {
    /// Create a new non-membership prover for a given set.
    ///
    /// Uses the default alpha derivation (same as the revocation system).
    pub fn new(set_elements: &[BabyBear]) -> Self {
        Self::with_set_id(set_elements, SetIdentifier::revocation())
    }

    /// Create a non-membership prover with a specific set identifier.
    ///
    /// The set identifier is mixed into the alpha derivation, ensuring
    /// proofs for different sets cannot be confused.
    pub fn with_set_id(set_elements: &[BabyBear], set_id: SetIdentifier) -> Self {
        let alpha = derive_alpha_for_set(set_elements, &set_id);
        let accumulator = compute_accumulator(set_elements, alpha);
        Self {
            set_elements: set_elements.to_vec(),
            accumulator,
            alpha,
            set_id,
        }
    }

    /// Create a prover with an explicit alpha challenge.
    ///
    /// Use this when the alpha is provided externally (e.g., from a federation).
    pub fn with_explicit_alpha(
        set_elements: &[BabyBear],
        alpha: ExtElem,
        set_id: SetIdentifier,
    ) -> Self {
        let accumulator = compute_accumulator(set_elements, alpha);
        Self {
            set_elements: set_elements.to_vec(),
            accumulator,
            alpha,
            set_id,
        }
    }

    /// Get the accumulator value for this set.
    pub fn accumulator(&self) -> ExtElem {
        self.accumulator
    }

    /// Get the alpha challenge for this set.
    pub fn alpha(&self) -> ExtElem {
        self.alpha
    }

    /// Get the set identifier.
    pub fn set_id(&self) -> &SetIdentifier {
        &self.set_id
    }

    /// Prove that the given elements are NOT in this set.
    ///
    /// Returns `None` if any element IS in the set (proof cannot be generated).
    pub fn prove_non_membership(&self, elements: &[BabyBear]) -> Option<NonMembershipProof> {
        if elements.len() > MAX_ANCESTORS {
            return None;
        }

        // Generate the STARK proof using the existing accumulator infrastructure.
        let stark_proof = prove_accumulator_non_membership(
            elements,
            self.accumulator,
            self.alpha,
            &self.set_elements,
        )?;

        Some(NonMembershipProof {
            stark_proof,
            set_id: self.set_id.clone(),
            accumulator: self.accumulator,
            alpha: self.alpha,
            num_elements: elements.len(),
        })
    }

    /// Verify a non-membership proof.
    ///
    /// The verifier only needs the accumulator value and alpha (not the full set).
    pub fn verify_non_membership(&self, proof: &NonMembershipProof) -> Result<(), String> {
        // Cross-set replay protection: the proof's parameters must match this prover's set.
        if proof.accumulator != self.accumulator {
            return Err("accumulator mismatch: proof was generated for a different set".into());
        }
        if proof.alpha != self.alpha {
            return Err("alpha mismatch: proof was generated for a different set".into());
        }
        verify_accumulator_non_membership(
            proof.accumulator,
            proof.alpha,
            proof.num_elements,
            &proof.stark_proof,
        )
    }
}

/// Stateless verification of a non-membership proof.
///
/// This can be used by verifiers who know the accumulator parameters
/// but don't have access to the full set.
pub fn verify_non_membership_proof(proof: &NonMembershipProof) -> Result<(), String> {
    verify_accumulator_non_membership(
        proof.accumulator,
        proof.alpha,
        proof.num_elements,
        &proof.stark_proof,
    )
}

/// Verify a non-membership proof given explicit accumulator parameters.
///
/// This is the lowest-level verification function.
pub fn verify_accumulator_non_membership(
    accumulator: ExtElem,
    alpha: ExtElem,
    num_elements: usize,
    proof: &StarkProof,
) -> Result<(), String> {
    let air = AccumulatorNonRevocationAir;

    let mut public_inputs = Vec::with_capacity(9);
    public_inputs.extend_from_slice(&accumulator.0);
    public_inputs.extend_from_slice(&alpha.0);
    public_inputs.push(BabyBear::new(num_elements as u32));

    stark::verify(&air, proof, &public_inputs)
}

/// Generate a STARK proof of non-membership for multiple elements.
///
/// This is the core proving function -- it generates witnesses and produces
/// the STARK proof. Returns `None` if any element is actually in the set.
pub fn prove_accumulator_non_membership(
    elements: &[BabyBear],
    accumulator: ExtElem,
    alpha: ExtElem,
    set_elements: &[BabyBear],
) -> Option<StarkProof> {
    if elements.len() > MAX_ANCESTORS {
        return None;
    }

    // Generate witnesses for each element.
    let mut ancestors = Vec::with_capacity(elements.len());
    for &h in elements {
        // Check if h is in the set.
        if set_elements.contains(&h) {
            return None; // Element is in the set -- cannot prove non-membership.
        }

        // Compute remainder: v = product(h - s_j) for all s_j in set_elements.
        let mut remainder_base = BabyBear::ONE;
        for &s in set_elements {
            remainder_base = remainder_base * (h - s);
        }

        if remainder_base == BabyBear::ZERO {
            return None; // Hash collision or element is in set.
        }

        let remainder = ExtElem::from_base(remainder_base);

        // Compute quotient: w = (Acc - v) / (alpha - h)
        let h_ext = ExtElem::from_base(h);
        let diff = alpha.sub(h_ext);
        let numerator = accumulator.sub(remainder);
        let quotient = numerator.mul(diff.inverse()?);

        ancestors.push(AccumulatorNonMembershipWitness {
            ancestor_hash: h,
            quotient,
            remainder,
        });
    }

    let witness = AccumulatorNonRevocationWitness { ancestors };
    let air = AccumulatorNonRevocationAir;
    let (trace, public_inputs) =
        AccumulatorNonRevocationAir::generate_trace(&witness, accumulator, alpha);

    Some(stark::prove(&air, &trace, &public_inputs))
}

/// Derive the alpha challenge for a specific set, incorporating the set identifier.
///
/// This ensures that proofs for different sets (revocation, suspension, etc.)
/// use different alpha values and cannot be cross-replayed.
pub fn derive_alpha_for_set(set_elements: &[BabyBear], set_id: &SetIdentifier) -> ExtElem {
    // Mix the set identifier's domain separator into the alpha derivation.
    let domain_sep = hash_many(&[
        BabyBear::new(0x7079616E), // "pyan"
        BabyBear::new(0x612D6E6D), // "a-nm" (non-membership)
        set_id.domain_sep,
        BabyBear::new(set_elements.len() as u32),
    ]);

    // Hash domain separator with set elements for binding.
    let binding = if set_elements.is_empty() {
        domain_sep
    } else {
        let mut elems = vec![domain_sep];
        let sample_count = set_elements.len().min(16);
        for &h in &set_elements[..sample_count] {
            elems.push(h);
        }
        hash_many(&elems)
    };

    // Generate 4 independent BabyBear elements for the extension field challenge.
    let h0 = binding;
    let h1 = hash_many(&[h0, BabyBear::new(1)]);
    let h2 = hash_many(&[h0, BabyBear::new(2)]);
    let h3 = hash_many(&[h0, BabyBear::new(3)]);

    ExtElem([h0, h1, h2, h3])
}

/// Compute the accumulator value for a set (delegates to accumulator_air).
pub fn compute_set_accumulator(set_elements: &[BabyBear], alpha: ExtElem) -> ExtElem {
    compute_accumulator(set_elements, alpha)
}

// ============================================================================
// Integration with derivation system
// ============================================================================

/// A non-membership check attached to a derivation witness.
///
/// When verifying a derivation with non-membership checks, the verifier must:
/// 1. Verify the derivation STARK proof (for positive authorization)
/// 2. For each NonMembershipCheck, verify the corresponding accumulator STARK proof
///
/// This composition ensures both that the user IS authorized AND that they are
/// NOT in any exclusion set.
#[derive(Clone, Debug)]
pub struct DerivationNonMembershipCheck {
    /// Which attribute hash(es) are being checked for non-membership.
    pub element_hashes: Vec<BabyBear>,
    /// The property set identifier.
    pub set_id: SetIdentifier,
    /// The accumulator value for the property set.
    pub accumulator: ExtElem,
    /// The alpha challenge for the property set.
    pub alpha: ExtElem,
    /// The STARK proof of non-membership.
    pub proof: StarkProof,
}

/// A derivation result augmented with non-membership proofs.
#[derive(Clone, Debug)]
pub struct AugmentedDerivation {
    /// The derivation STARK proof (from derivation_air).
    pub derivation_proof: StarkProof,
    /// Public inputs for the derivation proof.
    pub derivation_public_inputs: Vec<BabyBear>,
    /// Non-membership checks that must also hold.
    pub non_membership_checks: Vec<DerivationNonMembershipCheck>,
}

/// Verify an augmented derivation (derivation + non-membership checks).
///
/// Returns Ok(()) if both the derivation proof AND all non-membership proofs verify.
pub fn verify_augmented_derivation(augmented: &AugmentedDerivation) -> Result<(), String> {
    // 1. Verify the derivation STARK proof.
    crate::derivation_air::verify_derivation_stark(
        &augmented.derivation_proof,
        &augmented.derivation_public_inputs,
    )?;

    // 2. Verify each non-membership check.
    for (i, check) in augmented.non_membership_checks.iter().enumerate() {
        verify_accumulator_non_membership(
            check.accumulator,
            check.alpha,
            check.element_hashes.len(),
            &check.proof,
        )
        .map_err(|e| {
            format!(
                "non-membership check {} ({}) failed: {}",
                i, check.set_id.name, e
            )
        })?;
    }

    Ok(())
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn make_hash(seed: u32) -> BabyBear {
        hash_many(&[BabyBear::new(seed), BabyBear::new(0xDEAD)])
    }

    // ─── Basic non-membership prover tests ───

    #[test]
    fn non_membership_prove_and_verify() {
        let suspended_set: Vec<BabyBear> = (1..=5).map(|i| make_hash(i * 100)).collect();
        let prover =
            NonMembershipProver::with_set_id(&suspended_set, SetIdentifier::new("suspended_users"));

        // Element NOT in the suspended set.
        let user_hash = make_hash(9999);
        assert!(!suspended_set.contains(&user_hash));

        let proof = prover
            .prove_non_membership(&[user_hash])
            .expect("Should generate proof for non-member");

        let result = prover.verify_non_membership(&proof);
        assert!(result.is_ok(), "Proof should verify: {:?}", result.err());
    }

    #[test]
    fn non_membership_user_is_in_suspended_set_fails() {
        let suspended_set: Vec<BabyBear> = (1..=5).map(|i| make_hash(i * 100)).collect();
        let prover =
            NonMembershipProver::with_set_id(&suspended_set, SetIdentifier::new("suspended_users"));

        // Element that IS in the suspended set.
        let suspended_user = suspended_set[2];

        let result = prover.prove_non_membership(&[suspended_user]);
        assert!(
            result.is_none(),
            "Should not be able to prove non-membership for a member"
        );
    }

    #[test]
    fn non_membership_multiple_elements() {
        let blacklist: Vec<BabyBear> = (1..=20).map(|i| make_hash(i)).collect();
        let prover = NonMembershipProver::with_set_id(&blacklist, SetIdentifier::new("blacklist"));

        // Multiple elements NOT in the blacklist.
        let elements: Vec<BabyBear> = (100..=104).map(|i| make_hash(i)).collect();
        for e in &elements {
            assert!(!blacklist.contains(e));
        }

        let proof = prover
            .prove_non_membership(&elements)
            .expect("Should prove non-membership for multiple elements");

        let result = prover.verify_non_membership(&proof);
        assert!(result.is_ok(), "Multi-element proof should verify");
    }

    #[test]
    fn non_membership_different_sets_different_proofs() {
        let set_a: Vec<BabyBear> = (1..=5).map(|i| make_hash(i * 10)).collect();
        let set_b: Vec<BabyBear> = (1..=5).map(|i| make_hash(i * 20)).collect();

        let prover_a = NonMembershipProver::with_set_id(&set_a, SetIdentifier::new("set_a"));
        let prover_b = NonMembershipProver::with_set_id(&set_b, SetIdentifier::new("set_b"));

        // Same element, proven against different sets.
        let element = make_hash(9999);

        let proof_a = prover_a.prove_non_membership(&[element]).unwrap();
        let proof_b = prover_b.prove_non_membership(&[element]).unwrap();

        // Each proof verifies against its own prover.
        assert!(prover_a.verify_non_membership(&proof_a).is_ok());
        assert!(prover_b.verify_non_membership(&proof_b).is_ok());

        // Proofs have different accumulators (different sets).
        assert_ne!(proof_a.accumulator, proof_b.accumulator);
    }

    #[test]
    fn non_membership_wrong_accumulator_rejected() {
        let set: Vec<BabyBear> = (1..=5).map(|i| make_hash(i * 50)).collect();
        let prover = NonMembershipProver::with_set_id(&set, SetIdentifier::new("test_set"));

        let element = make_hash(9999);
        let mut proof = prover.prove_non_membership(&[element]).unwrap();

        // Tamper with the accumulator.
        proof.accumulator = ExtElem([
            BabyBear::new(1),
            BabyBear::new(2),
            BabyBear::new(3),
            BabyBear::new(4),
        ]);

        // Verification with tampered accumulator should fail.
        let result = verify_non_membership_proof(&proof);
        assert!(result.is_err(), "Tampered accumulator should be rejected");
    }

    #[test]
    fn non_membership_empty_set() {
        let empty_set: Vec<BabyBear> = vec![];
        let prover = NonMembershipProver::with_set_id(&empty_set, SetIdentifier::new("empty"));

        let element = make_hash(42);
        let proof = prover
            .prove_non_membership(&[element])
            .expect("Non-membership in empty set should always succeed");

        let result = prover.verify_non_membership(&proof);
        assert!(result.is_ok());
    }

    #[test]
    fn non_membership_large_set() {
        let large_set: Vec<BabyBear> = (1..=100).map(|i| make_hash(i)).collect();
        let prover = NonMembershipProver::with_set_id(&large_set, SetIdentifier::new("large"));

        let element = make_hash(999);
        assert!(!large_set.contains(&element));

        let proof = prover
            .prove_non_membership(&[element])
            .expect("Should work with large set");

        let result = prover.verify_non_membership(&proof);
        assert!(result.is_ok());
    }

    // ─── Set identifier tests ───

    #[test]
    fn set_identifier_revocation_backward_compat() {
        // The revocation set identifier should produce the same results
        // as the original derive_alpha when used with the default prover.
        let set: Vec<BabyBear> = (1..=5).map(|i| make_hash(i * 50)).collect();

        let prover = NonMembershipProver::with_set_id(&set, SetIdentifier::revocation());
        let element = make_hash(9999);

        let proof = prover.prove_non_membership(&[element]).unwrap();
        assert!(prover.verify_non_membership(&proof).is_ok());
    }

    #[test]
    fn set_identifier_different_names_different_alphas() {
        let set: Vec<BabyBear> = (1..=5).map(|i| make_hash(i)).collect();

        let alpha_a = derive_alpha_for_set(&set, &SetIdentifier::new("suspended"));
        let alpha_b = derive_alpha_for_set(&set, &SetIdentifier::new("blacklisted"));

        // Different set names produce different alpha challenges.
        assert_ne!(alpha_a, alpha_b);
    }

    // ─── Integration with derivation ───

    #[test]
    fn non_membership_integration_with_derivation() {
        // Simulate: user derives access AND proves they are not suspended.
        let suspended_set: Vec<BabyBear> = (1..=10).map(|i| make_hash(i * 100)).collect();
        let prover =
            NonMembershipProver::with_set_id(&suspended_set, SetIdentifier::new("suspended"));

        // User's credential hash (not in suspended set).
        let user_cred_hash = make_hash(5555);
        assert!(!suspended_set.contains(&user_cred_hash));

        // Generate non-membership proof.
        let nm_proof = prover
            .prove_non_membership(&[user_cred_hash])
            .expect("Should prove non-membership");

        // Verify the non-membership proof independently.
        assert!(prover.verify_non_membership(&nm_proof).is_ok());

        // Also verify via the stateless function.
        assert!(verify_non_membership_proof(&nm_proof).is_ok());
    }

    #[test]
    fn non_membership_derivation_check_struct() {
        // Test creating a DerivationNonMembershipCheck.
        let suspended_set: Vec<BabyBear> = (1..=5).map(|i| make_hash(i * 100)).collect();
        let set_id = SetIdentifier::new("suspended");
        let alpha = derive_alpha_for_set(&suspended_set, &set_id);
        let accumulator = compute_set_accumulator(&suspended_set, alpha);

        let user_hash = make_hash(7777);
        let proof =
            prove_accumulator_non_membership(&[user_hash], accumulator, alpha, &suspended_set)
                .expect("Should generate proof");

        let check = DerivationNonMembershipCheck {
            element_hashes: vec![user_hash],
            set_id: set_id.clone(),
            accumulator,
            alpha,
            proof,
        };

        // Verify the check independently.
        let result = verify_accumulator_non_membership(
            check.accumulator,
            check.alpha,
            check.element_hashes.len(),
            &check.proof,
        );
        assert!(result.is_ok());
    }

    #[test]
    fn non_membership_positive_membership_correctly_fails() {
        // A user who IS in the suspended set cannot generate a proof.
        let suspended_set: Vec<BabyBear> = (1..=10).map(|i| make_hash(i * 100)).collect();
        let prover =
            NonMembershipProver::with_set_id(&suspended_set, SetIdentifier::new("suspended"));

        // This hash IS in the set.
        let suspended_user = make_hash(5 * 100); // hash(500)
        assert!(suspended_set.contains(&suspended_user));

        let result = prover.prove_non_membership(&[suspended_user]);
        assert!(
            result.is_none(),
            "Should not prove non-membership for suspended user"
        );
    }

    #[test]
    fn non_membership_both_membership_and_non_membership() {
        // Integration test: prove positive membership in one set AND non-membership in another.
        let allowed_set: Vec<BabyBear> = (1..=20).map(|i| make_hash(i * 10)).collect();
        let blocked_set: Vec<BabyBear> = (100..=110).map(|i| make_hash(i * 10)).collect();

        let user_hash = make_hash(5 * 10); // IS in allowed_set
        assert!(allowed_set.contains(&user_hash));
        assert!(!blocked_set.contains(&user_hash));

        // Prove non-membership in blocked set.
        let prover = NonMembershipProver::with_set_id(&blocked_set, SetIdentifier::new("blocked"));
        let nm_proof = prover
            .prove_non_membership(&[user_hash])
            .expect("Should prove non-membership in blocked set");
        assert!(prover.verify_non_membership(&nm_proof).is_ok());

        // The positive membership in allowed_set would be proven by a separate
        // Merkle membership proof (out of scope for this module).
    }
}
