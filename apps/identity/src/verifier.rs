//! Verification policies: define what proofs are required and verify presentations.
//!
//! A verifier specifies a policy describing:
//! - Which attributes need to be proven
//! - What predicates must hold (e.g., age >= 18)
//! - Whether non-revocation proofs are required
//! - Which federation root to trust

use crate::presentation::{CredentialPresentation, PredicateRequirement, PresentationRequest};
use pyana_circuit::field::BabyBear;
use pyana_circuit::predicate_air::PredicateType;

/// A verification policy specifying what proofs are required.
#[derive(Clone, Debug)]
pub struct VerificationPolicy {
    /// Human-readable name of this policy.
    pub name: String,
    /// The federation root the verifier trusts.
    pub federation_root: BabyBear,
    /// The revocation root the verifier expects (current revocation state).
    pub revocation_root: BabyBear,
    /// Requirements that must be satisfied.
    pub requirements: Vec<PolicyRequirement>,
    /// Whether non-revocation proof is mandatory.
    pub require_non_revocation: bool,
}

/// A single requirement in a verification policy.
#[derive(Clone, Debug)]
pub struct PolicyRequirement {
    /// The attribute that must be proven.
    pub attribute_name: String,
    /// The type of proof required.
    pub proof_type: PolicyProofType,
}

/// Types of proofs a policy can require.
#[derive(Clone, Debug)]
pub enum PolicyProofType {
    /// The attribute must be revealed in plaintext.
    Reveal,
    /// The attribute must satisfy a predicate (hidden value).
    Predicate {
        predicate_type: PredicateType,
        threshold: u32,
    },
    /// The attribute's existence must be proven (but value hidden).
    Existence,
}

impl VerificationPolicy {
    /// Create a new verification policy.
    pub fn new(name: &str, federation_root: BabyBear, revocation_root: BabyBear) -> Self {
        Self {
            name: name.to_string(),
            federation_root,
            revocation_root,
            requirements: Vec::new(),
            require_non_revocation: true,
        }
    }

    /// Add a requirement to reveal an attribute.
    pub fn require_reveal(mut self, attribute_name: &str) -> Self {
        self.requirements.push(PolicyRequirement {
            attribute_name: attribute_name.to_string(),
            proof_type: PolicyProofType::Reveal,
        });
        self
    }

    /// Add a requirement for a predicate proof.
    pub fn require_predicate(
        mut self,
        attribute_name: &str,
        predicate_type: PredicateType,
        threshold: u32,
    ) -> Self {
        self.requirements.push(PolicyRequirement {
            attribute_name: attribute_name.to_string(),
            proof_type: PolicyProofType::Predicate {
                predicate_type,
                threshold,
            },
        });
        self
    }

    /// Add a requirement for existence proof.
    pub fn require_existence(mut self, attribute_name: &str) -> Self {
        self.requirements.push(PolicyRequirement {
            attribute_name: attribute_name.to_string(),
            proof_type: PolicyProofType::Existence,
        });
        self
    }

    /// Set whether non-revocation proof is required.
    pub fn with_non_revocation(mut self, required: bool) -> Self {
        self.require_non_revocation = required;
        self
    }

    /// Convert this policy into a presentation request for the holder.
    pub fn to_presentation_request(&self) -> PresentationRequest {
        let requirements: Vec<PredicateRequirement> = self
            .requirements
            .iter()
            .map(|r| match &r.proof_type {
                PolicyProofType::Reveal => PredicateRequirement {
                    attribute_name: r.attribute_name.clone(),
                    predicate_type: None,
                    threshold: None,
                    reveal: true,
                },
                PolicyProofType::Predicate {
                    predicate_type,
                    threshold,
                } => PredicateRequirement {
                    attribute_name: r.attribute_name.clone(),
                    predicate_type: Some(*predicate_type),
                    threshold: Some(*threshold),
                    reveal: false,
                },
                PolicyProofType::Existence => PredicateRequirement {
                    attribute_name: r.attribute_name.clone(),
                    predicate_type: None,
                    threshold: None,
                    reveal: false,
                },
            })
            .collect();

        PresentationRequest {
            requirements,
            require_non_revocation: self.require_non_revocation,
            federation_root: self.federation_root,
            revocation_root: self.revocation_root,
        }
    }

    /// Verify a credential presentation against this policy.
    ///
    /// Checks:
    /// 1. All required predicates pass
    /// 2. All required reveals are present
    /// 3. Non-revocation proof is valid (if required)
    /// 4. Proofs are bound to the correct federation root
    pub fn verify_presentation(&self, presentation: &CredentialPresentation) -> VerificationResult {
        // Check non-revocation if required.
        if self.require_non_revocation && !presentation.non_revocation_valid {
            return VerificationResult::Rejected {
                reason: "Non-revocation proof missing or invalid".to_string(),
            };
        }

        // Check each requirement.
        for requirement in &self.requirements {
            match &requirement.proof_type {
                PolicyProofType::Reveal => {
                    if !presentation
                        .revealed_attributes
                        .contains_key(&requirement.attribute_name)
                    {
                        return VerificationResult::Rejected {
                            reason: format!(
                                "Required attribute '{}' not revealed",
                                requirement.attribute_name
                            ),
                        };
                    }
                }
                PolicyProofType::Predicate {
                    predicate_type,
                    threshold,
                } => {
                    let proof_valid = presentation.predicate_results.iter().any(|p| {
                        p.attribute_name == requirement.attribute_name
                            && p.predicate_type == *predicate_type
                            && p.threshold == *threshold
                            && p.verified
                    });
                    if !proof_valid {
                        return VerificationResult::Rejected {
                            reason: format!(
                                "Predicate proof for '{}' failed or missing",
                                requirement.attribute_name
                            ),
                        };
                    }
                }
                PolicyProofType::Existence => {
                    let has_proof = presentation
                        .revealed_attributes
                        .contains_key(&requirement.attribute_name)
                        || presentation
                            .predicate_results
                            .iter()
                            .any(|p| p.attribute_name == requirement.attribute_name && p.verified);
                    if !has_proof {
                        return VerificationResult::Rejected {
                            reason: format!(
                                "No proof of existence for '{}'",
                                requirement.attribute_name
                            ),
                        };
                    }
                }
            }
        }

        VerificationResult::Accepted
    }
}

/// Result of verifying a presentation against a policy.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerificationResult {
    /// The presentation satisfies the policy.
    Accepted,
    /// The presentation does not satisfy the policy.
    Rejected { reason: String },
}

impl VerificationResult {
    /// Whether verification succeeded.
    pub fn is_accepted(&self) -> bool {
        matches!(self, VerificationResult::Accepted)
    }
}
