//! Presentation builder: selective disclosure, predicate proofs, and composition.
//!
//! The presentation layer allows a holder to:
//! - Selectively disclose specific attributes from a credential
//! - Prove predicates about hidden attributes (e.g., age >= 18)
//! - Compose proofs from multiple credentials into a single presentation
//! - Attach non-revocation proofs

use crate::credential::Credential;
use crate::revocation::NonRevocationProof;
use crate::{AttributeName, AttributeValue};
use pyana_circuit::dsl::predicates::{
    PredicateProof, PredicateType, PredicateWitness, prove_predicate_dsl, verify_predicate_dsl,
};
use pyana_circuit::field::BabyBear;
use pyana_dsl_runtime::revocation::{
    DslRevocationTree, generate_non_revocation_trace, non_revocation_dsl_circuit,
};
use std::collections::BTreeMap;

/// A request from a verifier specifying what must be proven.
#[derive(Clone, Debug)]
pub struct PresentationRequest {
    /// Requirements the holder must satisfy.
    pub requirements: Vec<PredicateRequirement>,
    /// Whether non-revocation proof is required.
    pub require_non_revocation: bool,
    /// The federation root the verifier trusts.
    pub federation_root: BabyBear,
    /// The revocation root for non-revocation proofs.
    pub revocation_root: BabyBear,
}

/// A single predicate requirement in a presentation request.
#[derive(Clone, Debug)]
pub struct PredicateRequirement {
    /// The attribute to prove about.
    pub attribute_name: String,
    /// The predicate type (None means reveal only).
    pub predicate_type: Option<PredicateType>,
    /// The threshold for comparison predicates.
    pub threshold: Option<u32>,
    /// Whether to reveal the attribute in plaintext.
    pub reveal: bool,
}

/// A completed credential presentation (the holder's response to a request).
#[derive(Clone, Debug)]
pub struct CredentialPresentation {
    /// Attributes revealed in plaintext (selective disclosure).
    pub revealed_attributes: BTreeMap<AttributeName, AttributeValue>,
    /// Results of predicate proofs.
    pub predicate_results: Vec<PredicateResult>,
    /// Whether non-revocation was proven valid.
    pub non_revocation_valid: bool,
    /// The credential IDs involved (opaque to verifier in anonymous mode).
    pub credential_ids: Vec<[u8; 32]>,
}

/// Result of a single predicate proof within a presentation.
#[derive(Clone, Debug)]
pub struct PredicateResult {
    /// The attribute proven about.
    pub attribute_name: String,
    /// The type of predicate.
    pub predicate_type: PredicateType,
    /// The threshold used.
    pub threshold: u32,
    /// Whether the proof verified successfully.
    pub verified: bool,
    /// The STARK proof (if generated).
    pub proof: Option<PredicateProof>,
}

/// Builder for constructing credential presentations.
pub struct PresentationBuilder {
    /// Credentials being used in this presentation.
    credentials: Vec<Credential>,
    /// Attributes to reveal.
    reveals: Vec<(usize, String)>,
    /// Predicate proofs to generate.
    predicates: Vec<(usize, String, PredicateType, u32)>,
    /// Non-revocation proof data.
    non_revocation: Option<NonRevocationProof>,
}

impl PresentationBuilder {
    /// Create a new presentation builder.
    pub fn new() -> Self {
        Self {
            credentials: Vec::new(),
            reveals: Vec::new(),
            predicates: Vec::new(),
            non_revocation: None,
        }
    }

    /// Add a credential to the presentation.
    /// Returns the index of the credential for referencing in reveals/predicates.
    pub fn add_credential(&mut self, credential: Credential) -> usize {
        let idx = self.credentials.len();
        self.credentials.push(credential);
        idx
    }

    /// Mark an attribute for selective disclosure (reveal in plaintext).
    pub fn reveal_attribute(&mut self, credential_idx: usize, attribute_name: &str) {
        self.reveals
            .push((credential_idx, attribute_name.to_string()));
    }

    /// Add a predicate proof requirement.
    pub fn add_predicate(
        &mut self,
        credential_idx: usize,
        attribute_name: &str,
        predicate_type: PredicateType,
        threshold: u32,
    ) {
        self.predicates.push((
            credential_idx,
            attribute_name.to_string(),
            predicate_type,
            threshold,
        ));
    }

    /// Attach a non-revocation proof.
    pub fn set_non_revocation(&mut self, proof: NonRevocationProof) {
        self.non_revocation = Some(proof);
    }

    /// Build the presentation, generating all required proofs.
    pub fn build(self) -> Option<CredentialPresentation> {
        let mut revealed_attributes = BTreeMap::new();
        let mut predicate_results = Vec::new();

        // Process reveals.
        for (cred_idx, attr_name) in &self.reveals {
            if let Some(cred) = self.credentials.get(*cred_idx) {
                if let Some(value) = cred.get_attribute(attr_name) {
                    revealed_attributes.insert(attr_name.clone(), value.clone());
                }
            }
        }

        // Process predicate proofs.
        for (cred_idx, attr_name, pred_type, threshold) in &self.predicates {
            if let Some(cred) = self.credentials.get(*cred_idx) {
                let result = generate_predicate_proof(cred, attr_name, *pred_type, *threshold);
                predicate_results.push(result);
            } else {
                predicate_results.push(PredicateResult {
                    attribute_name: attr_name.to_string(),
                    predicate_type: *pred_type,
                    threshold: *threshold,
                    verified: false,
                    proof: None,
                });
            }
        }

        let non_revocation_valid = self.non_revocation.as_ref().is_some_and(|p| p.is_valid);

        let credential_ids = self.credentials.iter().map(|c| c.id).collect();

        Some(CredentialPresentation {
            revealed_attributes,
            predicate_results,
            non_revocation_valid,
            credential_ids,
        })
    }
}

impl Default for PresentationBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Generate a predicate proof for a credential attribute.
fn generate_predicate_proof(
    credential: &Credential,
    attr_name: &str,
    predicate_type: PredicateType,
    threshold: u32,
) -> PredicateResult {
    let private_value = match credential.get_attribute_field(attr_name) {
        Some(v) => v,
        None => {
            return PredicateResult {
                attribute_name: attr_name.to_string(),
                predicate_type,
                threshold,
                verified: false,
                proof: None,
            };
        }
    };

    let fact_commitment = match credential.attribute_fact_commitment(attr_name) {
        Some(c) => c,
        None => {
            return PredicateResult {
                attribute_name: attr_name.to_string(),
                predicate_type,
                threshold,
                verified: false,
                proof: None,
            };
        }
    };

    let threshold_field = BabyBear::new(threshold);

    let witness = PredicateWitness {
        private_value,
        threshold: threshold_field,
        predicate_type,
        fact_commitment,
        blinding: None,
        fact_hash: credential.attribute_fact_hash(attr_name),
        state_root: Some(credential.commitment),
    };

    // Check satisfiability first via comparison.
    let satisfiable = match witness.predicate_type {
        PredicateType::Gte | PredicateType::InRangeLow => {
            witness.private_value >= witness.threshold
        }
        PredicateType::Lte | PredicateType::InRangeHigh => {
            witness.private_value <= witness.threshold
        }
        PredicateType::Gt => witness.private_value > witness.threshold,
        PredicateType::Lt => witness.private_value < witness.threshold,
        PredicateType::Neq => witness.private_value != witness.threshold,
    };
    if !satisfiable {
        return PredicateResult {
            attribute_name: attr_name.to_string(),
            predicate_type,
            threshold,
            verified: false,
            proof: None,
        };
    }

    // Generate the STARK proof using the DSL predicate circuit.
    let proof = prove_predicate_dsl(&witness).ok();
    let verified = proof
        .as_ref()
        .is_some_and(|p| verify_predicate_dsl(p, threshold_field, fact_commitment).is_ok());

    PredicateResult {
        attribute_name: attr_name.to_string(),
        predicate_type,
        threshold,
        verified,
        proof,
    }
}

/// Generate a non-revocation proof for a credential using the DSL circuit.
///
/// Proves that the credential's revocation hash does NOT appear in the
/// given revocation tree. Uses the 30-bit range check DSL circuit (sound).
pub fn prove_non_revocation(
    credential: &Credential,
    revocation_tree: &DslRevocationTree,
) -> NonRevocationProof {
    let witness = match revocation_tree.prove_non_membership(&credential.revocation_hash) {
        Some(w) => w,
        None => {
            return NonRevocationProof {
                revocation_root: revocation_tree.root(),
                is_valid: false,
            };
        }
    };

    let root = revocation_tree.root();
    let (trace, public_inputs) = generate_non_revocation_trace(&witness, root);
    let circuit = non_revocation_dsl_circuit();
    let proof = pyana_circuit::stark::prove(&circuit, &trace, &public_inputs);

    // Verify the generated proof.
    let is_valid = pyana_circuit::stark::verify(&circuit, &proof, &public_inputs).is_ok();

    NonRevocationProof {
        revocation_root: root,
        is_valid,
    }
}

/// Compose multiple credential presentations into a single combined presentation.
///
/// This is used when a verifier requires proofs from multiple credentials
/// (e.g., government ID + employment cert + bank statement).
pub fn compose_presentations(presentations: Vec<CredentialPresentation>) -> CredentialPresentation {
    let mut revealed_attributes = BTreeMap::new();
    let mut predicate_results = Vec::new();
    let mut credential_ids = Vec::new();
    let mut all_non_revocation_valid = true;

    for p in presentations {
        revealed_attributes.extend(p.revealed_attributes);
        predicate_results.extend(p.predicate_results);
        credential_ids.extend(p.credential_ids);
        if !p.non_revocation_valid {
            all_non_revocation_valid = false;
        }
    }

    CredentialPresentation {
        revealed_attributes,
        predicate_results,
        non_revocation_valid: all_non_revocation_valid,
        credential_ids,
    }
}
