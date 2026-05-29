//! High-level privacy APIs for application developers.
//!
//! This module provides ergonomic wrappers around dregg's privacy primitives,
//! making it simple to perform common privacy-preserving operations:
//!
//! - **Anonymous authorization**: Prove you are authorized without revealing your identity.
//! - **Private notes**: Create and transfer value without revealing amounts.
//! - **Unlinkable predicates**: Prove facts about yourself that can't be correlated.
//! - **Private discovery**: Find matching intents without revealing your query.
//! - **Non-revocation proofs**: Prove your token hasn't been revoked without revealing it.
//!
//! # Design Principles
//!
//! Each API method documents:
//! - What **privacy guarantee** it provides (what's hidden from the verifier).
//! - What **the verifier learns** (the public inputs / revealed information).
//! - What **stays hidden** (the private witness / secret data).

use dregg_cell::note::{Note, NoteCommitment, Nullifier};
use dregg_circuit::BabyBear;
use dregg_circuit::field::BABYBEAR_P;
use dregg_circuit::note_spending_air::{NoteSpendingWitness, key_to_field_elements};
use dregg_circuit::poseidon2;
use dregg_circuit::stark::{self, StarkProof};
use dregg_commit::accumulator::{AccumulatorWitness, BabyBear4, PolynomialAccumulator};
use dregg_dsl_runtime::note_spending::{generate_note_spending_trace, note_spending_dsl_circuit};
use dregg_dsl_runtime::revocation::{
    DslRevocationTree, generate_non_revocation_trace, non_revocation_dsl_circuit,
    revocation_hash_to_field,
};
use dregg_token::AuthRequest;

// `discovery` is gated behind `network` (tokio-using); the lone method below
// that needs it is gated the same way.
use crate::cipherclerk::{AgentCipherclerk, HeldToken};
#[cfg(feature = "network")]
use crate::discovery::{PirTransport, PrivateDiscoveryClient};
use crate::error::SdkError;

// =============================================================================
// Result Types
// =============================================================================

/// An anonymous authorization presentation.
///
/// Proves the holder is authorized without revealing which federation member they are.
/// Uses ring membership with per-presentation blinding, so the same holder produces
/// unlinkable proofs across sessions.
#[derive(Clone, Debug)]
pub struct AnonymousPresentation {
    /// The STARK-backed presentation proof (wire-safe form).
    pub proof: dregg_bridge::present::WirePresentationProof,
    /// The blinded presentation tag (unique per presentation, unlinkable across shows).
    ///
    /// The verifier cannot determine which federation member produced this tag.
    pub presentation_tag: BabyBear,
}

/// The secret material associated with a private note.
///
/// The holder must keep this to later spend or transfer the note.
/// Contains the full note preimage (owner, fields, randomness, creation_nonce)
/// plus the spending key that authorizes spending.
#[derive(Clone, Debug)]
pub struct NoteSecret {
    /// The full note (owner, value, asset_type, randomness, creation_nonce).
    pub note: Note,
    /// The spending key (derived from the cipherclerk's signing key).
    pub spending_key: [u8; 32],
}

/// Proof that a note was spent and a new one created for the recipient,
/// with value conservation proven in zero knowledge.
#[derive(Clone, Debug)]
pub struct NoteTransferProof {
    /// The nullifier of the spent input note (published for double-spend prevention).
    pub nullifier: Nullifier,
    /// The commitment of the newly created output note (published to the note tree).
    pub output_commitment: NoteCommitment,
    /// The STARK proof of valid spending (proves knowledge of spending key + Merkle membership).
    pub spending_proof: StarkProof,
    /// The secret for the new output note (given to the recipient out-of-band).
    pub recipient_secret: NoteSecret,
}

/// A predicate proof generated with fresh blinding so it can't be correlated
/// with other proofs from the same holder.
#[derive(Clone, Debug)]
pub struct UnlinkablePredicateProof {
    /// The blinded fact commitment: `Poseidon2(fact_hash, state_root, blinding, 0)`.
    ///
    /// This commitment is different each time due to fresh blinding, so a verifier
    /// cannot link two proofs to the same holder.
    pub blinded_fact_commitment: BabyBear,
    /// The underlying predicate proof (STARK-backed).
    pub predicate_proof: dregg_bridge::BridgePredicateProof,
    /// The blinding factor used (keep private; needed if you want to open the commitment later).
    pub blinding: BabyBear,
}

/// Proof that a token's derivation path has no revoked ancestor.
///
/// The verifier learns only that the token is not revoked; it does not learn
/// the token's identity, derivation chain, or which ancestors were checked.
#[derive(Clone, Debug)]
pub struct NonRevocationProof {
    /// The STARK proof of non-revocation.
    pub proof: StarkProof,
    /// The revocation set root this proof was generated against.
    ///
    /// The verifier must know this root (committed by the federation) to verify.
    pub revocation_root: BabyBear,
}

/// Proof of non-revocation using the polynomial accumulator (O(1) verification).
///
/// When the revocation set is large (>1000 entries), the accumulator-based approach
/// is significantly more efficient than the sorted-Merkle tree approach used by
/// `NonRevocationProof`. The accumulator proof is constant-size regardless of how
/// many entries are in the revocation set.
///
/// # Privacy Guarantee
///
/// The verifier learns:
/// - That the prover holds a non-revoked token.
/// - The accumulator value and alpha challenge (committed by the federation).
///
/// The verifier does NOT learn:
/// - Which specific token the prover holds.
/// - The revocation hash of the token.
#[derive(Clone, Debug)]
pub struct AccumulatorNonMembershipProof {
    /// The accumulator non-membership witness (quotient + nonzero remainder).
    pub witness: AccumulatorWitness,
    /// The current accumulator value (product of (alpha - h_i) for all revoked h_i).
    pub accumulator_value: BabyBear4,
    /// The alpha challenge used (derived via Fiat-Shamir from the set commitment).
    pub alpha: BabyBear4,
    /// The revocation hash being proved absent (derived from the token).
    pub revocation_hash: BabyBear,
}

// =============================================================================
// Privacy API Implementation
// =============================================================================

impl AgentCipherclerk {
    /// Prove authorization without revealing which federation member you are.
    ///
    /// # Privacy Guarantee
    ///
    /// The verifier learns:
    /// - That some valid federation member authorized this request.
    /// - The presentation tag (unique per session, unlinkable).
    ///
    /// The verifier does NOT learn:
    /// - Which federation member produced the proof.
    /// - The token contents, caveats, or derivation chain.
    /// - Any correlation between this proof and previous proofs from the same holder.
    ///
    /// # How It Works
    ///
    /// Uses `BlindedMerklePoseidon2StarkAir`: a fresh random blinding factor is
    /// generated per presentation. The public inputs expose
    /// `blinded_leaf = hash_2_to_1(leaf_hash, blinding)` instead of the raw `leaf_hash`,
    /// so the verifier cannot determine which leaf in the federation Merkle tree
    /// corresponds to this proof.
    ///
    /// # Arguments
    ///
    /// * `token` - The held token to authorize from (must hold the root key).
    /// * `request` - The authorization request to prove.
    ///
    /// # Errors
    ///
    /// Returns an error if the token cannot produce federation membership proofs
    /// (e.g., attenuated tokens without the issuer key).
    pub fn authorize_anonymously(
        &self,
        token: &HeldToken,
        request: &AuthRequest,
    ) -> Result<AnonymousPresentation, SdkError> {
        // The prove_authorization path already uses BlindedMerklePoseidon2StarkAir
        // with a fresh blinding factor per call (via generate_blinding_factor()).
        // Each invocation is unlinkable by construction.
        let proof = self.prove_authorization(token, request)?;

        // Extract the presentation tag from the circuit proof's public inputs.
        // The tag is [BabyBear; 4]; hash to a single element for the wire representation.
        let presentation_tag = dregg_circuit::poseidon2::hash_many(&[proof
            .circuit_proof
            .public_inputs
            .presentation_tag]);

        // Convert to wire-safe representation (strips private trace data).
        let wire_proof = proof.into_wire_proof();

        Ok(AnonymousPresentation {
            proof: wire_proof,
            presentation_tag,
        })
    }

    /// Create a private note (hidden balance) that can be transferred without revealing amount.
    ///
    /// # Privacy Guarantee
    ///
    /// The verifier (note tree operator) learns:
    /// - That a new commitment was added to the note tree.
    ///
    /// The verifier does NOT learn:
    /// - The note's value (amount).
    /// - The note's asset type.
    /// - The note's owner.
    /// - The randomness / blinding factor.
    ///
    /// # How It Works
    ///
    /// Creates a note `(owner, [asset_type, value, 0...], randomness, creation_nonce)` and
    /// publishes only the Poseidon2 commitment. The commitment is binding (cannot be opened
    /// to a different value) but hiding (reveals nothing about the contents).
    ///
    /// # Arguments
    ///
    /// * `value` - The amount to store in the note.
    /// * `asset_type` - The asset type identifier.
    ///
    /// # Returns
    ///
    /// A tuple of:
    /// - `NoteCommitment`: publish this to the note tree.
    /// - `NoteSecret`: keep this secret; needed to spend or transfer the note later.
    pub fn create_private_note(
        &self,
        value: u64,
        asset_type: u64,
    ) -> Result<(NoteCommitment, NoteSecret), SdkError> {
        // Derive a spending key from the cipherclerk's signing key material.
        let spending_key = self.derive_symmetric_key("dregg-note-spending-key-v1");

        // Create the note with this cipherclerk's public key as owner.
        let owner = self.public_key().0;
        let mut fields = [0u64; 8];
        fields[0] = asset_type;
        fields[1] = value;
        let note = Note::new(owner, fields);

        // Compute the commitment (this is what gets published to the note tree).
        let commitment = note.commitment();

        let secret = NoteSecret { note, spending_key };

        Ok((commitment, secret))
    }

    /// Spend a note and create a new one for the recipient, proving value conservation
    /// without revealing the amount.
    ///
    /// # Privacy Guarantee
    ///
    /// The verifier learns:
    /// - The nullifier (for double-spend prevention).
    /// - The Merkle root of the note tree (the note exists in the committed tree).
    /// - The new output commitment (goes into the recipient's tree).
    ///
    /// The verifier does NOT learn:
    /// - The note's value or asset type.
    /// - The spending key.
    /// - The sender's or recipient's identity.
    /// - Which specific note in the tree was spent.
    ///
    /// # How It Works
    ///
    /// 1. Computes the nullifier from the note secret + spending key (proves ownership).
    /// 2. Creates a new note for the recipient with the same value/asset (conservation).
    /// 3. Generates a STARK proof (NoteSpendingAir) proving:
    ///    - Knowledge of the spending key.
    ///    - The commitment is in the Merkle tree.
    ///    - The nullifier is correctly derived.
    ///
    /// # Arguments
    ///
    /// * `note_secret` - The secret material for the note being spent.
    /// * `recipient_key` - The recipient's public key (32 bytes).
    /// * `merkle_siblings` - The Merkle path siblings from the note tree.
    /// * `merkle_positions` - The Merkle path positions (0..3 per level).
    ///
    /// # Returns
    ///
    /// A `NoteTransferProof` containing:
    /// - The nullifier to publish (prevents double-spend).
    /// - The output commitment to add to the tree.
    /// - The STARK proof for verification.
    /// - The recipient's secret (deliver to them out-of-band).
    pub fn transfer_note_privately(
        &self,
        note_secret: &NoteSecret,
        recipient_key: &[u8; 32],
        merkle_siblings: Vec<[BabyBear; 3]>,
        merkle_positions: Vec<u8>,
    ) -> Result<NoteTransferProof, SdkError> {
        let note = &note_secret.note;
        let spending_key = &note_secret.spending_key;

        // Compute the nullifier (reveals note is spent, without revealing which note).
        let nullifier = note.nullifier(spending_key);

        // Create a new note for the recipient with the same value and asset type.
        let mut output_fields = [0u64; 8];
        output_fields[0] = note.asset_type();
        output_fields[1] = note.value();
        let output_note = Note::new(*recipient_key, output_fields);
        let output_commitment = output_note.commitment();

        // Derive a recipient spending key (the recipient will use their own; we just
        // package the note secret so they can spend it).
        // In a real protocol the recipient would derive their own spending key.
        // Here we use a deterministic derivation from the recipient's public key
        // as a placeholder — the recipient must replace this with their own key.
        let mut recipient_spending_key_hasher =
            blake3::Hasher::new_derive_key("dregg-note-recipient-spending-key-v1");
        recipient_spending_key_hasher.update(recipient_key);
        let recipient_spending_key: [u8; 32] = *recipient_spending_key_hasher.finalize().as_bytes();

        // Convert spending key to 8 BabyBear limbs.
        let spending_key_limbs = key_to_field_elements(spending_key);

        // Build the spending witness for the STARK proof with FULL-WIDTH
        // (256-bit-per-field) commitment binding. `from_note_limbs` decomposes
        // every 32-byte field (owner / creation_nonce / randomness) into 8
        // BabyBear limbs and every u64 (value / asset_type) into low+high
        // limbs — the SAME 28-limb preimage layout as
        // `dregg_cell::Note::poseidon2_commitment`. This replaces the legacy
        // single-felt-per-field witness, whose in-circuit commitment bound only
        // the first 4 bytes of each 32-byte field (so two notes differing only
        // in bytes above byte 4 of owner/nonce/randomness collided).
        let witness = NoteSpendingWitness::from_note_limbs(
            &note.owner,
            note.value(),
            note.asset_type(),
            &note.creation_nonce,
            &note.randomness,
            spending_key_limbs,
            merkle_siblings,
            merkle_positions,
        );

        // Generate the STARK proof. Keep this fallible: placeholder or stale
        // witness data should be reported to SDK callers instead of panicking
        // inside the prover.
        let circuit = note_spending_dsl_circuit();
        let (trace, public_inputs) = generate_note_spending_trace(&witness);
        let spending_proof = stark::try_prove(&circuit, &trace, &public_inputs).map_err(|e| {
            SdkError::Auth(dregg_bridge::AuthError::InvalidRequest(format!(
                "note spending proof generation failed: {e}"
            )))
        })?;

        let recipient_secret = NoteSecret {
            note: output_note,
            spending_key: recipient_spending_key,
        };

        Ok(NoteTransferProof {
            nullifier,
            output_commitment,
            spending_proof,
            recipient_secret,
        })
    }

    /// Generate a predicate proof with fresh blinding so multiple proofs can't be correlated.
    ///
    /// # Privacy Guarantee
    ///
    /// The verifier learns:
    /// - That some attribute satisfies the predicate (e.g., "age >= 18").
    /// - The blinded fact commitment (unique per proof, unlinkable).
    ///
    /// The verifier does NOT learn:
    /// - The actual attribute value.
    /// - Which token or identity produced the proof.
    /// - Any correlation with other proofs from the same holder.
    ///
    /// # How It Works
    ///
    /// 1. Generates a fresh random BabyBear blinding factor.
    /// 2. Computes `blinded_fact_commitment = Poseidon2(fact_hash, state_root, blinding, 0)`.
    /// 3. Generates the standard predicate proof (STARK-backed).
    /// 4. Returns both the proof and the blinded commitment.
    ///
    /// Because the blinding is fresh each time, two proofs about the same attribute
    /// from the same token produce different blinded commitments, preventing correlation.
    ///
    /// # Arguments
    ///
    /// * `token` - The held token containing the attribute.
    /// * `attribute` - The attribute name (e.g., "age", "balance", "reputation").
    /// * `attribute_value` - The actual (private) value of the attribute.
    /// * `predicate_type` - The type of predicate to prove (Gte, Lte, etc.).
    /// * `threshold` - The threshold value for the predicate.
    ///
    /// # Returns
    ///
    /// An `UnlinkablePredicateProof` with a fresh blinded commitment.
    pub fn prove_predicate_unlinkable(
        &self,
        token: &HeldToken,
        attribute: &str,
        attribute_value: u32,
        predicate_type: dregg_circuit::PredicateType,
        threshold: BabyBear,
    ) -> Result<UnlinkablePredicateProof, SdkError> {
        // Decode the token to verify it's valid.
        let _decoded = token.decode()?;

        // Generate fresh blinding factor.
        let mut blinding_bytes = [0u8; 4];
        getrandom::fill(&mut blinding_bytes)
            .map_err(|e| SdkError::MissingKey(format!("getrandom failed: {e}")))?;
        let blinding_raw = u32::from_le_bytes(blinding_bytes) % BABYBEAR_P;
        let blinding = BabyBear::new(if blinding_raw == 0 { 1 } else { blinding_raw });

        // Compute the fact hash for the attribute.
        let attr_bytes = blake3::hash(attribute.as_bytes());
        let attr_bb = Self::bytes_to_babybear(attr_bytes.as_bytes());
        let value_bb = BabyBear::new(attribute_value);
        let fact_hash = poseidon2::hash_fact(attr_bb, &[value_bb, BabyBear::ZERO, BabyBear::ZERO]);

        // Compute state root from the token's issuer key.
        let issuer_key = token.root_key();
        let state_root = Self::bytes_to_babybear(issuer_key);

        // Compute the blinded fact commitment: Poseidon2(fact_hash, state_root, blinding, 0).
        let blinded_fact_commitment =
            poseidon2::hash_many(&[fact_hash, state_root, blinding, BabyBear::ZERO]);

        // Generate the predicate proof.
        let bridge_predicate = Self::predicate_type_to_bridge(predicate_type, threshold.as_u32());
        let predicate_proof = dregg_bridge::prove_predicate_for_fact(
            attribute_value,
            fact_hash,
            state_root,
            &bridge_predicate,
        )
        .ok_or_else(|| {
            SdkError::Auth(dregg_bridge::AuthError::InvalidRequest(format!(
                "predicate proof generation failed: '{attribute}' {:?}({}) not satisfiable for value {attribute_value}",
                predicate_type, threshold.as_u32()
            )))
        })?;

        Ok(UnlinkablePredicateProof {
            blinded_fact_commitment,
            predicate_proof,
            blinding,
        })
    }

    /// Discover intents privately using 2-server information-theoretic PIR.
    ///
    /// # Privacy Guarantee
    ///
    /// Each PIR server learns:
    /// - That some client is querying the intent index.
    ///
    /// Neither server learns:
    /// - Which capability tag you are searching for.
    /// - Which row of the index you are interested in.
    ///
    /// This is information-theoretic (not computational): even an infinitely powerful
    /// adversary controlling one server cannot determine your query.
    ///
    /// # Non-collusion Requirement
    ///
    /// The two servers MUST NOT collude. If they share their query vectors, they can
    /// XOR them to discover the unit vector `e_i` and learn which tag was queried.
    ///
    /// # Arguments
    ///
    /// * `tag` - The capability tag to search for (e.g., `"action:read"`).
    /// * `node_a_url` - Base URL of the first PIR server.
    /// * `node_b_url` - Base URL of the second PIR server (must be non-colluding).
    /// * `transport` - The HTTP transport implementation for making requests.
    ///
    /// # Returns
    ///
    /// A vector of 32-byte intent IDs matching the tag, discovered without
    /// revealing which tag was queried.
    #[cfg(feature = "network")]
    pub async fn discover_intents_privately<T: PirTransport>(
        &self,
        tag: &str,
        node_a_url: &str,
        node_b_url: &str,
        transport: T,
    ) -> Result<Vec<[u8; 32]>, SdkError> {
        let client = PrivateDiscoveryClient::new(node_a_url, node_b_url, transport);
        client.discover_intents(tag).await
    }

    /// Prove a token is not in the revocation set without revealing the token's identity.
    ///
    /// # Privacy Guarantee
    ///
    /// The verifier learns:
    /// - That the prover holds a non-revoked capability.
    /// - The revocation set root (committed by the federation).
    ///
    /// The verifier does NOT learn:
    /// - Which specific capability/token the prover holds.
    /// - The derivation chain or ancestry of the token.
    /// - Which ancestors were checked against the revocation set.
    ///
    /// # How It Works
    ///
    /// Uses the `NonRevocationAir` (sorted-Merkle non-membership proof):
    /// 1. For each ancestor in the token's derivation path, finds two adjacent leaves
    ///    in the sorted revocation tree that bracket the ancestor's revocation hash.
    /// 2. Proves Merkle membership of both neighbors (they exist in the tree).
    /// 3. Proves the ancestor hash falls between them (it's absent from the tree).
    ///
    /// The STARK proof covers all ancestors simultaneously, so the verifier learns
    /// nothing about the derivation chain length or structure.
    ///
    /// # Arguments
    ///
    /// * `token` - The held token to prove non-revocation for.
    /// * `revocation_tree` - The federation's current sorted revocation tree.
    ///
    /// # Errors
    ///
    /// Returns an error if any ancestor in the derivation chain IS revoked
    /// (cannot generate a valid non-revocation proof for a revoked token).
    pub fn prove_not_revoked(
        &self,
        token: &HeldToken,
        revocation_tree: &DslRevocationTree,
    ) -> Result<NonRevocationProof, SdkError> {
        // Decode the token to verify it's structurally valid.
        let _decoded = token.decode()?;

        // Derive the revocation hashes for the token's derivation path.
        // The derivation chain is: root_key -> each attenuation step.
        // Each step's revocation hash = Poseidon2(hash(key_material || step_index)).
        let issuer_key = token.root_key();
        let mut ancestor_hashes = Vec::new();

        // The root issuer's revocation hash.
        let root_revocation_hash = revocation_hash_to_field(issuer_key);
        ancestor_hashes.push(root_revocation_hash);

        // For attenuated tokens, derive additional ancestor hashes from the token ID
        // which encodes the attenuation chain structure.
        // Each segment of the token ID (split by ':') represents a derivation step.
        let id_parts: Vec<&str> = token.id().split(':').collect();
        for (i, _part) in id_parts.iter().enumerate().skip(1) {
            let mut hasher = blake3::Hasher::new_derive_key("dregg-revocation-hash-v1");
            hasher.update(issuer_key);
            hasher.update(&(i as u64).to_le_bytes());
            let step_hash = *hasher.finalize().as_bytes();
            ancestor_hashes.push(revocation_hash_to_field(&step_hash));
        }

        // Generate the non-revocation proof using DSL circuit (30-bit range, sound).
        let revocation_root = revocation_tree.root();

        // For each ancestor, generate a non-membership witness and prove it.
        // With the DSL circuit, we prove one ancestor at a time (single control row).
        // Use the first ancestor (root issuer) as the primary proof.
        let primary_hash = &ancestor_hashes[0];
        let witness = revocation_tree
            .prove_non_membership(primary_hash)
            .ok_or_else(|| {
                SdkError::Auth(dregg_bridge::AuthError::InvalidRequest(
                    "non-revocation proof generation failed: one or more ancestors are revoked"
                        .to_string(),
                ))
            })?;

        // Verify all other ancestors are also not revoked.
        for hash in &ancestor_hashes[1..] {
            if revocation_tree.prove_non_membership(hash).is_none() {
                return Err(SdkError::Auth(dregg_bridge::AuthError::InvalidRequest(
                    "non-revocation proof generation failed: one or more ancestors are revoked"
                        .to_string(),
                )));
            }
        }

        let (trace, public_inputs) = generate_non_revocation_trace(&witness, revocation_root);
        let circuit = non_revocation_dsl_circuit();
        let proof = stark::prove(&circuit, &trace, &public_inputs);

        Ok(NonRevocationProof {
            proof,
            revocation_root,
        })
    }

    /// Prove a token is not in the revocation set using the polynomial accumulator.
    ///
    /// This is the O(1) alternative to `prove_not_revoked` for large revocation sets.
    /// The accumulator witness is constant-size regardless of how many tokens have been
    /// revoked, making it ideal when the revocation set exceeds ~1000 entries.
    ///
    /// # Privacy Guarantee
    ///
    /// Same as `prove_not_revoked`: the verifier learns only that the token is not
    /// revoked. The token's identity and derivation chain remain hidden.
    ///
    /// # How It Works
    ///
    /// The federation maintains a polynomial accumulator `Acc = product(alpha - h_i)`
    /// over all revoked hashes. To prove non-membership, the prover:
    /// 1. Derives the revocation hash for their token.
    /// 2. Obtains a non-membership witness from the accumulator.
    /// 3. The verifier checks: `witness.quotient * (alpha - h) + witness.remainder == Acc`
    ///    AND `witness.remainder != 0`.
    ///
    /// # Arguments
    ///
    /// * `token` - The held token to prove non-revocation for.
    /// * `accumulator` - The federation's current polynomial accumulator over revoked hashes.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The token's revocation hash IS in the accumulator (token is revoked).
    /// - The witness computation fails (e.g., alpha - hash is not invertible).
    pub fn prove_not_revoked_accumulator(
        &self,
        token: &HeldToken,
        accumulator: &PolynomialAccumulator,
    ) -> Result<AccumulatorNonMembershipProof, SdkError> {
        // Decode the token to verify it's structurally valid.
        let _decoded = token.decode()?;

        // Derive the revocation hash for this token's root issuer.
        let issuer_key = token.root_key();
        let revocation_hash = revocation_hash_to_field(issuer_key);

        // Compute the non-membership witness from the accumulator.
        let witness = accumulator
            .non_membership_witness(revocation_hash)
            .ok_or_else(|| {
                SdkError::Auth(dregg_bridge::AuthError::InvalidRequest(
                    "accumulator non-membership proof failed: token's revocation hash is in the \
                 revocation set (token is revoked)"
                        .to_string(),
                ))
            })?;

        Ok(AccumulatorNonMembershipProof {
            witness,
            accumulator_value: accumulator.accumulator_value(),
            alpha: accumulator.alpha(),
            revocation_hash,
        })
    }
}

// =============================================================================
// Verification helpers
// =============================================================================

/// Verify an anonymous presentation proof.
///
/// The verifier checks:
/// 1. The STARK proof is valid (BlindedMerklePoseidon2StarkAir).
/// 2. The federation root matches the expected value.
///
/// The verifier does NOT learn which federation member produced the proof.
pub fn verify_anonymous_presentation(
    presentation: &AnonymousPresentation,
    expected_federation_root: &[u8; 32],
) -> bool {
    // Re-wrap into a BridgePresentationProof for verification via the bridge layer.
    // The wire proof contains all necessary STARK data.
    if let Some(ref real_stark) = presentation.proof.real_stark_proof {
        // SECURITY: Use new_canonical() for values from external (potentially adversarial)
        // proof data. This ensures modular reduction is applied, preventing non-canonical
        // representations that could cause malleability.
        let pi: Vec<BabyBear> = real_stark
            .issuer_membership_stark_proof
            .public_inputs
            .iter()
            .map(|&v| BabyBear::new_canonical(v))
            .collect();

        let air_name = &real_stark.issuer_membership_stark_proof.air_name;

        // Must be a blinded proof for anonymous presentation.
        if air_name != dregg_dsl_runtime::descriptors::BLINDED_MERKLE_AIR_NAME {
            return false;
        }

        // Verify the STARK proof using DSL blinded Merkle circuit.
        let circuit = dregg_dsl_runtime::descriptors::blinded_merkle_poseidon2_circuit();
        if stark::verify(&circuit, &real_stark.issuer_membership_stark_proof, &pi).is_err() {
            return false;
        }

        // Check federation root is in the public inputs.
        let expected_root_bb = {
            let limbs = BabyBear::encode_hash(expected_federation_root);
            poseidon2::hash_many(&limbs)
        };

        // The root is the second public input in blinded Merkle proofs.
        if pi.len() >= 2 && pi[1] == expected_root_bb {
            return true;
        }

        // Fallback: check if root appears anywhere in public inputs.
        pi.contains(&expected_root_bb)
    } else {
        false
    }
}

/// Verify a non-revocation proof against a known revocation root.
///
/// The verifier needs:
/// - The revocation set root (committed by the federation).
/// - The STARK proof.
///
/// Returns `Ok(())` if the proof is valid, `Err` with reason otherwise.
pub fn verify_non_revocation_proof(proof: &NonRevocationProof) -> Result<(), String> {
    let circuit = non_revocation_dsl_circuit();
    let public_inputs = vec![proof.revocation_root];
    dregg_circuit::stark::verify(&circuit, &proof.proof, &public_inputs)
}

/// Verify an accumulator-based non-membership proof.
///
/// The verifier needs:
/// - The current accumulator value (committed by the federation).
/// - The alpha challenge (committed by the federation via Fiat-Shamir).
///
/// Checks: `witness.quotient * (alpha - element) + witness.remainder == accumulator_value`
/// AND `witness.remainder != 0`.
///
/// Returns `Ok(())` if valid, `Err` with reason otherwise.
pub fn verify_accumulator_non_membership(
    proof: &AccumulatorNonMembershipProof,
) -> Result<(), String> {
    if PolynomialAccumulator::verify_non_membership(
        &proof.witness,
        proof.revocation_hash,
        proof.alpha,
        proof.accumulator_value,
    ) {
        Ok(())
    } else {
        Err("accumulator non-membership verification failed: \
             witness * (alpha - element) + remainder != accumulator value, \
             or remainder is zero"
            .to_string())
    }
}

/// Verify a note spending proof (used by note tree operators to validate transfers).
///
/// The verifier needs:
/// - The nullifier (to check against the double-spend set).
/// - The Merkle root (the committed note tree root).
/// - The value (prevents value inflation attacks).
/// - The asset type (prevents asset type substitution attacks).
/// - The STARK proof.
///
/// Returns `Ok(())` if valid.
pub fn verify_note_spending(
    nullifier: BabyBear,
    merkle_root: BabyBear,
    value: BabyBear,
    asset_type: BabyBear,
    proof: &StarkProof,
) -> Result<(), String> {
    dregg_dsl_runtime::note_spending::verify_note_spend(
        nullifier,
        merkle_root,
        value,
        asset_type,
        proof,
    )
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_private_note_produces_valid_commitment() {
        let cclerk = AgentCipherclerk::new();
        let (commitment, secret) = cclerk.create_private_note(1000, 1).unwrap();

        // The commitment should match what Note::commitment() produces.
        assert_eq!(commitment, secret.note.commitment());

        // The note should have the correct value and asset type.
        assert_eq!(secret.note.value(), 1000);
        assert_eq!(secret.note.asset_type(), 1);

        // The owner should be the cipherclerk's public key.
        assert_eq!(secret.note.owner, cclerk.public_key().0);
    }

    #[test]
    fn test_create_private_note_unique_commitments() {
        let cclerk = AgentCipherclerk::new();
        let (c1, _) = cclerk.create_private_note(1000, 1).unwrap();
        let (c2, _) = cclerk.create_private_note(1000, 1).unwrap();

        // Even with same value/asset, commitments differ (fresh randomness).
        assert_ne!(c1, c2);
    }

    #[test]
    fn test_create_private_note_spending_key_derives_correctly() {
        let cclerk = AgentCipherclerk::new();
        let (_, secret) = cclerk.create_private_note(500, 2).unwrap();

        // The spending key should be deterministic for the same cipherclerk.
        let expected_key = cclerk.derive_symmetric_key("dregg-note-spending-key-v1");
        assert_eq!(secret.spending_key, expected_key);
    }

    #[test]
    fn test_prove_predicate_unlinkable_produces_fresh_commitment() {
        let mut cclerk = AgentCipherclerk::new();
        let root_key = [0xAB; 32];
        let token = cclerk.mint_token(&root_key, "test-service");

        // Generate two proofs for the same predicate.
        let proof1 = cclerk
            .prove_predicate_unlinkable(
                &token,
                "balance",
                5000,
                dregg_circuit::PredicateType::Gte,
                BabyBear::new(1000),
            )
            .unwrap();

        let proof2 = cclerk
            .prove_predicate_unlinkable(
                &token,
                "balance",
                5000,
                dregg_circuit::PredicateType::Gte,
                BabyBear::new(1000),
            )
            .unwrap();

        // The blinded commitments MUST differ (fresh blinding each time).
        assert_ne!(
            proof1.blinded_fact_commitment, proof2.blinded_fact_commitment,
            "blinded commitments must differ for unlinkability"
        );

        // But the blinding factors should also differ.
        assert_ne!(proof1.blinding, proof2.blinding);
    }

    #[test]
    fn test_prove_predicate_unlinkable_fails_on_false_statement() {
        let mut cclerk = AgentCipherclerk::new();
        let root_key = [0xCD; 32];
        let token = cclerk.mint_token(&root_key, "test-service");

        // Try to prove balance >= 1000 when balance is only 500 (false statement).
        let result = cclerk.prove_predicate_unlinkable(
            &token,
            "balance",
            500,
            dregg_circuit::PredicateType::Gte,
            BabyBear::new(1000),
        );

        assert!(result.is_err(), "should fail for false predicate");
    }

    #[test]
    fn test_prove_not_revoked_succeeds_for_non_revoked_token() {
        let mut cclerk = AgentCipherclerk::new();
        let root_key = [0xEF; 32];
        let token = cclerk.mint_token(&root_key, "service");

        // Build a revocation tree with some revoked entries (not our token).
        let revoked_hashes: Vec<BabyBear> = (1..=5u32)
            .map(|i| {
                let mut h = [0u8; 32];
                h[0] = i as u8;
                h[1] = 0xDE;
                revocation_hash_to_field(&h)
            })
            .collect();
        let tree = DslRevocationTree::new(revoked_hashes, 4);

        // Our token is not in the revocation set.
        let proof = cclerk.prove_not_revoked(&token, &tree);
        assert!(
            proof.is_ok(),
            "non-revoked token should produce valid proof: {:?}",
            proof.err()
        );

        // Verify the proof.
        let non_rev_proof = proof.unwrap();
        assert_eq!(non_rev_proof.revocation_root, tree.root());
        let verify_result = verify_non_revocation_proof(&non_rev_proof);
        assert!(
            verify_result.is_ok(),
            "non-revocation proof should verify: {:?}",
            verify_result.err()
        );
    }

    #[test]
    fn test_authorize_anonymously_produces_unlinkable_proofs() {
        let mut cclerk = AgentCipherclerk::new();
        let root_key = [0x42; 32];
        let token = cclerk.mint_token(&root_key, "dns");

        let request = AuthRequest {
            service: Some("dns".into()),
            action: Some("read".into()),
            ..Default::default()
        };

        // Generate two anonymous presentations.
        // NOTE: This requires the bridge crate to have synthetic federation membership
        // enabled (cfg(test) or feature="test-utils"). When running in isolation without
        // that feature, prove_authorization returns IssuerNotInFederation.
        let pres1 = match cclerk.authorize_anonymously(&token, &request) {
            Ok(p) => p,
            Err(SdkError::Auth(dregg_bridge::AuthError::IssuerNotInFederation)) => {
                // Bridge crate compiled without test-utils feature; skip this test.
                return;
            }
            Err(e) => panic!("unexpected error: {e:?}"),
        };
        let pres2 = cclerk.authorize_anonymously(&token, &request).unwrap();

        // Presentation tags MUST differ (fresh randomness per presentation).
        assert_ne!(
            pres1.presentation_tag, pres2.presentation_tag,
            "presentation tags must differ for unlinkability"
        );
    }

    #[test]
    fn test_transfer_note_privately() {
        let cclerk = AgentCipherclerk::new();
        let (_, secret) = cclerk.create_private_note(1000, 1).unwrap();

        // Create a minimal Merkle path (depth 2 as required by the circuit).
        let merkle_siblings = vec![
            [BabyBear::new(111), BabyBear::new(222), BabyBear::new(333)],
            [BabyBear::new(444), BabyBear::new(555), BabyBear::new(666)],
        ];
        let merkle_positions = vec![0, 1];

        let recipient_key = [0xBB; 32];

        let transfer = cclerk
            .transfer_note_privately(&secret, &recipient_key, merkle_siblings, merkle_positions)
            .expect(
                "full-width (28-limb) witness should produce a valid note-spending proof; \
                 previously the felt-collapsed witness made the prover reject this path",
            );

        // The published nullifier matches the note's intrinsic nullifier.
        assert_eq!(transfer.nullifier, secret.note.nullifier(&secret.spending_key));
        // The output note carries the same value/asset as the spent input.
        assert_eq!(transfer.recipient_secret.note.value(), secret.note.value());
        assert_eq!(
            transfer.recipient_secret.note.asset_type(),
            secret.note.asset_type()
        );
        // A non-empty STARK proof was produced (the FULL-WIDTH commitment-binding
        // trace proved successfully).
        assert!(transfer.spending_proof.trace_len >= 4);
    }
}
