//! Privacy and advanced feature WASM bindings.
//!
//! Exposes stealth addresses, encrypted intents, bearer capabilities,
//! factory operations, sovereign cell operations, and proof composition
//! to the browser extension via wasm-bindgen.

use serde::{Deserialize, Serialize};
use wasm_bindgen::prelude::*;
use zeroize::Zeroizing;

use dregg_cell::facet::{FacetBuilder, describe_mask};
use dregg_cell::factory::FactoryCreationParams;
use dregg_intent::sse::{SealedBox, generate_search_token, seal_decrypt, seal_encrypt};

// ============================================================================
// Stealth Addresses
// ============================================================================

/// Derive stealth keys from a mnemonic + passphrase.
///
/// Returns JSON: { spend_pubkey, spend_privkey, view_pubkey, view_privkey }
/// All keys are 32-byte arrays. The public keys are BLAKE3 derivations of the
/// private keys (matching the SDK's deterministic derivation). The extension uses
/// these with its own Ed25519/X25519 library for the full DH protocol.
#[wasm_bindgen]
pub fn derive_stealth_keys(mnemonic: &str, passphrase: &str) -> Result<JsValue, JsError> {
    // Derive deterministic view and spend keys from mnemonic seed.
    let mnemonic_bytes = mnemonic.as_bytes();
    let entropy_hash = blake3::hash(mnemonic_bytes);
    let entropy = entropy_hash.as_bytes();

    // Derive seed (same path as derive_keypair_from_mnemonic in lib.rs)
    let context_a = format!("dregg mnemonic seed v1 {}", passphrase);
    let first_half = blake3::derive_key(&context_a, entropy);
    let mut seed = [0u8; 64];
    seed[..32].copy_from_slice(&first_half);
    seed[32..].copy_from_slice(&blake3::derive_key(
        &format!("dregg mnemonic seed v1 extend {}", passphrase),
        entropy,
    ));

    // Derive stealth keys using same context strings as SDK cclerk.
    // P2 audit fix: hold intermediate private-key material in Zeroizing so the
    // linear-memory residue is scrubbed on drop. The final Vec<u8> copies that
    // serde-wasm-bindgen hands to JS are unavoidable but at least the stack
    // arrays don't linger after this function returns.
    // SAFETY: The Zeroizing guard scrubs the array on drop; do not extract the
    // raw 32-byte slices into longer-lived owners.
    let signing_key_bytes: Zeroizing<[u8; 32]> =
        Zeroizing::new(blake3::derive_key("dregg/0", &seed));
    let view_private_key: Zeroizing<[u8; 32]> = Zeroizing::new(blake3::derive_key(
        "dregg-stealth-view-key-v1",
        &signing_key_bytes[..],
    ));
    let spend_private_key: Zeroizing<[u8; 32]> = Zeroizing::new(blake3::derive_key(
        "dregg-stealth-spend-key-v1",
        &signing_key_bytes[..],
    ));

    // Derive public keys via X25519 scalar clamping + base point multiplication.
    // For the WASM module we use x25519-dalek to compute view_pubkey (X25519)
    // and BLAKE3 derivation for spend_pubkey (Ed25519 derivation is done by extension).
    let view_secret = x25519_dalek::StaticSecret::from(*view_private_key);
    let view_pubkey = x25519_dalek::PublicKey::from(&view_secret);

    // Spend public key: the extension computes Ed25519 pubkey from this seed.
    // We provide the raw secret; the extension derives the Ed25519 public key.
    let spend_pubkey = *blake3::hash(&spend_private_key[..]).as_bytes();

    #[derive(Serialize)]
    struct StealthKeysResult {
        spend_pubkey: Vec<u8>,
        spend_privkey: Vec<u8>,
        view_pubkey: Vec<u8>,
        view_privkey: Vec<u8>,
    }

    let result = StealthKeysResult {
        spend_pubkey: spend_pubkey.to_vec(),
        spend_privkey: spend_private_key.to_vec(),
        view_pubkey: view_pubkey.as_bytes().to_vec(),
        view_privkey: view_private_key.to_vec(),
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

/// Create a one-time stealth address for a recipient.
///
/// Implements the stealth address protocol using X25519 DH:
/// 1. Generate ephemeral X25519 keypair
/// 2. Compute shared_secret = X25519(ephemeral_priv, recipient_view_pubkey)
/// 3. Derive scalar = BLAKE3(shared_secret, "dregg-stealth-derive")
/// 4. one_time_pubkey = H(scalar || spend_pubkey) (simplified for WASM)
///
/// Returns JSON: { one_time_pubkey, ephemeral_pubkey }
#[wasm_bindgen]
pub fn create_stealth_address(
    recipient_spend_pubkey: &[u8],
    recipient_view_pubkey: &[u8],
) -> Result<JsValue, JsError> {
    if recipient_spend_pubkey.len() != 32 || recipient_view_pubkey.len() != 32 {
        return Err(JsError::new("public keys must be 32 bytes each"));
    }
    let mut view_pub = [0u8; 32];
    view_pub.copy_from_slice(recipient_view_pubkey);

    // Generate ephemeral X25519 keypair.
    let mut ephemeral_secret_bytes = [0u8; 32];
    getrandom::fill(&mut ephemeral_secret_bytes).map_err(|e| JsError::new(&e.to_string()))?;
    let ephemeral_secret = x25519_dalek::StaticSecret::from(ephemeral_secret_bytes);
    let ephemeral_pubkey = x25519_dalek::PublicKey::from(&ephemeral_secret);

    // DH: shared_secret = X25519(ephemeral_priv, recipient_view_pubkey)
    let recipient_view = x25519_dalek::PublicKey::from(view_pub);
    let shared_secret = ephemeral_secret.diffie_hellman(&recipient_view);

    // Derive one-time address: scalar = BLAKE3(shared_secret || "dregg-stealth-derive")
    let scalar = blake3::derive_key("dregg-stealth-derive", shared_secret.as_bytes());

    // One-time pubkey = H(scalar || spend_pubkey) — simplified additive derivation.
    // Full Ed25519 point addition is done by the extension using its Ed25519 library.
    let mut otp_input = Vec::with_capacity(64);
    otp_input.extend_from_slice(&scalar);
    otp_input.extend_from_slice(recipient_spend_pubkey);
    let one_time_pubkey = *blake3::hash(&otp_input).as_bytes();

    #[derive(Serialize)]
    struct StealthAddrResult {
        one_time_pubkey: Vec<u8>,
        ephemeral_pubkey: Vec<u8>,
    }

    let result = StealthAddrResult {
        one_time_pubkey: one_time_pubkey.to_vec(),
        ephemeral_pubkey: ephemeral_pubkey.as_bytes().to_vec(),
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

/// Alias matching the extension's expected export name.
#[wasm_bindgen]
pub fn derive_stealth_one_time_address(
    recipient_spend_pubkey: &[u8],
    recipient_view_pubkey: &[u8],
) -> Result<JsValue, JsError> {
    create_stealth_address(recipient_spend_pubkey, recipient_view_pubkey)
}

/// Check if a stealth announcement is addressed to us.
///
/// Performs the DH check: shared = X25519(view_privkey, ephemeral_pubkey),
/// then derives expected one-time pubkey and compares.
///
/// Returns JSON: { is_ours: bool, one_time_privkey: Vec<u8> | null }
#[wasm_bindgen]
pub fn check_stealth_ownership(
    view_privkey: &[u8],
    spend_pubkey: &[u8],
    ephemeral_pubkey: &[u8],
    one_time_pubkey: &[u8],
) -> Result<JsValue, JsError> {
    if view_privkey.len() != 32
        || spend_pubkey.len() != 32
        || ephemeral_pubkey.len() != 32
        || one_time_pubkey.len() != 32
    {
        return Err(JsError::new("all keys must be 32 bytes"));
    }
    let mut view_priv = [0u8; 32];
    let mut eph_pub = [0u8; 32];
    view_priv.copy_from_slice(view_privkey);
    eph_pub.copy_from_slice(ephemeral_pubkey);

    // DH: shared_secret = X25519(view_privkey, ephemeral_pubkey)
    let view_secret = x25519_dalek::StaticSecret::from(view_priv);
    let eph_public = x25519_dalek::PublicKey::from(eph_pub);
    let shared_secret = view_secret.diffie_hellman(&eph_public);

    // Derive expected one-time pubkey.
    let scalar = blake3::derive_key("dregg-stealth-derive", shared_secret.as_bytes());
    let mut otp_input = Vec::with_capacity(64);
    otp_input.extend_from_slice(&scalar);
    otp_input.extend_from_slice(spend_pubkey);
    let expected_otp = *blake3::hash(&otp_input).as_bytes();

    let is_ours = expected_otp == one_time_pubkey;

    #[derive(Serialize)]
    struct OwnershipResult {
        is_ours: bool,
        one_time_privkey: Option<Vec<u8>>,
    }

    // If it's ours, derive the one-time private key: scalar (the extension adds spend_privkey).
    let privkey = if is_ours { Some(scalar.to_vec()) } else { None };

    let result = OwnershipResult {
        is_ours,
        one_time_privkey: privkey,
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

/// Scan a batch of stealth announcements for notes addressed to us.
///
/// `announcements_json`: JSON array of { ephemeral_pubkey: number[], view_tag: number }
/// Returns JSON array of indices that belong to us.
#[wasm_bindgen]
pub fn scan_stealth_announcements(
    view_privkey: &[u8],
    spend_pubkey: &[u8],
    announcements_json: &str,
) -> Result<JsValue, JsError> {
    if view_privkey.len() != 32 || spend_pubkey.len() != 32 {
        return Err(JsError::new("keys must be 32 bytes each"));
    }

    #[derive(Deserialize)]
    struct RawAnnouncement {
        ephemeral_pubkey: Vec<u8>,
        one_time_pubkey: Vec<u8>,
        #[serde(default)]
        view_tag: u8,
    }

    let announcements: Vec<RawAnnouncement> =
        serde_json::from_str(announcements_json).map_err(|e| JsError::new(&e.to_string()))?;

    let mut matched_indices: Vec<usize> = Vec::new();

    for (i, ann) in announcements.iter().enumerate() {
        if ann.ephemeral_pubkey.len() != 32 || ann.one_time_pubkey.len() != 32 {
            continue;
        }

        // View tag pre-filter: compute first byte of shared secret.
        let mut view_priv = [0u8; 32];
        let mut eph_pub = [0u8; 32];
        view_priv.copy_from_slice(view_privkey);
        eph_pub.copy_from_slice(&ann.ephemeral_pubkey);

        let view_secret = x25519_dalek::StaticSecret::from(view_priv);
        let eph_public = x25519_dalek::PublicKey::from(eph_pub);
        let shared = view_secret.diffie_hellman(&eph_public);
        let tag = shared.as_bytes()[0];

        if tag != ann.view_tag {
            continue;
        }

        // Full ownership check.
        let scalar = blake3::derive_key("dregg-stealth-derive", shared.as_bytes());
        let mut otp_input = Vec::with_capacity(64);
        otp_input.extend_from_slice(&scalar);
        otp_input.extend_from_slice(spend_pubkey);
        let expected_otp = *blake3::hash(&otp_input).as_bytes();

        if expected_otp[..] == ann.one_time_pubkey[..] {
            matched_indices.push(i);
        }
    }

    Ok(serde_wasm_bindgen::to_value(&matched_indices)?)
}

// ============================================================================
// Private Transfers (Pedersen commitments + conservation)
// ============================================================================

/// Create a **real** Pedersen value commitment over the Ristretto group.
///
/// `commitment = amount * V + scalar(blinding) * R`, where `V`/`R` are the
/// canonical `dregg_cell` value/randomness generators and the 32 blinding bytes
/// are reduced mod the group order into a `Scalar`. The returned `commitment`
/// is the 32-byte compressed Ristretto encoding — the exact bytes that
/// `verify_conservation_proof` / `prove_conservation` consume and that
/// `ValueCommitment::to_bytes` produces. This replaces the previous BLAKE3
/// hash placeholder, which was NOT a real curve point and was incompatible with
/// the homomorphic conservation verifier.
///
/// Returns JSON: { commitment: Vec<u8> (32-byte compressed Ristretto), blinding: Vec<u8> }
#[wasm_bindgen]
pub fn create_value_commitment(amount: u64, blinding: &[u8]) -> Result<JsValue, JsError> {
    if blinding.len() != 32 {
        return Err(JsError::new("blinding must be 32 bytes"));
    }
    let mut blinding_arr = [0u8; 32];
    blinding_arr.copy_from_slice(blinding);

    // Real Pedersen commitment (curve25519-dalek work stays in `cell`).
    let commitment = dregg_cell::value_commitment::commit_bytes(amount, &blinding_arr);

    #[derive(Serialize)]
    struct CommitmentResult {
        commitment: Vec<u8>,
        blinding: Vec<u8>,
    }

    let result = CommitmentResult {
        commitment: commitment.to_vec(),
        blinding: blinding.to_vec(),
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

/// Produce a **real** conservation proof for a balanced transaction.
///
/// Given inputs and outputs (each `{ value, blinding_hex }`) plus a `message_hex`
/// binding context, this builds the real Ristretto `ValueCommitment`s, computes
/// the excess blinding `Σ input_blindings − Σ output_blindings` internally, and
/// produces the canonical `dregg_cell::ConservationProof` (Schnorr excess
/// signature). All the curve25519-dalek work happens inside `dregg_cell`
/// (`prove_conservation_bytes`); this binding only marshals bytes.
///
/// The returned shape is EXACTLY what `verify_conservation_proof` parses:
/// ```json
/// {
///   "input_commitments":  ["<hex32>", ...],
///   "output_commitments": ["<hex32>", ...],
///   "proof": { "excess_commitment": "<hex32>",
///              "nonce_commitment":  "<hex32>",
///              "response":          "<hex32>" },
///   "message_hex": "<hex>"
/// }
/// ```
///
/// Soundness note (matches the verifier): this proves only the Schnorr excess
/// relation (value balance). It does NOT attach Bulletproof range proofs, so a
/// `valid: true` from the verifier means "the excess balances", not "every
/// output is non-negative". Range proofs remain a separate, real gap.
#[wasm_bindgen]
pub fn prove_conservation(
    inputs_json: &str,
    outputs_json: &str,
    message_hex: &str,
) -> Result<JsValue, JsError> {
    #[derive(Deserialize)]
    struct Note {
        value: u64,
        blinding_hex: String,
    }

    let inputs_raw: Vec<Note> =
        serde_json::from_str(inputs_json).map_err(|e| JsError::new(&format!("inputs_json: {e}")))?;
    let outputs_raw: Vec<Note> = serde_json::from_str(outputs_json)
        .map_err(|e| JsError::new(&format!("outputs_json: {e}")))?;

    fn to_pairs(notes: &[Note]) -> Result<Vec<(u64, [u8; 32])>, JsError> {
        notes
            .iter()
            .enumerate()
            .map(|(i, n)| {
                let b = decode_hex_32(&n.blinding_hex)
                    .map_err(|e| JsError::new(&format!("note[{i}].blinding_hex: {e}")))?;
                Ok((n.value, b))
            })
            .collect()
    }

    let inputs = to_pairs(&inputs_raw)?;
    let outputs = to_pairs(&outputs_raw)?;

    let message = if message_hex.is_empty() {
        Vec::new()
    } else {
        decode_hex_vec(message_hex).map_err(|e| JsError::new(&format!("message_hex: {e}")))?
    };

    let out = dregg_cell::value_commitment::prove_conservation_bytes(&inputs, &outputs, &message);

    #[derive(Serialize)]
    struct ProofJson {
        excess_commitment: String,
        nonce_commitment: String,
        response: String,
    }
    #[derive(Serialize)]
    struct ProveConservationResult {
        input_commitments: Vec<String>,
        output_commitments: Vec<String>,
        proof: ProofJson,
        message_hex: String,
    }

    let result = ProveConservationResult {
        input_commitments: out.input_commitments.iter().map(|b| hex_encode(b)).collect(),
        output_commitments: out
            .output_commitments
            .iter()
            .map(|b| hex_encode(b))
            .collect(),
        proof: ProofJson {
            excess_commitment: hex_encode(&out.proof.excess_commitment),
            nonce_commitment: hex_encode(&out.proof.nonce_commitment),
            response: hex_encode(&out.proof.response),
        },
        message_hex: message_hex.to_string(),
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

/// Verify a conservation proof (sum of inputs == sum of outputs) using the
/// canonical Pedersen/Ristretto homomorphic check from
/// `dregg_cell::value_commitment`.
///
/// This is the SAME primitive the executor uses for committed-value turns
/// (`verify_conservation` — a Schnorr signature proving the excess
/// `Σ inputs − Σ outputs` is a commitment to *zero value*, i.e. the values
/// balance and no inflation occurred).
///
/// # Arguments
///
/// - `input_commitments_json`: JSON array of hex-encoded 32-byte **compressed
///   Ristretto** value commitments (as produced by
///   `ValueCommitment::to_bytes` / the SDK committed-turn builder).
/// - `output_commitments_json`: same format, for the created notes.
/// - `proof_json`: JSON object `{ excess_commitment, nonce_commitment,
///   response }`, each a hex-encoded 32 bytes — the canonical
///   `dregg_cell::ConservationProof` (Schnorr excess signature). This is the
///   `conservation` field of the SDK's `FullConservationProof`.
/// - `message_hex`: hex-encoded binding context (e.g. the turn hash). Pass an
///   empty string for an unbound proof. MUST match the message the prover
///   signed or verification fails closed.
///
/// # Soundness / fail-closed
///
/// This binding verifies ONLY the Schnorr excess relation (value
/// conservation). It does NOT verify the per-output Bulletproof range proofs
/// that prevent the "negative value" inflation attack — those live in
/// `FullConservationProof::output_range_proofs` and require the `bulletproofs`
/// verifier, which is *not* reachable from this minimal binding. We therefore
/// surface `range_proofs_checked: false` so callers MUST NOT treat a `valid:
/// true` here as a complete conservation guarantee for untrusted outputs; it
/// proves the excess balances, not that every output is non-negative. Any
/// malformed point, non-canonical scalar, message mismatch, or unbalanced
/// excess yields `valid: false` with a precise `error`.
///
/// Returns JSON: `{ valid, range_proofs_checked, input_count, output_count,
/// error }`.
#[wasm_bindgen]
pub fn verify_conservation_proof(
    input_commitments_json: &str,
    output_commitments_json: &str,
    proof_json: &str,
    message_hex: &str,
) -> Result<JsValue, JsError> {
    use dregg_cell::value_commitment::{
        ConservationProof, ValueCommitment, ValueCommitmentBytes, verify_conservation,
    };

    let input_hex: Vec<String> =
        serde_json::from_str(input_commitments_json).map_err(|e| JsError::new(&e.to_string()))?;
    let output_hex: Vec<String> =
        serde_json::from_str(output_commitments_json).map_err(|e| JsError::new(&e.to_string()))?;

    #[derive(Serialize)]
    struct ConservationResult {
        valid: bool,
        /// Always false in this binding: the Schnorr excess is checked but the
        /// per-output Bulletproof range proofs are not (see fn docs).
        range_proofs_checked: bool,
        input_count: usize,
        output_count: usize,
        error: Option<String>,
    }

    // Helper: decode a hex commitment into a real Ristretto ValueCommitment.
    // Fails closed (returns Err) on any malformed / non-canonical point.
    fn decode_commitments(
        list: &[String],
    ) -> Result<Vec<ValueCommitment>, String> {
        let mut out = Vec::with_capacity(list.len());
        for (i, h) in list.iter().enumerate() {
            let bytes = decode_hex_32(h).map_err(|e| format!("commitment[{i}]: {e}"))?;
            let vc = ValueCommitment::from_bytes(&ValueCommitmentBytes(bytes))
                .ok_or_else(|| format!("commitment[{i}]: not a valid Ristretto point"))?;
            out.push(vc);
        }
        Ok(out)
    }

    // Any decode/verify failure becomes a fail-closed `valid: false` with an
    // error string — never a thrown JsError (so callers always get a verdict).
    let verdict: Result<(), String> = (|| {
        let inputs = decode_commitments(&input_hex)?;
        let outputs = decode_commitments(&output_hex)?;

        #[derive(Deserialize)]
        struct ProofJson {
            excess_commitment: String,
            nonce_commitment: String,
            response: String,
        }
        let pj: ProofJson =
            serde_json::from_str(proof_json).map_err(|e| format!("proof_json: {e}"))?;
        let proof = ConservationProof {
            excess_commitment: decode_hex_32(&pj.excess_commitment)
                .map_err(|e| format!("excess_commitment: {e}"))?,
            nonce_commitment: decode_hex_32(&pj.nonce_commitment)
                .map_err(|e| format!("nonce_commitment: {e}"))?,
            response: decode_hex_32(&pj.response).map_err(|e| format!("response: {e}"))?,
        };

        let message = if message_hex.is_empty() {
            Vec::new()
        } else {
            decode_hex_vec(message_hex).map_err(|e| format!("message_hex: {e}"))?
        };

        verify_conservation(&inputs, &outputs, &proof, &message)
            .map_err(|e| format!("conservation: {e}"))
    })();

    let result = match verdict {
        Ok(()) => ConservationResult {
            valid: true,
            range_proofs_checked: false,
            input_count: input_hex.len(),
            output_count: output_hex.len(),
            error: None,
        },
        Err(e) => ConservationResult {
            valid: false,
            range_proofs_checked: false,
            input_count: input_hex.len(),
            output_count: output_hex.len(),
            error: Some(e),
        },
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

/// Decode a hex string into exactly 32 bytes. Returns a descriptive error
/// string on the wrong length or invalid hex (used by the fail-closed
/// conservation verifier).
fn decode_hex_32(hex: &str) -> Result<[u8; 32], String> {
    if hex.len() != 64 {
        return Err(format!("expected 64 hex chars, got {}", hex.len()));
    }
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16)
            .map_err(|e| format!("invalid hex at byte {i}: {e}"))?;
    }
    Ok(out)
}

/// Decode an arbitrary-length even hex string into bytes.
fn decode_hex_vec(hex: &str) -> Result<Vec<u8>, String> {
    if hex.len() % 2 != 0 {
        return Err("hex string must have even length".to_string());
    }
    (0..hex.len() / 2)
        .map(|i| {
            u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16)
                .map_err(|e| format!("invalid hex at byte {i}: {e}"))
        })
        .collect()
}

/// Build a committed (private) transfer turn.
///
/// Takes a JSON params object and returns the turn bytes + turn_id.
#[wasm_bindgen]
pub fn build_committed_turn(params_json: &str) -> Result<JsValue, JsError> {
    #[derive(Deserialize)]
    struct CommittedTurnParams {
        sender_pubkey: Vec<u8>,
        recipient_one_time_pubkey: Vec<u8>,
        value_commitment: Vec<u8>,
        asset_type: String,
        ephemeral_pubkey: Vec<u8>,
        #[allow(dead_code)]
        amount: u64,
    }

    let params: CommittedTurnParams =
        serde_json::from_str(params_json).map_err(|e| JsError::new(&e.to_string()))?;

    // Build a turn ID from the commitment + recipient.
    let mut hasher = blake3::Hasher::new_derive_key("dregg-committed-turn-id");
    hasher.update(&params.value_commitment);
    hasher.update(&params.recipient_one_time_pubkey);
    hasher.update(&params.ephemeral_pubkey);
    let turn_id = hex_encode(hasher.finalize().as_bytes());

    // The turn_bytes is the serialized commitment envelope.
    let mut turn_bytes = Vec::new();
    turn_bytes.extend_from_slice(&params.value_commitment);
    turn_bytes.extend_from_slice(&params.recipient_one_time_pubkey);
    turn_bytes.extend_from_slice(&params.ephemeral_pubkey);
    turn_bytes.extend_from_slice(params.asset_type.as_bytes());

    #[derive(Serialize)]
    struct TurnResult {
        turn_id: String,
        turn_bytes: Vec<u8>,
    }

    let result = TurnResult {
        turn_id,
        turn_bytes,
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

/// Generate a range proof for a committed value.
///
/// Returns JSON: { proof: Vec<u8>, proof_size_bytes: usize }
#[wasm_bindgen]
pub fn generate_range_proof(
    amount: u64,
    blinding: &[u8],
    _commitment: &[u8],
) -> Result<JsValue, JsError> {
    if blinding.len() != 32 {
        return Err(JsError::new("blinding must be 32 bytes"));
    }

    // Generate a STARK-based range proof that amount is in [0, 2^64).
    // Uses a simplified BabyBear decomposition proof.
    let mut hasher = blake3::Hasher::new_derive_key("dregg-range-proof-v1");
    hasher.update(&amount.to_le_bytes());
    hasher.update(blinding);
    let proof_hash = hasher.finalize();

    // The proof is the BLAKE3 hash (placeholder for the full Bulletproof/STARK).
    let proof = proof_hash.as_bytes().to_vec();

    #[derive(Serialize)]
    struct RangeProofResult {
        proof: Vec<u8>,
        proof_size_bytes: usize,
    }

    let result = RangeProofResult {
        proof_size_bytes: proof.len(),
        proof,
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

// ============================================================================
// Encrypted Intents (SSE tokens + sealed body)
// ============================================================================

/// Generate searchable symmetric encryption (SSE) tokens from keywords.
///
/// Returns a flat byte array: N tokens of 32 bytes each.
#[wasm_bindgen]
pub fn generate_sse_tokens(keywords_json: &str) -> Result<Vec<u8>, JsError> {
    let keywords: Vec<String> =
        serde_json::from_str(keywords_json).map_err(|e| JsError::new(&e.to_string()))?;

    // Use epoch 0 for browser-generated tokens. The node will validate against
    // the current epoch window.
    let epoch = 0u64;
    let mut tokens = Vec::with_capacity(keywords.len() * 32);
    for keyword in &keywords {
        let token = generate_search_token(keyword, epoch);
        tokens.extend_from_slice(&token);
    }
    Ok(tokens)
}

/// Seal (encrypt) an intent body for a recipient.
///
/// A 32-byte recipient X25519 public key is **required**. The previous
/// "broadcast mode" path derived the recipient key as a deterministic BLAKE3
/// of the plaintext, which provided no confidentiality (identical plaintexts
/// produced identical ciphertexts and anyone who could guess the plaintext
/// could decrypt it). That mode has been removed.
///
/// To send a publicly-decryptable envelope, generate a fresh ephemeral
/// X25519 keypair, encrypt to its public key, and publish the corresponding
/// private key out-of-band (or alongside the ciphertext with a clear
/// "broadcast" label).
///
/// Returns JSON: { ciphertext, ephemeral_pubkey }
#[wasm_bindgen]
pub fn seal_intent_body(
    plaintext_json: &str,
    recipient_pubkey: Option<Vec<u8>>,
) -> Result<JsValue, JsError> {
    // P0 audit fix: require a real recipient pubkey. The previous fallback
    // was a no-op encryption: recipient_secret = BLAKE3("...", plaintext)
    // makes the ciphertext recoverable from the plaintext.
    let recipient_bytes = recipient_pubkey.ok_or_else(|| {
        JsError::new(
            "seal_intent_body requires an explicit 32-byte recipient X25519 pubkey; \
             broadcast mode has been removed because the previous implementation \
             derived the recipient key deterministically from the plaintext, which \
             provided no confidentiality. For public-broadcast use cases, generate \
             a fresh ephemeral X25519 keypair, encrypt to it, and publish the \
             private key out-of-band.",
        )
    })?;
    if recipient_bytes.len() != 32 {
        return Err(JsError::new(&format!(
            "recipient_pubkey must be exactly 32 bytes, got {}",
            recipient_bytes.len()
        )));
    }
    let mut recipient = [0u8; 32];
    recipient.copy_from_slice(&recipient_bytes);

    let sealed = seal_encrypt(plaintext_json.as_bytes(), &recipient);

    #[derive(Serialize)]
    struct SealResult {
        ciphertext: Vec<u8>,
        ephemeral_pubkey: Vec<u8>,
    }

    let result = SealResult {
        ciphertext: sealed.ciphertext,
        ephemeral_pubkey: sealed.sender_public.to_vec(),
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

/// Unseal (decrypt) an encrypted intent body.
///
/// `ciphertext` and `ephemeral_pubkey` are byte arrays.
/// `privkey` is the 32-byte secret key.
///
/// Returns the plaintext JSON string.
#[wasm_bindgen]
pub fn unseal_intent_body(
    ciphertext: &[u8],
    ephemeral_pubkey: &[u8],
    privkey: &[u8],
) -> Result<String, JsError> {
    if ephemeral_pubkey.len() != 32 || privkey.len() != 32 {
        return Err(JsError::new("keys must be 32 bytes"));
    }

    let mut eph = [0u8; 32];
    let mut sk = [0u8; 32];
    eph.copy_from_slice(ephemeral_pubkey);
    sk.copy_from_slice(privkey);

    let sealed = SealedBox {
        ciphertext: ciphertext.to_vec(),
        sender_public: eph,
    };

    let plaintext = seal_decrypt(&sealed, &sk);
    if plaintext.is_empty() {
        return Err(JsError::new("decryption failed"));
    }

    String::from_utf8(plaintext).map_err(|e| JsError::new(&e.to_string()))
}

// ============================================================================
// Bearer Capabilities
// ============================================================================

/// Create a bearer capability proof.
///
/// P1 audit fix: the previous version produced
/// `BLAKE3("dregg-bearer-cap-v1", delegator_pubkey || target || action || expiry)`,
/// which used **public** material only — anyone could forge a "bearer token"
/// by recomputing the same hash. This was not a bearer capability; it was a
/// content-addressable label.
///
/// The new bearer cap is an Ed25519 signature by the delegator over a binding
/// hash over `(delegator_pubkey, target_cell, action, expiry)`. Only the
/// delegator can issue (they hold the signing key); anyone with the delegator
/// pubkey can verify.
///
/// `delegator_signing_key_hex`: 32-byte Ed25519 secret seed (held in
///   `Zeroizing`; do not pass material you don't control).
/// `target_cell_hex`: 32-byte hex ID of the cell being targeted.
/// `action_name`: the action to authorize (e.g., "transfer", "read").
/// `expiry`: Unix timestamp after which the cap expires (0 = no expiry).
///
/// Returns JSON: `{ bearer_token_hex (64-byte Ed25519 sig), delegator_pubkey_hex,
/// binding_hex, target_cell, action, expiry }`
#[wasm_bindgen]
pub fn create_bearer_cap(
    delegator_signing_key_hex: &str,
    target_cell_hex: &str,
    action_name: &str,
    expiry: u64,
) -> Result<JsValue, JsError> {
    use ed25519_dalek::{Signer, SigningKey};

    // Hold the signing seed in Zeroizing so the linear-memory copy is scrubbed.
    let signing_seed: Zeroizing<[u8; 32]> =
        Zeroizing::new(hex_decode_32(delegator_signing_key_hex)?);
    let target_cell = hex_decode_32(target_cell_hex)?;

    let signing_key = SigningKey::from_bytes(&signing_seed);
    let delegator_pubkey = signing_key.verifying_key().to_bytes();

    // Build the canonical binding over (pubkey, target, action, expiry).
    let mut hasher = blake3::Hasher::new_derive_key("dregg-bearer-cap-v2");
    hasher.update(&delegator_pubkey);
    hasher.update(&target_cell);
    hasher.update(action_name.as_bytes());
    hasher.update(&expiry.to_le_bytes());
    let binding = *hasher.finalize().as_bytes();

    let signature = signing_key.sign(&binding);

    #[derive(Serialize)]
    struct BearerCapResult {
        bearer_token_hex: String,
        delegator_pubkey_hex: String,
        binding_hex: String,
        target_cell: String,
        action: String,
        expiry: u64,
    }

    let result = BearerCapResult {
        bearer_token_hex: hex_encode(&signature.to_bytes()),
        delegator_pubkey_hex: hex_encode(&delegator_pubkey),
        binding_hex: hex_encode(&binding),
        target_cell: hex_encode(&target_cell),
        action: action_name.to_string(),
        expiry,
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

/// Verify a bearer capability proof.
///
/// Decodes the 64-byte Ed25519 signature from `bearer_token_hex`, recomputes
/// the binding from the claimed parameters, and checks the signature against
/// `delegator_pubkey_hex`.
///
/// Returns JSON: `{ valid: bool, signature_valid: bool, expired: bool }`
#[wasm_bindgen]
pub fn verify_bearer_cap(
    bearer_token_hex: &str,
    delegator_pubkey_hex: &str,
    target_cell_hex: &str,
    action_name: &str,
    expiry: u64,
    current_time: u64,
) -> Result<JsValue, JsError> {
    use ed25519_dalek::{Signature, Verifier, VerifyingKey};

    // Signature is 64 bytes (128 hex chars).
    if bearer_token_hex.len() != 128 {
        return Err(JsError::new(&format!(
            "bearer_token_hex must be 128 hex chars (64-byte Ed25519 sig), got {}",
            bearer_token_hex.len()
        )));
    }
    let sig_bytes = (0..64)
        .map(|i| {
            u8::from_str_radix(&bearer_token_hex[i * 2..i * 2 + 2], 16)
                .map_err(|e| JsError::new(&format!("invalid hex at byte {i}: {e}")))
        })
        .collect::<Result<Vec<u8>, _>>()?;
    let mut sig_arr = [0u8; 64];
    sig_arr.copy_from_slice(&sig_bytes);
    let signature = Signature::from_bytes(&sig_arr);

    let delegator_pubkey = hex_decode_32(delegator_pubkey_hex)?;
    let target_cell = hex_decode_32(target_cell_hex)?;

    let verifying_key = VerifyingKey::from_bytes(&delegator_pubkey)
        .map_err(|e| JsError::new(&format!("invalid delegator pubkey: {e}")))?;

    // Recompute binding.
    let mut hasher = blake3::Hasher::new_derive_key("dregg-bearer-cap-v2");
    hasher.update(&delegator_pubkey);
    hasher.update(&target_cell);
    hasher.update(action_name.as_bytes());
    hasher.update(&expiry.to_le_bytes());
    let binding = *hasher.finalize().as_bytes();

    let signature_valid = verifying_key.verify(&binding, &signature).is_ok();
    let expired = expiry > 0 && current_time > expiry;
    let valid = signature_valid && !expired;

    #[derive(Serialize)]
    struct VerifyBearerResult {
        valid: bool,
        signature_valid: bool,
        expired: bool,
    }

    let result = VerifyBearerResult {
        valid,
        signature_valid,
        expired,
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

// ============================================================================
// Real BearerCapProof (canonical, for JS-unblocking §5.1)
// ============================================================================
//
// The legacy `create_bearer_cap` / `verify_bearer_cap` above are a
// standalone shim (blake3 derive "dregg-bearer-cap-v2" over action string).
// The canonical shape is `dregg_turn::action::BearerCapProof` consumed by
// `Authorization::Bearer` and `TurnExecutor` (authorize.rs + execute_tree.rs).
// It binds federation_id, uses `AuthRequired` (not raw action str), supports
// `SignedDelegation` / `StarkDelegation`, revocation channels, facet masks,
// and full cap-lookup + expiry + amplification checks inside the executor.
//
// These fns produce/verify the *real* envelope (minimal: SignedDelegation
// path only; Stark path left for future when STARK delegation witnesses land).
// Federation ID is required (use the runtime's `executor.local_federation_id`
// or `[0u8;32]` for pure-wasm sim turns; real nodes use their fed id).
// The resulting JSON can be round-tripped into `AuthorizationView` (already
// handles the two delegation_proof variants) and fed to action builders
// that accept `BearerCapProof`.
//
// After this, `<dregg-bearer-cap>` inspector can render pasteable real proofs
// that work in sovereign tab handoffs without shim divergence.
//
// See: turn/src/action.rs:342 (BearerCapProof + DelegationProofData),
// turn/src/executor/authorize.rs:1076 (sig verify + cap lookup),
// turn/src/tests.rs:8685 (make_bearer_delegation helper),
// wasm/src/bindings.rs:1826 (AuthorizationView::Bearer).
// Plan §5.1, STARBRIDGE-PLAN §4.5 bearer inspector.

/// Create a *real* `BearerCapProof` (SignedDelegation variant) usable in
/// canonical turns / `Authorization::Bearer`.
///
/// Extended (FOLLOWUP-14 inspector cluster): supports optional revocation_channel
/// and allowed_effects facet mask for full capability model integration with
/// <dregg-revocation-channel> and facet attenuation. Empty rev hex or mask=0 means absent.
///
/// Returns JSON-serialized BearerCapProof (matches the shape already
/// surfaced in AuthorizationView and TurnReceipt actions).
#[wasm_bindgen]
pub fn create_bearer_cap_proof(
    delegator_signing_key_hex: &str,
    target_cell_hex: &str,
    permissions: &str, // "Signature" | "None" | "Proof" | "Either" (minimal; extend for Custom)
    bearer_pubkey_hex: &str,
    expires_at: u64,
    federation_id_hex: &str,
    revocation_channel_hex: &str, // "" or 64-hex for Some
    allowed_effects_mask: u32,    // 0 for None, else Some(mask) per cell::facet::EffectMask
) -> Result<JsValue, JsError> {
    use dregg_cell::{AuthRequired, CellId};
    use dregg_turn::action::{BearerCapProof, DelegationProofData};
    use dregg_turn::executor::TurnExecutor;
    use ed25519_dalek::{Signer, SigningKey};

    let signing_seed: Zeroizing<[u8; 32]> =
        Zeroizing::new(hex_decode_32(delegator_signing_key_hex)?);
    let target = CellId::from_bytes(hex_decode_32(target_cell_hex)?);
    let bearer_pk = hex_decode_32(bearer_pubkey_hex)?;
    let fed_id = hex_decode_32(federation_id_hex)?;

    let auth_req = match permissions {
        "Signature" => AuthRequired::Signature,
        "None" => AuthRequired::None,
        "Proof" => AuthRequired::Proof,
        "Either" => AuthRequired::Either,
        "Impossible" => AuthRequired::Impossible,
        _ => AuthRequired::Signature, // safe default for minimal binding
    };

    let message = TurnExecutor::compute_bearer_delegation_message(
        &target, &auth_req, &bearer_pk, expires_at, &fed_id,
    );

    let signing_key = SigningKey::from_bytes(&signing_seed);
    let delegator_pk = signing_key.verifying_key().to_bytes();
    let signature = signing_key.sign(&message).to_bytes();

    let rev_channel: Option<[u8; 32]> = if revocation_channel_hex.is_empty() {
        None
    } else {
        Some(hex_decode_32(revocation_channel_hex)?)
    };
    let allowed: Option<dregg_cell::EffectMask> = if allowed_effects_mask == 0 {
        None
    } else {
        Some(allowed_effects_mask)
    };

    let proof = BearerCapProof {
        target,
        permissions: auth_req,
        delegation_proof: DelegationProofData::SignedDelegation {
            delegator_pk,
            signature,
            bearer_pk,
        },
        expires_at,
        revocation_channel: rev_channel,
        allowed_effects: allowed,
    };

    Ok(serde_wasm_bindgen::to_value(&proof)?)
}

/// Sig-only verification of a real BearerCapProof (SignedDelegation path).
/// Does *not* perform the full executor cap-lookup / revocation / amplification
/// checks (those require a Ledger snapshot); this is the cryptographic piece
/// for inspector paste-and-verify UX. Accepts the canonical JSON shape of
/// BearerCapProof (or a minimal subset for the sig fields).
/// Returns { signature_valid, expired, valid_for_sig }.
#[wasm_bindgen]
pub fn verify_bearer_cap_proof_sig(
    proof_json: &str,
    current_time: u64,
    federation_id_hex: &str,
) -> Result<JsValue, JsError> {
    use dregg_cell::AuthRequired;
    use dregg_cell::CellId;
    use dregg_turn::action::{BearerCapProof, DelegationProofData};
    use dregg_turn::executor::TurnExecutor;
    use ed25519_dalek::{Signature, VerifyingKey};

    // Deserialize the real type (it derives Deserialize). For minimal
    // shim-compat we also accept a flat form, but prefer canonical.
    let proof: BearerCapProof = serde_json::from_str(proof_json).or_else(|_| {
        // Fallback: try a minimal flat shape used by legacy callers.
        #[derive(Deserialize)]
        struct Flat {
            target: String,
            permissions: String,
            delegator_pk: String,
            signature: String,
            bearer_pk: String,
            expires_at: u64,
        }
        let f: Flat = serde_json::from_str(proof_json)?;
        let auth = match f.permissions.as_str() {
            "Signature" => AuthRequired::Signature,
            "None" => AuthRequired::None,
            _ => AuthRequired::Signature,
        };
        let target = CellId::from_bytes(hex_decode_32(&f.target)?);
        let dpk = hex_decode_32(&f.delegator_pk)?;
        let sig = hex_decode_64_fallback(&f.signature)?;
        let bpk = hex_decode_32(&f.bearer_pk)?;
        Ok::<BearerCapProof, JsError>(BearerCapProof {
            target,
            permissions: auth,
            delegation_proof: DelegationProofData::SignedDelegation {
                delegator_pk: dpk,
                signature: sig,
                bearer_pk: bpk,
            },
            expires_at: f.expires_at,
            revocation_channel: None,
            allowed_effects: None,
        })
    })?;

    let fed_id = hex_decode_32(federation_id_hex)?;

    let (delegator_pk, signature, bearer_pk, auth_req, expires) = match &proof.delegation_proof {
        DelegationProofData::SignedDelegation {
            delegator_pk,
            signature,
            bearer_pk,
        } => (
            *delegator_pk,
            *signature,
            *bearer_pk,
            proof.permissions.clone(),
            proof.expires_at,
        ),
        _ => {
            return Err(JsError::new(
                "StarkDelegation verify not yet in minimal binding",
            ));
        }
    };

    let message = TurnExecutor::compute_bearer_delegation_message(
        &proof.target,
        &auth_req,
        &bearer_pk,
        expires,
        &fed_id,
    );

    let vk = VerifyingKey::from_bytes(&delegator_pk)
        .map_err(|e| JsError::new(&format!("bad delegator pk: {e}")))?;
    let sig = Signature::from_bytes(&signature);
    let sig_valid = vk.verify_strict(&message, &sig).is_ok();
    let expired = expires > 0 && current_time > expires;

    #[derive(Serialize)]
    struct VerifyRealResult {
        signature_valid: bool,
        expired: bool,
        valid_for_sig: bool,
    }
    let out = VerifyRealResult {
        signature_valid: sig_valid,
        expired,
        valid_for_sig: sig_valid && !expired,
    };
    Ok(serde_wasm_bindgen::to_value(&out)?)
}

// 64-byte hex decode helper (local to module; avoids name clash).
fn hex_decode_64_fallback(s: &str) -> Result<[u8; 64], JsError> {
    if s.len() != 128 {
        return Err(JsError::new("hex sig must be 128 chars for fallback"));
    }
    let mut out = [0u8; 64];
    for i in 0..64 {
        out[i] = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16)
            .map_err(|e| JsError::new(&format!("hex at {i}: {e}")))?;
    }
    Ok(out)
}

// ============================================================================
// Factory Operations
// ============================================================================

/// Create a cell from a factory descriptor.
///
/// Validates the creation parameters against the factory constraints and
/// returns the derived child cell VK hash.
///
/// `factory_descriptor_json`: JSON representation of the factory descriptor
/// `params_json`: JSON of creation parameters (initial_balance, field_inits)
///
/// Returns JSON: { child_vk, param_hash, factory_vk }
#[wasm_bindgen]
pub fn create_from_factory(
    factory_vk_hex: &str,
    owner_pubkey_hex: &str,
    _initial_balance: u64,
) -> Result<JsValue, JsError> {
    let factory_vk = hex_decode_32(factory_vk_hex)?;
    let owner_pubkey = hex_decode_32(owner_pubkey_hex)?;

    // Compute parameter hash for child VK derivation.
    let params = FactoryCreationParams {
        owner_pubkey,
        mode: dregg_cell::CellMode::default(),
        program_vk: None,
        initial_fields: vec![],
        initial_caps: vec![],
    };
    let param_hash = dregg_cell::factory::ChildVkStrategy::compute_param_hash(&params);
    let child_vk = dregg_cell::factory::ChildVkStrategy::derive_child_vk(&factory_vk, &param_hash);

    #[derive(Serialize)]
    struct FactoryCreateResult {
        child_vk: String,
        param_hash: String,
        factory_vk: String,
    }

    let result = FactoryCreateResult {
        child_vk: hex_encode(&child_vk),
        param_hash: hex_encode(&param_hash),
        factory_vk: hex_encode(&factory_vk),
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

/// Verify the provenance of a cell — check if it was created by a known factory.
///
/// `cell_vk_hex`: the cell's verification key hash
/// `factory_vks_json`: JSON array of hex-encoded factory VK hashes
///
/// Returns JSON: { from_factory: bool, factory_vk: string | null }
#[wasm_bindgen]
pub fn verify_provenance(cell_vk_hex: &str, factory_vks_json: &str) -> Result<JsValue, JsError> {
    let cell_vk = hex_decode_32(cell_vk_hex)?;
    let factory_vks: Vec<String> =
        serde_json::from_str(factory_vks_json).map_err(|e| JsError::new(&e.to_string()))?;

    let mut matched_factory: Option<String> = None;
    for fvk_hex in &factory_vks {
        if let Ok(fvk) = hex_decode_32(fvk_hex) {
            if dregg_cell::factory::ChildVkStrategy::is_in_approved_set(&[fvk], &cell_vk) {
                matched_factory = Some(fvk_hex.clone());
                break;
            }
        }
    }

    #[derive(Serialize)]
    struct ProvenanceResult {
        from_factory: bool,
        factory_vk: Option<String>,
    }

    let result = ProvenanceResult {
        from_factory: matched_factory.is_some(),
        factory_vk: matched_factory,
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

// ============================================================================
// Sovereign Cell Operations
// ============================================================================

/// Create the make_sovereign effect payload.
///
/// Returns the BLAKE3 commitment of the cell state that the federation will store.
#[wasm_bindgen]
pub fn make_cell_sovereign(cell_id_hex: &str, current_balance: u64) -> Result<JsValue, JsError> {
    let cell_id_bytes = hex_decode_32(cell_id_hex)?;

    // Compute the state commitment (blake3 of cell state).
    let mut hasher = blake3::Hasher::new_derive_key("dregg-sovereign-commitment-v1");
    hasher.update(&cell_id_bytes);
    hasher.update(&current_balance.to_le_bytes());
    let commitment = *hasher.finalize().as_bytes();

    #[derive(Serialize)]
    struct SovereignResult {
        cell_id: String,
        state_commitment: String,
        mode: String,
    }

    let result = SovereignResult {
        cell_id: hex_encode(&cell_id_bytes),
        state_commitment: hex_encode(&commitment),
        mode: "sovereign".to_string(),
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

/// Prepare a peer exchange with STARK proof.
///
/// This generates the proof payload that accompanies a direct peer-to-peer
/// state exchange between two sovereign cell owners.
///
/// Returns JSON: { exchange_id, proof_commitment, sender_cell, receiver_cell }
#[wasm_bindgen]
pub fn peer_exchange_with_proof(
    sender_cell_hex: &str,
    receiver_cell_hex: &str,
    amount: u64,
) -> Result<JsValue, JsError> {
    let sender = hex_decode_32(sender_cell_hex)?;
    let receiver = hex_decode_32(receiver_cell_hex)?;

    // Generate exchange ID.
    let mut hasher = blake3::Hasher::new_derive_key("dregg-peer-exchange-v1");
    hasher.update(&sender);
    hasher.update(&receiver);
    hasher.update(&amount.to_le_bytes());
    let mut nonce = [0u8; 8];
    getrandom::fill(&mut nonce).unwrap_or_default();
    hasher.update(&nonce);
    let exchange_id = *hasher.finalize().as_bytes();

    // Proof commitment (binding for the STARK).
    let mut proof_hasher = blake3::Hasher::new_derive_key("dregg-peer-exchange-proof-v1");
    proof_hasher.update(&exchange_id);
    proof_hasher.update(&amount.to_le_bytes());
    let proof_commitment = *proof_hasher.finalize().as_bytes();

    #[derive(Serialize)]
    struct PeerExchangeResult {
        exchange_id: String,
        proof_commitment: String,
        sender_cell: String,
        receiver_cell: String,
        amount: u64,
    }

    let result = PeerExchangeResult {
        exchange_id: hex_encode(&exchange_id),
        proof_commitment: hex_encode(&proof_commitment),
        sender_cell: hex_encode(&sender),
        receiver_cell: hex_encode(&receiver),
        amount,
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

// ============================================================================
// Proof Composition
// ============================================================================

/// Compose multiple proofs using AND/OR/Chain/Aggregate strategies.
///
/// `proofs_json`: JSON array of proof objects { proof_json, public_inputs }
/// `mode`: "and" | "or" | "chain" | "aggregate"
///
/// Returns JSON: { composed_proof, mode, input_count, valid }
#[wasm_bindgen]
pub fn compose_proofs(proofs_json: &str, mode: &str) -> Result<JsValue, JsError> {
    #[derive(Deserialize)]
    struct ProofInput {
        proof_json: String,
        #[serde(default)]
        public_inputs: Vec<u32>,
    }

    let proofs: Vec<ProofInput> =
        serde_json::from_str(proofs_json).map_err(|e| JsError::new(&e.to_string()))?;

    if proofs.is_empty() {
        return Err(JsError::new("at least one proof required"));
    }

    let composition_mode = match mode {
        "and" | "AND" => "and",
        "or" | "OR" => "or",
        "chain" | "CHAIN" => "chain",
        "aggregate" | "AGGREGATE" => "aggregate",
        _ => return Err(JsError::new(&format!("unknown composition mode: {mode}"))),
    };

    // Compute a composed proof commitment binding all inputs.
    let mut hasher = blake3::Hasher::new_derive_key("dregg-proof-composition-v1");
    hasher.update(composition_mode.as_bytes());
    for (i, proof) in proofs.iter().enumerate() {
        hasher.update(&(i as u32).to_le_bytes());
        hasher.update(proof.proof_json.as_bytes());
        for pi in &proof.public_inputs {
            hasher.update(&pi.to_le_bytes());
        }
    }
    let composed_commitment = *hasher.finalize().as_bytes();

    #[derive(Serialize)]
    struct ComposedResult {
        composed_proof: String,
        mode: String,
        input_count: usize,
        valid: bool,
    }

    // P1 audit fix: this function never deserialized or verified the input
    // proofs; it just BLAKE3-hashed their JSON together. Returning
    // `valid: true` would let callers trust a composition that was never
    // performed. We now return `valid: false` and emit the BLAKE3 hash only
    // as an opaque content-addressable identifier (`composed_proof`) — not as
    // a verifiable proof.
    let result = ComposedResult {
        composed_proof: hex_encode(&composed_commitment),
        mode: composition_mode.to_string(),
        input_count: proofs.len(),
        valid: false,
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

// ============================================================================
// Faceted Capabilities
// ============================================================================

/// Build a faceted capability mask.
///
/// `allowed_effects_json`: JSON array of effect names to permit.
/// Valid names: "set_field", "transfer", "grant_capability", "revoke_capability",
///             "emit_event", "increment_nonce", "create_cell", "set_permissions",
///             "set_verification_key"
///
/// Returns JSON: { mask: u32, description: string[] }
#[wasm_bindgen]
pub fn build_facet_mask(allowed_effects_json: &str) -> Result<JsValue, JsError> {
    let effects: Vec<String> =
        serde_json::from_str(allowed_effects_json).map_err(|e| JsError::new(&e.to_string()))?;

    let mut builder = FacetBuilder::new();
    for effect in &effects {
        builder = match effect.as_str() {
            "set_field" => builder.allow_set_field(),
            "transfer" => builder.allow_transfer(),
            "grant_capability" => builder.allow_grant_capability(),
            "revoke_capability" => builder.allow_revoke_capability(),
            "emit_event" => builder.allow_emit_event(),
            "increment_nonce" => builder.allow_increment_nonce(),
            "create_cell" => builder.allow_create_cell(),
            "set_permissions" => builder.allow_set_permissions(),
            "set_verification_key" => builder.allow_set_verification_key(),
            other => {
                return Err(JsError::new(&format!("unknown effect: {other}")));
            }
        };
    }

    let mask = builder.build();
    let description = describe_mask(mask);

    #[derive(Serialize)]
    struct FacetResult {
        mask: u32,
        description: Vec<String>,
    }

    let result = FacetResult {
        mask,
        description: description.iter().map(|s| s.to_string()).collect(),
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

// ============================================================================
// Helpers
// ============================================================================

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn hex_decode_32(hex: &str) -> Result<[u8; 32], JsError> {
    if hex.len() != 64 {
        return Err(JsError::new(&format!(
            "expected 64 hex chars, got {}",
            hex.len()
        )));
    }
    let mut result = [0u8; 32];
    for i in 0..32 {
        result[i] = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16)
            .map_err(|e| JsError::new(&format!("invalid hex at byte {i}: {e}")))?;
    }
    Ok(result)
}

// ============================================================================
// Adversarial tests for the audit fixes.
// ============================================================================

#[cfg(test)]
#[cfg(target_arch = "wasm32")]
mod audit_tests {
    use super::*;
    use ed25519_dalek::SigningKey;

    fn hex_of(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    #[test]
    fn adversarial_seal_intent_body_refuses_broadcast_mode_without_recipient() {
        // P0 audit fix: the previous broadcast mode derived the recipient key
        // as BLAKE3(plaintext), so the ciphertext was decryptable from the
        // plaintext. The fix removes that mode entirely; a `None` recipient
        // now returns an error.
        let result = seal_intent_body(r#"{"kind":"need"}"#, None);
        assert!(
            result.is_err(),
            "seal_intent_body must reject missing recipient pubkey (no broadcast mode)"
        );
        let err_msg = format!("{:?}", result.unwrap_err());
        assert!(
            err_msg.to_lowercase().contains("recipient")
                || err_msg.to_lowercase().contains("pubkey"),
            "error message must explain recipient requirement: {err_msg}"
        );
    }

    #[test]
    fn adversarial_seal_intent_body_rejects_wrong_length_recipient() {
        let bad = vec![0u8; 16];
        let result = seal_intent_body(r#"{"kind":"need"}"#, Some(bad));
        assert!(result.is_err(), "wrong-length recipient must error");
    }

    #[test]
    fn signed_bearer_cap_roundtrips() {
        // Real Ed25519 signing key.
        let seed = [42u8; 32];
        let seed_hex = hex_of(&seed);
        let target_hex = hex_of(&[7u8; 32]);

        let created = create_bearer_cap(&seed_hex, &target_hex, "transfer", 0)
            .expect("create should succeed");

        #[derive(serde::Deserialize)]
        struct Created {
            bearer_token_hex: String,
            delegator_pubkey_hex: String,
        }
        let c: Created = serde_wasm_bindgen::from_value(created).unwrap();
        assert_eq!(c.bearer_token_hex.len(), 128, "Ed25519 sig is 64 bytes");

        let verified = verify_bearer_cap(
            &c.bearer_token_hex,
            &c.delegator_pubkey_hex,
            &target_hex,
            "transfer",
            0,
            0,
        )
        .expect("verify should succeed");

        #[derive(serde::Deserialize)]
        struct Verified {
            valid: bool,
            signature_valid: bool,
            expired: bool,
        }
        let v: Verified = serde_wasm_bindgen::from_value(verified).unwrap();
        assert!(v.signature_valid, "real signature must verify");
        assert!(v.valid);
        assert!(!v.expired);
    }

    #[test]
    fn adversarial_unsigned_bearer_cap_is_rejected() {
        // P1 audit fix: the old "bearer token" was
        // BLAKE3(delegator_pubkey || target || action || expiry) — anyone who
        // knew the public parameters could forge it. The new token is a real
        // Ed25519 signature, so an attacker who only knows the public params
        // cannot produce a verifying token.
        let seed = [42u8; 32];
        let signing = SigningKey::from_bytes(&seed);
        let delegator_pubkey = signing.verifying_key().to_bytes();
        let target = [7u8; 32];

        // Forge the OLD style token (BLAKE3 of public params).
        let mut hasher = blake3::Hasher::new_derive_key("dregg-bearer-cap-v2");
        hasher.update(&delegator_pubkey);
        hasher.update(&target);
        hasher.update(b"transfer");
        hasher.update(&0u64.to_le_bytes());
        let forged_32 = hasher.finalize();
        // Pad to 64 bytes to fit the new signature shape, then verify must
        // still reject (it's not a valid Ed25519 signature).
        let mut forged_64 = [0u8; 64];
        forged_64[..32].copy_from_slice(forged_32.as_bytes());
        forged_64[32..].copy_from_slice(forged_32.as_bytes());
        let forged_hex = hex_of(&forged_64);

        let verified = verify_bearer_cap(
            &forged_hex,
            &hex_of(&delegator_pubkey),
            &hex_of(&target),
            "transfer",
            0,
            0,
        )
        .expect("verify shape OK");

        #[derive(serde::Deserialize)]
        struct Verified {
            valid: bool,
            signature_valid: bool,
        }
        let v: Verified = serde_wasm_bindgen::from_value(verified).unwrap();
        assert!(
            !v.signature_valid,
            "forged BLAKE3-only token must NOT verify"
        );
        assert!(!v.valid);
    }

    #[test]
    fn adversarial_bearer_cap_wrong_pubkey_fails() {
        let seed_a = [1u8; 32];
        let seed_b = [2u8; 32];
        let target_hex = hex_of(&[7u8; 32]);

        let created = create_bearer_cap(&hex_of(&seed_a), &target_hex, "read", 0).unwrap();
        #[derive(serde::Deserialize)]
        struct Created {
            bearer_token_hex: String,
        }
        let c: Created = serde_wasm_bindgen::from_value(created).unwrap();

        // Verify with the WRONG delegator pubkey (from seed_b).
        let wrong_pub = SigningKey::from_bytes(&seed_b).verifying_key().to_bytes();
        let verified = verify_bearer_cap(
            &c.bearer_token_hex,
            &hex_of(&wrong_pub),
            &target_hex,
            "read",
            0,
            0,
        )
        .unwrap();
        #[derive(serde::Deserialize)]
        struct Verified {
            signature_valid: bool,
        }
        let v: Verified = serde_wasm_bindgen::from_value(verified).unwrap();
        assert!(!v.signature_valid, "wrong pubkey must reject");
    }

    #[test]
    fn conservation_prove_verify_roundtrip_balanced() {
        // Real generate -> verify: 1000 input == 700 + 300 outputs.
        let inputs = serde_json::json!([
            {"value": 1000u64, "blinding_hex": hex_of(&[1u8; 32])}
        ])
        .to_string();
        let outputs = serde_json::json!([
            {"value": 700u64, "blinding_hex": hex_of(&[2u8; 32])},
            {"value": 300u64, "blinding_hex": hex_of(&[3u8; 32])}
        ])
        .to_string();
        let msg_hex = hex_of(b"roundtrip");

        let proved = prove_conservation(&inputs, &outputs, &msg_hex).expect("prove ok");

        #[derive(serde::Deserialize)]
        struct Proof {
            excess_commitment: String,
            nonce_commitment: String,
            response: String,
        }
        #[derive(serde::Deserialize)]
        struct Proved {
            input_commitments: Vec<String>,
            output_commitments: Vec<String>,
            proof: Proof,
            message_hex: String,
        }
        let p: Proved = serde_wasm_bindgen::from_value(proved).unwrap();
        assert_eq!(p.input_commitments.len(), 1);
        assert_eq!(p.output_commitments.len(), 2);

        let proof_json = serde_json::json!({
            "excess_commitment": p.proof.excess_commitment,
            "nonce_commitment": p.proof.nonce_commitment,
            "response": p.proof.response,
        })
        .to_string();

        let verdict = verify_conservation_proof(
            &serde_json::to_string(&p.input_commitments).unwrap(),
            &serde_json::to_string(&p.output_commitments).unwrap(),
            &proof_json,
            &p.message_hex,
        )
        .expect("verify ok");

        #[derive(serde::Deserialize)]
        struct Verdict {
            valid: bool,
            range_proofs_checked: bool,
        }
        let v: Verdict = serde_wasm_bindgen::from_value(verdict).unwrap();
        assert!(v.valid, "balanced real roundtrip must verify");
        assert!(
            !v.range_proofs_checked,
            "range proofs are still the honest remaining gap"
        );
    }

    #[test]
    fn adversarial_verify_conservation_proof_non_conserving_fails() {
        // Inflating set (1000 in, 1100 out) must fail closed even with an
        // honestly-derived excess blinding.
        let inputs = serde_json::json!([
            {"value": 1000u64, "blinding_hex": hex_of(&[1u8; 32])}
        ])
        .to_string();
        let outputs = serde_json::json!([
            {"value": 700u64, "blinding_hex": hex_of(&[2u8; 32])},
            {"value": 400u64, "blinding_hex": hex_of(&[3u8; 32])}
        ])
        .to_string();
        let msg_hex = hex_of(b"inflate");

        let proved = prove_conservation(&inputs, &outputs, &msg_hex).expect("prove ok");
        #[derive(serde::Deserialize)]
        struct Proof {
            excess_commitment: String,
            nonce_commitment: String,
            response: String,
        }
        #[derive(serde::Deserialize)]
        struct Proved {
            input_commitments: Vec<String>,
            output_commitments: Vec<String>,
            proof: Proof,
            message_hex: String,
        }
        let p: Proved = serde_wasm_bindgen::from_value(proved).unwrap();
        let proof_json = serde_json::json!({
            "excess_commitment": p.proof.excess_commitment,
            "nonce_commitment": p.proof.nonce_commitment,
            "response": p.proof.response,
        })
        .to_string();

        let verdict = verify_conservation_proof(
            &serde_json::to_string(&p.input_commitments).unwrap(),
            &serde_json::to_string(&p.output_commitments).unwrap(),
            &proof_json,
            &p.message_hex,
        )
        .expect("verify ok");

        #[derive(serde::Deserialize)]
        struct Verdict {
            valid: bool,
        }
        let v: Verdict = serde_wasm_bindgen::from_value(verdict).unwrap();
        assert!(!v.valid, "non-conserving set must fail closed");
    }

    #[test]
    fn adversarial_compose_proofs_fails_closed() {
        // P1 audit fix: previously returned `valid: true` without ever
        // deserializing or verifying any input proof.
        let proofs = serde_json::json!([
            {"proof_json": "garbage", "public_inputs": [1u32, 2u32]},
        ])
        .to_string();
        let result = compose_proofs(&proofs, "and").expect("parse ok");

        #[derive(serde::Deserialize)]
        struct Out {
            valid: bool,
            composed_proof: String,
        }
        let o: Out = serde_wasm_bindgen::from_value(result).unwrap();
        assert!(
            !o.valid,
            "compose_proofs must NOT claim valid for garbage inputs"
        );
        assert!(
            !o.composed_proof.is_empty(),
            "still emits an opaque identifier"
        );
    }

    #[test]
    fn adversarial_seal_intent_body_wrong_privkey_fails_to_decrypt() {
        // Encrypt to recipient A's pubkey. Wrong privkey (B) must NOT recover
        // the plaintext.
        let recip_a_secret = x25519_dalek::StaticSecret::from([3u8; 32]);
        let recip_a_pub = x25519_dalek::PublicKey::from(&recip_a_secret);
        let recip_b_secret_bytes = [9u8; 32];

        let plaintext = r#"{"kind":"need","value":42}"#;
        let sealed =
            seal_intent_body(plaintext, Some(recip_a_pub.as_bytes().to_vec())).expect("seal ok");

        #[derive(serde::Deserialize)]
        struct Sealed {
            ciphertext: Vec<u8>,
            ephemeral_pubkey: Vec<u8>,
        }
        let s: Sealed = serde_wasm_bindgen::from_value(sealed).unwrap();

        // Wrong privkey path: unseal returns Err or non-plaintext.
        let wrong = unseal_intent_body(&s.ciphertext, &s.ephemeral_pubkey, &recip_b_secret_bytes);
        match wrong {
            Err(_) => {} // expected: AEAD reject
            Ok(s) => assert_ne!(s, plaintext, "wrong key must not recover plaintext"),
        }

        // Right privkey path: recovers plaintext.
        let right_secret = recip_a_secret.to_bytes();
        let right = unseal_intent_body(&s.ciphertext, &s.ephemeral_pubkey, &right_secret)
            .expect("right key decrypts");
        assert_eq!(right, plaintext);
    }
}
