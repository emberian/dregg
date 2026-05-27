//! SP1 proof wrapping: STARK proof -> Groth16 proof for EVM verification.

use crate::error::ChainError;
use serde::{Deserialize, Serialize};

// ============================================================================
// Guest-compatible STARK proof types (subset of circuit crate's StarkProof)
// ============================================================================

/// STARK proof structure compatible with the SP1 guest program.
///
/// This mirrors the guest program's `StarkProof` struct exactly. It omits fields
/// present in the circuit crate's version (`air_name`, `nonce`, `boundary_commitment`,
/// `boundary_query_values`, `boundary_query_paths`) that the guest verifier doesn't use.
#[cfg(feature = "prove")]
#[derive(Clone, Debug, Serialize, Deserialize)]
struct GuestStarkProof {
    trace_commitment: [u8; 32],
    constraint_commitment: [u8; 32],
    fri_commitments: Vec<[u8; 32]>,
    fri_final_poly: Vec<u32>,
    query_proofs: Vec<GuestQueryProof>,
    public_inputs: Vec<u32>,
    trace_len: usize,
    num_cols: usize,
}

#[cfg(feature = "prove")]
#[derive(Clone, Debug, Serialize, Deserialize)]
struct GuestQueryProof {
    index: usize,
    trace_values: Vec<u32>,
    trace_path: Vec<[u8; 32]>,
    next_trace_values: Vec<u32>,
    next_trace_path: Vec<[u8; 32]>,
    constraint_value: u32,
    constraint_path: Vec<[u8; 32]>,
    constraint_sibling_value: u32,
    constraint_sibling_pos: usize,
    constraint_sibling_path: Vec<[u8; 32]>,
    fri_layers: Vec<GuestFriLayerQuery>,
}

#[cfg(feature = "prove")]
#[derive(Clone, Debug, Serialize, Deserialize)]
struct GuestFriLayerQuery {
    query_pos: usize,
    query_value: u32,
    query_path: Vec<[u8; 32]>,
    sibling_pos: usize,
    sibling_value: u32,
    sibling_path: Vec<[u8; 32]>,
}

/// Deserialize a STARK proof from the `proof_to_bytes()` binary format into
/// the guest-compatible struct.
///
/// The binary format starts with `DREG` magic (4 bytes) + version byte (1 byte),
/// then contains the proof fields in a fixed order. We parse this and produce
/// a `GuestStarkProof` that can be bincode-serialized into SP1 stdin.
#[cfg(feature = "prove")]
fn deserialize_for_guest(bytes: &[u8]) -> Result<GuestStarkProof, String> {
    if bytes.len() < 5 || &bytes[0..4] != b"DREG" {
        return Err("missing DREG magic header".to_string());
    }
    let _version = bytes[4];
    let mut pos = 5;

    let ru32 = |p: &mut usize, b: &[u8]| -> Result<u32, String> {
        if *p + 4 > b.len() {
            return Err("unexpected end of proof bytes".to_string());
        }
        let val = u32::from_le_bytes([b[*p], b[*p + 1], b[*p + 2], b[*p + 3]]);
        *p += 4;
        Ok(val)
    };
    let rhash = |p: &mut usize, b: &[u8]| -> Result<[u8; 32], String> {
        if *p + 32 > b.len() {
            return Err("unexpected end of proof bytes (hash)".to_string());
        }
        let mut h = [0u8; 32];
        h.copy_from_slice(&b[*p..*p + 32]);
        *p += 32;
        Ok(h)
    };

    let trace_commitment = rhash(&mut pos, bytes)?;
    let constraint_commitment = rhash(&mut pos, bytes)?;

    let fri_count = ru32(&mut pos, bytes)? as usize;
    let mut fri_commitments = Vec::with_capacity(fri_count);
    for _ in 0..fri_count {
        fri_commitments.push(rhash(&mut pos, bytes)?);
    }

    let final_poly_len = ru32(&mut pos, bytes)? as usize;
    let mut fri_final_poly = Vec::with_capacity(final_poly_len);
    for _ in 0..final_poly_len {
        fri_final_poly.push(ru32(&mut pos, bytes)?);
    }

    let pi_count = ru32(&mut pos, bytes)? as usize;
    let mut public_inputs = Vec::with_capacity(pi_count);
    for _ in 0..pi_count {
        public_inputs.push(ru32(&mut pos, bytes)?);
    }

    let trace_len = ru32(&mut pos, bytes)? as usize;
    let num_cols = ru32(&mut pos, bytes)? as usize;

    let query_count = ru32(&mut pos, bytes)? as usize;
    let mut query_proofs = Vec::with_capacity(query_count);
    for _ in 0..query_count {
        let index = ru32(&mut pos, bytes)? as usize;

        let tv_len = ru32(&mut pos, bytes)? as usize;
        let mut trace_values = Vec::with_capacity(tv_len);
        for _ in 0..tv_len {
            trace_values.push(ru32(&mut pos, bytes)?);
        }

        let tp_len = ru32(&mut pos, bytes)? as usize;
        let mut trace_path = Vec::with_capacity(tp_len);
        for _ in 0..tp_len {
            trace_path.push(rhash(&mut pos, bytes)?);
        }

        let ntv_len = ru32(&mut pos, bytes)? as usize;
        let mut next_trace_values = Vec::with_capacity(ntv_len);
        for _ in 0..ntv_len {
            next_trace_values.push(ru32(&mut pos, bytes)?);
        }

        let ntp_len = ru32(&mut pos, bytes)? as usize;
        let mut next_trace_path = Vec::with_capacity(ntp_len);
        for _ in 0..ntp_len {
            next_trace_path.push(rhash(&mut pos, bytes)?);
        }

        let constraint_value = ru32(&mut pos, bytes)?;

        let cp_len = ru32(&mut pos, bytes)? as usize;
        let mut constraint_path = Vec::with_capacity(cp_len);
        for _ in 0..cp_len {
            constraint_path.push(rhash(&mut pos, bytes)?);
        }

        let constraint_sibling_value = ru32(&mut pos, bytes)?;
        let constraint_sibling_pos = ru32(&mut pos, bytes)? as usize;

        let csp_len = ru32(&mut pos, bytes)? as usize;
        let mut constraint_sibling_path = Vec::with_capacity(csp_len);
        for _ in 0..csp_len {
            constraint_sibling_path.push(rhash(&mut pos, bytes)?);
        }

        let fri_layer_count = ru32(&mut pos, bytes)? as usize;
        let mut fri_layers = Vec::with_capacity(fri_layer_count);
        for _ in 0..fri_layer_count {
            let query_pos = ru32(&mut pos, bytes)? as usize;
            let query_value = ru32(&mut pos, bytes)?;

            let qp_len = ru32(&mut pos, bytes)? as usize;
            let mut query_path = Vec::with_capacity(qp_len);
            for _ in 0..qp_len {
                query_path.push(rhash(&mut pos, bytes)?);
            }

            let sibling_pos = ru32(&mut pos, bytes)? as usize;
            let sibling_value = ru32(&mut pos, bytes)?;

            let sp_len = ru32(&mut pos, bytes)? as usize;
            let mut sibling_path = Vec::with_capacity(sp_len);
            for _ in 0..sp_len {
                sibling_path.push(rhash(&mut pos, bytes)?);
            }

            fri_layers.push(GuestFriLayerQuery {
                query_pos,
                query_value,
                query_path,
                sibling_pos,
                sibling_value,
                sibling_path,
            });
        }

        query_proofs.push(GuestQueryProof {
            index,
            trace_values,
            trace_path,
            next_trace_values,
            next_trace_path,
            constraint_value,
            constraint_path,
            constraint_sibling_value,
            constraint_sibling_pos,
            constraint_sibling_path,
            fri_layers,
        });
    }

    // Skip remaining fields (air_name, nonce, boundary_*) - not needed by guest

    Ok(GuestStarkProof {
        trace_commitment,
        constraint_commitment,
        fri_commitments,
        fri_final_poly,
        query_proofs,
        public_inputs,
        trace_len,
        num_cols,
    })
}

/// A Groth16 proof ready for EVM on-chain verification.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EvmProof {
    /// The Groth16 proof bytes (formatted for the SP1 verifier contract).
    pub proof_bytes: Vec<u8>,
    /// The public values committed by the SP1 guest program.
    /// Contains: verification_result (bool) + original public inputs (leaf, root).
    pub public_values: Vec<u8>,
    /// The SP1 program verification key (identifies our STARK verifier program).
    pub vkey: String,
    /// The address of the SP1 verifier contract to call.
    pub verifier_address: String,
}

/// Generate a Groth16 proof wrapping a dregg STARK proof for EVM verification.
///
/// This function:
/// 1. Sets up the SP1 prover with our guest program ELF
/// 2. Passes the STARK proof + public inputs as guest program inputs
/// 3. Executes the guest (which runs the full STARK verifier)
/// 4. Generates a Groth16 proof of correct execution
/// 5. Returns proof bytes formatted for the on-chain SP1 verifier
///
/// # Arguments
/// * `stark_proof_bytes` - Serialized STARK proof (from `circuit::stark::proof_to_bytes()`)
/// * `public_inputs` - The public inputs (e.g., `[leaf_hash, merkle_root]` as u32 field elements)
///
/// # Requirements
/// Without the `prove` feature (default `mock` mode), this produces simulated proofs
/// suitable for testing the integration flow. With `prove` enabled:
/// - SP1 toolchain must be installed (`sp1up`)
/// - Guest program must be built (`cd chain/program && cargo prove build`)
///
/// # Returns
/// An `EvmProof` containing the Groth16 proof bytes and metadata for on-chain submission.
pub async fn wrap_for_evm(
    stark_proof_bytes: &[u8],
    public_inputs: &[u32],
) -> Result<EvmProof, ChainError> {
    #[cfg(feature = "mock")]
    {
        return mock_wrap(stark_proof_bytes, public_inputs).await;
    }

    #[cfg(all(feature = "prove", not(feature = "mock")))]
    {
        return real_wrap(stark_proof_bytes, public_inputs).await;
    }

    #[cfg(not(any(feature = "mock", feature = "prove")))]
    {
        let _ = (stark_proof_bytes, public_inputs);
        Err(ChainError::ToolchainMissing)
    }
}

/// Mock implementation for development without SP1 toolchain.
#[cfg(feature = "mock")]
async fn mock_wrap(
    stark_proof_bytes: &[u8],
    public_inputs: &[u32],
) -> Result<EvmProof, ChainError> {
    use blake3::Hasher;

    // Validate that the proof bytes look reasonable
    if stark_proof_bytes.len() < 5 || &stark_proof_bytes[0..4] != b"DREG" {
        return Err(ChainError::InvalidProof(
            "invalid proof header (expected DREG magic)".to_string(),
        ));
    }

    // Generate a deterministic mock proof (hash of inputs)
    let mut hasher = Hasher::new();
    hasher.update(b"mock-groth16-proof:");
    hasher.update(stark_proof_bytes);
    for pi in public_inputs {
        hasher.update(&pi.to_le_bytes());
    }
    let mock_proof = hasher.finalize().as_bytes().to_vec();

    // Serialize public values as the guest would
    let public_values = bincode::serialize(&(true, public_inputs.to_vec()))
        .map_err(|e| ChainError::InvalidProof(e.to_string()))?;

    Ok(EvmProof {
        proof_bytes: mock_proof,
        public_values,
        vkey: crate::SP1_PROGRAM_VKEY.to_string(),
        verifier_address: crate::contracts::BASE_MAINNET.to_string(),
    })
}

/// Real SP1 proving implementation (requires SP1 toolchain).
///
/// This compiles and runs only with `--features prove`.
/// The SP1 toolchain (`sp1up`) must be installed and the guest program
/// must have been built with `cargo prove build`.
#[cfg(all(feature = "prove", not(feature = "mock")))]
async fn real_wrap(
    stark_proof_bytes: &[u8],
    public_inputs: &[u32],
) -> Result<EvmProof, ChainError> {
    use sp1_sdk::{
        include_elf, HashableKey, ProveRequest, Prover, ProverClient, ProvingKey, SP1Stdin,
    };

    // Load the guest program ELF (built by `cargo prove build`).
    // include_elf! embeds the ELF at compile time from the build artifact produced
    // by sp1-build in build.rs.
    let elf = include_elf!("dregg-sp1-program");

    // Set up the CPU prover (local proving, no network).
    let prover = ProverClient::builder().cpu().build().await;

    // Prepare stdin with the STARK proof and public inputs.
    let mut stdin = SP1Stdin::new();

    // Deserialize the STARK proof from the custom binary format (DREG header + fields).
    // The guest program expects a bincode-serialized StarkProof (matching its struct layout).
    // We parse the proof_to_bytes() output and write the guest-compatible struct.
    //
    // NOTE: The guest's StarkProof struct omits `air_name`, `nonce`, and `boundary_*`
    // fields from the circuit crate's version. The host strips these during deserialization.
    let guest_proof = deserialize_for_guest(stark_proof_bytes)
        .map_err(|e| ChainError::InvalidProof(format!("failed to parse STARK proof: {e}")))?;
    stdin.write(&guest_proof);
    stdin.write(&public_inputs.to_vec());

    // Setup proving key from ELF.
    let pk = prover
        .setup(elf)
        .await
        .map_err(|e| ChainError::ProvingFailed(format!("{e}")))?;

    // Generate the Groth16 proof (this is the expensive step - may take minutes).
    // The guest executes the full STARK verifier inside the RISC-V zkVM, then SP1
    // wraps that execution trace in a Groth16 proof verifiable on EVM (~200k gas).
    let proof_result = prover
        .prove(&pk, stdin)
        .groth16()
        .await
        .map_err(|e| ChainError::ProvingFailed(format!("{e}")))?;

    // Extract the proof bytes formatted for the EVM verifier contract.
    let proof_bytes = proof_result.bytes();
    let public_values = proof_result.public_values.as_slice().to_vec();
    let vkey = pk.verifying_key().bytes32();

    Ok(EvmProof {
        proof_bytes,
        public_values,
        vkey,
        verifier_address: crate::contracts::BASE_MAINNET.to_string(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_wrap_rejects_invalid_proof() {
        let result = wrap_for_evm(b"garbage", &[1, 2]).await;
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), ChainError::InvalidProof(_)));
    }

    #[cfg(feature = "mock")]
    #[tokio::test]
    async fn test_mock_wrap_accepts_valid_header() {
        // Minimal valid-looking proof: DREG magic + version byte + some data
        let mut fake_proof = b"DREG".to_vec();
        fake_proof.push(1);
        fake_proof.extend_from_slice(&[0u8; 100]);

        let result = wrap_for_evm(&fake_proof, &[12345, 67890]).await;
        assert!(result.is_ok());

        let evm_proof = result.unwrap();
        assert!(!evm_proof.proof_bytes.is_empty());
        assert!(!evm_proof.public_values.is_empty());
        assert!(!evm_proof.verifier_address.is_empty());
    }

    #[cfg(feature = "mock")]
    #[tokio::test]
    async fn test_mock_wrap_deterministic() {
        let mut proof = b"DREG".to_vec();
        proof.push(1);
        proof.extend_from_slice(&[42u8; 64]);

        let r1 = wrap_for_evm(&proof, &[1, 2]).await.unwrap();
        let r2 = wrap_for_evm(&proof, &[1, 2]).await.unwrap();
        assert_eq!(r1.proof_bytes, r2.proof_bytes);
    }

    #[cfg(feature = "prove")]
    #[test]
    fn test_deserialize_for_guest_rejects_invalid() {
        assert!(deserialize_for_guest(b"not a proof").is_err());
        assert!(deserialize_for_guest(b"DREG").is_err()); // too short, no version byte

        // Valid header but truncated body
        let mut bytes = b"DREG".to_vec();
        bytes.push(1); // version
        bytes.extend_from_slice(&[0u8; 10]); // not enough for trace_commitment (32 bytes)
        assert!(deserialize_for_guest(&bytes).is_err());
    }
}
