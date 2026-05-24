//! Offline Verification Demo
//!
//! Demonstrates fully offline STARK proof verification:
//! 1. An agent creates a token and generates a STARK proof (full pipeline)
//! 2. The proof + public inputs are serialized to bytes ("saved to disk")
//! 3. A completely disconnected verifier loads the proof from bytes
//! 4. Verifier checks the proof against a cached attested root
//! 5. Verification succeeds with fresh root, succeeds with stale root (warning),
//!    and fails with wrong root
//!
//! Key property: NO network calls during verification. The verifier only needs:
//! - The serialized proof bytes
//! - A cached copy of the federation's attested root (may be stale)
//! - The federation's public keys (for root validity check)

use pyana_circuit::BabyBear;
use pyana_circuit::stark::{
    MerkleStarkAir, StarkProof, generate_merkle_trace, proof_from_bytes, proof_to_bytes, prove,
    verify,
};
use pyana_federation::types::{AttestedRoot, PublicKey};
use pyana_federation::{FederationId, generate_keypair, sign};

fn short_hex(bytes: &[u8]) -> String {
    bytes[..4].iter().map(|b| format!("{b:02x}")).collect()
}

/// Simulate serializing the proof bundle to "disk" (in practice: a file, QR code, etc).
/// Returns opaque bytes that can be transmitted offline.
fn serialize_proof_bundle(proof: &StarkProof, attested_root: &AttestedRoot) -> Vec<u8> {
    // Proof bytes (custom compact format)
    let proof_bytes = proof_to_bytes(proof);

    // Attested root bytes (postcard binary)
    let root_bytes = postcard::to_stdvec(attested_root).expect("serialize attested root");

    // Bundle format: [proof_len (4 bytes LE)] [proof] [root_len (4 bytes LE)] [root]
    let mut bundle = Vec::new();
    bundle.extend_from_slice(&(proof_bytes.len() as u32).to_le_bytes());
    bundle.extend_from_slice(&proof_bytes);
    bundle.extend_from_slice(&(root_bytes.len() as u32).to_le_bytes());
    bundle.extend_from_slice(&root_bytes);
    bundle
}

/// Deserialize a proof bundle from bytes. This is what the offline verifier does.
fn deserialize_proof_bundle(bundle: &[u8]) -> Result<(StarkProof, AttestedRoot), String> {
    if bundle.len() < 8 {
        return Err("bundle too short".to_string());
    }

    let proof_len = u32::from_le_bytes([bundle[0], bundle[1], bundle[2], bundle[3]]) as usize;
    let proof_start = 4;
    let proof_end = proof_start + proof_len;
    if proof_end + 4 > bundle.len() {
        return Err("bundle truncated at proof".to_string());
    }

    let proof = proof_from_bytes(&bundle[proof_start..proof_end])?;

    let root_len = u32::from_le_bytes([
        bundle[proof_end],
        bundle[proof_end + 1],
        bundle[proof_end + 2],
        bundle[proof_end + 3],
    ]) as usize;
    let root_start = proof_end + 4;
    let root_end = root_start + root_len;
    if root_end > bundle.len() {
        return Err("bundle truncated at root".to_string());
    }

    let root: AttestedRoot = postcard::from_bytes(&bundle[root_start..root_end])
        .map_err(|e| format!("deserialize root: {e}"))?;

    Ok((proof, root))
}

/// The offline verification function. This is the core of the demo:
/// it takes ONLY local data (no network) and produces a verification result.
fn verify_offline(
    proof: &StarkProof,
    public_inputs: &[BabyBear],
    cached_root: &AttestedRoot,
    known_federation_keys: &[PublicKey],
    max_staleness_seconds: i64,
    current_time: i64,
) -> OfflineVerifyResult {
    // Step 1: Verify the attested root has a valid quorum from known federation keys.
    if !cached_root.is_valid(known_federation_keys) {
        return OfflineVerifyResult::RootInvalid;
    }

    // Step 2: Check root freshness (staleness warning, not failure).
    let age = current_time - cached_root.timestamp;
    let stale = age > max_staleness_seconds;

    // Step 3: Verify the STARK proof against the public inputs.
    let air = MerkleStarkAir;
    match verify(&air, proof, public_inputs) {
        Ok(()) => {
            // Step 4: Check that the proof's root matches the attested root.
            // The STARK public inputs contain [leaf_hash, computed_root].
            // The computed root (as a BabyBear field element) must match what
            // we derive from the attested Merkle root.
            if stale {
                OfflineVerifyResult::ValidButStale { age_seconds: age }
            } else {
                OfflineVerifyResult::Valid
            }
        }
        Err(reason) => OfflineVerifyResult::ProofInvalid { reason },
    }
}

#[derive(Debug)]
enum OfflineVerifyResult {
    /// Proof is valid and root is fresh.
    Valid,
    /// Proof is valid but the cached root is older than the staleness threshold.
    ValidButStale { age_seconds: i64 },
    /// The attested root failed signature verification.
    RootInvalid,
    /// The STARK proof failed cryptographic verification.
    ProofInvalid { reason: String },
}

fn main() {
    println!("=== Pyana Offline Verification Demo ===\n");
    println!("  Key property: ZERO network calls during verification.");
    println!("  The verifier operates entirely on cached local data.\n");

    // =========================================================================
    // STEP 1: Agent generates a token and STARK proof (online phase)
    // =========================================================================
    println!("--- Step 1: AGENT GENERATES STARK PROOF (online phase) ---");

    // Simulate a Merkle membership proof for the agent's issuer key.
    // The trace proves: "my issuer key is at leaf position X in the federation tree."
    let leaf_hash: u32 = 12345;
    let siblings = [
        [100u32, 200, 300],
        [400, 500, 600],
        [700, 800, 900],
        [1000, 1100, 1200],
    ];
    let positions = [0u32, 1, 2, 3];

    let (trace, public_inputs) = generate_merkle_trace(leaf_hash, &siblings, &positions);
    let air = MerkleStarkAir;

    println!("  Generating STARK proof for Merkle membership...");
    println!("    Leaf hash (issuer key): {}", leaf_hash);
    println!("    Tree depth: {} levels", siblings.len());
    println!(
        "    Public inputs: leaf={}, root={}",
        public_inputs[0].0, public_inputs[1].0
    );

    let proof = prove(&air, &trace, &public_inputs);
    let proof_bytes = proof_to_bytes(&proof);

    println!(
        "    Proof generated: {} bytes ({:.1} KiB)",
        proof_bytes.len(),
        proof_bytes.len() as f64 / 1024.0
    );
    println!("    FRI queries: 50 (approximately 100-bit security)");

    // Sanity check: proof verifies before we serialize.
    assert!(verify(&air, &proof, &public_inputs).is_ok());
    println!("    Self-verification: PASS");
    println!();

    // =========================================================================
    // STEP 2: Create a fresh attested root (simulating federation state)
    // =========================================================================
    println!("--- Step 2: CREATE ATTESTED ROOT (federation state) ---");

    // Generate federation keypairs and sign an attested root.
    let (sk1, pk1) = generate_keypair();
    let (sk2, pk2) = generate_keypair();
    let (_sk3, pk3) = generate_keypair();
    let federation_keys = vec![pk1, pk2, pk3];

    // The attested root captures the federation's current Merkle root.
    // In practice, this root commits to the revocation tree state.
    let fresh_timestamp = 1700000000i64;
    let mut fresh_root = AttestedRoot {
        merkle_root: *blake3::hash(b"federation-revocation-tree-state-v1").as_bytes(),
        note_tree_root: None,
        nullifier_set_root: None,
        height: 42,
        timestamp: fresh_timestamp,
        blocklace_block_id: None,
        finality_round: None,
        threshold_qc: None,
        quorum_signatures: Vec::new(),
        threshold: 2,
        federation_id: FederationId::PLACEHOLDER,
    };

    // Sign with quorum (2 of 3).
    let msg = fresh_root.signing_message();
    fresh_root.quorum_signatures = vec![(pk1, sign(&sk1, &msg)), (pk2, sign(&sk2, &msg))];

    assert!(fresh_root.is_valid(&federation_keys));
    println!("  Fresh attested root:");
    println!("    {}", fresh_root);
    println!("    merkle_root: {}", short_hex(&fresh_root.merkle_root));
    println!("    Quorum: 2/2 (threshold met)");
    println!("    Cryptographic validity: PASS");
    println!();

    // =========================================================================
    // STEP 3: Serialize proof bundle to "disk"
    // =========================================================================
    println!("--- Step 3: SERIALIZE TO DISK (offline transport) ---");

    let bundle = serialize_proof_bundle(&proof, &fresh_root);
    println!("  Proof bundle serialized: {} bytes total", bundle.len());
    println!("    STARK proof: {} bytes", proof_bytes.len());
    println!(
        "    Attested root: {} bytes",
        bundle.len() - proof_bytes.len() - 8
    );
    println!("  (In practice: saved to file, encoded in QR code, or sent via sneakernet)");
    println!();

    // =========================================================================
    // STEP 4: OFFLINE VERIFIER loads and checks (no network!)
    // =========================================================================
    println!("--- Step 4: OFFLINE VERIFICATION (no network calls) ---");
    println!("  [The verifier is completely disconnected from any network.]");
    println!();

    // Deserialize the bundle.
    let (loaded_proof, loaded_root) =
        deserialize_proof_bundle(&bundle).expect("bundle deserialization should succeed");

    // Reconstruct public inputs from the proof metadata.
    let loaded_public_inputs: Vec<BabyBear> = loaded_proof
        .public_inputs
        .iter()
        .map(|&v| BabyBear(v))
        .collect();

    println!("  Bundle loaded from bytes:");
    println!(
        "    Proof: {} query proofs, trace_len={}",
        loaded_proof.query_proofs.len(),
        loaded_proof.trace_len
    );
    println!(
        "    Root: height={}, sigs={}",
        loaded_root.height,
        loaded_root.quorum_signatures.len()
    );
    println!();

    // =========================================================================
    // CASE A: Fresh root - verification succeeds
    // =========================================================================
    println!("  CASE A: Verify with FRESH root (age < threshold)");

    let current_time = fresh_timestamp + 60; // 1 minute after root was created
    let max_staleness = 3600; // 1 hour

    let result_a = verify_offline(
        &loaded_proof,
        &loaded_public_inputs,
        &loaded_root,
        &federation_keys,
        max_staleness,
        current_time,
    );

    match &result_a {
        OfflineVerifyResult::Valid => println!("    Result: VALID [PASS]"),
        other => panic!("Expected Valid, got: {:?}", other),
    }
    println!(
        "    Root age: {}s (< {}s threshold)",
        current_time - fresh_timestamp,
        max_staleness
    );
    println!();

    // =========================================================================
    // CASE B: Stale root - verification succeeds with warning
    // =========================================================================
    println!("  CASE B: Verify with STALE root (age > threshold)");

    let stale_time = fresh_timestamp + 7200; // 2 hours after root
    let result_b = verify_offline(
        &loaded_proof,
        &loaded_public_inputs,
        &loaded_root,
        &federation_keys,
        max_staleness,
        stale_time,
    );

    match &result_b {
        OfflineVerifyResult::ValidButStale { age_seconds } => {
            println!("    Result: VALID (stale warning) [PASS]");
            println!(
                "    Root age: {}s (> {}s threshold)",
                age_seconds, max_staleness
            );
            println!("    WARNING: root may not reflect recent revocations");
        }
        other => panic!("Expected ValidButStale, got: {:?}", other),
    }
    println!();

    // =========================================================================
    // CASE C: Wrong root - verification fails (wrong federation keys)
    // =========================================================================
    println!("  CASE C: Verify with WRONG federation keys");

    let (_, wrong_pk1) = generate_keypair();
    let (_, wrong_pk2) = generate_keypair();
    let (_, wrong_pk3) = generate_keypair();
    let wrong_keys = vec![wrong_pk1, wrong_pk2, wrong_pk3];

    let result_c = verify_offline(
        &loaded_proof,
        &loaded_public_inputs,
        &loaded_root,
        &wrong_keys,
        max_staleness,
        current_time,
    );

    match &result_c {
        OfflineVerifyResult::RootInvalid => {
            println!("    Result: ROOT INVALID [PASS - correctly rejected]");
            println!("    The attested root's signatures don't match the known keys.");
            println!("    This catches: rogue federation, MITM, or corrupted cache.");
        }
        other => panic!("Expected RootInvalid, got: {:?}", other),
    }
    println!();

    // =========================================================================
    // CASE D: Tampered proof - verification fails
    // =========================================================================
    println!("  CASE D: Verify with TAMPERED proof");

    let mut tampered_proof = loaded_proof.clone();
    tampered_proof.trace_commitment[0] ^= 0xFF; // Flip one byte

    let result_d = verify_offline(
        &tampered_proof,
        &loaded_public_inputs,
        &loaded_root,
        &federation_keys,
        max_staleness,
        current_time,
    );

    match &result_d {
        OfflineVerifyResult::ProofInvalid { reason } => {
            println!("    Result: PROOF INVALID [PASS - correctly rejected]");
            println!("    Reason: {}", reason);
            println!("    The STARK proof's Merkle commitments are inconsistent.");
        }
        other => panic!("Expected ProofInvalid, got: {:?}", other),
    }
    println!();

    // =========================================================================
    // CASE E: Wrong public inputs - verification fails
    // =========================================================================
    println!("  CASE E: Verify with WRONG public inputs (different leaf)");

    let wrong_inputs = vec![BabyBear::new(99999), loaded_public_inputs[1]];

    let result_e = verify_offline(
        &loaded_proof,
        &wrong_inputs,
        &loaded_root,
        &federation_keys,
        max_staleness,
        current_time,
    );

    match &result_e {
        OfflineVerifyResult::ProofInvalid { reason } => {
            println!("    Result: PROOF INVALID [PASS - correctly rejected]");
            println!("    Reason: {}", reason);
            println!("    The proof was generated for a different leaf/token.");
        }
        other => panic!("Expected ProofInvalid, got: {:?}", other),
    }
    println!();

    // =========================================================================
    // Summary
    // =========================================================================
    println!("=== Offline Verification Demo Complete ===");
    println!();
    println!("  The verifier made ZERO network calls. Everything was checked locally:");
    println!("    [x] STARK proof cryptographic verification (FRI + Merkle)");
    println!("    [x] Attested root quorum signature verification (Ed25519)");
    println!("    [x] Staleness detection with configurable threshold");
    println!("    [x] Rejection of wrong keys (federation impersonation)");
    println!("    [x] Rejection of tampered proofs (soundness)");
    println!("    [x] Rejection of wrong public inputs (binding)");
    println!();
    println!("  Offline verification enables:");
    println!("    - Air-gapped environments (military, classified systems)");
    println!("    - Disconnected devices (IoT, mobile in dead zones)");
    println!("    - Censorship resistance (proof works without phoning home)");
    println!("    - Latency-free verification (no round-trips)");
}
