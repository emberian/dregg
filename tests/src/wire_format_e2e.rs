//! End-to-end wire format integration test for the pyana presentation protocol.
//!
//! This test exercises the EXACT production path:
//!   wallet.authorize() -> serialize -> PyanaEngine::verify
//!
//! It exists to catch the P0 wire format mismatch where the wallet outputs raw
//! STARK bytes but the engine expects postcard-encoded `WirePresentationProof`.
//! If this test passes, the headline product demo works.
//! If it fails, we have a wire protocol mismatch.

use pyana_circuit::BabyBear;
use pyana_circuit::merkle_air::MerkleAir;
use pyana_circuit::poseidon2;

// =============================================================================
// Helpers (mirror the wallet's internal derivation logic)
// =============================================================================

fn test_key(name: &str) -> [u8; 32] {
    *blake3::hash(format!("wire-format-e2e:{name}").as_bytes()).as_bytes()
}

/// Compute the federation root for an issuer key, mirroring AgentWallet::compute_federation_root_bb.
fn compute_federation_root_bb(issuer_key: &[u8; 32]) -> BabyBear {
    let issuer_hash = wallet_bytes_to_babybear(issuer_key);
    let depth = 8;
    let mut current = issuer_hash;
    for i in 0..depth {
        let position = (i % 4) as u8;
        let siblings = [
            BabyBear::new(hash_index(i, 0, issuer_key)),
            BabyBear::new(hash_index(i, 1, issuer_key)),
            BabyBear::new(hash_index(i, 2, issuer_key)),
        ];
        let position_bb = BabyBear::new(position as u32);
        current = poseidon2::hash_fact(
            current,
            &[siblings[0], siblings[1], siblings[2], position_bb],
        );
    }
    current
}

fn wallet_bytes_to_babybear(bytes: &[u8; 32]) -> BabyBear {
    let limbs = BabyBear::encode_hash(bytes);
    poseidon2::hash_many(&limbs)
}

fn hash_index(level: usize, sibling_idx: usize, key: &[u8; 32]) -> u32 {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&level.to_le_bytes());
    hasher.update(&sibling_idx.to_le_bytes());
    hasher.update(key);
    let hash = hasher.finalize();
    let bytes = hash.as_bytes();
    u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]) % pyana_circuit::field::BABYBEAR_P
}

fn bb_to_bytes(bb: BabyBear) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    bytes[..4].copy_from_slice(&bb.as_u32().to_le_bytes());
    bytes
}

// =============================================================================
// The Test
// =============================================================================

/// End-to-end test: wallet.authorize() -> serialize -> PyanaEngine::verify
///
/// This test exercises the EXACT path a production deployment uses:
/// wallet outputs bytes, engine verifies bytes, action binding checked,
/// freshness checked, root checked.
///
/// If this test passes, the headline product demo works.
/// If it fails, we have a wire protocol mismatch.
#[test]
fn wire_format_e2e_happy_path_and_adversarial() {
    // =========================================================================
    // Setup
    // =========================================================================

    let root_key = test_key("issuer");

    // --- Step 1: Create AgentWallet ---
    let mut wallet = AgentWallet::new();

    // --- Step 2: Mint a root token ---
    let held_token = wallet.mint_token(&root_key, "storage");

    // --- Step 3: Create an AuthRequest ---
    let now_ts: i64 = 1700000000; // fixed timestamp for reproducibility
    let request = AuthRequest {
        action: Some("read".into()),
        service: Some("storage".into()),
        now: Some(now_ts),
        ..Default::default()
    };

    // --- Step 4: wallet.authorize() in FullyPrivate mode -> get proof bytes ---
    let presentation = wallet
        .authorize(&held_token, &request, VerificationMode::FullyPrivate)
        .expect("wallet.authorize() should succeed for a valid root token");

    let proof_bytes = match &presentation {
        pyana_sdk::AuthorizationPresentation::Private { proof, conclusion } => {
            assert!(
                *conclusion,
                "conclusion should be true for a valid authorization"
            );
            proof.clone()
        }
        other => panic!(
            "expected Private presentation, got {:?}",
            std::mem::discriminant(other)
        ),
    };

    assert!(
        !proof_bytes.is_empty(),
        "proof_bytes from wallet.authorize() must not be empty"
    );

    // --- Step 5: Create PyanaEngine with matching federation root ---
    // The wallet uses derive_proof_key(root_key) for federation membership, not root_key directly.
    let proof_key = blake3::derive_key("pyana-proof-key-v1", &root_key);
    let federation_root_bb = compute_federation_root_bb(&proof_key);
    let federation_root_bytes = bb_to_bytes(federation_root_bb);

    let config = EngineConfig {
        timestamp: now_ts,
        max_proof_age_secs: 300,
        ..EngineConfig::new(now_ts)
    };
    let mut engine = PyanaEngine::new(config);
    engine.set_federation_root(federation_root_bytes);

    // --- Step 6: Verify via the canonical engine path ---
    // This is the PRODUCTION path: engine receives bytes and verifies.
    let verify_result = engine.verify_presentation_bytes(&proof_bytes, "read", "storage");

    // --- Step 7: Assert: passes ---
    match verify_result {
        Ok(true) => {
            // SUCCESS: The wire format round-trip works end-to-end.
        }
        Ok(false) => {
            // Decode and call verify_proof_complete directly for detailed diagnostics.
            let wire_proof: WirePresentationProof =
                postcard::from_bytes(&proof_bytes).expect("already decoded above");
            let detail = pyana_bridge::verify_proof_complete(
                &wire_proof,
                "read",
                "storage",
                &federation_root_bytes,
                now_ts,
                300,
            );
            panic!(
                "WIRE FORMAT / BINDING MISMATCH (P0): engine.verify_presentation_bytes() returned Ok(false).\n\
                 Detailed verify_proof_complete error: {:?}\n\
                 \n\
                 This means the proof bytes produced by wallet.authorize() do not satisfy\n\
                 the engine's verification checks. The wire format or binding P0 bug is present.",
                detail.err()
            );
        }
        Err(e) => {
            panic!(
                "WIRE FORMAT MISMATCH (P0): engine.verify_presentation_bytes() returned Err({:?}).\n\
                 This means the proof bytes produced by wallet.authorize() could not even be\n\
                 decoded as a WirePresentationProof. The serialization format mismatch P0 bug\n\
                 is present (wallet outputs raw STARK bytes, engine expects postcard WirePresentationProof).",
                e
            );
        }
    }

    // =========================================================================
    // Adversarial Case 8: Wrong action -> MUST fail
    // =========================================================================

    let wrong_action_result = engine.verify_presentation_bytes(&proof_bytes, "admin", "storage");
    match wrong_action_result {
        Ok(true) => {
            panic!(
                "SECURITY BUG: proof bound to action='read' was accepted for action='admin'!\n\
                 Action binding is not enforced."
            );
        }
        Ok(false) | Err(_) => {
            // Expected: action binding mismatch correctly rejected.
        }
    }

    // =========================================================================
    // Adversarial Case 9: Wrong resource -> MUST fail
    // =========================================================================

    let wrong_resource_result = engine.verify_presentation_bytes(&proof_bytes, "read", "secrets");
    match wrong_resource_result {
        Ok(true) => {
            panic!(
                "SECURITY BUG: proof bound to resource='storage' was accepted for resource='secrets'!\n\
                 Resource binding is not enforced."
            );
        }
        Ok(false) | Err(_) => {
            // Expected: resource binding mismatch correctly rejected.
        }
    }

    // =========================================================================
    // Adversarial Case 10: Wrong federation root -> MUST fail
    // =========================================================================

    let wrong_root = test_key("wrong-issuer");
    let wrong_root_bb = compute_federation_root_bb(&wrong_root);
    let wrong_root_bytes = bb_to_bytes(wrong_root_bb);

    let wrong_root_result =
        engine.verify_presentation_against(&proof_bytes, &wrong_root_bytes, "read", "storage");
    match wrong_root_result {
        Ok(true) => {
            panic!(
                "SECURITY BUG: proof bound to one federation root was accepted against a different root!\n\
                 Federation root binding is not enforced."
            );
        }
        Ok(false) | Err(_) => {
            // Expected: wrong root correctly rejected.
        }
    }

    // =========================================================================
    // Adversarial Case 11: Stale proof (engine timestamp far in future) -> MUST fail
    // =========================================================================

    let future_config = EngineConfig {
        timestamp: now_ts + 3600, // 1 hour in the future
        max_proof_age_secs: 300,  // 5 minute window
        ..EngineConfig::new(now_ts + 3600)
    };
    let mut future_engine = PyanaEngine::new(future_config);
    future_engine.set_federation_root(federation_root_bytes);

    let stale_result = future_engine.verify_presentation_bytes(&proof_bytes, "read", "storage");
    match stale_result {
        Ok(true) => {
            panic!(
                "SECURITY BUG: proof with timestamp={} was accepted by engine at timestamp={}\n\
                 with max_proof_age_secs=300. Freshness check is not enforced.",
                now_ts,
                now_ts + 3600
            );
        }
        Ok(false) | Err(_) => {
            // Expected: stale proof correctly rejected.
        }
    }

    // =========================================================================
    // Adversarial Case 12: Empty bytes -> MUST fail
    // =========================================================================

    let empty_result = engine.verify_presentation_bytes(&[], "read", "storage");
    match empty_result {
        Ok(true) => {
            panic!("SECURITY BUG: empty bytes accepted as a valid proof!");
        }
        Ok(false) | Err(_) => {
            // Expected: empty bytes rejected.
        }
    }

    // =========================================================================
    // Adversarial Case 13: Garbage bytes -> MUST fail
    // =========================================================================

    let garbage: Vec<u8> = (0..256).map(|i| (i * 37 + 13) as u8).collect();
    let garbage_result = engine.verify_presentation_bytes(&garbage, "read", "storage");
    match garbage_result {
        Ok(true) => {
            panic!("SECURITY BUG: random garbage bytes accepted as a valid proof!");
        }
        Ok(false) | Err(_) => {
            // Expected: garbage bytes rejected.
        }
    }
}

// =============================================================================
// Wire Format Roundtrip Test (Case 14)
// =============================================================================

/// The bytes output by `wallet.authorize()` must be decodable as
/// `postcard::from_bytes::<WirePresentationProof>()`.
///
/// If this test fails, the P0 format mismatch still exists: the wallet is
/// emitting raw STARK bytes instead of the structured WirePresentationProof.
#[test]
fn wire_format_roundtrip_postcard_decodable() {
    let root_key = test_key("roundtrip-issuer");
    let mut wallet = AgentWallet::new();
    let held_token = wallet.mint_token(&root_key, "api");

    let request = AuthRequest {
        action: Some("read".into()),
        service: Some("api".into()),
        now: Some(1700000000),
        ..Default::default()
    };

    let presentation = wallet
        .authorize(&held_token, &request, VerificationMode::FullyPrivate)
        .expect("authorize should succeed");

    let proof_bytes = match &presentation {
        pyana_sdk::AuthorizationPresentation::Private { proof, .. } => proof.clone(),
        _ => panic!("expected Private variant"),
    };

    // THE KEY ASSERTION: the bytes must deserialize as WirePresentationProof.
    // If this fails, wallet is emitting raw STARK bytes (the P0 bug).
    let decoded: Result<WirePresentationProof, _> = postcard::from_bytes(&proof_bytes);
    match decoded {
        Ok(wire_proof) => {
            // Further sanity checks on the decoded proof structure.
            assert!(
                wire_proof.real_stark_proof.is_some(),
                "WirePresentationProof should contain a real STARK proof (not a stub)"
            );

            let real = wire_proof.real_stark_proof.as_ref().unwrap();
            assert!(
                !real.issuer_membership_stark_proof.query_proofs.is_empty(),
                "STARK proof should have query proofs (not synthetic)"
            );
            assert!(
                real.issuer_membership_stark_proof.public_inputs.len()
                    >= 2 + pyana_circuit::ACTION_BINDING_WIDTH,
                "STARK proof should have enough public inputs for root + action binding, got {}",
                real.issuer_membership_stark_proof.public_inputs.len()
            );
        }
        Err(e) => {
            panic!(
                "WIRE FORMAT P0 BUG DETECTED: wallet.authorize() output cannot be decoded as\n\
                 WirePresentationProof via postcard. The wallet is likely emitting raw STARK\n\
                 bytes instead of the structured wire format.\n\
                 \n\
                 Decode error: {}\n\
                 Proof bytes length: {}\n\
                 First 32 bytes: {:02x?}",
                e,
                proof_bytes.len(),
                &proof_bytes[..proof_bytes.len().min(32)]
            );
        }
    }
}
