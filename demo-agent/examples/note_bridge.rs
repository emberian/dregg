//! Note Bridge Demo — Cross-Federation Value Transfer via Proof-Carrying Notes
//!
//! Demonstrates:
//! 1. Federation A: Alice owns a note (100 GOLD)
//! 2. Alice spends the note in Fed A (nullifier published there)
//! 3. Alice creates a PortableNoteProof
//! 4. Federation B: Bob presents the PortableNoteProof
//! 5. Fed B: verifies the proof against Fed A's trusted root
//! 6. Fed B: mints a new note (100 GOLD) for Bob
//! 7. Show: double-bridge attempt fails (nullifier already used)
//! 8. Show: proof against untrusted root fails
//!
//! The key insight: notes are self-proving. The STARK proof carries all verification
//! needed. No light client, no relay chain, no committee — just math.

use pyana_cell::note::Note;
use pyana_cell::note_bridge::{
    BridgedNullifierSet, PortableNoteProof, create_portable_note, verify_portable_note,
};
use pyana_cell::nullifier_set::NullifierSet;
use pyana_types::AttestedRoot;

/// Asset type constant for GOLD.
const ASSET_GOLD: u64 = 0xABCD_0000_0000_0001;

/// Helper: derive a spending key from a name (deterministic for demo).
fn spending_key(name: &str) -> [u8; 32] {
    blake3::derive_key("pyana-note-bridge-demo-spending-key-v1", name.as_bytes())
}

/// Helper: derive an owner public key from a name (deterministic for demo).
fn owner_key(name: &str) -> [u8; 32] {
    blake3::derive_key("pyana-note-bridge-demo-owner-key-v1", name.as_bytes())
}

/// Create a mock attested root for a federation.
fn mock_attested_root(fed_name: &str, height: u64) -> AttestedRoot {
    let mut merkle_root = [0u8; 32];
    let fed_hash = blake3::hash(fed_name.as_bytes());
    merkle_root.copy_from_slice(fed_hash.as_bytes());

    // Note tree root: deterministic from federation name + height.
    let mut note_tree_hasher = blake3::Hasher::new_derive_key("mock-note-tree-root");
    note_tree_hasher.update(fed_name.as_bytes());
    note_tree_hasher.update(&height.to_le_bytes());
    let note_tree_root = *note_tree_hasher.finalize().as_bytes();

    AttestedRoot {
        merkle_root,
        note_tree_root: Some(note_tree_root),
        nullifier_set_root: None,
        height,
        timestamp: 1700000000 + height as i64,
        quorum_signatures: vec![],
        threshold_qc: None,
        threshold: 0,
    }
}

/// A mock STARK proof verifier that accepts all proofs with "valid" prefix.
fn mock_stark_verify(
    _nullifier: &[u8; 32],
    _merkle_root: &[u8; 32],
    _dest_federation: &[u8; 32],
    _value: u64,
    _asset_type: u64,
    proof_bytes: &[u8],
) -> Result<(), String> {
    // In a real system, this would call verify_note_spend from pyana-circuit.
    // For the demo, we check if the proof starts with "valid-stark-proof".
    if proof_bytes.starts_with(b"valid-stark-proof") {
        Ok(())
    } else {
        Err("mock STARK verification failed: invalid proof prefix".to_string())
    }
}

fn main() {
    println!("=== Pyana Note Bridge Demo (Cross-Federation Value Transfer) ===\n");
    println!("The proof IS the bridge. No light client needed.\n");

    // =========================================================================
    // SETUP: Two federations with independent state
    // =========================================================================
    println!("--- Setup: Two Independent Federations ---\n");

    let fed_a_root = mock_attested_root("federation-alpha", 100);
    let fed_b_root = mock_attested_root("federation-beta", 50);

    println!(
        "  Federation A (alpha): height={}, root={:02x}{:02x}{:02x}{:02x}...",
        fed_a_root.height,
        fed_a_root.merkle_root[0],
        fed_a_root.merkle_root[1],
        fed_a_root.merkle_root[2],
        fed_a_root.merkle_root[3],
    );
    println!(
        "  Federation B (beta):  height={}, root={:02x}{:02x}{:02x}{:02x}...",
        fed_b_root.height,
        fed_b_root.merkle_root[0],
        fed_b_root.merkle_root[1],
        fed_b_root.merkle_root[2],
        fed_b_root.merkle_root[3],
    );
    println!();

    // Federation B trusts Federation A's roots.
    let fed_b_trusted_roots: Vec<AttestedRoot> = vec![fed_a_root.clone()];
    println!("  Federation B trusts Federation A's attested roots.");
    println!();

    // Federation B's identity (derived deterministically for the demo).
    let fed_b_identity: [u8; 32] = *blake3::hash(b"federation-beta-identity-v1").as_bytes();

    // Each federation has its own nullifier set and bridged-nullifier set.
    let mut fed_a_nullifiers = NullifierSet::new();
    let mut fed_b_bridged = BridgedNullifierSet::new();

    // =========================================================================
    // STEP 1: Alice owns a note in Federation A (100 GOLD)
    // =========================================================================
    println!("--- Step 1: Alice Owns a Note in Federation A ---\n");

    let alice_owner = owner_key("alice");
    let alice_sk = spending_key("alice");

    let alice_note =
        Note::with_randomness(alice_owner, [ASSET_GOLD, 100, 0, 0, 0, 0, 0, 0], [0xA1; 32]);
    let alice_commitment = alice_note.commitment();

    println!(
        "  Alice's note commitment: {:02x}{:02x}{:02x}{:02x}...",
        alice_commitment.0[0], alice_commitment.0[1], alice_commitment.0[2], alice_commitment.0[3]
    );
    println!("  Value: 100 GOLD");
    println!("  Federation: A (alpha)");
    println!();

    // =========================================================================
    // STEP 2: Alice spends the note in Federation A
    // =========================================================================
    println!("--- Step 2: Alice Spends the Note in Federation A ---\n");

    let alice_nullifier = alice_note.nullifier(&alice_sk);
    fed_a_nullifiers
        .insert(alice_nullifier)
        .expect("first spend should succeed");

    println!(
        "  Nullifier revealed in Fed A: {:02x}{:02x}{:02x}{:02x}...",
        alice_nullifier.0[0], alice_nullifier.0[1], alice_nullifier.0[2], alice_nullifier.0[3]
    );
    println!("  Note is now spent in Federation A.");
    println!();

    // =========================================================================
    // STEP 3: Alice creates a PortableNoteProof for cross-federation transfer
    // =========================================================================
    println!("--- Step 3: Alice Creates a Portable Note Proof ---\n");

    // Bob's destination note in Federation B.
    let bob_owner = owner_key("bob");
    let bob_note =
        Note::with_randomness(bob_owner, [ASSET_GOLD, 100, 0, 0, 0, 0, 0, 0], [0xB2; 32]);
    let bob_commitment = bob_note.commitment();

    // In a real system, this would be a serialized StarkProof from prove_note_spend().
    // For the demo, we use a mock proof that our mock verifier accepts.
    let mock_proof_bytes = b"valid-stark-proof-for-alice-note-spend".to_vec();

    let portable_proof: PortableNoteProof = create_portable_note(
        alice_nullifier,
        mock_proof_bytes,
        fed_a_root.clone(),
        fed_b_identity,
        bob_commitment,
        100,
        ASSET_GOLD,
    );

    println!("  PortableNoteProof created:");
    println!(
        "    Nullifier: {:02x}{:02x}{:02x}{:02x}...",
        portable_proof.nullifier[0],
        portable_proof.nullifier[1],
        portable_proof.nullifier[2],
        portable_proof.nullifier[3]
    );
    println!(
        "    Source root height: {} (Federation A)",
        portable_proof.source_root.height
    );
    println!(
        "    Destination commitment: {:02x}{:02x}{:02x}{:02x}... (Bob's new note)",
        portable_proof.destination_commitment.0[0],
        portable_proof.destination_commitment.0[1],
        portable_proof.destination_commitment.0[2],
        portable_proof.destination_commitment.0[3]
    );
    println!("    Value: {} GOLD", portable_proof.value);
    println!(
        "    Spending proof: {} bytes",
        portable_proof.spending_proof.len()
    );
    println!();
    println!("  This proof is self-contained. It can be presented to ANY federation");
    println!("  that trusts Federation A's attested roots.");
    println!();

    // =========================================================================
    // STEP 4: Bob presents the proof to Federation B
    // =========================================================================
    println!("--- Step 4: Federation B Verifies the Portable Proof ---\n");

    // Federation B verifies the portable proof.
    let verify_result = verify_portable_note(
        &portable_proof,
        &fed_b_identity,
        &fed_b_trusted_roots,
        mock_stark_verify,
    );

    match &verify_result {
        Ok(()) => println!("  Verification: [PASS]"),
        Err(e) => println!("  Verification: [FAIL] {e}"),
    }
    assert!(verify_result.is_ok());

    println!("  Checks performed:");
    println!("    1. Source root is in trusted set: [PASS]");
    println!("    2. Source root has note_tree_root: [PASS]");
    println!("    3. STARK spending proof verifies: [PASS]");
    println!();

    // =========================================================================
    // STEP 5: Federation B mints the note (records bridged nullifier)
    // =========================================================================
    println!("--- Step 5: Federation B Mints the Note for Bob ---\n");

    // Record the nullifier in the bridged set (prevent double-bridge).
    fed_b_bridged
        .insert(portable_proof.nullifier)
        .expect("first bridge should succeed");

    println!(
        "  Bridged nullifier recorded: {:02x}{:02x}{:02x}{:02x}...",
        portable_proof.nullifier[0],
        portable_proof.nullifier[1],
        portable_proof.nullifier[2],
        portable_proof.nullifier[3]
    );
    println!(
        "  New note minted in Fed B: commitment {:02x}{:02x}{:02x}{:02x}...",
        bob_commitment.0[0], bob_commitment.0[1], bob_commitment.0[2], bob_commitment.0[3]
    );
    println!("  Value: 100 GOLD now belongs to Bob in Federation B.");
    println!();

    // =========================================================================
    // STEP 6: Double-bridge attempt fails
    // =========================================================================
    println!("--- Step 6: Double-Bridge Attempt FAILS ---\n");

    // Try to bridge the same proof again.
    let double_bridge = fed_b_bridged.insert(portable_proof.nullifier);
    match &double_bridge {
        Ok(()) => println!("  Double-bridge: [UNEXPECTED PASS]"),
        Err(e) => println!("  Double-bridge attempt: [REJECTED] {e}"),
    }
    assert!(double_bridge.is_err());
    println!();
    println!("  The bridged-nullifier set prevents the same note from being");
    println!("  minted twice in Federation B, regardless of how many times");
    println!("  the portable proof is presented.");
    println!();

    // =========================================================================
    // STEP 7: Proof against untrusted root fails
    // =========================================================================
    println!("--- Step 7: Untrusted Root FAILS ---\n");

    // Create a proof from a federation that B doesn't trust.
    let evil_root = mock_attested_root("federation-evil", 666);
    let evil_proof = PortableNoteProof {
        nullifier: [0xEE; 32],
        destination_federation: fed_b_identity,
        source_root: evil_root,
        spending_proof: b"valid-stark-proof-evil".to_vec(),
        destination_commitment: bob_commitment,
        value: 100,
        asset_type: ASSET_GOLD,
    };

    let untrusted_result = verify_portable_note(
        &evil_proof,
        &fed_b_identity,
        &fed_b_trusted_roots,
        mock_stark_verify,
    );
    match &untrusted_result {
        Ok(()) => println!("  Untrusted root: [UNEXPECTED PASS]"),
        Err(e) => println!("  Untrusted root: [REJECTED] {e}"),
    }
    assert!(untrusted_result.is_err());
    println!();
    println!("  Federation B only accepts proofs from federations in its");
    println!("  trusted root set. An attacker cannot forge a bridge from");
    println!("  an unrecognized federation.");
    println!();

    // =========================================================================
    // STEP 8: Invalid STARK proof fails
    // =========================================================================
    println!("--- Step 8: Invalid STARK Proof FAILS ---\n");

    // Create a proof with invalid STARK bytes.
    let bad_proof = PortableNoteProof {
        nullifier: [0xFF; 32],
        destination_federation: fed_b_identity,
        source_root: fed_a_root.clone(),
        spending_proof: b"garbage-not-a-real-proof".to_vec(),
        destination_commitment: bob_commitment,
        value: 100,
        asset_type: ASSET_GOLD,
    };

    let bad_stark_result = verify_portable_note(
        &bad_proof,
        &fed_b_identity,
        &fed_b_trusted_roots,
        mock_stark_verify,
    );
    match &bad_stark_result {
        Ok(()) => println!("  Invalid STARK proof: [UNEXPECTED PASS]"),
        Err(e) => println!("  Invalid STARK proof: [REJECTED] {e}"),
    }
    assert!(bad_stark_result.is_err());
    println!();
    println!("  Even if the source root is trusted, the STARK proof must");
    println!("  actually verify. An attacker cannot mint notes by presenting");
    println!("  a valid root with an invalid spending proof.");
    println!();

    // =========================================================================
    // SUMMARY
    // =========================================================================
    println!("=== Summary ===\n");
    println!("  The note bridge demonstrates that cross-federation value transfer");
    println!("  needs only a STARK proof and a trusted root set. No light client,");
    println!("  no relay chain, no watchtower, no exit ceremony.\n");
    println!("  Security properties:");
    println!("    - Double-bridge prevention: bridged-nullifier set");
    println!("    - Source authentication: trusted root set");
    println!("    - Spend validity: STARK proof verification");
    println!("    - Privacy: observers cannot link source/dest notes");
    println!();
    println!(
        "  Federation A nullifier set: {} entries",
        fed_a_nullifiers.len()
    );
    println!(
        "  Federation B bridged set:   {} entries",
        fed_b_bridged.len()
    );
    println!();
    println!("  Done.");
}
