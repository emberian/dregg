//! Sealer/Unsealer Partition-Tolerant Capability Transfer Demo
//!
//! Demonstrates E-style rights amplification for offline capability transfer:
//!
//! 1. Alice creates a sealer/unsealer pair.
//! 2. Alice keeps the sealer, gives the unsealer to Bob (via GrantCapability).
//! 3. Alice seals a capability into an opaque SealedBox.
//! 4. The sealed box is "stored" (serialized to bytes) -- could be sent via email,
//!    gossip protocol, relay, or even a QR code.
//! 5. Bob retrieves the sealed box later (he was NEVER online at the same time as Alice).
//! 6. Bob unseals it, recovering the original capability.
//! 7. Eve (who intercepts the sealed box but has no unsealer) CANNOT access the capability.
//!
//! Key property: Alice and Bob are never online simultaneously. The sealed box
//! is just opaque bytes that can traverse any untrusted channel.

use pyana_cell::capability::CapabilityRef;
use pyana_cell::id::CellId;
use pyana_cell::permissions::AuthRequired;
use pyana_cell::seal::{SealError, SealPair, SealedBox, test_seal_pair};

fn main() {
    println!("=== Pyana Sealer/Unsealer Partition-Tolerant Transfer Demo ===\n");

    // =========================================================================
    // SETUP: Create identities for Alice, Bob, Carol, and Eve
    // =========================================================================
    println!("--- Setup: Create identities ---\n");

    let alice_id = CellId::from_bytes([0xAA; 32]);
    let bob_id = CellId::from_bytes([0xBB; 32]);
    let carol_id = CellId::from_bytes([0xCC; 32]);
    let eve_id = CellId::from_bytes([0xEE; 32]);

    println!("  Alice: {:?}", &alice_id.as_bytes()[..4]);
    println!("  Bob:   {:?}", &bob_id.as_bytes()[..4]);
    println!("  Carol: {:?}", &carol_id.as_bytes()[..4]);
    println!("  Eve:   {:?}", &eve_id.as_bytes()[..4]);
    println!();

    // The capability Alice wants to transfer to Bob: access to Carol's cell.
    let carol_cap = CapabilityRef {
        target: carol_id,
        slot: 7,
        permissions: AuthRequired::Signature,
        breadstuff: None,
    };
    println!("  Capability to transfer: access to Carol (slot 7, requires Signature)");
    println!();

    // =========================================================================
    // STEP 1: Alice creates a sealer/unsealer pair
    // =========================================================================
    println!("--- Step 1: Alice creates a sealer/unsealer pair ---\n");

    let pair = SealPair::generate();
    println!("  Pair ID: {:02x}{:02x}{:02x}{:02x}...", pair.id[0], pair.id[1], pair.id[2], pair.id[3]);
    println!("  Sealer public key (Alice keeps): {:02x}{:02x}...", pair.sealer_public[0], pair.sealer_public[1]);
    println!("  Unsealer secret key (given to Bob): {:02x}{:02x}...", pair.unsealer_secret[0], pair.unsealer_secret[1]);
    println!();
    println!("  In practice: Alice submits a CreateSealPair effect naming herself as");
    println!("  sealer_holder and Bob as unsealer_holder. The executor grants the");
    println!("  respective capabilities to each cell's c-list.");
    println!();

    // =========================================================================
    // STEP 2: Alice seals the capability
    // =========================================================================
    println!("--- Step 2: Alice seals the capability into an opaque box ---\n");

    let sealed_box = pair.seal(&carol_cap);
    println!("  Sealed box created:");
    println!("    pair_id:    {:02x}{:02x}{:02x}{:02x}...", sealed_box.pair_id[0], sealed_box.pair_id[1], sealed_box.pair_id[2], sealed_box.pair_id[3]);
    println!("    commitment: {:02x}{:02x}{:02x}{:02x}...", sealed_box.commitment[0], sealed_box.commitment[1], sealed_box.commitment[2], sealed_box.commitment[3]);
    println!("    ciphertext: {} bytes", sealed_box.ciphertext.len());
    println!("    nonce:      {:02x}{:02x}{:02x}{:02x}...", sealed_box.nonce[0], sealed_box.nonce[1], sealed_box.nonce[2], sealed_box.nonce[3]);
    println!();

    // =========================================================================
    // STEP 3: Serialize the sealed box (it's just bytes -- can go anywhere)
    // =========================================================================
    println!("--- Step 3: Serialize sealed box for transport ---\n");

    let serialized = postcard::to_stdvec(&sealed_box).expect("serialize sealed box");
    println!("  Serialized size: {} bytes", serialized.len());
    println!("  (Could be sent via email, gossip, relay, QR code, carrier pigeon...)");
    println!();

    // Simulate Alice going offline. The sealed box is now "in transit."
    println!("  >>> Alice goes OFFLINE <<<");
    println!();

    // =========================================================================
    // STEP 4: Time passes. Bob comes online, retrieves the sealed box.
    // =========================================================================
    println!("--- Step 4: Bob retrieves the sealed box (Alice is offline) ---\n");

    // Bob deserializes the sealed box from whatever channel it arrived on.
    let recovered_box: SealedBox = postcard::from_bytes(&serialized).expect("deserialize sealed box");
    println!("  Bob received sealed box ({} bytes)", serialized.len());
    println!("  pair_id matches: {}", recovered_box.pair_id == sealed_box.pair_id);
    println!();

    // =========================================================================
    // STEP 5: Bob unseals the box, recovering the original capability
    // =========================================================================
    println!("--- Step 5: Bob unseals the box ---\n");

    let recovered_cap = pair.unseal(&recovered_box).expect("unseal should succeed");
    println!("  Unsealed successfully!");
    println!("  Recovered capability:");
    println!("    target: {:02x}{:02x}{:02x}{:02x}... (Carol)", recovered_cap.target.as_bytes()[0], recovered_cap.target.as_bytes()[1], recovered_cap.target.as_bytes()[2], recovered_cap.target.as_bytes()[3]);
    println!("    slot:   {}", recovered_cap.slot);
    println!("    perms:  {:?}", recovered_cap.permissions);
    println!();
    assert_eq!(recovered_cap, carol_cap, "Recovered capability must match original");
    println!("  VERIFIED: recovered capability == original capability");
    println!();
    println!("  In practice: Bob submits an Unseal effect with the SealedBox.");
    println!("  The executor decrypts it using the unsealer_secret stored in Bob's unsealer");
    println!("  capability breadstuff, then grants the recovered cap to Bob's c-list.");
    println!();

    // =========================================================================
    // STEP 6: Eve intercepts the sealed box but CANNOT unseal it
    // =========================================================================
    println!("--- Step 6: Eve tries to unseal (and fails) ---\n");

    // Eve has a different pair (she doesn't have the unsealer key).
    let eve_pair = test_seal_pair(99);
    let eve_result = eve_pair.unseal(&recovered_box);
    match &eve_result {
        Err(SealError::PairMismatch { expected, got }) => {
            println!("  Eve's unseal attempt: REJECTED (PairMismatch)");
            println!("    Eve's pair:   {:02x}{:02x}...", expected[0], expected[1]);
            println!("    Box's pair:   {:02x}{:02x}...", got[0], got[1]);
        }
        Err(e) => {
            println!("  Eve's unseal attempt: REJECTED ({e})");
        }
        Ok(_) => {
            panic!("Eve should NOT be able to unseal!");
        }
    }
    println!();

    // What if Eve tries tampering with the ciphertext?
    println!("  Eve tries tampering with the ciphertext...");
    let mut tampered_box = recovered_box.clone();
    tampered_box.ciphertext[0] ^= 0xFF;
    // Even with the correct pair, tampering is detected.
    let tamper_result = pair.unseal(&tampered_box);
    match &tamper_result {
        Err(SealError::DecryptionFailed) => {
            println!("  Tampered box: REJECTED (DecryptionFailed -- AEAD detects modification)");
        }
        Err(e) => {
            println!("  Tampered box: REJECTED ({e})");
        }
        Ok(_) => {
            panic!("Tampered box should NOT unseal!");
        }
    }
    println!();

    // =========================================================================
    // STEP 7: Verify seal without unsealing (provenance check)
    // =========================================================================
    println!("--- Step 7: Verify seal provenance (without unsealing) ---\n");

    let is_valid = pair.verify_seal(&recovered_box);
    println!("  verify_seal (correct pair): {}", is_valid);
    assert!(is_valid);

    let eve_valid = eve_pair.verify_seal(&recovered_box);
    println!("  verify_seal (Eve's pair):   {}", eve_valid);
    assert!(!eve_valid);
    println!();

    // =========================================================================
    // STEP 8: Demonstrate multiple sealed boxes from the same pair
    // =========================================================================
    println!("--- Step 8: Multiple seals from the same pair ---\n");

    let cap2 = CapabilityRef {
        target: alice_id,
        slot: 42,
        permissions: AuthRequired::Either,
        breadstuff: Some([0xDE; 32]),
    };

    let sealed2 = pair.seal(&cap2);
    let recovered2 = pair.unseal(&sealed2).expect("second unseal");
    assert_eq!(recovered2, cap2);
    println!("  Sealed and unsealed a second capability (Alice, slot 42, Either)");
    println!("  Different capabilities, same pair -- both work independently.");
    println!();

    // =========================================================================
    // SUMMARY
    // =========================================================================
    println!("=== Summary ===\n");
    println!("  - Alice and Bob were NEVER online at the same time.");
    println!("  - The sealed box traversed an untrusted channel (serialized bytes).");
    println!("  - Eve could not extract the capability despite intercepting the box.");
    println!("  - Tampering with the box is detected by authenticated encryption.");
    println!("  - The capability is recovered exactly as Alice sealed it.");
    println!("  - This enables partition-tolerant capability transfer in distributed systems.");
    println!();
    println!("Done.");
}
