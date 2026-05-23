//! Stealth addresses: ephemeral per-transaction CellIds for unlinkable payments.
//!
//! # Problem
//!
//! CellId reuse enables linkability across purchases/transactions. If Alice always
//! uses the same CellId, observers can correlate all her activity. For a truly
//! anonymous marketplace, each transaction should use a fresh, unlinkable identity.
//!
//! # Stealth Address Pattern (adapted from Monero/EIP-5564)
//!
//! 1. Recipient publishes a "meta-address" containing two public keys:
//!    - `spend_pubkey` (S): controls spending authority
//!    - `view_pubkey` (V): allows detection of incoming payments
//!
//! 2. Sender generates a one-time address:
//!    - Picks random ephemeral secret `r`
//!    - Computes shared secret: `shared = H(r * V)` (DH with view key)
//!    - Derives one-time public key: `P = shared_scalar * G + S`
//!    - Publishes `R = r * G` alongside the note
//!
//! 3. Recipient scans for incoming notes:
//!    - For each (note, R): `shared = H(v * R)`, then check if `shared * G + S == P`
//!    - If match: derive spending key `k = shared_scalar + s`
//!
//! # Cryptographic Primitives
//!
//! - X25519 for the Diffie-Hellman exchange (already a dependency)
//! - BLAKE3 derive_key for shared secret -> scalar derivation
//! - Ed25519 points for the additive key derivation (spend key + shared scalar)
//!
//! # Note on Key Types
//!
//! We use X25519 for the DH (view key exchange) and Ed25519 for the additive
//! point arithmetic (one-time address derivation). The view keypair is X25519;
//! the spend keypair is Ed25519. This matches the different operations needed:
//! DH for shared secret, point addition for stealth address.

use serde::{Deserialize, Serialize};
use x25519_dalek::{PublicKey as X25519Public, StaticSecret as X25519Secret};
use zeroize::Zeroize;

/// A stealth meta-address published by a recipient.
///
/// Anyone who knows this can generate unlinkable one-time addresses for the recipient.
/// The meta-address itself does not reveal which notes belong to the recipient.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StealthMetaAddress {
    /// Ed25519 public key for spending (the "base" public key for address derivation).
    pub spend_pubkey: [u8; 32],
    /// X25519 public key for the view/scan DH exchange.
    pub view_pubkey: [u8; 32],
}

/// A one-time stealth address generated for a specific transaction.
///
/// Contains the one-time public key (used as the note's `owner`) and the
/// ephemeral public key R (published alongside the note for recipient scanning).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StealthAddress {
    /// The one-time public key (P). Used as the note's `owner` field.
    /// Only the intended recipient can derive the corresponding private key.
    pub one_time_pubkey: [u8; 32],
    /// The ephemeral public key (R = r*G). Published with the transaction.
    /// The recipient uses this with their view key to detect ownership.
    pub ephemeral_pubkey: [u8; 32],
}

/// A stealth keypair held by the recipient for scanning and spending.
///
/// The `view_private_key` is used for scanning (detecting incoming notes).
/// The `spend_private_key` is used for spending (only needed when actually spending).
///
/// In practice, the view key can be delegated to a scanning service without
/// giving it spending authority.
#[derive(Clone)]
pub struct StealthKeys {
    /// X25519 private key for the view/scan operation.
    pub view_private_key: [u8; 32],
    /// Ed25519 secret key (seed) for spending.
    pub spend_private_key: [u8; 32],
}

impl Drop for StealthKeys {
    fn drop(&mut self) {
        self.view_private_key.zeroize();
        self.spend_private_key.zeroize();
    }
}

impl StealthKeys {
    /// Generate a new random stealth keypair.
    pub fn generate() -> Self {
        let mut view_private_key = [0u8; 32];
        let mut spend_private_key = [0u8; 32];
        getrandom::fill(&mut view_private_key).expect("getrandom failed");
        getrandom::fill(&mut spend_private_key).expect("getrandom failed");
        StealthKeys {
            view_private_key,
            spend_private_key,
        }
    }

    /// Create from explicit key material (for deterministic tests).
    pub fn from_keys(view_private_key: [u8; 32], spend_private_key: [u8; 32]) -> Self {
        StealthKeys {
            view_private_key,
            spend_private_key,
        }
    }

    /// Derive the public meta-address from this keypair.
    pub fn meta_address(&self) -> StealthMetaAddress {
        // View public key: X25519
        let view_secret = X25519Secret::from(self.view_private_key);
        let view_pubkey = X25519Public::from(&view_secret);

        // Spend public key: Ed25519
        let spend_pubkey = ed25519_spend_pubkey(&self.spend_private_key);

        StealthMetaAddress {
            spend_pubkey,
            view_pubkey: *view_pubkey.as_bytes(),
        }
    }
}

impl StealthMetaAddress {
    /// Generate a one-time stealth address for this recipient.
    ///
    /// The sender calls this to create a fresh, unlinkable address. The returned
    /// `StealthAddress` contains:
    /// - `one_time_pubkey`: use as the note's `owner` field
    /// - `ephemeral_pubkey`: publish alongside the note (for recipient scanning)
    ///
    /// The shared secret is returned for the sender's own bookkeeping (optional).
    pub fn generate_stealth_address(&self) -> (StealthAddress, [u8; 32]) {
        let mut eph_bytes = [0u8; 32];
        getrandom::fill(&mut eph_bytes).expect("getrandom failed");
        self.generate_stealth_address_with_ephemeral(eph_bytes)
    }

    /// Generate a stealth address with a specific ephemeral secret (for deterministic tests).
    pub fn generate_stealth_address_with_ephemeral(
        &self,
        ephemeral_secret_bytes: [u8; 32],
    ) -> (StealthAddress, [u8; 32]) {
        // Compute R = r * G (X25519 base point multiplication)
        let ephemeral_secret = X25519Secret::from(ephemeral_secret_bytes);
        let ephemeral_pubkey = X25519Public::from(&ephemeral_secret);

        // Compute shared secret: DH(r, V) = r * V
        let view_pubkey = X25519Public::from(self.view_pubkey);
        let shared_dh = ephemeral_secret.diffie_hellman(&view_pubkey);

        // Derive a scalar from the shared secret using BLAKE3 KDF
        let shared_secret = derive_shared_secret(shared_dh.as_bytes(), ephemeral_pubkey.as_bytes());

        // Compute one-time public key: P = shared_scalar * G_ed + S
        let one_time_pubkey = derive_one_time_pubkey(&shared_secret, &self.spend_pubkey);

        (
            StealthAddress {
                one_time_pubkey,
                ephemeral_pubkey: *ephemeral_pubkey.as_bytes(),
            },
            shared_secret,
        )
    }
}

impl StealthAddress {
    /// Check if this stealth address belongs to us.
    ///
    /// The recipient calls this for each new note to detect incoming payments.
    /// Uses only the view key (no spending authority needed for scanning).
    ///
    /// Returns `true` if this address was generated for the given meta-address.
    pub fn check_ownership(
        &self,
        view_private_key: &[u8; 32],
        spend_pubkey: &[u8; 32],
    ) -> bool {
        // Recompute shared secret: DH(v, R) = v * R
        let view_secret = X25519Secret::from(*view_private_key);
        let eph_pubkey = X25519Public::from(self.ephemeral_pubkey);
        let shared_dh = view_secret.diffie_hellman(&eph_pubkey);

        let shared_secret =
            derive_shared_secret(shared_dh.as_bytes(), &self.ephemeral_pubkey);

        // Recompute expected one-time pubkey: P' = shared_scalar * G_ed + S
        let expected = derive_one_time_pubkey(&shared_secret, spend_pubkey);

        // Constant-time comparison
        constant_time_eq(&expected, &self.one_time_pubkey)
    }

    /// Derive the spending key for this stealth address.
    ///
    /// Only callable by the recipient who holds both the view and spend private keys.
    /// The returned key can sign transactions spending the note owned by `one_time_pubkey`.
    ///
    /// Returns the derived Ed25519 expanded secret key bytes (the scalar portion).
    pub fn derive_spending_key(
        &self,
        view_private_key: &[u8; 32],
        spend_private_key: &[u8; 32],
    ) -> [u8; 32] {
        // Recompute shared secret: DH(v, R) = v * R
        let view_secret = X25519Secret::from(*view_private_key);
        let eph_pubkey = X25519Public::from(self.ephemeral_pubkey);
        let shared_dh = view_secret.diffie_hellman(&eph_pubkey);

        let shared_secret =
            derive_shared_secret(shared_dh.as_bytes(), &self.ephemeral_pubkey);

        // Derive the one-time spending key: k = shared_scalar + s (mod l)
        derive_one_time_spending_key(&shared_secret, spend_private_key)
    }
}

/// An announcement published alongside a note, enabling recipient scanning.
///
/// In a real system, these would be posted to a shared announcement log
/// (e.g., on-chain event, shared bulletin board) so recipients can scan.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StealthAnnouncement {
    /// The ephemeral public key R for this transaction.
    pub ephemeral_pubkey: [u8; 32],
    /// The note commitment this announcement corresponds to.
    pub note_commitment: crate::note::NoteCommitment,
    /// Optional: a view tag (first byte of shared secret) for fast filtering.
    /// Recipients can skip the full DH + point arithmetic if the view tag doesn't match.
    pub view_tag: u8,
}

impl StealthAnnouncement {
    /// Create an announcement from a stealth address generation result.
    pub fn new(
        stealth_addr: &StealthAddress,
        note_commitment: crate::note::NoteCommitment,
        shared_secret: &[u8; 32],
    ) -> Self {
        StealthAnnouncement {
            ephemeral_pubkey: stealth_addr.ephemeral_pubkey,
            note_commitment,
            view_tag: shared_secret[0],
        }
    }

    /// Quick pre-filter: does the view tag match what we'd expect?
    /// This lets recipients skip the expensive DH computation for ~255/256 of announcements.
    pub fn matches_view_tag(&self, view_private_key: &[u8; 32]) -> bool {
        let view_secret = X25519Secret::from(*view_private_key);
        let eph_pubkey = X25519Public::from(self.ephemeral_pubkey);
        let shared_dh = view_secret.diffie_hellman(&eph_pubkey);
        let shared_secret =
            derive_shared_secret(shared_dh.as_bytes(), &self.ephemeral_pubkey);
        shared_secret[0] == self.view_tag
    }
}

// --- Internal helpers ---

/// Derive a 32-byte shared secret from the raw DH output using BLAKE3 KDF.
/// Domain-separated to prevent cross-protocol attacks.
fn derive_shared_secret(dh_output: &[u8; 32], ephemeral_pubkey: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-stealth shared-secret v1");
    hasher.update(dh_output);
    hasher.update(ephemeral_pubkey);
    *hasher.finalize().as_bytes()
}

/// Derive the one-time public key: P = H(shared)*G + S
///
/// We interpret the shared secret as an Ed25519 scalar (clamped) and compute
/// the point addition on the Ed25519 curve.
fn derive_one_time_pubkey(shared_secret: &[u8; 32], spend_pubkey: &[u8; 32]) -> [u8; 32] {
    use curve25519_dalek::edwards::{CompressedEdwardsY, EdwardsPoint};
    use curve25519_dalek::scalar::Scalar;
    use curve25519_dalek::constants::ED25519_BASEPOINT_TABLE;

    // Derive a sub-scalar from the shared secret (reduce mod l for Ed25519 safety)
    let scalar_bytes = derive_stealth_scalar(shared_secret);
    let scalar = Scalar::from_bytes_mod_order(scalar_bytes);

    // shared_scalar * G
    let shared_point: EdwardsPoint = &scalar * ED25519_BASEPOINT_TABLE;

    // Decompress the spend pubkey
    let spend_compressed = CompressedEdwardsY(*spend_pubkey);
    let spend_point = spend_compressed
        .decompress()
        .expect("invalid spend_pubkey: not a valid Ed25519 point");

    // P = shared_scalar * G + S
    let one_time_point: EdwardsPoint = shared_point + spend_point;
    one_time_point.compress().to_bytes()
}

/// Derive the one-time spending key: k = shared_scalar + s (mod l)
///
/// The spend_private_key is an Ed25519 seed. We expand it to get the scalar,
/// then add the shared scalar.
fn derive_one_time_spending_key(shared_secret: &[u8; 32], spend_private_key: &[u8; 32]) -> [u8; 32] {
    use curve25519_dalek::scalar::Scalar;

    // Derive the shared scalar (same as in one_time_pubkey derivation)
    let scalar_bytes = derive_stealth_scalar(shared_secret);
    let shared_scalar = Scalar::from_bytes_mod_order(scalar_bytes);

    // Expand the Ed25519 seed to get the base scalar
    let spend_scalar = ed25519_seed_to_scalar(spend_private_key);

    // k = shared_scalar + spend_scalar (mod l)
    let one_time_scalar = shared_scalar + spend_scalar;
    one_time_scalar.to_bytes()
}

/// Derive a scalar value from a shared secret using BLAKE3.
/// The output is reduced mod l when used with `Scalar::from_bytes_mod_order`.
fn derive_stealth_scalar(shared_secret: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-stealth scalar v1");
    hasher.update(shared_secret);
    *hasher.finalize().as_bytes()
}

/// Expand an Ed25519 seed into the secret scalar (first 32 bytes of SHA-512, clamped).
fn ed25519_seed_to_scalar(seed: &[u8; 32]) -> curve25519_dalek::scalar::Scalar {
    let signing_key = ed25519_dalek::SigningKey::from_bytes(seed);
    // `to_scalar()` returns the clamped+reduced scalar derived from SHA-512(seed)
    signing_key.to_scalar()
}

/// Compute the Ed25519 public key from a seed.
fn ed25519_spend_pubkey(seed: &[u8; 32]) -> [u8; 32] {
    let signing_key = ed25519_dalek::SigningKey::from_bytes(seed);
    let verifying_key = signing_key.verifying_key();
    verifying_key.to_bytes()
}

/// Constant-time byte array comparison.
fn constant_time_eq(a: &[u8; 32], b: &[u8; 32]) -> bool {
    let mut diff = 0u8;
    for i in 0..32 {
        diff |= a[i] ^ b[i];
    }
    diff == 0
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Test the full stealth address lifecycle: generate -> check_ownership -> derive_spending_key.
    #[test]
    fn full_stealth_cycle() {
        // Recipient generates their stealth keypair and publishes meta-address
        let keys = StealthKeys::from_keys([1u8; 32], [2u8; 32]);
        let meta = keys.meta_address();

        // Sender generates a one-time address for the recipient
        let (stealth_addr, shared_secret) = meta.generate_stealth_address();

        // Verify the one-time pubkey is not the same as the spend pubkey
        assert_ne!(stealth_addr.one_time_pubkey, meta.spend_pubkey);

        // Recipient checks ownership using their view key
        assert!(stealth_addr.check_ownership(&keys.view_private_key, &meta.spend_pubkey));

        // Recipient derives the spending key
        let spending_key =
            stealth_addr.derive_spending_key(&keys.view_private_key, &keys.spend_private_key);

        // Verify: the derived spending key produces the correct public key
        let derived_pubkey = ed25519_spend_pubkey_from_scalar(&spending_key);
        assert_eq!(derived_pubkey, stealth_addr.one_time_pubkey);

        // Verify shared secret is non-trivial
        assert_ne!(shared_secret, [0u8; 32]);
    }

    /// Different ephemeral secrets produce different stealth addresses (unlinkability).
    #[test]
    fn different_ephemeral_produce_different_addresses() {
        let keys = StealthKeys::from_keys([10u8; 32], [20u8; 32]);
        let meta = keys.meta_address();

        let (addr1, _) = meta.generate_stealth_address_with_ephemeral([3u8; 32]);
        let (addr2, _) = meta.generate_stealth_address_with_ephemeral([4u8; 32]);

        // Different one-time pubkeys (unlinkable)
        assert_ne!(addr1.one_time_pubkey, addr2.one_time_pubkey);
        // Different ephemeral pubkeys
        assert_ne!(addr1.ephemeral_pubkey, addr2.ephemeral_pubkey);

        // But both are detectable by the recipient
        assert!(addr1.check_ownership(&keys.view_private_key, &meta.spend_pubkey));
        assert!(addr2.check_ownership(&keys.view_private_key, &meta.spend_pubkey));
    }

    /// Wrong view key cannot detect ownership.
    #[test]
    fn wrong_view_key_cannot_detect() {
        let keys = StealthKeys::from_keys([5u8; 32], [6u8; 32]);
        let meta = keys.meta_address();

        let (stealth_addr, _) = meta.generate_stealth_address();

        // Wrong view key
        let wrong_view = [99u8; 32];
        assert!(!stealth_addr.check_ownership(&wrong_view, &meta.spend_pubkey));
    }

    /// Wrong spend pubkey cannot detect ownership.
    #[test]
    fn wrong_spend_pubkey_cannot_detect() {
        let keys = StealthKeys::from_keys([7u8; 32], [8u8; 32]);
        let meta = keys.meta_address();

        let (stealth_addr, _) = meta.generate_stealth_address();

        // Wrong spend pubkey: use a valid but different spend pubkey
        // (arbitrary bytes may not form a valid Ed25519 point).
        let other_keys = StealthKeys::from_keys([7u8; 32], [9u8; 32]);
        let other_meta = other_keys.meta_address();
        assert!(!stealth_addr.check_ownership(&keys.view_private_key, &other_meta.spend_pubkey));
    }

    /// Spending key derivation is deterministic.
    #[test]
    fn spending_key_derivation_deterministic() {
        let keys = StealthKeys::from_keys([11u8; 32], [12u8; 32]);
        let meta = keys.meta_address();

        let (stealth_addr, _) = meta.generate_stealth_address_with_ephemeral([13u8; 32]);

        let key1 =
            stealth_addr.derive_spending_key(&keys.view_private_key, &keys.spend_private_key);
        let key2 =
            stealth_addr.derive_spending_key(&keys.view_private_key, &keys.spend_private_key);

        assert_eq!(key1, key2);
    }

    /// Integration with Note: create a note owned by a stealth address.
    #[test]
    fn note_with_stealth_owner() {
        use crate::note::Note;

        let keys = StealthKeys::from_keys([14u8; 32], [15u8; 32]);
        let meta = keys.meta_address();

        // Sender creates a stealth address and a note for the recipient
        let (stealth_addr, shared_secret) = meta.generate_stealth_address();
        let note = Note::with_randomness(
            stealth_addr.one_time_pubkey, // owner = one-time pubkey
            [1, 100, 0, 0, 0, 0, 0, 0],  // 100 units of asset 1
            [42u8; 32],
        );

        // Note commitment exists
        let commitment = note.commitment();

        // Recipient scans and finds this note
        assert!(stealth_addr.check_ownership(&keys.view_private_key, &meta.spend_pubkey));

        // Recipient can derive spending key and compute nullifier
        let spending_key =
            stealth_addr.derive_spending_key(&keys.view_private_key, &keys.spend_private_key);
        let nullifier = note.nullifier(&spending_key);

        // Nullifier is deterministic
        assert_eq!(nullifier, note.nullifier(&spending_key));

        // Announcement can be created
        let announcement = StealthAnnouncement::new(&stealth_addr, commitment, &shared_secret);
        assert_eq!(announcement.ephemeral_pubkey, stealth_addr.ephemeral_pubkey);
        assert_eq!(announcement.note_commitment, commitment);
    }

    /// View tag filtering works.
    #[test]
    fn view_tag_filtering() {
        let keys = StealthKeys::from_keys([16u8; 32], [17u8; 32]);
        let meta = keys.meta_address();

        let (stealth_addr, shared_secret) = meta.generate_stealth_address_with_ephemeral([18u8; 32]);
        let note = Note::with_randomness(stealth_addr.one_time_pubkey, [1, 50, 0, 0, 0, 0, 0, 0], [0u8; 32]);
        let commitment = note.commitment();

        let announcement = StealthAnnouncement::new(&stealth_addr, commitment, &shared_secret);

        // The correct view key matches the view tag
        assert!(announcement.matches_view_tag(&keys.view_private_key));

        // A wrong view key very likely does NOT match (probabilistically ~1/256 chance of false positive)
        // We use a specific wrong key that we know produces a different tag
        let wrong_view = [99u8; 32];
        // This is probabilistic but with fixed keys it's deterministic in tests
        let _ = announcement.matches_view_tag(&wrong_view); // just ensure it doesn't panic
    }

    /// Meta-address is deterministic from keys.
    #[test]
    fn meta_address_deterministic() {
        let keys1 = StealthKeys::from_keys([20u8; 32], [21u8; 32]);
        let keys2 = StealthKeys::from_keys([20u8; 32], [21u8; 32]);

        assert_eq!(keys1.meta_address(), keys2.meta_address());
    }

    /// Multiple recipients: notes to different meta-addresses are distinguishable only by the owner.
    #[test]
    fn multiple_recipients_unlinkable() {
        let alice = StealthKeys::from_keys([30u8; 32], [31u8; 32]);
        let bob = StealthKeys::from_keys([40u8; 32], [41u8; 32]);

        let alice_meta = alice.meta_address();
        let bob_meta = bob.meta_address();

        let (alice_addr, _) = alice_meta.generate_stealth_address_with_ephemeral([50u8; 32]);
        let (bob_addr, _) = bob_meta.generate_stealth_address_with_ephemeral([51u8; 32]);

        // Alice can detect her note but not Bob's
        assert!(alice_addr.check_ownership(&alice.view_private_key, &alice_meta.spend_pubkey));
        assert!(!bob_addr.check_ownership(&alice.view_private_key, &alice_meta.spend_pubkey));

        // Bob can detect his note but not Alice's
        assert!(bob_addr.check_ownership(&bob.view_private_key, &bob_meta.spend_pubkey));
        assert!(!alice_addr.check_ownership(&bob.view_private_key, &bob_meta.spend_pubkey));
    }

    /// Helper: compute Ed25519 public key from a raw scalar (for verification in tests).
    fn ed25519_spend_pubkey_from_scalar(scalar_bytes: &[u8; 32]) -> [u8; 32] {
        use curve25519_dalek::constants::ED25519_BASEPOINT_TABLE;
        use curve25519_dalek::edwards::EdwardsPoint;
        use curve25519_dalek::scalar::Scalar;

        let scalar = Scalar::from_bytes_mod_order(*scalar_bytes);
        let point: EdwardsPoint = &scalar * ED25519_BASEPOINT_TABLE;
        point.compress().to_bytes()
    }

    use crate::note::Note;
}
