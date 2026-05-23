//! Poseidon2-WOTS+ native signature scheme over BabyBear.
//!
//! This implements a Winternitz One-Time Signature (WOTS+) using Poseidon2
//! as the one-way function. Verification consists purely of Poseidon2
//! evaluations over BabyBear, making it STARK-native: verification in a
//! STARK circuit costs only ~16K constraints.
//!
//! # Design
//!
//! - **Winternitz parameter** w=16 (4-bit digits): each chain has 16 steps.
//! - **Message digest**: 256 bits => 64 base-16 digits.
//! - **Checksum**: prevents existential forgery. With 64 digits each in [0,15],
//!   max checksum = 64*15 = 960, needing ceil(log16(960)) = 3 extra chains.
//! - **Total chains**: 67 (64 message + 3 checksum).
//! - **KeyGen**: seed => PRF => 67 chain bottoms => walk each 15 steps => 67 tops = pk.
//! - **Sign(m)**: hash m to 64 digits + 3 checksum digits, reveal chain[i] at depth digit[i].
//! - **Verify(pk, sig, m)**: for each chain, walk from sig value (15 - digit) steps, check == pk top.
//!
//! # Security
//!
//! One-time security under the assumption that Poseidon2 is a one-way function
//! over BabyBear. Each key pair MUST only sign a single message.
//!
//! For multi-message use, combine with an XMSS/Merkle tree of WOTS keys
//! (also Poseidon2 Merkle, keeping the entire scheme STARK-native).

use crate::field::BabyBear;
use crate::poseidon2::{self, Poseidon2State};

/// Winternitz parameter: base-16 (4-bit digits).
pub const WOTS_W: usize = 16;

/// Number of steps per chain (w - 1).
pub const WOTS_CHAIN_STEPS: usize = WOTS_W - 1; // 15

/// Number of message chains (256-bit message hash / 4 bits per digit).
pub const WOTS_MSG_CHAINS: usize = 64;

/// Number of checksum chains.
/// Max checksum = 64 * 15 = 960, need ceil(log16(960+1)) = 3 chains (16^3 = 4096 > 960).
pub const WOTS_CHECKSUM_CHAINS: usize = 3;

/// Total number of chains.
pub const WOTS_TOTAL_CHAINS: usize = WOTS_MSG_CHAINS + WOTS_CHECKSUM_CHAINS; // 67

/// WOTS+ secret key: the chain bottoms (starting values).
#[derive(Clone, Debug)]
pub struct WotsSecretKey {
    /// 67 chain bottom values (each a BabyBear element).
    pub chain_bottoms: [BabyBear; WOTS_TOTAL_CHAINS],
}

/// WOTS+ public key: the chain tops (endpoints after walking WOTS_CHAIN_STEPS times).
#[derive(Clone, Debug)]
pub struct WotsPublicKey {
    /// 67 chain top values.
    pub chain_tops: [BabyBear; WOTS_TOTAL_CHAINS],
    /// Compressed public key: Poseidon2 hash of all chain tops.
    pub pk_hash: BabyBear,
}

/// WOTS+ signature: intermediate chain values at the digit-specified depth.
#[derive(Clone, Debug)]
pub struct WotsSignature {
    /// 67 intermediate chain values.
    pub chain_values: [BabyBear; WOTS_TOTAL_CHAINS],
    /// The message hash (32 bytes) that was signed.
    pub message_hash: [u8; 32],
}

/// One step of the WOTS chain function: H(value, chain_index, step_index).
///
/// We use Poseidon2 with domain separation to prevent cross-chain attacks:
/// state = [value, chain_idx, step_idx, 0, domain_sep, 0, 0, 0]
#[inline]
pub fn chain_step(value: BabyBear, chain_idx: usize, step_idx: usize) -> BabyBear {
    let mut state = Poseidon2State::new();
    state.state[0] = value;
    state.state[1] = BabyBear::new(chain_idx as u32);
    state.state[2] = BabyBear::new(step_idx as u32);
    state.state[4] = BabyBear::new(0x574F5453); // "WOTS" domain separator
    state.permute();
    state.state[0]
}

/// Walk a chain forward `steps` times starting from `value` at chain `chain_idx`,
/// beginning at step offset `start_step`.
pub fn chain_walk(value: BabyBear, chain_idx: usize, start_step: usize, steps: usize) -> BabyBear {
    let mut current = value;
    for s in 0..steps {
        current = chain_step(current, chain_idx, start_step + s);
    }
    current
}

/// Hash a message to a 256-bit digest using BLAKE3, then convert to 64 base-16 digits.
pub fn message_to_digits(message: &[u8]) -> [u8; WOTS_MSG_CHAINS] {
    let hash = blake3::hash(message);
    let hash_bytes = hash.as_bytes();
    let mut digits = [0u8; WOTS_MSG_CHAINS];
    for i in 0..32 {
        digits[i * 2] = hash_bytes[i] & 0x0F;
        digits[i * 2 + 1] = (hash_bytes[i] >> 4) & 0x0F;
    }
    digits
}

/// Compute the checksum for a set of message digits.
/// Checksum = sum(WOTS_CHAIN_STEPS - digit[i]) for all message digits.
/// Encoded in base-16 as WOTS_CHECKSUM_CHAINS digits.
pub fn compute_checksum(msg_digits: &[u8; WOTS_MSG_CHAINS]) -> [u8; WOTS_CHECKSUM_CHAINS] {
    let checksum: u32 = msg_digits
        .iter()
        .map(|&d| (WOTS_CHAIN_STEPS as u32) - (d as u32))
        .sum();
    let mut result = [0u8; WOTS_CHECKSUM_CHAINS];
    let mut val = checksum;
    for i in 0..WOTS_CHECKSUM_CHAINS {
        result[i] = (val % WOTS_W as u32) as u8;
        val /= WOTS_W as u32;
    }
    result
}

/// Combine message digits and checksum digits into the full digit vector.
pub fn full_digits(message: &[u8]) -> [u8; WOTS_TOTAL_CHAINS] {
    let msg_digits = message_to_digits(message);
    let checksum_digits = compute_checksum(&msg_digits);
    let mut digits = [0u8; WOTS_TOTAL_CHAINS];
    digits[..WOTS_MSG_CHAINS].copy_from_slice(&msg_digits);
    digits[WOTS_MSG_CHAINS..].copy_from_slice(&checksum_digits);
    digits
}

/// Generate a WOTS+ key pair from a 32-byte seed.
///
/// The seed is expanded via BLAKE3 keyed derivation into 67 chain bottoms,
/// then each bottom is walked 15 steps to produce the chain tops (public key).
pub fn wots_keygen(seed: &[u8; 32]) -> (WotsSecretKey, WotsPublicKey) {
    let mut chain_bottoms = [BabyBear::ZERO; WOTS_TOTAL_CHAINS];

    // Derive chain bottoms from seed
    for i in 0..WOTS_TOTAL_CHAINS {
        let derived = blake3::derive_key(&format!("pyana-wots-chain-{i}"), seed);
        let val = u32::from_le_bytes([derived[0], derived[1], derived[2], derived[3]]);
        chain_bottoms[i] = BabyBear::new(val);
    }

    // Walk each chain to get tops
    let mut chain_tops = [BabyBear::ZERO; WOTS_TOTAL_CHAINS];
    for i in 0..WOTS_TOTAL_CHAINS {
        chain_tops[i] = chain_walk(chain_bottoms[i], i, 0, WOTS_CHAIN_STEPS);
    }

    // Compress public key
    let pk_hash = poseidon2::hash_many(&chain_tops);

    let sk = WotsSecretKey { chain_bottoms };
    let pk = WotsPublicKey {
        chain_tops,
        pk_hash,
    };
    (sk, pk)
}

/// Sign a message with a WOTS+ secret key.
///
/// IMPORTANT: Each secret key MUST only be used to sign ONE message.
/// Signing a second message with the same key compromises security.
pub fn wots_sign(sk: &WotsSecretKey, message: &[u8]) -> WotsSignature {
    let digits = full_digits(message);
    let message_hash = *blake3::hash(message).as_bytes();

    let mut chain_values = [BabyBear::ZERO; WOTS_TOTAL_CHAINS];
    for i in 0..WOTS_TOTAL_CHAINS {
        // Walk from bottom to the digit-th position
        let d = digits[i] as usize;
        chain_values[i] = chain_walk(sk.chain_bottoms[i], i, 0, d);
    }

    WotsSignature {
        chain_values,
        message_hash,
    }
}

/// Verify a WOTS+ signature against a public key and message.
///
/// For each chain i with digit d:
///   chain_walk(sig.chain_values[i], i, d, WOTS_CHAIN_STEPS - d) should equal pk.chain_tops[i]
///
/// This is the function that will be proven inside a STARK.
pub fn wots_verify(pk: &WotsPublicKey, sig: &WotsSignature, message: &[u8]) -> bool {
    // Recompute digits from message
    let recomputed_hash = *blake3::hash(message).as_bytes();
    if recomputed_hash != sig.message_hash {
        return false;
    }

    let digits = full_digits(message);

    for i in 0..WOTS_TOTAL_CHAINS {
        let d = digits[i] as usize;
        let remaining = WOTS_CHAIN_STEPS - d;
        let computed_top = chain_walk(sig.chain_values[i], i, d, remaining);
        if computed_top != pk.chain_tops[i] {
            return false;
        }
    }
    true
}

/// Verify a WOTS+ signature against a public key, using a pre-computed message hash.
///
/// This is the "in-circuit" variant: the message hash is provided directly
/// (it would be a public input to the STARK). No BLAKE3 recomputation needed
/// inside the arithmetic circuit.
pub fn wots_verify_prehashed(
    pk: &WotsPublicKey,
    sig: &WotsSignature,
    message_hash: &[u8; 32],
) -> bool {
    if *message_hash != sig.message_hash {
        return false;
    }

    // Convert hash to digits
    let mut msg_digits = [0u8; WOTS_MSG_CHAINS];
    for i in 0..32 {
        msg_digits[i * 2] = message_hash[i] & 0x0F;
        msg_digits[i * 2 + 1] = (message_hash[i] >> 4) & 0x0F;
    }
    let checksum_digits = compute_checksum(&msg_digits);
    let mut digits = [0u8; WOTS_TOTAL_CHAINS];
    digits[..WOTS_MSG_CHAINS].copy_from_slice(&msg_digits);
    digits[WOTS_MSG_CHAINS..].copy_from_slice(&checksum_digits);

    for i in 0..WOTS_TOTAL_CHAINS {
        let d = digits[i] as usize;
        let remaining = WOTS_CHAIN_STEPS - d;
        let computed_top = chain_walk(sig.chain_values[i], i, d, remaining);
        if computed_top != pk.chain_tops[i] {
            return false;
        }
    }
    true
}

/// Compute the public key hash from chain tops.
/// This is what gets stored in the validator set Merkle tree.
pub fn compute_pk_hash(chain_tops: &[BabyBear; WOTS_TOTAL_CHAINS]) -> BabyBear {
    poseidon2::hash_many(chain_tops)
}

// ============================================================================
// Validator Set Management
// ============================================================================

/// A validator's identity in the STARK-native scheme.
#[derive(Clone, Debug)]
pub struct ValidatorIdentity {
    /// The validator's public key.
    pub public_key: WotsPublicKey,
    /// Index in the validator set.
    pub index: usize,
    /// Voting weight (typically 1 for equal-weight).
    pub weight: u32,
}

/// A validator set with a Poseidon2 Merkle commitment.
#[derive(Clone, Debug)]
pub struct ValidatorSet {
    /// Ordered list of validator public key hashes.
    pub pk_hashes: Vec<BabyBear>,
    /// Weights for each validator.
    pub weights: Vec<u32>,
    /// Poseidon2 Merkle root of the validator set.
    pub root: BabyBear,
}

impl ValidatorSet {
    /// Create a new validator set from public keys and weights.
    pub fn new(public_keys: &[WotsPublicKey], weights: &[u32]) -> Self {
        assert_eq!(public_keys.len(), weights.len());
        let pk_hashes: Vec<BabyBear> = public_keys.iter().map(|pk| pk.pk_hash).collect();
        let root = compute_validator_set_root(&pk_hashes);
        Self {
            pk_hashes,
            weights: weights.to_vec(),
            root,
        }
    }

    /// Total weight of the validator set.
    pub fn total_weight(&self) -> u32 {
        self.weights.iter().sum()
    }

    /// Check if a set of signer indices meets the threshold.
    pub fn meets_threshold(&self, signer_indices: &[usize], threshold: u32) -> bool {
        let signed_weight: u32 = signer_indices
            .iter()
            .filter_map(|&i| self.weights.get(i))
            .sum();
        signed_weight >= threshold
    }
}

/// Compute the Poseidon2 Merkle root of a validator set.
///
/// Uses a binary Merkle tree with Poseidon2 hash_2_to_1.
/// Pads to the next power of 2 with zeros.
pub fn compute_validator_set_root(pk_hashes: &[BabyBear]) -> BabyBear {
    if pk_hashes.is_empty() {
        return BabyBear::ZERO;
    }
    if pk_hashes.len() == 1 {
        return pk_hashes[0];
    }

    // Pad to next power of 2
    let n = pk_hashes.len().next_power_of_two();
    let mut layer: Vec<BabyBear> = pk_hashes.to_vec();
    layer.resize(n, BabyBear::ZERO);

    // Build tree bottom-up
    while layer.len() > 1 {
        let mut next_layer = Vec::with_capacity(layer.len() / 2);
        for i in (0..layer.len()).step_by(2) {
            next_layer.push(poseidon2::hash_2_to_1(layer[i], layer[i + 1]));
        }
        layer = next_layer;
    }

    layer[0]
}

/// Compute a Merkle proof (sibling path) for a leaf at the given index.
pub fn compute_merkle_proof(pk_hashes: &[BabyBear], index: usize) -> Vec<BabyBear> {
    let n = pk_hashes.len().next_power_of_two();
    let mut layer: Vec<BabyBear> = pk_hashes.to_vec();
    layer.resize(n, BabyBear::ZERO);

    let mut proof = Vec::new();
    let mut idx = index;

    while layer.len() > 1 {
        let sibling_idx = idx ^ 1;
        proof.push(layer[sibling_idx]);

        let mut next_layer = Vec::with_capacity(layer.len() / 2);
        for i in (0..layer.len()).step_by(2) {
            next_layer.push(poseidon2::hash_2_to_1(layer[i], layer[i + 1]));
        }
        layer = next_layer;
        idx /= 2;
    }

    proof
}

/// Verify a Merkle proof for a pk_hash at a given index against the root.
pub fn verify_merkle_proof(
    pk_hash: BabyBear,
    index: usize,
    proof: &[BabyBear],
    root: BabyBear,
) -> bool {
    let mut current = pk_hash;
    let mut idx = index;

    for sibling in proof {
        if idx & 1 == 0 {
            current = poseidon2::hash_2_to_1(current, *sibling);
        } else {
            current = poseidon2::hash_2_to_1(*sibling, current);
        }
        idx /= 2;
    }

    current == root
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn chain_step_deterministic() {
        let v = BabyBear::new(42);
        let s1 = chain_step(v, 0, 0);
        let s2 = chain_step(v, 0, 0);
        assert_eq!(s1, s2);
        assert_ne!(s1, v); // should actually hash
    }

    #[test]
    fn chain_step_domain_separation() {
        let v = BabyBear::new(42);
        // Different chain index => different output
        assert_ne!(chain_step(v, 0, 0), chain_step(v, 1, 0));
        // Different step index => different output
        assert_ne!(chain_step(v, 0, 0), chain_step(v, 0, 1));
    }

    #[test]
    fn keygen_produces_valid_keys() {
        let seed = [0xAB_u8; 32];
        let (sk, pk) = wots_keygen(&seed);

        // Verify that walking from bottom to top works
        for i in 0..WOTS_TOTAL_CHAINS {
            let computed_top = chain_walk(sk.chain_bottoms[i], i, 0, WOTS_CHAIN_STEPS);
            assert_eq!(computed_top, pk.chain_tops[i]);
        }
    }

    #[test]
    fn sign_verify_roundtrip() {
        let seed = [0x42_u8; 32];
        let (sk, pk) = wots_keygen(&seed);

        let message = b"hello world, this is a test message for WOTS+";
        let sig = wots_sign(&sk, message);
        assert!(wots_verify(&pk, &sig, message));
    }

    #[test]
    fn verify_rejects_wrong_message() {
        let seed = [0x42_u8; 32];
        let (sk, pk) = wots_keygen(&seed);

        let message = b"correct message";
        let sig = wots_sign(&sk, message);

        let wrong_message = b"wrong message";
        assert!(!wots_verify(&pk, &sig, wrong_message));
    }

    #[test]
    fn verify_rejects_wrong_key() {
        let seed1 = [0x42_u8; 32];
        let seed2 = [0x43_u8; 32];
        let (sk1, _pk1) = wots_keygen(&seed1);
        let (_sk2, pk2) = wots_keygen(&seed2);

        let message = b"test message";
        let sig = wots_sign(&sk1, message);

        // Verify against wrong public key
        assert!(!wots_verify(&pk2, &sig, message));
    }

    #[test]
    fn prehashed_verify_works() {
        let seed = [0x55_u8; 32];
        let (sk, pk) = wots_keygen(&seed);

        let message = b"prehashed verification test";
        let sig = wots_sign(&sk, message);
        let hash = *blake3::hash(message).as_bytes();

        assert!(wots_verify_prehashed(&pk, &sig, &hash));
    }

    #[test]
    fn checksum_prevents_trivial_forgery() {
        // The checksum ensures that you cannot decrease a digit without
        // increasing another (which would require inverting Poseidon2).
        let msg = b"test";
        let digits = full_digits(msg);

        // Verify all digits are in range
        for d in &digits {
            assert!(*d < WOTS_W as u8);
        }

        // Verify checksum is consistent
        let msg_digits: [u8; WOTS_MSG_CHAINS] = digits[..WOTS_MSG_CHAINS].try_into().unwrap();
        let cs = compute_checksum(&msg_digits);
        assert_eq!(&digits[WOTS_MSG_CHAINS..], &cs);
    }

    #[test]
    fn pk_hash_deterministic() {
        let seed = [0x99_u8; 32];
        let (_sk, pk) = wots_keygen(&seed);
        let recomputed = compute_pk_hash(&pk.chain_tops);
        assert_eq!(pk.pk_hash, recomputed);
    }

    #[test]
    fn validator_set_merkle() {
        let seeds: Vec<[u8; 32]> = (0..5).map(|i| [i as u8; 32]).collect();
        let keys: Vec<(WotsSecretKey, WotsPublicKey)> =
            seeds.iter().map(|s| wots_keygen(s)).collect();
        let pks: Vec<WotsPublicKey> = keys.iter().map(|(_, pk)| pk.clone()).collect();
        let weights = vec![1u32; 5];

        let vs = ValidatorSet::new(&pks, &weights);

        // Verify each validator's Merkle proof
        for i in 0..5 {
            let proof = compute_merkle_proof(&vs.pk_hashes, i);
            assert!(verify_merkle_proof(vs.pk_hashes[i], i, &proof, vs.root));
        }
    }

    #[test]
    fn validator_set_threshold() {
        let seeds: Vec<[u8; 32]> = (0..5).map(|i| [i as u8; 32]).collect();
        let keys: Vec<(WotsSecretKey, WotsPublicKey)> =
            seeds.iter().map(|s| wots_keygen(s)).collect();
        let pks: Vec<WotsPublicKey> = keys.iter().map(|(_, pk)| pk.clone()).collect();
        let weights = vec![1, 2, 1, 2, 1]; // total = 7

        let vs = ValidatorSet::new(&pks, &weights);
        assert_eq!(vs.total_weight(), 7);

        // 2/3 threshold = 5
        assert!(vs.meets_threshold(&[1, 3, 4], 5)); // weight 2+2+1 = 5
        assert!(!vs.meets_threshold(&[0, 2, 4], 5)); // weight 1+1+1 = 3
    }

    #[test]
    fn different_seeds_different_keys() {
        let (_, pk1) = wots_keygen(&[0x01; 32]);
        let (_, pk2) = wots_keygen(&[0x02; 32]);
        assert_ne!(pk1.pk_hash, pk2.pk_hash);
    }
}
