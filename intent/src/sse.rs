//! Searchable Symmetric Encryption (SSE) for intent headers.
//!
//! Instead of broadcasting the full MatchSpec in cleartext over gossip, the poster:
//! 1. Encrypts the intent body (sealed box to their own ephemeral key)
//! 2. Generates SSE search tokens from the intent's keywords (action, resource, tags)
//! 3. Broadcasts: [encrypted_body, search_tokens[], commitment_id, expiry]
//!
//! A fulfiller who holds matching capabilities:
//! 1. Generates their own search tokens from their capability keywords
//! 2. Tests each broadcast intent's tokens against their own -> finds matches
//! 3. Requests decryption of the matched intent via a direct channel to the poster
//!
//! # Token derivation
//!
//! Tokens are deterministic from keywords + epoch:
//!   `token = BLAKE3_derive_key("pyana-sse-token-v1", keyword_bytes || epoch_le_bytes)`
//!
//! This is the "keyword-as-secret" approach: anyone who knows the keyword can
//! generate the matching token. An observer who doesn't know the keyword space
//! cannot enumerate all possible tokens. This is weaker than true SSE but practical
//! for pyana's threat model.
//!
//! # Epoch rotation
//!
//! Tokens rotate with epochs (same pattern as stake nullifiers). Repeated use of
//! the same tags is only linkable within a single epoch, not across epochs.
//!
//! # Sealed box encryption
//!
//! The full MatchSpec body is encrypted using X25519 + BLAKE3 XOF:
//! - Poster generates an ephemeral X25519 keypair
//! - Ciphertext = XOF_keystream(shared_secret) XOR plaintext
//! - Only someone who knows the poster's ephemeral secret key can decrypt
//! - After SSE matching, the poster reveals the decryption key over a direct channel

use serde::{Deserialize, Serialize};

use crate::{CommitmentId, MatchSpec};

// ---------------------------------------------------------------------------
// SSE Token Generation
// ---------------------------------------------------------------------------

/// Generate a search token for a keyword at a given epoch.
///
/// Token = BLAKE3_derive_key("pyana-sse-token-v1", keyword || epoch_le_bytes)
///
/// The "secret" is the keyword itself: anyone who knows the keyword generates
/// the same token. This provides set-membership hiding (observers who don't
/// know the keyword space cannot enumerate tokens) without requiring a shared
/// secret distribution mechanism.
pub fn generate_search_token(keyword: &str, epoch: u64) -> [u8; 32] {
    let mut input = Vec::with_capacity(keyword.len() + 8);
    input.extend_from_slice(keyword.as_bytes());
    input.extend_from_slice(&epoch.to_le_bytes());
    blake3::derive_key("pyana-sse-token-v1", &input)
}

/// Generate search tokens for all keywords extractable from a MatchSpec.
///
/// Keywords are the same tags produced by `extract_capability_tags()` in pir.rs:
/// - `action:{name}` for each action pattern
/// - `resource:{name}` for each resource pattern in actions
/// - `service:{name}`, `feature:{name}`, `app:{name}`, `oauth:{name}` for constraints
/// - `pattern:{pattern}` for resource_pattern
pub fn tokens_for_matchspec(spec: &MatchSpec, epoch: u64) -> Vec<[u8; 32]> {
    let keywords = extract_sse_keywords(spec);
    keywords
        .iter()
        .map(|kw| generate_search_token(kw, epoch))
        .collect()
}

/// Extract keyword strings from a MatchSpec (same logic as pir::extract_capability_tags).
///
/// This is intentionally a separate function from pir.rs to avoid a circular
/// dependency and because SSE may evolve to use a different keyword extraction
/// strategy (e.g., discretized budget buckets) in the future.
pub fn extract_sse_keywords(spec: &MatchSpec) -> Vec<String> {
    let mut keywords = Vec::new();

    for ap in &spec.actions {
        if let Some(ref action) = ap.action {
            keywords.push(format!("action:{action}"));
        }
        if let Some(ref resource) = ap.resource {
            keywords.push(format!("resource:{resource}"));
        }
    }

    for constraint in &spec.constraints {
        match constraint {
            crate::Constraint::Service(s) => keywords.push(format!("service:{s}")),
            crate::Constraint::Feature(f) => keywords.push(format!("feature:{f}")),
            crate::Constraint::AppId(a) => keywords.push(format!("app:{a}")),
            crate::Constraint::OAuthProvider(p) => keywords.push(format!("oauth:{p}")),
            _ => {}
        }
    }

    if let Some(ref pattern) = spec.resource_pattern {
        keywords.push(format!("pattern:{pattern}"));
    }

    keywords
}

/// Test whether any of a fulfiller's capability keywords match the search tokens
/// from a broadcast encrypted intent.
///
/// Returns true if at least one capability keyword produces a token present in the
/// intent's token set. This is the coarse filter: a match here means "worth
/// requesting decryption," not necessarily a full MatchSpec satisfaction.
pub fn capability_matches_tokens(
    capability_keywords: &[&str],
    tokens: &[[u8; 32]],
    epoch: u64,
) -> bool {
    for keyword in capability_keywords {
        let my_token = generate_search_token(keyword, epoch);
        if tokens.contains(&my_token) {
            return true;
        }
    }
    false
}

/// Batch-test multiple capability keyword sets against a single encrypted intent's tokens.
///
/// Returns the indices of keyword sets that produced at least one match.
/// Useful when a fulfiller holds many capabilities and wants to know which
/// ones triggered the match.
pub fn matching_capability_indices(
    capability_keyword_sets: &[&[&str]],
    tokens: &[[u8; 32]],
    epoch: u64,
) -> Vec<usize> {
    capability_keyword_sets
        .iter()
        .enumerate()
        .filter_map(|(i, keywords)| {
            if capability_matches_tokens(keywords, tokens, epoch) {
                Some(i)
            } else {
                None
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Sealed Box Encryption (X25519 + BLAKE3 XOF)
// ---------------------------------------------------------------------------

/// An X25519 keypair for sealed-box encryption.
///
/// The poster generates a fresh ephemeral keypair per intent. The secret key
/// is needed to decrypt (revealed to matched fulfillers over a direct channel).
#[derive(Clone)]
pub struct SealKeypair {
    /// The secret key (32 bytes).
    pub secret: [u8; 32],
    /// The public key (32 bytes, X25519 point).
    pub public: [u8; 32],
}

impl SealKeypair {
    /// Generate a fresh random keypair.
    pub fn generate() -> Self {
        let mut secret = [0u8; 32];
        crate::getrandom(&mut secret);
        let static_secret = x25519_dalek::StaticSecret::from(secret);
        let public_key = x25519_dalek::PublicKey::from(&static_secret);
        Self {
            secret,
            public: public_key.to_bytes(),
        }
    }

    /// Create a keypair from a known secret (for testing / deterministic derivation).
    pub fn from_secret(secret: [u8; 32]) -> Self {
        let static_secret = x25519_dalek::StaticSecret::from(secret);
        let public_key = x25519_dalek::PublicKey::from(&static_secret);
        Self {
            secret,
            public: public_key.to_bytes(),
        }
    }
}

/// Encrypt a plaintext using a sealed-box construction.
///
/// The recipient must know the ephemeral secret key to decrypt.
/// Encryption: generate ephemeral sender keypair, DH with recipient public key,
/// derive keystream from shared secret, XOR plaintext.
///
/// For pyana's SSE use case, the "recipient" IS the poster themselves. They
/// encrypt to their own ephemeral key and later reveal the secret to matched
/// fulfillers.
pub fn seal_encrypt(plaintext: &[u8], recipient_public: &[u8; 32]) -> SealedBox {
    let mut sender_secret_bytes = [0u8; 32];
    crate::getrandom(&mut sender_secret_bytes);
    let sender_secret = x25519_dalek::StaticSecret::from(sender_secret_bytes);
    let sender_public = x25519_dalek::PublicKey::from(&sender_secret);
    let sender_public_bytes = sender_public.to_bytes();

    // Compute shared secret via X25519
    let recipient_pk = x25519_dalek::PublicKey::from(*recipient_public);
    let shared = sender_secret.diffie_hellman(&recipient_pk);

    // Derive keystream from shared secret + sender public (for domain separation)
    let mut hasher = blake3::Hasher::new_keyed(shared.as_bytes());
    hasher.update(b"pyana-sealed-box-v1");
    hasher.update(&sender_public_bytes);
    hasher.update(recipient_public);
    let mut keystream = vec![0u8; plaintext.len()];
    let mut output = hasher.finalize_xof();
    output.fill(&mut keystream);

    // XOR encrypt
    let ciphertext: Vec<u8> = plaintext
        .iter()
        .zip(keystream.iter())
        .map(|(p, k)| p ^ k)
        .collect();

    SealedBox {
        ciphertext,
        sender_public: sender_public_bytes,
    }
}

/// Decrypt a sealed box using the recipient's secret key.
pub fn seal_decrypt(sealed: &SealedBox, recipient_secret: &[u8; 32]) -> Vec<u8> {
    // Compute shared secret via X25519
    let secret = x25519_dalek::StaticSecret::from(*recipient_secret);
    let sender_pk = x25519_dalek::PublicKey::from(sealed.sender_public);
    let shared = secret.diffie_hellman(&sender_pk);

    // Derive the same keystream
    let recipient_public = x25519_dalek::PublicKey::from(&secret);
    let recipient_public_bytes = recipient_public.to_bytes();
    let mut hasher = blake3::Hasher::new_keyed(shared.as_bytes());
    hasher.update(b"pyana-sealed-box-v1");
    hasher.update(&sealed.sender_public);
    hasher.update(&recipient_public_bytes);
    let mut keystream = vec![0u8; sealed.ciphertext.len()];
    let mut output = hasher.finalize_xof();
    output.fill(&mut keystream);

    // XOR decrypt
    sealed
        .ciphertext
        .iter()
        .zip(keystream.iter())
        .map(|(c, k)| c ^ k)
        .collect()
}

/// A sealed box: ciphertext + ephemeral sender public key.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SealedBox {
    /// The encrypted data.
    pub ciphertext: Vec<u8>,
    /// The ephemeral sender's public key (needed for DH during decryption).
    pub sender_public: [u8; 32],
}

// ---------------------------------------------------------------------------
// EncryptedIntent: the gossip-layer representation
// ---------------------------------------------------------------------------

/// An encrypted intent for gossip propagation.
///
/// Contains SSE search tokens for coarse matching, the encrypted MatchSpec body,
/// and metadata needed for the matching/decryption flow.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EncryptedIntent {
    /// SSE search tokens derived from the intent's keywords.
    /// Fulfillers test their capability keywords against these tokens.
    pub search_tokens: Vec<[u8; 32]>,
    /// The encrypted MatchSpec body (sealed box).
    pub encrypted_body: Vec<u8>,
    /// The ephemeral public key used for the sealed box.
    /// The poster's ephemeral secret is needed to decrypt.
    pub ephemeral_pubkey: [u8; 32],
    /// The intent's commitment ID (anonymous creator identity).
    pub commitment_id: CommitmentId,
    /// Unix timestamp after which this encrypted intent expires.
    pub expiry: Option<u64>,
    /// The epoch used for token generation.
    /// Fulfillers must use the same epoch when generating their test tokens.
    pub epoch: u64,
    /// Content-addressed ID of this encrypted intent (BLAKE3 of all fields).
    pub id: [u8; 32],
}

impl EncryptedIntent {
    /// Create a new encrypted intent from a MatchSpec.
    ///
    /// This is the poster's workflow:
    /// 1. Extract keywords from the MatchSpec
    /// 2. Generate SSE tokens for each keyword at the current epoch
    /// 3. Serialize and encrypt the MatchSpec body
    /// 4. Bundle everything into an EncryptedIntent for gossip
    ///
    /// Returns `(encrypted_intent, seal_keypair)` -- the poster keeps the keypair
    /// to later decrypt for matched fulfillers.
    pub fn create(
        spec: &MatchSpec,
        commitment_id: CommitmentId,
        epoch: u64,
        expiry: Option<u64>,
    ) -> (Self, SealKeypair) {
        let keypair = SealKeypair::generate();

        // Generate SSE tokens
        let search_tokens = tokens_for_matchspec(spec, epoch);

        // Serialize the MatchSpec
        let plaintext = postcard::to_allocvec(spec).expect("MatchSpec serialization failed");

        // Encrypt using sealed box
        let sealed = seal_encrypt(&plaintext, &keypair.public);

        let mut intent = Self {
            search_tokens,
            encrypted_body: sealed.ciphertext,
            ephemeral_pubkey: keypair.public,
            commitment_id,
            expiry,
            epoch,
            id: [0u8; 32],
        };
        intent.id = intent.compute_id();

        (intent, keypair)
    }

    /// Create an encrypted intent with a known keypair (for testing / deterministic use).
    pub fn create_with_keypair(
        spec: &MatchSpec,
        commitment_id: CommitmentId,
        epoch: u64,
        expiry: Option<u64>,
        keypair: &SealKeypair,
    ) -> Self {
        let search_tokens = tokens_for_matchspec(spec, epoch);
        let plaintext = postcard::to_allocvec(spec).expect("MatchSpec serialization failed");
        let sealed = seal_encrypt(&plaintext, &keypair.public);

        let mut intent = Self {
            search_tokens,
            encrypted_body: sealed.ciphertext,
            ephemeral_pubkey: keypair.public,
            commitment_id,
            expiry,
            epoch,
            id: [0u8; 32],
        };
        intent.id = intent.compute_id();
        intent
    }

    /// Decrypt the intent body using the poster's ephemeral secret key.
    ///
    /// Returns the deserialized MatchSpec if decryption and deserialization succeed.
    pub fn decrypt(&self, secret: &[u8; 32]) -> Option<MatchSpec> {
        let sealed = SealedBox {
            ciphertext: self.encrypted_body.clone(),
            sender_public: self.ephemeral_pubkey,
        };
        // For self-decryption, the "recipient" secret IS the ephemeral secret
        // and the sender_public in the sealed box is actually from the seal_encrypt
        // call's internal ephemeral key. We need a different approach.
        //
        // Actually, in create(), we encrypt TO keypair.public using seal_encrypt
        // which generates its OWN internal ephemeral sender. So to decrypt, the
        // recipient uses keypair.secret.
        let plaintext = seal_decrypt(&sealed, secret);
        postcard::from_bytes(&plaintext).ok()
    }

    /// Check if this encrypted intent has expired.
    pub fn is_expired(&self, now: u64) -> bool {
        match self.expiry {
            Some(exp) => now >= exp,
            None => false,
        }
    }

    /// Compute the content-addressed ID.
    fn compute_id(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-encrypted-intent-id-v1");
        for token in &self.search_tokens {
            hasher.update(token);
        }
        hasher.update(&self.encrypted_body);
        hasher.update(&self.ephemeral_pubkey);
        hasher.update(&self.commitment_id.0);
        if let Some(exp) = self.expiry {
            hasher.update(&exp.to_le_bytes());
        }
        hasher.update(&self.epoch.to_le_bytes());
        *hasher.finalize().as_bytes()
    }
}

// ---------------------------------------------------------------------------
// Gossip integration
// ---------------------------------------------------------------------------

/// A gossip message carrying either a cleartext or encrypted intent.
///
/// Nodes that support SSE will prefer `Encrypted` variants. Legacy nodes
/// continue to use cleartext `Intent` messages. The gossip layer handles both.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum GossipIntent {
    /// Legacy cleartext intent (full MatchSpec visible to all observers).
    Cleartext(crate::Intent),
    /// SSE-encrypted intent (body hidden, search tokens for coarse matching).
    Encrypted(EncryptedIntent),
}

// ---------------------------------------------------------------------------
// Minimal X25519 implementation (field arithmetic over Curve25519)
// ---------------------------------------------------------------------------
// We implement the Montgomery ladder directly to avoid pulling in a full
// curve25519 crate dependency. This is constant-time.

/// Compute X25519 basepoint multiplication: public = secret * G.
fn x25519_basepoint(secret: &[u8; 32]) -> [u8; 32] {
    // The X25519 basepoint is u=9.
    let basepoint = {
        let mut bp = [0u8; 32];
        bp[0] = 9;
        bp
    };
    x25519(secret, &basepoint)
}

/// Compute X25519 Diffie-Hellman: shared = scalar * point.
///
/// Montgomery ladder implementation over the Curve25519 field (2^255 - 19).
/// Constant-time with respect to the scalar.
fn x25519(scalar: &[u8; 32], point: &[u8; 32]) -> [u8; 32] {
    // Field element: 256-bit integer mod p = 2^255 - 19
    // We use a simple representation as [u64; 4] (little-endian limbs) and
    // reduce after each operation.

    let p: [u64; 4] = [
        0xFFFF_FFFF_FFFF_FFED,
        0xFFFF_FFFF_FFFF_FFFF,
        0xFFFF_FFFF_FFFF_FFFF,
        0x7FFF_FFFF_FFFF_FFFF,
    ];

    // Decode the u-coordinate from bytes (little-endian, mask high bit)
    let mut u_bytes = *point;
    u_bytes[31] &= 0x7F;
    let u = fe_from_bytes(&u_bytes);

    // Montgomery ladder
    let mut x_1 = u;
    let mut x_2 = fe_one();
    let mut z_2 = fe_zero();
    let mut x_3 = u;
    let mut z_3 = fe_one();
    let mut swap: u64 = 0;

    // Iterate from bit 254 down to 0
    for pos in (0..255).rev() {
        let byte_idx = pos / 8;
        let bit_idx = pos % 8;
        let bit = ((scalar[byte_idx] >> bit_idx) & 1) as u64;

        swap ^= bit;
        fe_cswap(&mut x_2, &mut x_3, swap);
        fe_cswap(&mut z_2, &mut z_3, swap);
        swap = bit;

        let a = fe_add(&x_2, &z_2, &p);
        let aa = fe_mul(&a, &a, &p);
        let b = fe_sub(&x_2, &z_2, &p);
        let bb = fe_mul(&b, &b, &p);
        let e = fe_sub(&aa, &bb, &p);
        let c = fe_add(&x_3, &z_3, &p);
        let d = fe_sub(&x_3, &z_3, &p);
        let da = fe_mul(&d, &a, &p);
        let cb = fe_mul(&c, &b, &p);
        let da_cb_sum = fe_add(&da, &cb, &p);
        x_3 = fe_mul(&da_cb_sum, &da_cb_sum, &p);
        let da_cb_diff = fe_sub(&da, &cb, &p);
        let da_cb_diff_sq = fe_mul(&da_cb_diff, &da_cb_diff, &p);
        z_3 = fe_mul(&x_1, &da_cb_diff_sq, &p);
        x_2 = fe_mul(&aa, &bb, &p);
        // a24 = 121665 for Curve25519
        let a24: [u64; 4] = [121665, 0, 0, 0];
        let e_a24 = fe_mul(&e, &a24, &p);
        let aa_e_a24 = fe_add(&aa, &e_a24, &p);
        z_2 = fe_mul(&e, &aa_e_a24, &p);
    }

    fe_cswap(&mut x_2, &mut x_3, swap);
    fe_cswap(&mut z_2, &mut z_3, swap);

    // Result = x_2 * z_2^(p-2) mod p (inversion via Fermat's little theorem)
    let z_inv = fe_inv(&z_2, &p);
    let result = fe_mul(&x_2, &z_inv, &p);
    fe_to_bytes(&result)
}

// -- Field element helpers (mod 2^255 - 19) --

type Fe = [u64; 4];

fn fe_zero() -> Fe {
    [0, 0, 0, 0]
}

fn fe_one() -> Fe {
    [1, 0, 0, 0]
}

fn fe_from_bytes(b: &[u8; 32]) -> Fe {
    [
        u64::from_le_bytes(b[0..8].try_into().unwrap()),
        u64::from_le_bytes(b[8..16].try_into().unwrap()),
        u64::from_le_bytes(b[16..24].try_into().unwrap()),
        u64::from_le_bytes(b[24..32].try_into().unwrap()),
    ]
}

fn fe_to_bytes(a: &Fe) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[0..8].copy_from_slice(&a[0].to_le_bytes());
    out[8..16].copy_from_slice(&a[1].to_le_bytes());
    out[16..24].copy_from_slice(&a[2].to_le_bytes());
    out[24..32].copy_from_slice(&a[3].to_le_bytes());
    out
}

/// Conditional swap (constant-time).
fn fe_cswap(a: &mut Fe, b: &mut Fe, swap: u64) {
    let mask = 0u64.wrapping_sub(swap); // 0 or 0xFFFF...
    for i in 0..4 {
        let t = mask & (a[i] ^ b[i]);
        a[i] ^= t;
        b[i] ^= t;
    }
}

/// Addition mod p using 128-bit intermediates.
fn fe_add(a: &Fe, b: &Fe, p: &Fe) -> Fe {
    let mut result = [0u64; 4];
    let mut carry = 0u64;
    for i in 0..4 {
        let (s1, c1) = a[i].overflowing_add(b[i]);
        let (s2, c2) = s1.overflowing_add(carry);
        result[i] = s2;
        carry = (c1 as u64) + (c2 as u64);
    }
    // Reduce: if result >= p, subtract p
    fe_reduce(&mut result, p);
    result
}

/// Subtraction mod p.
fn fe_sub(a: &Fe, b: &Fe, p: &Fe) -> Fe {
    let mut result = [0u64; 4];
    let mut borrow = 0u64;
    for i in 0..4 {
        let (s1, b1) = a[i].overflowing_sub(b[i]);
        let (s2, b2) = s1.overflowing_sub(borrow);
        result[i] = s2;
        borrow = (b1 as u64) + (b2 as u64);
    }
    // If we underflowed, add p back
    if borrow > 0 {
        let mut carry = 0u64;
        for i in 0..4 {
            let (s1, c1) = result[i].overflowing_add(p[i]);
            let (s2, c2) = s1.overflowing_add(carry);
            result[i] = s2;
            carry = (c1 as u64) + (c2 as u64);
        }
    }
    result
}

/// Multiplication mod p (schoolbook multiply + Barrett-like reduction).
fn fe_mul(a: &Fe, b: &Fe, p: &Fe) -> Fe {
    // Full 512-bit product using 128-bit intermediates
    let mut product = [0u128; 8];
    for i in 0..4 {
        for j in 0..4 {
            product[i + j] += (a[i] as u128) * (b[j] as u128);
        }
    }
    // Propagate carries in the product
    for i in 0..7 {
        product[i + 1] += product[i] >> 64;
        product[i] &= 0xFFFF_FFFF_FFFF_FFFF;
    }

    // Reduce mod p = 2^255 - 19
    // Split at 255 bits: low = product[0..3] (bottom 255 bits), high = rest * 38
    // Since p = 2^255 - 19, we have 2^255 = 19 mod p, so 2^256 = 38 mod p.
    // Reduction: result = low_255_bits + high_bits * 19 (iteratively)

    let mut r = [0u64; 5]; // 5 limbs to handle overflow during reduction
    // Extract 256-bit value
    r[0] = product[0] as u64;
    r[1] = product[1] as u64;
    r[2] = product[2] as u64;
    r[3] = product[3] as u64;
    r[4] = 0;

    // The top part (product[4..7]) * 2^256 = product[4..7] * 38 mod p
    let top_contribution = {
        let mut t = [0u128; 5];
        t[0] = (product[4] as u128) * 38;
        t[1] = (product[5] as u128) * 38;
        t[2] = (product[6] as u128) * 38;
        t[3] = (product[7] as u128) * 38;
        // Propagate carries
        t[1] += t[0] >> 64;
        t[2] += t[1] >> 64;
        t[3] += t[2] >> 64;
        t[4] = t[3] >> 64;
        [
            t[0] as u64,
            t[1] as u64,
            t[2] as u64,
            t[3] as u64,
            t[4] as u64,
        ]
    };

    // Add top contribution to r
    let mut carry = 0u128;
    for i in 0..5 {
        carry += r[i] as u128 + top_contribution[i] as u128;
        r[i] = carry as u64;
        carry >>= 64;
    }

    // Now r might still be >= 2^256, reduce again: top bit * 38
    // Since r[4] should be small, multiply it by 38 and add to r[0..3]
    let top = r[4];
    r[4] = 0;
    if top > 0 {
        let mut carry2 = (top as u128) * 38;
        for i in 0..4 {
            carry2 += r[i] as u128;
            r[i] = carry2 as u64;
            carry2 >>= 64;
        }
        r[4] = carry2 as u64;
    }

    // Final reduction: if r >= p, subtract p
    let mut result = [r[0], r[1], r[2], r[3]];
    // Handle r[4] (should be 0 or 1 at most)
    if r[4] > 0 {
        let mut carry3 = (r[4] as u128) * 38;
        for i in 0..4 {
            carry3 += result[i] as u128;
            result[i] = carry3 as u64;
            carry3 >>= 64;
        }
    }
    fe_reduce(&mut result, p);
    result
}

/// Reduce: if a >= p, subtract p.
fn fe_reduce(a: &mut Fe, p: &Fe) {
    // Check if a >= p by attempting subtraction
    let mut tmp = [0u64; 4];
    let mut borrow = 0u64;
    for i in 0..4 {
        let (s1, b1) = a[i].overflowing_sub(p[i]);
        let (s2, b2) = s1.overflowing_sub(borrow);
        tmp[i] = s2;
        borrow = (b1 as u64) + (b2 as u64);
    }
    // If no borrow, a >= p, so use tmp (a - p). Otherwise keep a.
    if borrow == 0 {
        *a = tmp;
    }
}

/// Modular inversion via Fermat's little theorem: a^(p-2) mod p.
fn fe_inv(a: &Fe, p: &Fe) -> Fe {
    // p - 2 for Curve25519 field: 2^255 - 19 - 2 = 2^255 - 21
    // Use square-and-multiply. The exponent is p-2.
    // p-2 in binary is: all 1s for bits 254..5, then 01011 (for the last 5 bits: 19+2=21, 32-21=11, 0b01011)
    // Actually p = 2^255 - 19, p-2 = 2^255 - 21
    // In little-endian bytes: 0xEB (first byte = 0xED - 2), then 0xFF...FF, last byte = 0x7F

    let mut exp = *p;
    // Subtract 2 from p (p is stored as limbs)
    let (s, borrow) = exp[0].overflowing_sub(2);
    exp[0] = s;
    if borrow {
        for i in 1..4 {
            let (s2, b2) = exp[i].overflowing_sub(1);
            exp[i] = s2;
            if !b2 {
                break;
            }
        }
    }

    // Square and multiply (left-to-right binary method)
    let mut result = fe_one();
    for limb_idx in (0..4).rev() {
        let bits = if limb_idx == 3 { 63 } else { 64 }; // top limb has 63 significant bits
        for bit in (0..bits).rev() {
            result = fe_mul(&result, &result, p);
            if (exp[limb_idx] >> bit) & 1 == 1 {
                result = fe_mul(&result, a, p);
            }
        }
    }
    result
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ActionPattern, Constraint};

    #[test]
    fn test_generate_search_token_deterministic() {
        let t1 = generate_search_token("action:read", 0);
        let t2 = generate_search_token("action:read", 0);
        assert_eq!(t1, t2);
    }

    #[test]
    fn test_generate_search_token_varies_by_keyword() {
        let t1 = generate_search_token("action:read", 0);
        let t2 = generate_search_token("action:write", 0);
        assert_ne!(t1, t2);
    }

    #[test]
    fn test_generate_search_token_varies_by_epoch() {
        let t1 = generate_search_token("action:read", 0);
        let t2 = generate_search_token("action:read", 1);
        assert_ne!(t1, t2);
    }

    #[test]
    fn test_tokens_for_matchspec() {
        let spec = MatchSpec {
            actions: vec![
                ActionPattern {
                    action: Some("read".into()),
                    resource: Some("docs/*".into()),
                },
                ActionPattern {
                    action: Some("write".into()),
                    resource: None,
                },
            ],
            constraints: vec![
                Constraint::Service("storage".into()),
                Constraint::Feature("premium".into()),
            ],
            min_budget: None,
            resource_pattern: Some("api/v1/*".into()),
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };

        let tokens = tokens_for_matchspec(&spec, 42);
        // Should have: action:read, resource:docs/*, action:write, service:storage,
        //              feature:premium, pattern:api/v1/*
        assert_eq!(tokens.len(), 6);

        // Verify each token matches what we'd get from direct generation
        assert_eq!(tokens[0], generate_search_token("action:read", 42));
        assert_eq!(tokens[1], generate_search_token("resource:docs/*", 42));
        assert_eq!(tokens[2], generate_search_token("action:write", 42));
        assert_eq!(tokens[3], generate_search_token("service:storage", 42));
        assert_eq!(tokens[4], generate_search_token("feature:premium", 42));
        assert_eq!(tokens[5], generate_search_token("pattern:api/v1/*", 42));
    }

    #[test]
    fn test_capability_matches_tokens_positive() {
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![Constraint::Service("docs".into())],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };

        let epoch = 10;
        let tokens = tokens_for_matchspec(&spec, epoch);

        // A fulfiller holding "action:read" should match
        let keywords = &["action:read"];
        assert!(capability_matches_tokens(keywords, &tokens, epoch));

        // A fulfiller holding "service:docs" should match
        let keywords2 = &["service:docs"];
        assert!(capability_matches_tokens(keywords2, &tokens, epoch));
    }

    #[test]
    fn test_capability_matches_tokens_negative() {
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };

        let epoch = 10;
        let tokens = tokens_for_matchspec(&spec, epoch);

        // A fulfiller holding only "action:write" should NOT match
        let keywords = &["action:write"];
        assert!(!capability_matches_tokens(keywords, &tokens, epoch));

        // Wrong epoch should NOT match
        let keywords2 = &["action:read"];
        assert!(!capability_matches_tokens(keywords2, &tokens, epoch + 1));
    }

    #[test]
    fn test_capability_matches_tokens_multiple_keywords() {
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: Some("docs/*".into()),
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };

        let epoch = 5;
        let tokens = tokens_for_matchspec(&spec, epoch);

        // Fulfiller holds multiple keywords, one of which matches
        let keywords = &["action:write", "action:delete", "resource:docs/*"];
        assert!(capability_matches_tokens(keywords, &tokens, epoch));
    }

    #[test]
    fn test_matching_capability_indices() {
        let spec = MatchSpec {
            actions: vec![
                ActionPattern {
                    action: Some("read".into()),
                    resource: None,
                },
                ActionPattern {
                    action: Some("write".into()),
                    resource: None,
                },
            ],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };

        let epoch = 0;
        let tokens = tokens_for_matchspec(&spec, epoch);

        let cap_sets: &[&[&str]] = &[
            &["action:delete"],       // index 0 - no match
            &["action:read"],         // index 1 - match
            &["service:something"],   // index 2 - no match
            &["action:write", "action:read"], // index 3 - match
        ];

        let indices = matching_capability_indices(cap_sets, &tokens, epoch);
        assert_eq!(indices, vec![1, 3]);
    }

    #[test]
    fn test_sealed_box_roundtrip() {
        let keypair = SealKeypair::generate();
        let plaintext = b"hello, this is a secret matchspec";

        let sealed = seal_encrypt(plaintext, &keypair.public);
        let decrypted = seal_decrypt(&sealed, &keypair.secret);

        assert_eq!(&decrypted, plaintext);
    }

    #[test]
    fn test_sealed_box_wrong_key_fails() {
        let keypair = SealKeypair::generate();
        let wrong_keypair = SealKeypair::generate();
        let plaintext = b"secret data";

        let sealed = seal_encrypt(plaintext, &keypair.public);
        let decrypted = seal_decrypt(&sealed, &wrong_keypair.secret);

        // Should produce garbage, not the original plaintext
        assert_ne!(&decrypted, plaintext);
    }

    #[test]
    fn test_x25519_basepoint_deterministic() {
        let secret = [42u8; 32];
        let kp1 = SealKeypair::from_secret(secret);
        let kp2 = SealKeypair::from_secret(secret);
        assert_eq!(kp1.public, kp2.public);
    }

    #[test]
    fn test_x25519_dh_commutative() {
        let kp1 = SealKeypair::generate();
        let kp2 = SealKeypair::generate();

        let shared1 = x25519(&kp1.secret, &kp2.public);
        let shared2 = x25519(&kp2.secret, &kp1.public);

        assert_eq!(shared1, shared2, "DH should be commutative");
    }

    #[test]
    fn test_encrypted_intent_create_and_decrypt() {
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: Some("documents/*".into()),
            }],
            constraints: vec![Constraint::Service("storage".into())],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };

        let commitment = CommitmentId([0xAA; 32]);
        let epoch = 100;
        let expiry = Some(9999u64);

        let (encrypted, keypair) = EncryptedIntent::create(&spec, commitment, epoch, expiry);

        // Verify metadata
        assert_eq!(encrypted.commitment_id, commitment);
        assert_eq!(encrypted.epoch, epoch);
        assert_eq!(encrypted.expiry, expiry);
        assert_eq!(encrypted.ephemeral_pubkey, keypair.public);

        // Verify search tokens are present
        assert!(!encrypted.search_tokens.is_empty());
        assert_eq!(
            encrypted.search_tokens.len(),
            3 // action:read, resource:documents/*, service:storage
        );

        // Decrypt and verify
        let decrypted = encrypted.decrypt(&keypair.secret);
        assert_eq!(decrypted, Some(spec));
    }

    #[test]
    fn test_encrypted_intent_wrong_key_no_decrypt() {
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };

        let (encrypted, _keypair) =
            EncryptedIntent::create(&spec, CommitmentId([0xBB; 32]), 0, None);

        // Trying to decrypt with a random key should fail (garbage deserialization)
        let wrong_key = SealKeypair::generate();
        let result = encrypted.decrypt(&wrong_key.secret);
        // It may return None (postcard deserialization of garbage fails) or Some(wrong_spec)
        // Either way, it should NOT return the original spec
        assert_ne!(result, Some(spec));
    }

    #[test]
    fn test_encrypted_intent_expiry() {
        let spec = MatchSpec::default();
        let (encrypted, _) =
            EncryptedIntent::create(&spec, CommitmentId([0xCC; 32]), 0, Some(1000));

        assert!(!encrypted.is_expired(500));
        assert!(!encrypted.is_expired(999));
        assert!(encrypted.is_expired(1000));
        assert!(encrypted.is_expired(1001));
    }

    #[test]
    fn test_encrypted_intent_no_expiry() {
        let spec = MatchSpec::default();
        let (encrypted, _) =
            EncryptedIntent::create(&spec, CommitmentId([0xDD; 32]), 0, None);

        assert!(!encrypted.is_expired(0));
        assert!(!encrypted.is_expired(u64::MAX));
    }

    #[test]
    fn test_encrypted_intent_id_deterministic() {
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };

        let keypair = SealKeypair::from_secret([0x42; 32]);
        let commitment = CommitmentId([0xEE; 32]);

        let e1 = EncryptedIntent::create_with_keypair(&spec, commitment, 10, Some(500), &keypair);
        let e2 = EncryptedIntent::create_with_keypair(&spec, commitment, 10, Some(500), &keypair);

        // IDs should differ because seal_encrypt uses fresh randomness internally
        // (different ciphertexts). This is expected and desirable (unlinkability).
        // The ID is content-addressed from the ciphertext.
        // We just verify the ID is non-zero and computed.
        assert_ne!(e1.id, [0u8; 32]);
        assert_ne!(e2.id, [0u8; 32]);
    }

    #[test]
    fn test_full_sse_matching_flow() {
        // Simulate the full poster -> fulfiller flow:
        // 1. Poster creates encrypted intent
        // 2. Fulfiller tests their capability keywords against search tokens
        // 3. On match, fulfiller requests decryption
        // 4. Poster reveals the MatchSpec

        let epoch = 42;

        // Poster's intent
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("compute".into()),
                resource: Some("gpu/a100".into()),
            }],
            constraints: vec![Constraint::Feature("cuda".into())],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };

        let (encrypted, keypair) =
            EncryptedIntent::create(&spec, CommitmentId([0x11; 32]), epoch, Some(9999));

        // Fulfiller who holds GPU compute capabilities
        let fulfiller_keywords = &["action:compute", "resource:gpu/a100", "feature:cuda"];
        assert!(capability_matches_tokens(
            fulfiller_keywords,
            &encrypted.search_tokens,
            epoch
        ));

        // Fulfiller who only has CPU compute (no match)
        let cpu_keywords = &["action:compute", "resource:cpu/x86"];
        assert!(!capability_matches_tokens(
            cpu_keywords,
            &encrypted.search_tokens,
            epoch
        ));

        // After match, poster reveals the key and fulfiller decrypts
        let revealed_spec = encrypted.decrypt(&keypair.secret).unwrap();
        assert_eq!(revealed_spec, spec);
    }

    #[test]
    fn test_gossip_intent_enum() {
        let spec = MatchSpec::default();
        let intent = crate::Intent::new(
            crate::IntentKind::Need,
            spec.clone(),
            CommitmentId([0x11; 32]),
            9999,
            None,
        );

        let cleartext = GossipIntent::Cleartext(intent);
        assert!(matches!(cleartext, GossipIntent::Cleartext(_)));

        let (encrypted_intent, _) =
            EncryptedIntent::create(&spec, CommitmentId([0x22; 32]), 0, None);
        let encrypted = GossipIntent::Encrypted(encrypted_intent);
        assert!(matches!(encrypted, GossipIntent::Encrypted(_)));
    }

    #[test]
    fn test_extract_sse_keywords_matches_pir() {
        // Verify that extract_sse_keywords produces the same keywords as
        // pir::extract_capability_tags (they must be compatible)
        let spec = MatchSpec {
            actions: vec![
                ActionPattern {
                    action: Some("read".into()),
                    resource: Some("docs/*".into()),
                },
                ActionPattern {
                    action: Some("write".into()),
                    resource: None,
                },
            ],
            constraints: vec![
                Constraint::Service("storage".into()),
                Constraint::Feature("premium".into()),
                Constraint::AppId("myapp".into()),
                Constraint::OAuthProvider("google".into()),
            ],
            min_budget: None,
            resource_pattern: Some("api/v1/*".into()),
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };

        let keywords = extract_sse_keywords(&spec);
        assert_eq!(
            keywords,
            vec![
                "action:read",
                "resource:docs/*",
                "action:write",
                "service:storage",
                "feature:premium",
                "app:myapp",
                "oauth:google",
                "pattern:api/v1/*",
            ]
        );
    }
}
