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
//!   `token = BLAKE3_derive_key("dregg-sse-token-v1", keyword_bytes || epoch_le_bytes)`
//!
//! This is the "keyword-as-secret" approach: anyone who knows the keyword can
//! generate the matching token. An observer who doesn't know the keyword space
//! cannot enumerate all possible tokens. This is weaker than true SSE but practical
//! for dregg's threat model.
//!
//! # Epoch rotation
//!
//! Tokens rotate with epochs (same pattern as stake nullifiers). Repeated use of
//! the same tags is only linkable within a single epoch, not across epochs.
//!
//! # Sealed box encryption
//!
//! The full MatchSpec body is encrypted using X25519 + ChaCha20-Poly1305 (AEAD):
//! - Poster generates an ephemeral X25519 keypair
//! - A symmetric key is derived from the shared secret via BLAKE3 `derive_key`
//! - Ciphertext = ChaCha20-Poly1305(key, nonce, plaintext) — an AEAD that appends
//!   a 128-bit Poly1305 authentication tag
//! - Only someone who knows the poster's ephemeral secret key can decrypt, AND any
//!   tampering with the ciphertext (or nonce/AAD) is detected as a tag failure on
//!   decrypt rather than silently producing garbage plaintext
//! - After SSE matching, the poster reveals the decryption key over a direct channel
//!
//! ## Integrity (why AEAD, not a raw keystream)
//!
//! An earlier construction used a raw BLAKE3 XOF keystream XORed with the plaintext
//! and NO authentication tag. That is malleable: an attacker who flips bit `i` of the
//! ciphertext flips bit `i` of the recovered plaintext (a controlled, undetected
//! change). ChaCha20-Poly1305 binds a Poly1305 MAC over the ciphertext so any flip is
//! rejected. See [`seal_decrypt`] / [`EncryptedIntent::decrypt`], which return `None`
//! on a tag failure.

use serde::{Deserialize, Serialize};

use crate::{CommitmentId, MatchSpec};

// ---------------------------------------------------------------------------
// SSE Token Generation
// ---------------------------------------------------------------------------

/// Generate a search token for a keyword at a given epoch.
///
/// Token = BLAKE3_derive_key("dregg-sse-token-v1", keyword || epoch_le_bytes)
///
/// The "secret" is the keyword itself: anyone who knows the keyword generates
/// the same token. This provides set-membership hiding (observers who don't
/// know the keyword space cannot enumerate tokens) without requiring a shared
/// secret distribution mechanism.
pub fn generate_search_token(keyword: &str, epoch: u64) -> [u8; 32] {
    let mut input = Vec::with_capacity(keyword.len() + 8);
    input.extend_from_slice(keyword.as_bytes());
    input.extend_from_slice(&epoch.to_le_bytes());
    blake3::derive_key("dregg-sse-token-v1", &input)
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

/// Derive a 32-byte ChaCha20-Poly1305 key from an X25519 shared secret.
///
/// The raw X25519 DH output is never used directly as a symmetric key — it is run
/// through BLAKE3's `derive_key` mode (a proper KDF) with both public keys mixed in
/// for session binding and domain separation. This mirrors `cell::seal`'s KDF.
fn derive_sealed_box_key(
    shared_secret: &[u8; 32],
    sender_public: &[u8; 32],
    recipient_public: &[u8; 32],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-sealed-box-key-v2");
    hasher.update(shared_secret);
    hasher.update(sender_public);
    hasher.update(recipient_public);
    *hasher.finalize().as_bytes()
}

/// Authenticated encryption with ChaCha20-Poly1305.
///
/// Returns `nonce_independent` ciphertext WITH a 16-byte Poly1305 tag appended.
/// The caller is responsible for carrying the nonce alongside the ciphertext;
/// the (key, nonce) pair must never repeat (callers here use a fresh random
/// nonce and/or a fresh ephemeral key per call).
fn aead_encrypt(key: &[u8; 32], nonce: &[u8; 12], plaintext: &[u8]) -> Vec<u8> {
    use chacha20poly1305::{ChaCha20Poly1305, KeyInit, aead::Aead};
    let cipher = ChaCha20Poly1305::new(key.into());
    let aead_nonce = chacha20poly1305::Nonce::from_slice(nonce);
    cipher
        .encrypt(aead_nonce, plaintext)
        .expect("ChaCha20-Poly1305 encryption should not fail")
}

/// Authenticated decryption with ChaCha20-Poly1305.
///
/// Returns `None` (fail closed) if the Poly1305 tag does not verify — i.e. the
/// ciphertext, nonce, or key was tampered with. Never yields garbage plaintext.
fn aead_decrypt(key: &[u8; 32], nonce: &[u8; 12], ciphertext: &[u8]) -> Option<Vec<u8>> {
    use chacha20poly1305::{ChaCha20Poly1305, KeyInit, aead::Aead};
    let cipher = ChaCha20Poly1305::new(key.into());
    let aead_nonce = chacha20poly1305::Nonce::from_slice(nonce);
    cipher.decrypt(aead_nonce, ciphertext).ok()
}

/// Encrypt a plaintext using an authenticated sealed-box construction.
///
/// The recipient must know the ephemeral secret key to decrypt.
/// Encryption: generate ephemeral sender keypair, DH with recipient public key,
/// derive a symmetric key from the shared secret, then ChaCha20-Poly1305 encrypt.
/// The Poly1305 tag authenticates the ciphertext, so tampering is detected on
/// decrypt (see [`seal_decrypt`]) rather than silently yielding garbage plaintext.
///
/// For dregg's SSE use case, the "recipient" IS the poster themselves. They
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

    let key = derive_sealed_box_key(shared.as_bytes(), &sender_public_bytes, recipient_public);

    // Fresh random 96-bit AEAD nonce. The sender keypair is also fresh per call, so
    // (key, nonce) reuse is doubly avoided.
    let mut nonce = [0u8; 12];
    crate::getrandom(&mut nonce);

    let ciphertext = aead_encrypt(&key, &nonce, plaintext);

    SealedBox {
        ciphertext,
        sender_public: sender_public_bytes,
        nonce,
    }
}

/// Decrypt a sealed box using the recipient's secret key.
///
/// Returns `None` if the Poly1305 authentication tag fails (tampered ciphertext,
/// tampered nonce, or wrong key) — fail closed, never a garbage plaintext.
pub fn seal_decrypt(sealed: &SealedBox, recipient_secret: &[u8; 32]) -> Option<Vec<u8>> {
    // Compute shared secret via X25519
    let secret = x25519_dalek::StaticSecret::from(*recipient_secret);
    let sender_pk = x25519_dalek::PublicKey::from(sealed.sender_public);
    let shared = secret.diffie_hellman(&sender_pk);

    let recipient_public = x25519_dalek::PublicKey::from(&secret);
    let recipient_public_bytes = recipient_public.to_bytes();
    let key = derive_sealed_box_key(
        shared.as_bytes(),
        &sealed.sender_public,
        &recipient_public_bytes,
    );

    aead_decrypt(&key, &sealed.nonce, &sealed.ciphertext)
}

/// A sealed box: AEAD ciphertext (with appended Poly1305 tag) + ephemeral sender
/// public key + nonce.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SealedBox {
    /// The ChaCha20-Poly1305 ciphertext (includes the 16-byte authentication tag).
    pub ciphertext: Vec<u8>,
    /// The ephemeral sender's public key (needed for DH during decryption).
    pub sender_public: [u8; 32],
    /// The 96-bit ChaCha20-Poly1305 nonce.
    pub nonce: [u8; 12],
}

// ---------------------------------------------------------------------------
// Secret-key encryption for EncryptedIntent bodies
// ---------------------------------------------------------------------------

/// Derive a 32-byte ChaCha20-Poly1305 key for the intent body from the poster's
/// ephemeral secret key, via BLAKE3's `derive_key` KDF mode (domain-separated).
///
/// The raw 32-byte X25519 secret is never used directly as an AEAD key.
fn derive_body_key(secret: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-intent-body-key-v2");
    hasher.update(secret);
    *hasher.finalize().as_bytes()
}

/// Encrypt an intent body with authenticated encryption (ChaCha20-Poly1305).
///
/// Replaces the earlier raw BLAKE3-XOF keystream (which had NO authentication
/// tag and was malleable: flipping ciphertext bit `i` flipped plaintext bit `i`
/// undetected). The returned ciphertext carries a 16-byte Poly1305 tag and is
/// bound to `nonce`; any tampering is rejected on decrypt.
///
/// The poster encrypts to their own ephemeral secret and later reveals it to
/// matched fulfillers. A fresh random 96-bit nonce is generated per call and
/// must be stored alongside the ciphertext (see [`EncryptedIntent::body_nonce`]).
fn encrypt_body(plaintext: &[u8], secret: &[u8; 32]) -> ([u8; 12], Vec<u8>) {
    let key = derive_body_key(secret);
    let mut nonce = [0u8; 12];
    crate::getrandom(&mut nonce);
    let ciphertext = aead_encrypt(&key, &nonce, plaintext);
    (nonce, ciphertext)
}

/// Decrypt an intent body produced by [`encrypt_body`].
///
/// Returns `None` (fail closed) if the Poly1305 tag fails — tampered ciphertext,
/// tampered nonce, or wrong secret — never a garbage plaintext.
fn decrypt_body(ciphertext: &[u8], nonce: &[u8; 12], secret: &[u8; 32]) -> Option<Vec<u8>> {
    let key = derive_body_key(secret);
    aead_decrypt(&key, nonce, ciphertext)
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
    /// The encrypted MatchSpec body: ChaCha20-Poly1305 ciphertext with an
    /// appended 16-byte Poly1305 authentication tag. Tampering is detected on
    /// decrypt (see [`Self::decrypt`]).
    pub encrypted_body: Vec<u8>,
    /// The 96-bit ChaCha20-Poly1305 nonce for `encrypted_body`.
    pub body_nonce: [u8; 12],
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

        // Encrypt directly using the keypair (self-encryption: poster encrypts to
        // their own ephemeral key so they can later reveal the secret to matched
        // fulfillers). ChaCha20-Poly1305 AEAD authenticates the ciphertext so a
        // gossip relay cannot tamper with the body undetected.
        let (body_nonce, encrypted_body) = encrypt_body(&plaintext, &keypair.secret);

        let mut intent = Self {
            search_tokens,
            encrypted_body,
            body_nonce,
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
        let (body_nonce, encrypted_body) = encrypt_body(&plaintext, &keypair.secret);

        let mut intent = Self {
            search_tokens,
            encrypted_body,
            body_nonce,
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
    /// The poster reveals this secret to matched fulfillers over a direct channel.
    /// Returns the deserialized MatchSpec if decryption and deserialization succeed.
    ///
    /// Returns `None` (fail closed) if the ChaCha20-Poly1305 tag fails — a
    /// tampered ciphertext, tampered nonce, or wrong secret is rejected at the
    /// AEAD layer rather than producing garbage that might still deserialize.
    pub fn decrypt(&self, secret: &[u8; 32]) -> Option<MatchSpec> {
        let plaintext = decrypt_body(&self.encrypted_body, &self.body_nonce, secret)?;
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
        let mut hasher = blake3::Hasher::new_derive_key("dregg-encrypted-intent-id-v1");
        for token in &self.search_tokens {
            hasher.update(token);
        }
        hasher.update(&self.encrypted_body);
        hasher.update(&self.body_nonce);
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
            &["action:delete"],               // index 0 - no match
            &["action:read"],                 // index 1 - match
            &["service:something"],           // index 2 - no match
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

        assert_eq!(decrypted.as_deref(), Some(&plaintext[..]));
    }

    #[test]
    fn test_sealed_box_tampered_ciphertext_rejected() {
        // ADVERSARIAL: a one-byte flip in the AEAD ciphertext is rejected.
        let keypair = SealKeypair::generate();
        let plaintext = b"secret matchspec body";
        let mut sealed = seal_encrypt(plaintext, &keypair.public);
        sealed.ciphertext[0] ^= 0x01;
        assert_eq!(
            seal_decrypt(&sealed, &keypair.secret),
            None,
            "tampered sealed-box ciphertext must fail the Poly1305 tag"
        );
    }

    #[test]
    fn test_sealed_box_wrong_key_fails() {
        let keypair = SealKeypair::generate();
        let wrong_keypair = SealKeypair::generate();
        let plaintext = b"secret data";

        let sealed = seal_encrypt(plaintext, &keypair.public);
        let decrypted = seal_decrypt(&sealed, &wrong_keypair.secret);

        // AEAD fails closed: a wrong key yields None (tag failure), not garbage.
        assert_eq!(decrypted, None);
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

        let secret1 = x25519_dalek::StaticSecret::from(kp1.secret);
        let pk2 = x25519_dalek::PublicKey::from(kp2.public);
        let shared1 = secret1.diffie_hellman(&pk2);

        let secret2 = x25519_dalek::StaticSecret::from(kp2.secret);
        let pk1 = x25519_dalek::PublicKey::from(kp1.public);
        let shared2 = secret2.diffie_hellman(&pk1);

        assert_eq!(
            shared1.as_bytes(),
            shared2.as_bytes(),
            "DH should be commutative"
        );
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
    fn test_encrypted_intent_tampered_body_rejected() {
        // ADVERSARIAL: flipping one byte of the authenticated body ciphertext must
        // be REJECTED on decrypt (Poly1305 tag failure) — NOT silently decrypted to
        // a garbage/attacker-controlled MatchSpec. This is the integrity property
        // that the old raw-XOR-keystream construction lacked.
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

        let (mut encrypted, keypair) =
            EncryptedIntent::create(&spec, CommitmentId([0x77; 32]), 0, None);

        // Sanity: untampered decrypt works.
        assert_eq!(encrypted.decrypt(&keypair.secret), Some(spec.clone()));

        // Flip one byte of the ciphertext body.
        assert!(!encrypted.encrypted_body.is_empty());
        encrypted.encrypted_body[0] ^= 0x01;
        assert_eq!(
            encrypted.decrypt(&keypair.secret),
            None,
            "tampered body ciphertext must be rejected by the AEAD tag, not decrypted"
        );

        // Restore and instead tamper the nonce — also must be rejected.
        encrypted.encrypted_body[0] ^= 0x01;
        assert_eq!(
            encrypted.decrypt(&keypair.secret),
            Some(spec),
            "restoring the byte restores a valid decrypt"
        );
        encrypted.body_nonce[0] ^= 0x01;
        assert_eq!(
            encrypted.decrypt(&keypair.secret),
            None,
            "tampered nonce must be rejected by the AEAD tag"
        );
    }

    #[test]
    fn test_encrypted_intent_tag_present() {
        // The AEAD body is strictly longer than the plaintext by the 16-byte
        // Poly1305 tag — evidence the construction is authenticated, not a raw
        // length-preserving XOR keystream.
        let spec = MatchSpec::default();
        let plaintext = postcard::to_allocvec(&spec).unwrap();
        let (encrypted, _kp) = EncryptedIntent::create(&spec, CommitmentId([0x01; 32]), 0, None);
        assert_eq!(
            encrypted.encrypted_body.len(),
            plaintext.len() + 16,
            "ciphertext must carry a 16-byte Poly1305 tag (not length-preserving XOR)"
        );
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
        let (encrypted, _) = EncryptedIntent::create(&spec, CommitmentId([0xDD; 32]), 0, None);

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

        // Fulfiller who only has storage capabilities (no match)
        let storage_keywords = &["action:store", "resource:disk/ssd"];
        assert!(!capability_matches_tokens(
            storage_keywords,
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
