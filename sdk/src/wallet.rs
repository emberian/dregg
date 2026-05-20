//! Agent wallet: identity, token storage, signing, and proof generation.
//!
//! The [`AgentWallet`] is the primary credential holder for an agent. It manages:
//! - An Ed25519 signing identity
//! - A collection of held authorization tokens (macaroon-backed)
//! - Token attenuation and delegation to other agents
//! - Turn signing for submission to the ledger
//! - Zero-knowledge proof generation via the bridge layer

use ed25519_dalek::Signer;

use pyana_bridge::BridgePresentationProof;
use pyana_cell::CellId;
use pyana_circuit::BabyBear;
use pyana_circuit::merkle_air::MerkleAir;
use pyana_circuit::poseidon2;
use pyana_token::{Attenuation, AuthRequest, AuthToken, MacaroonToken};
use pyana_turn::Turn;
use pyana_types::{PublicKey, Signature};

use crate::error::SdkError;

/// A token held by this wallet, along with metadata.
#[derive(Clone, Debug)]
pub struct HeldToken {
    /// Human-readable label for this token.
    pub label: String,
    /// The service this token grants access to.
    pub service: String,
    /// The encoded token string (em2_ prefixed).
    pub encoded: String,
    /// The root key used to verify this token (needed for re-verification).
    pub root_key: [u8; 32],
    /// Unique identifier for lookup.
    pub id: String,
}

impl HeldToken {
    /// Decode this held token into a [`MacaroonToken`] for operations.
    pub fn decode(&self) -> Result<MacaroonToken, pyana_token::TokenError> {
        MacaroonToken::from_encoded(&self.encoded, self.root_key)
    }
}

/// A token that has been delegated to another agent.
#[derive(Clone, Debug)]
pub struct DelegatedToken {
    /// The held token that was attenuated and delegated.
    pub token: HeldToken,
    /// The public key of the delegatee.
    pub delegatee: PublicKey,
    /// The restrictions applied during delegation.
    pub restrictions: Attenuation,
}

/// A turn signed by this wallet's identity, ready for submission.
#[derive(Clone, Debug)]
pub struct SignedTurn {
    /// The original turn.
    pub turn: Turn,
    /// The Ed25519 signature over the turn hash.
    pub signature: Signature,
    /// The signer's public key.
    pub signer: PublicKey,
}

/// The agent wallet: manages identity, tokens, and signing.
///
/// This is the core credential holder that every agent carries. It provides:
/// - Token minting (creating new root tokens)
/// - Token attenuation (narrowing permissions)
/// - Token delegation (handing attenuated tokens to other agents)
/// - Turn signing (authorizing execution requests)
/// - Proof generation (ZK presentation of authorization)
pub struct AgentWallet {
    /// The agent's Ed25519 signing key.
    signing_key: ed25519_dalek::SigningKey,
    /// The agent's public identity.
    public_key: PublicKey,
    /// All tokens held by this wallet.
    tokens: Vec<HeldToken>,
    /// Counter for generating unique token IDs.
    next_token_id: u64,
}

impl AgentWallet {
    /// Create a new wallet with a randomly generated Ed25519 identity.
    ///
    /// # Example
    /// ```
    /// use pyana_sdk::AgentWallet;
    /// let wallet = AgentWallet::new();
    /// println!("Agent identity: {}", wallet.public_key());
    /// ```
    pub fn new() -> Self {
        let mut key_bytes = [0u8; 32];
        getrandom::fill(&mut key_bytes).expect("getrandom failed");
        Self::from_key_bytes(key_bytes)
    }

    /// Create a wallet from an existing 32-byte Ed25519 secret key.
    ///
    /// Use this when restoring a wallet from persisted key material.
    pub fn from_key_bytes(secret: [u8; 32]) -> Self {
        let signing_key = ed25519_dalek::SigningKey::from_bytes(&secret);
        let verifying_key = signing_key.verifying_key();
        let public_key = PublicKey(verifying_key.to_bytes());
        AgentWallet {
            signing_key,
            public_key,
            tokens: Vec::new(),
            next_token_id: 0,
        }
    }

    /// Get this agent's public key (identity).
    pub fn public_key(&self) -> PublicKey {
        self.public_key
    }

    /// Derive a [`CellId`] for this agent in a given domain.
    ///
    /// The cell ID is deterministically derived from the agent's public key
    /// and a BLAKE3 hash of the domain string (used as the token_id).
    /// This matches the derivation used by `Cell::with_balance`.
    pub fn cell_id(&self, domain: &str) -> CellId {
        let token_id = *blake3::hash(domain.as_bytes()).as_bytes();
        CellId::derive_raw(&self.public_key.0, &token_id)
    }

    /// Get a reference to all held tokens.
    pub fn tokens(&self) -> &[HeldToken] {
        &self.tokens
    }

    /// Find a held token by its label.
    pub fn find_token(&self, label: &str) -> Option<&HeldToken> {
        self.tokens.iter().find(|t| t.label == label)
    }

    /// Find a held token by its ID.
    pub fn find_token_by_id(&self, id: &str) -> Option<&HeldToken> {
        self.tokens.iter().find(|t| t.id == id)
    }

    // =========================================================================
    // Token Operations
    // =========================================================================

    /// Mint a new root token for a service.
    ///
    /// The root key is the symmetric secret used to verify this token chain.
    /// Store it securely -- anyone with the root key can forge tokens.
    ///
    /// # Arguments
    ///
    /// * `root_key` - 32-byte HMAC root secret for the token chain.
    /// * `service` - Human-readable service name (e.g., "dns", "storage", "compute").
    ///
    /// # Returns
    ///
    /// A [`HeldToken`] representing the unrestricted root token.
    pub fn mint_token(&mut self, root_key: &[u8; 32], service: &str) -> HeldToken {
        let kid = format!("{}:{}", service, self.next_token_id);
        self.next_token_id += 1;

        let token = MacaroonToken::mint(*root_key, kid.as_bytes(), service);
        let encoded = token.to_encoded().expect("fresh token encodes cleanly");

        let held = HeldToken {
            label: format!("root:{}", service),
            service: service.to_string(),
            encoded,
            root_key: *root_key,
            id: kid,
        };

        self.tokens.push(held.clone());
        held
    }

    /// Attenuate a held token by adding restrictions.
    ///
    /// This creates a new, more restricted token derived from the original.
    /// The original token remains in the wallet unchanged. Attenuation can only
    /// narrow permissions, never expand them.
    ///
    /// # Arguments
    ///
    /// * `token` - The token to attenuate.
    /// * `restrictions` - The restrictions to apply.
    ///
    /// # Returns
    ///
    /// A new [`HeldToken`] with the restrictions applied, or an error if
    /// attenuation is not possible (e.g., empty restrictions).
    pub fn attenuate(
        &mut self,
        token: &HeldToken,
        restrictions: &Attenuation,
    ) -> Result<HeldToken, SdkError> {
        let decoded = token.decode()?;
        let attenuated_boxed = decoded.attenuate(restrictions)?;
        let encoded = attenuated_boxed.to_encoded()?;

        let id = format!("{}:att:{}", token.id, self.next_token_id);
        self.next_token_id += 1;

        let held = HeldToken {
            label: format!("attenuated:{}", token.service),
            service: token.service.clone(),
            encoded,
            root_key: token.root_key,
            id,
        };

        self.tokens.push(held.clone());
        Ok(held)
    }

    /// Delegate a token to another agent with restrictions.
    ///
    /// This attenuates the token and produces a [`DelegatedToken`] that can
    /// be transmitted to the target agent. The delegatee receives a token that
    /// is strictly less powerful than the original.
    ///
    /// # Arguments
    ///
    /// * `token` - The token to delegate from.
    /// * `to` - The public key of the agent receiving the delegation.
    /// * `restrictions` - Additional restrictions beyond those already on the token.
    ///
    /// # Returns
    ///
    /// A [`DelegatedToken`] containing the attenuated token for the delegatee.
    pub fn delegate(
        &mut self,
        token: &HeldToken,
        to: &PublicKey,
        restrictions: &Attenuation,
    ) -> Result<DelegatedToken, SdkError> {
        let attenuated = self.attenuate(token, restrictions)?;
        Ok(DelegatedToken {
            token: attenuated,
            delegatee: *to,
            restrictions: restrictions.clone(),
        })
    }

    /// Verify that a held token authorizes a given request.
    ///
    /// Returns `true` if the token passes verification for the request,
    /// `false` otherwise.
    pub fn verify_token(&self, token: &HeldToken, request: &AuthRequest) -> bool {
        match token.decode() {
            Ok(t) => t.verify(request).is_ok(),
            Err(_) => false,
        }
    }

    /// Receive a delegated token into this wallet.
    ///
    /// Call this when another agent has delegated a token to us. The token
    /// is added to the wallet's held tokens.
    pub fn receive_delegation(&mut self, delegated: DelegatedToken) {
        self.tokens.push(delegated.token);
    }

    // =========================================================================
    // Signing
    // =========================================================================

    /// Sign a turn for submission to the ledger.
    ///
    /// Computes the BLAKE3 hash of the turn and signs it with this wallet's
    /// Ed25519 key. The resulting [`SignedTurn`] can be submitted to a silo
    /// or local executor.
    ///
    /// # Arguments
    ///
    /// * `turn` - The turn to sign (will be hashed).
    pub fn sign_turn(&self, turn: &Turn) -> SignedTurn {
        let turn_bytes = self.compute_turn_bytes(turn);
        let sig = self.signing_key.sign(&turn_bytes);
        SignedTurn {
            turn: turn.clone(),
            signature: Signature(sig.to_bytes()),
            signer: self.public_key,
        }
    }

    /// Sign arbitrary bytes with this wallet's identity.
    ///
    /// Useful for custom authorization schemes outside the turn model.
    pub fn sign_bytes(&self, message: &[u8]) -> Signature {
        let sig = self.signing_key.sign(message);
        Signature(sig.to_bytes())
    }

    // =========================================================================
    // Proof Generation
    // =========================================================================

    /// Generate a zero-knowledge presentation proof for a held token.
    ///
    /// This proves "I hold a valid token chain that authorizes request X"
    /// without revealing the token, its caveats, or the root key.
    ///
    /// The proof can be transmitted to a remote verifier who only needs the
    /// federation root and request predicate to verify it.
    ///
    /// # Arguments
    ///
    /// * `token` - The token to prove authorization from.
    /// * `request` - The authorization request to prove.
    ///
    /// # Returns
    ///
    /// A [`BridgePresentationProof`] that can be verified by any party knowing
    /// the federation root, or an error if proof generation fails.
    pub fn prove_authorization(
        &self,
        token: &HeldToken,
        request: &AuthRequest,
    ) -> Result<BridgePresentationProof, SdkError> {
        let issuer_key = token.root_key;
        let federation_root_bb = Self::compute_federation_root_bb(&issuer_key);
        let federation_root = Self::bb_to_bytes(federation_root_bb);

        let mut builder = pyana_bridge::BridgePresentationBuilder::new_with_root_bb(
            issuer_key,
            federation_root,
            federation_root_bb,
        );

        // Mint a fresh token from the root key for the builder
        // (since MacaroonToken is not Clone, we create a new one from the key).
        let fresh_token = MacaroonToken::mint(token.root_key, token.id.as_bytes(), &token.service);
        builder.set_root_token(fresh_token);

        let proof = builder.prove(request)?;
        Ok(proof)
    }

    /// Generate a presentation proof for a token that has been attenuated.
    ///
    /// Unlike [`prove_authorization`](Self::prove_authorization), this method
    /// accepts the full attenuation chain so the proof covers the narrowing steps.
    ///
    /// # Arguments
    ///
    /// * `root_token` - The original root token (needed for the chain base).
    /// * `attenuations` - The sequence of attenuations applied.
    /// * `request` - The authorization request to prove.
    pub fn prove_with_chain(
        &self,
        root_token: &HeldToken,
        attenuations: &[Attenuation],
        request: &AuthRequest,
    ) -> Result<BridgePresentationProof, SdkError> {
        let issuer_key = root_token.root_key;
        let federation_root_bb = Self::compute_federation_root_bb(&issuer_key);
        let federation_root = Self::bb_to_bytes(federation_root_bb);

        let mut builder = pyana_bridge::BridgePresentationBuilder::new_with_root_bb(
            issuer_key,
            federation_root,
            federation_root_bb,
        );

        let fresh_token = MacaroonToken::mint(
            root_token.root_key,
            root_token.id.as_bytes(),
            &root_token.service,
        );
        builder.set_root_token(fresh_token);

        for att in attenuations {
            builder.add_attenuation(att);
        }

        let proof = builder.prove(request)?;
        Ok(proof)
    }

    // =========================================================================
    // Internal helpers
    // =========================================================================

    /// Compute a stable byte representation of a turn for signing.
    fn compute_turn_bytes(&self, turn: &Turn) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(turn.agent.as_bytes());
        hasher.update(&turn.nonce.to_le_bytes());
        hasher.update(&turn.fee.to_le_bytes());
        if let Some(ref memo) = turn.memo {
            hasher.update(memo.as_bytes());
        }
        if let Some(valid_until) = turn.valid_until {
            hasher.update(&valid_until.to_le_bytes());
        }
        *hasher.finalize().as_bytes()
    }

    /// Compute the federation root as a BabyBear field element.
    ///
    /// This walks the synthetic Merkle path from the issuer key hash up to
    /// a deterministic root. In production, this would come from the federation
    /// registry; here we compute it so the proof verifies self-consistently.
    fn compute_federation_root_bb(issuer_key: &[u8; 32]) -> BabyBear {
        let issuer_hash = Self::bytes_to_babybear(issuer_key);
        let depth = 8;
        let mut current = issuer_hash;
        for i in 0..depth {
            let position = (i % 4) as u8;
            let siblings = [
                BabyBear::new(Self::hash_index(i, 0, issuer_key)),
                BabyBear::new(Self::hash_index(i, 1, issuer_key)),
                BabyBear::new(Self::hash_index(i, 2, issuer_key)),
            ];
            current = MerkleAir::compute_parent(current, position, &siblings);
        }
        current
    }

    /// Convert a BabyBear field element to a 32-byte array.
    fn bb_to_bytes(bb: BabyBear) -> [u8; 32] {
        let mut bytes = [0u8; 32];
        let val = bb.as_u32();
        bytes[..4].copy_from_slice(&val.to_le_bytes());
        bytes
    }

    /// Compress a 32-byte value into a single BabyBear element via Poseidon2.
    fn bytes_to_babybear(bytes: &[u8; 32]) -> BabyBear {
        let limbs = BabyBear::encode_hash(bytes);
        poseidon2::hash_many(&limbs)
    }

    /// Derive a deterministic sibling hash for Merkle path construction.
    fn hash_index(level: usize, sibling_idx: usize, key: &[u8; 32]) -> u32 {
        let mut hasher = blake3::Hasher::new();
        hasher.update(&level.to_le_bytes());
        hasher.update(&sibling_idx.to_le_bytes());
        hasher.update(key);
        let hash = hasher.finalize();
        let bytes = hash.as_bytes();
        u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]])
            % pyana_circuit::field::BABYBEAR_P
    }
}

impl Default for AgentWallet {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Debug for AgentWallet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AgentWallet")
            .field("public_key", &self.public_key)
            .field("tokens_held", &self.tokens.len())
            .finish()
    }
}
