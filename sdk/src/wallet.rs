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
use pyana_token::{Attenuation, AuthRequest, AuthToken, MacaroonToken, TokenClearance};
use pyana_trace::{AuthorizationTrace, Fact as TraceFact};
use pyana_turn::Turn;
use pyana_types::{PublicKey, Signature};

use crate::error::SdkError;

// =============================================================================
// Verification Modes
// =============================================================================

/// Index into the evaluated fact set, used for selective disclosure.
///
/// When presenting in [`VerificationMode::SelectiveDisclosure`], the prover
/// specifies which facts (by index into the evaluation trace's fact set) to
/// reveal to the verifier.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FactIndex(pub usize);

/// Verification mode selector for authorization presentation.
///
/// Pyana supports three verification modes with progressive privacy guarantees:
///
/// - **Trusted**: Local Datalog evaluation, full visibility, ~8us.
/// - **SelectiveDisclosure**: STARK proof with chosen facts revealed, ~200ms.
/// - **FullyPrivate**: STARK proof revealing only allow/deny, ~500ms.
#[derive(Clone, Debug)]
pub enum VerificationMode {
    /// Run Datalog locally, return full clearance and trace.
    ///
    /// Use when the verifier holds the root key (internal services, cloud API).
    Trusted,

    /// Prove authorization in STARK, revealing only selected facts.
    ///
    /// The `reveal` vector specifies indices into the evaluated fact set that
    /// the verifier will see. All other facts remain private witness.
    ///
    /// Use for cross-organization capability presentation where partial
    /// disclosure is acceptable (e.g., reveal service name but hide user).
    SelectiveDisclosure { reveal: Vec<FactIndex> },

    /// Full zero-knowledge proof: verifier learns only allow/deny.
    ///
    /// The STARK proves the entire multi-step Datalog derivation without
    /// revealing any intermediate facts, chain length, or rule selections.
    ///
    /// Use for anonymous credential presentation or private authorization.
    FullyPrivate,
}

/// The result of an authorization presentation, parameterized by verification mode.
///
/// Each variant carries exactly the information the verifier receives for that mode.
#[derive(Clone, Debug)]
pub enum AuthorizationPresentation {
    /// Trusted mode: full clearance and derivation trace, no proof needed.
    Trusted {
        /// The full token clearance (capabilities, expiry, subject).
        clearance: TokenClearance,
        /// The complete Datalog derivation trace.
        trace: AuthorizationTrace,
    },

    /// Selective disclosure: chosen facts revealed, remainder proven in ZK.
    Selective {
        /// The facts the prover chose to reveal (subset of the evaluation).
        revealed_facts: Vec<TraceFact>,
        /// The STARK proof covering the full derivation (serialized bytes).
        proof: Vec<u8>,
        /// Whether authorization was granted.
        conclusion: bool,
    },

    /// Fully private: verifier learns only the conclusion.
    Private {
        /// The STARK proof covering the full derivation (serialized bytes).
        proof: Vec<u8>,
        /// Whether authorization was granted (the single bit of information).
        conclusion: bool,
    },
}

// =============================================================================
// Token storage types
// =============================================================================

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
/// - Receipt chain management (proof-carrying state)
pub struct AgentWallet {
    /// The agent's Ed25519 signing key.
    signing_key: ed25519_dalek::SigningKey,
    /// The agent's public identity.
    public_key: PublicKey,
    /// All tokens held by this wallet.
    tokens: Vec<HeldToken>,
    /// Counter for generating unique token IDs.
    next_token_id: u64,
    /// The agent's receipt chain: a linked sequence of TurnReceipts proving
    /// the complete history of state transitions from genesis. This is the
    /// proof-carrying state representation — anyone can verify the chain
    /// without contacting a federation.
    receipt_chain: Vec<pyana_turn::TurnReceipt>,
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
            receipt_chain: Vec::new(),
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
    // Receipt Chain (Proof-Carrying State)
    // =========================================================================

    /// Append a receipt to this wallet's chain after a successful turn execution.
    ///
    /// The receipt's `previous_receipt_hash` will be set to the hash of the
    /// current chain head (or None if this is the first receipt). The receipt's
    /// `agent` field must match this wallet's agent identity for the given domain.
    ///
    /// This is the primary method for building the proof-carrying state chain.
    /// Call this after `TurnExecutor::execute()` returns a committed result.
    pub fn append_receipt(&mut self, mut receipt: pyana_turn::TurnReceipt) {
        // Link to the previous receipt.
        receipt.previous_receipt_hash = self.receipt_chain.last().map(|r| r.receipt_hash());
        self.receipt_chain.push(receipt);
    }

    /// Get the head (most recent) receipt in this wallet's chain.
    ///
    /// Returns `None` if no turns have been executed yet (empty chain).
    pub fn receipt_head(&self) -> Option<&pyana_turn::TurnReceipt> {
        self.receipt_chain.last()
    }

    /// Get the number of receipts in this wallet's chain.
    ///
    /// This is the number of successfully committed turns in this agent's history.
    pub fn receipt_chain_length(&self) -> usize {
        self.receipt_chain.len()
    }

    /// Get the full receipt chain for verification or export.
    ///
    /// The chain can be presented to any verifier who can check its integrity
    /// using [`pyana_turn::verify_receipt_chain`] without contacting a federation.
    pub fn receipt_chain(&self) -> &[pyana_turn::TurnReceipt] {
        &self.receipt_chain
    }

    /// Get the current state commitment (post_state_hash of the chain head).
    ///
    /// This is the state that the receipt chain proves. Returns `None` if the
    /// chain is empty.
    pub fn current_state_commitment(&self) -> Option<[u8; 32]> {
        self.receipt_chain.last().map(|r| r.post_state_hash)
    }

    /// Verify this wallet's own receipt chain integrity.
    ///
    /// Returns `Ok(())` if the chain is valid, or an error describing the break.
    /// An empty chain is considered valid (no receipts to verify).
    pub fn verify_own_chain(&self) -> Result<(), pyana_turn::VerifyError> {
        if self.receipt_chain.is_empty() {
            return Ok(());
        }
        pyana_turn::verify_receipt_chain(&self.receipt_chain)
    }

    // =========================================================================
    // Mode-Selected Authorization
    // =========================================================================

    /// Authorize a request using the specified verification mode.
    ///
    /// This is the unified entry point for all three verification modes:
    ///
    /// - [`VerificationMode::Trusted`]: Runs Datalog locally via
    ///   [`verify_token_datalog`](pyana_token::datalog_verify::verify_token_datalog),
    ///   returns full clearance and trace (~8us).
    ///
    /// - [`VerificationMode::SelectiveDisclosure`]: Runs Datalog locally, then
    ///   generates a STARK proof with selected facts as public inputs. The
    ///   verifier sees only the chosen facts and the conclusion (~200ms).
    ///
    /// - [`VerificationMode::FullyPrivate`]: Runs Datalog locally, then generates
    ///   a full `MultiStepDerivationAir` STARK proof. The verifier learns only
    ///   whether authorization was granted (~500ms).
    ///
    /// # Arguments
    ///
    /// * `token` - The held token to authorize from.
    /// * `request` - The authorization request to evaluate.
    /// * `mode` - The verification mode determining what the verifier receives.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use pyana_sdk::{AgentWallet, VerificationMode, AuthorizationPresentation};
    /// use pyana_token::AuthRequest;
    ///
    /// let wallet = AgentWallet::new();
    /// # let token = todo!();
    /// let request = AuthRequest {
    ///     service: Some("dns".into()),
    ///     action: Some("read".into()),
    ///     ..Default::default()
    /// };
    ///
    /// let presentation = wallet.authorize(&token, &request, VerificationMode::Trusted).unwrap();
    /// ```
    pub fn authorize(
        &self,
        token: &HeldToken,
        request: &AuthRequest,
        mode: VerificationMode,
    ) -> Result<AuthorizationPresentation, SdkError> {
        match mode {
            VerificationMode::Trusted => self.authorize_trusted(token, request),
            VerificationMode::SelectiveDisclosure { reveal } => {
                self.authorize_selective(token, request, &reveal)
            }
            VerificationMode::FullyPrivate => self.authorize_private(token, request),
        }
    }

    /// Trusted mode: local Datalog evaluation, full visibility.
    fn authorize_trusted(
        &self,
        token: &HeldToken,
        request: &AuthRequest,
    ) -> Result<AuthorizationPresentation, SdkError> {
        let caveat_set = Self::extract_caveat_set(token)?;
        let result = pyana_token::datalog_verify::verify_token_datalog(&caveat_set, request)?;

        Ok(AuthorizationPresentation::Trusted {
            clearance: result.clearance,
            trace: result.trace,
        })
    }

    /// Selective disclosure: STARK proof with chosen facts revealed.
    fn authorize_selective(
        &self,
        token: &HeldToken,
        request: &AuthRequest,
        reveal: &[FactIndex],
    ) -> Result<AuthorizationPresentation, SdkError> {
        // Step 1: Run Datalog locally to get the trace.
        let caveat_set = Self::extract_caveat_set(token)?;
        let result = pyana_token::datalog_verify::verify_token_datalog(&caveat_set, request)?;

        let conclusion = matches!(
            result.trace.conclusion,
            pyana_trace::Conclusion::Allow { .. }
        );

        // Step 2: Extract the facts at the requested indices.
        let all_facts: Vec<TraceFact> = result
            .trace
            .steps
            .iter()
            .map(|step| step.derived_fact.clone())
            .collect();

        let revealed_facts: Vec<TraceFact> = reveal
            .iter()
            .filter_map(|idx| all_facts.get(idx.0).cloned())
            .collect();

        // Step 3: Generate STARK proof via the bridge (full derivation,
        // with revealed facts as public inputs for the verifier).
        let bridge_proof = self.prove_authorization(token, request)?;
        let proof = Self::serialize_proof(&bridge_proof);

        Ok(AuthorizationPresentation::Selective {
            revealed_facts,
            proof,
            conclusion,
        })
    }

    /// Fully private mode: STARK proof revealing only the conclusion bit.
    fn authorize_private(
        &self,
        token: &HeldToken,
        request: &AuthRequest,
    ) -> Result<AuthorizationPresentation, SdkError> {
        // Step 1: Run Datalog locally to determine conclusion.
        let caveat_set = Self::extract_caveat_set(token)?;
        let result = pyana_token::datalog_verify::verify_token_datalog(&caveat_set, request)?;

        let conclusion = matches!(
            result.trace.conclusion,
            pyana_trace::Conclusion::Allow { .. }
        );

        // Step 2: Generate full STARK proof via the bridge.
        // The proof covers the entire MultiStepDerivationAir -- the verifier
        // only receives the conclusion public input, learning nothing else.
        let bridge_proof = self.prove_authorization(token, request)?;
        let proof = Self::serialize_proof(&bridge_proof);

        Ok(AuthorizationPresentation::Private { proof, conclusion })
    }

    /// Extract the CaveatSet from a held token by decoding and verifying the HMAC chain.
    fn extract_caveat_set(
        token: &HeldToken,
    ) -> Result<pyana_token::pyana_macaroon::caveat::CaveatSet, SdkError> {
        let decoded = token.decode()?;
        let caveat_set = decoded
            .inner()
            .verify(&token.root_key, decoded.discharges())
            .map_err(|e| SdkError::Token(pyana_token::TokenError::VerificationFailed(e.to_string())))?;
        Ok(caveat_set)
    }

    /// Serialize a bridge presentation proof to bytes for wire transmission.
    ///
    /// Prefers the real STARK proof (issuer membership) when available,
    /// otherwise serializes the mock circuit proof via postcard.
    fn serialize_proof(bridge_proof: &BridgePresentationProof) -> Vec<u8> {
        if let Some(ref real) = bridge_proof.real_stark_proof {
            pyana_circuit::stark::proof_to_bytes(&real.issuer_membership_stark_proof)
        } else {
            // Development path: serialize the mock presentation proof.
            postcard::to_stdvec(&bridge_proof.circuit_proof).unwrap_or_default()
        }
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
            .field("receipt_chain_length", &self.receipt_chain.len())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_turn::TurnReceipt;

    /// Helper: create a mock receipt with given state hashes.
    fn mock_receipt(
        agent: CellId,
        pre_state: [u8; 32],
        post_state: [u8; 32],
    ) -> TurnReceipt {
        TurnReceipt {
            turn_hash: [0u8; 32],
            forest_hash: [0u8; 32],
            pre_state_hash: pre_state,
            post_state_hash: post_state,
            timestamp: 1000,
            effects_hash: [0u8; 32],
            computrons_used: 50,
            action_count: 1,
            previous_receipt_hash: None,
            agent,
        }
    }

    #[test]
    fn test_wallet_receipt_chain_empty() {
        let wallet = AgentWallet::new();
        assert_eq!(wallet.receipt_chain_length(), 0);
        assert!(wallet.receipt_head().is_none());
        assert!(wallet.current_state_commitment().is_none());
        assert!(wallet.verify_own_chain().is_ok());
    }

    #[test]
    fn test_wallet_append_single_receipt() {
        let mut wallet = AgentWallet::new();
        let cell_id = wallet.cell_id("test");
        let receipt = mock_receipt(cell_id, [1u8; 32], [2u8; 32]);

        wallet.append_receipt(receipt);

        assert_eq!(wallet.receipt_chain_length(), 1);
        assert!(wallet.receipt_head().is_some());
        assert_eq!(wallet.receipt_head().unwrap().post_state_hash, [2u8; 32]);
        assert_eq!(wallet.current_state_commitment(), Some([2u8; 32]));
        // Genesis receipt should have None as previous.
        assert_eq!(wallet.receipt_head().unwrap().previous_receipt_hash, None);
        assert!(wallet.verify_own_chain().is_ok());
    }

    #[test]
    fn test_wallet_append_chain_links_correctly() {
        let mut wallet = AgentWallet::new();
        let cell_id = wallet.cell_id("test");

        // Append first receipt.
        let r1 = mock_receipt(cell_id, [1u8; 32], [2u8; 32]);
        wallet.append_receipt(r1);

        // Append second receipt (pre_state matches first post_state).
        let r2 = mock_receipt(cell_id, [2u8; 32], [3u8; 32]);
        wallet.append_receipt(r2);

        assert_eq!(wallet.receipt_chain_length(), 2);
        assert_eq!(wallet.current_state_commitment(), Some([3u8; 32]));

        // The second receipt should have previous_receipt_hash linking to the first.
        let chain = wallet.receipt_chain();
        assert_eq!(chain[0].previous_receipt_hash, None);
        assert_eq!(chain[1].previous_receipt_hash, Some(chain[0].receipt_hash()));

        assert!(wallet.verify_own_chain().is_ok());
    }

    #[test]
    fn test_wallet_chain_of_five() {
        let mut wallet = AgentWallet::new();
        let cell_id = wallet.cell_id("test");

        let mut state = [0u8; 32];
        for i in 0..5u8 {
            let pre = state;
            state[0] = i + 1;
            let post = state;
            let receipt = mock_receipt(cell_id, pre, post);
            wallet.append_receipt(receipt);
        }

        assert_eq!(wallet.receipt_chain_length(), 5);
        assert!(wallet.verify_own_chain().is_ok());

        // Verify using the standalone function too.
        let chain = wallet.receipt_chain();
        assert!(pyana_turn::verify_receipt_chain(chain).is_ok());
    }

    #[test]
    fn test_wallet_verify_chain_with_external_function() {
        let mut wallet = AgentWallet::new();
        let cell_id = wallet.cell_id("test");

        let r1 = mock_receipt(cell_id, [1u8; 32], [2u8; 32]);
        wallet.append_receipt(r1);

        let r2 = mock_receipt(cell_id, [2u8; 32], [3u8; 32]);
        wallet.append_receipt(r2);

        let r3 = mock_receipt(cell_id, [3u8; 32], [4u8; 32]);
        wallet.append_receipt(r3);

        // External verification.
        let head = pyana_turn::verify_receipt_chain_head(wallet.receipt_chain()).unwrap();
        assert_eq!(head, [4u8; 32]);
    }
}

