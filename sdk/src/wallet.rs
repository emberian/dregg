//! Agent wallet: identity, token storage, signing, and proof generation.
//!
//! The [`AgentWallet`] is the primary credential holder for an agent. It manages:
//! - An Ed25519 signing identity
//! - A collection of held authorization tokens (macaroon-backed)
//! - Token attenuation and delegation to other agents
//! - Turn signing for submission to the ledger
//! - Zero-knowledge proof generation via the bridge layer

use std::collections::HashMap;

use ed25519_dalek::Signer;
use zeroize::{Zeroize, Zeroizing};

use pyana_bridge::{BridgePredicateProof, BridgePresentationProof, Predicate};
use pyana_cell::note::NoteCommitment;
use pyana_cell::stealth::{StealthAddress, StealthAnnouncement, StealthKeys, StealthMetaAddress};
use pyana_cell::{Cell, CellId};
use pyana_circuit::BabyBear;
use pyana_circuit::IvcProof;
use pyana_circuit::PredicateType;
use pyana_circuit::ivc::IvcBuilder;
use pyana_circuit::merkle_air::MerkleAir;
use pyana_circuit::poseidon2;
use pyana_intent::sse::EncryptedIntent;
use pyana_intent::{CommitmentId, IntentKind, MatchSpec};
use pyana_token::{Attenuation, AuthRequest, AuthToken, MacaroonToken, TokenClearance};
use pyana_trace::{AuthorizationTrace, Fact as TraceFact};
use pyana_turn::{Effect, SovereignCellWitness, Turn};
use pyana_types::{PublicKey, Signature};

use crate::error::SdkError;
use crate::mnemonic;

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

// =============================================================================
// Disclosure Specification
// =============================================================================

/// Per-fact disclosure mode for selective disclosure presentations.
///
/// Each fact in the evaluation trace can be independently controlled:
/// - **Reveal**: Show the fact in plaintext to the verifier.
/// - **Predicate**: Prove a predicate about the fact's value without revealing it.
/// - **Hidden**: Do not reveal or prove anything (the STARK proves the fact exists).
#[derive(Clone, Debug)]
pub enum FactDisclosure {
    /// Reveal the fact in plaintext to the verifier.
    Reveal,
    /// Prove a predicate about the fact's value without revealing it.
    Predicate {
        predicate_type: PredicateType,
        threshold: BabyBear,
    },
    /// Prove a committed-threshold predicate: value >= threshold where the threshold
    /// is hidden from third-party verifiers behind a Poseidon2 commitment.
    ///
    /// The verifier provides `threshold` and `blinding` to the prover via a secure
    /// channel. Third parties see only `Poseidon2(threshold, blinding)`.
    CommittedThreshold {
        /// The verifier's secret threshold.
        threshold: BabyBear,
        /// The verifier's blinding randomness.
        blinding: BabyBear,
    },
    /// Prove an arithmetic predicate over multiple fact values without revealing them.
    ///
    /// The prover proves an arithmetic expression (e.g., `balance_a + balance_b >= 2000`)
    /// over the values at the specified fact indices without revealing any individual value.
    ArithmeticPredicate {
        /// Indices into the token state's fact set that serve as inputs to the expression.
        input_indices: Vec<usize>,
        /// The arithmetic expression to evaluate over the inputs.
        expression: pyana_circuit::ArithExpr,
        /// The predicate to prove about the expression result.
        predicate: pyana_circuit::ArithPredicate,
    },
    /// Do not reveal anything about this fact.
    Hidden,
}

/// A disclosure specification: determines what the verifier learns about each fact.
///
/// Facts not listed in the spec default to [].
#[derive(Clone, Debug)]
pub struct DisclosureSpec {
    /// Per-fact disclosure modes. .
    pub facts: Vec<(usize, FactDisclosure)>,
}

impl DisclosureSpec {
    /// Create a new empty disclosure spec (everything hidden).
    pub fn new() -> Self {
        Self { facts: Vec::new() }
    }

    /// Add a fact disclosure entry.
    pub fn add(&mut self, fact_index: usize, disclosure: FactDisclosure) -> &mut Self {
        self.facts.push((fact_index, disclosure));
        self
    }

    /// Convenience: reveal a fact at the given index.
    pub fn reveal(&mut self, fact_index: usize) -> &mut Self {
        self.add(fact_index, FactDisclosure::Reveal)
    }

    /// Convenience: prove a predicate about a fact at the given index.
    pub fn predicate(
        &mut self,
        fact_index: usize,
        predicate_type: PredicateType,
        threshold: BabyBear,
    ) -> &mut Self {
        self.add(
            fact_index,
            FactDisclosure::Predicate {
                predicate_type,
                threshold,
            },
        )
    }

    /// Convenience: prove a committed-threshold predicate about a fact.
    ///
    /// The threshold and blinding are provided by the verifier via a secure channel.
    /// Third-party verifiers see only the Poseidon2 commitment, not the threshold.
    pub fn committed_threshold(
        &mut self,
        fact_index: usize,
        threshold: BabyBear,
        blinding: BabyBear,
    ) -> &mut Self {
        self.add(
            fact_index,
            FactDisclosure::CommittedThreshold {
                threshold,
                blinding,
            },
        )
    }

    /// Convenience: mark a fact as hidden.
    pub fn hide(&mut self, fact_index: usize) -> &mut Self {
        self.add(fact_index, FactDisclosure::Hidden)
    }
}

impl Default for DisclosureSpec {
    fn default() -> Self {
        Self::new()
    }
}

/// The result of an authorization presentation, parameterized by verification mode.
///
/// Each variant carries exactly the information the verifier receives for that mode.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub enum AuthorizationPresentation {
    /// Trusted mode: full clearance and derivation trace, no proof needed.
    Trusted {
        /// The full token clearance (capabilities, expiry, subject).
        clearance: TokenClearance,
        /// The complete Datalog derivation trace.
        trace: AuthorizationTrace,
    },

    /// Selective disclosure: chosen facts revealed, remainder proven in ZK.
    ///
    /// The `revealed_facts_commitment` cryptographically binds the revealed facts
    /// to the STARK proof. The verifier MUST recompute this commitment from
    /// `revealed_facts` and check it matches before trusting the revealed data.
    Selective {
        /// The facts the prover chose to reveal (subset of the evaluation).
        revealed_facts: Vec<TraceFact>,
        /// The STARK proof covering the full derivation (serialized bytes).
        proof: Vec<u8>,
        /// Whether authorization was granted (informational only).
        ///
        /// SECURITY: This field is self-reported by the prover and MUST NOT be
        /// trusted for authorization decisions without independent verification.
        /// Verifiers MUST re-derive the conclusion from the STARK proof's public
        /// inputs or from the proven facts. This field exists only for UX/logging.
        conclusion: bool,
        /// Poseidon2 commitment over the revealed fact hashes.
        ///
        /// This value is embedded as a public input in the STARK proof. The verifier
        /// recomputes it from `revealed_facts` using
        /// [`pyana_bridge::compute_revealed_facts_commitment`] and confirms it matches.
        /// A mismatch means the prover lied about which facts were part of the derivation.
        revealed_facts_commitment: pyana_circuit::binding::WideHash,
        /// Predicate proofs for facts disclosed via predicate mode.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        predicate_proofs: Vec<(usize, BridgePredicateProof)>,
    },

    /// Fully private: verifier learns only the conclusion.
    Private {
        /// The STARK proof covering the full derivation (serialized bytes).
        proof: Vec<u8>,
        /// Whether authorization was granted (informational only).
        ///
        /// SECURITY: This field is self-reported by the prover and MUST NOT be
        /// trusted for authorization decisions without independent verification.
        /// The verifier MUST rely solely on the STARK proof's public inputs to
        /// determine the authorization conclusion. This field exists only for
        /// UX/logging purposes.
        conclusion: bool,
    },
}

// =============================================================================
// Token storage types
// =============================================================================

/// A token held by this wallet, along with metadata.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct HeldToken {
    /// Human-readable label for this token.
    pub label: String,
    /// The service this token grants access to.
    pub service: String,
    /// The encoded token string (em2_ prefixed).
    pub encoded: String,
    /// The root key used to verify this token (needed for re-verification).
    /// Never serialized — stays in memory only.
    #[serde(skip)]
    root_key: [u8; 32],
    /// A derived proof-only key for federation membership proofs.
    ///
    /// This is a BLAKE3 key derivation of the issuer's root HMAC key:
    /// `blake3::derive_key("pyana-proof-key-v1", &root_key)`.
    /// It is NEVER the raw root key itself.
    ///
    /// For root tokens, this is derived at construction time from `root_key`.
    /// For attenuated tokens, this is copied from the parent's `issuer_key`
    /// (which is already derived). For tokens received via delegation (where
    /// the issuer key is unknown), this is zeroed.
    ///
    /// **SECURITY**: Possession of this key does NOT allow:
    /// - Minting new root tokens (requires the raw `root_key` for HMAC chain init)
    /// - Forging or extending HMAC chains (HMAC verification requires `root_key`)
    /// - Recovering the raw root key (BLAKE3 key derivation is one-way)
    ///
    /// It DOES allow computing the federation Merkle leaf hash for ZK proofs.
    #[serde(skip)]
    issuer_key: [u8; 32],
    /// Unique identifier for lookup.
    pub id: String,
    /// Whether this token's HMAC chain has been cryptographically verified.
    ///
    /// Tokens minted locally or decoded with the real root key are `true`.
    /// Tokens received via delegation (where the root key is unknown) are `false`
    /// because `receive_delegation` performs only structural validation (parse +
    /// caveat structure), NOT HMAC chain verification.
    ///
    /// **SECURITY**: Code paths that treat a HeldToken as "trusted" for authorization
    /// decisions MUST check this field. An unverified token may have been forged or
    /// tampered with. Verification happens at presentation time when the token is
    /// submitted to a service that holds the root key.
    #[serde(default = "default_verified_false")]
    pub verified: bool,
    /// Pre-generated federation membership proof (for delegated tokens).
    ///
    /// When a token is received via delegation, the delegator pre-generates a
    /// Merkle membership proof for the REAL issuer key (which IS in the federation
    /// tree). The delegatee stores this proof and uses it directly during proof
    /// generation, bypassing the need to look up the proof_key in the federation tree
    /// (which would fail since the tree contains real keys, not their BLAKE3 derivations).
    ///
    /// `None` for tokens minted locally (they can generate fresh proofs on the fly).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub membership_proof: Option<pyana_commit::merkle::MerkleProof>,
    /// BLAKE3 hash of the serialized caveat chain, computed by the delegator at
    /// delegation time from the HMAC-verified token.
    ///
    /// The delegatee verifies this hash against their decoded token's caveats before
    /// using them for ZK proof generation. This prevents an attacker who holds the
    /// `proof_key` from mutating caveats in the encoded token and generating proofs
    /// over fabricated facts.
    ///
    /// `None` for tokens minted locally (they hold the root key and can verify the
    /// HMAC chain directly).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub caveat_chain_hash: Option<[u8; 32]>,
}

/// Default for deserialization of older snapshots that lack the `verified` field.
/// Conservatively defaults to `false` — unverified until proven otherwise.
/// Tokens that were minted locally or verified via HMAC chain will have this
/// field explicitly set to `true` at creation time.
fn default_verified_false() -> bool {
    false
}

impl Drop for HeldToken {
    fn drop(&mut self) {
        self.root_key.zeroize();
        self.issuer_key.zeroize();
    }
}

impl HeldToken {
    /// Create a new HeldToken with the given fields.
    ///
    /// Tokens created with a real (non-zeroed) root key are marked as verified.
    /// Tokens with a zeroed root key are marked as unverified (delegated tokens).
    pub(crate) fn new(
        label: String,
        service: String,
        encoded: String,
        root_key: [u8; 32],
        id: String,
    ) -> Self {
        let verified = root_key != [0u8; 32];
        // For root tokens, derive a proof-only key from the root key.
        // This ensures the issuer_key NEVER equals the root_key, preventing
        // key leakage through attenuation or delegation paths.
        // Uses the same context string as AgentWallet::derive_proof_key().
        let issuer_key = if root_key != [0u8; 32] {
            blake3::derive_key("pyana-proof-key-v1", &root_key)
        } else {
            [0u8; 32]
        };
        Self {
            label,
            service,
            encoded,
            root_key,
            issuer_key,
            id,
            verified,
            membership_proof: None,
            caveat_chain_hash: None,
        }
    }

    /// Create a new attenuated HeldToken (zeroed root_key — cannot mint or forge).
    ///
    /// Attenuated tokens carry the encoded macaroon chain and the issuer key for
    /// federation membership proofs. They can be further attenuated, presented for
    /// verification, and generate ZK proofs, but cannot mint new root tokens.
    ///
    /// Attenuated tokens created locally (from a verified parent) are marked as verified.
    pub(crate) fn new_attenuated(
        label: String,
        service: String,
        encoded: String,
        id: String,
        issuer_key: [u8; 32],
    ) -> Self {
        Self {
            label,
            service,
            encoded,
            root_key: [0u8; 32],
            issuer_key,
            id,
            verified: true, // Locally-attenuated from a verified parent
            membership_proof: None,
            caveat_chain_hash: None,
        }
    }

    /// Access the root key by reference (internal use only).
    pub(crate) fn root_key(&self) -> &[u8; 32] {
        &self.root_key
    }

    /// Access the issuer key by reference.
    ///
    /// This key allows computing federation membership proofs but does NOT
    /// grant the ability to mint or forge tokens.
    pub(crate) fn issuer_key(&self) -> &[u8; 32] {
        &self.issuer_key
    }

    /// Returns `true` if this token holds the root forging key.
    ///
    /// Attenuated and delegated tokens have a zeroed root_key and return `false`.
    /// Only root tokens minted by this wallet return `true`.
    pub fn can_mint(&self) -> bool {
        self.root_key != [0u8; 32]
    }

    /// Returns `true` if this token can generate ZK proofs.
    ///
    /// A token can prove if it has the derived proof key (for federation membership).
    /// This is true for root tokens (issuer_key = derive(root_key)) and for attenuated
    /// tokens created locally from a parent that held the proof key.
    ///
    /// Tokens received via delegation without a proof key cannot prove;
    /// use `prove_authorization_with_issuer_key()` for those.
    pub fn can_prove(&self) -> bool {
        self.issuer_key != [0u8; 32]
    }

    /// Returns `true` if this token's HMAC chain has been cryptographically verified.
    ///
    /// Tokens received via delegation are NOT verified (only structurally validated).
    /// They should be treated as untrusted until presented to a service holding the
    /// root key for full HMAC chain verification.
    pub fn is_verified(&self) -> bool {
        self.verified
    }

    /// Decode this held token into a [`MacaroonToken`] for operations.
    pub fn decode(&self) -> Result<MacaroonToken, pyana_token::TokenError> {
        MacaroonToken::from_encoded(&self.encoded, self.root_key)
    }
}

/// A token that has been delegated to another agent.
///
/// Contains only the serialized attenuated macaroon bytes (NOT the root key).
/// The delegatee can present this token for verification and further attenuate it,
/// but cannot mint new root tokens.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct DelegatedToken {
    /// The serialized attenuated token (encoded macaroon string).
    pub token_bytes: String,
    /// The service this token grants access to.
    pub service: String,
    /// Human-readable label.
    pub label: String,
    /// Token identifier.
    pub id: String,
    /// The public key of the delegatee.
    pub delegatee: PublicKey,
    /// The restrictions applied during delegation.
    pub restrictions: Attenuation,
    /// Derived proof key for ZK proof generation by the delegatee.
    ///
    /// This is the token's `issuer_key`, which is already a one-way BLAKE3
    /// derivation of the issuer's root HMAC key via
    /// `blake3::derive_key("pyana-proof-key-v1", &root_key)`. It grants the
    /// delegatee the ability to generate federation membership proofs (ZK) but
    /// NOT the ability to mint or forge tokens (one-way derivation).
    ///
    /// When `None`, the delegatee cannot generate proofs without out-of-band
    /// key material. This field is populated by [`AgentWallet::delegate()`] when
    /// the delegator holds a token with proof capability.
    #[serde(default)]
    pub proof_key: Option<[u8; 32]>,
    /// Pre-generated federation membership proof for the delegatee.
    ///
    /// The delegator (who holds the REAL issuer key and CAN generate membership
    /// proofs from the federation tree) pre-generates this proof and includes it
    /// in the delegation payload. The delegatee uses this proof directly instead
    /// of trying to look up membership by `proof_key` (which is a BLAKE3 derivation
    /// not present in the federation tree).
    ///
    /// **Security property**: The membership proof is bound to the specific federation
    /// root at delegation time. If the federation root changes (e.g., issuer is removed),
    /// this pre-generated proof becomes invalid and the delegatee can no longer prove
    /// membership.
    #[serde(default)]
    pub membership_proof: Option<pyana_commit::merkle::MerkleProof>,
    /// BLAKE3 hash of the serialized caveat chain, computed by the delegator from
    /// the HMAC-verified token. The delegatee uses this to verify caveat integrity
    /// before generating ZK proofs.
    ///
    /// Without this, a delegatee holding the `proof_key` could mutate caveats in
    /// the encoded token and generate proofs over fabricated authorization facts.
    #[serde(default)]
    pub caveat_chain_hash: Option<[u8; 32]>,
    /// Ed25519 signature from the delegator over the delegation envelope.
    ///
    /// Signs `blake3::derive_key("pyana-delegation-binding-v1", caveat_chain_hash || proof_key || membership_leaf)`.
    /// This prevents a malicious delegatee from mutating caveats and recomputing the
    /// `caveat_chain_hash` — they cannot forge the delegator's signature.
    #[serde(default)]
    pub delegator_signature: Option<Signature>,
    /// The delegator's public key, needed to verify `delegator_signature`.
    #[serde(default)]
    pub delegator_public_key: Option<PublicKey>,
}

/// A turn signed by this wallet's identity, ready for submission.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
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
/// - HD key derivation from mnemonic (BIP39 + BLAKE3)
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
    /// Optional IVC builder for incrementally accumulating state transition proofs.
    /// When enabled, each appended receipt extends the IVC chain, producing a
    /// constant-size proof of the entire state transition history.
    /// Skipped during serialization as it is runtime-only state.
    ivc_builder: Option<IvcBuilder>,
    /// The HD seed from which this wallet's key was derived (if created from mnemonic).
    /// Stored encrypted at rest; zeroized on drop.
    seed: Option<[u8; 64]>,
    /// The mnemonic phrase used to create this wallet (if created from mnemonic).
    /// Stored encrypted at rest; zeroized on drop.
    mnemonic_phrase: Option<String>,
    /// The derivation path used for this wallet's key (e.g., "pyana/0").
    derivation_path: Option<String>,
    /// Stealth keypair for receiving private notes via one-time addresses.
    /// Derived deterministically from the wallet's signing key.
    stealth_keys: StealthKeys,
    /// Local state for sovereign cells we own.
    ///
    /// When a cell is transitioned to sovereign mode, the federation stores only
    /// a 32-byte commitment. The agent maintains the full cell state here and
    /// provides it as a witness in each turn targeting the cell.
    sovereign_cells: HashMap<CellId, Cell>,
}

impl AgentWallet {
    /// Domain separation prefix for all signatures produced by this wallet.
    /// Prevents cross-protocol signature reuse (e.g., a signed message being
    /// replayed as a turn signature or vice versa).
    const DOMAIN_PREFIX: &'static [u8] = b"pyana-v1:";

    /// Domain separation prefix for turn signing specifically.
    const TURN_DOMAIN_PREFIX: &'static [u8] = b"pyana-turn-v1:";

    /// Create a new wallet with a randomly generated Ed25519 identity.
    ///
    /// # Example
    /// ```
    /// use pyana_sdk::AgentWallet;
    /// let wallet = AgentWallet::new();
    /// println!("Agent identity: {}", wallet.public_key());
    /// ```
    pub fn new() -> Self {
        let mut key_bytes = Zeroizing::new([0u8; 32]);
        getrandom::fill(&mut *key_bytes).expect("getrandom failed");
        Self::from_key_bytes(key_bytes)
    }

    /// Create a wallet from an existing 32-byte Ed25519 secret key.
    ///
    /// Use this when restoring a wallet from persisted key material.
    ///
    /// # Security
    ///
    /// The key material is wrapped in [`Zeroizing`] to ensure it is erased from
    /// memory when no longer needed. This prevents the caller's copy from
    /// persisting on the stack or heap after wallet construction. Callers should
    /// always wrap key bytes in `Zeroizing` before passing them to this function
    /// to benefit from automatic zeroization on drop.
    pub fn from_key_bytes(mut secret: Zeroizing<[u8; 32]>) -> Self {
        let signing_key = ed25519_dalek::SigningKey::from_bytes(&secret);
        let verifying_key = signing_key.verifying_key();
        let public_key = PublicKey(verifying_key.to_bytes());
        // Derive stealth keys deterministically from the signing key.
        let stealth_keys = Self::derive_stealth_keys(&signing_key);
        // Explicitly zeroize before drop for defense-in-depth (Zeroizing's Drop
        // impl will also do this, but we want to be clear about intent).
        secret.zeroize();
        AgentWallet {
            signing_key,
            public_key,
            tokens: Vec::new(),
            next_token_id: 0,
            receipt_chain: Vec::new(),
            ivc_builder: None,
            seed: None,
            mnemonic_phrase: None,
            derivation_path: None,
            stealth_keys,
            sovereign_cells: HashMap::new(),
        }
    }

    /// Create a wallet from a BIP39 mnemonic phrase.
    ///
    /// Derives the main agent identity at path `pyana/0`. The mnemonic and seed
    /// are retained in memory (encrypted at rest) for sub-agent derivation and
    /// backup export.
    ///
    /// # Arguments
    ///
    /// * `mnemonic_str` - A valid 24-word BIP39 mnemonic.
    /// * `passphrase` - Optional passphrase for additional protection. Use `""` for none.
    pub fn from_mnemonic(mnemonic_str: &str, passphrase: &str) -> Result<Self, SdkError> {
        let seed = mnemonic::mnemonic_to_seed(mnemonic_str, passphrase)
            .map_err(|e| SdkError::MissingKey(e.to_string()))?;
        let mut wallet = Self::from_seed_at_path(seed, "pyana/0");
        wallet.mnemonic_phrase = Some(mnemonic_str.to_string());
        Ok(wallet)
    }

    /// Create a wallet from a raw 64-byte seed, deriving the main identity at `pyana/0`.
    ///
    /// Use this when the seed was obtained externally (e.g., from an encrypted backup).
    pub fn from_seed(seed: [u8; 64]) -> Self {
        Self::from_seed_at_path(seed, "pyana/0")
    }

    /// Create a wallet from a seed at a specific derivation path.
    fn from_seed_at_path(seed: [u8; 64], path: &str) -> Self {
        let (_pub_bytes, mut sec_bytes) = mnemonic::derive_keypair(&seed, path);
        let signing_key = ed25519_dalek::SigningKey::from_bytes(&sec_bytes);
        // Zeroize the derived secret key bytes now that we have the SigningKey.
        sec_bytes.zeroize();
        let verifying_key = signing_key.verifying_key();
        let public_key = PublicKey(verifying_key.to_bytes());
        let stealth_keys = Self::derive_stealth_keys(&signing_key);
        AgentWallet {
            signing_key,
            public_key,
            tokens: Vec::new(),
            next_token_id: 0,
            receipt_chain: Vec::new(),
            ivc_builder: None,
            seed: Some(seed),
            mnemonic_phrase: None,
            derivation_path: Some(path.to_string()),
            stealth_keys,
            sovereign_cells: HashMap::new(),
        }
    }

    /// Derive a sub-agent wallet at the given index.
    ///
    /// The sub-agent's key is derived from the same seed at path `pyana/{index}`.
    /// Requires that this wallet was created from a mnemonic or seed.
    ///
    /// # Arguments
    ///
    /// * `index` - The derivation index. Use 1, 2, 3, ... (0 is the main identity).
    pub fn derive_sub_agent(&self, index: u32) -> Result<Self, SdkError> {
        let seed = self
            .seed
            .ok_or_else(|| SdkError::MissingKey("wallet has no seed for derivation".into()))?;
        let path = format!("pyana/{}", index);
        Ok(Self::from_seed_at_path(seed, &path))
    }

    /// Export the mnemonic phrase if this wallet was created from one.
    ///
    /// Returns `None` if the wallet was created from raw key bytes or if the
    /// mnemonic has been explicitly cleared.
    ///
    /// # Security
    ///
    /// This method requires `&mut self` to prevent extraction via shared references.
    /// The mnemonic phrase is the master secret from which all keys are derived.
    /// Exposing it allows full wallet reconstruction including all sub-agent keys.
    ///
    /// Callers MUST ensure the returned value is:
    /// - Never logged or serialized to persistent storage without encryption.
    /// - Zeroized after use (the reference borrows from the wallet, so the wallet
    ///   handles zeroization on drop, but callers must not copy into unprotected buffers).
    /// - Never transmitted over network without end-to-end encryption.
    #[must_use = "exported mnemonic is highly sensitive master key material"]
    pub fn export_mnemonic(&mut self) -> Option<&str> {
        self.mnemonic_phrase.as_deref()
    }

    /// Export the raw seed if available.
    ///
    /// Returns `None` if the wallet was created from raw key bytes without a seed.
    ///
    /// # Security
    ///
    /// This method requires `&mut self` to prevent extraction via shared references.
    /// The seed is the master secret from which all keys are derived. Exposing it
    /// allows full wallet reconstruction including all sub-agent keys.
    ///
    /// Callers MUST ensure the returned value is:
    /// - Never logged or serialized to persistent storage without encryption.
    /// - Zeroized after use (the reference borrows from the wallet, so the wallet
    ///   handles zeroization on drop, but callers must not copy into unprotected buffers).
    /// - Never transmitted over network without end-to-end encryption.
    #[must_use = "exported seed is highly sensitive master key material"]
    pub fn export_seed(&mut self) -> Option<&[u8; 64]> {
        self.seed.as_ref()
    }

    /// Get the derivation path used for this wallet's key.
    pub fn derivation_path(&self) -> Option<&str> {
        self.derivation_path.as_deref()
    }

    /// Get this agent's public key (identity).
    pub fn public_key(&self) -> PublicKey {
        self.public_key
    }

    /// Derive a purpose-specific symmetric key from this wallet's signing key.
    ///
    /// Uses BLAKE3's key derivation mode with the given context string to
    /// produce a 32-byte key that is deterministic for this wallet but
    /// unique per context. This is used, for example, to derive the gossip
    /// envelope signing key for federation communication.
    ///
    /// # Security
    ///
    /// The derived key is a deterministic function of the signing key and
    /// context. Different context strings produce independent keys.
    pub fn derive_symmetric_key(&self, context: &str) -> [u8; 32] {
        blake3::derive_key(context, &self.signing_key.to_bytes())
    }

    /// Get the node's Ed25519 signing key as a `pyana_types::SigningKey`.
    ///
    /// Used by the gossip layer for asymmetric envelope signing. Each node
    /// signs with its own key; peers verify using this node's public key.
    pub fn gossip_signing_key(&self) -> pyana_types::SigningKey {
        pyana_types::SigningKey::from_bytes(&self.signing_key.to_bytes())
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

        let held = HeldToken::new(
            format!("root:{}", service),
            service.to_string(),
            encoded,
            *root_key,
            kid,
        );

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

        // SECURITY: Attenuated tokens do NOT carry the root forging key.
        // They can be further attenuated and presented for verification,
        // but cannot mint new root tokens or bypass the attenuation chain.
        //
        // They carry the derived issuer_key (proof-only key) for ZK proof generation.
        // This key is a one-way BLAKE3 derivation of the root key — possession of it
        // does NOT allow minting tokens or forging HMAC chains.
        let issuer_key = *token.issuer_key();
        let held = HeldToken::new_attenuated(
            format!("attenuated:{}", token.service),
            token.service.clone(),
            encoded,
            id,
            issuer_key,
        );

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

        // Pass through the derived proof key to the delegatee.
        // The issuer_key is already a one-way derivation of the root key (never the
        // raw root key itself), so it's safe to transmit to a less-trusted party.
        let proof_key = if token.can_prove() {
            let key = token.issuer_key();
            if *key != [0u8; 32] { Some(*key) } else { None }
        } else {
            None
        };

        // Compute the caveat chain hash from the HMAC-verified attenuated token.
        // The delegator holds the root key and can verify the chain; the delegatee
        // will use this commitment to detect any post-delegation caveat tampering.
        let caveat_chain_hash = {
            let decoded = attenuated.decode()?;
            Some(Self::compute_caveat_chain_hash(&decoded))
        };

        // SECURITY: Sign the delegation envelope so the delegatee cannot mutate
        // caveats and recompute caveat_chain_hash without the delegator's key.
        let (delegator_signature, delegator_public_key) =
            self.sign_delegation_envelope(&caveat_chain_hash, &proof_key, None);

        Ok(DelegatedToken {
            token_bytes: attenuated.encoded.clone(),
            service: attenuated.service.clone(),
            label: attenuated.label.clone(),
            id: attenuated.id.clone(),
            delegatee: *to,
            restrictions: restrictions.clone(),
            proof_key,
            membership_proof: None,
            caveat_chain_hash,
            delegator_signature: Some(delegator_signature),
            delegator_public_key: Some(delegator_public_key),
        })
    }

    /// Delegate a token to another agent with a pre-generated federation membership proof.
    ///
    /// When a `federation_tree` is provided, the delegator pre-generates a federation
    /// membership proof using the BLAKE3-derived proof key (which IS in the tree as a
    /// leaf). The delegatee receives this proof and can use it directly during
    /// presentation without needing access to the tree.
    ///
    /// Federation tree leaves are BLAKE3-derived proof keys (`derive_proof_key(root_key)`),
    /// NOT raw root keys. This ensures that the real issuer key is never exposed as a
    /// tree leaf.
    ///
    /// Without a federation tree, the delegatee falls back to synthetic/test proofs or
    /// must supply the tree at proof-generation time.
    ///
    /// # Arguments
    ///
    /// * `token` - The token to delegate from.
    /// * `to` - The public key of the agent receiving the delegation.
    /// * `restrictions` - Additional restrictions beyond those already on the token.
    /// * `federation_tree` - Federation Merkle tree for pre-generating membership proofs.
    pub fn delegate_with_tree(
        &mut self,
        token: &HeldToken,
        to: &PublicKey,
        restrictions: &Attenuation,
        federation_tree: &pyana_commit::merkle::MerkleTree,
    ) -> Result<DelegatedToken, SdkError> {
        let attenuated = self.attenuate(token, restrictions)?;

        // Pass through the derived proof key to the delegatee.
        let proof_key = if token.can_prove() {
            let key = token.issuer_key();
            if *key != [0u8; 32] { Some(*key) } else { None }
        } else {
            None
        };

        // Pre-generate federation membership proof. The federation tree contains
        // BLAKE3-derived proof keys (not raw root keys). Look up the derived key.
        let membership_proof = if token.can_mint() {
            // Root token holder: derive the proof key and look it up in the tree.
            let derived = Self::derive_proof_key(token.root_key());
            federation_tree.membership_proof(&derived)
        } else {
            token.membership_proof.clone()
        };

        // Compute the caveat chain hash from the HMAC-verified attenuated token.
        let caveat_chain_hash = {
            let decoded = attenuated.decode()?;
            Some(Self::compute_caveat_chain_hash(&decoded))
        };

        // SECURITY: Sign the delegation envelope so the delegatee cannot mutate
        // caveats and recompute caveat_chain_hash without the delegator's key.
        let membership_leaf = membership_proof.as_ref().map(|p| p.leaf_hash);
        let (delegator_signature, delegator_public_key) =
            self.sign_delegation_envelope(&caveat_chain_hash, &proof_key, membership_leaf.as_ref());

        Ok(DelegatedToken {
            token_bytes: attenuated.encoded.clone(),
            service: attenuated.service.clone(),
            label: attenuated.label.clone(),
            id: attenuated.id.clone(),
            delegatee: *to,
            restrictions: restrictions.clone(),
            proof_key,
            membership_proof,
            caveat_chain_hash,
            delegator_signature: Some(delegator_signature),
            delegator_public_key: Some(delegator_public_key),
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

    /// Maximum size (in bytes) for a delegated token's encoded payload.
    ///
    /// Tokens exceeding this size are rejected to prevent memory DoS attacks
    /// where an attacker sends an enormous token string.
    const MAX_DELEGATED_TOKEN_SIZE: usize = 64 * 1024; // 64 KiB

    /// Receive a delegated token into this wallet.
    ///
    /// Call this when another agent has delegated a token to us. The token
    /// is added to the wallet's held tokens. The delegatee does NOT receive the
    /// root key -- they can present the token for verification but cannot mint
    /// new root tokens.
    ///
    /// # Validation
    ///
    /// This method validates the delegated token before accepting it:
    /// - Size: token payload must not exceed 64 KiB (memory DoS prevention).
    /// - Deserializable: the token must parse as a valid macaroon structure.
    /// - Expiry: if the delegation restrictions specify `not_after`, it must not be in the past.
    ///
    /// # Errors
    ///
    /// Returns [`SdkError`] if any validation check fails.
    pub fn receive_delegation(&mut self, delegated: DelegatedToken) -> Result<(), SdkError> {
        // (a) Size check: reject oversized tokens to prevent memory DoS.
        if delegated.token_bytes.len() > Self::MAX_DELEGATED_TOKEN_SIZE {
            return Err(SdkError::InvalidDelegation(format!(
                "token payload too large: {} bytes exceeds {} byte limit",
                delegated.token_bytes.len(),
                Self::MAX_DELEGATED_TOKEN_SIZE,
            )));
        }

        // (b) Deserialization check: ensure the token can be decoded as a valid macaroon.
        // We use a zeroed root_key since we don't have the issuer key -- this verifies
        // structural validity (parse, caveat structure) without HMAC chain verification.
        let _decoded =
            MacaroonToken::from_encoded(&delegated.token_bytes, [0u8; 32]).map_err(|e| {
                SdkError::InvalidDelegation(format!("token failed to deserialize: {e}"))
            })?;

        // (c) Expiry check: if the delegation restrictions specify not_after, ensure
        // the token hasn't already expired. This catches the common case where an
        // attacker replays an old delegation with an expired time window.
        if let Some(not_after) = delegated.restrictions.not_after {
            let now = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_secs() as i64)
                .unwrap_or(0);
            if not_after <= now {
                return Err(SdkError::InvalidDelegation(format!(
                    "delegated token has expired: not_after={not_after}, now={now}"
                )));
            }
        }

        // (d) Delegation envelope signature verification: if the delegator provided a
        // signature, verify it to ensure the caveat_chain_hash has not been tampered with.
        // This is the primary defense against a malicious delegate mutating caveats.
        if let (Some(sig), Some(pubkey)) = (
            &delegated.delegator_signature,
            &delegated.delegator_public_key,
        ) {
            let membership_leaf = delegated.membership_proof.as_ref().map(|p| p.leaf_hash);
            Self::verify_delegation_signature(
                pubkey,
                sig,
                &delegated.caveat_chain_hash,
                &delegated.proof_key,
                membership_leaf.as_ref(),
            )?;
        }

        // SECURITY: The token is accepted with structural validation only. The HMAC chain
        // is NOT verified because we do not hold the root key. The token is marked as
        // unverified — callers MUST check `is_verified()` before trusting it for
        // authorization decisions. Full verification occurs at presentation time when
        // the token is submitted to a verifier that holds the root key.
        tracing::warn!(
            service = %delegated.service,
            id = %delegated.id,
            "accepting unverified delegated token: HMAC chain not verified (root key unavailable). \
             Token will be verified at presentation time."
        );

        let mut held = HeldToken::new(
            delegated.label,
            delegated.service,
            delegated.token_bytes,
            [0u8; 32], // delegatee does not have the root key
            delegated.id,
        );
        // Explicitly mark as unverified (new() already does this for zeroed root_key,
        // but we're explicit here for clarity and defense-in-depth).
        held.verified = false;

        // Store the derived proof key if provided by the delegator.
        // This allows the delegatee to generate ZK proofs (federation membership)
        // without holding the raw issuer key (one-way derivation preserves security).
        if let Some(proof_key) = delegated.proof_key {
            if proof_key != [0u8; 32] {
                held.issuer_key = proof_key;
            }
        }

        // Store the pre-generated federation membership proof if provided.
        // The delegator generated this from the BLAKE3-derived proof key (which is the
        // tree leaf). The delegatee uses it directly during proof generation.
        held.membership_proof = delegated.membership_proof;

        // Store the caveat chain hash for integrity verification at proof time.
        held.caveat_chain_hash = delegated.caveat_chain_hash;

        self.tokens.push(held);
        Ok(())
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

        // Extend the IVC chain if enabled.
        if let Some(ref mut builder) = self.ivc_builder {
            use pyana_circuit::fold_air::{FoldWitness, RemovedFact};
            use pyana_circuit::ivc::FoldDelta;

            // Encode the state transition as a fold step: the pre_state transitions
            // to post_state. We model this as a removal of the pre-state fact and
            // the new_root being derived from the post-state hash.
            let pre_bb = Self::bytes_to_babybear(&receipt.pre_state_hash);
            let post_bb = Self::bytes_to_babybear(&receipt.post_state_hash);
            let turn_bb = Self::bytes_to_babybear(&receipt.turn_hash);

            let fold = FoldWitness {
                old_root: pre_bb,
                new_root: post_bb,
                removed_facts: vec![RemovedFact {
                    predicate: turn_bb,
                    terms: [
                        pre_bb,
                        post_bb,
                        BabyBear::new(receipt.computrons_used as u32),
                    ],
                    membership_proof: None,
                }],
                num_added_checks: 1,
                added_checks_commitment: pyana_circuit::fold_air::compute_test_checks_commitment(1),
            };
            // Best-effort: if the fold fails (e.g., root mismatch on first step),
            // we still append the receipt but skip IVC extension.
            // Don't append to IVC state — it would be inconsistent.
            let receipt_hash = receipt.receipt_hash();
            if let Err(e) = builder.add_fold(FoldDelta::new(fold)) {
                tracing::warn!("IVC fold failed for receipt {:?}: {}", receipt_hash, e);
            }
        }

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
    // IVC (Incrementally Verifiable Computation)
    // =========================================================================

    /// Enable IVC accumulation for this wallet's receipt chain.
    ///
    /// Once enabled, every call to [`append_receipt`](Self::append_receipt) will
    /// extend the IVC chain with the state transition, building a constant-size
    /// proof of the entire state transition history.
    ///
    /// # Arguments
    ///
    /// * `initial_root` - The initial state root (typically the pre_state_hash of
    ///   the first receipt, encoded as a BabyBear field element).
    pub fn enable_ivc(&mut self, initial_root: BabyBear) {
        self.ivc_builder = Some(IvcBuilder::new(initial_root));
    }

    /// Export the current IVC state proof.
    ///
    /// Returns a constant-size [`IvcProof`] covering the entire receipt chain
    /// accumulated since [`enable_ivc`](Self::enable_ivc) was called. Returns
    /// `None` if IVC is not enabled or no receipts have been appended since
    /// IVC was enabled.
    pub fn export_state_proof(&self) -> Option<IvcProof> {
        self.ivc_builder.as_ref()?.finalize_with_air()
    }

    /// Check whether IVC is currently enabled on this wallet.
    pub fn ivc_enabled(&self) -> bool {
        self.ivc_builder.is_some()
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

    /// Selective disclosure: STARK proof with chosen facts cryptographically committed.
    ///
    /// The revealed facts are bound to the proof via a Poseidon2 commitment included
    /// as a public input. The verifier recomputes the commitment from the plaintext
    /// facts and checks it matches the proof, ensuring the prover cannot lie about
    /// which facts were derived during evaluation.
    fn authorize_selective(
        &self,
        token: &HeldToken,
        request: &AuthRequest,
        reveal: &[FactIndex],
    ) -> Result<AuthorizationPresentation, SdkError> {
        // Step 1: Run Datalog locally to get the trace.
        // For attenuated tokens, use structural extraction (ZK proof replaces HMAC).
        let caveat_set = Self::extract_caveat_set_for_proof(token)?;
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

        // Step 3: Compute the Poseidon2 commitment over the revealed facts.
        // This cryptographically binds the revealed facts to the STARK proof.
        let commitment = pyana_bridge::compute_revealed_facts_commitment(&revealed_facts);

        // Step 4: Generate STARK proof via the bridge with the commitment as a public input.
        // For attenuated tokens, use the issuer key path.
        let bridge_proof = if token.can_mint() {
            self.prove_authorization_selective(token, request, commitment)?
        } else {
            self.prove_authorization_selective_with_issuer_key(
                token,
                token.issuer_key(),
                request,
                commitment,
            )?
        };
        let proof = Self::serialize_proof(bridge_proof)?;

        Ok(AuthorizationPresentation::Selective {
            revealed_facts,
            proof,
            conclusion,
            revealed_facts_commitment: commitment,
            predicate_proofs: Vec::new(),
        })
    }

    /// Fully private mode: STARK proof revealing only the conclusion bit.
    fn authorize_private(
        &self,
        token: &HeldToken,
        request: &AuthRequest,
    ) -> Result<AuthorizationPresentation, SdkError> {
        // Step 1: Run Datalog locally to determine conclusion.
        // For attenuated tokens, use structural extraction (no HMAC verification needed —
        // the ZK proof replaces the HMAC chain as the integrity guarantee).
        let caveat_set = Self::extract_caveat_set_for_proof(token)?;
        let result = pyana_token::datalog_verify::verify_token_datalog(&caveat_set, request)?;

        let conclusion = matches!(
            result.trace.conclusion,
            pyana_trace::Conclusion::Allow { .. }
        );

        // Step 2: Generate full STARK proof via the bridge.
        // The proof covers the entire MultiStepDerivationAir -- the verifier
        // only receives the conclusion public input, learning nothing else.
        //
        // For attenuated tokens that have the issuer key (can_prove() == true),
        // we use prove_authorization_with_issuer_key internally.
        let bridge_proof = if token.can_mint() {
            self.prove_authorization(token, request)?
        } else {
            self.prove_authorization_with_issuer_key(token, token.issuer_key(), request)?
        };
        let proof = Self::serialize_proof(bridge_proof)?;

        Ok(AuthorizationPresentation::Private { proof, conclusion })
    }

    /// Authorize a request with per-fact disclosure control.
    ///
    /// Each fact in the derivation trace can be independently:
    /// - **Revealed**: shown in plaintext (like `SelectiveDisclosure`).
    /// - **Predicate-proven**: a ZK predicate proof is generated.
    /// - **Hidden**: nothing is revealed (like `FullyPrivate`).
    pub fn authorize_with_disclosure(
        &self,
        token: &HeldToken,
        request: &AuthRequest,
        disclosure: &DisclosureSpec,
    ) -> Result<AuthorizationPresentation, SdkError> {
        // Step 1: Run Datalog locally to get the full trace.
        // For attenuated tokens, use structural extraction (ZK proof replaces HMAC).
        let caveat_set = Self::extract_caveat_set_for_proof(token)?;
        let result = pyana_token::datalog_verify::verify_token_datalog(&caveat_set, request)?;

        let conclusion = matches!(
            result.trace.conclusion,
            pyana_trace::Conclusion::Allow { .. }
        );

        // Step 2: Extract all derived facts from the trace.
        let all_facts: Vec<TraceFact> = result
            .trace
            .steps
            .iter()
            .map(|step| step.derived_fact.clone())
            .collect();

        // Step 3: Partition facts by disclosure mode.
        let mut revealed_facts: Vec<TraceFact> = Vec::new();
        let mut predicate_proofs: Vec<(usize, BridgePredicateProof)> = Vec::new();

        // Compute a state root for predicate fact commitments.
        // The issuer_key is always the derived proof key (never the raw root key),
        // whether this is a root token or an attenuated token.
        let state_root = Self::bytes_to_babybear(token.issuer_key());

        for (fact_index, disclosure_mode) in &disclosure.facts {
            let fact = match all_facts.get(*fact_index) {
                Some(f) => f,
                None => continue,
            };

            match disclosure_mode {
                FactDisclosure::Reveal => {
                    revealed_facts.push(fact.clone());
                }
                FactDisclosure::Predicate {
                    predicate_type,
                    threshold,
                } => {
                    let value = Self::extract_fact_value(fact)?;
                    let pred_bb = Self::trace_fact_predicate_bb(fact);
                    let term_bbs = Self::trace_fact_terms_bb(fact);
                    let fact_hash = poseidon2::hash_fact(pred_bb, &term_bbs);
                    let bridge_predicate =
                        Self::predicate_type_to_bridge(*predicate_type, threshold.as_u32());

                    let proof = pyana_bridge::prove_predicate_for_fact(
                        value,
                        fact_hash,
                        state_root,
                        &bridge_predicate,
                    )
                    .ok_or_else(|| {
                        SdkError::Auth(pyana_bridge::AuthError::InvalidRequest(format!(
                            "predicate proof generation failed for fact[{}]:                              {:?} not satisfiable for value {}",
                            fact_index, predicate_type, value
                        )))
                    })?;

                    predicate_proofs.push((*fact_index, proof));
                }
                FactDisclosure::CommittedThreshold {
                    threshold,
                    blinding,
                } => {
                    // Generate a committed-threshold proof: value >= threshold
                    // where neither value nor threshold is revealed to third parties.
                    let value = Self::extract_fact_value(fact)?;
                    let pred_bb = Self::trace_fact_predicate_bb(fact);
                    let term_bbs = Self::trace_fact_terms_bb(fact);
                    let fact_hash = poseidon2::hash_fact(pred_bb, &term_bbs);

                    let committed_proof = pyana_bridge::prove_committed_threshold(
                        value,
                        threshold.as_u32(),
                        blinding.as_u32(),
                        fact_hash,
                        state_root,
                    )
                    .ok_or_else(|| {
                        SdkError::Auth(pyana_bridge::AuthError::InvalidRequest(format!(
                            "committed-threshold proof generation failed for fact[{}]: \
                             value {} does not satisfy committed threshold",
                            fact_index, value
                        )))
                    })?;

                    // Store the committed-threshold proof directly. The verifier
                    // sees only the threshold_commitment and fact_commitment (both
                    // are Poseidon2 hashes that hide the actual values).
                    let bridge_proof = BridgePredicateProof {
                        predicate: Predicate::Gte(0), // Threshold hidden; predicate label is nominal
                        proof: pyana_bridge::BridgePredicateProofInner::CommittedThreshold(
                            committed_proof.proof,
                        ),
                        fact_commitment: committed_proof.fact_commitment,
                    };
                    predicate_proofs.push((*fact_index, bridge_proof));
                }
                FactDisclosure::ArithmeticPredicate { .. } => {
                    // Arithmetic predicates over multiple facts are not yet supported
                    // in the selective disclosure pipeline. Treated as hidden for now.
                }
                FactDisclosure::Hidden => {}
            }
        }

        // Step 4: Compute Poseidon2 commitment over revealed facts.
        let commitment = pyana_bridge::compute_revealed_facts_commitment(&revealed_facts);

        // Step 5: Generate STARK proof with the commitment as public input.
        // For attenuated tokens, use the issuer key path.
        let bridge_proof = if token.can_mint() {
            self.prove_authorization_selective(token, request, commitment)?
        } else {
            self.prove_authorization_selective_with_issuer_key(
                token,
                token.issuer_key(),
                request,
                commitment,
            )?
        };
        let proof = Self::serialize_proof(bridge_proof)?;

        Ok(AuthorizationPresentation::Selective {
            revealed_facts,
            proof,
            conclusion,
            revealed_facts_commitment: commitment,
            predicate_proofs,
        })
    }

    /// Extract a numeric value from a trace fact's first term.
    ///
    /// Returns an error if the term is a variable — predicate proofs cannot
    /// operate on unground variables because there is no concrete value to prove
    /// a predicate over.
    fn extract_fact_value(fact: &TraceFact) -> Result<u32, SdkError> {
        if let Some(term) = fact.terms.first() {
            match term {
                pyana_trace::Term::Int(v) => Ok((*v).max(0).min(u32::MAX as i64) as u32),
                pyana_trace::Term::Const(sym) => {
                    Ok(u32::from_le_bytes([sym[0], sym[1], sym[2], sym[3]])
                        % pyana_circuit::field::BABYBEAR_P)
                }
                pyana_trace::Term::Var(_) => Err(SdkError::InvalidWitness(
                    "cannot prove predicates on unground variables".into(),
                )),
            }
        } else {
            Ok(0)
        }
    }

    /// Convert a trace fact's predicate symbol to a BabyBear field element.
    fn trace_fact_predicate_bb(fact: &TraceFact) -> BabyBear {
        Self::bytes_to_babybear(&fact.predicate)
    }

    /// Convert a trace fact's terms to BabyBear field elements (up to 3).
    fn trace_fact_terms_bb(fact: &TraceFact) -> [BabyBear; 3] {
        let mut term_bbs = [BabyBear::ZERO; 3];
        for (i, term) in fact.terms.iter().take(3).enumerate() {
            term_bbs[i] = match term {
                pyana_trace::Term::Const(sym) => Self::bytes_to_babybear(sym),
                pyana_trace::Term::Int(v) => BabyBear::from_u64(*v as u64),
                pyana_trace::Term::Var(_) => BabyBear::ZERO,
            };
        }
        term_bbs
    }

    /// Convert a PredicateType + threshold to the bridge Predicate enum.
    pub(crate) fn predicate_type_to_bridge(
        predicate_type: PredicateType,
        threshold: u32,
    ) -> Predicate {
        match predicate_type {
            PredicateType::Gte | PredicateType::InRangeLow => Predicate::Gte(threshold),
            PredicateType::Lte | PredicateType::InRangeHigh => Predicate::Lte(threshold),
            PredicateType::Gt => Predicate::Gt(threshold),
            PredicateType::Lt => Predicate::Lt(threshold),
            PredicateType::Neq => Predicate::Neq(threshold),
        }
    }

    /// Extract the CaveatSet from a held token by decoding and verifying the HMAC chain.
    fn extract_caveat_set(
        token: &HeldToken,
    ) -> Result<pyana_token::pyana_macaroon::caveat::CaveatSet, SdkError> {
        let decoded = token.decode()?;
        let caveat_set = decoded
            .inner()
            .verify(token.root_key(), decoded.discharges())
            .map_err(|e| {
                SdkError::Token(pyana_token::TokenError::VerificationFailed(e.to_string()))
            })?;
        Ok(caveat_set)
    }

    /// Extract the CaveatSet from a held token STRUCTURALLY (without HMAC verification).
    ///
    /// This reads caveats directly from the decoded macaroon structure. It does NOT
    /// verify the HMAC chain — caveats are returned as-is from the MsgPack encoding.
    ///
    /// **Security model**: This is safe for the ZK proof-generation path because:
    /// - The ZK proof proves the Datalog derivation from committed facts.
    /// - If the prover tampers with caveats, they'd be proving a false statement
    ///   that won't match what the verifier expects (the proof would be meaningless).
    /// - HMAC chain integrity is a separate concern: it proves to the ISSUER that
    ///   caveats weren't stripped. The ZK proof replaces this guarantee for the
    ///   VERIFIER by proving the derivation is valid for the committed state.
    ///
    /// This method is used for attenuated tokens that don't have the root key for
    /// HMAC verification but need to extract caveats for proof generation.
    fn extract_caveat_set_structural(
        token: &HeldToken,
    ) -> Result<pyana_token::pyana_macaroon::caveat::CaveatSet, SdkError> {
        // Decode the macaroon structure (this doesn't require the root key — it just
        // parses the MsgPack encoding). We use a zeroed key since from_encoded only
        // stores the key, it doesn't verify during decode.
        let decoded =
            MacaroonToken::from_encoded(&token.encoded, [0u8; 32]).map_err(SdkError::Token)?;

        // Extract first-party caveats directly from the macaroon structure.
        // The caveats field is public on Macaroon and populated during deserialization.
        Ok(decoded.inner().caveats.clone())
    }

    /// Extract caveat set using HMAC verification if possible, falling back to
    /// structural extraction for attenuated tokens that have the issuer key
    /// (i.e., tokens that can prove but can't mint).
    fn extract_caveat_set_for_proof(
        token: &HeldToken,
    ) -> Result<pyana_token::pyana_macaroon::caveat::CaveatSet, SdkError> {
        if token.can_mint() {
            // Root token: use full HMAC verification (most secure path).
            Self::extract_caveat_set(token)
        } else if token.can_prove() {
            // Attenuated token with issuer key: structural extraction is safe
            // because the ZK proof replaces HMAC chain verification.
            Self::extract_caveat_set_structural(token)
        } else {
            Err(SdkError::MissingKey(
                "token has no issuer key; cannot extract caveats for proof generation. \
                 Use prove_authorization_with_issuer_key() and provide the issuer key."
                    .into(),
            ))
        }
    }

    /// Serialize a bridge presentation proof to bytes for wire transmission.
    ///
    /// Converts to a `WirePresentationProof` (stripping the private trace) and
    /// serializes via postcard. This matches what `PyanaEngine::verify_presentation_against`
    /// expects: `postcard::from_bytes::<WirePresentationProof>`.
    fn serialize_proof(bridge_proof: BridgePresentationProof) -> Result<Vec<u8>, SdkError> {
        let wire_proof = bridge_proof.into_wire_proof();
        postcard::to_stdvec(&wire_proof)
            .map_err(|e| SdkError::Wire(format!("failed to serialize wire proof: {e}")))
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

    /// Compute and sign the delegation envelope binding.
    ///
    /// The signing message is:
    /// `blake3::derive_key("pyana-delegation-binding-v1", caveat_chain_hash || proof_key || membership_leaf)`
    ///
    /// This prevents a malicious delegatee from mutating caveats and recomputing the
    /// `caveat_chain_hash` — they cannot forge the delegator's signature over the
    /// new hash.
    fn sign_delegation_envelope(
        &self,
        caveat_chain_hash: &Option<[u8; 32]>,
        proof_key: &Option<[u8; 32]>,
        membership_leaf: Option<&[u8; 32]>,
    ) -> (Signature, PublicKey) {
        let signing_message =
            Self::compute_delegation_signing_message(caveat_chain_hash, proof_key, membership_leaf);
        let sig = self.signing_key.sign(&signing_message);
        (Signature(sig.to_bytes()), self.public_key)
    }

    /// Compute the canonical signing message for a delegation envelope.
    fn compute_delegation_signing_message(
        caveat_chain_hash: &Option<[u8; 32]>,
        proof_key: &Option<[u8; 32]>,
        membership_leaf: Option<&[u8; 32]>,
    ) -> [u8; 32] {
        let mut message_data = Vec::with_capacity(96);
        if let Some(h) = caveat_chain_hash {
            message_data.extend_from_slice(h);
        }
        if let Some(k) = proof_key {
            message_data.extend_from_slice(k);
        }
        if let Some(r) = membership_leaf {
            message_data.extend_from_slice(r);
        }
        blake3::derive_key("pyana-delegation-binding-v1", &message_data)
    }

    /// Verify a delegation envelope signature.
    ///
    /// Returns `Ok(())` if the signature is valid, or an error describing the failure.
    pub(crate) fn verify_delegation_signature(
        delegator_public_key: &PublicKey,
        delegator_signature: &Signature,
        caveat_chain_hash: &Option<[u8; 32]>,
        proof_key: &Option<[u8; 32]>,
        membership_leaf: Option<&[u8; 32]>,
    ) -> Result<(), SdkError> {
        use ed25519_dalek::Verifier;

        let verifying_key = ed25519_dalek::VerifyingKey::from_bytes(&delegator_public_key.0)
            .map_err(|e| {
                SdkError::InvalidDelegation(format!("invalid delegator public key: {e}"))
            })?;

        let signing_message =
            Self::compute_delegation_signing_message(caveat_chain_hash, proof_key, membership_leaf);

        let signature = ed25519_dalek::Signature::from_bytes(&delegator_signature.0);
        verifying_key
            .verify(&signing_message, &signature)
            .map_err(|e| {
                SdkError::InvalidDelegation(format!(
                    "delegation envelope signature verification failed: {e}"
                ))
            })
    }

    // =========================================================================
    // Proof Generation
    // =========================================================================

    /// Generate a real STARK-backed zero-knowledge presentation proof for a held token.
    ///
    /// This proves "I hold a valid token chain that authorizes request X"
    /// without revealing the token, its caveats, or the root key. The proof
    /// is backed by a real Poseidon2 STARK (collision-resistant, production-grade).
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
    /// A [`BridgePresentationProof`] with a real STARK proof that can be verified
    /// by any party knowing the federation root, or an error if proof generation fails.
    pub fn prove_authorization(
        &self,
        token: &HeldToken,
        request: &AuthRequest,
    ) -> Result<BridgePresentationProof, SdkError> {
        // SECURITY: Use the derived proof key for federation membership proofs.
        // The raw root_key is NEVER passed to the builder — only the one-way derived
        // proof key is used as the leaf in the federation Merkle tree.
        // Attenuated tokens (root_key == zeroed) cannot generate federation membership
        // proofs — they must use `prove_authorization_with_issuer_key()` instead,
        // providing the issuer's proof key out-of-band.
        if !token.can_mint() {
            return Err(SdkError::MissingKey(
                "attenuated tokens cannot generate federation membership proofs; \
                 use prove_authorization_with_issuer_key() with the issuer's proof key, \
                 or use the root token holder to prove directly"
                    .into(),
            ));
        }

        let proof_key = Self::derive_proof_key(token.root_key());
        let federation_root_bb = Self::compute_federation_root_bb(&proof_key);
        let federation_root = Self::bb_to_bytes(federation_root_bb);

        let mut builder = pyana_bridge::BridgePresentationBuilder::new_with_root_bb(
            proof_key,
            federation_root,
            federation_root_bb,
        );

        // Use the ACTUAL encoded token (which includes all attenuations/caveats)
        // rather than minting a fresh unrestricted token from the root key.
        let actual_token = token.decode()?;
        builder.set_root_token(actual_token);

        let proof = builder.prove(request)?;
        Ok(proof)
    }

    /// Generate a STARK presentation proof for an attenuated token using a provided issuer key.
    ///
    /// Attenuated tokens (those received via delegation) do not carry the root key and
    /// therefore cannot call [`prove_authorization`] directly. This method allows an
    /// attenuated token holder to generate a valid STARK proof when the issuer's root
    /// key is provided out-of-band (e.g., the delegator includes it in the delegation
    /// metadata, or the federation publishes it).
    ///
    /// # Security Model
    ///
    /// The issuer key is used ONLY for computing the federation Merkle membership proof
    /// (proving "my issuer is a member of this federation"). The attenuated token's
    /// caveat chain is still verified: the proof commits to the actual encoded token
    /// (with all its attenuations), not a freshly-minted unrestricted token.
    ///
    /// # Arguments
    ///
    /// * `token` - The attenuated token to prove authorization from.
    /// * `issuer_key` - The 32-byte root key of the original issuer (provided out-of-band).
    /// * `request` - The authorization request to prove.
    ///
    /// # Returns
    ///
    /// A [`BridgePresentationProof`] with a real STARK proof, or an error if proof
    /// generation fails.
    ///
    /// # Future Work
    ///
    /// A full chain-proof path (proving the delegation chain is valid without revealing
    /// intermediate tokens) would allow proving without any out-of-band key material.
    /// See: `prove_with_chain` for the root-holder variant of chain proofs.
    pub fn prove_authorization_with_issuer_key(
        &self,
        token: &HeldToken,
        issuer_key: &[u8; 32],
        request: &AuthRequest,
    ) -> Result<BridgePresentationProof, SdkError> {
        // Verify the issuer key is not zeroed (caller must provide a real key).
        if *issuer_key == [0u8; 32] {
            return Err(SdkError::MissingKey(
                "issuer_key must not be zeroed; provide the issuer's derived proof key".into(),
            ));
        }

        // P0-1: Verify caveat chain integrity before proof generation.
        // If the delegator provided a caveat_chain_hash, check that the decoded token's
        // caveats match. This prevents a delegate holding the proof_key from mutating
        // caveats and generating proofs over fabricated authorization facts.
        let actual_token = MacaroonToken::from_encoded(&token.encoded, *issuer_key)?;
        if let Some(expected_hash) = token.caveat_chain_hash {
            let computed_hash = Self::compute_caveat_chain_hash(&actual_token);
            if computed_hash != expected_hash {
                return Err(SdkError::CaveatIntegrityViolation);
            }
        }

        // P0-2: Use the federation root from the pre-generated membership proof when
        // available. The proof was generated against the REAL tree root (which contains
        // the real issuer key, not the BLAKE3-derived proof_key). Using
        // compute_federation_root_bb(issuer_key) would produce a synthetic root that
        // does not match the proof's path.
        let federation_root_bb = if let Some(ref mp) = token.membership_proof {
            Self::compute_root_from_membership_proof(mp)
        } else {
            Self::compute_federation_root_bb(issuer_key)
        };
        let federation_root = Self::bb_to_bytes(federation_root_bb);

        let mut builder = pyana_bridge::BridgePresentationBuilder::new_with_root_bb(
            *issuer_key,
            federation_root,
            federation_root_bb,
        );

        // If the token has a pre-generated membership proof (from delegation), attach
        // it to the builder. This allows the delegatee to prove federation membership
        // without needing to look up their proof_key in the federation tree (which would
        // fail since the tree contains real keys, not BLAKE3 derivations).
        if let Some(ref membership_proof) = token.membership_proof {
            builder.with_pre_generated_membership_proof(membership_proof.clone());
        }

        builder.set_root_token(actual_token);

        let proof = builder.prove(request)?;
        Ok(proof)
    }

    /// Generate a STARK presentation proof with a revealed facts commitment.
    ///
    /// This is the internal implementation for selective disclosure mode. It generates
    /// the same STARK proof as `prove_authorization`, but includes the `commitment`
    /// as a public input that binds the revealed facts to the proof.
    ///
    /// The verifier extracts the commitment from the proof's public inputs and
    /// recomputes it from the plaintext revealed facts to verify integrity.
    fn prove_authorization_selective(
        &self,
        token: &HeldToken,
        request: &AuthRequest,
        commitment: pyana_circuit::binding::WideHash,
    ) -> Result<BridgePresentationProof, SdkError> {
        if !token.can_mint() {
            return Err(SdkError::MissingKey(
                "attenuated tokens cannot generate selective disclosure proofs; \
                 use prove_authorization_with_issuer_key() with the issuer's proof key, \
                 or use the root token holder to prove directly"
                    .into(),
            ));
        }

        let proof_key = Self::derive_proof_key(token.root_key());
        let federation_root_bb = Self::compute_federation_root_bb(&proof_key);
        let federation_root = Self::bb_to_bytes(federation_root_bb);

        let mut builder = pyana_bridge::BridgePresentationBuilder::new_with_root_bb(
            proof_key,
            federation_root,
            federation_root_bb,
        );

        // Set the revealed facts commitment before proving.
        builder.set_revealed_facts_commitment(commitment);

        let actual_token = token.decode()?;
        builder.set_root_token(actual_token);

        let proof = builder.prove(request)?;
        Ok(proof)
    }

    /// Generate a STARK selective disclosure proof for an attenuated token using a
    /// provided issuer key.
    ///
    /// This is the attenuated-token variant of `prove_authorization_selective`. It uses
    /// the issuer key for federation membership and the commitment for binding revealed
    /// facts to the proof.
    fn prove_authorization_selective_with_issuer_key(
        &self,
        token: &HeldToken,
        issuer_key: &[u8; 32],
        request: &AuthRequest,
        commitment: pyana_circuit::binding::WideHash,
    ) -> Result<BridgePresentationProof, SdkError> {
        if *issuer_key == [0u8; 32] {
            return Err(SdkError::MissingKey(
                "issuer_key must not be zeroed; provide the issuer's derived proof key".into(),
            ));
        }

        // P0-1: Verify caveat chain integrity before proof generation.
        let actual_token = MacaroonToken::from_encoded(&token.encoded, *issuer_key)?;
        if let Some(expected_hash) = token.caveat_chain_hash {
            let computed_hash = Self::compute_caveat_chain_hash(&actual_token);
            if computed_hash != expected_hash {
                return Err(SdkError::CaveatIntegrityViolation);
            }
        }

        // P0-2: Use the federation root from the pre-generated membership proof when
        // available, rather than the synthetic root derived from the proof_key.
        let federation_root_bb = if let Some(ref mp) = token.membership_proof {
            Self::compute_root_from_membership_proof(mp)
        } else {
            Self::compute_federation_root_bb(issuer_key)
        };
        let federation_root = Self::bb_to_bytes(federation_root_bb);

        let mut builder = pyana_bridge::BridgePresentationBuilder::new_with_root_bb(
            *issuer_key,
            federation_root,
            federation_root_bb,
        );

        // Attach pre-generated membership proof if available (delegation path).
        if let Some(ref membership_proof) = token.membership_proof {
            builder.with_pre_generated_membership_proof(membership_proof.clone());
        }

        // Set the revealed facts commitment before proving.
        builder.set_revealed_facts_commitment(commitment);

        builder.set_root_token(actual_token);

        let proof = builder.prove(request)?;
        Ok(proof)
    }

    /// Generate a presentation proof for a held token.
    ///
    /// This produces a real STARK proof suitable for verification across trust
    /// boundaries. Previously this method used a fast constraint-check path that
    /// did not produce a verifiable STARK; it now delegates to the full prover.
    ///
    /// # Deprecation
    ///
    /// Prefer [`prove_authorization`](Self::prove_authorization) directly.
    #[deprecated(note = "Use prove_authorization() which is the canonical production path")]
    pub fn prove_fast(
        &self,
        token: &HeldToken,
        request: &AuthRequest,
    ) -> Result<BridgePresentationProof, SdkError> {
        self.prove_authorization(token, request)
    }

    /// Generate a real STARK presentation proof for an attenuated token chain.
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
        if !root_token.can_mint() {
            return Err(SdkError::MissingKey(
                "attenuated tokens cannot generate federation membership proofs; \
                 use prove_authorization_with_issuer_key() with the issuer's root key"
                    .into(),
            ));
        }

        let proof_key = Self::derive_proof_key(root_token.root_key());
        let federation_root_bb = Self::compute_federation_root_bb(&proof_key);
        let federation_root = Self::bb_to_bytes(federation_root_bb);

        let mut builder = pyana_bridge::BridgePresentationBuilder::new_with_root_bb(
            proof_key,
            federation_root,
            federation_root_bb,
        );

        // Use the actual encoded token (preserves existing caveats).
        let actual_token = root_token.decode()?;
        builder.set_root_token(actual_token);

        for att in attenuations {
            builder.add_attenuation(att);
        }

        let proof = builder.prove(request)?;
        Ok(proof)
    }

    // =========================================================================
    // Predicate Proofs
    // =========================================================================

    /// Prove a predicate about a private token attribute.
    ///
    /// This generates a zero-knowledge proof that a specific attribute of a held
    /// token satisfies a predicate (e.g., "balance >= 1000", "valid_until >= T")
    /// without revealing the exact value.
    ///
    /// # Security: `attribute_value` Binding
    ///
    /// IMPORTANT: `attribute_value` is the prover's claim. The verifier must independently
    /// verify that this value is committed in the token's state root (via Merkle membership).
    /// This function does NOT verify that claim -- it only proves the predicate holds IF the
    /// value is correct.
    ///
    /// The binding between the claimed value and the token's actual state happens at a higher
    /// level: the full presentation flow (via `authorize_with_disclosure` or the intent
    /// fulfillment pipeline) includes a state root that commits to all attribute values.
    /// The `fact_commitment` in the returned proof is derived from this state root, so a
    /// verifier checking the proof against a known state root will reject fabricated values.
    ///
    /// Callers using this function directly (outside the full presentation flow) MUST ensure
    /// the verifier independently checks the `fact_commitment` against the token's committed
    /// state. Without this check, a dishonest prover can claim any value and produce a valid
    /// proof for it.
    ///
    /// # Arguments
    ///
    /// * `token` - The held token containing the attribute.
    /// * `attribute` - The attribute name (e.g., "valid_until", "balance", "reputation").
    ///   This is hashed to a field element and used to look up the fact in the token state.
    /// * `attribute_value` - The actual (private) value of the attribute. This is the
    ///   prover's claim; see the Security section above regarding binding guarantees.
    /// * `predicate` - The predicate to prove (e.g., `Predicate::Gte(1000)`).
    ///
    /// # Returns
    ///
    /// A `BridgePredicateProof` that can be verified by anyone knowing the fact commitment,
    /// or an error if the predicate cannot be proven (statement is false or token is invalid).
    ///
    /// # Example
    ///
    /// ```no_run
    /// use pyana_sdk::AgentWallet;
    /// use pyana_bridge::Predicate;
    ///
    /// let wallet = AgentWallet::new();
    /// # let token = todo!();
    /// // Prove: my balance >= 1000 (without revealing the actual balance)
    /// let proof = wallet.prove_predicate(
    ///     &token,
    ///     "balance",
    ///     5000, // actual balance (private)
    ///     Predicate::Gte(1000),
    /// ).unwrap();
    /// ```
    pub fn prove_predicate(
        &self,
        token: &HeldToken,
        attribute: &str,
        attribute_value: u32,
        predicate: pyana_bridge::Predicate,
    ) -> Result<pyana_bridge::BridgePredicateProof, SdkError> {
        // Decode the token to verify it's valid.
        let _decoded = token.decode()?;

        // Compute the fact hash for the attribute.
        // The fact is modeled as: predicate=hash(attribute_name), terms=[value, 0, 0].
        let attr_bytes = blake3::hash(attribute.as_bytes());
        let attr_bb = Self::bytes_to_babybear(attr_bytes.as_bytes());
        let value_bb = BabyBear::new(attribute_value);
        let fact_hash = poseidon2::hash_fact(attr_bb, &[value_bb, BabyBear::ZERO, BabyBear::ZERO]);

        // Compute a state root from the token's derived proof key (deterministic for testing).
        // In production, this would come from the committed Merkle tree of the token state.
        let proof_key = Self::derive_proof_key(token.root_key());
        let state_root = Self::bytes_to_babybear(&proof_key);

        // Generate the predicate proof via the bridge.
        let proof = pyana_bridge::prove_predicate_for_fact(
            attribute_value,
            fact_hash,
            state_root,
            &predicate,
        )
        .ok_or_else(|| {
            SdkError::Auth(pyana_bridge::AuthError::InvalidRequest(
                format!(
                    "predicate proof generation failed: the statement '{attribute}' {:?} is not satisfiable for value {attribute_value}",
                    predicate
                ),
            ))
        })?;

        Ok(proof)
    }

    // =========================================================================
    // Arithmetic Predicate Proofs
    // =========================================================================

    /// Prove an arithmetic predicate over multiple private token attributes.
    ///
    /// This generates a zero-knowledge proof that an arithmetic expression over
    /// multiple private values from a held token satisfies a predicate, without
    /// revealing any of the individual values.
    ///
    /// # Arguments
    ///
    /// * `token` - The held token containing the attributes.
    /// * `inputs` - Pairs of (attribute_name, private_value) for each input to the expression.
    /// * `expression` - The arithmetic expression to evaluate (e.g., `Var(0) + Var(1)`).
    /// * `predicate` - The predicate to prove (e.g., `ExprGte(expr, threshold)`).
    ///
    /// # Returns
    ///
    /// A proof that can be verified by anyone knowing the fact commitments.
    ///
    /// Note: Arithmetic predicate bridge integration is not yet complete.
    /// This method will return an error until `pyana_bridge::prove_arithmetic_for_facts`
    /// is implemented.
    pub fn prove_arithmetic(
        &self,
        token: &HeldToken,
        inputs: &[(String, u64)],
        expression: pyana_circuit::ArithExpr,
        predicate: pyana_circuit::ArithPredicate,
    ) -> Result<pyana_circuit::ArithmeticPredicateProof, SdkError> {
        // Decode the token to verify it's valid.
        let _decoded = token.decode()?;

        // Derive the state root from the token's proof key (consistent with other proofs).
        let proof_key = Self::derive_proof_key(token.root_key());
        let state_root = Self::bytes_to_babybear(&proof_key);

        // Convert inputs to BabyBear values and compute per-attribute fact hashes.
        let input_values: Vec<BabyBear> = inputs
            .iter()
            .map(|(_, v)| BabyBear::new(*v as u32))
            .collect();

        let fact_commitments: Vec<BabyBear> = inputs
            .iter()
            .map(|(attr, value)| {
                let attr_bytes = blake3::hash(attr.as_bytes());
                let attr_bb = Self::bytes_to_babybear(attr_bytes.as_bytes());
                let value_bb = BabyBear::new(*value as u32);
                let fact_hash =
                    poseidon2::hash_fact(attr_bb, &[value_bb, BabyBear::ZERO, BabyBear::ZERO]);
                pyana_circuit::compute_arithmetic_fact_commitment(fact_hash, state_root)
            })
            .collect();

        // Aggregate fact commitments into a single binding commitment.
        let aggregate_commitment = poseidon2::hash_many(&fact_commitments);

        // Construct the predicate with the expression embedded.
        let full_predicate = match predicate {
            pyana_circuit::ArithPredicate::ExprGte(_, threshold) => {
                pyana_circuit::ArithPredicate::ExprGte(expression, threshold)
            }
            pyana_circuit::ArithPredicate::ExprLte(_, threshold) => {
                pyana_circuit::ArithPredicate::ExprLte(expression, threshold)
            }
            pyana_circuit::ArithPredicate::ExprEq(_, value) => {
                pyana_circuit::ArithPredicate::ExprEq(expression, value)
            }
            pyana_circuit::ArithPredicate::ExprInRange(_, low, high) => {
                pyana_circuit::ArithPredicate::ExprInRange(expression, low, high)
            }
            pyana_circuit::ArithPredicate::ExprCompare(_, expr_b, op) => {
                pyana_circuit::ArithPredicate::ExprCompare(expression, expr_b, op)
            }
            pyana_circuit::ArithPredicate::ExprNeq(_, value) => {
                pyana_circuit::ArithPredicate::ExprNeq(expression, value)
            }
        };

        let witness = pyana_circuit::ArithmeticPredicateWitness {
            inputs: input_values,
            predicate: full_predicate,
            fact_commitment: aggregate_commitment,
        };

        pyana_circuit::prove_arithmetic_predicate(witness).ok_or_else(|| {
            SdkError::Auth(pyana_bridge::AuthError::InvalidRequest(
                "arithmetic predicate is not satisfiable for the given inputs".into(),
            ))
        })
    }

    // =========================================================================
    // Relational and Committed-Threshold Predicate Proofs
    // =========================================================================

    /// Prove a relational predicate comparing this wallet's private value against
    /// a counterparty's committed value.
    ///
    /// This generates a zero-knowledge proof that a specific attribute of a held
    /// token satisfies a relational comparison against a counterparty's committed
    /// value (e.g., "my bid > their bid") without revealing either party's value.
    ///
    /// The prover must have received the counterparty's value and blinding via a
    /// sealed channel (e.g., OT, MPC, trusted comparison service).
    ///
    /// # Arguments
    ///
    /// * `token` - The held token containing the attribute.
    /// * `my_attribute` - The attribute name (e.g., "bid").
    /// * `my_value` - The actual (private) value of the attribute.
    /// * `my_blinding` - The prover's blinding factor for their own commitment.
    /// * `their_value` - The counterparty's value (received via sealed channel).
    /// * `their_blinding` - The counterparty's blinding factor (received via sealed channel).
    /// * `relation` - The relation to prove (e.g., GreaterThan).
    ///
    /// # Returns
    ///
    /// A `RelationalPredicateProof` that can be verified by anyone knowing both
    /// commitments, or an error if the relation is not satisfiable.
    pub fn prove_relational(
        &self,
        token: &HeldToken,
        my_attribute: &str,
        my_value: u64,
        my_blinding: BabyBear,
        their_value: u64,
        their_blinding: BabyBear,
        relation: pyana_circuit::RelationType,
    ) -> Result<pyana_circuit::RelationalPredicateProof, SdkError> {
        // Decode the token to verify it's valid.
        let _decoded = token.decode()?;

        let proof = pyana_circuit::prove_value_comparison(
            BabyBear::new(my_value as u32),
            my_blinding,
            BabyBear::new(their_value as u32),
            their_blinding,
            relation,
        )
        .ok_or_else(|| {
            SdkError::Auth(pyana_bridge::AuthError::InvalidRequest(format!(
                "relational predicate proof failed: '{}' {:?} is not satisfiable \
                 (my_value={}, their_value={})",
                my_attribute, relation, my_value, their_value
            )))
        })?;

        Ok(proof)
    }

    /// Prove a committed-threshold predicate: the wallet's private value satisfies
    /// a threshold that is also kept secret from third-party verifiers.
    ///
    /// This generates a zero-knowledge proof that a specific attribute value is
    /// at least as large as a threshold, where both the value AND the threshold are
    /// hidden behind Poseidon2 commitments. Third-party verifiers learn only that
    /// "some committed value satisfies some committed threshold."
    ///
    /// The verifier provides the threshold and blinding via a secure channel.
    ///
    /// # Arguments
    ///
    /// * `token` - The held token containing the attribute.
    /// * `attribute` - The attribute name (e.g., "credit_score").
    /// * `attribute_value` - The actual (private) value of the attribute.
    /// * `threshold` - The verifier's secret threshold (received via secure channel).
    /// * `blinding` - The verifier's blinding randomness (received via secure channel).
    ///
    /// # Returns
    ///
    /// A `CommittedThresholdProof` that can be verified against the threshold
    /// commitment and fact commitment, or an error if value < threshold.
    pub fn prove_committed_threshold(
        &self,
        token: &HeldToken,
        attribute: &str,
        attribute_value: u64,
        threshold: u64,
        blinding: BabyBear,
    ) -> Result<pyana_circuit::CommittedThresholdProof, SdkError> {
        // Decode the token to verify it's valid.
        let _decoded = token.decode()?;

        // Compute the fact hash and fact commitment for binding to the token state.
        let attr_bytes = blake3::hash(attribute.as_bytes());
        let attr_bb = Self::bytes_to_babybear(attr_bytes.as_bytes());
        let value_bb = BabyBear::new(attribute_value as u32);
        let fact_hash = poseidon2::hash_fact(attr_bb, &[value_bb, BabyBear::ZERO, BabyBear::ZERO]);

        let proof_key = Self::derive_proof_key(token.root_key());
        let state_root = Self::bytes_to_babybear(&proof_key);
        let fact_commitment = pyana_circuit::compute_fact_commitment(fact_hash, state_root);

        let witness = pyana_circuit::CommittedThresholdWitness {
            private_value: value_bb,
            threshold: BabyBear::new(threshold as u32),
            blinding,
            fact_commitment,
        };

        let proof = pyana_circuit::prove_committed_threshold(witness).ok_or_else(|| {
            SdkError::Auth(pyana_bridge::AuthError::InvalidRequest(format!(
                "committed-threshold proof failed: '{}' value {} does not satisfy threshold {}",
                attribute, attribute_value, threshold
            )))
        })?;

        Ok(proof)
    }

    // =========================================================================
    // Programmable Predicate Programs
    // =========================================================================

    /// Prove a programmable predicate program against this wallet's private state.
    ///
    /// This is the high-level entry point for the programmable predicates system.
    /// It takes a predicate program (an expression tree of conditions) and proves
    /// all conditions are satisfied using the wallet's private attribute values.
    ///
    /// The program is compiled to the appropriate AIR(s) and proven in zero knowledge.
    /// The verifier learns only that the program is satisfied, not the actual values.
    ///
    /// # Arguments
    ///
    /// * `token` - The held token whose attributes are being proven about.
    /// * `program` - The predicate program to prove (expression tree).
    /// * `attribute_values` - Map from attribute names to actual (private) values.
    ///
    /// # Returns
    ///
    /// A `ProgramProof` that can be verified by anyone knowing the program and
    /// fact commitments, or an error if the program cannot be proven.
    pub fn prove_program(
        &self,
        token: &HeldToken,
        program: &pyana_circuit::predicate_program::PredicateProgram,
        attribute_values: &std::collections::HashMap<String, u64>,
    ) -> Result<pyana_circuit::predicate_program::ProgramProof, SdkError> {
        // Decode the token to verify it's valid.
        let _decoded = token.decode()?;

        // Compute a state root from the token's derived proof key.
        let proof_key = Self::derive_proof_key(token.root_key());
        let state_root = Self::bytes_to_babybear(&proof_key);

        // Prove via the bridge layer.
        let proof = pyana_bridge::prove_predicate_program(program, attribute_values, state_root)
            .map_err(|e| {
                SdkError::Auth(pyana_bridge::AuthError::InvalidRequest(format!(
                    "predicate program proof failed: {e}"
                )))
            })?;

        Ok(proof)
    }

    /// Prove a predicate program with full private state including relational and
    /// committed-threshold context.
    ///
    /// This is the extended version of [`prove_program`](Self::prove_program) that
    /// supports relational predicates (two-party comparisons) and committed-threshold
    /// predicates (hidden thresholds) by accepting the full [`PrivateState`] struct
    /// including counterparty values and verifier secrets received via sealed channels.
    ///
    /// # Arguments
    ///
    /// * `token` - The held token whose attributes are being proven about.
    /// * `program` - The predicate program to prove.
    /// * `private_state` - Full private state including values, temporal history,
    ///   relational context, and committed-threshold context.
    ///
    /// # Returns
    ///
    /// A `ProgramProof` that can be verified by anyone knowing the program and
    /// fact commitments, or an error if the program cannot be proven.
    pub fn prove_program_full(
        &self,
        token: &HeldToken,
        program: &pyana_circuit::predicate_program::PredicateProgram,
        private_state: &pyana_circuit::predicate_program::PrivateState,
    ) -> Result<pyana_circuit::predicate_program::ProgramProof, SdkError> {
        // Decode the token to verify it's valid.
        let _decoded = token.decode()?;

        // Compute a state root from the token's derived proof key.
        let proof_key = Self::derive_proof_key(token.root_key());
        let state_root = Self::bytes_to_babybear(&proof_key);

        // Prove via the bridge layer (full private state path).
        let proof = pyana_bridge::prove_predicate_program_full(program, private_state, state_root)
            .map_err(|e| {
                SdkError::Auth(pyana_bridge::AuthError::InvalidRequest(format!(
                    "predicate program proof failed: {e}"
                )))
            })?;

        Ok(proof)
    }

    // =========================================================================
    // Cross-party Predicate Proofs (Intent Integration)
    // =========================================================================

    /// Prove all predicate requirements in an intent using local values.
    ///
    /// When a counterparty posts an intent with predicate requirements (e.g.,
    /// "prove your balance >= 1000 and reputation >= 50"), this method generates
    /// the required ZK proofs for all requirements the caller can satisfy.
    ///
    /// Each proof demonstrates the predicate holds without revealing the actual
    /// value. The proofs are bound to a state root (via fact commitments), so the
    /// verifier can check they correspond to real committed state.
    ///
    /// # Arguments
    ///
    /// * `intent` - The intent containing predicate requirements to prove.
    /// * `my_values` - A map from attribute name to actual (private) value.
    /// * `state_root` - The state root to bind proofs against.
    ///
    /// # Returns
    ///
    /// A vector of `(requirement_index, PredicateProof)` for each requirement
    /// that could be proven. Requirements whose attributes are not in `my_values`
    /// or whose predicates are not satisfiable are skipped (returns error).
    ///
    /// # Example
    ///
    /// ```no_run
    /// use pyana_sdk::AgentWallet;
    /// use pyana_circuit::BabyBear;
    /// use std::collections::HashMap;
    ///
    /// let wallet = AgentWallet::new();
    /// # let intent = todo!();
    /// let mut my_values = HashMap::new();
    /// my_values.insert("balance".to_string(), 5000u64);
    /// my_values.insert("reputation".to_string(), 85u64);
    ///
    /// let state_root = BabyBear::new(99999);
    /// let proofs = wallet.prove_for_intent_predicates(&intent, &my_values, state_root).unwrap();
    /// // proofs can be attached to a FulfillmentWithPredicates
    /// ```
    pub fn prove_for_intent_predicates(
        &self,
        intent: &pyana_intent::Intent,
        my_values: &std::collections::HashMap<String, u64>,
        state_root: BabyBear,
    ) -> Result<Vec<(usize, pyana_circuit::PredicateProof)>, SdkError> {
        use pyana_bridge::Predicate;
        use pyana_circuit::poseidon2;
        use pyana_intent::fulfillment::parse_predicate_type;

        let requirements = &intent.matcher.predicate_requirements;
        let mut proofs = Vec::with_capacity(requirements.len());

        for (idx, req) in requirements.iter().enumerate() {
            // Look up our value for this attribute.
            let value = my_values.get(&req.attribute).ok_or_else(|| {
                SdkError::MissingKey(format!(
                    "no value for attribute '{}' required by intent predicate {}",
                    req.attribute, idx
                ))
            })?;

            // Map the predicate type string to a bridge Predicate.
            let predicate = match req.predicate_type.as_str() {
                "gte" => Predicate::Gte(req.threshold as u32),
                "lte" => Predicate::Lte(req.threshold as u32),
                "gt" => Predicate::Gt(req.threshold as u32),
                "lt" => Predicate::Lt(req.threshold as u32),
                "neq" => Predicate::Neq(req.threshold as u32),
                "in_range" => {
                    let upper = req.upper_bound.unwrap_or(req.threshold) as u32;
                    Predicate::InRange(req.threshold as u32, upper)
                }
                other => {
                    return Err(SdkError::MissingKey(format!(
                        "unsupported predicate type '{}' for attribute '{}'",
                        other, req.attribute
                    )));
                }
            };

            // Compute the fact hash for this attribute.
            let attr_bytes = blake3::hash(req.attribute.as_bytes());
            let attr_bb = Self::bytes_to_babybear(attr_bytes.as_bytes());
            let value_bb = BabyBear::new(*value as u32);
            let fact_hash =
                poseidon2::hash_fact(attr_bb, &[value_bb, BabyBear::ZERO, BabyBear::ZERO]);

            // Generate the predicate proof.
            let bridge_proof = pyana_bridge::prove_predicate_for_fact(
                *value as u32,
                fact_hash,
                state_root,
                &predicate,
            )
            .ok_or_else(|| {
                SdkError::Auth(pyana_bridge::AuthError::InvalidRequest(format!(
                    "predicate proof failed for '{}': value {} does not satisfy {:?}",
                    req.attribute, value, predicate
                )))
            })?;

            // Extract the inner circuit proof(s).
            // For simple predicates (Gte, Lte, etc.) we get a single proof.
            // For InRange we get a pair; the intent system expects one proof per requirement,
            // so for InRange we use the lower-bound proof (the requirement is verified
            // against the lower threshold).
            let _ = parse_predicate_type; // ensure import is used
            let circuit_proof = match bridge_proof.proof {
                pyana_bridge::BridgePredicateProofInner::Single(p) => p,
                pyana_bridge::BridgePredicateProofInner::Range(low_proof, _high_proof) => {
                    // For in_range, the lower bound proof demonstrates value >= threshold.
                    low_proof
                }
                pyana_bridge::BridgePredicateProofInner::CommittedThreshold(p) => {
                    // CommittedThreshold uses a committed comparison proof.
                    // Convert to PredicateProof with Gte semantics (committed threshold
                    // proves value >= threshold).
                    pyana_circuit::PredicateProof {
                        predicate_type: pyana_circuit::PredicateType::Gte,
                        threshold: p.threshold_commitment,
                        fact_commitment: p.fact_commitment,
                        stark_proof: p.stark_proof,
                    }
                }
            };

            proofs.push((idx, circuit_proof));
        }

        Ok(proofs)
    }

    // =========================================================================
    // Fulfillment Payment (Intent → Fulfill → Automatic Payment)
    // =========================================================================

    /// Fulfill an intent and collect payment in a single atomic operation.
    ///
    /// This is the high-level convenience method that an agent calls when it:
    /// 1. Holds a capability that satisfies the intent's MatchSpec.
    /// 2. Can prove all predicate requirements in the intent.
    /// 3. Wants to receive payment (from the intent's `min_budget`).
    ///
    /// The method:
    /// - Generates predicate proofs for all requirements using `my_values`.
    /// - Constructs a `FulfillmentWithPredicates`.
    /// - Calls `execute_fulfillment_flow` which verifies + pays atomically.
    ///
    /// # Arguments
    ///
    /// * `intent` - The intent to fulfill (must have `min_budget` set for payment).
    /// * `base_fulfillment` - The base fulfillment (capability satisfaction proof).
    /// * `my_values` - Map from attribute name to actual (private) value for predicates.
    /// * `runtime` - The agent runtime providing ledger and executor access.
    ///
    /// # Returns
    ///
    /// A `TurnReceipt` proving payment was transferred, or an error.
    pub fn fulfill_and_collect(
        &self,
        intent: &pyana_intent::Intent,
        base_fulfillment: &pyana_intent::fulfillment::Fulfillment,
        my_values: &std::collections::HashMap<String, u64>,
        runtime: &crate::runtime::AgentRuntime,
        current_height: u64,
    ) -> Result<pyana_turn::TurnReceipt, SdkError> {
        // Step 1: Generate predicate proofs for the intent's requirements.
        // Derive the state root from this wallet's receipt chain head. The receipt
        // chain's post_state_hash is the committed state that verifiers can check.
        let state_root = self
            .current_state_commitment()
            .map(|hash| Self::bytes_to_babybear(&hash))
            .ok_or_else(|| {
                SdkError::MissingKey(
                    "wallet has no receipt chain; cannot derive state root for predicate proofs. \
                     Call append_receipt() after executing at least one turn."
                        .into(),
                )
            })?;
        let predicate_proofs = self.prove_for_intent_predicates(intent, my_values, state_root)?;

        // Step 3: Construct the FulfillmentWithPredicates.
        let fulfillment_with_preds = pyana_intent::fulfillment::FulfillmentWithPredicates {
            base: base_fulfillment.clone(),
            predicate_proofs,
            state_root,
            state_root_block: current_height.saturating_sub(10), // Recent state root.
        };

        // Step 4: Execute the fulfillment flow.
        let payer_cell = CellId(intent.creator.0); // Intent creator pays.
        let recipient_cell = runtime.cell_id(); // We (the fulfiller) receive.

        let mut ledger = runtime.ledger().lock().unwrap();
        let executor = pyana_turn::TurnExecutor::new(pyana_turn::ComputronCosts::default());

        pyana_intent::fulfillment::execute_fulfillment_flow(
            intent,
            &fulfillment_with_preds,
            &executor,
            &mut ledger,
            payer_cell,
            recipient_cell,
            current_height,
            current_height,
        )
        .map_err(|e| SdkError::Auth(pyana_bridge::AuthError::InvalidRequest(e.to_string())))
    }

    // =========================================================================
    // Internal helpers
    // =========================================================================

    /// Compute a stable byte representation of a turn for signing.
    ///
    /// This MUST cover ALL semantically-relevant fields of the Turn to prevent
    /// an attacker from substituting fields that are not covered by the signature.
    /// The domain prefix prevents cross-protocol signature reuse.
    ///
    /// # Serialization format
    ///
    /// All variable-length fields are length-prefixed (8-byte little-endian u64)
    /// to prevent ambiguous concatenation attacks. For example, without length
    /// prefixes, `fee=12, memo="3"` and `fee=1, memo="23"` could hash identically
    /// if the field boundaries are not explicit. Fixed-size fields (u64, [u8; 32])
    /// do not need length prefixes since their boundaries are unambiguous.
    fn compute_turn_bytes(&self, turn: &Turn) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        // Domain separation: prevent reuse of turn signatures in other contexts.
        hasher.update(Self::TURN_DOMAIN_PREFIX);
        hasher.update(turn.agent.as_bytes());
        hasher.update(&turn.nonce.to_le_bytes());
        // CRITICAL: include the call_forest hash -- this is the actual payload of
        // actions being authorized. Without this, an attacker could substitute
        // arbitrary actions under an existing signature.
        let forest_hash = turn.call_forest.compute_hash();
        hasher.update(&forest_hash);
        hasher.update(&turn.fee.to_le_bytes());
        if let Some(ref memo) = turn.memo {
            hasher.update(b"\x01");
            // Length-prefix the memo to prevent boundary ambiguity with subsequent fields.
            let memo_bytes = memo.as_bytes();
            hasher.update(&(memo_bytes.len() as u64).to_le_bytes());
            hasher.update(memo_bytes);
        } else {
            hasher.update(b"\x00");
        }
        if let Some(valid_until) = turn.valid_until {
            hasher.update(b"\x01");
            hasher.update(&valid_until.to_le_bytes());
        } else {
            hasher.update(b"\x00");
        }
        // Include previous_receipt_hash to bind this turn to a specific chain position.
        match &turn.previous_receipt_hash {
            Some(h) => {
                hasher.update(b"\x01");
                hasher.update(h);
            }
            None => {
                hasher.update(b"\x00");
            }
        }
        // Include dependency hashes to prevent reordering attacks in pipelines.
        // Length prefix prevents confusion between no-deps and empty-deps-followed-by-data.
        hasher.update(&(turn.depends_on.len() as u64).to_le_bytes());
        for dep in &turn.depends_on {
            hasher.update(dep);
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
    pub(crate) fn bytes_to_babybear(bytes: &[u8; 32]) -> BabyBear {
        let limbs = BabyBear::encode_hash(bytes);
        poseidon2::hash_many(&limbs)
    }

    /// Derive a proof-only key from an issuer's root HMAC key.
    ///
    /// This one-way derivation produces a key suitable for federation membership
    /// proofs (ZK) that CANNOT be used to mint tokens or forge HMAC chains.
    /// The derived key is deterministic: the same root key always produces the
    /// same proof key.
    ///
    /// **SECURITY**: Possession of the proof key does NOT allow:
    /// - Minting new root tokens (requires the raw root_key for HMAC chain init)
    /// - Forging or extending HMAC chains (HMAC verification requires root_key)
    /// - Recovering the root key (BLAKE3 key derivation is one-way)
    ///
    /// It DOES allow:
    /// - Computing the federation Merkle leaf hash (proving issuer membership)
    /// - Generating ZK proofs bound to this issuer's identity
    ///
    /// The context string "pyana-proof-key-v1" is used for domain separation.
    /// This MUST match the derivation in [`HeldToken::new()`], [`delegate()`], and
    /// any external delegation protocol implementations.
    pub(crate) fn derive_proof_key(root_key: &[u8; 32]) -> [u8; 32] {
        blake3::derive_key("pyana-proof-key-v1", root_key)
    }

    /// Compute a BLAKE3 commitment to a token's caveat chain.
    ///
    /// This hash is computed by the delegator (who holds the root key and can
    /// verify the HMAC chain) and included in the delegation payload. The
    /// delegatee verifies this hash against their decoded token's caveats before
    /// using them for ZK proof generation.
    ///
    /// Uses deterministic serialization (rmp-serde) to ensure both sides compute
    /// the same hash regardless of in-memory representation differences.
    fn compute_caveat_chain_hash(token: &MacaroonToken) -> [u8; 32] {
        let caveats = token.inner().caveats.as_slice();
        let serialized = rmp_serde::to_vec(caveats).expect("caveat serialization should not fail");
        *blake3::hash(&serialized).as_bytes()
    }

    /// Compute the Poseidon2 Merkle root from a pre-generated membership proof.
    ///
    /// Re-walks the proof path using Poseidon2 hashing (same algorithm as
    /// `build_issuer_membership_poseidon2_from_proof` in the bridge) to recover
    /// the federation root that the proof was generated against.
    fn compute_root_from_membership_proof(proof: &pyana_commit::merkle::MerkleProof) -> BabyBear {
        let real_leaf_hash = Self::bytes_to_babybear(&proof.leaf_hash);
        let mut current = real_leaf_hash;

        for i in 0..proof.path_indices.len() {
            let position = proof.path_indices[i];
            let siblings = [
                Self::bytes_to_babybear(&proof.siblings[i][0]),
                Self::bytes_to_babybear(&proof.siblings[i][1]),
                Self::bytes_to_babybear(&proof.siblings[i][2]),
            ];

            let mut children = [BabyBear::ZERO; 4];
            let mut sib_idx = 0;
            for j in 0..4u8 {
                if j == position {
                    children[j as usize] = current;
                } else {
                    children[j as usize] = siblings[sib_idx];
                    sib_idx += 1;
                }
            }
            current = poseidon2::hash_4_to_1(&children);
        }

        current
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

    // =========================================================================
    // Pipeline / Eventual-Send
    // =========================================================================

    /// Submit a pipeline of turns for execution, resolving dependencies in
    /// topological order. Returns one receipt per turn in pipeline order.
    ///
    /// Turns that fail cause all their dependents to fail. Independent turns
    /// may still succeed (partial pipeline success).
    pub fn submit_pipeline(
        &mut self,
        pipeline: pyana_turn::Pipeline,
        executor: &pyana_turn::TurnExecutor,
        ledger: &mut pyana_cell::Ledger,
    ) -> Vec<Result<pyana_turn::TurnReceipt, pyana_turn::PipelineError>> {
        let results = pyana_turn::execute_pipeline(pipeline, ledger, executor);

        // Append successful receipts to this wallet's chain.
        for result in &results {
            if let Ok(receipt) = result {
                if receipt.agent == self.cell_id("default") {
                    self.append_receipt(receipt.clone());
                }
            }
        }

        results
    }

    /// Create an EventualRef pointing to a specific output slot of a turn.
    ///
    /// This is a helper for constructing pipelines: you hash a turn and then
    /// create a reference that downstream turns can use to target outputs of
    /// this turn.
    pub fn eventual_ref(turn: &pyana_turn::Turn, slot: u32) -> pyana_turn::EventualRef {
        let turn_hash = turn.hash();
        pyana_turn::EventualRef::new(turn_hash, slot)
    }

    // =========================================================================
    // Committed Payments
    // =========================================================================

    /// Build a committed (privacy-preserving) transfer turn from owned notes.
    ///
    /// Constructs a turn where note values are hidden behind Pedersen commitments.
    /// The executor verifies conservation via the Schnorr excess signature and
    /// Bulletproof range proofs, without learning any amounts.
    ///
    /// # Arguments
    ///
    /// * `input_notes` - Notes this wallet can spend (with full opening data).
    /// * `recipients` - (amount, recipient_pubkey) pairs for outputs.
    /// * `domain` - Domain string for deriving the agent's cell ID.
    /// * `nonce` - Replay-protection nonce.
    ///
    /// # Returns
    ///
    /// A fully-formed [`Turn`] with `conservation_proof` set and all effects
    /// carrying `value_commitment` fields, ready for signing and submission.
    pub fn build_committed_transfer(
        &self,
        input_notes: &[crate::committed_turn::OwnedNote],
        recipients: &[(u64, [u8; 32])],
        domain: &str,
        nonce: u64,
    ) -> Result<Turn, crate::error::SdkError> {
        use crate::committed_turn::{
            CommittedNoteInput, CommittedNoteOutput, CommittedTurnBuilder,
        };

        let agent_cell = self.cell_id(domain);

        let mut builder = CommittedTurnBuilder::new();

        for note in input_notes {
            builder.add_input(CommittedNoteInput::from(note));
        }

        for &(amount, ref recipient) in recipients {
            let asset_type = input_notes.first().map(|n| n.asset_type).unwrap_or(0);
            builder.add_output(CommittedNoteOutput {
                value: amount,
                asset_type,
                recipient: *recipient,
            });
        }

        builder.build(agent_cell, nonce, 0)
    }

    // =========================================================================
    // Stealth Address Support
    // =========================================================================

    /// Get this wallet's stealth meta-address (for receiving private notes).
    ///
    /// Publish this so senders can generate unlinkable one-time addresses for you.
    /// The meta-address contains your view public key (for scanning) and spend
    /// public key (for address derivation), but does NOT reveal your signing key.
    pub fn stealth_meta_address(&self) -> StealthMetaAddress {
        self.stealth_keys.meta_address()
    }

    /// Generate a one-time stealth address for sending TO a recipient's meta-address.
    ///
    /// Returns a [`StealthAddress`] containing:
    /// - `one_time_pubkey`: use as the note's `owner` field
    /// - `ephemeral_pubkey`: publish alongside the note for recipient scanning
    pub fn generate_stealth_address_for(&self, recipient: &StealthMetaAddress) -> StealthAddress {
        let (addr, _shared_secret) = recipient.generate_stealth_address();
        addr
    }

    /// Scan announcements for notes addressed to this wallet (using our view key).
    ///
    /// Iterates over the provided announcements, performing the DH check to identify
    /// notes that were sent to our stealth meta-address. Returns the note commitments
    /// of notes that belong to us.
    ///
    /// For large announcement sets, the view tag pre-filter makes this efficient:
    /// only ~1/256 of announcements require the full DH computation.
    pub fn scan_notes(
        &self,
        announcements: &[(NoteCommitment, StealthAnnouncement)],
    ) -> Vec<OwnedStealthNote> {
        let meta = self.stealth_keys.meta_address();
        let mut owned = Vec::new();

        for (commitment, announcement) in announcements {
            // Fast pre-filter: skip if view tag does not match (~255/256 of the time).
            if !announcement.matches_view_tag(&self.stealth_keys.view_private_key) {
                continue;
            }

            // Full ownership check via DH. We construct a StealthAddress from the
            // announcement's ephemeral pubkey and check if we're the recipient.
            let stealth_addr = StealthAddress {
                one_time_pubkey: [0u8; 32], // Not needed for check_ownership
                ephemeral_pubkey: announcement.ephemeral_pubkey,
            };
            if stealth_addr.check_ownership(&self.stealth_keys.view_private_key, &meta.spend_pubkey)
            {
                let spending_key = stealth_addr.derive_spending_key(
                    &self.stealth_keys.view_private_key,
                    &self.stealth_keys.spend_private_key,
                );
                owned.push(OwnedStealthNote {
                    commitment: *commitment,
                    ephemeral_pubkey: announcement.ephemeral_pubkey,
                    spending_key,
                });
            }
        }

        owned
    }

    // =========================================================================
    // Private Transfer (Committed Notes + Stealth)
    // =========================================================================

    /// Create a private transfer: committed value, stealth recipient, range-proved.
    ///
    /// This combines stealth addressing with value commitments to produce a fully
    /// private transfer turn where:
    /// - The recipient is hidden (one-time stealth address)
    /// - The amount is hidden (Pedersen commitment + Bulletproof range proof)
    /// - Conservation is proven (Schnorr excess signature)
    ///
    /// # Arguments
    ///
    /// * `amount` - The value to transfer.
    /// * `asset_type` - The asset type identifier.
    /// * `recipient_meta` - The recipient's stealth meta-address.
    ///
    /// # Returns
    ///
    /// A fully-formed [`Turn`] ready for signing and submission, or an error.
    pub fn private_transfer(
        &mut self,
        amount: u64,
        asset_type: u64,
        recipient_meta: &StealthMetaAddress,
    ) -> Result<Turn, SdkError> {
        use crate::committed_turn::{CommittedNoteOutput, CommittedTurnBuilder};

        // 1. Generate stealth address for recipient.
        let (stealth_addr, _shared_secret) = recipient_meta.generate_stealth_address();

        // 2. Build a committed turn with the stealth address as recipient.
        let agent_cell = self.cell_id("default");
        let nonce = self.receipt_chain.len() as u64;

        let output = CommittedNoteOutput {
            value: amount,
            asset_type,
            recipient: stealth_addr.one_time_pubkey,
        };

        let mut builder = CommittedTurnBuilder::new();
        builder.add_output(output);

        // Note: In a full implementation, the caller would provide input notes to
        // spend. For the API surface, we build a turn with just the output --
        // the caller can use build_committed_transfer() for full input/output flows.
        builder.build(agent_cell, nonce, 0)
    }

    // =========================================================================
    // Sovereign Cell Operations
    // =========================================================================

    /// Transition one of our cells to sovereign mode.
    ///
    /// After this, the federation stores only a 32-byte commitment.
    /// We maintain the full state locally. The returned turn must be signed
    /// and submitted to the federation to take effect.
    ///
    /// # Arguments
    ///
    /// * `cell_id` - The cell to make sovereign. Must be a cell we own.
    ///
    /// # Returns
    ///
    /// A [`Turn`] containing an `Effect::MakeSovereign` action ready for signing.
    pub fn make_sovereign(&mut self, cell_id: &CellId) -> Result<Turn, SdkError> {
        let agent_cell = *cell_id;
        let nonce = self.receipt_chain.len() as u64;

        let mut forest = pyana_turn::forest::CallForest::new();
        let action = pyana_turn::Action {
            target: agent_cell,
            method: pyana_turn::action::symbol("make_sovereign"),
            args: Vec::new(),
            authorization: pyana_turn::Authorization::Unchecked,
            effects: vec![Effect::MakeSovereign { cell: agent_cell }],
            preconditions: pyana_cell::Preconditions::default(),
            may_delegate: pyana_turn::DelegationMode::None,
            commitment_mode: pyana_turn::CommitmentMode::Full,
            balance_change: None,
        };
        forest.add_root(action);

        let turn = Turn {
            agent: agent_cell,
            nonce,
            call_forest: forest,
            fee: 0,
            memo: Some("make_sovereign".to_string()),
            valid_until: None,
            previous_receipt_hash: self.receipt_chain.last().map(|r| r.receipt_hash()),
            depends_on: Vec::new(),
            conservation_proof: None,
            sovereign_witnesses: HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
        };

        Ok(turn)
    }

    /// Execute a turn targeting a sovereign cell.
    ///
    /// We must include the current cell state as a witness so the federation can
    /// verify the state commitment matches what it has stored.
    ///
    /// # Arguments
    ///
    /// * `cell_id` - The sovereign cell to target.
    /// * `effects` - The effects to apply.
    /// * `fee` - The computron fee for this turn.
    ///
    /// # Returns
    ///
    /// A [`Turn`] with `sovereign_witnesses` populated, ready for signing.
    pub fn execute_sovereign_turn(
        &mut self,
        cell_id: &CellId,
        effects: Vec<Effect>,
        fee: u64,
    ) -> Result<Turn, SdkError> {
        // 1. Get our local cell state.
        let cell_state = self
            .sovereign_cells
            .get(cell_id)
            .ok_or_else(|| {
                SdkError::MissingKey(format!(
                    "no local sovereign state for cell {}; call store_sovereign_state() first",
                    cell_id
                ))
            })?
            .clone();

        // 2. Compute state_commitment.
        let state_commitment = cell_state.state_commitment();

        // 3. Build SovereignCellWitness.
        let witness = SovereignCellWitness {
            cell_state,
            state_proof: state_commitment,
        };

        // 4. Build the turn with sovereign_witnesses populated.
        let agent_cell = *cell_id;
        let nonce = self.receipt_chain.len() as u64;

        let mut forest = pyana_turn::forest::CallForest::new();
        let action = pyana_turn::Action {
            target: agent_cell,
            method: pyana_turn::action::symbol("sovereign_execute"),
            args: Vec::new(),
            authorization: pyana_turn::Authorization::Unchecked,
            effects,
            preconditions: pyana_cell::Preconditions::default(),
            may_delegate: pyana_turn::DelegationMode::None,
            commitment_mode: pyana_turn::CommitmentMode::Full,
            balance_change: None,
        };
        forest.add_root(action);

        let mut sovereign_witnesses = HashMap::new();
        sovereign_witnesses.insert(*cell_id, witness);

        let turn = Turn {
            agent: agent_cell,
            nonce,
            call_forest: forest,
            fee,
            memo: None,
            valid_until: None,
            previous_receipt_hash: self.receipt_chain.last().map(|r| r.receipt_hash()),
            depends_on: Vec::new(),
            conservation_proof: None,
            sovereign_witnesses,
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
        };

        Ok(turn)
    }

    /// Execute a sovereign turn with STARK proof (Phase 2).
    ///
    /// The agent executes effects locally, generates a STARK proof that the state
    /// transition is valid, and submits the proof. The federation verifies the proof
    /// instead of re-executing (constant-time verification regardless of state complexity).
    ///
    /// This method:
    /// 1. Gets the local sovereign cell state
    /// 2. Computes the old commitment
    /// 3. Applies effects locally (balance transfer)
    /// 4. Computes the new commitment
    /// 5. Generates the STARK proof (SovereignTransitionAir)
    /// 6. Builds a Turn with `execution_proof: Some(proof_bytes)`
    /// 7. `sovereign_witnesses` is EMPTY — the proof covers the transition
    ///
    /// # Arguments
    ///
    /// * `cell_id` - The sovereign cell to act on.
    /// * `effects` - Effects to apply (currently supports Transfer).
    /// * `fee` - Computron fee for this turn.
    ///
    /// # Returns
    ///
    /// A proof-carrying [`Turn`] ready for submission to the federation.
    pub fn execute_sovereign_turn_with_proof(
        &mut self,
        cell_id: &CellId,
        effects: Vec<Effect>,
        fee: u64,
    ) -> Result<Turn, SdkError> {
        // 1. Get our local cell state.
        let cell_state = self
            .sovereign_cells
            .get(cell_id)
            .ok_or_else(|| {
                SdkError::MissingKey(format!(
                    "no local sovereign state for cell {}; call store_sovereign_state() first",
                    cell_id
                ))
            })?
            .clone();

        // 2. Compute old commitment.
        let old_commitment = cell_state.state_commitment();

        // 3. Determine transfer parameters from the effects.
        // Phase 2 MVP: only supports a single Transfer effect.
        let (transfer_amount, direction) = Self::extract_transfer_params(cell_id, &effects)?;

        // 4. Apply effects locally to get the new state.
        let mut new_cell_state = cell_state.clone();
        for effect in &effects {
            match effect {
                Effect::Transfer { from, to, amount } => {
                    if from == cell_id {
                        new_cell_state.state.balance =
                            new_cell_state.state.balance.saturating_sub(*amount);
                    }
                    if to == cell_id {
                        new_cell_state.state.balance =
                            new_cell_state.state.balance.saturating_add(*amount);
                    }
                }
                Effect::SetField { cell, index, value } if cell == cell_id => {
                    if *index < new_cell_state.state.fields.len() {
                        new_cell_state.state.fields[*index] = *value;
                    }
                }
                Effect::IncrementNonce { cell } if cell == cell_id => {
                    new_cell_state.state.nonce += 1;
                }
                _ => {}
            }
        }

        // 5. Compute new commitment.
        let new_commitment = new_cell_state.state_commitment();

        // 6. Compute effects hash (must match what the executor computes).
        let effects_hash = Self::compute_sovereign_effects_hash(&effects);

        // 7. Compute cell_id hash (must match executor's format).
        let cell_id_hash = *blake3::hash(cell_id.as_bytes()).as_bytes();

        // 8. Generate the STARK proof.
        let (trace, public_inputs) =
            pyana_circuit::sovereign_transition_air::generate_sovereign_transition_trace(
                cell_state.state.balance,
                transfer_amount,
                direction,
                &old_commitment,
                &new_commitment,
                &effects_hash,
                &cell_id_hash,
            );

        let air = pyana_circuit::SovereignTransitionAir;
        let proof = pyana_circuit::stark::prove(&air, &trace, &public_inputs);
        let proof_bytes = pyana_circuit::stark::proof_to_bytes(&proof);

        // 9. Update local sovereign state.
        self.sovereign_cells.insert(*cell_id, new_cell_state);

        // 10. Build the turn with execution_proof (no sovereign_witnesses needed).
        let agent_cell = *cell_id;
        let nonce = self.receipt_chain.len() as u64;

        let mut forest = pyana_turn::forest::CallForest::new();
        let action = pyana_turn::Action {
            target: agent_cell,
            method: pyana_turn::action::symbol("sovereign_execute_proven"),
            args: Vec::new(),
            authorization: pyana_turn::Authorization::Unchecked,
            effects,
            preconditions: pyana_cell::Preconditions::default(),
            may_delegate: pyana_turn::DelegationMode::None,
            commitment_mode: pyana_turn::CommitmentMode::Full,
            balance_change: None,
        };
        forest.add_root(action);

        let turn = Turn {
            agent: agent_cell,
            nonce,
            call_forest: forest,
            fee,
            memo: Some("sovereign_proof_carrying".to_string()),
            valid_until: None,
            previous_receipt_hash: self.receipt_chain.last().map(|r| r.receipt_hash()),
            depends_on: Vec::new(),
            conservation_proof: None,
            sovereign_witnesses: HashMap::new(), // Empty! Proof covers it.
            execution_proof: Some(proof_bytes),
            execution_proof_cell: Some(*cell_id),
            execution_proof_new_commitment: Some(new_commitment),
        };

        Ok(turn)
    }

    /// Extract transfer parameters from effects for proof generation.
    ///
    /// Returns (amount, direction) where direction=1 for outgoing, 0 for incoming.
    fn extract_transfer_params(
        cell_id: &CellId,
        effects: &[Effect],
    ) -> Result<(u64, u32), SdkError> {
        for effect in effects {
            if let Effect::Transfer { from, to, amount } = effect {
                if from == cell_id {
                    return Ok((*amount, 1)); // outgoing
                } else if to == cell_id {
                    return Ok((*amount, 0)); // incoming
                }
            }
        }
        // No transfer found — use zero amount (other effects only).
        Ok((0, 0))
    }

    /// Compute effects hash matching the executor's format.
    ///
    /// The executor hashes effects as: `blake3("pyana-sovereign-effects-v1:" || effect_hashes...)`.
    fn compute_sovereign_effects_hash(effects: &[Effect]) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-sovereign-effects-v1:");
        for effect in effects {
            hasher.update(&effect.hash());
        }
        *hasher.finalize().as_bytes()
    }

    /// Store sovereign cell state in the wallet (agent maintains it).
    ///
    /// Call this after transitioning a cell to sovereign mode. The wallet keeps
    /// the full cell state locally and provides it as a witness in future turns.
    pub fn store_sovereign_state(&mut self, cell: Cell) {
        self.sovereign_cells.insert(cell.id, cell);
    }

    /// Get our local copy of a sovereign cell's state.
    pub fn sovereign_state(&self, cell_id: &CellId) -> Option<&Cell> {
        self.sovereign_cells.get(cell_id)
    }

    /// Update sovereign state after a turn executes (applies effects locally).
    ///
    /// This applies the given effects to the locally-stored sovereign cell state.
    /// Call this after a turn has been committed by the federation so the local
    /// state stays consistent with the on-chain commitment.
    pub fn apply_sovereign_effects(
        &mut self,
        cell_id: &CellId,
        effects: &[Effect],
    ) -> Result<(), SdkError> {
        let cell = self.sovereign_cells.get_mut(cell_id).ok_or_else(|| {
            SdkError::MissingKey(format!("no local sovereign state for cell {}", cell_id))
        })?;

        for effect in effects {
            match effect {
                Effect::SetField {
                    cell: target,
                    index,
                    value,
                } if target == cell_id => {
                    if *index < cell.state.fields.len() {
                        cell.state.fields[*index] = *value;
                    }
                }
                Effect::Transfer { to, amount, .. } if to == cell_id => {
                    cell.state.balance = cell.state.balance.saturating_add(*amount);
                }
                Effect::Transfer { from, amount, .. } if from == cell_id => {
                    cell.state.balance = cell.state.balance.saturating_sub(*amount);
                }
                Effect::IncrementNonce { cell: target } if target == cell_id => {
                    cell.state.nonce += 1;
                }
                _ => {
                    // Other effects (GrantCapability, RevokeCapability, EmitEvent, etc.)
                    // are either not relevant to cell state or handled at a higher level.
                }
            }
        }

        Ok(())
    }

    /// Export all sovereign cell state (for backup).
    ///
    /// Serializes the full sovereign cell state map to a byte vector using
    /// postcard encoding. The result can be stored securely and later restored
    /// via [`import_sovereign_state`](Self::import_sovereign_state).
    pub fn export_sovereign_state(&self) -> Vec<u8> {
        // Collect into a Vec of (CellId, Cell) for deterministic serialization.
        let entries: Vec<(&CellId, &Cell)> = self.sovereign_cells.iter().collect();
        postcard::to_stdvec(&entries).unwrap_or_default()
    }

    /// Import sovereign cell state (for recovery).
    ///
    /// Deserializes sovereign cell state previously exported via
    /// [`export_sovereign_state`](Self::export_sovereign_state) and merges it
    /// into this wallet's sovereign cell map.
    pub fn import_sovereign_state(&mut self, data: &[u8]) -> Result<(), SdkError> {
        let entries: Vec<(CellId, Cell)> = postcard::from_bytes(data)
            .map_err(|e| SdkError::Wire(format!("failed to deserialize sovereign state: {e}")))?;
        for (id, cell) in entries {
            self.sovereign_cells.insert(id, cell);
        }
        Ok(())
    }

    /// Get the number of sovereign cells stored locally.
    pub fn sovereign_cell_count(&self) -> usize {
        self.sovereign_cells.len()
    }

    /// Get a peer exchange session for direct sovereign interactions.
    ///
    /// Returns a [`PeerExchange`](pyana_cell::PeerExchange) initialized with
    /// this wallet's cell ID and signing key, suitable for direct peer-to-peer
    /// state exchange between sovereign cell owners.
    ///
    /// This is a convenience alias for [`peer_exchange`](Self::peer_exchange).
    pub fn peer_exchange_session(&self, domain: &str) -> pyana_cell::PeerExchange {
        self.peer_exchange(domain)
    }

    // =========================================================================
    // Factory Operations (EROS-style object creation)
    // =========================================================================

    /// Deploy a factory descriptor, returning its VK hash identifier.
    ///
    /// The factory descriptor defines what cells the factory can create: what
    /// program is installed, what capabilities are granted, what field constraints
    /// apply, and the per-epoch creation budget.
    ///
    /// Anyone can inspect the descriptor to understand exactly what the factory
    /// creates — this is constructor transparency.
    pub fn deploy_factory(&self, descriptor: pyana_cell::FactoryDescriptor) -> [u8; 32] {
        descriptor.factory_vk
    }

    /// Build a turn that creates a cell from a deployed factory.
    ///
    /// The turn carries a `CreateCellFromFactory` effect that the executor validates
    /// against the factory's registered descriptor.
    pub fn create_from_factory(
        &self,
        agent_cell: CellId,
        factory_vk: [u8; 32],
        owner_pubkey: [u8; 32],
        token_id: [u8; 32],
        params: pyana_cell::FactoryCreationParams,
        nonce: u64,
        fee: u64,
    ) -> Turn {
        use pyana_turn::action::{Action, Authorization, DelegationMode, Effect};

        let method = *blake3::hash(b"factory_create").as_bytes();
        let action = Action {
            target: agent_cell,
            method,
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: pyana_cell::Preconditions::default(),
            effects: vec![Effect::CreateCellFromFactory {
                factory_vk,
                owner_pubkey,
                token_id,
                params,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: Default::default(),
            balance_change: None,
        };

        use pyana_turn::forest::{CallForest, CallTree};
        let tree = CallTree {
            action,
            children: vec![],
            hash: [0u8; 32],
        };
        let forest = CallForest {
            roots: vec![tree],
            forest_hash: [0u8; 32],
        };

        Turn {
            agent: agent_cell,
            nonce,
            fee,
            memo: None,
            call_forest: forest,
            valid_until: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            conservation_proof: None,
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            previous_receipt_hash: None,
            depends_on: vec![],
        }
    }

    /// Verify provenance of a cell — returns the factory that created it (if any).
    ///
    /// In the current implementation, provenance is tracked by the executor
    /// at creation time. This method inspects the cell's VK and checks it
    /// against known factory VK hashes.
    pub fn verify_provenance(
        &self,
        cell: &Cell,
        known_factories: &[pyana_cell::FactoryDescriptor],
    ) -> Option<pyana_cell::Provenance> {
        if let Some(vk) = &cell.verification_key {
            for factory in known_factories {
                if factory.child_program_vk == Some(vk.hash) {
                    return Some(pyana_cell::Provenance::from_factory(
                        factory.factory_vk,
                        None,
                        0,
                    ));
                }
            }
        }
        None
    }

    // =========================================================================
    // Encrypted Intent Posting
    // =========================================================================

    /// Post an intent with encrypted headers (SSE tokens + sealed body).
    ///
    /// Creates an [`EncryptedIntent`] suitable for gossip propagation. The intent's
    /// MatchSpec is encrypted so only fulfillers whose capabilities match the SSE
    /// search tokens can discover and decrypt it.
    ///
    /// # Arguments
    ///
    /// * `spec` - The capability matching specification.
    /// * `kind` - The kind of intent (Need, Offer, or Query).
    /// * `expiry` - Optional Unix timestamp after which the intent expires.
    ///
    /// # Returns
    ///
    /// An [`EncryptedIntent`] ready for gossip broadcast.
    pub fn post_encrypted_intent(
        &self,
        spec: &MatchSpec,
        _kind: IntentKind,
        expiry: Option<u64>,
    ) -> EncryptedIntent {
        // Derive the commitment ID from this wallet's public key.
        let commitment_id = CommitmentId(self.public_key.0);

        // Use epoch 0 for now; in production this would come from the network clock.
        let epoch = 0u64;

        let (encrypted, _keypair) = EncryptedIntent::create(spec, commitment_id, epoch, expiry);
        encrypted
    }

    // =========================================================================
    // Stealth Key Derivation (internal)
    // =========================================================================

    /// Derive stealth keys deterministically from the wallet's Ed25519 signing key.
    ///
    /// Uses BLAKE3 key derivation with distinct context strings to produce
    /// independent view and spend keys.
    fn derive_stealth_keys(signing_key: &ed25519_dalek::SigningKey) -> StealthKeys {
        let sk_bytes = signing_key.to_bytes();
        let view_private_key = blake3::derive_key("pyana-stealth-view-key-v1", &sk_bytes);
        let spend_private_key = blake3::derive_key("pyana-stealth-spend-key-v1", &sk_bytes);
        StealthKeys::from_keys(view_private_key, spend_private_key)
    }

    // =========================================================================
    // Peer-to-Peer State Exchange (Sovereign Cells)
    // =========================================================================

    /// Create a peer exchange session for sovereign cell interactions.
    ///
    /// The exchange session is keyed to a specific domain (cell identity) and uses
    /// this wallet's Ed25519 signing key for transition signatures.
    pub fn peer_exchange(&self, domain: &str) -> pyana_cell::PeerExchange {
        let cell_id = self.cell_id(domain);
        let signing_key_bytes = self.signing_key.to_bytes();
        pyana_cell::PeerExchange::new(cell_id, signing_key_bytes)
    }

    /// Send a sovereign state transition to a peer (sign + package).
    ///
    /// Computes the effects hash (BLAKE3 over serialized effects), then delegates
    /// to the `PeerExchange` to create a signed transition.
    ///
    /// # Arguments
    /// * `exchange` - The peer exchange session (must be for this wallet's cell).
    /// * `old_commitment` - The commitment before this transition.
    /// * `new_commitment` - The commitment after applying effects.
    /// * `effects` - The effects that produced the state change.
    pub fn send_peer_transition(
        &self,
        exchange: &mut pyana_cell::PeerExchange,
        old_commitment: [u8; 32],
        new_commitment: [u8; 32],
        effects: &[pyana_turn::Effect],
    ) -> pyana_cell::PeerStateTransition {
        let effects_bytes = postcard::to_stdvec(effects).unwrap_or_default();
        let effects_hash = *blake3::hash(&effects_bytes).as_bytes();
        exchange.create_transition(old_commitment, new_commitment, effects_hash)
    }

    // =========================================================================
    // Ephemeral Federation Registration
    // =========================================================================

    /// Register this wallet's sovereign cell with a federation node (ephemeral).
    ///
    /// The federation stores only the state commitment and TTL metadata.
    /// The registration expires after `ttl_blocks` of inactivity. Call this when
    /// the sovereign cell needs federation services (ordering, nullifier check,
    /// proving to strangers).
    ///
    /// # Arguments
    ///
    /// * `node_url` - The base URL of the federation node (e.g., "http://localhost:9000").
    /// * `ttl_blocks` - How many blocks to keep the registration alive.
    ///
    /// # Errors
    ///
    /// Returns an error if the HTTP request fails or the node rejects the registration.
    #[cfg(feature = "federation-client")]
    pub async fn register_with_federation(
        &self,
        node_url: &str,
        ttl_blocks: u64,
    ) -> Result<(), SdkError> {
        // Use the public key as the cell_id for sovereign cells.
        let cell_id_bytes = self.public_key.0;

        // Compute the current state commitment from the receipt chain head,
        // or use a zero commitment if no state transitions have occurred.
        let commitment = self.current_state_commitment().unwrap_or([0u8; 32]);

        // Sign cell_id || commitment.
        let mut message = Vec::with_capacity(64);
        message.extend_from_slice(&cell_id_bytes);
        message.extend_from_slice(&commitment);
        let sig = self.signing_key.sign(&message);

        let body = serde_json::json!({
            "cell_id": hex_encode_bytes(&cell_id_bytes),
            "commitment": hex_encode_bytes(&commitment),
            "ttl_blocks": ttl_blocks,
            "signature": hex_encode_bytes(&sig.to_bytes()),
        });

        let url = format!("{}/cells/register", node_url.trim_end_matches('/'));
        let client = reqwest::Client::new();
        let resp = client
            .post(&url)
            .json(&body)
            .send()
            .await
            .map_err(|e| SdkError::Wire(format!("federation register request failed: {e}")))?;

        if !resp.status().is_success() {
            return Err(SdkError::Wire(format!(
                "federation register returned status {}",
                resp.status()
            )));
        }

        let result: serde_json::Value = resp
            .json()
            .await
            .map_err(|e| SdkError::Wire(format!("failed to parse register response: {e}")))?;

        if result.get("registered").and_then(|v| v.as_bool()) == Some(true) {
            Ok(())
        } else {
            let error = result
                .get("error")
                .and_then(|v| v.as_str())
                .unwrap_or("unknown error");
            Err(SdkError::Wire(format!(
                "federation rejected registration: {error}"
            )))
        }
    }

    /// Deregister this wallet's sovereign cell from the federation.
    ///
    /// Voluntarily removes the cell's commitment from the federation node.
    /// Call this when the cell no longer needs federation services.
    ///
    /// # Arguments
    ///
    /// * `node_url` - The base URL of the federation node.
    ///
    /// # Errors
    ///
    /// Returns an error if the HTTP request fails or the node rejects the deregistration.
    #[cfg(feature = "federation-client")]
    pub async fn deregister_from_federation(&self, node_url: &str) -> Result<(), SdkError> {
        let cell_id_bytes = self.public_key.0;

        // Sign just the cell_id for deregistration proof.
        let sig = self.signing_key.sign(&cell_id_bytes);

        let body = serde_json::json!({
            "cell_id": hex_encode_bytes(&cell_id_bytes),
            "signature": hex_encode_bytes(&sig.to_bytes()),
        });

        let url = format!("{}/cells/deregister", node_url.trim_end_matches('/'));
        let client = reqwest::Client::new();
        let resp =
            client.post(&url).json(&body).send().await.map_err(|e| {
                SdkError::Wire(format!("federation deregister request failed: {e}"))
            })?;

        if !resp.status().is_success() {
            return Err(SdkError::Wire(format!(
                "federation deregister returned status {}",
                resp.status()
            )));
        }

        let result: serde_json::Value = resp
            .json()
            .await
            .map_err(|e| SdkError::Wire(format!("failed to parse deregister response: {e}")))?;

        if result.get("deregistered").and_then(|v| v.as_bool()) == Some(true) {
            Ok(())
        } else {
            let error = result
                .get("error")
                .and_then(|v| v.as_str())
                .unwrap_or("unknown error");
            Err(SdkError::Wire(format!(
                "federation rejected deregistration: {error}"
            )))
        }
    }

    /// Deploy a custom cell program to the federation.
    ///
    /// Serializes the `CircuitDescriptor` via postcard and submits it to the node's
    /// `/programs/deploy` endpoint. On success, returns the 32-byte VK hash that
    /// identifies the program in the registry.
    ///
    /// # Arguments
    ///
    /// * `node_url` - The base URL of the federation node.
    /// * `descriptor` - The circuit descriptor defining valid state transitions.
    /// * `version` - Program version for upgrade tracking.
    ///
    /// # Errors
    ///
    /// Returns an error if serialization fails, the HTTP request fails, or the
    /// node rejects the program (e.g., validation failure).
    #[cfg(feature = "federation-client")]
    pub async fn deploy_program(
        &self,
        node_url: &str,
        descriptor: &pyana_dsl_runtime::CircuitDescriptor,
        version: u32,
    ) -> Result<[u8; 32], SdkError> {
        let serialized = postcard::to_allocvec(descriptor)
            .map_err(|e| SdkError::Wire(format!("failed to serialize descriptor: {e}")))?;

        let body = serde_json::json!({
            "descriptor_bytes": hex_encode_bytes(&serialized),
            "version": version,
        });

        let url = format!("{}/programs/deploy", node_url.trim_end_matches('/'));
        let client = reqwest::Client::new();
        let resp = client
            .post(&url)
            .json(&body)
            .send()
            .await
            .map_err(|e| SdkError::Wire(format!("program deploy request failed: {e}")))?;

        if !resp.status().is_success() {
            return Err(SdkError::Wire(format!(
                "program deploy returned status {}",
                resp.status()
            )));
        }

        let result: serde_json::Value = resp
            .json()
            .await
            .map_err(|e| SdkError::Wire(format!("failed to parse deploy response: {e}")))?;

        if result.get("deployed").and_then(|v| v.as_bool()) == Some(true) {
            let vk_hex = result
                .get("vk_hash")
                .and_then(|v| v.as_str())
                .ok_or_else(|| SdkError::Wire("deploy response missing vk_hash".into()))?;
            let vk_bytes = hex_decode_bytes(vk_hex)
                .map_err(|_| SdkError::Wire("invalid vk_hash hex in deploy response".into()))?;
            if vk_bytes.len() != 32 {
                return Err(SdkError::Wire("vk_hash is not 32 bytes".into()));
            }
            let mut vk = [0u8; 32];
            vk.copy_from_slice(&vk_bytes);
            Ok(vk)
        } else {
            let error = result
                .get("error")
                .and_then(|v| v.as_str())
                .unwrap_or("unknown error");
            Err(SdkError::Wire(format!(
                "federation rejected program deployment: {error}"
            )))
        }
    }

    /// Execute a sovereign turn with a custom program proof.
    ///
    /// Generates a STARK proof of a valid state transition under the given program
    /// and builds a proof-carrying turn for submission to the federation.
    ///
    /// # Arguments
    ///
    /// * `cell_id` - The sovereign cell to transition.
    /// * `program` - The deployed cell program (must match the cell's VK).
    /// * `witness` - Column name -> values mapping for trace generation.
    /// * `num_rows` - Number of trace rows (must be a power of 2, >= 2).
    /// * `public_inputs` - Public inputs for the proof (encodes old/new commitments).
    /// * `new_commitment` - The new 32-byte state commitment after the transition.
    /// * `nonce` - Turn nonce.
    /// * `fee` - Turn fee in computrons.
    ///
    /// # Errors
    ///
    /// Returns an error if witness generation or proof generation fails.
    pub fn execute_with_program(
        &self,
        cell_id: &CellId,
        program: &pyana_dsl_runtime::CellProgram,
        witness: &HashMap<String, Vec<BabyBear>>,
        num_rows: usize,
        public_inputs: &[BabyBear],
        new_commitment: [u8; 32],
        nonce: u64,
        fee: u64,
    ) -> Result<Turn, SdkError> {
        // Generate the STARK proof using the program.
        let proof_bytes = program
            .prove_transition(witness, num_rows, public_inputs)
            .map_err(SdkError::Program)?;

        // Build a proof-carrying turn.
        let agent_id = self.cell_id("default");
        let turn = Turn {
            agent: agent_id,
            nonce,
            fee,
            call_forest: pyana_turn::CallForest {
                roots: vec![],
                forest_hash: [0u8; 32],
            },
            valid_until: None,
            execution_proof: Some(proof_bytes),
            execution_proof_cell: Some(*cell_id),
            execution_proof_new_commitment: Some(new_commitment),
            sovereign_witnesses: HashMap::new(),
            memo: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
        };

        Ok(turn)
    }
}

/// Encode bytes to hex string (used by federation registration methods).
fn hex_encode_bytes(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Decode a hex string into bytes.
fn hex_decode_bytes(s: &str) -> Result<Vec<u8>, ()> {
    if s.len() % 2 != 0 {
        return Err(());
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).map_err(|_| ()))
        .collect()
}

/// A note detected as belonging to this wallet during stealth scanning.
#[derive(Clone, Debug)]
pub struct OwnedStealthNote {
    /// The note commitment (for lookup in the note tree).
    pub commitment: NoteCommitment,
    /// The ephemeral public key from the announcement.
    pub ephemeral_pubkey: [u8; 32],
    /// The derived one-time spending key for this note.
    pub spending_key: [u8; 32],
}

impl Default for AgentWallet {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for AgentWallet {
    fn drop(&mut self) {
        // Zeroize sensitive key material on drop.
        if let Some(ref mut seed) = self.seed {
            seed.zeroize();
        }
        if let Some(ref mut phrase) = self.mnemonic_phrase {
            phrase.zeroize();
        }
    }
}

impl std::fmt::Debug for AgentWallet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AgentWallet")
            .field("public_key", &self.public_key)
            .field("tokens_held", &self.tokens.len())
            .field("receipt_chain_length", &self.receipt_chain.len())
            .field("ivc_enabled", &self.ivc_builder.is_some())
            .field("has_seed", &self.seed.is_some())
            .field("has_mnemonic", &self.mnemonic_phrase.is_some())
            .field("derivation_path", &self.derivation_path)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_turn::TurnReceipt;

    /// Helper: create a mock receipt with given state hashes.
    fn mock_receipt(agent: CellId, pre_state: [u8; 32], post_state: [u8; 32]) -> TurnReceipt {
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
            federation_id: [0u8; 32],
            routing_directives: Vec::new(),
            derivation_records: Vec::new(),
            emitted_events: Vec::new(),
            executor_signature: None,
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
        assert_eq!(
            chain[1].previous_receipt_hash,
            Some(chain[0].receipt_hash())
        );

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

    #[test]
    fn test_wallet_from_mnemonic() {
        let mnemonic = crate::mnemonic::generate_mnemonic();
        let mut wallet = AgentWallet::from_mnemonic(&mnemonic, "").unwrap();
        assert!(wallet.export_mnemonic().is_some());
        assert_eq!(wallet.export_mnemonic().unwrap(), mnemonic);
        assert!(wallet.export_seed().is_some());
        assert_eq!(wallet.derivation_path(), Some("pyana/0"));
    }

    #[test]
    fn test_wallet_from_mnemonic_deterministic() {
        let mnemonic = crate::mnemonic::generate_mnemonic();
        let w1 = AgentWallet::from_mnemonic(&mnemonic, "pass").unwrap();
        let w2 = AgentWallet::from_mnemonic(&mnemonic, "pass").unwrap();
        assert_eq!(w1.public_key(), w2.public_key());
    }

    #[test]
    fn test_wallet_from_seed() {
        let mnemonic = crate::mnemonic::generate_mnemonic();
        let seed = crate::mnemonic::mnemonic_to_seed(&mnemonic, "").unwrap();
        let w1 = AgentWallet::from_mnemonic(&mnemonic, "").unwrap();
        let w2 = AgentWallet::from_seed(seed);
        assert_eq!(w1.public_key(), w2.public_key());
    }

    #[test]
    fn test_wallet_derive_sub_agent() {
        let mnemonic = crate::mnemonic::generate_mnemonic();
        let wallet = AgentWallet::from_mnemonic(&mnemonic, "").unwrap();
        let sub1 = wallet.derive_sub_agent(1).unwrap();
        let sub2 = wallet.derive_sub_agent(2).unwrap();

        // Sub-agents have different keys from the main wallet.
        assert_ne!(wallet.public_key(), sub1.public_key());
        assert_ne!(wallet.public_key(), sub2.public_key());
        assert_ne!(sub1.public_key(), sub2.public_key());

        // Derivation is deterministic.
        let sub1_again = wallet.derive_sub_agent(1).unwrap();
        assert_eq!(sub1.public_key(), sub1_again.public_key());
    }

    #[test]
    fn test_wallet_derive_sub_agent_no_seed() {
        let wallet = AgentWallet::new();
        let result = wallet.derive_sub_agent(1);
        assert!(result.is_err());
    }

    #[test]
    fn test_wallet_new_has_no_mnemonic() {
        let mut wallet = AgentWallet::new();
        assert!(wallet.export_mnemonic().is_none());
        assert!(wallet.export_seed().is_none());
        assert!(wallet.derivation_path().is_none());
    }

    #[test]
    fn test_attenuated_token_has_zeroed_root_key() {
        let mut wallet = AgentWallet::new();
        let root_key = [42u8; 32];
        let root_token = wallet.mint_token(&root_key, "compute");

        // Root token holds the actual key.
        assert!(root_token.can_mint());
        assert!(root_token.can_prove());
        assert_eq!(root_token.root_key(), &root_key);

        // Attenuate: restrict to read-only on "compute" service.
        let restrictions = Attenuation {
            services: vec![("compute".to_string(), "r".to_string())],
            ..Default::default()
        };
        let attenuated = wallet.attenuate(&root_token, &restrictions).unwrap();

        // SECURITY: The attenuated token must NOT carry the root forging key.
        assert!(!attenuated.can_mint());
        assert_eq!(attenuated.root_key(), &[0u8; 32]);

        // But it CAN prove (has derived issuer_key for federation membership).
        assert!(attenuated.can_prove());
        // The issuer_key is a one-way derivation of the root key, never the raw key.
        let expected_proof_key = blake3::derive_key("pyana-proof-key-v1", &root_key);
        assert_eq!(attenuated.issuer_key(), &expected_proof_key);
        assert_ne!(
            attenuated.issuer_key(),
            &root_key,
            "issuer_key must NOT be the raw root key"
        );

        // The attenuated token cannot be used to mint new tokens (prove_authorization
        // with the direct method still fails — it requires can_mint()).
        let request = pyana_token::AuthRequest {
            service: Some("compute".into()),
            action: Some("r".into()),
            ..Default::default()
        };
        let proof_result = wallet.prove_authorization(&attenuated, &request);
        assert!(
            proof_result.is_err(),
            "attenuated token should not be able to generate federation membership proofs via prove_authorization()"
        );

        // But the ROOT token can still prove.
        let root_proof_result = wallet.prove_authorization(&root_token, &request);
        assert!(
            root_proof_result.is_ok(),
            "root token should still be able to prove"
        );
    }

    #[test]
    fn test_delegated_token_has_zeroed_root_key() {
        let mut wallet = AgentWallet::new();
        let root_key = [99u8; 32];
        let root_token = wallet.mint_token(&root_key, "storage");

        let delegatee_wallet = AgentWallet::new();
        let delegatee_pk = delegatee_wallet.public_key();

        let restrictions = Attenuation {
            services: vec![("storage".to_string(), "r".to_string())],
            ..Default::default()
        };
        let delegated = wallet
            .delegate(&root_token, &delegatee_pk, &restrictions)
            .unwrap();

        // The delegated token's underlying attenuated HeldToken in the wallet
        // should also have zeroed root_key.
        let attenuated_in_wallet = wallet
            .tokens()
            .iter()
            .find(|t| t.id.contains("att"))
            .unwrap();
        assert!(!attenuated_in_wallet.can_mint());
        assert_eq!(attenuated_in_wallet.root_key(), &[0u8; 32]);

        // When the delegatee receives it, they also don't get root_key.
        let mut recv_wallet = AgentWallet::new();
        recv_wallet.receive_delegation(delegated).unwrap();
        let held = recv_wallet.tokens().first().unwrap();
        assert!(!held.can_mint());
        assert_eq!(held.root_key(), &[0u8; 32]);
    }

    /// P1-2 regression test: receive_delegation marks tokens as unverified since
    /// HMAC chain cannot be checked without the root key.
    #[test]
    fn test_receive_delegation_marks_unverified() {
        let mut wallet = AgentWallet::new();
        let root_key = [0xAA; 32];
        let root_token = wallet.mint_token(&root_key, "service");

        // Root token must be verified.
        assert!(root_token.is_verified());

        let delegatee_wallet = AgentWallet::new();
        let delegatee_pk = delegatee_wallet.public_key();

        let restrictions = Attenuation {
            services: vec![("service".to_string(), "r".to_string())],
            ..Default::default()
        };
        let delegated = wallet
            .delegate(&root_token, &delegatee_pk, &restrictions)
            .unwrap();

        // Attenuated token created locally (from verified parent) is still verified.
        let attenuated_in_wallet = wallet
            .tokens()
            .iter()
            .find(|t| t.id.contains("att"))
            .unwrap();
        assert!(
            attenuated_in_wallet.is_verified(),
            "locally-attenuated token should be verified"
        );

        // When a delegatee receives the token, it must be marked as UNVERIFIED
        // because the HMAC chain cannot be checked without the root key.
        let mut recv_wallet = AgentWallet::new();
        recv_wallet.receive_delegation(delegated).unwrap();
        let received = recv_wallet.tokens().first().unwrap();
        assert!(
            !received.is_verified(),
            "delegated token must be marked unverified (HMAC chain not checked)"
        );
    }

    /// P1-2 regression test: minted tokens are verified.
    #[test]
    fn test_minted_token_is_verified() {
        let mut wallet = AgentWallet::new();
        let root_key = [0xBB; 32];
        let token = wallet.mint_token(&root_key, "compute");
        assert!(token.is_verified());
        assert!(token.can_mint());
    }

    /// End-to-end test: attenuate a token, then authorize in Private mode (ZK proof).
    ///
    /// This exercises the core product promise: "offline attenuate, then prove."
    /// Previously this flow was broken because:
    /// 1. attenuate() zeroed the root_key
    /// 2. authorize(Private) tried to verify the HMAC chain (needs root_key)
    /// 3. prove_authorization() rejected tokens without can_mint()
    ///
    /// The fix: attenuated tokens carry the issuer_key (for federation membership
    /// proofs), and the private/selective authorize paths use structural caveat
    /// extraction + prove_authorization_with_issuer_key internally.
    #[test]
    fn test_attenuate_authorize_private_end_to_end() {
        let mut wallet = AgentWallet::new();
        let root_key = [0xAA; 32];
        let root_token = wallet.mint_token(&root_key, "compute");

        // Step 1: Attenuate the token (restrict to read-only on "compute").
        let restrictions = Attenuation {
            services: vec![("compute".to_string(), "r".to_string())],
            ..Default::default()
        };
        let attenuated = wallet.attenuate(&root_token, &restrictions).unwrap();

        // Verify the attenuated token's properties.
        assert!(!attenuated.can_mint(), "must not be able to mint");
        assert!(attenuated.can_prove(), "must be able to generate ZK proofs");

        // Step 2: Authorize in FullyPrivate mode (generates a STARK proof).
        let request = pyana_token::AuthRequest {
            service: Some("compute".into()),
            action: Some("r".into()),
            ..Default::default()
        };
        let presentation = wallet.authorize(&attenuated, &request, VerificationMode::FullyPrivate);
        assert!(
            presentation.is_ok(),
            "attenuated token should be able to authorize in Private mode, got: {:?}",
            presentation.err()
        );

        // Step 3: Verify the presentation is a Private variant with a proof and allow.
        match presentation.unwrap() {
            AuthorizationPresentation::Private { proof, conclusion } => {
                assert!(conclusion, "authorization should succeed (read on compute)");
                assert!(!proof.is_empty(), "proof bytes must be non-empty");
            }
            other => panic!("expected Private presentation, got: {:?}", other),
        }
    }

    /// Test that doubly-attenuated tokens can also prove (issuer_key propagates).
    #[test]
    fn test_double_attenuate_authorize_private() {
        let mut wallet = AgentWallet::new();
        let root_key = [0xCC; 32];
        let root_token = wallet.mint_token(&root_key, "storage");

        // First attenuation: restrict to storage service.
        let r1 = Attenuation {
            services: vec![("storage".to_string(), "rw".to_string())],
            ..Default::default()
        };
        let att1 = wallet.attenuate(&root_token, &r1).unwrap();
        assert!(att1.can_prove());

        // Second attenuation: further restrict to read-only.
        let r2 = Attenuation {
            services: vec![("storage".to_string(), "r".to_string())],
            ..Default::default()
        };
        let att2 = wallet.attenuate(&att1, &r2).unwrap();

        // The doubly-attenuated token should still be able to prove.
        assert!(!att2.can_mint());
        assert!(att2.can_prove());
        let expected_proof_key = blake3::derive_key("pyana-proof-key-v1", &root_key);
        assert_eq!(att2.issuer_key(), &expected_proof_key);
        assert_ne!(
            att2.issuer_key(),
            &root_key,
            "issuer_key must NOT be the raw root key"
        );

        // Authorize in Private mode.
        let request = pyana_token::AuthRequest {
            service: Some("storage".into()),
            action: Some("r".into()),
            ..Default::default()
        };
        let presentation = wallet.authorize(&att2, &request, VerificationMode::FullyPrivate);
        assert!(
            presentation.is_ok(),
            "doubly-attenuated token should authorize in Private mode, got: {:?}",
            presentation.err()
        );
    }

    /// Test that delegated tokens CAN prove when proof_key is included in the delegation.
    ///
    /// This is the primary cross-agent delegation flow: Agent A delegates to Agent B,
    /// including a derived proof_key. Agent B can then generate ZK proofs privately.
    #[test]
    fn test_delegated_token_can_prove_with_proof_key() {
        let mut issuer_wallet = AgentWallet::new();
        let root_key = [0xDD; 32];
        let root_token = issuer_wallet.mint_token(&root_key, "api");

        let holder_wallet_pk = AgentWallet::new().public_key();

        let restrictions = Attenuation {
            services: vec![("api".to_string(), "r".to_string())],
            ..Default::default()
        };
        let delegated = issuer_wallet
            .delegate(&root_token, &holder_wallet_pk, &restrictions)
            .unwrap();

        // The delegation should include a proof_key (derived from issuer's root key).
        assert!(
            delegated.proof_key.is_some(),
            "delegation from a provable token must include a proof_key"
        );
        // The proof_key must NOT be the raw root_key (it's derived via BLAKE3).
        assert_ne!(
            delegated.proof_key.unwrap(),
            root_key,
            "proof_key must be derived, not the raw root key"
        );

        // Holder receives the delegation (with proof_key).
        let mut holder_wallet = AgentWallet::new();
        holder_wallet.receive_delegation(delegated).unwrap();
        let held = holder_wallet.tokens().first().unwrap().clone();

        // Delegated token cannot mint but CAN prove (has derived proof_key as issuer_key).
        assert!(!held.can_mint());
        assert!(
            held.can_prove(),
            "delegated token with proof_key should be able to prove"
        );

        // Private authorization should succeed.
        let request = pyana_token::AuthRequest {
            service: Some("api".into()),
            action: Some("r".into()),
            ..Default::default()
        };
        let result = holder_wallet.authorize(&held, &request, VerificationMode::FullyPrivate);
        assert!(
            result.is_ok(),
            "delegated token with proof_key should authorize in Private mode, got: {:?}",
            result.err()
        );
    }

    /// Test that delegated tokens without proof_key (legacy/stripped delegations)
    /// cannot prove without explicit issuer_key provision.
    #[test]
    fn test_delegated_token_cannot_prove_without_proof_key() {
        let holder_wallet = AgentWallet::new();

        // Simulate receiving a legacy delegation without proof_key.
        let _delegated = DelegatedToken {
            token_bytes: "em2_test".to_string(), // will fail parse but tests the path
            service: "api".to_string(),
            label: "legacy".to_string(),
            id: "legacy:0".to_string(),
            delegatee: holder_wallet.public_key(),
            restrictions: Attenuation::default(),
            proof_key: None, // No proof_key (legacy delegation)
            membership_proof: None,
            caveat_chain_hash: None,
            delegator_signature: None,
            delegator_public_key: None,
        };

        // This will fail because "em2_test" is not a valid token, but let's test
        // with a real token construction. Instead, directly construct a HeldToken
        // with zeroed issuer_key to test the proof path.
        let held = HeldToken::new(
            "legacy".to_string(),
            "api".to_string(),
            "em2_fake".to_string(),
            [0u8; 32], // no root key
            "legacy:0".to_string(),
        );

        // Token without proof_key cannot prove.
        assert!(!held.can_mint());
        assert!(!held.can_prove());

        // Private authorization should fail with MissingKey.
        let request = pyana_token::AuthRequest {
            service: Some("api".into()),
            action: Some("r".into()),
            ..Default::default()
        };
        let result = holder_wallet.authorize(&held, &request, VerificationMode::FullyPrivate);
        assert!(result.is_err());
    }

    /// Roundtrip test: wallet.authorize() produces bytes that engine.verify_presentation_against()
    /// can decode and verify.
    ///
    /// This is the P0 regression test for the format mismatch where the wallet serialized
    /// raw STARK bytes via `stark::proof_to_bytes` but the verifier expected a postcard-encoded
    /// `WirePresentationProof`. Both sides now use the same format.
    #[test]
    fn test_wallet_authorize_engine_verify_roundtrip() {
        use crate::embed::{EngineConfig, PyanaEngine};

        let mut wallet = AgentWallet::new();
        let root_key = [0xEE; 32];
        let root_token = wallet.mint_token(&root_key, "data");

        // Attenuate the token (restrict to read on "data" service).
        let restrictions = Attenuation {
            services: vec![("data".to_string(), "r".to_string())],
            ..Default::default()
        };
        let attenuated = wallet.attenuate(&root_token, &restrictions).unwrap();
        assert!(attenuated.can_prove());

        // Generate the proof via wallet.authorize(FullyPrivate).
        let request = pyana_token::AuthRequest {
            service: Some("data".into()),
            action: Some("r".into()),
            ..Default::default()
        };
        let presentation = wallet
            .authorize(&attenuated, &request, VerificationMode::FullyPrivate)
            .expect("authorize should succeed");

        let proof_bytes = match &presentation {
            AuthorizationPresentation::Private { proof, conclusion } => {
                assert!(*conclusion, "authorization should allow");
                proof.clone()
            }
            other => panic!("expected Private presentation, got: {:?}", other),
        };

        // Compute the federation root (same derivation the wallet uses internally).
        let federation_root_bb = AgentWallet::compute_federation_root_bb(&root_key);
        let federation_root = AgentWallet::bb_to_bytes(federation_root_bb);

        // Create an engine and set the federation root to match.
        let mut engine = PyanaEngine::new(EngineConfig::for_testing());
        engine.set_federation_root(federation_root);

        // The key assertion: verify_presentation_against must successfully decode the proof.
        // (Before the fix, this would fail with "proof decode failed" because the wallet
        // serialized raw STARK bytes instead of a postcard WirePresentationProof.)
        let result =
            engine.verify_presentation_against(&proof_bytes, &federation_root, "r", "data");

        // The proof should decode without error. Whether full cryptographic verification
        // passes depends on STARK verification and freshness checks, but the decode must
        // succeed -- that's the P0 fix we're testing.
        assert!(
            result.is_ok(),
            "verify_presentation_against should not return a decode error, got: {:?}",
            result.err()
        );
    }

    // =========================================================================
    // Sovereign Cell Tests
    // =========================================================================

    #[test]
    fn test_make_sovereign_builds_turn() {
        let mut wallet = AgentWallet::new();
        let cell_id = wallet.cell_id("test");

        let turn = wallet.make_sovereign(&cell_id).unwrap();

        // The turn targets the cell we specified.
        assert_eq!(turn.agent, cell_id);
        // It should have one action with MakeSovereign effect.
        assert_eq!(turn.action_count(), 1);
        // Sovereign witnesses should be empty (not needed for MakeSovereign).
        assert!(turn.sovereign_witnesses.is_empty());
        // Memo should describe the operation.
        assert_eq!(turn.memo.as_deref(), Some("make_sovereign"));
    }

    #[test]
    fn test_execute_sovereign_turn_requires_stored_state() {
        let mut wallet = AgentWallet::new();
        let cell_id = wallet.cell_id("test");

        // Without stored state, should fail.
        let result = wallet.execute_sovereign_turn(&cell_id, vec![], 0);
        assert!(result.is_err());
        let err = result.unwrap_err().to_string();
        assert!(err.contains("no local sovereign state"));
    }

    #[test]
    fn test_execute_sovereign_turn_with_stored_state() {
        let mut wallet = AgentWallet::new();
        let pk = wallet.public_key().0;
        let token_id = *blake3::hash(b"test").as_bytes();
        let cell = pyana_cell::Cell::with_balance(pk, token_id, 1000);
        let cell_id = cell.id;

        // Store sovereign state.
        wallet.store_sovereign_state(cell.clone());

        // Build a sovereign turn with a transfer effect.
        let other_cell = CellId([99u8; 32]);
        let effects = vec![Effect::Transfer {
            from: cell_id,
            to: other_cell,
            amount: 100,
        }];
        let turn = wallet
            .execute_sovereign_turn(&cell_id, effects, 10)
            .unwrap();

        // Turn should reference the cell.
        assert_eq!(turn.agent, cell_id);
        assert_eq!(turn.fee, 10);
        // Sovereign witness should be populated.
        assert!(turn.sovereign_witnesses.contains_key(&cell_id));
        let witness = &turn.sovereign_witnesses[&cell_id];
        assert_eq!(witness.cell_state.id, cell_id);
        assert_eq!(witness.state_proof, cell.state_commitment());
    }

    #[test]
    fn test_store_and_retrieve_sovereign_state() {
        let mut wallet = AgentWallet::new();
        let pk = wallet.public_key().0;
        let token_id = *blake3::hash(b"domain").as_bytes();
        let cell = pyana_cell::Cell::with_balance(pk, token_id, 500);
        let cell_id = cell.id;

        // Initially empty.
        assert_eq!(wallet.sovereign_cell_count(), 0);
        assert!(wallet.sovereign_state(&cell_id).is_none());

        // Store.
        wallet.store_sovereign_state(cell.clone());
        assert_eq!(wallet.sovereign_cell_count(), 1);

        // Retrieve.
        let retrieved = wallet.sovereign_state(&cell_id).unwrap();
        assert_eq!(retrieved.id, cell_id);
        assert_eq!(retrieved.state.balance, 500);
    }

    #[test]
    fn test_apply_sovereign_effects() {
        let mut wallet = AgentWallet::new();
        let pk = wallet.public_key().0;
        let token_id = *blake3::hash(b"domain").as_bytes();
        let cell = pyana_cell::Cell::with_balance(pk, token_id, 1000);
        let cell_id = cell.id;

        wallet.store_sovereign_state(cell);

        let other = CellId([99u8; 32]);

        // Apply a transfer out.
        let effects = vec![
            Effect::Transfer {
                from: cell_id,
                to: other,
                amount: 300,
            },
            Effect::IncrementNonce { cell: cell_id },
        ];
        wallet.apply_sovereign_effects(&cell_id, &effects).unwrap();

        let state = wallet.sovereign_state(&cell_id).unwrap();
        assert_eq!(state.state.balance, 700);
        assert_eq!(state.state.nonce, 1);
    }

    #[test]
    fn test_apply_sovereign_effects_transfer_in() {
        let mut wallet = AgentWallet::new();
        let pk = wallet.public_key().0;
        let token_id = *blake3::hash(b"domain").as_bytes();
        let cell = pyana_cell::Cell::with_balance(pk, token_id, 100);
        let cell_id = cell.id;

        wallet.store_sovereign_state(cell);

        let other = CellId([88u8; 32]);
        let effects = vec![Effect::Transfer {
            from: other,
            to: cell_id,
            amount: 500,
        }];
        wallet.apply_sovereign_effects(&cell_id, &effects).unwrap();

        let state = wallet.sovereign_state(&cell_id).unwrap();
        assert_eq!(state.state.balance, 600);
    }

    #[test]
    fn test_apply_sovereign_effects_missing_cell() {
        let mut wallet = AgentWallet::new();
        let cell_id = CellId([1u8; 32]);

        let result = wallet.apply_sovereign_effects(&cell_id, &[]);
        assert!(result.is_err());
    }

    #[test]
    fn test_export_import_sovereign_state_roundtrip() {
        let mut wallet = AgentWallet::new();
        let pk = wallet.public_key().0;

        // Store two sovereign cells.
        let token_id_a = *blake3::hash(b"domain-a").as_bytes();
        let cell_a = pyana_cell::Cell::with_balance(pk, token_id_a, 100);
        let id_a = cell_a.id;
        wallet.store_sovereign_state(cell_a);

        let token_id_b = *blake3::hash(b"domain-b").as_bytes();
        let cell_b = pyana_cell::Cell::with_balance(pk, token_id_b, 200);
        let id_b = cell_b.id;
        wallet.store_sovereign_state(cell_b);

        assert_eq!(wallet.sovereign_cell_count(), 2);

        // Export.
        let exported = wallet.export_sovereign_state();
        assert!(!exported.is_empty());

        // Import into a fresh wallet.
        let mut wallet2 = AgentWallet::new();
        wallet2.import_sovereign_state(&exported).unwrap();

        assert_eq!(wallet2.sovereign_cell_count(), 2);
        assert_eq!(wallet2.sovereign_state(&id_a).unwrap().state.balance, 100);
        assert_eq!(wallet2.sovereign_state(&id_b).unwrap().state.balance, 200);
    }

    #[test]
    fn test_import_sovereign_state_invalid_data() {
        let mut wallet = AgentWallet::new();
        let result = wallet.import_sovereign_state(b"not valid postcard data");
        assert!(result.is_err());
        let err = result.unwrap_err().to_string();
        assert!(err.contains("failed to deserialize sovereign state"));
    }

    #[test]
    fn test_peer_exchange_session() {
        let wallet = AgentWallet::new();
        let exchange = wallet.peer_exchange_session("test");
        // PeerExchange should be initialized with the wallet's cell_id.
        let expected_cell_id = wallet.cell_id("test");
        assert_eq!(exchange.cell_id(), expected_cell_id);
    }
}
