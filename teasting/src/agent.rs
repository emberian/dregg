//! Simulated agent: wallet + actions + proof generation for integration tests.
//!
//! A `SimAgent` wraps an [`AgentWallet`] with a human-readable name and provides
//! ergonomic methods for the common test scenarios: minting, attenuating, delegating,
//! proving, and presenting tokens.

use pyana_bridge::{BridgePredicateProof, BridgePresentationProof, Predicate};
use pyana_sdk::{AgentWallet, Attenuation, AuthRequest, DelegatedToken, HeldToken};
use pyana_types::PublicKey;

/// A simulated agent participating in integration tests.
pub struct SimAgent {
    /// Human-readable agent name (e.g., "Alice", "Bob", "Carol").
    pub name: String,
    /// The agent's wallet (identity + tokens + signing).
    pub wallet: AgentWallet,
}

impl SimAgent {
    /// Create a new agent with a fresh identity.
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            wallet: AgentWallet::new(),
        }
    }

    /// Get this agent's public key.
    pub fn public_key(&self) -> PublicKey {
        self.wallet.public_key()
    }

    /// Mint a root token for the given service with a deterministic root key
    /// derived from the agent's name + service name.
    pub fn mint_token(&mut self, service: &str) -> HeldToken {
        let root_key = self.derive_root_key(service);
        self.wallet.mint_token(&root_key, service)
    }

    /// Mint a token with an explicit root key.
    pub fn mint_token_with_key(&mut self, root_key: &[u8; 32], service: &str) -> HeldToken {
        self.wallet.mint_token(root_key, service)
    }

    /// Attenuate a held token with restrictions.
    pub fn attenuate(
        &mut self,
        token: &HeldToken,
        restrictions: &Attenuation,
    ) -> Result<HeldToken, pyana_sdk::SdkError> {
        self.wallet.attenuate(token, restrictions)
    }

    /// Delegate a token to another agent.
    pub fn delegate(
        &mut self,
        token: &HeldToken,
        to: &SimAgent,
        restrictions: &Attenuation,
    ) -> Result<DelegatedToken, pyana_sdk::SdkError> {
        self.wallet.delegate(token, &to.public_key(), restrictions)
    }

    /// Receive a delegated token into this agent's wallet.
    pub fn receive_delegation(
        &mut self,
        delegated: DelegatedToken,
    ) -> Result<(), pyana_sdk::SdkError> {
        self.wallet.receive_delegation(delegated)
    }

    /// Verify that a token authorizes a request (plaintext Datalog evaluation).
    pub fn verify_token(&self, token: &HeldToken, request: &AuthRequest) -> bool {
        self.wallet.verify_token(token, request)
    }

    /// Generate a full STARK presentation proof for a held token.
    pub fn prove_authorization(
        &self,
        token: &HeldToken,
        request: &AuthRequest,
    ) -> Result<BridgePresentationProof, pyana_sdk::SdkError> {
        self.wallet.prove_authorization(token, request)
    }

    /// Generate a STARK presentation proof for a token chain (root + attenuations).
    pub fn prove_with_chain(
        &self,
        root_token: &HeldToken,
        attenuations: &[Attenuation],
        request: &AuthRequest,
    ) -> Result<BridgePresentationProof, pyana_sdk::SdkError> {
        self.wallet
            .prove_with_chain(root_token, attenuations, request)
    }

    /// Prove a predicate about a token attribute (ZK range proof).
    pub fn prove_predicate(
        &self,
        token: &HeldToken,
        attribute: &str,
        attribute_value: u32,
        predicate: Predicate,
    ) -> Result<BridgePredicateProof, pyana_sdk::SdkError> {
        self.wallet
            .prove_predicate(token, attribute, attribute_value, predicate)
    }

    /// Derive a deterministic root key from agent name + service name.
    /// Useful for tests where multiple agents need to agree on the same root.
    fn derive_root_key(&self, service: &str) -> [u8; 32] {
        let input = format!("teasting:root-key:{}:{}", self.name, service);
        *blake3::hash(input.as_bytes()).as_bytes()
    }
}

/// Create a shared root key that multiple agents can reference.
/// This simulates a pre-shared issuer secret for testing delegation chains.
pub fn shared_root_key(label: &str) -> [u8; 32] {
    let input = format!("teasting:shared-root:{}", label);
    *blake3::hash(input.as_bytes()).as_bytes()
}
