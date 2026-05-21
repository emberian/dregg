//! Silo client: interaction with a remote pyana silo.
//!
//! The [`SiloClient`] connects to a remote silo over TCP and provides
//! high-level operations for token presentation, turn submission, and
//! revocation checking using the pyana wire protocol.

use std::net::SocketAddr;
use std::sync::Arc;
use std::time::Duration;

use pyana_wire::prelude::*;

use crate::error::SdkError;
use crate::wallet::{AgentWallet, HeldToken};

/// Result of presenting a token to a remote silo.
#[derive(Clone, Debug)]
pub struct PresentationResult {
    /// Whether the presentation was accepted.
    pub accepted: bool,
    /// Human-readable reason/message from the silo.
    pub reason: Option<String>,
    /// The request digest this result corresponds to.
    pub request_digest: [u8; 32],
}

/// Client for interacting with a remote pyana silo.
///
/// Provides async operations for:
/// - Connecting to a silo over TCP
/// - Presenting tokens (with ZK proofs) for cross-silo authorization
/// - Checking token revocation status via non-membership proofs
/// - Requesting attested revocation roots
///
/// # Example
///
/// ```no_run
/// use pyana_sdk::{AgentWallet, SiloClient};
/// use std::sync::Arc;
///
/// # async fn example() -> Result<(), pyana_sdk::SdkError> {
/// let wallet = Arc::new(AgentWallet::new());
/// let client = SiloClient::connect("127.0.0.1:9100".parse().unwrap(), wallet).await?;
/// # Ok(())
/// # }
/// ```
pub struct SiloClient {
    /// Remote silo address.
    address: SocketAddr,
    /// The agent's wallet (for signing and proof generation).
    wallet: Arc<AgentWallet>,
    /// The underlying TCP connection.
    connection: PeerConnection,
}

impl SiloClient {
    /// Connect to a remote silo.
    ///
    /// Establishes a TCP connection to the silo. Does NOT perform a handshake
    /// automatically -- call [`handshake`](Self::handshake) if the silo expects
    /// a Hello/Welcome exchange before other operations.
    ///
    /// # Arguments
    ///
    /// * `addr` - The socket address of the remote silo.
    /// * `wallet` - A shared reference to the agent's wallet.
    ///
    /// # Errors
    ///
    /// Returns [`SdkError::Wire`] if the connection cannot be established.
    pub async fn connect(addr: SocketAddr, wallet: Arc<AgentWallet>) -> Result<Self, SdkError> {
        let conn = PeerConnection::connect(&addr.to_string())
            .await
            .map_err(|e| SdkError::Wire(format!("connect failed: {e}")))?;

        Ok(SiloClient {
            address: addr,
            wallet,
            connection: conn,
        })
    }

    /// Connect with a timeout.
    pub async fn connect_timeout(
        addr: SocketAddr,
        wallet: Arc<AgentWallet>,
        timeout: Duration,
    ) -> Result<Self, SdkError> {
        let conn = PeerConnection::connect_timeout(&addr.to_string(), timeout)
            .await
            .map_err(|e| SdkError::Wire(format!("connect failed: {e}")))?;

        Ok(SiloClient {
            address: addr,
            wallet,
            connection: conn,
        })
    }

    /// Get the remote silo address.
    pub fn address(&self) -> SocketAddr {
        self.address
    }

    /// Get connection statistics.
    pub fn stats(&self) -> &ConnectionStats {
        self.connection.stats()
    }

    /// Perform the federation handshake (Hello/Welcome exchange).
    ///
    /// Sends a Hello message with this agent's identity and awaits the Welcome
    /// response containing the federation root and member count.
    ///
    /// # Returns
    ///
    /// The federation root from the remote silo's Welcome response.
    pub async fn handshake(&mut self) -> Result<[u8; 32], SdkError> {
        let hello = WireMessage::Hello {
            node_id: self.wallet.public_key().0,
            node_name: format!("agent-{}", self.wallet.public_key().short_hex()),
            protocol_version: PROTOCOL_VERSION,
            capabilities: vec!["present".to_string(), "revoke-check".to_string()],
        };

        let response = self
            .connection
            .request(hello)
            .await
            .map_err(|e| SdkError::Wire(format!("handshake failed: {e}")))?;

        match response {
            WireMessage::Welcome {
                federation_root, ..
            } => Ok(federation_root),
            WireMessage::Error { message, .. } => Err(SdkError::Rejected(message)),
            other => Err(SdkError::Wire(format!(
                "unexpected handshake response: {}",
                other.variant_name()
            ))),
        }
    }

    /// Present a token to the remote silo for authorization.
    ///
    /// Generates a ZK presentation proof from the held token and sends it
    /// over the wire protocol. The silo verifies the proof without seeing
    /// the token itself.
    ///
    /// # Arguments
    ///
    /// * `token` - The token to present.
    /// * `request` - The authorization request context.
    ///
    /// # Returns
    ///
    /// A [`PresentationResult`] indicating whether the silo accepted the proof.
    pub async fn present_token(
        &mut self,
        token: &HeldToken,
        request: &pyana_token::AuthRequest,
    ) -> Result<PresentationResult, SdkError> {
        // Generate the ZK proof.
        let proof = self.wallet.prove_authorization(token, request)?;

        // Build the wire-level authorization request.
        let wire_request = AuthorizationRequest::new(
            request.app_id.as_deref().unwrap_or(""),
            request.action.as_deref().unwrap_or(""),
            &self.wallet.public_key().hex(),
        );

        let federation_root = proof.federation_root;
        // Serialize the STARK proof for transmission using the canonical binary format
        // (proof_to_bytes / proof_from_bytes). The wire server deserializes with
        // proof_from_bytes() which expects the PYNA header format, not postcard.
        let proof_bytes = proof.issuer_proof_bytes().unwrap_or_default();

        let msg = WireMessage::PresentToken {
            proof: proof_bytes,
            request: wire_request.clone(),
            federation_root,
        };

        let response = self
            .connection
            .request(msg)
            .await
            .map_err(|e| SdkError::Wire(format!("present_token failed: {e}")))?;

        match response {
            WireMessage::PresentationResult {
                accepted,
                reason,
                request_digest,
            } => Ok(PresentationResult {
                accepted,
                reason,
                request_digest,
            }),
            WireMessage::Error { message, .. } => Ok(PresentationResult {
                accepted: false,
                reason: Some(message),
                request_digest: wire_request.digest(),
            }),
            other => Err(SdkError::Wire(format!(
                "unexpected response to PresentToken: {}",
                other.variant_name()
            ))),
        }
    }

    /// Check whether a token has been revoked.
    ///
    /// Sends a `RequestNonMembership` message to the silo and interprets the
    /// response. If the silo returns a non-membership proof, the token is NOT
    /// revoked. If the proof is `None`, the token IS revoked.
    ///
    /// # Arguments
    ///
    /// * `token_id` - The token identifier to check.
    ///
    /// # Returns
    ///
    /// `true` if the token has been revoked, `false` if it is still valid.
    pub async fn check_revocation(&mut self, token_id: &str) -> Result<bool, SdkError> {
        let msg = WireMessage::RequestNonMembership {
            token_id: token_id.to_string(),
        };

        let response = self
            .connection
            .request(msg)
            .await
            .map_err(|e| SdkError::Wire(format!("check_revocation failed: {e}")))?;

        match response {
            WireMessage::NonMembershipResponse { proof, .. } => {
                // proof == Some(...) means NOT revoked (non-membership proven)
                // proof == None means IS revoked (membership confirmed)
                Ok(proof.is_none())
            }
            WireMessage::Error { message, .. } => {
                Err(SdkError::Wire(format!("revocation check error: {message}")))
            }
            other => Err(SdkError::Wire(format!(
                "unexpected response to RequestNonMembership: {}",
                other.variant_name()
            ))),
        }
    }

    /// Request the current attested revocation root from the silo.
    ///
    /// Returns the root, height, and timestamp if the silo responds correctly.
    pub async fn get_attested_root(&mut self) -> Result<([u8; 32], u64, i64), SdkError> {
        let msg = WireMessage::RequestAttestedRoot;

        let response = self
            .connection
            .request(msg)
            .await
            .map_err(|e| SdkError::Wire(format!("get_attested_root failed: {e}")))?;

        match response {
            WireMessage::AttestedRoot {
                root,
                height,
                timestamp,
                ..
            } => Ok((root, height, timestamp)),
            WireMessage::Error { message, .. } => {
                Err(SdkError::Wire(format!("attested root error: {message}")))
            }
            other => Err(SdkError::Wire(format!(
                "unexpected response to RequestAttestedRoot: {}",
                other.variant_name()
            ))),
        }
    }

    /// Submit a revocation to the remote silo.
    ///
    /// Signs the token ID with this wallet's identity and sends a
    /// `SubmitRevocation` message.
    ///
    /// # Arguments
    ///
    /// * `token_id` - The token to revoke.
    ///
    /// # Returns
    ///
    /// The new Merkle root and height after revocation, or an error.
    pub async fn submit_revocation(&mut self, token_id: &str) -> Result<([u8; 32], u64), SdkError> {
        let sig = self.wallet.sign_bytes(token_id.as_bytes());

        let msg = WireMessage::SubmitRevocation {
            token_id: token_id.to_string(),
            authority: PublicKey(self.wallet.public_key().0),
            authority_sig: Signature(sig.0),
        };

        let response = self
            .connection
            .request(msg)
            .await
            .map_err(|e| SdkError::Wire(format!("submit_revocation failed: {e}")))?;

        match response {
            WireMessage::RevocationAck { new_root, height } => Ok((new_root, height)),
            WireMessage::Error { message, .. } => Err(SdkError::Rejected(format!(
                "revocation rejected: {message}"
            ))),
            other => Err(SdkError::Wire(format!(
                "unexpected response to SubmitRevocation: {}",
                other.variant_name()
            ))),
        }
    }
}

impl std::fmt::Debug for SiloClient {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SiloClient")
            .field("address", &self.address)
            .field("wallet", &self.wallet.public_key())
            .finish()
    }
}
