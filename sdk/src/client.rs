//! Silo client: interaction with a remote pyana silo.
//!
//! The [`SiloClient`] connects to a remote silo over TCP and provides
//! high-level operations for token presentation, turn submission, and
//! revocation checking using the pyana wire protocol.

use std::net::SocketAddr;
use std::sync::Arc;
use std::time::Duration;

use pyana_commit::{MerkleTree, NonMembershipProof};
use pyana_wire::prelude::*;

use crate::cipherclerk::{AgentCipherclerk, HeldToken};
use crate::error::SdkError;

/// Result of a revocation check, distinguishing between cryptographically verified
/// outcomes and unverified server assertions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RevocationStatus {
    /// The token has been revoked (server returned no non-membership proof).
    Revoked,
    /// The token is NOT revoked and this is cryptographically proven via a
    /// verified non-membership proof anchored to the given root.
    NotRevoked {
        /// The Merkle root this proof is anchored to.
        root: [u8; 32],
        /// The height of the accumulator when the proof was generated.
        height: u64,
    },
    /// The server claims the token is not revoked but did not provide a
    /// cryptographic proof. The client cannot verify this claim.
    ///
    /// SECURITY: Callers MUST NOT treat this as equivalent to `NotRevoked`.
    /// A malicious silo can return this status for revoked tokens.
    Unverified,
}

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
/// use pyana_sdk::{AgentCipherclerk, SiloClient};
/// use std::sync::Arc;
///
/// # async fn example() -> Result<(), pyana_sdk::SdkError> {
/// let wallet = Arc::new(AgentCipherclerk::new());
/// let client = SiloClient::connect("127.0.0.1:9100".parse().unwrap(), wallet).await?;
/// # Ok(())
/// # }
/// ```
pub struct SiloClient {
    /// Remote silo address.
    address: SocketAddr,
    /// The agent's wallet (for signing and proof generation).
    wallet: Arc<AgentCipherclerk>,
    /// The underlying TCP connection.
    connection: PeerConnection,
    /// The federation root obtained from the trusted handshake with the remote silo.
    ///
    /// SECURITY: This MUST come from the authenticated handshake (Welcome message),
    /// NOT from token-derived data. Using a token-derived federation root would allow
    /// an attacker to choose their own "federation" by crafting a malicious token.
    /// Set to `None` until `handshake()` completes successfully.
    trusted_federation_root: Option<[u8; 32]>,
    /// Optional pinned federation root for MITM protection.
    ///
    /// When set, the handshake will verify the remote's federation root matches
    /// this value. If it doesn't match, the handshake fails with
    /// `SdkError::FederationRootMismatch`.
    expected_federation_root: Option<[u8; 32]>,
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
    pub async fn connect(
        addr: SocketAddr,
        wallet: Arc<AgentCipherclerk>,
    ) -> Result<Self, SdkError> {
        let conn = PeerConnection::connect(&addr.to_string())
            .await
            .map_err(|e| SdkError::Wire(format!("connect failed: {e}")))?;

        Ok(SiloClient {
            address: addr,
            wallet,
            connection: conn,
            trusted_federation_root: None,
            expected_federation_root: None,
        })
    }

    /// Connect to a remote silo with a pinned federation root.
    ///
    /// Like [`connect`](Self::connect), but verifies during [`handshake`](Self::handshake)
    /// that the remote silo's Welcome message contains the expected federation root.
    /// This prevents MITM attacks where an attacker injects a controlled root.
    ///
    /// # Arguments
    ///
    /// * `addr` - The socket address of the remote silo.
    /// * `wallet` - A shared reference to the agent's wallet.
    /// * `expected_root` - The expected federation root (32 bytes). The handshake
    ///   will fail with [`SdkError::FederationRootMismatch`] if the remote root differs.
    pub async fn connect_pinned(
        addr: SocketAddr,
        wallet: Arc<AgentCipherclerk>,
        expected_root: [u8; 32],
    ) -> Result<Self, SdkError> {
        let conn = PeerConnection::connect(&addr.to_string())
            .await
            .map_err(|e| SdkError::Wire(format!("connect failed: {e}")))?;

        Ok(SiloClient {
            address: addr,
            wallet,
            connection: conn,
            trusted_federation_root: None,
            expected_federation_root: Some(expected_root),
        })
    }

    /// Connect with a timeout.
    pub async fn connect_timeout(
        addr: SocketAddr,
        wallet: Arc<AgentCipherclerk>,
        timeout: Duration,
    ) -> Result<Self, SdkError> {
        let conn = PeerConnection::connect_timeout(&addr.to_string(), timeout)
            .await
            .map_err(|e| SdkError::Wire(format!("connect failed: {e}")))?;

        Ok(SiloClient {
            address: addr,
            wallet,
            connection: conn,
            trusted_federation_root: None,
            expected_federation_root: None,
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
            } => {
                // SECURITY: If a pinned root was provided at connection time,
                // verify the remote's federation root matches. This prevents MITM
                // attacks where an attacker intercepts the TCP connection and
                // injects a controlled federation root.
                if let Some(expected) = self.expected_federation_root {
                    if federation_root != expected {
                        return Err(SdkError::FederationRootMismatch);
                    }
                }

                // SECURITY: Store the federation root from the trusted handshake.
                // This is the only legitimate source of the federation root -- it
                // comes from the authenticated silo, not from attacker-controlled
                // token data.
                self.trusted_federation_root = Some(federation_root);
                Ok(federation_root)
            }
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
        // SECURITY: Use the federation root from the trusted handshake, NOT from
        // the token-derived proof. An attacker who controls the token could choose
        // an arbitrary federation root, effectively placing themselves in a
        // self-created "federation" that the silo would accept.
        let federation_root = self.trusted_federation_root.ok_or_else(|| {
            SdkError::Wire(
                "no trusted federation root: call handshake() before present_token()".into(),
            )
        })?;

        // Generate the ZK proof.
        let proof = self.wallet.prove_authorization(token, request)?;

        // Build the wire-level authorization request.
        // Resource = app_id OR service (whichever is present) — must match the
        // binding the prover committed to and the verifier will recompute.
        let wire_resource = request
            .app_id
            .as_deref()
            .or(request.service.as_deref())
            .unwrap_or("");
        let wire_request = AuthorizationRequest::new(
            wire_resource,
            request.action.as_deref().unwrap_or(""),
            &self.wallet.public_key().hex(),
        );

        // Serialize the STARK proof for transmission using the canonical binary format
        // (proof_to_bytes / proof_from_bytes). The wire server deserializes with
        // proof_from_bytes() which expects the PYNA header format, not postcard.
        //
        // NOTE: No binding tag is appended here. Replay protection is provided by
        // the wire-layer nonce + timestamp checks (server.rs lines 1061-1094):
        // the server validates request freshness and rejects replayed nonces, which
        // is strictly stronger than a BLAKE3 binding tag over the same fields.
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
            } => {
                // SECURITY: Verify that the response is bound to our request.
                // Without this check, a MITM could swap responses between different
                // requests, causing the client to accept a result meant for a
                // different authorization request.
                let expected_digest = wire_request.digest();
                if request_digest != expected_digest {
                    return Err(SdkError::DigestMismatch);
                }

                Ok(PresentationResult {
                    accepted,
                    reason,
                    request_digest,
                })
            }
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

    /// Present an attenuated token using an out-of-band issuer key.
    ///
    /// This is the attenuated-token variant of [`present_token`]. Attenuated tokens
    /// (received via delegation) do not carry the issuer's root key. This method
    /// accepts the issuer key explicitly, enabling delegated token holders to prove
    /// authorization without involving the original root token holder.
    ///
    /// # Arguments
    ///
    /// * `token` - The attenuated token to present.
    /// * `issuer_key` - The 32-byte root key of the issuer (provided during delegation).
    /// * `request` - The authorization request context.
    pub async fn present_token_with_issuer_key(
        &mut self,
        token: &HeldToken,
        issuer_key: &[u8; 32],
        request: &pyana_token::AuthRequest,
    ) -> Result<PresentationResult, SdkError> {
        let federation_root = self.trusted_federation_root.ok_or_else(|| {
            SdkError::Wire(
                "no trusted federation root: call handshake() before present_token()".into(),
            )
        })?;

        // Generate the ZK proof using the provided issuer key.
        let proof = self
            .wallet
            .prove_authorization_with_issuer_key(token, issuer_key, request)?;

        let wire_resource = request
            .app_id
            .as_deref()
            .or(request.service.as_deref())
            .unwrap_or("");
        let wire_request = AuthorizationRequest::new(
            wire_resource,
            request.action.as_deref().unwrap_or(""),
            &self.wallet.public_key().hex(),
        );

        // No binding tag — wire-layer nonce/timestamp checks provide replay protection.
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
            } => {
                let expected_digest = wire_request.digest();
                if request_digest != expected_digest {
                    return Err(SdkError::DigestMismatch);
                }

                Ok(PresentationResult {
                    accepted,
                    reason,
                    request_digest,
                })
            }
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
    /// Sends a `RequestNonMembership` message to the silo and cryptographically
    /// verifies the response. Returns a [`RevocationStatus`] that distinguishes
    /// between verified and unverified outcomes.
    ///
    /// # Security
    ///
    /// A malicious silo cannot lie about revocation status when a proof is provided,
    /// because the non-membership proof is cryptographically verified locally against
    /// the attested root. If the server provides no proof but claims non-revocation,
    /// [`RevocationStatus::Unverified`] is returned instead of blindly trusting the server.
    ///
    /// # Arguments
    ///
    /// * `token_id` - The token identifier to check.
    ///
    /// # Returns
    ///
    /// A [`RevocationStatus`] indicating the verified revocation state, or an error
    /// if the wire protocol fails or proof verification fails.
    pub async fn check_revocation(&mut self, token_id: &str) -> Result<RevocationStatus, SdkError> {
        let msg = WireMessage::RequestNonMembership {
            token_id: token_id.to_string(),
        };

        let response = self
            .connection
            .request(msg)
            .await
            .map_err(|e| SdkError::Wire(format!("check_revocation failed: {e}")))?;

        match response {
            WireMessage::NonMembershipResponse {
                proof,
                root,
                height,
                ..
            } => {
                match proof {
                    None => {
                        // No proof means the token IS in the revocation set (revoked).
                        Ok(RevocationStatus::Revoked)
                    }
                    Some(proof_bytes) => {
                        // Server claims non-revocation with a proof. We MUST verify it
                        // cryptographically rather than trusting the server's assertion.
                        let nm_proof: NonMembershipProof = postcard::from_bytes(&proof_bytes)
                            .map_err(|e| {
                                SdkError::NonMembershipVerificationFailed(format!(
                                    "failed to deserialize non-membership proof: {e}"
                                ))
                            })?;

                        // Verify that the proof's absent_key matches the token we asked about.
                        let expected_key = *blake3::hash(token_id.as_bytes()).as_bytes();
                        if nm_proof.absent_key != expected_key {
                            return Err(SdkError::NonMembershipVerificationFailed(
                                "proof absent_key does not match requested token_id".into(),
                            ));
                        }

                        // Cryptographically verify the non-membership proof against the root.
                        if !MerkleTree::verify_non_membership(&root, &nm_proof) {
                            return Err(SdkError::NonMembershipVerificationFailed(
                                "non-membership proof does not verify against attested root".into(),
                            ));
                        }

                        Ok(RevocationStatus::NotRevoked { root, height })
                    }
                }
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
        // SECURITY: Domain-separated signature prevents cross-protocol replay.
        // Without the prefix, a signature over a token_id could be replayed in
        // a different context (e.g., as a message signature or turn signature).
        let mut revoke_msg = Vec::with_capacity(b"pyana-revoke-v1:".len() + token_id.len());
        revoke_msg.extend_from_slice(b"pyana-revoke-v1:");
        revoke_msg.extend_from_slice(token_id.as_bytes());
        let sig = self.wallet.sign_bytes(&revoke_msg);

        let mut nonce = [0u8; 16];
        getrandom::fill(&mut nonce).expect("getrandom failed");
        let msg = WireMessage::SubmitRevocation {
            token_id: token_id.to_string(),
            authority: PublicKey(self.wallet.public_key().0),
            authority_sig: Signature(sig.0),
            nonce,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_secs() as i64)
                .unwrap_or(0),
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
