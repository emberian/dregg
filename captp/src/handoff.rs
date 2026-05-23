//! Handoff Protocol: transferring live capability references to third parties.
//!
//! A handoff transfers a live capability reference to a third party without
//! requiring the original holder and the target to be online simultaneously.
//!
//! The key insight: a [`HandoffCertificate`] is like a bearer capability proof but
//! at the NETWORK layer. It is a signed statement: "I (the introducer) authorize
//! recipient R to contact target T with these permissions."
//!
//! # Flow
//!
//! 1. **Introducer** creates a swiss entry at the target federation, then signs
//!    a `HandoffCertificate` naming the recipient.
//! 2. The certificate can travel out-of-band (QR code, email, file, BLE mesh).
//! 3. **Recipient** presents the certificate to the target federation.
//! 4. **Target** validates the introducer's signature, checks the swiss number,
//!    and creates a routing entry granting the recipient access.
//!
//! # Security Properties
//!
//! - Only the named recipient can present the certificate (recipient signature check).
//! - The target must recognize the introducer (trust path).
//! - Swiss numbers are pre-registered, preventing replay after revocation.
//! - Optional expiration and use-count limits.

use pyana_cell::{AuthRequired, EffectMask};
use pyana_types::{CellId, PublicKey, Signature, SigningKey, sign};
use serde::{Deserialize, Serialize};

use crate::FederationId;
use crate::sturdy::SwissTable;

// =============================================================================
// Errors
// =============================================================================

/// Errors during handoff validation or presentation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HandoffError {
    /// The introducer's signature on the certificate is invalid.
    InvalidIntroducerSignature,
    /// The recipient's signature on the presentation is invalid.
    InvalidRecipientSignature,
    /// The introducer is not a recognized/trusted federation.
    UntrustedIntroducer,
    /// The swiss number in the certificate is not in the target's swiss table.
    SwissNotFound,
    /// The certificate has expired (past the expiration height).
    Expired,
    /// The certificate has been used the maximum number of times.
    MaxUsesExhausted,
    /// Deserialization failed.
    DeserializationFailed(String),
    /// The nonce has already been seen (replay attempt).
    ReplayDetected,
}

impl std::fmt::Display for HandoffError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HandoffError::InvalidIntroducerSignature => {
                write!(f, "invalid introducer signature on handoff certificate")
            }
            HandoffError::InvalidRecipientSignature => {
                write!(f, "invalid recipient signature on handoff presentation")
            }
            HandoffError::UntrustedIntroducer => {
                write!(f, "introducer is not a trusted federation")
            }
            HandoffError::SwissNotFound => {
                write!(f, "swiss number not found in target's table")
            }
            HandoffError::Expired => write!(f, "handoff certificate has expired"),
            HandoffError::MaxUsesExhausted => {
                write!(f, "handoff certificate max uses exhausted")
            }
            HandoffError::DeserializationFailed(msg) => {
                write!(f, "handoff deserialization failed: {msg}")
            }
            HandoffError::ReplayDetected => write!(f, "replay detected: nonce already seen"),
        }
    }
}

impl std::error::Error for HandoffError {}

// =============================================================================
// HandoffCertificate
// =============================================================================

/// A certificate that authorizes a recipient to enliven a capability at a target federation.
///
/// Can travel out-of-band (QR code, email, file, BLE mesh message). The recipient
/// presents this to the target federation along with a proof that they are indeed
/// the named recipient.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HandoffCertificate {
    /// Who is granting the handoff (the current holder introducing the recipient).
    pub introducer: FederationId,
    /// Ed25519 signature by the introducer over the certificate's signing message.
    pub introducer_signature: Signature,

    /// The target federation hosting the capability.
    pub target_federation: FederationId,
    /// The cell on the target federation being handed off.
    pub target_cell: CellId,

    /// The recipient's Ed25519 public key (who is receiving the handoff).
    pub recipient_pk: [u8; 32],

    /// What authority is being delegated.
    pub permissions: AuthRequired,
    /// Optional effect mask restricting which effects the recipient can trigger.
    pub allowed_effects: Option<EffectMask>,

    /// Optional expiration expressed as a federation block height.
    pub expires_at: Option<u64>,
    /// Maximum number of times this certificate can be presented.
    pub max_uses: Option<u32>,
    /// Random nonce for replay prevention.
    pub nonce: [u8; 32],

    /// The swiss number the recipient should present to the target.
    /// Pre-registered by the introducer with the target's `SwissTable`.
    pub swiss: [u8; 32],
}

impl HandoffCertificate {
    /// Create a handoff certificate (called by the introducer).
    ///
    /// The introducer must have already registered a swiss entry at the target
    /// federation (via `SwissTable::export_with_options` or similar). The `swiss`
    /// parameter is the number registered at the target.
    pub fn create(
        introducer_key: &SigningKey,
        introducer_federation: FederationId,
        target_federation: FederationId,
        target_cell: CellId,
        recipient_pk: [u8; 32],
        permissions: AuthRequired,
        allowed_effects: Option<EffectMask>,
        expires_at: Option<u64>,
        max_uses: Option<u32>,
        swiss: [u8; 32],
    ) -> Self {
        let mut nonce = [0u8; 32];
        getrandom::fill(&mut nonce).expect("getrandom failed");

        // Build the certificate without signature first
        let mut cert = HandoffCertificate {
            introducer: introducer_federation,
            introducer_signature: Signature([0u8; 64]),
            target_federation,
            target_cell,
            recipient_pk,
            permissions,
            allowed_effects,
            expires_at,
            max_uses,
            nonce,
            swiss,
        };

        // Sign and fill in the signature
        let message = cert.signing_message();
        cert.introducer_signature = sign(introducer_key, &message);

        cert
    }

    /// Compute the canonical message that the introducer signs.
    ///
    /// Includes all fields except the signature itself, domain-separated
    /// to prevent cross-protocol confusion.
    pub fn signing_message(&self) -> Vec<u8> {
        let mut msg = Vec::new();
        msg.extend_from_slice(b"pyana-handoff-cert-v1");
        msg.extend_from_slice(&self.introducer.0);
        msg.extend_from_slice(&self.target_federation.0);
        msg.extend_from_slice(&self.target_cell.0);
        msg.extend_from_slice(&self.recipient_pk);
        // Encode permissions as a tag byte
        msg.push(match &self.permissions {
            AuthRequired::None => 0,
            AuthRequired::Signature => 1,
            AuthRequired::Proof => 2,
            AuthRequired::Either => 3,
            AuthRequired::Impossible => 4,
        });
        // Encode allowed_effects
        match self.allowed_effects {
            Some(mask) => {
                msg.push(0x01);
                msg.extend_from_slice(&mask.to_le_bytes());
            }
            None => {
                msg.push(0x00);
            }
        }
        // Encode expires_at
        match self.expires_at {
            Some(h) => {
                msg.push(0x01);
                msg.extend_from_slice(&h.to_le_bytes());
            }
            None => {
                msg.push(0x00);
            }
        }
        // Encode max_uses
        match self.max_uses {
            Some(n) => {
                msg.push(0x01);
                msg.extend_from_slice(&n.to_le_bytes());
            }
            None => {
                msg.push(0x00);
            }
        }
        msg.extend_from_slice(&self.nonce);
        msg.extend_from_slice(&self.swiss);
        msg
    }

    /// Verify the introducer's signature on this certificate.
    ///
    /// Requires knowing the introducer's public key (derived from their
    /// federation identity or looked up from a directory).
    pub fn verify_signature(&self, introducer_pk: &PublicKey) -> bool {
        let message = self.signing_message();
        introducer_pk.verify(&message, &self.introducer_signature)
    }

    /// Check if the certificate is still valid (not expired, not exhausted).
    ///
    /// Note: use-count checking requires external state (a nonce registry);
    /// this only checks the expiration.
    pub fn is_valid(&self, current_height: u64) -> bool {
        if let Some(exp) = self.expires_at {
            if current_height > exp {
                return false;
            }
        }
        true
    }

    /// Serialize for out-of-band transport (QR code, file, BLE).
    pub fn to_bytes(&self) -> Vec<u8> {
        postcard::to_allocvec(self).expect("handoff certificate serialization failed")
    }

    /// Deserialize from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, HandoffError> {
        postcard::from_bytes(bytes).map_err(|e| HandoffError::DeserializationFailed(e.to_string()))
    }

    /// Encode as a compact string for URLs and QR codes.
    ///
    /// Format: `pyana-handoff:<base58-encoded-bytes>`
    pub fn to_compact_string(&self) -> String {
        let bytes = self.to_bytes();
        format!("pyana-handoff:{}", bs58::encode(&bytes).into_string())
    }

    /// Decode from a compact string.
    pub fn from_compact_string(s: &str) -> Result<Self, HandoffError> {
        let rest = s.strip_prefix("pyana-handoff:").ok_or_else(|| {
            HandoffError::DeserializationFailed("missing pyana-handoff: prefix".into())
        })?;

        let bytes = bs58::decode(rest)
            .into_vec()
            .map_err(|e| HandoffError::DeserializationFailed(format!("base58 decode: {e}")))?;

        Self::from_bytes(&bytes)
    }
}

// =============================================================================
// HandoffPresentation
// =============================================================================

/// A presentation of a handoff certificate to the target federation.
///
/// The recipient signs the certificate's nonce to prove they are the named
/// recipient (not someone who intercepted the certificate in transit).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HandoffPresentation {
    /// The handoff certificate being presented.
    pub certificate: HandoffCertificate,
    /// Ed25519 signature by the recipient, proving they own the recipient_pk.
    /// Signs the presentation message (domain-separated with the nonce).
    pub recipient_signature: Signature,
}

impl HandoffPresentation {
    /// Create a presentation (called by the recipient).
    ///
    /// The recipient signs a message binding themselves to this specific certificate,
    /// proving they own the `recipient_pk` named in the certificate.
    pub fn create(certificate: HandoffCertificate, recipient_key: &SigningKey) -> Self {
        let message = Self::presentation_message(&certificate);
        let recipient_signature = sign(recipient_key, &message);
        HandoffPresentation {
            certificate,
            recipient_signature,
        }
    }

    /// The message the recipient signs to prove identity.
    ///
    /// Domain-separated and includes the nonce to prevent cross-certificate replay.
    pub fn presentation_message(cert: &HandoffCertificate) -> Vec<u8> {
        let mut msg = Vec::new();
        msg.extend_from_slice(b"pyana-handoff-present-v1");
        msg.extend_from_slice(&cert.nonce);
        msg.extend_from_slice(&cert.target_cell.0);
        msg.extend_from_slice(&cert.target_federation.0);
        msg
    }

    /// Verify the recipient's signature on this presentation.
    pub fn verify_recipient_signature(&self) -> bool {
        let pk = PublicKey(self.certificate.recipient_pk);
        let message = Self::presentation_message(&self.certificate);
        pk.verify(&message, &self.recipient_signature)
    }
}

// =============================================================================
// Handoff Validation (target side)
// =============================================================================

/// The result of a successful handoff validation at the target federation.
#[derive(Clone, Debug)]
pub struct HandoffAcceptance {
    /// A routing token the recipient can use for subsequent access.
    pub routing_token: [u8; 32],
    /// The cell they now have access to.
    pub cell_id: CellId,
    /// The permissions they were granted.
    pub permissions: AuthRequired,
    /// The effect mask, if any.
    pub allowed_effects: Option<EffectMask>,
}

/// Validate and accept/reject a handoff presentation at the target federation.
///
/// Performs the following checks:
/// 1. Verify introducer signature on certificate
/// 2. Verify recipient signature on presentation
/// 3. Check introducer is a known/trusted federation
/// 4. Check swiss number is valid in our swiss table
/// 5. Check certificate is not expired
///
/// On success, enlivens the swiss entry and returns a `HandoffAcceptance` with
/// a routing token for ongoing access.
pub fn validate_handoff(
    presentation: &HandoffPresentation,
    introducer_pk: &PublicKey,
    swiss_table: &mut SwissTable,
    known_federations: &[FederationId],
    current_height: u64,
) -> Result<HandoffAcceptance, HandoffError> {
    let cert = &presentation.certificate;

    // 1. Verify introducer signature
    if !cert.verify_signature(introducer_pk) {
        return Err(HandoffError::InvalidIntroducerSignature);
    }

    // 2. Verify recipient signature (proves the presenter owns recipient_pk)
    if !presentation.verify_recipient_signature() {
        return Err(HandoffError::InvalidRecipientSignature);
    }

    // 3. Check the introducer is a known federation
    if !known_federations.contains(&cert.introducer) {
        return Err(HandoffError::UntrustedIntroducer);
    }

    // 4. Check expiration
    if !cert.is_valid(current_height) {
        return Err(HandoffError::Expired);
    }

    // 5. Check and enliven the swiss number
    let _entry = swiss_table
        .enliven(&cert.swiss, current_height)
        .map_err(|e| match e {
            crate::sturdy::EnlivenError::NotFound => HandoffError::SwissNotFound,
            crate::sturdy::EnlivenError::Expired => HandoffError::Expired,
            crate::sturdy::EnlivenError::ExhaustedUses => HandoffError::MaxUsesExhausted,
        })?;

    // Generate a routing token for the recipient
    let mut routing_token = [0u8; 32];
    getrandom::fill(&mut routing_token).expect("getrandom failed");

    Ok(HandoffAcceptance {
        routing_token,
        cell_id: cert.target_cell,
        permissions: cert.permissions.clone(),
        allowed_effects: cert.allowed_effects,
    })
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_types::generate_keypair;

    fn setup_introducer() -> (SigningKey, PublicKey, FederationId) {
        let (sk, pk) = generate_keypair();
        let fed = FederationId(pk.0);
        (sk, pk, fed)
    }

    fn setup_recipient() -> (SigningKey, PublicKey) {
        generate_keypair()
    }

    /// Helper: create a full handoff scenario (introducer registers swiss, creates cert).
    fn full_handoff_setup() -> (
        HandoffCertificate,
        SigningKey,   // recipient key
        PublicKey,    // introducer pk
        FederationId, // introducer federation
        FederationId, // target federation
        SwissTable,   // target's swiss table (with the swiss pre-registered)
    ) {
        let (intro_sk, intro_pk, intro_fed) = setup_introducer();
        let (recip_sk, recip_pk) = setup_recipient();
        let target_fed = FederationId([0xDD; 32]);
        let target_cell = CellId([0xEE; 32]);

        // Introducer registers a swiss entry at the target
        let mut swiss_table = SwissTable::new();
        let swiss = swiss_table.export(target_cell, AuthRequired::Signature, 100, None);

        // Introducer creates the handoff certificate
        let cert = HandoffCertificate::create(
            &intro_sk,
            intro_fed,
            target_fed,
            target_cell,
            recip_pk.0,
            AuthRequired::Signature,
            None,
            None, // no expiration
            None, // unlimited uses
            swiss,
        );

        (cert, recip_sk, intro_pk, intro_fed, target_fed, swiss_table)
    }

    #[test]
    fn create_and_verify_signature() {
        let (cert, _recip_sk, intro_pk, _intro_fed, _target_fed, _swiss_table) =
            full_handoff_setup();

        assert!(cert.verify_signature(&intro_pk));

        // Wrong key should fail
        let (_, wrong_pk) = generate_keypair();
        assert!(!cert.verify_signature(&wrong_pk));
    }

    #[test]
    fn present_to_target_success() {
        let (cert, recip_sk, intro_pk, intro_fed, _target_fed, mut swiss_table) =
            full_handoff_setup();

        // Recipient creates presentation
        let presentation = HandoffPresentation::create(cert, &recip_sk);

        // Target validates
        let known = vec![intro_fed];
        let result = validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 150);

        let acceptance = result.unwrap();
        assert_eq!(acceptance.cell_id, CellId([0xEE; 32]));
        assert_eq!(acceptance.permissions, AuthRequired::Signature);
    }

    #[test]
    fn expired_certificate_rejected() {
        let (intro_sk, intro_pk, intro_fed) = setup_introducer();
        let (recip_sk, recip_pk) = setup_recipient();
        let target_fed = FederationId([0xDD; 32]);
        let target_cell = CellId([0xEE; 32]);

        let mut swiss_table = SwissTable::new();
        let swiss = swiss_table.export(target_cell, AuthRequired::Signature, 100, Some(200));

        let cert = HandoffCertificate::create(
            &intro_sk,
            intro_fed,
            target_fed,
            target_cell,
            recip_pk.0,
            AuthRequired::Signature,
            None,
            Some(200), // expires at height 200
            None,
            swiss,
        );

        let presentation = HandoffPresentation::create(cert, &recip_sk);

        let known = vec![intro_fed];
        // Present at height 201 (past expiration)
        let result = validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 201);

        assert_eq!(result.unwrap_err(), HandoffError::Expired);
    }

    #[test]
    fn wrong_recipient_rejected() {
        let (cert, _recip_sk, intro_pk, intro_fed, _target_fed, mut swiss_table) =
            full_handoff_setup();

        // An impostor tries to present (different key than recipient_pk)
        let (impostor_sk, _impostor_pk) = generate_keypair();
        let presentation = HandoffPresentation::create(cert, &impostor_sk);

        let known = vec![intro_fed];
        let result = validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 150);

        assert_eq!(result.unwrap_err(), HandoffError::InvalidRecipientSignature);
    }

    #[test]
    fn untrusted_introducer_rejected() {
        let (cert, recip_sk, intro_pk, _intro_fed, _target_fed, mut swiss_table) =
            full_handoff_setup();

        let presentation = HandoffPresentation::create(cert, &recip_sk);

        // Empty known federations list (introducer not trusted)
        let known: Vec<FederationId> = vec![];
        let result = validate_handoff(&presentation, &intro_pk, &mut swiss_table, &known, 150);

        assert_eq!(result.unwrap_err(), HandoffError::UntrustedIntroducer);
    }

    #[test]
    fn max_uses_exhausted() {
        let (intro_sk, intro_pk, intro_fed) = setup_introducer();
        let (recip_sk, recip_pk) = setup_recipient();
        let target_fed = FederationId([0xDD; 32]);
        let target_cell = CellId([0xEE; 32]);

        let mut swiss_table = SwissTable::new();
        // Swiss entry with max_uses = 1
        let swiss = swiss_table.export_with_options(
            target_cell,
            AuthRequired::Signature,
            100,
            None,
            None,
            Some(1), // one-time use
        );

        let cert = HandoffCertificate::create(
            &intro_sk,
            intro_fed,
            target_fed,
            target_cell,
            recip_pk.0,
            AuthRequired::Signature,
            None,
            None,
            Some(1),
            swiss,
        );

        let known = vec![intro_fed];

        // First presentation succeeds
        let presentation1 = HandoffPresentation::create(cert.clone(), &recip_sk);
        let result = validate_handoff(&presentation1, &intro_pk, &mut swiss_table, &known, 150);
        assert!(result.is_ok());

        // Second presentation fails (swiss exhausted)
        let presentation2 = HandoffPresentation::create(cert, &recip_sk);
        let result = validate_handoff(&presentation2, &intro_pk, &mut swiss_table, &known, 151);
        assert_eq!(result.unwrap_err(), HandoffError::MaxUsesExhausted);
    }

    #[test]
    fn compact_string_roundtrip() {
        let (cert, _recip_sk, _intro_pk, _intro_fed, _target_fed, _swiss_table) =
            full_handoff_setup();

        let compact = cert.to_compact_string();
        assert!(compact.starts_with("pyana-handoff:"));

        let decoded = HandoffCertificate::from_compact_string(&compact).unwrap();
        assert_eq!(decoded.introducer, cert.introducer);
        assert_eq!(decoded.target_federation, cert.target_federation);
        assert_eq!(decoded.target_cell, cert.target_cell);
        assert_eq!(decoded.recipient_pk, cert.recipient_pk);
        assert_eq!(decoded.nonce, cert.nonce);
        assert_eq!(decoded.swiss, cert.swiss);
        assert_eq!(decoded.introducer_signature, cert.introducer_signature);
    }

    #[test]
    fn bytes_roundtrip() {
        let (cert, _recip_sk, _intro_pk, _intro_fed, _target_fed, _swiss_table) =
            full_handoff_setup();

        let bytes = cert.to_bytes();
        let decoded = HandoffCertificate::from_bytes(&bytes).unwrap();
        assert_eq!(decoded.nonce, cert.nonce);
        assert_eq!(decoded.swiss, cert.swiss);
    }

    #[test]
    fn invalid_compact_string_prefix() {
        let result = HandoffCertificate::from_compact_string("invalid:abc");
        assert!(matches!(
            result,
            Err(HandoffError::DeserializationFailed(_))
        ));
    }

    #[test]
    fn certificate_validity_check() {
        let (cert_no_expiry, _, _, _, _, _) = full_handoff_setup();

        // No expiry: always valid
        assert!(cert_no_expiry.is_valid(0));
        assert!(cert_no_expiry.is_valid(u64::MAX));

        // With expiry
        let (intro_sk, _intro_pk, intro_fed) = setup_introducer();
        let (_, recip_pk) = setup_recipient();
        let target_fed = FederationId([0xDD; 32]);
        let target_cell = CellId([0xEE; 32]);

        let cert_with_expiry = HandoffCertificate::create(
            &intro_sk,
            intro_fed,
            target_fed,
            target_cell,
            recip_pk.0,
            AuthRequired::Signature,
            None,
            Some(500), // expires at height 500
            None,
            [0x42; 32],
        );

        assert!(cert_with_expiry.is_valid(499));
        assert!(cert_with_expiry.is_valid(500)); // at expiry height: still valid
        assert!(!cert_with_expiry.is_valid(501)); // past expiry: invalid
    }

    #[test]
    fn out_of_band_scenario() {
        // Simulates: create certificate offline, transport as string, present later
        let (intro_sk, intro_pk, intro_fed) = setup_introducer();
        let (recip_sk, recip_pk) = setup_recipient();
        let target_fed = FederationId([0xDD; 32]);
        let target_cell = CellId([0xEE; 32]);

        // Step 1: Introducer registers swiss at target (online)
        let mut swiss_table = SwissTable::new();
        let swiss = swiss_table.export(target_cell, AuthRequired::Signature, 100, None);

        // Step 2: Introducer creates cert and encodes to string (can be offline)
        let cert = HandoffCertificate::create(
            &intro_sk,
            intro_fed,
            target_fed,
            target_cell,
            recip_pk.0,
            AuthRequired::Signature,
            None,
            None,
            None,
            swiss,
        );
        let compact = cert.to_compact_string();

        // Step 3: Time passes... certificate travels out-of-band (QR, email, etc.)

        // Step 4: Recipient decodes and presents (online, potentially much later)
        let decoded_cert = HandoffCertificate::from_compact_string(&compact).unwrap();
        let presentation = HandoffPresentation::create(decoded_cert, &recip_sk);

        // Step 5: Target validates
        let known = vec![intro_fed];
        let acceptance = validate_handoff(
            &presentation,
            &intro_pk,
            &mut swiss_table,
            &known,
            500, // much later
        )
        .unwrap();

        assert_eq!(acceptance.cell_id, target_cell);
        assert_eq!(acceptance.permissions, AuthRequired::Signature);
    }
}
