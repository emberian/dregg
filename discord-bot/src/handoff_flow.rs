//! Real, canonical capability-handoff flow — the bot as a genuine third dregg
//! peer (§4.7 "bot-as-third-dregg-peer").
//!
//! This module is **Discord-independent** on purpose. It produces and validates
//! the canonical [`dregg_captp::handoff::HandoffCertificate`] /
//! [`HandoffPresentation`] artifacts using the canonical CapTP crate. There is
//! NO placeholder MAC, NO mock string: the certificate carries a real Ed25519
//! signature by the introducer (the bot, acting on behalf of a hosted user
//! cell), the compact wire form is the canonical `dregg-handoff:<base58>`, and
//! redemption runs the canonical `validate_handoff` against a real
//! [`SwissTable`].
//!
//! The contrast with the legacy [`crate::captp_client`] path (a BLAKE3-MAC over
//! a `dregg-handoff-<hex>` token, stored only in the bot's SQLite) is
//! deliberate: that path never produced a verifiable protocol artifact. This
//! module is the real thing and is unit-tested without Discord.
//!
//! # Roles
//!
//! - **Introducer**: the bot, signing with the *hosted user's* derived
//!   Ed25519 key (the user delegating a capability they own). The introducer
//!   federation id is the user's cell-derived `FederationId` so
//!   `verify_signature` checks against the same key that signed.
//! - **Target federation**: the bot's own soft-federation root (the friend
//!   clique), whose `SwissTable` holds the pre-registered swiss entry. This is
//!   the [`crate::BotState::nullifier_set`] sibling — the bot is the tiny
//!   federation that orders redemptions.
//! - **Recipient**: another hosted user, identified by their Ed25519 public
//!   key (== first 32 bytes of their cell-key material). Only the named
//!   recipient can present the certificate (recipient-signature check).
//!
//! # What is real end-to-end vs. what needs a node round-trip
//!
//! Real, headless-testable here: cert creation + signature, compact
//! encode/decode, recipient presentation, and `validate_handoff` against the
//! bot's swiss table (introducer-sig, recipient-sig, known-federation, swiss
//! enliven). The resulting `HandoffAcceptance.routing_token` is a real grant
//! *within the bot's soft-federation*. Promoting that routing token into a
//! live capability session on the canonical `dregg-node` still needs the node
//! to expose a `/captp/enliven`-style endpoint (it does not yet — see
//! `captp_client.rs` module docs). That is the one named gap; everything up to
//! and including a verified `HandoffAcceptance` is genuine.

use dregg_captp::FederationId;
use dregg_captp::handoff::{
    HandoffAcceptance, HandoffCertificate, HandoffError, HandoffPresentation, validate_handoff,
};
use dregg_captp::sturdy::SwissTable;
use dregg_cell::permissions::AuthRequired;
use dregg_types::{CellId, PublicKey, SigningKey};

/// Errors from the canonical handoff flow.
#[derive(Debug, Clone)]
pub enum HandoffFlowError {
    /// A hex field (cell id / pubkey) was malformed.
    BadHex(String),
    /// The canonical CapTP layer rejected the operation.
    Captp(HandoffError),
}

impl std::fmt::Display for HandoffFlowError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HandoffFlowError::BadHex(m) => write!(f, "invalid hex: {m}"),
            HandoffFlowError::Captp(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for HandoffFlowError {}

impl From<HandoffError> for HandoffFlowError {
    fn from(e: HandoffError) -> Self {
        HandoffFlowError::Captp(e)
    }
}

fn parse_32(hex_str: &str, what: &str) -> Result<[u8; 32], HandoffFlowError> {
    let bytes =
        hex::decode(hex_str).map_err(|e| HandoffFlowError::BadHex(format!("{what}: {e}")))?;
    bytes
        .try_into()
        .map_err(|b: Vec<u8>| HandoffFlowError::BadHex(format!("{what}: expected 32 bytes, got {}", b.len())))
}

/// The bot's soft-federation handoff broker.
///
/// Holds the canonical target [`SwissTable`] (the friend clique's federation)
/// plus the set of introducer federations the bot trusts. A single
/// [`HandoffBroker`] is the "bot as a tiny federation" of §4.7: it is the
/// target that orders and accepts handoff redemptions among the clique.
pub struct HandoffBroker {
    /// The bot's federation id — the target federation hosting handed-off cells.
    target_federation: FederationId,
    /// Canonical swiss table for the target federation.
    swiss: SwissTable,
    /// Introducer federations the bot recognizes (clique members + the bot).
    known_introducers: Vec<FederationId>,
}

/// The output of minting a handoff: the canonical certificate plus its
/// compact `dregg-handoff:<base58>` wire form (paste into a Discord channel).
#[derive(Debug, Clone)]
pub struct MintedHandoff {
    /// The signed canonical certificate.
    pub certificate: HandoffCertificate,
    /// The paste-friendly compact form.
    pub compact: String,
    /// The introducer public key the recipient (or anyone) uses to verify.
    pub introducer_pk: [u8; 32],
}

impl HandoffBroker {
    /// Create a broker for the bot's federation.
    pub fn new(target_federation: FederationId) -> Self {
        Self {
            target_federation,
            swiss: SwissTable::new(),
            known_introducers: Vec::new(),
        }
    }

    /// Trust an introducer federation (a clique member who may delegate).
    pub fn trust_introducer(&mut self, fed: FederationId) {
        if !self.known_introducers.contains(&fed) {
            self.known_introducers.push(fed);
        }
    }

    /// Number of live swiss entries the broker is hosting.
    pub fn swiss_len(&self) -> usize {
        self.swiss.len()
    }

    /// Mint a **real** signed handoff certificate.
    ///
    /// `introducer_secret` is the hosted user's derived 32-byte Ed25519 seed
    /// (the same seed `UserCipherclerk` holds). The introducer federation id is
    /// derived from that key's public key so `verify_signature` lines up. The
    /// introducer is auto-trusted (the bot recognizes its own clique members).
    ///
    /// The swiss entry for `target_cell` is registered in the broker's table so
    /// the recipient can later redeem.
    pub fn mint_handoff(
        &mut self,
        introducer_secret: &[u8; 32],
        target_cell_hex: &str,
        recipient_pk_hex: &str,
        current_height: u64,
        expires_at: Option<u64>,
        max_uses: Option<u32>,
    ) -> Result<MintedHandoff, HandoffFlowError> {
        let target_cell = CellId(parse_32(target_cell_hex, "target_cell")?);
        let recipient_pk = parse_32(recipient_pk_hex, "recipient_pk")?;

        let introducer_key = SigningKey::from_bytes(introducer_secret);
        let introducer_pk = introducer_key.public_key();
        // The introducer's federation identity is its own public key — a single
        // Ed25519 trust root per clique peer (matches the §4.7 "single Ed25519
        // trust root for the clique" framing and the captp test convention
        // `FederationId(pk.0)`).
        let introducer_federation = FederationId(introducer_pk.0);
        self.trust_introducer(introducer_federation);

        // Register the swiss entry in the *target* (bot) federation's table.
        // Signature auth: the recipient must prove ownership of recipient_pk.
        let swiss = self.swiss.export_with_options(
            target_cell,
            AuthRequired::Signature,
            current_height,
            expires_at,
            None,
            max_uses,
        );

        let certificate = HandoffCertificate::create(
            // dregg_captp re-exports its own SigningKey type alias from
            // dregg_types, so this is the same concrete type.
            &introducer_key,
            introducer_federation,
            self.target_federation,
            target_cell,
            recipient_pk,
            AuthRequired::Signature,
            None,
            expires_at,
            max_uses,
            swiss,
        );

        // Sanity: the cert we just produced must verify against the introducer
        // key (defensive — proves we wired signing correctly before posting).
        debug_assert!(certificate.verify_signature(&introducer_pk));

        let compact = certificate.to_compact_string();
        Ok(MintedHandoff {
            certificate,
            compact,
            introducer_pk: introducer_pk.0,
        })
    }

    /// Redeem a handoff: the recipient presents the certificate and proves
    /// ownership of `recipient_pk`. Runs the canonical `validate_handoff`
    /// against the broker's swiss table.
    ///
    /// `recipient_secret` is the redeeming user's derived 32-byte Ed25519 seed.
    /// Returns a real [`HandoffAcceptance`] (routing token + granted authority)
    /// on success.
    pub fn redeem_handoff(
        &mut self,
        compact: &str,
        recipient_secret: &[u8; 32],
        introducer_pk: &[u8; 32],
        current_height: u64,
    ) -> Result<HandoffAcceptance, HandoffFlowError> {
        let certificate = HandoffCertificate::from_compact_string(compact)?;
        let recipient_key = SigningKey::from_bytes(recipient_secret);
        let presentation = HandoffPresentation::create(certificate, &recipient_key);

        let introducer_public = PublicKey(*introducer_pk);
        let acceptance = validate_handoff(
            &presentation,
            &introducer_public,
            &mut self.swiss,
            &self.known_introducers,
            current_height,
        )?;
        Ok(acceptance)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Derive a user's 32-byte seed exactly as `UserCipherclerk::derive` does,
    /// so this test exercises the same key material the bot would use.
    fn user_seed(bot_secret: &[u8; 32], discord_user_id: u64) -> [u8; 32] {
        let mut input = Vec::with_capacity(40);
        input.extend_from_slice(bot_secret);
        input.extend_from_slice(&discord_user_id.to_le_bytes());
        blake3::derive_key("dregg-discord-bot-v1", &input)
    }

    fn pubkey_hex(seed: &[u8; 32]) -> String {
        hex::encode(SigningKey::from_bytes(seed).public_key().0)
    }

    #[test]
    fn mint_produces_a_real_signed_certificate_that_verifies() {
        let bot_secret = [7u8; 32];
        let alice_seed = user_seed(&bot_secret, 1111);
        let bob_seed = user_seed(&bot_secret, 2222);

        let mut broker = HandoffBroker::new(FederationId([42u8; 32]));

        // Alice (introducer) delegates a cell she owns to Bob (recipient).
        let target_cell = hex::encode([0xabu8; 32]);
        let minted = broker
            .mint_handoff(&alice_seed, &target_cell, &pubkey_hex(&bob_seed), 100, Some(200), Some(1))
            .expect("mint should succeed");

        // The compact string is the canonical wire form.
        assert!(minted.compact.starts_with("dregg-handoff:"));

        // The signature on the certificate verifies against the *real*
        // introducer public key — this is the core "real signed artifact"
        // assertion. A placeholder MAC could never satisfy ed25519 verify.
        let introducer_pk = PublicKey(minted.introducer_pk);
        assert!(
            minted.certificate.verify_signature(&introducer_pk),
            "minted certificate must carry a valid Ed25519 introducer signature"
        );

        // Round-trips through the canonical compact codec losslessly.
        let decoded = HandoffCertificate::from_compact_string(&minted.compact).unwrap();
        assert!(decoded.verify_signature(&introducer_pk));
        assert_eq!(decoded.recipient_pk, SigningKey::from_bytes(&bob_seed).public_key().0);
        assert_eq!(decoded.swiss, minted.certificate.swiss);
    }

    #[test]
    fn tampered_certificate_fails_verification() {
        let bot_secret = [9u8; 32];
        let alice_seed = user_seed(&bot_secret, 1);
        let bob_seed = user_seed(&bot_secret, 2);
        let mut broker = HandoffBroker::new(FederationId([1u8; 32]));
        let minted = broker
            .mint_handoff(&alice_seed, &hex::encode([5u8; 32]), &pubkey_hex(&bob_seed), 0, None, None)
            .unwrap();

        // Flip the recipient pubkey — signature must no longer verify.
        let mut tampered = minted.certificate.clone();
        tampered.recipient_pk[0] ^= 0xff;
        let introducer_pk = PublicKey(minted.introducer_pk);
        assert!(
            !tampered.verify_signature(&introducer_pk),
            "tampering with a signed field must invalidate the signature"
        );
    }

    #[test]
    fn named_recipient_redeems_real_acceptance() {
        let bot_secret = [3u8; 32];
        let alice_seed = user_seed(&bot_secret, 10);
        let bob_seed = user_seed(&bot_secret, 20);
        let bot_fed = FederationId([77u8; 32]);
        let mut broker = HandoffBroker::new(bot_fed);

        let minted = broker
            .mint_handoff(&alice_seed, &hex::encode([0xcdu8; 32]), &pubkey_hex(&bob_seed), 5, Some(100), Some(1))
            .unwrap();
        assert_eq!(broker.swiss_len(), 1);

        // Bob, the named recipient, redeems against the bot's swiss table.
        let acceptance = broker
            .redeem_handoff(&minted.compact, &bob_seed, &minted.introducer_pk, 6)
            .expect("named recipient must be able to redeem");
        assert_eq!(acceptance.cell_id, CellId([0xcdu8; 32]));
        assert_eq!(acceptance.permissions, AuthRequired::Signature);
    }

    #[test]
    fn wrong_recipient_cannot_redeem() {
        let bot_secret = [4u8; 32];
        let alice_seed = user_seed(&bot_secret, 100);
        let bob_seed = user_seed(&bot_secret, 200);
        let mallory_seed = user_seed(&bot_secret, 300);
        let mut broker = HandoffBroker::new(FederationId([8u8; 32]));

        let minted = broker
            .mint_handoff(&alice_seed, &hex::encode([1u8; 32]), &pubkey_hex(&bob_seed), 0, None, None)
            .unwrap();

        // Mallory (not the named recipient) presents — recipient-sig check fails.
        let err = broker
            .redeem_handoff(&minted.compact, &mallory_seed, &minted.introducer_pk, 1)
            .expect_err("only the named recipient may redeem");
        assert!(matches!(
            err,
            HandoffFlowError::Captp(HandoffError::InvalidRecipientSignature)
        ));
    }

    #[test]
    fn untrusted_introducer_is_rejected() {
        // A certificate whose introducer the broker does not know must fail.
        let bot_secret = [6u8; 32];
        let alice_seed = user_seed(&bot_secret, 1);
        let bob_seed = user_seed(&bot_secret, 2);
        let mut broker = HandoffBroker::new(FederationId([2u8; 32]));
        let minted = broker
            .mint_handoff(&alice_seed, &hex::encode([7u8; 32]), &pubkey_hex(&bob_seed), 0, None, None)
            .unwrap();

        // Forget the introducer to simulate an unknown delegator.
        broker.known_introducers.clear();
        let err = broker
            .redeem_handoff(&minted.compact, &bob_seed, &minted.introducer_pk, 1)
            .expect_err("unknown introducer must be rejected");
        assert!(matches!(
            err,
            HandoffFlowError::Captp(HandoffError::UntrustedIntroducer)
        ));
    }
}
