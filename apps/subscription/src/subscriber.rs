//! Subscribers: subscribe to tiers, hold an X25519 receive key, and authorize
//! the payment executor to auto-debit them via a signed `DelegatedToken`.
//!
//! # Identity model
//!
//! A subscriber has TWO distinct keypairs:
//!
//! 1. **Ed25519 identity** (`identity_pk`): the subscriber's cclerk pubkey.
//!    This is what signs delegation envelopes and identifies them in the
//!    `Ledger`. The corresponding private key is held by the subscriber's
//!    `pyana_sdk::AgentCipherclerk`.
//! 2. **X25519 receive key** (`recv_pubkey`): published so content creators
//!    can encrypt-to-subscriber. See `crypto.rs::encrypt_for`.
//!
//! These keys are **independent** — they protect different concerns (signing
//! vs. encryption) and would have different rotation cadences in production.

use std::collections::HashMap;

use pyana_sdk::cipherclerk::{DelegatedToken, DelegationAuthority};
use pyana_sdk::{AgentCipherclerk, SdkError};
use pyana_types::PublicKey;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::creator::Tier;

/// One subscription record: subscriber X tier.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Subscription {
    /// Subscriber's Ed25519 identity.
    pub subscriber: PublicKey,
    /// Tier id (must exist in the creator's tier list).
    pub tier_id: String,
    /// Creator (a single subscription targets exactly one creator).
    pub creator: PublicKey,
    /// X25519 public key the creator should encrypt content to.
    pub recv_pubkey: [u8; 32],
    /// Active flag — set false when the subscriber cancels.
    pub active: bool,
}

/// Errors specific to subscriber operations.
#[derive(Debug, Error)]
pub enum SubscriberError {
    #[error("tier {0:?} not offered by creator")]
    UnknownTier(String),
    #[error("tier {0:?} is gated but subscriber presented no credential")]
    MissingCredential(String),
    #[error("credential not signed by tier's expected issuer")]
    WrongCredentialIssuer,
    #[error("credential rejected by the SDK: {0}")]
    InvalidCredential(String),
    #[error("auto-debit delegation envelope rejected: {0}")]
    InvalidDelegation(String),
    #[error("auto-debit envelope is missing the budget caveat (asset+limit)")]
    MissingBudgetCaveat,
    #[error("auto-debit envelope's budget.class {0:?} is not 'asset:<u64>'")]
    BadBudgetAssetClass(String),
}

/// Auto-debit authorization, derived from a verified `DelegatedToken`.
///
/// **Only constructed via [`SubscriberRegistry::receive_debit_delegation`]**,
/// which runs the SDK's full
/// [`AgentCipherclerk::receive_signed_delegation`](pyana_sdk::AgentCipherclerk::receive_signed_delegation)
/// path under [`DelegationAuthority::TrustedKey(subscriber)`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DebitAuthorization {
    /// The subscriber whose balance can be debited.
    pub subscriber: PublicKey,
    /// The asset (token) this delegation authorizes debits of.
    pub asset_id: u64,
    /// Max units the executor may debit per epoch.
    pub max_per_epoch: u64,
    /// Wall-clock seconds (Unix epoch) at which this authorization expires.
    /// Mirrors the envelope's `restrictions.not_after`.
    pub expires_at_unix_secs: Option<i64>,
    /// The delegation envelope hash; used for revocation lookups
    /// (REVIEW[P2]: revocation set not yet implemented).
    pub envelope_hash: [u8; 32],
}

// REVIEW[P2]: `envelope_hash` is recorded but no revocation set exists. The
// signed envelope's signature has already been verified in
// `receive_debit_delegation`; what's missing is a way to *revoke* a specific
// envelope later (e.g., the subscriber changes limits). Cleanest fix: a
// `revoked: HashSet<[u8; 32]>` on `SubscriberRegistry` consulted by the
// executor before debiting.

/// In-memory registry of subscribers, their subscriptions, and their active
/// auto-debit authorizations.
#[derive(Default)]
pub struct SubscriberRegistry {
    /// Subscriber identity -> their X25519 receive key.
    pub recv_keys: HashMap<PublicKey, [u8; 32]>,
    /// All subscriptions.
    pub subscriptions: Vec<Subscription>,
    /// All active auto-debit authorizations, keyed by subscriber pk.
    pub debit_authorizations: HashMap<PublicKey, DebitAuthorization>,
}

impl SubscriberRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register (or update) a subscriber's X25519 receive pubkey.
    pub fn register_subscriber(&mut self, identity: PublicKey, recv_pubkey: [u8; 32]) {
        self.recv_keys.insert(identity, recv_pubkey);
    }

    /// Subscribe `subscriber` to `creator`'s `tier`.
    ///
    /// If the tier is credential-gated, `credential` must be `Some(envelope)`,
    /// the envelope's `delegatee` must equal `subscriber`, and the envelope
    /// must be signed by the tier's `credential_issuer`. We verify the
    /// signature using the SDK's envelope-hash helper + ed25519 directly
    /// (the SDK's full `receive_signed_delegation` path is exercised on the
    /// executor side for auto-debit envelopes; credential envelopes are
    /// directly verified here because we don't have a subscriber-side
    /// AgentCipherclerk in process).
    pub fn subscribe(
        &mut self,
        subscriber: PublicKey,
        creator: PublicKey,
        tier: &Tier,
        credential: Option<DelegatedToken>,
    ) -> Result<&Subscription, SubscriberError> {
        if let Some(issuer) = tier.credential_issuer {
            let envelope =
                credential.ok_or_else(|| SubscriberError::MissingCredential(tier.id.clone()))?;
            verify_credential_envelope(&envelope, &subscriber, &issuer)?;
        }

        let recv_pubkey = self
            .recv_keys
            .get(&subscriber)
            .copied()
            .unwrap_or([0u8; 32]);

        self.subscriptions.retain(|s| {
            !(s.subscriber == subscriber && s.creator == creator && s.tier_id == tier.id)
        });
        self.subscriptions.push(Subscription {
            subscriber,
            tier_id: tier.id.clone(),
            creator,
            recv_pubkey,
            active: true,
        });
        Ok(self.subscriptions.last().unwrap())
    }

    /// Receive a subscriber's auto-debit delegation envelope.
    ///
    /// `executor_cipherclerk` MUST be the payment executor's cipherclerk — its
    /// `public_key()` must equal the envelope's `delegatee`. This function
    /// uses [`AgentCipherclerk::receive_signed_delegation`] with
    /// [`DelegationAuthority::TrustedKey(subscriber)`] to perform the full
    /// envelope verification (signature, structural validity, authority).
    ///
    /// On success, the executor cipherclerk adds a `HeldToken` to its token list
    /// **and** this registry records a [`DebitAuthorization`] keyed by
    /// `subscriber`.
    pub fn receive_debit_delegation(
        &mut self,
        executor_cipherclerk: &mut AgentCipherclerk,
        subscriber: PublicKey,
        envelope: DelegatedToken,
    ) -> Result<&DebitAuthorization, SubscriberError> {
        // (1) Pre-check delegatee matches the executor's cclerk.
        if envelope.delegatee != executor_cipherclerk.public_key() {
            return Err(SubscriberError::InvalidDelegation(format!(
                "envelope addressed to {:?}, not executor {:?}",
                envelope.delegatee,
                executor_cipherclerk.public_key(),
            )));
        }

        // (2) Pre-check claimed delegator matches the subscriber.
        if envelope.delegator_public_key != subscriber {
            return Err(SubscriberError::InvalidDelegation(format!(
                "envelope claims delegator {:?}, expected subscriber {:?}",
                envelope.delegator_public_key, subscriber,
            )));
        }

        // (3) Extract asset+limit from the budget caveat BEFORE consuming the
        //     envelope (we need to clone the budget). The SDK accepts
        //     restrictions of any shape, but for auto-debit we MANDATE a
        //     budget caveat.
        let budget = envelope
            .restrictions
            .budget
            .clone()
            .ok_or(SubscriberError::MissingBudgetCaveat)?;
        let asset_id: u64 = budget
            .class
            .strip_prefix("asset:")
            .and_then(|s| s.parse::<u64>().ok())
            .ok_or_else(|| SubscriberError::BadBudgetAssetClass(budget.class.clone()))?;
        let max_per_epoch = budget.limit;
        let expires_at_unix_secs = envelope.restrictions.not_after;
        let envelope_hash = envelope.envelope_hash();

        // (4) THE CANONICAL CALL: hand the envelope to the SDK's full
        //     verification path. This checks: structural validity, expiry,
        //     delegatee binding, signature, authority (`TrustedKey`), and
        //     freshness of the binding.
        executor_cipherclerk
            .receive_signed_delegation(envelope, &DelegationAuthority::TrustedKey(subscriber))
            .map_err(SubscriberError::from)?;

        let auth = DebitAuthorization {
            subscriber,
            asset_id,
            max_per_epoch,
            expires_at_unix_secs,
            envelope_hash,
        };
        self.debit_authorizations.insert(subscriber, auth);
        Ok(self.debit_authorizations.get(&subscriber).unwrap())
    }

    /// All ACTIVE subscriptions for `creator` and `tier_id`.
    pub fn subscribers_of(&self, creator: PublicKey, tier_id: &str) -> Vec<&Subscription> {
        self.subscriptions
            .iter()
            .filter(|s| s.active && s.creator == creator && s.tier_id == tier_id)
            .collect()
    }
}

/// Verify a credential envelope (delegatee = subscriber, signer = expected
/// issuer). We don't have a subscriber-side `AgentCipherclerk` to drive
/// `receive_signed_delegation`, so verify the signature directly using the
/// envelope's published `envelope_hash()` helper.
fn verify_credential_envelope(
    envelope: &DelegatedToken,
    subscriber_pk: &PublicKey,
    expected_issuer: &PublicKey,
) -> Result<(), SubscriberError> {
    use ed25519_dalek::{Signature, Verifier, VerifyingKey};

    if envelope.delegatee != *subscriber_pk {
        return Err(SubscriberError::InvalidCredential(format!(
            "credential.delegatee {:?} != subscriber {:?}",
            envelope.delegatee, subscriber_pk,
        )));
    }
    if envelope.delegator_public_key != *expected_issuer {
        return Err(SubscriberError::WrongCredentialIssuer);
    }
    // Expiry.
    if let Some(not_after) = envelope.restrictions.not_after {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0);
        if not_after <= now {
            return Err(SubscriberError::InvalidCredential(format!(
                "credential expired (not_after={not_after}, now={now})"
            )));
        }
    }
    let signing_message = envelope.envelope_hash();
    let vk = VerifyingKey::from_bytes(&envelope.delegator_public_key.0)
        .map_err(|e| SubscriberError::InvalidCredential(format!("bad issuer pubkey: {e}")))?;
    let sig = Signature::from_bytes(&envelope.delegator_signature.0);
    vk.verify(&signing_message, &sig)
        .map_err(|e| SubscriberError::InvalidCredential(format!("signature failed: {e}")))?;
    Ok(())
}

// REVIEW[P3]: credential verification here is hand-rolled (ed25519 + envelope
// hash). The SDK exposes `receive_signed_delegation` for envelopes addressed
// to the current cclerk, but credentials are addressed to the *subscriber*,
// not to the executor, so the executor's cclerk can't drive that path
// directly. A framework gap: `AgentCipherclerk::verify_envelope` (no token
// installation, just signature+authority) would let us reuse the SDK path
// for third-party credentials.

/// Helper: bridge `SdkError` -> `SubscriberError` for `?`.
impl From<SdkError> for SubscriberError {
    fn from(e: SdkError) -> Self {
        SubscriberError::InvalidDelegation(e.to_string())
    }
}

/// Construct an `AgentCipherclerk` bound to a given 32-byte secret. Used by tests
/// and the server to build the executor cipherclerk with a predictable identity.
pub fn deterministic_cclerk(secret: [u8; 32]) -> AgentCipherclerk {
    use zeroize::Zeroizing;
    AgentCipherclerk::from_key_bytes(Zeroizing::new(secret))
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::creator::{Creator, Tier};
    use pyana_sdk::Attenuation;
    use pyana_token::BudgetSpec;

    fn cclerk(seed: u8) -> AgentCipherclerk {
        let mut s = [0u8; 32];
        s[0] = seed;
        s[31] = seed.wrapping_mul(13);
        deterministic_cclerk(s)
    }

    #[test]
    fn free_tier_subscribe_no_credential() {
        let mut reg = SubscriberRegistry::new();
        let alice_w = cclerk(1);
        let creator_w = cclerk(2);

        reg.register_subscriber(alice_w.public_key(), [9u8; 32]);
        let mut creator = Creator::new(creator_w.public_key());
        creator.add_tier(Tier::free("free", "Free", 1));

        let r = reg.subscribe(
            alice_w.public_key(),
            creator_w.public_key(),
            creator.tier("free").unwrap(),
            None,
        );
        assert!(r.is_ok());
    }

    #[test]
    fn premium_tier_without_credential_is_rejected() {
        let mut reg = SubscriberRegistry::new();
        let alice_w = cclerk(3);
        let creator_w = cclerk(4);
        let issuer_w = cclerk(5);

        reg.register_subscriber(alice_w.public_key(), [9u8; 32]);
        let mut creator = Creator::new(creator_w.public_key());
        creator.add_tier(Tier::premium("vip", "VIP", 1, 100, issuer_w.public_key()));

        let r = reg.subscribe(
            alice_w.public_key(),
            creator_w.public_key(),
            creator.tier("vip").unwrap(),
            None,
        );
        assert!(matches!(r, Err(SubscriberError::MissingCredential(_))));
    }

    #[test]
    fn premium_tier_with_wrong_issuer_is_rejected() {
        let mut reg = SubscriberRegistry::new();
        let alice_w = cclerk(6);
        let creator_w = cclerk(7);
        let real_issuer_w = cclerk(8);
        let mut fake_issuer_w = cclerk(9);

        reg.register_subscriber(alice_w.public_key(), [9u8; 32]);
        let mut creator = Creator::new(creator_w.public_key());
        creator.add_tier(Tier::premium(
            "vip",
            "VIP",
            1,
            100,
            real_issuer_w.public_key(),
        ));

        let token = fake_issuer_w.mint_token(&[42u8; 32], "premium");
        let restrictions = Attenuation {
            not_after: Some(i64::MAX),
            ..Default::default()
        };
        let env = fake_issuer_w
            .delegate(&token, &alice_w.public_key(), &restrictions)
            .unwrap();

        let r = reg.subscribe(
            alice_w.public_key(),
            creator_w.public_key(),
            creator.tier("vip").unwrap(),
            Some(env),
        );
        assert!(matches!(r, Err(SubscriberError::WrongCredentialIssuer)));
    }

    #[test]
    fn premium_tier_with_correct_issuer_accepted() {
        let mut reg = SubscriberRegistry::new();
        let alice_w = cclerk(10);
        let creator_w = cclerk(11);
        let mut issuer_w = cclerk(12);

        reg.register_subscriber(alice_w.public_key(), [9u8; 32]);
        let mut creator = Creator::new(creator_w.public_key());
        creator.add_tier(Tier::premium("vip", "VIP", 1, 100, issuer_w.public_key()));

        let token = issuer_w.mint_token(&[42u8; 32], "premium");
        let restrictions = Attenuation {
            not_after: Some(i64::MAX),
            ..Default::default()
        };
        let env = issuer_w
            .delegate(&token, &alice_w.public_key(), &restrictions)
            .unwrap();

        let r = reg.subscribe(
            alice_w.public_key(),
            creator_w.public_key(),
            creator.tier("vip").unwrap(),
            Some(env),
        );
        assert!(r.is_ok(), "subscribe should succeed: {:?}", r);
    }

    #[test]
    fn debit_delegation_accepts_well_signed_envelope() {
        let mut reg = SubscriberRegistry::new();
        let mut alice_w = cclerk(20);
        let mut executor_w = cclerk(21);

        reg.register_subscriber(alice_w.public_key(), [9u8; 32]);

        let token = alice_w.mint_token(&[7u8; 32], "subscription-debit");
        let restrictions = Attenuation {
            budget: Some(BudgetSpec {
                id: "subscription:debit".into(),
                parent_id: None,
                class: "asset:1".into(),
                limit: 100,
                window: Some("epoch".into()),
            }),
            not_after: Some(i64::MAX),
            ..Default::default()
        };
        let envelope = alice_w
            .delegate(&token, &executor_w.public_key(), &restrictions)
            .unwrap();

        let r =
            reg.receive_debit_delegation(&mut executor_w, alice_w.public_key(), envelope.clone());
        assert!(r.is_ok(), "valid delegation should be accepted: {:?}", r);
        let auth = r.unwrap();
        assert_eq!(auth.asset_id, 1);
        assert_eq!(auth.max_per_epoch, 100);
    }

    /// ADVERSARIAL: a delegation with a tampered signature is rejected.
    #[test]
    fn debit_delegation_tampered_signature_rejected() {
        let mut reg = SubscriberRegistry::new();
        let mut alice_w = cclerk(22);
        let mut executor_w = cclerk(23);

        reg.register_subscriber(alice_w.public_key(), [9u8; 32]);
        let token = alice_w.mint_token(&[7u8; 32], "subscription-debit");
        let restrictions = Attenuation {
            budget: Some(BudgetSpec {
                id: "subscription:debit".into(),
                parent_id: None,
                class: "asset:1".into(),
                limit: 100,
                window: Some("epoch".into()),
            }),
            not_after: Some(i64::MAX),
            ..Default::default()
        };
        let mut envelope = alice_w
            .delegate(&token, &executor_w.public_key(), &restrictions)
            .unwrap();
        envelope.delegator_signature.0[0] ^= 0xFF;

        let r = reg.receive_debit_delegation(&mut executor_w, alice_w.public_key(), envelope);
        assert!(matches!(r, Err(SubscriberError::InvalidDelegation(_))));
    }

    /// ADVERSARIAL: a delegation with NO budget caveat is rejected (we have
    /// no way to know how much to debit).
    #[test]
    fn debit_delegation_missing_budget_rejected() {
        let mut reg = SubscriberRegistry::new();
        let mut alice_w = cclerk(24);
        let mut executor_w = cclerk(25);

        let token = alice_w.mint_token(&[7u8; 32], "subscription-debit");
        let restrictions = Attenuation {
            not_after: Some(i64::MAX),
            ..Default::default()
        }; // no budget!
        let envelope = alice_w
            .delegate(&token, &executor_w.public_key(), &restrictions)
            .unwrap();

        let r = reg.receive_debit_delegation(&mut executor_w, alice_w.public_key(), envelope);
        assert!(matches!(r, Err(SubscriberError::MissingBudgetCaveat)));
    }

    /// ADVERSARIAL: a delegation that authorizes "asset:99" stores asset_id=99.
    #[test]
    fn debit_delegation_pins_asset_id() {
        let mut reg = SubscriberRegistry::new();
        let mut alice_w = cclerk(30);
        let mut executor_w = cclerk(31);

        reg.register_subscriber(alice_w.public_key(), [9u8; 32]);
        let token = alice_w.mint_token(&[7u8; 32], "subscription-debit");
        let restrictions = Attenuation {
            budget: Some(BudgetSpec {
                id: "subscription:debit".into(),
                parent_id: None,
                class: "asset:99".into(),
                limit: 500,
                window: Some("epoch".into()),
            }),
            not_after: Some(i64::MAX),
            ..Default::default()
        };
        let env = alice_w
            .delegate(&token, &executor_w.public_key(), &restrictions)
            .unwrap();
        let auth = reg
            .receive_debit_delegation(&mut executor_w, alice_w.public_key(), env)
            .unwrap();
        assert_eq!(auth.asset_id, 99);
        assert_eq!(auth.max_per_epoch, 500);
    }

    /// ADVERSARIAL: budget.class with the wrong shape is rejected.
    #[test]
    fn debit_delegation_bad_budget_class_rejected() {
        let mut reg = SubscriberRegistry::new();
        let mut alice_w = cclerk(32);
        let mut executor_w = cclerk(33);

        let token = alice_w.mint_token(&[7u8; 32], "subscription-debit");
        let restrictions = Attenuation {
            budget: Some(BudgetSpec {
                id: "subscription:debit".into(),
                parent_id: None,
                class: "wrong_format".into(),
                limit: 500,
                window: Some("epoch".into()),
            }),
            not_after: Some(i64::MAX),
            ..Default::default()
        };
        let env = alice_w
            .delegate(&token, &executor_w.public_key(), &restrictions)
            .unwrap();
        let r = reg.receive_debit_delegation(&mut executor_w, alice_w.public_key(), env);
        assert!(matches!(r, Err(SubscriberError::BadBudgetAssetClass(_))));
    }
}
