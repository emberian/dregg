//! Real, canonical signed-intent flow — the bot brokers genuine signed Intents
//! between clique members (§4.7 "broker signed intents").
//!
//! This module is **Discord-independent**. A posted intent is a canonical
//! `dregg_turn::action::Action` with method `"intent.post"`, carrying the
//! human-readable spec in its `args`, and signed with the poster's real Ed25519
//! key through the canonical `AppCipherclerk::sign_action` path. The
//! authorization is a real `Authorization::Signature` over
//! `TurnExecutor::compute_signing_message(action, federation_id)` — NOT a mock
//! string. Anyone can verify the signature against the poster's public key.
//!
//! # Why a signed Action, not `dregg_intent::Intent`
//!
//! The `dregg-intent` crate's `Intent` is an *anonymous-commitment* primitive
//! (Poseidon2 stake proofs, content-addressed ids, no signer identity) built
//! for the trustless solver/gossip path, and it pulls in circuit/commit deps
//! the bot deliberately does not carry. For a Discord clique where members post
//! intents under their own (hosted) identity and react to fulfill, the honest
//! real artifact is a *signed* canonical Action — the same envelope the node
//! ingests. If/when the bot should publish anonymous solver-network intents,
//! that is a separate, named follow-up (see the report).

use dregg_app_framework::AppCipherclerk;
use dregg_turn::action::{Action, Authorization};

/// A signed intent ready to post to a channel.
#[derive(Debug, Clone)]
pub struct SignedIntent {
    /// The canonical signed action (method `"intent.post"`).
    pub action: Action,
    /// The poster's public key bytes (for verification / display).
    pub poster_pk: [u8; 32],
    /// The federation id the signature is bound to.
    pub federation_id: [u8; 32],
    /// The human-readable spec, echoed for display.
    pub spec: String,
}

/// Build a **real** signed intent: a canonical `Action` carrying `spec`,
/// authorized with the poster's Ed25519 signature.
///
/// `cclerk` is the poster's hosted [`AppCipherclerk`]; the signature is
/// produced by `sign_action` and binds the spec bytes + federation id.
pub fn build_signed_intent(cclerk: &AppCipherclerk, spec: &str) -> SignedIntent {
    let target = cclerk.cell_id();
    // method "intent.post"; `args` are canonical field elements ([u8; 32]), so
    // we bind the spec by its BLAKE3 hash as the single arg. The canonical
    // signing message hashes target + method + args, so the signature is bound
    // to the exact spec content (full text is echoed in `spec` for display).
    let spec_hash = *blake3::hash(spec.as_bytes()).as_bytes();
    let mut action = cclerk.make_action(target, "intent.post", Vec::new());
    action.args = vec![spec_hash];
    // Re-sign now that args carry the spec hash (make_action signed the empty form).
    let action = cclerk.sign_action(action);

    SignedIntent {
        action,
        poster_pk: cclerk.public_key().0,
        federation_id: *cclerk.federation_id(),
        spec: spec.to_string(),
    }
}

/// Verify a signed intent's Ed25519 authorization against the poster's public
/// key. This is the canonical check the node executor performs.
pub fn verify_signed_intent(intent: &SignedIntent) -> bool {
    verify_action_signature(&intent.action, &intent.poster_pk, &intent.federation_id)
}

/// Canonical Ed25519 verification of an `Authorization::Signature` action.
///
/// Reconstructs the 64-byte signature from the `(r, s)` halves and verifies it
/// against `compute_signing_message(action, federation_id)` — exactly as
/// `dregg_turn`'s executor does, using `dregg_types::PublicKey::verify`
/// (`verify_strict` under the hood, rejecting malleable signatures).
pub fn verify_action_signature(
    action: &Action,
    signer_pk: &[u8; 32],
    federation_id: &[u8; 32],
) -> bool {
    use dregg_turn::executor::TurnExecutor;
    use dregg_types::{PublicKey, Signature};

    let Authorization::Signature(r, s) = &action.authorization else {
        return false;
    };
    let mut sig_bytes = [0u8; 64];
    sig_bytes[..32].copy_from_slice(r);
    sig_bytes[32..].copy_from_slice(s);

    let message = TurnExecutor::compute_signing_message(action, federation_id);
    PublicKey(*signer_pk).verify(&message, &Signature(sig_bytes))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cipherclerk::UserCipherclerk;

    fn cclerk_for(bot_secret: &[u8; 32], uid: u64, fed: [u8; 32]) -> AppCipherclerk {
        UserCipherclerk::derive(bot_secret, uid, fed).app
    }

    #[test]
    fn build_produces_a_real_signed_intent_that_verifies() {
        let fed = [11u8; 32];
        let cclerk = cclerk_for(&[1u8; 32], 4242, fed);
        let intent = build_signed_intent(&cclerk, "want: 5 GOOSE for 1 hr of compute");

        // Real Ed25519 signature over the canonical signing message — a mock
        // string could never satisfy verify_strict.
        assert!(
            verify_signed_intent(&intent),
            "signed intent must carry a valid Ed25519 authorization"
        );
        assert!(matches!(intent.action.authorization, Authorization::Signature(_, _)));
        assert_eq!(intent.action.args, vec![*blake3::hash(intent.spec.as_bytes()).as_bytes()]);
        assert_eq!(intent.poster_pk, cclerk.public_key().0);
    }

    #[test]
    fn tampered_spec_fails_verification() {
        let fed = [12u8; 32];
        let cclerk = cclerk_for(&[2u8; 32], 1, fed);
        let mut intent = build_signed_intent(&cclerk, "original spec");

        // Mutate the spec args after signing — the signature must no longer
        // verify (the signing message hashes the args).
        intent.action.args = vec![*blake3::hash(b"forged spec").as_bytes()];
        assert!(
            !verify_signed_intent(&intent),
            "tampering with the intent spec must invalidate the signature"
        );
    }

    #[test]
    fn wrong_pubkey_fails_verification() {
        let fed = [13u8; 32];
        let cclerk = cclerk_for(&[3u8; 32], 7, fed);
        let other = cclerk_for(&[3u8; 32], 8, fed);
        let mut intent = build_signed_intent(&cclerk, "spec");
        // Claim a different poster — verification must fail.
        intent.poster_pk = other.public_key().0;
        assert!(!verify_signed_intent(&intent));
    }
}
