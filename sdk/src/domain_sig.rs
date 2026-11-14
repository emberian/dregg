//! Domain-tagged signatures over application bytes, by a dregg identity.
//!
//! A consumer that wants "this dregg identity signed these bytes" (a signed
//! chat row, an attestation of an off-chain record) signs through here instead
//! of deriving the key and calling Ed25519 itself. The key path is the
//! cipherclerk's own (`mnemonic::derive_keypair` at `dregg/0`, ML-DSA-65 from
//! the same 32-byte Ed25519 seed), so the signer is the identity the node
//! knows, and both halves are produced: Ed25519 and ML-DSA-65.
//!
//! # What is signed
//!
//! ```text
//! M = "dregg-domain-sig-v1:" ‖ u64le(len(domain)) ‖ domain ‖ BLAKE3(message)
//! ```
//!
//! The Ed25519 half signs `M`. The ML-DSA half signs `M` under the FIPS 204
//! context `dregg-domain-sig-v1`.
//!
//! # Separation from the turn path, by construction
//!
//! Every signature the turn path makes or accepts is over a 32-byte digest:
//! `Turn::hash() -> [u8; 32]` for the envelope and
//! `TurnExecutor::compute_signing_message -> [u8; 32]` for an action. `M` is
//! never 32 bytes ([`DOMAIN_SIG_MIN_LEN`] is 61), so no `M` equals a turn-path
//! message, whatever domain and message an application is induced to sign,
//! including a message that IS a turn hash. That needs no hash assumption: an
//! Ed25519 signature valid for one message is not valid for a different one.
//! The ML-DSA half is separated a second time by its context string, which is
//! not [`dregg_turn::pq::HYBRID_TURN_PQ_CTX`].
//!
//! In the other direction the verifier here only ever checks a signature
//! against an `M` it built, so a turn signature (over 32 bytes) never passes.
//!
//! The domain is length-prefixed, so `(domain, message)` is read back from `M`
//! unambiguously, and two domains never share a signature.

use dregg_types::{PublicKey, Signature};

use crate::cipherclerk::AgentCipherclerk;

/// The ASCII prefix of every domain-tagged signing message.
pub const DOMAIN_SIG_TAG: &[u8] = b"dregg-domain-sig-v1:";

/// The FIPS 204 context of the ML-DSA half. Not the turn context.
pub const DOMAIN_SIG_PQ_CTX: &[u8] = b"dregg-domain-sig-v1";

/// The longest domain accepted, in bytes.
pub const DOMAIN_MAX_LEN: usize = 255;

/// The shortest possible signing message: the tag, the length word, a one-byte
/// domain and the 32-byte digest.
pub const DOMAIN_SIG_MIN_LEN: usize = DOMAIN_SIG_TAG.len() + 8 + 1 + 32;

/// The length of every turn-path signing message (`Turn::hash`, the action
/// signing message).
pub const TURN_PATH_MESSAGE_LEN: usize = 32;

// The separation the module docs claim, checked by the compiler.
const _: () = assert!(DOMAIN_SIG_MIN_LEN > TURN_PATH_MESSAGE_LEN);

/// Why a domain-tagged signature was not made, or did not verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DomainSigError {
    /// The domain is empty, longer than [`DOMAIN_MAX_LEN`], or holds a byte
    /// outside printable non-space ASCII.
    BadDomain(String),
    /// The ML-DSA signer produced nothing.
    PqSignFailed,
    /// The Ed25519 half does not verify under the given public key.
    Ed25519Invalid,
    /// The ML-DSA half does not verify under the given public key.
    MlDsaInvalid,
}

impl std::fmt::Display for DomainSigError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DomainSigError::BadDomain(why) => write!(f, "bad domain tag: {why}"),
            DomainSigError::PqSignFailed => write!(f, "the ML-DSA-65 signer produced no signature"),
            DomainSigError::Ed25519Invalid => {
                write!(
                    f,
                    "the Ed25519 half does not verify for this domain, message and key"
                )
            }
            DomainSigError::MlDsaInvalid => {
                write!(
                    f,
                    "the ML-DSA-65 half does not verify for this domain, message and key"
                )
            }
        }
    }
}

impl std::error::Error for DomainSigError {}

/// Both halves of a domain-tagged signature, with the keys that made them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DomainSignature {
    /// Ed25519 over the signing message.
    pub ed25519: Signature,
    /// ML-DSA-65 over the signing message, under [`DOMAIN_SIG_PQ_CTX`].
    pub ml_dsa: Vec<u8>,
    /// The signer's Ed25519 public key.
    pub public_key: PublicKey,
    /// The signer's ML-DSA-65 public key.
    pub ml_dsa_public_key: Vec<u8>,
}

fn check_domain(domain: &str) -> Result<(), DomainSigError> {
    if domain.is_empty() {
        return Err(DomainSigError::BadDomain("it is empty".to_string()));
    }
    if domain.len() > DOMAIN_MAX_LEN {
        return Err(DomainSigError::BadDomain(format!(
            "it is {} bytes, more than {DOMAIN_MAX_LEN}",
            domain.len()
        )));
    }
    if let Some(bad) = domain.bytes().find(|b| !b.is_ascii_graphic()) {
        return Err(DomainSigError::BadDomain(format!(
            "byte 0x{bad:02x} is not printable non-space ASCII"
        )));
    }
    Ok(())
}

/// The message both halves sign for `(domain, message)`.
pub fn domain_sig_message(domain: &str, message: &[u8]) -> Result<Vec<u8>, DomainSigError> {
    check_domain(domain)?;
    let mut m = Vec::with_capacity(DOMAIN_SIG_TAG.len() + 8 + domain.len() + 32);
    m.extend_from_slice(DOMAIN_SIG_TAG);
    m.extend_from_slice(&(domain.len() as u64).to_le_bytes());
    m.extend_from_slice(domain.as_bytes());
    m.extend_from_slice(blake3::hash(message).as_bytes());
    Ok(m)
}

impl AgentCipherclerk {
    /// Sign `message` under `domain` with this identity, both halves.
    /// Deterministic: the same identity, domain and message give the same
    /// signature bytes.
    pub fn sign_domain_tagged(
        &self,
        domain: &str,
        message: &[u8],
    ) -> Result<DomainSignature, DomainSigError> {
        let m = domain_sig_message(domain, message)?;
        let (ml_dsa, ml_dsa_public_key) = self
            .ml_dsa_sign_under(DOMAIN_SIG_PQ_CTX, &m)
            .ok_or(DomainSigError::PqSignFailed)?;
        Ok(DomainSignature {
            ed25519: self.sign_bytes(&m),
            ml_dsa,
            public_key: self.public_key(),
            ml_dsa_public_key,
        })
    }
}

/// Check both halves of a domain-tagged signature against keys the CALLER
/// names. A key carried beside a signature is not a trust anchor: pass the
/// keys this verifier already expects.
pub fn verify_domain_tagged(
    domain: &str,
    message: &[u8],
    public_key: &PublicKey,
    ml_dsa_public_key: &[u8],
    ed25519: &Signature,
    ml_dsa: &[u8],
) -> Result<(), DomainSigError> {
    let m = domain_sig_message(domain, message)?;
    if !public_key.verify(&m, ed25519) {
        return Err(DomainSigError::Ed25519Invalid);
    }
    crate::runtime::install_verified_pq_cores();
    if !dregg_pq::ml_dsa_verify(ml_dsa_public_key, DOMAIN_SIG_PQ_CTX, &m, ml_dsa) {
        return Err(DomainSigError::MlDsaInvalid);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use dregg_turn::action::{Effect, Event, symbol};
    use dregg_turn::executor::TurnExecutor;

    use super::*;

    fn clerk(byte: u8) -> AgentCipherclerk {
        AgentCipherclerk::from_seed([byte; 64])
    }

    fn verify(sig: &DomainSignature, domain: &str, message: &[u8]) -> Result<(), DomainSigError> {
        verify_domain_tagged(
            domain,
            message,
            &sig.public_key,
            &sig.ml_dsa_public_key,
            &sig.ed25519,
            &sig.ml_dsa,
        )
    }

    #[test]
    fn a_domain_tagged_signature_verifies_and_is_deterministic() {
        let c = clerk(7);
        let sig = c
            .sign_domain_tagged("fleet.chat-row.v1", b"row bytes")
            .unwrap();
        assert_eq!(
            sig,
            c.sign_domain_tagged("fleet.chat-row.v1", b"row bytes")
                .unwrap()
        );
        assert_eq!(sig.public_key, c.public_key());
        assert_eq!(sig.ml_dsa_public_key, c.ml_dsa_public_bytes());
        verify(&sig, "fleet.chat-row.v1", b"row bytes").expect("the honest signature verifies");
    }

    #[test]
    fn another_domain_message_or_key_does_not_verify() {
        let c = clerk(7);
        let sig = c
            .sign_domain_tagged("fleet.chat-row.v1", b"row bytes")
            .unwrap();
        assert_eq!(
            verify(&sig, "fleet.chat-row.v2", b"row bytes"),
            Err(DomainSigError::Ed25519Invalid)
        );
        assert_eq!(
            verify(&sig, "fleet.chat-row.v1", b"row bytez"),
            Err(DomainSigError::Ed25519Invalid)
        );
        let other = clerk(8);
        assert_eq!(
            verify_domain_tagged(
                "fleet.chat-row.v1",
                b"row bytes",
                &other.public_key(),
                &sig.ml_dsa_public_key,
                &sig.ed25519,
                &sig.ml_dsa,
            ),
            Err(DomainSigError::Ed25519Invalid)
        );
        // The Ed25519 half alone is not the signature: a PQ half by another
        // key, or under the pinned key with a flipped byte, is refused.
        assert_eq!(
            verify_domain_tagged(
                "fleet.chat-row.v1",
                b"row bytes",
                &sig.public_key,
                &other.ml_dsa_public_bytes(),
                &sig.ed25519,
                &sig.ml_dsa,
            ),
            Err(DomainSigError::MlDsaInvalid)
        );
        let mut bent = sig.clone();
        bent.ml_dsa[10] ^= 1;
        assert_eq!(
            verify(&bent, "fleet.chat-row.v1", b"row bytes"),
            Err(DomainSigError::MlDsaInvalid)
        );
    }

    #[test]
    fn the_domain_is_required_and_bounded() {
        let c = clerk(7);
        for bad in [
            "",
            "has space",
            "new\nline",
            "caf\u{e9}",
            &"x".repeat(DOMAIN_MAX_LEN + 1),
        ] {
            assert!(
                matches!(
                    c.sign_domain_tagged(bad, b"m"),
                    Err(DomainSigError::BadDomain(_))
                ),
                "domain {bad:?} must be refused"
            );
        }
        c.sign_domain_tagged(&"x".repeat(DOMAIN_MAX_LEN), b"m")
            .expect("the bound is inclusive");
    }

    #[test]
    fn the_domain_boundary_does_not_slide() {
        // Without the length word, ("ab", m) and ("a", m') could share a
        // preimage prefix. With it the two messages differ in the length word.
        let a = domain_sig_message("ab", b"c").unwrap();
        let b = domain_sig_message("a", b"bc").unwrap();
        assert_ne!(a, b);
        assert_eq!(a[DOMAIN_SIG_TAG.len()], 2);
        assert_eq!(b[DOMAIN_SIG_TAG.len()], 1);
    }

    /// A turn of this identity, with both of its turn-path signatures.
    fn signed_turn(c: &AgentCipherclerk) -> (dregg_turn::SignedTurn, [u8; 32]) {
        let cell = c.cell_id("default");
        let federation_id = [9u8; 32];
        let effect = Effect::EmitEvent {
            cell,
            event: Event {
                topic: symbol("t"),
                data: vec![],
            },
        };
        let unsigned = crate::raw::unsigned_action_named(cell, "t", vec![effect]);
        let action_message = TurnExecutor::compute_signing_message(&unsigned, &federation_id, 0);
        let action = c.sign_action_hybrid(unsigned, &federation_id, 0);
        let mut turn = c.make_turn_with_actions(vec![action]);
        turn.agent = cell;
        (c.sign_turn(&turn), action_message)
    }

    #[test]
    fn a_domain_tagged_signature_is_not_a_turn_signature() {
        let c = clerk(7);
        let (signed, action_message) = signed_turn(&c);
        let turn_hash = signed.turn.hash();
        // The honest turn signatures verify: the refusals below are about the
        // domain-tagged ones, not about a verifier that refuses everything.
        assert!(signed.signer.verify(&turn_hash, &signed.signature));
        assert!(dregg_turn::pq::ml_dsa_verify(
            &signed.pq_signer,
            &turn_hash,
            &signed.pq_signature
        ));

        // The strongest attempt: an application is induced to sign the turn
        // hash itself, or the action signing message, as its "message", under
        // any domain an attacker likes.
        for target in [turn_hash, action_message] {
            for domain in ["x", "dregg-turn-v3:", "dregg-action-sig-v3:"] {
                let sig = c.sign_domain_tagged(domain, &target).unwrap();
                assert!(
                    !signed.signer.verify(&target, &sig.ed25519),
                    "the Ed25519 half must not verify as a turn-path signature"
                );
                assert!(
                    !dregg_turn::pq::ml_dsa_verify(&sig.ml_dsa_public_key, &target, &sig.ml_dsa),
                    "the ML-DSA half must not verify under the turn context"
                );
            }
        }
        // Every signing message is longer than any turn-path message.
        assert!(domain_sig_message("x", b"").unwrap().len() >= DOMAIN_SIG_MIN_LEN);
        assert_eq!(turn_hash.len(), TURN_PATH_MESSAGE_LEN);
        assert_eq!(action_message.len(), TURN_PATH_MESSAGE_LEN);
    }

    #[test]
    fn a_turn_signature_is_not_a_domain_tagged_signature() {
        let c = clerk(7);
        let (signed, _) = signed_turn(&c);
        let turn_hash = signed.turn.hash();
        // The envelope's two halves, offered as a domain-tagged signature over
        // the turn hash, the empty message, or anything else.
        for domain in ["x", "dregg-turn-v3:"] {
            for message in [&turn_hash[..], b""] {
                assert_eq!(
                    verify_domain_tagged(
                        domain,
                        message,
                        &signed.signer,
                        &signed.pq_signer,
                        &signed.signature,
                        &signed.pq_signature,
                    ),
                    Err(DomainSigError::Ed25519Invalid)
                );
            }
        }
        // And the PQ half on its own terms: the turn's ML-DSA signature does
        // not verify under the domain context even over the bytes it signed.
        assert!(!dregg_pq::ml_dsa_verify(
            &signed.pq_signer,
            DOMAIN_SIG_PQ_CTX,
            &turn_hash,
            &signed.pq_signature
        ));
    }
}
