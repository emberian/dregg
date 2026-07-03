//! **The bind cap.** WHO may bind a custom domain — a `dregg-auth` credential that
//! must VERIFY under the registry's trusted root as granting the binding authority
//! for the domain.
//!
//! A [`DomainCap`] presents a real `dregg-auth` credential (`dga1_…`, an ed25519
//! caveat-chain — the native successor of a prior imperative credential core). It is
//! *not* a self-asserted token: [`verify_bind_authority`] verifies it offline under
//! the registry's trusted root authority for the domain and derives the binding's
//! `owner` from the credential's pinned subject (so only that owner may later rebind
//! — no takeover of a victim's binding). The two grants:
//!
//! * a **broad** domains cap ([`mint_domains_cap`]) — bind ANY domain (pins the
//!   holder's subject + `action = bind`);
//! * a **per-domain** delegate cap ([`mint_domain_bind_cap`]) — the broad cap
//!   `attenuate`d to one domain. By the no-amplify property of `Credential::attenuate`
//!   (`metatheory/Dregg2/Authority/Caveat.lean` `attenuate_subset`), a delegate
//!   confined to `blog.acme.dev` cannot widen back to all domains: appending a
//!   second-domain caveat only makes the meet unsatisfiable.
//!
//! Verification binds two teeth against the context: `subject` (the owner, so a
//! forged subject is a bad-signature refusal) and `domain` (the per-domain scope).

use dregg_auth::credential::{Caveat, Context, Credential, Pred, PublicKey, RootKey};

use crate::DomainError;

/// The context attribute key for the binding owner's subject — pinned into every
/// domains credential and re-bound at verify (so the subject value is chain-signed).
pub const SUBJECT_KEY: &str = "subject";
/// The context attribute key for the domain a bind is exercised for — the per-domain
/// scoping tooth an attenuated delegate cap pins.
pub const DOMAIN_KEY: &str = "domain";
/// The context attribute key for the action — every domains credential pins
/// `action = bind`, so it only ever satisfies a bind context.
pub const ACTION_KEY: &str = "action";
/// The single action a domains credential authorizes: `bind`.
pub const ACTION_BIND: &str = "bind";

/// A capability authorizing a domain binding: a **real `dregg-auth` credential**
/// (`dga1_…`) presented for a domain. Verified under the registry's trusted root by
/// [`verify_bind_authority`]; the binding's owner is the credential's pinned subject.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DomainCap {
    /// The presented credential's wire form (`dga1_…`) proving binding authority.
    pub credential: String,
    /// The domain this cap is exercised for (lowercased).
    pub domain: String,
}

impl DomainCap {
    /// A binding cap presenting `credential` for `domain`.
    pub fn new(credential: impl Into<String>, domain: &str) -> DomainCap {
        DomainCap {
            credential: credential.into(),
            domain: domain.trim().to_ascii_lowercase(),
        }
    }
}

/// The `AttrEq{key = value}` first-party caveat — the single building block of a
/// domains credential's teeth.
fn attr_eq(key: &str, value: &str) -> Caveat {
    Caveat::FirstParty(Pred::AttrEq {
        key: key.to_string(),
        value: value.to_string(),
    })
}

/// Mint the **broad domains cap** for `subject` — authority to bind ANY domain the
/// holder can DNS-prove control of. Pins the subject (the binding owner) and
/// `action = bind`. Held by a developer account; the registry authority mints it.
pub fn mint_domains_cap(root: &RootKey, subject: &str) -> Credential {
    root.mint([
        attr_eq(SUBJECT_KEY, subject),
        attr_eq(ACTION_KEY, ACTION_BIND),
    ])
}

/// Mint the **per-domain delegate cap** — the broad cap for `subject`, `attenuate`d
/// to exactly `domain` (one appended `AttrEq{domain}` caveat). The attenuated form
/// confines a delegate to one domain and can only ever narrow (no amplification).
pub fn mint_domain_bind_cap(root: &RootKey, subject: &str, domain: &str) -> Credential {
    mint_domains_cap(root, subject)
        .attenuate([attr_eq(DOMAIN_KEY, &domain.trim().to_ascii_lowercase())])
}

/// The verification context for a bind of `domain` by `owner` at clock `now`. Binds
/// the three attributes a domains credential's caveats read: `subject`, `action`, and
/// `domain`.
pub fn bind_context(owner: &str, domain: &str, now: u64) -> Context {
    Context::new()
        .at(now)
        .attr(SUBJECT_KEY, owner)
        .attr(ACTION_KEY, ACTION_BIND)
        .attr(DOMAIN_KEY, domain.trim().to_ascii_lowercase())
}

/// The subject a domains credential pins (its binding owner) — the value of the
/// first `AttrEq{key = "subject"}` caveat on the chain. `None` if the credential pins
/// no subject (not a domains credential). The value is authenticated by
/// [`verify_bind_authority`]'s chain-signature check, so a forged subject is refused.
pub fn subject_of(cred: &Credential) -> Option<String> {
    cred.caveats().find_map(|(_, caveat)| match caveat {
        Caveat::FirstParty(Pred::AttrEq { key, value }) if key.as_str() == SUBJECT_KEY => {
            Some(value.clone())
        }
        _ => None,
    })
}

/// Verify `credential` under the trusted `root` as authorizing a bind of `domain`,
/// returning the credential's pinned subject (the binding owner) on success.
///
/// Fully offline + fail-closed: the credential must decode, pin a subject, and verify
/// (proof-of-possession + the ed25519 chain from `root` + the caveat meet) for the
/// bind of `domain`. A self-fabricated / wrong-root / wrong-domain / no-subject
/// credential is refused with [`DomainError::CapRefused`].
pub fn verify_bind_authority(
    credential: &str,
    root: &PublicKey,
    domain: &str,
    now: u64,
) -> Result<String, DomainError> {
    let domain = domain.trim().to_ascii_lowercase();
    let cred = Credential::decode(credential).map_err(|e| DomainError::CapRefused {
        domain: domain.clone(),
        reason: format!("credential did not decode: {e}"),
    })?;
    let owner = subject_of(&cred).ok_or_else(|| DomainError::CapRefused {
        domain: domain.clone(),
        reason: "credential pins no subject".to_string(),
    })?;
    cred.verify(root, &bind_context(&owner, &domain, now))
        .map_err(|refusal| DomainError::CapRefused {
            domain: domain.clone(),
            reason: refusal.to_string(),
        })?;
    Ok(owner)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn root() -> RootKey {
        RootKey::from_seed([7u8; 32])
    }

    #[test]
    fn broad_cap_binds_any_domain_and_yields_its_subject() {
        let root = root();
        let cred = mint_domains_cap(&root, "dregg:alice").encode();
        let owner = verify_bind_authority(&cred, &root.public(), "blog.example.com", 100)
            .expect("the broad cap binds blog.example.com");
        assert_eq!(owner, "dregg:alice");
        // …and any other domain too.
        assert_eq!(
            verify_bind_authority(&cred, &root.public(), "shop.example.org", 100).unwrap(),
            "dregg:alice"
        );
    }

    #[test]
    fn a_forged_root_credential_is_refused() {
        // A credential minted by a DIFFERENT (attacker) root does not verify under
        // the trusted root — the self-asserted-cap attack is refused.
        let attacker = RootKey::from_seed([99u8; 32]);
        let forged = mint_domains_cap(&attacker, "dregg:mallory").encode();
        assert!(matches!(
            verify_bind_authority(&forged, &root().public(), "blog.example.com", 100),
            Err(DomainError::CapRefused { .. })
        ));
    }

    #[test]
    fn per_domain_delegate_binds_only_its_domain() {
        let root = root();
        let cred = mint_domain_bind_cap(&root, "dregg:alice", "blog.example.com").encode();
        // Its domain: ok.
        assert!(verify_bind_authority(&cred, &root.public(), "blog.example.com", 100).is_ok());
        // Any other domain: the pinned `AttrEq{domain}` caveat refuses.
        assert!(matches!(
            verify_bind_authority(&cred, &root.public(), "shop.example.com", 100),
            Err(DomainError::CapRefused { .. })
        ));
    }

    #[test]
    fn a_delegate_cannot_amplify_back_to_all_domains() {
        let root = root();
        let delegate = mint_domain_bind_cap(&root, "dregg:alice", "blog.example.com");
        // Appending a second-domain caveat only NARROWS: the meet
        // (domain = blog) AND (domain = shop) is unsatisfiable for any single domain.
        let forged = delegate
            .attenuate([attr_eq(DOMAIN_KEY, "shop.example.com")])
            .encode();
        assert!(matches!(
            verify_bind_authority(&forged, &root.public(), "shop.example.com", 100),
            Err(DomainError::CapRefused { .. })
        ));
        assert!(matches!(
            verify_bind_authority(&forged, &root.public(), "blog.example.com", 100),
            Err(DomainError::CapRefused { .. })
        ));
    }

    #[test]
    fn distinct_subjects_yield_distinct_owners() {
        let root = root();
        let alice = mint_domains_cap(&root, "dregg:alice").encode();
        let bob = mint_domains_cap(&root, "dregg:bob").encode();
        let a = verify_bind_authority(&alice, &root.public(), "a.example.com", 1).unwrap();
        let b = verify_bind_authority(&bob, &root.public(), "b.example.com", 1).unwrap();
        assert_ne!(a, b);
    }
}
