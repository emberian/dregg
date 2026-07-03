//! The custom-domain **control plane** — the plaintext `domain -> binding` routing
//! index a gateway consults, the cap-gated `bind`, the DNS-driven `verify`, and the
//! two verified reads (`site_for_host` / `is_verified`).
//!
//! This is the routing-plane companion to the verified per-domain cell (`src/lib.rs`):
//! a gateway needs the plaintext `domain -> site` map to route, so the registry holds
//! the serializable [`DomainBinding`] records (the source of truth for routing) while
//! the cell mirrors their commitments under the executor-enforced `WriteOnce` /
//! `Monotonic` invariants ([`mirror_binding`](crate::mirror_binding)). Binding inserts
//! a cap-gated Pending record; [`verify`](DomainRegistry::verify) resolves its
//! challenge through a [`DnsResolver`] and flips it to Verified. Resolution
//! ([`site_for_host`](DomainRegistry::site_for_host)) and the cert ask
//! ([`is_verified`](DomainRegistry::is_verified)) read only *verified* bindings — a
//! byte is routed (and a cert minted) only for a domain a tenant has *proven*.

use std::collections::BTreeMap;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};

use dregg_auth::credential::PublicKey;
use serde::{Deserialize, Serialize};

use crate::cap::{DomainCap, verify_bind_authority};
use crate::dns::{
    ChallengeMethod, DnsChallenge, DnsResolver, HOSTING_APEX, TXT_CHALLENGE_PREFIX,
    VerificationState, challenge_satisfied, challenge_token, is_valid_domain, is_valid_label,
};

/// A **domain binding** — the routing-plane record backing a custom-domain -> site
/// map. The committed state a domain cell mirrors: the custom `domain`, the bound
/// `site` (`<name>`, whose `<name>.<apex>` cell serves the bytes), the `owner` (the
/// bind cap's subject), the chosen challenge `method`, the `challenge` nonce, the
/// verification `state`, and the `verified_seq` of the verifying turn.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DomainBinding {
    /// The custom domain bound (lowercased).
    pub domain: String,
    /// The bound site `<name>` — the `<name>.<apex>` cell that serves the bytes.
    pub site: String,
    /// The owner (the bind cap's subject). Provable: the bind receipt binds
    /// `(domain, site, owner)`, and the owner is sealed `WriteOnce` on the cell.
    pub owner: String,
    /// Which DNS record proves control.
    pub method: ChallengeMethod,
    /// The challenge nonce (the value published in DNS; carried for both methods so
    /// the expected record value is re-derivable).
    pub challenge: String,
    /// Whether control has been proven.
    pub state: VerificationState,
    /// The registry-monotonic sequence of the verifying turn (who proved control,
    /// when), `None` while [`VerificationState::Pending`].
    pub verified_seq: Option<u64>,
}

impl DomainBinding {
    /// A bound-but-unproven binding (Pending, no verifying turn yet).
    pub fn pending(
        domain: &str,
        site: &str,
        owner: &str,
        method: ChallengeMethod,
        challenge: &str,
    ) -> DomainBinding {
        DomainBinding {
            domain: domain.trim().to_ascii_lowercase(),
            site: site.to_string(),
            owner: owner.to_string(),
            method,
            challenge: challenge.to_string(),
            state: VerificationState::Pending,
            verified_seq: None,
        }
    }

    /// A proven binding (Verified at `verified_seq`).
    pub fn verified(
        domain: &str,
        site: &str,
        owner: &str,
        method: ChallengeMethod,
        challenge: &str,
        verified_seq: u64,
    ) -> DomainBinding {
        DomainBinding {
            state: VerificationState::Verified,
            verified_seq: Some(verified_seq),
            ..DomainBinding::pending(domain, site, owner, method, challenge)
        }
    }

    /// The DNS record an owner must publish to satisfy this binding's challenge.
    pub fn dns_challenge(&self) -> DnsChallenge {
        match self.method {
            ChallengeMethod::Txt => DnsChallenge {
                record_type: ChallengeMethod::Txt,
                record_name: format!("{TXT_CHALLENGE_PREFIX}{}", self.domain),
                expected_value: self.challenge.clone(),
            },
            ChallengeMethod::Cname => DnsChallenge {
                record_type: ChallengeMethod::Cname,
                record_name: self.domain.clone(),
                expected_value: format!("{}.{HOSTING_APEX}", self.site),
            },
        }
    }

    /// Whether this binding has proven control.
    pub fn is_verified(&self) -> bool {
        self.state.is_verified()
    }
}

/// The verifiable record a bind leaves: who bound which domain to which site, under
/// what challenge. The routing-plane analog of the bind turn's receipt.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BindReceipt {
    /// The registry-monotonic sequence of this bind (bind order).
    pub seq: u64,
    /// The custom domain bound.
    pub domain: String,
    /// The site `<name>` it was bound to.
    pub site: String,
    /// The owner (the cap's subject) that bound it.
    pub owner: String,
    /// The DNS challenge the owner must satisfy to verify.
    pub challenge: DnsChallenge,
}

/// Why a domain operation was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DomainError {
    /// The presented credential does not authorize binding `domain` (it did not
    /// decode, pins no subject, did not verify under the trusted root, or is scoped
    /// to a different domain).
    CapRefused { domain: String, reason: String },
    /// A rebind was attempted by a credential whose subject is not the existing
    /// binding's owner — only the owner may rebind (no takeover).
    OwnerMismatch { domain: String },
    /// The registry has no trusted root authority configured, so no credential can be
    /// verified — every bind is refused (fail-closed). Construct with
    /// [`DomainRegistry::with_authority`].
    NoAuthority,
    /// `domain` is not a usable custom domain (not a multi-label FQDN, a bad label, or
    /// it is a platform-apex host — the wildcard path, not a custom domain).
    InvalidDomain(String),
    /// `site` is not a valid site `<name>` label.
    InvalidSite(String),
    /// No binding exists for `domain` (verify/lookup on an unbound domain).
    NotBound(String),
    /// The DNS challenge is not (yet) satisfied — control is unproven.
    ChallengeUnmet { domain: String },
}

impl std::fmt::Display for DomainError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DomainError::CapRefused { domain, reason } => {
                write!(
                    f,
                    "credential does not authorize binding `{domain}`: {reason}"
                )
            }
            DomainError::OwnerMismatch { domain } => {
                write!(
                    f,
                    "only the owner of the binding for `{domain}` may rebind it"
                )
            }
            DomainError::NoAuthority => write!(
                f,
                "no trusted root authority configured — binding is refused (fail-closed)"
            ),
            DomainError::InvalidDomain(d) => write!(f, "`{d}` is not a valid custom domain"),
            DomainError::InvalidSite(s) => write!(f, "`{s}` is not a valid site name"),
            DomainError::NotBound(d) => write!(f, "no binding for domain `{d}`"),
            DomainError::ChallengeUnmet { domain } => write!(
                f,
                "DNS challenge for `{domain}` is not satisfied (control unproven)"
            ),
        }
    }
}

impl std::error::Error for DomainError {}

/// The registry of domain bindings — the custom-domain control plane.
#[derive(Default)]
pub struct DomainRegistry {
    bindings: Mutex<BTreeMap<String, DomainBinding>>,
    next_seq: AtomicU64,
    /// The trusted root authority that mints domain-binding credentials. A bind must
    /// present a credential verifying under this root for the domain. `None` (the
    /// [`DomainRegistry::new`] default) = no authority → every bind is refused
    /// (fail-closed); the verify / route / `ask` read paths do not need it.
    authority: Option<PublicKey>,
}

impl DomainRegistry {
    /// A fresh, empty registry with **no** binding authority configured — verify /
    /// route / cert-`ask` work, but [`bind`](Self::bind) is refused (fail-closed)
    /// until a root is set. A gateway adopts this read side; the binding control
    /// surface uses [`with_authority`](Self::with_authority).
    pub fn new() -> DomainRegistry {
        DomainRegistry::default()
    }

    /// A registry whose binds are gated by credentials verifying under `root` — the
    /// trusted domain-binding authority. Only a holder of a credential this root
    /// minted (or attenuated) may bind, and the binding's owner is that credential's
    /// pinned subject.
    pub fn with_authority(root: PublicKey) -> DomainRegistry {
        DomainRegistry {
            authority: Some(root),
            ..Default::default()
        }
    }

    /// Bind a custom domain to a site as a cap-gated turn (Pending).
    ///
    /// Verifies `cap`'s credential under the trusted root as granting the binding
    /// authority for `domain` (NOT a self-asserted token — a forged/wrong-root/wrong-
    /// domain credential is refused), validates the domain as a custom FQDN and the
    /// site as a valid `<name>` label, then — **only if the domain is unbound or
    /// already owned by this credential's subject** — issues the challenge nonce and
    /// writes the [`DomainBinding`] (owner = the credential's subject, state =
    /// Pending). A rebind by any other subject is refused
    /// ([`DomainError::OwnerMismatch`]); a rebind by the owner replaces the binding
    /// (a fresh nonce, back to Pending).
    pub fn bind(
        &self,
        cap: &DomainCap,
        domain: &str,
        site: &str,
        method: ChallengeMethod,
    ) -> Result<BindReceipt, DomainError> {
        let domain = domain.trim().to_ascii_lowercase();
        if !is_valid_domain(&domain) {
            return Err(DomainError::InvalidDomain(domain));
        }
        if cap.domain != domain {
            return Err(DomainError::CapRefused {
                domain,
                reason: format!(
                    "cap is exercised for `{}`, not the bound domain",
                    cap.domain
                ),
            });
        }
        // Real cap authority: verify the credential under the trusted root. A registry
        // with no authority refuses every bind (fail-closed).
        let root = self.authority.as_ref().ok_or(DomainError::NoAuthority)?;
        let owner = verify_bind_authority(&cap.credential, root, &domain, unix_now())?;
        if !is_valid_label(site) {
            return Err(DomainError::InvalidSite(site.to_string()));
        }

        let seq = self.next_seq.fetch_add(1, Ordering::Relaxed);
        let challenge = challenge_token(&domain, &owner, seq);
        let binding = DomainBinding::pending(&domain, site, &owner, method, &challenge);
        let receipt = BindReceipt {
            seq,
            domain: domain.clone(),
            site: site.to_string(),
            owner: owner.clone(),
            challenge: binding.dns_challenge(),
        };
        // Owner-gated rebind, atomic with the insert: a different subject cannot
        // overwrite (takeover) or reset (takedown) a victim's existing binding.
        let mut guard = self.bindings.lock().expect("bindings poisoned");
        if let Some(existing) = guard.get(&domain) {
            if existing.owner != owner {
                return Err(DomainError::OwnerMismatch { domain });
            }
        }
        guard.insert(domain, binding);
        Ok(receipt)
    }

    /// Verify a binding's control by resolving its challenge through `dns`.
    ///
    /// On a satisfied challenge the binding flips to [`VerificationState::Verified`]
    /// (recording the verifying turn's sequence) and the now-verified binding is
    /// returned. An unmet challenge leaves the binding Pending and returns
    /// [`DomainError::ChallengeUnmet`]; an unbound domain is
    /// [`DomainError::NotBound`]. Idempotent: verifying an already-verified binding
    /// re-checks and is a no-op success.
    pub fn verify(
        &self,
        domain: &str,
        dns: &impl DnsResolver,
    ) -> Result<DomainBinding, DomainError> {
        let domain = domain.trim().to_ascii_lowercase();
        // Snapshot the binding, then release the lock for the (slow) DNS lookup so a
        // black-holed resolver cannot stall all routing / cert asks while it runs.
        let snapshot = {
            let guard = self.bindings.lock().expect("bindings poisoned");
            guard
                .get(&domain)
                .cloned()
                .ok_or_else(|| DomainError::NotBound(domain.clone()))?
        };
        if !challenge_satisfied(&snapshot.dns_challenge(), dns) {
            return Err(DomainError::ChallengeUnmet { domain });
        }
        // Re-acquire to commit. The binding may have been rebound (a fresh nonce)
        // while the lock was dropped — only flip the binding whose challenge is the
        // one we actually proved, so a concurrent rebind is not wrongly verified.
        let mut guard = self.bindings.lock().expect("bindings poisoned");
        let binding = guard
            .get_mut(&domain)
            .ok_or_else(|| DomainError::NotBound(domain.clone()))?;
        if binding.challenge != snapshot.challenge || binding.method != snapshot.method {
            return Err(DomainError::ChallengeUnmet { domain });
        }
        if binding.state != VerificationState::Verified {
            binding.state = VerificationState::Verified;
            binding.verified_seq = Some(self.next_seq.fetch_add(1, Ordering::Relaxed));
        }
        Ok(binding.clone())
    }

    /// Look up a binding by domain (a clone of the committed record).
    pub fn get(&self, domain: &str) -> Option<DomainBinding> {
        self.bindings
            .lock()
            .expect("bindings poisoned")
            .get(&domain.trim().to_ascii_lowercase())
            .cloned()
    }

    /// The bound site `<name>` for an inbound `Host`, **only when verified**.
    ///
    /// Strips a `:port` suffix and lowercases, then returns the verified binding's
    /// site. An unbound or still-Pending host yields `None` — a gateway routes (and
    /// the edge mints a cert for) only proven domains.
    pub fn site_for_host(&self, host: &str) -> Option<String> {
        let domain = host_key(host)?;
        let guard = self.bindings.lock().expect("bindings poisoned");
        let binding = guard.get(&domain)?;
        binding.is_verified().then(|| binding.site.clone())
    }

    /// Whether `host` is a verified custom domain — a gateway's on-demand-TLS `ask`
    /// gate (a cert is minted only for a proven domain).
    pub fn is_verified(&self, host: &str) -> bool {
        host_key(host)
            .and_then(|d| {
                self.bindings
                    .lock()
                    .expect("bindings poisoned")
                    .get(&d)
                    .map(|b| b.is_verified())
            })
            .unwrap_or(false)
    }

    /// All bindings, sorted by domain (a snapshot of the committed set).
    pub fn list(&self) -> Vec<DomainBinding> {
        self.bindings
            .lock()
            .expect("bindings poisoned")
            .values()
            .cloned()
            .collect()
    }

    /// Adopt a pre-existing [`DomainBinding`] (e.g. one mirrored from a domain cell or
    /// a persisted snapshot) into this registry — so a fresh process can drive
    /// [`verify`](Self::verify) / routing over bindings a prior turn created, without
    /// re-issuing the challenge nonce. The registry's sequence is bumped past the
    /// adopted binding's verifying turn so later turns stay monotonic.
    pub fn adopt(&self, binding: DomainBinding) {
        if let Some(seq) = binding.verified_seq {
            self.next_seq.fetch_max(seq + 1, Ordering::Relaxed);
        }
        self.bindings
            .lock()
            .expect("bindings poisoned")
            .insert(binding.domain.clone(), binding);
    }
}

/// Normalize an inbound `Host` to a binding key: strip `:port`, trim, lowercase.
/// `None` for an empty host.
fn host_key(host: &str) -> Option<String> {
    let bare = host.split(':').next().unwrap_or(host).trim();
    if bare.is_empty() {
        return None;
    }
    Some(bare.to_ascii_lowercase())
}

/// The verifier's clock (unix seconds) — for a credential's temporal caveats. The
/// domains caps this crate mints carry no expiry, so the value is not load-bearing;
/// a real deployment standardizes the clock unit mint + verify agree on.
fn unix_now() -> u64 {
    use std::time::{SystemTime, UNIX_EPOCH};
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cap::mint_domains_cap;
    use crate::dns::MockDns;
    use dregg_auth::credential::RootKey;

    fn root() -> RootKey {
        RootKey::from_seed([7u8; 32])
    }

    fn registry() -> DomainRegistry {
        DomainRegistry::with_authority(root().public())
    }

    fn cap(domain: &str) -> DomainCap {
        DomainCap::new(mint_domains_cap(&root(), "dregg:alice").encode(), domain)
    }

    #[test]
    fn bind_requires_a_real_authorized_credential() {
        // No authority → every bind is refused (fail-closed).
        let no_auth = DomainRegistry::new();
        assert_eq!(
            no_auth.bind(
                &cap("blog.example.com"),
                "blog.example.com",
                "blog",
                ChallengeMethod::Txt
            ),
            Err(DomainError::NoAuthority),
        );

        // The rightful, root-minted credential binds; owner is its subject.
        let reg = registry();
        let r = reg
            .bind(
                &cap("blog.example.com"),
                "blog.example.com",
                "blog",
                ChallengeMethod::Txt,
            )
            .expect("bind");
        assert_eq!(r.domain, "blog.example.com");
        assert_eq!(r.site, "blog");
        assert_eq!(r.owner, "dregg:alice");
        assert_eq!(r.challenge.record_name, "_dregg-verify.blog.example.com");

        // A cap exercised for a different domain cannot bind blog.example.com.
        assert!(matches!(
            reg.bind(
                &cap("shop.example.com"),
                "blog.example.com",
                "blog",
                ChallengeMethod::Txt
            ),
            Err(DomainError::CapRefused { .. }),
        ));
        // Invalid site refused.
        assert!(matches!(
            reg.bind(
                &cap("x.example.com"),
                "x.example.com",
                "Bad.Name",
                ChallengeMethod::Txt
            ),
            Err(DomainError::InvalidSite(_)),
        ));
    }

    #[test]
    fn unverified_domain_does_not_resolve() {
        let reg = registry();
        let _ = reg
            .bind(
                &cap("blog.example.com"),
                "blog.example.com",
                "blog",
                ChallengeMethod::Txt,
            )
            .unwrap();
        // Pending → the gateway reads decline: no route, no cert.
        assert!(!reg.is_verified("blog.example.com"));
        assert_eq!(reg.site_for_host("blog.example.com"), None);
    }

    #[test]
    fn verify_flips_once_and_a_wrong_nonce_is_refused() {
        let reg = registry();
        let r = reg
            .bind(
                &cap("blog.example.com"),
                "blog.example.com",
                "blog",
                ChallengeMethod::Txt,
            )
            .unwrap();

        // A wrong TXT value → ChallengeUnmet, stays Pending.
        let wrong = MockDns::new().with_txt(&r.challenge.record_name, "dregg-verify-WRONG");
        assert_eq!(
            reg.verify("blog.example.com", &wrong),
            Err(DomainError::ChallengeUnmet {
                domain: "blog.example.com".into()
            }),
        );
        assert!(!reg.is_verified("blog.example.com"));

        // The exact nonce → Verified, and site_for_host now resolves.
        let dns = MockDns::new().with_txt(&r.challenge.record_name, &r.challenge.expected_value);
        let b = reg.verify("blog.example.com", &dns).expect("verify");
        assert!(b.is_verified());
        let seq = b.verified_seq.expect("a verifying turn was recorded");
        assert!(reg.is_verified("blog.example.com"));
        assert_eq!(
            reg.site_for_host("Blog.Example.Com:443").as_deref(),
            Some("blog")
        );

        // Idempotent re-verify does NOT advance the verifying sequence (flips once).
        let b2 = reg.verify("blog.example.com", &dns).expect("re-verify");
        assert_eq!(b2.verified_seq, Some(seq), "the flip happened once");
    }

    #[test]
    fn an_attacker_cannot_overwrite_a_victims_binding() {
        let reg = registry();
        let alice = DomainCap::new(
            mint_domains_cap(&root(), "dregg:alice").encode(),
            "blog.example.com",
        );
        reg.bind(&alice, "blog.example.com", "blog", ChallengeMethod::Txt)
            .unwrap();

        // Mallory holds her OWN valid root-minted credential — a different subject.
        let mallory = DomainCap::new(
            mint_domains_cap(&root(), "dregg:mallory").encode(),
            "blog.example.com",
        );
        assert_eq!(
            reg.bind(&mallory, "blog.example.com", "evil", ChallengeMethod::Txt),
            Err(DomainError::OwnerMismatch {
                domain: "blog.example.com".into()
            }),
        );
        assert_eq!(reg.get("blog.example.com").unwrap().owner, "dregg:alice");
    }

    #[test]
    fn verify_unbound_is_not_bound() {
        let reg = registry();
        assert_eq!(
            reg.verify("nope.example.com", &MockDns::new()),
            Err(DomainError::NotBound("nope.example.com".into())),
        );
    }
}
