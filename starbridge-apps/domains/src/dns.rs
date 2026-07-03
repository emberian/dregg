//! The DNS challenge seam — the injected [`DnsResolver`] trait, the deterministic
//! [`MockDns`] test instance, the challenge-satisfaction check, domain validity, and
//! the deterministic challenge nonce.
//!
//! Verification is driven through the [`DnsResolver`] trait so the check is a real
//! DNS query in production (a host-wired client implementing the sync trait) and a
//! deterministic [`MockDns`] in tests — the bind -> challenge -> verify round-trip
//! proves locally with no live DNS and no real cert. The trait is kept minimal: only
//! the two record types a challenge needs (TXT and CNAME).
//!
//! A production resolver implements [`DnsResolver`] over a real DNS client (bridging
//! its async lookups to the sync trait the bind/verify state machine and the gateway
//! routing use). This crate ships no live client — the resolver is the injected seam,
//! wired by the host — so the crate stays portable and dependency-light.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

/// The DNS label a TXT challenge is published under: `_dregg-verify.<domain>`.
pub const TXT_CHALLENGE_PREFIX: &str = "_dregg-verify.";

/// The platform apex custom domains bind *onto* — a binding's site `<name>` serves at
/// `<name>.<apex>`, and a CNAME challenge points the custom domain here. A `<x>.<apex>`
/// host is the platform wildcard path, not a "custom" domain, so it is refused by
/// [`is_valid_domain`].
pub const HOSTING_APEX: &str = "acme.dev";

/// Which DNS record proves control of a custom domain.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ChallengeMethod {
    /// Publish a TXT record at `_dregg-verify.<domain>` equal to the nonce.
    Txt,
    /// Point `<domain>` (CNAME) at `<site>.<apex>`.
    Cname,
}

impl ChallengeMethod {
    /// The stable numeric code (for the field-image of a method, if committed).
    pub fn code(self) -> u64 {
        match self {
            ChallengeMethod::Txt => 0,
            ChallengeMethod::Cname => 1,
        }
    }
}

/// Whether a binding has proven control of its domain yet — the field-imaged
/// `verification_state` a domain cell commits (`Monotonic`, one-way).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum VerificationState {
    /// Bound, challenge issued, control not yet proven. Not routed; no cert.
    Pending,
    /// Control proven — the binding routes and is eligible for a certificate.
    Verified,
}

impl VerificationState {
    /// The stable numeric code committed at [`VERIFICATION_STATE_SLOT`](crate::VERIFICATION_STATE_SLOT):
    /// `0` pending, `1` verified. The `Monotonic` caveat makes `0 -> 1` one-way.
    pub fn code(self) -> u64 {
        match self {
            VerificationState::Pending => 0,
            VerificationState::Verified => 1,
        }
    }

    /// Whether this state is [`VerificationState::Verified`].
    pub fn is_verified(self) -> bool {
        matches!(self, VerificationState::Verified)
    }
}

/// The DNS record that proves control of a custom domain — what the owner publishes
/// and what the verify path checks for.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DnsChallenge {
    /// TXT or CNAME.
    pub record_type: ChallengeMethod,
    /// The DNS name the record lives at (`_dregg-verify.<domain>` for TXT, the
    /// `<domain>` itself for CNAME).
    pub record_name: String,
    /// The value the record must carry (the nonce for TXT, `<site>.<apex>` for CNAME).
    pub expected_value: String,
}

/// A DNS resolver the verify check queries. The production instance is a host-wired
/// client over live DNS; tests use [`MockDns`]. Kept minimal — only the two record
/// types a challenge needs.
pub trait DnsResolver {
    /// The TXT values published at `name` (empty if none / NXDOMAIN).
    fn txt(&self, name: &str) -> Vec<String>;
    /// The CNAME target of `name`, if any. The returned target may carry a trailing
    /// dot (FQDN form); the verify check compares case-insensitively without it.
    fn cname(&self, name: &str) -> Option<String>;
}

/// An in-memory [`DnsResolver`] for tests: a fixed set of TXT and CNAME records.
/// Drives the verify path deterministically with no live DNS.
#[derive(Debug, Default, Clone)]
pub struct MockDns {
    txt: BTreeMap<String, Vec<String>>,
    cname: BTreeMap<String, String>,
}

impl MockDns {
    /// An empty resolver (no records — every lookup misses, so every verify is
    /// [`ChallengeUnmet`](crate::DomainError::ChallengeUnmet)).
    pub fn new() -> MockDns {
        MockDns::default()
    }

    /// Add a TXT value at `name`.
    pub fn with_txt(mut self, name: &str, value: &str) -> MockDns {
        self.txt
            .entry(name.to_ascii_lowercase())
            .or_default()
            .push(value.to_string());
        self
    }

    /// Add a CNAME target at `name`.
    pub fn with_cname(mut self, name: &str, target: &str) -> MockDns {
        self.cname
            .insert(name.to_ascii_lowercase(), target.to_string());
        self
    }
}

impl DnsResolver for MockDns {
    fn txt(&self, name: &str) -> Vec<String> {
        self.txt
            .get(&name.to_ascii_lowercase())
            .cloned()
            .unwrap_or_default()
    }
    fn cname(&self, name: &str) -> Option<String> {
        self.cname.get(&name.to_ascii_lowercase()).cloned()
    }
}

/// Whether a DNS `challenge` is satisfied by `dns`. TXT: any published value equals
/// the nonce. CNAME: the target (trailing dot tolerated) matches `<site>.<apex>`
/// case-insensitively. An unreachable resolver (empty answer) reads as "no proof" —
/// never a false positive.
pub fn challenge_satisfied(challenge: &DnsChallenge, dns: &impl DnsResolver) -> bool {
    match challenge.record_type {
        ChallengeMethod::Txt => dns
            .txt(&challenge.record_name)
            .iter()
            .any(|v| v == &challenge.expected_value),
        ChallengeMethod::Cname => dns
            .cname(&challenge.record_name)
            .map(|t| {
                t.trim_end_matches('.')
                    .eq_ignore_ascii_case(&challenge.expected_value)
            })
            .unwrap_or(false),
    }
}

/// Whether `domain` is a usable custom domain: a multi-label FQDN whose labels are
/// each valid DNS labels, and which is NOT the platform apex or a `<x>.<apex>` host
/// (that is the wildcard hosting path, served without a binding).
pub fn is_valid_domain(domain: &str) -> bool {
    let domain = domain.trim().trim_end_matches('.').to_ascii_lowercase();
    if domain.is_empty() || domain.len() > 253 {
        return false;
    }
    // A custom domain owns its own apex; the platform wildcard is not "custom".
    if domain == HOSTING_APEX || domain.ends_with(&format!(".{HOSTING_APEX}")) {
        return false;
    }
    let labels: Vec<&str> = domain.split('.').collect();
    if labels.len() < 2 {
        return false;
    }
    labels.iter().all(|l| is_valid_label(l))
}

/// A single DNS label: non-empty, `<= 63`, `[a-z0-9-]`, not edge-`-`. Used for both a
/// domain's per-label validity and a bound site `<name>`.
pub fn is_valid_label(label: &str) -> bool {
    let label = label.to_ascii_lowercase();
    if label.is_empty() || label.len() > 63 {
        return false;
    }
    if label.starts_with('-') || label.ends_with('-') {
        return false;
    }
    label
        .bytes()
        .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-')
}

/// A deterministic challenge nonce for `(domain, owner, seq)`. FNV-1a/64 hex,
/// prefixed `dregg-verify-`. Deterministic so a bind receipt is re-derivable; bound
/// to the owner + the registry seq so two binds never collide. (On a real node the
/// nonce is drawn from the cell's commitment; the property — a value the owner must
/// place in DNS to prove control — is the same.)
pub fn challenge_token(domain: &str, owner: &str, seq: u64) -> String {
    const OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
    const PRIME: u64 = 0x0000_0100_0000_01b3;
    let mut h: u64 = OFFSET;
    let mut mix = |bytes: &[u8]| {
        for &b in bytes {
            h ^= b as u64;
            h = h.wrapping_mul(PRIME);
        }
        h ^= 0xff;
        h = h.wrapping_mul(PRIME);
    };
    mix(domain.as_bytes());
    mix(owner.as_bytes());
    mix(&seq.to_le_bytes());
    format!("dregg-verify-{h:016x}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn domain_validity() {
        assert!(is_valid_domain("blog.example.com"));
        assert!(is_valid_domain("shop.example.co.uk"));
        assert!(!is_valid_domain(""));
        assert!(!is_valid_domain("localhost")); // single label
        assert!(!is_valid_domain("has space.com"));
        assert!(!is_valid_domain("-bad.com"));
        assert!(!is_valid_domain("bad-.com"));
        // The platform wildcard path is not a "custom" domain.
        assert!(!is_valid_domain(HOSTING_APEX));
        assert!(!is_valid_domain(&format!("blog.{HOSTING_APEX}")));
    }

    #[test]
    fn txt_challenge_is_satisfied_only_by_the_exact_nonce() {
        let challenge = DnsChallenge {
            record_type: ChallengeMethod::Txt,
            record_name: "_dregg-verify.blog.example.com".into(),
            expected_value: "dregg-verify-abc123".into(),
        };
        // No record → unmet.
        assert!(!challenge_satisfied(&challenge, &MockDns::new()));
        // A wrong value → unmet.
        let wrong = MockDns::new().with_txt(&challenge.record_name, "dregg-verify-WRONG");
        assert!(!challenge_satisfied(&challenge, &wrong));
        // The exact nonce → met.
        let right = MockDns::new().with_txt(&challenge.record_name, &challenge.expected_value);
        assert!(challenge_satisfied(&challenge, &right));
    }

    #[test]
    fn cname_challenge_tolerates_the_trailing_dot() {
        let challenge = DnsChallenge {
            record_type: ChallengeMethod::Cname,
            record_name: "www.example.com".into(),
            expected_value: "blog.acme.dev".into(),
        };
        let wrong = MockDns::new().with_cname("www.example.com", "evil.acme.dev");
        assert!(!challenge_satisfied(&challenge, &wrong));
        let right = MockDns::new().with_cname("www.example.com", "blog.acme.dev.");
        assert!(challenge_satisfied(&challenge, &right));
    }

    #[test]
    fn challenge_token_is_deterministic_and_owner_seq_bound() {
        let a = challenge_token("blog.example.com", "dregg:alice", 0);
        assert_eq!(a, challenge_token("blog.example.com", "dregg:alice", 0));
        assert!(a.starts_with("dregg-verify-"));
        // Different owner / seq → different nonce.
        assert_ne!(a, challenge_token("blog.example.com", "dregg:bob", 0));
        assert_ne!(a, challenge_token("blog.example.com", "dregg:alice", 1));
    }

    #[test]
    fn verification_state_codes_are_stable() {
        assert_eq!(VerificationState::Pending.code(), 0);
        assert_eq!(VerificationState::Verified.code(), 1);
        assert!(VerificationState::Verified.is_verified());
        assert!(!VerificationState::Pending.is_verified());
    }
}
