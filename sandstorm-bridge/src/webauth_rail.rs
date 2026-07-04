//! **The powerbox on the `dregg-auth` cap rail.**
//!
//! A grain capability is a [`dregg_auth::credential::Credential`] — an ed25519
//! caveat-chain token (`dga1_…`), rooted at the host's
//! [`dregg_auth::credential::RootKey`], that only ever attenuates and is
//! re-verified cryptographically on every present. This module mints, attenuates,
//! and reads a grain capability on that rail, so the powerbox grant a grain
//! presents is a credential the host's forward-auth already understands.
//!
//! The mapping from Sandstorm's powerbox onto the rail:
//!
//! | powerbox / SturdyRef notion          | `dregg-auth` realization                            |
//! |--------------------------------------|-----------------------------------------------------|
//! | the host seal secret                 | the host [`RootKey`] (the authority root keypair)   |
//! | the cap target (a grain `CellId`)    | a `grain` attribute caveat `AttrEq{grain, <id>}`    |
//! | sealed-to-owner (`sealFor: Owner`)   | a `subject` attribute caveat `AttrEq{subject, <k>}` |
//! | the cap's effect facets              | a `cap` disjunction `AnyOf[AttrEq{cap, f}, …]`       |
//! | attenuate (narrow facets)            | [`Credential::attenuate`] — append a tighter `cap`  |
//! | restore + read facets                | [`Credential::verify`] under the host pubkey + ctx  |
//!
//! A forged credential (not signed by the host root) fails the ed25519 chain
//! verify; a leaked credential presented by a non-owner fails the `subject`
//! caveat; a credential for another grain fails the `grain` caveat; amplification
//! is impossible because [`Credential::attenuate`] only appends caveats (the facet
//! set can only shrink, never grow).

use dregg_auth::credential::{Caveat, Context, Credential, Pred, PublicKey, RootKey};

/// The grain capability's attribute keys on the real rail. A grain cap is a
/// `dga1_` credential whose first-party caveats bind these three.
const ATTR_GRAIN: &str = "grain";
const ATTR_SUBJECT: &str = "subject";
const ATTR_CAP: &str = "cap";

/// The host's powerbox authority — the [`RootKey`] every grain capability on this
/// host is rooted at (the real-rail analog of the in-crate `SealKey` host secret).
/// A credential that does not chain back to this root's public key is a forgery and
/// fails [`Credential::verify`]; only a holder of the root can mint a grain cap.
pub struct HostAuthority {
    root: RootKey,
}

impl HostAuthority {
    /// A host authority from a 32-byte secret seed — deterministic, for a host that
    /// derives its powerbox root from its master secret (or a KMS-held key).
    pub fn from_seed(seed: [u8; 32]) -> Self {
        HostAuthority {
            root: RootKey::from_seed(seed),
        }
    }

    /// A freshly generated host authority (OS randomness).
    pub fn generate() -> Self {
        HostAuthority {
            root: RootKey::generate(),
        }
    }

    /// The host root's public key — the verifier a grain (or a light client) checks a
    /// presented `dga1_` grain cap against. Safe to publish.
    pub fn public(&self) -> PublicKey {
        self.root.public()
    }

    /// **Mint a grain capability** on the real rail: a `dga1_…` credential conferring
    /// `facets` over grain `grain_cell_id`, sealed to `owner_subject` (only that
    /// subject can present it), optionally expiring at `not_after` (a unix-seconds
    /// vesting bound). The returned [`Credential`] encodes to a `dga1_` token with
    /// [`Credential::encode`]. This is the powerbox designation — the real
    /// `Effect::GrantCapability` artifact on the operated-layer side (the witnessed kernel
    /// turn lives in the breadstuffs authority core; the credential is its wire form).
    pub fn mint_grain_cap(
        &self,
        grain_cell_id: &str,
        owner_subject: &str,
        facets: &[&str],
        not_after: Option<u64>,
    ) -> Credential {
        let mut caveats = vec![
            Caveat::FirstParty(Pred::AttrEq {
                key: ATTR_GRAIN.into(),
                value: grain_cell_id.into(),
            }),
            Caveat::FirstParty(Pred::AttrEq {
                key: ATTR_SUBJECT.into(),
                value: owner_subject.into(),
            }),
            Caveat::FirstParty(facet_disjunction(facets)),
        ];
        if let Some(at) = not_after {
            caveats.push(Caveat::FirstParty(Pred::NotAfter { at }));
        }
        self.root.mint(caveats)
    }
}

/// The facet-set caveat: `AnyOf[AttrEq{cap, f} for f in facets]`. With the request
/// context binding exactly one `cap` attribute, the disjunction passes iff the
/// exercised facet is in the set. An empty facet set is `AnyOf[]`, which is
/// fail-closed (no facet ever satisfies it) — a cap with no facets confers nothing.
fn facet_disjunction(facets: &[&str]) -> Pred {
    Pred::AnyOf(
        facets
            .iter()
            .map(|f| Pred::AttrEq {
                key: ATTR_CAP.into(),
                value: (*f).to_string(),
            })
            .collect(),
    )
}

/// **Attenuate** a grain capability down to `restrict_to` facets, for a (possibly
/// different) `to_subject` — the delegation step. Appends a tighter `cap`
/// disjunction; the effective facet set becomes the intersection of every `cap`
/// caveat in the chain, so attenuation can only narrow (no amplification, ever).
/// The re-binding to `to_subject` adds a `subject` caveat so the sub-cap is sealed
/// to the recipient; the original owner caveat still holds (both must match), so a
/// delegated sub-cap is honored only when the chain's subject bindings agree —
/// i.e. delegate to the same subject, or leave `to_subject` `None` to keep the
/// original owner binding.
pub fn attenuate_grain_cap(
    cred: Credential,
    restrict_to: &[&str],
    to_subject: Option<&str>,
) -> Credential {
    let mut caveats = vec![Caveat::FirstParty(facet_disjunction(restrict_to))];
    if let Some(s) = to_subject {
        caveats.push(Caveat::FirstParty(Pred::AttrEq {
            key: ATTR_SUBJECT.into(),
            value: s.into(),
        }));
    }
    cred.attenuate(caveats)
}

/// **Derive the permission set** a presented `dga1_` grain cap confers — exactly the
/// facets the cap lattice admits for this presenter over this grain, right now. This
/// is the real-rail replacement for "restore the SturdyRef and read its facets": for
/// each facet the app declares, it asks the *real* [`Credential::verify`] whether the
/// cap admits it (under the host root, with the grain/subject/cap context bound). The
/// returned set is the `X-Sandstorm-Permissions` the bridge injects — derived from
/// the cap, never asserted by the host.
///
/// Returns an empty set (⇒ the bridge answers `403`) when the credential is a
/// forgery (chain verify fails), is for another grain, is presented by a non-owner,
/// has expired, or simply grants none of the declared facets — every refusal a hard,
/// fail-closed deny.
pub fn derive_permissions(
    token: &str,
    host_pub: &PublicKey,
    grain_cell_id: &str,
    presenter_subject: &str,
    declared_permissions: &[String],
    now: u64,
) -> Vec<String> {
    let cred = match Credential::decode(token) {
        Ok(c) => c,
        Err(_) => return Vec::new(),
    };
    let mut granted = Vec::new();
    for facet in declared_permissions {
        let ctx = Context::new()
            .at(now)
            .attr(ATTR_GRAIN, grain_cell_id)
            .attr(ATTR_SUBJECT, presenter_subject)
            .attr(ATTR_CAP, facet.clone());
        if cred.verify(host_pub, &ctx).is_ok() {
            granted.push(facet.clone());
        }
    }
    granted.sort();
    granted.dedup();
    granted
}

#[cfg(test)]
mod tests {
    use super::*;

    fn declared() -> Vec<String> {
        vec!["view".into(), "edit".into(), "admin".into()]
    }

    #[test]
    fn a_minted_grain_cap_is_a_real_dga1_credential() {
        let host = HostAuthority::from_seed([3u8; 32]);
        let cred = host.mint_grain_cap("cell:grain1", "u:alice", &["view", "edit"], None);
        let token = cred.encode();
        // The deployed wire is the real dregg-auth `dga1_` credential.
        assert!(token.starts_with("dga1_"));
        // And it decodes + verifies on the real rail.
        assert!(Credential::decode(&token).is_ok());
    }

    #[test]
    fn permissions_are_derived_from_the_cap_lattice() {
        let host = HostAuthority::from_seed([4u8; 32]);
        let token = host
            .mint_grain_cap("cell:grain1", "u:alice", &["view", "edit"], None)
            .encode();
        let perms = derive_permissions(
            &token,
            &host.public(),
            "cell:grain1",
            "u:alice",
            &declared(),
            1000,
        );
        // Exactly the granted facets — `admin` (declared but not granted) is absent.
        assert_eq!(perms, vec!["edit".to_string(), "view".to_string()]);
    }

    #[test]
    fn a_cap_for_another_grain_confers_nothing() {
        let host = HostAuthority::from_seed([5u8; 32]);
        let token = host
            .mint_grain_cap("cell:OTHER", "u:alice", &["view", "edit"], None)
            .encode();
        // Presented at cell:grain1 — the `grain` caveat fails, every facet refused.
        let perms = derive_permissions(
            &token,
            &host.public(),
            "cell:grain1",
            "u:alice",
            &declared(),
            1000,
        );
        assert!(perms.is_empty());
    }

    #[test]
    fn a_leaked_cap_presented_by_a_non_owner_confers_nothing() {
        let host = HostAuthority::from_seed([6u8; 32]);
        let token = host
            .mint_grain_cap("cell:grain1", "u:alice", &["view", "edit"], None)
            .encode();
        // mallory steals the token and presents it — the `subject` caveat fails.
        let perms = derive_permissions(
            &token,
            &host.public(),
            "cell:grain1",
            "u:mallory",
            &declared(),
            1000,
        );
        assert!(perms.is_empty());
    }

    #[test]
    fn a_forged_cap_not_signed_by_the_host_root_confers_nothing() {
        let host = HostAuthority::from_seed([7u8; 32]);
        // The attacker mints under their OWN root (they lack the host root key).
        let attacker = HostAuthority::from_seed([99u8; 32]);
        let forged = attacker
            .mint_grain_cap("cell:grain1", "u:mallory", &["view", "edit", "admin"], None)
            .encode();
        // Verified under the HOST root → the ed25519 chain verify fails, nothing granted.
        let perms = derive_permissions(
            &forged,
            &host.public(),
            "cell:grain1",
            "u:mallory",
            &declared(),
            1000,
        );
        assert!(perms.is_empty());
    }

    #[test]
    fn attenuation_only_narrows_no_amplification() {
        let host = HostAuthority::from_seed([8u8; 32]);
        let wide = host.mint_grain_cap("cell:grain1", "u:alice", &["view", "edit"], None);
        // Narrow to view-only (same subject).
        let narrowed = attenuate_grain_cap(wide, &["view"], None).encode();
        let perms = derive_permissions(
            &narrowed,
            &host.public(),
            "cell:grain1",
            "u:alice",
            &declared(),
            1000,
        );
        assert_eq!(perms, vec!["view".to_string()]);

        // Asking for `edit` back in a later attenuation cannot re-grant it: the chain
        // intersection has already dropped it.
        let narrowed2 = Credential::decode(&narrowed).unwrap();
        let reamped = attenuate_grain_cap(narrowed2, &["view", "edit"], None).encode();
        let perms2 = derive_permissions(
            &reamped,
            &host.public(),
            "cell:grain1",
            "u:alice",
            &declared(),
            1000,
        );
        assert_eq!(perms2, vec!["view".to_string()]);
    }

    #[test]
    fn an_expired_cap_confers_nothing() {
        let host = HostAuthority::from_seed([9u8; 32]);
        let token = host
            .mint_grain_cap("cell:grain1", "u:alice", &["view"], Some(500))
            .encode();
        // now = 1000 > not_after = 500 → the NotAfter caveat refuses.
        let perms = derive_permissions(
            &token,
            &host.public(),
            "cell:grain1",
            "u:alice",
            &declared(),
            1000,
        );
        assert!(perms.is_empty());
        // Before expiry it works.
        let ok = derive_permissions(
            &token,
            &host.public(),
            "cell:grain1",
            "u:alice",
            &declared(),
            100,
        );
        assert_eq!(ok, vec!["view".to_string()]);
    }
}
