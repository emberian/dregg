//! **The grain share model: roles as an attenuable region of a facet lattice,
//! grounded natively on the `dregg-auth` credential rail.**
//!
//! Single-owner isolation (the `Tenant::owner`) answers *is this grain yours?*
//! with `owner == subject`. Sharing generalizes that to a **membership + role**:
//! the owner (implicit [`Role::Admin`]) plus a per-grain ACL of
//! `(verified X-Dregg-Subject → [`Role`])` grants.
//!
//! ### The port (the audit's finding, honoured)
//! The upstream crate re-exported this algebra from a separate attach portal that
//! layered its own `dga1_` twin over a `Credential` rail. The audit flagged that as
//! a *different* credential model than breadstuffs' native `dregg-auth`, so this is
//! a real **port**, not a retarget: the Role lattice and its cryptographic twin
//! ([`ShareAuthority`]) are implemented here directly on
//! [`dregg_auth::credential`] — the same proven caveat chain the `sandstorm-bridge`
//! powerbox rail uses, verified offline. The Role LATTICE semantics
//! (Viewer ⊂ Driver ⊂ Admin, no-amplify) are preserved exactly; the public surface
//! the rest of the crate expects (the `Role` enum + `ShareAuthority`) is unchanged.
//!
//! The mapping (mirrors `sandstorm-bridge/src/webauth_rail.rs`, scoped to a grain):
//!
//! | share notion                       | `dregg-auth` realization                             |
//! |------------------------------------|------------------------------------------------------|
//! | the grain being shared             | a `session` attribute caveat `AttrEq{session, <id>}` |
//! | sealed-to-the-holder               | a `subject` attribute caveat `AttrEq{subject, <k>}`  |
//! | a role's capability facets         | a `cap` disjunction `AnyOf[AttrEq{cap, f}, …]`       |
//! | share at a role (narrow the facets)| [`Credential::attenuate`] — append a tighter `cap`   |
//! | what may this holder do?           | [`Credential::verify`] under the host root + context |
//!
//! ### Roles ARE a facet lattice
//! `Viewer ⊂ Driver ⊂ Admin`, exactly as their facet sets nest
//! (`{read} ⊂ {read,drive} ⊂ {read,drive,admin}`). A Viewer may read the
//! transcript/receipts + re-witness but **cannot drive**; a Driver drives (spends
//! the grain's budget through the cap-gate); an Admin also shares/unshares. Because
//! a share is only ever an **attenuation** of the grain's base cap, a Viewer's
//! share can never be re-widened back up to `drive` — amplification is impossible
//! on the wire, not merely refused by policy.
//!
//! ### What enforces the served routes — and why (the trust boundary, crisply)
//! The runtime gate on the served HTTP routes is the **in-memory ACL**
//! ([`crate::AgentPlatform::role_of`]) keyed on the *verified* `X-Dregg-Subject`
//! the forward-auth proxy set — fail-closed (an unknown subject or an unparseable
//! role confers nothing → a non-member 404s, no existence oracle). That is a
//! deliberate choice: **`/unshare` must actually revoke**, and a bearer `dga1_`
//! share verifies offline regardless of any later revocation, so a token-only
//! runtime gate would make revocation a lie. The ACL is the revocable authority;
//! the [`ShareAuthority`] `dga1_` twin is the **offline/edge verifier** — the
//! ground a holder on another host (or a light client) checks a presented share
//! against without trusting this host's memory — and the grain-scoped agreement
//! between the two gates is pinned by
//! [`tests::the_dga1_twin_agrees_with_the_acl_gate_on_a_grain`]. What the wire twin
//! adds that the ACL cannot: non-amplification is a property of the TOKEN (a Viewer
//! share can never be re-widened to `drive`), which survives a malicious host.

use serde::{Deserialize, Serialize};

use dregg_auth::credential::{Caveat, Context, Credential, Pred, PublicKey, RootKey};

/// **Read** the transcript + receipts + re-witness the grain. Every role holds it.
pub const FACET_READ: &str = "read";
/// **Drive** the agent — converse / drive its tools (a metered, receipted turn).
pub const FACET_DRIVE: &str = "drive";
/// **Administer** the grain — reconfigure / backup / transfer / share (grant+revoke).
pub const FACET_ADMIN: &str = "admin";

/// Every facet a grain cap can carry — the `declared_permissions` the derive step
/// probes (the app declares what it will ask for; the cap decides what it admits).
pub const ALL_FACETS: [&str; 3] = [FACET_READ, FACET_DRIVE, FACET_ADMIN];

/// The share cap's attribute keys on the real rail (the `session`/`subject`/`cap`
/// context every presented share is verified under).
const ATTR_SESSION: &str = "session";
const ATTR_SUBJECT: &str = "subject";
const ATTR_CAP: &str = "cap";

/// A holder's role on a shared grain — an attenuable region of the facet lattice.
///
/// The order is the subset order on [`Role::facets`]: `Viewer ⊂ Driver ⊂ Admin`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Role {
    /// Read the transcript/receipts and re-witness — but **cannot drive** a tool.
    Viewer,
    /// Converse with + drive the agent (plus everything a Viewer may do).
    Driver,
    /// Reconfigure / backup / transfer / share the grain (plus Driver + Viewer).
    Admin,
}

impl Role {
    /// The facet subset this role confers — the `cap` disjunction a share at this
    /// role carries. Nested by construction, so the roles form the lattice.
    pub fn facets(self) -> &'static [&'static str] {
        match self {
            Role::Viewer => &[FACET_READ],
            Role::Driver => &[FACET_READ, FACET_DRIVE],
            Role::Admin => &[FACET_READ, FACET_DRIVE, FACET_ADMIN],
        }
    }

    /// Every role may read (view the transcript/receipts + re-witness).
    pub fn can_read(self) -> bool {
        self.facets().contains(&FACET_READ)
    }

    /// May this role **drive** a tool? Driver + Admin — never a Viewer (fail-closed).
    pub fn can_drive(self) -> bool {
        self.facets().contains(&FACET_DRIVE)
    }

    /// May this role **administer** (grant/revoke/reconfigure)? Admin only.
    pub fn can_admin(self) -> bool {
        self.facets().contains(&FACET_ADMIN)
    }

    /// The wire/JSON spelling (`"viewer"` / `"driver"` / `"admin"`).
    pub fn as_str(self) -> &'static str {
        match self {
            Role::Viewer => "viewer",
            Role::Driver => "driver",
            Role::Admin => "admin",
        }
    }

    /// Parse a role name (case-insensitive). `None` for an unknown role — the caller
    /// fails closed (an unrecognized role grants nothing).
    pub fn parse(s: &str) -> Option<Role> {
        match s.trim().to_ascii_lowercase().as_str() {
            "viewer" | "view" => Some(Role::Viewer),
            "driver" | "drive" => Some(Role::Driver),
            "admin" => Some(Role::Admin),
            _ => None,
        }
    }

    /// The **maximal** role a derived facet set admits — the cryptographic ground of
    /// a role. Maps a set of facets read back off a presented `dga1_` share (via
    /// [`ShareAuthority::derive_facets`]) to the strongest role it supports, so the
    /// gate can be driven by the *cap* and not merely the stored row. `None` when the
    /// facet set does not even carry `read` (confers nothing → not a member).
    pub fn from_facets(facets: &[String]) -> Option<Role> {
        let has = |f: &str| facets.iter().any(|g| g == f);
        if has(FACET_ADMIN) {
            Some(Role::Admin)
        } else if has(FACET_DRIVE) {
            Some(Role::Driver)
        } else if has(FACET_READ) {
            Some(Role::Viewer)
        } else {
            None
        }
    }
}

/// The `cap` facet caveat: `AnyOf[AttrEq{cap, f} for f in facets]`. With the request
/// context binding exactly one `cap` attribute, the disjunction passes iff the
/// exercised facet is in the set. An empty set is `AnyOf[]` — fail-closed (no facet
/// satisfies it), so a cap with no facets confers nothing.
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

/// **The per-host share-signing authority** — a [`RootKey`] the grain shares are
/// rooted at (the grain-scoped analog of the powerbox `HostAuthority` in
/// `sandstorm-bridge`). A share that does not chain back to this root's public key
/// is a forgery and fails [`Credential::verify`]; only the host holding the root can
/// mint or extend a grain share.
pub struct ShareAuthority {
    root: RootKey,
}

impl ShareAuthority {
    /// A deterministic authority from a 32-byte seed (a host that derives its
    /// share-signing root from its master secret / a KMS-held key).
    pub fn from_seed(seed: [u8; 32]) -> Self {
        ShareAuthority {
            root: RootKey::from_seed(seed),
        }
    }

    /// A freshly generated authority (OS randomness).
    pub fn generate() -> Self {
        ShareAuthority {
            root: RootKey::generate(),
        }
    }

    /// The root's public key — the verifier a holder (or an offline light client)
    /// checks a presented `dga1_` share against. Safe to publish.
    pub fn public(&self) -> PublicKey {
        self.root.public()
    }

    /// **Mint the grain's base cap** — the root of every share for `session_id` (the
    /// grain host id). It binds the grain and carries the full facet set, but is
    /// **NOT sealed to a subject**, so each share can be an attenuation that seals
    /// itself to its own holder. The host holds this; it is never handed out (a share
    /// is always the narrowed, sealed [`ShareAuthority::share_at`] of it). Returned as
    /// its `dga1_` wire form.
    pub fn mint_base(&self, session_id: &str) -> String {
        self.root
            .mint([
                Caveat::FirstParty(Pred::AttrEq {
                    key: ATTR_SESSION.into(),
                    value: session_id.into(),
                }),
                Caveat::FirstParty(facet_disjunction(&ALL_FACETS)),
            ])
            .encode()
    }

    /// **Share at a role**: attenuate the grain's base cap down to `role`'s facet
    /// subset and **seal it to `to_subject`** (only that holder can present it). The
    /// effective facet set is the *intersection* of every `cap` caveat in the chain,
    /// so a share can only ever narrow — a Viewer share cannot be re-widened to
    /// `drive`. Returns the sealed `dga1_` token the second holder carries; `None`
    /// if the base token does not decode (a corrupt base).
    pub fn share_at(
        &self,
        base_token: &str,
        role: Role,
        to_subject: &str,
        not_after: Option<u64>,
    ) -> Option<String> {
        let base = Credential::decode(base_token).ok()?;
        let mut caveats = vec![
            Caveat::FirstParty(facet_disjunction(role.facets())),
            Caveat::FirstParty(Pred::AttrEq {
                key: ATTR_SUBJECT.into(),
                value: to_subject.into(),
            }),
        ];
        if let Some(at) = not_after {
            caveats.push(Caveat::FirstParty(Pred::NotAfter { at }));
        }
        Some(base.attenuate(caveats).encode())
    }

    /// **Derive the facets a presented share confers** — exactly what this presenter
    /// may do on this grain, right now, per the cap lattice. For each declared facet
    /// it asks the *real* [`Credential::verify`] whether the share admits it (under
    /// the host root, with the session/subject/cap context bound). The cryptographic
    /// ground of the role gate.
    ///
    /// Returns an empty set (⇒ confers nothing) when the token is a forgery (chain
    /// verify fails), is for another grain, is presented by a non-holder (the
    /// `subject` seal fails), has expired, or simply grants none of the declared
    /// facets — every refusal a hard, fail-closed deny.
    pub fn derive_facets(
        &self,
        token: &str,
        session_id: &str,
        presenter_subject: &str,
        now: u64,
    ) -> Vec<String> {
        let cred = match Credential::decode(token) {
            Ok(c) => c,
            Err(_) => return Vec::new(),
        };
        let host_pub = self.public();
        let mut granted = Vec::new();
        for facet in ALL_FACETS {
            let ctx = Context::new()
                .at(now)
                .attr(ATTR_SESSION, session_id)
                .attr(ATTR_SUBJECT, presenter_subject)
                .attr(ATTR_CAP, facet);
            if cred.verify(&host_pub, &ctx).is_ok() {
                granted.push(facet.to_string());
            }
        }
        granted.sort();
        granted.dedup();
        granted
    }

    /// The role a presented share cryptographically supports for this presenter —
    /// [`Role::from_facets`] over [`ShareAuthority::derive_facets`]. `None` ⇒ the
    /// share confers nothing (forged / wrong grain / wrong holder / expired), the
    /// same fail-closed shape as a non-member.
    pub fn role_of_cap(
        &self,
        token: &str,
        session_id: &str,
        presenter_subject: &str,
        now: u64,
    ) -> Option<Role> {
        Role::from_facets(&self.derive_facets(token, session_id, presenter_subject, now))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const GRAIN: &str = "alice.agents.dregg";
    const BOB: &str = "dga1_bob";
    const MALLORY: &str = "dga1_mallory";

    /// The ported lattice keeps its teeth here (a regression in the algebra would
    /// break the GRAIN's gate, so the grain crate pins it).
    #[test]
    fn roles_are_a_facet_lattice() {
        assert!(Role::Viewer.can_read() && !Role::Viewer.can_drive() && !Role::Viewer.can_admin());
        assert!(Role::Driver.can_read() && Role::Driver.can_drive() && !Role::Driver.can_admin());
        assert!(Role::Admin.can_read() && Role::Admin.can_drive() && Role::Admin.can_admin());
        // Viewer ⊂ Driver ⊂ Admin as facet sets.
        for f in Role::Viewer.facets() {
            assert!(Role::Driver.facets().contains(f));
        }
        for f in Role::Driver.facets() {
            assert!(Role::Admin.facets().contains(f));
        }
    }

    #[test]
    fn role_parses_fail_closed_and_round_trips() {
        assert_eq!(Role::parse("viewer"), Some(Role::Viewer));
        assert_eq!(Role::parse("Driver"), Some(Role::Driver));
        assert_eq!(Role::parse("ADMIN"), Some(Role::Admin));
        // An unknown role confers nothing (the gate fails closed).
        assert_eq!(Role::parse("root"), None);
        assert_eq!(Role::parse("superuser"), None);
        assert_eq!(Role::parse(""), None);
        for r in [Role::Viewer, Role::Driver, Role::Admin] {
            assert_eq!(Role::parse(r.as_str()), Some(r));
        }
    }

    /// **The dga1_ twin agrees with the ACL gate on a GRAIN.** The offline
    /// cryptographic rail, exercised with a grain host as the shared-resource id:
    /// a Viewer share sealed to Bob confers exactly Viewer (cannot drive), a
    /// stolen share presented by Mallory confers NOTHING (subject seal), and a
    /// share for another grain confers nothing here — the same fail-closed shape
    /// the ACL gate gives the routes. Both polarities.
    #[test]
    fn the_dga1_twin_agrees_with_the_acl_gate_on_a_grain() {
        let host = ShareAuthority::from_seed([42u8; 32]);
        let base = host.mint_base(GRAIN);

        // Positive: Bob's Viewer share is exactly Viewer — read yes, drive no.
        let viewer = host
            .share_at(&base, Role::Viewer, BOB, None)
            .expect("share");
        assert!(viewer.starts_with("dga1_"), "the twin rides the real rail");
        assert_eq!(
            host.role_of_cap(&viewer, GRAIN, BOB, 1000),
            Some(Role::Viewer)
        );
        assert!(
            !host
                .role_of_cap(&viewer, GRAIN, BOB, 1000)
                .unwrap()
                .can_drive()
        );

        // Positive: a Driver share drives.
        let driver = host
            .share_at(&base, Role::Driver, BOB, None)
            .expect("share");
        assert!(
            host.role_of_cap(&driver, GRAIN, BOB, 1000)
                .unwrap()
                .can_drive()
        );

        // Negative: Mallory presenting Bob's share gets nothing (subject seal).
        assert_eq!(host.role_of_cap(&driver, GRAIN, MALLORY, 1000), None);

        // Negative: a share minted for ANOTHER grain confers nothing on this one.
        let other_base = host.mint_base("other.agents.dregg");
        let other = host
            .share_at(&other_base, Role::Admin, BOB, None)
            .expect("share");
        assert_eq!(host.role_of_cap(&other, GRAIN, BOB, 1000), None);
    }
}
