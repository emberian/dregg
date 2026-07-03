//! **Role → permission → cap.** The bridge that makes the dregg-auth
//! attenuation lattice legible as orgs + roles — the crate's whole design.
//!
//! The org is its own dregg cell: it has its own minting authority (a
//! [`RootKey`](dregg_auth::credential::RootKey), held by [`crate::OrgAuthority`]).
//! The org-owner's authority is the **owner grant** ([`org_owner_grant`]) — a
//! credential minted by the org root that:
//! 1. pins `AttrEq{org = <org id>}` (so EVERY cap descended from it is
//! org-scoped: it only ever satisfies a context naming this org), and
//! 2. grants `AnyOf(all permissions)` (the full owner authority).
//!
//! A role-cap is that grant **attenuated** to the role's permission subset
//! ([`attenuate_to_role`]): one appended `AnyOf(role perms)` caveat. By the meet
//! semantics of the caveat chain (`metatheory/Dregg2/Authority/Caveat.lean`
//! `Token.admits`), the attenuated cap admits a request iff the request satisfies
//! *both* the owner grant (any perm, this org) *and* the role caveat (a perm in
//! the role) — i.e. exactly the role's permissions over exactly this org. And
//! because dregg-auth's `Credential::attenuate` has no removal API and the
//! signature chain is unforgeable (`attenuate_subset` / the `BiscuitGraph`
//! forged-block tooth), appending a caveat can only ever *narrow*: a viewer who
//! tries to append a `write` caveat to self-promote only makes the meet `read AND
//! write` = unsatisfiable, never `write`. That no-amplify property IS the security
//! of roles — proven over the very `attenuate` the `dregg-auth` credential core
//! carries (`the migration plan` §3.5: the same lattice `dregg-auth/src/grant.rs`
//! proves; the credential core is `webauth/cred.rs`'s native successor).

use dregg_auth::credential::{Caveat, Context, Credential, Pred, PublicKey, Refusal, RootKey};

use crate::role::{ORG_KEY, PERM_KEY, Permission, Role};

/// Derive the org's stable id from its minting authority's public key. The org is
/// a cell; its id is `org:<first 16 hex of the org root pubkey>` — the same shape
/// as a dregg subject (`dregg:<16 hex>`), but for an org-account.
pub fn org_id_of(root_pubkey: &PublicKey) -> String {
    format!("org:{}", &root_pubkey.to_hex()[..16])
}

/// The `AnyOf(perm = p for p in perms)` caveat — admits iff the context's `perm`
/// is one of `perms`. The single building block of both the owner grant and every
/// role attenuation.
fn perm_anyof(perms: &[Permission]) -> Caveat {
    Caveat::FirstParty(Pred::AnyOf(
        perms
            .iter()
            .map(|p| Pred::AttrEq {
                key: PERM_KEY.to_string(),
                value: p.as_str().to_string(),
            })
            .collect(),
    ))
}

/// Mint the **owner grant** — the org-owner's full, org-scoped authority. Every
/// role-cap is an attenuation of this. Held by the founding owner; re-minted by
/// the org authority to issue each member's role-cap.
pub fn org_owner_grant(root: &RootKey, org_id: &str) -> Credential {
    root.mint([
        // The org-scoping tooth: pinned for the whole descent.
        Caveat::FirstParty(Pred::AttrEq {
            key: ORG_KEY.to_string(),
            value: org_id.to_string(),
        }),
        // The full owner authority — every permission.
        perm_anyof(&Permission::ALL),
    ])
}

/// Attenuate an owner grant down to a role's permissions (and optionally a tighter
/// expiry). The appended `AnyOf(role perms)` caveat can only *narrow* reach — this
/// is where "the role IS an attenuation of the owner's authority" is literal.
pub fn attenuate_to_role(grant: Credential, role: Role, until: Option<u64>) -> Credential {
    let mut caveats = vec![perm_anyof(&role.permissions())];
    if let Some(at) = until {
        caveats.push(Caveat::FirstParty(Pred::NotAfter { at }));
    }
    grant.attenuate(caveats)
}

/// Mint a fresh role-cap for `role` over the org named by `root` — the owner
/// grant, attenuated to the role. This is what an org issues to a member when it
/// accepts them: their portable, offline-verifiable authority over the org's
/// resources, narrowed to their role.
pub fn mint_role_cap(root: &RootKey, org_id: &str, role: Role, until: Option<u64>) -> Credential {
    attenuate_to_role(org_owner_grant(root, org_id), role, until)
}

/// The verification context for an action requiring `perm` over `org_id` at clock
/// `now`. Binds the two teeth: `org` (scoping) and `perm` (role-gating).
pub fn action_context(org_id: &str, perm: Permission, now: u64) -> Context {
    Context::new()
        .at(now)
        .attr(ORG_KEY, org_id)
        .attr(PERM_KEY, perm.as_str())
}

/// Authorize a role-cap to perform `perm` over `org_id` at clock `now`, verifying
/// it against the org's root public key — fully offline, fail-closed. `Ok(())` iff
/// the cap was minted by THIS org's authority AND its role grants `perm`. A
/// viewer-cap for `ResourceWrite`, or any org's cap against another org's id/key,
/// is a [`Refusal`].
pub fn authorize(
    cap: &Credential,
    org_root_pubkey: &PublicKey,
    org_id: &str,
    perm: Permission,
    now: u64,
) -> Result<(), Refusal> {
    cap.verify(org_root_pubkey, &action_context(org_id, perm, now))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn org() -> (RootKey, String) {
        let root = RootKey::from_seed([3u8; 32]);
        let id = org_id_of(&root.public());
        (root, id)
    }

    #[test]
    fn role_cap_admits_exactly_its_permissions() {
        let (root, id) = org();
        let pk = root.public();

        let viewer = mint_role_cap(&root, &id, Role::Viewer, None);
        // viewer reads…
        assert!(authorize(&viewer, &pk, &id, Permission::ResourceRead, 100).is_ok());
        // …but cannot write/create/delete/manage/bill/delete-org.
        for p in [
            Permission::ResourceWrite,
            Permission::ResourceCreate,
            Permission::ResourceDelete,
            Permission::MembersManage,
            Permission::BillingPay,
            Permission::OrgDelete,
        ] {
            assert!(
                authorize(&viewer, &pk, &id, p, 100).is_err(),
                "viewer must be refused {p:?}"
            );
        }

        let admin = mint_role_cap(&root, &id, Role::Admin, None);
        assert!(authorize(&admin, &pk, &id, Permission::MembersManage, 100).is_ok());
        assert!(authorize(&admin, &pk, &id, Permission::ResourceDelete, 100).is_ok());
        // admin cannot delete the org or transfer ownership.
        assert!(authorize(&admin, &pk, &id, Permission::OrgDelete, 100).is_err());
        assert!(authorize(&admin, &pk, &id, Permission::OrgTransfer, 100).is_err());
    }

    #[test]
    fn org_scoping_tooth_refuses_a_foreign_org() {
        let (root_a, id_a) = org();
        let root_b = RootKey::from_seed([4u8; 32]);
        let id_b = org_id_of(&root_b.public());

        let cap_a = mint_role_cap(&root_a, &id_a, Role::Member, None);

        // Same key, but the action names org B → the pinned AttrEq{org=A} refuses.
        assert!(
            authorize(
                &cap_a,
                &root_a.public(),
                &id_b,
                Permission::ResourceWrite,
                100
            )
            .is_err()
        );
        // And verified under org B's key (the real cross-org case) → bad signature.
        assert!(
            authorize(
                &cap_a,
                &root_b.public(),
                &id_b,
                Permission::ResourceWrite,
                100
            )
            .is_err()
        );
        // It of course still works over its own org.
        assert!(
            authorize(
                &cap_a,
                &root_a.public(),
                &id_a,
                Permission::ResourceWrite,
                100
            )
            .is_ok()
        );
    }

    #[test]
    fn no_amplify_a_viewer_cannot_self_promote_to_write() {
        let (root, id) = org();
        let pk = root.public();
        let viewer = mint_role_cap(&root, &id, Role::Viewer, None);

        // The viewer holds the bearer token and tries to widen it by appending a
        // "write" caveat (the obvious self-promotion attack). attenuate ONLY
        // narrows: the meet is now (read) AND (write) — unsatisfiable for any
        // single perm — so the forged cap reaches NOTHING, not write.
        let forged = viewer.attenuate([perm_anyof(&[Permission::ResourceWrite])]);
        assert!(
            authorize(&forged, &pk, &id, Permission::ResourceWrite, 100).is_err(),
            "appending a write caveat must not grant write (no amplification)"
        );
        assert!(
            authorize(&forged, &pk, &id, Permission::ResourceRead, 100).is_err(),
            "the meet read AND write is unsatisfiable — the forge self-revokes"
        );
    }

    #[test]
    fn expiry_attenuation_bites() {
        let (root, id) = org();
        let pk = root.public();
        let temp = mint_role_cap(&root, &id, Role::Member, Some(1_000));
        assert!(authorize(&temp, &pk, &id, Permission::ResourceWrite, 999).is_ok());
        assert!(authorize(&temp, &pk, &id, Permission::ResourceWrite, 1_001).is_err());
    }
}
