//! **Roles and permissions — the legible face of the cap lattice.**
//!
//! A real cloud's org has *roles* (owner / admin / member / billing / viewer).
//! dregg does not invent a second authorization mechanism for them: a role is a
//! named **set of [`Permission`]s**, and a permission is one allowed action over
//! the org's resources / membership / billing. The whole point of this crate is
//! that a role then compiles to an **attenuated capability** over the org-owner's
//! authority ([`crate::cap`]): the role-cap admits exactly the role's permissions
//! and — by the dregg-auth no-amplify property (`Credential::attenuate` can only
//! ever *narrow*; `metatheory/Dregg2/Authority/Caveat.lean` `attenuate_subset`) —
//! nothing more. So "viewer is read-only" and "admin can't delete the org" are not
//! enforced by an `if role == …` check a bug could skip; they are the cap-verify
//! *refusing* a context whose `perm` is outside the role's grant.
//!
//! The verification [`Context`](dregg_auth::credential::Context) a role-cap is
//! checked against binds two attributes:
//! * `org` — the org id the action targets (the **org-scoping** tooth: a cap
//! minted for org A never satisfies a context naming org B), and
//! * `perm` — the permission the action requires (the **role-gating** tooth).

use serde::{Deserialize, Serialize};

/// The context attribute key carrying the org id an action targets.
pub const ORG_KEY: &str = "org";
/// The context attribute key carrying the permission an action requires.
pub const PERM_KEY: &str = "perm";

/// One allowed action over an org's resources / membership / billing. A
/// permission is the atom a [`Role`] is a set of, and the value bound to
/// [`PERM_KEY`] when an action is authorized.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Permission {
    /// Read an org-owned resource (list/inspect). The floor every member has.
    ResourceRead,
    /// Mutate an existing org-owned resource (publish, configure, restart).
    ResourceWrite,
    /// Create a new org-owned resource (a site/server/agent/bucket).
    ResourceCreate,
    /// Destroy an org-owned resource.
    ResourceDelete,
    /// Manage membership: invite, change a member's role, remove a member.
    MembersManage,
    /// See invoices + billing state.
    BillingView,
    /// Pay invoices / change the payment method.
    BillingPay,
    /// Delete the entire org (the irreversible, owner-only action).
    OrgDelete,
    /// Transfer ownership of the org to another member (owner-only).
    OrgTransfer,
}

impl Permission {
    /// Every permission, owner-complete. The org-owner's grant is exactly this
    /// set — every role is one of its subsets.
    pub const ALL: [Permission; 9] = [
        Permission::ResourceRead,
        Permission::ResourceWrite,
        Permission::ResourceCreate,
        Permission::ResourceDelete,
        Permission::MembersManage,
        Permission::BillingView,
        Permission::BillingPay,
        Permission::OrgDelete,
        Permission::OrgTransfer,
    ];

    /// The stable string bound to [`PERM_KEY`] in the verification context. This
    /// IS the cap's matched value — colon-namespaced for legibility in an
    /// `explain()` dump (`requires any of (attribute \`perm\` = \`resource:read\`)`).
    pub fn as_str(self) -> &'static str {
        match self {
            Permission::ResourceRead => "resource:read",
            Permission::ResourceWrite => "resource:write",
            Permission::ResourceCreate => "resource:create",
            Permission::ResourceDelete => "resource:delete",
            Permission::MembersManage => "members:manage",
            Permission::BillingView => "billing:view",
            Permission::BillingPay => "billing:pay",
            Permission::OrgDelete => "org:delete",
            Permission::OrgTransfer => "org:transfer",
        }
    }

    /// A stable small integer code for a permission — the value the org cell's
    /// witnessed roster mirror packs (so a light client reading the committed
    /// heap can name the permission without the string table). `1`-based so a
    /// zeroed heap key reads as "absent", never as a real permission.
    pub fn code(self) -> u64 {
        match self {
            Permission::ResourceRead => 1,
            Permission::ResourceWrite => 2,
            Permission::ResourceCreate => 3,
            Permission::ResourceDelete => 4,
            Permission::MembersManage => 5,
            Permission::BillingView => 6,
            Permission::BillingPay => 7,
            Permission::OrgDelete => 8,
            Permission::OrgTransfer => 9,
        }
    }
}

/// An org member's role. Ordered most-privileged → least so a `>=` answers "is at
/// least as privileged as". Each role maps (via [`Role::permissions`]) to the
/// permission subset its role-cap is attenuated to.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Role {
    /// Everything, including the irreversible org:delete and ownership transfer +
    /// billing. Exactly one member is the owner at a time.
    Owner,
    /// Manage resources AND membership, and see billing — but NOT delete the org,
    /// transfer ownership, or pay/change billing. The org's day-to-day operator.
    Admin,
    /// Create + manage resources (the builder). No member management, no billing,
    /// no org-level actions.
    Member,
    /// See + pay invoices. NO resource access at all — the finance seat.
    Billing,
    /// Read-only across the org's resources. The auditor / stakeholder seat.
    Viewer,
}

impl Role {
    /// The wire/display label.
    pub fn as_str(self) -> &'static str {
        match self {
            Role::Owner => "owner",
            Role::Admin => "admin",
            Role::Member => "member",
            Role::Billing => "billing",
            Role::Viewer => "viewer",
        }
    }

    /// A stable small integer code for a role — the value the org cell stores in
    /// its witnessed roster mirror (`ROLE_COLL`) and its `OWNER`/`RoleChanged`
    /// events. `1`-based so a zeroed heap key reads as "not a member", never as a
    /// real role.
    pub fn code(self) -> u64 {
        match self {
            Role::Owner => 1,
            Role::Admin => 2,
            Role::Member => 3,
            Role::Billing => 4,
            Role::Viewer => 5,
        }
    }

    /// The inverse of [`Role::code`] — decode a role from its stored code (a
    /// light client reading the committed roster mirror). `None` for `0`
    /// (absent / not a member) or an unknown code.
    pub fn from_code(code: u64) -> Option<Role> {
        match code {
            1 => Some(Role::Owner),
            2 => Some(Role::Admin),
            3 => Some(Role::Member),
            4 => Some(Role::Billing),
            5 => Some(Role::Viewer),
            _ => None,
        }
    }

    /// The permission set this role grants — the subset of [`Permission::ALL`]
    /// the role-cap is attenuated to. This is the single table that makes roles
    /// legible; everything else derives from it.
    pub fn permissions(self) -> Vec<Permission> {
        use Permission::*;
        match self {
            Role::Owner => Permission::ALL.to_vec(),
            Role::Admin => vec![
                ResourceRead,
                ResourceWrite,
                ResourceCreate,
                ResourceDelete,
                MembersManage,
                BillingView,
            ],
            Role::Member => vec![ResourceRead, ResourceWrite, ResourceCreate, ResourceDelete],
            Role::Billing => vec![BillingView, BillingPay],
            Role::Viewer => vec![ResourceRead],
        }
    }

    /// Whether a member in this role is *granted* `perm` (the table lookup, the
    /// trusted-side mirror of what the role-cap proves cryptographically). Used
    /// for display + as the spec the cap-verify is checked to agree with.
    pub fn grants(self, perm: Permission) -> bool {
        self.permissions().contains(&perm)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn role_lattice_is_a_subset_tower_for_resources() {
        // viewer ⊆ member ⊆ admin ⊆ owner on the resource-read axis; and the
        // owner-only / billing-only powers sit where they should.
        assert!(Role::Viewer.grants(Permission::ResourceRead));
        assert!(!Role::Viewer.grants(Permission::ResourceWrite));
        assert!(Role::Member.grants(Permission::ResourceWrite));
        assert!(!Role::Member.grants(Permission::MembersManage));
        assert!(Role::Admin.grants(Permission::MembersManage));
        assert!(!Role::Admin.grants(Permission::OrgDelete));
        assert!(Role::Owner.grants(Permission::OrgDelete));
        // billing is orthogonal: it pays but cannot touch resources.
        assert!(Role::Billing.grants(Permission::BillingPay));
        assert!(!Role::Billing.grants(Permission::ResourceRead));
        // owner is the full grant.
        for p in Permission::ALL {
            assert!(Role::Owner.grants(p), "owner must grant {p:?}");
        }
    }

    #[test]
    fn role_codes_round_trip_and_reserve_zero_for_absent() {
        for r in [
            Role::Owner,
            Role::Admin,
            Role::Member,
            Role::Billing,
            Role::Viewer,
        ] {
            assert_ne!(r.code(), 0, "0 is reserved for 'not a member'");
            assert_eq!(Role::from_code(r.code()), Some(r));
        }
        assert_eq!(Role::from_code(0), None);
        assert_eq!(Role::from_code(99), None);
    }
}
