//! **Org-owned resources + org-scoping.**
//!
//! In the single-wallet world a resource's `owner` is the subject of the
//! cap-account that made it (a console scopes "my stuff" by `owner == subject`).
//! Orgs change exactly one thing: a resource created in an org context is
//! **org-owned** — its owner is the *org id*, not the acting member's subject. The
//! member acted *under their role-cap*; the org holds the resource. So a teammate
//! who later joins sees it, a member who leaves stops seeing it, and ownership is
//! the team's, not one person's.
//!
//! This lifts the console `Owned` shape (a resource is in a subject's view iff it
//! is owned by something the subject can see) one level: an org-owned resource is
//! in a subject's view iff the subject is a **member** of the owning org. That
//! membership check is the **org-scoping tooth** for the read side
//! ([`OrgResource::visible_to`]); the cap-verify is the tooth for the write side
//! ([`crate::cap::authorize`]). A non-member sees nothing of the org.

use serde::{Deserialize, Serialize};

use crate::org::Org;

/// The kind of an org-owned resource — the surfaces a console renders
/// (sites/servers/agents/domains/storage), now ownable by a team.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ResourceKind {
    Site,
    Server,
    Agent,
    Domain,
    Bucket,
}

/// A resource owned by an org. Its `owner` is the org id (`org:<16hex>`), and it
/// records which member created it (the audit trail) — but the *authority* over it
/// is the org's, exercised through members' role-caps.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrgResource {
    /// The owning org's id — the scoping key. NOT a member subject.
    pub org: String,
    /// What kind of resource this is.
    pub kind: ResourceKind,
    /// A stable id within the org.
    pub id: String,
    /// A human name.
    pub name: String,
    /// The member subject that created it (provenance; not the owner).
    pub created_by: String,
}

impl OrgResource {
    /// The org id that owns this resource. The mirror of a console's
    /// `Owned::owner`, but the owner is the org, not a person.
    pub fn owner(&self) -> &str {
        &self.org
    }

    /// The **org-scoping read tooth**: this resource is in `subject`'s view iff
    /// `subject` is a member of the owning org. A non-member — or a member of a
    /// *different* org — sees nothing.
    pub fn visible_to(&self, org: &Org, subject: &str) -> bool {
        org.id == self.org && org.is_member(subject)
    }
}

/// Filter a slice of org-owned resources to those `subject` may see — exactly the
/// ones owned by `org` when `subject` is a member, else none. The org-level twin
/// of a console's `scope`: the "team's stuff" view.
pub fn scope_for_member<'a>(
    resources: &'a [OrgResource],
    org: &Org,
    subject: &str,
) -> Vec<&'a OrgResource> {
    if !org.is_member(subject) {
        return Vec::new();
    }
    resources.iter().filter(|r| r.org == org.id).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::OrgAuthority;

    #[test]
    fn an_org_resource_is_visible_only_to_members_of_its_org() {
        let auth = OrgAuthority::found_with_seed([7u8; 32], "acme", "dregg:owner");
        let org = auth.org();
        let res = OrgResource {
            org: org.id.clone(),
            kind: ResourceKind::Site,
            id: "site-1".into(),
            name: "marketing".into(),
            created_by: "dregg:owner".into(),
        };
        assert!(res.visible_to(org, "dregg:owner"));
        assert!(!res.visible_to(org, "dregg:stranger"));
        assert_eq!(scope_for_member(&[res], org, "dregg:owner").len(), 1);
    }
}
