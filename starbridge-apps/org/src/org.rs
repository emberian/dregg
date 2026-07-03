//! **The org's membership record + the receipted membership turns (the pure
//! core).**
//!
//! An [`Org`] is the public record of a team: its id (`org:<16hex>`, derived from
//! the org's own minting key), name, current owner, the org root public key
//! members' caps verify under, the [`Membership`] roster, pending [`Invite`]s, and
//! a monotone [`MembershipEvent`] log (the audit trail).
//!
//! [`OrgAuthority`] is the org cell's *secret* side — it holds the
//! [`RootKey`](dregg_auth::credential::RootKey) and is what mints members' role-
//! caps and authorizes/records the membership turns (invite / accept / remove /
//! change-role / transfer). Every mutating turn is **authorized by a role-cap**
//! ([`crate::cap::authorize`], the dregg-auth no-amplify verify), not by a trusted
//! role flag — an admin's cap simply does not satisfy an `org:delete` context, so
//! the delete is *refused*, not skipped by a check.
//!
//! This is the executor-seedable, unit-testable heart; [`crate`] wraps it as a
//! factory-born cell (the `member/role` slots + witnessed roster mirror) and an
//! `invoke()` service front door.

use serde::{Deserialize, Serialize};

use dregg_auth::credential::{Credential, PublicKey, RootKey};

use crate::cap;
use crate::resource::{OrgResource, ResourceKind};
use crate::role::{Permission, Role};

/// One member of an org: a cap-account subject + the role it holds.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Membership {
    /// The member's stable subject (`dregg:<16hex>`), a cap-account.
    pub subject: String,
    /// The member's role — which maps (via [`Role::permissions`]) to the role-cap
    /// the org minted them.
    pub role: Role,
}

/// A pending invitation: the org offers `subject` the `role`. Becomes a
/// [`Membership`] only when the named subject accepts
/// ([`OrgAuthority::accept_invite`]).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Invite {
    /// The org this invite is for (the scoping the acceptance is checked against).
    pub org: String,
    /// The invited subject.
    pub subject: String,
    /// The role being offered.
    pub role: Role,
    /// Who extended the invite (provenance).
    pub invited_by: String,
}

/// What a membership turn did — the log label set.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MembershipAction {
    /// The org was founded (its first owner installed).
    Founded,
    /// A subject was invited to a role (pending).
    Invited,
    /// A pending invite was accepted (the subject became a member).
    Accepted,
    /// A member was removed.
    Removed,
    /// A member's role was changed.
    RoleChanged,
    /// Ownership was transferred to another member.
    OwnershipTransferred,
    /// An org-owned resource was created.
    ResourceCreated,
}

impl MembershipAction {
    /// A stable small integer code — the value the org cell's `membership` events
    /// carry as their first field (so a light client naming the turn from the
    /// committed event does not need the string table).
    pub fn code(self) -> u64 {
        match self {
            MembershipAction::Founded => 1,
            MembershipAction::Invited => 2,
            MembershipAction::Accepted => 3,
            MembershipAction::Removed => 4,
            MembershipAction::RoleChanged => 5,
            MembershipAction::OwnershipTransferred => 6,
            MembershipAction::ResourceCreated => 7,
        }
    }
}

/// One sealed line of the membership audit trail. Today an in-record typed event
/// (`seq` orders the stream); the org cell mirrors the count into the `Monotonic`
/// [`SEQ_SLOT`](crate::SEQ_SLOT) and emits each as a real cell `Event`, so a light
/// client witnesses the membership history advancing monotonically.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MembershipEvent {
    /// Monotone sequence number (ordering / append-only check).
    pub seq: u64,
    /// What happened.
    pub action: MembershipAction,
    /// The subject that performed the turn (or the org owner, for `Founded`).
    pub actor: String,
    /// The subject the turn was about (the invitee/member/new-owner/resource id).
    pub subject: String,
    /// The role involved, if any.
    pub role: Option<Role>,
}

/// The public record of an organization. Serializable — a console renders it as
/// "the team", and it scopes the team's resources.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Org {
    /// The org id (`org:<16hex>`), derived from the org root key — the scoping key
    /// every org-owned resource records as its owner.
    pub id: String,
    /// A human name.
    pub name: String,
    /// The current owner's subject. Exactly one at a time; moves only via
    /// [`OrgAuthority::transfer_ownership`].
    pub owner: String,
    /// The org root public key (hex) members' role-caps verify under.
    pub root_pubkey: String,
    /// The roster.
    pub members: Vec<Membership>,
    /// Outstanding invites awaiting acceptance.
    pub pending: Vec<Invite>,
    /// The append-only membership audit trail.
    pub events: Vec<MembershipEvent>,
    /// The next event sequence number.
    pub(crate) next_seq: u64,
}

impl Org {
    /// Whether `subject` is a member of this org (the org-scoping read predicate).
    pub fn is_member(&self, subject: &str) -> bool {
        self.members.iter().any(|m| m.subject == subject)
    }

    /// The role `subject` holds here, if any.
    pub fn role_of(&self, subject: &str) -> Option<Role> {
        self.members
            .iter()
            .find(|m| m.subject == subject)
            .map(|m| m.role)
    }

    /// The number of members currently on the roster.
    pub fn member_count(&self) -> u64 {
        self.members.len() as u64
    }

    /// The current membership-event sequence height (the value the org cell's
    /// `Monotonic` [`SEQ_SLOT`](crate::SEQ_SLOT) mirrors).
    pub fn seq(&self) -> u64 {
        self.next_seq
    }

    /// The org root public key, parsed.
    pub fn root_public(&self) -> Result<PublicKey, OrgError> {
        PublicKey::from_hex(&self.root_pubkey).map_err(|e| OrgError::Malformed(e.to_string()))
    }

    /// Authorize a presented role-cap to perform `perm` over this org at `now` —
    /// the membership-turn gate. `Ok(())` iff the cap was minted by this org and
    /// its role grants `perm`; otherwise [`OrgError::NotAuthorized`] carrying the
    /// underlying cap refusal.
    pub fn authorize(
        &self,
        actor_cap: &Credential,
        perm: Permission,
        now: u64,
    ) -> Result<(), OrgError> {
        let pk = self.root_public()?;
        cap::authorize(actor_cap, &pk, &self.id, perm, now).map_err(|r| OrgError::NotAuthorized {
            perm,
            detail: r.to_string(),
        })
    }

    fn record(&mut self, action: MembershipAction, actor: &str, subject: &str, role: Option<Role>) {
        let seq = self.next_seq;
        self.next_seq += 1;
        self.events.push(MembershipEvent {
            seq,
            action,
            actor: actor.to_string(),
            subject: subject.to_string(),
            role,
        });
    }
}

/// The org cell's authority — it holds the secret minting [`RootKey`] and owns the
/// public [`Org`] record. The only thing that can mint members' role-caps and seal
/// membership turns.
pub struct OrgAuthority {
    root: RootKey,
    org: Org,
}

impl OrgAuthority {
    /// Found a new org with a fresh authority, installing `owner_subject` as the
    /// sole owner.
    pub fn found(name: impl Into<String>, owner_subject: impl Into<String>) -> OrgAuthority {
        Self::found_with_root(RootKey::generate(), name, owner_subject)
    }

    /// Found an org from a deterministic seed (tests / reproducible derivation).
    pub fn found_with_seed(
        seed: [u8; 32],
        name: impl Into<String>,
        owner_subject: impl Into<String>,
    ) -> OrgAuthority {
        Self::found_with_root(RootKey::from_seed(seed), name, owner_subject)
    }

    fn found_with_root(
        root: RootKey,
        name: impl Into<String>,
        owner_subject: impl Into<String>,
    ) -> OrgAuthority {
        let id = cap::org_id_of(&root.public());
        let owner = owner_subject.into();
        let mut org = Org {
            id,
            name: name.into(),
            owner: owner.clone(),
            root_pubkey: root.public().to_hex(),
            members: vec![Membership {
                subject: owner.clone(),
                role: Role::Owner,
            }],
            pending: Vec::new(),
            events: Vec::new(),
            next_seq: 0,
        };
        org.record(MembershipAction::Founded, &owner, &owner, Some(Role::Owner));
        OrgAuthority { root, org }
    }

    /// The public org record.
    pub fn org(&self) -> &Org {
        &self.org
    }

    /// Consume the authority, yielding the public record (e.g. to persist).
    pub fn into_org(self) -> Org {
        self.org
    }

    /// The org id.
    pub fn id(&self) -> &str {
        &self.org.id
    }

    /// The org root public key (what role-caps verify under).
    pub fn public(&self) -> PublicKey {
        self.root.public()
    }

    /// Mint a role-cap for `role` over this org (optionally expiring). The portable
    /// authority a member holds — issued on accept, re-issuable on demand (e.g. to
    /// hand the founding owner their owner-cap).
    pub fn mint_cap(&self, role: Role, until: Option<u64>) -> Credential {
        cap::mint_role_cap(&self.root, &self.org.id, role, until)
    }

    /// The founding owner's owner-cap.
    pub fn owner_cap(&self) -> Credential {
        self.mint_cap(Role::Owner, None)
    }

    /// **Invite** `invitee` to `role`. The actor must hold `MembersManage` (owner
    /// or admin). Owner cannot be granted by invite — ownership moves only via
    /// [`Self::transfer_ownership`]. Records a pending invite; no membership yet.
    pub fn invite(
        &mut self,
        actor_cap: &Credential,
        actor_subject: &str,
        invitee: impl Into<String>,
        role: Role,
        now: u64,
    ) -> Result<Invite, OrgError> {
        self.org
            .authorize(actor_cap, Permission::MembersManage, now)?;
        if role == Role::Owner {
            return Err(OrgError::CannotGrantOwnerRole);
        }
        let invitee = invitee.into();
        if self.org.is_member(&invitee) {
            return Err(OrgError::AlreadyMember(invitee));
        }
        let invite = Invite {
            org: self.org.id.clone(),
            subject: invitee.clone(),
            role,
            invited_by: actor_subject.to_string(),
        };
        // De-dup an outstanding invite for the same subject (latest role wins).
        self.org.pending.retain(|i| i.subject != invitee);
        self.org.pending.push(invite.clone());
        self.org.record(
            MembershipAction::Invited,
            actor_subject,
            &invitee,
            Some(role),
        );
        Ok(invite)
    }

    /// **Accept** a pending invite — the named subject joins, and the org mints +
    /// returns their role-cap. The acceptance is checked against the recorded
    /// invite (the subject and org must match), so a third party cannot redeem
    /// someone else's invite.
    pub fn accept_invite(
        &mut self,
        invite: &Invite,
        accepting_subject: &str,
    ) -> Result<Credential, OrgError> {
        if invite.org != self.org.id || invite.subject != accepting_subject {
            return Err(OrgError::InviteMismatch);
        }
        let pos = self
            .org
            .pending
            .iter()
            .position(|i| i.subject == accepting_subject && i.role == invite.role)
            .ok_or(OrgError::NoSuchInvite)?;
        let pending = self.org.pending.remove(pos);
        if self.org.is_member(accepting_subject) {
            return Err(OrgError::AlreadyMember(accepting_subject.to_string()));
        }
        self.org.members.push(Membership {
            subject: accepting_subject.to_string(),
            role: pending.role,
        });
        self.org.record(
            MembershipAction::Accepted,
            accepting_subject,
            accepting_subject,
            Some(pending.role),
        );
        Ok(self.mint_cap(pending.role, None))
    }

    /// **Remove** a member. The actor must hold `MembersManage`. The owner cannot
    /// be removed (transfer ownership first) — this keeps every org with exactly
    /// one owner.
    pub fn remove_member(
        &mut self,
        actor_cap: &Credential,
        actor_subject: &str,
        target: &str,
        now: u64,
    ) -> Result<(), OrgError> {
        self.org
            .authorize(actor_cap, Permission::MembersManage, now)?;
        if target == self.org.owner {
            return Err(OrgError::CannotRemoveOwner);
        }
        let before = self.org.members.len();
        self.org.members.retain(|m| m.subject != target);
        if self.org.members.len() == before {
            return Err(OrgError::NotAMember(target.to_string()));
        }
        self.org
            .record(MembershipAction::Removed, actor_subject, target, None);
        Ok(())
    }

    /// **Change** a member's role (re-issuing their role-cap). The actor must hold
    /// `MembersManage`; the owner role cannot be assigned this way (use transfer),
    /// and the owner's own role cannot be changed out from under them.
    pub fn change_role(
        &mut self,
        actor_cap: &Credential,
        actor_subject: &str,
        target: &str,
        new_role: Role,
        now: u64,
    ) -> Result<Credential, OrgError> {
        self.org
            .authorize(actor_cap, Permission::MembersManage, now)?;
        if new_role == Role::Owner {
            return Err(OrgError::CannotGrantOwnerRole);
        }
        if target == self.org.owner {
            return Err(OrgError::CannotRemoveOwner);
        }
        let m = self
            .org
            .members
            .iter_mut()
            .find(|m| m.subject == target)
            .ok_or_else(|| OrgError::NotAMember(target.to_string()))?;
        m.role = new_role;
        self.org.record(
            MembershipAction::RoleChanged,
            actor_subject,
            target,
            Some(new_role),
        );
        Ok(self.mint_cap(new_role, None))
    }

    /// **Transfer ownership** to an existing member. The actor must hold
    /// `OrgTransfer` (owner-only). The new owner becomes `Owner`; the old owner is
    /// demoted to `Admin`. Returns the new owner's owner-cap.
    pub fn transfer_ownership(
        &mut self,
        actor_cap: &Credential,
        actor_subject: &str,
        new_owner: &str,
        now: u64,
    ) -> Result<Credential, OrgError> {
        self.org
            .authorize(actor_cap, Permission::OrgTransfer, now)?;
        if !self.org.is_member(new_owner) {
            return Err(OrgError::NotAMember(new_owner.to_string()));
        }
        if new_owner == self.org.owner {
            return Err(OrgError::AlreadyOwner(new_owner.to_string()));
        }
        let old_owner = self.org.owner.clone();
        for m in &mut self.org.members {
            if m.subject == new_owner {
                m.role = Role::Owner;
            } else if m.subject == old_owner {
                m.role = Role::Admin;
            }
        }
        self.org.owner = new_owner.to_string();
        self.org.record(
            MembershipAction::OwnershipTransferred,
            actor_subject,
            new_owner,
            Some(Role::Owner),
        );
        Ok(self.mint_cap(Role::Owner, None))
    }

    /// **Delete the org** — the irreversible owner-only action. The actor must hold
    /// `OrgDelete`; an admin's cap is *refused*. Consumes the authority.
    pub fn delete_org(self, actor_cap: &Credential, now: u64) -> Result<(), OrgError> {
        self.org.authorize(actor_cap, Permission::OrgDelete, now)?;
        Ok(())
    }

    /// **Create an org-owned resource.** The actor must hold `ResourceCreate`. The
    /// resulting [`OrgResource`]'s owner is the *org* (not the member), recording
    /// the acting member as `created_by`. Resources belong to the team, exercised
    /// through role-caps.
    pub fn create_resource(
        &mut self,
        actor_cap: &Credential,
        actor_subject: &str,
        kind: ResourceKind,
        id: impl Into<String>,
        name: impl Into<String>,
        now: u64,
    ) -> Result<OrgResource, OrgError> {
        self.org
            .authorize(actor_cap, Permission::ResourceCreate, now)?;
        let id = id.into();
        let resource = OrgResource {
            org: self.org.id.clone(),
            kind,
            id: id.clone(),
            name: name.into(),
            created_by: actor_subject.to_string(),
        };
        self.org
            .record(MembershipAction::ResourceCreated, actor_subject, &id, None);
        Ok(resource)
    }
}

/// Why a membership turn was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OrgError {
    /// The actor's role-cap does not grant `perm` over this org (the cap-verify
    /// refused — the role-gating / org-scoping tooth biting). `detail` carries the
    /// underlying dregg-auth refusal.
    NotAuthorized { perm: Permission, detail: String },
    /// Owner cannot be granted by invite/change-role — use transfer.
    CannotGrantOwnerRole,
    /// The owner cannot be removed or demoted (transfer ownership first).
    CannotRemoveOwner,
    /// The subject is already a member.
    AlreadyMember(String),
    /// The subject is already the owner (a no-op transfer to self).
    AlreadyOwner(String),
    /// The subject is not a member.
    NotAMember(String),
    /// The acceptance did not match a recorded invite (wrong subject/org).
    InviteMismatch,
    /// No matching pending invite to accept.
    NoSuchInvite,
    /// The org root key (or a cap) was malformed.
    Malformed(String),
}

impl std::fmt::Display for OrgError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OrgError::NotAuthorized { perm, detail } => {
                write!(f, "not authorized for {} ({detail})", perm.as_str())
            }
            OrgError::CannotGrantOwnerRole => write!(
                f,
                "the owner role cannot be granted by invite/change-role — transfer ownership"
            ),
            OrgError::CannotRemoveOwner => {
                write!(f, "the owner cannot be removed or demoted (transfer first)")
            }
            OrgError::AlreadyMember(s) => write!(f, "{s} is already a member"),
            OrgError::AlreadyOwner(s) => write!(f, "{s} is already the owner"),
            OrgError::NotAMember(s) => write!(f, "{s} is not a member"),
            OrgError::InviteMismatch => {
                write!(f, "the acceptance does not match the recorded invite")
            }
            OrgError::NoSuchInvite => write!(f, "no matching pending invite"),
            OrgError::Malformed(e) => write!(f, "malformed: {e}"),
        }
    }
}

impl std::error::Error for OrgError {}

#[cfg(test)]
mod tests {
    use super::*;

    fn founded() -> OrgAuthority {
        OrgAuthority::found_with_seed([9u8; 32], "acme", "dregg:owner")
    }

    /// invite → accept mints a role-cap that reaches EXACTLY the role's permissions.
    #[test]
    fn invite_then_accept_mints_a_role_cap_reaching_exactly_the_role() {
        let mut auth = founded();
        let owner_cap = auth.owner_cap();
        let pk = auth.public();
        let id = auth.id().to_string();

        // Owner invites a new subject as a Member; the invitee accepts and gets
        // their role-cap.
        let invite = auth
            .invite(&owner_cap, "dregg:owner", "dregg:alice", Role::Member, 10)
            .expect("owner may invite");
        let alice_cap = auth
            .accept_invite(&invite, "dregg:alice")
            .expect("alice accepts her own invite");

        // The minted cap reaches EXACTLY Member's permissions and nothing else.
        for p in Role::Member.permissions() {
            assert!(
                cap::authorize(&alice_cap, &pk, &id, p, 20).is_ok(),
                "member cap must reach {p:?}"
            );
        }
        for p in [
            Permission::MembersManage,
            Permission::BillingPay,
            Permission::OrgDelete,
            Permission::OrgTransfer,
        ] {
            assert!(
                cap::authorize(&alice_cap, &pk, &id, p, 20).is_err(),
                "member cap must NOT reach {p:?}"
            );
        }
        assert_eq!(auth.org().role_of("dregg:alice"), Some(Role::Member));
    }

    /// A viewer's attempt to manage members is refused IN-BAND (the cap-verify
    /// refuses), and cannot be forged wider (no amplification).
    #[test]
    fn a_viewer_cannot_manage_members_and_cannot_forge_the_power() {
        let mut auth = founded();
        let owner_cap = auth.owner_cap();
        let invite = auth
            .invite(&owner_cap, "dregg:owner", "dregg:val", Role::Viewer, 5)
            .unwrap();
        let viewer_cap = auth.accept_invite(&invite, "dregg:val").unwrap();

        // The viewer tries to invite someone (needs MembersManage) → refused, and
        // the refusal is the cap-verify biting, surfaced as NotAuthorized.
        let refused = auth.invite(&viewer_cap, "dregg:val", "dregg:mallory", Role::Admin, 6);
        assert!(matches!(
            refused,
            Err(OrgError::NotAuthorized {
                perm: Permission::MembersManage,
                ..
            })
        ));
        // The roster is unchanged: no one was invited on a refusal.
        assert!(
            auth.org()
                .pending
                .iter()
                .all(|i| i.subject != "dregg:mallory")
        );
    }

    /// transfer-ownership moves the owner exactly once: owner→new_owner, old owner
    /// demoted to Admin, one OwnershipTransferred event, and only the owner may do
    /// it.
    #[test]
    fn transfer_ownership_moves_the_owner_once() {
        let mut auth = founded();
        let owner_cap = auth.owner_cap();
        // Bring a second member aboard.
        let inv = auth
            .invite(&owner_cap, "dregg:owner", "dregg:bob", Role::Admin, 1)
            .unwrap();
        auth.accept_invite(&inv, "dregg:bob").unwrap();

        // A non-owner (bob, an admin) CANNOT transfer — OrgTransfer is owner-only.
        let bob_cap = auth.mint_cap(Role::Admin, None);
        assert!(matches!(
            auth.transfer_ownership(&bob_cap, "dregg:bob", "dregg:bob", 2),
            Err(OrgError::NotAuthorized {
                perm: Permission::OrgTransfer,
                ..
            })
        ));
        assert_eq!(auth.org().owner, "dregg:owner");

        // The owner transfers to bob: the owner slot moves once.
        let transfers_before = auth
            .org()
            .events
            .iter()
            .filter(|e| e.action == MembershipAction::OwnershipTransferred)
            .count();
        auth.transfer_ownership(&owner_cap, "dregg:owner", "dregg:bob", 3)
            .expect("the owner may transfer to a member");
        assert_eq!(auth.org().owner, "dregg:bob", "owner slot moved");
        assert_eq!(auth.org().role_of("dregg:bob"), Some(Role::Owner));
        assert_eq!(
            auth.org().role_of("dregg:owner"),
            Some(Role::Admin),
            "the old owner is demoted to admin, not removed"
        );
        let transfers_after = auth
            .org()
            .events
            .iter()
            .filter(|e| e.action == MembershipAction::OwnershipTransferred)
            .count();
        assert_eq!(
            transfers_after - transfers_before,
            1,
            "exactly one ownership-transfer turn was recorded"
        );
    }

    #[test]
    fn a_stranger_cannot_redeem_someone_elses_invite() {
        let mut auth = founded();
        let owner_cap = auth.owner_cap();
        let inv = auth
            .invite(&owner_cap, "dregg:owner", "dregg:alice", Role::Member, 1)
            .unwrap();
        // A different subject cannot accept alice's invite.
        assert!(matches!(
            auth.accept_invite(&inv, "dregg:eve"),
            Err(OrgError::InviteMismatch)
        ));
        assert!(!auth.org().is_member("dregg:eve"));
    }
}
