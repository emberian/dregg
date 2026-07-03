//! # org — the membership lifecycle as a SERVICE CELL on the `invoke()` front door.
//!
//! The org re-expressed as a CELLS-AS-SERVICE-OBJECTS citizen (after the
//! `execution-lease` / `tool-access-delegation` exemplars). This module publishes a
//! first-class, typed [`InterfaceDescriptor`] and drives the membership vocabulary
//! through the [`dregg_app_framework::invoke`] front door — the userspace
//! method-dispatch layer that desugars a method call to the ordinary verified
//! effects it names. There is **no `Effect::Invoke`**, no kernel change, no new
//! circuit rung: the kernel and the light client keep seeing only the
//! [`SetField`](dregg_app_framework::Effect::SetField) /
//! [`EmitEvent`](dregg_app_framework::Effect::EmitEvent) effects they already
//! enforce and witness. The one extra fact — that an invoked method is a member of
//! the cell's interface — is decided by the SAME verified DFA router the protocol
//! already uses.
//!
//! ## The published interface (the membership lifecycle as typed methods)
//!
//! | method | semantics | auth | args | desugars to |
//! |---------------|--------------|-------------|-------------------------|-------------|
//! | `invite` | `Replayable` | `Signature` | `(subject, role)` | `SetField(SEQ := s+1)` + `org-membership` event |
//! | `accept` | `Replayable` | `Signature` | `(subject, role)` | `SetField(SEQ, MEMBER_COUNT)` + event (mints the role-cap out-of-band) |
//! | `remove` | `Replayable` | `Signature` | `(subject)` | `SetField(SEQ, MEMBER_COUNT)` + event |
//! | `change_role` | `Replayable` | `Signature` | `(subject, role)` | `SetField(SEQ)` + event |
//! | `transfer` | `Replayable` | `Signature` | `(new_owner)` | `SetField(OWNER, SEQ)` + `org-owner-transferred` event |
//! | `view` | `Serviced` | `None` | `()` | — (the named OFE seam: a pure read, no turn) |
//!
//! The mutators are **replayable**: they desugar to a verified turn whose post-state
//! the executor checks against the org [`org_cell_program`](crate::org_cell_program)
//! (the `Monotonic(SEQ)` append-only-audit tooth + the `WriteOnce` identity/name
//! bite). `view` is **serviced**: a state read rides the OFE cross-cell-read, so
//! `invoke()` refuses to desugar it and names the seam honestly.
//!
//! ## Where the ROLE ENFORCEMENT lives
//!
//! The front door gates the COARSE cap-graph tier (`Signature`). The FINE,
//! unforgeable role-gate is the dregg-auth role-cap ([`crate::cap::authorize`]),
//! checked by the authority before it seals a membership turn (an admin's cap does
//! not satisfy an `org:delete`/`org:transfer` context — refused, not skipped). This
//! service builds the ledger turn; [`crate::OrgAuthority`] is the authoritative
//! record-keeper that mints the accepted member's attenuated role-cap.

use dregg_app_framework::{
    AppCipherclerk, FieldElement, InvokeAuthority, InvokeRefused, Turn, field_from_u64,
    invoke_with_descriptor,
};
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_types::CellId;

use crate::{MembershipAction, Role, membership_effects, subject_tag, transfer_effects};

/// The `invite` method — an ADMIN offers `subject` a `role` (pending).
pub const METHOD_INVITE: &str = "invite";
/// The `accept` method — the invitee joins (the org mints their role-cap).
pub const METHOD_ACCEPT: &str = "accept";
/// The `remove` method — an ADMIN removes a member.
pub const METHOD_REMOVE: &str = "remove";
/// The `change_role` method — an ADMIN re-roles a member (re-issuing their cap).
pub const METHOD_CHANGE_ROLE: &str = "change_role";
/// The `transfer` method — the OWNER transfers ownership to a member.
pub const METHOD_TRANSFER: &str = "transfer";
/// The `view` method — a `Serviced` read (the named OFE seam): read the team.
pub const METHOD_VIEW: &str = "view";

/// **The org's first-class typed interface** — the six methods it publishes, with
/// their auth and replayable-vs-serviced semantics.
///
/// The richer-than-derived descriptor: the five mutators are `Signature`-gated and
/// `view` is marked `Serviced`. An app registers THIS in an
/// [`InterfaceRegistry`](dregg_app_framework::InterfaceRegistry) so the Service
/// Explorer resolves the real auth + seam shape.
pub fn interface_descriptor() -> InterfaceDescriptor {
    let mutator = |name: &str, args: u8| MethodSig {
        args_schema: ArgsSchema::Fixed(args),
        auth_required: AuthRequired::Signature,
        ..MethodSig::replayable(method_symbol(name))
    };
    InterfaceDescriptor::new(vec![
        // invite(subject, role): offer a subject a role.
        mutator(METHOD_INVITE, 2),
        // accept(subject, role): the invitee joins.
        mutator(METHOD_ACCEPT, 2),
        // remove(subject): remove a member.
        mutator(METHOD_REMOVE, 1),
        // change_role(subject, role): re-role a member.
        mutator(METHOD_CHANGE_ROLE, 2),
        // transfer(new_owner): move ownership to a member.
        mutator(METHOD_TRANSFER, 1),
        // view(): a pure read — the named OFE seam, never desugared.
        MethodSig {
            args_schema: ArgsSchema::Fixed(0),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol(METHOD_VIEW))
        },
    ])
}

/// Register the org's [`interface_descriptor`] for `cell` in a userspace
/// [`InterfaceRegistry`](dregg_app_framework::InterfaceRegistry) — the resolution
/// path the Service Explorer consults before falling back to derive-from-program.
pub fn register_interface(registry: &mut dregg_app_framework::InterfaceRegistry, cell: CellId) {
    registry.register(cell, interface_descriptor());
}

/// **A handle to a deployed org cell** — bundles the org cell with its published
/// interface, and builds method invocations through the `invoke()` front door.
///
/// Each builder returns a fully-signed [`Turn`] (the build half); submit it through
/// an executor to actually commit. A refusal at the front door (unknown method,
/// insufficient authority, a serviced seam) is surfaced as an [`InvokeRefused`]
/// before any turn is built — fail-closed.
#[derive(Clone, Debug)]
pub struct OrgService {
    /// The org cell this handle drives.
    pub cell: CellId,
    /// The org's published typed interface.
    pub descriptor: InterfaceDescriptor,
}

impl OrgService {
    /// A handle to the org cell `cell`, carrying the org's published
    /// [`interface_descriptor`].
    pub fn new(cell: CellId) -> Self {
        OrgService {
            cell,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `invite(subject, role)`** — an ADMIN offers `subject` a `role`. The
    /// turn advances the audit height (`SEQ := seq + 1`) and emits the
    /// `org-membership` event; no roster change yet (the invite is pending).
    /// `seq` / `member_count` are the org cell's live values.
    pub fn invite(
        &self,
        cipherclerk: &AppCipherclerk,
        subject: &str,
        role: Role,
        seq: u64,
        member_count: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, OrgServiceError> {
        if subject.is_empty() {
            return Err(OrgServiceError::EmptyField);
        }
        if role == Role::Owner {
            return Err(OrgServiceError::CannotGrantOwner);
        }
        let effects = membership_effects(
            self.cell,
            MembershipAction::Invited,
            subject,
            Some(role),
            seq + 1,
            member_count,
        );
        self.invoke(
            cipherclerk,
            METHOD_INVITE,
            vec![subject_tag(subject), field_from_u64(role.code())],
            effects,
            authority,
        )
    }

    /// **Invoke `accept(subject, role)`** — the invitee joins: the roster grows and
    /// the audit height advances. (The authoritative
    /// [`OrgAuthority::accept_invite`](crate::OrgAuthority::accept_invite) mints the
    /// member their attenuated role-cap.) `member_count` is the POST count (with the
    /// new member added).
    pub fn accept(
        &self,
        cipherclerk: &AppCipherclerk,
        subject: &str,
        role: Role,
        seq: u64,
        member_count: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, OrgServiceError> {
        if subject.is_empty() {
            return Err(OrgServiceError::EmptyField);
        }
        let effects = membership_effects(
            self.cell,
            MembershipAction::Accepted,
            subject,
            Some(role),
            seq + 1,
            member_count,
        );
        self.invoke(
            cipherclerk,
            METHOD_ACCEPT,
            vec![subject_tag(subject), field_from_u64(role.code())],
            effects,
            authority,
        )
    }

    /// **Invoke `remove(subject)`** — an ADMIN removes a member: the roster shrinks
    /// and the audit height advances. `member_count` is the POST count.
    pub fn remove(
        &self,
        cipherclerk: &AppCipherclerk,
        subject: &str,
        seq: u64,
        member_count: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, OrgServiceError> {
        if subject.is_empty() {
            return Err(OrgServiceError::EmptyField);
        }
        let effects = membership_effects(
            self.cell,
            MembershipAction::Removed,
            subject,
            None,
            seq + 1,
            member_count,
        );
        self.invoke(
            cipherclerk,
            METHOD_REMOVE,
            vec![subject_tag(subject)],
            effects,
            authority,
        )
    }

    /// **Invoke `change_role(subject, role)`** — an ADMIN re-roles a member (the org
    /// re-issues their attenuated role-cap out-of-band). The roster size is
    /// unchanged; the audit height advances.
    pub fn change_role(
        &self,
        cipherclerk: &AppCipherclerk,
        subject: &str,
        role: Role,
        seq: u64,
        member_count: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, OrgServiceError> {
        if subject.is_empty() {
            return Err(OrgServiceError::EmptyField);
        }
        if role == Role::Owner {
            return Err(OrgServiceError::CannotGrantOwner);
        }
        let effects = membership_effects(
            self.cell,
            MembershipAction::RoleChanged,
            subject,
            Some(role),
            seq + 1,
            member_count,
        );
        self.invoke(
            cipherclerk,
            METHOD_CHANGE_ROLE,
            vec![subject_tag(subject), field_from_u64(role.code())],
            effects,
            authority,
        )
    }

    /// **Invoke `transfer(new_owner)`** — the OWNER transfers ownership to a member:
    /// `OWNER_SLOT` moves and the audit height advances. The executor re-enforces
    /// `Monotonic(SEQ)`. (The owner-only `OrgTransfer` role-cap tooth is the fine
    /// gate the authority checks.)
    pub fn transfer(
        &self,
        cipherclerk: &AppCipherclerk,
        new_owner: &str,
        seq: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, OrgServiceError> {
        if new_owner.is_empty() {
            return Err(OrgServiceError::EmptyField);
        }
        let effects = transfer_effects(self.cell, new_owner, seq + 1);
        self.invoke(
            cipherclerk,
            METHOD_TRANSFER,
            vec![subject_tag(new_owner)],
            effects,
            authority,
        )
    }

    /// **Attempt to invoke `view()`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: `view` is a [`Semantics::Serviced`] read,
    /// answered by the OFE cross-cell-read (the committed roster mirror), not a
    /// replay desugar. This makes the seam legible (and testable). To actually READ
    /// the team, read the committed roster ([`MEMBER_COLL`](crate::MEMBER_COLL), …).
    pub fn view(&self, cipherclerk: &AppCipherclerk) -> Result<Turn, OrgServiceError> {
        self.invoke(
            cipherclerk,
            METHOD_VIEW,
            vec![],
            vec![],
            InvokeAuthority::None,
        )
    }

    /// Route → cap-gate → desugar → sign, through the `invoke()` front door against
    /// this org's published descriptor.
    fn invoke(
        &self,
        cipherclerk: &AppCipherclerk,
        method: &str,
        args: Vec<FieldElement>,
        effects: Vec<dregg_app_framework::Effect>,
        authority: InvokeAuthority,
    ) -> Result<Turn, OrgServiceError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            method,
            args,
            effects,
            authority,
        )
        .map_err(OrgServiceError::Refused)
    }
}

/// Why an [`OrgService`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OrgServiceError {
    /// A required subject field was empty.
    EmptyField,
    /// The owner role cannot be granted by invite/change-role — use `transfer`.
    CannotGrantOwner,
    /// The `invoke()` front door refused (unknown method, insufficient authority,
    /// or a serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for OrgServiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OrgServiceError::EmptyField => write!(f, "a required subject field must be non-empty"),
            OrgServiceError::CannotGrantOwner => write!(
                f,
                "the owner role cannot be granted by invite/change_role — use transfer"
            ),
            OrgServiceError::Refused(r) => write!(f, "invoke refused: {r}"),
        }
    }
}

impl std::error::Error for OrgServiceError {}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::AgentCipherclerk;

    fn test_cipherclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32])
    }

    #[test]
    fn interface_publishes_six_typed_methods() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 6);
        assert!(iface.verify_id());
        for m in [
            METHOD_INVITE,
            METHOD_ACCEPT,
            METHOD_REMOVE,
            METHOD_CHANGE_ROLE,
            METHOD_TRANSFER,
        ] {
            let sig = iface.method(&method_symbol(m)).unwrap();
            assert_eq!(sig.semantics, Semantics::Replayable, "{m} is replayable");
            assert_eq!(
                sig.auth_required,
                AuthRequired::Signature,
                "{m} is sig-gated"
            );
        }
        let view = iface.method(&method_symbol(METHOD_VIEW)).unwrap();
        assert_eq!(view.semantics, Semantics::Serviced);
        assert_eq!(view.auth_required, AuthRequired::None);
    }

    #[test]
    fn invite_desugars_to_a_seq_advance_and_membership_event() {
        let cclerk = test_cipherclerk();
        let svc = OrgService::new(cclerk.cell_id());
        let turn = svc
            .invite(
                &cclerk,
                "dregg:alice",
                Role::Member,
                3,
                1,
                InvokeAuthority::Signature,
            )
            .expect("invite routes through the interface");
        let action = &turn.call_forest.roots[0].action;
        assert_eq!(action.method, method_symbol(METHOD_INVITE));
        // SetField(SEQ := 4), SetField(MEMBER_COUNT), EmitEvent.
        assert_eq!(action.effects.len(), 3);
    }

    #[test]
    fn transfer_desugars_to_owner_move_and_seq_bump() {
        let cclerk = test_cipherclerk();
        let svc = OrgService::new(cclerk.cell_id());
        let turn = svc
            .transfer(&cclerk, "dregg:bob", 5, InvokeAuthority::Signature)
            .expect("transfer routes");
        let action = &turn.call_forest.roots[0].action;
        assert_eq!(action.method, method_symbol(METHOD_TRANSFER));
        assert_eq!(action.effects.len(), 3);
    }

    #[test]
    fn owner_role_cannot_be_granted_through_invite_or_change_role() {
        let cclerk = test_cipherclerk();
        let svc = OrgService::new(cclerk.cell_id());
        assert!(matches!(
            svc.invite(
                &cclerk,
                "dregg:x",
                Role::Owner,
                0,
                1,
                InvokeAuthority::Signature
            ),
            Err(OrgServiceError::CannotGrantOwner)
        ));
        assert!(matches!(
            svc.change_role(
                &cclerk,
                "dregg:x",
                Role::Owner,
                0,
                1,
                InvokeAuthority::Signature
            ),
            Err(OrgServiceError::CannotGrantOwner)
        ));
    }

    #[test]
    fn unauthorized_invite_refused_at_the_front_door() {
        let cclerk = test_cipherclerk();
        let svc = OrgService::new(cclerk.cell_id());
        // `invite` needs `Signature`; a `None` holder is refused before any turn.
        assert!(matches!(
            svc.invite(
                &cclerk,
                "dregg:alice",
                Role::Member,
                0,
                1,
                InvokeAuthority::None
            ),
            Err(OrgServiceError::Refused(InvokeRefused::Unauthorized { .. }))
        ));
    }

    #[test]
    fn empty_subject_rejected_before_any_turn() {
        let cclerk = test_cipherclerk();
        let svc = OrgService::new(cclerk.cell_id());
        assert!(matches!(
            svc.invite(&cclerk, "", Role::Member, 0, 1, InvokeAuthority::Signature),
            Err(OrgServiceError::EmptyField)
        ));
    }

    #[test]
    fn view_is_a_serviced_seam_never_desugared() {
        let cclerk = test_cipherclerk();
        let svc = OrgService::new(cclerk.cell_id());
        assert!(matches!(
            svc.view(&cclerk),
            Err(OrgServiceError::Refused(InvokeRefused::ServicedSeam { .. }))
        ));
    }
}
