//! # guard — the abuse-governance vocabulary as a SERVICE CELL on the `invoke()`
//! front door (AX3).
//!
//! The per-subject account re-expressed as a CELLS-AS-SERVICE-OBJECTS citizen (after
//! the `tool-access-delegation` / `bounty-board` / `kvstore` exemplars). This module
//! publishes a first-class, typed [`InterfaceDescriptor`] and drives the account
//! vocabulary through the [`dregg_app_framework::invoke`] front door — the userspace
//! method-dispatch layer that desugars a method call to the ordinary verified effects
//! it names. There is **no `Effect::Invoke`**, no kernel change, no new circuit rung:
//! the kernel and the light client keep seeing only the
//! [`SetField`](dregg_app_framework::Effect::SetField) /
//! [`EmitEvent`](dregg_app_framework::Effect::EmitEvent) effects they already enforce
//! and witness.
//!
//! ## The published interface (the abuse-governance vocabulary as typed methods)
//!
//! | method        | semantics                 | auth        | tier       | desugars to |
//! |---------------|---------------------------|-------------|------------|-------------|
//! | `constitute`  | [`Semantics::Replayable`] | `Signature` | subject    | `SetField(SUBJECT, CEILING, GOVERNANCE_ROOT, CONSUMED=0)` |
//! | `consume`     | [`Semantics::Replayable`] | `Signature` | subject    | `SetField(CONSUMED := c+1)` (`c+1 <= ceiling`) |
//! | `set_standing`| [`Semantics::Replayable`] | `None`/root | GOVERNANCE  | `SetField(STANDING := s)` (executor-gated on `SenderAuthorized`) |
//! | `view`        | [`Semantics::Serviced`]   | `None`      | subject    | — (the named OFE seam: a pure read, no turn) |
//!
//! ## Why `set_standing` is published here but built elsewhere
//!
//! The interface NAMES the whole vocabulary (so the Service Explorer resolves
//! `set_standing`'s true GOVERNANCE tier), but the [`GuardService`] handle — a
//! SUBJECT's self-service handle — deliberately builds only its own subset
//! (`constitute` / `consume` / `view`). A subject's front door must NOT expose the
//! takedown (that would be a confused deputy). `set_standing` is the GOVERNANCE turn:
//! it carries a Merkle-membership witness the `SenderAuthorized(PublicRoot)` clause
//! binds, which the front-door desugar cannot thread, so governance moves standing
//! through the dedicated witnessed builder [`crate::build_set_standing_action`] (the
//! `Action` path, re-enforced by the seeded [`crate::guard_program`]).
//!
//! ## Non-degrading: the SAME ceiling the FactoryDescriptor bakes
//!
//! The service installs the IDENTICAL [`crate::guard_born_cell_program`] — the
//! [`crate::guard_state_constraints`] the [`crate::guard_factory_descriptor`] bakes
//! into every factory-born account cell (an `Always` program, so it re-enforces
//! method-agnostically on every invoke()-desugared turn): `WriteOnce` ceiling /
//! governance-root / subject, and `Monotonic(consumed) + FieldLteField(consumed <=
//! ceiling)` on every `consume`.

use dregg_app_framework::{
    AppCipherclerk, Effect, EmbeddedExecutor, FieldElement, InterfaceRegistry, InvokeAuthority,
    InvokeRefused, field_from_u64, invoke_with_descriptor,
};
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_turn::Turn;
use dregg_types::CellId;

use crate::{
    CEILING_SLOT, CONSUMED_SLOT, GOVERNANCE_ROOT_SLOT, SUBJECT_SLOT, governance_root,
    guard_born_cell_program, guard_program, subject_id_field,
};

// =============================================================================
// Method names — the card's button vocabulary.
// =============================================================================

/// The `constitute` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// bind the account's `SUBJECT` / `CEILING` / `GOVERNANCE_ROOT` (all `WriteOnce`) and
/// the meter `CONSUMED → 0`.
pub const METHOD_CONSTITUTE: &str = "constitute";
/// The `consume` method — a [`Semantics::Replayable`], `Signature`-gated mutator: the
/// subject meters one quota unit (`CONSUMED := c+1`, re-enforced `c+1 <= ceiling`).
pub const METHOD_CONSUME: &str = "consume";
/// The `set_standing` method — a [`Semantics::Replayable`], `None`/root GOVERNANCE
/// mutator: move the subject's standing. Published so the interface names the
/// vocabulary; built through the witnessed [`crate::build_set_standing_action`] (see
/// the module doc for why it is not a subject front-door builder).
pub const METHOD_SET_STANDING: &str = "set_standing";
/// The `view` method — a [`Semantics::Serviced`] read (the named OFE seam): read the
/// account's standing / budget / ceiling. Never desugared.
pub const METHOD_VIEW: &str = "view";

// =============================================================================
// The published, typed interface.
// =============================================================================

/// **The account's first-class typed interface** — the four methods it publishes,
/// with their auth and replayable-vs-serviced semantics. The three subject-tier
/// mutators are `Signature`-gated; `set_standing` is `None`/root (the GOVERNANCE
/// tier the executor additionally gates on `SenderAuthorized` membership); `view` is
/// `Serviced`.
pub fn interface_descriptor() -> InterfaceDescriptor {
    let subject_mutator = |name: &str, args: u8| MethodSig {
        args_schema: ArgsSchema::Fixed(args),
        auth_required: AuthRequired::Signature,
        ..MethodSig::replayable(method_symbol(name))
    };
    InterfaceDescriptor::new(vec![
        // constitute(subject, ceiling): bind the account.
        subject_mutator(METHOD_CONSTITUTE, 2),
        // consume(): meter one quota unit (ceiling-bounded).
        subject_mutator(METHOD_CONSUME, 0),
        // set_standing(standing): the GOVERNANCE takedown/suspension — root tier.
        MethodSig {
            args_schema: ArgsSchema::Fixed(1),
            auth_required: AuthRequired::None,
            ..MethodSig::replayable(method_symbol(METHOD_SET_STANDING))
        },
        // view(): a pure read — the named OFE seam, never desugared.
        MethodSig {
            args_schema: ArgsSchema::Fixed(0),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol(METHOD_VIEW))
        },
    ])
}

/// Register the account's [`interface_descriptor`] for `cell` in a userspace
/// [`InterfaceRegistry`] — the resolution path the Service Explorer consults before
/// falling back to derive-from-program.
pub fn register_interface(registry: &mut InterfaceRegistry, cell: CellId) {
    registry.register(cell, interface_descriptor());
}

// =============================================================================
// Seeding.
// =============================================================================

/// **Seed a configured account cell** so the service's `consume` has live state + the
/// caveats bite: install the full [`guard_program`] (`Cases`, with the governance
/// standing gate) on the executor's agent cell, then bind the configuration directly
/// into the embedded ledger — `CEILING` / `GOVERNANCE_ROOT` / `SUBJECT` (`WriteOnce`,
/// frozen after) and `CONSUMED = 0`, the firing signer as the sole governance
/// authority. After seeding, the account is configured with the meter at 0 — a real
/// `(old, new)` baseline against which `consume` advances the counter up to `ceiling`.
pub fn seed_configured_account(
    executor: &EmbeddedExecutor,
    cipherclerk: &AppCipherclerk,
    subject: &str,
    ceiling: u64,
) {
    let cell = executor.cell_id();
    executor.install_program(cell, guard_program());
    let gov_root = governance_root(cipherclerk);
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&cell) {
            c.state
                .set_field(CEILING_SLOT as usize, field_from_u64(ceiling));
            c.state
                .set_field(SUBJECT_SLOT as usize, subject_id_field(subject));
            c.state.set_field(GOVERNANCE_ROOT_SLOT as usize, gov_root);
            c.state.set_field(CONSUMED_SLOT as usize, field_from_u64(0));
        }
    });
}

/// **Install just the account program** (the flat, method-agnostic
/// [`guard_born_cell_program`]) on the executor's agent cell — a born-empty account
/// the service drives `constitute` against (the `WriteOnce` ceiling/root/subject
/// admit-from-zero on the constitute turn). For tests that exercise `constitute`
/// through the front door.
pub fn seed_empty_account(executor: &EmbeddedExecutor) {
    executor.install_program(executor.cell_id(), guard_born_cell_program());
}

// =============================================================================
// The service handle — building invocations through invoke().
// =============================================================================

/// **A handle to a deployed subject-account cell** — bundles the account cell with
/// its published interface, and builds a SUBJECT's method invocations through the
/// `invoke()` front door. (Governance moves standing through the witnessed
/// [`crate::build_set_standing_action`], not this subject handle.)
///
/// Each builder returns a fully-signed [`Turn`]; submit it through an executor to
/// commit. A refusal at the front door (unknown method, insufficient authority, a
/// serviced seam) is surfaced as an [`InvokeRefused`] before any turn is built —
/// fail-closed.
#[derive(Clone, Debug)]
pub struct GuardService {
    /// The account cell this handle drives.
    pub cell: CellId,
    /// The account's published typed interface.
    pub descriptor: InterfaceDescriptor,
}

impl GuardService {
    /// A handle to the account cell `cell`, carrying the account's published
    /// [`interface_descriptor`].
    pub fn new(cell: CellId) -> Self {
        GuardService {
            cell,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `constitute(subject, ceiling)`** — bind `SUBJECT`, `CEILING`,
    /// `GOVERNANCE_ROOT` (all `WriteOnce`, admitted from zero on this first turn) and
    /// the meter `CONSUMED → 0`. The `governance_root` value authorizes the governance
    /// authority the later witnessed `set_standing` proves membership in.
    pub fn constitute(
        &self,
        cipherclerk: &AppCipherclerk,
        subject: &str,
        ceiling: u64,
        governance_root: FieldElement,
        authority: InvokeAuthority,
    ) -> Result<Turn, GuardServiceError> {
        if subject.is_empty() {
            return Err(GuardServiceError::EmptyField);
        }
        let effects = vec![
            self.set(SUBJECT_SLOT, subject_id_field(subject)),
            self.set(CEILING_SLOT, field_from_u64(ceiling)),
            self.set(GOVERNANCE_ROOT_SLOT, governance_root),
            self.set(CONSUMED_SLOT, field_from_u64(0)),
        ];
        self.invoke(
            cipherclerk,
            METHOD_CONSTITUTE,
            vec![subject_id_field(subject), field_from_u64(ceiling)],
            effects,
            authority,
        )
    }

    /// **Invoke `consume()`** — the subject meters one quota unit: advance `CONSUMED`
    /// from `prev_consumed` to `prev_consumed + 1`. The executor's
    /// `FieldLteField(consumed <= ceiling)` refuses the consume that would overrun the
    /// budget (the in-band `402`/`429`), and `Monotonic(consumed)` refuses a meter
    /// rollback.
    pub fn consume(
        &self,
        cipherclerk: &AppCipherclerk,
        prev_consumed: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, GuardServiceError> {
        let new_count = prev_consumed + 1;
        let effects = vec![self.set(CONSUMED_SLOT, field_from_u64(new_count))];
        self.invoke(cipherclerk, METHOD_CONSUME, vec![], effects, authority)
    }

    /// **Attempt to invoke `view()`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: `view` is a [`Semantics::Serviced`] read,
    /// answered by the OFE cross-cell-read (the account's committed standing /
    /// budget), not a replay desugar. To actually READ the account, read the committed
    /// state at its slots ([`CONSUMED_SLOT`](crate::CONSUMED_SLOT), …).
    pub fn view(&self, cipherclerk: &AppCipherclerk) -> Result<Turn, GuardServiceError> {
        self.invoke(
            cipherclerk,
            METHOD_VIEW,
            vec![],
            vec![],
            InvokeAuthority::None,
        )
    }

    /// A `SetField` effect on this account cell.
    fn set(&self, index: u8, value: FieldElement) -> Effect {
        Effect::SetField {
            cell: self.cell,
            index: index as usize,
            value,
        }
    }

    /// Route → cap-gate → desugar → sign, through the `invoke()` front door against
    /// this account's published descriptor.
    fn invoke(
        &self,
        cipherclerk: &AppCipherclerk,
        method: &str,
        args: Vec<FieldElement>,
        effects: Vec<Effect>,
        authority: InvokeAuthority,
    ) -> Result<Turn, GuardServiceError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            method,
            args,
            effects,
            authority,
        )
        .map_err(GuardServiceError::Refused)
    }
}

/// Why a [`GuardService`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GuardServiceError {
    /// A required text field (the subject id) was empty.
    EmptyField,
    /// The `invoke()` front door refused (unknown method, insufficient authority, or a
    /// serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for GuardServiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GuardServiceError::EmptyField => write!(f, "a required text field must be non-empty"),
            GuardServiceError::Refused(r) => write!(f, "invoke refused: {r}"),
        }
    }
}

impl std::error::Error for GuardServiceError {}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::AgentCipherclerk;

    fn test_cipherclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32])
    }

    #[test]
    fn interface_publishes_four_typed_methods() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 4);
        assert!(iface.verify_id());

        for m in [METHOD_CONSTITUTE, METHOD_CONSUME] {
            let sig = iface.method(&method_symbol(m)).unwrap();
            assert_eq!(sig.semantics, Semantics::Replayable, "{m} is replayable");
            assert_eq!(
                sig.auth_required,
                AuthRequired::Signature,
                "{m} is sig-gated"
            );
        }
        // set_standing is published at the GOVERNANCE tier (root).
        let ss = iface.method(&method_symbol(METHOD_SET_STANDING)).unwrap();
        assert_eq!(
            ss.auth_required,
            AuthRequired::None,
            "set_standing is root-tier"
        );
        // view is the serviced seam.
        let view = iface.method(&method_symbol(METHOD_VIEW)).unwrap();
        assert_eq!(view.semantics, Semantics::Serviced);
        assert_eq!(view.auth_required, AuthRequired::None);
    }

    #[test]
    fn empty_subject_rejected_before_any_turn() {
        let cclerk = test_cipherclerk();
        let svc = GuardService::new(cclerk.cell_id());
        assert!(matches!(
            svc.constitute(
                &cclerk,
                "",
                8,
                crate::governance_root(&cclerk),
                InvokeAuthority::Signature
            ),
            Err(GuardServiceError::EmptyField)
        ));
    }

    #[test]
    fn unauthorized_consume_refused_at_the_front_door() {
        let cclerk = test_cipherclerk();
        let svc = GuardService::new(cclerk.cell_id());
        // `consume` needs `Signature`; a `None` holder is refused before any turn.
        assert!(matches!(
            svc.consume(&cclerk, 0, InvokeAuthority::None),
            Err(GuardServiceError::Refused(
                InvokeRefused::Unauthorized { .. }
            ))
        ));
    }

    #[test]
    fn view_is_a_serviced_seam_never_desugared() {
        let cclerk = test_cipherclerk();
        let svc = GuardService::new(cclerk.cell_id());
        assert!(matches!(
            svc.view(&cclerk),
            Err(GuardServiceError::Refused(
                InvokeRefused::ServicedSeam { .. }
            ))
        ));
    }

    #[test]
    fn unknown_method_does_not_route() {
        let iface = interface_descriptor();
        assert!(
            iface.method(&method_symbol("drain")).is_none(),
            "an unknown method is not a member of the interface"
        );
    }
}
