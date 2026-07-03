//! # edge-mandate — the mandate as a SERVICE CELL on the `invoke()` front door.
//!
//! The third axis of a modern starbridge-app: the edge-identity mandate
//! re-expressed as a CELLS-AS-SERVICE-OBJECTS citizen (after the `execution-lease`
//! / `agent-orchestration` exemplars). A `service` module publishes a first-class,
//! typed [`InterfaceDescriptor`] and drives the mandate operations through the
//! [`dregg_app_framework::invoke`] front door — the userspace method-dispatch layer
//! that desugars a method call to the ordinary verified effects it names. There is
//! **no `Effect::Invoke`**, no kernel change, no new circuit rung: the kernel and
//! the light client keep seeing only the
//! [`SetField`](dregg_app_framework::Effect::SetField) /
//! [`EmitEvent`](dregg_app_framework::Effect::EmitEvent) effects they already
//! enforce and witness.
//!
//! ## The published interface (the mandate as typed methods)
//!
//! | method   | semantics    | auth        | args                | desugars to |
//! |----------|--------------|-------------|---------------------|-------------|
//! | `enrol`  | `Replayable` | `Signature` | `(account, budget)` | [`crate::enrol_effects`] (the WriteOnce identity/economics binds) |
//! | `spend`  | `Replayable` | `Signature` | `(spent, epoch)`    | [`crate::spend_effects`] (the metered draw, `AffineLe`-gated) |
//! | `revoke` | `Replayable` | `Signature` | `()`                | [`crate::revoke_effects`] (flip REVOKED, the kill switch) |
//! | `view`   | `Serviced`   | `None`      | `()`                | — (the OFE read seam: read the mandate state, never desugared) |
//!
//! `enrol`/`spend`/`revoke` are **replayable**: they desugar to a verified turn
//! whose post-state the executor checks against the mandate
//! [`CellProgram`](crate::mandate_cell_program) (the `AffineLe(spent ≤ budget)`
//! budget tooth, the `WriteOnce` identity/economics, the monotone meter/revocation,
//! the no-replay epoch). `view` is **serviced**: a state read rides the OFE
//! cross-cell-read, so `invoke()` refuses to desugar it and names the seam honestly
//! rather than faking a turn.
//!
//! ## The verified guarantee (the program bites)
//!
//! The cap-gate (`Signature` on every mutator) is enforced twice over: at the
//! `invoke()` front door (an unauthorized caller is refused before any turn is
//! built — anti-ghost) and again by the executor (the desugared turn carries a real
//! signature the kernel verifies). The budget bound is rollback-proof at the
//! verified commit path: an over-budget `spend` is an EXECUTOR REFUSAL on the
//! `AffineLe(spent ≤ budget)` gate, a replayed step is refused on
//! `StrictMonotonic(EPOCH)`, and a meter rollback on `Monotonic(SPENT)` — none of
//! them a userspace check.

use dregg_app_framework::{
    AppCipherclerk, Effect, FieldElement, InvokeAuthority, InvokeRefused, Turn, field_from_bytes,
    field_from_u64, invoke_with_descriptor,
};
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_types::CellId;

use crate::{CapMandate, enrol_effects, revoke_effects, spend_effects};

/// The `enrol` method — a `Replayable`, `Signature`-gated bind of the WriteOnce
/// identity / account / budget / caps-digest (from zero), spend=0, revoked=0,
/// epoch 0 -> 1.
pub const METHOD_ENROL: &str = "enrol";
/// The `spend` method — a `Replayable`, `Signature`-gated metered draw (advance the
/// spend meter, `AffineLe`-gated, + the no-replay epoch).
pub const METHOD_SPEND: &str = "spend";
/// The `revoke` method — a `Replayable`, `Signature`-gated flip of REVOKED (the kill
/// switch the authorized_keys adapter reads to go dark).
pub const METHOD_REVOKE: &str = "revoke";
/// The `view` method — a `Serviced` read of the mandate state (the OFE seam).
pub const METHOD_VIEW: &str = "view";

/// **The mandate's first-class typed interface** — the four methods it publishes,
/// with their auth and replayable-vs-serviced semantics.
pub fn interface_descriptor() -> InterfaceDescriptor {
    let mutator = |name: &str, args: u8| MethodSig {
        args_schema: ArgsSchema::Fixed(args),
        auth_required: AuthRequired::Signature,
        ..MethodSig::replayable(method_symbol(name))
    };
    InterfaceDescriptor::new(vec![
        // enrol(account, budget): seal the identity/economics + caps digest.
        mutator(METHOD_ENROL, 2),
        // spend(spent, epoch): a metered draw, AffineLe-gated.
        mutator(METHOD_SPEND, 2),
        // revoke(): flip REVOKED (the kill switch).
        mutator(METHOD_REVOKE, 0),
        // view(): a pure read — the named OFE seam, never desugared.
        MethodSig {
            args_schema: ArgsSchema::Fixed(0),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol(METHOD_VIEW))
        },
    ])
}

/// The cell program the mandate SERVICE face installs/assumes — the SAME canonical
/// [`mandate_cell_program`](crate::mandate_cell_program) the
/// [`FactoryDescriptor`](crate::mandate_factory_descriptor) bakes into every
/// factory-born mandate cell (the non-degrading invariant).
pub fn mandate_service_program() -> dregg_cell::program::CellProgram {
    crate::mandate_cell_program()
}

/// **A handle to a deployed mandate cell** — bundles the mandate cell with its
/// published interface, and builds method invocations through the `invoke()` front
/// door. Each builder returns a fully-signed [`Turn`]; a refusal (unknown method,
/// insufficient authority, a serviced seam) is surfaced as [`InvokeRefused`] before
/// any turn is built — fail-closed.
#[derive(Clone, Debug)]
pub struct MandateService {
    /// The mandate cell this handle drives.
    pub cell: CellId,
    /// The mandate's published typed interface.
    pub descriptor: InterfaceDescriptor,
}

impl MandateService {
    /// A handle to mandate cell `cell`, carrying the published [`interface_descriptor`].
    pub fn new(cell: CellId) -> Self {
        MandateService {
            cell,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `enrol`** — seal the attenuated `minted` mandate's identity /
    /// account / budget / caps-digest (the `WriteOnce` binds, admitted from zero on
    /// this first turn), spend=0, revoked=0, epoch 0 -> 1. Routes through the
    /// verified DFA, cap-gates on `Signature`, and desugars to
    /// [`enrol_effects`](crate::enrol_effects). (The enrolment-record heap strings
    /// are mirrored executor-side via [`crate::mirror_record`] after commit.)
    pub fn enrol(
        &self,
        cipherclerk: &AppCipherclerk,
        minted: &CapMandate,
        ssh_pubkey: &str,
        authority: InvokeAuthority,
    ) -> Result<Turn, MandateServiceError> {
        let effects = enrol_effects(self.cell, minted, ssh_pubkey);
        self.invoke(
            cipherclerk,
            METHOD_ENROL,
            vec![
                field_from_bytes(minted.subject.as_bytes()),
                field_from_u64(minted.budget),
            ],
            effects,
            authority,
        )
    }

    /// **Invoke `spend`** — a metered draw: advance the meter to `new_spent`
    /// (`Monotonic`, summed by the `AffineLe` budget gate) and the epoch to
    /// `new_epoch` (no replay), binding the `cost`. An over-budget draw is an
    /// executor refusal on `AffineLe(spent ≤ budget)`; a replay is refused on
    /// `StrictMonotonic(EPOCH)`.
    pub fn spend(
        &self,
        cipherclerk: &AppCipherclerk,
        new_spent: u64,
        cost: u64,
        new_epoch: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, MandateServiceError> {
        let effects = spend_effects(self.cell, new_spent, cost, new_epoch);
        self.invoke(
            cipherclerk,
            METHOD_SPEND,
            vec![field_from_u64(new_spent), field_from_u64(new_epoch)],
            effects,
            authority,
        )
    }

    /// **Invoke `revoke`** — flip `REVOKED` to `1` (`Monotonic`) and advance the
    /// epoch to `new_epoch`. After the turn commits, the authorized_keys adapter's
    /// line for this cell goes dark.
    pub fn revoke(
        &self,
        cipherclerk: &AppCipherclerk,
        new_epoch: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, MandateServiceError> {
        let effects = revoke_effects(self.cell, new_epoch);
        self.invoke(cipherclerk, METHOD_REVOKE, vec![], effects, authority)
    }

    /// **Attempt to invoke `view`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: a state read is answered by the OFE
    /// cross-cell read (the mandate's committed account / budget / spend / revoked
    /// state), not a replay desugar. This makes the seam legible (and testable).
    pub fn view(&self, cipherclerk: &AppCipherclerk) -> Result<Turn, MandateServiceError> {
        self.invoke(
            cipherclerk,
            METHOD_VIEW,
            vec![],
            vec![],
            InvokeAuthority::None,
        )
    }

    fn invoke(
        &self,
        cipherclerk: &AppCipherclerk,
        method: &str,
        args: Vec<FieldElement>,
        effects: Vec<Effect>,
        authority: InvokeAuthority,
    ) -> Result<Turn, MandateServiceError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            method,
            args,
            effects,
            authority,
        )
        .map_err(MandateServiceError::Refused)
    }
}

/// Why a [`MandateService`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MandateServiceError {
    /// The `invoke()` front door refused (unknown method, insufficient authority, or
    /// a serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for MandateServiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MandateServiceError::Refused(r) => write!(f, "invoke refused: {r}"),
        }
    }
}

impl std::error::Error for MandateServiceError {}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::AgentCipherclerk;

    fn minted() -> CapMandate {
        CapMandate::held(["fs", "http:api.github.com"], 500, "dga1_alice")
    }

    #[test]
    fn interface_publishes_four_typed_methods() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 4);
        assert!(iface.verify_id());
        for m in [METHOD_ENROL, METHOD_SPEND, METHOD_REVOKE] {
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
    fn the_service_program_is_the_canonical_mandate_program() {
        // The service face installs the SAME program the factory bakes — no
        // divergent program is invented (the non-degrading invariant).
        assert_eq!(mandate_service_program(), crate::mandate_cell_program());
    }

    #[test]
    fn enrol_routes_through_the_interface() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = MandateService::new(cclerk.cell_id());
        let turn = svc
            .enrol(
                &cclerk,
                &minted(),
                "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIAlIcEoZ1ENESf0Kk6zc8alICEforAlIcEkeyblob a@b",
                InvokeAuthority::Signature,
            )
            .expect("enrol routes through the interface");
        let action = &turn.call_forest.roots[0].action;
        assert_eq!(action.method, method_symbol(METHOD_ENROL));
        // enrol sets the seven scalar slots + emits the enrolled event.
        assert_eq!(action.effects.len(), 8);
    }

    #[test]
    fn unauthorized_spend_refused_at_the_front_door() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = MandateService::new(cclerk.cell_id());
        assert!(matches!(
            svc.spend(&cclerk, 100, 100, 2, InvokeAuthority::None),
            Err(MandateServiceError::Refused(
                InvokeRefused::Unauthorized { .. }
            ))
        ));
    }

    #[test]
    fn view_is_a_serviced_seam_never_desugared() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = MandateService::new(cclerk.cell_id());
        assert!(matches!(
            svc.view(&cclerk),
            Err(MandateServiceError::Refused(
                InvokeRefused::ServicedSeam { .. }
            ))
        ));
    }
}
