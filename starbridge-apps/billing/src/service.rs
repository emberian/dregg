//! # billing — the billing account as a SERVICE CELL on the `invoke()` front door.
//!
//! The third axis of a modern starbridge-app: the billing account re-expressed as a
//! CELLS-AS-SERVICE-OBJECTS citizen. A `service` module publishes a first-class, typed
//! [`InterfaceDescriptor`] and drives the billing operations through the
//! [`dregg_app_framework::invoke`] front door — the userspace method-dispatch layer that
//! desugars a method call to the ordinary verified effects it names. There is **no
//! `Effect::Invoke`**, no kernel change, no new circuit rung: the kernel and the light
//! client keep seeing only the [`SetField`](dregg_app_framework::Effect::SetField) /
//! [`Transfer`](dregg_app_framework::Effect::Transfer) /
//! [`EmitEvent`](dregg_app_framework::Effect::EmitEvent) effects they already enforce.
//!
//! ## The published interface (billing as typed methods)
//!
//! | method     | semantics    | auth        | args                         | desugars to |
//! |------------|--------------|-------------|------------------------------|-------------|
//! | `charge`   | `Replayable` | `Signature` | `(new_spent, amount, provider)` | the cap-guarded [`crate::charge_effects`] — the executor's `FieldLteField(spent ≤ cap)` refuses an over-cap charge (the 402) |
//! | `seal`     | `Replayable` | `Signature` | `(body_hash, total)`         | the [`crate::seal_invoice_effects`] binding the invoice `body_hash` into the cell |
//! | `estimate` | `Serviced`   | `None`      | `()`                         | — (the pure-fn read seam; never desugared) |
//! | `status`   | `Serviced`   | `None`      | `()`                         | — (the OFE read seam: read the account state, never desugared) |
//!
//! `charge`/`seal` are **replayable**: they desugar to a verified turn whose post-state the
//! executor checks against the billing [`CellProgram`](crate::billing_cell_program) (the
//! `FieldLteField(spent ≤ cap)` ceiling + the `Monotonic`/`WriteOnce` economics bite).
//! `estimate`/`status` are **serviced**: a pure estimate / a state read rides the OFE seam,
//! so `invoke()` refuses to desugar them and names the seam honestly rather than faking a
//! turn.

use dregg_app_framework::{
    AppCipherclerk, Effect, FieldElement, InvokeAuthority, InvokeRefused, Turn, field_from_u64,
    invoke_with_descriptor,
};
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_types::CellId;

use crate::{Invoice, cell_tag, charge_effects, seal_invoice_effects};

/// The `charge` method — a `Replayable`, `Signature`-gated cap-guarded charge (a
/// `SetField` on the accrued-spend slot + a conserving `Transfer` to the provider).
pub const METHOD_CHARGE: &str = "charge";
/// The `seal` method — a `Replayable`, `Signature`-gated invoice seal (bind the invoice
/// `body_hash` into the cell — the invoice's own turn-receipt seal).
pub const METHOD_SEAL: &str = "seal";
/// The `estimate` method — a `Serviced` pure-fn read of the cost of a declaration.
pub const METHOD_ESTIMATE: &str = "estimate";
/// The `status` method — a `Serviced` read of the account state (the OFE seam).
pub const METHOD_STATUS: &str = "status";

/// **The billing account's first-class typed interface** — the four methods it publishes,
/// with their auth and replayable-vs-serviced semantics.
pub fn interface_descriptor() -> InterfaceDescriptor {
    let mutator = |name: &str, args: u8| MethodSig {
        args_schema: ArgsSchema::Fixed(args),
        auth_required: AuthRequired::Signature,
        ..MethodSig::replayable(method_symbol(name))
    };
    let read = |name: &str| MethodSig {
        args_schema: ArgsSchema::Fixed(0),
        auth_required: AuthRequired::None,
        semantics: Semantics::Serviced,
        ..MethodSig::replayable(method_symbol(name))
    };
    InterfaceDescriptor::new(vec![
        // charge(new_spent, amount, provider): the cap-guarded charge.
        mutator(METHOD_CHARGE, 3),
        // seal(body_hash, total): seal the invoice as a turn receipt.
        mutator(METHOD_SEAL, 2),
        // estimate(): a pure read — never desugared.
        read(METHOD_ESTIMATE),
        // status(): a pure read — the named OFE seam, never desugared.
        read(METHOD_STATUS),
    ])
}

/// **A handle to a deployed billing-account cell** — bundles the cell with its published
/// interface, and builds method invocations through the `invoke()` front door. Each builder
/// returns a fully-signed [`Turn`]; a refusal (unknown method, insufficient authority, a
/// serviced seam) is surfaced as [`InvokeRefused`] before any turn is built — fail-closed.
#[derive(Clone, Debug)]
pub struct BillingService {
    /// The billing-account cell this handle drives.
    pub cell: CellId,
    /// The account's published typed interface.
    pub descriptor: InterfaceDescriptor,
}

impl BillingService {
    /// A handle to billing cell `cell`, carrying the published [`interface_descriptor`].
    pub fn new(cell: CellId) -> Self {
        BillingService {
            cell,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `charge`** — advance the accrued spend to `new_spent` and move `amount` to
    /// the provider. Re-enforced by the executor's `FieldLteField(spent ≤ cap)`: an over-cap
    /// charge is a REAL refusal on the desugared turn (the 402, in-band).
    pub fn charge(
        &self,
        cipherclerk: &AppCipherclerk,
        provider: CellId,
        new_spent: i64,
        amount: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, BillingServiceError> {
        let effects = charge_effects(self.cell, provider, new_spent, amount);
        self.invoke(
            cipherclerk,
            METHOD_CHARGE,
            vec![
                field_from_u64(new_spent.max(0) as u64),
                field_from_u64(amount),
                cell_tag(provider),
            ],
            effects,
            authority,
        )
    }

    /// **Invoke `seal`** — bind `invoice`'s canonical `body_hash` into the account cell (the
    /// invoice's own turn-receipt seal).
    pub fn seal(
        &self,
        cipherclerk: &AppCipherclerk,
        invoice: &Invoice,
        authority: InvokeAuthority,
    ) -> Result<Turn, BillingServiceError> {
        let body_hash = invoice.body_hash();
        let effects = seal_invoice_effects(self.cell, body_hash, invoice.total_units);
        self.invoke(
            cipherclerk,
            METHOD_SEAL,
            vec![body_hash, field_from_u64(invoice.total_units.max(0) as u64)],
            effects,
            authority,
        )
    }

    /// **Attempt to invoke `estimate`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: a cost estimate is a pure function
    /// ([`crate::estimate`]), answered directly, not a replay desugar. This makes the seam
    /// legible.
    pub fn estimate(&self, cipherclerk: &AppCipherclerk) -> Result<Turn, BillingServiceError> {
        self.invoke(
            cipherclerk,
            METHOD_ESTIMATE,
            vec![],
            vec![],
            InvokeAuthority::None,
        )
    }

    /// **Attempt to invoke `status`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: a state read is answered by the OFE cross-cell read,
    /// not a replay desugar.
    pub fn status(&self, cipherclerk: &AppCipherclerk) -> Result<Turn, BillingServiceError> {
        self.invoke(
            cipherclerk,
            METHOD_STATUS,
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
    ) -> Result<Turn, BillingServiceError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            method,
            args,
            effects,
            authority,
        )
        .map_err(BillingServiceError::Refused)
    }
}

/// Why a [`BillingService`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BillingServiceError {
    /// The `invoke()` front door refused (unknown method, insufficient authority, or a
    /// serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for BillingServiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BillingServiceError::Refused(r) => write!(f, "invoke refused: {r}"),
        }
    }
}

impl std::error::Error for BillingServiceError {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BillingPeriod;
    use dregg_app_framework::{AgentCipherclerk, Effect};

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    #[test]
    fn interface_publishes_four_typed_methods() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 4);
        assert!(iface.verify_id());
        for m in [METHOD_CHARGE, METHOD_SEAL] {
            let sig = iface.method(&method_symbol(m)).unwrap();
            assert_eq!(sig.semantics, Semantics::Replayable, "{m} is replayable");
            assert_eq!(
                sig.auth_required,
                AuthRequired::Signature,
                "{m} is sig-gated"
            );
        }
        for m in [METHOD_ESTIMATE, METHOD_STATUS] {
            let sig = iface.method(&method_symbol(m)).unwrap();
            assert_eq!(sig.semantics, Semantics::Serviced, "{m} is serviced");
        }
    }

    #[test]
    fn charge_desugars_to_a_setfield_and_a_conserving_transfer() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = BillingService::new(cclerk.cell_id());
        let turn = svc
            .charge(&cclerk, cid(2), 60, 60, InvokeAuthority::Signature)
            .expect("charge routes through the interface");
        let action = &turn.call_forest.roots[0].action;
        assert_eq!(action.method, method_symbol(METHOD_CHARGE));
        // SetField(spent) + Transfer(→provider) + EmitEvent.
        assert!(matches!(action.effects[1], Effect::Transfer { amount, .. } if amount == 60));
    }

    #[test]
    fn seal_desugars_to_binding_the_invoice_digest() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = BillingService::new(cclerk.cell_id());
        let inv = Invoice::assemble(
            "alice",
            BillingPeriod::new("2026-06", 0, 1000),
            "CREDIT",
            &[],
            "t0",
        );
        let turn = svc
            .seal(&cclerk, &inv, InvokeAuthority::Signature)
            .expect("seal routes through the interface");
        let action = &turn.call_forest.roots[0].action;
        assert_eq!(action.method, method_symbol(METHOD_SEAL));
        assert!(matches!(
            action.effects[0],
            Effect::SetField { value, .. } if value == inv.body_hash()
        ));
    }

    #[test]
    fn unauthorized_charge_refused_at_the_front_door() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = BillingService::new(cclerk.cell_id());
        assert!(matches!(
            svc.charge(&cclerk, cid(2), 60, 60, InvokeAuthority::None),
            Err(BillingServiceError::Refused(
                InvokeRefused::Unauthorized { .. }
            ))
        ));
    }

    #[test]
    fn estimate_and_status_are_serviced_seams_never_desugared() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = BillingService::new(cclerk.cell_id());
        assert!(matches!(
            svc.estimate(&cclerk),
            Err(BillingServiceError::Refused(
                InvokeRefused::ServicedSeam { .. }
            ))
        ));
        assert!(matches!(
            svc.status(&cclerk),
            Err(BillingServiceError::Refused(
                InvokeRefused::ServicedSeam { .. }
            ))
        ));
    }
}
