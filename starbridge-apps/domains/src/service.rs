//! # domains — the binding lifecycle as a SERVICE CELL on the `invoke()` front door.
//!
//! The custom-domain binding re-expressed as a CELLS-AS-SERVICE-OBJECTS citizen (the
//! sibling of `starbridge-nameservice`'s registry face). This module publishes a
//! first-class, typed [`InterfaceDescriptor`] and drives the `register` / `bind` /
//! `verify` / `resolve` vocabulary through the [`dregg_app_framework::invoke`] front
//! door — the userspace method-dispatch layer that desugars a method call to the
//! ordinary verified effects it names. There is **no `Effect::Invoke`**, no kernel
//! change, no new circuit rung: the kernel and the light client keep seeing only the
//! [`SetField`](dregg_app_framework::Effect::SetField) /
//! [`EmitEvent`](dregg_app_framework::Effect::EmitEvent) effects they already enforce
//! and witness.
//!
//! ## The published interface
//!
//! | method     | semantics    | auth        | args              | desugars to |
//! |------------|--------------|-------------|-------------------|-------------|
//! | `register` | `Replayable` | `Signature` | `(domain, owner)` | seal `DOMAIN` + `OWNER` + `domain-registered` |
//! | `bind`     | `Replayable` | `Signature` | `(site, nonce)`   | point `SITE` + seal `CHALLENGE_NONCE` + `domain-bound` |
//! | `verify`   | `Replayable` | `Signature` | `(verified_seq)`  | flip `VERIFICATION_STATE` + advance `VERIFIED_SEQ` + `domain-verified` |
//! | `resolve`  | `Serviced`   | `None`      | `()`              | — (the named OFE seam: read the verified `site`, no turn) |
//!
//! The mutators are **replayable**: they desugar to a verified turn whose post-state
//! the executor checks against the [`domain_cell_program`](crate::domain_cell_program)
//! (`WriteOnce(DOMAIN/OWNER/CHALLENGE_NONCE)` + `Monotonic(VERIFICATION_STATE/VERIFIED_SEQ)`).
//! `resolve` is **serviced**: reading the verified `site` rides the OFE cross-cell-read
//! (the committed `SITE` field), so `invoke()` refuses to desugar it and names the seam
//! honestly rather than faking a write.
//!
//! ## Where the BIND-CAP ENFORCEMENT lives
//!
//! The front door gates the COARSE cap-graph tier (`Signature`). The FINE, unforgeable
//! bind-cap gate is the `dregg-auth` credential ([`crate::cap::verify_bind_authority`]),
//! checked by the control plane ([`crate::DomainRegistry::bind`]) before it issues a
//! challenge — a forged / wrong-domain credential is refused, not skipped. This service
//! builds the ledger turn; the registry is the authoritative routing-plane record.

use dregg_app_framework::{
    AppCipherclerk, Effect, FieldElement, InvokeAuthority, InvokeRefused, Turn, field_from_u64,
    invoke_with_descriptor,
};
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_types::CellId;

use crate::{
    METHOD_BIND, METHOD_REGISTER, METHOD_RESOLVE, METHOD_VERIFY, bind_effects, domain_tag,
    nonce_tag, owner_tag, register_effects, site_tag, verify_effects,
};

/// **The binding's first-class typed interface** — the four methods it publishes,
/// with their auth and replayable-vs-serviced semantics. The richer-than-derived
/// descriptor: the three mutators are `Signature`-gated and `resolve` is `Serviced`.
pub fn interface_descriptor() -> InterfaceDescriptor {
    let mutator = |name: &str, args: u8| MethodSig {
        args_schema: ArgsSchema::Fixed(args),
        auth_required: AuthRequired::Signature,
        ..MethodSig::replayable(method_symbol(name))
    };
    InterfaceDescriptor::new(vec![
        // register(domain, owner): establish + seal the binding cell.
        mutator(METHOD_REGISTER, 2),
        // bind(site, nonce): point at a site + seal the DNS challenge.
        mutator(METHOD_BIND, 2),
        // verify(verified_seq): flip to verified once DNS proves control.
        mutator(METHOD_VERIFY, 1),
        // resolve(): a pure read — the named OFE seam, never desugared.
        MethodSig {
            args_schema: ArgsSchema::Fixed(0),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol(METHOD_RESOLVE))
        },
    ])
}

/// Register the binding's [`interface_descriptor`] for `cell` in a userspace
/// [`InterfaceRegistry`](dregg_app_framework::InterfaceRegistry) — the resolution path
/// the Service Explorer consults before falling back to derive-from-program.
pub fn register_interface(registry: &mut dregg_app_framework::InterfaceRegistry, cell: CellId) {
    registry.register(cell, interface_descriptor());
}

/// **A handle to a deployed domain-binding cell** — bundles the cell with its
/// published interface, and builds method invocations through the `invoke()` front
/// door. Each builder returns a fully-signed [`Turn`] (the build half); submit it
/// through an executor to commit. A refusal at the front door (unknown method,
/// insufficient authority, a serviced seam) is surfaced as an [`InvokeRefused`] before
/// any turn is built — fail-closed.
#[derive(Clone, Debug)]
pub struct DomainService {
    /// The domain cell this handle drives.
    pub cell: CellId,
    /// The binding's published typed interface.
    pub descriptor: InterfaceDescriptor,
}

impl DomainService {
    /// A handle to the domain cell `cell`, carrying the published [`interface_descriptor`].
    pub fn new(cell: CellId) -> Self {
        DomainService {
            cell,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `register(domain, owner)`** — establish + seal the binding cell
    /// (`DOMAIN` + `OWNER`, `WriteOnce`). Signature-gated.
    pub fn register(
        &self,
        cipherclerk: &AppCipherclerk,
        domain: &str,
        owner: &str,
        authority: InvokeAuthority,
    ) -> Result<Turn, DomainServiceError> {
        if domain.is_empty() || owner.is_empty() {
            return Err(DomainServiceError::EmptyField);
        }
        self.invoke(
            cipherclerk,
            METHOD_REGISTER,
            vec![domain_tag(domain), owner_tag(owner)],
            register_effects(self.cell, domain, owner),
            authority,
        )
    }

    /// **Invoke `bind(site, nonce)`** — point the domain at `site` and seal the DNS
    /// challenge `nonce` (`WriteOnce(CHALLENGE_NONCE)`). Signature-gated. (The FINE
    /// bind-cap gate is [`crate::cap::verify_bind_authority`], checked by the registry
    /// before it issues the nonce.)
    pub fn bind(
        &self,
        cipherclerk: &AppCipherclerk,
        site: &str,
        nonce: &str,
        authority: InvokeAuthority,
    ) -> Result<Turn, DomainServiceError> {
        if site.is_empty() || nonce.is_empty() {
            return Err(DomainServiceError::EmptyField);
        }
        self.invoke(
            cipherclerk,
            METHOD_BIND,
            vec![site_tag(site), nonce_tag(nonce)],
            bind_effects(self.cell, site, nonce),
            authority,
        )
    }

    /// **Invoke `verify(verified_seq)`** — flip `VERIFICATION_STATE` to verified and
    /// advance `VERIFIED_SEQ`. The executor re-enforces the `Monotonic` teeth (a
    /// re-verify / rewind is refused). Signature-gated.
    pub fn verify(
        &self,
        cipherclerk: &AppCipherclerk,
        verified_seq: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, DomainServiceError> {
        self.invoke(
            cipherclerk,
            METHOD_VERIFY,
            vec![field_from_u64(verified_seq)],
            verify_effects(self.cell, verified_seq),
            authority,
        )
    }

    /// **Attempt to invoke `resolve()`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: `resolve` is a [`Semantics::Serviced`] read,
    /// answered by the OFE cross-cell-read (the committed `SITE` field), not a replay
    /// desugar. This makes the seam legible (and testable). To actually READ the
    /// target, read the committed state at [`SITE_SLOT`](crate::SITE_SLOT) — only
    /// meaningful once `VERIFICATION_STATE` is verified.
    pub fn resolve(&self, cipherclerk: &AppCipherclerk) -> Result<Turn, DomainServiceError> {
        self.invoke(
            cipherclerk,
            METHOD_RESOLVE,
            vec![],
            vec![],
            InvokeAuthority::None,
        )
    }

    /// Route → cap-gate → desugar → sign, through the `invoke()` front door against
    /// this binding's published descriptor.
    fn invoke(
        &self,
        cipherclerk: &AppCipherclerk,
        method: &str,
        args: Vec<FieldElement>,
        effects: Vec<Effect>,
        authority: InvokeAuthority,
    ) -> Result<Turn, DomainServiceError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            method,
            args,
            effects,
            authority,
        )
        .map_err(DomainServiceError::Refused)
    }
}

/// Why a [`DomainService`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DomainServiceError {
    /// A required field (domain / owner / site / nonce) was empty.
    EmptyField,
    /// The `invoke()` front door refused (unknown method, insufficient authority, or a
    /// serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for DomainServiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DomainServiceError::EmptyField => write!(f, "a required field must be non-empty"),
            DomainServiceError::Refused(r) => write!(f, "invoke refused: {r}"),
        }
    }
}

impl std::error::Error for DomainServiceError {}

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
        for m in [METHOD_REGISTER, METHOD_BIND, METHOD_VERIFY] {
            let sig = iface.method(&method_symbol(m)).unwrap();
            assert_eq!(sig.semantics, Semantics::Replayable, "{m} is replayable");
            assert_eq!(
                sig.auth_required,
                AuthRequired::Signature,
                "{m} is sig-gated"
            );
        }
        let resolve = iface.method(&method_symbol(METHOD_RESOLVE)).unwrap();
        assert_eq!(resolve.semantics, Semantics::Serviced);
        assert_eq!(resolve.auth_required, AuthRequired::None);
    }

    #[test]
    fn register_desugars_to_the_seal_effects() {
        let cclerk = test_cipherclerk();
        let svc = DomainService::new(cclerk.cell_id());
        let turn = svc
            .register(
                &cclerk,
                "blog.example.com",
                "dregg:alice",
                InvokeAuthority::Signature,
            )
            .expect("register routes through the interface");
        let action = &turn.call_forest.roots[0].action;
        assert_eq!(action.method, method_symbol(METHOD_REGISTER));
        // SetField(DOMAIN), SetField(OWNER), EmitEvent.
        assert_eq!(action.effects.len(), 3);
    }

    #[test]
    fn verify_desugars_to_the_flip() {
        let cclerk = test_cipherclerk();
        let svc = DomainService::new(cclerk.cell_id());
        let turn = svc
            .verify(&cclerk, 4, InvokeAuthority::Signature)
            .expect("verify routes");
        assert_eq!(turn.call_forest.roots[0].action.effects.len(), 3);
    }

    #[test]
    fn unauthorized_bind_refused_at_the_front_door() {
        let cclerk = test_cipherclerk();
        let svc = DomainService::new(cclerk.cell_id());
        // `bind` needs `Signature`; a `None` holder is refused before any turn.
        assert!(matches!(
            svc.bind(&cclerk, "blog", "dregg-verify-abc", InvokeAuthority::None),
            Err(DomainServiceError::Refused(
                InvokeRefused::Unauthorized { .. }
            ))
        ));
    }

    #[test]
    fn empty_field_rejected_before_any_turn() {
        let cclerk = test_cipherclerk();
        let svc = DomainService::new(cclerk.cell_id());
        assert!(matches!(
            svc.register(&cclerk, "", "dregg:alice", InvokeAuthority::Signature),
            Err(DomainServiceError::EmptyField)
        ));
    }

    #[test]
    fn resolve_is_a_serviced_seam_never_desugared() {
        let cclerk = test_cipherclerk();
        let svc = DomainService::new(cclerk.cell_id());
        assert!(matches!(
            svc.resolve(&cclerk),
            Err(DomainServiceError::Refused(
                InvokeRefused::ServicedSeam { .. }
            ))
        ));
    }
}
