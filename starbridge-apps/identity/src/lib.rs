//! `starbridge-identity` — Userspace identity app composing
//! `pyana-credentials` (G31).
//!
//! # Why this crate exists
//!
//! `apps/identity/` (audited 2026-05-24) re-invented credential
//! primitives badly: `Credential` had no signature field; the verifier
//! trusted a `verified: bool` set on the holder; selective disclosure
//! truncated text to 4 bytes. The audit explicitly recommended
//! promoting `bridge::present` to a dedicated crate (G31) and deprecating
//! the app's reinvention.
//!
//! This starbridge-app is the *thin* identity app that survives once
//! the credential primitive is correctly factored out. It carries:
//!
//! 1. **Schema definitions** for common credential types (KYC, government
//!    ID, employment). These are *data*, not new circuits.
//! 2. **Turn-builder helpers** for credential lifecycle events:
//!    - `build_issue_event_action` — emit a `credential-issued` event
//!      on the issuer cell.
//!    - `build_revoke_event_action` — emit a `credential-revoked`
//!      event on the issuer cell.
//!    - `build_present_event_action` — record a presentation attestation
//!      on the holder's cell (no PII leak; only the revealed-facts
//!      commitment is logged).
//!
//! All ZK heavy lifting routes through `pyana-credentials` —
//! `issue` / `present` / `verify` / `revoke` are re-exported so callers
//! can avoid touching `pyana_bridge::present::*` directly.
//!
//! # What this crate is NOT
//!
//! - Not an HTTP service. Mounting credentials under axum routes is the
//!   host's responsibility.
//! - Not a wallet. The holder's credentials live wherever the host
//!   chooses to store them.
//! - Not a federation registry. Issuer-membership Merkle trees are
//!   maintained outside this crate; the host wires them in via
//!   `PresentationOptions::federation_registry`.

#![forbid(unsafe_code)]

use pyana_app_framework::{Action, AppWallet, CellId, Effect, Event, FieldElement, symbol};

pub use pyana_credentials::{
    AttrValue, AttributeAttenuation, Credential, CredentialAttributes, CredentialSchema,
    IssuanceError, IssuerKeys, Predicate, PredicateRequest, Presentation, PresentationError,
    PresentationOptions, RevocationProof, RevocationRegistry, VerificationError,
    VerificationOptions, VerifiedPresentation, issue, present, present_anonymous, revoke, verify,
    verify_anonymous,
};

// =============================================================================
// Common schemas
// =============================================================================

/// A KYC-tier credential schema: name + date-of-birth + verification level.
pub fn kyc_schema() -> CredentialSchema {
    CredentialSchema::new(
        "kyc-v1",
        vec![
            "given_name".into(),
            "family_name".into(),
            "dob".into(),
            "verification_level".into(),
        ],
    )
}

/// A government-id credential schema: id_number + issuing country + expiry.
pub fn gov_id_schema() -> CredentialSchema {
    CredentialSchema::new(
        "gov-id-v1",
        vec!["id_number".into(), "country".into(), "expires_on".into()],
    )
}

/// An employment-verification credential schema: employer + role + start date.
pub fn employment_schema() -> CredentialSchema {
    CredentialSchema::new(
        "employment-v1",
        vec!["employer".into(), "role".into(), "start_date".into()],
    )
}

// =============================================================================
// Turn-builders for credential lifecycle events
// =============================================================================

/// Field-slot index used to commit the issuer's credential commitment
/// on the issuer cell.
pub const ISSUER_COMMITMENT_SLOT: usize = 2;

/// Field-slot index used to commit the revocation root on the issuer cell.
pub const REVOCATION_ROOT_SLOT: usize = 3;

/// Build an `Action` recording a credential issuance.
///
/// Emits two effects on the issuer cell:
/// 1. `SetField(ISSUER_COMMITMENT_SLOT, credential_id)` — anchors the
///    credential id so that anyone reading the cell can verify the
///    issuance is on-record.
/// 2. `EmitEvent("credential-issued", [credential_id, holder_id])` —
///    surfaces the issuance for off-chain indexers. **No attribute
///    values are emitted in cleartext.**
pub fn build_issue_event_action(
    wallet: &AppWallet,
    issuer_cell: CellId,
    credential: &Credential,
) -> Action {
    let id = credential.id();
    let effects = vec![
        Effect::SetField {
            cell: issuer_cell,
            index: ISSUER_COMMITMENT_SLOT,
            value: id,
        },
        Effect::EmitEvent {
            cell: issuer_cell,
            event: Event::new(symbol("credential-issued"), vec![id, credential.holder_id]),
        },
    ];
    wallet.make_action(issuer_cell, "issue_credential", effects)
}

/// Build an `Action` recording a credential revocation.
///
/// Emits:
/// 1. `SetField(REVOCATION_ROOT_SLOT, new_root)` — anchors the updated
///    revocation root.
/// 2. `EmitEvent("credential-revoked", [credential_id, new_root])` —
///    surfaces the revocation.
pub fn build_revoke_event_action(
    wallet: &AppWallet,
    issuer_cell: CellId,
    credential_id: [u8; 32],
    new_root: [u8; 32],
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: issuer_cell,
            index: REVOCATION_ROOT_SLOT,
            value: new_root,
        },
        Effect::EmitEvent {
            cell: issuer_cell,
            event: Event::new(symbol("credential-revoked"), vec![credential_id, new_root]),
        },
    ];
    wallet.make_action(issuer_cell, "revoke_credential", effects)
}

/// Build an `Action` recording a successful presentation.
///
/// Logs only the revealed-facts commitment, not the disclosed values.
/// The presentation itself was already verified off-chain; this action
/// is the on-chain record that the verifier consumed it.
pub fn build_present_event_action(
    wallet: &AppWallet,
    verifier_cell: CellId,
    revealed_facts_commitment: FieldElement,
    holder_id: [u8; 32],
) -> Action {
    let effects = vec![Effect::EmitEvent {
        cell: verifier_cell,
        event: Event::new(
            symbol("credential-presented"),
            vec![revealed_facts_commitment, holder_id],
        ),
    }];
    wallet.make_action(verifier_cell, "present_credential", effects)
}

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_app_framework::{AgentWallet, AppWallet, Authorization, EmbeddedExecutor};

    fn test_wallet() -> AppWallet {
        AppWallet::new(AgentWallet::new(), [42u8; 32])
    }

    fn test_cell() -> CellId {
        CellId::from_bytes([1u8; 32])
    }

    fn test_issuer() -> IssuerKeys {
        IssuerKeys::new(
            [100u8; 32],
            [50u8; 32],
            b"test-issuer",
            "starbridge-identity-test",
        )
    }

    #[test]
    fn kyc_schema_has_expected_attributes() {
        let s = kyc_schema();
        assert_eq!(s.name, "kyc-v1");
        assert!(s.has_attribute("given_name"));
        assert!(s.has_attribute("verification_level"));
    }

    #[test]
    fn build_issue_event_records_credential_id() {
        let wallet = test_wallet();
        let issuer = test_issuer();
        let schema = kyc_schema();
        let attrs = CredentialAttributes::new()
            .with("given_name", AttrValue::Text("Alice".into()))
            .with("family_name", AttrValue::Text("Doe".into()))
            .with("dob", AttrValue::Date(10_000))
            .with("verification_level", AttrValue::Integer(2));
        let cred = issue(&issuer, &schema, [3u8; 32], attrs, 1_700_000_000, None).unwrap();
        let action = build_issue_event_action(&wallet, test_cell(), &cred);
        assert_eq!(action.effects.len(), 2);
        match &action.effects[0] {
            Effect::SetField { value, .. } => assert_eq!(*value, cred.id()),
            other => panic!("expected SetField, got {other:?}"),
        }
        assert!(matches!(&action.effects[1], Effect::EmitEvent { .. }));
    }

    #[test]
    fn build_revoke_event_records_new_root() {
        let wallet = test_wallet();
        let new_root = [0xa5u8; 32];
        let credential_id = [0x55u8; 32];
        let action = build_revoke_event_action(&wallet, test_cell(), credential_id, new_root);
        assert_eq!(action.effects.len(), 2);
        match &action.effects[0] {
            Effect::SetField { value, index, .. } => {
                assert_eq!(*index, REVOCATION_ROOT_SLOT);
                assert_eq!(*value, new_root);
            }
            other => panic!("expected SetField, got {other:?}"),
        }
    }

    #[test]
    fn action_carries_real_signature() {
        let wallet = test_wallet();
        let issuer = test_issuer();
        let schema = kyc_schema();
        let attrs = CredentialAttributes::new()
            .with("given_name", AttrValue::Text("Bob".into()))
            .with("family_name", AttrValue::Text("Roe".into()))
            .with("dob", AttrValue::Date(10_000))
            .with("verification_level", AttrValue::Integer(1));
        let cred = issue(&issuer, &schema, [4u8; 32], attrs, 1_700_000_000, None).unwrap();
        let action = build_issue_event_action(&wallet, test_cell(), &cred);
        match action.authorization {
            Authorization::Signature(a, b) => {
                assert!(
                    a != [0u8; 32] || b != [0u8; 32],
                    "signature must be non-zero"
                );
            }
            other => panic!("expected Signature, got {other:?}"),
        }
    }
}
