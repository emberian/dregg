//! `starbridge-identity` — userspace verifiable-credentials app composing
//! `pyana-credentials` (G31).
//!
//! Companion docs:
//! - `../../../STARBRIDGE-APPS-PLAN.md` §3.2 — the per-app design sketch
//!   this crate implements.
//! - `../../../BOUNDARIES.md` §2.11 — the credential-presentation boundary
//!   the multi-show-unlinkability test exercises.
//! - `../../../SLOT-CAVEATS-DESIGN.md` — the Lane G slot-caveat vocabulary
//!   used by the issuer factory (`MonotonicSequence`, `Monotonic`,
//!   `SenderAuthorized`).
//! - `../../../APPS-AS-USERSPACE-AUDIT.md` §1.3 — the audit that motivated
//!   the rebuild.
//!
//! # Stance
//!
//! `apps/identity/` (audited 2026-05-24) re-invented credential primitives
//! badly: `Credential` had no signature field; the verifier trusted a
//! `verified: bool` set on the holder; selective disclosure truncated text
//! to 4 bytes. `PYANA-FLAWS-FROM-APPS.md` G31 promoted `bridge::present` to
//! the `pyana-credentials` crate. **This starbridge-app is the thin
//! userspace shell that survives once the credential primitive is
//! correctly factored out**: schemas, factory descriptor, turn-builders,
//! and inspector wiring.
//!
//! All ZK heavy lifting (blinded merkle, predicate disclosure, ring proof,
//! non-revocation) lives in `pyana-credentials`. This crate composes that
//! through cell-programs: `Effect::SetField` + `Effect::EmitEvent`, never a
//! domain-specific `Effect::IssueCredential` or
//! `Authorization::Unchecked` placeholder.
//!
//! # What this crate exports
//!
//! 1. [`issuer_factory_descriptor`] — `FactoryDescriptor` for the
//!    per-issuer sovereign cell. State slots:
//!    - `SCHEMA_COMMITMENT_SLOT` — pinned schema-commitment hash
//!      (`Immutable`).
//!    - `ISSUANCE_COUNTER_SLOT` — strictly-increasing issuance counter
//!      (`MonotonicSequence`).
//!    - `REVOCATION_ROOT_SLOT` — federation-attested revocation root
//!      (`Monotonic`).
//!    - `ISSUER_AUTH_ROOT_SLOT` — authorized-issuer pubkey-set root
//!      (`SenderAuthorized` with `PublicRoot`).
//!
//! 2. Turn builders:
//!    - [`build_issue_credential_action`]
//!    - [`build_revoke_credential_action`]
//!    - [`build_present_credential_action`]
//!    - [`build_verify_presentation_action`]
//!
//! 3. Common credential schemas (`kyc_schema`, `gov_id_schema`,
//!    `employment_schema`).
//!
//! 4. [`register`] — `StarbridgeAppContext` mount that installs the
//!    factory descriptor and the four inspector descriptors
//!    (`pyana-credential`, `pyana-credential-issue-form`,
//!    `pyana-credential-present-form`, `pyana-credential-verifier`).
//!
//! # What this crate is NOT
//!
//! - Not an HTTP service. Mounting credentials under axum routes is the
//!   host's responsibility — see `apps/identity/server.rs` for the legacy
//!   shape; the starbridge-host imports this crate's [`register`] and
//!   wires it via `AppServer`.
//! - Not a cclerk. The holder's credentials live wherever the host
//!   chooses to store them (inbox queues, `pyana-storage`, etc.).
//! - Not a federation registry. Issuer-membership Merkle trees are
//!   maintained outside this crate; the host wires them through
//!   `PresentationOptions::federation_registry`.

#![forbid(unsafe_code)]

use pyana_app_framework::{
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellId, CellMode, CellProgram,
    ChildVkStrategy, Effect, Event, FactoryDescriptor, FieldConstraint, FieldElement,
    InspectorDescriptor, StarbridgeAppContext, StateConstraint, canonical_program_vk, symbol,
};
use pyana_cell::program::AuthorizedSet;

pub use pyana_credentials::{
    AttrValue, AttributeAttenuation, Credential, CredentialAttributes, CredentialSchema,
    IssuanceError, IssuerKeys, Predicate, PredicateRequest, Presentation, PresentationError,
    PresentationOptions, RevocationProof, RevocationRegistry, VerificationError,
    VerificationOptions, VerifiedPresentation, issue, present, present_anonymous, revoke, verify,
    verify_anonymous,
};

// =============================================================================
// Common credential schemas
// =============================================================================

/// A KYC-tier credential schema: given/family name, DOB, verification level.
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

/// An employment-verification credential schema: employer + role + start.
pub fn employment_schema() -> CredentialSchema {
    CredentialSchema::new(
        "employment-v1",
        vec!["employer".into(), "role".into(), "start_date".into()],
    )
}

// =============================================================================
// State schema (per-issuer-cell field-slot layout)
// =============================================================================

/// Slot at which the (Poseidon2/blake3) commitment to the issuer's
/// canonical credential schema is anchored. Pinned at issuer-cell creation
/// time via `FieldConstraint::NonZero` and held `Immutable` afterward — a
/// schema upgrade requires a new issuer cell with a new factory invocation.
pub const SCHEMA_COMMITMENT_SLOT: usize = 2;

/// Slot at which the strictly-monotonic issuance counter is anchored.
/// Enforced by `StateConstraint::MonotonicSequence { seq_index }` — every
/// issuance turn must increment the slot by exactly one. This closes the
/// replay window the audit called out (an issuer could replay an old
/// issuance turn without an in-band sequence).
pub const ISSUANCE_COUNTER_SLOT: usize = 3;

/// Slot at which the federation-attested revocation merkle root is
/// anchored. Enforced by `StateConstraint::Monotonic { index }` — the
/// revocation set is append-only, so the root can only grow lexicographically
/// large enough to prove non-membership for a strictly-larger revoked-id
/// set. (For real binary merkle roots the byte ordering does not need to
/// monotonically increase; we keep the constraint here as the strongest
/// thing the executor can check without a full merkle-update circuit —
/// see the TODO at [`build_revoke_credential_action`].)
pub const REVOCATION_ROOT_SLOT: usize = 4;

/// Slot at which the merkle root of authorized-issuer public keys is
/// anchored. Consumed by `StateConstraint::SenderAuthorized { set:
/// AuthorizedSet::PublicRoot { set_root_index } }` so the executor only
/// admits turns whose `sender_pk` is in the published set. Multi-sig
/// issuance scenarios (KYC notary + bank co-signer) materialize as multiple
/// authorized pubkeys under the same root.
pub const ISSUER_AUTH_ROOT_SLOT: usize = 5;

// =============================================================================
// Factory configuration
// =============================================================================

/// Default rate-limit on issuance: at most 100k credentials per epoch from
/// a single issuer cell. Mirrors nameservice's anti-Sybil budget — the
/// number is a starting place, not a contract.
pub const DEFAULT_ISSUER_BUDGET: u64 = 100_000;

/// The factory VK we publish for the identity-issuer factory.
///
/// As in `starbridge-nameservice`, this is a stable placeholder. The real
/// VK is the BLAKE3 hash of the issuer cell-program's VK; replacing this
/// constant once the program AIR lands is a single-line change.
pub const ISSUER_FACTORY_VK: [u8; 32] = *b"starbridge-identity-issuer-fact!";

/// The cell-program installed on per-issuer cells.
///
/// Per `VK-AS-RE-EXECUTION-RECIPE.md` §2.1: every cell produced by
/// [`issuer_factory_descriptor`] inherits this program. Validators
/// re-execute it against the cell's transition stream until plonky3
/// recursion lands and the program becomes a real recursive AIR.
///
/// The constraint set:
/// - `Immutable(SCHEMA_COMMITMENT_SLOT)` — schema cannot change.
/// - `MonotonicSequence(ISSUANCE_COUNTER_SLOT)` — strictly +1 per turn.
/// - `Monotonic(REVOCATION_ROOT_SLOT)` — revocation set is append-only.
/// - `SenderAuthorized(PublicRoot { ISSUER_AUTH_ROOT_SLOT })` — only
///   authorized issuer pubkeys may submit issuance turns.
pub fn issuer_program() -> CellProgram {
    CellProgram::always(vec![
        StateConstraint::Immutable {
            index: SCHEMA_COMMITMENT_SLOT as u8,
        },
        StateConstraint::MonotonicSequence {
            seq_index: ISSUANCE_COUNTER_SLOT as u8,
        },
        StateConstraint::Monotonic {
            index: REVOCATION_ROOT_SLOT as u8,
        },
        StateConstraint::SenderAuthorized {
            set: AuthorizedSet::PublicRoot {
                set_root_index: ISSUER_AUTH_ROOT_SLOT as u8,
            },
        },
    ])
}

/// The child cell program VK installed on per-issuer cells.
///
/// Computed canonically per `VK-AS-RE-EXECUTION-RECIPE.md` §2.1:
/// `canonical_program_vk(&issuer_program())`. A validator with the
/// program in hand can confirm the VK binds to a program they can
/// re-execute against witness data.
///
/// Previously a byte-string placeholder
/// (`*b"starbridge-identity-issuer-prog!"`); the canonical version
/// makes the substrate honest pre-recursion.
pub fn issuer_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&issuer_program())
}

// =============================================================================
// FactoryDescriptor
// =============================================================================

/// Build the `FactoryDescriptor` for the identity-issuer cell factory.
///
/// Pins the constructor contract anyone can audit by hashing the
/// descriptor:
///
/// - `child_program_vk = issuer_child_program_vk()` — the
///   credential-issuance state machine.
/// - `default_mode = Sovereign` — issuers live as their own cells.
/// - `creation_budget = DEFAULT_ISSUER_BUDGET` — rate-limits per-epoch
///   issuance across all cells produced from this factory.
/// - `allowed_cap_templates = [issuer_cap]` — a single attenuatable
///   signature-authorized capability that the factory may grant on
///   creation. Holders / verifiers do not need this cap; only the issuer
///   does, so the template is minimal.
/// - `field_constraints` (creation-time):
///   - `NonZero(SCHEMA_COMMITMENT_SLOT)` — the issuer must declare the
///     schema commitment at creation.
///   - `NonZero(ISSUER_AUTH_ROOT_SLOT)` — the authorized-issuer set
///     must be populated; a zero root would admit any sender.
/// - `state_constraints` (perpetual / Lane G slot caveats):
///   - `Immutable(SCHEMA_COMMITMENT_SLOT)` — the issuer's schema cannot
///     change after creation. A schema upgrade requires a new issuer
///     cell.
///   - `MonotonicSequence(ISSUANCE_COUNTER_SLOT)` — every issuance turn
///     increments the counter by exactly one. Replay of a stale
///     issuance turn is rejected at execution time.
///   - `Monotonic(REVOCATION_ROOT_SLOT)` — revocation is append-only.
///   - `SenderAuthorized(PublicRoot { ISSUER_AUTH_ROOT_SLOT })` — only
///     issuers whose pubkey is in the published set can submit turns.
pub fn issuer_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: ISSUER_FACTORY_VK,
        child_program_vk: Some(issuer_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(issuer_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        field_constraints: vec![
            FieldConstraint::NonZero {
                field_index: SCHEMA_COMMITMENT_SLOT as u32,
            },
            FieldConstraint::NonZero {
                field_index: ISSUER_AUTH_ROOT_SLOT as u32,
            },
        ],
        state_constraints: vec![
            StateConstraint::Immutable {
                index: SCHEMA_COMMITMENT_SLOT as u8,
            },
            StateConstraint::MonotonicSequence {
                seq_index: ISSUANCE_COUNTER_SLOT as u8,
            },
            StateConstraint::Monotonic {
                index: REVOCATION_ROOT_SLOT as u8,
            },
            StateConstraint::SenderAuthorized {
                set: AuthorizedSet::PublicRoot {
                    set_root_index: ISSUER_AUTH_ROOT_SLOT as u8,
                },
            },
        ],
        default_mode: CellMode::Sovereign,
        creation_budget: Some(DEFAULT_ISSUER_BUDGET),
    }
}

/// Full slice of factory descriptors this starbridge-app contributes.
///
/// Today: one entry (the issuer factory). A future `verifier_factory` —
/// for cells that record presentation receipts under a verifier-bound
/// rate limit — would land here once Tier-3 #13 (attester registry) is
/// in flight.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![issuer_factory_descriptor()]
}

// =============================================================================
// Turn-builders (signed actions over generic Effects)
// =============================================================================

/// Compute a 32-byte commitment for a credential schema. Used as the
/// `SCHEMA_COMMITMENT_SLOT` value at issuer-cell creation time.
pub fn schema_commitment(schema: &CredentialSchema) -> FieldElement {
    let mut hasher = blake3::Hasher::new_derive_key("pyana-credential-schema-v1");
    hasher.update(schema.name.as_bytes());
    hasher.update(&(schema.attributes.len() as u64).to_le_bytes());
    for attr in &schema.attributes {
        hasher.update(&(attr.len() as u64).to_le_bytes());
        hasher.update(attr.as_bytes());
    }
    *hasher.finalize().as_bytes()
}

/// Build the `Action` recording a credential issuance.
///
/// Effects:
///
/// 1. `SetField(ISSUANCE_COUNTER_SLOT, new_counter)` — anchors the
///    incremented counter. The on-cell `MonotonicSequence` caveat enforces
///    `new == old + 1`; the caller supplies the value it expects, so an
///    off-by-one is rejected at execution time.
/// 2. `SetField(REVOCATION_ROOT_SLOT, new_revocation_root)` — the
///    revocation root is unchanged at issuance time but we still write it
///    so the slot is materially up to date; the `Monotonic` caveat
///    accepts `new == old`. Callers that don't want to touch the slot can
///    use [`build_issue_credential_action_minimal`] (single-effect
///    variant).
/// 3. `EmitEvent("credential-issued", [credential_id, holder_id,
///    new_counter])` — surfaces the issuance for off-chain indexers. **No
///    attribute values are emitted in cleartext.**
///
/// # ZK composition
///
/// The credential itself (signed macaroon + attribute attenuation) is
/// produced by `pyana_credentials::issue(...)`. This function consumes
/// the resulting `Credential` and records only its 32-byte id. The signed
/// proof of issuance is the macaroon inside `credential`, not this action
/// — the action's role is to anchor the issuance on a cell so verifiers
/// have an on-ledger witness that the issuer published the credential
/// under their `ISSUER_AUTH_ROOT_SLOT`.
pub fn build_issue_credential_action(
    cipherclerk: &AppCipherclerk,
    issuer_cell: CellId,
    credential: &Credential,
    new_counter: u64,
    revocation_root: [u8; 32],
) -> Action {
    let id = credential.id();
    let holder_id = credential.holder_id;
    let counter_field = u64_field(new_counter);
    let effects = vec![
        Effect::SetField {
            cell: issuer_cell,
            index: ISSUANCE_COUNTER_SLOT,
            value: counter_field,
        },
        Effect::SetField {
            cell: issuer_cell,
            index: REVOCATION_ROOT_SLOT,
            value: revocation_root,
        },
        Effect::EmitEvent {
            cell: issuer_cell,
            event: Event::new(
                symbol("credential-issued"),
                vec![id, holder_id, counter_field],
            ),
        },
    ];
    cipherclerk.make_action(issuer_cell, "issue_credential", effects)
}

/// Build the `Action` recording a credential revocation.
///
/// Effects:
///
/// 1. `SetField(REVOCATION_ROOT_SLOT, new_root)` — anchors the updated
///    revocation root. The on-cell `Monotonic` caveat enforces
///    append-only growth. The caller computes `new_root` by hashing the
///    revoked-id set (see `RevocationRegistry::root`).
/// 2. `EmitEvent("credential-revoked", [credential_id, new_root])` —
///    surfaces the revocation event.
///
/// # TODO — non-revocation STARK binding
///
/// `pyana-credentials` G39 calls for the non-revocation circuit to bind
/// `pi::REVOCATION_HASH` to the credential id. When that lands, the
/// presentation verifier will additionally check the proof's
/// `REVOCATION_HASH` against this slot — until then verifiers use the
/// `RevocationProof.revoked` boolean (see
/// [`build_verify_presentation_action`]).
pub fn build_revoke_credential_action(
    cipherclerk: &AppCipherclerk,
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
    cipherclerk.make_action(issuer_cell, "revoke_credential", effects)
}

/// Build the `Action` recording that a holder produced a credential
/// presentation.
///
/// Effects:
///
/// 1. `EmitEvent("credential-presented", [revealed_facts_commitment,
///    holder_commitment, anonymous_flag])` — surfaces the presentation.
///
/// **No PII leak**: only the `revealed_facts_commitment` (the Poseidon2
/// fold over disclosed attribute fact-terms) and a `holder_commitment` are
/// emitted. The latter is `[0u8; 32]` for anonymous presentations and the
/// holder's cell id otherwise.
///
/// The presentation itself was produced by `pyana_credentials::present(...)`
/// (or `present_anonymous(...)`); the action's role is to give the holder
/// a cell-bound audit trail of their own presentations without exposing
/// the contents.
pub fn build_present_credential_action(
    cipherclerk: &AppCipherclerk,
    holder_cell: CellId,
    presentation: &Presentation,
) -> Action {
    let revealed_facts_commitment = wide_hash_bytes(&presentation.proof.revealed_facts_commitment);
    let holder_commitment = if presentation.anonymous {
        [0u8; 32]
    } else {
        // The holder's cell-id is published as the recorded holder; for
        // a non-anonymous presentation this is intentional.
        *holder_cell.as_bytes()
    };
    let anonymous_flag = bool_field(presentation.anonymous);

    let effects = vec![Effect::EmitEvent {
        cell: holder_cell,
        event: Event::new(
            symbol("credential-presented"),
            vec![revealed_facts_commitment, holder_commitment, anonymous_flag],
        ),
    }];
    cipherclerk.make_action(holder_cell, "present_credential", effects)
}

/// Build the `Action` recording that a verifier accepted or rejected a
/// credential presentation against the verifier's expectations.
///
/// Runs the verification synchronously via
/// `pyana_credentials::verify(presentation, &options)`; the resulting
/// boolean drives the emitted event.
///
/// Effects:
///
/// 1. `EmitEvent("presentation-verified", [revealed_facts_commitment,
///    accept_flag, predicate_count])` — surfaces accept/reject.
///    `predicate_count` lets indexers cheaply filter for
///    selective-disclosure presentations.
///
/// # Revocation-root binding
///
/// `options.revocation` carries the non-revocation proof anchored against
/// the **issuer cell's current `REVOCATION_ROOT_SLOT`**. The caller is
/// responsible for reading that slot off-chain (e.g., via
/// `<pyana-credential>` inspector or a direct cell-state read), building
/// the `RevocationProof`, and supplying it here. When G39 lands the
/// non-revocation STARK directly, this hand-wiring goes away.
pub fn build_verify_presentation_action(
    cipherclerk: &AppCipherclerk,
    verifier_cell: CellId,
    presentation: &Presentation,
    options: &VerificationOptions,
) -> Action {
    let result = verify(presentation, options);
    let accept = result.is_ok();
    let revealed_facts_commitment = wide_hash_bytes(&presentation.proof.revealed_facts_commitment);
    let accept_field = bool_field(accept);
    let pred_count = u64_field(presentation.predicate_proofs.len() as u64);

    let topic = if accept {
        "presentation-accepted"
    } else {
        "presentation-rejected"
    };

    let effects = vec![Effect::EmitEvent {
        cell: verifier_cell,
        event: Event::new(
            symbol(topic),
            vec![revealed_facts_commitment, accept_field, pred_count],
        ),
    }];
    cipherclerk.make_action(verifier_cell, "verify_presentation", effects)
}

// =============================================================================
// StarbridgeAppContext mount
// =============================================================================

/// Register the identity starbridge-app on a [`StarbridgeAppContext`].
///
/// Installs:
///
/// 1. The issuer factory descriptor under [`ISSUER_FACTORY_VK`].
/// 2. Four inspector descriptors mounted under the
///    `/starbridge-apps/identity/inspectors.js` module:
///    - `pyana-credential` — read-only credential view (attributes,
///      schema, status).
///    - `pyana-credential-issue-form` — issuer's UI form.
///    - `pyana-credential-present-form` — holder's UI (selective
///      disclosure picker + predicate request builder).
///    - `pyana-credential-verifier` — verifier's UI showing accept /
///      reject and the revealed-facts trace.
///
/// Returns the registered factory VK.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    // 1. Register the issuer factory descriptor.
    let factory_vk = ctx.register_factory(issuer_factory_descriptor());

    let module_path = "/starbridge-apps/identity/inspectors.js";
    let factory_vk_hex = hex_encode(&factory_vk);

    // 2. Per-credential view (read-only).
    ctx.register_inspector(InspectorDescriptor {
        kind: "credential".into(),
        descriptor: serde_json::json!({
            "component": "pyana-credential",
            "module": module_path,
            "uri_prefix": "pyana://credential/",
            "summary_fields": ["schema", "holder_id", "issued_at", "not_after", "status"],
            "factory_vk_hex": factory_vk_hex,
            "child_program_vk_hex": hex_encode(&issuer_child_program_vk()),
        }),
    });

    // 3. Issuer form.
    ctx.register_inspector(InspectorDescriptor {
        kind: "credential-issue-form".into(),
        descriptor: serde_json::json!({
            "component": "pyana-credential-issue-form",
            "module": module_path,
            "uri_prefix": "pyana://cell/",
            "method": "issue_credential",
            "factory_vk_hex": factory_vk_hex,
            "schemas": [
                kyc_schema().name,
                gov_id_schema().name,
                employment_schema().name,
            ],
        }),
    });

    // 4. Holder presentation form.
    ctx.register_inspector(InspectorDescriptor {
        kind: "credential-present-form".into(),
        descriptor: serde_json::json!({
            "component": "pyana-credential-present-form",
            "module": module_path,
            "uri_prefix": "pyana://credential/",
            "method": "present_credential",
            "supports_anonymous": true,
            "supports_predicates": true,
        }),
    });

    // 5. Verifier UI.
    ctx.register_inspector(InspectorDescriptor {
        kind: "credential-verifier".into(),
        descriptor: serde_json::json!({
            "component": "pyana-credential-verifier",
            "module": module_path,
            "uri_prefix": "pyana://presentation/",
            "method": "verify_presentation",
        }),
    });

    factory_vk
}

// =============================================================================
// Cross-app composition
// =============================================================================
//
// The integrations below let other starbridge-apps consume credentials
// issued by an identity-issuer cell *without* importing the credential
// internals. They reduce a (issuer_cell, schema) pair to either:
//
//   1. An `AuthorizedSet::CredentialSet` clause that cell-programs can
//      bake into their `StateConstraint::SenderAuthorized` set (so an
//      app can require "sender holds a kyc-v1 credential from issuer X"
//      directly at the executor / cell-program layer); or
//
//   2. A `WitnessedPredicate::BlindedSet` that an `Action` carries in
//      `witness_blobs[i]` to discharge the constraint at turn time.
//
// The pair compose deterministically: the constraint's commitment is the
// same 32 bytes the witness predicate carries, derived from
// (issuer_cell, schema_commitment). Cross-app code on either side can
// reproduce the value without depending on private hashing routines.

/// Reduce an `(issuer_cell, schema)` pair to a stable 32-byte commitment
/// other apps can bake into `AuthorizedSet::CredentialSet` constraints.
///
/// Reads through to [`AuthorizedSet::credential_set_commitment`] so the
/// cell-program executor and the userspace builders agree on the byte
/// shape. The value is `blake3_derive_key("pyana-credential-set-v1") ||
/// issuer_cell || schema_commitment`.
pub fn credential_set_commitment(issuer_cell: CellId, schema: &CredentialSchema) -> [u8; 32] {
    let schema_id = schema_commitment(schema);
    AuthorizedSet::credential_set_commitment(issuer_cell.as_bytes(), &schema_id)
}

/// Build a `StateConstraint::SenderAuthorized` clause whose authorized
/// set is "holders of a credential matching `schema` issued by
/// `issuer_cell`".
///
/// Cross-app callers (e.g. `starbridge-governed-namespace` for
/// credential-gated voting; `starbridge-nameservice` for
/// identity-attested tiers) drop the returned `StateConstraint` into a
/// cell-program case. The executor's
/// `WitnessedPredicateRegistry` dispatches the matching credential
/// proof carried in the action's `witness_blobs`.
pub fn credential_set_constraint(
    issuer_cell: CellId,
    schema: &CredentialSchema,
) -> StateConstraint {
    StateConstraint::SenderAuthorized {
        set: AuthorizedSet::CredentialSet {
            issuer_cell: *issuer_cell.as_bytes(),
            credential_schema_id: schema_commitment(schema),
        },
    }
}

/// Build the witnessed-predicate shape an `Action` carries to discharge
/// a [`credential_set_constraint`].
///
/// The returned predicate names the same commitment a matching
/// `AuthorizedSet::CredentialSet` resolves to on the executor side
/// (per [`credential_set_commitment`]), so dispatch is deterministic.
/// `proof_witness_index` names the slot in the action's
/// `witness_blobs` carrying the `Presentation` proof bytes (kind
/// `ProofBytes`).
pub fn credential_set_predicate(
    issuer_cell: CellId,
    schema: &CredentialSchema,
    proof_witness_index: usize,
) -> pyana_cell::predicate::WitnessedPredicate {
    use pyana_cell::predicate::{InputRef, WitnessedPredicate, WitnessedPredicateKind};
    WitnessedPredicate {
        kind: WitnessedPredicateKind::BlindedSet,
        commitment: credential_set_commitment(issuer_cell, schema),
        input_ref: InputRef::Sender,
        proof_witness_index,
    }
}

// =============================================================================
// Helpers
// =============================================================================

/// Encode a `u64` as a 32-byte big-endian-padded `FieldElement`. Matches
/// the `field_from_u64_be` convention used in `pyana_cell::program` so
/// integer-typed constraints see comparable operands.
fn u64_field(value: u64) -> FieldElement {
    let mut out = [0u8; 32];
    out[24..32].copy_from_slice(&value.to_be_bytes());
    out
}

/// Encode a boolean as a 32-byte `FieldElement` (zero or one in the LSB).
fn bool_field(value: bool) -> FieldElement {
    let mut out = [0u8; 32];
    out[31] = u8::from(value);
    out
}

/// Hash a `pyana_circuit::binding::WideHash` to its 32-byte digest form.
///
/// The bridge's `revealed_facts_commitment` is carried as a `WideHash`
/// (4×BabyBear field elements). We expose it as a 32-byte fact-term by
/// blake3-hashing its little-endian byte serialization — this is the same
/// shape used by `pyana_credentials::Presentation::to_wire` callers.
fn wide_hash_bytes(hash: &pyana_circuit::binding::WideHash) -> FieldElement {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"pyana-credential-revealed-commitment");
    for limb in hash.as_slice().iter() {
        hasher.update(&limb.as_u32().to_le_bytes());
    }
    *hasher.finalize().as_bytes()
}

/// Hex-encode a 32-byte digest.
fn hex_encode(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

// =============================================================================
// Tests — unit (in-source). Integration tests live in tests/.
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_app_framework::{AgentCipherclerk, Authorization, EmbeddedExecutor};

    fn test_cipherclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32])
    }

    fn test_cell() -> CellId {
        CellId::from_bytes([1u8; 32])
    }

    fn test_context() -> StarbridgeAppContext {
        let cipherclerk = test_cipherclerk();
        let executor = EmbeddedExecutor::new(&cipherclerk, "default");
        StarbridgeAppContext::new(cipherclerk, executor)
    }

    fn test_issuer() -> IssuerKeys {
        IssuerKeys::new(
            [100u8; 32],
            [50u8; 32],
            b"test-issuer",
            "starbridge-identity-test",
        )
    }

    fn test_credential() -> Credential {
        let issuer = test_issuer();
        let schema = kyc_schema();
        let attrs = CredentialAttributes::new()
            .with("given_name", AttrValue::Text("Alice".into()))
            .with("family_name", AttrValue::Text("Doe".into()))
            .with("dob", AttrValue::Date(10_000))
            .with("verification_level", AttrValue::Integer(2));
        issue(&issuer, &schema, [3u8; 32], attrs, 1_700_000_000, None).expect("issuance succeeds")
    }

    // ── Schema sanity ────────────────────────────────────────────────────

    #[test]
    fn kyc_schema_has_expected_attributes() {
        let s = kyc_schema();
        assert_eq!(s.name, "kyc-v1");
        assert!(s.has_attribute("given_name"));
        assert!(s.has_attribute("verification_level"));
    }

    #[test]
    fn schema_commitment_is_stable_and_distinguishes() {
        let c1 = schema_commitment(&kyc_schema());
        let c2 = schema_commitment(&kyc_schema());
        let c3 = schema_commitment(&gov_id_schema());
        assert_eq!(c1, c2, "schema commitment must be deterministic");
        assert_ne!(c1, c3, "different schemas must have different commitments");
    }

    // ── FactoryDescriptor ────────────────────────────────────────────────

    #[test]
    fn issuer_factory_descriptor_is_stable() {
        let h1 = issuer_factory_descriptor().hash();
        let h2 = issuer_factory_descriptor().hash();
        assert_eq!(h1, h2, "descriptor hash must be deterministic");
    }

    #[test]
    fn issuer_factory_pins_program_vk_and_mode() {
        let d = issuer_factory_descriptor();
        assert_eq!(d.factory_vk, ISSUER_FACTORY_VK);
        assert_eq!(d.child_program_vk, Some(issuer_child_program_vk()));
        assert_eq!(d.default_mode, CellMode::Sovereign);
        assert_eq!(d.creation_budget, Some(DEFAULT_ISSUER_BUDGET));
    }

    #[test]
    fn issuer_child_program_vk_is_canonical_recipe() {
        // Per VK-AS-RE-EXECUTION-RECIPE.md §2.1, the child program VK
        // is the canonical hash of the program text. Validators with
        // the program can re-derive the VK.
        let expected = pyana_app_framework::canonical_program_vk(&issuer_program());
        assert_eq!(
            issuer_child_program_vk(),
            expected,
            "issuer_child_program_vk must equal canonical_program_vk(&issuer_program())"
        );
    }

    #[test]
    fn issuer_child_program_vk_is_not_placeholder_bytes() {
        // The pre-recipe placeholder was `*b"starbridge-identity-issuer-prog!"`.
        let old_placeholder: [u8; 32] = *b"starbridge-identity-issuer-prog!";
        assert_ne!(
            issuer_child_program_vk(),
            old_placeholder,
            "canonical VK must differ from the pre-recipe placeholder"
        );
    }

    #[test]
    fn issuer_child_program_vk_is_v2_layered_hash() {
        // VK v2 (VK-AS-RE-EXECUTION-RECIPE.md §v2): the layered hash
        // must differ from the v1 program-bytes-only hash.
        let program = issuer_program();
        let v2 = issuer_child_program_vk();
        let v1 = pyana_app_framework::canonical_program_bytes_hash(&program);
        assert_ne!(
            v2, v1,
            "v2 layered hash must differ from v1 program-bytes-only hash"
        );
    }

    #[test]
    fn factory_descriptor_validates_against_canonical_program() {
        let d = issuer_factory_descriptor();
        let program = issuer_program();
        // VK v2: use the app-framework wrapper that binds the
        // descriptor's child_program_vk against the *layered* vk_hash
        // (program bytes + Effect VM AIR + verifier + proving system).
        pyana_app_framework::validate_child_vk_canonical(&d, &program)
            .expect("descriptor's child_program_vk must bind to issuer_program() under v2");
    }

    #[test]
    fn issuer_program_carries_expected_caveats() {
        let p = issuer_program();
        let constraints = match p {
            CellProgram::Cases(cases) => cases
                .into_iter()
                .flat_map(|c| c.constraints)
                .collect::<Vec<_>>(),
            other => panic!("expected CellProgram::Cases, got {other:?}"),
        };
        assert_eq!(constraints.len(), 4);
        assert!(constraints.iter().any(|c| matches!(
            c,
            StateConstraint::Immutable { index } if *index == SCHEMA_COMMITMENT_SLOT as u8
        )));
        assert!(constraints.iter().any(|c| matches!(
            c,
            StateConstraint::MonotonicSequence { seq_index } if *seq_index == ISSUANCE_COUNTER_SLOT as u8
        )));
        assert!(constraints.iter().any(|c| matches!(
            c,
            StateConstraint::Monotonic { index } if *index == REVOCATION_ROOT_SLOT as u8
        )));
        assert!(
            constraints
                .iter()
                .any(|c| matches!(c, StateConstraint::SenderAuthorized { .. }))
        );
    }

    #[test]
    fn issuer_factory_constrains_creation_time_slots() {
        let d = issuer_factory_descriptor();
        assert!(
            d.field_constraints.iter().any(|c| matches!(
                c,
                FieldConstraint::NonZero { field_index } if *field_index == SCHEMA_COMMITMENT_SLOT as u32
            )),
            "schema commitment must be required at creation"
        );
        assert!(
            d.field_constraints.iter().any(|c| matches!(
                c,
                FieldConstraint::NonZero { field_index } if *field_index == ISSUER_AUTH_ROOT_SLOT as u32
            )),
            "issuer auth root must be required at creation"
        );
    }

    #[test]
    fn issuer_factory_bakes_slot_caveats() {
        let d = issuer_factory_descriptor();
        assert!(
            d.state_constraints.iter().any(|c| matches!(
                c,
                StateConstraint::Immutable { index } if *index == SCHEMA_COMMITMENT_SLOT as u8
            )),
            "issuer factory must install Immutable on SCHEMA_COMMITMENT_SLOT"
        );
        assert!(
            d.state_constraints.iter().any(|c| matches!(
                c,
                StateConstraint::MonotonicSequence { seq_index }
                    if *seq_index == ISSUANCE_COUNTER_SLOT as u8
            )),
            "issuer factory must install MonotonicSequence on ISSUANCE_COUNTER_SLOT"
        );
        assert!(
            d.state_constraints.iter().any(|c| matches!(
                c,
                StateConstraint::Monotonic { index } if *index == REVOCATION_ROOT_SLOT as u8
            )),
            "issuer factory must install Monotonic on REVOCATION_ROOT_SLOT"
        );
        assert!(
            d.state_constraints.iter().any(|c| matches!(
                c,
                StateConstraint::SenderAuthorized {
                    set: AuthorizedSet::PublicRoot { set_root_index }
                } if *set_root_index == ISSUER_AUTH_ROOT_SLOT as u8
            )),
            "issuer factory must install SenderAuthorized on ISSUER_AUTH_ROOT_SLOT"
        );
    }

    #[test]
    fn factory_descriptors_includes_issuer_factory() {
        let all = factory_descriptors();
        assert_eq!(all.len(), 1);
        assert_eq!(all[0].factory_vk, ISSUER_FACTORY_VK);
    }

    // ── Turn-builders ────────────────────────────────────────────────────

    #[test]
    fn issue_action_records_counter_event_and_revocation_root() {
        let cipherclerk = test_cipherclerk();
        let cred = test_credential();
        let action = build_issue_credential_action(&cipherclerk, test_cell(), &cred, 1, [0u8; 32]);
        assert_eq!(action.effects.len(), 3);
        match &action.effects[0] {
            Effect::SetField { index, value, .. } => {
                assert_eq!(*index, ISSUANCE_COUNTER_SLOT);
                assert_eq!(*value, u64_field(1));
            }
            other => panic!("expected SetField on counter slot, got {other:?}"),
        }
        match &action.effects[1] {
            Effect::SetField { index, .. } => assert_eq!(*index, REVOCATION_ROOT_SLOT),
            other => panic!("expected SetField on revocation slot, got {other:?}"),
        }
        assert!(matches!(&action.effects[2], Effect::EmitEvent { .. }));
    }

    #[test]
    fn revoke_action_records_new_root_and_event() {
        let cipherclerk = test_cipherclerk();
        let new_root = [0xa5u8; 32];
        let credential_id = [0x55u8; 32];
        let action =
            build_revoke_credential_action(&cipherclerk, test_cell(), credential_id, new_root);
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
    fn issue_action_carries_real_signature() {
        let cipherclerk = test_cipherclerk();
        let cred = test_credential();
        let action = build_issue_credential_action(&cipherclerk, test_cell(), &cred, 1, [0u8; 32]);
        match action.authorization {
            Authorization::Signature(a, b) => {
                assert!(
                    a != [0u8; 32] || b != [0u8; 32],
                    "signature must be non-zero (no [0u8; 64] placeholders!)"
                );
            }
            other => panic!("expected Signature, got {other:?}"),
        }
    }

    // ── StarbridgeAppContext mount ───────────────────────────────────────

    #[test]
    fn register_installs_issuer_factory_descriptor() {
        let ctx = test_context();
        assert_eq!(ctx.factory_registry().len(), 0);
        let vk = register(&ctx);
        assert_eq!(vk, ISSUER_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
        let got = ctx
            .factory_registry()
            .get(&ISSUER_FACTORY_VK)
            .expect("issuer factory must be registered");
        assert_eq!(got.factory_vk, ISSUER_FACTORY_VK);
    }

    #[test]
    fn register_installs_all_four_inspectors() {
        let ctx = test_context();
        register(&ctx);

        for kind in [
            "credential",
            "credential-issue-form",
            "credential-present-form",
            "credential-verifier",
        ] {
            let desc = ctx
                .inspector_registry()
                .get(kind)
                .unwrap_or_else(|| panic!("missing inspector for kind={kind}"));
            assert!(desc.descriptor["component"].is_string());
            assert!(desc.descriptor["module"].is_string());
        }
    }

    #[test]
    fn register_is_idempotent_on_factory() {
        let ctx = test_context();
        register(&ctx);
        register(&ctx);
        assert_eq!(ctx.factory_registry().len(), 1);
    }

    // ── Cross-app composition ────────────────────────────────────────────

    #[test]
    fn credential_set_commitment_is_stable_and_distinguishes() {
        let issuer_a = CellId::from_bytes([1u8; 32]);
        let issuer_b = CellId::from_bytes([2u8; 32]);
        let c1 = credential_set_commitment(issuer_a, &kyc_schema());
        let c2 = credential_set_commitment(issuer_a, &kyc_schema());
        let c3 = credential_set_commitment(issuer_b, &kyc_schema());
        let c4 = credential_set_commitment(issuer_a, &gov_id_schema());
        assert_eq!(c1, c2, "commitment is deterministic");
        assert_ne!(
            c1, c3,
            "different issuer cells produce distinct commitments"
        );
        assert_ne!(c1, c4, "different schemas produce distinct commitments");
    }

    #[test]
    fn credential_set_constraint_uses_credential_set_variant() {
        let issuer = CellId::from_bytes([7u8; 32]);
        let constraint = credential_set_constraint(issuer, &kyc_schema());
        match constraint {
            StateConstraint::SenderAuthorized {
                set:
                    AuthorizedSet::CredentialSet {
                        issuer_cell,
                        credential_schema_id,
                    },
            } => {
                assert_eq!(issuer_cell, *CellId::from_bytes([7u8; 32]).as_bytes());
                assert_eq!(credential_schema_id, schema_commitment(&kyc_schema()));
            }
            other => panic!("expected CredentialSet variant, got {other:?}"),
        }
    }

    #[test]
    fn credential_set_predicate_matches_constraint_commitment() {
        // Cross-app dispatch contract: the witness-predicate commitment
        // an Action carries MUST equal the AuthorizedSet commitment the
        // cell program resolves to. Otherwise the executor cannot
        // dispatch deterministically.
        let issuer = CellId::from_bytes([11u8; 32]);
        let schema = kyc_schema();
        let pred = credential_set_predicate(issuer, &schema, 0);
        let cset_commit = credential_set_commitment(issuer, &schema);
        assert_eq!(pred.commitment, cset_commit);

        // And it also matches the cell-side AuthorizedSet helper.
        let from_authset = AuthorizedSet::credential_set_commitment(
            issuer.as_bytes(),
            &schema_commitment(&schema),
        );
        assert_eq!(pred.commitment, from_authset);
    }
}
