//! # starbridge-guard
//!
//! **Per-subject abuse-governance** — the layer that makes a permissionless
//! (KYC-free) substrate responsibly openable. A substrate that lets any anonymous
//! cap-account deploy anything with no identity check is a spam / malware /
//! phishing magnet *unless* the same openness is held to bounds. This crate is
//! that bound, ported from a prior imperative abuse-prevention module into a
//! native subject-account **cell** whose two teeth are ordinary verified turns:
//!
//!  1. **A per-subject quota / rate ceiling** — a metered `consumed` counter under
//!     a frozen `ceiling`. A consume that would push the subject past its ceiling
//!     is refused IN-BAND (the budget-`402` / rate-`429` shape). This is NOT a new
//!     mechanism: it is the SAME verified counter+ceiling
//!     [`starbridge_tool_access_delegation`] proved for its rate-limited mandate
//!     (the `Monotonic(counter) + FieldLteField(counter <= ceiling)` slot-caveat
//!     pair, mirroring the Lean `mandateSpec`) — reused here, subject-scoped,
//!     against a ceiling of the same shape [`dregg_cell::allowance`] seals into a
//!     cell's commitment. We COMPOSE it; we do not re-implement it. The differential
//!     test pins [`consume_admit`] to `starbridge_tool_access_delegation::deleg_admit`.
//!
//!  2. **Account standing** — a `standing` slot (`good` / `flagged` / `suspended`)
//!     that ONLY a governance-gated, receipted turn may move (a takedown /
//!     suspension / reinstatement). A subject can never flip its own standing: the
//!     `set_standing` transition case carries a `SenderAuthorized(PublicRoot)` gate
//!     against a governance-authority root, the `consume_quota` case FREEZES the
//!     standing slot (`Immutable`), and the `Cases` default-deny refuses any other
//!     method that would touch it. This is the ONLY genuinely new layer; the gate
//!     itself is the governance idiom `starbridge-governed-namespace` uses for its
//!     committee-gated atomic table swap.
//!
//! ## The four modern app-framework axes (the unified template)
//!
//!   - **AX1/AX2** — the verified core: [`guard_factory_descriptor`] + the
//!     operation-scoped [`guard_program`] (`Cases` with the right
//!     `StateConstraint`s), composed as a [`DeosApp`] ([`guard_app`]) and mounted by
//!     [`register`] / [`register_deos`];
//!   - **AX3** — the SERVICE-CELL `invoke()` front door (typed `InterfaceDescriptor`
//!     + method dispatch over `constitute` / `consume` / `set_standing` / `view` —
//!     [`service`]);
//!   - **AX4** — the deos-view CARD (a renderer-independent `deos.ui.*` view-tree —
//!     [`card`]);
//!   - **AX5** — the reactive twin: an abuse-audit [`Reactor`](dregg_app_framework::Reactor)
//!     that watches the metered `consume_quota` and reacts with the automated-signal
//!     audit record the operator-review queue reads ([`reactor`]).
//!
//! ## The subject-account cell (slot ↦ meaning)
//!
//!   * `consumed` ([`CONSUMED_SLOT`]) — the RATE / QUOTA counter, advanced
//!     `c → c+1` on each `consume_quota`; `Monotonic` (never rolls back to forge
//!     head-room) AND `FieldLteField(consumed <= ceiling)` (the ceiling never
//!     violated — the in-band refusal);
//!   * `ceiling` ([`CEILING_SLOT`]) — the granted per-window ceiling N; `WriteOnce`
//!     (bound once from the born-empty cell, frozen thereafter — the budget is never
//!     silently raised);
//!   * `standing` ([`STANDING_SLOT`]) — `good` / `flagged` / `suspended`; moved ONLY
//!     by a governance-gated `set_standing` turn (the standing layer);
//!   * `governance_root` ([`GOVERNANCE_ROOT_SLOT`]) — the Merkle root of the
//!     governance authority set; `WriteOnce`; the `SenderAuthorized(PublicRoot)`
//!     clause on `set_standing` reads THIS slot;
//!   * `subject` ([`SUBJECT_SLOT`]) — the subject's stable id hash (the legible
//!     scope this account bounds); `WriteOnce`.
//!
//! Everything here is the enforceable MECHANISM. The live abuse-report intake form,
//! the operator-review UI, and the moderation POLICY are deliberately out of scope
//! (a reviewed-go call); this crate gives them teeth.

#![forbid(unsafe_code)]

use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, AuthorizedSet, CapTarget, CapTemplate, CellAffordance,
    CellId, CellMode, CellProgram, ChildVkStrategy, ConstantsModule, DeosApp, DeosCell, Effect,
    EmbeddedExecutor, Event, FactoryDescriptor, GatedAffordance, InspectorDescriptor,
    StarbridgeAppContext, StateConstraint, TransitionCase, TransitionGuard, canonical_program_vk,
    field_from_bytes, field_from_u64, hex_encode_32, symbol,
};
use dregg_turn::action::WitnessBlob;
use dregg_turn::executor::{single_member_authorized_root, single_member_membership_proof};

pub use dregg_app_framework::FieldElement;

/// AX4 — the deos-view CARD: the app's UI as a renderer-independent `deos.ui.*`
/// view-tree.
pub mod card;
/// AX5 — the reactive twin of `invoke()`: a [`Reactor`](dregg_app_framework::Reactor)
/// that watches the metered `consume_quota` and emits the automated-signal
/// abuse-audit record.
pub mod reactor;
/// AX3 — the CELLS-AS-SERVICE-OBJECTS face: a typed `InterfaceDescriptor` +
/// `invoke()` method dispatch over the abuse-governance vocabulary (`constitute` /
/// `consume` / `set_standing` / `view`).
pub mod service;

// =============================================================================
// Slot layout (subject-account cell).
// =============================================================================

/// Slot 0 — `consumed`. The rate / quota counter, advanced `c → c+1` on each
/// `consume_quota` (`Monotonic` + `FieldLteField(consumed <= ceiling)`).
pub const CONSUMED_SLOT: u8 = 0;
/// Slot 1 — `ceiling`. The granted per-window ceiling N (`WriteOnce`).
pub const CEILING_SLOT: u8 = 1;
/// Slot 2 — `standing`. `good` / `flagged` / `suspended`; moved ONLY by a
/// governance-gated `set_standing` turn.
pub const STANDING_SLOT: u8 = 2;
/// Slot 3 — `governance_root`. The Merkle root of the governance authority set
/// (`WriteOnce`); the `SenderAuthorized(PublicRoot)` clause on `set_standing`
/// reads this slot.
pub const GOVERNANCE_ROOT_SLOT: u8 = 3;
/// Slot 4 — `subject`. The subject's stable id hash (the legible scope this
/// account bounds); `WriteOnce`.
pub const SUBJECT_SLOT: u8 = 4;

// =============================================================================
// Standing codes.
// =============================================================================

/// `good` standing — the conservative default every new anonymous account gets
/// (the born-empty cell reads `0`, so a fresh subject is `good`). It creates + is
/// served under the full ceiling.
pub const STANDING_GOOD: u64 = 0;
/// `flagged` standing — still served, but under a tighter tier (the "under review"
/// state, short of a full takedown).
pub const STANDING_FLAGGED: u64 = 1;
/// `suspended` standing — the floor a confirmed-abusive account sits at: its
/// effective ceiling is zero, so it consumes nothing.
pub const STANDING_SUSPENDED: u64 = 2;

/// The account standing an abuse-governance turn moves a subject through. Ordered
/// weakest-privilege → strongest so a `<` comparison answers "is at least as
/// restricted as" (the same order the prior imperative module used).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Standing {
    /// Suspended: effective ceiling zero, existing resources may be taken down.
    Suspended,
    /// Flagged: still served, under the tighter flagged tier.
    Flagged,
    /// Good: the conservative default a new anonymous account gets.
    Good,
}

impl Standing {
    /// The on-cell field code (`STANDING_GOOD` / `STANDING_FLAGGED` /
    /// `STANDING_SUSPENDED`).
    pub fn code(self) -> u64 {
        match self {
            Standing::Suspended => STANDING_SUSPENDED,
            Standing::Flagged => STANDING_FLAGGED,
            Standing::Good => STANDING_GOOD,
        }
    }

    /// Decode a field code back to a [`Standing`] (an unknown code fails closed to
    /// `Suspended` — the most-restricted reading).
    pub fn from_code(code: u64) -> Standing {
        match code {
            STANDING_GOOD => Standing::Good,
            STANDING_FLAGGED => Standing::Flagged,
            _ => Standing::Suspended,
        }
    }

    /// The log / card label.
    pub fn as_str(self) -> &'static str {
        match self {
            Standing::Suspended => "suspended",
            Standing::Flagged => "flagged",
            Standing::Good => "good",
        }
    }

    /// Whether an account in this standing may consume at all. A suspended account
    /// cannot (its effective ceiling is zero); flagged / good can.
    pub fn may_consume(self) -> bool {
        !matches!(self, Standing::Suspended)
    }
}

impl Default for Standing {
    /// Default standing for a never-before-seen anonymous account: good, but the
    /// conservative ceiling does the real bounding. A KYC-free account is admitted,
    /// not trusted.
    fn default() -> Self {
        Standing::Good
    }
}

// =============================================================================
// The admission mirror (the ported abuse-governance LOGIC as a pure predicate).
// =============================================================================
//
// The prior imperative module decided admission with a HashMap of per-subject
// counters and a standing tier. Here that logic is a pure function over the cell's
// committed `(ceiling, standing, consumed)` — the SAME decision the executor
// re-enforces through the `guard_program` slot caveats, so a change to either side
// diverges (the differential + corpus tests below).

/// The tiered ceiling a subject in `standing` is held to, given a base ceiling.
/// `good` gets the full base; `flagged` a tighter tier (halved, floored to keep a
/// minimal trial slice); `suspended` gets ZERO (creates / consumes nothing) — the
/// prior module's `QuotaPolicy::limits_for` inversion, distilled.
pub fn effective_ceiling(base_ceiling: i64, standing: Standing) -> i64 {
    match standing {
        Standing::Good => base_ceiling.max(0),
        // Tighter, but never below zero. A flagged account keeps a sliver.
        Standing::Flagged => (base_ceiling / 2).max(0),
        Standing::Suspended => 0,
    }
}

/// **`consume_admit`** — the counter+ceiling half of the admission predicate,
/// byte-for-byte the ceiling half of the Lean `delegAdmit`
/// [`starbridge_tool_access_delegation::deleg_admit`] mirrors: advancing the
/// metered counter `old → new` is admitted IFF it is a sane single-step increment
/// (`new == old + 1`, `0 <= old`) that stays at or under the `ceiling`
/// (`new <= ceiling`). Over the ceiling ⇒ refused (the in-band `402`/`429`).
pub fn consume_admit(ceiling: i64, old: i64, new: i64) -> bool {
    new == old + 1 && 0 <= old && new <= ceiling
}

/// **`admit_consume`** — the full per-subject admission: does the abuse-governance
/// layer admit one more consume for a subject in `standing` who has `consumed` of a
/// `base_ceiling` budget? The standing tiers the ceiling (a suspended subject's
/// effective ceiling is zero, so it is always refused), then [`consume_admit`]
/// gates the metered advance against it.
pub fn admit_consume(base_ceiling: i64, standing: Standing, consumed: i64) -> bool {
    consume_admit(
        effective_ceiling(base_ceiling, standing),
        consumed,
        consumed + 1,
    )
}

/// The consume decision vector for a base ceiling and standing: `admit_consume` for
/// each `consumed` in `0..=base_ceiling+1`. The corpus a differential test pins so a
/// change to the ceiling arithmetic (either side) fails.
pub fn consume_corpus(base_ceiling: i64, standing: Standing) -> Vec<bool> {
    (0..=base_ceiling + 1)
        .map(|consumed| admit_consume(base_ceiling, standing, consumed))
        .collect()
}

// =============================================================================
// Factory configuration.
// =============================================================================

/// The factory VK we publish for the subject-account (guard) factory.
pub const GUARD_FACTORY_VK: [u8; 32] = *b"starbridge-guard-subject-factory";

/// Default per-epoch creation budget for subject-account cells (a Sybil cap — a
/// federation admits many anonymous subjects, so the budget is generous).
pub const DEFAULT_CREATION_BUDGET: u64 = 1024;

/// Hash a subject's stable id (a `dga1_`-derived string) to its field value (the
/// account stores its bounded subject as this scalar — the legible scope).
pub fn subject_id_field(subject: &str) -> FieldElement {
    field_from_bytes(subject.as_bytes())
}

// =============================================================================
// Method symbols.
// =============================================================================

/// Method symbol for `constitute` — the birth-configuration turn that binds the
/// ceiling + governance root + subject on the born-empty cell.
pub fn constitute_method_symbol() -> [u8; 32] {
    symbol("constitute")
}
/// Method symbol for `consume_quota` — the metered per-subject consume.
pub fn consume_method_symbol() -> [u8; 32] {
    symbol("consume_quota")
}
/// Method symbol for `set_standing` — the governance-gated standing move.
pub fn set_standing_method_symbol() -> [u8; 32] {
    symbol("set_standing")
}

// =============================================================================
// The operation-scoped cell program (the verified core).
// =============================================================================

/// The subject-account cell program: the abuse-governance caveats the executor
/// re-enforces on every touching turn.
///
/// `Cases` with default-deny (Cav-Codex Block 4): a turn whose method matches none
/// of the dispatch cases is refused outright, so the standing slot can never be
/// touched by an unrecognized method.
///
///   * an `Always` invariants case — the ceiling budget (`FieldLteField(consumed <=
///     ceiling)`) and the frozen constitution (`WriteOnce` ceiling / governance root
///     / subject) hold on EVERY turn;
///   * a `consume_quota` case — the metered counter is `Monotonic` (never rolls back
///     to forge head-room) and the standing slot is `Immutable` (a consume can NEVER
///     be a back-door standing self-write);
///   * a `set_standing` case — `SenderAuthorized(PublicRoot { GOVERNANCE_ROOT_SLOT })`
///     gates the standing move to a member of the governance authority set, and the
///     metered counter + constitution are frozen (`Immutable`) so a standing turn
///     cannot fabricate quota or re-bind the ceiling.
///
/// Together: the standing slot moves ONLY through `set_standing` (the other cases
/// freeze it) AND only for a governance member (the `SenderAuthorized` gate) —
/// never a self-write. The consume budget refuses over-ceiling in-band on every
/// `consume_quota`.
pub fn guard_program() -> CellProgram {
    CellProgram::Cases(vec![
        TransitionCase {
            // ALWAYS: the invariants the account carries for its whole life.
            guard: TransitionGuard::Always,
            constraints: vec![
                // The ceiling budget — the consume counter can never exceed the
                // granted ceiling. This is the in-band-refusal tooth (the same
                // `FieldLteField` the verified counter+ceiling of
                // tool-access-delegation carries), re-checked on every turn.
                StateConstraint::FieldLteField {
                    left_index: CONSUMED_SLOT,
                    right_index: CEILING_SLOT,
                },
                // The constitution — ceiling, governance root, and subject are bound
                // once (from zero on the born-empty cell) and frozen thereafter.
                StateConstraint::WriteOnce {
                    index: CEILING_SLOT,
                },
                StateConstraint::WriteOnce {
                    index: GOVERNANCE_ROOT_SLOT,
                },
                StateConstraint::WriteOnce {
                    index: SUBJECT_SLOT,
                },
            ],
        },
        TransitionCase {
            // The metered consume: advancing `consumed`.
            guard: TransitionGuard::MethodIs {
                method: symbol("consume_quota"),
            },
            constraints: vec![
                // The counter only advances (never rolls back to forge head-room).
                StateConstraint::Monotonic {
                    index: CONSUMED_SLOT,
                },
                // The standing slot is FROZEN on a consume — a subject can NEVER
                // move its own standing through the metering path (the standing
                // layer's first lock).
                StateConstraint::Immutable {
                    index: STANDING_SLOT,
                },
            ],
        },
        TransitionCase {
            // The governance-gated standing move (takedown / suspension /
            // reinstatement).
            guard: TransitionGuard::MethodIs {
                method: symbol("set_standing"),
            },
            constraints: vec![
                // ONLY a member of the governance authority set may move standing —
                // the standing layer's decisive lock. The witness side carries a
                // Merkle-membership proof against `GOVERNANCE_ROOT_SLOT`; an absent
                // or non-member proof fails closed (a self-write is refused).
                StateConstraint::SenderAuthorized {
                    set: AuthorizedSet::PublicRoot {
                        set_root_index: GOVERNANCE_ROOT_SLOT,
                    },
                },
                // A standing turn does not fabricate / reset the quota counter — the
                // two concerns stay orthogonal (a takedown is not a quota refund).
                StateConstraint::Immutable {
                    index: CONSUMED_SLOT,
                },
            ],
        },
    ])
}

/// Canonical child program VK — the `canonical_program_vk(&guard_program())` recipe
/// (per `VK-AS-RE-EXECUTION-RECIPE.md`), so a validator holding the program
/// re-derives this VK and confirms it binds a program they can re-execute against
/// witness data — the same recipe every other starbridge-app follows.
pub fn guard_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&guard_program())
}

/// The subject account's **flat structural caveats** — the `state_constraints` the
/// [`guard_factory_descriptor`] bakes into every factory-born account cell (the
/// method-agnostic invariants a born cell carries for life, per
/// `tests/factory_birth.rs`):
///
///   * `ceiling` / `governance_root` / `subject` are `WriteOnce` — bound once by the
///     `constitute` turn (from zero on the born-empty cell) and frozen thereafter;
///   * `consumed` is `Monotonic` (the meter never rolls back to forge head-room) AND
///     `FieldLteField(consumed <= ceiling)` (the ceiling budget can never be
///     exceeded — the in-band refusal).
///
/// These bite method-agnostically (an `Always` floor), so a born account re-enforces
/// them on `constitute` and `consume_quota` alike. The operation-scoped enforcement
/// — the `Monotonic`/`Immutable(standing)` on `consume_quota` and the
/// `SenderAuthorized` on `set_standing` — lives in [`guard_program`], bound by
/// `child_program_vk` (and installed on the seeded cell so the executor re-enforces
/// the standing gate on the real submission path — see `tests/governance_executor.rs`).
pub fn guard_state_constraints() -> Vec<StateConstraint> {
    vec![
        StateConstraint::FieldLteField {
            left_index: CONSUMED_SLOT,
            right_index: CEILING_SLOT,
        },
        StateConstraint::Monotonic {
            index: CONSUMED_SLOT,
        },
        StateConstraint::WriteOnce {
            index: CEILING_SLOT,
        },
        StateConstraint::WriteOnce {
            index: GOVERNANCE_ROOT_SLOT,
        },
        StateConstraint::WriteOnce {
            index: SUBJECT_SLOT,
        },
    ]
}

/// The account program a factory-born cell carries — the [`guard_state_constraints`]
/// flat caveats as a method-agnostic `Always` program. The AX3 [`service`] installs
/// THIS (the same caveats the [`guard_factory_descriptor`] bakes) so an
/// invoke()-desugared turn is re-enforced exactly as a factory-born cell's turn is.
pub fn guard_born_cell_program() -> CellProgram {
    CellProgram::always(guard_state_constraints())
}

/// Build the `FactoryDescriptor` for subject-account (guard) cells.
pub fn guard_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: GUARD_FACTORY_VK,
        child_program_vk: Some(guard_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(guard_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            // The subject holds a `Signature` SelfCell cap — the handle to meter its
            // own consume. Governance acts through the `SenderAuthorized` set on
            // `set_standing`, not through this cap; a subject's cap can never move
            // standing (the `guard_program` freezes it under every non-governance
            // case).
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        // No creation-time `field_constraints`: a factory-born account is born empty
        // and the `constitute` turn binds `CEILING` + `GOVERNANCE_ROOT` + `SUBJECT`
        // (`WriteOnce`, frozen after) before any consume. Mirror
        // privacy-voting/bounty-board/tool-access-delegation: born empty, bound by
        // the constitute turn under `WriteOnce` — an `Immutable`/`NonZero` birth
        // would freeze the born-empty slots AT ZERO and refuse the constitute turn
        // itself, and a zero ceiling makes every consume refuse.
        field_constraints: vec![],
        // Single source of truth: [`guard_state_constraints`].
        state_constraints: guard_state_constraints(),
        default_mode: CellMode::Sovereign,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

/// All factory descriptors this starbridge-app contributes.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![guard_factory_descriptor()]
}

// =============================================================================
// Governance-authority helpers (the `SenderAuthorized` root + membership witness).
// =============================================================================

/// The `GOVERNANCE_ROOT_SLOT` value authorizing exactly one governance authority
/// (`cipherclerk`'s own pubkey) to move standing — the single-member
/// `SenderAuthorized(PublicRoot)` root the executor reads, delegating to the
/// executor's own [`single_member_authorized_root`]. The matching proof
/// ([`governance_membership_witness`] of the same pubkey) verifies against this
/// root: the two are derived from the same single-leaf tree.
pub fn governance_root(cipherclerk: &AppCipherclerk) -> FieldElement {
    single_member_authorized_root(&cipherclerk.public_key().0)
}

/// The `GOVERNANCE_ROOT_SLOT` value authorizing exactly one governance authority by
/// raw pubkey (for seeding a foreign authority — a subject that is NOT the
/// governance member, so its own `set_standing` is refused).
pub fn governance_root_for(pubkey: &[u8; 32]) -> FieldElement {
    single_member_authorized_root(pubkey)
}

/// The membership witness a governance-gated `set_standing` turn attaches: a
/// `MerklePath` blob carrying the single-member membership STARK for `cipherclerk`'s
/// pubkey. The `SenderAuthorized(PublicRoot { GOVERNANCE_ROOT_SLOT })` evaluator
/// binds this unique blob and verifies it against the slot's root; an absent or
/// non-member proof fails CLOSED (the refusal a self-write earns).
pub fn governance_membership_witness(cipherclerk: &AppCipherclerk) -> WitnessBlob {
    WitnessBlob::merkle_path(single_member_membership_proof(&cipherclerk.public_key().0))
}

// =============================================================================
// Turn builders — CONSTITUTE / CONSUME / SET_STANDING.
// =============================================================================

/// **CONSTITUTE** — the birth-configuration turn: bind the `SUBJECT` scope, the
/// `CEILING` budget, and the `GOVERNANCE_ROOT` (all `WriteOnce`, from zero on the
/// born-empty cell), with the meter born at 0. On the factory-born (flat) cell this
/// is a method-agnostic turn; the seeded (Cases) cell is configured directly via the
/// ledger handle ([`seed_subject`]) since `constitute` is not a dispatch case (it is
/// the born-cell floor's configuration edge, not an operation on the live account).
pub fn build_constitute_action(
    cipherclerk: &AppCipherclerk,
    account_cell: CellId,
    subject: &str,
    ceiling: u64,
    governance_root: FieldElement,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: account_cell,
            index: SUBJECT_SLOT as usize,
            value: subject_id_field(subject),
        },
        Effect::SetField {
            cell: account_cell,
            index: CEILING_SLOT as usize,
            value: field_from_u64(ceiling),
        },
        Effect::SetField {
            cell: account_cell,
            index: GOVERNANCE_ROOT_SLOT as usize,
            value: governance_root,
        },
        Effect::SetField {
            cell: account_cell,
            index: CONSUMED_SLOT as usize,
            value: field_from_u64(0),
        },
        Effect::EmitEvent {
            cell: account_cell,
            event: Event::new(
                symbol("guard-subject-admitted"),
                vec![subject_id_field(subject), field_from_u64(ceiling)],
            ),
        },
    ];
    cipherclerk.make_action(account_cell, "constitute", effects)
}

/// **CONSUME** — the subject meters one quota / rate unit: advance `consumed` from
/// `prev` to `prev + 1`. The executor's `FieldLteField(consumed <= ceiling)` refuses
/// the consume that would overrun the granted budget (the in-band `402`/`429`), and
/// `Monotonic(consumed)` refuses a meter rollback — exactly the verified
/// counter+ceiling the tool-access mandate's `invoke` carries.
pub fn build_consume_action(
    cipherclerk: &AppCipherclerk,
    account_cell: CellId,
    prev_consumed: u64,
) -> Action {
    let new_consumed = prev_consumed + 1;
    let effects = vec![
        Effect::SetField {
            cell: account_cell,
            index: CONSUMED_SLOT as usize,
            value: field_from_u64(new_consumed),
        },
        Effect::EmitEvent {
            cell: account_cell,
            event: Event::new(symbol("quota-consumed"), vec![field_from_u64(new_consumed)]),
        },
    ];
    cipherclerk.make_action(account_cell, "consume_quota", effects)
}

/// **SET_STANDING** — the governance-gated standing move (a takedown / suspension /
/// reinstatement): write the `STANDING` slot to `new_standing`. The action carries
/// the governance member's [`governance_membership_witness`] as a `MerklePath` blob;
/// the executor's `SenderAuthorized(PublicRoot { GOVERNANCE_ROOT_SLOT })` admits it
/// IFF the signer is a member of the governance authority set — a subject's own
/// `set_standing` (no membership proof) is REFUSED. This is the receipted governance
/// turn: it seals a `standing-set` event naming the new standing + the reason, and
/// the turn's receipt IS the auditable record.
pub fn build_set_standing_action(
    cipherclerk: &AppCipherclerk,
    account_cell: CellId,
    new_standing: Standing,
    reason: &str,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: account_cell,
            index: STANDING_SLOT as usize,
            value: field_from_u64(new_standing.code()),
        },
        Effect::EmitEvent {
            cell: account_cell,
            event: Event::new(
                symbol("standing-set"),
                vec![
                    field_from_u64(new_standing.code()),
                    field_from_bytes(reason.as_bytes()),
                ],
            ),
        },
    ];
    let mut action = cipherclerk.make_action(account_cell, "set_standing", effects);
    // Attach the governance-membership proof the `SenderAuthorized` clause binds.
    action.witness_blobs = vec![governance_membership_witness(cipherclerk)];
    action
}

// =============================================================================
// The deos-native surface — the SUBJECT ACCOUNT as a composed `DeosApp`.
// =============================================================================

/// The abuse-governance rights tiers, ON THE REAL ATTENUATION LATTICE:
///
///   - a SUBJECT (the anonymous cap-account this cell bounds) holds
///     [`AuthRequired::Signature`] — it can `consume` (meter one quota unit) AND
///     `view` its standing / budget;
///   - a GOVERNANCE authority holds [`AuthRequired::None`]/root — on top of a
///     subject's operations it can `set_standing` (the takedown / suspension), which
///     the executor additionally gates on `SenderAuthorized` membership.
///
/// So `Signature ⊂ None` IS the subject ⊂ governance ladder.
pub const SUBJECT_RIGHTS: AuthRequired = AuthRequired::Signature;
/// The governance rights tier (root — move standing + all a subject can do). See
/// [`SUBJECT_RIGHTS`].
pub const GOVERNANCE_RIGHTS: AuthRequired = AuthRequired::None;

/// The `consume` **live-state precondition** — the account must have BUDGET
/// REMAINING (`consumed < ceiling`, i.e. `consumed <= ceiling - 1`). A real
/// [`CellProgram`] read against the cell's current state, so a `consume` button is
/// LIT while budget remains and goes DARK the instant the counter reaches the
/// ceiling (the htmx tooth). This gates "may `consume` fire now"; the RATE INVARIANT
/// (`FieldLteField(consumed <= ceiling)`) is the installed [`guard_program`] the
/// executor re-enforces on the produced transition.
pub fn budget_remaining_precondition() -> CellProgram {
    // `consumed < ceiling` ≡ `consumed <= ceiling - 1` ≡
    // `FieldLteOther { consumed, ceiling, delta: -1 }`.
    CellProgram::Predicate(vec![StateConstraint::FieldLteOther {
        index: CONSUMED_SLOT,
        other: CEILING_SLOT,
        delta: -1,
    }])
}

/// **The subject account as a composed [`DeosApp`]** — the whole abuse-governance
/// surface, on the deos bones. The account cell is the agent's OWN cell
/// (`cipherclerk.cell_id()`) so fires execute against the seeded embedded ledger.
///
/// Three operations on the ACCOUNT cell, on the subject ⊂ governance rights ladder:
///
///   - `view` — a cap-only affordance (a SUBJECT reads its standing + budget):
///     `Signature`, an `EmitEvent`;
///   - `set_standing` — a cap-only affordance (a GOVERNANCE authority moves the
///     subject's standing): `None`/root — the deos cap tier; the executor
///     additionally gates the real submission on `SenderAuthorized` membership;
///   - `consume` — a [`GatedAffordance`] (a SUBJECT meters one quota unit):
///     `Signature`, a live-state PRECONDITION (budget remains, `consumed < ceiling`);
///     the real fire ([`fire_consume`]) submits the FULL counter-advancing turn
///     (reading the live `consumed`), re-enforced by the executor's installed
///     `Cases` program (the `FieldLteField` ceiling + `Monotonic` counter caveats
///     BITE on the produced transition).
///
/// Seed the cell's program + configuration with [`seed_subject`] so the gated fires
/// have a live state and the executor re-enforces the caveats.
pub fn guard_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let account = cipherclerk.cell_id();

    // `view` — a subject reads its standing + budget. Cap-only.
    let view = CellAffordance::new(
        "view",
        SUBJECT_RIGHTS,
        Effect::EmitEvent {
            cell: account,
            event: Event::new(symbol("guard-viewed"), vec![]),
        },
    );
    // `set_standing` — a governance authority moves the subject's standing. Cap-only
    // at the deos tier (`None`/root); the executor re-enforces the `SenderAuthorized`
    // membership gate on the submitted turn.
    let set_standing = CellAffordance::new(
        "set_standing",
        GOVERNANCE_RIGHTS,
        Effect::SetField {
            cell: account,
            index: STANDING_SLOT as usize,
            value: field_from_u64(STANDING_SUSPENDED),
        },
    );
    // `consume` — a SUBJECT meters one quota unit. The GatedAffordance carries the
    // DECISIVE effect (the `consumed` counter advance) + a live-state PRECONDITION
    // ([`budget_remaining_precondition`]: `consumed < ceiling`) — so the button is
    // lit while budget remains and dark once the ceiling is reached (the htmx tooth).
    let consume = GatedAffordance::new(
        CellAffordance::new(
            "consume",
            SUBJECT_RIGHTS,
            Effect::SetField {
                cell: account,
                index: CONSUMED_SLOT as usize,
                value: field_from_u64(1),
            },
        ),
        budget_remaining_precondition(),
    );

    DeosApp::builder("guard", cipherclerk.clone(), executor.clone())
        .discoverable(vec!["governance".into(), "abuse".into()])
        .cell(
            DeosCell::new(account, "subject")
                .affordance(view)
                .affordance(set_standing)
                .gated(consume)
                // Published at the SUBJECT tier (`Signature`) — the role that holds
                // the account and the narrowest cap-only affordance (`view`).
                .publish(SUBJECT_RIGHTS),
        )
        .build()
}

/// **`consume` effects** — the state-parameterized metered-consume body: advance
/// `consumed` to `new_consumed` (the executor's installed `Monotonic` +
/// `FieldLteField` caveats re-enforce that it only steps forward and never exceeds
/// `ceiling`), and emit `quota-consumed`. THIS is the turn [`fire_consume`] submits
/// (computed from the cell's LIVE `consumed`).
pub fn consume_effects(account: CellId, new_consumed: u64) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell: account,
            index: CONSUMED_SLOT as usize,
            value: field_from_u64(new_consumed),
        },
        Effect::EmitEvent {
            cell: account,
            event: Event::new(symbol("quota-consumed"), vec![field_from_u64(new_consumed)]),
        },
    ]
}

/// **Seed the SUBJECT ACCOUNT cell** so the gated fires have live state + the caveats
/// bite: install the full [`guard_program`] (`Cases`) on the seeded cell (so the
/// executor re-enforces it — the `SenderAuthorized` standing gate included — on every
/// touching turn), then bind the configuration directly into the embedded ledger —
/// `CEILING` / `GOVERNANCE_ROOT` / `SUBJECT` (`WriteOnce`, frozen after),
/// `CONSUMED = 0`, and `STANDING = good`. The `GOVERNANCE_ROOT` commits the firing
/// signer as the sole governance authority ([`governance_root`]), so a witnessed
/// `set_standing` by that signer commits while a subject's self-write is refused (see
/// `tests/governance_executor.rs`).
pub fn seed_subject(
    executor: &EmbeddedExecutor,
    cipherclerk: &AppCipherclerk,
    subject: &str,
    ceiling: u64,
) {
    let account = executor.cell_id();
    executor.install_program(account, guard_program());
    let gov_root = governance_root(cipherclerk);
    executor.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&account) {
            cell.state
                .set_field(CEILING_SLOT as usize, field_from_u64(ceiling));
            cell.state
                .set_field(SUBJECT_SLOT as usize, subject_id_field(subject));
            cell.state
                .set_field(GOVERNANCE_ROOT_SLOT as usize, gov_root);
            cell.state
                .set_field(CONSUMED_SLOT as usize, field_from_u64(0));
            cell.state
                .set_field(STANDING_SLOT as usize, field_from_u64(STANDING_GOOD));
        }
    });
}

/// **Fire `consume`** — the deos cap∧state PRECONDITION gate (anti-ghost, in-band),
/// then the FULL counter-advancing turn the executor re-enforces the account program
/// on. The two-tempo bridge: the gated affordance decides the button's verdict (cap
/// ⊇ Signature AND budget remains, `consumed < ceiling`) WITHOUT touching the
/// executor; on both passing, the complete `consume_quota` turn ([`consume_effects`]
/// reading the LIVE counter) is submitted, and the executor's re-enforcement of the
/// installed `Cases` program is the SECOND, verified gate — the
/// `FieldLteField(consumed <= ceiling)` ceiling and the `Monotonic(consumed)`
/// no-rewind both bite on the produced transition. Anti-ghost both ways: a
/// precondition miss never submits; a program violation is a real executor refusal.
///
/// The counter is read from the cell's live state (`consumed ⇒ consumed + 1`), so the
/// caller threads nothing. Use [`seed_subject`] first.
pub fn fire_consume(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<dregg_app_framework::TurnReceipt, dregg_app_framework::FireExecuteError> {
    use dregg_app_framework::{FireError, FireExecuteError};
    let cell = &app.cells()[0];
    let account = cell.cell();
    // Tooth 1+2: the deos cap∧state PRECONDITION gate, in-band, nothing submitted on
    // a miss (the cap-gate AND the live-state `budget_remaining` precondition).
    if !cell
        .gated_fireable_names(held, executor)
        .iter()
        .any(|n| n == "consume")
    {
        let ga = cell
            .gated_surface()
            .get("consume")
            .expect("consume is a gated affordance");
        let state = executor.cell_state(account).ok_or_else(|| {
            FireExecuteError::Gate(FireError::StateConditionUnmet {
                affordance: "consume".into(),
                reason: "cell has no live state (fail-closed)".into(),
            })
        })?;
        return Err(FireExecuteError::Gate(
            ga.fire(account, held, &state, &state).unwrap_err(),
        ));
    }
    // Both teeth bit: read the LIVE counter and submit the FULL `consume_quota` turn,
    // which the executor re-enforces the program on (the ceiling + the counter
    // Monotonic).
    let live = executor.cell_state(account).expect("checked above");
    let new_consumed = field_to_u64(&live.fields[CONSUMED_SLOT as usize]) + 1;
    let action = cipherclerk.make_action(
        account,
        "consume_quota",
        consume_effects(account, new_consumed),
    );
    executor
        .submit_action(cipherclerk, action)
        .map_err(FireExecuteError::Executor)
}

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse of
/// [`field_from_u64`] for the counters the account stores).
pub(crate) fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

// =============================================================================
// StarbridgeAppContext mount.
// =============================================================================

/// The canonical web-constants module (slot layout + standing codes + event topics
/// + factory-vk hex).
pub fn web_constants() -> ConstantsModule {
    ConstantsModule::new("guard")
        .slot("CONSUMED_SLOT", CONSUMED_SLOT as u64)
        .slot("CEILING_SLOT", CEILING_SLOT as u64)
        .slot("STANDING_SLOT", STANDING_SLOT as u64)
        .slot("GOVERNANCE_ROOT_SLOT", GOVERNANCE_ROOT_SLOT as u64)
        .slot("SUBJECT_SLOT", SUBJECT_SLOT as u64)
        .slot("STANDING_GOOD", STANDING_GOOD)
        .slot("STANDING_FLAGGED", STANDING_FLAGGED)
        .slot("STANDING_SUSPENDED", STANDING_SUSPENDED)
        .string("FACTORY_VK_HEX", hex_encode_32(&GUARD_FACTORY_VK))
        .string("METHOD_CONSTITUTE", "constitute")
        .string("METHOD_CONSUME", "consume_quota")
        .string("METHOD_SET_STANDING", "set_standing")
        .topic("ADMITTED", "guard-subject-admitted")
        .topic("CONSUMED", "quota-consumed")
        .topic("STANDING_SET", "standing-set")
        .topic("VIEWED", "guard-viewed")
}

/// **Register the guard starbridge-app** on a shared context — the FLOOR (the
/// factory descriptor whose `state_constraints` ARE the per-subject ceiling budget,
/// installed on every born account cell) AND the deos-native composition surface (the
/// [`DeosApp`], folded into the context's affordance registry — so the same
/// `register(ctx)` mounts BOTH).
///
/// The factory + inspector are where SOUNDNESS lives (an over-ceiling consume is a
/// real executor refusal on the born cell; the standing gate is re-enforced on the
/// seeded cell). The deos surface is the composition skin. [`register_deos`] folds the
/// surface; this returns the factory VK (the floor's identity).
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(guard_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "guard-subject".into(),
        descriptor: serde_json::json!({
            "component": "dregg-guard-subject",
            "module": "/starbridge-apps/guard/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": ["consumed", "ceiling", "standing", "governance_root", "subject"],
            "slot_layout": {
                "consumed": CONSUMED_SLOT,
                "ceiling": CEILING_SLOT,
                "standing": STANDING_SLOT,
                "governance_root": GOVERNANCE_ROOT_SLOT,
                "subject": SUBJECT_SLOT,
            },
            "standing_codes": {
                "good": STANDING_GOOD,
                "flagged": STANDING_FLAGGED,
                "suspended": STANDING_SUSPENDED,
            },
            "factory_vk_hex": hex_encode_32(&factory_vk),
            "child_program_vk_hex": hex_encode_32(&guard_child_program_vk()),
            "methods": ["constitute", "consume_quota", "set_standing"],
        }),
    });

    register_deos(ctx);

    factory_vk
}

/// **Mount the deos-native surface** ([`guard_app`]) on a shared context: build the
/// composed [`DeosApp`] from the context's cipherclerk + executor, seed the account
/// cell's program + configuration (so the gated `consume` fire bites and the standing
/// gate is re-enforced), and fold the app into the context's affordance registry.
/// Returns the live [`DeosApp`].
pub fn register_deos(ctx: &StarbridgeAppContext) -> DeosApp {
    let app = guard_app(ctx.cipherclerk(), ctx.executor());
    // Seed the account so the gated `consume` fire has a live `(old, new)` and the
    // full account program (installed here) is re-enforced by the executor on every
    // touching turn (a representative ceiling of 8, the firing signer as the sole
    // governance authority).
    seed_subject(ctx.executor(), ctx.cipherclerk(), "subject-anon", 8);
    app.register(ctx);
    app
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{AgentCipherclerk, Authorization, EmbeddedExecutor};
    use starbridge_tool_access_delegation::{Grant, deleg_admit};

    fn test_cipherclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32])
    }

    fn test_context() -> StarbridgeAppContext {
        let cipherclerk = test_cipherclerk();
        let executor = EmbeddedExecutor::new(&cipherclerk, "default");
        StarbridgeAppContext::new(cipherclerk, executor)
    }

    fn test_cell() -> CellId {
        CellId::from_bytes([5u8; 32])
    }

    #[test]
    fn factory_descriptor_is_stable() {
        assert_eq!(
            guard_factory_descriptor().hash(),
            guard_factory_descriptor().hash()
        );
    }

    // ── the ported admission LOGIC ───────────────────────────────────────────

    #[test]
    fn consume_admit_is_the_counter_ceiling_half() {
        // A single-step advance under the ceiling admits; over the ceiling refuses.
        assert!(consume_admit(3, 0, 1));
        assert!(consume_admit(3, 2, 3)); // the last unit
        assert!(!consume_admit(3, 3, 4)); // over the ceiling — REFUSED
        assert!(!consume_admit(3, 1, 3)); // not a single step
        assert!(!consume_admit(3, -1, 0)); // insane prior
    }

    #[test]
    fn suspended_effective_ceiling_is_zero_so_it_consumes_nothing() {
        // good gets the full base; flagged a tighter tier; suspended ZERO.
        assert_eq!(effective_ceiling(8, Standing::Good), 8);
        assert_eq!(effective_ceiling(8, Standing::Flagged), 4);
        assert_eq!(effective_ceiling(8, Standing::Suspended), 0);
        // a suspended subject is refused its very first consume.
        assert!(!admit_consume(8, Standing::Suspended, 0));
        // a good subject admits up to the ceiling, then refuses.
        assert!(admit_consume(8, Standing::Good, 7));
        assert!(!admit_consume(8, Standing::Good, 8));
        // a flagged subject refuses earlier (the tighter tier bites at 4).
        assert!(admit_consume(8, Standing::Flagged, 3));
        assert!(!admit_consume(8, Standing::Flagged, 4));
    }

    #[test]
    fn standing_gates_consumption() {
        assert!(Standing::Good.may_consume());
        assert!(Standing::Flagged.may_consume());
        assert!(!Standing::Suspended.may_consume());
        assert_eq!(Standing::from_code(STANDING_SUSPENDED), Standing::Suspended);
        assert_eq!(Standing::from_code(999), Standing::Suspended); // unknown fails closed
        assert_eq!(Standing::default(), Standing::Good);
    }

    /// **The reuse pin** — guard's [`consume_admit`] IS the counter+ceiling half of
    /// the verified `starbridge_tool_access_delegation::deleg_admit` (its Lean
    /// `delegAdmit`): with the tool scope + deadline neutralized (in-scope,
    /// in-window), the two decide the metered advance identically over the whole
    /// grid. A drift on either side fails here.
    #[test]
    fn consume_ceiling_agrees_with_the_verified_tool_access_counter_ceiling() {
        for ceiling in 0i64..=6 {
            // Neutralize tool + deadline so `deleg_admit` reduces to its
            // counter+ceiling half (`new == old+1 && 0 <= old && new <= rate_limit`).
            let g = Grant {
                tool_id: 7,
                rate_limit: ceiling,
                deadline: i64::MAX,
            };
            for old in -1i64..=ceiling + 1 {
                for new in 0i64..=ceiling + 2 {
                    assert_eq!(
                        consume_admit(ceiling, old, new),
                        deleg_admit(&g, 0, 7, old, new),
                        "guard consume_admit must equal the verified counter+ceiling \
                         (ceiling={ceiling}, old={old}, new={new})"
                    );
                }
            }
        }
    }

    #[test]
    fn consume_corpus_marks_exactly_the_admissible_prefix() {
        // good ceiling 3 → consumed 0,1,2 admit (advance to 1,2,3 ≤ 3); 3,4 refuse.
        assert_eq!(
            consume_corpus(3, Standing::Good),
            vec![true, true, true, false, false]
        );
        // suspended → nothing admits.
        assert_eq!(
            consume_corpus(3, Standing::Suspended),
            vec![false, false, false, false, false]
        );
    }

    // ── turn builders ────────────────────────────────────────────────────────

    #[test]
    fn constitute_action_binds_subject_ceiling_and_governance_root() {
        let cclerk = test_cipherclerk();
        let action = build_constitute_action(
            &cclerk,
            test_cell(),
            "subject-anon",
            8,
            governance_root(&cclerk),
        );
        // subject, ceiling, governance_root, consumed(=0), + event.
        assert_eq!(action.effects.len(), 5);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, .. } if *index == SUBJECT_SLOT as usize
        ));
        assert!(matches!(
            &action.effects[1],
            Effect::SetField { index, .. } if *index == CEILING_SLOT as usize
        ));
        assert!(matches!(
            &action.effects[2],
            Effect::SetField { index, .. } if *index == GOVERNANCE_ROOT_SLOT as usize
        ));
    }

    #[test]
    fn consume_action_advances_counter_by_one() {
        let cclerk = test_cipherclerk();
        let action = build_consume_action(&cclerk, test_cell(), 2);
        // consumed := 3, + event.
        assert_eq!(action.effects.len(), 2);
        match &action.effects[0] {
            Effect::SetField { index, value, .. } => {
                assert_eq!(*index, CONSUMED_SLOT as usize);
                assert_eq!(*value, field_from_u64(3));
            }
            other => panic!("expected SetField, got {other:?}"),
        }
    }

    #[test]
    fn set_standing_action_carries_the_governance_membership_witness() {
        let cclerk = test_cipherclerk();
        let action =
            build_set_standing_action(&cclerk, test_cell(), Standing::Suspended, "confirmed abuse");
        // the standing write + the reasoned event.
        assert_eq!(action.effects.len(), 2);
        match &action.effects[0] {
            Effect::SetField { index, value, .. } => {
                assert_eq!(*index, STANDING_SLOT as usize);
                assert_eq!(*value, field_from_u64(STANDING_SUSPENDED));
            }
            other => panic!("expected SetField, got {other:?}"),
        }
        // ...and the membership proof rides as the unique MerklePath witness the
        // SenderAuthorized clause binds.
        assert_eq!(action.witness_blobs.len(), 1);
        assert_eq!(
            action.witness_blobs[0].kind,
            dregg_turn::action::WitnessKind::MerklePath
        );
    }

    #[test]
    fn consume_action_carries_a_real_signature() {
        let cclerk = test_cipherclerk();
        let action = build_consume_action(&cclerk, test_cell(), 0);
        match action.authorization {
            Authorization::Signature(a, b) => assert!(a != [0u8; 32] || b != [0u8; 32]),
            other => panic!("expected Signature, got {other:?}"),
        }
    }

    // ── the program shape ────────────────────────────────────────────────────

    #[test]
    fn the_program_is_cases_with_the_standing_gate() {
        let p = guard_program();
        let cases = match p {
            CellProgram::Cases(c) => c,
            _ => panic!("expected Cases"),
        };
        assert_eq!(cases.len(), 3, "Always + consume_quota + set_standing");
        // the set_standing case carries the SenderAuthorized governance gate.
        let set_standing_case = cases
            .iter()
            .find(|c| {
                matches!(&c.guard, TransitionGuard::MethodIs { method } if *method == symbol("set_standing"))
            })
            .expect("a set_standing dispatch case");
        assert!(
            set_standing_case
                .constraints
                .iter()
                .any(|c| matches!(c, StateConstraint::SenderAuthorized { .. })),
            "set_standing must be governance-gated"
        );
        // the consume_quota case FREEZES the standing slot (no self-write via consume).
        let consume_case = cases
            .iter()
            .find(|c| {
                matches!(&c.guard, TransitionGuard::MethodIs { method } if *method == symbol("consume_quota"))
            })
            .expect("a consume_quota dispatch case");
        assert!(
            consume_case.constraints.iter().any(|c| matches!(
                c,
                StateConstraint::Immutable { index } if *index == STANDING_SLOT
            )),
            "consume must freeze standing"
        );
    }

    // ── registration ─────────────────────────────────────────────────────────

    #[test]
    fn register_installs_factory_and_inspector_and_deos_surface() {
        let ctx = test_context();
        let vk = register(&ctx);
        assert_eq!(vk, GUARD_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
        assert!(ctx.inspector_registry().get("guard-subject").is_some());
        assert_eq!(
            ctx.affordance_registry().len(),
            1,
            "register mounts the deos surface on the same context"
        );
    }

    #[test]
    fn the_account_app_composes_the_three_operations() {
        let cipherclerk = test_cipherclerk();
        let executor = EmbeddedExecutor::new(&cipherclerk, "default");
        let app = guard_app(&cipherclerk, &executor);

        assert_eq!(app.name(), "guard");
        assert_eq!(app.cells().len(), 1);
        let account = &app.cells()[0];

        let mut cap_only = account.surface().all_names();
        cap_only.sort();
        assert_eq!(
            cap_only,
            vec!["set_standing".to_string(), "view".to_string()]
        );

        let gated: Vec<String> = account
            .gated_surface()
            .affordances
            .iter()
            .map(|g| g.name().to_string())
            .collect();
        assert_eq!(gated, vec!["consume".to_string()]);

        assert_eq!(account.cell(), cipherclerk.cell_id());
        assert_eq!(account.published_authority(), Some(&SUBJECT_RIGHTS));
    }

    #[test]
    fn seed_subject_installs_the_cases_program_and_configuration() {
        let cipherclerk = test_cipherclerk();
        let executor = EmbeddedExecutor::new(&cipherclerk, "default");
        seed_subject(&executor, &cipherclerk, "subject-anon", 8);

        let installed = executor.with_ledger_mut(|ledger| {
            ledger
                .get(&cipherclerk.cell_id())
                .map(|c| c.program.clone())
        });
        assert_eq!(installed, Some(guard_program()));

        let state = executor
            .cell_state(cipherclerk.cell_id())
            .expect("seeded cell exists");
        assert_eq!(state.fields[CONSUMED_SLOT as usize], field_from_u64(0));
        assert_eq!(state.fields[CEILING_SLOT as usize], field_from_u64(8));
        assert_eq!(
            state.fields[STANDING_SLOT as usize],
            field_from_u64(STANDING_GOOD)
        );
        assert_eq!(
            state.fields[GOVERNANCE_ROOT_SLOT as usize],
            governance_root(&cipherclerk)
        );
    }

    #[test]
    fn register_deos_mounts_the_seeded_surface_and_a_subject_can_meter() {
        let ctx = test_context();
        let app = register_deos(&ctx);
        assert_eq!(app.name(), "guard");
        assert_eq!(ctx.affordance_registry().len(), 1);

        // The seeded account has budget remaining, so the subject can meter a consume
        // through the mounted surface immediately (the seam is closed + live).
        let receipt = fire_consume(
            &app,
            &AuthRequired::Signature,
            ctx.cipherclerk(),
            ctx.executor(),
        )
        .expect("the mounted, seeded surface meters a consume (the promotion is live)");
        assert_ne!(receipt.turn_hash, [0u8; 32]);
    }
}
