//! # starbridge-edge-mandate — an ACCESS EDGE identity, bound to a budget and a
//! caps mandate, as a VERIFIED CELL.
//!
//! The distribution model is *hosted attach*: instead of a user installing the
//! agent runtime, an operator HOSTS a cap-bounded, budget-bounded, receipted
//! [`dregg_agent`] session and the user ATTACHES over SSH. What decides *who
//! attaches with what authority* is an **edge-identity map** — an SSH public key
//! (the identity at the edge) bound to a dregg **account**, a **budget** ceiling,
//! and a **cap bundle** (the tools/vendors the session may use). This crate makes
//! that map a first-class **mandate cell** on the dregg substrate, not a mutable
//! record in a file.
//!
//! ## The binding, as a mandate cell
//!
//! One enrolled subject is ONE mandate cell. Its committed state binds:
//!
//!   * **identity** — [`SUBJECT_SLOT`] (a digest of the SSH key's type+blob) and
//!     [`ACCOUNT_SLOT`] (a digest of the `dga1_` account the session meters
//!     against). `WriteOnce`: sealed at enrol, frozen for life;
//!   * **budget** — [`BUDGET_SLOT`], the spend ceiling. `WriteOnce`: a live
//!     mandate is never silently widened;
//!   * **caps** — [`CAPS_DIGEST_SLOT`], a digest of the sealed, canonical
//!     **granted tool-set**; the full caps string lives in the committed heap
//!     ([`REC_COLL`]) so the deploy adapter reads it back and a light client
//!     witnesses exactly which tools were granted. `WriteOnce`: the scope cannot
//!     be widened after enrol;
//!   * **spend** — [`SPENT_SLOT`], the running meter. `Monotonic` AND bounded by
//!     the `AffineLe(spent ≤ budget)` gate: an over-budget spend is a REAL
//!     executor refusal, in the fire path;
//!   * **revocation** — [`REVOKED_SLOT`], `0` live / `1` revoked. `Monotonic`
//!     (once revoked, stays revoked — the attach line goes dark);
//!   * **no-replay** — [`EPOCH_SLOT`], `StrictMonotonic` (every witnessed turn
//!     strictly advances).
//!
//! ## The SAME attenuation `starbridge-agent-orchestration` proves
//!
//! The enrol is an **attenuation**: the minted subject mandate is no wider than the
//! operator's HELD grant — `granted ⊑ held` on the exact lattice the sibling
//! [`starbridge-agent-orchestration`](https://docs.rs/starbridge-agent-orchestration)
//! coordinator→worker delegation proves (a tool-set SUBSET ∧ a sub-budget). Here
//! the tool vocabulary is the real [`dregg_agent`] caps grammar (`fs`,
//! `http:HOST`, `pay:VENDOR`, `spend`, `cell:/path`, …) rather than a fixed enum,
//! so [`CapMandate`] mirrors that lattice ([`CapMandate::le`] /
//! [`CapMandate::attenuate`]) over a `BTreeSet<String>` of cap tokens. A request
//! for a tool the operator does not hold is DROPPED; a request for more budget than
//! held is CLAMPED — the mandate that lands in the cell can only ever be a narrowing
//! of the operator's grant (`derive_no_amplify`).
//!
//! The operator's held grant lifts from a [`dregg_auth::Grant`]
//! ([`held_from_grant`]): the grant's `tools` ARE the held cap-set, so "enrol mints
//! a mandate no wider than the grant" is literal.
//!
//! ## Enrol / spend / revoke are witnessed turns
//!
//! * [`enrol`] seals the attenuated mandate + the enrolment record into a cell;
//! * [`spend`] draws the meter (refused past the sub-budget, two gates that agree:
//!   the off-ledger pre-check here AND the executor's `AffineLe`);
//! * [`revoke`] flips [`REVOKED_SLOT`] (the slot the adapter reads to go dark).
//!
//! Each has a pure `Cell` form (unit-testable / seed) and a verified-turn form
//! (the `*_effects` / `build_*_action` builders + the [`service`] `invoke()` front
//! door), so the executor re-enforces the invariants on every real turn.
//!
//! ## The `authorized_keys` adapter is a PURE FUNCTION of the cell
//!
//! The deploy side is a thin **adapter** ([`authorized_keys_line`]): a pure
//! function from a mandate cell to one OpenSSH `authorized_keys` forced-command
//! line that drops the connecting key into ITS confined `dregg-agent attach`
//! session — scoped to the cell's account + budget + caps, `restrict`ed to the
//! REPL. It reads ONLY committed cell state; a revoked mandate yields no line. It
//! is substrate-general — it names the native `dregg-agent` attach binary, nothing
//! deployment-specific.
//!
//! ## The four axes (the unified starbridge-app template)
//!
//!   * the verified CORE — the [`FactoryDescriptor`] + [`mandate_cell_program`]
//!     (this file): the identity/budget/caps invariants the executor re-enforces;
//!   * the SERVICE-CELL `invoke()` front door ([`service`]): a typed
//!     `InterfaceDescriptor` (`enrol` / `spend` / `revoke` / `view`);
//!   * the deos-view CARD ([`card`]): the mandate dashboard as a `deos.ui.*` tree.
//!
//! ## Honest gaps (what this is, and is not)
//!
//! This is the faithful port of the IDENTITY→BUDGET→CAPS binding + the
//! `authorized_keys` lowering onto verified cells. The prior imperative module's
//! unwired per-tenant OS-isolation scaffolding is DROPPED — the hosted posture here
//! is enforced the honest way it always was: [`Confinement::Hosted`] refuses a raw
//! `shell` at enrol (a hosted box holds the operator's keys; a shell is restored
//! only behind real per-tenant OS isolation, which is a deploy concern, not this
//! crate's). Standing up the live SSH edge (a real `sshd` whose
//! `AuthorizedKeysCommand` serves [`authorized_keys`]) is the reviewed deploy step;
//! the forced-command generation + the per-subject confinement are proven here.

#![forbid(unsafe_code)]

use std::collections::BTreeSet;

use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellId, CellMode, CellProgram,
    ChildVkStrategy, ConstantsModule, Effect, EmbeddedExecutor, Event, FactoryDescriptor,
    InspectorDescriptor, StarbridgeAppContext, StateConstraint, canonical_program_vk,
    hex_encode_32, symbol,
};
pub use dregg_app_framework::{FieldElement, field_from_bytes, field_from_u64};

use dregg_agent::session::{Confinement, parse_caps_confined};
use dregg_auth::Grant;
use dregg_cell::Cell;

/// The deos-view CARD: the mandate dashboard as a renderer-independent view-tree.
pub mod card;
/// The CELLS-AS-SERVICE-OBJECTS face: a typed `InterfaceDescriptor` + `invoke()`
/// dispatch over `enrol` / `spend` / `revoke` / `view`.
pub mod service;

// =============================================================================
// §1 — The CAP MANDATE: the attenuation lattice (tool-set ⊆ held ∧ sub-budget),
// the Rust image of the `starbridge-agent-orchestration` coordinator→worker
// `keep`-attenuation, re-pointed at an access-edge subject and the real
// `dregg-agent` caps vocabulary (string tokens, not a fixed enum).
// =============================================================================

/// A **cap mandate** — the authority an access-edge subject holds: the caps
/// (tool-set SCOPE) it may use, the `budget` (spend CEILING) it may draw, and the
/// `subject` label (the account it is scoped to). A mandate is an element of a
/// lattice ordered by attenuation: `granted ⊑ held` ([`CapMandate::le`]) iff the
/// granted caps are a SUBSET and the granted budget is NO LARGER.
/// [`CapMandate::attenuate`] produces a mandate `⊑` the original — never wider.
///
/// This is the same attenuation triple `starbridge-agent-orchestration`'s
/// `Mandate` proves, over the real [`dregg_agent`] caps grammar: each element of
/// [`CapMandate::caps`] is a caps token (`fs`, `http:api.github.com`,
/// `pay:openai`, `spend`, `cell:/path`, …), so the SUBSET order IS the tool-scope
/// order and a subject can only ever hold caps the operator was willing to grant.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CapMandate {
    /// The granted caps (the tool-scope). A subject's set is a subset of the
    /// operator's held set. Sorted (a `BTreeSet`) so the canonical caps string +
    /// its digest are deterministic.
    pub caps: BTreeSet<String>,
    /// The spend ceiling in USD-cents (the conserved budget the `AffineLe` gate
    /// bounds the running meter by). No larger than the operator's held budget.
    pub budget: u64,
    /// The subject the mandate is scoped to (the `dga1_` account label — also the
    /// meter subject the hosted session derives from).
    pub subject: String,
}

impl CapMandate {
    /// The operator's own (broad) **held** mandate: all the caps it is willing to
    /// delegate, the full budget ceiling it will underwrite, and its own label.
    pub fn held<I, S>(caps: I, budget: u64, subject: &str) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        Self {
            caps: caps.into_iter().map(Into::into).collect(),
            budget,
            subject: subject.to_string(),
        }
    }

    /// **`granted ⊑ held`** — does `self` (the granted/subject mandate) sit BELOW
    /// `held` (the operator's) in the attenuation lattice? True iff
    /// `self.caps ⊆ held.caps` AND `self.budget <= held.budget`. (The subject label
    /// is not part of the order — the operator scopes a subject to any account it
    /// likes; what cannot be amplified is the caps and the budget.) The Rust image
    /// of `agent-orchestration`'s `Mandate::le` /
    /// `worker_authority_subset_orchestrator`.
    pub fn le(&self, held: &CapMandate) -> bool {
        self.caps.is_subset(&held.caps) && self.budget <= held.budget
    }

    /// **`attenuate`** — derive a subject mandate from `self` (the held grant) by
    /// INTERSECTING the requested caps with what is held, CLAMPING the requested
    /// budget to what is held, and labeling the subject account. The result is
    /// GUARANTEED `⊑ self` (`derive_no_amplify`: the output is always a narrowing).
    /// A request for a cap the operator does not hold is simply absent from the
    /// result; a request for more budget than held is clamped — you can never
    /// amplify past what you hold.
    pub fn attenuate<I, S>(&self, request_caps: I, request_budget: u64, subject: &str) -> CapMandate
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let requested: BTreeSet<String> = request_caps.into_iter().map(Into::into).collect();
        CapMandate {
            caps: requested.intersection(&self.caps).cloned().collect(),
            budget: request_budget.min(self.budget),
            subject: subject.to_string(),
        }
    }

    /// Whether this mandate AUTHORIZES a spend of `cost` given `prior_spent` already
    /// drawn under it: `prior_spent + cost <= self.budget` (the conserved ceiling).
    /// The off-ledger pre-check [`spend`] runs BEFORE building the turn (fail-closed:
    /// it does not even submit an over-budget spend); the executor independently
    /// re-checks the same bound on commit (the real `AffineLe` gate). Two gates that
    /// provably agree.
    pub fn authorizes(&self, prior_spent: u64, cost: u64) -> bool {
        prior_spent.saturating_add(cost) <= self.budget
    }

    /// The canonical caps string — the sorted tokens joined by `,` (the form the
    /// [`authorized_keys_line`] carries and [`CAPS_DIGEST_SLOT`] digests). Empty for
    /// an empty tool-set.
    pub fn canonical_caps(&self) -> String {
        self.caps.iter().cloned().collect::<Vec<_>>().join(",")
    }
}

/// Lift the operator's ergonomic [`dregg_auth::Grant`] into the HELD [`CapMandate`]
/// the enrol attenuates against: the grant's `tools` ARE the held cap-set, and
/// `budget` is the operator's underwritten ceiling. This is why "enrol mints a
/// mandate no wider than the grant" is literal — the enrolled tool-set is a subset
/// of the grant's tools, and the enrolled budget is `<= budget`.
pub fn held_from_grant(grant: &Grant, budget: u64) -> CapMandate {
    CapMandate {
        caps: grant.tools.iter().cloned().collect(),
        budget,
        subject: grant.subject.clone(),
    }
}

// =============================================================================
// §2 — The mandate-cell slot + heap layout.
// =============================================================================

/// Slot 0 — `SUBJECT`. A digest ([`field_from_bytes`]) of the SSH key's identity
/// (type + blob, the comment dropped). `WriteOnce` — the edge identity is sealed at
/// enrol. The "who authenticates the attach".
pub const SUBJECT_SLOT: u8 = 0;
/// Slot 1 — `ACCOUNT`. A digest of the `dga1_` account this subject's session
/// meters against. `WriteOnce`.
pub const ACCOUNT_SLOT: u8 = 1;
/// Slot 2 — `BUDGET`. The spend ceiling in cents. `WriteOnce` — a live mandate is
/// never silently widened. The conserved bound the `AffineLe` gate sums against.
pub const BUDGET_SLOT: u8 = 2;
/// Slot 3 — `SPENT`. The running cumulative spend. `Monotonic` (never rolled back)
/// AND bounded by `AffineLe(spent - budget <= 0)`: an over-budget spend is refused.
pub const SPENT_SLOT: u8 = 3;
/// Slot 4 — `CAPS_DIGEST`. A digest of the sealed canonical granted caps string
/// (the full string lives in the committed heap, [`REC_CAPS`]). `WriteOnce` — the
/// tool-scope cannot be widened after enrol.
pub const CAPS_DIGEST_SLOT: u8 = 4;
/// Slot 5 — `REVOKED`. `0` = live, `1` = revoked. `Monotonic` (once revoked, stays
/// revoked — the attach line goes dark). The kill switch the adapter reads.
pub const REVOKED_SLOT: u8 = 5;
/// Slot 6 — `EPOCH`. The strictly-monotone witnessed-turn counter (no replay).
/// `StrictMonotonic`.
pub const EPOCH_SLOT: u8 = 6;

/// The committed-heap collection id holding the deploy-facing **enrolment record**
/// strings (account / ssh-pubkey / caps / brain), folded into the cell's state
/// commitment so a light client witnesses exactly what authority was granted and
/// the [`authorized_keys_line`] adapter reads them back. Chosen high to avoid
/// colliding with any application heap collection.
pub const REC_COLL: u32 = 0x0000_ED6E; // "EDGE"

/// Heap base key (in [`REC_COLL`]) — the `dga1_` account string.
pub const REC_ACCOUNT: u32 = 0;
/// Heap base key (in [`REC_COLL`]) — the full SSH public key line (type blob
/// comment), trimmed. The identity that rides at the end of the attach line.
pub const REC_SSHKEY: u32 = 64;
/// Heap base key (in [`REC_COLL`]) — the canonical granted caps string.
pub const REC_CAPS: u32 = 128;
/// Heap base key (in [`REC_COLL`]) — the session brain tag (may be empty).
pub const REC_BRAIN: u32 = 192;

// =============================================================================
// §3 — Field / string codecs (over the committed cell heap).
// =============================================================================

/// Read a `u64` from the trailing 8 big-endian bytes of a field element (the
/// inverse of [`field_from_u64`]).
pub fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

/// Store a UTF-8 string into the committed heap at `(REC_COLL, base)`: the byte
/// length at `base`, then 32-byte raw chunks at `base + 1 + i`. The inverse of
/// [`load_str`]. (Heap values are opaque 32-byte field elements — arbitrary bytes,
/// like a `CellId` tag — so a chunked string round-trips exactly.)
fn store_str(cell: &mut Cell, base: u32, s: &str) {
    let bytes = s.as_bytes();
    cell.state
        .set_heap(REC_COLL, base, field_from_u64(bytes.len() as u64));
    for (i, chunk) in bytes.chunks(32).enumerate() {
        let mut f = [0u8; 32];
        f[..chunk.len()].copy_from_slice(chunk);
        cell.state.set_heap(REC_COLL, base + 1 + i as u32, f);
    }
}

/// Read a UTF-8 string stored by [`store_str`] from `(REC_COLL, base)`. `None` if
/// the length key is absent (never enrolled) or the bytes are not valid UTF-8.
fn load_str(cell: &Cell, base: u32) -> Option<String> {
    let len = field_to_u64(&cell.state.get_heap(REC_COLL, base)?) as usize;
    let mut out = Vec::with_capacity(len);
    let mut i = 0u32;
    while out.len() < len {
        let f = cell.state.get_heap(REC_COLL, base + 1 + i)?;
        let take = (len - out.len()).min(32);
        out.extend_from_slice(&f[..take]);
        i += 1;
    }
    String::from_utf8(out).ok()
}

// =============================================================================
// §4 — The verified core: CellProgram + FactoryDescriptor.
// =============================================================================

/// The **life-of-mandate invariants** the executor re-enforces on every touching
/// turn:
///
///   * **budget** (`AffineLe`): `spent - budget <= 0` — the running meter never
///     exceeds the sealed ceiling. An over-budget spend is a REAL refusal, in the
///     fire path;
///   * **write-once identity/economics** (`WriteOnce SUBJECT/ACCOUNT/BUDGET/
///     CAPS_DIGEST`): bound once at enrol (from zero), frozen thereafter — the edge
///     identity, the metered account, the ceiling, and the tool-scope cannot be
///     silently re-pointed or WIDENED on a live mandate (born-empty-compatible, so
///     the enrol turn admits the from-zero binds; `Immutable` would freeze at zero
///     and refuse the enrol);
///   * **monotone meter/revocation** (`Monotonic SPENT/REVOKED`): spend only
///     accumulates; a revoked mandate stays revoked;
///   * **no replay** (`StrictMonotonic EPOCH`): every touching turn strictly
///     advances the epoch.
pub fn mandate_constraints() -> Vec<StateConstraint> {
    vec![
        StateConstraint::AffineLe {
            terms: vec![(1, SPENT_SLOT), (-1, BUDGET_SLOT)],
            c: 0,
        },
        StateConstraint::WriteOnce {
            index: SUBJECT_SLOT,
        },
        StateConstraint::WriteOnce {
            index: ACCOUNT_SLOT,
        },
        StateConstraint::WriteOnce { index: BUDGET_SLOT },
        StateConstraint::WriteOnce {
            index: CAPS_DIGEST_SLOT,
        },
        StateConstraint::Monotonic { index: SPENT_SLOT },
        StateConstraint::Monotonic {
            index: REVOKED_SLOT,
        },
        StateConstraint::StrictMonotonic { index: EPOCH_SLOT },
    ]
}

/// The mandate cell program — [`mandate_constraints`] as a `CellProgram::Predicate`
/// re-enforced on EVERY touching turn (the budget gate + the WriteOnce identity/
/// economics + the monotone meter/revocation + the no-replay epoch). A pure
/// invariants program, so every operation the mandate supports — `enrol` / `spend`
/// / `revoke` — is admitted as long as the invariants hold. The service face and
/// the factory install/assume this SAME program (the non-degrading invariant).
pub fn mandate_cell_program() -> CellProgram {
    CellProgram::Predicate(mandate_constraints())
}

/// Canonical child program VK for mandate cells.
pub fn mandate_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&mandate_cell_program())
}

/// The factory VK the operator publishes for edge-mandate cells.
pub const MANDATE_FACTORY_VK: [u8; 32] = *b"starbridge-edge-mandate-factory!";

/// Default per-epoch slot-creation budget (how many subjects the operator enrols).
pub const DEFAULT_CREATION_BUDGET: u64 = 256;

/// The default binary an enrolled key's forced-command invokes — the native
/// `dregg-agent` attach subcommand. A deploy overrides it with an absolute path via
/// the `attach_bin` argument to [`authorized_keys_line`] / [`authorized_keys`].
pub const DEFAULT_ATTACH_BIN: &str = "dregg-agent";

/// Build the [`FactoryDescriptor`] for edge-mandate cells. A factory-born mandate
/// is born EMPTY; the `enrol` turn binds the identity/account/budget/caps-digest
/// (from zero, under `WriteOnce`) before any spend, and the budget gate + monotone
/// meter/revocation + no-replay epoch caveats are installed at birth FOR LIFE.
pub fn mandate_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: MANDATE_FACTORY_VK,
        child_program_vk: Some(mandate_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(mandate_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            // The mandate holds an attenuatable SelfCell cap — the ocap handle the
            // hosted session runs under. Sub-delegation NARROWS it (no amplification).
            target: CapTarget::SelfCell,
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        field_constraints: vec![],
        state_constraints: mandate_constraints(),
        default_mode: CellMode::Sovereign,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

/// All factory descriptors this starbridge-app contributes.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![mandate_factory_descriptor()]
}

// =============================================================================
// §5 — The enrolment request + errors + validation.
// =============================================================================

/// A request to enrol an access-edge subject: the `dga1_` account its session
/// meters against, the SSH public key that authenticates the attach, the requested
/// budget ceiling (cents), the requested caps string, and the session brain tag
/// (may be empty). The minted mandate is the ATTENUATION of this against the
/// operator's held grant — no wider.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct EnrolRequest {
    /// The `dga1_` / account id the session meters + receipts under.
    pub account: String,
    /// The full SSH public key line (`ssh-ed25519 AAAA… comment`).
    pub ssh_pubkey: String,
    /// The requested budget ceiling in USD-cents (clamped to the held budget).
    pub budget_cents: i64,
    /// The requested caps string (validated against the real grant vocabulary under
    /// the hosted posture, then intersected with the held tool-set).
    pub caps: String,
    /// The session brain (`nemotron` / `hermes` / a replay tag). Empty = default.
    pub brain: String,
}

impl EnrolRequest {
    /// A request with the default (empty) brain.
    pub fn new(
        account: impl Into<String>,
        ssh_pubkey: impl Into<String>,
        budget_cents: i64,
        caps: impl Into<String>,
    ) -> Self {
        Self {
            account: account.into(),
            ssh_pubkey: ssh_pubkey.into(),
            budget_cents,
            caps: caps.into(),
            brain: String::new(),
        }
    }

    /// A request selecting the session brain.
    pub fn with_brain(mut self, brain: impl Into<String>) -> Self {
        self.brain = brain.into();
        self
    }
}

/// Why an enrol / spend / revoke was refused — fail-closed, never silent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EdgeMandateError {
    /// The account id was empty.
    EmptyAccount,
    /// The budget was not a positive number of cents.
    BadBudget(i64),
    /// The SSH public key was empty or obviously malformed (not `type base64 …`).
    BadSshKey,
    /// The caps string did not parse against the real grant vocabulary under the
    /// hosted posture (e.g. a raw `shell`, or an unknown token) — carries the
    /// parser's reason.
    BadCaps {
        /// The offending caps string.
        caps: String,
        /// The parser's reason.
        reason: String,
    },
    /// The mandate has been REVOKED — no further spend (the slot was reclaimed).
    Revoked,
    /// A spend would breach the sub-budget: `spent + cost > budget`.
    OverBudget {
        /// The running spend before this draw.
        spent: u64,
        /// The requested draw.
        cost: u64,
        /// The sealed ceiling.
        budget: u64,
    },
}

impl std::fmt::Display for EdgeMandateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EdgeMandateError::EmptyAccount => write!(f, "account id must not be empty"),
            EdgeMandateError::BadBudget(b) => write!(f, "budget must be > 0 cents (got {b})"),
            EdgeMandateError::BadSshKey => write!(
                f,
                "malformed ssh public key (expected `ssh-ed25519 AAAA… [comment]`)"
            ),
            EdgeMandateError::BadCaps { caps, reason } => {
                write!(f, "invalid caps `{caps}`: {reason}")
            }
            EdgeMandateError::Revoked => write!(f, "mandate is revoked: no further spend"),
            EdgeMandateError::OverBudget {
                spent,
                cost,
                budget,
            } => write!(f, "spend {spent}+{cost} would breach sub-budget {budget}"),
        }
    }
}

impl std::error::Error for EdgeMandateError {}

/// A minimal SSH public-key shape check: `type base64blob [comment]`, the type a
/// known key algorithm and the blob non-empty. Not a cryptographic validation — the
/// sshd does that; this catches obvious enrol-time fat-fingers.
pub fn looks_like_ssh_key(s: &str) -> bool {
    let s = s.trim();
    let mut parts = s.split_whitespace();
    let (Some(kind), Some(blob)) = (parts.next(), parts.next()) else {
        return false;
    };
    const KINDS: &[&str] = &[
        "ssh-ed25519",
        "ssh-rsa",
        "ecdsa-sha2-nistp256",
        "ecdsa-sha2-nistp384",
        "ecdsa-sha2-nistp521",
        "sk-ssh-ed25519@openssh.com",
        "sk-ecdsa-sha2-nistp256@openssh.com",
    ];
    KINDS.contains(&kind) && blob.len() >= 16 && blob.bytes().all(|b| b != b'"')
}

/// Normalize an SSH key to its identity (type + blob), dropping the comment, so
/// re-enrol / lookup match regardless of the trailing comment. This is what the
/// [`SUBJECT_SLOT`] digest is taken over.
pub fn normalize_key(s: &str) -> String {
    let mut parts = s.split_whitespace();
    match (parts.next(), parts.next()) {
        (Some(kind), Some(blob)) => format!("{kind} {blob}"),
        _ => s.trim().to_string(),
    }
}

/// Split a caps string into its trimmed, non-empty tokens (the requested tool-set).
fn cap_tokens(caps: &str) -> BTreeSet<String> {
    caps.split(',')
        .map(str::trim)
        .filter(|t| !t.is_empty())
        .map(|t| t.to_string())
        .collect()
}

/// Validate an [`EnrolRequest`] and derive the minted [`CapMandate`] — WITHOUT
/// touching a cell (the pure decision half, so a caller can inspect the mandate the
/// enrol would seal). Fail-closed on each axis:
///
///   * the account is non-empty;
///   * the budget is `> 0`;
///   * the SSH key is well-shaped;
///   * the REQUESTED caps parse against the real [`dregg_agent`] grant vocabulary
///     under [`Confinement::Hosted`] (a raw `shell` is refused at parse — the
///     hosted box holds the operator's keys — as is any unknown token);
///
/// then the requested caps + budget are ATTENUATED against `held`: the minted
/// mandate is `⊑ held` by construction (`derive_no_amplify` — a cap the operator
/// does not hold is dropped, an over-ceiling budget is clamped).
pub fn mint_mandate(held: &CapMandate, req: &EnrolRequest) -> Result<CapMandate, EdgeMandateError> {
    if req.account.trim().is_empty() {
        return Err(EdgeMandateError::EmptyAccount);
    }
    if req.budget_cents <= 0 {
        return Err(EdgeMandateError::BadBudget(req.budget_cents));
    }
    if !looks_like_ssh_key(&req.ssh_pubkey) {
        return Err(EdgeMandateError::BadSshKey);
    }
    // Validate the REQUESTED caps against the real grant vocabulary UNDER THE HOST'S
    // confinement posture, so a bad bundle — or a `shell` cap on a host without
    // per-tenant OS isolation — is rejected at enrol, not at login.
    parse_caps_confined(
        &req.caps,
        "agent:session",
        req.budget_cents,
        "/workdir",
        Confinement::Hosted,
    )
    .map_err(|reason| EdgeMandateError::BadCaps {
        caps: req.caps.clone(),
        reason,
    })?;
    // Attenuate: the minted mandate is `⊑ held` (no amplification).
    Ok(held.attenuate(
        cap_tokens(&req.caps),
        req.budget_cents as u64,
        req.account.trim(),
    ))
}

// =============================================================================
// §6 — Pure Cell operations (unit-testable / executor-seedable).
// =============================================================================

/// **Enrol** a subject on a cell: [`mint_mandate`] the attenuated authority, then
/// SEAL it into the cell — the identity/account/budget/caps-digest scalars +
/// spend=0 + revoked=0 + epoch=1, plus the deploy-facing enrolment record
/// (account / ssh-pubkey / canonical caps / brain) in the committed [`REC_COLL`]
/// heap. After this the cell's commitment binds the whole mandate AND the record.
/// Returns the minted mandate (the one that landed — `⊑ held`). Rejects an invalid
/// request without touching the cell.
pub fn enrol(
    cell: &mut Cell,
    held: &CapMandate,
    req: &EnrolRequest,
) -> Result<CapMandate, EdgeMandateError> {
    let minted = mint_mandate(held, req)?;
    seal_mandate(cell, &minted, req);
    Ok(minted)
}

/// Seal a already-minted [`CapMandate`] + its [`EnrolRequest`] record into `cell`'s
/// committed state (the state-binding half of [`enrol`]). Sets the scalar slots and
/// writes the enrolment-record strings into the [`REC_COLL`] heap.
pub fn seal_mandate(cell: &mut Cell, minted: &CapMandate, req: &EnrolRequest) {
    let caps = minted.canonical_caps();
    let st = &mut cell.state;
    st.set_field(
        SUBJECT_SLOT as usize,
        field_from_bytes(normalize_key(&req.ssh_pubkey).as_bytes()),
    );
    st.set_field(
        ACCOUNT_SLOT as usize,
        field_from_bytes(minted.subject.as_bytes()),
    );
    st.set_field(BUDGET_SLOT as usize, field_from_u64(minted.budget));
    st.set_field(SPENT_SLOT as usize, field_from_u64(0));
    st.set_field(CAPS_DIGEST_SLOT as usize, field_from_bytes(caps.as_bytes()));
    st.set_field(REVOKED_SLOT as usize, field_from_u64(0));
    st.set_field(EPOCH_SLOT as usize, field_from_u64(1));
    // The deploy-facing enrolment record (committed heap): the adapter reads these.
    store_str(cell, REC_ACCOUNT, &minted.subject);
    store_str(cell, REC_SSHKEY, req.ssh_pubkey.trim());
    store_str(cell, REC_CAPS, &caps);
    store_str(cell, REC_BRAIN, req.brain.trim());
}

/// **Spend** `cost` against a mandate cell: draw the running meter, refused
/// fail-closed if the mandate is revoked ([`EdgeMandateError::Revoked`]) or the draw
/// would breach the sealed sub-budget ([`EdgeMandateError::OverBudget`]) — the
/// off-ledger pre-check that provably agrees with the executor's `AffineLe` gate.
/// On success advances [`SPENT_SLOT`] and the no-replay [`EPOCH_SLOT`], and returns
/// the new running spend.
pub fn spend(cell: &mut Cell, cost: u64) -> Result<u64, EdgeMandateError> {
    if is_revoked(cell) {
        return Err(EdgeMandateError::Revoked);
    }
    let budget = budget_of(cell);
    let prior = spent_of(cell);
    if prior.saturating_add(cost) > budget {
        return Err(EdgeMandateError::OverBudget {
            spent: prior,
            cost,
            budget,
        });
    }
    let new_spent = prior + cost;
    let epoch = epoch_of(cell);
    let st = &mut cell.state;
    st.set_field(SPENT_SLOT as usize, field_from_u64(new_spent));
    st.set_field(EPOCH_SLOT as usize, field_from_u64(epoch + 1));
    Ok(new_spent)
}

/// **Revoke** a mandate cell: flip [`REVOKED_SLOT`] to `1` (the kill switch the
/// [`authorized_keys_line`] adapter reads to go dark) and advance the epoch.
/// Idempotent — revoking an already-revoked mandate is a no-op.
pub fn revoke(cell: &mut Cell) {
    if is_revoked(cell) {
        return;
    }
    let epoch = epoch_of(cell);
    let st = &mut cell.state;
    st.set_field(REVOKED_SLOT as usize, field_from_u64(1));
    st.set_field(EPOCH_SLOT as usize, field_from_u64(epoch + 1));
}

// ── Readers ──────────────────────────────────────────────────────────────────

/// The sealed budget ceiling (cents).
pub fn budget_of(cell: &Cell) -> u64 {
    cell.state
        .get_field(BUDGET_SLOT as usize)
        .map(field_to_u64)
        .unwrap_or(0)
}

/// The running cumulative spend.
pub fn spent_of(cell: &Cell) -> u64 {
    cell.state
        .get_field(SPENT_SLOT as usize)
        .map(field_to_u64)
        .unwrap_or(0)
}

/// The remaining headroom (`budget - spent`, saturating).
pub fn headroom_of(cell: &Cell) -> u64 {
    budget_of(cell).saturating_sub(spent_of(cell))
}

/// The no-replay epoch (the witnessed-turn counter).
pub fn epoch_of(cell: &Cell) -> u64 {
    cell.state
        .get_field(EPOCH_SLOT as usize)
        .map(field_to_u64)
        .unwrap_or(0)
}

/// Whether the mandate has been revoked.
pub fn is_revoked(cell: &Cell) -> bool {
    cell.state
        .get_field(REVOKED_SLOT as usize)
        .map(|f| field_to_u64(f) != 0)
        .unwrap_or(false)
}

/// The account this subject's session meters against (from the committed record).
pub fn account_of(cell: &Cell) -> Option<String> {
    load_str(cell, REC_ACCOUNT)
}

/// The full SSH public key line (from the committed record).
pub fn ssh_pubkey_of(cell: &Cell) -> Option<String> {
    load_str(cell, REC_SSHKEY)
}

/// The canonical granted caps string (from the committed record).
pub fn caps_of(cell: &Cell) -> Option<String> {
    load_str(cell, REC_CAPS)
}

/// The session brain tag (from the committed record; empty if none).
pub fn brain_of(cell: &Cell) -> Option<String> {
    load_str(cell, REC_BRAIN)
}

// =============================================================================
// §7 — Verified-turn builders / effects + seed.
// =============================================================================

/// **`enrol` effects** — the scalar binds the enrol turn commits: the
/// identity/account/budget/caps-digest (`WriteOnce`, admitted from zero on this
/// turn), spend=0, revoked=0, epoch 0 -> 1, plus an `edge-mandate-enrolled` record
/// event. (The enrolment-record STRINGS in the [`REC_COLL`] heap are mirrored
/// executor-side via [`mirror_record`] after the turn — there is no heap-write
/// effect, mirroring the sibling execution-lease checkpoint mirror.)
pub fn enrol_effects(cell: CellId, minted: &CapMandate, ssh_pubkey: &str) -> Vec<Effect> {
    let caps = minted.canonical_caps();
    vec![
        Effect::SetField {
            cell,
            index: SUBJECT_SLOT as usize,
            value: field_from_bytes(normalize_key(ssh_pubkey).as_bytes()),
        },
        Effect::SetField {
            cell,
            index: ACCOUNT_SLOT as usize,
            value: field_from_bytes(minted.subject.as_bytes()),
        },
        Effect::SetField {
            cell,
            index: BUDGET_SLOT as usize,
            value: field_from_u64(minted.budget),
        },
        Effect::SetField {
            cell,
            index: SPENT_SLOT as usize,
            value: field_from_u64(0),
        },
        Effect::SetField {
            cell,
            index: CAPS_DIGEST_SLOT as usize,
            value: field_from_bytes(caps.as_bytes()),
        },
        Effect::SetField {
            cell,
            index: REVOKED_SLOT as usize,
            value: field_from_u64(0),
        },
        Effect::SetField {
            cell,
            index: EPOCH_SLOT as usize,
            value: field_from_u64(1),
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(
                symbol("edge-mandate-enrolled"),
                vec![
                    field_from_bytes(minted.subject.as_bytes()),
                    field_from_u64(minted.budget),
                ],
            ),
        },
    ]
}

/// **`spend` effects** — advance the running meter to `new_spent` (`Monotonic`;
/// summed by the `AffineLe` budget gate) and strictly advance `EPOCH` to
/// `new_epoch` (no-replay), plus an `edge-mandate-spent` event binding the `cost`.
/// The executor admits this IFF `new_spent <= budget` (`AffineLe`) — an over-budget
/// spend is REFUSED here, in the fire path.
pub fn spend_effects(cell: CellId, new_spent: u64, cost: u64, new_epoch: u64) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell,
            index: SPENT_SLOT as usize,
            value: field_from_u64(new_spent),
        },
        Effect::SetField {
            cell,
            index: EPOCH_SLOT as usize,
            value: field_from_u64(new_epoch),
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(
                symbol("edge-mandate-spent"),
                vec![field_from_u64(cost), field_from_u64(new_spent)],
            ),
        },
    ]
}

/// **`revoke` effects** — flip `REVOKED` to `1` (`Monotonic`) and strictly advance
/// `EPOCH`, plus an `edge-mandate-revoked` event. After this the adapter's line goes
/// dark; the slot is reclaimed.
pub fn revoke_effects(cell: CellId, new_epoch: u64) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell,
            index: REVOKED_SLOT as usize,
            value: field_from_u64(1),
        },
        Effect::SetField {
            cell,
            index: EPOCH_SLOT as usize,
            value: field_from_u64(new_epoch),
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(symbol("edge-mandate-revoked"), vec![]),
        },
    ]
}

/// Build the signed on-ledger [`Action`] enrolling a subject (the scalar binds).
/// The enrolment-record heap strings are mirrored after commit via [`mirror_record`].
pub fn build_enrol_action(
    cipherclerk: &AppCipherclerk,
    cell: CellId,
    minted: &CapMandate,
    ssh_pubkey: &str,
) -> Action {
    cipherclerk.make_action(cell, "enrol", enrol_effects(cell, minted, ssh_pubkey))
}

/// Build the signed on-ledger [`Action`] for a `spend` of `cost` (advancing the
/// meter to `new_spent` and the epoch to `new_epoch`).
pub fn build_spend_action(
    cipherclerk: &AppCipherclerk,
    cell: CellId,
    new_spent: u64,
    cost: u64,
    new_epoch: u64,
) -> Action {
    cipherclerk.make_action(
        cell,
        "spend",
        spend_effects(cell, new_spent, cost, new_epoch),
    )
}

/// Build the signed on-ledger [`Action`] revoking a mandate (advancing the epoch to
/// `new_epoch`).
pub fn build_revoke_action(cipherclerk: &AppCipherclerk, cell: CellId, new_epoch: u64) -> Action {
    cipherclerk.make_action(cell, "revoke", revoke_effects(cell, new_epoch))
}

/// **Mirror the enrolment record into the committed heap** after a verified
/// [`enrol_effects`] turn bound the scalar slots. Keeps the deploy-facing record
/// (account / ssh-pubkey / canonical caps / brain) — which the [`authorized_keys_line`]
/// adapter reads — in step with the executor-enforced scalars.
pub fn mirror_record(cell: &mut Cell, minted: &CapMandate, req: &EnrolRequest) {
    store_str(cell, REC_ACCOUNT, &minted.subject);
    store_str(cell, REC_SSHKEY, req.ssh_pubkey.trim());
    store_str(cell, REC_CAPS, &minted.canonical_caps());
    store_str(cell, REC_BRAIN, req.brain.trim());
}

/// **Seed a mandate cell** so a verified spend/revoke turn has live state + the
/// invariants bite: install [`mandate_cell_program`] on the executor's own cell
/// (so it re-enforces the budget/economics/monotonicity invariants on every
/// touching turn), then enrol the subject genesis state directly into the embedded
/// ledger. Returns the minted mandate. Mirrors the sibling execution-lease
/// `seed_lease`.
pub fn seed_mandate(
    executor: &EmbeddedExecutor,
    held: &CapMandate,
    req: &EnrolRequest,
) -> Result<CapMandate, EdgeMandateError> {
    let cell = executor.cell_id();
    executor.install_program(cell, mandate_cell_program());
    let mut minted = None;
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&cell) {
            minted = Some(enrol(c, held, req));
        }
    });
    minted.unwrap_or(Err(EdgeMandateError::EmptyAccount))
}

// =============================================================================
// §8 — The authorized_keys ADAPTER: a PURE FUNCTION from a mandate cell to an
// OpenSSH forced-command line. Deploy-side; substrate-general; reads only the
// committed cell state.
// =============================================================================

/// **The `authorized_keys` line for a mandate cell** — a PURE FUNCTION of the
/// committed cell state. It reads the enrolment record (account / ssh-pubkey /
/// caps / brain) + the sealed budget and produces the OpenSSH `authorized_keys`
/// line that drops the connecting key into ITS confined `dregg-agent attach`
/// session: a `command=` forced-command scoped to this account + budget + caps,
/// plus the lock-down options (`restrict` disables agent/port/X11 forwarding
/// fail-closed; `pty` re-enables a terminal so the REPL is usable).
///
/// A **revoked** mandate yields `None` — the line goes dark, the slot reclaimed.
/// A cell that was never enrolled (no record) also yields `None`.
///
/// The forced command IGNORES whatever the client asked to run — except that
/// `dregg-agent attach` reads `SSH_ORIGINAL_COMMAND`, so `ssh acct@host "goal"`
/// runs that one goal non-interactively. The line NEVER carries a raw-shell escape:
/// the caps were validated hosted at enrol (a `shell` cap is refused there).
pub fn authorized_keys_line(cell: &Cell, attach_bin: &str) -> Option<String> {
    if is_revoked(cell) {
        return None;
    }
    let account = account_of(cell)?;
    let ssh = ssh_pubkey_of(cell)?;
    let caps = caps_of(cell).unwrap_or_default();
    let brain = brain_of(cell).unwrap_or_default();
    let budget = budget_of(cell);

    let mut cmd = format!(
        "{attach_bin} attach --account {acct} --budget {budget} --caps {caps}",
        acct = shell_quote(&account),
        caps = shell_quote(&caps),
    );
    if !brain.is_empty() {
        cmd.push_str(" --brain ");
        cmd.push_str(&shell_quote(&brain));
    }
    // The `command="…"` value is double-quoted in authorized_keys; escape any `"`/`\`
    // in it per the OpenSSH rule (a backslash escapes the next char).
    let escaped = cmd.replace('\\', "\\\\").replace('"', "\\\"");
    Some(format!(
        "command=\"{escaped}\",restrict,pty {key}",
        key = ssh.trim()
    ))
}

/// **The full `authorized_keys` content** for a set of mandate cells — a header
/// comment plus one forced-command line per LIVE (non-revoked) enrolled mandate.
/// Drop this at the host agent-user's `~/.ssh/authorized_keys` (or serve it from an
/// `AuthorizedKeysCommand`), and every enrolled key, on login, lands in its OWN
/// confined `dregg-agent attach` session. A pure function of the cells' committed
/// state.
pub fn authorized_keys<'a>(cells: impl IntoIterator<Item = &'a Cell>, attach_bin: &str) -> String {
    let mut s = String::new();
    s.push_str(
        "# Generated by the edge-mandate authorized_keys adapter. Each line drops the\n\
         # connecting key into its OWN cap-bounded, budget-bounded, receipted\n\
         # `dregg-agent attach` session. The forced command + `restrict` make the SSH\n\
         # session BE the agent REPL. A revoked mandate emits no line.\n",
    );
    for cell in cells {
        if let Some(line) = authorized_keys_line(cell, attach_bin) {
            s.push_str(&line);
            s.push('\n');
        }
    }
    s
}

/// Single-quote a value for the forced command (the command runs under the user's
/// login shell). A value containing `'` is wrapped with the `'\''` idiom. Our values
/// (account ids, caps tokens, brain names) are tame, but quote defensively.
fn shell_quote(s: &str) -> String {
    if !s.is_empty()
        && s.bytes()
            .all(|b| b.is_ascii_alphanumeric() || b":._/-,@".contains(&b))
    {
        return s.to_string();
    }
    format!("'{}'", s.replace('\'', "'\\''"))
}

// =============================================================================
// §9 — StarbridgeAppContext mount + web constants.
// =============================================================================

/// The canonical web-constants module — the slot layout + event topics + factory
/// VK the JS surface is rendered from.
pub fn web_constants() -> ConstantsModule {
    ConstantsModule::new("edge-mandate")
        .slot("SUBJECT_SLOT", SUBJECT_SLOT as u64)
        .slot("ACCOUNT_SLOT", ACCOUNT_SLOT as u64)
        .slot("BUDGET_SLOT", BUDGET_SLOT as u64)
        .slot("SPENT_SLOT", SPENT_SLOT as u64)
        .slot("CAPS_DIGEST_SLOT", CAPS_DIGEST_SLOT as u64)
        .slot("REVOKED_SLOT", REVOKED_SLOT as u64)
        .slot("EPOCH_SLOT", EPOCH_SLOT as u64)
        .string("FACTORY_VK_HEX", hex_encode_32(&MANDATE_FACTORY_VK))
        .topic("ENROLLED", "edge-mandate-enrolled")
        .topic("SPENT", "edge-mandate-spent")
        .topic("REVOKED", "edge-mandate-revoked")
}

/// Register the edge-mandate starbridge-app on a shared context: publish the
/// factory (so the operator can mint mandate cells) and the inspector descriptor
/// (so a host surface can render a mandate cell). Returns the registered factory VK.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(mandate_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "edge-mandate".into(),
        descriptor: serde_json::json!({
            "component": "dregg-edge-mandate",
            "module": "/starbridge-apps/edge-mandate/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": ["account", "budget", "spent", "revoked"],
            "slot_layout": {
                "subject": SUBJECT_SLOT,
                "account": ACCOUNT_SLOT,
                "budget": BUDGET_SLOT,
                "spent": SPENT_SLOT,
                "caps_digest": CAPS_DIGEST_SLOT,
                "revoked": REVOKED_SLOT,
                "epoch": EPOCH_SLOT,
            },
            "record_collection": REC_COLL,
            "factory_vk_hex": hex_encode_32(&factory_vk),
            "child_program_vk_hex": hex_encode_32(&mandate_child_program_vk()),
            "operations": ["enrol", "spend", "revoke"],
        }),
    });

    factory_vk
}

#[cfg(test)]
mod tests {
    use super::*;

    const ALICE_KEY: &str = "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIAlIcEoZ1ENESf0Kk6zc8alICEforAlIcEkeyblob alice@laptop";
    const BOB_KEY: &str =
        "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIBobBobBobBobBobBobBobBobBobBobBobBobBobx bob@desktop";

    /// The operator's held grant: fs + a scoped GitHub egress + a scoped pay vendor,
    /// underwriting up to $50.00. Enrolments attenuate against this.
    fn operator_held() -> CapMandate {
        CapMandate::held(
            ["fs", "http:api.github.com", "pay:openai"],
            5000,
            "operator",
        )
    }

    fn fresh_cell() -> Cell {
        Cell::with_balance([7u8; 32], [9u8; 32], 0)
    }

    #[test]
    fn factory_descriptor_is_stable() {
        assert_eq!(
            mandate_factory_descriptor().hash(),
            mandate_factory_descriptor().hash()
        );
    }

    // ── THE REQUIRED PROPERTY #1: enrol mints a mandate NO WIDER than the grant. ──
    #[test]
    fn enrol_mints_a_mandate_no_wider_than_the_grant() {
        let held = operator_held();
        let mut cell = fresh_cell();
        // Request a cap the operator does NOT hold (`pay:evil`) and MORE budget than
        // held (9999 > 5000). Both must be narrowed.
        let req = EnrolRequest::new(
            "dga1_alice",
            ALICE_KEY,
            9999,
            "fs,http:api.github.com,pay:evil",
        );
        let minted = enrol(&mut cell, &held, &req).expect("valid enrol");

        // The minted mandate is `⊑` the operator's held grant — no amplification.
        assert!(minted.le(&held), "granted ⊑ held");
        // The out-of-grant cap was DROPPED.
        assert!(
            !minted.caps.contains("pay:evil"),
            "a cap the operator does not hold is dropped"
        );
        assert_eq!(
            minted.caps,
            ["fs", "http:api.github.com"]
                .into_iter()
                .map(String::from)
                .collect::<BTreeSet<_>>()
        );
        // The over-ceiling budget was CLAMPED to the held budget.
        assert_eq!(minted.budget, 5000, "budget clamped to the held ceiling");
        assert_eq!(budget_of(&cell), 5000);
        // The sealed caps digest matches the canonical minted caps.
        assert_eq!(
            cell.state.get_field(CAPS_DIGEST_SLOT as usize).copied(),
            Some(field_from_bytes(minted.canonical_caps().as_bytes()))
        );
    }

    // ── THE REQUIRED PROPERTY #2: a spend past the sub-budget is refused. ─────────
    #[test]
    fn a_spend_past_the_sub_budget_is_refused() {
        let held = operator_held();
        let mut cell = fresh_cell();
        // Enrol with a requested budget BELOW the held ceiling (300 cents).
        let req = EnrolRequest::new("dga1_alice", ALICE_KEY, 300, "fs");
        let minted = enrol(&mut cell, &held, &req).unwrap();
        assert_eq!(minted.budget, 300, "the sub-budget is the requested 300");

        // A spend within the sub-budget is admitted; the meter draws down.
        assert_eq!(spend(&mut cell, 200), Ok(200));
        assert_eq!(spent_of(&cell), 200);
        assert_eq!(headroom_of(&cell), 100);

        // A spend that would breach the sub-budget (200 + 150 > 300) is REFUSED, and
        // the meter is unchanged (fail-closed).
        assert_eq!(
            spend(&mut cell, 150),
            Err(EdgeMandateError::OverBudget {
                spent: 200,
                cost: 150,
                budget: 300,
            })
        );
        assert_eq!(spent_of(&cell), 200, "the refused spend moved nothing");
        // A spend that exactly hits the ceiling is fine.
        assert_eq!(spend(&mut cell, 100), Ok(300));
        assert_eq!(headroom_of(&cell), 0);
    }

    // ── THE REQUIRED PROPERTY #3: the authorized_keys line is a PURE FUNCTION of
    //    the cell (deterministic; scoped; revoked → dark). ────────────────────────
    #[test]
    fn the_authorized_keys_line_is_a_pure_function_of_the_cell() {
        let held = operator_held();
        let mut cell = fresh_cell();
        let req = EnrolRequest::new("dga1_alice", ALICE_KEY, 500, "fs,http:api.github.com")
            .with_brain("hermes");
        enrol(&mut cell, &held, &req).unwrap();

        // Pure: reading twice yields byte-identical lines.
        let a = authorized_keys_line(&cell, DEFAULT_ATTACH_BIN).unwrap();
        let b = authorized_keys_line(&cell, DEFAULT_ATTACH_BIN).unwrap();
        assert_eq!(a, b, "the line is a deterministic function of the cell");

        // The forced command scopes to THIS account + budget + caps + brain.
        assert!(a.contains("dregg-agent attach --account dga1_alice --budget 500"));
        assert!(a.contains("--caps fs,http:api.github.com"));
        assert!(a.contains("--brain hermes"));
        // Locked down to the REPL; the user's key rides at the end.
        assert!(a.starts_with("command=\""));
        assert!(a.contains(",restrict,pty "));
        assert!(a.ends_with("alice@laptop"));
        // NO raw shell escape (the caps were hosted-validated at enrol).
        assert!(!a.contains("--caps shell"));

        // A deploy can override the attach binary; the line follows the cell + arg.
        let abs = authorized_keys_line(&cell, "/usr/local/bin/dregg-agent").unwrap();
        assert!(abs.contains("/usr/local/bin/dregg-agent attach"));

        // Revoke → the line goes DARK (the cell now determines an absent line).
        revoke(&mut cell);
        assert!(is_revoked(&cell));
        assert!(
            authorized_keys_line(&cell, DEFAULT_ATTACH_BIN).is_none(),
            "a revoked mandate emits no attach line"
        );
    }

    #[test]
    fn a_hosted_shell_cap_is_refused_at_enrol() {
        let held = CapMandate::held(["shell", "fs"], 5000, "operator");
        let mut cell = fresh_cell();
        // Even though the operator "holds" shell, the HOSTED posture refuses it at
        // parse — a hosted box holds the operator's keys.
        let err = enrol(
            &mut cell,
            &held,
            &EnrolRequest::new("dga1_alice", ALICE_KEY, 500, "shell,fs"),
        )
        .expect_err("a hosted box must refuse the shell cap");
        match err {
            EdgeMandateError::BadCaps { reason, .. } => {
                assert!(reason.contains("shell"), "the reason names the shell cap");
            }
            other => panic!("expected BadCaps, got {other:?}"),
        }
        // Nothing was sealed — the cell is untouched (budget still zero).
        assert_eq!(budget_of(&cell), 0);
    }

    #[test]
    fn bad_budget_and_key_and_account_are_rejected() {
        let held = operator_held();
        let mut cell = fresh_cell();
        assert_eq!(
            enrol(
                &mut cell,
                &held,
                &EnrolRequest::new("dga1_x", ALICE_KEY, 0, "fs")
            ),
            Err(EdgeMandateError::BadBudget(0))
        );
        assert_eq!(
            enrol(
                &mut cell,
                &held,
                &EnrolRequest::new("dga1_x", "not-a-key", 100, "fs")
            ),
            Err(EdgeMandateError::BadSshKey)
        );
        assert_eq!(
            enrol(
                &mut cell,
                &held,
                &EnrolRequest::new("", ALICE_KEY, 100, "fs")
            ),
            Err(EdgeMandateError::EmptyAccount)
        );
    }

    #[test]
    fn a_revoked_mandate_refuses_further_spend() {
        let held = operator_held();
        let mut cell = fresh_cell();
        enrol(
            &mut cell,
            &held,
            &EnrolRequest::new("dga1_alice", ALICE_KEY, 500, "fs"),
        )
        .unwrap();
        revoke(&mut cell);
        assert_eq!(spend(&mut cell, 1), Err(EdgeMandateError::Revoked));
    }

    #[test]
    fn two_subjects_get_two_isolated_scoped_lines() {
        let held = operator_held();
        let mut alice = fresh_cell();
        let mut bob = fresh_cell();
        enrol(
            &mut alice,
            &held,
            &EnrolRequest::new("dga1_alice", ALICE_KEY, 200, "fs"),
        )
        .unwrap();
        enrol(
            &mut bob,
            &held,
            &EnrolRequest::new("dga1_bob", BOB_KEY, 5000, "fs,pay:openai"),
        )
        .unwrap();

        let ak = authorized_keys([&alice, &bob], DEFAULT_ATTACH_BIN);
        let lines: Vec<&str> = ak.lines().filter(|l| l.starts_with("command=")).collect();
        assert_eq!(lines.len(), 2, "one forced-command line per subject");

        let a = lines.iter().find(|l| l.contains("dga1_alice")).unwrap();
        let b = lines.iter().find(|l| l.contains("dga1_bob")).unwrap();
        assert!(a.contains("--budget 200") && a.contains("--caps fs"));
        assert!(!a.contains("pay:openai"), "alice has no pay cap");
        assert!(b.contains("--budget 5000") && b.contains("pay:openai"));
    }

    #[test]
    fn held_from_grant_lifts_the_operator_grant() {
        let grant = Grant::new("operator").tools(["fs", "http:api.github.com"]);
        let held = held_from_grant(&grant, 5000);
        assert!(held.caps.contains("fs"));
        assert!(held.caps.contains("http:api.github.com"));
        // Enrol against the lifted grant: a request for a tool NOT in the grant is
        // dropped — the enrolled tool-set is a subset of the grant's tools.
        let mut cell = fresh_cell();
        let minted = enrol(
            &mut cell,
            &held,
            &EnrolRequest::new("dga1_alice", ALICE_KEY, 500, "fs,pay:openai"),
        )
        .unwrap();
        assert!(minted.le(&held));
        assert!(!minted.caps.contains("pay:openai"), "not in the grant");
        assert_eq!(minted.canonical_caps(), "fs");
    }

    #[test]
    fn the_record_round_trips_through_the_committed_heap() {
        let held = operator_held();
        let mut cell = fresh_cell();
        // A long RSA-ish key exercises the multi-chunk string codec.
        let long_key = format!("ssh-rsa {} rsa@host", "A".repeat(540));
        enrol(
            &mut cell,
            &held,
            &EnrolRequest::new("dga1_rsa", &long_key, 400, "fs").with_brain("nemotron"),
        )
        .unwrap();
        assert_eq!(account_of(&cell).as_deref(), Some("dga1_rsa"));
        assert_eq!(ssh_pubkey_of(&cell).as_deref(), Some(long_key.as_str()));
        assert_eq!(caps_of(&cell).as_deref(), Some("fs"));
        assert_eq!(brain_of(&cell).as_deref(), Some("nemotron"));
        // The long key survives into the attach line verbatim.
        let line = authorized_keys_line(&cell, DEFAULT_ATTACH_BIN).unwrap();
        assert!(line.ends_with("rsa@host"));
    }

    #[test]
    fn a_spend_advances_the_no_replay_epoch_and_moves_the_commitment() {
        let held = operator_held();
        let mut cell = fresh_cell();
        enrol(
            &mut cell,
            &held,
            &EnrolRequest::new("dga1_alice", ALICE_KEY, 500, "fs"),
        )
        .unwrap();
        let e0 = epoch_of(&cell);
        let before = cell.state_commitment();
        spend(&mut cell, 100).unwrap();
        assert_eq!(epoch_of(&cell), e0 + 1, "the epoch strictly advances");
        assert_ne!(before, cell.state_commitment(), "the spend is witnessed");
    }
}
