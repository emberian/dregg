//! # starbridge-org — teams / organizations (IAM) as a dregg-native cell.
//!
//! dregg identity is **single-subject** by default — a `dga1_` cap-account is the
//! whole subject, and a console scopes "my stuff" by `owner == subject`. Real
//! clouds have **organizations** with **members** and **roles** (AWS
//! Organizations / IAM, GCP projects + IAM, a Vercel/Cloudflare team). This crate
//! adds that — and the elegant part is that it adds **no new authorization
//! primitive**. dregg's capability-attenuation lattice (the `dregg-auth`
//! credential core, whose `Credential::attenuate` provably only ever *narrows*
//! authority — `metatheory/Dregg2/Authority/Caveat.lean` `attenuate_subset`)
//! **already is** the role mechanism. This crate just makes it legible as orgs +
//! roles, and binds the membership record into a factory-born cell whose
//! invariants the executor re-enforces.
//!
//! ## How the cap lattice becomes orgs + roles
//!
//! * An [`Org`] is **its own dregg cell** — it has its own minting authority
//! ([`OrgAuthority`] holds the [`RootKey`](dregg_auth::credential::RootKey))
//! and a stable id `org:<16hex>`. The org **owns** resources: a resource
//! created in an org context is owned by the *org*, not the acting member.
//! * **Members** are `dga1_` cap-accounts (subjects) added to the org; each holds
//! a [`Role`] (`owner` / `admin` / `member` / `billing` / `viewer`).
//! * A role maps to a set of [`Permission`]s, which compiles to an **attenuated
//! capability** over the org-owner's authority ([`cap::mint_role_cap`]): the
//! owner grant (`AnyOf(all perms)`, pinned to this org) is `attenuate`d to the
//! role's perms. So **"admin" = a cap attenuated to manage-but-not-delete-org**;
//! **"viewer" = a read-only attenuation.** A member acts by presenting their
//! role-cap, verified ([`cap::authorize`]) against the org root key + a context
//! binding `org` (the **scoping** tooth) and `perm` (the **role-gating** tooth).
//! A viewer-cap simply does not satisfy a `resource:write` context — the write
//! is *refused*, and by the no-amplify property it cannot be forged wider.
//! **The role IS an attenuation of the lattice — that is the whole design.**
//!
//! ## The four axes (the unified starbridge-app template)
//!
//! * **the verified core** — the [`org_factory_descriptor`] + the
//! [`org_cell_program`] (this file): the org identity is sealed (`WriteOnce`
//! [`ROOT_PUBKEY_SLOT`]/[`NAME_SLOT`]) and the membership-event log is
//! append-only (`Monotonic` [`SEQ_SLOT`]) — invariants the executor re-enforces
//! on every touching turn. The `member/role` roster is a witnessed committed
//! heap image ([`MEMBER_COLL`]/[`ROLE_COLL`]); the org-scope + role-gate are the
//! cap-context caveats [`cap::authorize`] checks on every membership turn. The
//! receipted turns live in the pure [`OrgAuthority`] ([`org`]);
//! * the SERVICE-CELL `invoke()` front door ([`service`]): a typed
//! `InterfaceDescriptor` (`invite` / `accept` / `remove` / `change_role` /
//! `transfer` / `view`);
//! * the deos-view CARD ([`card`]): the team dashboard as a `deos.ui.*` tree;
//! * the deos surface — the composed [`DeosApp`] ([`org_app`] / [`register_deos`]).
//!
//! ## Two enforcement surfaces (both REAL)
//!
//! 1. **Capability attenuation (the role-cap)** — WHO may act, with WHICH
//! permissions. The dregg-auth attenuated role-cap ([`cap`]): [`cap::authorize`]
//! verifies a presented cap against the org root key + the action's (org, perm)
//! context. A viewer's cap does not satisfy a `members:manage` context — the
//! turn is *refused* in-band, and cannot be forged wider (no amplification).
//! 2. **The org cell invariants** — the [`org_factory_descriptor`]'s
//! `state_constraints`, re-enforced by the executor on every turn: the org
//! identity key + name are `WriteOnce` (a live org can never be re-pointed at a
//! new signing key or silently renamed), and the membership sequence is
//! `Monotonic` (the audit height never rewinds).
//!
//! ## Honest gaps (what this is, and is not)
//!
//! The roster's source of truth is the pure serializable [`Org`] record (the
//! console's "team"); the cell mirrors its owner / member-count / seq into scalar
//! slots (the executor-enforced invariants) and its members into a committed heap
//! image (`MEMBER_COLL`/`ROLE_COLL`, a light client witnesses the roster). The
//! `WriteOnce(ROOT_PUBKEY/NAME)` + `Monotonic(SEQ)` teeth and the role-cap
//! authorize (a viewer's admin attempt refused, unforgeably) are REAL. Threading
//! the full roster mutation through a per-member `SetField` allow-list program (so
//! an off-roster write is itself an executor refusal, not just a mirror the
//! authority keeps honest) is the production lane this models.

#![forbid(unsafe_code)]

pub use dregg_app_framework::FieldElement;
use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellAffordance, CellId, CellMode,
    CellProgram, ChildVkStrategy, ConstantsModule, DeosApp, DeosCell, Effect, EmbeddedExecutor,
    Event, FactoryDescriptor, GatedAffordance, InspectorDescriptor, StarbridgeAppContext,
    StateConstraint, TransitionCase, TransitionGuard, canonical_program_vk, field_from_bytes,
    field_from_u64, hex_encode_32, symbol,
};

use dregg_cell::Cell;

/// The role-cap bridge: role → permission → attenuated dregg-auth credential.
pub mod cap;
/// The deos-view CARD: the team dashboard as a renderer-independent view-tree.
pub mod card;
/// The pure membership state machine: [`Org`] / [`OrgAuthority`] + the receipted
/// membership turns.
pub mod org;
/// Org-owned resources + the org-scoping read tooth.
pub mod resource;
/// The legible role → permission table.
pub mod role;
/// The CELLS-AS-SERVICE-OBJECTS face: a typed `InterfaceDescriptor` + `invoke()`
/// dispatch over the membership vocabulary.
pub mod service;

pub use org::{Invite, Membership, MembershipAction, MembershipEvent, Org, OrgAuthority, OrgError};
pub use resource::{OrgResource, ResourceKind, scope_for_member};
pub use role::{ORG_KEY, PERM_KEY, Permission, Role};

// =============================================================================
// Slot layout (the org cell) — the program-enforced scalars
// =============================================================================

/// Slot 0 — `root_pubkey`. A commitment to the org's minting key (the key members'
/// role-caps verify under). `WriteOnce` — sealed at founding: a live org can never
/// be re-pointed at a new signing authority (the identity tooth).
pub const ROOT_PUBKEY_SLOT: u8 = 0;
/// Slot 1 — `owner`. The current owner's subject tag. Moves only via the
/// role-gated `transfer` turn (owner-only `OrgTransfer`).
pub const OWNER_SLOT: u8 = 1;
/// Slot 2 — `seq`. The membership-event sequence height. `Monotonic` — the audit
/// trail is append-only; the history height never rewinds.
pub const SEQ_SLOT: u8 = 2;
/// Slot 3 — `member_count`. The current roster size (members join and leave, so
/// NOT monotone — informational, the gauge denominator).
pub const MEMBER_COUNT_SLOT: u8 = 3;
/// Slot 4 — `name`. A commitment to the org's human name. `WriteOnce` — sealed at
/// founding (a live org is not silently renamed).
pub const NAME_SLOT: u8 = 4;

// =============================================================================
// The witnessed roster image — the committed umem heap
// =============================================================================

/// Reserved heap collection id for the org's **member subject roster** — key `i`
/// holds [`subject_tag`] of member `i` (for `i` in `0..member_count`). Lives inside
/// the cell's committed heap (folded into the canonical state commitment), so the
/// roster is witnessed + passable. Chosen high to avoid colliding with application
/// heap collections.
pub const MEMBER_COLL: u32 = 0x0000_0A61; // "ORG-a"
/// Reserved heap collection id for the **member role roster** — key `i` holds
/// [`field_from_u64`]`(role.code())` of member `i`, the parallel of [`MEMBER_COLL`].
pub const ROLE_COLL: u32 = 0x0000_0A62;

// =============================================================================
// Factory configuration
// =============================================================================

/// The factory VK the platform publishes for org cells.
pub const ORG_FACTORY_VK: [u8; 32] = *b"starbridge-org-membership-fact!!";

/// Default per-epoch slot-creation budget (how many orgs the factory mints).
pub const DEFAULT_CREATION_BUDGET: u64 = 256;

// =============================================================================
// Field helpers
// =============================================================================

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse
/// of [`field_from_u64`]).
pub fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

/// The org cell's tag for a member subject — a domain-separated commitment to the
/// subject string (what [`MEMBER_COLL`] and [`OWNER_SLOT`] store). Always non-zero
/// (a blake3 image), so a zeroed slot reads as "absent".
pub fn subject_tag(subject: &str) -> FieldElement {
    let mut buf = Vec::with_capacity(subject.len() + 12);
    buf.extend_from_slice(b"org-subject:");
    buf.extend_from_slice(subject.as_bytes());
    field_from_bytes(&buf)
}

/// The org cell's tag for the org name — a domain-separated commitment (what
/// [`NAME_SLOT`] seals `WriteOnce`).
pub fn name_tag(name: &str) -> FieldElement {
    let mut buf = Vec::with_capacity(name.len() + 9);
    buf.extend_from_slice(b"org-name:");
    buf.extend_from_slice(name.as_bytes());
    field_from_bytes(&buf)
}

/// A commitment to the org's root public key — the value [`ROOT_PUBKEY_SLOT`]
/// seals `WriteOnce` (the identity role-caps verify under, never re-pointed).
pub fn root_pubkey_field(org: &Org) -> FieldElement {
    let mut buf = Vec::with_capacity(org.root_pubkey.len() + 12);
    buf.extend_from_slice(b"org-rootkey:");
    buf.extend_from_slice(org.root_pubkey.as_bytes());
    field_from_bytes(&buf)
}

// =============================================================================
// The verified core — CellProgram + FactoryDescriptor
// =============================================================================

/// The **life-of-org invariants** the executor re-enforces on every touching turn:
///
/// * `WriteOnce` on `ROOT_PUBKEY` — the org's minting-key identity is sealed at
/// founding; a live org can never be re-pointed at a new signing authority (so
/// the key members' role-caps verify under cannot be swapped);
/// * `WriteOnce` on `NAME` — the org name is sealed at founding;
/// * `Monotonic` on `SEQ` — the membership-event sequence height only advances
/// (the audit trail is append-only; a rewind is refused).
///
/// `OWNER` and `MEMBER_COUNT` are intentionally mutable: ownership transfers move
/// `OWNER` (a role-gated turn), and the roster grows/shrinks as members join/leave.
pub fn org_invariants() -> Vec<StateConstraint> {
    vec![
        StateConstraint::WriteOnce {
            index: ROOT_PUBKEY_SLOT,
        },
        StateConstraint::WriteOnce { index: NAME_SLOT },
        StateConstraint::Monotonic { index: SEQ_SLOT },
    ]
}

/// The org cell program: an `Always` case carrying [`org_invariants`] (the identity
/// + audit invariants re-enforced on EVERY touching turn). A pure invariants
/// program (no method-dispatch case), so every membership operation — `invite` /
/// `accept` / `remove` / `change_role` / `transfer` — is admitted as long as the
/// invariants hold (and the role-cap [`cap::authorize`] gate passes in-band).
pub fn org_cell_program() -> CellProgram {
    CellProgram::Cases(vec![TransitionCase {
        guard: TransitionGuard::Always,
        constraints: org_invariants(),
    }])
}

/// The life-of-org invariants as a flat `Predicate` program (the method-agnostic
/// floor the factory + the service share).
pub fn org_invariants_program() -> CellProgram {
    CellProgram::Predicate(org_invariants())
}

/// Canonical child program VK for org cells.
pub fn org_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&org_cell_program())
}

/// The platform's factory descriptor for minting org cells.
pub fn org_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: ORG_FACTORY_VK,
        child_program_vk: Some(org_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(org_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            // The org owner holds an attenuatable SelfCell cap — the root the
            // role-caps descend from (each attenuated to a role's permission set).
            target: CapTarget::SelfCell,
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        // A factory-born org cell is born empty; the FOUND turn binds ROOT_PUBKEY /
        // NAME (`WriteOnce`, admit-from-zero) + OWNER + the genesis roster.
        field_constraints: vec![],
        state_constraints: org_invariants(),
        default_mode: CellMode::Sovereign,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

/// All factory descriptors this starbridge-app contributes.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![org_factory_descriptor()]
}

// =============================================================================
// The cell-state layer — mirror the pure Org record into the committed cell
// =============================================================================

/// **Mirror the pure [`Org`] record into the org cell's committed state** — the
/// executor-enforced scalar invariants (owner / seq / member-count, + the sealed
/// identity/name) and the witnessed roster heap image ([`MEMBER_COLL`]/[`ROLE_COLL`]).
/// After this, the cell's commitment binds the current roster + audit height; a
/// light client reads the team off the committed heap.
pub fn mirror_org(cell: &mut Cell, org: &Org) {
    cell.state
        .set_field(ROOT_PUBKEY_SLOT as usize, root_pubkey_field(org));
    cell.state
        .set_field(NAME_SLOT as usize, name_tag(&org.name));
    cell.state
        .set_field(OWNER_SLOT as usize, subject_tag(&org.owner));
    cell.state
        .set_field(SEQ_SLOT as usize, field_from_u64(org.seq()));
    cell.state.set_field(
        MEMBER_COUNT_SLOT as usize,
        field_from_u64(org.member_count()),
    );
    for (i, m) in org.members.iter().enumerate() {
        cell.state
            .set_heap(MEMBER_COLL, i as u32, subject_tag(&m.subject));
        cell.state
            .set_heap(ROLE_COLL, i as u32, field_from_u64(m.role.code()));
    }
    // Clear any stale tail entries from a prior, larger roster so a reader bounded
    // by MEMBER_COUNT never mistakes a removed member for a live one.
    let mut i = org.members.len() as u32;
    while cell.state.get_heap(MEMBER_COLL, i).is_some() {
        cell.state.set_heap(MEMBER_COLL, i, [0u8; 32]);
        cell.state.set_heap(ROLE_COLL, i, [0u8; 32]);
        i += 1;
    }
}

/// **Seed an org cell** so the deos fires have live state + the invariants bite:
/// install [`org_cell_program`] (so the executor re-enforces the identity + audit
/// invariants on every touching turn), then mirror the founding org record
/// ([`mirror_org`]) directly into the embedded ledger.
pub fn seed_org(executor: &EmbeddedExecutor, org: &Org) {
    let cell = executor.cell_id();
    executor.install_program(cell, org_cell_program());
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&cell) {
            mirror_org(c, org);
        }
    });
}

// =============================================================================
// Cell-turn effect templates (shared by the deos affordances + the service)
// =============================================================================

/// **The `transfer` cell effects** — move [`OWNER_SLOT`] to `new_owner`'s tag,
/// bump the audit height [`SEQ_SLOT`] to `new_seq`, and emit `org-owner-transferred`.
/// The executor re-enforces `Monotonic(SEQ)` on the produced transition (an audit
/// rewind is a real refusal). This is the ONE state-parameterized transfer body
/// (computed from the cell's live seq).
pub fn transfer_effects(org_cell: CellId, new_owner: &str, new_seq: u64) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell: org_cell,
            index: OWNER_SLOT as usize,
            value: subject_tag(new_owner),
        },
        Effect::SetField {
            cell: org_cell,
            index: SEQ_SLOT as usize,
            value: field_from_u64(new_seq),
        },
        Effect::EmitEvent {
            cell: org_cell,
            event: Event::new(
                symbol("org-owner-transferred"),
                vec![subject_tag(new_owner), field_from_u64(new_seq)],
            ),
        },
    ]
}

/// **A membership-turn's cell effects** — advance the audit height [`SEQ_SLOT`] to
/// `new_seq`, set [`MEMBER_COUNT_SLOT`] to `member_count`, and emit a
/// `org-membership` event carrying `(action code, subject tag, role code)`. The
/// executor re-enforces `Monotonic(SEQ)`. The single shared body for `invite` /
/// `accept` / `remove` / `change_role`.
pub fn membership_effects(
    org_cell: CellId,
    action: MembershipAction,
    subject: &str,
    role: Option<Role>,
    new_seq: u64,
    member_count: u64,
) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell: org_cell,
            index: SEQ_SLOT as usize,
            value: field_from_u64(new_seq),
        },
        Effect::SetField {
            cell: org_cell,
            index: MEMBER_COUNT_SLOT as usize,
            value: field_from_u64(member_count),
        },
        Effect::EmitEvent {
            cell: org_cell,
            event: Event::new(
                symbol("org-membership"),
                vec![
                    field_from_u64(action.code()),
                    subject_tag(subject),
                    field_from_u64(role.map(Role::code).unwrap_or(0)),
                ],
            ),
        },
    ]
}

/// Build the on-ledger [`Action`] recording an org founding (the genesis seal — the
/// sealed identity/name + the owner + the founded event). The state-binding
/// [`mirror_org`] runs executor-side; this is the signed turn that records it.
pub fn build_found_org_action(cipherclerk: &AppCipherclerk, org: &Org) -> Action {
    let org_cell = cipherclerk.cell_id();
    let effects = vec![
        Effect::SetField {
            cell: org_cell,
            index: ROOT_PUBKEY_SLOT as usize,
            value: root_pubkey_field(org),
        },
        Effect::SetField {
            cell: org_cell,
            index: NAME_SLOT as usize,
            value: name_tag(&org.name),
        },
        Effect::SetField {
            cell: org_cell,
            index: OWNER_SLOT as usize,
            value: subject_tag(&org.owner),
        },
        Effect::EmitEvent {
            cell: org_cell,
            event: Event::new(
                symbol("org-founded"),
                vec![
                    root_pubkey_field(org),
                    name_tag(&org.name),
                    subject_tag(&org.owner),
                ],
            ),
        },
    ];
    cipherclerk.make_action(org_cell, "found_org", effects)
}

// =============================================================================
// The deos-native surface — the org as a composed DeosApp
// =============================================================================

/// The org rights tiers, on the real attenuation lattice:
/// * the OWNER holds [`AuthRequired::None`]/root — it can `transfer` ownership +
/// everything below (the owner-cap is the root the role-caps descend from);
/// * an ADMIN holds [`AuthRequired::Signature`] — it can `invite` / `remove` /
/// `change_role` (the `MembersManage` tier);
/// * a MEMBER holds [`AuthRequired::Either`] — it can `accept` an invite + read.
///
/// So `Either ⊂ Signature ⊂ None` IS the member ⊂ admin ⊂ owner ladder. (The
/// coarse cap-graph tier here; the FINE gate is the role-cap [`cap::authorize`],
/// which refuses a viewer's `members:manage` context unforgeably.)
pub const OWNER_RIGHTS: AuthRequired = AuthRequired::None;
/// The admin rights tier (`MembersManage`). See [`OWNER_RIGHTS`].
pub const ADMIN_RIGHTS: AuthRequired = AuthRequired::Signature;
/// The member rights tier (accept + read). See [`OWNER_RIGHTS`].
pub const MEMBER_RIGHTS: AuthRequired = AuthRequired::Either;

/// The `transfer` **live-state precondition** — the org must have at least two
/// members (`MEMBER_COUNT >= 2`): you cannot transfer ownership in a one-person
/// org (there is no other member to transfer TO). So a `transfer` button is DARK on
/// a solo org and LIT once a second member has joined. The owner-only gate itself
/// is the role-cap `OrgTransfer` tooth; this precondition is the surface
/// reactivity.
pub fn transferable_precondition() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldGte {
        index: MEMBER_COUNT_SLOT,
        value: field_from_u64(2),
    }])
}

/// **The org (team) as a composed [`DeosApp`]** — the whole membership surface on
/// the deos bones. The org cell is the acting agent's own cell
/// (`cipherclerk.cell_id()`).
///
/// * `invite` — cap-only (an ADMIN invites a subject to a role): `Signature`;
/// * `accept` — cap-only (the invitee joins, minting their role-cap): `Either`;
/// * `remove` — cap-only (an ADMIN removes a member): `Signature`;
/// * `change_role` — cap-only (an ADMIN re-roles a member): `Signature`;
/// * `transfer` — a [`GatedAffordance`] (the OWNER transfers ownership): a
/// live-state PRECONDITION ([`transferable_precondition`], `>= 2` members); the
/// real fire ([`fire_transfer`]) submits the owner-moving turn (reading the LIVE
/// seq), re-enforced by the executor's `Monotonic(SEQ)`.
pub fn org_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let org_cell = cipherclerk.cell_id();

    let invite = CellAffordance::new(
        "invite",
        ADMIN_RIGHTS,
        Effect::EmitEvent {
            cell: org_cell,
            event: Event::new(symbol("org-member-invited"), vec![]),
        },
    );
    let accept = CellAffordance::new(
        "accept",
        MEMBER_RIGHTS,
        Effect::EmitEvent {
            cell: org_cell,
            event: Event::new(symbol("org-member-joined"), vec![]),
        },
    );
    let remove = CellAffordance::new(
        "remove",
        ADMIN_RIGHTS,
        Effect::EmitEvent {
            cell: org_cell,
            event: Event::new(symbol("org-member-removed"), vec![]),
        },
    );
    let change_role = CellAffordance::new(
        "change_role",
        ADMIN_RIGHTS,
        Effect::EmitEvent {
            cell: org_cell,
            event: Event::new(symbol("org-role-changed"), vec![]),
        },
    );
    let transfer = GatedAffordance::new(
        CellAffordance::new(
            "transfer",
            OWNER_RIGHTS,
            Effect::SetField {
                cell: org_cell,
                index: OWNER_SLOT as usize,
                value: field_from_u64(1),
            },
        ),
        transferable_precondition(),
    );

    DeosApp::builder("org", cipherclerk.clone(), executor.clone())
        .discoverable(vec!["teams".into(), "iam".into(), "org".into()])
        .cell(
            DeosCell::new(org_cell, "org")
                .affordance(invite)
                .affordance(accept)
                .affordance(remove)
                .affordance(change_role)
                .gated(transfer)
                // Published at the MEMBER tier (`Either`) — the narrowest role that
                // holds the org (a member reacquires the team across the membrane).
                .publish(MEMBER_RIGHTS),
        )
        .build()
}

/// **Fire `transfer`** — the deos cap∧state PRECONDITION gate (>= 2 members,
/// anti-ghost in-band), then the verified owner-moving turn (reading the LIVE seq
/// and adding one), re-enforced by the executor's `Monotonic(SEQ)`. A solo org's
/// `transfer` never submits; an audit rewind is a real executor refusal.
///
/// This is the CELL half; the AUTHORITATIVE record move (owner→new_owner, old owner
/// demoted to admin, one receipted turn) is [`OrgAuthority::transfer_ownership`],
/// whose owner-only `OrgTransfer` cap-gate is the fine tooth. After the turn commits
/// the caller re-mirrors the updated record with [`mirror_org`].
pub fn fire_transfer(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
    new_owner: &str,
) -> Result<dregg_app_framework::TurnReceipt, dregg_app_framework::FireExecuteError> {
    let cell = &app.cells()[0];
    let org_cell = cell.cell();
    let new_owner = new_owner.to_string();
    cell.fire_gated_through_executor_with("transfer", held, cipherclerk, executor, move |live| {
        let live_seq = field_to_u64(&live.fields[SEQ_SLOT as usize]);
        transfer_effects(org_cell, &new_owner, live_seq + 1)
    })
}

// =============================================================================
// StarbridgeAppContext mount
// =============================================================================

/// **Mount the deos-native surface** ([`org_app`]) on a shared context: build the
/// composed [`DeosApp`], seed a demo org cell's program + genesis state, and fold
/// the app into the context's affordance registry. Returns the live [`DeosApp`].
pub fn register_deos(ctx: &StarbridgeAppContext) -> DeosApp {
    let app = org_app(ctx.cipherclerk(), ctx.executor());
    // A demo org so the gated `transfer` fire has live state (two members, so the
    // `>= 2` precondition is LIT), and the invariants bite on every touching turn.
    let mut auth = OrgAuthority::found_with_seed([0x0A; 32], "demo-org", "dregg:owner");
    let owner_cap = auth.owner_cap();
    if let Ok(inv) = auth.invite(&owner_cap, "dregg:owner", "dregg:teammate", Role::Admin, 0) {
        let _ = auth.accept_invite(&inv, "dregg:teammate");
    }
    seed_org(ctx.executor(), auth.org());
    app.register(ctx);
    app
}

/// **Register the org starbridge-app** on a shared context — the FLOOR (the factory
/// descriptor whose `state_constraints` seal the org identity + append-only audit,
/// installed on every born org cell) AND the deos-native composition surface (the
/// [`DeosApp`], folded into the context's affordance registry). Returns the factory
/// VK (the floor's identity).
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(org_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "org".into(),
        descriptor: serde_json::json!({
        "component": "dregg-org",
        "module": "/starbridge-apps/org/inspectors.js",
        "uri_prefix": "dregg://cell/",
        "summary_fields": ["owner", "member_count", "seq", "name"],
        "slot_layout": {
        "root_pubkey": ROOT_PUBKEY_SLOT,
        "owner": OWNER_SLOT,
        "seq": SEQ_SLOT,
        "member_count": MEMBER_COUNT_SLOT,
        "name": NAME_SLOT,
        },
        "heap_collections": { "members": MEMBER_COLL, "roles": ROLE_COLL },
        "factory_vk_hex": hex_encode_32(&factory_vk),
        "child_program_vk_hex": hex_encode_32(&org_child_program_vk()),
        "roles": ["owner", "admin", "member", "billing", "viewer"],
        "methods": ["invite", "accept", "remove", "change_role", "transfer", "view"],
        }),
    });

    register_deos(ctx);
    factory_vk
}

/// The canonical web-constants module — the slot layout + role/event topics + the
/// factory VK the JS surface is rendered from.
pub fn web_constants() -> ConstantsModule {
    ConstantsModule::new("org")
        .slot("ROOT_PUBKEY_SLOT", ROOT_PUBKEY_SLOT as u64)
        .slot("OWNER_SLOT", OWNER_SLOT as u64)
        .slot("SEQ_SLOT", SEQ_SLOT as u64)
        .slot("MEMBER_COUNT_SLOT", MEMBER_COUNT_SLOT as u64)
        .slot("NAME_SLOT", NAME_SLOT as u64)
        .string("FACTORY_VK_HEX", hex_encode_32(&ORG_FACTORY_VK))
        .topic("FOUNDED", "org-founded")
        .topic("MEMBERSHIP", "org-membership")
        .topic("TRANSFERRED", "org-owner-transferred")
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{AgentCipherclerk, EmbeddedExecutor};

    fn test_context() -> StarbridgeAppContext {
        let cipherclerk = AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32]);
        let executor = EmbeddedExecutor::new(&cipherclerk, "default");
        StarbridgeAppContext::new(cipherclerk, executor)
    }

    #[test]
    fn factory_descriptor_is_stable() {
        assert_eq!(
            org_factory_descriptor().hash(),
            org_factory_descriptor().hash()
        );
        assert_eq!(org_factory_descriptor().factory_vk, ORG_FACTORY_VK);
    }

    #[test]
    fn org_invariants_seal_identity_and_append_only_audit() {
        let inv = org_invariants();
        assert!(inv.contains(&StateConstraint::WriteOnce {
            index: ROOT_PUBKEY_SLOT
        }));
        assert!(inv.contains(&StateConstraint::WriteOnce { index: NAME_SLOT }));
        assert!(inv.contains(&StateConstraint::Monotonic { index: SEQ_SLOT }));
    }

    #[test]
    fn mirror_org_writes_the_scalars_and_the_witnessed_roster() {
        let mut auth = OrgAuthority::found_with_seed([1u8; 32], "acme", "dregg:owner");
        let owner_cap = auth.owner_cap();
        let inv = auth
            .invite(&owner_cap, "dregg:owner", "dregg:alice", Role::Member, 0)
            .unwrap();
        auth.accept_invite(&inv, "dregg:alice").unwrap();
        let org = auth.org();

        let mut cell = Cell::with_balance([7u8; 32], [9u8; 32], 0);
        mirror_org(&mut cell, org);

        // The scalar invariants mirror the record.
        assert_eq!(
            cell.state.get_field(OWNER_SLOT as usize).copied(),
            Some(subject_tag("dregg:owner"))
        );
        assert_eq!(
            field_to_u64(cell.state.get_field(MEMBER_COUNT_SLOT as usize).unwrap()),
            2
        );
        assert_eq!(
            field_to_u64(cell.state.get_field(SEQ_SLOT as usize).unwrap()),
            org.seq()
        );
        // The witnessed roster: member 0 (owner) + member 1 (alice, Member).
        assert_eq!(
            cell.state.get_heap(MEMBER_COLL, 0),
            Some(subject_tag("dregg:owner"))
        );
        assert_eq!(
            cell.state.get_heap(ROLE_COLL, 1),
            Some(field_from_u64(Role::Member.code()))
        );
    }

    #[test]
    fn transfer_effects_move_the_owner_slot_and_bump_seq() {
        let org_cell = CellId::from_bytes([5u8; 32]);
        let effects = transfer_effects(org_cell, "dregg:bob", 7);
        // SetField(OWNER := bob), SetField(SEQ := 7), EmitEvent.
        assert_eq!(effects.len(), 3);
        assert!(matches!(
        &effects[0],
        Effect::SetField { index, value, .. }
        if *index == OWNER_SLOT as usize && *value == subject_tag("dregg:bob")
        ));
        assert!(matches!(
        &effects[1],
        Effect::SetField { index, value, .. }
        if *index == SEQ_SLOT as usize && *value == field_from_u64(7)
        ));
    }

    #[test]
    fn seed_then_fire_transfer_moves_the_owner_slot_through_the_executor() {
        // A demo org with two members: the gated `transfer` precondition (>= 2)
        // is LIT, and the owner-moving turn commits, moving OWNER_SLOT once.
        let ctx = test_context();
        let app = org_app(ctx.cipherclerk(), ctx.executor());
        let mut auth = OrgAuthority::found_with_seed([2u8; 32], "acme", "dregg:owner");
        let owner_cap = auth.owner_cap();
        let inv = auth
            .invite(&owner_cap, "dregg:owner", "dregg:bob", Role::Admin, 0)
            .unwrap();
        auth.accept_invite(&inv, "dregg:bob").unwrap();
        seed_org(ctx.executor(), auth.org());

        let before = ctx
            .executor()
            .cell_state(ctx.executor().cell_id())
            .unwrap()
            .fields[OWNER_SLOT as usize];

        let receipt = fire_transfer(
            &app,
            &OWNER_RIGHTS,
            ctx.cipherclerk(),
            ctx.executor(),
            "dregg:bob",
        )
        .expect("the owner transfers to a member through the gated fire");
        assert_ne!(receipt.turn_hash, [0u8; 32]);

        let after = ctx
            .executor()
            .cell_state(ctx.executor().cell_id())
            .unwrap()
            .fields[OWNER_SLOT as usize];
        assert_ne!(before, after, "the owner slot moved");
        assert_eq!(after, subject_tag("dregg:bob"), "…to the new owner");
    }

    #[test]
    fn register_installs_factory_and_inspector_and_deos_surface() {
        let ctx = test_context();
        let vk = register(&ctx);
        assert_eq!(vk, ORG_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
        assert!(ctx.inspector_registry().get("org").is_some());
        assert_eq!(
            ctx.affordance_registry().len(),
            1,
            "register mounts the deos surface on the same context"
        );
    }
}
