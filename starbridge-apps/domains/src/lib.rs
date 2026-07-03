//! # starbridge-domains — BYO custom domains as a dregg-native cell.
//!
//! **A domain binding is a cell.** Where the sibling [`starbridge-nameservice`]
//! runs a *federation name directory* (a name is minted inside a federation and
//! resolves to a `dregg://` sturdyref), this crate lets an owner point *their own*
//! DNS domain (`blog.acme.dev`) at a published site, with the standard ACME-style
//! proof-of-DNS-control before any traffic — or any certificate — is routed. The
//! two are duals: a federation name is *granted*; a custom domain is *proven*.
//!
//! ```text
//!   REGISTER                 BIND (cap-gated)             VERIFY                 ROUTE / CERT
//!   ───────────              ────────────────             ──────────             ─────────────
//!   own the domain           point at a site +            a DnsResolver          gateway Host -> site
//!   (DOMAIN, OWNER)          issue a challenge nonce       proves control          site_for_host()
//!    WriteOnce               WriteOnce(CHALLENGE_NONCE)     Monotonic(VERIFIED_SEQ) is_verified()
//! ```
//!
//! ## The four axes (the unified starbridge-app template)
//!
//! * **the verified core** — [`domain_factory_descriptor`] + [`domain_cell_program`]
//!   (this file): a per-domain sovereign cell whose committed slots are
//!   `{domain, site, owner, verification_state, challenge_nonce, verified_seq}`. The
//!   domain / owner / challenge-nonce are sealed (`WriteOnce`) and the verification
//!   is one-way (`Monotonic` on `verification_state` + `verified_seq`) — so a
//!   REBIND of the proven challenge, an owner TAKEOVER, and an UN-VERIFY are all
//!   real executor refusals on the born cell (the tooth `tests/domain_lifecycle.rs`
//!   drives through the executor);
//! * the SERVICE-CELL `invoke()` front door ([`service`]): a typed
//!   `InterfaceDescriptor` (`register` / `bind` / `verify` / `resolve`);
//! * the deos-view CARD ([`card`]): the binding surface as a `deos.ui.*` tree;
//! * the deos surface — the composed [`DeosApp`] ([`domain_app`] / [`register_deos`]).
//!
//! ## Two enforcement surfaces (both REAL)
//!
//! 1. **The bind cap** ([`cap`]) — WHO may bind. A [`cap::DomainCap`] presents a
//!    `dregg-auth` credential that must VERIFY under the registry's trusted root
//!    ([`cap::verify_bind_authority`]) as granting the binding authority for the
//!    domain. A forged / wrong-root / wrong-domain credential is refused, and the
//!    binding's owner is the credential's pinned subject — so only that owner may
//!    later rebind (no takeover). By the no-amplify property of `Credential::attenuate`
//!    a delegate confined to one domain cannot widen back to all.
//! 2. **The domain cell invariants** — [`domain_factory_descriptor`]'s
//!    `state_constraints`, re-enforced by the executor on every touching turn:
//!    `WriteOnce(DOMAIN/OWNER/CHALLENGE_NONCE)` + `Monotonic(VERIFICATION_STATE/VERIFIED_SEQ)`.
//!
//! ## The DNS seam + the gateway reads
//!
//! Verification is driven through the injected [`dns::DnsResolver`] trait — a
//! deterministic [`dns::MockDns`] in tests, a host-wired real DNS client in prod
//! (the sync trait is the seam; a production resolver implements it over a live
//! client). [`registry::DomainRegistry::site_for_host`] maps an inbound custom
//! `Host` -> its bound site *only when verified*, and
//! [`registry::DomainRegistry::is_verified`] is what a gateway's on-demand-TLS `ask`
//! consults — a byte is routed (and a cert minted) only for a domain a tenant has
//! *proven* they control.
//!
//! ## Honest gaps (what this is, and is not)
//!
//! The routing plane's source of truth is the pure serializable
//! [`registry::DomainBinding`] record (the plaintext `domain -> site` map a gateway
//! needs); the cell mirrors its commitments into scalar slots (the executor-enforced
//! invariants) via [`mirror_binding`]. The `WriteOnce`/`Monotonic` teeth and the
//! cap-verify (a forged credential refused, unforgeably) are REAL. A production lane
//! threads the DNS challenge issuance itself through a witnessed-predicate program
//! (so an off-challenge verify is an executor refusal, not just a registry check) —
//! this models the shape; the challenge compare lives in [`dns::challenge_satisfied`].

#![forbid(unsafe_code)]

pub use dregg_app_framework::FieldElement;
use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellAffordance, CellId, CellMode,
    CellProgram, ChildVkStrategy, ConstantsModule, DeosApp, DeosCell, Effect, EmbeddedExecutor,
    Event, FactoryDescriptor, FireExecuteError, GatedAffordance, InspectorDescriptor,
    StarbridgeAppContext, StateConstraint, TurnReceipt, canonical_program_vk, field_from_bytes,
    field_from_u64, hex_encode_32, symbol,
};

use dregg_cell::Cell;

/// The bind-cap bridge: a `dregg-auth` credential verifying under the registry's
/// trusted root as granting the binding authority for a domain.
pub mod cap;
/// The deos-view CARD: the binding surface as a renderer-independent view-tree.
pub mod card;
/// The DNS challenge seam: [`dns::DnsResolver`] + [`dns::MockDns`], domain validity,
/// and the deterministic challenge nonce.
pub mod dns;
/// The custom-domain control plane: the plaintext `domain -> binding` routing index,
/// the cap-gated `bind`, the DNS-driven `verify`, and the gateway reads.
pub mod registry;
/// The CELLS-AS-SERVICE-OBJECTS face: a typed `InterfaceDescriptor` + `invoke()`
/// dispatch over the `register` / `bind` / `verify` / `resolve` vocabulary.
pub mod service;

pub use dns::{ChallengeMethod, DnsChallenge, DnsResolver, MockDns, VerificationState};
pub use registry::{BindReceipt, DomainBinding, DomainError, DomainRegistry};

// =============================================================================
// Slot layout (the per-domain cell) — the program-enforced scalars
// =============================================================================

/// Slot 0 — `domain`. A commitment to the bound custom domain
/// ([`domain_tag`]). `WriteOnce` — the domain a cell is bound to is permanent for
/// the cell's life (the binding `cell -> domain` never re-points).
pub const DOMAIN_SLOT: u8 = 0;
/// Slot 1 — `site`. A commitment to the bound site name ([`site_tag`]). NOT
/// constrained: the owner may freely re-point the domain at a different site
/// (exactly the semantics a custom-domain host wants — repointing does not require
/// re-proving DNS control).
pub const SITE_SLOT: u8 = 1;
/// Slot 2 — `owner`. A commitment to the binding owner's subject ([`owner_tag`]).
/// `WriteOnce` — sealed at register: a live binding can never be re-owned, so no
/// takeover of a victim's domain cell.
pub const OWNER_SLOT: u8 = 2;
/// Slot 3 — `challenge_nonce`. A commitment to the DNS challenge nonce
/// ([`nonce_tag`]). `WriteOnce` — sealed at bind: the value the owner must place in
/// DNS is frozen, so `verify` always checks against a fixed challenge (an attacker
/// cannot re-issue a nonce that matches a record they happen to control).
pub const CHALLENGE_NONCE_SLOT: u8 = 3;
/// Slot 4 — `verification_state`. `0` = pending (bound, control unproven; not routed,
/// no cert), `1` = verified (control proven; routes + eligible for a certificate).
/// `Monotonic` — the flip is one-way: a proven domain can never be un-verified.
pub const VERIFICATION_STATE_SLOT: u8 = 4;
/// Slot 5 — `verified_seq`. The registry-monotonic sequence of the verifying turn
/// (who proved control, when). `Monotonic` — the verification height only advances;
/// a replay / reorder that would rewind it is an executor refusal.
pub const VERIFIED_SEQ_SLOT: u8 = 5;

// =============================================================================
// Factory configuration
// =============================================================================

/// The factory VK the platform publishes for domain-binding cells.
pub const DOMAIN_FACTORY_VK: [u8; 32] = *b"starbridge-domains-binding-fac!!";

/// Default per-epoch slot-creation budget (how many domain cells the factory mints
/// per epoch — a Sybil rate-limit on binding).
pub const DEFAULT_CREATION_BUDGET: u64 = 4_096;

// =============================================================================
// Field helpers + slot commitments
// =============================================================================

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse of
/// [`field_from_u64`]). Used for the `verification_state` / `verified_seq` counters.
pub fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

/// The cell's tag for a custom domain — a domain-separated commitment to the
/// (lowercased) domain string. Always non-zero (a blake3 image), so a zeroed
/// [`DOMAIN_SLOT`] reads as "absent".
pub fn domain_tag(domain: &str) -> FieldElement {
    tag(b"domain:", &domain.trim().to_ascii_lowercase())
}

/// The cell's tag for a bound site name — a domain-separated commitment. What
/// [`SITE_SLOT`] carries (the owner may re-point it freely).
pub fn site_tag(site: &str) -> FieldElement {
    tag(b"domain-site:", site)
}

/// The cell's tag for the binding owner's subject — a domain-separated commitment.
/// What [`OWNER_SLOT`] seals `WriteOnce` (the owner never re-keyed → no takeover).
pub fn owner_tag(owner: &str) -> FieldElement {
    tag(b"domain-owner:", owner)
}

/// The cell's tag for the DNS challenge nonce — a domain-separated commitment. What
/// [`CHALLENGE_NONCE_SLOT`] seals `WriteOnce` (the challenge value is frozen at bind).
pub fn nonce_tag(nonce: &str) -> FieldElement {
    tag(b"domain-nonce:", nonce)
}

/// The field-element image of a [`VerificationState`] — `0` pending, `1` verified.
/// What [`VERIFICATION_STATE_SLOT`] carries (`Monotonic`, one-way).
pub fn state_field(state: VerificationState) -> FieldElement {
    field_from_u64(state.code())
}

/// A domain-separated blake3 commitment `field_from_bytes(prefix || value)`.
fn tag(prefix: &[u8], value: &str) -> FieldElement {
    let mut buf = Vec::with_capacity(prefix.len() + value.len());
    buf.extend_from_slice(prefix);
    buf.extend_from_slice(value.as_bytes());
    field_from_bytes(&buf)
}

// =============================================================================
// The verified core — CellProgram + FactoryDescriptor
// =============================================================================

/// The **life-of-binding invariants** the executor re-enforces on every touching turn:
///
/// * `WriteOnce(DOMAIN)` — the domain a cell is bound to is permanent (never re-pointed);
/// * `WriteOnce(OWNER)` — the owner is sealed at register (no takeover of the cell);
/// * `WriteOnce(CHALLENGE_NONCE)` — the DNS challenge value is frozen at bind, so
///   `verify` always checks a fixed challenge;
/// * `Monotonic(VERIFICATION_STATE)` — the pending -> verified flip is one-way (a
///   proven domain can never be un-verified);
/// * `Monotonic(VERIFIED_SEQ)` — the verification height only advances (no rewind).
///
/// `SITE` is intentionally mutable: the owner may re-point the domain at a different
/// site without re-proving DNS control.
pub fn domain_invariants() -> Vec<StateConstraint> {
    vec![
        StateConstraint::WriteOnce { index: DOMAIN_SLOT },
        StateConstraint::WriteOnce { index: OWNER_SLOT },
        StateConstraint::WriteOnce {
            index: CHALLENGE_NONCE_SLOT,
        },
        StateConstraint::Monotonic {
            index: VERIFICATION_STATE_SLOT,
        },
        StateConstraint::Monotonic {
            index: VERIFIED_SEQ_SLOT,
        },
    ]
}

/// The domain cell program: an `Always` case carrying [`domain_invariants`] (the
/// sealed identity + one-way verification re-enforced on EVERY touching turn). A
/// pure invariants program (no method-dispatch case), so `register` / `bind` /
/// `verify` are each admitted as long as the invariants hold (and the bind-cap
/// [`cap::verify_bind_authority`] gate passes in-band).
pub fn domain_cell_program() -> CellProgram {
    CellProgram::always(domain_invariants())
}

/// The life-of-binding invariants as a flat `Predicate` program — the
/// method-agnostic floor the factory and the executor-side regression tests share.
pub fn domain_invariants_program() -> CellProgram {
    CellProgram::Predicate(domain_invariants())
}

/// Canonical child program VK for domain cells (per `VK-AS-RE-EXECUTION-RECIPE.md`:
/// `canonical_program_vk(&domain_cell_program())` — the VK is a re-execution recipe).
pub fn domain_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&domain_cell_program())
}

/// The platform's factory descriptor for minting per-domain binding cells.
///
/// Pins the constructor contract anyone can audit by hashing the descriptor: the
/// child program VK (the sealed-identity + one-way-verification state machine),
/// `Sovereign` mode (a domain binding lives as its own cell), a creation budget
/// (Sybil rate-limit), and the perpetual [`domain_invariants`] slot caveats every
/// produced cell inherits. Like `nameservice`, it carries NO creation-time
/// `field_constraints`: a born cell is empty (all slots zero) and the FIRST
/// `register` turn writes `DOMAIN` + `OWNER` under the perpetual `WriteOnce` caveats
/// (which admit the first write from zero and bite thereafter).
pub fn domain_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: DOMAIN_FACTORY_VK,
        child_program_vk: Some(domain_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(domain_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            // The binding owner holds an attenuatable SelfCell cap — the root a
            // per-domain delegate cap descends from (attenuated to one domain).
            target: CapTarget::SelfCell,
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        field_constraints: vec![],
        state_constraints: domain_invariants(),
        default_mode: CellMode::Sovereign,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

/// All factory descriptors this starbridge-app contributes (today: one).
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![domain_factory_descriptor()]
}

// =============================================================================
// The cell-state layer — mirror a pure binding record into the committed cell
// =============================================================================

/// **Mirror a pure [`DomainBinding`] record into a domain cell's committed state** —
/// the executor-enforced scalar invariants. After this, the cell's commitment binds
/// the current `(domain, site, owner, verification_state, challenge_nonce, verified_seq)`;
/// a light client reads the binding off the committed cell. Only ever writes forward
/// (a fresh cell is all-zero, so the first mirror is admitted by `WriteOnce` /
/// `Monotonic` from zero).
pub fn mirror_binding(cell: &mut Cell, binding: &DomainBinding) {
    cell.state
        .set_field(DOMAIN_SLOT as usize, domain_tag(&binding.domain));
    cell.state
        .set_field(SITE_SLOT as usize, site_tag(&binding.site));
    cell.state
        .set_field(OWNER_SLOT as usize, owner_tag(&binding.owner));
    cell.state
        .set_field(CHALLENGE_NONCE_SLOT as usize, nonce_tag(&binding.challenge));
    cell.state
        .set_field(VERIFICATION_STATE_SLOT as usize, state_field(binding.state));
    cell.state.set_field(
        VERIFIED_SEQ_SLOT as usize,
        field_from_u64(binding.verified_seq.unwrap_or(0)),
    );
}

/// **Seed a domain cell** so the deos fires have live state + the invariants bite:
/// install [`domain_cell_program`] (so the executor re-enforces the sealed-identity +
/// one-way-verification invariants on every touching turn), then mirror `binding`
/// ([`mirror_binding`]) directly into the embedded ledger. Returns the [`domain_tag`]
/// of the seeded domain.
pub fn seed_domain(executor: &EmbeddedExecutor, binding: &DomainBinding) -> FieldElement {
    let cell = executor.cell_id();
    executor.install_program(cell, domain_cell_program());
    executor.with_ledger_mut(|ledger| {
        if let Some(c) = ledger.get_mut(&cell) {
            mirror_binding(c, binding);
        }
    });
    domain_tag(&binding.domain)
}

// =============================================================================
// Cell-turn effect templates (shared by the deos affordances + the service)
// =============================================================================

/// **The `register` cell effects** — establish a domain binding cell: seal `DOMAIN`
/// + `OWNER` (`WriteOnce`, admit-from-zero) and emit `domain-registered`. The first
/// turn a factory-born cell takes; the executor freezes both slots thereafter.
pub fn register_effects(cell: CellId, domain: &str, owner: &str) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell,
            index: DOMAIN_SLOT as usize,
            value: domain_tag(domain),
        },
        Effect::SetField {
            cell,
            index: OWNER_SLOT as usize,
            value: owner_tag(owner),
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(
                symbol("domain-registered"),
                vec![domain_tag(domain), owner_tag(owner)],
            ),
        },
    ]
}

/// **The `bind` cell effects** — point the domain at `site` and seal the DNS
/// challenge `nonce` (`WriteOnce(CHALLENGE_NONCE)`), then emit `domain-bound`. The
/// DomainCap-gated turn (the cap-verify is the in-band gate; the frozen nonce is the
/// on-cell tooth). `SITE` is un-caveated, so a later re-point is admitted.
pub fn bind_effects(cell: CellId, site: &str, nonce: &str) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell,
            index: SITE_SLOT as usize,
            value: site_tag(site),
        },
        Effect::SetField {
            cell,
            index: CHALLENGE_NONCE_SLOT as usize,
            value: nonce_tag(nonce),
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(
                symbol("domain-bound"),
                vec![site_tag(site), nonce_tag(nonce)],
            ),
        },
    ]
}

/// **The `verify` cell effects** — flip `VERIFICATION_STATE` to `Verified` and set
/// `VERIFIED_SEQ` to `verified_seq`, then emit `domain-verified`. The executor
/// re-enforces `Monotonic(VERIFICATION_STATE)` + `Monotonic(VERIFIED_SEQ)` on the
/// produced transition — so the flip is one-way and a rewound sequence is a real
/// refusal. Built only after [`dns::challenge_satisfied`] holds.
pub fn verify_effects(cell: CellId, verified_seq: u64) -> Vec<Effect> {
    vec![
        Effect::SetField {
            cell,
            index: VERIFICATION_STATE_SLOT as usize,
            value: state_field(VerificationState::Verified),
        },
        Effect::SetField {
            cell,
            index: VERIFIED_SEQ_SLOT as usize,
            value: field_from_u64(verified_seq),
        },
        Effect::EmitEvent {
            cell,
            event: Event::new(
                symbol("domain-verified"),
                vec![field_from_u64(verified_seq)],
            ),
        },
    ]
}

/// Build the on-ledger [`Action`] that records a domain registration (the genesis
/// seal — `DOMAIN` + `OWNER`, sealed `WriteOnce`). The signed turn a caller ships to
/// establish the binding cell.
pub fn build_register_action(cipherclerk: &AppCipherclerk, domain: &str, owner: &str) -> Action {
    let cell = cipherclerk.cell_id();
    cipherclerk.make_action(
        cell,
        "register_domain",
        register_effects(cell, domain, owner),
    )
}

/// Build the on-ledger [`Action`] that records a bind (point at a site + seal the
/// DNS challenge nonce). The DomainCap-gate is checked by the caller before this is
/// built; the frozen `CHALLENGE_NONCE` is the on-cell tooth.
pub fn build_bind_action(cipherclerk: &AppCipherclerk, site: &str, nonce: &str) -> Action {
    let cell = cipherclerk.cell_id();
    cipherclerk.make_action(cell, "bind_domain", bind_effects(cell, site, nonce))
}

/// Build the on-ledger [`Action`] that records a verification (flip
/// `VERIFICATION_STATE` + advance `VERIFIED_SEQ`). Built only after the DNS challenge
/// is satisfied; the executor re-enforces the `Monotonic` teeth.
pub fn build_verify_action(cipherclerk: &AppCipherclerk, verified_seq: u64) -> Action {
    let cell = cipherclerk.cell_id();
    cipherclerk.make_action(cell, "verify_domain", verify_effects(cell, verified_seq))
}

// =============================================================================
// The deos-native surface — the binding as a composed DeosApp
// =============================================================================

/// The binding rights tiers, on the real attenuation lattice:
/// * the OWNER holds [`AuthRequired::None`]/root — it can `register` / `bind` /
///   `verify` (the full binding lifecycle);
/// * a RESOLVER (the public / a gateway) holds [`AuthRequired::Signature`] — the
///   narrow read tier: it can `resolve` (read the verified `site` a domain points at)
///   and nothing else.
///
/// So `Signature ⊂ None` IS the resolver ⊂ owner ladder — a two-tier domain authority.
pub const OWNER_RIGHTS: AuthRequired = AuthRequired::None;
/// The resolver (read) rights tier — see [`OWNER_RIGHTS`].
pub const RESOLVER_RIGHTS: AuthRequired = AuthRequired::Signature;

/// The owner-lifecycle + read method names on a domain cell — the deos affordance
/// vocabulary [`domain_app`] exposes and the `fire_*` helpers route. Shared constants
/// so an affordance's name, its `fire_*` lookup, and the card's button `turn` payload
/// (`src/card.rs`) can never drift apart.
pub const METHOD_REGISTER: &str = "register";
/// The OWNER points the domain at a site + issues the DNS challenge — the
/// DomainCap-gated, `WriteOnce(CHALLENGE_NONCE)` op. See [`METHOD_REGISTER`].
pub const METHOD_BIND: &str = "bind";
/// The OWNER flips the domain to verified once DNS proves control — the one-way
/// `Monotonic` op. See [`METHOD_REGISTER`].
pub const METHOD_VERIFY: &str = "verify";
/// A RESOLVER reads the verified `site` a domain points at. See [`METHOD_REGISTER`].
pub const METHOD_RESOLVE: &str = "resolve";

/// The **not-yet-verified precondition** — the domain must still be PENDING
/// (`VERIFICATION_STATE == 0`). A real [`CellProgram`] read against the cell's live
/// state, so the `verify` button is LIT on a pending domain and goes DARK the instant
/// it is verified (the htmx tooth). The one-way `Monotonic(VERIFICATION_STATE)` is the
/// installed invariant the executor re-enforces on the produced transition.
pub fn pending_precondition() -> CellProgram {
    CellProgram::Predicate(vec![StateConstraint::FieldEquals {
        index: VERIFICATION_STATE_SLOT,
        value: field_from_u64(VerificationState::Pending.code()),
    }])
}

/// **The custom-domain binding as a composed [`DeosApp`]** — the whole lifecycle
/// surface on the deos bones. The domain cell is the acting agent's own cell
/// (`cipherclerk.cell_id()`).
///
/// * `register` — cap-only (the OWNER establishes + seals the binding): `None`/root,
///   a `SetField` sealing `OWNER` (the genesis representative);
/// * `bind` — cap-only (the OWNER points at a site + seals the nonce): `None`/root, a
///   `SetField` sealing `CHALLENGE_NONCE` (the DomainCap-gated write);
/// * `verify` — a [`GatedAffordance`] (the OWNER proves DNS control): `None`/root, the
///   not-yet-verified PRECONDITION; the real fire ([`fire_verify`]) submits a turn that
///   flips `VERIFICATION_STATE` + advances `VERIFIED_SEQ` off the LIVE height,
///   re-enforced by the executor's `Monotonic` teeth (a re-verify goes DARK, a rewind
///   is refused);
/// * `resolve` — cap-only (a RESOLVER reads the target): `Signature`, an `EmitEvent`
///   reading `SITE`.
///
/// Seed the cell's program + genesis state with [`seed_domain`] so the gated fire has
/// live state and the executor re-enforces the invariants.
pub fn domain_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let cell = cipherclerk.cell_id();

    let register = CellAffordance::new(
        METHOD_REGISTER,
        OWNER_RIGHTS,
        Effect::SetField {
            cell,
            index: OWNER_SLOT as usize,
            value: owner_tag("owner"),
        },
    );
    let bind = CellAffordance::new(
        METHOD_BIND,
        OWNER_RIGHTS,
        Effect::SetField {
            cell,
            index: CHALLENGE_NONCE_SLOT as usize,
            value: nonce_tag("challenge"),
        },
    );
    let verify = GatedAffordance::new(
        CellAffordance::new(
            METHOD_VERIFY,
            OWNER_RIGHTS,
            Effect::SetField {
                cell,
                index: VERIFICATION_STATE_SLOT as usize,
                value: state_field(VerificationState::Verified),
            },
        ),
        pending_precondition(),
    );
    let resolve = CellAffordance::new(
        METHOD_RESOLVE,
        RESOLVER_RIGHTS,
        Effect::EmitEvent {
            cell,
            event: Event::new(
                symbol("domain-resolved"),
                vec![field_from_u64(SITE_SLOT as u64)],
            ),
        },
    );

    DeosApp::builder("domains", cipherclerk.clone(), executor.clone())
        .discoverable(vec!["domains".into(), "custom-domains".into()])
        .cell(
            DeosCell::new(cell, "domain")
                .affordance(register)
                .affordance(bind)
                .gated(verify)
                .affordance(resolve)
                // Published at the RESOLVER tier (`Signature`) — the narrowest tier
                // that holds the binding (a gateway reacquires the verified target).
                .publish(RESOLVER_RIGHTS),
        )
        .build()
}

/// **Fire `verify`** — the deos cap∧state PRECONDITION gate (cap ⊇ root AND the domain
/// is still pending), then a turn that flips `VERIFICATION_STATE` -> verified and
/// advances `VERIFIED_SEQ` off the cell's LIVE height (by one). The two-tempo bridge:
/// the gated affordance decides the button in-band (nothing submitted once verified);
/// on passing, the executor's re-enforcement of `Monotonic(VERIFICATION_STATE)` +
/// `Monotonic(VERIFIED_SEQ)` is the SECOND, verified gate — a re-verify / rewind is a
/// real refusal. Use [`seed_domain`] first.
pub fn fire_verify(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
) -> Result<TurnReceipt, FireExecuteError> {
    let deos_cell = &app.cells()[0];
    let domain_cell = deos_cell.cell();
    deos_cell.fire_gated_through_executor_with(
        METHOD_VERIFY,
        held,
        cipherclerk,
        executor,
        move |live| {
            // The verified height advances the LIVE height by one (Monotonic holds).
            let live_seq = field_to_u64(&live.fields[VERIFIED_SEQ_SLOT as usize]);
            verify_effects(domain_cell, live_seq + 1)
        },
    )
}

// =============================================================================
// StarbridgeAppContext mount
// =============================================================================

/// **Mount the deos-native surface** ([`domain_app`]) on a shared context: build the
/// composed [`DeosApp`], seed a demo domain cell's program + genesis state (a bound,
/// still-pending domain so the gated `verify` fire is LIT), and fold the app into the
/// context's affordance registry. Returns the live [`DeosApp`].
pub fn register_deos(ctx: &StarbridgeAppContext) -> DeosApp {
    let app = domain_app(ctx.cipherclerk(), ctx.executor());
    // A demo binding so the gated `verify` fire has live state (PENDING, so the
    // not-yet-verified precondition is LIT), and the invariants bite on every turn.
    let demo = DomainBinding::pending(
        "blog.acme.dev",
        "blog",
        "dregg:owner",
        ChallengeMethod::Txt,
        "dregg-verify-demo",
    );
    seed_domain(ctx.executor(), &demo);
    app.register(ctx);
    app
}

/// **Register the domains starbridge-app** on a shared context — the FLOOR (the
/// factory descriptor whose `state_constraints` seal the binding identity + the
/// one-way verification, installed on every born domain cell) AND the deos-native
/// composition surface (the [`DeosApp`], folded into the context's affordance
/// registry). Returns the factory VK.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(domain_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "domain".into(),
        descriptor: serde_json::json!({
            "component": "dregg-domain",
            "module": "/starbridge-apps/domains/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": ["domain", "site", "owner", "verification_state", "challenge_nonce"],
            "slot_layout": {
                "domain": DOMAIN_SLOT,
                "site": SITE_SLOT,
                "owner": OWNER_SLOT,
                "challenge_nonce": CHALLENGE_NONCE_SLOT,
                "verification_state": VERIFICATION_STATE_SLOT,
                "verified_seq": VERIFIED_SEQ_SLOT,
            },
            "factory_vk_hex": hex_encode_32(&factory_vk),
            "child_program_vk_hex": hex_encode_32(&domain_child_program_vk()),
            "methods": ["register", "bind", "verify", "resolve"],
        }),
    });

    register_deos(ctx);
    factory_vk
}

/// The canonical web-constants module — the slot layout + factory VK + event topics
/// the JS surface is rendered from. Every value is read from this crate's `pub const`s
/// / `symbol(..)` topics, so a consumer cannot drift from the executor's slot layout.
pub fn web_constants() -> ConstantsModule {
    ConstantsModule::new("domains")
        .slot("DOMAIN_SLOT", DOMAIN_SLOT as u64)
        .slot("SITE_SLOT", SITE_SLOT as u64)
        .slot("OWNER_SLOT", OWNER_SLOT as u64)
        .slot("CHALLENGE_NONCE_SLOT", CHALLENGE_NONCE_SLOT as u64)
        .slot("VERIFICATION_STATE_SLOT", VERIFICATION_STATE_SLOT as u64)
        .slot("VERIFIED_SEQ_SLOT", VERIFIED_SEQ_SLOT as u64)
        .string("FACTORY_VK_HEX", hex_encode_32(&DOMAIN_FACTORY_VK))
        .string("TXT_CHALLENGE_PREFIX", dns::TXT_CHALLENGE_PREFIX)
        .topic("REGISTERED", "domain-registered")
        .topic("BOUND", "domain-bound")
        .topic("VERIFIED", "domain-verified")
        .topic("RESOLVED", "domain-resolved")
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{AgentCipherclerk, EmbeddedExecutor};
    use dregg_cell::CellProgram as CellProg;

    fn test_context() -> StarbridgeAppContext {
        let cipherclerk = AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32]);
        let executor = EmbeddedExecutor::new(&cipherclerk, "default");
        StarbridgeAppContext::new(cipherclerk, executor)
    }

    #[test]
    fn factory_descriptor_is_stable_and_pins_program_vk() {
        assert_eq!(
            domain_factory_descriptor().hash(),
            domain_factory_descriptor().hash(),
            "descriptor hash must be deterministic"
        );
        let d = domain_factory_descriptor();
        assert_eq!(d.factory_vk, DOMAIN_FACTORY_VK);
        assert_eq!(d.child_program_vk, Some(domain_child_program_vk()));
        assert_eq!(d.default_mode, CellMode::Sovereign);
        assert_eq!(d.creation_budget, Some(DEFAULT_CREATION_BUDGET));
    }

    #[test]
    fn factory_bakes_the_slot_caveats() {
        let d = domain_factory_descriptor();
        for want in [
            StateConstraint::WriteOnce { index: DOMAIN_SLOT },
            StateConstraint::WriteOnce { index: OWNER_SLOT },
            StateConstraint::WriteOnce {
                index: CHALLENGE_NONCE_SLOT,
            },
            StateConstraint::Monotonic {
                index: VERIFICATION_STATE_SLOT,
            },
            StateConstraint::Monotonic {
                index: VERIFIED_SEQ_SLOT,
            },
        ] {
            assert!(
                d.state_constraints.contains(&want),
                "factory must install {want:?}"
            );
        }
        // Pin the exact set so additions are caught in review.
        assert_eq!(d.state_constraints.len(), 5);
        // SITE is intentionally unconstrained (the owner may re-point freely).
        for c in &d.state_constraints {
            if let StateConstraint::WriteOnce { index }
            | StateConstraint::Immutable { index }
            | StateConstraint::Monotonic { index }
            | StateConstraint::StrictMonotonic { index } = c
            {
                assert_ne!(*index, SITE_SLOT, "SITE_SLOT must remain unconstrained");
            }
        }
    }

    // ── Executor-side regression: the slot caveats bite. ─────────────────────

    fn program() -> CellProg {
        CellProg::Predicate(domain_invariants())
    }

    fn empty_state() -> dregg_cell::state::CellState {
        dregg_cell::state::CellState::new(0)
    }

    #[test]
    fn legal_register_then_bind_then_verify_succeeds() {
        let p = program();
        // Register: seal DOMAIN + OWNER from a fresh (all-zero) cell.
        let old = empty_state();
        let mut registered = empty_state();
        registered.fields[DOMAIN_SLOT as usize] = domain_tag("blog.acme.dev");
        registered.fields[OWNER_SLOT as usize] = owner_tag("dregg:alice");
        assert!(
            p.evaluate(&registered, Some(&old), None).is_ok(),
            "sealing DOMAIN + OWNER from zero is admitted"
        );

        // Bind: seal CHALLENGE_NONCE + point SITE.
        let mut bound = registered.clone();
        bound.set_nonce(1);
        bound.fields[SITE_SLOT as usize] = site_tag("blog");
        bound.fields[CHALLENGE_NONCE_SLOT as usize] = nonce_tag("dregg-verify-abc");
        assert!(p.evaluate(&bound, Some(&registered), None).is_ok());

        // Verify: flip VERIFICATION_STATE 0 -> 1 and advance VERIFIED_SEQ 0 -> 1.
        let mut verified = bound.clone();
        verified.set_nonce(2);
        verified.fields[VERIFICATION_STATE_SLOT as usize] =
            state_field(VerificationState::Verified);
        verified.fields[VERIFIED_SEQ_SLOT as usize] = field_from_u64(1);
        assert!(p.evaluate(&verified, Some(&bound), None).is_ok());
    }

    #[test]
    fn re_pointing_the_owner_is_a_write_once_violation() {
        let p = program();
        let mut old = empty_state();
        old.set_nonce(1);
        old.fields[OWNER_SLOT as usize] = owner_tag("dregg:alice");
        let mut new = old.clone();
        new.fields[OWNER_SLOT as usize] = owner_tag("dregg:mallory");
        let err = p
            .evaluate(&new, Some(&old), None)
            .expect_err("re-owning a bound domain cell must be refused");
        assert!(matches!(
            err,
            dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::WriteOnce { index },
                ..
            } if index == OWNER_SLOT
        ));
    }

    #[test]
    fn re_issuing_the_challenge_nonce_is_a_write_once_violation() {
        let p = program();
        let mut old = empty_state();
        old.set_nonce(1);
        old.fields[CHALLENGE_NONCE_SLOT as usize] = nonce_tag("dregg-verify-abc");
        let mut new = old.clone();
        new.fields[CHALLENGE_NONCE_SLOT as usize] = nonce_tag("dregg-verify-attacker");
        let err = p
            .evaluate(&new, Some(&old), None)
            .expect_err("re-issuing a frozen challenge nonce must be refused");
        assert!(matches!(
            err,
            dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::WriteOnce { index },
                ..
            } if index == CHALLENGE_NONCE_SLOT
        ));
    }

    #[test]
    fn un_verifying_is_a_monotonic_violation() {
        let p = program();
        // A verified domain (state = 1, seq = 3).
        let mut old = empty_state();
        old.set_nonce(2);
        old.fields[VERIFICATION_STATE_SLOT as usize] = state_field(VerificationState::Verified);
        old.fields[VERIFIED_SEQ_SLOT as usize] = field_from_u64(3);
        // Attempt: roll VERIFICATION_STATE 1 -> 0 (un-verify).
        let mut new = old.clone();
        new.fields[VERIFICATION_STATE_SLOT as usize] = state_field(VerificationState::Pending);
        let err = p
            .evaluate(&new, Some(&old), None)
            .expect_err("un-verifying a proven domain must be refused");
        assert!(matches!(
            err,
            dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::Monotonic { index },
                ..
            } if index == VERIFICATION_STATE_SLOT
        ));
    }

    #[test]
    fn rewinding_the_verified_seq_is_a_monotonic_violation() {
        let p = program();
        let mut old = empty_state();
        old.set_nonce(2);
        old.fields[VERIFIED_SEQ_SLOT as usize] = field_from_u64(5);
        let mut new = old.clone();
        new.fields[VERIFIED_SEQ_SLOT as usize] = field_from_u64(4);
        let err = p
            .evaluate(&new, Some(&old), None)
            .expect_err("rewinding the verification height must be refused");
        assert!(matches!(
            err,
            dregg_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::Monotonic { index },
                ..
            } if index == VERIFIED_SEQ_SLOT
        ));
    }

    // ── Effect templates + mirror. ───────────────────────────────────────────

    #[test]
    fn register_effects_seal_domain_and_owner() {
        let cell = CellId::from_bytes([5u8; 32]);
        let effects = register_effects(cell, "blog.acme.dev", "dregg:alice");
        assert_eq!(effects.len(), 3);
        assert!(matches!(
            &effects[0],
            Effect::SetField { index, value, .. }
                if *index == DOMAIN_SLOT as usize && *value == domain_tag("blog.acme.dev")
        ));
        assert!(matches!(
            &effects[1],
            Effect::SetField { index, value, .. }
                if *index == OWNER_SLOT as usize && *value == owner_tag("dregg:alice")
        ));
        assert!(matches!(&effects[2], Effect::EmitEvent { .. }));
    }

    #[test]
    fn verify_effects_flip_state_and_advance_seq() {
        let cell = CellId::from_bytes([6u8; 32]);
        let effects = verify_effects(cell, 7);
        assert_eq!(effects.len(), 3);
        assert!(matches!(
            &effects[0],
            Effect::SetField { index, value, .. }
                if *index == VERIFICATION_STATE_SLOT as usize
                    && *value == state_field(VerificationState::Verified)
        ));
        assert!(matches!(
            &effects[1],
            Effect::SetField { index, value, .. }
                if *index == VERIFIED_SEQ_SLOT as usize && *value == field_from_u64(7)
        ));
    }

    #[test]
    fn mirror_binding_writes_the_committed_slots() {
        let binding = DomainBinding::verified(
            "blog.acme.dev",
            "blog",
            "dregg:alice",
            ChallengeMethod::Txt,
            "dregg-verify-abc",
            9,
        );
        let mut cell = Cell::with_balance([7u8; 32], [9u8; 32], 0);
        mirror_binding(&mut cell, &binding);
        assert_eq!(
            cell.state.get_field(DOMAIN_SLOT as usize).copied(),
            Some(domain_tag("blog.acme.dev"))
        );
        assert_eq!(
            cell.state.get_field(OWNER_SLOT as usize).copied(),
            Some(owner_tag("dregg:alice"))
        );
        assert_eq!(
            field_to_u64(
                cell.state
                    .get_field(VERIFICATION_STATE_SLOT as usize)
                    .unwrap()
            ),
            VerificationState::Verified.code()
        );
        assert_eq!(
            field_to_u64(cell.state.get_field(VERIFIED_SEQ_SLOT as usize).unwrap()),
            9
        );
    }

    // ── The deos mount + the gated verify fire through the executor. ──────────

    #[test]
    fn register_installs_factory_inspector_and_deos_surface() {
        let ctx = test_context();
        let vk = register(&ctx);
        assert_eq!(vk, DOMAIN_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
        assert!(ctx.inspector_registry().get("domain").is_some());
        assert_eq!(
            ctx.affordance_registry().len(),
            1,
            "register mounts the deos surface on the same context"
        );
    }

    #[test]
    fn seed_then_fire_verify_flips_state_once_through_the_executor() {
        // A demo binding (PENDING): the gated `verify` precondition is LIT, and the
        // flip commits, moving VERIFICATION_STATE 0 -> 1 through a real signed turn.
        let ctx = test_context();
        let app = domain_app(ctx.cipherclerk(), ctx.executor());
        let demo = DomainBinding::pending(
            "blog.acme.dev",
            "blog",
            "dregg:owner",
            ChallengeMethod::Txt,
            "dregg-verify-seed",
        );
        seed_domain(ctx.executor(), &demo);

        let before = ctx
            .executor()
            .cell_state(ctx.executor().cell_id())
            .unwrap()
            .fields[VERIFICATION_STATE_SLOT as usize];
        assert_eq!(field_to_u64(&before), VerificationState::Pending.code());

        let receipt = fire_verify(&app, &OWNER_RIGHTS, ctx.cipherclerk(), ctx.executor())
            .expect("the owner verifies through the gated fire");
        assert_ne!(receipt.turn_hash, [0u8; 32]);

        let after = ctx
            .executor()
            .cell_state(ctx.executor().cell_id())
            .unwrap()
            .fields[VERIFICATION_STATE_SLOT as usize];
        assert_eq!(
            field_to_u64(&after),
            VerificationState::Verified.code(),
            "the verification state flipped to verified"
        );
    }
}
