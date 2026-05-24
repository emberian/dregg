//! # starbridge-nameservice
//!
//! Greenfield rebuild of the nameservice as a **starbridge-app**: a thin
//! library of `FactoryDescriptor`s plus turn-builder helpers that compose
//! pyana-native primitives only. No `Effect::RegisterName`, no
//! `Authorization::Unchecked`, no `[0u8; 64]` placeholder signatures, no
//! reaching past the framework into `pyana_turn::builder::*`.
//!
//! Companion docs:
//! - `../../../STARBRIDGE-APPS-PLAN.md` §3.1 ("nameservice — recommended
//!   first build") — the per-app design sketch this crate implements.
//! - `../../../SLOT-CAVEATS-DESIGN.md` — the design lane (Lane G) for
//!   slot-level caveats; the `register_name` flow below has a TODO on
//!   the `WriteOnce` constraint that lives there.
//! - `../../../APPS-AS-USERSPACE-AUDIT.md` §1.3 — the userspace audit
//!   that motivated rebuilding nameservice as pyana-native.
//!
//! ## What this crate exports
//!
//! 1. [`name_factory_descriptor`] — the `FactoryDescriptor` for
//!    per-name sovereign cells (rent + ownership state machine). Bakes
//!    in the rent-extension field constraint, the
//!    monotone-increasing name-hash slot, and a per-epoch creation
//!    budget to rate-limit Sybil registration.
//!
//! 2. [`FACTORY_DESCRIPTORS`] — a slice of all factory descriptors this
//!    starbridge-app contributes. The wasm runtime preloads these at
//!    startup so `window.pyana.createFromFactory(factory_vk, ..)` can
//!    resolve string VKs into real descriptors. (Today the slice has
//!    one entry; the dispute-resolution factory and the registry
//!    factory follow once Tier-2 paired escrow lands — see
//!    `STARBRIDGE-APPS-PLAN.md` §3.1 "Real version".)
//!
//! 3. [`build_register_action`] — turn-builder helper that takes an
//!    [`AppWallet`] and produces a real signed
//!    [`Action`] recording a name registration via
//!    `Effect::SetField` + `Effect::EmitEvent`. No new Effect variant
//!    is introduced.
//!
//! 4. [`build_renew_action`] — increments the registry cell's
//!    `EXPIRY_SLOT` by the configured rent-extension epoch length and
//!    emits a `name-renewed` event. The on-cell `FieldDelta` constraint
//!    baked into the factory descriptor enforces the increment is
//!    exact.
//!
//! 5. [`build_transfer_action`] — emits `name-transferred` and updates
//!    the owner-hash slot. Uses two events + two SetFields composed in
//!    a single action; capability handoff (`Effect::GrantCapability` /
//!    `Effect::RevokeCapability`) is the responsibility of the
//!    capability-broker turn that issues *with* this one — kept
//!    separate so this helper stays pure-state.
//!
//! ## The userspace stance
//!
//! "Register a name" is *userspace policy*, not a pyana primitive. The
//! ledger only needs to see:
//!
//! 1. **A name binding** — `SetField(NAME_HASH_SLOT, name_hash)` —
//!    anchoring the registration in cell state.
//! 2. **An owner binding** — `SetField(OWNER_HASH_SLOT, owner_hash)`.
//! 3. **An expiry binding** — `SetField(EXPIRY_SLOT, expiry_height)`.
//! 4. **An event for off-chain indexers** —
//!    `EmitEvent("name-registered", [name_hash, owner_hash])`.
//!
//! If we needed *cell-program-enforced uniqueness* ("the slot at
//! index `NAME_HASH_SLOT` may only be set if its prior value is
//! zero"), that's a **cell program caveat** (`WriteOnce`), not a new
//! `Effect` variant — see the TODO on [`build_register_action`].
//!
//! ## Compatibility with the in-browser PyanaRuntime + extension wallet
//!
//! `build_register_action` returns an [`Action`] carrying a real
//! `Authorization::Signature(..)` produced by the wallet. That action
//! is what `wallet::signTurn(turnSpec)` (the extension API
//! surface — see `../../../extension/src/page.ts`) expects to wrap in
//! a `Turn` for submission. The in-browser `PyanaRuntime`
//! (`../../../wasm/src/runtime.rs`) executes the resulting turn
//! against the same `pyana_turn::TurnExecutor` code-path that native
//! CLIs use.

use pyana_app_framework::{
    Action, AppWallet, AuthRequired, CapTarget, CapTemplate, CellId, CellMode, ChildVkStrategy,
    Effect, Event, FactoryDescriptor, FieldConstraint, FieldElement, InspectorDescriptor,
    StarbridgeAppContext, StateConstraint, symbol,
};

// =============================================================================
// State schema (per-registry-cell field-slot layout)
// =============================================================================

/// State field slot at which a registered name's hash is anchored.
///
/// Slot indices are 0..8 (per [`pyana_cell::STATE_SLOTS`]); `nonce` and
/// `balance` are *not* in `fields[]` (they live on separate `CellState`
/// accessors), so all 8 slots are addressable. The constants here pin a
/// stable schema so:
///
/// - The factory descriptor's `FieldConstraint::NonZero { field_index:
///   NAME_HASH_SLOT as u32 }` constraint is meaningful.
/// - The wasm-side inspector (`shared/inspectors/name.js`) can index
///   into the cell's state at the same slot.
pub const NAME_HASH_SLOT: usize = 2;

/// State field slot at which the registered name's owner-hash is anchored.
pub const OWNER_HASH_SLOT: usize = 3;

/// State field slot at which the rent expiry block height is recorded.
pub const EXPIRY_SLOT: usize = 4;

// =============================================================================
// Rent / factory configuration
// =============================================================================

/// Default rent-extension window (in blocks) baked into the name factory.
///
/// One year ≈ 31_536_000 seconds; at a notional 6-second block time
/// that's ~5_256_000 blocks. Chosen so a single `renew` extends a
/// name's expiry by one "year" of clock time.
pub const DEFAULT_RENT_EPOCH_BLOCKS: u64 = 5_256_000;

/// Creation budget per epoch baked into the name factory.
///
/// Rate-limits Sybil registration: at most 10_000 names may be
/// created per epoch from this factory.
pub const DEFAULT_CREATION_BUDGET: u64 = 10_000;

/// The factory VK we publish for the name factory.
///
/// In a real deployment this is the BLAKE3 hash of the
/// `NAMESERVICE_NAME_PROGRAM_VK` cell-program VK. We bake a stable
/// placeholder here so the descriptor hash is reproducible across
/// builds; the eventual real-program VK replacement is a single
/// constant change.
pub const NAME_FACTORY_VK: [u8; 32] = *b"starbridge-nameservice-factory!!";

/// The child cell program VK installed on per-name cells.
///
/// As above, a stable placeholder. The real VK is the verifying key
/// of the (yet-to-be-written) `name_program.rs` AIR that enforces
/// `WriteOnce(NAME_HASH_SLOT)` and `FieldDelta(EXPIRY_SLOT, +epoch)`
/// in-circuit.
pub const NAME_CHILD_PROGRAM_VK: [u8; 32] = *b"starbridge-nameservice-childprog";

// =============================================================================
// FactoryDescriptors (the constructor transparency)
// =============================================================================

/// Build the `FactoryDescriptor` for the per-name sovereign-cell factory.
///
/// Pins the constructor contract anyone can audit by hashing the
/// descriptor:
///
/// - `child_program_vk = NAME_CHILD_PROGRAM_VK` — the rent +
///   ownership state machine.
/// - `default_mode = Sovereign` — names live as their own cells, not
///   inside a host.
/// - `creation_budget = DEFAULT_CREATION_BUDGET` (rate-limits Sybil
///   registration to 10_000 per epoch).
/// - `allowed_cap_templates = [owner_cap]` — the factory may grant a
///   single attenuatable, signature-authorized capability to the
///   creator (the owner cap). Renewal, transfer, sub-delegation are
///   all derived from the owner cap via attenuation
///   (`Caveat::ResourcePrefix`, etc.); the factory itself does not
///   mint those separately.
/// - `field_constraints` (creation-time): every created name cell *must*
///     initialize its `NAME_HASH_SLOT` and `EXPIRY_SLOT` to non-zero
///     values. These run once at constructor invocation.
/// - `state_constraints` (perpetual / Lane G slot caveats):
///   - `StateConstraint::WriteOnce { index: NAME_HASH_SLOT }` — the
///     name-hash slot may only be written from `FIELD_ZERO`. After the
///     first registration the slot is frozen for the cell's lifetime.
///     This closes `APPS-USERSPACE-GAPS.md` Gap 1 ("name-hash slot may
///     only be written once") — the gap that the
///     `SLOT-CAVEATS-DESIGN.md` TODO above pointed at.
///   - `StateConstraint::Monotonic { index: EXPIRY_SLOT }` — rent
///     extensions may only push the expiry *forward*; an attacker
///     cannot shorten a rental they've already sold by writing a
///     smaller expiry value.
pub fn name_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: NAME_FACTORY_VK,
        child_program_vk: Some(NAME_CHILD_PROGRAM_VK),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(NAME_CHILD_PROGRAM_VK))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        field_constraints: vec![
            FieldConstraint::NonZero {
                field_index: NAME_HASH_SLOT as u32,
            },
            FieldConstraint::NonZero {
                field_index: EXPIRY_SLOT as u32,
            },
        ],
        state_constraints: vec![
            StateConstraint::WriteOnce {
                index: NAME_HASH_SLOT as u8,
            },
            StateConstraint::Monotonic {
                index: EXPIRY_SLOT as u8,
            },
        ],
        default_mode: CellMode::Sovereign,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

/// The full slice of factory descriptors this starbridge-app contributes.
///
/// Today: one entry (the name factory). Future:
/// - A `dispute_factory` for the paired-escrow dispute flow (blocked
///   on Tier-2 #6, paired escrow).
/// - A `registry_factory` for the federation-attested reverse-index
///   `CommittedMap<TargetUri, NameId>` cell (blocked on Tier-2 #10,
///   `CommittedMap<K, V>`).
///
/// Returned as a `Vec` (not `&'static [..]`) because
/// `FactoryDescriptor` carries non-`const`-constructible
/// `Vec<CapTemplate>` / `Vec<FieldConstraint>` fields. Hosts call
/// this once at startup and stash the result.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![name_factory_descriptor()]
}

// =============================================================================
// Turn-builders (signed actions consuming only generic Effects)
// =============================================================================

/// Build the on-ledger [`Action`] that records a name registration.
///
/// The action carries four effects:
///
/// 1. `SetField(cell=registry_cell, index=NAME_HASH_SLOT, value=name_hash)`
///    — anchors the name binding in the cell's state.
/// 2. `SetField(cell=registry_cell, index=OWNER_HASH_SLOT, value=owner_hash)`
///    — anchors the owner.
/// 3. `SetField(cell=registry_cell, index=EXPIRY_SLOT, value=expiry_height)`
///    — anchors the rent expiry. The on-cell `FieldDelta` constraint
///    (when Tier-1 #1 lands) enforces subsequent `renew_name` turns
///    increment exactly by `DEFAULT_RENT_EPOCH_BLOCKS`.
/// 4. `EmitEvent(cell=registry_cell, topic="name-registered",
///    data=[name_hash, owner_hash, expiry])` — surfaces the
///    registration for off-chain indexers.
///
/// The action is signed by the framework's [`AppWallet`]; the
/// signature binds to the wallet's `federation_id`.
///
/// # Slot-caveat enforcement
///
/// The "name-hash slot may only be written once" guarantee is now
/// enforced by [`name_factory_descriptor`]'s
/// `StateConstraint::WriteOnce { index: NAME_HASH_SLOT }` — every name
/// cell carries this caveat on its `CellProgram`, and the executor
/// rejects any subsequent `SetField(NAME_HASH_SLOT, ..)` that would
/// overwrite a non-zero slot. Likewise,
/// `StateConstraint::Monotonic { index: EXPIRY_SLOT }` prevents
/// expiry decreases. See `SLOT-CAVEATS-DESIGN.md` and
/// `SLOT-CAVEATS-EVALUATION.md` for the Lane G design that landed
/// these.
pub fn build_register_action(
    wallet: &AppWallet,
    registry_cell: CellId,
    name: &str,
    owner: [u8; 32],
    expiry_height: u64,
) -> Action {
    let name_hash = blake3_field(name.as_bytes());
    let owner_hash = blake3_field(&owner);
    let expiry_field = u64_field(expiry_height);

    let effects = vec![
        Effect::SetField {
            cell: registry_cell,
            index: NAME_HASH_SLOT,
            value: name_hash,
        },
        Effect::SetField {
            cell: registry_cell,
            index: OWNER_HASH_SLOT,
            value: owner_hash,
        },
        Effect::SetField {
            cell: registry_cell,
            index: EXPIRY_SLOT,
            value: expiry_field,
        },
        Effect::EmitEvent {
            cell: registry_cell,
            event: Event::new(
                symbol("name-registered"),
                vec![name_hash, owner_hash, expiry_field],
            ),
        },
    ];

    wallet.make_action(registry_cell, "register_name", effects)
}

/// Build the on-ledger [`Action`] that extends a name's rent.
///
/// Emits a `name-renewed` event and updates the `EXPIRY_SLOT` to
/// `new_expiry_height = old_expiry + rent_epoch_blocks`. The caller is
/// responsible for reading the prior expiry off the cell state and
/// supplying the correct `new_expiry_height` — when the
/// `FieldDelta(EXPIRY_SLOT, +rent_epoch_blocks)` constraint (Tier 1 #1)
/// lands on the cell program, an off-by-one will be rejected at
/// execution time.
pub fn build_renew_action(
    wallet: &AppWallet,
    registry_cell: CellId,
    name: &str,
    new_expiry_height: u64,
) -> Action {
    let name_hash = blake3_field(name.as_bytes());
    let new_expiry_field = u64_field(new_expiry_height);

    let effects = vec![
        Effect::SetField {
            cell: registry_cell,
            index: EXPIRY_SLOT,
            value: new_expiry_field,
        },
        Effect::EmitEvent {
            cell: registry_cell,
            event: Event::new(symbol("name-renewed"), vec![name_hash, new_expiry_field]),
        },
    ];

    wallet.make_action(registry_cell, "renew_name", effects)
}

/// Build the on-ledger [`Action`] that records a name-owner transfer.
///
/// Updates `OWNER_HASH_SLOT` and emits `name-transferred` with the
/// old/new owner hashes. Capability handoff
/// (`Effect::GrantCapability` to the new owner /
/// `Effect::RevokeCapability` from the old owner) is intentionally
/// *not* part of this action — capability brokerage is the
/// responsibility of the issuer turn that pairs with this one,
/// because the broker's identity is typically distinct from the
/// owner's. Composing them at the call-site (rather than
/// hard-coding the pair here) keeps the helper pure-state.
pub fn build_transfer_action(
    wallet: &AppWallet,
    registry_cell: CellId,
    name: &str,
    old_owner: [u8; 32],
    new_owner: [u8; 32],
) -> Action {
    let name_hash = blake3_field(name.as_bytes());
    let old_hash = blake3_field(&old_owner);
    let new_hash = blake3_field(&new_owner);

    let effects = vec![
        Effect::SetField {
            cell: registry_cell,
            index: OWNER_HASH_SLOT,
            value: new_hash,
        },
        Effect::EmitEvent {
            cell: registry_cell,
            event: Event::new(
                symbol("name-transferred"),
                vec![name_hash, old_hash, new_hash],
            ),
        },
    ];

    wallet.make_action(registry_cell, "transfer_name", effects)
}

// =============================================================================
// StarbridgeAppContext mount
// =============================================================================

/// Register the nameservice starbridge-app on a [`StarbridgeAppContext`].
///
/// Concrete `register(ctx)` hook a host calls at startup to bind this
/// app's factory descriptors and inspector surfaces into the shared
/// context. After this call:
///
/// - `ctx.factory_registry().get(&NAME_FACTORY_VK)` returns the
///   [`name_factory_descriptor`]. The in-browser PyanaRuntime can
///   resolve `window.pyana.createFromFactory(NAME_FACTORY_VK, ..)`
///   against the host's HTTP descriptor service backed by this
///   registry.
/// - `ctx.inspector_registry().get("name")` returns the
///   [`InspectorDescriptor`] pointing the Studio at
///   `/starbridge-apps/nameservice/inspectors.js` for any
///   `<pyana-name uri="..."/>` mount.
/// - `ctx.inspector_registry().get("name-registry")` returns the
///   parent-list inspector (the registry-cell view that links
///   into individual name cells).
///
/// Returns the registered `factory_vk` so the host can log or
/// surface it.
///
/// ## Typical host wiring
///
/// ```ignore
/// use pyana_app_framework::{
///     AgentWallet, AppServer, AppConfig, AppWallet, EmbeddedExecutor,
///     StarbridgeAppContext,
/// };
///
/// #[tokio::main]
/// async fn main() {
///     let federation_id = [42u8; 32];
///     let wallet = AppWallet::new(AgentWallet::new(), federation_id);
///     let executor = EmbeddedExecutor::new(&wallet, "default");
///     let ctx = StarbridgeAppContext::new(wallet.clone(), executor.clone());
///
///     // Each starbridge-app contributes its factories + inspectors.
///     starbridge_nameservice::register(&ctx);
///     // starbridge_identity::register(&ctx);
///     // ...
///
///     AppServer::new(AppConfig::from_env())
///         .service_name("starbridge-host")
///         .with_health()
///         .with_cors()
///         .with_wallet(wallet)
///         .with_embedded_executor(executor)
///         .with_starbridge(ctx)
///         .serve()
///         .await
///         .unwrap();
/// }
/// ```
///
/// Per-handler use: extract `axum::Extension<StarbridgeAppContext>`
/// and reach `ctx.wallet()`, `ctx.executor()`, or
/// `ctx.factory_registry()` uniformly across all starbridge-apps
/// mounted on the same host.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    // 1. Register the name factory descriptor. The returned vk is
    // `NAME_FACTORY_VK`; downstream code looks descriptors up by it.
    let factory_vk = ctx.register_factory(name_factory_descriptor());

    // 2. Register the per-name inspector. The descriptor points the
    // Studio runtime at this app's `inspectors.js` module under the
    // `<pyana-name uri="..."/>` webcomponent name. The shape matches
    // `site/_includes/studio/inspectors.js`'s registration grammar.
    ctx.register_inspector(InspectorDescriptor {
        kind: "name".into(),
        descriptor: serde_json::json!({
            "component": "pyana-name",
            "module": "/starbridge-apps/nameservice/inspectors.js",
            "uri_prefix": "pyana://cell/",
            "summary_fields": ["name_hash", "owner_hash", "expiry"],
            "factory_vk_hex": hex_encode(&factory_vk),
            "child_program_vk_hex": hex_encode(&NAME_CHILD_PROGRAM_VK),
        }),
    });

    // 3. Register the registry-list inspector (the parent view that
    // links to each name cell). Apps with no parent view can skip
    // this; for nameservice it is the "browse all registered names"
    // surface.
    ctx.register_inspector_with("name-registry", || {
        serde_json::json!({
            "component": "pyana-name-registry",
            "module": "/starbridge-apps/nameservice/inspectors.js",
            "uri_prefix": "pyana://cell/",
            "child_inspector": "name",
        })
    });

    factory_vk
}

/// Hex-encode a 32-byte array (small helper used by inspector
/// descriptor JSON). Kept private to this crate.
fn hex_encode(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

// =============================================================================
// Helpers
// =============================================================================

/// Hash arbitrary bytes into a [`FieldElement`] (32-byte) suitable
/// for effect data fields.
fn blake3_field(bytes: &[u8]) -> FieldElement {
    *blake3::hash(bytes).as_bytes()
}

/// Encode a `u64` as a big-endian-padded 32-byte [`FieldElement`].
///
/// Big-endian so the low bytes are at the end — matches the
/// `field_from_u64_be` convention used in `pyana_cell::program`
/// (which keeps SetField values comparable to integer-typed
/// constraint operands).
fn u64_field(value: u64) -> FieldElement {
    let mut out = [0u8; 32];
    out[24..32].copy_from_slice(&value.to_be_bytes());
    out
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_app_framework::{AgentWallet, Authorization, EmbeddedExecutor};

    fn test_wallet() -> AppWallet {
        AppWallet::new(AgentWallet::new(), [42u8; 32])
    }

    fn test_context() -> StarbridgeAppContext {
        let wallet = test_wallet();
        let executor = EmbeddedExecutor::new(&wallet, "default");
        StarbridgeAppContext::new(wallet, executor)
    }

    fn test_cell() -> CellId {
        CellId::from_bytes([1u8; 32])
    }

    #[test]
    fn factory_descriptor_is_stable() {
        // The descriptor hash is the constructor-transparency
        // identity. Two builds must produce the same hash.
        let h1 = name_factory_descriptor().hash();
        let h2 = name_factory_descriptor().hash();
        assert_eq!(h1, h2, "descriptor hash must be deterministic");
    }

    #[test]
    fn factory_descriptor_pins_program_vk() {
        let d = name_factory_descriptor();
        assert_eq!(d.child_program_vk, Some(NAME_CHILD_PROGRAM_VK));
        assert_eq!(d.factory_vk, NAME_FACTORY_VK);
        assert_eq!(d.default_mode, CellMode::Sovereign);
        assert_eq!(d.creation_budget, Some(DEFAULT_CREATION_BUDGET));
    }

    #[test]
    fn factory_descriptor_constrains_name_hash_slot() {
        let d = name_factory_descriptor();
        assert!(
            d.field_constraints
                .iter()
                .any(|c| matches!(c, FieldConstraint::NonZero { field_index } if *field_index == NAME_HASH_SLOT as u32)),
            "name factory must constrain NAME_HASH_SLOT to be non-zero"
        );
        assert!(
            d.field_constraints
                .iter()
                .any(|c| matches!(c, FieldConstraint::NonZero { field_index } if *field_index == EXPIRY_SLOT as u32)),
            "name factory must constrain EXPIRY_SLOT to be non-zero"
        );
    }

    #[test]
    fn factory_descriptor_bakes_slot_caveats() {
        // Lane G slot caveats are baked into the descriptor's
        // `state_constraints` — every produced cell inherits them.
        let d = name_factory_descriptor();
        assert!(
            d.state_constraints.iter().any(|c| matches!(
                c,
                StateConstraint::WriteOnce { index } if *index == NAME_HASH_SLOT as u8
            )),
            "name factory must install WriteOnce on NAME_HASH_SLOT"
        );
        assert!(
            d.state_constraints.iter().any(|c| matches!(
                c,
                StateConstraint::Monotonic { index } if *index == EXPIRY_SLOT as u8
            )),
            "name factory must install Monotonic on EXPIRY_SLOT"
        );
    }

    // ── Slot-caveat enforcement (positive + negative). ───────────────────
    //
    // These exercise the `StateConstraint` evaluator directly against the
    // descriptor's slot caveats. They are the executor-side regression for
    // the Lane G migration: a legal registration succeeds; a second
    // registration on the same cell is rejected with `WriteOnceViolation`
    // and an expiry decrement is rejected with `MonotonicViolation`.

    fn build_name_program() -> pyana_cell::CellProgram {
        pyana_cell::CellProgram::Predicate(name_factory_descriptor().state_constraints.clone())
    }

    fn empty_state() -> pyana_cell::state::CellState {
        pyana_cell::state::CellState::new(0)
    }

    fn state_with(name_hash: FieldElement, expiry: u64) -> pyana_cell::state::CellState {
        let mut s = empty_state();
        s.fields[NAME_HASH_SLOT] = name_hash;
        s.fields[EXPIRY_SLOT] = u64_field(expiry);
        s
    }

    #[test]
    fn slot_caveats_legal_registration_succeeds() {
        // Initial registration: old slot is FIELD_ZERO (fresh cell), new
        // slot is `blake3("alice.pyana")`. WriteOnce permits this because
        // the prior value is zero; Monotonic permits any expiry on init.
        let program = build_name_program();
        let old = empty_state();
        let new = state_with(blake3_field(b"alice.pyana"), 1_000);
        let result = program.evaluate(&new, Some(&old), None);
        assert!(
            result.is_ok(),
            "legal registration must succeed: {result:?}"
        );
    }

    #[test]
    fn slot_caveats_reregister_taken_name_is_write_once_violation() {
        let program = build_name_program();
        let alice_hash = blake3_field(b"alice.pyana");
        let bob_hash = blake3_field(b"bob.pyana");
        let mut old = state_with(alice_hash, 1_000);
        old.set_nonce(1); // not a fresh cell
        // Attempt: overwrite NAME_HASH_SLOT with a different value.
        let new = state_with(bob_hash, 1_000);
        let err = program
            .evaluate(&new, Some(&old), None)
            .expect_err("re-registration must be rejected");
        match err {
            pyana_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::WriteOnce { index },
                ..
            } => assert_eq!(index, NAME_HASH_SLOT as u8),
            other => panic!("expected WriteOnce violation, got: {other:?}"),
        }
    }

    #[test]
    fn slot_caveats_expiry_decrease_is_monotonic_violation() {
        let program = build_name_program();
        let alice_hash = blake3_field(b"alice.pyana");
        let mut old = state_with(alice_hash, 5_000);
        old.set_nonce(1);
        // Attempt: shorten expiry from 5000 → 4000.
        let new = state_with(alice_hash, 4_000);
        let err = program
            .evaluate(&new, Some(&old), None)
            .expect_err("expiry decrement must be rejected");
        match err {
            pyana_cell::ProgramError::ConstraintViolated {
                constraint: StateConstraint::Monotonic { index },
                ..
            } => assert_eq!(index, EXPIRY_SLOT as u8),
            other => panic!("expected Monotonic violation, got: {other:?}"),
        }
    }

    #[test]
    fn slot_caveats_legal_renewal_succeeds() {
        // Renewal extends expiry — Monotonic permits new >= old.
        let program = build_name_program();
        let alice_hash = blake3_field(b"alice.pyana");
        let mut old = state_with(alice_hash, 5_000);
        old.set_nonce(1);
        let new = state_with(alice_hash, 10_000);
        let result = program.evaluate(&new, Some(&old), None);
        assert!(result.is_ok(), "legal renewal must succeed: {result:?}");
    }

    #[test]
    fn factory_descriptors_includes_name_factory() {
        let all = factory_descriptors();
        assert_eq!(all.len(), 1, "expected exactly one descriptor today");
        assert_eq!(all[0].factory_vk, NAME_FACTORY_VK);
    }

    #[test]
    fn register_action_writes_three_slots_and_emits_event() {
        let wallet = test_wallet();
        let action = build_register_action(&wallet, test_cell(), "alice.pyana", [3u8; 32], 1_000);

        assert_eq!(action.effects.len(), 4);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, .. } if *index == NAME_HASH_SLOT
        ));
        assert!(matches!(
            &action.effects[1],
            Effect::SetField { index, .. } if *index == OWNER_HASH_SLOT
        ));
        assert!(matches!(
            &action.effects[2],
            Effect::SetField { index, .. } if *index == EXPIRY_SLOT
        ));
        assert!(matches!(&action.effects[3], Effect::EmitEvent { .. }));
    }

    #[test]
    fn register_action_carries_real_signature() {
        // The whole point of the userspace stance: actions carry a real
        // framework-issued signature, not a `[0u8; 64]` placeholder.
        let wallet = test_wallet();
        let action = build_register_action(&wallet, test_cell(), "alice.pyana", [3u8; 32], 1_000);
        match action.authorization {
            Authorization::Signature(a, b) => {
                assert!(
                    a != [0u8; 32] || b != [0u8; 32],
                    "signature must be non-zero (no [0u8; 64] placeholders!)"
                );
            }
            other => panic!("expected Signature variant, got {other:?}"),
        }
    }

    #[test]
    fn different_names_produce_different_name_hashes() {
        let wallet = test_wallet();
        let pick = |action: &Action| match &action.effects[0] {
            Effect::SetField { value, .. } => *value,
            _ => panic!("first effect is not SetField"),
        };
        let a = build_register_action(&wallet, test_cell(), "alice.pyana", [3u8; 32], 1_000);
        let b = build_register_action(&wallet, test_cell(), "bob.pyana", [3u8; 32], 1_000);
        assert_ne!(pick(&a), pick(&b));
    }

    #[test]
    fn renew_action_updates_expiry_slot_and_emits_event() {
        let wallet = test_wallet();
        let action = build_renew_action(&wallet, test_cell(), "alice.pyana", 2_000);
        assert_eq!(action.effects.len(), 2);
        match &action.effects[0] {
            Effect::SetField { index, value, .. } => {
                assert_eq!(*index, EXPIRY_SLOT);
                assert_eq!(*value, u64_field(2_000));
            }
            other => panic!("expected SetField, got {other:?}"),
        }
        assert!(matches!(&action.effects[1], Effect::EmitEvent { .. }));
    }

    #[test]
    fn transfer_action_updates_owner_slot_and_emits_event() {
        let wallet = test_wallet();
        let old = [3u8; 32];
        let new = [4u8; 32];
        let action = build_transfer_action(&wallet, test_cell(), "alice.pyana", old, new);
        assert_eq!(action.effects.len(), 2);
        match &action.effects[0] {
            Effect::SetField { index, value, .. } => {
                assert_eq!(*index, OWNER_HASH_SLOT);
                assert_eq!(*value, blake3_field(&new));
            }
            other => panic!("expected SetField, got {other:?}"),
        }
        assert!(matches!(&action.effects[1], Effect::EmitEvent { .. }));
    }

    // ── StarbridgeAppContext mount integration. ──────────────────────────

    #[test]
    fn register_installs_name_factory_descriptor() {
        let ctx = test_context();
        assert_eq!(ctx.factory_registry().len(), 0);
        let vk = register(&ctx);
        assert_eq!(vk, NAME_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
        let got = ctx
            .factory_registry()
            .get(&NAME_FACTORY_VK)
            .expect("factory descriptor registered");
        assert_eq!(got.factory_vk, NAME_FACTORY_VK);
        assert_eq!(got.child_program_vk, Some(NAME_CHILD_PROGRAM_VK));
        assert_eq!(got.default_mode, CellMode::Sovereign);
    }

    #[test]
    fn register_installs_inspector_descriptors() {
        let ctx = test_context();
        register(&ctx);
        let name_insp = ctx
            .inspector_registry()
            .get("name")
            .expect("name inspector registered");
        assert_eq!(name_insp.descriptor["component"], "pyana-name");
        assert_eq!(
            name_insp.descriptor["module"],
            "/starbridge-apps/nameservice/inspectors.js"
        );
        let registry_insp = ctx
            .inspector_registry()
            .get("name-registry")
            .expect("name-registry inspector registered");
        assert_eq!(registry_insp.descriptor["component"], "pyana-name-registry");
        assert_eq!(registry_insp.descriptor["child_inspector"], "name");
    }

    #[test]
    fn register_is_idempotent_on_factory() {
        // Calling register twice with the same ctx should not panic
        // and should not duplicate the factory entry (constructor
        // transparency: one descriptor per factory_vk).
        let ctx = test_context();
        register(&ctx);
        register(&ctx);
        assert_eq!(ctx.factory_registry().len(), 1);
    }

    #[test]
    fn register_inspector_descriptor_contains_factory_vk_hex() {
        // Inspectors need the factory VK to mount the
        // constructor-transparency view. Confirm the JSON carries it
        // as a hex string.
        let ctx = test_context();
        register(&ctx);
        let name_insp = ctx.inspector_registry().get("name").unwrap();
        let hex = name_insp.descriptor["factory_vk_hex"]
            .as_str()
            .expect("factory_vk_hex must be a string");
        assert_eq!(hex.len(), 64);
        assert_eq!(hex, hex_encode(&NAME_FACTORY_VK));
    }

    #[test]
    fn wallet_identity_binds_into_signature() {
        // Two different wallets sign the same logical action with
        // different signatures — confirms the wallet's identity is
        // actually bound in.
        let w1 = AppWallet::new(AgentWallet::new(), [42u8; 32]);
        let w2 = AppWallet::new(AgentWallet::new(), [42u8; 32]);
        let cell = test_cell();
        let a1 = build_register_action(&w1, cell, "alice", [3u8; 32], 1_000);
        let a2 = build_register_action(&w2, cell, "alice", [3u8; 32], 1_000);
        let (Authorization::Signature(r1, _), Authorization::Signature(r2, _)) =
            (&a1.authorization, &a2.authorization)
        else {
            panic!("expected Signature variants");
        };
        assert_ne!(
            r1, r2,
            "different wallets must produce different signatures"
        );
    }
}
