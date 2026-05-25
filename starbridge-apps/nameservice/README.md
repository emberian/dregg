# starbridge-nameservice — the anchor starbridge-app

`starbridge-nameservice` is the **first proper starbridge-app** and the
exemplar future apps build from. It implements a federation name
directory entirely from pyana-native primitives — `FactoryDescriptor`,
`StateConstraint`, `Effect::SetField` / `Effect::EmitEvent`,
`Authorization::Signature` produced by `AppCipherclerk::make_action`. No
`Effect::RegisterName`, no `Authorization::Unchecked`, no `[0u8; 64]`
placeholder signatures, no reaching past the framework into
`pyana_turn::builder::*`.

It is the **paint-by-numbers exemplar** every other starbridge-app
follows. The pattern is:

1. **Declare a slot layout** — name a fixed set of `usize` constants
   pinning which field-slot in the cell's `[FieldElement; 8]` carries
   which piece of domain state.
2. **Build a `FactoryDescriptor`** that pins:
   - the program VK (the AIR the cell-program enforces in-circuit);
   - **state constraints** — Lane-G slot caveats (`WriteOnce`,
     `Monotonic`, …) the executor evaluates on every turn against
     this cell;
   - **field constraints** — creation-time checks that initial state
     is well-formed (e.g. `NonZero(NAME_HASH_SLOT)`);
   - capability templates the factory is permitted to mint;
   - a per-epoch creation budget to rate-limit Sybil spam.
3. **Write turn-builders** that take an `AppCipherclerk` and produce a
   real signed `Action` via `AppCipherclerk::make_action`. The cipherclerk's
   `federation_id` binds into the signature; the executor sees real
   Ed25519, never a placeholder.
4. **Define web components** (`pages/inspectors.js`) that render the
   per-cell state machine, plus a JS shim
   (`pages/turn-builders.js`) that mirrors the Rust builders and
   dispatches through `window.pyana.signTurn`.
5. **Mount via `register(ctx)`** on a shared
   `StarbridgeAppContext`: register the factory + inspector
   descriptors so the host's `createFromFactory` and Studio
   inspector chain resolve them.

The Rust crate is the **single source of truth**. The JS surface mirrors
the slot layout and event-topic names from `src/lib.rs`; the executor
sees only signed Rust-shaped `Action`s.

---

## State machine

Each registered name lives in a sovereign cell whose state is laid out
across five slots:

| Slot | Constant | Purpose | Constraint |
|:---:|---|---|---|
| `2` | `NAME_HASH_SLOT`        | `blake3(name_bytes)` | `WriteOnce` |
| `3` | `OWNER_HASH_SLOT`       | `blake3(owner_pubkey_bytes)` | (auth — see below) |
| `4` | `EXPIRY_SLOT`           | block-height of rent expiry (BE-padded u64) | `Monotonic` |
| `5` | `REVOKED_SLOT`          | `0` while active; tombstone after revocation | `WriteOnce` |
| `6` | `RESOLVE_TARGET_SLOT`   | content-address (`blake3(uri_bytes)`) of the resolve target | _unconstrained_ |

`WriteOnce` on `NAME_HASH_SLOT` closes the duplicate-registration gap
(`APPS-USERSPACE-GAPS.md` §Gap 1) — the slot transitions from `FIELD_ZERO`
to `blake3(name)` exactly once and freezes.

`Monotonic` on `EXPIRY_SLOT` makes rent extensions strictly forward —
an attacker cannot shorten a rental they've already sold by writing a
smaller expiry value.

`WriteOnce` on `REVOKED_SLOT` makes revocation one-way. The tombstone
is `blake3(b"pyana-nameservice-revoked:" || name_bytes)` so a replay
attacker cannot move tombstones between cells to spoof revocations.

`RESOLVE_TARGET_SLOT` carries no slot caveat: the owner may freely
re-point the name. The binding `name → cell` is permanent
(`WriteOnce(NAME_HASH_SLOT)`); the binding `cell → target` is mutable.

### Owner authorization

The lifecycle helpers — `renew`, `transfer`, `revoke`, `set_target` —
all carry a real `Authorization::Signature` from the cclerk, bound to
the cipherclerk's `federation_id` and the action's canonical hash. Two
different cipherclerks produce two different signatures for the same logical
action (see the `auth_different_cclerks_produce_different_signatures_on_same_logical_action`
test in `tests/lifecycle.rs`).

The factory descriptor does **not** currently install a
`StateConstraint::SenderAuthorized { set: AuthorizedSet::PublicRoot { set_root_index: OWNER_HASH_SLOT } }`
on the cell. **TODO (follow-up):** add this so the executor will reject
a transfer/renew action whose signer is not the holder of the owner cap.
The slot layout already supports it — `OWNER_HASH_SLOT` would just be
reinterpreted as a single-element Merkle root over the owner's pubkey
— but the witness-side plumbing (`SenderAuthorized` requires a
`Merkle-membership` witness in the action's `auth_witness` blob) is not
yet wired through `AppCipherclerk::make_action`. The current authorization
story is: actions carry a real signature, so the executor *can* tell
who signed, but the cell program does not yet refuse transfers from
non-owners. Tracked in this README and in the comment on
`build_transfer_action` in `src/lib.rs`.

---

## What this crate exports

### `name_factory_descriptor() -> FactoryDescriptor`

The `FactoryDescriptor` for the per-name sovereign-cell factory. Pins
the constructor-transparency contract anyone can audit by hashing the
descriptor:

- `child_program_vk = name_child_program_vk()` (canonical hash of
  `name_cell_program()` per `VK-AS-RE-EXECUTION-RECIPE.md`)
- `default_mode = CellMode::Sovereign`
- `creation_budget = 10_000` per epoch (Sybil rate-limit)
- `allowed_cap_templates = [owner_cap]` — single attenuatable
  signature-authorized capability the factory may grant to the
  creator; renewal/transfer/sub-delegation derive from this via
  `Caveat::ResourcePrefix` attenuation
- `field_constraints` (creation-time):
  `NonZero(NAME_HASH_SLOT)`, `NonZero(EXPIRY_SLOT)`
- `state_constraints` (perpetual):
  `WriteOnce(NAME_HASH_SLOT)`, `Monotonic(EXPIRY_SLOT)`,
  `WriteOnce(REVOKED_SLOT)`

`factory_descriptors() -> Vec<FactoryDescriptor>` returns the full
slice this app contributes (today: one entry).

### Turn-builders (every action carries a real Ed25519 signature)

```rust
build_register_action(cclerk,   registry_cell, name, owner, expiry_height)
build_renew_action(cclerk,      registry_cell, name, new_expiry_height)
build_transfer_action(cclerk,   registry_cell, name, old_owner, new_owner)
build_revoke_action(cclerk,     registry_cell, name)
build_set_target_action(cclerk, registry_cell, name, target_field)
```

Each builds an `Action` via `AppCipherclerk::make_action(target, method,
effects)` — the cclerk signs with its Ed25519 key bound to its
`federation_id`. No `Authorization::Unchecked`, no `[0u8; 64]`.

Convenience helpers exposed for off-chain indexers / cross-app code:

```rust
name_hash(name)             -> FieldElement   // blake3(name_bytes)
expiry_field(height)        -> FieldElement   // BE-padded u64
revoked_tombstone(name)     -> FieldElement   // blake3("pyana-nameservice-revoked:" || name)
resolve_target(uri)         -> FieldElement   // blake3(uri_bytes)
```

### `register(ctx: &StarbridgeAppContext) -> [u8; 32]`

Mounts the app on a shared context. Registers the factory descriptor
and three Studio inspector descriptors:

| Inspector kind | JS component | Purpose |
|---|---|---|
| `name`               | `<pyana-name>`               | per-cell state view |
| `name-registry`      | `<pyana-name-registry>`      | parent-list browse / search / paginate |
| `name-register-form` | `<pyana-name-register-form>` | mutation surface (register / renew / transfer / revoke / set-target) |

The `name` inspector descriptor carries the `slot_layout` JSON so the
Studio can index into a name cell's state without hardcoding slot
indices.

---

## The web surface

`pages/inspectors.js` defines the three custom elements above. Each is
a vanilla shadow-DOM element (no Preact/htm/signals dependency yet — the
Studio's `<pyana-app>` context wires them via the standard
`customElements` registry that all Studio inspectors share). Each
component dispatches a `CustomEvent` so host pages can wire their own
analytics, persistence, or navigation without forking these.

`pages/turn-builders.js` is the thin JS shim that mirrors the Rust
builders. It exposes:

```js
window.pyana.builders.nameservice = {
  register_name(registryUri, { name, owner, expiry }),
  renew_name(registryUri,    { name, expiry }),
  transfer_name(registryUri, { name, old_owner, new_owner }),
  revoke_name(registryUri,   { name }),
  set_target_name(registryUri, { name, target }),
};
```

Every builder calls `window.pyana.signTurn(turnSpec)` — the extension
cclerk API (`extension/src/page.ts`). The page never holds raw private
keys.

`pages/index.html` is the site fragment, mounted under
`/starbridge-apps/nameservice/`. It loads the in-browser wasm node
(`/pkg/pyana_wasm.js`), the shared Studio chrome
(`/_includes/studio/runtimes.js`), the shared inspector registry
(`/starbridge-apps/shared/inspectors/index.js` — which itself
lazy-imports this app's inspectors), and finally this app's inspectors
+ turn-builders directly so the fragment is self-contained.

The hardcoded `factory-vk` hex on the page is the literal byte pattern
of `NAME_FACTORY_VK` in `src/lib.rs`:

```
*b"starbridge-nameservice-factory!!"
= 0x737461726272696467652d6e616d65736572766963652d666163746f72792121
```

A real deployment swaps `NAME_FACTORY_VK` for the hash of the
production cell-program VK; the HTML's factory-vk hex must be
regenerated to match.

---

## Composition with `pyana-directory`

The toplevel `directory/` crate provides the **canonical name-directory
primitive**: a `Directory` trait with `register / lookup / revoke /
discover`, an `InMemoryDirectory` reference implementation, and
versioned `DirectoryEntry`s carrying `ResourceHandle`, `EntryKind`,
tags, expiry, and revocation flags.

`starbridge-nameservice` is **a specialized directory** — every name
cell is a `DirectoryEntry` whose:

| `DirectoryEntry` field | nameservice mapping |
|---|---|
| `handle: ResourceHandle`   | `pyana://cell/<NAME_CELL_ID>` (resolves via `RESOLVE_TARGET_SLOT`) |
| `version: Version`         | the cell's nonce |
| `kind: EntryKind`          | `EntryKind::Capability` for owner-cap names; `EntryKind::SubDirectory` if the cell points at another directory |
| `tags: Vec<String>`        | not currently surfaced; a future `TAGS_SLOT` could carry a content-addressed tag commitment |
| `registered_at: u64`       | block height of the registration turn |
| `expires_at: Option<u64>`  | `EXPIRY_SLOT` decoded as a BE-padded u64 |
| `revoked: bool`            | `REVOKED_SLOT != FIELD_ZERO` |

**Composition stance — consume, don't reimplement.** The directory
primitive is the in-process reference for `register / lookup / revoke /
discover`. Nameservice is the *ledger-backed* realisation: every
mutation goes through a signed turn, every entry is a real
`FactoryDescriptor`-pinned cell, every state transition is enforced by
slot caveats the executor evaluates each turn. An off-chain indexer
that consumes nameservice events (`name-registered`,
`name-renewed`, `name-transferred`, `name-revoked`, `name-target-set`)
can project the federation's nameservice state into an
`InMemoryDirectory` for fast lookups, then serve `Directory::discover`
queries against that projection.

A future integration sketch:

```rust
// indexer side
use pyana_directory::{InMemoryDirectory, DirectoryEntry, EntryKind};
use starbridge_nameservice::{NAME_HASH_SLOT, EXPIRY_SLOT, REVOKED_SLOT};

fn project_event_into_directory(event: &Event, dir: &mut InMemoryDirectory) {
    match event.topic.as_str() {
        "name-registered" => dir.register(name, DirectoryEntry { .. })?,
        "name-renewed"    => /* extend expires_at */ ,
        "name-transferred"=> /* update handle's owner pubkey */ ,
        "name-revoked"    => dir.revoke(name)?,
        _ => {}
    }
}
```

This pattern — **ledger as authority, directory as projection** — is
the storage-as-cell-programs stance from
`STORAGE-AS-CELL-PROGRAMS.md`: the directory primitive's
data-structure mechanics (BTreeMap + version counter + CAS) supply
the *lookup convenience*; the cell program + slot caveats supply the
*enforcement*. They compose; they don't compete.

---

## Wiring (typical `main.rs`)

```rust
use pyana_app_framework::{
    AgentCipherclerk, AppServer, AppConfig, AppCipherclerk, EmbeddedExecutor,
    StarbridgeAppContext,
};

#[tokio::main]
async fn main() {
    let federation_id = [42u8; 32];
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), federation_id);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    let ctx = StarbridgeAppContext::new(cclerk.clone(), executor.clone());

    // Each starbridge-app contributes its factories + inspectors.
    starbridge_nameservice::register(&ctx);
    // starbridge_identity::register(&ctx);
    // starbridge_subscription::register(&ctx);

    AppServer::new(AppConfig::from_env())
        .service_name("starbridge-host")
        .with_health()
        .with_cors()
        .with_cclerk(cclerk)
        .with_embedded_executor(executor)
        .with_starbridge(ctx)
        .serve()
        .await
        .unwrap();
}
```

After this call:

- `ctx.factory_registry().get(&NAME_FACTORY_VK)` returns the factory
  descriptor. The in-browser `PyanaRuntime` resolves
  `window.pyana.createFromFactory(NAME_FACTORY_VK, owner_pk, 0)`
  against the host's descriptor service backed by this registry.
- `ctx.inspector_registry().get("name")` returns the inspector
  descriptor pointing the Studio at
  `/starbridge-apps/nameservice/inspectors.js`.

---

## Tests

| Test (`tests/lifecycle.rs`) | What it pins |
|---|---|
| `lifecycle_register_set_target_renew_transfer_revoke_round_trips` | every step's post-state passes `StateConstraint` evaluation against the prior state |
| `adversarial_duplicate_name_registration_rejected_by_write_once` | `WriteOnce(NAME_HASH_SLOT)` rejects second-name-on-same-cell |
| `adversarial_expiry_decrement_rejected_by_monotonic`              | `Monotonic(EXPIRY_SLOT)` rejects backwards expiry |
| `adversarial_expiry_held_equal_is_permitted_by_monotonic`         | `new == old` is permitted (no-op turn) |
| `adversarial_double_revoke_rejected_by_write_once_on_revoked_slot`| second tombstone write is rejected |
| `auth_register_action_carries_real_signature`                     | no `[0u8; 64]` placeholders |
| `auth_all_lifecycle_actions_carry_real_signatures`                | every entry point emits `Authorization::Signature` |
| `auth_different_cclerks_produce_different_signatures_on_same_logical_action` | the cipherclerk's identity is bound into the signature |
| `factory_descriptors_publishes_exactly_one_factory_today`         | the slice has exactly the expected one entry (forces deliberate updates) |
| `factory_descriptor_hash_is_deterministic_across_builds`          | constructor transparency: two builds yield the same hash |
| `factory_descriptor_hash_changes_with_state_constraints`          | dropping a slot caveat must change the descriptor hash |
| `register_function_is_idempotent_across_repeated_calls`           | calling `register(ctx)` twice does not duplicate factory entries |

Unit tests in `src/lib.rs::tests` cover slot-caveat enforcement
end-to-end (`slot_caveats_*`), factory-descriptor shape, action
construction, and the `StarbridgeAppContext` mount integration.

---

## Standalone check

The workspace-stabilization lane verifies compile + test passage. This
crate's contract:

```sh
cargo check -p starbridge-nameservice
cargo test  -p starbridge-nameservice
```

---

## See also

- `../../STARBRIDGE-APPS-PLAN.md` §3.1 — the per-app design sketch this
  crate implements.
- `../../STORAGE-AS-CELL-PROGRAMS.md` — the pattern this app embodies
  (storage primitives as cell-program patterns, not new effects).
- `../../SLOT-CAVEATS-DESIGN.md` / `SLOT-CAVEATS-EVALUATION.md` —
  Lane G: the slot caveat vocabulary the factory descriptor draws from.
- `../../APPS-USERSPACE-GAPS.md` — the gap catalogue this crate closes
  (Gap 1: name-hash uniqueness; Gap 4: dropped-on-floor actions).
- `../../APPS-AS-USERSPACE-AUDIT.md` §1.3 — the audit reading that
  motivated rebuilding nameservice as pyana-native.
- `../../directory/src/directory.rs` — the canonical name-directory
  primitive this app specializes.
- `../identity/` — sibling starbridge-app; the issuer factory follows
  the same pattern.
