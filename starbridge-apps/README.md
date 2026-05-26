# starbridge-apps/

The successor to `apps/`. See `../STARBRIDGE-APPS-PLAN.md` for full
context.

A **starbridge-app** is a web surface that:

1. Loads `/pkg/dregg_wasm.js` (the in-browser node, see `../wasm/`) for
   local simulation / preview / time-travel.
2. Talks to `window.dregg` (the browser extension cclerk, see
   `../extension/`) for real identity, signing, capability brokerage,
   intent posting.
3. Optionally talks to a live federation node via the Studio's
   `RemoteRuntime` for production data.
4. Renders state via the Studio's URI-addressable inspector system
   (`<dregg-cell uri="dregg://cell/..." />`), the same components
   `site/src/starbridge.html` (the Playground / Explorer / Starbridge
   surfaces) uses.
5. Contributes **domain-specific inspectors and turn-builder presets**
   to the shared inspector registry under `shared/`.

A starbridge-app is *not* a separate stack. The wasm runtime is
generic — it knows about `Effect`, `Cell`, `Turn`, `Factory`,
`Authorization` — and a starbridge-app is mostly **data**: a set of
`FactoryDescriptor`s, a set of inspectors, a set of turn-builder
helpers.

## The userspace stance (the brief's hard rule)

> The answer is never `Effect::FooApp`.

When an app wants a domain Effect, the missing primitive is the
*generic* one (Caveat, StateConstraint, Authorization, Factory) it
would compose from. Every starbridge-app in this directory must be
buildable from dregg-native primitives only.

See `DREGG-FLAWS-FROM-APPS.md` and `APPS-AS-USERSPACE-AUDIT.md` for
the prior survey of which primitives are missing.

## Layout

```
starbridge-apps/
├── README.md              ← this file
├── shared/
│   ├── inspectors/        ← Preact components published as ES modules
│   ├── turn-builders/     ← JS preset turn-builder modules (per app)
│   └── factories/         ← FactoryDescriptors checked in as JSON (mirrors of Rust definitions)
├── nameservice/           ← first proper starbridge-app
│   ├── Cargo.toml
│   ├── src/lib.rs         ← FactoryDescriptor builders, turn helpers, thin server (if any)
│   ├── pages/index.html   ← site fragment, mounted at /starbridge-apps/nameservice/
│   └── README.md
└── ... (future starbridge-apps land here per STARBRIDGE-APPS-PLAN.md §6)
```

## How a starbridge-app crate plugs in

Each Rust crate exports two things:

- A `FACTORY_DESCRIPTORS` slice (or per-factory constructors) baking
  the program VK + state constraints + capability templates the app
  needs. The wasm runtime preloads these at startup so
  `window.dregg.createFromFactory(factory_vk, ...)` can resolve the
  string into a real descriptor.
- Turn-builder helpers that take an `AppCipherclerk` (from
  `dregg-app-framework`) and produce signed `Action`s. No
  `Authorization::Unchecked`. No `[0u8; 64]` placeholder signatures.
  No reaching past the framework into `dregg_turn::builder::*`.

`dregg-app-framework::StarbridgeAppContext` (see plan §5.3) is the
host-side mount point. A host (`dregg-node`, a back-end aggregator
binary, or the wasm runtime in browser-only mode) calls
`app::register(&ctx)` to plug a starbridge-app crate into a running
federation. The app registers its factory descriptors, inspector
metadata, and turn-builder surface through that context; descriptor
constructors remain exported so tests and offline tooling can hash the
same source of truth directly.

## Workspace shape (Option A — single root workspace)

Each starbridge-app's `Cargo.toml` is a member of the root workspace
in `../Cargo.toml`. This shares deps and compile artifacts with the
dregg core. Per the plan §5.2, we'll only switch to a multi-workspace
shape if there's a concrete reason to (e.g. trimmer wasm-only deps).

## Dual-existence transition

The existing `apps/nameservice/`, `apps/identity/`, etc. crates stay
for now — Lane C just migrated them to use `AppCipherclerk` and they still
ship. `starbridge-apps/nameservice/` is the *new* canonical
implementation; the `apps/` ones will be retired once the
starbridge-apps version reaches parity. The dual-existence is
documented in the plan §2.
