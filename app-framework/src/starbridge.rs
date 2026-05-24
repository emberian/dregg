//! `StarbridgeAppContext` — the canonical mount point for starbridge-apps.
//!
//! A `StarbridgeAppContext` is what every starbridge-app receives when
//! its `register(ctx)` hook fires. It carries the four things a
//! starbridge-app needs:
//!
//! 1. An [`AppWallet`] — narrow signing handle (six methods, no key
//!    export). Apps build signed [`pyana_turn::action::Action`]s through
//!    it.
//! 2. An [`EmbeddedExecutor`] — turn-submission handle. Apps submit
//!    signed [`pyana_turn::Turn`]s through it and receive real
//!    [`pyana_turn::TurnReceipt`]s. Closes the "action authored and
//!    dropped on the floor" pattern from `APPS-USERSPACE-GAPS.md`
//!    §Gap 4.
//! 3. A [`FactoryRegistry`] — the in-process registry that the
//!    in-browser PyanaRuntime / extension wallet's
//!    `createFromFactory(factory_vk, ...)` resolves against.
//!    Starbridge-apps call [`StarbridgeAppContext::register_factory`]
//!    at startup; the host (this context) holds the descriptors so
//!    constructor-transparency lookups by `factory_vk` work uniformly.
//! 4. An [`InspectorRegistry`] — the surface the future Studio
//!    webcomponents register against. Each entry is a
//!    [`InspectorDescriptor`] (kind tag + JSON-shaped descriptor) the
//!    site's `_includes/studio/inspectors.js` can mount under
//!    `<pyana-${kind} uri="..."/>`.
//!
//! The optional [`StarbridgeAppContext::known_federations`] handle
//! threads through `KnownFederations` (the Mega-Federation registry
//! from `pyana_federation`) for apps that need to verify cross-fed
//! receipts or look up peer-federation public keys. It is held as an
//! `Arc` so multiple apps share the same registry view.
//!
//! ## Why a context object (and not free args)?
//!
//! Three reasons:
//!
//! - **Composition.** A single binary can mount many starbridge-apps
//!   side-by-side; each one's `register(ctx)` extends the shared
//!   registries.
//! - **Lifetimes.** The wallet, executor, and registries all live for
//!   the process lifetime; bundling them once at startup avoids
//!   threading four args into every helper.
//! - **Future-proofing.** As starbridge-apps need new shared services
//!   (federation client, content-blob store, scheduler), they get added
//!   here. Apps that don't need them ignore the field.
//!
//! ## Wiring (typical `main.rs`)
//!
//! ```ignore
//! let wallet = AppWallet::new(AgentWallet::new(), federation_id);
//! let executor = EmbeddedExecutor::new(&wallet, "default");
//! let mut ctx = StarbridgeAppContext::new(wallet.clone(), executor.clone());
//!
//! // Each starbridge-app registers its factories + inspectors.
//! starbridge_nameservice::register(&mut ctx);
//! // starbridge_identity::register(&mut ctx);
//! // ...
//!
//! AppServer::new(config)
//!     .with_wallet(wallet)
//!     .with_embedded_executor(executor)
//!     .with_starbridge(ctx)
//!     .serve()
//!     .await
//! ```

use std::collections::BTreeMap;
use std::sync::{Arc, RwLock};

use pyana_cell::FactoryDescriptor;

use crate::wallet::{AppWallet, EmbeddedExecutor};

// =============================================================================
// FactoryRegistry
// =============================================================================

/// In-process registry mapping `factory_vk` -> [`FactoryDescriptor`].
///
/// Used by the host to resolve `window.pyana.createFromFactory(factory_vk, ..)`
/// lookups: each starbridge-app pushes its descriptors at startup,
/// then the in-browser PyanaRuntime / extension wallet can fetch them
/// by hash to verify a cell's constructor-transparency contract.
///
/// Cheap to clone (internally `Arc<RwLock<BTreeMap<..>>>`).
#[derive(Clone, Default)]
pub struct FactoryRegistry {
    inner: Arc<RwLock<BTreeMap<[u8; 32], FactoryDescriptor>>>,
}

impl FactoryRegistry {
    /// Empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a descriptor. Returns the descriptor's `factory_vk`
    /// (which is the hash that downstream code uses as the lookup key).
    ///
    /// If a descriptor with the same `factory_vk` is already present,
    /// it is **not** replaced (factories are constructor-transparency
    /// contracts; once registered, the entry is immutable). Use
    /// [`Self::reregister`] if you genuinely need to overwrite (e.g.,
    /// hot-reload during development).
    pub fn register(&self, desc: FactoryDescriptor) -> [u8; 32] {
        let vk = desc.factory_vk;
        let mut map = self.write();
        map.entry(vk).or_insert(desc);
        vk
    }

    /// Force-replace any existing descriptor at `factory_vk`. Intended
    /// for dev-mode hot-reload only; production hosts should call
    /// [`Self::register`].
    pub fn reregister(&self, desc: FactoryDescriptor) -> [u8; 32] {
        let vk = desc.factory_vk;
        self.write().insert(vk, desc);
        vk
    }

    /// Look up a descriptor by `factory_vk`.
    pub fn get(&self, factory_vk: &[u8; 32]) -> Option<FactoryDescriptor> {
        self.read().get(factory_vk).cloned()
    }

    /// Number of registered descriptors.
    pub fn len(&self) -> usize {
        self.read().len()
    }

    /// True if the registry is empty.
    pub fn is_empty(&self) -> bool {
        self.read().is_empty()
    }

    /// All registered descriptors (snapshot).
    pub fn descriptors(&self) -> Vec<FactoryDescriptor> {
        self.read().values().cloned().collect()
    }

    fn read(&self) -> std::sync::RwLockReadGuard<'_, BTreeMap<[u8; 32], FactoryDescriptor>> {
        self.inner.read().unwrap_or_else(|e| e.into_inner())
    }

    fn write(&self) -> std::sync::RwLockWriteGuard<'_, BTreeMap<[u8; 32], FactoryDescriptor>> {
        self.inner.write().unwrap_or_else(|e| e.into_inner())
    }
}

impl std::fmt::Debug for FactoryRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FactoryRegistry")
            .field("count", &self.len())
            .finish()
    }
}

// =============================================================================
// InspectorRegistry
// =============================================================================

/// A single entry in the [`InspectorRegistry`].
///
/// Each entry binds a **kind tag** (e.g., `"name"`, `"auction"`,
/// `"proposal"`) to a JSON-shaped descriptor that the site's
/// `_includes/studio/inspectors.js` mounts as a webcomponent under
/// `<pyana-{kind} uri="..."/>`.
///
/// The descriptor itself is intentionally `serde_json::Value` — the
/// app-framework does not constrain the shape; it is whatever the
/// Studio's `inspectors.js` expects. Today that is (per
/// `site/STUDIO.md` §6):
///
/// ```json
/// {
///   "component": "pyana-name",
///   "module": "/starbridge-apps/nameservice/inspectors.js",
///   "uri_prefix": "pyana://cell/",
///   "summary_fields": ["name", "owner", "expiry"]
/// }
/// ```
///
/// but evolution of that contract lives in the site, not here.
#[derive(Clone, Debug)]
pub struct InspectorDescriptor {
    /// The kind tag — the suffix in `<pyana-{kind} uri="..."/>`.
    pub kind: String,
    /// JSON-shaped descriptor; structure is owned by the Studio's
    /// `inspectors.js`.
    pub descriptor: serde_json::Value,
}

/// In-process registry mapping `kind` -> [`InspectorDescriptor`].
///
/// Apps register inspector descriptors at startup via
/// [`StarbridgeAppContext::register_inspector`]; the host serves them
/// to the browser (e.g., as a JSON list at
/// `GET /__starbridge/inspectors`) so the Studio runtime can preload
/// the registry before any URI is resolved.
///
/// Cheap to clone (internally `Arc<RwLock<BTreeMap<..>>>`).
#[derive(Clone, Default)]
pub struct InspectorRegistry {
    inner: Arc<RwLock<BTreeMap<String, InspectorDescriptor>>>,
}

impl InspectorRegistry {
    /// Empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register an inspector descriptor under `kind`.
    ///
    /// If a descriptor for `kind` is already present, it is replaced
    /// (later registrations win — this matches the JS-side semantics
    /// where the most-recently-loaded module's mount survives).
    pub fn register(&self, descriptor: InspectorDescriptor) {
        let kind = descriptor.kind.clone();
        self.write().insert(kind, descriptor);
    }

    /// Convenience: build a descriptor from a kind tag + a closure
    /// that produces the JSON. The closure is invoked once at
    /// registration time.
    pub fn register_with<F>(&self, kind: impl Into<String>, factory: F)
    where
        F: FnOnce() -> serde_json::Value,
    {
        let kind = kind.into();
        let descriptor = InspectorDescriptor {
            kind: kind.clone(),
            descriptor: factory(),
        };
        self.write().insert(kind, descriptor);
    }

    /// Look up an inspector descriptor by kind.
    pub fn get(&self, kind: &str) -> Option<InspectorDescriptor> {
        self.read().get(kind).cloned()
    }

    /// Number of registered inspectors.
    pub fn len(&self) -> usize {
        self.read().len()
    }

    /// True if no inspectors are registered.
    pub fn is_empty(&self) -> bool {
        self.read().is_empty()
    }

    /// All registered descriptors (snapshot).
    pub fn descriptors(&self) -> Vec<InspectorDescriptor> {
        self.read().values().cloned().collect()
    }

    /// Serialize the full registry as a JSON object keyed by kind.
    /// Useful for `GET /__starbridge/inspectors` responses.
    pub fn to_json(&self) -> serde_json::Value {
        let map = self.read();
        let obj: serde_json::Map<String, serde_json::Value> = map
            .iter()
            .map(|(k, v)| (k.clone(), v.descriptor.clone()))
            .collect();
        serde_json::Value::Object(obj)
    }

    fn read(&self) -> std::sync::RwLockReadGuard<'_, BTreeMap<String, InspectorDescriptor>> {
        self.inner.read().unwrap_or_else(|e| e.into_inner())
    }

    fn write(&self) -> std::sync::RwLockWriteGuard<'_, BTreeMap<String, InspectorDescriptor>> {
        self.inner.write().unwrap_or_else(|e| e.into_inner())
    }
}

impl std::fmt::Debug for InspectorRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("InspectorRegistry")
            .field("count", &self.len())
            .finish()
    }
}

// =============================================================================
// StarbridgeAppContext
// =============================================================================

/// Canonical mount point starbridge-apps consume at registration time.
///
/// See module-level docs for the design rationale. Cheap to clone —
/// every field is internally `Arc`-backed.
#[derive(Clone)]
pub struct StarbridgeAppContext {
    /// Narrow wallet handle (Lane C). Apps build signed actions through
    /// it.
    wallet: AppWallet,
    /// Embedded executor (Lane H). Apps submit signed turns through it
    /// and receive real receipts.
    executor: EmbeddedExecutor,
    /// Factory descriptors registered by starbridge-apps.
    factories: FactoryRegistry,
    /// Studio inspector descriptors registered by starbridge-apps.
    inspectors: InspectorRegistry,
    /// Optional `KnownFederations` reference (the Mega-Federation
    /// registry). Held as `Arc<dyn Any + Send + Sync>` to avoid
    /// coupling app-framework to a specific federation API while
    /// still allowing apps that *do* depend on `pyana_federation` to
    /// downcast and use it.
    ///
    /// In practice today this is always
    /// `Arc<pyana_federation::KnownFederations>` (when set), but the
    /// `Any` boxing keeps the framework's surface stable across
    /// federation-crate revisions.
    known_federations: Option<Arc<dyn std::any::Any + Send + Sync>>,
}

impl StarbridgeAppContext {
    /// Build a context from a wallet + executor pair.
    ///
    /// The factory/inspector registries start empty; apps populate them
    /// in their `register(ctx)` hook.
    pub fn new(wallet: AppWallet, executor: EmbeddedExecutor) -> Self {
        Self {
            wallet,
            executor,
            factories: FactoryRegistry::new(),
            inspectors: InspectorRegistry::new(),
            known_federations: None,
        }
    }

    /// Attach a `KnownFederations` reference (the Mega-Federation
    /// registry). Use this on the host that has the federation crate
    /// in its dep tree (typically `pyana-node`):
    ///
    /// ```ignore
    /// use pyana_federation::KnownFederations;
    /// let known = Arc::new(KnownFederations::new());
    /// ctx.with_known_federations(known);
    /// ```
    ///
    /// Apps that need to access the registry call
    /// [`Self::known_federations_as`] with the concrete type they
    /// expect.
    pub fn with_known_federations<T>(mut self, known: Arc<T>) -> Self
    where
        T: Send + Sync + 'static,
    {
        self.known_federations = Some(known as Arc<dyn std::any::Any + Send + Sync>);
        self
    }

    /// Wallet handle (signing surface).
    pub fn wallet(&self) -> &AppWallet {
        &self.wallet
    }

    /// Embedded executor handle (turn submission surface).
    pub fn executor(&self) -> &EmbeddedExecutor {
        &self.executor
    }

    /// The factory registry (shared by all mounted apps).
    pub fn factory_registry(&self) -> &FactoryRegistry {
        &self.factories
    }

    /// The inspector registry (shared by all mounted apps).
    pub fn inspector_registry(&self) -> &InspectorRegistry {
        &self.inspectors
    }

    /// Convenience: register a [`FactoryDescriptor`] on the context's
    /// factory registry. Returns the descriptor's `factory_vk`.
    pub fn register_factory(&self, desc: FactoryDescriptor) -> [u8; 32] {
        self.factories.register(desc)
    }

    /// Convenience: register an inspector descriptor on the context's
    /// inspector registry.
    ///
    /// Apps typically call this with a kind tag and a JSON descriptor
    /// shaped for the site's `_includes/studio/inspectors.js`:
    ///
    /// ```ignore
    /// ctx.register_inspector(InspectorDescriptor {
    ///     kind: "name".into(),
    ///     descriptor: serde_json::json!({
    ///         "component": "pyana-name",
    ///         "module": "/starbridge-apps/nameservice/inspectors.js",
    ///         "uri_prefix": "pyana://cell/",
    ///     }),
    /// });
    /// ```
    pub fn register_inspector(&self, descriptor: InspectorDescriptor) {
        self.inspectors.register(descriptor);
    }

    /// Build-then-register convenience: takes a kind tag and a closure
    /// that produces the JSON descriptor. Matches the
    /// `register_inspector(kind, factory)` shape the brief requested.
    pub fn register_inspector_with<F>(&self, kind: impl Into<String>, factory: F)
    where
        F: FnOnce() -> serde_json::Value,
    {
        self.inspectors.register_with(kind, factory);
    }

    /// Downcast the attached `KnownFederations` registry (if any) to
    /// the caller's expected concrete type.
    ///
    /// Returns `None` if no registry was attached, or if the attached
    /// value's type does not match `T`.
    pub fn known_federations_as<T: Send + Sync + 'static>(&self) -> Option<Arc<T>> {
        let any = self.known_federations.as_ref()?;
        Arc::clone(any).downcast::<T>().ok()
    }

    /// True if a `KnownFederations` reference is attached.
    pub fn has_known_federations(&self) -> bool {
        self.known_federations.is_some()
    }
}

impl std::fmt::Debug for StarbridgeAppContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StarbridgeAppContext")
            .field("wallet", &self.wallet)
            .field("executor", &self.executor)
            .field("factories", &self.factories)
            .field("inspectors", &self.inspectors)
            .field("has_known_federations", &self.has_known_federations())
            .finish()
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_sdk::AgentWallet;

    fn fixture() -> (AppWallet, EmbeddedExecutor) {
        let sdk = AgentWallet::new();
        let wallet = AppWallet::new(sdk, [99u8; 32]);
        let executor = EmbeddedExecutor::new(&wallet, "default");
        (wallet, executor)
    }

    fn fixture_descriptor(vk: [u8; 32]) -> FactoryDescriptor {
        use pyana_cell::{
            AuthRequired, CapTarget, CapTemplate, CellMode, ChildVkStrategy, FactoryDescriptor,
        };
        FactoryDescriptor {
            factory_vk: vk,
            child_program_vk: Some([1u8; 32]),
            child_vk_strategy: Some(ChildVkStrategy::Fixed(Some([1u8; 32]))),
            allowed_cap_templates: vec![CapTemplate {
                target: CapTarget::SelfCell,
                max_permissions: AuthRequired::Signature,
                attenuatable: true,
            }],
            field_constraints: vec![],
            state_constraints: vec![],
            default_mode: CellMode::Sovereign,
            creation_budget: None,
        }
    }

    #[test]
    fn context_holds_wallet_and_executor() {
        let (w, e) = fixture();
        let ctx = StarbridgeAppContext::new(w.clone(), e.clone());
        assert_eq!(ctx.wallet().cell_id(), w.cell_id());
        assert_eq!(ctx.executor().cell_id(), e.cell_id());
    }

    #[test]
    fn factory_registry_register_and_lookup() {
        let (w, e) = fixture();
        let ctx = StarbridgeAppContext::new(w, e);
        let vk = [7u8; 32];
        let desc = fixture_descriptor(vk);
        let returned = ctx.register_factory(desc.clone());
        assert_eq!(returned, vk);
        let looked_up = ctx.factory_registry().get(&vk).expect("registered");
        assert_eq!(looked_up.factory_vk, vk);
        assert_eq!(ctx.factory_registry().len(), 1);
    }

    #[test]
    fn factory_registry_register_is_idempotent() {
        let registry = FactoryRegistry::new();
        let vk = [3u8; 32];
        registry.register(fixture_descriptor(vk));
        // Second register with same vk must not overwrite (constructor
        // transparency: descriptor at a given vk is immutable).
        let mut d2 = fixture_descriptor(vk);
        d2.child_program_vk = Some([0xFFu8; 32]);
        registry.register(d2);
        let got = registry.get(&vk).unwrap();
        assert_eq!(
            got.child_program_vk,
            Some([1u8; 32]),
            "second register must not have replaced the first"
        );
    }

    #[test]
    fn factory_registry_reregister_overwrites() {
        let registry = FactoryRegistry::new();
        let vk = [3u8; 32];
        registry.register(fixture_descriptor(vk));
        let mut d2 = fixture_descriptor(vk);
        d2.child_program_vk = Some([0xFFu8; 32]);
        registry.reregister(d2);
        let got = registry.get(&vk).unwrap();
        assert_eq!(got.child_program_vk, Some([0xFFu8; 32]));
    }

    #[test]
    fn inspector_registry_register_and_lookup() {
        let (w, e) = fixture();
        let ctx = StarbridgeAppContext::new(w, e);
        ctx.register_inspector(InspectorDescriptor {
            kind: "name".into(),
            descriptor: serde_json::json!({"component": "pyana-name"}),
        });
        let got = ctx.inspector_registry().get("name").unwrap();
        assert_eq!(got.kind, "name");
        assert_eq!(got.descriptor["component"], "pyana-name");
    }

    #[test]
    fn inspector_register_with_closure() {
        let (w, e) = fixture();
        let ctx = StarbridgeAppContext::new(w, e);
        ctx.register_inspector_with(
            "auction",
            || serde_json::json!({"component": "pyana-auction", "phases": ["commit", "reveal"]}),
        );
        let got = ctx.inspector_registry().get("auction").unwrap();
        assert_eq!(got.descriptor["phases"][0], "commit");
    }

    #[test]
    fn inspector_register_replaces_existing() {
        let registry = InspectorRegistry::new();
        registry.register(InspectorDescriptor {
            kind: "x".into(),
            descriptor: serde_json::json!({"v": 1}),
        });
        registry.register(InspectorDescriptor {
            kind: "x".into(),
            descriptor: serde_json::json!({"v": 2}),
        });
        assert_eq!(registry.get("x").unwrap().descriptor["v"], 2);
    }

    #[test]
    fn inspector_to_json_shape() {
        let registry = InspectorRegistry::new();
        registry.register(InspectorDescriptor {
            kind: "name".into(),
            descriptor: serde_json::json!({"component": "pyana-name"}),
        });
        registry.register(InspectorDescriptor {
            kind: "auction".into(),
            descriptor: serde_json::json!({"component": "pyana-auction"}),
        });
        let j = registry.to_json();
        assert_eq!(j["name"]["component"], "pyana-name");
        assert_eq!(j["auction"]["component"], "pyana-auction");
    }

    #[test]
    fn known_federations_default_absent() {
        let (w, e) = fixture();
        let ctx = StarbridgeAppContext::new(w, e);
        assert!(!ctx.has_known_federations());
        assert!(ctx.known_federations_as::<u32>().is_none());
    }

    #[test]
    fn known_federations_downcast_round_trip() {
        // Use a concrete stand-in (a plain Vec<u8>) — federation/ is
        // off-limits to this lane per the constraints, and this test
        // exercises the Any-downcast path uniformly.
        let (w, e) = fixture();
        let payload: Arc<Vec<u8>> = Arc::new(vec![1, 2, 3]);
        let ctx = StarbridgeAppContext::new(w, e).with_known_federations(Arc::clone(&payload));
        assert!(ctx.has_known_federations());
        let recovered: Arc<Vec<u8>> = ctx
            .known_federations_as::<Vec<u8>>()
            .expect("downcast to Vec<u8> succeeds");
        assert_eq!(*recovered, vec![1, 2, 3]);
        // Wrong type returns None, not a panic.
        assert!(ctx.known_federations_as::<String>().is_none());
    }
}
