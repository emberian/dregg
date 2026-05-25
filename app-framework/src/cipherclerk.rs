//! App-framework wallet handle.
//!
//! Apps are *userspace*: they should not reach past the SDK into
//! `pyana_turn::builder::ActionBuilder` or hand-encode `[0u8; 64]`
//! placeholder signatures. Instead, the framework hands them a narrow,
//! wallet-bound action-construction surface backed by the SDK's
//! [`pyana_sdk::AgentCipherclerk`].
//!
//! ## What this gives apps
//!
//! - [`AppCipherclerk::cell_id`] — the agent's canonical CellId in its default
//!   federation domain (no string-threading every call).
//! - [`AppCipherclerk::public_key`] — the wallet's identity (32-byte public key).
//! - [`AppCipherclerk::make_action`] — build a single-method action with
//!   multiple effects, signed for the framework's federation_id binding.
//! - [`AppCipherclerk::make_turn`] — wrap a signed action in a Turn with
//!   sane defaults (nonce/forest hash filled by the executor path).
//! - [`AppCipherclerk::sign_action`] — re-sign a pre-built action.
//!
//! ## What apps cannot do through this handle
//!
//! - Extract the underlying signing key (only the framework holds the SDK
//!   wallet; apps see [`AppCipherclerk`] which deliberately exposes no
//!   key-export methods).
//! - Mutate the wallet's receipt chain or token list.
//! - Reach into `AgentCipherclerk`'s 107-method surface — that's an SDK
//!   concern, not an app concern.
//!
//! ## Why a wrapper and not `&AgentCipherclerk`?
//!
//! Exposing `AgentCipherclerk` directly to apps couples the userspace surface
//! to every method we add to the SDK. The framework wallet handle is the
//! intentional narrow waist — when an app needs a new primitive, it's
//! either a *new framework method* (small, reviewed) or a *missing SDK
//! method* (we add it once, the framework method delegates).
//!
//! ## Federation binding
//!
//! Action signatures carry a 32-byte `federation_id` to prevent
//! cross-federation replay (see `pyana_turn::executor::TurnExecutor::compute_signing_message`).
//! The framework holds *one* federation_id per process — set at
//! [`AppCipherclerk::new`] — and threads it into every `make_action` /
//! `sign_action` call. Apps never see it.

use std::sync::{Arc, Mutex, RwLock};

use pyana_sdk::{AgentRuntime, AgentCipherclerk};
use pyana_turn::action::{Action, Effect};
use pyana_turn::{Turn, TurnReceipt};
use pyana_types::{CellId, PublicKey};

/// A wallet handle suitable for app-level userspace.
///
/// Wraps an [`AgentCipherclerk`] and a `federation_id`, exposing only the
/// methods apps need to build signed actions and turns. Cheap to clone
/// (internally `Arc<RwLock<AgentCipherclerk>>` — same shared cell as the
/// embedded executor's runtime, so signing the wallet sees the same
/// receipt chain head as turn submission).
#[derive(Clone)]
pub struct AppCipherclerk {
    inner: Arc<RwLock<AgentCipherclerk>>,
    federation_id: [u8; 32],
    domain: String,
}

impl AppCipherclerk {
    /// Construct an app wallet from an SDK wallet and the federation
    /// identifier this app operates in.
    ///
    /// The default domain is `"default"` — matches `AgentCipherclerk::cell_id("default")`.
    /// Override with [`Self::with_domain`].
    pub fn new(wallet: AgentCipherclerk, federation_id: [u8; 32]) -> Self {
        Self {
            inner: Arc::new(RwLock::new(wallet)),
            federation_id,
            domain: "default".to_string(),
        }
    }

    /// Construct an app wallet from an already-shared SDK wallet handle.
    ///
    /// Use this when the wallet is *also* owned by an
    /// [`EmbeddedExecutor`]'s runtime — both this handle and the
    /// runtime's lock guard share the same underlying agent identity
    /// and receipt chain. The framework constructs the shared handle
    /// itself in [`EmbeddedExecutor::app_wallet`]; apps rarely need to
    /// call this directly.
    pub fn from_shared(wallet: Arc<RwLock<AgentCipherclerk>>, federation_id: [u8; 32]) -> Self {
        Self {
            inner: wallet,
            federation_id,
            domain: "default".to_string(),
        }
    }

    /// Set the default domain used by [`Self::cell_id`] and
    /// [`Self::make_turn`].
    pub fn with_domain(mut self, domain: impl Into<String>) -> Self {
        self.domain = domain.into();
        self
    }

    /// This wallet's public key (the agent identity).
    pub fn public_key(&self) -> PublicKey {
        self.read().public_key()
    }

    /// This wallet's CellId in the framework's default domain.
    pub fn cell_id(&self) -> CellId {
        self.read().cell_id(&self.domain)
    }

    /// This wallet's CellId in an explicit domain (rarely needed; prefer
    /// [`Self::cell_id`]).
    pub fn cell_id_for(&self, domain: &str) -> CellId {
        self.read().cell_id(domain)
    }

    /// The federation_id this wallet signs against.
    pub fn federation_id(&self) -> &[u8; 32] {
        &self.federation_id
    }

    /// Build a self-signed [`Action`] targeting one cell with a list of
    /// effects.
    ///
    /// The action carries a real `Authorization::Signature(..)` — no
    /// `[0u8; 64]` placeholders. The signature binds to this wallet's
    /// public key, the action's canonical bytes, and the framework's
    /// federation_id.
    pub fn make_action(&self, target: CellId, method: &str, effects: Vec<Effect>) -> Action {
        self.read()
            .make_action(target, method, effects, &self.federation_id)
    }

    /// Build a self-signed [`Action`] targeting this wallet's own cell.
    ///
    /// Equivalent to `wallet.make_action(wallet.cell_id(), method, effects)`.
    /// Use this for app-internal actions where the target is the agent's
    /// own cell (transferring between an app's own cells, mutating the
    /// app's local state slot, etc.) and the caller does not want to
    /// repeat `wallet.cell_id()` at every call site.
    ///
    /// See `APPS-USERSPACE-GAPS.md` §Gap 3 for the design framing.
    pub fn make_self_action(&self, method: &str, effects: Vec<Effect>) -> Action {
        self.make_action(self.cell_id(), method, effects)
    }

    /// Re-sign an already-built [`Action`] with this wallet, overwriting
    /// its existing authorization.
    ///
    /// Use this when an action needs to be assembled by lower-level
    /// builders (e.g. multi-step `ActionBuilder` typestate flows that
    /// the framework cannot anticipate) but should still carry a real
    /// framework-issued signature.
    pub fn sign_action(&self, action: Action) -> Action {
        self.read().sign_action(action, &self.federation_id)
    }

    /// Wrap a signed [`Action`] in a [`Turn`] ready for submission.
    ///
    /// The Turn's `agent` is `self.cell_id()`, `previous_receipt_hash` is
    /// pulled from the wallet's chain head, `nonce` defaults to 0 (the
    /// caller's submission path is expected to set the real nonce; see
    /// `pyana_sdk::AgentRuntime::execute`), and forest/tree hashes are
    /// zeroed and filled in by `compute_turn_bytes` at signing time.
    pub fn make_turn(&self, action: Action) -> Turn {
        self.read().make_turn_for(&self.domain, action)
    }

    /// Wrap multiple already-signed [`Action`]s in one [`Turn`] (atomic
    /// group). All actions appear as roots in the same call forest — they
    /// commit or roll back together.
    ///
    /// Use this for cross-action consistency in app settlement flows:
    /// orderbook settlement (release one escrow + create the counterparty
    /// escrow), escrow-swap, multi-leg trades, etc. The per-action
    /// signatures are preserved as-is; this method does not re-sign.
    ///
    /// See `APPS-USERSPACE-GAPS.md` §Gap 5 for the design framing.
    pub fn make_turn_with_actions(&self, actions: Vec<Action>) -> Turn {
        self.read()
            .make_turn_with_actions_for(&self.domain, actions)
    }

    /// Build a signed [`Turn`] that mints a new cell from a deployed
    /// factory descriptor via the canonical `Effect::CreateCellFromFactory`
    /// path.
    ///
    /// This is the *userspace* entry to constructor-transparency cell
    /// birth: the extension wallet's `window.pyana.createFromFactory`,
    /// the wasm runtime's `create_agent`, and any in-process app that
    /// mints cells go through here. No callers should reach past the
    /// `AppCipherclerk` for `Effect::CreateCellFromFactory` — when they do, a
    /// new framework method is the right answer.
    ///
    /// # Arguments
    ///
    /// * `factory_vk` — VK hash of a factory previously deployed via
    ///   `TurnExecutor::deploy_factory`. The factory must accept the
    ///   `mode` from `params`; mismatches surface as a runtime
    ///   `FactoryError::ModeMismatch` when the turn executes.
    /// * `owner_pubkey` — the ed25519 public key of the new cell's owner.
    /// * `token_id` — the token-domain identifier for the new cell.
    /// * `params` — additional creation parameters (program VK, initial
    ///   fields/caps, mode).
    ///
    /// The issuing cell is this wallet's `cell_id()`; the federation_id
    /// is the wallet's bound `federation_id`.
    ///
    /// The returned `Turn` is fully signed (real
    /// `Authorization::Signature(..)`); pair with
    /// [`EmbeddedExecutor::submit_turn`] (or any in-process executor /
    /// remote node `/turns/submit`) to actually mint the cell.
    pub fn create_from_factory(
        &self,
        factory_vk: [u8; 32],
        owner_pubkey: [u8; 32],
        token_id: [u8; 32],
        params: pyana_cell::FactoryCreationParams,
    ) -> Turn {
        let issuer = self.cell_id();
        self.read().create_from_factory(
            issuer,
            factory_vk,
            owner_pubkey,
            token_id,
            params,
            &self.federation_id,
        )
    }

    /// Get a shared handle to the underlying SDK wallet lock.
    ///
    /// Used by the framework to construct an [`EmbeddedExecutor`] that
    /// shares this wallet's receipt chain and signing key. App code
    /// should not call this — if you find yourself reaching here from
    /// an `apps/*` crate, the framework is missing a narrow method.
    pub fn shared_wallet(&self) -> Arc<RwLock<AgentCipherclerk>> {
        Arc::clone(&self.inner)
    }

    /// Take a read lock on the underlying SDK wallet (panic-safe).
    ///
    /// Lock poisoning is recovered by surfacing the (possibly stale)
    /// inner value — matches the convention `pyana_sdk::AgentRuntime`
    /// already uses.
    fn read(&self) -> std::sync::RwLockReadGuard<'_, AgentCipherclerk> {
        self.inner.read().unwrap_or_else(|e| e.into_inner())
    }
}

impl std::fmt::Debug for AppCipherclerk {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AppCipherclerk")
            .field("public_key", &hex_short(&self.public_key().0))
            .field("domain", &self.domain)
            .field("federation_id", &hex_short(&self.federation_id))
            .finish()
    }
}

/// An embedded executor + ledger handle suitable for app-internal turn
/// submission.
///
/// This is the "load-bearing" closure of `APPS-USERSPACE-GAPS.md` §Gap 4:
/// the framework owns a private [`AgentRuntime`] (wallet + local ledger +
/// turn executor) that handlers can reach through an axum
/// `Extension<EmbeddedExecutor>`. When a handler builds a signed
/// [`Action`] via the [`AppCipherclerk`], it can immediately submit the
/// resulting [`Turn`] through this executor and receive a real
/// [`TurnReceipt`] — closing the "action authored and dropped on the
/// floor" pattern that the gap analysis flagged as the remaining seam
/// in the userspace surface.
///
/// Cheap to clone (the runtime sits behind an `Arc`).
///
/// ## When to use embedded vs federation client
///
/// - **`EmbeddedExecutor`** (this type) — for in-process apps that own
///   their own state (nameservice, identity, single-process demos). The
///   ledger lives inside the framework; no network call.
/// - **`FederationClient`** (future) — for apps that submit to a remote
///   federation node. Same handler-side shape; different backend.
///
/// Both routes converge on `submit_turn(turn) -> Result<TurnReceipt, _>`,
/// which is the only method handlers need.
#[derive(Clone)]
pub struct EmbeddedExecutor {
    /// `AgentRuntime` is not Send/Sync because `TurnExecutor` holds a
    /// `RefCell<EpochMinter>`. We make the framework-side wrapper
    /// Send+Sync by serializing all access through a `Mutex`. This is
    /// adequate for single-process apps (the embedded executor is
    /// per-process — there is no contention model that benefits from
    /// concurrent submission, since turns mutate the same ledger).
    runtime: Arc<Mutex<AgentRuntime>>,
    /// Cached read-only handle on the cell id so `Debug` and
    /// `cell_id()` accessors do not have to take the mutex.
    cell_id: CellId,
}

impl EmbeddedExecutor {
    /// Construct an executor that shares the given [`AppCipherclerk`]'s
    /// underlying SDK wallet — so the action-signing handle and the
    /// turn-submission handle both see the same receipt chain head and
    /// signing key.
    ///
    /// The framework wraps the shared wallet in an [`AgentRuntime`] —
    /// which constructs a local [`pyana_cell::Ledger`] seeded with the
    /// agent's cell (1M computrons default balance, see
    /// `AgentRuntime::new_simple`).
    ///
    /// `domain` is the agent's domain string; should match the
    /// `AppCipherclerk`'s [`AppCipherclerk::with_domain`] setting if it was
    /// customized. Defaults to `"default"`.
    pub fn new(wallet: &AppCipherclerk, domain: &str) -> Self {
        let shared = wallet.shared_wallet();
        let runtime = AgentRuntime::new(shared, domain);
        let cell_id = runtime.cell_id();
        Self {
            runtime: Arc::new(Mutex::new(runtime)),
            cell_id,
        }
    }

    /// Construct an executor wrapping a caller-provided runtime.
    ///
    /// Use this when the app constructs an `AgentRuntime` with custom
    /// shared state (e.g., a ledger restored from disk via
    /// `AgentRuntime::with_ledger`). The framework does not own the
    /// runtime in that case — it simply borrows it for submission.
    pub fn from_runtime(runtime: AgentRuntime) -> Self {
        let cell_id = runtime.cell_id();
        Self {
            runtime: Arc::new(Mutex::new(runtime)),
            cell_id,
        }
    }

    /// The cell id of the agent the embedded runtime drives turns from.
    pub fn cell_id(&self) -> CellId {
        self.cell_id
    }

    /// Submit a pre-built [`Turn`] to the embedded executor and return
    /// its [`TurnReceipt`].
    ///
    /// The submitted turn is executed against the framework's private
    /// ledger. On success the agent's receipt chain is extended (in the
    /// runtime's owned wallet copy). This is the path that closes
    /// `APPS-USERSPACE-GAPS.md` §Gap 4 — handlers can now actually
    /// observe a receipt instead of building an action and dropping it.
    pub fn submit_turn(&self, turn: &Turn) -> Result<TurnReceipt, ExecutorSubmitError> {
        let rt = self.runtime.lock().unwrap_or_else(|e| e.into_inner());
        rt.execute_turn(turn)
            .map_err(|e| ExecutorSubmitError(e.to_string()))
    }

    /// Convenience: submit a single signed [`Action`] by wrapping it in
    /// a turn (via [`AppCipherclerk::make_turn`]'s shape) and running through
    /// [`Self::submit_turn`].
    ///
    /// The action's signature is preserved verbatim; the wrapping just
    /// builds the canonical single-action call forest the executor
    /// expects. Useful for endpoints that produced their own signed
    /// action through [`AppCipherclerk::make_action`] and just want to ship it.
    pub fn submit_action(
        &self,
        wallet: &AppCipherclerk,
        action: Action,
    ) -> Result<TurnReceipt, ExecutorSubmitError> {
        let turn = wallet.make_turn(action);
        self.submit_turn(&turn)
    }
}

impl std::fmt::Debug for EmbeddedExecutor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EmbeddedExecutor")
            .field("cell_id", &self.cell_id)
            .finish()
    }
}

/// Error returned by [`EmbeddedExecutor::submit_turn`] /
/// [`EmbeddedExecutor::submit_action`] when the executor rejects the
/// submission.
///
/// Wraps the underlying `pyana_sdk::SdkError` string so the framework
/// surface does not leak the SDK error enum (apps just need to surface
/// the failure to clients; the structured details live in the
/// receipt-chain side of the runtime).
#[derive(Clone, Debug)]
pub struct ExecutorSubmitError(pub String);

impl std::fmt::Display for ExecutorSubmitError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "embedded executor rejected submission: {}", self.0)
    }
}

impl std::error::Error for ExecutorSubmitError {}

fn hex_short(bytes: &[u8]) -> String {
    let n = bytes.len().min(8);
    let mut s = String::with_capacity(2 * n + 1);
    for b in &bytes[..n] {
        s.push_str(&format!("{b:02x}"));
    }
    if bytes.len() > n {
        s.push('…');
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wallet_signs_action_with_real_signature() {
        let sdk = AgentCipherclerk::new();
        let fed = [7u8; 32];
        let wallet = AppCipherclerk::new(sdk, fed);
        let target = CellId::from_bytes([1u8; 32]);

        let action = wallet.make_action(target, "noop", vec![]);

        // The whole point: not Unchecked, and not a zero signature.
        match action.authorization {
            pyana_turn::action::Authorization::Signature(a, b) => {
                assert!(
                    a != [0u8; 32] || b != [0u8; 32],
                    "signature must be non-zero"
                );
            }
            other => panic!("expected Signature variant, got {other:?}"),
        }
    }

    #[test]
    fn wallet_make_turn_binds_to_default_domain() {
        let sdk = AgentCipherclerk::new();
        let wallet = AppCipherclerk::new(sdk, [0u8; 32]);
        let cell = wallet.cell_id();
        let action = wallet.make_action(cell, "noop", vec![]);
        let turn = wallet.make_turn(action);
        assert_eq!(turn.agent, cell);
        assert_eq!(turn.nonce, 0);
    }

    #[test]
    fn with_domain_changes_cell_id() {
        let sdk = AgentCipherclerk::new();
        let w1 = AppCipherclerk::new(sdk, [0u8; 32]);
        let w2 = w1.clone().with_domain("alt-domain");
        assert_ne!(w1.cell_id(), w2.cell_id());
    }

    // NOTE: the "sign_action overwrites Unchecked" test lives in
    // `app-framework/tests/wallet_sign_action.rs` (an integration test
    // directory) — the in-`src/` grep guard
    // (`tests/no_unchecked.rs`) refuses to allow the literal
    // `Authorization::Unchecked` anywhere under `src/`, including in
    // `#[cfg(test)]` blocks. That is by design.

    #[test]
    fn make_self_action_targets_wallet_cell() {
        // Gap 3: ergonomic wrapper for app-internal actions.
        let sdk = AgentCipherclerk::new();
        let wallet = AppCipherclerk::new(sdk, [11u8; 32]);
        let action = wallet.make_self_action("local-bump", vec![]);
        assert_eq!(action.target, wallet.cell_id());
        match action.authorization {
            pyana_turn::action::Authorization::Signature(a, b) => {
                assert!(a != [0u8; 32] || b != [0u8; 32]);
            }
            other => panic!("expected Signature variant, got {other:?}"),
        }
    }

    #[test]
    fn create_from_factory_emits_signed_turn_with_factory_effect() {
        // The canonical constructor-transparency mint path: AppCipherclerk wraps
        // AgentCipherclerk::create_from_factory and binds it to the framework's
        // federation_id. The returned Turn must carry one
        // Effect::CreateCellFromFactory action with a real signature.
        use pyana_cell::{CellMode, FactoryCreationParams};
        use pyana_turn::action::{Authorization, Effect};

        let sdk = AgentCipherclerk::new();
        let wallet = AppCipherclerk::new(sdk, [33u8; 32]);
        let factory_vk = [44u8; 32];
        let owner = [55u8; 32];
        let token = [66u8; 32];
        let params = FactoryCreationParams {
            mode: CellMode::Hosted,
            program_vk: None,
            initial_fields: vec![],
            initial_caps: vec![],
            owner_pubkey: owner,
        };

        let turn = wallet.create_from_factory(factory_vk, owner, token, params);

        // Issuer is the wallet's own cell.
        assert_eq!(turn.agent, wallet.cell_id());
        // Exactly one root action, carrying the factory effect.
        assert_eq!(turn.call_forest.roots.len(), 1);
        let root = &turn.call_forest.roots[0];
        assert_eq!(root.action.effects.len(), 1);
        match &root.action.effects[0] {
            Effect::CreateCellFromFactory {
                factory_vk: fv,
                owner_pubkey: op,
                token_id: tid,
                ..
            } => {
                assert_eq!(*fv, factory_vk);
                assert_eq!(*op, owner);
                assert_eq!(*tid, token);
            }
            other => panic!("expected CreateCellFromFactory effect, got {other:?}"),
        }
        // Real signature, not Unchecked.
        match &root.action.authorization {
            Authorization::Signature(a, b) => {
                assert!(*a != [0u8; 32] || *b != [0u8; 32]);
            }
            other => panic!("expected Signature variant, got {other:?}"),
        }
    }

    #[test]
    fn make_turn_with_actions_bundles_all_roots() {
        // Gap 5: multi-action atomic turn.
        let sdk = AgentCipherclerk::new();
        let wallet = AppCipherclerk::new(sdk, [22u8; 32]);
        let t1 = CellId::from_bytes([1u8; 32]);
        let t2 = CellId::from_bytes([2u8; 32]);
        let a1 = wallet.make_action(t1, "first", vec![]);
        let a2 = wallet.make_action(t2, "second", vec![]);

        // Sanity: the two actions hash differently (different targets/methods).
        assert_ne!(a1.hash(), a2.hash());

        let turn = wallet.make_turn_with_actions(vec![a1.clone(), a2.clone()]);
        assert_eq!(turn.call_forest.roots.len(), 2);
        assert_eq!(turn.call_forest.roots[0].action.target, t1);
        assert_eq!(turn.call_forest.roots[1].action.target, t2);
        // Per-action signatures preserved (not re-signed at turn level).
        assert_eq!(turn.call_forest.roots[0].action.hash(), a1.hash());
        assert_eq!(turn.call_forest.roots[1].action.hash(), a2.hash());
        // Turn agent is the wallet's default cell.
        assert_eq!(turn.agent, wallet.cell_id());
    }
}
