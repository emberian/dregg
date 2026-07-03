//! Starbridge v2 — the native dregg master interface (library core).
//!
//! The headless, gpui-free heart lives here so it is `cargo test`-able and
//! reusable by both builds:
//!   * [`world`] — the embedded verified executor + live local dregg world.
//!   * [`dynamics`] — the observation/event stream of state transitions.
//!   * [`reflect`] — the uniform reflective object model the views consume.
//!   * [`surface`] / [`shell`] / [`compositor`] — the cap-first multi-SURFACE
//!     desktop shell: each dregg cell can be a cap-confined surface
//!     (apps-as-cells), the shell is a cap-first window manager over the live
//!     world, and the [`compositor`] enforces the VERIFIED-SCENE discipline
//!     (T1 non-overlap · T2 label-binding · T3 focus-exclusivity — the Lean
//!     `Dregg2.Apps.Compositor` teeth) at the pixel layer.
//!   * [`agent`] — the AGENT-ACTIVITY surface (the ADOS keystone): an agent
//!     loop's provable activity (held mandate · cap-gated turns · receipts ·
//!     authorization), rendered as a cap-gated surface cell.
//!
//!   * [`swarm`] — the SWARM COORDINATOR (A2 tool-call seam): N agent cells
//!     coordinating as confined Surface cells, with the notify-edge inbox
//!     threading async wakes (`EmitEvent` → `NotifyEdge` → drain turn) between
//!     them. Every action is cap-gated + receipted; the notify edge is async
//!     (the recipient drains in its OWN future turn, not a joint turn).
//!
//! The `native-full` binary (`src/main.rs`) wires these into the gpui cockpit.
//! The wire-contract client (`client`/`model`) lives in the binary crate for
//! the remote-node + `sel4-thin` paths.

// THE SELF-ALIAS — `cockpit`/`login`/`views` (lifted here from the bin so the web
// cdylib can reach the real `Cockpit`) reach their sibling lib modules by the crate
// name (`starbridge_v2::dock`, `starbridge_v2::world`, …) exactly as they did when
// they were bin modules depending on the library. Aliasing self to that name keeps
// every such path resolving WITHOUT editing the cockpit's internals.
#[cfg(any(feature = "gpui-ui", feature = "gpui-web"))]
extern crate self as starbridge_v2;

// The wire-contract DATA MODEL (`GET /status`, `/api/cells`, `/api/events/stream`
// receipt events, the `POST /turn/submit` request shape). Pure serde structs (no
// reqwest, no gpui), so they compile in BOTH builds and are `cargo test`-able —
// the embedded build's LIVE-NODE panel reflects a remote node through these, and
// the sel4-thin build speaks them as its only contract. Single-sourced here (the
// bin re-exports them) so the live-node lane and the thin client share one mirror.
#[cfg(any(feature = "embedded-executor", feature = "sel4-thin"))]
pub mod model;
// The wire-contract CLIENT (`NodeClient::{Mock,Http}`) + the SSE/snapshot I/O.
// The HTTP/SSE byte-pull is gated on `live-node` (pulls `reqwest`); the Mock
// backend + the wire types are always available. Lives in the library so the
// embedded master interface's live-node panel reuses it (not just the thin bin).
#[cfg(any(feature = "embedded-executor", feature = "sel4-thin"))]
pub mod client;

// The LIVE NODE connection — the SSE-drain + live-reflection heart (the pure
// layer is gpui-free + `cargo test`-able; the reqwest I/O is gated on `live-node`).
#[cfg(feature = "embedded-executor")]
pub mod live_node;

// AGENT MEMORY AS A umem — checkpoint/resume a live confined agent's working-set as a
// witnessed portable umem-ref (`project_cell`/`reify_cell` over the per-cell umem Stage
// A), fail-closed under the canonical root tooth. The agent-memory sibling of the
// time-travel scrub's `reify_ledger` boundary restore — gpui-free, mozjs-free.
#[cfg(feature = "embedded-executor")]
pub mod agent_memory;

// The native deos AFFORDANCE surface — htmx-on-crack with the firing→executed-turn
// seam CLOSED through the embedded executor (the thesis `starbridge-web-surface`
// could only model). gpui-free, `cargo test`-able.
#[cfg(feature = "embedded-executor")]
pub mod affordance;

// THE SELF-DESCRIBING VESSEL — a cap-bounded READ surface over a bundled copy of
// the dregg SOURCE (the Rust/Lean/docs that DEFINE the system), shipped inside the
// AppImage at `usr/share/dregg-src/dregg-src.tar.zst`. An agent put INTO deos (the
// embedded Hermes, or the cockpit) can read the source it is trapped within — a
// read cap, no write authority. Always available (zstd/tar only; the firmament
// read-only mount helper is feature-gated inside). See
// `docs/deos/SELF-DESCRIBING-VESSEL.md`.
pub mod source_vessel;

// The WEB-OF-CELLS browser — the cockpit as a native browser of the `dregg://`
// docuverse: it lists the addressable cells (the real `WebOfCells` attested
// fetch + ledger-drawn `OriginChrome`), opens one to its per-viewer affordance
// surface (the real `AffordanceSurface::project_for` attenuation) + rehydration
// liveness-type, and fires an affordance through THIS crate's embedded executor.
// gpui-free, `cargo test`-able (the model is pure data, like `landing`).
#[cfg(feature = "embedded-executor")]
pub mod web_cells;

// WHOLE-CELL TRANSCLUSION — a document/desktop embeds an ENTIRE peer cell as a
// per-viewer attenuated VIEW (vs `web_cells`'s field-VALUE quote). The concrete
// substrate-backed `ChildResolver` for the composition algebra
// (`dregg_doc::composition`): `WholeCellTransclusion::{embed, project_for,
// reshare_to}` over the REAL `TranscludedField` (provenance/anti-forge/no-rot) +
// `Membrane` (per-viewer meet, reshare non-amp) + `AffordanceSurface::project_for`.
// `ComposedCellDocument::resolve_for` resolves a document COMPOSED FROM whole cells
// per-viewer — the runtime resolution sibling of the patch-core `composition.rs`
// structural operator (they meet at the §2.3 resolver seam). gpui-free,
// `cargo test`-able (pure model over the membrane, like `web_cells`).
// See docs/deos/DOC-CELL-COMPOSITION.md §3.4.
#[cfg(feature = "embedded-executor")]
pub mod cell_transclusion;

// The STITCHER — hyperdreggmedia authoring (NOTES §6): render a merge conflict as
// two live alternatives, resolve by a verified patch (conflicts-as-objects).
#[cfg(feature = "embedded-executor")]
pub mod stitcher;

// PROVENANCE NAVIGATOR (NOTES §6): blame/who-did-what over a cell's receipt-chain;
// a turn's detail; go-to-that-point (time-travel cursor).
#[cfg(feature = "embedded-executor")]
pub mod provenance_navigator;

// FORK / CONSENT (NOTES §6): the membrane's shared-fork tiers made visible — a
// consent inbox of pending ConditionalTurns, upgrade requests; each grant a turn.
#[cfg(feature = "embedded-executor")]
pub mod fork_ui;

// DESKTOP AUTHORING (NOTES §6): open/close/raise/lower the desktop layout as
// witnessed SetField turns — the layout itself a rewindable cell (a layout
// commitment in its own slot, like the torn-tab bitset).
#[cfg(feature = "embedded-executor")]
pub mod desktop_authoring;

// dregg:// LINK-PASTE (NOTES §6): select a cell → a dregg:// URI → paste a live
// provenanced transclusion (receipt-pinned, per-viewer, darkens if unauthorized).
#[cfg(feature = "embedded-executor")]
pub mod link_paste;

// The DREGGVERSE navigation — "what links here", the verified per-viewer query on
// the witness-graph. VENDORED byte-identical from the committed
// `dregg_app_framework::dreggverse_map` (a thin pure navigation over the REAL
// `starbridge_web_surface` `Backlinks` + `Membrane`, both already deps here), so the
// cockpit renders the genuine `DreggverseMap::project_for` WITHOUT dragging
// app-framework's heavy tokio/axum/captp tree into this standalone workspace.
#[cfg(feature = "embedded-executor")]
pub mod dreggverse_map;

// The WHAT-LINKS-HERE panel model — Ted Nelson's two-way link, navigable: for the
// focused cell it builds a REAL `Backlinks` witness-graph from the live image, walks
// it with the vendored `DreggverseMap`, and projects through the focused agent's
// `Membrane` (the link fog-of-war). gpui-free, `cargo test`-able (pure data, like
// `web_cells`/`landing`).
#[cfg(feature = "embedded-executor")]
pub mod links_here;

// THE DOCUMENT EDITOR model (the DOCS tab) — the dreggverse document language made a
// cockpit surface (`docs/deos/DOCUMENT-LANGUAGE.md`). A document IS a real
// `dregg_cell::Cell`, an edit IS a cap-gated turn through the genuine
// `dregg_turn::TurnExecutor` (riding `dregg_doc::ExecutorDrivenDoc`), a conflict is a
// first-class `ConflictRegion` STATE (two live alternatives, each attributed to who
// wrote it — provenance IS the receipt), resolved by a later patch. Transclusion +
// backlinks reuse the existing `web_cells`/`links_here` Nelson pieces. gpui-free,
// `cargo test`-able (pure model over the `dregg-doc` patch core, like `web_cells`).
#[cfg(feature = "embedded-executor")]
pub mod doc_editor;

// XANADU, END TO END — the dreggverse document language as ONE running demonstration
// (`docs/deos/DOCUMENT-LANGUAGE.md`). The WELD over the built organs: a document of
// patches branched + merged (clean + conflict-as-object + resolve, via the `dregg-doc`
// patch core AND the real executor `DocEditor`), a live provenanced whole-cell
// transclusion that darkens per-viewer, and the two-way link registered both directions
// so the cited cell's "what links here" lists the document. gpui-free, `cargo test`-able.
#[cfg(feature = "embedded-executor")]
pub mod xanadu_e2e;

// The interactive POWERBOX (CapDesk) — the trusted designation flow: an app-cell
// requests a capability it lacks; the trusted UI (the cockpit principal, NOT the app)
// presents a picker filtered to what the USER actually holds (mint_needs_held_factory
// made visible); the user designates a target + attenuated rights; the powerbox mints
// a fresh attenuated cap into the app's c-list via a REAL grant turn through the
// embedded executor. gpui-free, `cargo test`-able (pure flow model, like `web_cells`).
#[cfg(feature = "embedded-executor")]
pub mod powerbox;

// THE GRAPHIDEOS SYSTEMUI CAP-CHROME — the deos cockpit AS the android system UI
// (GRAPHIDEOS.md §1 SystemUI row · §2 stage 4). Dresses a confined android-cell's live
// cap-badge set (`android_cell::PermWorld`) as the two SystemUI surfaces a phone user
// sees — the status bar (compact `🛡 held/total` cap strip) and the quick-settings shade
// (the WHOLE roster lit ●/dim ○, no hidden Settings tree) — plus the powerbox hand-over
// sheet, which grants a dangerous cap through the REAL `Effect::GrantCapability` so the
// permission cap lands in the app's c-list with a kernel receipt. App/presentation over
// proven machinery; no new kernel effect. gpui-free, `cargo test`-able (like `powerbox`).
#[cfg(feature = "android-systemui")]
pub mod systemui_caps;

// DREGG-MUD — the first slice of a decentralized multi-user world: a room is a
// cell, an inhabitant is a cap-rooted session, an item is a capability, an action
// is a verified turn. `Room`/`Inhabitant`/`Item` over the REAL world+powerbox; the
// load-bearing test proves "two players, one picks up an item, the other can't dupe
// it" (capability conservation). gpui-free, `cargo test`-able. See
// `docs/deos/DREGG-MUD.md`.
#[cfg(feature = "embedded-executor")]
pub mod mud;

// THE APP REGISTRY — pre-built starbridge-apps (gallery / tussle / sealed-auction /
// bounty-board) wired into the live cockpit. An `AppRegistry` lists each app with
// its real `*_app(cipherclerk, executor) -> DeosApp` ctor; launching one
// instantiates it over a live app-substrate (an `AppCipherclerk` + `EmbeddedExecutor`
// from `dregg-app-framework`), seeds its backing cell, and its affordances fire REAL
// verified turns on that substrate's ledger — visible to a second reader (the
// inspector seam). Gated on `app-registry` (pulled by `embedded-executor`);
// gpui-free + `cargo test`-able. See `docs/deos/APP-AND-FEDERATION-CENSUS-2026-06-23.md`.
#[cfg(feature = "app-registry")]
pub mod app_registry;

// THE APP→WORLD COMMIT BRIDGE — re-point a launched starbridge-app's seed cell AND
// its affordance turns onto the cockpit's LIVE `World` ledger (the SAME one the
// cell inspector reads), exactly as the editor lane's `WorldSpine` mounts file-cells
// onto the live World. `AppWorldSpine::seed` genesis-installs the app cell + program
// + state on `World`; `AppWorldSpine::commit` runs each affordance through
// `World::turn` → `World::commit_turn`, so the app's cells + receipts show in the
// cockpit's own inspector, not the app framework's side-ledger. Used by
// `app_registry::AppEntry::launch_on_world`. gpui-free + `cargo test`-able. Gated on
// BOTH `embedded-executor` (for `crate::world::World`) AND `app-registry` (for the
// `dregg-app-framework` types it bridges) — the app crates are non-wasm-only, so this
// bridge is a native-only surface (the wasm web bundle carries neither).
#[cfg(all(feature = "embedded-executor", feature = "app-registry"))]
pub mod app_worldspine;

// SHARED CONFINED FORK WITH GRADUATED CONSENT — "invite someone to my computer":
// a `World::fork` handed to another principal, confined (firmament sandbox) so they
// cannot escape it, whose culled cap-subgraph is graduated into three tiers —
// EMBEDDED (exercised locally, no consent), STUDYREF (a read-only `ReadCap`; exercise
// needs an upgrade request), NETWORKBOUNDARY (exercise = a `ConditionalTurn` whose
// `ProofCondition` is the owner's grant; resolves on consent, fail-closed otherwise).
// The authority/consent TYPING of the membrane (the deos-chat lane owns transport).
// See docs/deos/SHARED-FORK-CONSENT.md. Welds over powerbox + read_cap + conditional +
// branch_stitch; reinvents none of them.
#[cfg(feature = "embedded-executor")]
pub mod shared_fork;

// THE MEMBRANE ON UMEMS — distributed branch-and-stitch recast as universal-memory
// operations. The membrane's three moves over the ONE address space of `dregg_turn::umem`:
// a FORK is a umem branch (a cap-bounded subgraph projected to a `UProjection`), a CARRY
// is a passable umem (the projection serialized into a `UmemEnvelope` with an
// anti-substitution root tooth), a STITCH is a umem merge (a per-`UKey` join of two driven
// projections — conflicts surface as first-class `UmemConflict` objects keyed at the EXACT
// address that diverged, so two principals editing DIFFERENT fields of the SAME cell fold
// clean where the cell-granular `Atom` merge would collide). Distributed state-handoff
// becomes witnessed-umem-handoff. The per-handoff Blum-trace witness (the carry binding
// pre→post to the executor's op trace) is the named seam. gpui-free + `cargo test`-able.
#[cfg(feature = "embedded-executor")]
pub mod umem_membrane;

// BRANCH-AND-STITCH SESSION — the distributed-Houyhnhnm primitive made transport-free. The
// GUTS of `ForkMembraneHost::stitch_pair` (fork → drive → project → settlement-sound gate)
// lifted out of the deos-matrix-gated host into a `World`-native API a plain demo can call:
// `BranchStitchSession::{open, fork, base_mut, stitch}` + `Branch::drive`. Composition only —
// it imports the existing public surface of `world`/`shared_fork`/`umem_membrane` and edits
// none of them. Two participants fork one shared verified world, diverge on independent
// branches, and stitch back through one gated door: disjoint edits merge clean, a same-address
// clash is refused fail-closed (both readings kept), and a cap revoked on main between branch
// and settlement is LINEAR-DROPPED — the operable shadow of `Metatheory.SettlementSoundness`.
// gpui-free + deos-matrix-free + `cargo test`-able under `--features embedded-executor`.
#[cfg(feature = "embedded-executor")]
pub mod branch_stitch_session;

// AGENT ATTACH — bind the confined agent's `run_js` (deos-js) to the cockpit's LIVE
// World, so a Claude in Hermes drives the operator's ACTUAL cells (or a fork). The
// cockpit-side `deos_js::WorldSink` weld + the cap-bounded attach. Gated on
// `agent-js` (pulls deos-js's mozjs/SpiderMonkey).
#[cfg(feature = "agent-js")]
pub mod agent_attach;

// THE HIRELING — a real confined agent (deos-hermes brain + gate) that LIVES in the
// desktop World: `hire_resident` mints it a real cell under an attenuated mandate,
// each ADMITTED tool-call mirrors a real verified turn onto the resident's cell
// (`World::turn` + `commit_turn`, the `agent_attach` shape), and each gate REFUSAL is
// surfaced (not fabricated). The named seam the Agent Room drives (Hire/Fire buttons
// weld later — see the module doc). gpui-free + mozjs-free; needs deos-hermes (from
// `dev-surfaces`) + the World (`embedded-executor`).
#[cfg(all(feature = "dev-surfaces", feature = "embedded-executor"))]
pub mod resident_agent;

// DISTRIBUTED MULTIPLAYER CARDS — two principals on DIFFERENT instances co-drive ONE
// shared card across a membrane boundary. Welds deos-js's `coauthored_card` (the LOCAL
// fork/drive/stitch) to the `shared_fork` membrane's serialize→carry→rehydrate pattern
// (with an anti-substitution root tooth): principal A seals its driven card-fork to a
// portable `CardForkEnvelope`, B opens it on its own instance, rehydrates its OWN live
// cap-bounded fork, drives it, and stitches by the `dregg_doc` pushout — a clean merge
// keeps both edits, an overlap surfaces a resolvable `ConflictRegion`, an unauthorized B
// contributes no patch (the cap tooth). gpui-free + `cargo test`-able. Gated on
// `agent-js` (pulls deos-js; implies `embedded-executor` → `dregg-doc` + the membrane).
#[cfg(feature = "agent-js")]
pub mod distributed_card;

// CARD PANE — mount a hyperdreggmedia CARD (a deos-js applet's view-tree) as a LIVE
// cockpit surface, backed by the cockpit's REAL `World` (a `CardPane` gpui `Render`
// view that fires verified turns on the live ledger). Gated on `card-pane` (pulls
// deos-view's gpui renderer + deos-js via `agent-js`).
#[cfg(feature = "card-pane")]
pub mod card_pane;

// The comms-PD chat source — the REAL, executor-backed `deos_matrix::ChatSource`
// the interactive deos-chat surface drives: it holds a live `World` and makes the
// chat UI's membrane affordances genuine (mint/rehydrate/drive/stitch over real
// `Cell` frusta), never a mock envelope. Gated on `dev-surfaces` (where the
// deos-matrix `ChatSource` trait is in scope).
#[cfg(feature = "dev-surfaces")]
pub mod comms_pd_source;

// The world-backed chat TRANSPORT — "the chat IS the dregg world". Rooms are real
// cells, a sent message is a real verified turn, the timeline is read back from
// real cell state. No mock, no recorded sync — the in-process / nested real
// transport (a live `MatrixHandle` is the federated alternative). Gated on
// `dev-surfaces`.
#[cfg(feature = "dev-surfaces")]
pub mod world_chat;

// The deos SESSION / LOGIN MANAGER — login = receiving your ROOT CAPABILITY, a
// session = the cap-tree you hold, logout = revoking it. The L6-adjacent trusted
// piece the WM/login investigation found missing. Authenticate (a key proof) →
// derive the identity cell (`CellId::derive_raw(pubkey, ROOT_TOKEN)`) → grant the
// per-user `CapTemplate` into it FROM the system principal via the REAL grant
// turn (so mint_needs_held_factory + attenuation bite) → the root-cell c-list IS
// the session → logout revokes it (synchronous, the whole tree dark at n=1). An
// agent (Hermes) login is the SAME ceremony with a narrower template — a
// cap-bounded inhabitant of the deos polis. See docs/deos/SESSION-LOGIN.md.
// Welds over powerbox + derive_raw + Grant/RevokeCapability; reinvents none.
#[cfg(feature = "embedded-executor")]
pub mod session;
#[cfg(feature = "embedded-executor")]
pub use session::{
    agent_template, default_user_template, demo_identities, provision_system_principal, CapEntry,
    CapTemplate, DemoIdentity, IdentityKind, LoginManager, LoginOutcome, Principal, Session,
    ROOT_TOKEN,
};

#[cfg(feature = "embedded-executor")]
pub mod agent;
// THE LETTER OFFICE (docs: the Postmark resonance): mail between agents as cells on
// the live World — a letter IS a cell carrying its markdown in the heap; sending drops
// it in an outbox cell; delivery is a receipted turn moving it to an inbox cell. gpui-free
// + `cargo test`-able; the desktop `mail_room` maps it onto an NT window.
#[cfg(feature = "embedded-executor")]
pub mod buffer;
#[cfg(feature = "embedded-executor")]
pub mod cipherclerk;
#[cfg(feature = "embedded-executor")]
pub mod compositor;
#[cfg(feature = "embedded-executor")]
pub mod coordination;
#[cfg(feature = "embedded-executor")]
pub mod debug;
#[cfg(feature = "embedded-executor")]
pub mod demo;
#[cfg(feature = "embedded-executor")]
pub mod dynamics;
#[cfg(feature = "embedded-executor")]
pub mod edit;
#[cfg(feature = "embedded-executor")]
pub mod graph;
#[cfg(feature = "embedded-executor")]
pub mod landing;
#[cfg(feature = "embedded-executor")]
pub mod letter_office;
#[cfg(feature = "embedded-executor")]
pub mod narration;
#[cfg(feature = "embedded-executor")]
pub mod organs;
#[cfg(feature = "embedded-executor")]
pub mod palette;
#[cfg(feature = "embedded-executor")]
pub mod proofs;
#[cfg(feature = "embedded-executor")]
pub mod reflect;
#[cfg(feature = "embedded-executor")]
pub mod replay;
// THE ROOM + INHABITANT (ORGAN 5): a room is a place that CONTAINS inhabitants;
// an inhabitant is a cell + a held MANDATE + presence; the room view renders each
// inhabitant's mandate + live actions, surfacing every in-room REFUSAL with the
// receipt-why (the anti-ghost tooth, visible). Welds the `agent` activity model.
// gpui-free, `cargo test`-able (pure room model over the World, like `web_cells`).
#[cfg(feature = "embedded-executor")]
pub mod room;
#[cfg(feature = "embedded-executor")]
pub mod scene;
// WHAT-IF SIMULATION — compose any intent over any cell + an exhaustive effect
// palette, predict its consequences in a FORKED throwaway world (the real
// executor over a deep copy of the live ledger), then commit it for real. The
// prediction is the live executor's verdict run one turn ahead; the live world is
// never touched until commit. gpui-free, `cargo test`-able.
#[cfg(feature = "embedded-executor")]
pub mod organ_ops;
#[cfg(feature = "embedded-executor")]
pub mod shell;
#[cfg(feature = "embedded-executor")]
pub mod simulate;
#[cfg(feature = "embedded-executor")]
pub mod surface;
#[cfg(feature = "embedded-executor")]
pub mod swarm;
#[cfg(feature = "embedded-executor")]
pub mod swarm_budget;
#[cfg(feature = "embedded-executor")]
pub mod terminal;
#[cfg(feature = "embedded-executor")]
pub mod token_inspector;
#[cfg(feature = "embedded-executor")]
pub mod world;
// THE PARTIAL-TURN LIFT (docs/deos/PARTIAL-TURN-LIFT.md): the held-promise
// continuation. `held_promise` is the standalone model (holes + guards +
// EMPTY/HELD/READY lifecycle); `pipeline_continuation` is the LIFT — that
// continuation carried by a real `dregg_turn::Pipeline` whose holes are real
// `EventualRef`s on `Target::Eventual`/`PipelinedSend` targets (a hole IS a
// nullifier; resolution IS a spend, once, fail-closed). gpui-free, test-able.
#[cfg(feature = "embedded-executor")]
pub mod held_promise;
#[cfg(feature = "embedded-executor")]
pub mod pipeline_continuation;
// NATIVE WORLD PERSISTENCE (M4 — docs/deos/WORLD-PERSISTENCE-PLAN.md): the
// durable-image weld onto the node's already-built `dregg-persist` spine (redb
// commit log + checkpoint⊕overlay recovery). gpui-free, `cargo test`-able.
#[cfg(all(feature = "embedded-executor", not(target_arch = "wasm32")))]
pub mod persistence;
// On wasm32 there is no `dregg-persist` (it pulls `redb`, native-only). The
// browser image is always ephemeral; this stub supplies exactly what `world.rs`
// imports (`WorldPersist`/`OpenError`/`RecoveredImage` + `canonical_ledger_root`).
#[cfg(all(feature = "embedded-executor", target_arch = "wasm32"))]
#[path = "persistence_wasm.rs"]
pub mod persistence;

// THE DURABLE-IMAGE WELD for the windowed desktop (docs/deos/WORLD-PERSISTENCE-PLAN.md):
// make "your world is one durable image" LITERALLY true for `--desktop` by booting the
// desktop's World from the durable redb image (open-recovering + seed-on-first-run) beside
// the layout sidecar, with a :memory:/ephemeral escape hatch for bakes/tests/CI. Builds NO
// persistence — it is the boot policy over `persistence` + `World::open_recovering`,
// mirroring `session::open_session_world`. Native-only (durable open pulls redb),
// gpui-free + `cargo test`-able.
#[cfg(all(feature = "embedded-executor", not(target_arch = "wasm32")))]
pub mod durable_desktop;

// THE LIVE INSPECT→ACT LOOP — the Smalltalk inspect→act→inspect keystone: an
// inspected object shows the messages it understands (its cap-gated affordances)
// inline, fires one as a real verified turn, and re-inspects the post-state.
// gpui-free, `cargo test`-able (reuses `reflect` + `affordance` + `world`).
#[cfg(feature = "embedded-executor")]
pub mod inspect_act;
// THE DESKTOP IN A LINK — the share-URL tape codec (`deos1!ts=…!act=…`): a
// desktop shared as its pinned instant + message tape + root claim, replayed
// against a FRESH world by the recipient (read-only re-derivation, never a
// trusted screenshot). The codec half is pure std+hex (gpui-free, compiles
// everywhere the crate does — the wasm cockpit can adopt the same format);
// the `replay_onto`/`replay_fresh` half is embedded-executor-gated and fires
// the REAL `inspect_act` send path. Served by the serve-ie6 `/shared` route;
// the static viewer page lives at `site/deos-viewer/`.
pub mod share_link;
// THE SERVICE EXPLORER — a Postman-like surface for INVOKING cell methods: it
// discovers a cell's published interface (derive-from-program, or a registered
// descriptor), lets you pick a method + fill args, and invokes it as a real
// verified turn (the `invoke()` front door, deos-interior — no kernel effect).
// gpui-free, `cargo test`-able (reuses `reflect` + `world` + dregg-cell's
// InterfaceDescriptor routing). The cockpit renders this model.
#[cfg(feature = "embedded-executor")]
pub mod service_explorer;
// THE SERVICE DIRECTORY — the whole-image sibling of `service_explorer`: it
// BROWSES every service-publishing cell in the live ledger (deriving each cell's
// interface, the cells-as-service-objects directory of the image) and lets the
// operator ANNOUNCE a service as a real verified turn (an `Effect::EmitEvent`
// carrying the interface_id — the `dregg-directory` "emit standard effects"
// stance), read back from the receipt history so the discover↔announce loop
// closes over the real ledger. gpui-free, `cargo test`-able. See
// `docs/deos/SERVICE-DISCOVERY-UI.md`. The cockpit panel that renders this model
// is the named next build.
#[cfg(feature = "embedded-executor")]
pub mod service_directory;
// THE LIVE WORKSPACE — the doIt / printIt / inspectIt evaluator: compose an
// intent, evaluate it in a forked throwaway world (predict, never mutate), print
// the predicted receipt, inspect the predicted post-state as live objects, then
// commit-or-discard. gpui-free, `cargo test`-able (reuses `simulate` + `reflect`).
#[cfg(feature = "embedded-executor")]
pub mod workspace;
// THE WONDER ROOM — the AOL-wonder front door: every cell a pokeable glowing
// object (glow = real recent activity from `dynamics`), with direct-manipulation
// halos (inspect/grab/explain) and drag-value transfers (predict-then-commit).
// gpui-free, `cargo test`-able. See `docs/deos/AOL-WONDER.md`.
#[cfg(feature = "embedded-executor")]
pub mod wonder;
// THE PRESENTATION SPINE (L1) — the Pharo-moldable framework primitive: every protocol
// object offers MULTIPLE named presentations (the 7 PresentationKinds; RawFields = the
// existing reflect::Inspectable floor) + the Gadget/CommittingGadget traits (interactive
// construction on the simulate→commit spine) + Spotter (universal search) + the
// generalized Halo. The spine everything inherits. See docs/deos/INSPECTOR-FRAMEWORK.md.
#[cfg(feature = "embedded-executor")]
pub mod presentable;
// THE REHYDRATABLE UI-SLICE SNAPSHOT — "the camera you can re-run": a tiny witness-cursor
// (focus + presentation-kind + height/receipt-head) that re-derives the SAME inspector view
// from the durability log (replay → re-project), liveness-typed (Live/ReplayedDeterministic/
// ReconstructedApproximate). The screenshot keeps the angle, drops the frame. See REHYDRATABLE-SURFACES.md.
#[cfg(feature = "embedded-executor")]
pub mod ui_snapshot;
// THE FRUSTUM / SNAPSHOT EDITOR (the ⤳ SHARE surface) — the pre-send editor where you
// sculpt a UI-slice snapshot, CULL the frustum (which lenses/sub-objects are IN the
// shared slice), PARE the authority (the real `AttenuationDial` over `is_attenuation` —
// it REFUSES amplification in-band), VERIFY live (the membrane-projected per-viewer
// preview), and SHARE a revocable, attenuated, rehydratable `SharedArtifact`. Reuses
// `ui_snapshot` + `affordance` (the membrane `rehydrate_for`) + `cap_inspector`
// (`AttenuationDial`) + the genuine `is_attenuation`. gpui-free, `cargo test`-able. The
// GitHub-org-settings cap UX. See `docs/desktop-os-research/REHYDRATABLE-SURFACES.md`.
#[cfg(feature = "embedded-executor")]
pub mod snapshot_editor;
// THE UI-CELL SUBSTRATE (M3 · reflexive migration §3) — the cockpit's own view-state
// self-hosted as real dregg cells via the proven BufferCell two-tier split: ViewCell
// (a view's focus/present-idx camera-aim, free in-memory draft + occasional witnessed
// SetField commit, revision = backing nonce) is itself Presentable (FocusTarget::ViewCell)
// so the inspector can inspect ITSELF; WorkspaceCell carries the active-tab selector.
// `present` stays PURE and reads the COMMITTED (prior-frame) aim — the unit-delay that
// breaks the reflexive self-cycle. See docs/deos/{REFLEXIVE-MIGRATION,STRATIFIED-FIXPOINT}.md.
#[cfg(feature = "embedded-executor")]
pub mod view_cell;
// THE FRACTAL META-DEBUG (M5 · reflexive migration §4) — suspend the live system,
// inspect it as an object, recursively (debug the debugger). Suspend=halt-the-live-loop
// (the World gate + pending queue, distinct from Snapshot=freeze-a-cursor); MetaDebugView
// impl Presentable over the suspended world (FocusTarget::DebugFrame/World/Cockpit — the
// one-arm reflexivity); the MetaStack is the lazily-materialized 3-Lisp tower, grounded at
// the gpui loop. See docs/deos/{FIRMAMENT-REFLEXIVE-SUBSTRATE,REFLEXIVE-MIGRATION,STRATIFIED-FIXPOINT}.md.
#[cfg(feature = "embedded-executor")]
pub mod meta_debug;
// THE TEMPORAL COCKPIT model — the gpui-free brain behind the "⏳ TIME" tab: the
// rewind scrubber (verified History::replay_to + the Liveness badge), the ⏸ suspend
// gate readout (the M5 World gate + the staged continuation), and the MetaStack
// breadcrumb (the reflective tower). Reuses replay/ui_snapshot/meta_debug — never a
// parallel time/debug model. The cockpit's TIME tab paints this pure projection.
#[cfg(feature = "embedded-executor")]
pub mod cell_inspector;
#[cfg(feature = "embedded-executor")]
pub mod time_travel;
// THE READ-CAP / PRIVACY lens — the read-confidentiality membrane, welded onto the
// landed `dregg_cell_crypto::read_cap` organ (docs/deos/PRIVACY-CONFIDENTIALITY.md M0): the
// encrypted-field set off live field-visibility, the `granted ⊆ held` read-lattice
// (real ReadCap::attenuate), and the byte-identical-commitment invariant demonstrated
// live. Lights up the cockpit's "🔒 read-cap / privacy" lens (was a weld placeholder).
#[cfg(feature = "embedded-executor")]
pub mod read_cap_lens;
// THE DOCUMENT lens — a literate `dregg_doc` document through the moldable inspector
// (docs/deos/DOCUMENT-LANGUAGE.md §4): rendered content · patch-history trail ·
// conflict-as-state · commitment + two-regime. The uniform INSPECT face to the DOCS
// tab's AUTHOR face, riding the green dregg-doc patch core. First-class ObjectKind.
#[cfg(feature = "embedded-executor")]
pub mod doc_lens;
// THE DESKTOP IS A DOCUMENT — the reflexive projection of the live cockpit
// workspace (its CompositorScene of surfaces + its WorkspaceCell tab selector) as a
// dregg_doc document, so a desktop is shareable/rehydratable/branchable/diffable
// through the SAME machinery a prose document is. gpui-free + cargo-testable; the
// WELD between the scene graph and the patch core (docs/deos/DOC-CELL-COMPOSITION.md).
#[cfg(feature = "embedded-executor")]
pub mod desktop_doc;
// THE DOCUMENT COMPOSER — author a document COMPOSED FROM cells, by hand
// (HYPERDREGGMEDIA-NOTES.md §6, authoring surface #7): add an embed (a cell), reorder
// children, remove one, set a child's role — each a real composition patch on the
// document cell's layout (`Op::Embed`/`Order`/`Remove`), returning its receipt. The
// AUTHORING face to the embed algebra `cell_transclusion`/`desktop_doc` already READ.
// gpui-free logic core over `dregg_doc::composition`; cargo-testable.
#[cfg(feature = "embedded-executor")]
pub mod document_composer;
// THE HISTORY / UNDO lens — per-cell reversibility welded onto the landed
// `dregg_turn::reversible` organ (M-REV-0): the reversibility map (each change-kind
// classified by the real Effect::invert over the live ledger into clean/contextual/
// committed) + the cell's lifecycle posture + the un-turn model. Lights up the
// cockpit's "⟲ history / undo" lens (was the last weld placeholder).
#[cfg(feature = "embedded-executor")]
pub mod cap_inspector;
#[cfg(feature = "embedded-executor")]
pub mod history_lens;
#[cfg(feature = "embedded-executor")]
pub mod predicate_composer;
#[cfg(feature = "embedded-executor")]
pub mod receipts_inspector;
// THE TRUST PANEL (human-layer M1 · docs/deos/HUMAN-LAYER.md §3) — the WHO-I-AM face
// (identity card: devices = the current key set, guardians-as-faces = the recovery
// council with its M-of-N threshold drawn, the KEL/rotation timeline) + the recovery
// UX (set guardians, "ask your guardians" quorum progress, the cooling window as a
// safety feature). A gpui-free Presentable over the REAL `dregg_sdk::identity`
// reflection + cipherclerk, the same shape as the other inspector lanes.
#[cfg(feature = "embedded-executor")]
pub mod trust_panel;
// L1-LANE INSPECTORS/GADGETS (the moldable-inspector multiplicity, all on the spine):
// turn_builder (effect/call-forest/turn) · predicate_composer (the caveat-language uplift) ·
// cap_inspector (attenuation/cap-crown) · cell_inspector (deep state) · receipts_inspector
// (time-travel) · token_inspector (macaroon loop). See docs/deos/INSPECTOR-FRAMEWORK.md.
#[cfg(feature = "embedded-executor")]
pub mod settlement_inspector;
#[cfg(feature = "embedded-executor")]
pub mod turn_builder;
// L8/L9 INSPECTORS: federation_inspector (consensus/blocklace/finality — wire-backed +
// honest remote-path catalog) · circuit_inspector (the 8-felt commitment anti-omission
// binding, nullifier non-membership, proof tiers). On the spine; see INSPECTOR-FRAMEWORK.md.
#[cfg(feature = "embedded-executor")]
pub mod circuit_inspector;
#[cfg(feature = "embedded-executor")]
pub mod federation_inspector;
// THE CV-BRIDGE (milestone #1): "blame this cell" — ClusterVision's provenance
// (`cv blame`) wired into the inspector as a Presentable. Bridges EXTERNALLY (cv
// as the read/query face; no substrate change), degrades honestly when cv is
// absent. See docs/deos/REFLEXIVE-DISTRIBUTED-IMAGE.md §2.5/§3.3.
#[cfg(feature = "embedded-executor")]
pub mod cv_provenance;

// THE REFLEXIVE DISTRIBUTED IMAGE (n > 1) — one dregg image inspects/debugs/branches
// a REMOTE one across distance (docs/deos/REFLEXIVE-DISTRIBUTED-IMAGE.md +
// FIRMAMENT-REFLEXIVE-SUBSTRATE.md §4). `remote_mirror` is the static read face (a
// `MirrorCap` = a real `dregg_firmament::Capability` over a `Target::Distributed`
// cell × a `MirrorDepth` attenuation axis; the read/write split is
// `viewSurface_confers_no_edge`). `remote_mirror_live` is the live face (a `Live`
// mirror follows the remote dynamics tail; a `ReadState` mirror is refused —
// `viewState_confers_no_dynamics`). `netlayer_image` is the WELD that makes n > 1 a
// WIRE FACT: a `RemoteImage` resolved over a REAL `dregg_captp` `NetConnection` (the
// `MirrorFrame` request/response over `send`/`recv`, served by an `ImageResponder`
// at the inbound mirror-cap's authorized depth — never amplifying). gpui-free,
// `cargo test`-able (the in-process netlayer fabric, no sockets).
#[cfg(feature = "embedded-executor")]
pub mod netlayer_image;
#[cfg(feature = "embedded-executor")]
pub mod remote_mirror;
#[cfg(feature = "embedded-executor")]
pub mod remote_mirror_live;

// BRANCH-AND-STITCH — distributed time-travel as two first-class effects:
// `EnterVirtualization` (a cap-confined fork of a PAST config whose side-effects are
// structurally imaginary — `branch_cannot_drain_main`) and `Stitch` (the
// pushout-correct, explicitly-lossy settlement gated by Settlement Soundness —
// authority read at the SETTLEMENT TIP). The operable Rust face of the proven Lean
// `Dregg2.Deos.BranchStitch` + `Dregg2.Circuit.SettlementSoundness` keystones.
// `distributed_timetravel` is the runnable two-party collaborative-rewind scenario
// over a `SharedTimeline`. gpui-free, `cargo test`-able. See
// docs/deos/{DISTRIBUTED-TIMETRAVEL-SEMANTICS,BRANCH-AND-STITCH-PROTOCOL}.md.
#[cfg(feature = "embedded-executor")]
pub mod branch_stitch;
#[cfg(feature = "embedded-executor")]
pub mod distributed_timetravel;
// THE TWO-IMAGE FIRMAMENT runnable — TWO in-process dregg images on ONE
// `InProcessNetlayer` that mirror+reflect each other's cells over a DIALED captp
// session, REFUSE the write edge across the wire, and branch+stitch a shared past
// with the settlement gate read at the dialed tip. n > 1 made a wire fact.
#[cfg(feature = "embedded-executor")]
pub mod two_image_firmament;

#[cfg(feature = "embedded-executor")]
pub use presentable::{
    CommittingGadget, FocusTarget, Gadget, GadgetError, GadgetField, GadgetInput, GadgetKind,
    GadgetValidation, GaugeView, GraphView, Halo, HaloCommand, LatticeView, MerkleTreeView,
    PresentCtx, Presentable, PresentableExt, Presentation, PresentationBody, PresentationKind,
    ReflectedCell, Registry, SmState, SmTransition, Spotter, SpotterHit, StateMachineView,
    TimelineEvent, TimelineView, TraceStep, TraceView,
};
#[cfg(feature = "embedded-executor")]
pub use view_cell::{ViewCell, ViewDoc, ViewError, WorkspaceCell};

#[cfg(feature = "embedded-executor")]
pub use affordance::{
    AffordanceIntent, AffordanceSnapshot, AffordanceSurface, CellAffordance, EffectSummary,
    FireError, FireOutcome, Rehydration,
};
#[cfg(feature = "embedded-executor")]
pub use agent::{AgentActivity, AgentSurface};
#[cfg(feature = "embedded-executor")]
pub use buffer::{BufferCell, BufferDoc, BufferError, BufferView};
#[cfg(feature = "embedded-executor")]
pub use compositor::{
    label_of, CompositedSurface, Compositor, CompositorScene, FrameCommit, Present, PresentError,
    RegionId,
};
#[cfg(feature = "embedded-executor")]
pub use coordination::{MandateArrow, NotifyArrow, SwarmGraph, SwarmNode};
#[cfg(feature = "embedded-executor")]
pub use demo::{render_headless_report, DemoError, DemoFrame, HeadlineDemo};
#[cfg(feature = "embedded-executor")]
pub use doc_editor::{AttributedAlternative, ConflictView, DocAuthor, DocEditor, EditOutcome};
#[cfg(feature = "embedded-executor")]
pub use dreggverse_map::{DreggverseGraph, DreggverseLink, DreggverseMap};
#[cfg(feature = "embedded-executor")]
pub use graph::{GraphEdge, GraphLayer, GraphNode, OcapGraph};
#[cfg(feature = "embedded-executor")]
pub use landing::{LandingPortal, PortalLine, PortalSection, Tone};
#[cfg(feature = "embedded-executor")]
pub use links_here::{BacklinkRow, LinksHerePanel};
#[cfg(feature = "embedded-executor")]
pub use live_node::{LiveReflection, ReceiptFeed, SseParser, SseRecord};
#[cfg(feature = "embedded-executor")]
pub use narration::{
    ClaimPosture, ClaimedAction, Correlation, Divergence, NarrationPanel, NarrationRow,
};
#[cfg(feature = "embedded-executor")]
pub use organ_ops::{OrganDriver, OrganOp, OrganOpError, OrganOpOutcome};
#[cfg(feature = "embedded-executor")]
pub use organs::{
    FlashWellReflection, OrganKind, OrganReach, OrganSurvey, RemoteOrgan, TrustlineReflection,
};
#[cfg(feature = "embedded-executor")]
pub use powerbox::{
    AppLauncher, CapabilityRequest, GrantableTarget, GrantedCap, LaunchedApp, Powerbox,
    PowerboxOutcome,
};
#[cfg(feature = "embedded-executor")]
pub use proofs::{AttachStatus, ProofBoard, ProofEntry, VerificationTier};
#[cfg(feature = "embedded-executor")]
pub use scene::{
    baked_admit_table, compositor_program, scene_admit, surface_factory, PresentVerdict,
    VerifiedScene, PRESENT_DIGEST_SLOT, SURFACE_FACTORY_VK,
};
#[cfg(feature = "embedded-executor")]
pub use shell::{Layout, Scene, SceneItem, Shell, ShellError};
#[cfg(feature = "embedded-executor")]
pub use simulate::{
    commit as simulate_commit, render_outcome, simulate, CellDelta, DraftAction, EffectKind,
    IntentDraft, SimOutcome,
};
#[cfg(feature = "embedded-executor")]
pub use snapshot_editor::{
    recipient_window_cap, Frustum, PareOutcome, ShareError, SharedArtifact, SnapshotEditor,
    Verification, ALL_LENSES,
};
#[cfg(feature = "embedded-executor")]
pub use surface::{Rect, Surface, SurfaceCapability, SurfaceId, SurfaceKind};
#[cfg(feature = "embedded-executor")]
pub use swarm::{
    BudgetMeter, NotifyEdge, Swarm, SwarmBudget, SwarmError, SwarmMember, SwarmMemberView,
    SwarmView,
};
#[cfg(feature = "embedded-executor")]
pub use swarm_budget::{
    StingrayBudgetView, StingrayDrawError, StingraySwarmBudget, SWARM_POOL_SILO,
};
#[cfg(feature = "embedded-executor")]
pub use terminal::{Command, CommandError, OutputLine, TerminalCell, TerminalView};
#[cfg(feature = "embedded-executor")]
pub use web_cells::{
    AffordanceRow, CellRow, SemiReinteractiveTransclusion, Transclusion, WebCellsBrowser,
};
#[cfg(feature = "embedded-executor")]
pub use world::{demo_genesis, demo_world, CommitOutcome, DemoSeed, World};

// THE REFLEXIVE DISTRIBUTED IMAGE (n > 1) re-exports.
#[cfg(feature = "embedded-executor")]
pub use branch_stitch::{
    Atom, BranchCap, BranchDebit, CrossPartyResolution, DocGraph, MainFrontier, SettleOutcome,
    Stitch, StitchCap, VirtualBranch,
};
#[cfg(feature = "embedded-executor")]
pub use distributed_timetravel::{
    run_collaborative_rewind, AlternateHistory, BranchEdit, Party, RewindRun, SharedTimeline, Tick,
};
#[cfg(feature = "embedded-executor")]
pub use netlayer_image::{ImageResponder, MirrorFrame, NetlayerImage, ResponderError};
#[cfg(feature = "embedded-executor")]
pub use remote_mirror::{
    FixtureImage, MirrorCap, MirrorDepth, MirrorRefusal, RemoteImage, RemoteMirror,
    RemoteReflection,
};
#[cfg(feature = "embedded-executor")]
pub use remote_mirror_live::{LiveMirror, LiveRefusal, LiveStep, LiveTail};
#[cfg(feature = "embedded-executor")]
pub use two_image_firmament::{run_two_image_firmament, TwoImageOutcome, TwoImageRefusal};

// THE GPUI PRESENTATION PLANE — the cockpit + login + dock element trees, lifted
// into the LIBRARY so they render on EITHER gpui platform:
//   * native (`gpui-ui`) — the `starbridge-v2` bin opens a window (`main.rs`).
//   * web (`gpui-web`) — the `starbridge-v2/web` cdylib boots `cockpit::Cockpit`
//     on `gpui_web` (wasm32 + WebGPU canvas), driving the SAME in-browser `World`.
// One renderer, one cockpit, two platforms (see docs/deos/WEB-DEOS.md). These
// modules build a pure gpui `Element` tree (`div().child(...)`), platform-agnostic;
// the gate is the union of the two gpui feature paths. (The native-only surface
// backends they reach — dev-surfaces' deos-zed/deos-terminal, web-shell's servo —
// are each independently feature-gated INSIDE these modules, OFF on the web path.)
// Also available under `process-pd` (without gpui): the shell's surface-migration
// LIVE TRANSPORT (`dock::migrate::PresentTransport`) is the firmament Endpoint
// re-home `Shell::migrate_surface` drives, and it must compile in the gpui-free
// `process-pd` test/headless path. `dock/mod.rs` independently gates its
// gpui-only submodules, so pulling `dock` in here pulls only its gpui-free members
// (`migrate`, gated on `embedded-executor`, which `process-pd` implies).
#[cfg(any(feature = "gpui-ui", feature = "gpui-web", feature = "process-pd"))]
pub mod dock;

// THE COCKPIT — the comprehensive visual master interface (the dock + the 28
// surfaces + the gpui-component widget set), rendering the live embedded `World`.
#[cfg(any(feature = "gpui-ui", feature = "gpui-web"))]
pub mod cockpit;
// THE TOUCH SHELL — deos on a phone (the graphideOS / mobile shape): the SAME live
// `World` + the SAME gpui renderer, re-bodied for a thumb (a bottom-bar mode switch,
// a tappable cell garden, long-press → a face sheet). DISTINCT from the desktop
// cockpit (it does not disturb it); reuses the gpui-free view model
// (`wonder::WonderRoom`, `reflect`). gpui-gated. See `docs/deos/MOBILE-DEOS.md` +
// `docs/deos/HIG.md`, and `--render-touch` in main.rs.
#[cfg(any(feature = "gpui-ui", feature = "gpui-web"))]
pub mod touch;
// THE SHOWCASE BAKE — a headless render of the full deos desktop with every dev
// surface mounted + seeded (the marketing money shot). Needs the dock surface
// wrappers (`dev-surfaces`) + gpui. See `--render-showcase` in main.rs.
#[cfg(all(feature = "gpui-ui", feature = "dev-surfaces"))]
pub mod showcase;
// THE GUEST / APP-FORWARD FRONT DOOR — the welcoming, low-verbosity desktop a
// newcomer lands on: the real app surfaces (browser · editor · terminal · chat) +
// a launcher-rolodex of acquired gadgets (read off the `AppRegistry`) + a wonder
// strip, with the dense inspector NOT shown by default but SUMMONABLE (⌘K). The
// "after you dismiss the inspector" view. Needs the dock surfaces (`dev-surfaces`)
// + the app registry (`app-registry`) + gpui. See `--render-guest` in main.rs.
#[cfg(all(
    feature = "gpui-ui",
    feature = "dev-surfaces",
    feature = "app-registry"
))]
pub mod guest;
// THE SELF-HOSTING LOOP, DEMONSTRATED — both REAL halves in one view: a firmament
// editor over the live World (a save = a real receipted turn) + a live-PTY
// terminal running real cargo/git INSIDE deos. The host drives + asserts both
// proofs; `--render-self-hosting` in main.rs bakes the PNG. Needs the firmament
// editor (`firmament` + `embedded-executor`) + the live PTY pane (`dev-surfaces`).
#[cfg(all(
    feature = "gpui-ui",
    feature = "dev-surfaces",
    feature = "firmament",
    feature = "embedded-executor"
))]
pub mod self_hosting;
// THE WHOLE ZED WORKSPACE AS A COCKPIT PANE — `src/zed_full_pane.rs` is the
// `CockpitSurface` that hosts the full `Entity<workspace::Workspace>` (the real
// editor/workspace/project + every panel over a FirmamentFs cell-ledger). It is
// gated on `zed-full-pane`, a feature deliberately LEFT UNDECLARED: pulling
// deos-zed-full collides at `links = "sqlite3"` (Zed's `sqlez` vs this cockpit's
// matrix-sdk-sqlite), so the dep can't be declared without breaking the default
// build. The module compiles + the gpui graph unifies the instant that one
// dep-graph seam is reconciled (see the Cargo.toml `deos-zed-full` comment). The
// full Workspace runs + bakes its PNG STANDALONE in `deos-zed-full` today.
#[cfg(feature = "zed-full-pane")]
pub mod zed_full_pane;
// THE ONE UNIFIED BOOT — a live `--node`-attached pane (the node's real
// cells/receipts/status over the wire) STANDING ALONGSIDE the firmament editor +
// the live-PTY terminal, in a SINGLE window/frame. `--render-unified-boot` bakes
// the PNG; the editor-save write-back seam is exercised + reported by the bake.
// Needs the live-node wire client (`live-node` + `embedded-executor`) plus the
// firmament editor + live PTY (`firmament` + `dev-surfaces`).
#[cfg(all(
    feature = "gpui-ui",
    feature = "dev-surfaces",
    feature = "firmament",
    feature = "embedded-executor",
    feature = "live-node"
))]
pub mod unified_boot;
// THE LOGIN CEREMONY surface — the boot front door; picking an identity runs the
// real session ceremony (`crate::session`) and swaps the window root to the cockpit.
// `gpui-ui` ONLY (native): the login surface drives the DURABLE-session-image path
// (`session::{open_session_world, session_base_dir}` + `LoginManager::logout_durable`),
// all `cfg(not(wasm32))` filesystem code. The web boot mounts `Cockpit` directly
// (the in-tab image is ephemeral), so it never needs the login front door.
// THE deos DESKTOP — a Windows-NT / Pharo-Smalltalk workbench over the live verified
// World: a desktop of cell-icons (draggable, spatially persisted), overlapping NT
// windows (inspectors), right-click context menus that fire REAL verified turns
// (the actuation), a menu bar, and drag-to-compose. Built NEW beside the cockpit;
// gpui-gated. See `src/deos_desktop.rs`.
#[cfg(all(feature = "gpui-ui", feature = "embedded-executor"))]
pub mod deos_desktop;
#[cfg(feature = "gpui-ui")]
pub mod login;
// The older NodeClient-bound rail components + the shared theme/pill/section_title
// helpers `cockpit`/`login` reuse. gpui-gated.
#[cfg(any(feature = "gpui-ui", feature = "gpui-web"))]
pub mod views;
