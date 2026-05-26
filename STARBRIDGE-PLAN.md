# STARBRIDGE-PLAN

**Audience:** the next set of agents and humans (grok-build, kimi, codex, ember) picking up after the Claude Opus session ends. The Opus session built the substrate; you build the rest.

**Status:** plan-of-record. This document IS the truth of what's done, what's in flight, what's needed. If something in `site/STUDIO.md` or `STUDIO-REFACTOR-PICKUP.md` contradicts this, this wins (it's newer). Update this doc as work lands.

**Cross-refs:** `NEW-WORLD.md` (pyana surface), `site/STUDIO.md` (Studio design), `site/PLAN.md` (design system), `STUDIO-REFACTOR-PICKUP.md` (in-flight refactor list as of 2026-05-24), `HOUYHNHNM-COMPARISON.md` + `HOUYHNHNM-DEEP-CRITIQUE.md` (frontend philosophy constraints).

---

## 1. Vision (one screen)

**Starbridge is a proof-carrying-capability-mesh IDE in the browser.** Three surfaces — `/playground/`, `/explorer/`, `/starbridge/` — share one substrate: web-component inspectors composed via a `Runtime` interface with three implementations (`InMemoryRuntime` over wasm-bindgen'd canonical pyana, `RemoteRuntime` over HTTP/WS to a live node, `RecordedRuntime` over a snapshot). Every protocol concept gets a `<pyana-X>` web component. The eventual form: Starbridge embedded **inside the Chrome extension** as a live debugger of all pyana activity across all open tabs.

**Substrate rule (Houyhnhnm-derived; non-negotiable):**

> Don't add JS-side reimplementations of pyana behavior. Use the canonical Rust types via wasm-bindgen. If a feature isn't reachable through canonical types, leave a visible placeholder in the inspector ("awaiting wasm32 support for X") and a TODO in this doc — never fake it. The Studio's value is partly that it forces wasm-side improvements by exposing gaps loudly.

**Inspectors are platform vocabulary, not per-app widgets.** `<pyana-cell>`, `<pyana-capability>`, `<pyana-proof>` are reusable across all starbridge-apps. An inspector reimplemented inside an individual app is the silo anti-pattern.

**Trust-tier visibility is a UX requirement.** A receipt verified via `MockProofVerifier` must render differently from one with a real STARK. Blame is sub-additive; the UI does not hide this. Three tiers: `Placeholder` (no proof attached, sim runtime), `Silver` (real STARK but some executor-trusted boundaries remain), `Golden` (full γ.2 bilateral PI present).

---

## 2. Where the substrate is, today (2026-05-25)

These are landed and stable. Do not redo.

### 2.1 Wasm crate (canonical pyana in browser)

- `wasm/src/runtime.rs::SimAgent { wallet: pyana_sdk::AgentCipherclerk, … }` — real `AgentCipherclerk` per agent. Signing goes through `cipherclerk.sign_action(...)`. No hand-rolled Ed25519.
- `wasm/src/runtime.rs::PyanaRuntime` — real `pyana_cell::Ledger`, real `pyana_turn::TurnExecutor`, real `pyana_cell::NullifierSet`, real `pyana_cell::RevocationChannelSet`, real `pyana_cell::PeerExchange` (one per agent, via `cipherclerk.peer_exchange(WASM_SIM_DOMAIN)`), real `pyana_federation::Federation` instances in a `Vec<SimFederation>` (Sim* prefix is a friendly-name wrapper around a canonical Federation; no fictional behavior).
- Cell genesis: agent 0 is direct insert (mirrors `node/src/genesis.rs:149-158`); subsequent cells are minted via `Effect::CreateCell` factory turns signed by genesis. `GENESIS_MINT_FEE = 2000` is debited from genesis on each subsequent agent creation — this is real fee accounting.
- Per-turn signing in `execute_turn_for_agent`: post-build, walk the call forest, replace `Authorization::Unchecked` with `AgentCipherclerk::sign_action(...)` (canonical sdk path, no hand-rolled crypto). Receipt chaining auto-threaded via `executor.get_last_receipt_hash(&cell_id)`.

### 2.2 Cargo features added

- `pyana-sdk` gained `network`, `captp` features (gates tokio + pyana-wire + pyana-captp). Default = both. Wasm consumes with `default-features = false`.
- `pyana-federation` gained `runtime` feature (gates tokio + crossbeam-channel + async TCP transport). Default = on. Wasm consumes with `default-features = false`.
- `wasm/Cargo.toml` has direct overrides: `clear_on_drop = { features = ["no_cc"] }` (bypasses C build path), `lockstitch = { features = ["portable"] }` (no AES intrinsics on wasm32).

### 2.3 Wasm bindings enriched (Refactors 3/6/7/8 + `get_turn_trace`)

These are the wasm exports the Studio reads. Read `wasm/src/bindings.rs` for shapes.

- `get_receipt_chain(handle)` — each receipt now carries `actions: Vec<ActionView>` (Refactor 3) and `proof_view: Option<ProofView>` (Refactor 7).
- `ActionView { target_cell, method, effects, authorization }`.
- `AuthorizationView` — tagged union `{ kind, …payload }` over all 7 variants (Signature, Proof, Breadstuff, Bearer, Unchecked, CapTpDelivered, Custom, OneOf). `HandoffCertSummary` nested for CapTpDelivered.
- `ProofView { kind, public_inputs, bilateral_pi?, is_agent_cell, is_sovereign_cell }`. `BilateralPiView { outgoing_transfer_root, incoming_transfer_root, outgoing_grant_root, incoming_grant_root, outgoing_introduce_root, incoming_introduce_root }`. Sim runtime returns `None` (scope-0, honest about no proof).
- `get_cell_state(handle, id)` — now includes `program: CellProgramView` (Refactor 6). One of `None` / `Predicate { constraints: Vec<StateConstraintView> }` / `Cases { … }` / `Circuit { circuit_hash }`. `StateConstraintView` is the 21-variant tagged union.
- `decode_peer_transition(bytes) -> { cell_id, old_commitment, new_commitment, effects_hash, timestamp, sequence, signature, has_transition_proof }` (Refactor 8).
- `get_turn_trace(handle, turn_hash)` — list of trace steps for step-by-step debugging.
- All existing fields are byte-equivalent to the prior shape; the new fields are additive.

### 2.4 JS substrate (Studio runtime)

- `site/src/_includes/studio/runtime-in-memory.js` — 440-line JS driver around the wasm runtime. Signal-cached getters for cell, receipt-chain, capabilities, intents, federations, blocks, peers. Mutations bump a coarse `version` signal.
- `site/src/_includes/studio/runtime-remote.js` — read-only HTTP/SSE viewport (only `getCell`/`listCells` wired; everything else throws NotPermitted).
- `site/src/_includes/studio/runtimes.js` — registry `{ 'in-memory': {…}, 'remote': {…} }`.
- `site/src/_includes/studio/context.js` — `<pyana-app>` DOM-context provider with `findRuntime(host)` walk.
- `site/src/_includes/studio/uri.js` — `pyana://` URI parser.
- `site/src/_includes/studio/inspectors.js` — barrel that imports each inspector module.
- `site/src/_includes/studio/inspectors/{cell,turn,receipt,receipt-list,capability,capability-list,intent,federation,block}.js` — 9 inspector modules currently registered.
- **Two-tab cooperation works.** `PeerExchange` exposed via wasm with paste-friendly bytes; round-trip proven with `/tmp/peer-exchange-spike.mjs`.

### 2.5 Pages

- `site/src/studio.html` — Phase-0 spike with a cell-list, peer-exchange textarea UX, "Last turn result" pane.
- `site/src/starbridge.html` — three-pane IDE layout (object tree | inspector | raw JSON), URI input bar, runtime picker, time-cursor scrubber (read-only on sim).

### 2.6 Other landed

- pyana-sdk has been renamed wallet→cipherclerk (`AgentCipherclerk`, alias `AgentCClerk`, legacy `AgentCipherclerk` alias preserved). 16 follow-on edits in extension TS to match.
- Studio site builds clean with `BASE_PATH=/pyana` for GitHub Pages subpath.
- `site/extension/index.html` is a "install the Cipherclerk Extension" download page.

---

## 3. In flight as of session end (2026-05-25)

Wave 2 swarm of 8 sonnet agents launched. One has returned. **DO NOT REDO these — wait for them to land.**

| Agent | Status | Deliverable |
|---|---|---|
| `<pyana-authorization>` | ✅ landed | `inspectors/authorization.js` — color-coded variant badge, full payload KV grid, HandoffCertSummary expansion |
| `<pyana-proof>` (γ.2 + trust-tier) | ⏳ in flight | `inspectors/proof.js` — Placeholder/Silver/Golden badge |
| `<pyana-cell-program>` (21-variant) | ⏳ in flight | `inspectors/cell-program.js` + `<pyana-state-constraint>` |
| `<pyana-turn-debugger>` | ⏳ in flight | `inspectors/turn-debugger.js` — AIR trace table |
| `<pyana-peer-transition>` | ⏳ in flight | `inspectors/peer-transition.js` + updates `studio.html` peer section |
| `<pyana-delegation-graph>` | ⏳ in flight | `inspectors/delegation-graph.js` — SVG showpiece |
| `<pyana-merkle-tree>` | ⏳ in flight | `inspectors/merkle-tree.js` — port from `playground/sections/merkle.js` |
| sdk-ts consolidation | ⏳ in flight | archives `ts-sdk/`, syncs `sdk-ts/` to current wasm bindings, updates docs |

After they land, run the Wave 2 integration step (§4.1 below) before launching anything else.

---

## 4. Next work (Wave 3)

Ordered by (a) unblock-other-work first, (b) blast radius, (c) value per LOC.

### 4.1 Wave 2 integration (do FIRST after Wave 2 returns)

**One-shot integration agent.** When Wave 2 inspector agents finish their files, this stitches them in. Touches shared files (`inspectors.js`, `turn.js`, `receipt.js`, `cell.js`, `runtime-in-memory.js`); must not be parallelized.

Tasks:
1. Update `inspectors.js` barrel — add one `import './inspectors/X.js';` line per Wave 2 module.
2. Embed `<pyana-authorization>` in `turn.js` and `receipt.js` per-action.
3. Embed `<pyana-cell-program>` as a tab inside `<pyana-cell>`.
4. Add a "Proof" tab to `<pyana-receipt>` rendering `<pyana-proof data="...">`.
5. Add a "Trace" tab to `<pyana-turn>` rendering `<pyana-turn-debugger uri="...">`.
6. Add `getTurnTrace(turnHash)` and `decodePeerTransition(bytes)` signal-cached methods to `runtime-in-memory.js`.
7. Run regression: `node /tmp/studio-spike.mjs` and `node /tmp/playground-deep.mjs` should remain green.

### 4.2 Substrate cleanup

**Each is small and unblocks downstream:**

- **Rename `window.pyana` → `window.pyanaUi`** in `runtime-bootstrap.js` (+ all Studio JS that reads it + the `pyana:ready` event dispatch + listeners). Resolves the silent-failure collision with the extension cipherclerk (which `Object.defineProperty(writable: false)` claims the namespace). The extension keeps `window.pyana` as canonical user-facing dapp surface. Files: `site/src/_includes/runtime-bootstrap.js`, `site/src/_includes/studio/**/*.js`, `site/src/starbridge.html`. Finite scope: ~30 references. **Task #29.**

- **Encode Houyhnhnm directives into STUDIO.md** (§ 1, § 3, § 5 of STUDIO.md). Six concrete additions per the Houyhnhnm digest:
  - Frame inspector registry as "the meta-program for cells; inspectors never cooperate with cells, they read receipts" (Houyhnhnm Ch.3).
  - Add a "Platform vocabulary" subsection in § 5 — `<pyana-credential>`, `<pyana-slot>`, `<pyana-caveat>` are platform-level, never per-app.
  - Specify a `trust_tier: Silver | Golden | Placeholder` field on every receipt/proof inspector. Mandatory. UI must surface it visually.
  - Frame snapshot/export (§ 8) as "bringing the Studio session into the WitnessedReceipt persistence stream" — not a convenience feature.
  - Cap-gated affordances: read-only runtimes show **no mutation affordances at all** — not greyed-out, not present.
  - Resolve Q1 (window.pyana collision): commit to renaming bootstrap to `window.pyanaUi`. Document why.
  - Reserve a "Monitor" mode on Starbridge for inspecting a wedged federation/runtime (Houyhnhnm Ch.3 monitor concept).
  - **Task #25.**

- **Studio.html transfer button fix.** Conservation declaration needs to include the fee burn. Currently rejects with "excess not zero at turn end: 100." Single-button cosmetic fix to the spike page. **Task #23.**

### 4.3 Extension bugfixes (Task #28)

From the extension audit. **TS only, no cargo.** All in `extension/src/`.

Order (most-broken first):

1. **Wire `note_announcement` WS handler** (`background.ts` ~line 2752). Currently subscribed but no `case "note_announcement":` — stealth notes silently dropped. Add: call `wasm.check_stealth_ownership(...)` for each held stealth keypair, push matches to `cc.stealthNotes`, fire `notifySubscribers("stealthNoteReceived", ...)`.
2. **Remove or hard-error `signTurn` JSON fallback** (`background.ts` ~lines 1741-1762). The fallback builds a non-v3 turn the executor now rejects post-soundness-sweep. Hard-error with "v3 build_turn path required" if `w.build_turn` is absent.
3. **Implement or remove orphan queue methods** (`types.ts:179-183`). `pyana:queueAllocate/Enqueue/Dequeue/AtomicTx/Status` are in the `MessageType` union with zero handlers. Either route + handle (referenced from STORAGE-AS-CELL-PROGRAMS.md), or remove the types.
4. **Fix `getNodeConfig` dual-set** — in both `PAGE_ALLOWED_METHODS` and `POPUP_ONLY_METHODS`. Remove from PAGE_ALLOWED (info-leak risk).
5. **Add `signTurnV3(turnBytes: Uint8Array)`** to `PyanaAPI`. Required for starbridge-apps that build postcard bytes via turn-builders.
6. **Add `registerFederation(federationId, name, committeePubkeys)`** + **`listKnownFederations()`** to `PyanaAPI`. Needed for KnownFederations registry GUI.
7. **Add `createCapTpDeliveredAuth(...)`** constructor. Allows starbridge-apps performing CapTP handoffs to build the auth variant client-side.
8. **Fix `types.ts:74`** — stale "held in the wallet" → "held in the cipherclerk."

### 4.4 Observability live-feed (Task #30)

`pyana-observability` crate exists with stable wire format (7 variants: `TurnLifecycle`, `Authorization`, `SovereignWitnessVerified`, `StateConstraintEvaluated`, `BilateralReceipt`, `BilateralRollup`, `Federation`). **Not currently wired into anything.** Three steps:

1. **Wasm32 gate**: `pyana-circuit`/`pyana-federation` deps in `observability/Cargo.toml` need `default-features = false`. Then add to `wasm/Cargo.toml` with the same.
2. **Wire `Emitter` into `TurnExecutor` result paths** in `wasm/src/runtime.rs::execute_turn_for_agent` (Committed/Rejected/Expired branches). Add `events: pyana_observability::EventLog` field on `PyanaRuntime`. Expose `get_trace_events_json(handle) -> JsValue` wasm-bindgen getter.
3. **Build `<pyana-activity>` inspector** subscribing via a JS signal in `runtime-in-memory.js`. Live event feed; the foundation of the embedded-debugger vision.

For the remote path: node-side `GET /observability/stream` SSE backed by `tokio::sync::broadcast`. `RemoteRuntime` consumes the stream and pushes events into the same signal `<pyana-activity>` reads. Inspector becomes node-topology-agnostic.

### 4.5 More inspectors (Wave 3 inspector swarm)

From the visualization coverage audit's gap list. Each new file in `site/src/_includes/studio/inspectors/`. Each follows the `cell.js` pattern. Don't touch shared files; the integration agent handles barrel + cross-embedding.

| Inspector | Source / wasm path | Notes |
|---|---|---|
| `<pyana-note>` | `create_note`, `spend_note` already in wasm; new `get_notes(handle, agent)` may be needed | UTXO lifecycle: commitment + nullifier; replaces `playground/sections/notes.js` |
| `<pyana-revocation-channel>` | `create_revocation_channel`, `trip_channel`, `is_channel_active` already in wasm | List + per-channel state + trip affordance |
| `<pyana-conditional-turn>` | `submit_conditional`, `compute_conditional_deposit` | Pending conditional state + ProofCondition view |
| `<pyana-stealth-address>` | `wasm/src/privacy.rs` exports + the playground `private-transfers.js` flow | Full lifecycle: derive keys, one-time address, commit, recipient scan, conservation proof. Includes Pedersen commitment view. Use platform vocabulary `<pyana-pedersen-commitment>` for the value-commitment piece — reusable. |
| `<pyana-blocklace-sim>` | Port from `playground/sections/blocklace-sim.js` | Cordial Miners DAG + equivocator injection; can become the "consensus" tab inside `<pyana-federation>` |
| `<pyana-handoff-certificate>` | `pyana_captp::handoff::HandoffCertificate` | Compact `pyana-handoff:<base58>` form + structured view of fields |
| `<pyana-bearer-cap>` | `create_bearer_cap`, `verify_bearer_cap` (real Rust version, not the wasm-only mini-shim) | After the wasm rebases to expose the real `BearerCapProof` shape (see § 5.1) |
| `<pyana-attenuated-token>` | `cipherclerk.attenuate`, `HeldToken` already in wasm | Token chain: each attenuation step + restrictions; can drill into `DelegatedToken` envelope |
| `<pyana-witnessed-receipt>` | Wraps `<pyana-receipt>` + `<pyana-proof>` | Scope-0/1/2 badge; surfaces inline `WitnessBundle` when scope-2 |
| `<pyana-federation-list>` | `KnownFederations` registry; needs new `list_known_federations(handle)` wasm binding | Lists all federations the runtime knows; add/remove affordances |
| `<pyana-block-dag>` | `list_federation_blocks` already in wasm | Real DAG layout for the blocklace; per-block QC threshold + finality status |
| `<pyana-predicate>` | `evaluate_datalog` in wasm; pyana-dsl crate | DSL/Datalog policy eval with derivation trace; port from `playground/sections/datalog.js` |
| `<pyana-witnessed-predicate>` | The unified type from NEW-WORLD.md "Predicates everywhere" | Dispatches to a kind-specific renderer: `<pyana-dfa>`, `<pyana-temporal>`, `<pyana-blinded-set>`, `<pyana-merkle-membership>`, `<pyana-custom-vk>` |
| `<pyana-dfa>` | `pyana-dfa` crate; `compile_to_air`; existing playground refs | Node-and-edge SVG; URIs `pyana://dfa/<service>` |
| `<pyana-encrypted-intent>` | `EncryptedIntent`, threshold-decryption flow | Per-validator share status; reveal-progress bar |
| `<pyana-factory-descriptor>` | `FactoryDescriptor` from `cell/src/factory.rs` | Program VK + state constraints + capability templates; provenance chain |
| `<pyana-cipherclerk>` | `AgentCipherclerk` state | Signing keys (public only), held tokens, receipt-chain head, stealth meta-address; the wallet-equivalent inspector |
| `<pyana-blinded-queue>` | Real wasm primitives + new `WitnessedPredicate::BlindedSet` registry | `STORAGE-AS-CELL-PROGRAMS.md` reference design pattern |
| `<pyana-programmable-queue>` | Same; the simpler case (slot-caveat vocabulary directly) | |
| `<pyana-cap-inbox>` | Same; `WriteOnce` + `MonotonicSequence` + `SenderAuthorized` composition | |
| `<pyana-pubsub-topic>` | Same; append-only log + Merkle-root subscribers | |
| `<pyana-relay-operator>` | Uses DFA caveats for dispatch | |

The storage-as-cell-programs inspectors (last 4) should ship alongside the Phase 1 storage migrations per `STORAGE-AS-CELL-PROGRAMS.md`. They're not stand-alone — they're cell-program patterns demonstrated.

### 4.6 SDK integration

**After sdk-ts consolidation (Wave 2 in flight):**

- Wire `sdk-ts/` into `runtime-in-memory.js`. Replace the 27 raw `wasm.*` calls with typed `runtime.X(...)` via the SDK. Eliminates the `(wasm as any).foo()` class of bugs.
- Publish `@pyana/sdk` as the canonical API for starbridge-apps. The example in `starbridge-apps/README.md` should import from `@pyana/sdk`.
- `starbridge-apps/shared/turn-builders/` becomes SDK-typed. Each turn-builder accepts `runtime: PyanaRuntime` and constructs a typed `TurnSpec`.

### 4.7 Discord bot (Task #21)

The bot already speaks pyana via `pyana_captp`. **Add an HTTP read endpoint** the Starbridge `RemoteRuntime` can target:

- `GET /api/cells` — bot's known cells
- `GET /api/cell/<id>` — full cell state via `CellStateView` (mirror the wasm binding shape so `RemoteRuntime` can use the same `<pyana-cell>` inspector)
- `GET /api/receipts/recent` — last-N receipts
- `GET /api/federations` — known federations
- `GET /observability/stream` (SSE) — live activity feed

Then bot-as-third-pyana-peer flows:

- Slash command `/intent post <spec>` → bot publishes a signed intent + relays to #pyana-intents channel
- Slash command `/handoff <cap> <recipient>` → bot creates a HandoffCertificate, relays as a paste-friendly string
- Reaction-to-fulfill on intent messages → bot orchestrates a multi-party turn via `TurnComposer`

Bot becomes the **soft-federation** for the friend clique: maintains a small `NullifierSet`, orders note-spends from the clique. Single Ed25519 trust root for the clique; defers to real federation when needed.

### 4.8 Starbridge "Apps" tab + nameservice (Task — implicit; see STARBRIDGE-APPS-PLAN.md)

- Build the app browser in `/starbridge/`. New `<pyana-app-list>` inspector reading `starbridge-apps/*/manifest.json` (manifest format Q3 from STUDIO-REFACTOR-PICKUP §7).
- Write the first turn-builder: `starbridge-apps/shared/turn-builders/nameservice.js`. Pattern matches the README example.
- Write the first per-app inspectors: `starbridge-apps/shared/inspectors/name.js` exporting `<pyana-name>`, `<pyana-name-registry>`. Reuse platform-level `<pyana-capability>`, `<pyana-cell>`, etc. inside.
- Hook `starbridge-apps/nameservice/pages/index.html` to actually mount.
- This becomes the **first end-to-end starbridge-app demonstration** — a real user journey from "register a name" to "see the cell-program slot caveats that govern the name in the inspector."

### 4.9 Playground migration (Task #31)

Three tiers, no big-bang. From the playground breadth audit.

**Tier 1 (no new inspectors needed):** wire deep-links from each playground section to the equivalent Starbridge URI. Both surfaces coexist during the transition. Sections: tokens, bearer, capabilities, proofs, sandbox, merkle, overview, nameservice.

**Tier 2 (new inspectors that serve multiple sections):** when `<pyana-proof>`, `<pyana-note>`, `<pyana-predicate>`, `<pyana-turn-debugger>` land, retire the playground originals. Specifically:
- `playground/sections/proofs.js` → `<pyana-proof>` (preserve the tamper-and-verify-it-fails button)
- `playground/sections/notes.js` → `<pyana-note>`
- `playground/sections/datalog.js` → `<pyana-predicate>`
- `playground/sections/effect-vm.js` → `<pyana-turn-debugger>`

**Tier 3 (storage cell-program inspectors):** ship the four `<pyana-X-queue>` / `<pyana-cap-inbox>` inspectors with the Phase 1 storage migrations from STORAGE-AS-CELL-PROGRAMS.md.

**Retire outright (already on the list):** `full-turn-proof.js` (100% Math.random()), `crossfed.js` (pure setTimeout), `gallery.js`-AMM-tab (references deleted slop app), `tiered-revocation.js` (stale epoch model), `nameservice.js` (replaced by starbridge-app).

**Carve-out:** `/playground/learn/` keeps the standalone educational widgets (tamper demo, absence-proof visualizer, blocklace-sim with equivocator injection). STUDIO.md § 9 Phase 3 already names this.

---

## 5. Substrate gaps (work that touches Rust crates; needs cargo, plan for slow turnaround)

These need cargo. They are not blocking JS-side inspector work — JS can use the runtime APIs we already have. But they're the work that closes Silver Vision.

### 5.1 Real `BearerCapProof` in wasm (currently a wasm-only shim)

The wasm `create_bearer_cap` in `wasm/src/privacy.rs` is a bespoke parallel mini-protocol — a single Ed25519 sig over a hash. The canonical `BearerCapProof { delegation_proof: SignedDelegation | StarkDelegation, … }` consumed by the executor is a different shape. Rebase the wasm binding to produce + verify real `BearerCapProof` envelopes. Then `<pyana-bearer-cap>` becomes a real cooperation primitive (paste-friendly between sovereign tabs).

### 5.2 AIR completeness (9 placeholder Effect VM PI variants)

`QueueAtomicTx`, `ValidateHandoff`, `QueueDequeue`, `EnlivenRef`, 5 others. Plus 30-bit value truncations on `BridgeMint`/`BridgeLock`/`CreateEscrow`. NEW-WORLD.md "What's not done" § 1. Trust-tier badge in `<pyana-proof>` flips from Silver → Golden when these close.

### 5.3 StateConstraint AIR teeth

Most variants are executor-side only; AIR boundary constraints are opt-in per variant. Start with `SenderAuthorized` (the swiss-table-membership gadget exists). NEW-WORLD.md "What's not done" § 2.

### 5.4 Sovereign-witness AIR Phase 1 + 2

Phase 1: AIR boundary constraints gated by `IS_SOVEREIGN_CELL`. Phase 2: depends on plonky3 recursion completion. T9 in the executor honesty audit. Closes a real soundness gap.

### 5.5 Bridge proof-to-action binding

Currently lives in executor comments, not in the circuit. Backwater audit finding. Trust-tier badge depends on this.

### 5.6 `coord::BudgetCoordinator` signature verification

Two real security bugs. Test comment: "Forged signature not verified in rebalance yet." Fix or remove the coord crate.

### 5.7 KnownFederations registry depth

`KnownFederations` registry is in place. Needed: a `list_known_federations(handle)` wasm binding so `<pyana-federation-list>` can render the registry. Plus a `register_federation(handle, fed_id, committee_pubkeys)` write path.

### 5.8 Real STARK `ProofVerifier` for intent fulfillment

Currently `MockProofVerifier`. NEW-WORLD.md "What's not done" § 10. Trust-tier on `<pyana-encrypted-intent>` is Placeholder until this lands.

### 5.9 Snapshot format design

Studio session state isn't persisted. STUDIO.md § 8 names this as the snapshot/export feature. Per Houyhnhnm: this is a **protocol** question, not a UI feature — the Studio session must enter the WitnessedReceipt persistence stream. Concretely: `serialize_runtime_state(handle) → Vec<u8>` + matching `deserialize`. Format should be `Vec<Turn>` + bootstrap header (agent identities, initial cell genesis), readable by future `pyana-node import-snapshot`.

### 5.10 Time-travel cursor on InMemoryRuntime

`caps.timeTravel = false` today. Wasm runtime is cumulative — no rewind primitive. Options per STUDIO-REFACTOR-PICKUP § 7 Q4: snapshot-and-replay, parallel runtimes for last-N heights, or declare it Explorer-only. **Recommend snapshot-and-replay** once snapshot format lands.

---

## 6. The "live debugger embedded in extension" plan

This is the eventual form. Three milestones.

### 6.1 Passive event-feed (feasible today, zero manifest changes)

The extension already has a live WS event bus (node → background → content → page). Inject a content-script-mounted shadow-DOM panel that subscribes to: `receipt`, `root`, `revocation`, `intent`, `note_announcement` (after § 4.3 fix #1). Render a live activity stream. **Each event renders via the Studio's `<pyana-X>` inspectors** — the inspectors are loaded as web components inside the panel's shadow DOM.

This is "Starbridge inspectors as the extension's debugger UI" with no new permissions. Achievable as soon as Wave 2 + § 4.4 observability + § 4.2 namespace cleanup land.

### 6.2 Read-only Starbridge in the extension panel

Wrap a `/starbridge/`-style page inside an extension-injected iframe. The iframe runs the same wasm runtime; consumes events from the background-script bridge. User clicks a `pyana://...` URI in any page → extension routes it to the embedded Starbridge → inspector opens. **Manifest changes:** `debugger-panel.html` as a `web_accessible_resource`. CSP already includes `'wasm-unsafe-eval'`. Bundle the wasm (~1.2 MB) as a web-accessible resource.

### 6.3 Full step-through debugger

Needs `"debugger"` + `"scripting"` permissions in `manifest.json`. Trigger browser warnings; may limit Chrome Web Store distribution. Real breakpoints + step-into + step-over via Chrome's debugger API. Goes beyond passive read-only viewing.

---

## 7. Working rules (read this before touching anything)

### 7.1 Don't reinvent pyana behavior in JS

If you find yourself writing crypto in JS — stop. Use the wasm binding. If the binding doesn't exist, the right answers are (a) add a wasm binding, or (b) leave a visible placeholder in the UI saying "awaiting wasm-side X." Never (c) fake it.

### 7.2 Cargo / wasm-pack contention

Multiple agents can't safely run cargo simultaneously. If you start a wasm-touching task and cargo fails with a lockfile or build-script conflict, sleep 60s and retry. Don't roll back. See `~/.claude/CLAUDE.md`.

### 7.3 Don't run cargo if the user has cargo running in another terminal

If you're told the user is in a flux state with cargo, **don't invoke cargo at all**. Edit files; verify by reading. Trust the user to rebuild on their side.

### 7.4 Inspector pattern (cribbing reference)

Every new inspector is a custom element. Pattern is in `site/src/_includes/studio/inspectors/cell.js`:

```js
class InspectorBase extends HTMLElement {
  static get observedAttributes() { return ['uri', 'mode', 'data']; }
  async connectedCallback() {
    const [api, runtime] = await Promise.all([ready(), findRuntime(this)]);
    this._runtime = runtime; this._api = api; this._render();
  }
  disconnectedCallback() { if (this._dispose) this._dispose(); }
  attributeChangedCallback() { if (this._api) this._render(); }
}

class PyanaCell extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    if (this._dispose) this._dispose();
    this.replaceChildren();
    const cellSignal = this._runtime.getCell(parsedRef.id);  // signal
    const root = document.createElement('div');
    this.appendChild(root);
    const Component = () => {
      const c = cellSignal.value;
      if (!c) return html`<div class="pyana-inspector--empty">not found</div>`;
      return html`...full view...`;
    };
    this._dispose = effect(() => render(h(Component, {}), root));
  }
}
customElements.define('pyana-cell', PyanaCell);
```

Key constraints:
- Attribute `uri` is the URI for the inspected object. Attribute `mode` is `compact|default|inspector|raw` (use the first two by default; later modes can land later).
- **NEVER use `ref` as an attribute — Preact reserves it.** Always `uri` (string) or `data` (JSON-stringified inline data).
- Compose by URI: an inspector embeds child inspectors via `<pyana-X uri="pyana://..."></pyana-X>`.
- Read state via runtime signals from `runtime-in-memory.js`. Don't call wasm directly (the runtime caches and bumps versions).
- New inspector files go in `site/src/_includes/studio/inspectors/<name>.js`. Add an `import` line to `inspectors.js` barrel (or wait for the integration agent to do it).

### 7.5 Don't `git stash`

`git stash` is not swarm-safe. Every parallel agent is in the same working directory. Stashing breaks them all.

### 7.6 Build the site

`cd site && node build.js`. Local dev server at `http://localhost:4818` (`npx serve dist` or equivalent).

### 7.7 Build wasm

Only when explicitly cleared to do so:

```
cd /Users/ember/dev/breadstuffs && wasm-pack build wasm --target web --out-dir ../site/pkg
```

Triggers a 2–3 minute build. Has been known to need `cargo clean -p lockstitch` once after the federation-agent's `clear_on_drop`/`lockstitch` workaround landed. If you hit a stale-build-product error, that's the fix.

### 7.8 Test in browser

The studio spike test is `/tmp/studio-spike.mjs`. Run after substrate changes:

```
node /tmp/studio-spike.mjs
```

Same agents Alice + Bob, three transfers. Compare turn hashes against last known-good. The deep test is `/tmp/playground-deep.mjs`. The peer-exchange test is `/tmp/peer-exchange-spike.mjs`.

### 7.9 Wave-2 inspector tests

Each new inspector should ship with a Playwright test in `/tmp/<inspector>-check.mjs` exercising at least: (a) compact-mode renders without crashing, (b) default-mode renders without crashing, (c) signal-driven re-render after a runtime mutation. Use `/Users/ember/dev/breadstuffs/site/node_modules/playwright/index.mjs` as the import root.

---

## 8. Open design questions (need a human call)

From STUDIO-REFACTOR-PICKUP § 7 plus Houyhnhnm-derived additions. **These block specific work; resolve before committing the dependent code.**

**Q1.** `window.pyana` collision — **resolution: rename bootstrap to `window.pyanaUi`.** Extension keeps `window.pyana` as user-facing dapp API. Acted on in Task #29.

**Q2.** Capability URI stability for things-without-global-IDs. Today: `pyana://capability/<agent_idx>/<slot>` is sim-specific. Real capabilities don't have stable IDs either — they're attenuated tokens or in-cell slots. Houyhnhnm directive: stable identity must be cryptographic. **Decision needed:** is the canonical URI `pyana://capability/<cell_id>/<slot>` (positional but cryptographically anchored to the holding cell) or `pyana://capability/<cap_hash>` (content-addressed, derived from the cap's invariant content)? **Blocking** Remote runtime growing capability inspection.

**Q3.** App manifest format. JSON file in each `starbridge-apps/*/manifest.json`? Or dynamic via `StarbridgeAppContext::register` in the Rust crate? **Recommend:** JSON manifest as authoritative; Rust `register()` writes the manifest at build time. Manifest fields: name, description, factory_vks, page-fragment URL, required `window.pyana` methods, declared inspector elements. **Blocking** the Starbridge "Apps" tab (§ 4.8).

**Q4.** Time-travel on InMemoryRuntime. **Recommend:** snapshot-and-replay once snapshot format (§ 5.9) lands.

**Q5.** Inspector registration namespace. Starbridge-apps want their own (`<pyana-name>`, `<pyana-name-registry>`). Naming-conflict risk between apps. **Decision needed:** namespace as `<starbridge-nameservice-name>` (collision-proof but ugly) OR rely on per-app reservation via the manifest (cleaner; collisions caught at app-install time). **Recommend** reservation-based; the manifest declares `inspectors: ["pyana-name", "pyana-name-registry"]` and the Starbridge host fails to register a second app that conflicts.

**Q6.** Read-only Remote runtime parity. STUDIO.md implies full Runtime interface applies; today only `getCell`/`listCells` are wired. **Decision needed:** phase-1 goal of full parity, or "Explorer = read cells + status" floor? **Recommend** full parity is the goal; phase-1 is "read paths for every inspector that has a sim equivalent." Block on node-side endpoint shapes.

**Q7.** Multi-runtime `<pyana-app>` for write-here-read-there. Sub-question of Q5 ergonomics. **Recommend** defer until a starbridge-app actually needs it.

**Q8.** Playground migration scope — is the resumed agent expected to do that migration, or is it strictly inspector + starbridge-app work? **Resolution:** § 4.9 plan above. Migration is a phase-3 task, lower priority than wave 2 integration.

---

## 9. Reading list per next-worker

If you're a **subagent** picking up a single task, read these in order before editing:

1. This document (you're here).
2. `NEW-WORLD.md` — what pyana is. Especially the predicate vocabulary section.
3. `site/STUDIO.md` — Studio design (some parts will be obsoleted by § 4.2's Houyhnhnm encoding; read with that in mind).
4. The specific module you're touching: `wasm/src/bindings.rs` for wasm shape, `site/src/_includes/studio/inspectors/cell.js` for inspector pattern, `site/src/_includes/studio/runtime-in-memory.js` for runtime API.

If you're **ember (the human)** picking up after the Claude refresh:

1. This document — scan § 3 to know what landed during sub-7's session and § 4.1 to know what to do first.
2. Audit results in `/tmp/` from the wave-1 swarm (they're in agent JSONL transcripts but the digests in earlier session text are the summary).
3. `STUDIO-REFACTOR-PICKUP.md` for the 13-refactor table — most of refactors 3/4/5/6/7/8 are now landed (covered in § 2.3 above).

If you're **grok / kimi / codex** running a single shot:

- Read this whole doc.
- Pick one § 4.x task.
- Use `site/src/_includes/studio/inspectors/cell.js` as your pattern reference.
- Don't run cargo unless the user explicitly clears it.
- Don't reimplement pyana in JS.

---

## 10. Inventory: tasks at handoff

Tasks #21, #23, #25, #28–32 are pending. Tasks #17, #18, #20, #22, #24, #26, #27 are completed or in flight at session end. See `TaskList`.

Specifically:
- **#21** Discord bot as third pyana peer (§ 4.7)
- **#23** Studio.html transfer-button conservation fix (§ 4.2)
- **#25** Encode Houyhnhnm directives into STUDIO.md (§ 4.2)
- **#26** Consolidate sdk-ts (in flight Wave 2)
- **#27** Inspector Wave 2 (in flight; 1 of 8 landed)
- **#28** Extension bugfixes (§ 4.3)
- **#29** Rename window.pyana → window.pyanaUi (§ 4.2)
- **#30** Wire pyana-observability + `<pyana-activity>` (§ 4.4)
- **#31** Playground migration plan (§ 4.9)
- **#32** Wave 2 integration stitch (§ 4.1; do first when Wave 2 returns)

New tasks not yet filed (file as work begins):
- Wave 3 inspector swarm (§ 4.5; 22 new inspectors enumerated)
- SDK integration into Studio (§ 4.6)
- Starbridge "Apps" tab + nameservice (§ 4.8)
- 10 Rust-substrate gaps (§ 5)
- Embedded debugger Phase 1 / 2 / 3 (§ 6)

---

## 11. End-state success criteria

Starbridge is "done" (Silver vision form) when:

1. **Every protocol concept enumerated in NEW-WORLD.md has a `<pyana-X>` inspector.** Coverage matrix shows zero opaque concepts.
2. **Inspectors are platform vocabulary.** No starbridge-app reimplements an inspector that exists at the platform layer.
3. **Trust-tier visualization is universal.** Every receipt and proof view shows its tier (Placeholder/Silver/Golden) prominently.
4. **Cross-runtime cooperation works fully.** Two tabs exchange `PeerStateTransition` bytes via Discord paste; bob's view of alice updates structurally. `<pyana-peer-transition>` renders the bytes. (Tier-1 done; UX polish remaining.)
5. **The extension hosts a passive event-feed debugger** subscribing to live node events, rendering them via Studio inspectors. Inspectors loaded as web components inside a content-script shadow-DOM panel.
6. **Starbridge runs `RemoteRuntime` against the Discord bot** and gets a navigable view of all bot-relayed activity for the friend clique.
7. **At least one starbridge-app (nameservice) is mounted in the Apps tab** end-to-end, demonstrating the platform vocabulary + manifest format.
8. **Playwright test coverage ≥ 1 per inspector** plus regression-level coverage of substrate paths (signing, cell-genesis, peer-exchange, federation).

Golden vision — γ.2 Phase 2 joint aggregation AIR, full mesh attestation, every PI variant non-placeholder, all StateConstraint AIR teeth — extends from this. Not in scope for Starbridge frontend work directly; visible only as the trust-tier badges flipping from Silver to Golden as the substrate matures.
