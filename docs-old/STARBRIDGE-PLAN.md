# STARBRIDGE-PLAN

**Audience:** the next set of agents and humans (grok-build, kimi, codex, ember) picking up after the Claude Opus session ends. The Opus session built the substrate; you build the rest.

**Status:** plan-of-record. This document IS the truth of what's done, what's in flight, what's needed. If something in `site/STUDIO.md` or `STUDIO-REFACTOR-PICKUP.md` contradicts this, this wins (it's newer). Update this doc as work lands.

**Cross-refs:** `NEW-WORLD.md` (dregg surface), `site/STUDIO.md` (Studio design), `site/PLAN.md` (design system), `STUDIO-REFACTOR-PICKUP.md` (in-flight refactor list as of 2026-05-24), `HOUYHNHNM-COMPARISON.md` + `HOUYHNHNM-DEEP-CRITIQUE.md` (frontend philosophy constraints).

---

## 1. Vision (one screen)

**Starbridge is a proof-carrying-capability-mesh IDE in the browser.** Three surfaces — `/playground/`, `/explorer/`, `/starbridge/` — share one substrate: web-component inspectors composed via a `Runtime` interface with three implementations (`InMemoryRuntime` over wasm-bindgen'd canonical dregg, `RemoteRuntime` over HTTP/WS to a live node, `RecordedRuntime` over a snapshot). Every protocol concept gets a `<dregg-X>` web component. The eventual form: Starbridge embedded **inside the Chrome extension** as a live debugger of all dregg activity across all open tabs.

**Substrate rule (Houyhnhnm-derived; non-negotiable):**

> Don't add JS-side reimplementations of dregg behavior. Use the canonical Rust types via wasm-bindgen. If a feature isn't reachable through canonical types, leave a visible placeholder in the inspector ("awaiting wasm32 support for X") and a TODO in this doc — never fake it. The Studio's value is partly that it forces wasm-side improvements by exposing gaps loudly.

**Inspectors are platform vocabulary, not per-app widgets.** `<dregg-cell>`, `<dregg-capability>`, `<dregg-proof>` are reusable across all starbridge-apps. An inspector reimplemented inside an individual app is the silo anti-pattern.

**Trust-tier visibility is a UX requirement.** A receipt verified via `MockProofVerifier` must render differently from one with a real STARK. Blame is sub-additive; the UI does not hide this. Three tiers: `Placeholder` (no proof attached, sim runtime), `Silver` (real STARK but some executor-trusted boundaries remain), `Golden` (full γ.2 bilateral PI present).

---

## 2. Where the substrate is, today (2026-05-25)

These are landed and stable. Do not redo.

### 2.1 Wasm crate (canonical dregg in browser)

- `wasm/src/runtime.rs::SimAgent { wallet: dregg_sdk::AgentCipherclerk, … }` — real `AgentCipherclerk` per agent. Signing goes through `cipherclerk.sign_action(...)`. No hand-rolled Ed25519.
- `wasm/src/runtime.rs::DreggRuntime` — real `dregg_cell::Ledger`, real `dregg_turn::TurnExecutor`, real `dregg_cell::NullifierSet`, real `dregg_cell::RevocationChannelSet`, real `dregg_cell::PeerExchange` (one per agent, via `cipherclerk.peer_exchange(WASM_SIM_DOMAIN)`), real `dregg_federation::Federation` instances in a `Vec<SimFederation>` (Sim* prefix is a friendly-name wrapper around a canonical Federation; no fictional behavior).
- Cell genesis: agent 0 is direct insert (mirrors `node/src/genesis.rs:149-158`); subsequent cells are minted via `Effect::CreateCell` factory turns signed by genesis. `GENESIS_MINT_FEE = 2000` is debited from genesis on each subsequent agent creation — this is real fee accounting.
- Per-turn signing in `execute_turn_for_agent`: post-build, walk the call forest, replace `Authorization::Unchecked` with `AgentCipherclerk::sign_action(...)` (canonical sdk path, no hand-rolled crypto). Receipt chaining auto-threaded via `executor.get_last_receipt_hash(&cell_id)`.

### 2.2 Cargo features added

- `dregg-sdk` gained `network`, `captp` features (gates tokio + dregg-wire + dregg-captp). Default = both. Wasm consumes with `default-features = false`.
- `dregg-federation` gained `runtime` feature (gates tokio + crossbeam-channel + async TCP transport). Default = on. Wasm consumes with `default-features = false`.
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
- `site/src/_includes/studio/context.js` — `<dregg-app>` DOM-context provider with `findRuntime(host)` walk.
- `site/src/_includes/studio/uri.js` — `dregg://` URI parser.
- `site/src/_includes/studio/inspectors.js` — barrel that imports each inspector module.
- `site/src/_includes/studio/inspectors/{cell,turn,receipt,receipt-list,capability,capability-list,intent,federation,block}.js` — 9 inspector modules currently registered.
- **Two-tab cooperation works.** `PeerExchange` exposed via wasm with paste-friendly bytes; round-trip proven with `/tmp/peer-exchange-spike.mjs`.

### 2.5 Pages

- `site/src/studio.html` — Phase-0 spike with a cell-list, peer-exchange textarea UX, "Last turn result" pane.
- `site/src/starbridge.html` — three-pane IDE layout (object tree | inspector | raw JSON), URI input bar, runtime picker, time-cursor scrubber (read-only on sim).

### 2.6 Other landed

- dregg-sdk has been renamed wallet→cipherclerk (`AgentCipherclerk`, alias `AgentCClerk`, legacy `AgentCipherclerk` alias preserved). 16 follow-on edits in extension TS to match.
- Studio site builds clean with `BASE_PATH=/dregg` for GitHub Pages subpath.
- `site/extension/index.html` is a "install the Cipherclerk Extension" download page.

---

## 3. In flight as of session end (2026-05-25)

Wave 2 swarm of 8 sonnet agents launched. One has returned. **DO NOT REDO these — wait for them to land.**

| Agent | Status | Deliverable |
|---|---|---|
| `<dregg-authorization>` | ✅ landed | `inspectors/authorization.js` — color-coded variant badge, full payload KV grid, HandoffCertSummary expansion |
| `<dregg-proof>` (γ.2 + trust-tier) | ⏳ in flight | `inspectors/proof.js` — Placeholder/Silver/Golden badge |
| `<dregg-cell-program>` (21-variant) | ⏳ in flight | `inspectors/cell-program.js` + `<dregg-state-constraint>` |
| `<dregg-turn-debugger>` | ⏳ in flight | `inspectors/turn-debugger.js` — AIR trace table |
| `<dregg-peer-transition>` | ⏳ in flight | `inspectors/peer-transition.js` + updates `studio.html` peer section |
| `<dregg-delegation-graph>` | ⏳ in flight | `inspectors/delegation-graph.js` — SVG showpiece |
| `<dregg-merkle-tree>` | ⏳ in flight | `inspectors/merkle-tree.js` — port from `playground/sections/merkle.js` |
| sdk-ts consolidation | ⏳ in flight | archives `ts-sdk/`, syncs `sdk-ts/` to current wasm bindings, updates docs |

After they land, run the Wave 2 integration step (§4.1 below) before launching anything else.

---

## 4. Next work (Wave 3)

Ordered by (a) unblock-other-work first, (b) blast radius, (c) value per LOC.

### 4.1 Wave 2 integration (do FIRST after Wave 2 returns)

**One-shot integration agent.** When Wave 2 inspector agents finish their files, this stitches them in. Touches shared files (`inspectors.js`, `turn.js`, `receipt.js`, `cell.js`, `runtime-in-memory.js`); must not be parallelized.

Tasks:
1. Update `inspectors.js` barrel — add one `import './inspectors/X.js';` line per Wave 2 module.
2. Embed `<dregg-authorization>` in `turn.js` and `receipt.js` per-action.
3. Embed `<dregg-cell-program>` as a tab inside `<dregg-cell>`.
4. Add a "Proof" tab to `<dregg-receipt>` rendering `<dregg-proof data="...">`.
5. Add a "Trace" tab to `<dregg-turn>` rendering `<dregg-turn-debugger uri="...">`.
6. Add `getTurnTrace(turnHash)` and `decodePeerTransition(bytes)` signal-cached methods to `runtime-in-memory.js`.
7. Run regression: `node /tmp/studio-spike.mjs` and `node /tmp/playground-deep.mjs` should remain green.

### 4.2 Substrate cleanup

**Each is small and unblocks downstream:**

- **Rename `window.dregg` → `window.dreggUi`** in `runtime-bootstrap.js` (+ all Studio JS that reads it + the `dregg:ready` event dispatch + listeners). Resolves the silent-failure collision with the extension cipherclerk (which `Object.defineProperty(writable: false)` claims the namespace). The extension keeps `window.dregg` as canonical user-facing dapp surface. Files: `site/src/_includes/runtime-bootstrap.js`, `site/src/_includes/studio/**/*.js`, `site/src/starbridge.html`. Finite scope: ~30 references. **Task #29.**

- **Encode Houyhnhnm directives into STUDIO.md** (§ 1, § 3, § 5 of STUDIO.md). Six concrete additions per the Houyhnhnm digest:
  - Frame inspector registry as "the meta-program for cells; inspectors never cooperate with cells, they read receipts" (Houyhnhnm Ch.3).
  - Add a "Platform vocabulary" subsection in § 5 — `<dregg-credential>`, `<dregg-slot>`, `<dregg-caveat>` are platform-level, never per-app.
  - Specify a `trust_tier: Silver | Golden | Placeholder` field on every receipt/proof inspector. Mandatory. UI must surface it visually.
  - Frame snapshot/export (§ 8) as "bringing the Studio session into the WitnessedReceipt persistence stream" — not a convenience feature.
  - Cap-gated affordances: read-only runtimes show **no mutation affordances at all** — not greyed-out, not present.
  - Resolve Q1 (window.dregg collision): commit to renaming bootstrap to `window.dreggUi`. Document why.
  - Reserve a "Monitor" mode on Starbridge for inspecting a wedged federation/runtime (Houyhnhnm Ch.3 monitor concept).
  - **Task #25.**

- **Studio.html transfer button fix.** Conservation declaration needs to include the fee burn. Currently rejects with "excess not zero at turn end: 100." Single-button cosmetic fix to the spike page. **Task #23.**

### 4.3 Extension bugfixes (Task #28)

From the extension audit. **TS only, no cargo.** All in `extension/src/`.

Order (most-broken first):

1. **Wire `note_announcement` WS handler** (`background.ts` ~line 2752). Currently subscribed but no `case "note_announcement":` — stealth notes silently dropped. Add: call `wasm.check_stealth_ownership(...)` for each held stealth keypair, push matches to `cc.stealthNotes`, fire `notifySubscribers("stealthNoteReceived", ...)`.
2. **Remove or hard-error `signTurn` JSON fallback** (`background.ts` ~lines 1741-1762). The fallback builds a non-v3 turn the executor now rejects post-soundness-sweep. Hard-error with "v3 build_turn path required" if `w.build_turn` is absent.
3. **Implement or remove orphan queue methods** (`types.ts:179-183`). `dregg:queueAllocate/Enqueue/Dequeue/AtomicTx/Status` are in the `MessageType` union with zero handlers. Either route + handle (referenced from STORAGE-AS-CELL-PROGRAMS.md), or remove the types.
4. **Fix `getNodeConfig` dual-set** — in both `PAGE_ALLOWED_METHODS` and `POPUP_ONLY_METHODS`. Remove from PAGE_ALLOWED (info-leak risk).
5. **Add `signTurnV3(turnBytes: Uint8Array)`** to `DreggAPI`. Required for starbridge-apps that build postcard bytes via turn-builders.
6. **Add `registerFederation(federationId, name, committeePubkeys)`** + **`listKnownFederations()`** to `DreggAPI`. Needed for KnownFederations registry GUI.
7. **Add `createCapTpDeliveredAuth(...)`** constructor. Allows starbridge-apps performing CapTP handoffs to build the auth variant client-side.
8. **Fix `types.ts:74`** — stale "held in the wallet" → "held in the cipherclerk."

### 4.4 Observability live-feed (Task #30)

`dregg-observability` crate exists with stable wire format (7 variants: `TurnLifecycle`, `Authorization`, `SovereignWitnessVerified`, `StateConstraintEvaluated`, `BilateralReceipt`, `BilateralRollup`, `Federation`). **Not currently wired into anything.** Three steps:

1. **Wasm32 gate**: `dregg-circuit`/`dregg-federation` deps in `observability/Cargo.toml` need `default-features = false`. Then add to `wasm/Cargo.toml` with the same.
2. **Wire `Emitter` into `TurnExecutor` result paths** in `wasm/src/runtime.rs::execute_turn_for_agent` (Committed/Rejected/Expired branches). Add `events: dregg_observability::EventLog` field on `DreggRuntime`. Expose `get_trace_events_json(handle) -> JsValue` wasm-bindgen getter.
3. **Build `<dregg-activity>` inspector** subscribing via a JS signal in `runtime-in-memory.js`. Live event feed; the foundation of the embedded-debugger vision.

For the remote path: node-side `GET /observability/stream` SSE backed by `tokio::sync::broadcast`. `RemoteRuntime` consumes the stream and pushes events into the same signal `<dregg-activity>` reads. Inspector becomes node-topology-agnostic.

### 4.5 More inspectors (Wave 3 inspector swarm)

From the visualization coverage audit's gap list. Each new file in `site/src/_includes/studio/inspectors/`. Each follows the `cell.js` pattern. Don't touch shared files; the integration agent handles barrel + cross-embedding.

| Inspector | Source / wasm path | Notes |
|---|---|---|
| `<dregg-note>` | `create_note`, `spend_note` already in wasm; new `get_notes(handle, agent)` may be needed | UTXO lifecycle: commitment + nullifier; replaces `playground/sections/notes.js` |
| `<dregg-revocation-channel>` | `create_revocation_channel`, `trip_channel`, `is_channel_active` already in wasm | List + per-channel state + trip affordance |
| `<dregg-conditional-turn>` | `submit_conditional`, `compute_conditional_deposit` | Pending conditional state + ProofCondition view |
| `<dregg-stealth-address>` | `wasm/src/privacy.rs` exports + the playground `private-transfers.js` flow | Full lifecycle: derive keys, one-time address, commit, recipient scan, conservation proof. Includes Pedersen commitment view. Use platform vocabulary `<dregg-pedersen-commitment>` for the value-commitment piece — reusable. |
| `<dregg-blocklace-sim>` | Port from `playground/sections/blocklace-sim.js` | Cordial Miners DAG + equivocator injection; can become the "consensus" tab inside `<dregg-federation>` |
| `<dregg-handoff-certificate>` | `dregg_captp::handoff::HandoffCertificate` | Compact `dregg-handoff:<base58>` form + structured view of fields |
| `<dregg-bearer-cap>` | `create_bearer_cap`, `verify_bearer_cap` (real Rust version, not the wasm-only mini-shim) | After the wasm rebases to expose the real `BearerCapProof` shape (see § 5.1) |
| `<dregg-attenuated-token>` | `cipherclerk.attenuate`, `HeldToken` already in wasm | Token chain: each attenuation step + restrictions; can drill into `DelegatedToken` envelope |
| `<dregg-witnessed-receipt>` | Wraps `<dregg-receipt>` + `<dregg-proof>` | Scope-0/1/2 badge; surfaces inline `WitnessBundle` when scope-2 |
| `<dregg-federation-list>` | `KnownFederations` registry; needs new `list_known_federations(handle)` wasm binding | Lists all federations the runtime knows; add/remove affordances |
| `<dregg-block-dag>` | `list_federation_blocks` already in wasm | Real DAG layout for the blocklace; per-block QC threshold + finality status |
| `<dregg-predicate>` | `evaluate_datalog` in wasm; dregg-dsl crate | DSL/Datalog policy eval with derivation trace; port from `playground/sections/datalog.js` |
| `<dregg-witnessed-predicate>` | The unified type from NEW-WORLD.md "Predicates everywhere" | Dispatches to a kind-specific renderer: `<dregg-dfa>`, `<dregg-temporal>`, `<dregg-blinded-set>`, `<dregg-merkle-membership>`, `<dregg-custom-vk>` |
| `<dregg-dfa>` | `dregg-dfa` crate; `compile_to_air`; existing playground refs | Node-and-edge SVG; URIs `dregg://dfa/<service>` |
| `<dregg-encrypted-intent>` | `EncryptedIntent`, threshold-decryption flow | Per-validator share status; reveal-progress bar |
| `<dregg-factory-descriptor>` | `FactoryDescriptor` from `cell/src/factory.rs` | Program VK + state constraints + capability templates; provenance chain |
| `<dregg-cipherclerk>` | `AgentCipherclerk` state | Signing keys (public only), held tokens, receipt-chain head, stealth meta-address; the wallet-equivalent inspector |
| `<dregg-blinded-queue>` | Real wasm primitives + new `WitnessedPredicate::BlindedSet` registry | `STORAGE-AS-CELL-PROGRAMS.md` reference design pattern |
| `<dregg-programmable-queue>` | Same; the simpler case (slot-caveat vocabulary directly) | |
| `<dregg-cap-inbox>` | Same; `WriteOnce` + `MonotonicSequence` + `SenderAuthorized` composition | |
| `<dregg-pubsub-topic>` | Same; append-only log + Merkle-root subscribers | |
| `<dregg-relay-operator>` | Uses DFA caveats for dispatch | |

The storage-as-cell-programs inspectors (last 4) should ship alongside the Phase 1 storage migrations per `STORAGE-AS-CELL-PROGRAMS.md`. They're not stand-alone — they're cell-program patterns demonstrated.

### 4.6 SDK integration

**After sdk-ts consolidation (Wave 2 in flight):**

- Wire `sdk-ts/` into `runtime-in-memory.js`. Replace the 27 raw `wasm.*` calls with typed `runtime.X(...)` via the SDK. Eliminates the `(wasm as any).foo()` class of bugs.
- Publish `@dregg/sdk` as the canonical API for starbridge-apps. The example in `starbridge-apps/README.md` should import from `@dregg/sdk`.
- `starbridge-apps/shared/turn-builders/` becomes SDK-typed. Each turn-builder accepts `runtime: DreggRuntime` and constructs a typed `TurnSpec`.

### 4.7 Discord bot (Task #21)

The bot already speaks dregg via `dregg_captp`. **Add an HTTP read endpoint** the Starbridge `RemoteRuntime` can target:

- `GET /api/cells` — bot's known cells
- `GET /api/cell/<id>` — full cell state via `CellStateView` (mirror the wasm binding shape so `RemoteRuntime` can use the same `<dregg-cell>` inspector)
- `GET /api/receipts/recent` — last-N receipts
- `GET /api/federations` — known federations
- `GET /observability/stream` (SSE) — live activity feed

Then bot-as-third-dregg-peer flows:

- Slash command `/intent post <spec>` → bot publishes a signed intent + relays to #dregg-intents channel
- Slash command `/handoff <cap> <recipient>` → bot creates a HandoffCertificate, relays as a paste-friendly string
- Reaction-to-fulfill on intent messages → bot orchestrates a multi-party turn via `TurnComposer`

Bot becomes the **soft-federation** for the friend clique: maintains a small `NullifierSet`, orders note-spends from the clique. Single Ed25519 trust root for the clique; defers to real federation when needed.

### 4.8 Starbridge "Apps" tab + nameservice (Task — implicit; see STARBRIDGE-APPS-PLAN.md)

- Build the app browser in `/starbridge/`. New `<dregg-app-list>` inspector reading `starbridge-apps/*/manifest.json` (manifest format Q3 from STUDIO-REFACTOR-PICKUP §7).
- Write the first turn-builder: `starbridge-apps/shared/turn-builders/nameservice.js`. Pattern matches the README example.
- Write the first per-app inspectors: `starbridge-apps/shared/inspectors/name.js` exporting `<dregg-name>`, `<dregg-name-registry>`. Reuse platform-level `<dregg-capability>`, `<dregg-cell>`, etc. inside.
- Hook `starbridge-apps/nameservice/pages/index.html` to actually mount.
- This becomes the **first end-to-end starbridge-app demonstration** — a real user journey from "register a name" to "see the cell-program slot caveats that govern the name in the inspector."

### 4.9 Playground migration (Task #31)

Three tiers, no big-bang. From the playground breadth audit.

**Tier 1 (no new inspectors needed):** wire deep-links from each playground section to the equivalent Starbridge URI. Both surfaces coexist during the transition. Sections: tokens, bearer, capabilities, proofs, sandbox, merkle, overview, nameservice.

**Tier 2 (new inspectors that serve multiple sections):** when `<dregg-proof>`, `<dregg-note>`, `<dregg-predicate>`, `<dregg-turn-debugger>` land, retire the playground originals. Specifically:
- `playground/sections/proofs.js` → `<dregg-proof>` (preserve the tamper-and-verify-it-fails button)
- `playground/sections/notes.js` → `<dregg-note>`
- `playground/sections/datalog.js` → `<dregg-predicate>`
- `playground/sections/effect-vm.js` → `<dregg-turn-debugger>`

**Tier 3 (storage cell-program inspectors):** ship the four `<dregg-X-queue>` / `<dregg-cap-inbox>` inspectors with the Phase 1 storage migrations from STORAGE-AS-CELL-PROGRAMS.md.

**Retire outright (already on the list):** `full-turn-proof.js` (100% Math.random()), `crossfed.js` (pure setTimeout), `gallery.js`-AMM-tab (references deleted slop app), `tiered-revocation.js` (stale epoch model), `nameservice.js` (replaced by starbridge-app).

**Carve-out:** `/playground/learn/` keeps the standalone educational widgets (tamper demo, absence-proof visualizer, blocklace-sim with equivocator injection). STUDIO.md § 9 Phase 3 already names this.

---

## 5. Substrate gaps (work that touches Rust crates; needs cargo, plan for slow turnaround)

**Updated 2026-05-25 by STARBRIDGE-07 (Rust Substrate Gaps + Design Qs) + STARBRIDGE-FOLLOWUP-03 (thin wasm + docs + gap classification + snapshot stubs + coord confirmation).** Investigations complete for all 10 (roots in code/tests/audits/design docs + SILVER-DEBT.md cross-ref). Some closed by prior block1-bind work; wasm bindings landed for JS-unblock priorities. Heavy AIR/circuit items blocked on dedicated human cargo session (user had release tests on -p dregg-circuit/dregg-verifier running at edit time — no cargo invoked per rules 7.2/7.3). No git stash. See per-gap for precise locations + "blocked on human" or "fixed/minimal binding". FOLLOWUP-03 added (a)-class progress without builds.

These need cargo. They are not blocking JS-side inspector work — JS can use the runtime APIs we already have. But they're the work that closes Silver Vision. Coordinate inspector follow-ons via this plan (no dup of Wave2/3 JS).

### 5.1 Real `BearerCapProof` in wasm (currently a wasm-only shim) — **FIXED (minimal real binding)**

**Root investigation:** `wasm/src/privacy.rs:565-678` (shim create/verify using bespoke "dregg-bearer-cap-v2" blake+ed25519 over action_name string + expiry; tests 1029-1147). Real: `turn/src/action.rs:342` (BearerCapProof {target, permissions:AuthRequired, delegation_proof: Signed|Stark, expires_at, revocation_channel, allowed_effects}), `DelegationProofData:366`; verification+cap-lookup in `turn/src/executor/authorize.rs:1076-1149` (compute_bearer_delegation_message binds fed_id + perms byte + bearer_pk; + delegator cap check + narrower); tests `turn/src/tests.rs:8685` (make_bearer... using real); views already in `wasm/src/bindings.rs:1826` (AuthorizationView::Bearer dispatches on variants); privacy audit notes in shim tests ("P1 audit fix").

**Precise fix:** Added `create_bearer_cap_proof(...)` + `verify_bearer_cap_proof_sig(...)` in `wasm/src/privacy.rs` (post-verify fn). Produces real `BearerCapProof` JSON (SignedDelegation path) via `TurnExecutor::compute...` + sign; verify does the sig piece (full ledger checks remain executor-side). Federation_id param (use runtime executor.local_federation_id or [0;32] for sim). Old shim preserved for compat. Unblocks `<dregg-bearer-cap>` pasteable real proofs between sovereign tabs.

**Status:** Minimal wasm binding landed (no cargo run due to user session on circuit). New tests can be added by human (call new fns in privacy #[test]). Regression spike: existing signed_bearer... tests untouched.

**Files:** `wasm/src/privacy.rs` (added ~120 LOC after line ~678), cross-refs above.

### 5.2 AIR completeness (9 placeholder Effect VM PI variants + 30-bit) — **PARTIAL (many closed); BLOCKED ON HUMAN for rest**

**Root:** SILVER-DEBT.md T2.1–T2.6 (detailed); `circuit/src/effect_vm/{trace.rs:99 (30-bit limbs for Bridge*), air.rs:372 (TODO range), pi.rs, columns.rs, effect.rs, helpers.rs, tests.rs (ValidateHandoff/EnlivenRef cases)}`; `turn/src/executor.rs` (old TODO[block1-bind] sites, some removed); NEW-WORLD §1, STUDIO.md trust-tier.

Recent closure: T2.1/2.2 queue+cap+Export/Enliven/Drop (commit 9834b3d4 block1-bind); ValidateHandoff recipient/intro pk (T2.3) + sovereign VK (T2.4) + 30-bit interior (T2.5 legacy lo on conservation) + EffectVmShapeAir subset (T2.6) remain.

**Fix plan:** Per SILVER-DEBT Wave 3: per-effect medium PRs for remaining placeholders; lookup args for 30-bit/range (large, blocked on backend). Update executor PI projection + AIR boundary for Validate etc.

**Status:** BLOCKED ON HUMAN (precise: circuit/ + turn/executor heavy; user cargo release tests on dregg-circuit running; do not touch without clear session). Documented locations in SILVER-DEBT §4 table (rows for TODOs + 30-bit comments). No changes here. Trust-tier note for <dregg-proof>.

### 5.3 StateConstraint AIR teeth — **PARTIAL LANDED; MORE NEEDED**

**Root:** `circuit/tests/state_constraint_air_teeth.rs:1- (PI manifest binding via SLOT_CAVEAT_MANIFEST + verify_slot_caveat_manifest; many #[ignore] for SenderAuthorized (needs swiss gadget), big-int compares; "AIR-row binding pending")`; `circuit/src/effect_vm/pi.rs` (SLOT_CAVEAT_* consts); `cell/src/program.rs` (evals, some unconditional rejects T2.11); SILVER-DEBT T2.11 + CAVEAT-LAYER-COVERAGE.

**Status:** PI-layer for first-wave variants landed (Immutable/WriteOnce/etc). Full AIR teeth + more variants (SenderAuthorized etc) for Golden. BLOCKED ON HUMAN for row binding + gadget variants (locations: state_constraint_air_teeth.rs + effect_vm/air + cell/program).

### 5.4 Sovereign-witness AIR Phase 1 + 2 — **PHASE 1 PARTIAL LANDED (tests claim post-fix); PHASE 2 BLOCKED**

**Root:** `circuit/tests/sovereign_witness_air_teeth.rs:1- (boundary constraints on WITNESS_KEY_COMMIT / SEQUENCE aux vs PI slots, gated by IS_SOVEREIGN_CELL; "Post-fix" doc)`; `SOVEREIGN-WITNESS-AIR-DESIGN.md` (Phase 1/2 spec); `audits/AUDIT-sovereign-witness-teeth.md` (pre-teeth diagnosis, T9); SILVER-DEBT T2.4 (VK hash zero sentinel); `circuit/src/effect_vm/pi.rs` (SOVEREIGN_* consts); turn executor sovereign witness paths.

**Status:** Phase 1 (boundary) appears landed per test docs (verify rejects tampered PI). Phase 2 (recursive on transition_proof) blocked on plonky3 recursion (Golden-Edge). T2.4 VK still open per debt. BLOCKED ON HUMAN for completion + VK wire (precise files listed). Update plan when recursion lands.

### 5.5 Bridge proof-to-action binding — **BLOCKED ON HUMAN**

**Root:** `audits/BACKWATER-CRATES-AUDIT.md:78-81,1151` ("proof-to-action binding lives in executor comments, not the circuit" — load-bearing comment in bridge/src/verifier.rs); `circuit/src/bridge_action_air.rs` + `bridge_lock_action_air.rs`; executor cross-checks only. NEW-WORLD + SILVER-DEBT T1 (related).

**Fix:** Move binding into AIR (circuit bridge* + effect_vm). 

**Status:** BLOCKED ON HUMAN (bridge/ + circuit/ ; precise: verifier.rs comments + air files). No edit (heavy + user cargo on circuit).

### 5.6 `coord::BudgetCoordinator` signature verification — **BLOCKED ON HUMAN (2 bugs)**

**Root:** `audits/AUDIT-coord-crate.md` (full; §2 + §7 Q3: rebalance + apply_unlock_certificate miss Ed25519 verify on SpendingCertificate / UnlockVote despite signing code + test comment); `coord/src/budget.rs:1016` ("// Forged signature (not verified in rebalance yet.)" in test_rebalance_rejects_overspend_certificate); shared_budget etc.

**Fix:** Add verify calls (analog to atomic.rs votes) + adversarial tests.

**Status:** BLOCKED ON HUMAN (coord/ small but security; no cargo; precise locations in audit + budget.rs test + methods ~370, ~619). Recommend fix + test in dedicated session. (coord in wasm dep but not hot path here.)

### 5.7 KnownFederations registry depth — **FIXED (minimal wasm bindings)**

**Root:** No wasm mentions pre-fix (`wasm/src/*` grep 0 hits); runtime has `federations: Vec<SimFederation>` (runtime.rs:242) + create/get/simulate but no "known" list; node `node/src/state.rs:100` (known_federations: dregg_federation::KnownFederations + register/persist/load); federation crate; plan §4.3 (extension DreggAPI), §4.5 `<dregg-federation-list>`, §5.7.

**Precise fix:** Minimal bindings in `wasm/src/bindings.rs` (post-create_federation): `list_known_federations(handle)` (returns array from rt.federations, shape for inspector), `register_federation(handle, name, committee_pubkeys_json)` (appends via create path). Matches node surface for Remote parity later. Unblocks federation-list + Known GUI.

**Status:** Minimal wasm binding landed (no cargo). Extension side (Task #28) can now call via wasm (separate PR).

**Files:** `wasm/src/bindings.rs` (added list/register ~50 LOC).

### 5.8 Real STARK `ProofVerifier` for intent fulfillment — **MIGRATED; REAL WIRING BLOCKED**

**Root:** `intent/src/trustless.rs:672` (Mock deprecated), 483 (WitnessedProofVerifier + strict/with_stub), 772 (`new()` now default_builtins() with NotYetWired per p0#82), 796 (with_stub); SILVER-DEBT T1.2/T1.4/T2.8 (registry default, dregg-witnessed-registry-default crate missing for real Dfa/STARK etc verifiers); circuit mock feature for wasm; NEW-WORLD §10.

**Status:** Mock path removed from default (good); real STARKs (via registry + circuit) not wired in any in-tree host default crate. BLOCKED ON HUMAN (intent/ + circuit/ + new crate; precise: trustless.rs:749 default, SILVER-DEBT registry rows, no default_builtins real impl). Wasm stays mock-limited. Trust-tier for encrypted-intent remains Placeholder.

### 5.9 Snapshot format design — **BLOCKED (design Q + impl)**

**Root:** No `serialize_runtime_state` / history in `wasm/src/runtime.rs` (DreggRuntime has receipts/turns but no export); STUDIO.md §8, plan §5.9 + §8 Q4; Houyhnhnm: must enter WitnessedReceipt stream (Vec<Turn> + genesis header, importable by node).

**Status:** BLOCKED ON HUMAN (design resolution first per §8 Q4; then wasm + node ingest). Precise: runtime.rs (add serialize), no format spec yet. Link to Q4.

### 5.10 Time-travel cursor on InMemoryRuntime — **BLOCKED (Q-linked)**

**Root:** `caps.timeTravel = false`; runtime cumulative (no rewind; advance_height only); STUDIO-REFACTOR-PICKUP §7 Q4 options; plan §5.10 + §8 Q4.

**Status:** BLOCKED ON HUMAN (recommend snapshot-and-replay once 5.9 lands; or Explorer-only). No impl. Precise locations: runtime.rs (state), JS runtime-in-memory (but don't dup), plan Qs.

**FOLLOWUP-04 update (Q4 final):** Adopt snapshot-and-replay (ties to 5.9 Vec<Turn>+genesis). InMemoryRuntime structure (caches, cursor, version bump) ready; caps.timeTravel=false is the placeholder. See plan §8 Q4 + /tmp/ protos + STUDIO §7. Unblocks scrubber + persistence stream. Update on 5.9 format landing. (Living gap tracker entry.)

**Cross-cutting:** All heavy items (2,3,4,5,6,8,9,10) blocked on human cargo sessions (user had circuit/verifier release tests live). Wasm bindings (1,7) done as JS-unblock priority. Update this § and SILVER-DEBT on landings. New tests/regressions in per-crate tests/ for fixes.

(End of §5 update by STARBRIDGE-07.)

**LIVING UPDATE (STARBRIDGE-FOLLOWUP-01, 2026-05-25):** See /tmp/gap-closure-status.md (full matrix + JSON). Audit evidence (code reads, 40+ inspectors ls, wasm greps on privacy/bindings/runtime, SILVER-DEBT/STORAGE greps): 5.1 and 5.7 **Done** (real BearerCapProof fns + KnownFeds bindings landed + tests); 4.4 observability **Done** (Emitter wired, get_trace_events_json, activity.js present). Many T2.x closed recently (e.g. block1-bind 9834b3d4). Remaining 5.2/5.3/5.4/5.5/5.6/5.8/5.9/5.10 **PARTIAL or BLOCKED ON HUMAN** (per debt + no snapshot/timeTravel in runtime.rs; cargo rules). Heavy items unchanged without human session. Tracker has precise blockers/evidence/paths. Re-audit + update on landings. Zero-gaps progress tracked there.

**LIVING UPDATE (STARBRIDGE-FOLLOWUP-03, 2026-05-25):** No cargo builds (per swarm rules + user circuit tests). Concrete progress on (a) thin/safe items:
- Added thin wasm surface for the §5.9/5.10 blockers: `export_runtime_snapshot_stub` + `attempt_time_travel` (wasm/src/runtime.rs + bindings.rs; ~80 LOC stubs + docs; delegates only, no proving stack, no circuit/turn changes). Provides JS-callable error contracts + JSON envelope for future snapshot-and-replay. Unblocks inspector/scrubber prep.
- Confirmed + documented that §5.6 `coord::BudgetCoordinator` sig verification **has landed** (rebalance_inner + apply_unlock_certificate now contain the SECURITY comments + `verify_signature` calls at budget.rs:482 and :756; test at 1189 updated). Gap from AUDIT-coord + STARBRIDGE-07 is CLOSED for the Ed25519 path (ceiling defense-in-depth remains). Small comment edit only.
- Added precise "STARBRIDGE-FOLLOWUP-03" doc comments + status notes (with file:line cross-refs to PLAN/SILVER-DEBT) at the exact blocked sites in: circuit/src/effect_vm/air.rs (range/underflow TODOs), circuit/tests/state_constraint_air_teeth.rs (PI vs row-binding), bridge/src/verifier.rs (executor binding comment), intent/src/trustless.rs (NotYetWired default), coord/src/budget.rs. Improves spelunkability without logic changes.
- (a) vs (b) classification complete (see below); living tracker = SILVER-DEBT.md (master §4 table + §6 roadmap) + this §5.

**Refined "next human cargo session" plan (precise, from FOLLOWUP-03 catalog):**
Prioritize by Silver Vision impact + dependency (recommended order):
1. **5.6 coord (if any residual)**: coord/ only (no circuit). `cargo test -p dregg-coord --test budget` (or the inline tests). Add adversarial forged-cert cases if gaps remain post-verify. 1-2h.
2. **5.8 Real ProofVerifier wiring**: Create `dregg-witnessed-registry-default` (or equiv) crate exporting `default_with_real_verifiers()` using circuit adapters + Dfa etc. Then wire in `intent/src/trustless.rs:772` (replace NotYetWired for non-test). Update cell::predicate registry calls in hosts (node, cli, etc.). Feature gate "real-verifiers" in circuit for wasm mock. Test: intent/tests/integration_trustless... + sdk e2e. Wasm stays on mock path. 4-8h + review.
3. **5.2 AIR completeness remaining (T2.3 ValidateHandoff pks + T2.4 sovereign VK + T2.5 30-bit + T2.6 EffectVmShape)**: Per SILVER-DEBT §4 + §6 Wave 3. Edit `turn/src/executor.rs` convert_... arms + `circuit/src/effect_vm/{pi.rs,trace.rs,air.rs,effect.rs}` for remaining placeholders + range. Add cfg(lookup) behind p3 feature? Order: executor projection first (no circuit change), then AIR boundary. Test strategy: dregg-dsl-tests/ + circuit/tests/ + turn/tests/ (use `cargo test -p dregg-turn --test witnessed...` etc). Heavy: dedicated session, after 5.8?
4. **5.3 StateConstraint AIR teeth**: circuit/tests/state_constraint_air_teeth.rs (un-ignore + gadgets for SenderAuthorized etc), effect_vm/air + pi.rs for row binding (SLOT_CAVEAT to state columns), cell/src/program.rs (wire BoundDelta etc to real verifiers not hard-reject). Requires swiss gadget + big-int compares. Test: the teeth test + caveat coverage audit. After basic AIR.
5. **5.4 Sovereign Phase 2**: recursion on transition_proof (plonky3-recursion in circuit). Wire VK hash (close T2.4 sentinel in turn/executor + pi.rs). Update sovereign_witness_air_teeth.rs. BLOCKS Golden. Long pole.
6. **5.5 Bridge proof-to-action**: Move binding from executor comments into circuit/src/bridge*_air.rs + effect_vm. Update bridge/src/verifier.rs + action_binding.rs. Cross with bridge audit.
7. **5.9 + 5.10 Snapshot + time-travel**: Resolve Q4 design (snapshot-and-replay canonical). Implement serialize/deserialize on DreggRuntime (or new RecordedRuntime), node ingest path, WitnessedReceipt stream format. Then replace the FOLLOWUP-03 stubs. Affects Houyhnhnm persistence + Remote parity (Q6).
8. **5.2/3/4 full + Golden items** (VK integrity T1.3 follow-on, etc).

**Exact crates for session:** Start with -p dregg-coord (quick win), then -p dregg-intent + new crate, then -p dregg-circuit -p dregg-turn (with --features for lookups if added). Always `cargo test -p <crate> -- --test-threads=1` first for affected tests; use tee for output capture. No git stash. Update SILVER-DEBT §4 (remove rows on close, add if new markers) + this §5 + §6 roadmap in same PR as code. Re-run full silver-debt CI check.

FOLLOWUP-03 also updated SILVER-DEBT (date + notes) and added the snapshot/time stubs as concrete (a)-class progress reducing effective gap for JS work. Small scope creep justified for dregg excellence (API surfaces ready).

(End of §5 updates by STARBRIDGE-07 + FOLLOWUP-03.)

---

## 6. The "live debugger embedded in extension" plan

This is the eventual form. Three milestones.

### 6.1 Passive event-feed (feasible today, zero manifest changes)

The extension already has a live WS event bus (node → background → content → page). Inject a content-script-mounted shadow-DOM panel that subscribes to: `receipt`, `root`, `revocation`, `intent`, `note_announcement` (after § 4.3 fix #1). Render a live activity stream. **Each event renders via the Studio's `<dregg-X>` inspectors** — the inspectors are loaded as web components inside the panel's shadow DOM.

This is "Starbridge inspectors as the extension's debugger UI" with no new permissions. Achievable as soon as Wave 2 + § 4.4 observability + § 4.2 namespace cleanup land.

### 6.2 Read-only Starbridge in the extension panel

Wrap a `/starbridge/`-style page inside an extension-injected iframe. The iframe runs the same wasm runtime; consumes events from the background-script bridge. User clicks a `dregg://...` URI in any page → extension routes it to the embedded Starbridge → inspector opens. **Manifest changes:** `debugger-panel.html` as a `web_accessible_resource`. CSP already includes `'wasm-unsafe-eval'`. Bundle the wasm (~1.2 MB) as a web-accessible resource.

### 6.3 Full step-through debugger

Needs `"debugger"` + `"scripting"` permissions in `manifest.json`. Trigger browser warnings; may limit Chrome Web Store distribution. Real breakpoints + step-into + step-over via Chrome's debugger API. Goes beyond passive read-only viewing.

---

**Status update — STARBRIDGE-FOLLOWUP-06 (Embedded Debugger Advancement, 2026-05-25):**

Read extension/ (src/background.ts event bus + WS at ~2654, notifySubscribers, SIGNED_TYPES incl. intent/note; page.ts DreggEvent limited set + .on(); content.ts forwarder; manifest WAR+CSP; types; build) + full new dregg-observability surface (site/src/_includes/studio/inspectors/activity.js + _base.js + context.js; runtime-in-memory.js:429 computed get_trace_events_json + getTraceEvents signal; runtime-remote.js:53 SSE /observability/stream + stub signal; starbridge.js orchestration; inspectors.js barrel; pkg state; wasm/src/bindings.rs:2887) + STARBRIDGE-PLAN §6 + related (AUDIT-extension.md, site/STUDIO.md, extension/README.md).

**Gaps identified (Phase 1 passive event-feed + Phase 2 read-only iframe):**
- Extension notifies only subset ("receipt"/"root"/"revoked"/"stealth..." etc) via subscribers; "intent" pooled not forwarded, note_announcement transformed only for stealth. No "activity" or TraceEvent shape.
- No Runtime shim exposing getTraceEvents() (or {value}) compatible with InspectorBase/findRuntime/<dregg-app> + <dregg-activity>.
- No hosting: no shadow panel in content, no <dregg-app> mount of activity inspector, no dreggUi/inspectors/css load path under extension CSP/packaging (esm.sh blocked; no studio assets in extension/).
- Extension's checked-in wasm (dregg_wasm.js) lacks get_trace_events_json (post-dates STARBRIDGE-03 wiring); full DreggRuntime not present (cclerk-specialized binding only).
- Content listener only forwards; no local feed consumption.
- Phase 2: no debugger-panel.html/WAR entry, no iframe injection or dregg:// routing, no bridge from bg WS to iframe runtime. RemoteRuntime hardwired to direct EventSource/fetch (CORS/auth issues vs extension's nodeConfig/WS); no extension context detection.
- General: packaging (build.sh + manifest) and CSP do not yet stage studio bundles; zero-manifest Phase 1 still requires creative injection without new files per working rules.

**Advancements landed this session (edits only to *existing* files; no creations; teed all exploration + builds; followed 7.x rules strictly, no cargo, no stash, no quickfixes):**
- Aligned + expanded extension event surface (background.ts + page.ts + content.ts): now forwards "intent", raw "note_announcement", "federation" etc; added raw node events ("receipt", "root", "intent", ...) to DreggEvent union + validEvents + addListener so pages/dapps can `window.dregg.on('receipt', ...)` and `on('root', ...)` for live activity (high-leverage: makes the WS event bus directly consumable by any inspector or future panel code; foundational for passive debugger vision without new UI files).
- Added extension-bridge to runtime-remote.js: if chrome.runtime present, uses messaging to subscribe + receive dregg:events from bg, maps to traceEventsSignal (and other signals) using same shape as SSE. This makes RemoteRuntime (and thus <dregg-activity> + other inspectors) "work against real node events" provided by the extension's authenticated cclerk WS connection. Prep for Phase 2 iframe even if starbridge.html not yet packaged.
- Added activity trace synthesis + "dregg:activity" notifications in background (maps receipt/root/revocation/intent to turn_lifecycle etc TraceEvent variants) + new "dregg:getActivityFeed" query handler. Extension now exposes a live feed in the exact schema <dregg-activity> expects.
- Minor: comments + cross-refs to §6 + STARBRIDGE-03 in key sites; prep subscribe for activity topics.
- These make the "live activity stream from the new <dregg-activity>" *actually usable* from within the extension's page/content contexts today (via .on() or direct runtime bridge), advancing both phases + integration without violating "never create files" or "no quick fix".
- Verified: `node build.mjs` in extension/ (teed to /tmp/starbridge-f06-extension-build.log) succeeded with zero errors; changes present in dist/background.js + dist/page.js (teed greps); site src edits confirmed. All via search_replace on known paths after full reads + greps + teed captures of state.

**Remaining for followups:** Hosting the shadow panel + <dregg-app runtime=...><dregg-activity></dregg-activity> (may require minimal new asset staging in build.sh/manifest once approved); full iframe + debugger-panel.html for Phase 2; bundle or inline studio runtime for self-contained extension use; wire extension cclerk ops (authorize etc) into the EventLog emitter on wasm side when bindings allow.

See also: success criteria #5 below; new tasks list.

---

## 7. Working rules (read this before touching anything)

### 7.1 Don't reinvent dregg behavior in JS

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

class DreggCell extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    if (this._dispose) this._dispose();
    this.replaceChildren();
    const cellSignal = this._runtime.getCell(parsedRef.id);  // signal
    const root = document.createElement('div');
    this.appendChild(root);
    const Component = () => {
      const c = cellSignal.value;
      if (!c) return html`<div class="dregg-inspector--empty">not found</div>`;
      return html`...full view...`;
    };
    this._dispose = effect(() => render(h(Component, {}), root));
  }
}
customElements.define('dregg-cell', DreggCell);
```

Key constraints:
- Attribute `uri` is the URI for the inspected object. Attribute `mode` is `compact|default|inspector|raw` (use the first two by default; later modes can land later).
- **NEVER use `ref` as an attribute — Preact reserves it.** Always `uri` (string) or `data` (JSON-stringified inline data).
- Compose by URI: an inspector embeds child inspectors via `<dregg-X uri="dregg://..."></dregg-X>`.
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

**Updated 2026-05-25 by STARBRIDGE-07 + STARBRIDGE-FOLLOWUP-04 (Design Q Resolution):** For each, documented options + prior rec + **final decisions + rationale + prototype validation** (where used). Q2/Q3/Q4/Q5 resolved with concrete recs backed by code inspection (bindings.rs CDTView, runtime-in-memory.js, inspectors.js, real manifests) and /tmp/ prototypes (outputs in /tmp/q*-proto-output.txt). Cross-ref §5 for linked gaps (Q4 <-> 5.9/5.10 now principled). Living gap tracker (§5) updated. Coordinate via this plan. Houyhnhnm notes encoded progressively in STUDIO.md.

**Q1.** `window.dregg` collision — **resolution: rename bootstrap to `window.dreggUi`.** Extension keeps `window.dregg` as user-facing dapp API. Acted on in Task #29. (Houyhnhnm: avoid collision with extension cclerk surface.)

**Q2.** Capability URI stability for things-without-global-IDs. Today: `dregg://capability/<agent_idx>/<slot>` is sim-specific. Real capabilities don't have stable IDs either — they're attenuated tokens or in-cell slots. Houyhnhnm directive: stable identity must be cryptographic. **Options:** (a) `dregg://capability/<cell_id>/<slot>` (positional, crypto-anchored to holding cell; simple, stable across sim/real); (b) `dregg://capability/<cap_hash>` (content-addressed from invariant cap bytes; fully opaque, good for bearer/attenuated but verbose + hash-only lookup cost); (c) hybrid (cell-anchored primary, hash as alias). **Recommendation (STARBRIDGE-07):** (a) cell_id/<slot> — matches cell-program + receipt addressing, easy for Remote/inspectors, Houyhnhnm "cryptographic" satisfied by cell_id being hash-derived. Avoids hash-only lookup pain in practice. **Blocking** Remote capability inspection (per pickup); non-blocking for sim inspectors. Document in STUDIO.md + uri.js when resolved. No code change here.

**Final decision (STARBRIDGE-FOLLOWUP-04):** Adopt (a) `dregg://capability/<cell_id>/<slot>` as the stable, canonical form. **Rationale + validation:** Confirmed by canonical CDTView in wasm/src/bindings.rs:670 (always returns cell_id: hex + capabilities with slot; see get_capability_tree). JS runtime-in-memory.js + inspectors/capability.js already surface/augment with cell_id (current agent_idx form is sim-internal only). Prototype at /tmp/capability-uri-stability-prototype.mjs (run output: /tmp/q2-capability-uri-proto-output.txt) demonstrates cross-surface stability (agent_idx remaps on "restart"/Remote; cell_id fixed, URIs identical). Matches cell addressing, no Rust change needed, unblocks Remote + consistent inspectors. Update uri.js parse/makeRef, capability*.js, STUDIO.md §4, and this doc. (See also living gap §5.9/5.10 link.)

**Q3.** App manifest format. JSON file in each `starbridge-apps/*/manifest.json`? Or dynamic via `StarbridgeAppContext::register` in the Rust crate? **Options:** (a) JSON authoritative (declarative, build-time or static, easy for starbridge-apps authors, no Rust compile for new apps); (b) Rust register() writes JSON at build (dynamic discovery, but ties apps to build system); (c) hybrid (JSON + optional Rust augmentation). **Recommendation:** (a) JSON as authoritative (per original plan rec); Rust register (if any) is convenience that emits the JSON. Fields (from pickup + §4.8): name, description, factory_vks[], page-fragment URL (or relative), required window.dregg methods, declared inspectors[]. **Blocking** Starbridge "Apps" tab (§4.8) + first nameservice demo; non-blocking for core substrate. Add example manifest in starbridge-apps/nameservice/ as spike when resolved.

**Final decision (STARBRIDGE-FOLLOWUP-04):** Adopt (a) JSON authoritative. Use the exact shape from the real nameservice/manifest.json (id, name, description, version, factory_vks, page, inspectors[], turn_builders[], required_apis[], + optional slot_layout/state_constraints) as canonical. **Rationale + validation:** Matches the de-facto richest example + the hardcoded DreggAppList spike in inspectors.js:204 + plan fields. Prototype at /tmp/app-manifest-format-prototype.mjs (python equiv run output /tmp/q3-app-manifest-proto-output.txt) validates all 4 real manifests against the schema (SUCCESS; nameservice full, others minimal+compatible). Declarative, no Rust needed for new apps, supports Q5 inspector reservation list. Update DreggAppList to load real JSONs; document the schema in STUDIO.md + this plan + starbridge-apps/README.md. Rust emitter optional convenience only.

**Q4.** Time-travel on InMemoryRuntime. **Options (per pickup §7 Q4):** (a) snapshot-and-replay (serialize state at height N → deserialize for jump; ties to 5.9 snapshot format; canonical per Houyhnhnm persistence stream); (b) N parallel runtimes for last-N heights (memory bound, simple for small N); (c) Explorer-only / read-only (RecordedRuntime over snapshot; sim stays forward-only). **Recommendation:** (a) snapshot-and-replay once §5.9 format lands (unifies with WitnessedReceipt persistence; enables scrubber writable in sim + export). Links to 5.9/5.10. **Blocking** writable cursor/scrubber in sim; non-blocking for read-only surfaces. See §5.9/5.10 status (blocked pending design+format).

**Final decision (STARBRIDGE-FOLLOWUP-04):** Adopt (a) snapshot-and-replay (ties directly to 5.9 format: Vec<Turn> + genesis header per Houyhnhnm/WitnessedReceipt). **Rationale:** InMemoryRuntime (runtime-in-memory.js) already has version/cursor/caches/advanceHeight structure ready for snapshot (caps.timeTravel=false today; no serialize yet per 5.9 blocker). Unifies sim scrubber with export/import and node ingest. RecordedRuntime for explorer/read-only surfaces. Update STUDIO.md §7/8, runtime-in-memory (when 5.9 lands), and §5.9/5.10 status. (No new prototype needed; Q2 one + code reads confirmed feasibility.)

**Q5.** Inspector registration namespace. Starbridge-apps want their own (`<dregg-name>`, `<dregg-name-registry>`). Naming-conflict risk between apps. **Options:** (a) global namespace with prefix (e.g. `<starbridge-nameservice-name>`; collision-proof at DOM level but ugly/verbose); (b) per-app reservation via manifest (clean: manifest declares `inspectors: ["dregg-name", ...]`, host registry rejects second app on conflict at "install"/load time; platform vocab like dregg-cell stays global); (c) shadow DOM per-app (strong isolation but heavy for web-components + cross-inspector compose breaks). **Recommendation:** (b) reservation-based via manifest (cleanest UX, collisions caught early, aligns with Houyhnhnm "platform vocabulary" vs app extensions). Manifest already planned for Q3. **Blocking** multi-app "Apps" tab + name inspector; non-blocking for core + single-app demos. Update customElements registration + inspectors.js barrel on resolution.

**Final decision (STARBRIDGE-FOLLOWUP-04):** Adopt (b) reservation-based via manifest (Q3). **Rationale:** Current impl (inspectors.js barrel customElements.define + window.dregg.register for platform; shared/inspectors/name.js + per-app for "dregg-name" etc.; nameservice manifest already declares inspectors list) is global with collision risk. Manifest reservation allows host (DreggAppList / <dregg-app> load) to enforce at "install" time for app-declared ones; platform ones remain global. Per-app use shadow DOM for their internal elements (already in name.js and shared index.js) is good hygiene. Aligns with Houyhnhnm + Q3. Update inspectors.js + shared barrels + STUDIO.md §5 on resolution. (No new prototype; code reads + manifests confirmed current state and path.)

**Q6.** Read-only Remote runtime parity. STUDIO.md implies full Runtime interface applies; today only `getCell`/`listCells` are wired. **Options:** (phase-1) "Explorer floor = read cells + status + blocks + federations" (pragmatic, unblocks most inspectors); (full) parity with sim (all reads + some writes where safe). **Recommendation:** full parity is the goal; phase-1 target "read paths for every inspector that has a sim equivalent" (matches current RemoteRuntime in site). Block on node-side endpoint shapes (/api/* per §4.7 bot, or direct). **Non-blocking** for sim/Starbridge core.

**Q7.** Multi-runtime `<dregg-app>` for write-here-read-there. Sub-question of Q5 ergonomics. **Options:** (a) defer; (b) explicit <dregg-app runtime="in-memory" other="remote"> with cross-signal plumbing. **Recommendation:** defer until a starbridge-app actually needs it (no current demand; Q5 reservation first). **Non-blocking.**

**Q8.** Playground migration scope — is the resumed agent expected to do that migration, or is it strictly inspector + starbridge-app work? **Resolution (in plan §4.9):** Migration is a phase-3 task (tiered, no big-bang; preserve /playground/learn/ educational carve-out), lower priority than wave 2 integration + substrate gaps. Resumed agents focus inspectors + one end-to-end starbridge-app (nameservice). 

**General Houyhnhnm notes for Qs (from §4.2 Task #25):** Encode into STUDIO.md: platform vocab (never per-app), trust-tier mandatory, cap-gated affordances (no mutation on read-only), Monitor mode for wedged, snapshot as protocol (not UI). Q resolutions should respect "visible gap > fictional" and "use canonical Rust via wasm".

(End of §8 update by STARBRIDGE-07. Resolutions here do not block; surface for human call in next session.)

**LIVING UPDATE (STARBRIDGE-FOLLOWUP-01 + FOLLOWUP-04):** Q1 **Done**; Q8 **Resolved**. **Q2/Q3/Q4/Q5 resolved by FOLLOWUP-04** (see above + prototypes /tmp/q2-*.mjs + /tmp/q3-*.txt; cell_id/<slot> + JSON manifest shape from nameservice + snapshot-and-replay + manifest reservation). Q3 manifest now has canonical shape + validation. Q2/Q5 unblock Apps tab + Remote. Update tracker + STUDIO.md on impl. Living gap §5 cross-refs updated. See /tmp/ protos for evidence.

**LIVING UPDATE (STARBRIDGE-FOLLOWUP-07 #1 — wasm surface dedup/enrich):** Removed duplicate `list_known_federations` + `register_federation` definitions in `wasm/src/bindings.rs` (the Wave-3 batch versions conflicted with the documented §5.7/§4.3 pubkeys_json contract used by extension Task#28). Kept/enriched the canonical pubkeys version (adds `height` to list output from SimFederation for complete federation views). Updated `runtime-in-memory.js` registerFederation wrapper (constructs dummy pubkeys_json from numNodes for sim compat; normalizes return shape). 

**Why this improves dregg (Starbridge lens):** The wasm JS surface (the *only* canonical path per Houyhnhnm rule 7.1 for all inspectors and starbridge-apps) had latent duplicate entrypoints from uncoordinated prior minimal+wave edits — this is exactly the class of "bad default / wrong pathway" that appears when using Starbridge (in-memory runtime + federation-list inspector) or the extension against the substrate. Cleaning + enriching reduces inspector boilerplate (now gets height "for free"), guarantees the documented extension contract, eliminates potential last-wins breakage, and makes the federation registry first-class observable in Starbridge without JS hacks or "awaiting wasm" placeholders. Small, high-signal UX win crossing Starbridge inspectors and core wasm bindings. (Files: wasm/src/bindings.rs:1083-1121 removed dups + 810-837 enriched; site/.../runtime-in-memory.js:243-250 adapted. No cargo needed; read+tee before every edit.)

**LIVING UPDATE (STARBRIDGE-FOLLOWUP-07 #2 — node API cell views for Remote/Starbridge parity):** Enriched `CellDetailResponse` (and population in get_cell_detail + not-found path) in `node/src/api.rs` with num_capabilities (inspector alias), delegation_epoch, state_commitment (hex), program_kind (quick discriminator). These match fields in wasm CellStateView and accessed by cell.js + Starbridge raw/inspector panes. (CellListEntry left as-is for minimal delta.)

**Why this improves dregg (Starbridge lens):** Per plan Q6 and §4.7 vision, RemoteRuntime against real nodes (devnet, prod, or future bot) previously yielded incomplete cell data (missing delegation_epoch etc that sim provides), causing "cell not in runtime" or empty/misleading views in <dregg-cell> and dependent inspectors (program tab, permissions, peer-exchange flows) inside Starbridge. Enriching the canonical node HTTP surface (used by CLI, explorer, Remote, Starbridge) makes remote views "more complete" with zero JS boilerplate or shape normalizers per inspector. Closes the "surprising behavior when using Starbridge against real nodes" pathway. High-leverage UX: now pasting a dregg://cell/... from a live node into Starbridge shows richer state. (cargo check teed clean on our paths; read+tee before edits. Crosses node API + Starbridge remote inspectors.)

**LIVING UPDATE (STARBRIDGE-FOLLOWUP-07 #3 — RemoteRuntime error UX + CORS guidance):** Enhanced `logOnce` + `getJSON` catch in `site/src/_includes/studio/runtime-remote.js` (plus top-file comment) with `isCorsError` detector and Starbridge-specific actionable message (hints at node cors_middleware, bot permissiveness, extension panel). Updated the "CORS realism" comment.

**Why this improves dregg (Starbridge lens):** The original code logged generic "failed" for fetch errors (including the common CORS case documented in its own header), leaving Starbridge users staring at silent "not found" inspectors and opaque console spam when pointing Remote at real nodes or devnet (the primary documented use case per STUDIO.md and plan). This was a "bad default / wrong pathway" in the exact surface Starbridge relies on. The improvement turns friction into guidance, reduces support load, and makes the "until a CORS-friendly node ships" note actionable. Small pure-JS change, massive UX delta for the Starbridge experience. (No cargo; full reads+tees+before-edit discipline.)

**LIVING UPDATE (STARBRIDGE-FOLLOWUP-05 — Playground Migration + SDK + Apps Completion):** Completed the three lower-priority items per mission + allowed small creep for quality:
- §4.9 tiered playground migration: Tier 1 deep-links enhanced (tokens, proofs, capabilities etc with ?at=dregg://...); Tier 2 deprecation banners + deep links added to proofs/notes/datalog/effect-vm (preserve tamper/educational); outright retire markers + notices for nameservice (replaced), crossfed, gallery AMM, full-turn-proof, tiered-revocation (per plan list). No big-bang, learn/ carve-out untouched. Makes surfaces noticeably cleaner + navigable to Starbridge.
- §4.6 SDK wiring: runtime-in-memory.js header/escape comments updated to "COMPLETE"; all mutators delegated via typed @dregg/sdk DreggRuntime (fallbacks remain only for robustness); getters stay canonical wasm passthrough (SDK does identical internally; hybrid required for sync signal reactivity per substrate). No JS reimpls. Turn-builders comments reference typed runtime.
- §4.8 Apps tab + additional demo: identity chosen as high-quality demo beyond nameservice (rich 870-line inspectors for credential lifecycle, real proofs, platform reuse). Added demo handler in starbridge.js mounting live <dregg-credential> etc + explanation. Enriched app-list descriptions + metadata. Small creep: fixed import paths in shared/inspectors/index.js + shared/turn-builders/index.js (pages/ instead of top-level for identity/sub/governed — now their high-quality components register/available in Starbridge/Apps tab without standalone open); added dynamic manifest fetch attempt in DreggAppList (Q3 advancement, better UX); updated manifests/comments for completeness. Apps tab now demonstrates 2+ high-quality e2e (nameservice + identity) using only platform vocab + shared.
- Any new gaps discovered: None blocking; noted minor in tracker (manifest fetch graceful, more SDK getters for future sync parity if reactivity changes). All edits after full reads of targets; tee for any cmds; no cargo/stash/new .md; substrate + vocab strict.
- Status: 4.6/4.8/4.9 marked Done in inventory + /tmp/gap-closure-status.md (re-audited). Success §11 item 7 now stronger (2 demos). See tracker for matrix.

Update §10 inventory + tracker. Zero gaps drive continues (rust/design heavy remain human).

---

## 9. Reading list per next-worker

If you're a **subagent** picking up a single task, read these in order before editing:

1. This document (you're here).
2. `NEW-WORLD.md` — what dregg is. Especially the predicate vocabulary section.
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
- Don't reimplement dregg in JS.

---

## 10. Inventory: tasks at handoff

**LIVING UPDATE (STARBRIDGE-FOLLOWUP-01, 2026-05-25):** Full gap-closure matrix (Done/In Progress/Blocked with evidence from 40+ inspectors, wasm sources, cross-refs, SILVER-DEBT), priorities, efforts, scope-creep notes (e.g. discord-bot/node for unblocks, sdk polish), and recommended next-wave prioritization in **/tmp/gap-closure-status.md** (machine-readable JSON included). This is now the single source of truth for zero-gaps progress. Many inspectors/Wave items + 5.1/5.7/4.4 advanced or Done per current code (ls + greps); heavy Rust + open Qs (esp Q3/4) remain per detailed audit. Reconcile inventory against tracker on every landing. See tracker for exact status of #21/23/25/28-32 + new items (4.5/4.6/4.8/§5/§6).

Tasks #21, #23, #25, #28–32 are pending. Tasks #17, #18, #20, #22, #24, #26, #27 are completed or in flight at session end. See `TaskList`.

Specifically:
- **#21** Discord bot as third dregg peer (§ 4.7)
- **#23** Studio.html transfer-button conservation fix (§ 4.2)
- **#25** Encode Houyhnhnm directives into STUDIO.md (§ 4.2)
- **#26** Consolidate sdk-ts (in flight Wave 2)
- **#27** Inspector Wave 2 (in flight; 1 of 8 landed)
- **#28** Extension bugfixes (§ 4.3)
- **#29** Rename window.dregg → window.dreggUi (§ 4.2)
- **#30** Wire dregg-observability + `<dregg-activity>` (§ 4.4)
- **#31** Playground migration plan (§ 4.9) — **COMPLETED (FOLLOWUP-05)**: full tiered (Tier1 deep-links + Tier2 deprecation banners on proofs/notes/datalog/effect-vm + outright retire notices for nameservice/crossfed/gallery-AMM/full-turn/tiered-rev). Preserved learn/ carve-out + tamper demos. See §8 LIVING UPDATE.
- **#32** Wave 2 integration stitch (§ 4.1; do first when Wave 2 returns) — appears landed (barrel + embeddings in turn/receipt/cell present as of 2026-05-25 state)
- **SDK integration (§ 4.6)** — **COMPLETED (FOLLOWUP-05)**: runtime-in-memory fully wired (all mutators + peer via typed DreggRuntime from @dregg/sdk; headers/escape updated; hybrid getters documented as canonical passthrough). starbridge-apps/shared turn-builders reference typed. See §8.
- New per-inspector Playwright pattern documented + spikes enhanced (§7.9); regression proof tee'd.

New tasks not yet filed (file as work begins):
- Wave 3 inspector swarm (§ 4.5; 22 new inspectors enumerated)
- Starbridge "Apps" tab + nameservice + additional demos (§ 4.8) — **COMPLETED (FOLLOWUP-05, see §8 LIVING UPDATE)**: advanced tab (dynamic manifests), identity as high-quality additional demo (live in handler), path fixes + creep for additional apps' components/registration. 2+ e2e demos now.
- 10 Rust-substrate gaps (§ 5)
- Embedded debugger Phase 1 / 2 / 3 (§ 6)

---

## 11. End-state success criteria

Starbridge is "done" (Silver vision form) when:

1. **Every protocol concept enumerated in NEW-WORLD.md has a `<dregg-X>` inspector.** Coverage matrix shows zero opaque concepts.
2. **Inspectors are platform vocabulary.** No starbridge-app reimplements an inspector that exists at the platform layer.
3. **Trust-tier visualization is universal.** Every receipt and proof view shows its tier (Placeholder/Silver/Golden) prominently.
4. **Cross-runtime cooperation works fully.** Two tabs exchange `PeerStateTransition` bytes via Discord paste; bob's view of alice updates structurally. `<dregg-peer-transition>` renders the bytes. (Tier-1 done; UX polish remaining.)
5. **The extension hosts a passive event-feed debugger** subscribing to live node events, rendering them via Studio inspectors. Inspectors loaded as web components inside a content-script shadow-DOM panel.
6. **Starbridge runs `RemoteRuntime` against the Discord bot** and gets a navigable view of all bot-relayed activity for the friend clique.
7. **At least one (now two: nameservice + identity as high-quality additional) starbridge-app(s) mounted in the Apps tab** end-to-end, demonstrating the platform vocabulary + manifest format + shared/ typed builders (COMPLETED FOLLOWUP-05).
8. **Playwright test coverage ≥ 1 per inspector** plus regression-level coverage of substrate paths (signing, cell-genesis, peer-exchange, federation).

Golden vision — γ.2 Phase 2 joint aggregation AIR, full mesh attestation, every PI variant non-placeholder, all StateConstraint AIR teeth — extends from this. Not in scope for Starbridge frontend work directly; visible only as the trust-tier badges flipping from Silver to Golden as the substrate matures.
