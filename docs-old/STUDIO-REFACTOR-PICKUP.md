# STUDIO-REFACTOR-PICKUP

**Audience:** the studio agent, returning after a pause.
**Author:** survey agent. Read-only on the code; produced from a sweep on
2026-05-24 of `site/`, `wasm/`, `extension/`, `starbridge-apps/`, and the
13 in-flight refactors named in the work brief.
**Status:** survey, not a TODO list to silently execute. Pick what's ready,
file what isn't, push back on §6/§7 where the framing is wrong.

The document has seven sections:

- §1 — what Studio is today (the actual surface)
- §2 — the extension-cclerk contract (`window.dregg`)
- §3 — the wasm runtime contract (`DreggRuntime`)
- §4 — refactor-by-refactor pickup table (the working surface)
- §5 — prioritized resume tasks
- §6 — things Studio wants but we haven't designed
- §7 — questions for the studio designer

---

## §1. What Studio is today

### 1.1 Surface map

Three surfaces share one substrate (per `site/STUDIO.md`):

| Surface     | URL              | Default runtime           | Authority      |
|-------------|------------------|---------------------------|----------------|
| Playground  | `/playground/`   | `InMemoryRuntime` (wasm)  | Owner          |
| Explorer    | `/explorer/`     | `RemoteRuntime` (live WS) | Read-only      |
| Starbridge  | `/starbridge/`   | User-selected             | User-selected  |

Plus a smaller "Studio Phase-0 spike" page at `/studio/` that demonstrates
a single `<dregg-cell>` + `<dregg-cell-list>` + the peer-exchange
Discord-paste UX (`site/src/studio.html`).

### 1.2 Source-of-truth files

**Substrate (Studio's actual code):**

- `site/STUDIO.md` — the design doc; § references throughout this pickup
  refer to it
- `site/PLAN.md` — the design-system spec it sits on top of
- `site/src/_includes/studio/`
  - `starbridge.js` — the `/starbridge/` page orchestrator (runtime picker,
    URI input, time cursor, object tree, raw JSON pane). 411 lines.
  - `starbridge.css`
  - `runtimes.js` — runtime-kind registry (`in-memory`, `remote`)
  - `runtime-in-memory.js` — the JS driver around the wasm `DreggRuntime`
    handle. 441 lines. Owns the signal cache and the JS-side intent
    ledger / block log (workarounds for missing wasm getters)
  - `runtime-remote.js` — read-only HTTP/SSE viewport onto a live node
  - `inspectors.js` — barrel; defines `<dregg-cell>` + `<dregg-cell-list>`
    inline, imports the rest
  - `inspectors/_base.js` — shared `InspectorBase` custom-element class
    + `renderParseError` + `shortHex`
  - `inspectors/turn.js`, `receipt.js`, `receipt-list.js`,
    `capability.js`, `capability-list.js`, `intent.js`,
    `federation.js`, `block.js`
  - `context.js` — `<dregg-app>` custom element + `findRuntime(host)`
  - `uri.js` — `dregg://` URI parser

**Page chrome:**

- `site/src/starbridge.html` — Starbridge page (topbar + 3-pane layout)
- `site/src/studio.html` — Phase-0 spike page (controls + cell list + peer
  exchange textareas)
- `site/src/_includes/runtime-bootstrap.js` — loads Preact + signals +
  htm, exposes them via `window.dregg` (NOT the cclerk — colliding name;
  see §2 note)

**Wasm shim (Studio depends on it):**

- `wasm/src/runtime.rs` — `DreggRuntime` (877 lines)
- `wasm/src/bindings.rs` — `#[wasm_bindgen]` JS surface (1900+ lines)
- `wasm/src/lib.rs` — non-runtime crypto helpers (mint_token,
  stark proof helpers, etc.)
- `wasm/src/privacy.rs` — stealth-address helpers

**Adjacent surfaces (not Studio, but Studio reads/forwards into them):**

- `site/explorer/` — own JS app; uses its own `api.js` against a live
  node. Studio's `RemoteRuntime` intentionally does *not* import
  `explorer/api.js` (different base-URL config).
- `site/playground/` — 29 atomized demo sections. Pre-Studio; STUDIO.md
  Phase 3 deprecates them as inspectors absorb their content.

**Starbridge-apps (separate stack consuming Studio):**

- `starbridge-apps/README.md` — defines the contract
- `starbridge-apps/nameservice/` — first concrete app (Rust crate +
  `pages/index.html` + intended JS inspectors)
- `starbridge-apps/shared/inspectors/index.js` — stub
- `starbridge-apps/shared/turn-builders/index.js` — stub
- `starbridge-apps/shared/factories/README.md` — stub

### 1.3 What Studio does today (read paths verified)

- Loads wasm, creates a `DreggRuntime` handle, attaches it to a
  `<dregg-app>` runtime context provider.
- Parses `dregg://<kind>/<id>[/<sub>...]` URIs (no `?at=`/`@height`
  fragments yet beyond URL state).
- Reads via wasm getters: `get_cell_state`, `get_all_cells`,
  `get_receipt_chain`, `get_capability_tree`, `get_federation_state`,
  `get_federation_block`, `list_federation_blocks`, `get_peer_view`,
  `list_peers`, `get_peer_pubkey`, `get_cell_state_commitment`.
- Mutates via wasm setters: `create_agent`, `create_cell`, `execute_turn`,
  `agent_mint_token`, `advance_height`, `create_federation`,
  `create_intent`, `propose_block`, `simulate_consensus_round`,
  `register_peer`, `create_peer_transition`, `verify_peer_transition`.
- Renders all of the above through 9 custom elements:
  `<dregg-app>`, `<dregg-cell>`, `<dregg-cell-list>`, `<dregg-turn>`,
  `<dregg-receipt>`, `<dregg-receipt-list>`, `<dregg-capability>`,
  `<dregg-capability-list>`, `<dregg-intent>`, `<dregg-federation>`,
  `<dregg-block>`.

### 1.4 What Studio does NOT do today (gaps documented in code)

- `listTurns`, `listReceipts` (cross-runtime), `listIntents`,
  `listCapabilities` placeholders are wired up in `starbridge.html` but
  not yet bound to runtime signals — the right column shows
  "listX not yet exposed on runtime" `<details>` blocks.
- `RemoteRuntime` exposes only `getCell` / `listCells`; every other
  getter throws `NotPermitted`.
- `RecordedRuntime` (snapshot replay) — not implemented. Snapshot button
  alerts "Snapshot export will be wired up once the wasm side is shipped."
- No turn-builder inspector. No debugger inspector. No time-travel
  cursor on the sim runtime (cursor advances on `advance_height` but is
  read-only; `caps.timeTravel = false`).
- No `<dregg-proof>` inspector.
- No discovery/peer pickers, no federation-registry UX, no slot-caveat
  editor.

---

## §2. The extension cclerk contract

### 2.1 Where it lives

- `extension/src/page.ts` — the page-injected script that exposes
  `window.dregg` (frozen). 326 lines. Communicates with `content.ts`
  via nonce-keyed `CustomEvent`s on `window`.
- `extension/src/types.ts` — shared TS definitions for the
  page↔content↔background message protocol
- `extension/src/background.ts`, `content.ts`, `api.ts` — the rest of
  the extension; Studio doesn't talk to them directly

**Naming collision warning:** `window.dregg` is overloaded.
- The *extension* defines it as the **cclerk** (the `DreggAPI`
  interface in `page.ts`, frozen).
- The Studio's `site/src/_includes/runtime-bootstrap.js` ALSO sets
  `window.dregg` to a Preact-and-signals namespace (`h`, `html`,
  `signal`, `effect`, `render`, `toast`, etc.).

Both contexts assume they own the global. The page that hosts the
Studio gets the Preact one; the page that hosts a *starbridge-app
loaded with the extension installed* will have BOTH trying to claim it
(extension page-injection happens before page scripts run; the
extension wins via `Object.defineProperty` with `writable: false`,
which means the bootstrap's later assignment throws in strict mode).
This is a **landmine for the studio agent** the moment a real
starbridge-app needs to call `window.dregg.signTurn` AND mount a
`<dregg-app>`. **See §6.1 for the fix-it-once proposal.**

### 2.2 The `DreggAPI` surface (43 methods)

Grouped by concern. All return Promises.

**Authorization & connection:**
- `authorize(request)` → `AuthorizeResult`
- `isConnected()` → `boolean`
- `canAuthorize(request)` → `boolean`
- `provision(tokenBytes)` — accept a capability into the cclerk

**Intents:**
- `postIntent(matchSpec, options?)`
- `postEncryptedIntent(matchSpec, options?)`
- `getStealthAddress()`

**Privacy:**
- `privateTransfer(amount, assetType, recipientStealthMeta)`

**Bearer caps:**
- `createBearerCap(targetCellHex, action, expiry?)`
- `verifyBearerCap(...)`

**Factories:**
- `createFromFactory(factoryVkHex, ownerPubkeyHex, initialBalance)`
- `verifyProvenance(cellVkHex, knownFactoryVks)`

**Sovereign cells / peer exchange:**
- `makeCellSovereign(cellIdHex)`
- `peerExchange(receiverCellHex, amount)`

**Proof composition:**
- `composeProofs(proofs, mode)`

**Turn submission:**
- `signTurn(turnSpec)` — the canonical write path apps use
- `queryBalance()`

**Node config:**
- `getNodeConfig()` / `setNodeConfig(config)`

**CapTP:**
- `shareCapability(cellId)`
- `acceptCapability(uri)`
- `createHandoff(cellId, recipientPk)`

**Directory / nameservice substrate:**
- `mountService(path, opts)`
- `discoverServices(tags)`
- `resolvePath(path)`

**Storage:**
- `storageWrite(data)` / `storageRead(hash)` / `storageQuota()`

**Federation:**
- `federationStatus()` — returns `{ mode, height, peerCount, merkleRoot }`
- `proposeRoutes(routes)`
- `voteOnProposal(proposalId, approve)`

**Events:**
- `on(event, cb)` / `off(event, cb)` — events: `ready`,
  `authorization`, `revoked`, `stealthNoteReceived`,
  `privateTransfer`, `intentFulfilled`, `privacyModeChanged`

### 2.3 What Studio uses today from `window.dregg` (the cclerk)

**Approximately nothing.** The Studio's `runtime-in-memory.js` drives
the wasm `DreggRuntime` directly — it does not call cclerk methods.
The `runtime-remote.js` similarly speaks raw HTTP to the node.

The only place the cclerk contract enters Studio code today is the
*expectation* in `starbridge-apps/shared/turn-builders/index.js`:
those builders WILL call `window.dregg.signTurn(...)` once written.
None are written yet.

This is the cleanest pickup point: **a starbridge-app's mutating UX
goes through the extension cclerk; its viewing UX goes through the
Studio inspectors.** The two surfaces have not yet met in code.

### 2.4 What the cclerk does NOT yet expose

Anticipated by the refactor list:
- No `registerFederation(federation_id, name, committee_pubkeys, ...)` — needed by Lane M; CLI is being built by Lane N.
- No `listKnownFederations()`.
- No `signTurn` overload that takes a pre-built `Turn` (current shape is `TurnSpec` — `{ action, resource?, amount?, recipient?, metadata? }`, very thin).
- No `signTurnV3(turnBytes)` — required to absorb the v3 signed-message change (soundness sweep).
- No `Authorization::CapTpDelivered` constructor on the cclerk side.
- No slot-caveat picker / disclosure shim.

---

## §3. The wasm / DreggRuntime contract

### 3.1 Wiring (real, not simulated)

Per `site/STUDIO.md` § 3 and verified in `wasm/src/runtime.rs`:

- **Ledger:** real `dregg_cell::Ledger`.
- **Executor:** real `dregg_turn::TurnExecutor` with default
  `ComputronCosts`. Timestamp + block height managed by the runtime
  (`set_timestamp`, `set_block_height`).
- **AgentCipherclerk:** real `dregg_sdk::AgentCipherclerk`. Constructed from a
  deterministic blake3-derived 32-byte seed (`dregg-wasm-agent-key`
  derive-key + name + idx). Signing goes through
  `cclerk.sign_action(...)`. No JS-side cryptography.
- **PeerExchange:** real `dregg_cell::PeerExchange`, one per agent,
  constructed via `cclerk.peer_exchange(WASM_SIM_DOMAIN)`. Uses
  `create_transition_at(...)` to thread the runtime's logical clock
  into the signed message (the default `create_transition` calls
  `SystemTime::now()` which panics on wasm32-unknown-unknown).
- **NullifierSet:** real `dregg_cell::NullifierSet`.
- **RevocationChannelSet:** real `dregg_cell::RevocationChannelSet`.
- **Federation:** **real `dregg_federation::Federation`** — the
  previous `SimFederation` was deleted. The `dregg-federation` crate
  gained a `runtime` Cargo feature that gates its tokio +
  crossbeam-channel transport (wasm-incompatible); the wasm crate
  pulls it in with `default-features = false`. Federations have real
  Ed25519 keypairs, a real Merkle revocation tree, and the canonical
  `run_consensus_round` quorum logic (`n - floor(n/3)` online votes).
  The async TCP transport (`TcpFederationTransport`,
  `NetworkConsensusNode`) is unchanged and is NOT exposed to wasm.
  Memory note: federation removed for wasm was stale; verify against
  the current source — federation IS wired.
- **IntentPool:** a `Vec<Intent>` lives directly on the runtime; no
  separate pool type. Intents created via `create_intent` are stored;
  matching via `match_intent_for_agent`.
- **Conditional turns:** real `dregg_turn::ConditionalTurn` queue
  (`PendingConditional`).

### 3.2 What the JS layer fakes around the wasm

These are workarounds in `runtime-in-memory.js` for wasm getters that
don't exist yet:

- **Intent ledger** — wasm has no `get_intent(idx)` / `list_intents`.
  JS keeps `intentLedger[]` populated by `createIntent` calls. Intents
  created out-of-band (none today) won't appear in `<dregg-intent>`.
- **Block log** — wasm has no `get_block(fed_idx, height)`. Wait, the
  comment in `block.js` says wasm exposes `get_federation_block` —
  and indeed `runtime-in-memory.js` uses it. The block inspector's
  stale comment should be updated. The JS-side block log used to be
  the workaround; the wasm getter now exists. **(Filing this as a
  fix in §5.)**
- **Federation count** — wasm has no `count_federations`; JS bumps a
  local signal in `createFederation`. Federations created outside the
  JS path (none today) won't surface in `listBlocks()`.
- **Capability per-id resolution** — caps are agent-indexed by slot,
  not by global ID. URI form is `dregg://capability/<agent_idx>/<slot>`,
  which violates STUDIO.md § 4's "stable URI" promise. This is a known
  protocol-level mismatch: caps don't *have* global IDs in this
  runtime; the sim addresses them by (holder, slot). Needs design
  closure before the URI scheme can stabilize.

### 3.3 What `DreggRuntime` exposes (the wasm side)

**World management:** `create_runtime` / `destroy_runtime`

**Cell ops:** `create_cell` (mint from genesis), `get_cell_state`,
`get_all_cells`, `get_cell_state_commitment`

**Agent ops:** `create_agent` (genesis or minted-from-genesis),
`agent_mint_token`, `grant_capability`, `get_capability_tree`

**Turn ops:** `execute_turn` (auto-signs Unchecked actions via
`sign_call_forest`), `get_receipt_chain`,
`compute_conditional_deposit`, `submit_conditional`

**Intent ops:** `create_intent`, `match_intent_for_agent`

**Notes / nullifiers:** `create_note`, `spend_note`

**Federation ops:** `create_federation`, `propose_block`,
`simulate_consensus_round`, `get_federation_state`,
`get_federation_block`, `list_federation_blocks`

**Peer exchange:** `register_peer`, `create_peer_transition`,
`verify_peer_transition`, `get_peer_view`, `list_peers`,
`get_peer_pubkey`

**Revocation channels:** `create_revocation_channel`, `trip_channel`,
`is_channel_active`

**Block clock:** `advance_height`

**Crypto helpers (non-runtime, in `lib.rs`):** mint_token,
stark/predicate/committed-threshold/schnorr/garbled proofs,
intent ID derivation, BLAKE3, fold deltas, datalog evaluator,
stealth addresses, range proofs, encrypted intents.

### 3.4 Trust model in the browser

Every cryptographic primitive surfaced in the Studio is the canonical
Rust implementation: Ed25519 from `dregg_sdk::AgentCipherclerk`,
Poseidon2/STARK from `dregg_circuit`, federation consensus from
`dregg_federation`, peer transitions from `dregg_cell::PeerExchange`,
nullifiers from `dregg_cell::NullifierSet`. **No JS-side
re-implementation of any of these.** This is the bedrock the studio
agent should defend: a Studio bug is a real bug; a Studio passing
test is a real test.

---

## §4. Refactor-by-refactor pickup table

For each row: which Studio files reference (or will reference) the
soon-to-change surface; what the change looks like; rough LOC delta;
prerequisites.

### Refactor 1 — `AppCipherclerk` (Lane C, landed in `app-framework/src/cipherclerk.rs`)

| Field | Value |
|---|---|
| **Studio surface affected** | None today — Studio drives `AgentCipherclerk` directly via `runtime.rs::SimAgent`. Starbridge-apps surface IS affected once the JS turn-builders land. |
| **Where it lands** | `starbridge-apps/shared/turn-builders/index.js` is the JS analog: each builder constructs a turn-spec that the cclerk signs via `window.dregg.signTurn`. The Rust `AppCipherclerk` is the *server* / *node* side; the Studio is a thin viewer + signer, NOT an `AppCipherclerk` consumer in Rust. |
| **Change to Studio** | Nothing structural in the inspectors. The doc `starbridge-apps/README.md` correctly frames the JS turn-builders as `window.dregg.signTurn` wrappers — that's the right pattern; the studio agent should write the first one (`nameservice.js` per the README example). |
| **LOC delta** | ~60 (one nameservice turn-builder + its inspector hookup). |
| **Prereqs** | None. `AppCipherclerk` is landed in Rust; the JS side is independent. |

### Refactor 2 — `StarbridgeAppContext` (Lane C/I)

| Field | Value |
|---|---|
| **Studio surface affected** | The mounting flow used by `starbridge-apps/*/pages/index.html`. Today `nameservice/pages/index.html` declares `factory-vk="..."` as an attribute on `<dregg-app>`; nothing reads it. |
| **Where it lands** | `<dregg-app>` in `site/src/_includes/studio/context.js` should grow `factory-vk`, `registry-uri`, and a per-app `FactoryDescriptor[]` registration hook. The framework's preload contract (apps export `FACTORY_DESCRIPTORS`, host calls `register`) needs a JS mirror that hands the wasm runtime the array at boot — equivalent to the Rust `StarbridgeAppContext::register`. |
| **Change to Studio** | (a) extend `<dregg-app>` to read `factory-vk` / `registry-uri` attrs and expose them to children via the same closest-ancestor protocol; (b) add `runtime.preloadFactory(descriptorJson)` on `InMemoryRuntime`; (c) wasm needs `preload_factory_descriptor(handle, json)` binding — Rust side. |
| **LOC delta** | ~80 JS + ~40 Rust binding. |
| **Prereqs** | Need the `StarbridgeAppContext` Rust trait stabilized in `app-framework`; today `starbridge-apps/README.md` says it's not yet defined. Coordinate with Lane I. |

### Refactor 3 — `Authorization::CapTpDelivered` (Lane A, landed in `turn/src/action.rs`)

| Field | Value |
|---|---|
| **Studio surface affected** | The receipt/turn inspectors. Today `inspectors/turn.js` and `inspectors/receipt.js` render `r.action_count` and `r.computrons_used` — they do NOT surface action authorization at all. So nothing breaks; the variant is invisible to Studio. |
| **Where it lands** | `wasm/src/bindings.rs::get_receipt_chain` would have to grow per-action authorization fields (currently it returns only top-level receipt metadata; see the `Receipt shape` doc-comment in `inspectors/receipt.js`). Then `<dregg-turn>` and `<dregg-receipt>` grow an "authorization" row with a 6-variant badge: `Signature` / `Proof` / `Breadstuff` / `Bearer` / `Unchecked` / `CapTpDelivered`. |
| **Change to Studio** | New inspector helper `<dregg-authorization>` (compact mode renders a badge; default mode shows the typed payload, e.g. for `CapTpDelivered` show capability_id + delivery_proof_hash). Wire it into `<dregg-turn>` (per-action) and `<dregg-receipt>`. |
| **LOC delta** | ~120 JS (new inspector + integration). ~30 Rust (binding enrichment). |
| **Prereqs** | Wasm binding must surface per-action authorization. Today it doesn't. |

### Refactor 4 — Federation unification (Lane M); `KnownFederations` registry

| Field | Value |
|---|---|
| **Studio surface affected** | `inspectors/federation.js`, `runtime-in-memory.js::createFederation`, `runtime-remote.js::pickHeight` (status payload changes). |
| **Where it lands** | The new `Federation` type subsumes `SimFederation`, `Federation`, `FederationNode`, `FederationState` (the latter two live in `extension/src/types.ts`). The studio agent owns the JS-side unification: collapse `SimFederation` (in `runtime.rs`) and the federation summaries returned by `get_federation_state` into one shape that matches the unified Rust type. The `KnownFederations` registry needs a Studio UX: a "Federations" pane listing the federations this runtime knows, with add/remove. |
| **Change to Studio** | (a) new `<dregg-federation-list>` inspector that reads `runtime.listKnownFederations()` — new method. (b) new `<dregg-federation-add>` form (Lane N CLI will exist; this is the GUI sibling) talking to `window.dregg` via a new `registerFederation` method (see §2.4). (c) extend `runtime-remote.js` to discover via `GET /api/federations`. |
| **LOC delta** | ~180 JS. Lane M Rust + Lane N CLI + extension cclerk additions are dependencies. |
| **Prereqs** | Lane M (Federation type unification) must land; Lane N CLI shape should be stable so the GUI doesn't drift; extension cclerk needs `registerFederation` / `listKnownFederations` methods. |

### Refactor 5 — `federation_id = H(committee_pubkeys)` (Lane D, landed)

| Field | Value |
|---|---|
| **Studio surface affected** | `inspectors/federation.js` (the `latest_root` field — but that's a different hash). The actual federation_id is sourced from `executor.local_federation_id` in `wasm/src/runtime.rs::execute_turn_for_agent`; it never reaches the JS layer. |
| **Where it lands** | (a) `bindings.rs::get_federation_state` should return `federation_id` derived from committee_pubkeys (per `dregg_federation::Federation::id()`, if such a getter exists or needs to be added). (b) `<dregg-federation>` shows the derived `federation_id` as a top-level field. |
| **Change to Studio** | Add `federation_id` to the federation summary serde struct in `bindings.rs`. Add a row to `<dregg-federation>`. |
| **LOC delta** | ~20 JS + ~10 Rust. |
| **Prereqs** | None — landed. |
| **Acceptance test** | Display value must equal `BLAKE3-derive("dregg-federation-id-v1", concat(sort(committee_pubkeys)))` (or whatever Lane D specifies); the studio agent must NOT show random bytes from the federation node's local config. |

### Refactor 6 — Slot caveats (`cell::program::StateConstraint` → 21 variants, in flight)

| Field | Value |
|---|---|
| **Studio surface affected** | No existing inspector reads cell-program state constraints. `<dregg-cell>` renders `permissions` as `JSON.stringify` — the StateConstraint shape is hidden inside `cell.state` / `cell.program` which the JS layer doesn't unpack. |
| **Where it lands** | (a) `bindings.rs::get_cell_state` must surface `cell.program.constraints: Vec<StateConstraint>` as a structured field; today the `CellStateView` struct omits the program entirely. (b) New `<dregg-cell-program>` inspector renders the 21-variant list with per-variant compact display. (c) `<dregg-cell>` shows the program inspector in a tab or sub-pane. |
| **LOC delta** | ~250 JS (the 21-variant switch is large) + ~80 Rust binding. |
| **Prereqs** | The 21-variant enum must be stable. Today `SLOT-CAVEATS-DESIGN.md` and `SLOT-CAVEATS-EVALUATION.md` exist; the variants list should be locked before the studio agent writes the inspector — otherwise the inspector enum-switch becomes the canonical reference, which is upside-down. |

### Refactor 7 — γ.2 bilateral binding (bilateral PI slots in cell proofs)

| Field | Value |
|---|---|
| **Studio surface affected** | The receipt inspector. Today `<dregg-receipt>` shows `pre_state_hash`, `post_state_hash`, `computrons_used`, `timestamp`, `action_count`. Bilateral PI slots are part of the proof attached to a receipt; the Studio doesn't surface proofs at all. |
| **Where it lands** | (a) `bindings.rs::get_receipt_chain` exposes per-receipt proof metadata: `proof_kind`, `public_inputs`, bilateral binding slots. (b) New `<dregg-proof>` inspector (mentioned in STUDIO.md table but not built yet) renders the PI vector, marking the γ.2 bilateral slots. (c) `<dregg-receipt>` links to `<dregg-proof uri="dregg://proof/<hash>">`. |
| **LOC delta** | ~150 JS + ~50 Rust binding. |
| **Prereqs** | γ.2 design must land (`STAGE-7-GAMMA-2-PI-DESIGN.md` exists; check status). |

### Refactor 8 — `SovereignCellWitness` redesigned (soundness sweep)

| Field | Value |
|---|---|
| **Studio surface affected** | The peer-exchange UI in `site/src/studio.html` calls `runtime.createPeerTransition(...)` and `runtime.verifyPeerTransition(...)`; the witness shape is opaque (postcard bytes; base64'd for paste). The witness's *internal structure* is not displayed. |
| **Where it lands** | New `<dregg-peer-transition>` inspector that decodes the postcard bytes and renders `{ cell_id, sequence, old_commitment, new_commitment, effects_hash, signature, optional_stark_proof }`. The new shape per the soundness sweep is `PeerStateTransition`-shaped (sig + sequence + optional STARK); studio renders all four fields. |
| **Change to Studio** | (a) wasm binding `decode_peer_transition(bytes) -> JsValue` returning the structured shape (currently the JS layer only sees the encoded bytes). (b) `<dregg-peer-transition>` inspector. (c) studio.html surfaces it next to `pxMine` and `pxView`. |
| **LOC delta** | ~140 JS + ~40 Rust binding. |
| **Prereqs** | Soundness sweep — Sovereign witness redesign must land. |

### Refactor 9 — Cipherclerk `compute_turn_bytes` v1 → v3 (soundness sweep)

| Field | Value |
|---|---|
| **Studio surface affected** | The wasm runtime signs via `cclerk.sign_action(...)` and the executor verifies — if both sides upgrade together, the runtime is fine. But the *extension* cclerk has its own `signTurn` path that must also upgrade, AND the receipt now must surface `sovereign_witnesses` so the user can see what was bound. |
| **Where it lands** | (a) `extension/src/page.ts::signTurn` may need to accept a `sovereign_witnesses?: Witness[]` field in `turnSpec`. (b) `<dregg-receipt>` shows a "sovereign witnesses" section if non-empty. (c) `<dregg-turn>` likewise. |
| **LOC delta** | ~80 JS (UI) + ~30 extension cclerk (types + envelope). |
| **Prereqs** | The v3 message format must be locked; the extension cclerk author must agree on the new `signTurn` shape. |

### Refactor 10 — DFA rationalization (userspace primitive surface)

| Field | Value |
|---|---|
| **Studio surface affected** | Indirect. Routing DFAs are referenced in `site/src/index.html` and `site/src/learn/*` as a marketing/learn topic but not surfaced anywhere in Studio inspectors. |
| **Where it lands** | A new `<dregg-route>` / `<dregg-dfa>` inspector that shows the routing DFA for a given service path. URI form: `dregg://dfa/<service>` or `dregg://route/<id>`. Reads `runtime.getRoute(serviceId)` — new method, needs wasm binding and (for Remote) HTTP endpoint. |
| **LOC delta** | ~200 JS (the DFA viz is non-trivial — node-and-edge SVG) + wasm binding. |
| **Prereqs** | `DFA-RATIONALIZATION-DESIGN.md` must conclude; the userspace primitive shape must be fixed. |

### Refactor 11 — Slop apps deleted (Lane I)

| Field | Value |
|---|---|
| **Studio surface affected** | Site/marketing content, NOT the Studio substrate. References found: |
| | `site/src/index.html` lines 133, 138, 143, 218, 260 — "stablecoin", "amm", "orderbook" icons in the "usecases" section and a code block of `cargo run -p dregg-stablecoin --example demo`-style snippets |
| | `site/src/apps.html` lines 174-200 — multiple references to `dregg-stablecoin`, `dregg-amm`, `dregg-orderbook` examples |
| | `site/src/paper.html`, `site/src/learn/architecture/{consensus,privacy,overview}.html`, `site/src/learn/users/{captp,cli}.html`, `site/src/learn/developers/building-apps.html` — text/snippet references |
| | `apps/` directory still contains `amm/`, `lending/`, `orderbook/`, `stablecoin/`, etc. (the brief says deleted; verify against current git state — `ls apps/` at survey time shows them still present). The brief may mean "scheduled for deletion in Lane I" or "deleted in the in-flight branch". |
| **Change to Studio** | Marketing copy edit, NOT inspector work. The inspector surface is generic (`<dregg-cell>` doesn't care whether the cell is an AMM pool or a name registration). The studio agent should: (a) remove dead `cargo run -p dregg-X --example Y` snippets from `apps.html`; (b) replace the marketing icons in `index.html` with starbridge-app names that exist (nameservice today; more per `STARBRIDGE-APPS-PLAN.md §6`); (c) ensure no inspector silently special-cases an app domain. |
| **LOC delta** | ~50 HTML/markup edits. |
| **Prereqs** | Confirm with Lane I which apps are *actually* deleted (not "scheduled"). |

### Refactor 12 — `starbridge-apps/nameservice` (first proper starbridge-app)

| Field | Value |
|---|---|
| **Studio surface affected** | The "app browser" surface. There is no app browser today; `starbridge-apps/nameservice/pages/index.html` exists but is a standalone page, not surfaced from the Studio top-bar. |
| **Where it lands** | (a) New "Apps" tab in Starbridge: read `starbridge-apps/*/manifest.json` (a file that doesn't exist yet; needs design) and render an app card grid linking to each app's `pages/index.html`. (b) Write the first turn-builder (`starbridge-apps/shared/turn-builders/nameservice.js`) per the README example. (c) Write the first inspectors (`shared/inspectors/name.js` exporting `NameInspector`, `NameRegistryInspector`). (d) Hook them into `nameservice/pages/index.html` (today references `<dregg-name-registry>` / `<dregg-name-inspector>` which are undefined custom elements — would log a "no inspector registered" message). |
| **LOC delta** | ~400 (~200 JS for inspectors, ~80 for turn-builders, ~100 for the app browser, ~20 for manifest plumbing). |
| **Prereqs** | (a) `FactoryDescriptor` preload contract from refactor 2; (b) `window.dregg.createFromFactory(NAME_FACTORY_VK, ...)` resolution must work — needs the descriptor to be in scope on the cclerk side; (c) app-manifest format design. |

### Refactor 13 — Discord-bot moved to top-level

| Field | Value |
|---|---|
| **Studio surface affected** | Marketing/docs only. References found: `site/src/apps.html:206` says `apps/discord-bot` — should be `discord-bot/`. |
| **Change to Studio** | Path string update in `apps.html` (and any other markdown/html that mentions `apps/discord-bot`). Studio inspectors don't depend on the discord-bot path. |
| **LOC delta** | ~5. |
| **Prereqs** | None. |

---

## §5. Net work for the resumed studio agent (prioritized)

Ordered by (a) prereqs satisfied, (b) blast radius, (c) value to other lanes.

### Quick wins (no prereqs, < ~2 hours each)

1. **Refactor 13** — Path fixes in `site/src/apps.html` and any other
   markup that says `apps/discord-bot`.
2. **Refactor 11 (the doc parts)** — Marketing copy edit:
   `site/src/index.html` use-case icons; `site/src/apps.html` dead
   snippet block. **First** verify with Lane I which apps are actually
   deleted vs. scheduled — don't run ahead.
3. **`runtime-in-memory.js` cleanup** — the block-inspector workaround
   comment (`block.js` says wasm has no `get_block`; wasm now has
   `get_federation_block`). Update the comment; the code is already
   correct.
4. **Refactor 5** — Add `federation_id` derived from committee_pubkeys
   to the wasm `get_federation_state` response, surface it in
   `<dregg-federation>`. Acceptance: not a random byte string.

### Inspector enrichment (prereqs landed; ~1 day each)

5. **Refactor 3** — `<dregg-authorization>` inspector + wire into
   `<dregg-turn>` and `<dregg-receipt>`. Wasm binding enrichment
   (`get_receipt_chain` returns per-action auth).
6. **Refactor 8** — `<dregg-peer-transition>` inspector. New wasm
   binding `decode_peer_transition`. Replaces the opaque base64 blob
   in `site/src/studio.html` with structured display.
7. **Refactor 7 / Refactor 9** — `<dregg-proof>` inspector + sovereign-
   witness section on `<dregg-receipt>`. Bilateral PI slots and v3
   `sovereign_witnesses` both need the same binding enrichment, so
   batch them.

### Structural (prereqs in flight; coordinate with other lanes)

8. **Refactor 2** — `StarbridgeAppContext` JS mirror: extend
   `<dregg-app>` with `factory-vk` / `registry-uri` attrs, add
   `runtime.preloadFactory()`, add `preload_factory_descriptor` wasm
   binding. Block on the Rust trait stabilizing (Lane I).
9. **Refactor 12 piece A** — Write `starbridge-apps/shared/turn-builders/nameservice.js`
   matching the README example. Wire `nameservice/pages/index.html` to
   actually mount the (now-defined) custom elements.
10. **Refactor 12 piece B** — Write `starbridge-apps/shared/inspectors/name.js`
    exporting `NameInspector` and `NameRegistryInspector`. Register
    via `window.dregg.register('dregg-name', ...)`. The starbridge-app
    page becomes the first end-to-end demonstration.
11. **Refactor 12 piece C** — "Apps" tab in Starbridge with manifest
    discovery. Coordinate on manifest format (§7 Q4).
12. **Refactor 4** — Federation registry GUI. Block on Lane M
    (federation unification) and Lane N (CLI shape).
13. **Refactor 6** — Slot caveats inspector. Block on the 21-variant
    enum stabilizing. This will be the largest single piece of
    inspector work; do it last.
14. **Refactor 10** — DFA inspector. Block on the userspace primitive
    landing.

### Cross-cutting cleanup (any time)

15. Resolve the `window.dregg` naming collision (see §6.1). Either
    rename the Preact bootstrap namespace to `window.dreggUi` /
    `window.dreggRt`, or wrap them both behind a `window.dregg = {
    cclerk: ..., runtime: ... }` indirection. **Either path is a
    breaking change for whichever side moves; coordinate with the
    extension author.**
16. Real time-travel cursor on `InMemoryRuntime` (caps.timeTravel =
    true). Today the cursor is read-only. The wasm runtime needs a
    "rewind-to-height" capability, which it lacks — every mutation is
    cumulative.

---

## §6. Things Studio might WANT but we haven't designed

### 6.1 Resolution of `window.dregg` collision

Already flagged in §2.1. The fix is structural and the two owners
(extension page-injection, Studio runtime-bootstrap) don't currently
talk. Options:

- **(a) Rename bootstrap.** `window.dreggUi = { h, html, render, ... }`.
  Cheapest. Forces every inspector and starbridge-app page to update.
- **(b) Namespace both.** `window.dregg = { cclerk: <api>, ui: <api>,
  runtime: <studio rt registry> }`. Requires the extension to define
  `dregg.cclerk` instead of `dregg.<flat methods>`. Breaking change
  for every dapp consuming the cclerk today.
- **(c) Detection + merge.** Bootstrap checks for an existing
  `window.dregg`; if it's the cclerk, attach UI fields to a sibling
  rather than overwriting. The `Object.freeze` on the cclerk side
  makes this awkward.

The studio agent should NOT pick this unilaterally; surface as §7 Q1.

### 6.2 Receipt-chain replay viewer

Cross-federation receipt chains are referenced in
`WITNESSED-RECEIPT-CHAIN-DESIGN.md`. Studio shows a *list* of receipts
(`<dregg-receipt-list>`) but no chain navigation — clicking a receipt
doesn't surface its predecessor. The `previous_receipt_hash` link is
the obvious primitive; a `<dregg-receipt-chain>` inspector that walks
backward visually would close the loop.

### 6.3 Cross-federation peer discovery UX

`dregg_cell::PeerExchange` is the "Discord-paste" primitive; the
studio demonstrates it manually. A real discovery mechanism (e.g.
"my agent is in federation A; show me what federation B knows about
my counterparty") is not designed. The brief mentions
`register-federation` UX (Lane N CLI); a sibling GUI flow + a peer
discovery viewer would complete the picture.

### 6.4 Slot-caveat editor (not just viewer)

Refactor 6 produces a *viewer* for slot caveats. The harder UX is the
*editor*: "I want this cell's slot 7 to be `RequireGteThreshold(100)`
unless slot 8 is `True`". A form-based slot-caveat composer that emits
a `StateConstraint` would be a userspace primitive of its own. Out of
scope for the resumed agent unless requested.

### 6.5 Turn-builder inspector (mentioned in STUDIO.md, never built)

`<dregg-turn-builder>` is in the STUDIO.md inspector table. There's
no implementation. A mutation-mode inspector that walks the user
through "select cell → select method → fill effects → sign" would
make Starbridge a real IDE rather than a viewer. Highest user value
once the basics land; do not build before refactors 2, 5, 8 stabilize.

### 6.6 Debugger inspector (also in the STUDIO.md table)

`<dregg-debugger>` is mentioned, never built. The Trace step type
exists in `wasm/src/runtime.rs::TraceStep`; the wasm binding to expose
it does not. A step-into / step-over / breakpoint UI for turn
execution would close a real gap — there's no way to debug a failing
turn in the browser today.

### 6.7 Snapshot export/import (STUDIO.md § 8)

The Snapshot button alerts "will be wired up". The Rust side
(`DreggRuntime::serializeHistory`) doesn't exist. The dregg-node
ingest path doesn't exist. This is a feature, not a refactor; it
deserves its own design pass.

---

## §7. Open questions for the studio designer

These need a human/designer call. Decisions here gate sections of §5.

**Q1.** `window.dregg` collision — see §6.1. Rename, namespace, or
merge? Whichever path, BOTH the extension cclerk team and the studio
team must agree before either changes. **Blocking** for any
starbridge-app that needs both extension cclerk AND Studio inspectors.

**Q2.** URI scheme stability for things-without-global-IDs.
`dregg://capability/<agent_idx>/<slot>` is sim-specific. Real
capabilities don't have stable IDs either (they're attenuated tokens
or in-cell slots). What's the canonical addressing? **Blocking** for
the Federation/Remote runtime growing capability inspection.

**Q3.** App manifest format for the "Apps" browser (refactor 12 piece
C). JSON file in each `starbridge-apps/*/manifest.json` with name,
description, factory_vks, page-fragment URL, required `window.dregg`
methods? Or something more dynamic via the Rust crate's
`StarbridgeAppContext::register`? **Blocking** §5 task 11.

**Q4.** Time-travel on `InMemoryRuntime`. The wasm runtime is
cumulative — no rewind primitive. Options: (a) snapshot-and-replay
(serialize at height N, deserialize for jump-back); (b) keep N
parallel runtimes for the last N heights (memory-bound); (c) declare
time-travel an Explorer-only feature backed by a recorded snapshot.
**Blocking** the cursor scrubber actually being writable.

**Q5.** Inspector registration namespace. Today `<dregg-cell>` etc. are
in the global custom-elements registry. Starbridge-apps want to add
their own (`<dregg-name>`, `<dregg-name-registry>`, etc.). Naming
conflict risk: two apps both want `<dregg-token>`. Should we namespace
(`<starbridge-nameservice-name>`)? Or rely on per-app reservation?

**Q6.** Read-only Remote runtime parity. Today it exposes only
`getCell` / `listCells`. STUDIO.md implies the full Runtime interface
applies. Should the studio agent treat parity as a phase-1 goal, or is
"Explorer = read cells + status" a permanent floor and the full
inspector set is in-memory-only?

**Q7.** Should `<dregg-app>` accept multiple runtimes (e.g.
`runtime-write="sim" runtime-read="remote"`) so a starbridge-app can
preview locally and submit upstream? STUDIO.md doesn't say.

**Q8.** Migration of the 29 playground sections. STUDIO.md § 9 Phase
3 says "deprecate as content is absorbed". Is the resumed studio agent
expected to do that migration, or is it strictly the inspector +
starbridge-app work? Scope clarity prevents drift.

---

## Appendix A — file inventory for quick reference

```
site/STUDIO.md
site/PLAN.md
site/src/starbridge.html
site/src/studio.html
site/src/_includes/runtime-bootstrap.js
site/src/_includes/studio/
  context.js
  inspectors.js
  inspectors/{_base,turn,receipt,receipt-list,capability,
              capability-list,intent,federation,block}.js
  runtime-in-memory.js
  runtime-remote.js
  runtimes.js
  starbridge.css
  starbridge.js
  uri.js
extension/src/{page,types,content,background,api}.ts
wasm/src/{lib,runtime,bindings,privacy}.rs
starbridge-apps/README.md
starbridge-apps/nameservice/{Cargo.toml,README.md,src/lib.rs,
                             pages/index.html}
starbridge-apps/shared/inspectors/index.js
starbridge-apps/shared/turn-builders/index.js
starbridge-apps/shared/factories/README.md
app-framework/src/cipherclerk.rs              (the AppCipherclerk — Rust-side)
turn/src/action.rs                       (Authorization::CapTpDelivered)
```

## Appendix B — counted methods on `window.dregg` (cclerk)

43 methods total. 6 are the canonical ones called out in the brief
(`signTurn`, `createFromFactory`, `verifyProvenance` named explicitly;
plus `authorize`, `postIntent`, `peerExchange` as the next-most-load-
bearing). The remainder are surface-area for the existing extension
features (privacy, storage, federation discovery, CapTP brokerage,
queue ops). Studio uses zero of them today.

## Appendix C — quick verifications done during this survey

- Federation is wired (not "removed for wasm" as memory suggested);
  `wasm/src/runtime.rs::SimFederation` wraps `dregg_federation::Federation`.
- `Authorization::CapTpDelivered` is landed in `turn/src/action.rs`.
- `AppCipherclerk` is landed in `app-framework/src/cipherclerk.rs`.
- `starbridge-apps/nameservice/` exists with the README example
  matching the code; the JS turn-builders and inspectors are stubs.
- `discord-bot/` is at the toplevel.
- Slop apps (`amm`, `lending`, `orderbook`, `stablecoin`,
  `bounty-board`, `compute-exchange`, `gallery`,
  `governed-namespace`, `privacy-voting`, `subscription`) are still
  present under `apps/` at survey time. Verify deletion before
  removing references from the site.
