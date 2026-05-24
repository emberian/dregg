# Pyana Studio — Runtime Substrate Plan

**Status:** design draft. Successor / addendum to `site/PLAN.md`. Where the
two conflict, this document wins for the runtime layer; `PLAN.md` continues
to govern the design system, visualizer rubric, and accessibility floor.

This document does **not** redesign the visual identity, the page chrome, or
the inline `<pyana-vizzer>` widgets. Those are stable and good. It adds the
layer above them: a **runtime substrate** that turns Playground, Explorer,
and a new third surface (**Starbridge**) into three viewports onto the same
distributed-runtime IDE.

---

## 1. Vision

Today the playground is 29 atomized demos. The explorer is a separate read-only
viewer for a live node. They share no protocol semantics — clicking a cell in
one tells you nothing about the same cell in the other.

The Studio vision: **all three surfaces are the same IDE**, fed by different
data sources.

- **Playground** — runs a `pyana::PyanaRuntime` in the browser. You drive a
  simulated testnet: create cells, post intents, execute turns, advance
  blockheight. State is yours; you can fork, undo, export.
- **Explorer** — read-only viewport onto a live federation node (over WS /
  HTTP). Same inspectors as the playground; only the data source differs.
- **Starbridge** — power-user surface. Connects to a live node *with write
  authority*, plus an in-browser node for "what if" branching, plus
  breakpoint / fault-injection controls on the simulator runtime. Same
  components again; the runtime context just exposes more capabilities.

The user types `pyana://cell/abc123` into Starbridge and gets the same
`<pyana-cell>` view they'd see in Playground or Explorer — backed by whichever
runtime is currently active.

---

## 2. Three surfaces, one substrate

| Surface     | URL           | Default runtime           | Authority      | Audience                |
|-------------|---------------|---------------------------|----------------|-------------------------|
| Playground  | `/playground/`| `InMemoryRuntime` (wasm)  | Owner          | Tutorials, exploration  |
| Explorer    | `/explorer/`  | `RemoteRuntime` (live WS) | Read-only      | Journalists, end-users  |
| Starbridge  | `/starbridge/`| User-selected             | User-selected  | Devs, operators, debug  |

Same nav links, same theme, same components. Each surface picks a *default*
runtime and a *default* set of inspectors-on-screen; the rest is shared.

---

## 3. Runtime interface

The core abstraction. Every inspector takes a `Runtime` (via DOM context
provider) and an object reference. Three implementations.

```ts
interface Runtime {
  // Capability advertisement — UI gates affordances on these
  readonly caps: { read: true; mutate: boolean; debug: boolean; timeTravel: boolean };
  readonly source: { kind: 'sim' | 'remote' | 'recorded'; label: string };

  // Object resolution — every getter returns a Signal so visualizers react
  getCell(id: CellId): Signal<CellState | null>;
  getTurn(hash: TurnHash): Signal<Turn | null>;
  getReceipt(hash: ReceiptHash): Signal<TurnReceipt | null>;
  getCapability(id: CapId): Signal<Capability | null>;
  getIntent(id: IntentId): Signal<Intent | null>;
  getProof(id: ProofId): Signal<Proof | null>;
  // ...one per protocol object type

  // Bulk / index views
  listCells(filter?: CellFilter): Signal<CellId[]>;
  listTurns(range?: HeightRange): Signal<TurnHash[]>;
  // ...

  // Mutation (errors with NotPermitted on read-only runtimes)
  executeTurn(turn: TurnSpec): Promise<TurnReceipt>;
  postIntent(intent: IntentSpec): Promise<IntentId>;
  advanceHeight(blocks: number): Promise<void>;
  // ...

  // Subscription — for live updates (driver depends on impl)
  subscribe(filter: EventFilter, cb: (event: RuntimeEvent) => void): Unsubscribe;

  // Time cursor (only when caps.timeTravel)
  cursor: Signal<BlockHeight>;     // read+write on sim; read-only on live replay

  // Lifecycle
  destroy(): void;
}
```

**Three implementations:**

- `InMemoryRuntime` — wraps the `PyanaRuntime` exposed by `wasm/src/runtime.rs`,
  which itself is a thin orchestrator over the **real** `pyana_sdk::AgentWallet`,
  `pyana_cell::Ledger`, and `pyana_turn::TurnExecutor`. All cryptographic
  paths (signing, key derivation, receipt chaining) are the canonical
  pyana-sdk implementations — not parallel reimplementations. The Studio
  in-browser path exercises the same code native callers do; finding bugs
  here finds bugs in the real system.
- `RemoteRuntime` — speaks the federation node's HTTP/WS API. Read-only by
  default. Subscription via SSE or WebSocket gossip stream.
- `RecordedRuntime` — replays a snapshot. Read-only but supports `cursor`
  scrub through full history. Built from `InMemoryRuntime.serializeHistory()`
  or from a live-node export.

**No in-JS simulation.** The Studio does not include parallel implementations
of pyana behavior in JavaScript. If a feature isn't exposed by the wasm
crate, the inspector shows a placeholder until the wasm path lands — we'd
rather have a visible gap than a fictional demonstration. This is what
makes the Studio useful as a forcing function for wasm-side improvements.

**Federation** is now wired. `pyana-federation` gained a `runtime` feature
that gates its tokio + crossbeam-channel transport (the wasm-incompatible
bits), and the wasm crate depends on it with `default-features = false`.
The in-browser runtime constructs real `pyana_federation::Federation`
instances; every block hash, quorum certificate, proposer signature, and
merkle root surfaced in `<pyana-federation>` / `<pyana-block>` comes from
the canonical types. Behavior differences vs. the deleted `SimFederation`
are real — e.g. `propose_block` requires `n - floor(n/3)` online votes to
finalize and rejects empty event lists. The native async TCP transport
(`TcpFederationTransport`, `NetworkConsensusNode`) is unchanged but is not
exposed to wasm.

A fourth runtime eventually: `RelayedRuntime` — an in-browser node that
joins a real blocklace via a relaying server (since browsers can't open
QUIC). Out of scope for this doc; the interface already accommodates it.

---

## 4. URI scheme

Every protocol object has a stable URI. Inspectors take a `uri` attribute
(not `ref` — Preact reserves that for DOM-element references). Resolution
happens via the active `Runtime` context.

```
pyana://cell/<hex32>                  cell by id
pyana://turn/<hex32>                  turn by hash
pyana://receipt/<hex32>               receipt by hash
pyana://capability/<token-id>         capability by id (root or attenuated)
pyana://intent/<hex32>                intent by id
pyana://block/<height-or-hex>         blocklace vertex
pyana://proof/<hex32>                 STARK proof by content-hash
pyana://federation/<name>             federation by stable handle
```

Two extras that make the IDE feel real:

```
pyana://cell/<id>@<height>            cell state at a specific block height
pyana://cell/<id>/cap/<service>       sub-object query: caps on this cell
```

Resolution: a URI is resolved against the current `Runtime`. If the runtime
can't see the object (e.g. you pasted a sim URI into the explorer), the
inspector shows a "not found in this runtime — switch?" prompt.

URIs are addressable in the URL bar: `/starbridge/?at=pyana://turn/abc...`
deep-links to a specific object. Sharable.

---

## 5. Inspector components

Built as Preact functional components registered via the existing
`window.pyana.register` registry. **One inspector per protocol-object type**;
each composes its sub-objects by URI.

```html
<!-- the consuming page -->
<pyana-app runtime="sim">
  <pyana-cell uri="pyana://cell/abc123"></pyana-cell>
</pyana-app>
```

```js
// site/src/_includes/inspectors/cell.js
import { defineInspector } from '/_includes/inspector-base.js';

defineInspector('pyana-cell', ({ ref, runtime, mode }) => {
  const cell = runtime.getCell(parseRef(ref).id);  // Signal<CellState | null>
  return html`
    <pyana-card title=${`cell ${ref}`}>
      ${() => cell.value
        ? html`
            <pyana-kv data=${cellSummary(cell.value)} />
            <pyana-tabs>
              <pyana-tab label="Capabilities">
                ${cell.value.capabilities.map(cap => html`
                  <pyana-capability ref=${`pyana://capability/${cap.id}`} mode="compact" />
                `)}
              </pyana-tab>
              <pyana-tab label="State"><pyana-state-tree value=${cell.value.state} /></pyana-tab>
              <pyana-tab label="History"><pyana-turn-list filter=${{ touched: ref }} /></pyana-tab>
              <pyana-tab label="Raw"><pyana-json value=${cell.value} /></pyana-tab>
            </pyana-tabs>
          `
        : html`<pyana-empty message="cell not found in this runtime" />`
      }
    </pyana-card>`;
});
```

**Inspector contract:**

1. Receives `uri` (the pyana:// string), `runtime` (DOM-context), `mode`
   (`compact`, `default`, `inspector`, `raw`). Same inspector renders four ways.
2. All data fetched through `runtime.get*()` — never directly from wasm.
3. All embedded sub-objects use the same `<pyana-X uri="...">` pattern. No
   special "embedded vs. standalone" code paths.
4. Capability-gates UI on `runtime.caps`. Read-only runtimes hide mutation
   affordances entirely; they don't show greyed-out buttons.
5. Static fallback under `<noscript>`: the JSON of the object as a `<pre>`.

**Initial inspector set** (matches existing protocol objects):

| Inspector              | Required runtime cap | Default mode |
|------------------------|----------------------|--------------|
| `<pyana-cell>`         | read                 | default      |
| `<pyana-turn>`         | read                 | default      |
| `<pyana-receipt>`      | read                 | default      |
| `<pyana-capability>`   | read                 | compact      |
| `<pyana-intent>`       | read                 | default      |
| `<pyana-proof>`        | read                 | compact      |
| `<pyana-block>`        | read                 | compact      |
| `<pyana-federation>`   | read                 | default      |
| `<pyana-turn-builder>` | mutate               | inspector    |
| `<pyana-debugger>`     | debug                | inspector    |

---

## 6. State management

Already chosen by `PLAN.md` § 3: **Preact + @preact/signals-core + htm**, via
CDN. Studio adds two conventions on top.

1. **Runtime objects are signals.** `runtime.getCell(id)` returns
   `Signal<CellState | null>`. Inspectors that read it auto-rerender when the
   underlying state changes. Runtime impls are responsible for invalidating
   the signal on mutation/subscription events.
2. **Runtime context via custom element.** `<pyana-app runtime="sim">` puts a
   `Runtime` on the DOM context. Inspectors look it up via
   `host.closest('pyana-app').runtime`. No prop-drilling.

No new dependency. ~100 lines of glue on top of the existing
`runtime-bootstrap.js`.

---

## 7. Time cursor

Every runtime exposes `cursor: Signal<BlockHeight>`. Sim runtimes let you
write to it (rewind / fast-forward through replay); live runtimes track the
node's head and let you scrub back through cached history.

All `runtime.get*()` reads are implicitly *at the cursor's height*. Moving
the cursor invalidates all cached signals and triggers re-render. This is
how `pyana://cell/<id>@<height>` URIs work — the inspector pins the cursor
locally instead of reading the global one.

UI: a horizontal scrubber at the bottom of Starbridge, showing block heights
with markers for turn count, intent count, proof count. Click any height to
jump. Hold shift-arrow to step one block at a time.

---

## 8. In-browser node + export / import

The `wasm/src/runtime.rs` `PyanaRuntime` is *already* a complete in-browser
distributed-runtime simulation (ledger, executor, nullifier set, intents,
federations, conditional turns). What we need to add:

1. **JS-side runtime driver** that owns the wasm handle and exposes the
   `Runtime` interface above.
2. **Snapshot format**: `runtime.serializeHistory() → Uint8Array`. Contains
   genesis block, full ordered turn log, intent log, federation events. Per
   the existing `wasm/src/runtime.rs` types, postcard-serializable.
3. **`pyana-node` ingest path**: a CLI subcommand
   `pyana-node import-snapshot <bytes>` that replays the log into a real
   on-disk ledger. *This piece lives in `node/`, not `site/`.* The site
   produces the bytes; the node consumes them.
4. **Live → snapshot path** (eventually): the federation node exposes a
   `GET /snapshot?from=<h>&to=<h>` endpoint that returns the same format.
   `RecordedRuntime` ingests it for offline forensics.

Round-trip property: a snapshot taken from sim, ingested into `pyana-node`,
re-exported from the node, should hash-match (modulo timestamps).

---

## 9. Migration plan

The existing 29 playground sections work. They are not blocking the vision.
Migrate incrementally; do not big-bang.

**Phase 0** (this PR or the next, ~1 day): the vertical spike.
- Land `Runtime` interface + `InMemoryRuntime` driving a few `PyanaRuntime`
  calls (create_cell, execute_turn, get_all_cells).
- Land URI parsing + `<pyana-app>` context provider.
- Build `<pyana-cell>` inspector end-to-end.
- Add a "Studio preview" route on the playground that hosts a single
  `<pyana-app><pyana-cell ref="..."></pyana-cell></pyana-app>`. The old
  sections stay; they don't see this.

**Phase 1** (~1 week): the prototype Studio inside the playground.
- Build the remaining inspectors: turn, receipt, capability, intent,
  proof, block.
- Build `RemoteRuntime` against the explorer's existing API.
- Wire the explorer's existing per-view tabs to use inspectors instead of
  bespoke HTML. Old views can stay until parity is reached.

**Phase 2** (~2 weeks): `/starbridge/` as a new surface.
- Page chrome (re-uses head/nav from `_layouts/default.html`).
- Time-cursor scrubber, runtime picker, multi-pane layout.
- Turn-builder inspector (mutation), debugger inspector (step-into).
- Snapshot export/import flow (UI side; node-side import is its own ticket).

**Phase 3** (open-ended): deprecate the old 29 sections page by page as
their content is absorbed into inspector workflows. Some (the pure crypto
micro-demos: token-mint, predicate-proof, range-proof) probably stay forever
as educational standalone widgets in `/playground/learn/`.

---

## 10. Open questions

1. **Snapshot format scope.** Do we ship the full turn log, or just the
   final state + a "since-X" delta? Affects size and replay semantics.
   *Default*: full log. Compresses well, lets us replay anything.

2. **Authority for live mutation in Starbridge.** Does the explorer node
   accept *any* signed turn from a connected wallet, or only ones whose
   capability chain it can verify against its own state? Probably the latter,
   but we need a UX for "your turn was rejected — here's why."

3. **Runtime swap mid-session.** If I'm viewing `pyana://cell/X` on the sim
   and switch to the remote runtime, do we (a) try to resolve X on the remote
   and show "not found", (b) pop a prompt, (c) clear the workspace? Defaulting
   to (b) for now.

4. **Performance.** Wasm linear memory holds the sim state. A long session
   with many turns will grow. Need to instrument and decide if we need
   periodic GC, snapshot+restart, or LRU on observed objects.

5. **Schema evolution.** As the protocol changes, old snapshots break. Same
   problem as on-disk ledger; defer to the same versioning strategy
   (`pyana_types::Version`).
