# Pyana Site Overhaul — Architect Plan

**Owner:** site overhaul architect.
**Audience:** the three Builder agents (Playground, Explorer, Learn-pages) and the
human reviewer.
**Status:** plan-of-record. Do not edit without coordinating with the architect.

This document is the spec. The builders execute against it. The architect does
not build the playground / explorer / learn pages.

The repository already has a coherent visual identity (canopy / moss / lantern /
ink — see `site/src/assets/style.css`). The job is *not* a redesign from zero;
it is to (a) **factor** that identity into a real design system, (b) **wire** a
minimal interactive runtime that lets us write *good* visualizers without a
bundler, and (c) **surface** the new-world features (blinded queues,
programmable queues, ring trades, inboxes, BatchExecutor, nameservice, signed
delegation v2) in the playground and explorer.

---

## 1. Goals + scope

### Success looks like
1. **Every page on the site renders with the same tokens** — colors, type
   scale, spacing, motion timing, radii — from a single CSS file
   (`site/src/_includes/design-tokens.css`). No more drift between marketing,
   docs, playground, and explorer.
2. **The playground has dedicated, real visualizers for the new-world
   primitives**: a blinded-queue tab that runs `commit → consume → nullifier`
   with real BLAKE3 in-browser; a ring-trade tab that animates cycle search
   over a real intent graph; a programmable-queue tab that lets the user write
   constraints and watch `try_enqueue` accept or reject candidates; an inbox
   tab that walks the `push → drain → gc` lifecycle with the anti-spam deposit
   visible; a delegation-envelope tab that shows the signed payload tree and
   the v2 authority policy; a nameservice tab that registers/resolves names.
3. **The explorer gains parity views**: a "Queues" view that reads
   `/blinded/<service>`, `/queue/<service>`, and `/inbox/<service>` endpoints
   from any connected app; a "Delegations" view that walks the authority chain
   of any capability; a "Names" view backed by the nameservice client.
4. **Learn pages are visually re-leveled** — same tokens, real diagrams (SVG
   inline, not images), embedded `<pyana-vizzer data-vizzer="…">` cards where
   text alone is not enough. The content stays; only the chrome and the
   inline figures change.
5. **A single `pyana` JS namespace** (loaded via CDN ESM, ~15-25KB gz) gives
   builders a tiny reactive layer (signals + functional components), a code
   highlighter wrapper, a copy-to-clipboard helper, a toast, and a
   `pyana.register('vizzer-name', factory)` registry. No npm install on the
   host machine.
6. **Accessibility floor**: WCAG AA contrast everywhere; visible focus rings
   in moss/lantern; full keyboard navigation in all tabs and detail panels;
   `prefers-reduced-motion` honored by every animation.
7. **The build script (`site/build.js`) is unchanged in spirit** — still
   shiki + lightningcss + vanilla Node + the `<layout>` / `<include>` macros.
   Only the *runtime* gets richer.

### Explicit non-goals (out of scope)
- **No SSR**, no static-site generator framework (no Astro/Eleventy/Hugo).
- **No SPA routing across pages**. Each top-level page (`/`, `/learn/...`,
  `/playground/`, `/explorer/`) remains its own document. Within the playground
  and explorer, in-page section switching is fine (already exists).
- **No bundler.** No webpack/vite/esbuild/rollup as part of `npm run build`.
- **No new build-time npm dependency** unless the user explicitly approves it
  via a Docker invocation. Runtime libs come from CDN ESM at page load.
- **No new framework on top of WASM.** WASM bindings stay where they are.
- **No changes outside `site/`.** Don't touch `apps/`, `app-framework/`, `sdk/`,
  `circuit/`, `intent/`, `turn/`, `wire/`, etc.
- **No mass rewrite** of existing playground sections that already work.
  Migration is additive — new tabs land alongside old, then we cull what is
  obsoleted (see §8).

---

## 2. Information architecture

```
site/
├── index.html                          (marketing landing — keep, restyle)
├── apps.html                           (apps catalog — keep, restyle)
├── learn.html                          (learn landing — keep, restyle)
├── paper.html                          (PDF embed — minor)
├── demo.html / demos/                  (existing demo flow — keep)
├── learn/
│   ├── architecture/   (overview, consensus, captp, privacy, cryptography,
│   │                    capabilities, federation, economics)
│   ├── developers/     (sdk, building-apps, tokens, storage, privacy-api,
│   │                    service-mesh, bridges, mcp, wasm, tutorial-first-app,
│   │                    typescript-sdk)
│   ├── operators/      (running-a-node, setup, federation, monitoring,
│   │                    security, relay, bridge)
│   └── users/          (quickstart, cli, cipherclerk, intents, privacy, captp)
├── playground/
│   └── (existing section modules + new ones; see §7.Playground)
├── explorer/
│   └── (existing views + new "queues", "delegations", "names"; see §7.Explorer)
└── src/_includes/
    ├── design-tokens.css        ← NEW (architect)
    ├── runtime-bootstrap.js     ← NEW (architect)
    ├── visualizer-base.js       ← NEW (architect)
    ├── head.html                (extend to load design-tokens.css)
    ├── nav.html                 (unchanged; verify all top-level links)
    ├── footer.html
    └── sidebar-learn.html
```

### Where new-world features live

| Feature                | Playground tab                | Explorer view             | Learn page                                       |
|------------------------|-------------------------------|---------------------------|--------------------------------------------------|
| Blinded queues         | `blinded-queues` (new)        | `queues` (new, "blinded") | `developers/storage.html` (extend)               |
| Programmable queues    | `programmable-queues` (new)   | `queues` (new, "policy")  | `developers/storage.html` (extend)               |
| Ring trade solver      | `ring-trades` (new)           | `intents` (extend)        | `developers/building-apps.html` (extend)         |
| Inboxes (S&F)          | `inboxes` (new)               | `queues` (new, "inbox")   | `developers/service-mesh.html` (extend)          |
| BatchExecutor          | `batch-executor` (new)        | `turns` (extend)          | `developers/building-apps.html` (extend)         |
| Nameservice            | `nameservice` (new)           | `names` (new)             | `users/cli.html` (extend)                        |
| Signed delegation v2   | `delegation-v2` (new)         | `delegations` (new)       | `architecture/capabilities.html` (extend)        |
| DFA routing            | `dfa-routing` (existing,      | (existing routes)         | `architecture/federation.html` (already present) |
|                        | restyle)                      |                           |                                                  |

---

## 3. Runtime choice + justification

**Choice: Preact 10 + `@preact/signals-core`, loaded via esm.sh.**

```js
// site/src/_includes/runtime-bootstrap.js (excerpt)
import { h, render, Fragment } from 'https://esm.sh/preact@10.22.0';
import { signal, computed, effect, batch } from 'https://esm.sh/@preact/signals-core@1.7.0';
import htm from 'https://esm.sh/htm@3.1.1';

// Optional integrity hashes can be added once tags are stable.
```

### Why Preact (not Alpine, not Lit, not vanilla)
| Criterion             | Preact + signals          | Alpine.js                 | Lit + lit-html         | Vanilla / DOM           |
|-----------------------|---------------------------|---------------------------|------------------------|-------------------------|
| Gz size               | ~4 KB + ~2 KB signals     | ~7 KB                     | ~5-6 KB                | 0                       |
| Reactivity model      | fine-grained signals      | string-templated `x-data` | reactive properties    | manual                  |
| Composition           | functional components     | sprinkles                 | web components         | ad-hoc                  |
| A11y story            | renders real DOM, easy    | DOM stays, OK             | shadow DOM friction    | trivial                 |
| Pizzazz-to-complexity | high (animations + state) | medium                    | medium                 | low (we have this now)  |
| Learning curve        | familiar to React devs    | small                     | small                  | none                    |

Signals matter here: every visualizer has a *small* piece of state (queue
items, a selected node, a hovered intent leg) that several sub-components
need to react to. Without signals, each builder reinvents an event bus. With
signals, `const queue = signal([])` and any component that reads `queue.value`
re-renders automatically. We get this for ~6 KB gzip.

`htm` lets us write JSX-like templates with tagged template literals and **no
JSX build step**:

```js
const html = htm.bind(h);
const Item = ({ entry }) => html`<li class="q-item">${entry.commitment}</li>`;
```

### How builders import it
Every page that wants the runtime adds **one line** to its `<head>`:

```html
<script type="module" src="/_includes/runtime-bootstrap.js"></script>
```

`runtime-bootstrap.js` puts a single namespace on `window`:

```
window.pyana = {
  h, render, Fragment, html,      // Preact + htm
  signal, computed, effect, batch,// signals
  register(name, factory),         // visualizer registry
  mount(rootEl),                   // upgrade <pyana-vizzer> elements
  highlight(code, lang),           // shiki-light wrapper (server-rendered when build-time)
  copy(text),                      // copy-to-clipboard + toast
  toast(msg, kind),
  reducedMotion(),                 // boolean
  hex: { to(bytes), from(s) },     // utilities
};
```

### How it integrates with `build.js`
**It does not.** `build.js` is unchanged — it still copies through
`playground/` and `explorer/`, compiles HTML/CSS, runs shiki on `<pre><code>`
at build time. The runtime is loaded at *page time* from CDN, with optional
SRI hashes pinned in `runtime-bootstrap.js` once a builder freezes versions.

The one tiny change is in `site/src/_includes/head.html`: it must
`<link rel="stylesheet" href="/_includes/design-tokens.css">` *before* the
main stylesheet so tokens are available. `build.js` already walks `src/` for
CSS — to keep `_includes/*.css` from being inlined into `style.css`, we
emit it as a normal asset. The builder responsible for the head should
copy `_includes/design-tokens.css` to `dist/_includes/design-tokens.css`
explicitly (one extra pass in `walk()` or a dedicated copy step).

---

## 4. Design system

### 4.1 Tokens

These tokens are defined in `site/src/_includes/design-tokens.css`. They are
the **only** authoritative source. Any value not derived from these tokens
is a bug.

#### Color (semantic, dark default; light override scoped to `[data-theme="light"]`)

| Token              | Dark value             | Light value            | Role                                  |
|--------------------|------------------------|------------------------|---------------------------------------|
| `--bg`             | `#0a0f0d` (canopy)     | `#f5f0e8` (chalk)      | page background                       |
| `--bg-raised`      | `#121b16` (loam)       | `#ffffff`              | cards, panels                         |
| `--bg-inset`       | `#080c0a` (void)       | `#ede7da`              | code, table headers                   |
| `--fg`             | `#e4ddd0` (ink)        | `#1c1b18`              | body text                             |
| `--fg-dim`         | `#a89e8e`              | `#4a453e`              | secondary text                        |
| `--fg-muted`       | `#7a7265`              | `#7a7265`              | tertiary / hints                      |
| `--accent`         | `#5b8a5a` (moss)       | `#3f6a3e`              | primary action                        |
| `--accent-bright` | `#7aab6f` (fern)       | `#5b8a5a`              | hover, link                           |
| `--warm`           | `#c49245` (lantern)    | `#a07432`              | warning / highlight / "active"        |
| `--info`           | `#6ba3c7`              | `#3e7593`              | informational                         |
| `--danger`         | `#d4685c`              | `#a73e32`              | destructive                           |

Contrast for AA body text against `--bg` is verified: `#e4ddd0 on #0a0f0d` =
14.3:1. For dim: `#a89e8e on #0a0f0d` = 7.5:1. Lantern on canopy: 6.4:1.

#### Type scale (modular, base 16, ratio 1.2)
| Token         | Value                          | Use                       |
|---------------|--------------------------------|---------------------------|
| `--text-xs`   | `clamp(0.72rem, 0.7rem + 0.1vw, 0.8rem)`  | meta, badges    |
| `--text-sm`   | `0.875rem`                     | UI body                   |
| `--text-base` | `1rem`                         | body copy                 |
| `--text-md`   | `1.125rem`                     | lede                      |
| `--text-lg`   | `1.4rem`                       | section eyebrows          |
| `--text-xl`   | `clamp(1.75rem, 1.4rem + 1.5vw, 2.4rem)`  | h2              |
| `--text-2xl`  | `clamp(2.2rem, 1.6rem + 2.5vw, 3.4rem)`   | h1 / hero       |

Fonts: `--font-body` (system sans), `--font-mono` (SF Mono / JetBrains Mono /
Cascadia), `--font-display` (Iowan Old Style / Palatino — kept for hero only).

#### Spacing (4-px base)
`--s1 4` `--s2 8` `--s3 12` `--s4 16` `--s5 24` `--s6 36` `--s7 56` `--s8 80`.

#### Motion
| Token              | Value                                   |
|--------------------|-----------------------------------------|
| `--dur-fast`       | `90ms`                                  |
| `--dur`            | `180ms`                                 |
| `--dur-slow`       | `360ms`                                 |
| `--dur-deliberate` | `720ms`  (visualizer animations)        |
| `--ease`           | `cubic-bezier(0.25, 0.46, 0.45, 0.94)`  |
| `--ease-out`       | `cubic-bezier(0.16, 1, 0.3, 1)`         |
| `--ease-in-out`    | `cubic-bezier(0.83, 0, 0.17, 1)`        |

`@media (prefers-reduced-motion: reduce)` collapses all durations to `1ms`
and disables transforms in visualizers.

#### Radii / shadows
Radii: `--r1 3px` `--r2 6px` `--r3 10px` `--r4 16px` `--r5 28px` (rare).
Shadow scale (subtle on dark, use sparingly): `--sh1`, `--sh2`, `--sh3`.

### 4.2 Components — naming + 1-line contract

These are the reusable building blocks the builders MUST use. Each is exposed
either as a Preact component on `window.pyana` (camelCase) or a CSS class
(`.pyana-...`).

| Component              | Contract                                                              |
|------------------------|-----------------------------------------------------------------------|
| `Pyana.Card`           | Padded raised surface with optional title bar + footer actions.       |
| `Pyana.Tabs`           | Keyboard-navigable tab strip; `aria-selected`, arrow-key nav.         |
| `Pyana.Stepper`        | Linear `1 → 2 → 3` flow with prev/next + completion state.            |
| `Pyana.Code`           | Wraps shiki output; copy button; optional line highlighting.          |
| `Pyana.HexDisplay`     | Truncated 32-byte hex with full-on-hover + click-to-copy.             |
| `Pyana.HashBadge`      | Inline 7-char prefix + colored swatch derived from hash.              |
| `Pyana.Vizzer`         | The host element `<pyana-vizzer data-vizzer="name" data-…>`.          |
| `Pyana.Toast`          | Bottom-right transient notification (info/success/warn/error).        |
| `Pyana.KV`             | Two-column key/value list, monospace values.                          |
| `Pyana.Empty`          | Standard empty state with icon + message + optional action.           |
| `Pyana.Spinner`        | Three sizes; reduces to a static dot under reduced-motion.            |
| `Pyana.LogStream`      | Auto-scrolling append-only log with timestamps + filter.              |
| `Pyana.Diff`           | Side-by-side before/after for state changes.                          |
| `Pyana.Slider`         | Labeled range input with value readout + steps.                       |
| `Pyana.Pill`           | Status pill (ok/warn/err/pending), used everywhere status is shown.   |

### 4.3 Accessibility floor (concrete WCAG checks)
- All interactive elements have a **2px outline + 1px offset** focus ring
  using `outline-color: var(--warm)`. **No `outline: none` without an
  explicit replacement.**
- Body text contrast ≥ **4.5:1**; large text ≥ 3:1. Dim text ≥ 4.5:1 on
  raised surfaces.
- Every tab strip implements **`aria-selected`, `role="tablist"`,** and
  Left/Right/Home/End keyboard nav.
- Every modal traps focus, restores it on close, and is dismissible with
  **Escape**.
- Every visualizer must work with `prefers-reduced-motion: reduce` — animation
  is replaced with discrete step controls (Prev / Next).
- Every visualizer must have a **fallback `<noscript>` block** describing what
  it shows in prose, and the static "rest state" must render without JS for
  the case where Preact fails to load.
- Color is never the only signal — every status pill pairs color with an icon
  or word ("ok", "warn", "err").

---

## 5. Visualizer rubric

A good visualizer in this codebase:
1. **Shows a real data model** — not a metaphor. The blinded-queue vizzer
   shows the actual Merkle tree being built from real BLAKE3 hashes the user
   produces; the ring-trade vizzer shows the actual leg graph our solver
   would see.
2. **Updates from user input** — sliders, buttons, text inputs. No
   auto-running animation as the primary mode.
3. **Is inspectable** — every visible node/edge/cell has hover-to-reveal the
   underlying hex/struct. No opaque "magic happens here" boxes.
4. **Is steppable** — at any moment the user can advance one step (or back
   up), and the state diff between steps is visible.
5. **Has a static fallback** — under reduced-motion or no-JS, it renders a
   final snapshot with prose explaining what the live version would show.
6. **Registers itself**: `pyana.register('vizzer-name', (host, dataset) => {...})`,
   so any HTML page can drop `<pyana-vizzer data-vizzer="blinded-queue">` to
   instantiate one.

### The 8-12 visualizers we will ship

| Name                          | Data model shown                                                                                 |
|-------------------------------|--------------------------------------------------------------------------------------------------|
| `blinded-queue`               | `storage/blinded::BlindedQueue`: commit-tree leaves, nullifier set, consumption proof.           |
| `programmable-queue`          | `storage::ProgrammableQueue` constraint set + try-enqueue accept/reject decisions over time.     |
| `ring-trade`                  | `app-framework/ring_trade::RingTradeParticipant` leg graph; cycle search; atomic settle/rollback.|
| `inbox-lifecycle`             | `app-framework/inbox_endpoint`: deposit anti-spam, push, drain, gc; message TTL.                 |
| `batch-executor`              | `app-framework/batch_executor`: client queue → collect_batch → execute_batch → proof.            |
| `delegation-envelope-v2`      | `DelegationAuthority` signed payload tree + caveat chain + revocation snapshot.                  |
| `captp-sturdy-ref`            | sturdy `pyana://` URI lifecycle, 3-party handoff cert, swiss number rotation.                    |
| `nameservice-registration`    | `apps/nameservice` register → resolve → reverse → rental; DFA route after resolve.               |
| `effect-vm-trace`             | Effect VM trace columns (24 effects, 371 AIR columns) — restyle of existing.                     |
| `merkle-membership`           | Existing merkle vizzer, restyled + linked into blinded-queue/notes/explorer.                     |
| `intent-pool-graph`           | `intent::trustless`: encrypted intents → decrypted batch → solver submissions → winning compound. |
| `dfa-routing`                 | DFA over message tags; restyle of existing route visualizer with the new tokens.                  |

Each vizzer is a single JS module in `site/playground/visualizers/<name>.js`
that calls `pyana.register('<name>', factory)`. They are reused by Learn
pages and (where relevant) by Explorer views.

---

## 6. Builder-agent assignments

Three builders run **in parallel** after this plan lands. Each owns a
**disjoint** set of files. They coordinate **only** through `PLAN.md`,
`design-tokens.css`, `runtime-bootstrap.js`, and `visualizer-base.js`.

### Builder A — Playground (`site/playground/**`)
- **Scope**: `site/playground/index.html`, `playground.js`, `style.css`,
  `sections/*.js`, `visualizers/*.js`.
- **Outcomes**:
  1. Re-skin `index.html` + `style.css` to consume `design-tokens.css`.
     Replace local `:root` color block with `@import` (or rely on global).
  2. Add new section files: `blinded-queues.js`, `programmable-queues.js`,
     `ring-trades.js`, `inboxes.js`, `batch-executor.js`, `nameservice.js`,
     `delegation-v2.js`.
  3. Implement the new visualizers listed in §5 in
     `visualizers/<name>.js`, each registering via `pyana.register`.
  4. Keep all existing sections working. Their internals can stay; only
     re-skin them to use the new tokens + `Pyana.Card` / `Pyana.Tabs`.
- **Forbidden**:
  - Don't modify `build.js`.
  - Don't introduce a framework other than the runtime-bootstrap namespace.
  - Don't fetch new CDN packages without adding them to `runtime-bootstrap.js`
    (single import surface).
- **Example tasks**:
  - "Add a `blinded-queues` tab; mount the `blinded-queue` vizzer; on commit
    button, BLAKE3 hash the order text + random secret in the browser,
    insert into the on-page commitment tree, animate the leaf joining."
  - "Re-skin the `tokens` section: replace `.pg-card` with `.pyana-card`
    classnames; verify all hover/focus states still work."

### Builder B — Explorer (`site/explorer/**`)
- **Scope**: `site/explorer/index.html`, `app.js`, `explorer.js`, `api.js`,
  `style.css`, `views/*.js`, `components/*.js`, `tweakers/*.js`,
  `visualizers/*.js`.
- **Outcomes**:
  1. Re-skin to consume `design-tokens.css`.
  2. Add new views: `views/queues.js` (sub-tabs: blinded / policy / inbox),
     `views/names.js`, `views/delegations.js`.
  3. Extend `api.js` with thin clients for `/blinded/<svc>`, `/queue/<svc>`,
     `/inbox/<svc>`, `/names/resolve`, `/delegations/<id>`.
  4. Reuse the playground visualizers — call `pyana.register`-ed factories
     from explorer views where appropriate (do NOT fork them).
- **Forbidden**:
  - Don't fork visualizers; if one is missing, file an issue and stub.
  - Don't add a real-time WebSocket without specifying back-pressure.
- **Example tasks**:
  - "Add `views/queues.js`. Tabs: Blinded / Policy / Inbox. Each lists known
    services from `discovery.json`; clicking a service fetches its current
    queue state + renders the matching vizzer."
  - "Add `views/delegations.js`. Search by capability id; render the v2
    envelope vizzer with the resolved authority chain."

### Builder C — Learn pages (`site/src/learn/**` + `site/src/*.html`)
- **Scope**: every `.html` under `site/src/learn/`; `site/src/index.html`,
  `apps.html`, `learn.html`, `demo.html`, `paper.html`.
- **Outcomes**:
  1. Audit every page for the new tokens; remove any hard-coded colors that
     conflict with `design-tokens.css`.
  2. Replace flat-text figures with `<pyana-vizzer data-vizzer="…">` cards
     in the architecture + developers sections.
  3. Add a per-page "On this page" mini-TOC for any page over ~600 words
     (use a small standardized component, no new framework).
  4. Update `site/src/_includes/head.html` to link `design-tokens.css`
     **before** `style.css`, and to optionally load `runtime-bootstrap.js`
     when the page uses `data-needs-runtime="true"` on `<body>`.
- **Forbidden**:
  - Don't rewrite content. Restyle, restructure, augment — do not delete
    prose that wasn't replaced by something equivalent or better.
  - Don't change the URL structure.
- **Example tasks**:
  - "On `architecture/capabilities.html`, add the `delegation-envelope-v2`
    vizzer inline after the `<h2 id='delegation'>` heading."
  - "On `developers/storage.html`, embed both `blinded-queue` and
    `programmable-queue` vizzers in the relevant subsections."

---

## 7. Migration plan

- **Existing playground sections stay running** during the transition. Each
  is re-skinned (CSS changes) but the JS section module keeps its current
  shape until the corresponding *new* vizzer ships and is wired in.
- **Old visualizers** (`playground/visualizers/dag-graph.js`,
  `merkle-tree.js`, `state-diff.js`) stay where they are. They get adapted
  to the `pyana.register` registry as part of Builder A's work.
- **Explorer views are additive.** The existing nav stays; new entries are
  appended. No view is deleted in this overhaul.
- **Risk areas**:
  1. **Token drift during transition** — Builder A and Builder B both touch
     local stylesheets. Both must import design tokens early; any local
     `:root { --color-… }` must be deleted, not overridden.
  2. **CDN reliability** — esm.sh has been stable but is a single point of
     failure. `runtime-bootstrap.js` should `try / catch` the dynamic import
     and surface a graceful banner ("Interactive features unavailable —
     refresh or check network"). Optionally pin to a Cloudflare R2 mirror in
     a follow-up.
  3. **`<pyana-vizzer>` is unknown to the HTML spec.** Treat as a *plain
     element with a class*, not a real custom element — `runtime-bootstrap.js`
     uses `document.querySelectorAll('[data-vizzer]')` and mounts Preact
     inside. This sidesteps shadow DOM and works under no-JS (the element
     just shows its fallback content).

### What is already good and stays
- The marketing tone on `index.html`. Restyle, don't rewrite.
- The blocklace DAG visualizer in the explorer. Solid; just rethemes.
- `build.js`. It is exactly the right size.
- The `<layout>` / `<include>` macros. They are the right level of magic.
- Shiki for code blocks. Best-in-class.
- The capability / proof / federation prose in `learn/architecture/`. The
  content is good. The presentation needs the vizzers we're shipping.

---

## 8. Open questions for the user
1. **Light theme** — the tokens include light values, but no page currently
   honors a light theme. Should Builder C add a theme toggle in the nav, or
   keep the site dark-only for now?
2. **Real cryptography in the playground** — for `blinded-queue` we need
   BLAKE3 in the browser. Two options: (a) load a tiny BLAKE3 WASM blob from
   the existing pyana wasm package, or (b) load a third-party BLAKE3 ESM
   module. The architect's pick is (a); confirm.
3. **Live data in the explorer** — the new `queues` view assumes apps expose
   `/blinded/<svc>` etc. publicly. Some apps gate this behind admin auth.
   Should the explorer surface admin-auth prompts, or only show what the
   anonymous endpoint exposes?
4. **Versioning the runtime** — pin to specific esm.sh versions (e.g.
   `preact@10.22.0`) or float on `preact@10`? The architect's pick is to pin
   and bump deliberately; confirm.
5. **Hosting the runtime locally** — if the user prefers no CDN at all, the
   architect can vendor Preact + signals + htm into
   `site/src/_includes/vendor/` (3 files, ~12 KB) and adjust
   `runtime-bootstrap.js`. Confirm preference.
