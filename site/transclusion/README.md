# /transclusion/ — Xanadu made honest, on the open web

Two deliverables live behind this directory:

1. **The demo page** (`site/transclusion/index.html`, shipped at `/transclusion/`)
   — drives the real wasm transclusion bindings
   (`wasm/src/bindings_transclusion.rs`) in the visitor's tab: publish →
   transclude → amend (live follows, snapshot pins) → forge (refused with
   `ContentHashMismatch`) → per-viewer projection (attenuate or darken, never
   amplify) → receipt-pinned backlinks.
2. **The embeddable script** (`site/dregg-works/transclude.js`, shipped at
   `/dregg-works/transclude.js` and at the `dregg.works` apex beside
   `verify-badge.js`) — lets ANY web page carry a verified `dregg://` quote
   with one script tag.

## What is real, what is demo

- The demo page's federation is the in-tab
  [`WebOfCells`](../../starbridge-web-surface/src/web_of_cells.rs): a genuine
  ledger + 3-of-3 quorum attestation, verified with the structural gate
  (`AttestedResource::verify`). The quotes, refusals, projections, and
  backlinks are all produced by the real
  [`starbridge_web_surface::transclusion`](../../starbridge-web-surface/src/transclusion.rs)
  machinery — no parallel model.
- The embeddable script's trust root is a **node API the visitor selects**
  (`data-node`, overridable everywhere) and the **content-addressed cell id**.
  It checks `blake3(served bytes) == on-chain slot-0 commitment`
  (`GET <node>/api/cell/<cell>` → `fields[0]`, the same lookup
  `verify-badge.js` performs) — it does not run the receipt/quorum chain in
  JS. For the full chain in a browser, that is exactly what the wasm demo
  page runs.

## The honest fallback (both surfaces)

The rule everywhere: **verification lightens; nothing else does.**

- The demo page's quote spans are *darkened placeholders in static HTML*.
  Only a successful verified render replaces them. No JS, a failed wasm load,
  or a non-verifying read all leave the placeholder dark, with the failure
  named in a banner. A forge attempt renders refusal chrome — the forged
  bytes are shown struck-through as *evidence*, never as content.
- `transclude.js` keeps the author's fallback text through every non-verified
  state: `pending` and `unverified` darken it, `refused` strikes it and names
  the mismatch (served vs committed hash), and only `verified` swaps in the
  actual committed bytes — painted with `textContent`, never as markup, so a
  quoted source cannot script the quoting page.

## Embed API (transclude.js)

```html
<script src="https://<your-host>/transclude.js"></script>

<blockquote data-dregg="dregg://<64-hex cell id>#b=120-240"
            cite="https://any-host.example/charter.html"
            data-node="https://devnet.dregg.fg-goose.online">
  fallback text — darkened until the bytes verify
</blockquote>
```

| attribute | meaning |
|---|---|
| `data-dregg` | the source ref; optional `#b=<start>-<end>` selects a byte range of the committed document |
| `data-dregg-cell` + `data-start`/`data-end` | split form of the same |
| `cite` / `data-src` | where the source document's bytes are served (any untrusted host; `data-src` wins) |
| `data-node` | per-element node API base for the commitment lookup |

Page-wide node default: `data-node` on the script tag → `<meta name="dregg:node">`
→ `window.__DREGG__.node` → the public devnet node (`sdk/src/endpoints.rs`
`defaults::DEVNET`). `window.dreggTransclude.rescan()` re-verifies after
dynamically inserting quotes.

## Backlinks — the other half of the two-way link

`transclude.js` is the *forward* direction (this page quotes that cell,
verifiably). The *reverse* direction — "who quotes this cell" — is the
`Backlinks` registry (`starbridge-web-surface/src/transclusion.rs`), exposed
to the browser by `transclusion_include_into` / `transclusion_backlinks`
(`wasm/src/bindings_transclusion.rs`) and rendered live on the demo page.
Each backlink pins the receipt + content commitment that was observed, so an
old quote visibly cites the old value: quotes are dated, not overwritten.

## How it plugs into the pages build

`scripts/build-pages-dist.sh` changes (all additive; nothing existing moves):

- **step 0** copies `site/transclusion` → `dist/transclusion` next to the
  other static pages, and grows two `test -f` teeth
  (`dist/transclusion/index.html`, `dist/dregg-works/transclude.js` — the
  latter already rode the existing `cp -R site/dregg-works`).
- **after the light-client freshness tooth** (which the transclusion tooth
  mirrors) a **transclusion tooth** runs the just-built `dist/cards/pkg`
  engine headless under node and asserts the demo's polarity green-or-bust:
  include verifies the committed bytes, a live read follows an amend, and a
  byte-tamper forge is REFUSED with `ContentHashMismatch`. A wasm surface
  that stops refusing fails the assembly, exactly like a stale
  `history.json` does.
- the final summary echoes a `/transclusion/` line.

The page imports the wasm from `../cards/pkg/dregg_wasm.js` — the same pkg the
cards and light-client pages already share (`bindings_transclusion` is a
module of the `wasm/` crate), so **no new wasm build step** is added and the
gpui/atlas/REUSE_WASM knobs are untouched.
