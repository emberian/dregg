# Pyana Cipherclerk Extension

Chrome browser extension for capability-based authorization with ZK proofs.

No build step. No npm. Plain JS loaded directly by Chrome.

## Architecture

```
Page Context               Content Script            Background SW
+-----------------+       +----------------+       +------------------+
| window.pyana    |       |                |       | Cipherclerk State     |
|   .authorize()  | ====> | CustomEvent    | ====> | - Ed25519 keys   |
|   .isConnected()|       | bridge         |       | - Cap tokens     |
|   .getCapabili  | <==== |                | <==== | - Receipt chain  |
|    ties()       |       |                |       | - Datalog eval   |
+-----------------+       +----------------+       | - ZK prover      |
     page.js              content.js               +------------------+
                                                      background.js
```

## Load in Chrome

1. Open `chrome://extensions/`
2. Enable "Developer mode" (top right)
3. Click "Load unpacked" and select this `extension/` directory
4. The Pyana Cipherclerk icon appears in the toolbar

## Files

- `manifest.json` — Manifest V3, no special permissions beyond storage
- `background.js` — Service worker: cipherclerk state, token evaluation, proof generation
- `content.js` — Bridges page events to background via chrome.runtime
- `page.js` — Defines `window.pyana` API in page context
- `popup.html` + `popup-script.js` — Extension popup UI

## Page API

```js
// Check if pyana cipherclerk is available
const connected = await window.pyana.isConnected();

// Request authorization
const result = await window.pyana.authorize({
  action: 'read',
  resource: '/data/x',
  mode: 'private',  // 'trusted' | 'selective' | 'private'
});
// result: { allowed: true, proof: [...], facts: [...] }

// List available action types
const caps = await window.pyana.getCapabilities();
```

## WASM integration (planned)

The crypto stubs in `background.js` will be replaced with calls to the pyana WASM
crate (`crates/wasm`) for real Ed25519 signing, Datalog evaluation, and STARK proof
generation. The WASM binary loads as a module in the service worker context.
