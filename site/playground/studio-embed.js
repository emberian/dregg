// Playground ↔ Studio inspector bridge (STARBRIDGE-PLAN §4.9 Tier 2).
//
// The legacy playground sections each owned a bespoke per-section JS widget.
// This module lets a section embed the *real* platform inspectors instead:
//
//     <dregg-app><dregg-proof uri="..."></dregg-proof></dregg-app>
//
// Every <dregg-app> on the page shares ONE in-memory DreggRuntime (the same
// canonical wasm runtime Starbridge uses). The runtime is seeded with real
// data — two agents, a real transfer turn, a real note, a real federation
// block — so the embedded inspectors render canonical state, never JS
// simulation or placeholders.
//
// Mutators are async (await runtime.createAgent / runtime.executeTurn).
//
// We do NOT depend on app-boot.js's one-shot mount: playground sections render
// their DOM lazily inside init*(), so we attach the runtime to <dregg-app>
// elements both eagerly and via a MutationObserver as sections appear.

import { createInMemoryRuntime } from '/_includes/studio/runtime-in-memory.js';
import '/_includes/studio/context.js';
import '/_includes/studio/inspectors.js';

/** Resolves to { runtime, wasm, seed } once the shared runtime is seeded. */
let _readyPromise = null;

/** Seed identifiers other modules build inspector URIs from. */
export const seed = {
  turnHash: null,     // hex32 — the committed transfer turn (proof + turn-debugger)
  aliceCell: null,    // hex64 — alice's cell id (cell/capability/peer inspectors)
  bobCell: null,      // hex64 — bob's cell id
  noteCommitment: null, // hex — a real note commitment (note inspector)
  note: null,         // { commitment, value, asset_type } — full canonical note
  fedIndex: null,     // number — a real federation index (federation/block-dag)
};

/** Callbacks fired (with `seed`) once the shared runtime is seeded. */
const _seedReadyCbs = [];
let _seeded = false;

/**
 * Register a callback to run once seed identifiers (turnHash, cells, note,
 * fed) are populated. Fires immediately if already seeded. Sections use this
 * to point embedded inspectors at the real seeded URIs.
 */
export function onSeedReady(cb) {
  if (_seeded) { try { cb(seed); } catch (e) { console.warn(e); } return; }
  _seedReadyCbs.push(cb);
}

function whenDreggUi() {
  return new Promise((resolve) => {
    if (window.dreggUi) return resolve(window.dreggUi);
    window.addEventListener('dreggUi:ready', (e) => resolve(e.detail), { once: true });
  });
}

async function loadWasm() {
  const wasm = await import('/pkg/dregg_wasm.js');
  await wasm.default();
  return wasm;
}

async function seedRuntime(runtime, wasm) {
  // Two agents + a real transfer turn. The turn produces a canonical
  // turn_hash used by <dregg-proof> (dregg://receipt/<hash>) and
  // <dregg-turn-debugger> (dregg://turn/<hash>).
  const alice = await runtime.createAgent('alice', 5000);
  const bob = await runtime.createAgent('bob', 0);
  seed.aliceCell = alice?.cell_id || alice?.cellId || null;
  seed.bobCell = bob?.cell_id || bob?.cellId || null;

  try {
    // Mirror the Starbridge lab transfer flow exactly: alice (balance 5000)
    // sends 100 to bob, declaring the remaining 500 as conservation excess /
    // fee burn (the genesis mint already debited per-agent fees).
    const result = await runtime.executeTurn(
      Number(alice?.agent_index ?? 0),
      [{ type: 'transfer', to: bob.cell_id, amount: 100, excess: 500 }],
      500,
    );
    seed.turnHash = result?.turn_hash || result?.receipt_hash || result?.hash || null;
  } catch (e) {
    console.warn('[playground] seed transfer turn failed', e);
  }
  // If the receipt chain is the authoritative source, fall back to its head.
  if (!seed.turnHash) {
    try {
      const receipts = runtime.listReceipts?.()?.value || [];
      const last = receipts[receipts.length - 1];
      seed.turnHash = last?.turn_hash || last?.receipt_hash || last?.hash || null;
    } catch {}
  }

  // A real note (commitment + nullifier lifecycle) via canonical wasm.
  try {
    if (wasm.create_note && runtime._handle != null) {
      const note = wasm.create_note(runtime._handle, Number(alice?.agent_index ?? 0), BigInt(100), BigInt(0));
      // create_note returns the canonical { commitment, value, asset_type }.
      // The wasm note index (get_notes) does not yet surface minted notes
      // (capability gap), so we keep the full object to feed <dregg-note data=>.
      const n = note && typeof note === 'object' && !Array.isArray(note)
        ? note
        : (Array.isArray(note) ? note[0] : null);
      seed.note = n
        ? { commitment: n.commitment, value: Number(n.value), asset_type: Number(n.asset_type) }
        : null;
      seed.noteCommitment = seed.note?.commitment || null;
      // Refresh signal-cached getNotes consumers.
      if (runtime.version) runtime.version.value++;
    }
  } catch (e) {
    console.warn('[playground] seed note failed', e);
  }
  // If create_note didn't return a commitment, pull one from the note index.
  if (!seed.noteCommitment) {
    try {
      const notes = runtime.getNotes?.(Number(alice?.agent_index ?? 0))?.value || [];
      seed.noteCommitment = notes[0]?.commitment || null;
    } catch {}
  }

  // A real federation + block so <dregg-federation> / <dregg-block-dag> have data.
  try {
    const fed = await runtime.createFederation('playground-fed', 4);
    seed.fedIndex = Number(fed?.fed_index ?? fed?.registered_index ?? 0);
    if (typeof runtime.proposeBlock === 'function') {
      await runtime.proposeBlock(seed.fedIndex, [
        `event-${Date.now().toString(36)}`,
        `height-${runtime.cursor?.value ?? 0}`,
      ]);
    }
  } catch (e) {
    console.warn('[playground] seed federation failed', e);
  }
}

/**
 * Initialize (once) the shared runtime, seed it, and start attaching it to
 * every <dregg-app> on the page (now and as sections render later).
 */
export function ensureStudioRuntime() {
  if (_readyPromise) return _readyPromise;
  _readyPromise = (async () => {
    const api = await whenDreggUi();
    const wasm = await loadWasm();
    const runtime = await createInMemoryRuntime({ wasm, signals: api });
    await seedRuntime(runtime, wasm);
    _seeded = true;
    for (const cb of _seedReadyCbs.splice(0)) {
      try { cb(seed); } catch (e) { console.warn('[playground] seed-ready cb failed', e); }
    }

    const attach = (root = document) => {
      root.querySelectorAll('dregg-app').forEach((el) => {
        if (el.runtime) return;
        el.runtime = runtime;
      });
    };
    attach();

    // Sections render lazily; keep attaching as <dregg-app> nodes appear.
    const obs = new MutationObserver((mutations) => {
      for (const m of mutations) {
        for (const node of m.addedNodes) {
          if (node.nodeType !== 1) continue;
          if (node.localName === 'dregg-app' && !node.runtime) node.runtime = runtime;
          if (node.querySelectorAll) attach(node);
        }
      }
    });
    obs.observe(document.body, { childList: true, subtree: true });

    return { runtime, wasm, seed };
  })();
  return _readyPromise;
}

/**
 * Build a small Tier-1 deeplink banner that routes to the matching dregg://
 * URI in /starbridge/. Returns an HTML string (sections inject it into their
 * header). `links` is an array of { label, uri }.
 */
export function deepLinkBanner(links, note) {
  const chips = links
    .map(
      (l) =>
        `<a class="pg-sb-link" href="/starbridge/?at=${encodeURIComponent(l.uri)}" target="_blank" rel="noreferrer">${escape(l.label)} ▸</a>`,
    )
    .join('');
  return `<div class="pg-sb-banner">
      <span class="pg-sb-banner__eyebrow">Open in Starbridge</span>
      ${chips}
      ${note ? `<span class="pg-sb-banner__note">${escape(note)}</span>` : ''}
    </div>`;
}

/**
 * Build an embedded inspector block. `inner` is the inspector custom-element
 * markup (e.g. '<dregg-proof uri="..."></dregg-proof>'). Wrapped in a
 * <dregg-app> so it shares the seeded runtime. `runtime` defaults to in-memory.
 */
export function inspectorEmbed(inner, label) {
  return `<div class="pg-embed">
      ${label ? `<div class="pg-embed__label">${escape(label)}</div>` : ''}
      <dregg-app runtime="in-memory">${inner}</dregg-app>
    </div>`;
}

function escape(s) {
  return String(s ?? '').replace(/[&<>"']/g, (c) => ({
    '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;',
  })[c]);
}
