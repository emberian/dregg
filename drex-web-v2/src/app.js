// app.js — the DrEX v2 product frontend (Preact + htm + signals).
//
// The primary DrEX terminal (the v1 :8781 demo's endpoint surface is fully
// ported to this server; v1 remains as the legacy scripted walkthrough). The
// extension (window.dregg) is the identity + wallet + signer; this app is the
// orchestrator. What is wired REAL end-to-end here:
//   • the app SHELL (header, wallet handshake, node probe, engine report);
//   • the TIER-DIAL as a first-class control — Open/Shielded/Dark, with the
//     "what each viewer sees" honest display, reusing the session's viz
//     (drex-web/drex-viz.js ringGraph) to redact the REAL cleared ring per tier;
//   • the OPEN-tier multilateral ring order-entry wired to the REAL /clear
//     (drex_clear: solver.rs + verified_settle.rs), built by REAL entry;
//   • the SHIELDED Cert-F circulation clearing wired to the REAL /clear-shielded
//     (fhegg_clear: PDHG + Cert-F + the verified AIR gate), and the REAL
//     reveal-nothing STARK at /prove-shielded (cert_f_prove) — both with honest
//     not-built fallbacks when a binary is absent (never faked);
//   • the SEALED-BID commit→reveal two-phase ceremony routed through the REAL
//     extension (dregg.sealedBid.commit/reveal → real keccak256 + EIP-712 +
//     secp256k1), with the on-chain escrow post labelled deploy-gated;
//   • the live-node SETTLE with the full proof-receipt read back from the node
//     (turn hash, STARK proof, finality, per-trader balances);
//   • a session RECEIPT LEDGER — every completed action's real result, one row
//     per move, because every move here IS a receipt.
// Dark tier and the not-yet-wired mechanisms are PRESENT as honestly-labelled
// controls; nothing not-yet-live is shown as live.
import { h, render } from 'preact';
import { signal, computed } from '@preact/signals';
import htm from 'htm';
import { clearOpen, clearShielded, proveShielded, settle, nodeStatus, engines } from './api.js';
import * as ext from './extension.js';
import { TIERS, MECHANISMS, COMPOSITION, ASSETS } from './model.js';
import { ringGraph } from '../../drex-web/drex-viz.js';

const html = htm.bind(h);
const SHOW = (s) => ({ dangerouslySetInnerHTML: { __html: s } });

// ── app state ──
const activeTier = signal('open');
const activeMech = signal('ring');
const entryMode  = signal('direct');   // 'direct' | 'sealed'
const theme      = signal(document.documentElement.getAttribute('data-theme') || 'dark');
const book = signal([
  { id: 1, trader: 'Ada',  offerAsset: 'GOLD', offerAmount: 100, wantAsset: 'ART',  wantMin: 10, priority: 3 },
  { id: 2, trader: 'Bram', offerAsset: 'ART',  offerAmount: 50,  wantAsset: 'WINE', wantMin: 20, priority: 1 },
  { id: 3, trader: 'Cyl',  offerAsset: 'WINE', offerAmount: 80,  wantAsset: 'GOLD', wantMin: 40, priority: 2 },
]);
const draft = signal({ trader: '', offerAsset: 'SILVER', offerAmount: 30, wantAsset: 'PEARL', wantMin: 5, priority: 4 });
const draftErr = signal(null);
const clearing = signal(null);
const clearBusy = signal(false);
const settleState = signal(null);
const shielded2 = signal(null);           // /clear-shielded result
const shieldedBusy = signal(false);
const worldProof = signal(null);           // /prove-shielded result
const proveBusy = signal(false);
const node = signal({ up: null });
const engineMap = signal(null);            // GET /engines — which binary backs each route
const wallet = signal({ status: 'unknown' });     // unknown|absent|detected|connected|error
const sealed = signal({ phase: 'idle' });          // idle|committed|revealed|error
const yourOrder = signal({ trader: 'You', offerAsset: 'SILVER', offerAmount: 30, wantAsset: 'PEARL', wantMin: 5, priority: 4 });
const receipts = signal([]);               // the session receipt ledger — real results only

const tierById = (id) => TIERS.find(t => t.id === id);
const mechById = (id) => MECHANISMS.find(m => m.id === id);
const activeMechObj = computed(() => mechById(activeMech.value));

// Append a row to the session receipt ledger. Only called with REAL endpoint
// results — the ledger is a view of what actually happened, never a synthesis.
function logReceipt(kind, ok, headline, detail) {
  const t = new Date();
  const ts = t.toTimeString().slice(0, 8);
  receipts.value = [...receipts.value, { id: receipts.value.length + 1, ts, kind, ok, headline, detail }];
}

// Convert a REAL drex_clear result into the shape drex-viz.ringGraph expects
// (assets=nodes, orders parallel to solverCert edges/flows/caps). Faithful — it
// reads the cleared allocations, it does not synthesize a book.
function toVizRing(res) {
  const allocs = (res.allocations || []).filter(a => !a.rested);
  if (!allocs.length) return null;
  const assets = [...new Set(allocs.flatMap(a => [a.sentAsset, a.recvAsset]))];
  const idx = (a) => assets.indexOf(a);
  return {
    assets,
    orders: allocs.map(a => ({ trader: a.trader, offerAsset: a.sentAsset, wantAsset: a.recvAsset, offerAmount: a.offer, wantMin: a.wantMin })),
    solverCert: { edges: allocs.map(a => [idx(a.sentAsset), idx(a.recvAsset)]), f: allocs.map(a => Number(a.sent)), c: allocs.map(a => Number(a.offer)) },
  };
}
const vizRing = computed(() => (clearing.value && clearing.value.ring ? toVizRing(clearing.value) : null));

function toggleTheme() {
  const next = theme.value === 'dark' ? 'light' : 'dark';
  document.documentElement.setAttribute('data-theme', next);
  theme.value = next;
}

// ── header ──
function Header() {
  const n = node.value, w = wallet.value;
  const wlabel = w.status === 'connected' ? 'wallet: cipherclerk · connected' + (w.evmAddress ? ' · ' + w.evmAddress.slice(0, 6) + '…' : '')
    : w.status === 'detected' ? 'wallet: cipherclerk · detected'
    : w.status === 'absent' ? 'wallet: extension not installed'
    : 'wallet: detecting…';
  return html`
    <header class="hdr">
      <div class="brand">
        <span class="logo">◇</span>
        <div><div class="title">DrEX</div><div class="sub">one exchange · a privacy dial · one verified kernel · every move is a receipt</div></div>
      </div>
      <div class="pills">
        <span class=${'pill ' + (n.up === true ? 'live' : n.up === false ? 'warn' : '')}>
          ${n.up === true ? 'node: live @ ' + (n.node || '').replace(/^https?:\/\//, '') : n.up === false ? 'node: offline · local clear only' : 'node: probing…'}</span>
        <span class=${'pill ' + (w.status === 'connected' ? 'live' : w.status === 'absent' || w.status === 'error' ? 'warn' : '')}>${wlabel}</span>
        <button class="themetog" onClick=${toggleTheme} title="toggle light/dark" aria-label="toggle theme">${theme.value === 'dark' ? '☀' : '◑'}</button>
      </div>
    </header>`;
}

// ── wallet handshake — connect to the installed extension ──
function WalletPanel() {
  const w = wallet.value;
  if (w.status === 'connected') {
    return html`<section class="card wallet ok">
      <div class="card-h">Wallet — Dragon's Egg Cipherclerk <span class="badge live">connected</span></div>
      <div class="wrow">dregg identity authorized for <span class="mono">drex.trade</span>${w.evmAddress ? html` · EVM leg <span class="mono">${w.evmAddress}</span>` : ''}</div>
      <div class="hint">one identity does both the dregg-native order-turn and the on-chain escrow leg. Every signature is gated by the extension's confirm-intent popup.</div>
    </section>`;
  }
  if (w.status === 'absent') {
    return html`<section class="card wallet warn">
      <div class="card-h">Wallet — extension required</div>
      <p>The Dragon's Egg Cipherclerk (<span class="mono">./extension</span>) is not installed in this browser, so there is no <span class="mono">window.dregg</span> to sign with.</p>
      <p class="honest">The terminal refuses to fake a wallet. Sealed-bid signing and dregg-native order-turns route through the installed extension; without it those actions are unavailable. The Open-tier clear below still runs (the matcher does not need your key).</p>
      <button class="ghost" onClick=${detectWallet}>Re-check for the extension</button>
    </section>`;
  }
  // unknown / detected / error
  return html`<section class="card wallet">
    <div class="card-h">Wallet — Dragon's Egg Cipherclerk</div>
    <p>${w.status === 'detected' ? 'Extension detected. Connect to authorize DrEX trading and pull your identity.' : w.status === 'error' ? ('Connect failed: ' + (w.error || 'unknown')) : 'Detecting the installed extension…'}</p>
    <button class="primary" disabled=${w.status === 'unknown'} onClick=${connectWallet}>Connect the cipherclerk</button>
  </section>`;
}

async function detectWallet() {
  wallet.value = { status: 'unknown' };
  const d = await ext.detect();
  wallet.value = d.installed ? { status: 'detected' } : { status: 'absent' };
}
async function connectWallet() {
  try {
    const r = await ext.connect();
    wallet.value = { status: 'connected', evmAddress: r.evmAddress, auth: r.auth };
  } catch (e) {
    wallet.value = { status: 'error', error: String(e && e.message || e) };
  }
}

// ── the tier dial — first-class; live viewer-lens over the REAL cleared ring ──
function TierDial() {
  const t = tierById(activeTier.value);
  const vr = vizRing.value;
  theme.value; // subscribe: the lens SVG reads the current theme at render time
  return html`
    <section class="card dial">
      <div class="card-h">Privacy tier <span class="hint">— the dial over one kernel; the guarantee never moves, only what the world sees</span></div>
      <div class="dial-row">
        ${TIERS.slice().sort((a, b) => a.order - b.order).map(tier => html`
          <button class=${'tierbtn ' + (activeTier.value === tier.id ? 'on ' : '') + (tier.live ? '' : 'preview')}
            onClick=${() => (activeTier.value = tier.id)}
            title=${tier.live ? tier.tagline : 'preview — ' + (tier.deployDeps || []).join('; ')}>
            <span class="tname">${tier.name}</span>
            <span class=${'grade g-' + tier.grade.toLowerCase()}>${tier.grade}</span>
          </button>`)}
      </div>
      <div class="dial-body">
        <div class="lens">
          ${vr ? html`<div class="lenssvg" ...${SHOW(ringGraph(vr, activeTier.value))}></div>`
               : html`<div class="lens-empty">Clear a batch below to see the same ring through each viewer's eyes — Open shows every flow, Shielded blurs the amounts, Dark seals the orders.</div>`}
          ${!t.live && html`<div class="preview-tag">PREVIEW — not live with real money. ${t.grade}.</div>`}
        </div>
        <div class="tier-detail">
          <div class="tagline">${t.tagline}</div>
          <div class="posture">${t.posture}</div>
          <div class="whosees">
            <div><b>world sees</b><span>${t.whoSees.world}</span></div>
            <div><b>solver sees</b><span>${t.whoSees.solver}</span></div>
            <div><b>you see</b><span>${t.whoSees.you}</span></div>
          </div>
          ${!t.live && html`<div class="deploydeps">Deploy-gated: ${(t.deployDeps || []).join(' · ')}</div>`}
        </div>
      </div>
    </section>`;
}

// ── mechanism rail ──
function MechanismRail() {
  return html`
    <section class="card rail">
      <div class="card-h">Mechanism <span class="hint">— the 8-mechanism family; each has its own order shape</span></div>
      <div class="mech-list">
        ${MECHANISMS.map(m => {
          const runnable = m.live && m.tier === activeTier.value;
          return html`<button class=${'mechbtn ' + (activeMech.value === m.id ? 'on ' : '') + (runnable ? '' : 'muted')}
            onClick=${() => (activeMech.value = m.id)} title=${m.blurb}>
            <span class="mname">${m.name}</span>
            <span class=${'mtier tier-' + m.tier}>${m.tier}</span>
            ${!m.live && html`<span class="soon">${m.endpoint ? 'engine live · other tier' : 'not wired'}</span>`}
          </button>`;
        })}
      </div>
    </section>`;
}

// ── order entry — dispatch on the active mechanism ──
function OrderEntry() {
  const m = activeMechObj.value;
  if (!m) return null;
  if (m.id === 'ring') return html`<${RingEntry} />`;
  if (m.id === 'circulation') return html`<${ShieldedEntry} />`;
  return html`
    <section class="card entry">
      <div class="card-h">Order entry — ${m.name}</div>
      <div class="notlive">
        <p><b>${m.name}</b> takes a <b>${m.orderShape}</b>-shaped order.</p>
        <p class="blurb">${m.blurb}</p>
        <p class="honest">Its order-entry form is part of the phased architecture (see the overhaul plan).
          ${m.endpoint ? html`A real engine serves it at <span class="mono">${m.endpoint}</span>, but at the <b>${m.tier}</b> tier — not the live Open path.` : 'It is not wired to a live endpoint yet.'}
          The live end-to-end flows today are the Open ring clear and the shielded Cert-F circulation.</p>
        <button class="ghost" onClick=${() => { activeTier.value = 'open'; activeMech.value = 'ring'; }}>→ Go to the live Open ring clear</button>
      </div>
    </section>`;
}

// ── the shared batch editor: the order book + the draft-order row ──
function BookEditor() {
  const d = draft.value;
  const err = draftErr.value;
  const setD = (k, v) => { draft.value = { ...draft.value, [k]: v }; if (draftErr.value) draftErr.value = null; };
  const addOrder = () => {
    const t = (d.trader || '').trim();
    if (!t) return (draftErr.value = 'name the trader first');
    if (book.value.some(o => o.trader.toLowerCase() === t.toLowerCase())) return (draftErr.value = `"${t}" is already in the batch — one order per trader`);
    if (!(+d.offerAmount > 0)) return (draftErr.value = 'offer amount must be > 0');
    if (!(+d.wantMin >= 0)) return (draftErr.value = 'want-min must be ≥ 0');
    if (d.offerAsset === d.wantAsset) return (draftErr.value = 'offer and want must be different assets');
    const id = Math.max(0, ...book.value.map(o => o.id)) + 1;
    book.value = [...book.value, { id, ...d, trader: t, offerAmount: +d.offerAmount, wantMin: +d.wantMin, priority: Math.max(1, +d.priority || 1) }];
    draft.value = { ...draft.value, trader: '' };
    draftErr.value = null;
  };
  const rm = (id) => (book.value = book.value.filter(o => o.id !== id));
  return html`
    <div>
      <div class="book">
        ${book.value.map(o => html`<div class="ord" key=${o.id}>
          <span class="who">${o.trader}</span>
          <span class="leg">offer <b>${o.offerAmount} ${o.offerAsset}</b> · want ≥ <b>${o.wantMin} ${o.wantAsset}</b></span>
          <span class="prio">p${o.priority}</span>
          <button class="x" onClick=${() => rm(o.id)} aria-label=${'remove ' + o.trader}>✕</button></div>`)}
        ${book.value.length === 0 && html`<div class="empty">no orders — add one below</div>`}
      </div>
      <div class="draft">
        <input class="in trader" placeholder="trader" value=${d.trader} onInput=${e => setD('trader', e.target.value)} onKeyDown=${e => e.key === 'Enter' && addOrder()} />
        <label>offer<input class="in num" type="number" min="1" value=${d.offerAmount} onInput=${e => setD('offerAmount', e.target.value)} /></label>
        <${AssetSel} value=${d.offerAsset} onChange=${v => setD('offerAsset', v)} />
        <span class="arrow">→</span>
        <label>want ≥<input class="in num" type="number" min="0" value=${d.wantMin} onInput=${e => setD('wantMin', e.target.value)} /></label>
        <${AssetSel} value=${d.wantAsset} onChange=${v => setD('wantAsset', v)} />
        <label>prio<input class="in num sm" type="number" min="1" value=${d.priority} onInput=${e => setD('priority', e.target.value)} /></label>
        <button class="add" onClick=${addOrder}>+ add</button>
      </div>
      ${err && html`<div class="drafterr" role="alert">${err}</div>`}
    </div>`;
}

// ── the ring entry: a mode toggle between the direct open clear and the ──
// ── sealed-bid two-phase ceremony (routed through the extension) ──
function RingEntry() {
  return html`
    <section class="card entry">
      <div class="card-h">Order entry — Open multilateral ring <span class="badge live">LIVE · /clear</span></div>
      <div class="modetog">
        <button class=${'mtog ' + (entryMode.value === 'direct' ? 'on' : '')} onClick=${() => (entryMode.value = 'direct')}>Direct clear</button>
        <button class=${'mtog ' + (entryMode.value === 'sealed' ? 'on' : '')} onClick=${() => (entryMode.value = 'sealed')}>Sealed-bid (commit → reveal)</button>
      </div>
      ${entryMode.value === 'direct' ? html`<${DirectBook} />` : html`<${SealedBidFlow} />`}
    </section>`;
}

function DirectBook() {
  const eng = engineMap.value;
  const where = eng && eng.clear && eng.clear.where;
  return html`
    <div>
      <p class="entry-lead">Build the batch with real orders. Each is an intent: <i>offer</i> an asset, <i>want</i> ≥ a minimum of another. The real
        matcher (Johnson circuits + Shapley–Scarf TTC) finds the multilateral ring no pairwise swap can close; the verified kernel settles it conserving + all-or-nothing.</p>
      <${BookEditor} />
      <div class="actions">
        <button class="primary" disabled=${clearBusy.value || book.value.length < 2} onClick=${runClear}>${clearBusy.value ? html`<span class="spin"></span> clearing…` : 'Clear the batch →'}</button>
        <span class="hint">real POST /clear · ${book.value.length} order(s)${where ? ' · matcher @ ' + where : ''}</span>
      </div>
      ${clearing.value && html`<${ClearingResult} res=${clearing.value} />`}
    </div>`;
}

// ── the SHIELDED entry: the same batch through the real fhEgg engine ──
// (/clear-shielded: PDHG circulation + Cert-F + the verified AIR gate), and the
// reveal-nothing STARK (/prove-shielded) as a separate, seconds-long action.
function ShieldedEntry() {
  const eng = engineMap.value;
  const fheggReady = !eng || eng.clearShielded.ready;   // unknown → let the server answer honestly
  const proveReady = !eng || eng.proveShielded.ready;
  return html`
    <section class="card entry">
      <div class="card-h">Order entry — Cert-F circulation clearing
        ${fheggReady ? html`<span class="badge live">ENGINE LIVE · /clear-shielded</span>` : html`<span class="badge gated">engine not built</span>`}
        <span class="badge tier">shielded tier — labelled preview</span>
      </div>
      <p class="entry-lead">The same batch, cleared as a <b>convex circulation</b> (PDHG) with a primal-dual <b>Cert-F certificate</b> the
        verified AIR re-checks — partial fills in [0,1], volume-maximizing, machine-checked fair. The certificate here is the
        <b>solver's plaintext view</b>; hiding it from the world is the separate reveal-nothing STARK below.</p>
      <${BookEditor} />
      <div class="actions">
        <button class="primary" disabled=${shieldedBusy.value || book.value.length < 2} onClick=${runShieldedClear2}>${shieldedBusy.value ? html`<span class="spin"></span> clearing…` : 'Clear shielded →'}</button>
        <span class="hint">real POST /clear-shielded · fhegg_clear${eng ? ' @ ' + eng.clearShielded.where : ''}</span>
      </div>
      ${!fheggReady && html`<div class="buildhint">honest fallback — the engine binary is not built on this box. Build it:
        <span class="mono">cargo build --release --bin fhegg_clear</span> (in <span class="mono">fhegg-solver/</span>)</div>`}
      ${shielded2.value && html`<${ShieldedResult} res=${shielded2.value} />`}
      ${shielded2.value && !shielded2.value.error && html`
        <div class="provezone">
          <div class="pz-h">Reveal-nothing — prove it without showing it</div>
          <p class="entry-lead">The clearing above is the solver's view. <b>Prove</b> runs the same batch into a real dregg STARK
            (BabyBear + FRI over the Cert-F AIR): the world gets the proof + one public scalar (wᵀf) — never the flows, prices, or slacks.
            The witness stays server-side; the redaction is structural. Real proving work: seconds, not a click.</p>
          <div class="actions">
            <button class="primary" disabled=${proveBusy.value} onClick=${runProveShielded}>${proveBusy.value ? html`<span class="spin"></span> proving (real STARK — a moment)…` : 'Prove reveal-nothing STARK →'}</button>
            <span class="hint">real POST /prove-shielded · cert_f_prove${eng ? ' @ ' + eng.proveShielded.where : ''}</span>
          </div>
          ${!proveReady && html`<div class="buildhint">honest fallback — the prover binary is not built on this box. Build it:
            <span class="mono">cargo build --release -p dregg-circuit-prove --bin cert_f_prove</span></div>`}
          ${worldProof.value && html`<${WorldView} r=${worldProof.value} />`}
        </div>`}
    </section>`;
}

// ── the sealed-bid two-phase ceremony, routed through the extension ──
function SealedBidFlow() {
  const w = wallet.value, o = yourOrder.value, s = sealed.value;
  const setO = (k, v) => (yourOrder.value = { ...yourOrder.value, [k]: v });
  if (w.status !== 'connected') {
    return html`<div class="notlive">
      <p class="honest">The sealed-bid commit→reveal ceremony signs through the installed extension (keccak256 commitment + EIP-712 <span class="mono">SealedBid</span>/<span class="mono">RevealBid</span> + secp256k1). Connect the cipherclerk first.</p>
      <button class="primary" disabled=${w.status === 'absent'} onClick=${connectWallet}>Connect the cipherclerk</button>
      ${w.status === 'absent' && html`<p class="hint">extension not installed — sealed-bid is unavailable in this browser (honest fallback; no faked signature).</p>`}
    </div>`;
  }
  return html`
    <div>
      <p class="entry-lead">A sealed bid hides your order until a reveal window. <b>Commit</b>: publish a binding-but-hiding keccak256 commitment, escrow-signed by the extension. <b>Reveal</b>: publish the opening; anyone re-hashes to check it binds. Both phases are separate, extension-signed actions.</p>
      <div class="yourorder">
        <span>your order:</span>
        <label>offer<input class="in num" type="number" min="1" value=${o.offerAmount} onInput=${e => setO('offerAmount', +e.target.value)} /></label>
        <${AssetSel} value=${o.offerAsset} onChange=${v => setO('offerAsset', v)} />
        <span class="arrow">→</span>
        <label>want ≥<input class="in num" type="number" min="0" value=${o.wantMin} onInput=${e => setO('wantMin', +e.target.value)} /></label>
        <${AssetSel} value=${o.wantAsset} onChange=${v => setO('wantAsset', v)} />
      </div>
      <div class="phases">
        <div class=${'phase ' + (s.phase !== 'idle' ? 'done' : 'active')}>
          <div class="ph-h"><span class="ph-n">1</span> Commit — hide the order</div>
          <button class="primary sm" disabled=${s.busy} onClick=${doCommit}>${s.busy && s.phase === 'idle' ? 'signing…' : 'Commit (extension signs)'}</button>
          ${s.commit && html`<div class="sealbox">
            <div class="srow"><b>commitment</b> <span class="mono">${s.commit.commitment.slice(0, 34)}…</span></div>
            <div class="srow"><b>escrow sig</b> <span class="mono">${(s.commit.signature || '').slice(0, 34)}…</span> <span class="chip">EIP-712 SealedBid</span></div>
            <div class="srow hint">the order is hidden — only H(bidder‖order‖salt) is public. Posting to an on-chain SealedAuction escrow is deploy-gated (no contract deployed).</div>
          </div>`}
        </div>
        <div class=${'phase ' + (s.phase === 'revealed' ? 'done' : s.phase === 'committed' ? 'active' : '')}>
          <div class="ph-h"><span class="ph-n">2</span> Reveal — open + check it binds</div>
          <button class="primary sm" disabled=${s.phase !== 'committed' || s.busy} onClick=${doReveal}>${s.busy && s.phase === 'committed' ? 'signing…' : 'Reveal (extension signs)'}</button>
          ${s.reveal && html`<div class="sealbox">
            <div class="srow"><b>opening</b> offer ${s.reveal.order.offerAmount} ${s.reveal.order.offerAsset} → want ≥ ${s.reveal.order.wantMin} ${s.reveal.order.wantAsset}</div>
            <div class="srow"><b>binds commitment</b> <span class=${s.reveal.bindsCommitment ? 'ok' : 'no'}>${s.reveal.bindsCommitment ? '✔ verified (re-hash matches)' : '✗'}</span></div>
            <div class="srow hint">the extension re-hashed the opening — the same check an on-chain revealBid runs. The revealed order can now join the open batch and clear.</div>
            <button class="ghost sm" onClick=${addRevealedToBook}>Add revealed order to the batch →</button>
          </div>`}
        </div>
      </div>
      ${s.error && html`<div class="result err">Sealed-bid error: ${s.error}</div>`}
    </div>`;
}

const AUCTION_ID = 1;
async function doCommit() {
  sealed.value = { phase: 'idle', busy: true };
  try {
    const order = { ...yourOrder.value };
    const commit = await ext.sealedCommit({ auctionId: AUCTION_ID, order });
    sealed.value = { phase: 'committed', commit, order };
    logReceipt('sealed-commit', true, 'commitment ' + (commit.commitment || '').slice(0, 18) + '…', 'EIP-712 SealedBid, extension-signed');
  } catch (e) {
    sealed.value = { phase: 'error', error: String(e && e.message || e) };
  }
}
async function doReveal() {
  const prev = sealed.value;
  sealed.value = { ...prev, busy: true };
  try {
    const reveal = await ext.sealedReveal({ auctionId: AUCTION_ID });
    sealed.value = { ...prev, phase: 'revealed', reveal, busy: false };
    logReceipt('sealed-reveal', !!reveal.bindsCommitment, reveal.bindsCommitment ? 'opening binds commitment ✔' : 'opening does NOT bind ✗', 'extension re-hash check');
  } catch (e) {
    sealed.value = { ...prev, phase: 'error', error: String(e && e.message || e), busy: false };
  }
}
function addRevealedToBook() {
  const o = (sealed.value.reveal && sealed.value.reveal.order) || yourOrder.value;
  const id = Math.max(0, ...book.value.map(x => x.id)) + 1;
  book.value = [...book.value, { id, trader: 'You', offerAsset: o.offerAsset, offerAmount: +o.offerAmount, wantAsset: o.wantAsset, wantMin: +o.wantMin, priority: +o.priority || 3 }];
  entryMode.value = 'direct';
}

function AssetSel({ value, onChange }) {
  return html`<select class="in sel" value=${value} onChange=${e => onChange(e.target.value)}>${ASSETS.map(a => html`<option value=${a}>${a}</option>`)}</select>`;
}

const bookOrders = () => book.value.map(({ trader, offerAsset, offerAmount, wantAsset, wantMin, priority }) =>
  ({ trader, offerAsset, offerAmount: +offerAmount, wantAsset, wantMin: +wantMin, priority: +priority }));

// ── run the real clear / shielded clear / prove / settle ──
async function runClear() {
  clearBusy.value = true; clearing.value = null; settleState.value = null;
  try { clearing.value = await clearOpen(bookOrders()); }
  catch (e) { clearing.value = { error: String(e && e.message || e) }; }
  finally { clearBusy.value = false; }
  const r = clearing.value;
  if (r && !r.error) logReceipt('clear', !!r.ring, r.ring ? `${r.ring.participants.length}-party ring cleared` : 'no ring — book rests', 'drex_clear · verified settle');
  else if (r) logReceipt('clear', false, 'matcher error', r.error);
}
async function runShieldedClear2() {
  shieldedBusy.value = true; shielded2.value = null; worldProof.value = null;
  try { shielded2.value = await clearShielded(bookOrders()); }
  catch (e) { shielded2.value = { error: String(e && e.message || e) }; }
  finally { shieldedBusy.value = false; }
  const r = shielded2.value;
  if (r && !r.error) {
    const c = r.certificate || {};
    logReceipt('clear-shielded', !!c.valid, `Cert-F ${c.valid ? 'valid' : 'INVALID'} · wᵀf = ${c.clearedVolume}`, 'fhegg_clear · PDHG + verified AIR gate');
  } else if (r) logReceipt('clear-shielded', false, 'engine unavailable', r.error);
}
async function runProveShielded() {
  proveBusy.value = true; worldProof.value = null;
  const t0 = performance.now();
  let r;
  try { r = await proveShielded(bookOrders()); }
  catch (e) { r = { ok: false, error: String(e && e.message || e) }; }
  r.wallMs = Math.round(performance.now() - t0);   // set BEFORE the signal assignment (assignment triggers the render)
  worldProof.value = r;
  proveBusy.value = false;
  if (r.ok) logReceipt('prove', !!r.verify, `STARK ${r.verify ? 'verifies' : 'FAILED'} · ${r.proofBytes} bytes · ${r.proveMs} ms`, 'cert_f_prove · reveal-nothing world view');
  else logReceipt('prove', false, 'prover unavailable', r.error);
}
async function runSettle() {
  if (!clearing.value || !clearing.value.ring) return;
  settleState.value = { busy: true };
  try { settleState.value = await settle(clearing.value); }
  catch (e) { settleState.value = { nodeUp: false, error: String(e && e.message || e) }; }
  const s = settleState.value;
  if (s && s.accepted) {
    const proven = !!(s.proof && s.proof.present);
    logReceipt('settle', proven, (proven ? 'settled · proven' : 'committed · proof pending') + ' · turn ' + (s.turnHash || '').slice(0, 14) + '…', 'live node ' + (s.node || ''));
  } else if (s && !s.busy) logReceipt('settle', false, s.nodeUp === false ? 'no live node — clear kept local' : 'node up · not landed (' + (s.stage || 'settle') + ')', s.error || '');
}

function ClearingResult({ res }) {
  if (res.error) return html`<div class="result err"><b>Matcher error.</b> ${res.error}
    ${res.stderr && html`<div class="mono errdetail">${res.stderr}</div>`}
    <div class="hint">the server shells to the real drex_clear binary — check <span class="mono">GET /engines</span> for where it runs (local target/ vs the build host over ssh)</div></div>`;
  const ring = res.ring, cleared = res.allocations || [];
  const live = cleared.filter(a => !a.rested), rested = cleared.filter(a => a.rested);
  const color = { GOLD: '#f0c14b', ART: '#bc8cff', WINE: '#f85149', SILVER: '#8b949e', PEARL: '#58a6ff' };
  return html`<div class="result">
    ${!ring ? html`<div class="noring">No clearing ring over this book — every order rests. <span class="hint">${res.provenance || ''}</span></div>` : html`
      <div class="res-h">Cleared · real solver <span class=${'chip ' + (res.ok ? 'ok' : 'warn')}>${res.ok ? 'fair · conserving · no-mint' : 'partial'}</span></div>
      <div class="ring"><span class="rlabel">ring (${ring.participants.length}-party${res.twoCycles === 0 ? ', genuinely multilateral' : ''}):</span>
        ${ring.legs.map(l => html`<span class="rleg">${l.fromTrader}→${l.toTrader} ${l.amount} ${l.asset}</span>`)}</div>
      <div class="allocs">
        ${live.map(a => html`<div class="alloc"><span class="who">${a.trader}</span><span class="leg">sent ${a.sent} ${a.sentAsset} · got <b>${a.received} ${a.recvAsset}</b> (≥${a.wantMin})</span><span class=${a.ir && a.budget ? 'ok' : 'no'}>${a.ir && a.budget ? '✔' : '✗'}</span></div>`)}
        ${rested.map(a => html`<div class="alloc rest"><span class="who">${a.trader}</span><span class="leg">rests — no match this batch</span><span>·</span></div>`)}
      </div>
      ${res.conservation && res.conservation.length > 0 && html`<div class="cons"><div class="hint">per-asset conservation (in = out) — from the verified settle:</div>
        ${res.conservation.map(c => html`<div class="consrow"><span>${c.asset}: ${c.in} in = ${c.out} out</span><span class=${c.ok ? 'ok' : 'no'}>${c.ok ? '✔' : '✗'}</span><div class="bar"><span style=${'width:100%;background:' + (color[c.asset] || '#58a6ff')}></span></div></div>`)}</div>`}
      ${res.reject && html`<div class="reject">reject-polarity: drain a sender one short → leg ${res.reject.refusedAt} REFUSED by the verified kernel; whole ring aborts. <span class="hint">over-debit is provably impossible, not merely avoided.</span></div>`}
      <div class="settle-line">
        <button class="ghost" disabled=${settleState.value && settleState.value.busy} onClick=${runSettle}>${settleState.value && settleState.value.busy ? html`<span class="spin"></span> settling…` : 'Settle on the live node →'}</button>
        <span class="hint">lands the ring as per-trader Transfer turns (solo dev node; no on-chain settle yet)</span>
      </div>
      ${settleState.value && !settleState.value.busy && html`<${SettleResult} s=${settleState.value} />`}`}
  </div>`;
}

// ── the shielded clearing result: the solver's certificate as a checkable object ──
function ShieldedResult({ res }) {
  if (res.error) return html`<div class="result err"><b>Shielded engine unavailable.</b> ${res.error}
    ${res.stderr && html`<div class="mono errdetail">${res.stderr}</div>`}</div>`;
  const c = res.certificate || {}, air = res.air || {}, t = res.tamper || {}, st = res.starkStage || {};
  const check = (ok, label, val) => html`<div class=${'chk ' + (ok ? 'ok' : 'no')}><span class="ci">${ok ? '✓' : '✕'}</span><span class="cl">${label}</span><span class="cv">${val}</span></div>`;
  return html`<div class="result">
    <div class="res-h">Cleared · real fhEgg engine <span class="chip">${res.nodes} assets · ${res.edges} orders · T=${res.iters} iters</span></div>
    <div class="allocs">
      ${(res.orders || []).map(o => html`<div class="alloc"><span class="who">${o.trader}</span>
        <span class="leg">${o.offerAsset}→${o.wantAsset}: cleared <b>${o.clearedFlow}</b> of ${o.offerAmount} (want ≥${o.wantMin})</span>
        <span class=${o.filled ? 'ok' : 'restdot'}>${o.filled ? '✔' : '·'}</span></div>`)}
    </div>
    <div class="certbox">
      <div class="hint">Cert-F primal-dual certificate — the fair-batch gate the verified AIR checks:</div>
      <div class="certgrid">
        ${check(c.conserves, 'conservation ‖Af‖∞ = 0', c.conservationResidual)}
        ${check(c.gapOk !== false && c.dualityGap !== undefined, 'duality gap ≤ ε', 'wᵀf ' + c.clearedVolume + ' vs cᵀs ' + c.dualObjective + ' · gap ' + c.dualityGap)}
        ${check(c.primalBoxed !== false, 'primal boxed 0 ≤ f ≤ c', c.primalBoxed === false ? 'no' : 'yes')}
        ${check(c.sNonneg !== false, 'dual slack s ≥ 0', c.sNonneg === false ? 'no' : 'yes')}
        ${check(c.dualFeasible !== false, 'dual feasible', c.dualFeasible === false ? 'no' : 'yes')}
        ${check(c.valid, 'certificate valid', c.valid ? 'PROVED-sound checks pass' : 'INVALID')}
      </div>
    </div>
    <div class="gate">
      <div class="gcol ok">
        <div class="gh">✓ honest certificate</div>
        <div class="gb">the verified AIR (${air.constraints} constraints · ${air.terms} terms · ${air.witnessCells} witness cells) <b class="ok">${air.accept ? 'ACCEPTS' : 'rejects (BUG)'}</b></div>
        <div class="gm">the exact n+4m+1 rows <span class="mono">Market/CertF.lean</span> proves sound</div>
      </div>
      <div class="gcol no">
        <div class="gh">✕ tampered certificate</div>
        <div class="gb">${t.what || 'tamper'} → the AIR <b class=${!t.accept ? 'ok' : 'no'}>${!t.accept ? 'REJECTS' : 'accepted (BUG)'}</b></div>
        <div class="gm">violated: <span class="mono">${(t.violated || []).join(', ') || '—'}</span> — a cheat can't even be built</div>
      </div>
    </div>
    <div class="hint">who sees what: ${(res.tiers || []).map(x => html`<span class="tiersee"><b>${x.tier}</b> ${x.sees}</span>`)}</div>
    ${st.status && html`<div class="hint">STARK-ZK stage: ${st.status} — hides ${(st.hides || []).join(', ')}. Run the prove below to produce the world view.</div>`}
  </div>`;
}

// ── the reveal-nothing world view: what the world gets, and only that ──
function WorldView({ r }) {
  if (!r.ok) return html`<div class="result err"><b>Reveal-nothing prover: honest fallback.</b> ${r.error}${r.stage ? ' (stage: ' + r.stage + ')' : ''}
    ${r.stderr && html`<div class="mono errdetail">${r.stderr}</div>`}</div>`;
  const p = r.program || {}, tr = r.trace || {};
  const rem = r.remaining || {};
  return html`<div class="worldview">
    <div class="wv-boundary">
      <div class="wv-col solver"><div class="wv-h">the solver saw</div>
        <div class="wv-b">every order, every flow f, the dual prices π, the slacks s — plaintext, server-side, to clear fast.</div>
        <div class="wv-flows">${book.value.map(o => html`<div class="wv-flow"><span class="who">${o.trader}</span><span class="mono blurred" aria-hidden="true">${o.offerAsset}→${o.wantAsset} · ██ units</span><span class="chip">hidden</span></div>`)}</div>
      </div>
      <div class="wv-col world"><div class="wv-h">the world sees</div>
        <div class="wv-rows">
          <div class="wv-row"><span class="k">fair batch cleared</span><span class="v"><span class=${r.conserves ? 'ok' : 'no'}>${r.conserves ? '✔ conservation held' : '✗'}</span></span></div>
          <div class="wv-row"><span class="k">cleared volume wᵀf</span><span class="v num"><b>${r.clearedVolume}</b> <span class="hint">(the ONLY witness-derived scalar; public inputs = [${(r.publicInputs || []).join(', ')}])</span></span></div>
          <div class="wv-row"><span class="k">proof verifies</span><span class="v"><span class=${r.verify ? 'ok' : 'no'}>${r.verify ? '✔ verify_cert_f → true' : '✗ did NOT verify'}</span></span></div>
          <div class="wv-row"><span class="k">proof</span><span class="v num">${r.proofBytes} bytes · descriptor <span class="mono">${r.descriptor || 'cert-f'}</span> · trace width ${tr.width} (${tr.valueBits}-bit range gadget)</span></div>
          <div class="wv-row"><span class="k">public shape</span><span class="v num">${p.nodes} assets, ${p.edges} orders, ε=${p.epsilon} <span class="hint">(A, w, c ride as public descriptor constants)</span></span></div>
          <div class="wv-row"><span class="k">latency</span><span class="v num"><b>${r.proveMs} ms</b> prove · ${r.verifyMs} ms verify · ${r.wallMs} ms wall</span></div>
        </div>
      </div>
    </div>
    <div class="hint wv-honest">honest scope — hidden here means hidden from the PUBLIC OUTPUT (this proof): ${(r.hides || []).join(' · ')}.
      Full input-privacy still needs: ${rem.noteCommitmentMatching}. ZK floor: ${rem.zkFloor}.</div>
  </div>`;
}

// ── the settle result: the full proof-receipt, read back from the node ──
function SettleResult({ s }) {
  // GENUINELY offline: the node did not answer /status. Only this — a reachable
  // node that merely could not complete the settle is NEVER shown as "offline".
  if (s.nodeUp === false) return html`<div class="settle warn"><b>No live node reachable</b> (${s.error || 'offline'}). The clearing above is the real verified solver, but it did not land on a node this run. <span class="hint">start one: dregg-node run --port 8420 --enable-faucet --prove-turns</span></div>`;
  // Reachable node, settle did not complete — name the stage and the real cause,
  // and keep it VISIBLY distinct from a finalized settlement (this is not it).
  if (!s.accepted) return html`<div class="settle warn"><b>Node is up — settlement not landed</b> (${s.stage || 'settle'}): ${s.error || 'unknown'}.${s.faucetDisabled ? html` <span class="hint">this node runs without a faucet; fund the settle operator out of band, or point the terminal at a --enable-faucet dev node.</span>` : ''} <span class="hint">The clearing above is the real verified solver and stands; it was not finalized on-chain this run.</span></div>`;
  const proof = s.proof || {}, rc = s.receipt || {};
  const proven = !!(proof.present || rc.hasProof);
  const exempt = !proven && (rc.proofStatus || s.proofStatus) === "not_required";
  const h = s.turnHash || '';
  const st = s.settle || {};
  const copyHash = (e) => {
    try { navigator.clipboard && navigator.clipboard.writeText(h); } catch (_e) {}
    const b = e.currentTarget; b.textContent = 'copied ✓'; setTimeout(() => { b.textContent = 'copy'; }, 1400);
  };
  return html`<div class=${'proofcard ' + (proven ? 'proven' : 'pending')}>
    <div class="pc-crest">
      <div class=${'pc-seal ' + (proven ? 'ok' : '')} aria-hidden="true">${proven ? '✓' : '…'}</div>
      <div>
        <div class="pc-title">${proven ? html`Settled · <span class="pc-proven">proven</span>` : exempt ? 'Committed · signature only' : 'Committed · unattested'}</div>
        <div class="pc-say">${proven ? 'The batch cleared as real per-trader turns on the live node — and math itself signed the receipt.' : exempt ? 'Coordination turn: signature attestation only, no validity proof' : (s.proofNote || 'the async prove_pool has not attached the STARK yet — committed-but-unattested, surfaced honestly')}</div>
      </div>
    </div>
    <div class="pc-rows">
      <div class="pc-r"><span class="k">turn hash</span><span class="v mono hashv">${h}<button class="copybtn" onClick=${copyHash}>copy</button></span></div>
      ${proven && html`<div class="pc-r"><span class="k">proof</span><span class="v">${proof.mode === 'stark_full_turn' ? `full-turn STARK proof · ${proof.len} bytes` : `witnessed receipt · prove_pool (witnesses ${proof.witnessCount || rc.witnessCount || 1})`}</span></div>`}
      <div class="pc-r"><span class="k">finality</span><span class="v">${rc.finality || '—'} · ${rc.computronsUsed ?? '—'} computrons · ${rc.actionCount ?? '—'} action(s) · executor-signed ${String(rc.executorSigned ?? '—')}</span></div>
      <div class="pc-r"><span class="k">ledger</span><span class="v mono">${(rc.preState || '').slice(0, 16)}… → ${(rc.postState || '').slice(0, 16)}…</span></div>
      <div class="pc-r"><span class="k">node</span><span class="v">${s.node || ''} · operator <span class="mono">${(s.operator || '').slice(0, 14)}…</span></span></div>
    </div>
    ${(s.perTrader || []).length > 0 && html`<div class="pc-traders">
      <div class="hint">per-trader allocations settled as REAL transfers — balances read back from the node${st.scaled ? html` · <span class="warntext">settled at scale ${st.scale} (devnet computron-budget envelope; true cleared amounts kept)</span>` : ''}:</div>
      ${s.perTrader.map(t => html`<div class="pc-tr"><span class="who">${t.trader}</span>
        <span class="leg mono">${(t.cell || '').slice(0, 12)}…</span>
        <span class="leg">got <b>${t.settled}</b>${t.settled !== t.received ? ` (of ${t.received} cleared)` : ''} ${t.recvAsset}</span>
        <span class="num">balance ${t.balance ?? '—'}</span></div>`)}
    </div>`}
    ${proven && html`<div class="pc-recheck">Don't take our word for it — <b>anyone can re-run this check.</b> The proof is fetchable at
      <span class="mono">/api/turn/${h.slice(0, 10)}…/proof</span> and re-verifies against the committed turn. The guarantee comes from the math, not from us.</div>`}
  </div>`;
}

// ── the session receipt ledger — every move is a receipt ──
function ReceiptLedger() {
  const rs = receipts.value;
  if (!rs.length) return null;
  return html`<section class="card ledger">
    <div class="card-h">Session receipts <span class="hint">— every action's real result, one row per move; nothing synthesized</span></div>
    <div class="ledger-rows">
      ${rs.slice().reverse().map(r => html`<div class="lrow" key=${r.id}>
        <span class="lts mono">${r.ts}</span>
        <span class=${'lkind lk-' + r.kind}>${r.kind}</span>
        <span class=${'lhead ' + (r.ok ? '' : 'warntext')}>${r.headline}</span>
        <span class="ldetail hint">${r.detail}</span>
      </div>`)}
    </div>
  </section>`;
}

function CompositionStrip() {
  return html`<section class="card comp">
    <div class="card-h">Composition journey <span class="hint">— deposit → shield → clear → settle (Phase 3; each stage's honest grade)</span></div>
    <div class="comp-row">
      ${COMPOSITION.map((c, i) => html`<div class="comp-stage"><div class="cstage-h">${i + 1}. ${c.name}</div><div class="cverb">${c.verb}</div><div class=${'cgrade ' + (c.live ? 'live' : 'gated')}>${c.grade}</div></div>${i < COMPOSITION.length - 1 ? html`<span class="comp-arrow">→</span>` : ''}`)}
    </div>
  </section>`;
}

function App() {
  return html`<div class="app">
    <${Header} />
    <${WalletPanel} />
    <${TierDial} />
    <div class="grid"><${MechanismRail} /><${OrderEntry} /></div>
    <${ReceiptLedger} />
    <${CompositionStrip} />
    <footer class="foot">DrEX v2 — the primary terminal (the :8781 demo remains as the legacy scripted walkthrough). Real end-to-end: the Open ring clear
    (solver.rs + verified_settle.rs), the shielded Cert-F circulation + reveal-nothing STARK (fhegg_clear + cert_f_prove, honest not-built
    fallbacks), the sealed-bid ceremony (extension-signed), and the solo-node settle with the proof-receipt read back from the node. Dark tier
    and the remaining mechanisms are honestly-labelled previews — not live with real money — and wire in per the phased plan
    (docs/deos/DREX-FRONTEND-OVERHAUL.md).</footer>
  </div>`;
}

render(html`<${App} />`, document.getElementById('root'));

nodeStatus().then(s => (node.value = s)).catch(() => (node.value = { up: false }));
engines().then(e => (engineMap.value = e)).catch(() => {});
detectWallet();
