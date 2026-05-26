// dregg playground — main orchestrator
// Loads WASM, manages shared state, handles navigation, coordinates sections.

import { initOverview } from './sections/overview.js';
import { initTokens } from './sections/tokens.js';
import { initProofs } from './sections/proofs.js';
import { initMerkle } from './sections/merkle.js';
import { initDatalog } from './sections/datalog.js';
import { initNotes } from './sections/notes.js';
import { initCapabilities } from './sections/capabilities.js';
import { initCrossfed } from './sections/crossfed.js';
import { initSovereign } from './sections/sovereign.js';
import { initBearer } from './sections/bearer.js';
import { initFactories } from './sections/factories.js';
import { initPrivateTransfers } from './sections/private-transfers.js';
import { initComposition } from './sections/composition.js';
import { initGallery } from './sections/gallery.js';
import { initFederation } from './sections/federation.js';
import { initMarketplace } from './sections/marketplace.js';
import { initSandbox } from './sections/sandbox.js';
import { initEffectVm } from './sections/effect-vm.js';
import { initBlocklaceSim } from './sections/blocklace-sim.js';
import { initFullTurnProof } from './sections/full-turn-proof.js';
import { initTieredRevocation } from './sections/tiered-revocation.js';
import { initCircuitPlayground } from './sections/circuit-playground.js';

// New-world sections
import { initThemeToggle } from './sections/theme-toggle.js';
import { initBlindedQueues } from './sections/blinded-queues.js';
import { initProgrammableQueues } from './sections/programmable-queues.js';
import { initRingTrades } from './sections/ring-trades.js';
import { initInboxes } from './sections/inboxes.js';
import { initBatchExecutor } from './sections/batch-executor.js';
import { initNameservice } from './sections/nameservice.js';
import { initDelegationV2 } from './sections/delegation-v2.js';

// ============================================================================
// Global Shared State
// ============================================================================

export const state = {
  tokens: [],         // { encoded, location, attenuated, service, actions, format }
  rootKey: null,      // Uint8Array
  rootKeyHex: null,   // string
  merkleRoot: null,   // hex string
  merkleLeaves: [],   // string[]
  nullifiers: [],     // hex string[]
  receipts: [],       // proof receipt chain
  proofCount: 0,
  notes: [],          // { id, asset, amount, commitment, nullifier, owner, spent }
  capChain: [],       // capability delegation chain
  federation: {
    status: 'loading',
    nodes: 0,
    commit: null,
  },
  liveConnection: null,  // WebSocket connection to gateway
  liveMode: false,       // Whether using live network vs local WASM
};

// ============================================================================
// State Update Notification
// ============================================================================

export function notifyStateChange() {
  updateStatePanel();
  updateNavBadges();
}

function updateStatePanel() {
  // Token count
  document.getElementById('state-token-count').textContent = state.tokens.length;
  const tokenList = document.getElementById('state-token-list');
  tokenList.innerHTML = state.tokens.slice(-5).map(t =>
    `<div class="pg-state__list-item">${t.attenuated ? 'att' : 'root'}: ${t.encoded.slice(0, 20)}...</div>`
  ).join('');

  // Merkle root
  const rootEl = document.getElementById('state-merkle-root');
  rootEl.textContent = state.merkleRoot ? state.merkleRoot.slice(0, 32) + '...' : '--';

  // Nullifiers
  document.getElementById('state-nullifier-count').textContent = state.nullifiers.length;
  const nullList = document.getElementById('state-nullifier-list');
  nullList.innerHTML = state.nullifiers.slice(-3).map(n =>
    `<div class="pg-state__list-item">${n.slice(0, 24)}...</div>`
  ).join('');

  // Receipts
  document.getElementById('state-receipt-count').textContent = state.receipts.length;

  // Proofs
  document.getElementById('state-proof-count').textContent = state.proofCount;

  // Federation
  document.getElementById('state-fed-status').textContent = state.federation.status;
  document.getElementById('state-fed-nodes').textContent = state.federation.nodes || '--';
  document.getElementById('state-fed-commit').textContent =
    state.federation.commit ? state.federation.commit.slice(0, 8) : '--';
}

function updateNavBadges() {
  const tokenBadge = document.getElementById('nav-badge-tokens');
  if (state.tokens.length > 0) {
    tokenBadge.textContent = state.tokens.length;
    tokenBadge.classList.add('visible');
  } else {
    tokenBadge.classList.remove('visible');
  }

  const notesBadge = document.getElementById('nav-badge-notes');
  const unspentNotes = state.notes.filter(n => !n.spent).length;
  if (unspentNotes > 0) {
    notesBadge.textContent = unspentNotes;
    notesBadge.classList.add('visible');
  } else {
    notesBadge.classList.remove('visible');
  }
}

// ============================================================================
// Navigation
// ============================================================================

const PLAYGROUND_SCENARIOS = [
  {
    id: 'foundations',
    label: 'Foundations',
    lede: 'Core browser-local primitives: tokens, proofs, commitments, policy, notes, and delegation.',
    starbridgeHref: '/starbridge/?at=dregg://token/demo',
    starbridgeLabel: 'Open token demo in Starbridge',
    sections: ['overview', 'tokens', 'proofs', 'merkle', 'datalog', 'notes', 'capabilities'],
  },
  {
    id: 'federation',
    label: 'Federation',
    lede: 'Federated turns, sovereign exits, bearer capabilities, factories, and private transfer flows.',
    starbridgeHref: '/starbridge/?at=dregg://federation/0',
    starbridgeLabel: 'Open federation in Starbridge',
    sections: ['crossfed', 'sovereign', 'bearer', 'factories', 'private-transfers', 'composition'],
  },
  {
    id: 'apps',
    label: 'Apps',
    lede: 'Mostly self-contained application demos that compose the lower-level primitives.',
    starbridgeHref: '/starbridge/?at=dregg://app/nameservice',
    starbridgeLabel: 'Open app demo in Starbridge',
    sections: ['gallery', 'federation', 'marketplace', 'nameservice', 'delegation-v2'],
  },
  {
    id: 'proving',
    label: 'Proving',
    lede: 'Effect traces, blocklace simulation, proof composition, revocation, circuit design, and sandboxing.',
    starbridgeHref: '/starbridge/?at=dregg://turn/demo',
    starbridgeLabel: 'Open turn demo in Starbridge',
    sections: ['effect-vm', 'blocklace-sim', 'full-turn-proof', 'tiered-revocation', 'circuit-playground', 'sandbox'],
  },
  {
    id: 'queues',
    label: 'Queues',
    lede: 'Queue, inbox, ring-trade, and batch execution demos with their own visualizers.',
    starbridgeHref: '/starbridge/?at=dregg://queue/demo',
    starbridgeLabel: 'Open queue demo in Starbridge',
    sections: ['blinded-queues', 'programmable-queues', 'ring-trades', 'inboxes', 'batch-executor'],
  },
];

const SCENARIO_BY_SECTION = new Map(
  PLAYGROUND_SCENARIOS.flatMap(scenario =>
    scenario.sections.map(sectionId => [sectionId, scenario.id])
  )
);

let activeScenarioId = PLAYGROUND_SCENARIOS[0].id;

function setupNavigation() {
  const items = document.querySelectorAll('.pg-nav__item');
  const sections = document.querySelectorAll('.pg-section');

  setupScenarioTabs();

  items.forEach(item => {
    item.addEventListener('click', () => {
      const sectionId = item.dataset.section;
      activateSection(sectionId);
    });
  });

  // Handle hash-based navigation on load
  const hash = location.hash.slice(1);
  if (hash) {
    activateSection(hash, { replaceHash: false });
  } else {
    activateSection('overview', { replaceHash: false });
  }

  window.addEventListener('hashchange', () => {
    const nextHash = location.hash.slice(1);
    if (nextHash) activateSection(nextHash, { replaceHash: false });
  });
}

function setupScenarioTabs() {
  const root = document.getElementById('pg-scenarios');
  if (!root) return;

  root.innerHTML = `
    <div class="pg-scenarios__eyebrow">Scenarios</div>
    <div class="pg-scenarios__tabs" role="tablist" aria-label="Playground scenarios">
      ${PLAYGROUND_SCENARIOS.map(scenario => `
        <button
          class="pg-scenarios__tab"
          type="button"
          role="tab"
          aria-selected="false"
          data-scenario="${scenario.id}"
        >${scenario.label}</button>
      `).join('')}
    </div>
    <div class="pg-scenarios__summary" id="pg-scenario-summary"></div>
  `;

  root.querySelectorAll('[data-scenario]').forEach(tab => {
    tab.addEventListener('click', () => {
      const scenarioId = tab.dataset.scenario;
      const scenario = PLAYGROUND_SCENARIOS.find(s => s.id === scenarioId);
      if (!scenario) return;
      setActiveScenario(scenarioId);
      activateSection(scenario.sections[0]);
    });
  });
}

function setActiveScenario(scenarioId) {
  const scenario = PLAYGROUND_SCENARIOS.find(s => s.id === scenarioId) || PLAYGROUND_SCENARIOS[0];
  activeScenarioId = scenario.id;
  const sectionSet = new Set(scenario.sections);

  document.querySelectorAll('.pg-scenarios__tab').forEach(tab => {
    const selected = tab.dataset.scenario === scenario.id;
    tab.classList.toggle('active', selected);
    tab.setAttribute('aria-selected', selected ? 'true' : 'false');
  });

  document.querySelectorAll('.pg-nav__item').forEach(item => {
    item.hidden = !sectionSet.has(item.dataset.section);
  });

  const summary = document.getElementById('pg-scenario-summary');
  if (summary) {
    summary.innerHTML = `
      <p>${scenario.lede}</p>
      <a href="${scenario.starbridgeHref}" target="_blank" rel="noreferrer">${scenario.starbridgeLabel}</a>
    `;
  }

  const hint = document.getElementById('pg-nav-hint');
  if (hint) {
    hint.textContent = `${scenario.label}: ${scenario.sections.length} demos`;
  }
}

function activateSection(sectionId, options = {}) {
  const { replaceHash = true } = options;
  const items = document.querySelectorAll('.pg-nav__item');
  const sections = document.querySelectorAll('.pg-section');
  const section = document.getElementById(`section-${sectionId}`);
  if (!section) return false;

  const scenarioId = SCENARIO_BY_SECTION.get(sectionId);
  if (scenarioId && scenarioId !== activeScenarioId) {
    setActiveScenario(scenarioId);
  } else if (!document.querySelector('.pg-scenarios__tab.active')) {
    setActiveScenario(activeScenarioId);
  }

  items.forEach(i => i.classList.remove('active'));
  sections.forEach(s => s.classList.remove('active'));
  const target = document.querySelector(`[data-section="${sectionId}"]`);
  if (target) target.classList.add('active');
  section.classList.add('active');
  if (replaceHash) {
    history.replaceState(null, '', `#${sectionId}`);
  }
  return true;
}

export function navigateTo(sectionId) {
  activateSection(sectionId);
}

// ============================================================================
// WASM Loading
// ============================================================================

let wasm = null;

async function loadWasm() {
  const statusEl = document.getElementById('wasm-status');
  try {
    const { default: init, ...exports } = await import('../pkg/dregg_wasm.js');
    await init();
    wasm = exports;
    statusEl.textContent = 'wasm ready';
    statusEl.classList.add('ready');
    return exports;
  } catch (e) {
    statusEl.textContent = 'wasm error';
    statusEl.classList.add('error');
    console.error('[dregg] WASM load failed:', e);
    return null;
  }
}

export function getWasm() {
  return wasm;
}

// ============================================================================
// Federation Discovery
// ============================================================================

async function fetchFederation() {
  try {
    const resp = await fetch('../discovery.json');
    if (!resp.ok) throw new Error(`HTTP ${resp.status}`);
    const data = await resp.json();
    state.federation.status = 'online';
    state.federation.nodes = data.federation?.length || 0;
    state.federation.commit = data.commit || null;
    state.federation.gateway = data.gateway || null;
  } catch {
    state.federation.status = 'offline';
  }
  notifyStateChange();
}

// ============================================================================
// Live Network Connection
// ============================================================================

/**
 * Connect to the live gateway node via WebSocket.
 * When connected, operations can be routed to the live network instead of
 * running locally in WASM.
 */
export async function connectToLiveNetwork() {
  // Fetch discovery to get gateway address
  let gatewayWs = 'wss://devnet.dregg.fg-goose.online/ws';
  try {
    const resp = await fetch('../discovery.json');
    if (resp.ok) {
      const data = await resp.json();
      if (data.gateway?.ws) {
        gatewayWs = data.gateway.ws;
      }
    }
  } catch {
    // Fall back to hardcoded gateway address
  }

  if (state.liveConnection) {
    state.liveConnection.close();
    state.liveConnection = null;
  }

  return new Promise((resolve, reject) => {
    const ws = new WebSocket(gatewayWs);

    ws.onopen = () => {
      state.liveConnection = ws;
      state.liveMode = true;
      console.log('[dregg] Connected to live network:', gatewayWs);
      notifyStateChange();
      resolve(ws);
    };

    ws.onclose = () => {
      state.liveConnection = null;
      state.liveMode = false;
      console.log('[dregg] Disconnected from live network');
      notifyStateChange();
    };

    ws.onerror = (err) => {
      console.error('[dregg] WebSocket error:', err);
      state.liveMode = false;
      notifyStateChange();
      reject(err);
    };

    ws.onmessage = (event) => {
      try {
        const msg = JSON.parse(event.data);
        handleLiveMessage(msg);
      } catch (e) {
        console.warn('[dregg] Failed to parse live message:', e);
      }
    };
  });
}

/** Disconnect from the live network. */
export function disconnectFromLiveNetwork() {
  if (state.liveConnection) {
    state.liveConnection.close();
    state.liveConnection = null;
  }
  state.liveMode = false;
  notifyStateChange();
}

/** Handle incoming messages from the live gateway. */
function handleLiveMessage(msg) {
  switch (msg.type) {
    case 'state_update':
      // Sync federation state from live node
      if (msg.merkle_root) state.merkleRoot = msg.merkle_root;
      if (msg.nullifiers) state.nullifiers = msg.nullifiers;
      break;
    case 'new_block':
      // A new attested root was produced
      state.federation.status = 'online';
      break;
    case 'receipt':
      state.receipts.push(msg.receipt);
      break;
    default:
      console.log('[dregg] Unknown live message type:', msg.type);
  }
  notifyStateChange();
}

// ============================================================================
// State Reset
// ============================================================================

function setupReset() {
  document.getElementById('btn-reset-state').addEventListener('click', () => {
    state.tokens = [];
    state.rootKey = null;
    state.rootKeyHex = null;
    state.merkleRoot = null;
    state.merkleLeaves = [];
    state.nullifiers = [];
    state.receipts = [];
    state.proofCount = 0;
    state.notes = [];
    state.capChain = [];
    notifyStateChange();
  });
}

// ============================================================================
// Boot
// ============================================================================

async function main() {
  setupNavigation();
  setupReset();

  // Fetch federation status in parallel with WASM load
  fetchFederation();
  const wasmExports = await loadWasm();

  // Initialize all sections (they render their own DOM)
  initOverview();
  initTokens(wasmExports);
  initProofs(wasmExports);
  initMerkle(wasmExports);
  initDatalog(wasmExports);
  initNotes(wasmExports);
  initCapabilities(wasmExports);
  initCrossfed(wasmExports);
  initSovereign(wasmExports);
  initBearer(wasmExports);
  initFactories(wasmExports);
  initPrivateTransfers(wasmExports);
  initComposition(wasmExports);
  initGallery(wasmExports);
  initFederation(wasmExports);
  initMarketplace(wasmExports);
  initSandbox(wasmExports);
  initEffectVm(wasmExports);
  initBlocklaceSim(wasmExports);
  initFullTurnProof(wasmExports);
  initTieredRevocation(wasmExports);
  initCircuitPlayground(wasmExports);
  initThemeToggle();
  initBlindedQueues(wasmExports);
  initProgrammableQueues(wasmExports);
  initRingTrades(wasmExports);
  initInboxes(wasmExports);
  initBatchExecutor(wasmExports);
  initNameservice(wasmExports);
  initDelegationV2(wasmExports);

  // Initial state render
  notifyStateChange();
}

main();
