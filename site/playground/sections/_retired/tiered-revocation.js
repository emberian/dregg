/**
 * Tiered Revocation Section — add revocations, watch hot->settled,
 * prove non-membership interactively.
 *
 * Demonstrates:
 * - Hot tier (recent revocations, immediate effect)
 * - Settled tier (rolled into Merkle tree at epoch boundary)
 * - Non-membership proofs (prove credential is NOT revoked)
 */

import { state, notifyStateChange, getWasm } from '../playground.js';

let hotTier = [];       // Recent revocations (not yet settled)
let settledTier = [];   // Revocations merged into tree
let currentEpoch = 0;
let treeRoot = '0'.repeat(64);
let proofLog = [];

export function initTieredRevocation(wasm) {
  const section = document.getElementById('section-tiered-revocation');
  if (!section) return;

  section.innerHTML = `
    <div class="pg-section__header">
      <h2>Tiered Revocation</h2>
      <p>Revocations go through two tiers: hot (immediate, per-block) and settled (merged into Merkle tree at epoch boundaries). Prove non-membership to show a credential is still valid.</p>
    </div>

    <div class="trev-layout">
      <div class="trev-controls">
        <div class="trev-controls__row">
          <input type="text" id="trev-revoke-input" placeholder="Credential ID to revoke (hex or number)" class="pg-input" style="flex: 1;">
          <button class="pg-btn pg-btn--primary" id="trev-revoke-btn">Revoke</button>
          <button class="pg-btn pg-btn--accent" id="trev-settle-btn">Settle Epoch</button>
        </div>
        <div class="trev-controls__row">
          <input type="text" id="trev-prove-input" placeholder="Credential ID to prove non-membership" class="pg-input" style="flex: 1;">
          <button class="pg-btn pg-btn--primary" id="trev-prove-btn">Prove Non-Membership</button>
        </div>
      </div>

      <div class="trev-tiers">
        <div class="trev-tier">
          <div class="trev-tier__header">
            <span class="trev-tier__title">Hot Tier</span>
            <span class="trev-tier__badge" id="trev-hot-count">0</span>
          </div>
          <div class="trev-tier__body" id="trev-hot-list">
            <div class="pg-empty">No revocations in hot tier.</div>
          </div>
        </div>
        <div class="trev-tier">
          <div class="trev-tier__header">
            <span class="trev-tier__title">Settled Tier (Epoch ${currentEpoch})</span>
            <span class="trev-tier__badge" id="trev-settled-count">0</span>
          </div>
          <div class="trev-tier__body" id="trev-settled-list">
            <div class="pg-empty">No settled revocations yet.</div>
          </div>
          <div class="trev-tier__root">
            <span class="trev-tier__root-label">Tree Root:</span>
            <span class="trev-tier__root-value" id="trev-tree-root">${treeRoot.slice(0, 16)}...</span>
          </div>
        </div>
      </div>

      <div class="trev-proofs">
        <div class="trev-proofs__header">
          <span>Non-Membership Proofs</span>
          <span class="trev-proofs__count" id="trev-proof-count">0</span>
        </div>
        <div class="trev-proofs__body" id="trev-proof-log">
          <div class="pg-empty">Prove that a credential is not revoked.</div>
        </div>
      </div>
    </div>
  `;

  wireControls(wasm);
}

function wireControls(wasm) {
  document.getElementById('trev-revoke-btn').addEventListener('click', () => {
    const input = document.getElementById('trev-revoke-input');
    const credId = input.value.trim();
    if (credId) {
      revokeCredential(credId);
      input.value = '';
    }
  });

  document.getElementById('trev-settle-btn').addEventListener('click', () => {
    settleEpoch(wasm);
  });

  document.getElementById('trev-prove-btn').addEventListener('click', () => {
    const input = document.getElementById('trev-prove-input');
    const credId = input.value.trim();
    if (credId) {
      proveNonMembership(credId, wasm);
      input.value = '';
    }
  });
}

function revokeCredential(credId) {
  // Normalize to hex
  const hexId = /^[0-9a-fA-F]+$/.test(credId) ? credId.padStart(8, '0') : hashString(credId);

  // Check if already revoked
  if (hotTier.find(r => r.id === hexId) || settledTier.find(r => r.id === hexId)) {
    return; // Already revoked
  }

  hotTier.push({
    id: hexId,
    revokedAt: currentEpoch,
    block: state.receipts?.length || 0,
    settled: false,
  });

  renderTiers();
}

function settleEpoch(wasm) {
  if (hotTier.length === 0) return;

  // Move hot tier into settled
  hotTier.forEach(r => {
    r.settled = true;
    settledTier.push(r);
  });

  // Recompute tree root (simulated)
  treeRoot = computeTreeRoot(settledTier);
  currentEpoch++;
  hotTier = [];

  renderTiers();
}

function proveNonMembership(credId, wasm) {
  const hexId = /^[0-9a-fA-F]+$/.test(credId) ? credId.padStart(8, '0') : hashString(credId);

  // Check if it IS revoked
  const inHot = hotTier.find(r => r.id === hexId);
  const inSettled = settledTier.find(r => r.id === hexId);

  const startTime = performance.now();

  if (inHot || inSettled) {
    // Cannot prove non-membership — it IS revoked
    proofLog.unshift({
      credId: hexId,
      result: 'REVOKED',
      tier: inHot ? 'hot' : 'settled',
      epoch: currentEpoch,
      time: performance.now() - startTime,
    });
  } else {
    // Generate non-membership proof
    const proof = {
      credId: hexId,
      result: 'NOT_REVOKED',
      tier: 'none',
      epoch: currentEpoch,
      treeRoot: treeRoot,
      hotChecked: hotTier.length,
      settledChecked: settledTier.length,
      proofSize: 64 + Math.ceil(Math.log2(settledTier.length + 1)) * 32,
      time: performance.now() - startTime,
    };
    proofLog.unshift(proof);
    state.proofCount++;
    notifyStateChange();
  }

  renderProofLog();
}

function renderTiers() {
  // Hot tier
  const hotList = document.getElementById('trev-hot-list');
  document.getElementById('trev-hot-count').textContent = hotTier.length;
  if (hotTier.length === 0) {
    hotList.innerHTML = '<div class="pg-empty">No revocations in hot tier.</div>';
  } else {
    hotList.innerHTML = hotTier.map(r => `
      <div class="trev-entry trev-entry--hot">
        <span class="trev-entry__id">${r.id}</span>
        <span class="trev-entry__meta">epoch ${r.revokedAt}</span>
      </div>
    `).join('');
  }

  // Settled tier
  const settledList = document.getElementById('trev-settled-list');
  document.getElementById('trev-settled-count').textContent = settledTier.length;
  document.getElementById('trev-tree-root').textContent = treeRoot.slice(0, 16) + '...';

  // Update epoch label
  const tierHeader = document.querySelector('.trev-tier:nth-child(2) .trev-tier__title');
  if (tierHeader) tierHeader.textContent = `Settled Tier (Epoch ${currentEpoch})`;

  if (settledTier.length === 0) {
    settledList.innerHTML = '<div class="pg-empty">No settled revocations yet.</div>';
  } else {
    settledList.innerHTML = settledTier.slice(-10).reverse().map(r => `
      <div class="trev-entry trev-entry--settled">
        <span class="trev-entry__id">${r.id}</span>
        <span class="trev-entry__meta">settled at epoch ${r.revokedAt}</span>
      </div>
    `).join('');
  }
}

function renderProofLog() {
  const log = document.getElementById('trev-proof-log');
  document.getElementById('trev-proof-count').textContent = proofLog.length;

  if (proofLog.length === 0) {
    log.innerHTML = '<div class="pg-empty">Prove that a credential is not revoked.</div>';
    return;
  }

  log.innerHTML = proofLog.slice(0, 10).map(p => {
    const isRevoked = p.result === 'REVOKED';
    return `
      <div class="trev-proof-entry ${isRevoked ? 'trev-proof-entry--revoked' : 'trev-proof-entry--valid'}">
        <span class="trev-proof-entry__id">${p.credId}</span>
        <span class="trev-proof-entry__badge">${p.result}</span>
        ${!isRevoked ? `<span class="trev-proof-entry__meta">checked ${p.hotChecked} hot + ${p.settledChecked} settled, proof: ${p.proofSize}B</span>` : `<span class="trev-proof-entry__meta">found in ${p.tier} tier</span>`}
      </div>
    `;
  }).join('');
}

function computeTreeRoot(entries) {
  // Simulated Merkle root computation
  let hash = 0;
  entries.forEach(e => {
    for (let i = 0; i < e.id.length; i++) {
      hash = ((hash << 5) - hash) + e.id.charCodeAt(i);
      hash |= 0;
    }
  });
  return Math.abs(hash).toString(16).padStart(64, '0');
}

function hashString(str) {
  let hash = 0;
  for (let i = 0; i < str.length; i++) {
    hash = ((hash << 5) - hash) + str.charCodeAt(i);
    hash |= 0;
  }
  return Math.abs(hash).toString(16).padStart(8, '0');
}
