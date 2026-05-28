// Factories section — deploy factories, create cells from them, verify provenance

import { state, notifyStateChange, navigateTo, getWasm } from '../playground.js';

export function initFactories(wasm) {
  const container = document.getElementById('section-factories');
  container.innerHTML = `
    <div class="section-header">
      <h2>Cell Factories</h2>
      <p>
        A factory is a template for creating cells with verified provenance. Deploy a factory
        with a verification key, create child cells from it, and later verify that any cell
        was produced by a known factory. This enables whitelisting and compliance patterns.
      </p>
      <span class="next-hint" data-next="private-transfers">Next: private transfers &#8594;</span>
    </div>

    <div class="controls-row">
      <button class="btn btn-primary" id="fac-deploy" ${wasm ? '' : 'disabled'}>Deploy Factory</button>
      <button class="btn btn-primary" id="fac-create-child" disabled>Create Child Cell</button>
      <button class="btn btn-primary" id="fac-verify" disabled>Verify Provenance</button>
    </div>

    <div id="fac-display"></div>
    <div id="fac-result"></div>
    <div id="fac-explainer"></div>
  `;

  if (!wasm) return;

  let factories = []; // { vk, name, children: [] }
  let allCells = [];  // { vk, fromFactory, ownerPubkey }
  const displayDiv = container.querySelector('#fac-display');
  const resultDiv = container.querySelector('#fac-result');
  const explainerDiv = container.querySelector('#fac-explainer');
  const createChildBtn = container.querySelector('#fac-create-child');
  const verifyBtn = container.querySelector('#fac-verify');

  container.querySelector('.next-hint').addEventListener('click', () => navigateTo('private-transfers'));

  function randomHex(n) {
    const bytes = new Uint8Array(n);
    crypto.getRandomValues(bytes);
    return Array.from(bytes).map(b => b.toString(16).padStart(2, '0')).join('');
  }

  function renderDisplay() {
    let html = '';

    if (factories.length > 0) {
      html += '<div class="result-panel"><div class="result-panel__header"><span class="result-panel__title">Deployed Factories</span></div><div class="result-panel__body">';
      factories.forEach((fac, i) => {
        html += `<div class="output-entry info">
          Factory "${fac.name}" | VK: ${fac.vk.slice(0, 20)}... | Children: ${fac.children.length}
        </div>`;
      });
      html += '</div></div>';
    }

    if (allCells.length > 0) {
      html += '<div class="result-panel" style="margin-top:12px;"><div class="result-panel__header"><span class="result-panel__title">Created Cells</span></div><div class="result-panel__body">';
      allCells.forEach((cell, i) => {
        const provenance = cell.fromFactory ? `from "${cell.fromFactory}"` : 'INDEPENDENT (no factory)';
        const cls = cell.fromFactory ? 'success' : 'warning';
        html += `<div class="output-entry ${cls}">
          Cell #${i}: ${cell.vk.slice(0, 20)}...
          <br>Owner: ${cell.ownerPubkey.slice(0, 16)}... | Provenance: ${provenance}
          ${cell.paramHash ? `<br>Param hash: ${cell.paramHash.slice(0, 24)}...` : ''}
        </div>`;
      });
      html += '</div></div>';
    }

    if (!html) {
      html = `<div class="result-panel"><div class="result-panel__body">
        <div class="output-entry info">Deploy a factory to begin. Factories define templates for cell creation with verified provenance.</div>
      </div></div>`;
    }

    displayDiv.innerHTML = html;
  }

  function updateButtons() {
    createChildBtn.disabled = factories.length === 0;
    verifyBtn.disabled = allCells.length === 0;
  }

  container.querySelector('#fac-deploy').addEventListener('click', () => {
    const factoryVk = randomHex(32);
    const factoryName = `factory-${factories.length + 1}`;

    const t0 = performance.now();
    factories.push({ vk: factoryVk, name: factoryName, children: [] });
    const elapsed = (performance.now() - t0).toFixed(2);

    renderDisplay();
    updateButtons();

    showExplainer(explainerDiv, {
      prover: `Deployed factory: "${factoryName}"\nVerification key: ${factoryVk.slice(0, 24)}...\n\nThis factory can now produce child cells. Each child's VK is deterministically derived from the factory VK + creation params.`,
      verifier: `Factory VK registered in the approved set\nAny cell claiming provenance from this factory can be verified in O(1)\nThe factory VK is a trust anchor`,
      delta: `Factories enable whitelisting patterns: "only accept cells from approved factories." This is useful for compliance (KYC'd cell templates), gaming (official item factories), and DAOs (member cell templates). The provenance check is a single hash comparison.`,
      timing: elapsed,
    });
  });

  createChildBtn.addEventListener('click', () => {
    const factory = factories[factories.length - 1];
    if (!factory) return;

    const ownerPubkey = randomHex(32);
    const t0 = performance.now();

    let result;
    try {
      result = wasm.create_from_factory(factory.vk, ownerPubkey, BigInt(100));
    } catch (e) {
      // No fabrication: a real derivation failure is surfaced, not simulated.
      showResult(resultDiv, 'error', `create_from_factory failed: ${e && e.message || e}`);
      return;
    }
    const elapsed = (performance.now() - t0).toFixed(2);

    const childCell = {
      vk: result.child_vk,
      fromFactory: factory.name,
      ownerPubkey,
      paramHash: result.param_hash,
    };
    factory.children.push(childCell);
    allCells.push(childCell);

    renderDisplay();
    updateButtons();

    showExplainer(explainerDiv, {
      prover: `Created child cell from "${factory.name}"\nChild VK: ${result.child_vk.slice(0, 20)}...\nParam hash: ${result.param_hash.slice(0, 20)}...\nOwner: ${ownerPubkey.slice(0, 16)}...\n\nchild_vk = derive(factory_vk, param_hash)`,
      verifier: `Child VK is deterministically derived:\n\nchild_vk = BLAKE3(\n  "dregg-factory-child-vk"\n  || factory_vk\n  || param_hash\n)\n\nThis binding is unforgeable.`,
      delta: `The child cell's VK cryptographically commits to its factory origin. You cannot forge a child VK without knowing the factory's VK. This means provenance verification is trustless — no need to query the factory or any registry.`,
      timing: elapsed,
    });
  });

  verifyBtn.addEventListener('click', () => {
    if (allCells.length === 0) return;

    // Pick a random cell to verify
    const cellIdx = allCells.length - 1;
    const cell = allCells[cellIdx];
    const factoryVks = factories.map(f => f.vk);

    const t0 = performance.now();
    let result;
    try {
      result = wasm.verify_provenance(cell.vk, JSON.stringify(factoryVks));
    } catch (e) {
      // No fabrication: surface the real verification failure.
      showResult(resultDiv, 'error', `verify_provenance failed: ${e && e.message || e}`);
      return;
    }
    const elapsed = (performance.now() - t0).toFixed(2);

    const verified = result.from_factory;
    showResult(resultDiv, verified ? 'success' : 'warning',
      `Provenance check for cell ${cell.vk.slice(0, 16)}...: ${verified ? 'FROM KNOWN FACTORY' : 'UNKNOWN ORIGIN'}`
      + (result.factory_vk ? `\nFactory: ${result.factory_vk.slice(0, 20)}...` : ''));

    showExplainer(explainerDiv, {
      prover: `Checking cell: ${cell.vk.slice(0, 16)}...\nAgainst ${factoryVks.length} known factory VK(s)\n\nResult: ${verified ? 'VERIFIED — from approved factory' : 'NOT FOUND — independent cell'}`,
      verifier: `Checked against approved factory set\n${verified ? `Matched factory: ${(result.factory_vk || '').slice(0, 16)}...` : 'No match in approved set'}\n\nVerification: O(n) where n = number of factories\n(Can be O(1) with Merkle membership proof)`,
      delta: `Provenance verification answers: "Was this cell created by an approved source?" This is the foundation for:\n- KYC compliance (only interact with KYC'd cells)\n- Game item authenticity\n- DAO membership verification\n- Supply chain provenance`,
      timing: elapsed,
    });

    // Also add an independent cell for contrast
    if (allCells.every(c => c.fromFactory)) {
      allCells.push({
        vk: randomHex(32),
        fromFactory: null,
        ownerPubkey: randomHex(32),
        paramHash: null,
      });
      renderDisplay();
    }
  });

  renderDisplay();
}

function showResult(el, type, message) {
  el.innerHTML = `<div class="result-panel">
    <div class="result-panel__body">
      <div class="output-entry ${type}">${escapeHtml(message)}</div>
    </div>
  </div>`;
}

function showExplainer(el, { prover, verifier, delta, timing }) {
  el.innerHTML = `
    <div class="explainer">
      <div class="explainer__title">What just happened</div>
      <div class="explainer__grid">
        <div class="explainer__cell explainer__cell--prover">
          <div class="explainer__cell-label">Factory / Cell</div>
          <div class="explainer__cell-content">${escapeHtml(prover)}</div>
        </div>
        <div class="explainer__cell explainer__cell--verifier">
          <div class="explainer__cell-label">Verifier</div>
          <div class="explainer__cell-content">${escapeHtml(verifier)}</div>
        </div>
        <div class="explainer__cell explainer__cell--delta">
          <div class="explainer__cell-label">Use case</div>
          <div class="explainer__cell-content">${escapeHtml(delta)}</div>
        </div>
      </div>
      <div class="explainer__timing">Operation completed in <span>${timing}ms</span></div>
    </div>
  `;
}

function escapeHtml(str) {
  return String(str).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/\n/g, '<br>');
}
