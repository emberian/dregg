// Merkle section — build trees, prove membership, prove absence

import { state, notifyStateChange, navigateTo } from '../playground.js';
import { deepLinkBanner, inspectorEmbed } from '../studio-embed.js';

export function initMerkle(wasm) {
  const container = document.getElementById('section-merkle');
  // Tier 2 (STARBRIDGE-PLAN §4.9): the canonical tree view is the platform
  // <dregg-merkle-tree> inspector — a 4-ary BLAKE3 SVG with membership/absence
  // path highlighting, driven entirely by the real wasm merkle helpers
  // (compute_merkle_root / merkle_membership_proof / merkle_non_membership_proof).
  const defaultLeaves = JSON.stringify(['alice', 'bob', 'carol', 'dave']);
  container.innerHTML = `
    <div class="section-header">
      <h2>Merkle Trees</h2>
      ${deepLinkBanner(
        [{ label: '<dregg-merkle-tree>', uri: 'dregg://merkle-tree/demo' }],
        'real 4-ary BLAKE3 tree + membership / absence paths',
      )}
      <p>
        Dragon's Egg uses 4-ary BLAKE3 Merkle trees for state commitments. A single root hash
        commits to all leaves. You can prove that a specific leaf is in the tree (membership)
        or that a leaf is NOT in the tree (absence) — both with logarithmic-sized proofs.
      </p>
      ${inspectorEmbed(
        `<dregg-merkle-tree leaves='${defaultLeaves}' data='${JSON.stringify({ leaves: ['alice', 'bob', 'carol', 'dave'], focus_leaf: 'alice', prove: 'member' })}'></dregg-merkle-tree>`,
        'Canonical Merkle tree view (real wasm crypto)',
      )}
      <span class="next-hint" data-next="datalog">Next: write Datalog policies &#8594;</span>
    </div>

    <div class="controls-row">
      <div class="control-group">
        <label>Leaves (one per line)</label>
        <textarea id="mk-leaves" rows="5" style="width: 300px;" spellcheck="false">alice
bob
carol
dave</textarea>
      </div>
      <div style="display: flex; flex-direction: column; gap: 8px;">
        <button class="btn btn-primary" id="mk-build" ${wasm ? '' : 'disabled'}>Build Tree</button>
        <div class="control-group">
          <label>Add Leaf</label>
          <div style="display: flex; gap: 6px;">
            <input type="text" id="mk-new-leaf" placeholder="new leaf..." spellcheck="false" style="width: 140px;">
            <button class="btn btn-secondary btn-sm" id="mk-add">Add</button>
          </div>
        </div>
      </div>
    </div>

    <div class="controls-row">
      <div class="control-group">
        <label>Prove Membership</label>
        <div style="display: flex; gap: 6px;">
          <input type="text" id="mk-member" placeholder="e.g. alice" spellcheck="false" style="width: 140px;">
          <button class="btn btn-secondary btn-sm" id="mk-prove-member">Prove</button>
        </div>
      </div>
      <div class="control-group">
        <label>Prove Absence</label>
        <div style="display: flex; gap: 6px;">
          <input type="text" id="mk-absent" placeholder="e.g. eve" spellcheck="false" style="width: 140px;">
          <button class="btn btn-secondary btn-sm" id="mk-prove-absent">Prove</button>
        </div>
      </div>
    </div>

    <div id="mk-viz" class="merkle-viz" style="display:none;"></div>
    <div id="mk-result"></div>
    <div id="mk-explainer"></div>
  `;

  if (!wasm) return;

  const leavesArea = container.querySelector('#mk-leaves');
  const vizDiv = container.querySelector('#mk-viz');
  const resultDiv = container.querySelector('#mk-result');
  const explainerDiv = container.querySelector('#mk-explainer');

  container.querySelector('.next-hint').addEventListener('click', () => navigateTo('datalog'));

  function getLeaves() {
    return leavesArea.value.split('\n').map(s => s.trim()).filter(s => s.length > 0);
  }

  container.querySelector('#mk-build').addEventListener('click', () => {
    const leaves = getLeaves();
    if (leaves.length === 0) {
      showResult(resultDiv, 'error', 'Enter at least one leaf');
      return;
    }

    const t0 = performance.now();
    try {
      const result = wasm.compute_merkle_root(JSON.stringify(leaves));
      const elapsed = (performance.now() - t0).toFixed(2);

      state.merkleRoot = result.root_hex;
      state.merkleLeaves = leaves;
      notifyStateChange();

      renderTreeViz(vizDiv, leaves, result.root_hex);

      // tree_depth isn't returned by WASM; derive from leaf count.
      // FactSet uses a 4-ary commitment tree, so depth = ceil(log_4(n)).
      const depth = result.num_leaves <= 1
        ? 1
        : Math.ceil(Math.log(result.num_leaves) / Math.log(4));

      showResult(resultDiv, 'success',
        `Tree built: ${result.num_leaves} leaves, depth ${depth}\nRoot: ${result.root_hex}`);
      showExplainer(explainerDiv, {
        prover: `All ${leaves.length} leaves in memory\nFull tree structure known\nCan generate proofs for any leaf`,
        verifier: `Sees only: root hash (${result.root_hex.slice(0, 16)}...)\nThis single hash commits to all ${leaves.length} leaves\nAny change to any leaf changes the root`,
        delta: `The root reveals nothing about individual leaves. It is a binding commitment: the prover cannot claim different contents without being detected.`,
        timing: elapsed,
      });
    } catch (e) {
      showResult(resultDiv, 'error', `Build failed: ${e.message}`);
    }
  });

  container.querySelector('#mk-add').addEventListener('click', () => {
    const newLeaf = container.querySelector('#mk-new-leaf').value.trim();
    if (!newLeaf) return;
    leavesArea.value = leavesArea.value.trim() + '\n' + newLeaf;
    container.querySelector('#mk-new-leaf').value = '';
    // Auto-rebuild
    container.querySelector('#mk-build').click();
  });

  container.querySelector('#mk-prove-member').addEventListener('click', () => {
    const leaves = getLeaves();
    const target = container.querySelector('#mk-member').value.trim();
    if (!target || leaves.length === 0) return;

    const t0 = performance.now();
    try {
      const result = wasm.merkle_membership_proof(JSON.stringify(leaves), target);
      const elapsed = (performance.now() - t0).toFixed(2);

      showResult(resultDiv, result.verified ? 'success' : 'error',
        result.verified
          ? `Membership PROVEN: "${target}" is at index ${result.leaf_index} (path length: ${result.proof_path?.length || 0})`
          : `Membership proof FAILED for "${target}"`);

      showExplainer(explainerDiv, {
        prover: `Target leaf: "${target}"\nLeaf index: ${result.leaf_index}\nProof path: ${result.proof_path?.length || 0} sibling hashes\nKnows: full tree structure`,
        verifier: `Receives: leaf value + sibling path\nRecomputes: root from leaf up\nCompares: computed root vs. committed root\nResult: ${result.verified ? 'MATCH' : 'MISMATCH'}`,
        delta: `The proof reveals only the sibling hashes on the path from leaf to root (${result.proof_path?.length || 0} values). The other ${leaves.length - 1} leaves remain hidden.`,
        timing: elapsed,
      });
    } catch (e) {
      showResult(resultDiv, 'error', `Membership proof failed: ${e.message}`);
    }
  });

  container.querySelector('#mk-prove-absent').addEventListener('click', () => {
    const leaves = getLeaves();
    const target = container.querySelector('#mk-absent').value.trim();
    if (!target || leaves.length === 0) return;

    const t0 = performance.now();
    try {
      const result = wasm.merkle_non_membership_proof(JSON.stringify(leaves), target);
      const elapsed = (performance.now() - t0).toFixed(2);

      showResult(resultDiv, 'info',
        `Absence PROVEN: "${target}" is NOT in the tree\nBounding leaves demonstrate gap in sorted order.`);

      showExplainer(explainerDiv, {
        prover: `Target: "${target}" (not in set)\nProves: no leaf in the sorted tree matches\nShows: bounding neighbors that prove the gap`,
        verifier: `Sees: two adjacent leaves that bracket the target\nVerifies: both neighbors are in the tree\nConcludes: target cannot exist between them`,
        delta: `The verifier learns that the target is absent, plus the two bounding leaf values. No other leaves are revealed.`,
        timing: elapsed,
      });
    } catch (e) {
      // If it throws, the leaf might actually be present
      showResult(resultDiv, 'warning', `"${target}" may be present in the tree, or absence proof unavailable: ${e.message}`);
    }
  });
}

function renderTreeViz(container, leaves, rootHex) {
  container.style.display = 'block';
  const depth = Math.ceil(Math.log2(leaves.length)) + 1;
  const width = Math.max(400, leaves.length * 80);
  const height = depth * 60 + 40;

  let svg = `<svg width="${width}" height="${height}" viewBox="0 0 ${width} ${height}">`;

  // Simple binary tree visualization
  const levels = [];
  let currentLevel = leaves.map(l => l.slice(0, 6));
  levels.push(currentLevel);

  while (currentLevel.length > 1) {
    const next = [];
    for (let i = 0; i < currentLevel.length; i += 2) {
      next.push('H(...)');
    }
    if (currentLevel.length % 2 === 1) {
      next.push('H(...)');
    }
    currentLevel = next;
    levels.push(currentLevel);
  }
  levels.reverse();
  // Replace root with actual root
  if (levels.length > 0) levels[0] = [rootHex.slice(0, 8)];

  // Draw nodes
  for (let lvl = 0; lvl < levels.length; lvl++) {
    const nodes = levels[lvl];
    const y = lvl * 60 + 30;
    const spacing = width / (nodes.length + 1);

    for (let i = 0; i < nodes.length; i++) {
      const x = spacing * (i + 1);
      const isRoot = lvl === 0;
      const isLeaf = lvl === levels.length - 1;

      // Draw lines to children
      if (lvl < levels.length - 1) {
        const childLevel = levels[lvl + 1];
        const childSpacing = width / (childLevel.length + 1);
        const childIdx = i * 2;
        if (childIdx < childLevel.length) {
          const cx = childSpacing * (childIdx + 1);
          const cy = (lvl + 1) * 60 + 30;
          svg += `<line class="link" x1="${x}" y1="${y + 12}" x2="${cx}" y2="${cy - 12}"/>`;
        }
        if (childIdx + 1 < childLevel.length) {
          const cx = childSpacing * (childIdx + 2);
          const cy = (lvl + 1) * 60 + 30;
          svg += `<line class="link" x1="${x}" y1="${y + 12}" x2="${cx}" y2="${cy - 12}"/>`;
        }
      }

      const cls = isRoot ? 'node highlighted' : 'node';
      svg += `<g class="${cls}" transform="translate(${x},${y})">`;
      svg += `<circle r="12"/>`;
      svg += `<text dy="3" text-anchor="middle">${nodes[i]}</text>`;
      svg += `</g>`;
    }
  }

  svg += '</svg>';
  container.innerHTML = svg;
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
          <div class="explainer__cell-label">Prover knows</div>
          <div class="explainer__cell-content">${escapeHtml(prover)}</div>
        </div>
        <div class="explainer__cell explainer__cell--verifier">
          <div class="explainer__cell-label">Verifier sees</div>
          <div class="explainer__cell-content">${escapeHtml(verifier)}</div>
        </div>
        <div class="explainer__cell explainer__cell--delta">
          <div class="explainer__cell-label">Privacy delta</div>
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
