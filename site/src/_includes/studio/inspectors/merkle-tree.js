/**
 * <pyana-merkle-tree> — 4-ary BLAKE3 Merkle tree visualizer.
 *
 * The beating heart of MerkleMembership / SenderAuthorized / BlindedSet
 * predicates. Renders an SVG tree with hover-to-see-hash, membership path
 * highlighted in green, absence proof path highlighted in amber.
 *
 * Attributes:
 *   leaves  — JSON-stringified string[]                         (required)
 *   data    — JSON-stringified { leaves, focus_leaf?, prove? }  (optional override)
 *             prove: 'member' | 'absent'
 *   mode    — 'default' (full SVG) | 'compact' (one-liner)
 *
 * Crypto calls (pure — no runtime handle needed):
 *   runtime._wasm.compute_merkle_root(JSON.stringify(leaves))
 *   runtime._wasm.merkle_membership_proof(JSON.stringify(leaves), leaf)
 *   runtime._wasm.merkle_non_membership_proof(JSON.stringify(leaves), leaf)
 */

import { InspectorBase, shortHex } from './_base.js';

// ---------------------------------------------------------------------------
// Pure tree-layout helpers (4-ary)
// ---------------------------------------------------------------------------

/**
 * Build a 4-ary level array from flat leaves. Returns an array-of-arrays
 * from root (index 0) down to leaves (last index). Each node is:
 *   { label, fullLabel, nodeIndex, leafIndex? }
 *
 * We store just display strings here; proof highlighting is done via the
 * returned path indices from wasm.
 */
function buildLevels(leaves, rootHex) {
  const levels = [];

  // Bottom level: the actual leaves
  let current = leaves.map((l, i) => ({
    label: l.length > 8 ? l.slice(0, 8) + '…' : l,
    fullLabel: l,
    leafIndex: i,
  }));
  levels.unshift(current); // we'll reverse at end

  // Walk up: group by 4, hash each group
  while (current.length > 1) {
    const next = [];
    for (let i = 0; i < current.length; i += 4) {
      const group = current.slice(i, i + 4);
      next.push({
        label: 'H(…)',
        fullLabel: `hash of ${group.length} child${group.length > 1 ? 'ren' : ''}`,
        childStart: i,
        childEnd: i + group.length - 1,
      });
    }
    current = next;
    levels.unshift(current);
  }

  // Replace root label with actual root hex
  if (levels[0] && levels[0][0]) {
    levels[0][0].label = rootHex ? rootHex.slice(0, 8) + '…' : 'root';
    levels[0][0].fullLabel = rootHex || 'root';
  }

  return levels;
}

/**
 * Given a leaf index and tree depth (branching = 4), compute all ancestor
 * node positions as { level, nodeIdx } from the leaf level up to root.
 * Returns an array of { level, nodeIdx } sorted leaf→root.
 */
function membershipPath(leafIndex, numLeaves) {
  const path = [];
  let idx = leafIndex;
  // Walk from leaf level up
  // At each level the node at position `idx` is on the path.
  // Its parent is at Math.floor(idx / 4).
  const depth = Math.ceil(Math.log(Math.max(numLeaves, 2)) / Math.log(4));
  for (let lvl = depth; lvl >= 0; lvl--) {
    path.push({ level: lvl, nodeIdx: idx });
    idx = Math.floor(idx / 4);
  }
  return path; // leaf at front, root at back
}

// ---------------------------------------------------------------------------
// Wasm proof shape notes
// ---------------------------------------------------------------------------
//
// compute_merkle_root(leavesJson)
//   → { root_hex, num_leaves }
//
// merkle_membership_proof(leavesJson, leaf)
//   → { root_hex, leaf, is_member, proof_path_len }
//   (no leaf_index; derive by indexOf on sorted leaves or linear scan)
//
// merkle_non_membership_proof(leavesJson, leaf)
//   → { root_hex, leaf, proven_absent }
//   (no bounding indices exposed)

// ---------------------------------------------------------------------------
// SVG renderer (plain DOM, no Preact — SVG + html`` mixing is awkward)
// ---------------------------------------------------------------------------

const PALETTE = {
  bg: '#0d1410',
  node: '#1a2420',
  nodeBorder: '#2a302d',
  nodeRoot: '#1a2e1a',
  nodeRootBorder: '#3a5a3a',
  nodeLeaf: '#12201a',
  nodeLeafBorder: '#2a3a2a',
  fg: '#c8d4cc',
  fgDim: '#6a8070',
  link: '#2a302d',
  memberFill: '#1a3a1a',
  memberBorder: '#5b8a5a',
  memberLink: '#5b8a5a',
  absentFill: '#2a1e10',
  absentBorder: '#c07830',
  absentLink: '#c07830',
  rootFill: '#0a2810',
  rootBorder: '#5b8a5a',
};

const NODE_W = 88;
const NODE_H = 28;
const LEVEL_H = 70;
const PAD_X = 40;
const PAD_Y = 20;

function renderSVG(leaves, rootHex, proofResult, proveMode) {
  const levels = buildLevels(leaves, rootHex);
  const depth = levels.length;
  const maxNodes = leaves.length; // bottom level always widest
  const svgW = Math.max(400, maxNodes * (NODE_W + 12) + PAD_X * 2);
  const svgH = depth * LEVEL_H + PAD_Y * 2;

  // Compute x positions for each level
  function nodeX(level, nodeIdx, count) {
    const spacing = svgW / (count + 1);
    return spacing * (nodeIdx + 1);
  }
  function nodeY(level) {
    return PAD_Y + level * LEVEL_H + NODE_H / 2;
  }

  // Which nodes are on the proof path?
  const pathSet = new Set();
  let focusLeafIdx = -1;
  if (proofResult && proveMode !== 'absent') {
    // Derive leaf index by value since wasm does not return leaf_index.
    // The wasm tree uses sorted leaves internally; fall back to indexOf.
    if (proofResult.is_member) {
      focusLeafIdx = leaves.indexOf(proofResult.leaf ?? '');
      if (focusLeafIdx < 0) focusLeafIdx = leaves.indexOf(proofResult.leaf ?? '');
    }
    if (focusLeafIdx >= 0) {
      const path = membershipPath(focusLeafIdx, leaves.length);
      path.forEach(p => pathSet.add(`${p.level}:${p.nodeIdx}`));
    }
  }
  // For absence proofs: highlight all leaves (since wasm returns no bounding indices)
  // and mark the full leaf row in amber to indicate sorted-order gap checking.
  const absenceSet = new Set();
  if (proveMode === 'absent' && proofResult?.proven_absent) {
    // Highlight all leaves as the "gap evidence" set since we have no index bounds
    for (let ai = 0; ai < leaves.length; ai++) {
      absenceSet.add(`${depth - 1}:${ai}`);
    }
  }

  let lines = '';
  let nodes = '';

  for (let lvl = 0; lvl < depth; lvl++) {
    const levelNodes = levels[lvl];
    const count = levelNodes.length;

    for (let ni = 0; ni < count; ni++) {
      const node = levelNodes[ni];
      const cx = nodeX(lvl, ni, count);
      const cy = nodeY(lvl);
      const key = `${lvl}:${ni}`;
      const onMemberPath = pathSet.has(key) && proveMode !== 'absent';
      const onAbsentPath = absenceSet.has(key);
      const isRoot = lvl === 0;
      const isLeaf = lvl === depth - 1;

      // Draw lines to children
      if (lvl < depth - 1) {
        const childLevel = levels[lvl + 1];
        const childCount = childLevel.length;
        const childStart = ni * 4;
        for (let ci = 0; ci < 4; ci++) {
          const childIdx = childStart + ci;
          if (childIdx >= childCount) break;
          const childCx = nodeX(lvl + 1, childIdx, childCount);
          const childCy = nodeY(lvl + 1);
          const childKey = `${lvl + 1}:${childIdx}`;
          const childOnMember = pathSet.has(childKey) && onMemberPath;
          const childOnAbsent = absenceSet.has(childKey);
          const stroke = childOnMember ? PALETTE.memberLink
            : childOnAbsent ? PALETTE.absentLink
            : PALETTE.link;
          const sw = (childOnMember || childOnAbsent) ? 2 : 1;
          lines += `<line x1="${cx.toFixed(1)}" y1="${(cy + NODE_H / 2).toFixed(1)}" x2="${childCx.toFixed(1)}" y2="${(childCy - NODE_H / 2).toFixed(1)}" stroke="${stroke}" stroke-width="${sw}" opacity="${(childOnMember || childOnAbsent) ? 1 : 0.35}"/>`;
        }
      }

      // Decide node color
      let fill = PALETTE.node;
      let border = PALETTE.nodeBorder;
      if (isRoot) { fill = PALETTE.nodeRoot; border = PALETTE.nodeRootBorder; }
      if (isLeaf) { fill = PALETTE.nodeLeaf; border = PALETTE.nodeLeafBorder; }
      if (onMemberPath) { fill = PALETTE.memberFill; border = PALETTE.memberBorder; }
      if (isRoot && onMemberPath) { fill = PALETTE.rootFill; border = PALETTE.rootBorder; }
      if (onAbsentPath) { fill = PALETTE.absentFill; border = PALETTE.absentBorder; }

      const textColor = onMemberPath ? PALETTE.memberBorder : onAbsentPath ? PALETTE.absentBorder : PALETTE.fg;
      const rx = (cx - NODE_W / 2).toFixed(1);
      const ry = (cy - NODE_H / 2).toFixed(1);

      // tooltip via <title>
      const fullLabel = isRoot && rootHex
        ? rootHex
        : (node.fullLabel || node.label);
      nodes += `<g class="mk-node" data-key="${key}" data-full="${escAttr(fullLabel)}">`;
      nodes += `<title>${escAttr(fullLabel)}</title>`;
      nodes += `<rect x="${rx}" y="${ry}" width="${NODE_W}" height="${NODE_H}" rx="5" fill="${fill}" stroke="${border}" stroke-width="${(onMemberPath || onAbsentPath) ? 1.5 : 1}"/>`;
      nodes += `<text x="${cx.toFixed(1)}" y="${(cy + 4).toFixed(1)}" text-anchor="middle" font-family="ui-monospace,monospace" font-size="10" fill="${textColor}">${escText(node.label)}</text>`;
      // leaf index badge
      if (isLeaf) {
        nodes += `<text x="${(cx - NODE_W / 2 + 5).toFixed(1)}" y="${(cy - NODE_H / 2 + 9).toFixed(1)}" font-family="ui-monospace,monospace" font-size="7" fill="${PALETTE.fgDim}">${ni}</text>`;
      }
      nodes += `</g>`;
    }
  }

  return `<svg xmlns="http://www.w3.org/2000/svg" width="${svgW}" height="${svgH}" viewBox="0 0 ${svgW} ${svgH}" style="display:block;overflow:visible;max-width:100%;height:auto;">
  <rect width="${svgW}" height="${svgH}" fill="${PALETTE.bg}" rx="8"/>
  <g class="mk-links">${lines}</g>
  <g class="mk-nodes">${nodes}</g>
</svg>`;
}

function escAttr(s) {
  return String(s).replace(/&/g, '&amp;').replace(/"/g, '&quot;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}
function escText(s) {
  return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

// ---------------------------------------------------------------------------
// Legend + proof summary strip
// ---------------------------------------------------------------------------
function proofSummaryHTML(leaves, proofResult, proveMode, focusLeaf, error) {
  if (error) {
    return `<div class="mk-proof mk-proof--error">${escText(error)}</div>`;
  }
  if (!focusLeaf || !proofResult) return '';

  if (proveMode === 'absent') {
    const proven = proofResult.proven_absent;
    return `<div class="mk-proof mk-proof--absent">
      <span class="mk-proof__badge mk-proof__badge--absent">${proven ? 'ABSENT' : 'PRESENT'}</span>
      <code>${escText(focusLeaf)}</code> is <strong>${proven ? 'not' : 'already'}</strong> in this tree.
    </div>`;
  }

  // membership — wasm shape: { root_hex, leaf, is_member, proof_path_len }
  const verified = proofResult.is_member;
  const leafIdx = leaves.indexOf(focusLeaf);
  return `<div class="mk-proof mk-proof--${verified ? 'member' : 'fail'}">
    <span class="mk-proof__badge mk-proof__badge--${verified ? 'member' : 'fail'}">${verified ? 'MEMBER' : 'NOT FOUND'}</span>
    <code>${escText(focusLeaf)}</code>
    ${leafIdx >= 0 ? `at index <code>${leafIdx}</code>` : ''}
    · path length <code>${proofResult.proof_path_len ?? 0}</code>
    ${verified ? '' : '· not in this tree'}
  </div>`;
}

// ---------------------------------------------------------------------------
// Custom element
// ---------------------------------------------------------------------------

class PyanaMerkleTree extends HTMLElement {
  static get observedAttributes() { return ['leaves', 'data', 'mode']; }

  constructor() {
    super();
    this._runtime = null;
  }

  async connectedCallback() {
    // Import findRuntime lazily (avoids hard dep if used standalone)
    const { findRuntime } = await import('../context.js');
    try {
      this._runtime = await findRuntime(this);
    } catch {
      // No <pyana-app> ancestor — render in degraded mode (no wasm calls)
      this._runtime = null;
    }
    this._render();
  }

  attributeChangedCallback() {
    this._render();
  }

  disconnectedCallback() {}

  // Parse all attributes → canonical { leaves, focusLeaf, prove }
  _parseAttrs() {
    let leaves = [];
    let focusLeaf = null;
    let prove = null;

    // `data` overrides `leaves`
    const dataAttr = this.getAttribute('data');
    if (dataAttr) {
      try {
        const d = JSON.parse(dataAttr);
        leaves = Array.isArray(d.leaves) ? d.leaves.map(String) : [];
        focusLeaf = d.focus_leaf ? String(d.focus_leaf) : null;
        prove = d.prove || null;
      } catch { /* bad JSON — fall through */ }
    }

    const leavesAttr = this.getAttribute('leaves');
    if (leavesAttr && leaves.length === 0) {
      try {
        const parsed = JSON.parse(leavesAttr);
        leaves = Array.isArray(parsed) ? parsed.map(String) : [];
      } catch { /* ignore */ }
    }

    // Allow prove to come from a top-level attribute too (undocumented convenience)
    const proveAttr = this.getAttribute('prove');
    if (!prove && proveAttr) prove = proveAttr;

    return { leaves, focusLeaf, prove };
  }

  _render() {
    const mode = this.getAttribute('mode') || 'default';
    const { leaves, focusLeaf, prove } = this._parseAttrs();

    // Clear
    this.innerHTML = '';

    if (leaves.length === 0) {
      this.innerHTML = `<div class="pyana-inspector pyana-inspector--empty">pyana-merkle-tree: no leaves</div>`;
      return;
    }

    // Compact mode: one-liner
    if (mode === 'compact') {
      let rootSnippet = '';
      if (this._runtime?._wasm) {
        try {
          const r = this._runtime._wasm.compute_merkle_root(JSON.stringify(leaves));
          rootSnippet = ` · root <code title="${escAttr(r.root_hex)}">${shortHex(r.root_hex)}</code>`;
        } catch { /* degraded */ }
      }
      this.innerHTML = `<span class="pyana-inspector pyana-inspector--compact pyana-inspector--merkle">
        <code>${leaves.length} leaf${leaves.length === 1 ? '' : 'ves'}</code>${rootSnippet}
      </span>`;
      return;
    }

    // Full mode
    if (!this._runtime?._wasm) {
      this.innerHTML = `<div class="pyana-inspector pyana-inspector--empty">pyana-merkle-tree: wasm not available (no runtime)</div>`;
      return;
    }

    const wasm = this._runtime._wasm;

    // 1. Compute root
    let rootHex = '';
    let rootErr = null;
    try {
      const r = wasm.compute_merkle_root(JSON.stringify(leaves));
      rootHex = r.root_hex;
    } catch (e) {
      rootErr = String(e?.message || e);
    }

    if (rootErr) {
      this.innerHTML = `<div class="pyana-inspector pyana-inspector--err">merkle root failed: ${escText(rootErr)}</div>`;
      return;
    }

    // 2. Optional proof
    let proofResult = null;
    let proofError = null;
    if (focusLeaf && prove) {
      try {
        if (prove === 'absent') {
          proofResult = wasm.merkle_non_membership_proof(JSON.stringify(leaves), focusLeaf);
        } else {
          proofResult = wasm.merkle_membership_proof(JSON.stringify(leaves), focusLeaf);
        }
      } catch (e) {
        proofError = String(e?.message || e);
      }
    } else if (focusLeaf) {
      // Default to membership
      try {
        proofResult = wasm.merkle_membership_proof(JSON.stringify(leaves), focusLeaf);
      } catch (e) {
        proofError = String(e?.message || e);
      }
    }

    // 3. Render SVG
    const svgHTML = renderSVG(leaves, rootHex, proofResult, prove || (focusLeaf ? 'member' : null));

    // 4. Proof strip
    const stripHTML = proofSummaryHTML(leaves, proofResult, prove || (focusLeaf ? 'member' : null), focusLeaf, proofError);

    // 5. Root line
    const depth = leaves.length <= 1
      ? 1
      : Math.ceil(Math.log(leaves.length) / Math.log(4));

    const wrapper = document.createElement('div');
    wrapper.className = 'pyana-inspector pyana-inspector--merkle-tree';
    wrapper.innerHTML = `
      <div class="mk-header">
        <span class="mk-header__badge">merkle</span>
        <code class="mk-header__root" title="${escAttr(rootHex)}">${shortHex(rootHex, 16)}</code>
        <span class="mk-header__meta">${leaves.length} leaves · depth ${depth} · 4-ary BLAKE3</span>
      </div>
      ${stripHTML}
      <div class="mk-svg-wrap">${svgHTML}</div>
      <div class="mk-legend">
        <span class="mk-legend__item mk-legend__item--member">membership path</span>
        <span class="mk-legend__item mk-legend__item--absent">absence bound</span>
        <span class="mk-legend__item mk-legend__item--node">hover any node for full hash</span>
      </div>
    `;

    this.appendChild(wrapper);
    this._attachHoverTooltip(wrapper);
  }

  /** Add a floating tooltip that shows full hash on node hover. */
  _attachHoverTooltip(wrapper) {
    const svgWrap = wrapper.querySelector('.mk-svg-wrap');
    if (!svgWrap) return;

    const tip = document.createElement('div');
    tip.className = 'mk-tooltip';
    tip.style.cssText = 'position:fixed;display:none;pointer-events:none;z-index:9999;padding:4px 8px;background:#0a0f0d;border:1px solid #2a302d;border-radius:4px;font:12px/1.5 ui-monospace,monospace;color:#c8d4cc;max-width:420px;word-break:break-all;';
    document.body.appendChild(tip);

    svgWrap.addEventListener('mousemove', e => {
      const node = e.target.closest('.mk-node');
      if (!node) { tip.style.display = 'none'; return; }
      const full = node.dataset.full || '';
      if (!full) { tip.style.display = 'none'; return; }
      tip.textContent = full;
      tip.style.display = 'block';
      tip.style.left = (e.clientX + 12) + 'px';
      tip.style.top = (e.clientY - 4) + 'px';
    });
    svgWrap.addEventListener('mouseleave', () => { tip.style.display = 'none'; });
    // Clean up tooltip when element is disconnected
    this._tipCleanup = () => { tip.remove(); };
  }

  disconnectedCallback() {
    if (this._tipCleanup) { this._tipCleanup(); this._tipCleanup = null; }
  }
}

// ---------------------------------------------------------------------------
// Styles (injected once)
// ---------------------------------------------------------------------------

const STYLES = `
.pyana-inspector--merkle-tree {
  font-family: ui-monospace, monospace;
  font-size: 0.875rem;
  background: var(--bg-raised, #0d1410);
  border: 1px solid var(--line, #2a302d);
  border-radius: 8px;
  padding: 12px;
  overflow: hidden;
}
.mk-header {
  display: flex;
  align-items: baseline;
  gap: 10px;
  margin-bottom: 8px;
  flex-wrap: wrap;
}
.mk-header__badge {
  padding: 2px 7px;
  background: #2a3a2a;
  color: #5b8a5a;
  border-radius: 3px;
  font-size: 0.72rem;
  text-transform: uppercase;
  letter-spacing: 0.06em;
}
.mk-header__root { color: #5b8a5a; word-break: break-all; }
.mk-header__meta { color: var(--fg-dim, #6a8070); font-size: 0.8rem; }

.mk-proof {
  display: flex;
  align-items: center;
  gap: 8px;
  padding: 6px 10px;
  border-radius: 5px;
  margin-bottom: 8px;
  font-size: 0.82rem;
  flex-wrap: wrap;
}
.mk-proof--member  { background: #0d200d; border: 1px solid #3a5a3a; color: #c8d4cc; }
.mk-proof--absent  { background: #1e1208; border: 1px solid #6a4020; color: #c8b88c; }
.mk-proof--fail    { background: #200d0d; border: 1px solid #6a2020; color: #d4908c; }
.mk-proof--error   { background: #200d0d; border: 1px solid #d4685c; color: #d4685c; padding: 6px 10px; border-radius: 5px; margin-bottom: 8px; }
.mk-proof__badge {
  padding: 1px 6px;
  border-radius: 3px;
  font-size: 0.7rem;
  font-weight: 700;
  letter-spacing: 0.06em;
  text-transform: uppercase;
  flex-shrink: 0;
}
.mk-proof__badge--member { background: #3a5a3a; color: #a0d4a0; }
.mk-proof__badge--absent { background: #5a3a18; color: #d4a060; }
.mk-proof__badge--fail   { background: #5a2020; color: #d4a0a0; }

.mk-svg-wrap { overflow-x: auto; margin: 0 -4px; padding: 4px; }
.mk-svg-wrap svg .mk-node { cursor: pointer; }
.mk-svg-wrap svg .mk-node rect { transition: stroke-width 0.1s, filter 0.1s; }
.mk-svg-wrap svg .mk-node:hover rect { filter: brightness(1.3); }

.mk-legend {
  display: flex;
  gap: 14px;
  margin-top: 8px;
  flex-wrap: wrap;
}
.mk-legend__item {
  font-size: 0.75rem;
  color: var(--fg-dim, #6a8070);
  padding-left: 14px;
  position: relative;
}
.mk-legend__item::before {
  content: '';
  position: absolute;
  left: 0; top: 50%;
  transform: translateY(-50%);
  width: 9px; height: 9px;
  border-radius: 2px;
  background: #2a302d;
}
.mk-legend__item--member::before { background: #3a5a3a; border: 1px solid #5b8a5a; }
.mk-legend__item--absent::before { background: #5a3a18; border: 1px solid #c07830; }

.pyana-inspector--merkle { display: inline-flex; gap: 8px; padding: 4px 8px; background: var(--bg-raised, #0d1410); border-radius: 4px; }
`;

let _stylesInjected = false;
function injectStyles() {
  if (_stylesInjected) return;
  _stylesInjected = true;
  const style = document.createElement('style');
  style.id = 'pyana-merkle-tree-styles';
  style.textContent = STYLES;
  document.head.appendChild(style);
}

if (typeof window !== 'undefined') {
  injectStyles();
}

if (!customElements.get('pyana-merkle-tree')) {
  customElements.define('pyana-merkle-tree', PyanaMerkleTree);
}
