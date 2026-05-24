/**
 * Merkle Tree Visualizer.
 *
 * Two entry points:
 *   - `render(container, data)` — legacy direct-render helper kept for
 *     historical callers (none currently in tree).
 *   - `defineVisualizer('merkle-tree', ...)` — `<pyana-vizzer>` registration
 *     for static embedding in Learn pages.
 *
 * Dataset (JSON in `data-dataset` or kebab-cased data-attrs):
 *   {
 *     "leaves":   ["a","b","c","d"],     // optional, default 4 placeholders
 *     "depth":    2,                      // optional, derived from leaves
 *     "proofPath": ["l-1","n-0-0"]       // optional, path nodes to highlight
 *   }
 */

import { defineVisualizer } from '/_includes/visualizer-base.js';

export const name = 'merkle-tree';

function simHash(str) {
  let h = 0;
  for (let i = 0; i < str.length; i++) h = ((h << 5) - h) + str.charCodeAt(i) | 0;
  return Math.abs(h).toString(16).padStart(8, '0').slice(0, 8);
}

function buildTree(leaves, depth) {
  const totalLeaves = Math.pow(2, depth);
  const padded = [...leaves];
  while (padded.length < totalLeaves) padded.push(null);

  let level = padded.map((leaf, i) => ({
    id: `l-${i}`,
    hash: leaf ? (typeof leaf === 'string' ? leaf : String(leaf)) : '00000000',
    isEmpty: !leaf,
    isLeaf: true,
  }));
  const allLevels = [level];

  for (let d = depth - 1; d >= 0; d--) {
    const next = [];
    for (let i = 0; i < level.length; i += 2) {
      const left = level[i];
      const right = level[i + 1] || { hash: '00000000', isEmpty: true };
      next.push({
        id: `n-${d}-${i / 2}`,
        hash: simHash(left.hash + right.hash),
        isEmpty: left.isEmpty && right.isEmpty,
        isLeaf: false,
        left, right,
      });
    }
    allLevels.push(next);
    level = next;
  }

  return level[0];
}

export function renderMerkleTreeSvg(html, root, depth, proofPath) {
  const W = 480;
  const H = (depth + 1) * 70 + 40;
  const paths = new Set(proofPath || []);

  function recur(node, x, y, spread, d) {
    if (!node || d < 0) return [];
    const out = [];
    const onPath = paths.has(node.id);
    const fill = onPath
      ? 'var(--warm)'
      : (node.isEmpty ? 'var(--line-strong)' : 'var(--accent)');
    const r = node.isLeaf ? 5 : 7;

    if (node.left) {
      const cy = y + 60;
      const lx = x - spread;
      const rx = x + spread;
      out.push(html`<line x1=${x} y1=${y} x2=${lx} y2=${cy} stroke="var(--line-strong)" stroke-width="1"/>`);
      out.push(html`<line x1=${x} y1=${y} x2=${rx} y2=${cy} stroke="var(--line-strong)" stroke-width="1"/>`);
      out.push(...recur(node.left, lx, cy, spread / 2, d - 1));
      out.push(...recur(node.right, rx, cy, spread / 2, d - 1));
    }

    out.push(html`<circle cx=${x} cy=${y} r=${r} fill=${fill}/>`);
    out.push(html`<text x=${x} y=${y - r - 3} text-anchor="middle"
      font-family="var(--font-mono, monospace)" font-size="8"
      fill="var(--fg-muted)">${(node.hash || '').slice(0, 4)}</text>`);
    return out;
  }

  return html`
    <svg class="viz-svg" viewBox=${`0 0 ${W} ${H}`} role="img"
         aria-label=${`Merkle tree, depth ${depth}`}>
      <text class="label" x="8" y="14">Merkle tree · depth ${depth} · ${root.isEmpty ? 'empty' : `root ${root.hash.slice(0, 8)}`}</text>
      ${recur(root, W / 2, 30, W / 4, depth)}
    </svg>
  `;
}

/**
 * Legacy direct-render API (kept for non-vizzer callers).
 */
export function render(container, data) {
  const { leaves = [], proofPath = null, depth = 4 } = data;
  const tree = buildTree(leaves, depth);
  // Fall back to plain DOM rendering — no Preact dependency on legacy path.
  // Build an SVG string manually.
  const W = container.clientWidth || 500;
  const H = (depth + 1) * 70 + 40;
  let svg = `<svg width="${W}" height="${H}" xmlns="http://www.w3.org/2000/svg">`;
  const paths = new Set(proofPath || []);
  function recur(node, x, y, spread, d) {
    if (!node || d < 0) return '';
    let out = '';
    const onPath = paths.has(node.id);
    const color = onPath ? '#d99a3f' : (node.isEmpty ? 'rgba(232,224,208,0.1)' : '#5b8a5a');
    const r = node.isLeaf ? 5 : 7;
    if (node.left) {
      const cy = y + 60, lx = x - spread, rx = x + spread;
      out += `<line x1="${x}" y1="${y}" x2="${lx}" y2="${cy}" stroke="rgba(232,224,208,0.15)"/>`;
      out += `<line x1="${x}" y1="${y}" x2="${rx}" y2="${cy}" stroke="rgba(232,224,208,0.15)"/>`;
      out += recur(node.left, lx, cy, spread / 2, d - 1);
      out += recur(node.right, rx, cy, spread / 2, d - 1);
    }
    out += `<circle cx="${x}" cy="${y}" r="${r}" fill="${color}"/>`;
    out += `<text x="${x}" y="${y - r - 3}" text-anchor="middle" font-family="monospace" font-size="7" fill="rgba(232,224,208,0.4)">${(node.hash || '').slice(0, 4)}</text>`;
    return out;
  }
  svg += recur(tree, W / 2, 30, W / 4, depth);
  svg += `</svg>`;
  container.innerHTML = svg;
}

defineVisualizer('merkle-tree', ({ dataset, api }) => {
  const { html } = api;
  let leaves, depth, proofPath;
  // Accept either a JSON blob on data-dataset or individual data-* attrs.
  try {
    if (dataset.dataset) {
      const parsed = JSON.parse(dataset.dataset);
      leaves = parsed.leaves;
      depth = parsed.depth;
      proofPath = parsed.proofPath;
    }
  } catch (_) { /* fall through */ }
  if (!leaves) {
    leaves = (dataset.leaves || 'alice,bob,carol,dave').split(',').map(s => s.trim());
  }
  if (depth === undefined) {
    depth = parseInt(dataset.depth || Math.max(1, Math.ceil(Math.log2(Math.max(2, leaves.length)))), 10);
  }
  if (!proofPath && dataset.proofPath) {
    proofPath = dataset.proofPath.split(',').map(s => s.trim());
  }
  const tree = buildTree(leaves, depth);
  return renderMerkleTreeSvg(html, tree, depth, proofPath);
});
