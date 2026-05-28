// Federation Simulator section — interactive multi-node consensus visualization

import { state, notifyStateChange, navigateTo, getWasm } from '../playground.js';
import { deepLinkBanner, onSeedReady } from '../studio-embed.js';

export function initFederation(wasm) {
  const container = document.getElementById('section-federation');
  container.innerHTML = `
    <div class="section-header">
      <h2>Federation Simulator</h2>
      ${deepLinkBanner([
        { label: '<dregg-federation>', uri: 'dregg://federation/0' },
        { label: '<dregg-block-dag>', uri: 'dregg://block-dag/0' },
      ])}
      <p>
        Simulate a multi-node federation running consensus. Spawn nodes, propose blocks,
        submit turns, and watch them get ordered. Exit a federation and rejoin another —
        your receipt chain proves your history to any verifier.
      </p>
      <span class="next-hint" data-next="marketplace">Next: compute marketplace &rarr;</span>
    </div>

    <div class="fed-sim-container">
      <!-- Federation A -->
      <div class="fed-sim-group" id="fed-group-a">
        <div class="fed-sim-group__header">
          <span class="fed-sim-group__title">Federation Alpha</span>
          <span class="fed-sim-group__height" id="fed-a-height">height: 0</span>
        </div>
        <div class="fed-sim-nodes" id="fed-a-nodes"></div>
        <div class="fed-sim-consensus" id="fed-a-consensus"></div>
      </div>

      <!-- Federation B (hidden until rejoin) -->
      <div class="fed-sim-group hidden" id="fed-group-b">
        <div class="fed-sim-group__header">
          <span class="fed-sim-group__title">Federation Beta</span>
          <span class="fed-sim-group__height" id="fed-b-height">height: 0</span>
        </div>
        <div class="fed-sim-nodes" id="fed-b-nodes"></div>
        <div class="fed-sim-consensus" id="fed-b-consensus"></div>
      </div>
    </div>

    <div class="controls-row">
      <button class="btn btn-primary" id="fed-add-node">Add Node</button>
      <button class="btn btn-secondary" id="fed-remove-node" disabled>Remove Node</button>
      <button class="btn btn-primary" id="fed-propose" disabled>Propose Block</button>
      <button class="btn btn-primary" id="fed-submit-turn" disabled>Submit Turn</button>
      <button class="btn btn-danger" id="fed-exit" disabled>Exit Federation</button>
      <button class="btn btn-secondary" id="fed-rejoin" disabled>Rejoin (Beta)</button>
      <button class="btn btn-secondary" id="fed-reset">Reset</button>
    </div>

    <div class="fed-sim-state" id="fed-state-panel">
      <div class="fed-sim-state__title">Node State</div>
      <div class="fed-sim-state__body" id="fed-state-body">
        <span class="fed-sim-state__empty">Add nodes to begin</span>
      </div>
    </div>

    <div id="fed-timeline"></div>
    <div id="fed-explainer"></div>
  `;

  // Point the Starbridge federation/block-dag deeplinks at the real seeded
  // federation once the shared runtime is ready.
  onSeedReady((s) => {
    if (s.fedIndex == null) return;
    const links = container.querySelectorAll('.pg-sb-link');
    if (links[0]) links[0].href = `/starbridge/?at=${encodeURIComponent('dregg://federation/' + s.fedIndex)}`;
    if (links[1]) links[1].href = `/starbridge/?at=${encodeURIComponent('dregg://block-dag/' + s.fedIndex)}`;
  });

  // --- Internal state ---
  let federationA = { nodes: [], height: 0, root: '0000000000000000', pending: [] };
  let federationB = { nodes: [], height: 0, root: '0000000000000000', pending: [] };
  let exitedNode = null;
  let exitedReceipts = [];
  let animating = false;
  let nodeIdCounter = 0;

  const addBtn = container.querySelector('#fed-add-node');
  const removeBtn = container.querySelector('#fed-remove-node');
  const proposeBtn = container.querySelector('#fed-propose');
  const turnBtn = container.querySelector('#fed-submit-turn');
  const exitBtn = container.querySelector('#fed-exit');
  const rejoinBtn = container.querySelector('#fed-rejoin');
  const resetBtn = container.querySelector('#fed-reset');
  const timelineDiv = container.querySelector('#fed-timeline');
  const explainerDiv = container.querySelector('#fed-explainer');

  container.querySelector('.next-hint').addEventListener('click', () => navigateTo('marketplace'));

  // --- Utility ---
  function fnvHash(str) {
    let h = 0x811c9dc5;
    for (let i = 0; i < str.length; i++) {
      h ^= str.charCodeAt(i);
      h = Math.imul(h, 0x01000193);
    }
    return (h >>> 0).toString(16).padStart(8, '0');
  }

  function computeRoot(leaves) {
    if (wasm && wasm.compute_merkle_root) {
      try {
        const result = wasm.compute_merkle_root(JSON.stringify(leaves));
        return result.root_hex.slice(0, 16);
      } catch { /* fallback */ }
    }
    // Fallback: simple hash chain
    let acc = '0000000000000000';
    for (const leaf of leaves) {
      acc = fnvHash(acc + leaf) + fnvHash(leaf + acc);
    }
    return acc.slice(0, 16);
  }

  function delay(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
  }

  function createNode(federation) {
    nodeIdCounter++;
    const isLeader = federation.nodes.length === 0;
    return {
      id: nodeIdCounter,
      name: `Node-${nodeIdCounter}`,
      role: isLeader ? 'leader' : 'follower',
      status: 'online',
      height: federation.height,
      root: federation.root,
      pending: [],
      receipts: [],
    };
  }

  // --- Rendering ---
  function renderNodes(federation, containerId) {
    const container = document.getElementById(containerId);
    container.innerHTML = federation.nodes.map(node => {
      const roleClass = node.role === 'leader' ? 'leader' : 'follower';
      const statusClass = node.status;
      return `
        <div class="fed-node-circle ${roleClass} ${statusClass}" data-node-id="${node.id}">
          <div class="fed-node-circle__role">${node.role === 'leader' ? 'L' : 'F'}</div>
          <div class="fed-node-circle__name">${node.name}</div>
          <div class="fed-node-circle__status">${node.status}</div>
        </div>
      `;
    }).join('');
  }

  function renderStatePanel() {
    const body = container.querySelector('#fed-state-body');
    const allNodes = [...federationA.nodes, ...federationB.nodes];
    if (allNodes.length === 0) {
      body.innerHTML = '<span class="fed-sim-state__empty">Add nodes to begin</span>';
      return;
    }
    body.innerHTML = allNodes.map(node => `
      <div class="fed-state-row">
        <span class="fed-state-row__name">${node.name}</span>
        <span class="fed-state-row__role ${node.role}">${node.role}</span>
        <span class="fed-state-row__detail">h:${node.height}</span>
        <span class="fed-state-row__detail">root:${node.root.slice(0, 8)}...</span>
        <span class="fed-state-row__detail">pending:${node.pending.length}</span>
        <span class="fed-state-row__status ${node.status}">${node.status}</span>
      </div>
    `).join('');
  }

  function updateUI() {
    renderNodes(federationA, 'fed-a-nodes');
    renderNodes(federationB, 'fed-b-nodes');
    renderStatePanel();

    container.querySelector('#fed-a-height').textContent = `height: ${federationA.height}`;
    container.querySelector('#fed-b-height').textContent = `height: ${federationB.height}`;

    const onlineA = federationA.nodes.filter(n => n.status === 'online').length;
    removeBtn.disabled = onlineA < 1 || animating;
    proposeBtn.disabled = onlineA < 2 || animating;
    turnBtn.disabled = onlineA < 2 || animating;
    exitBtn.disabled = onlineA < 2 || exitedNode !== null || animating;
    rejoinBtn.disabled = exitedNode === null || animating;
    addBtn.disabled = animating;

    // Show federation B if it has nodes
    const groupB = container.querySelector('#fed-group-b');
    if (federationB.nodes.length > 0) {
      groupB.classList.remove('hidden');
    } else {
      groupB.classList.add('hidden');
    }

    // Update global state
    state.federation.nodes = federationA.nodes.length + federationB.nodes.length;
    state.federation.status = onlineA >= 2 ? 'consensus' : (onlineA >= 1 ? 'degraded' : 'offline');
    state.federation.commit = federationA.root;
    notifyStateChange();
  }

  function addTimelineEntry(entries) {
    let html = '<div class="result-panel"><div class="result-panel__header"><span class="result-panel__title">Federation Timeline</span></div><div class="result-panel__body">';
    entries.forEach((entry, i) => {
      const cls = entry.type || (i === entries.length - 1 ? 'success' : 'info');
      html += `<div class="output-entry ${cls}">${escapeHtml(entry.text)}</div>`;
    });
    html += '</div></div>';
    timelineDiv.innerHTML = html;
  }

  function showExplainer(data) {
    explainerDiv.innerHTML = `
      <div class="explainer">
        <div class="explainer__title">What just happened</div>
        <div class="explainer__grid">
          <div class="explainer__cell explainer__cell--prover">
            <div class="explainer__cell-label">${data.leftLabel || 'Leader'}</div>
            <div class="explainer__cell-content">${escapeHtml(data.left)}</div>
          </div>
          <div class="explainer__cell explainer__cell--verifier">
            <div class="explainer__cell-label">${data.centerLabel || 'Followers'}</div>
            <div class="explainer__cell-content">${escapeHtml(data.center)}</div>
          </div>
          <div class="explainer__cell explainer__cell--delta">
            <div class="explainer__cell-label">${data.rightLabel || 'Result'}</div>
            <div class="explainer__cell-content">${escapeHtml(data.right)}</div>
          </div>
        </div>
        <div class="explainer__timing">${data.footer || ''}</div>
      </div>
    `;
  }

  // --- Flash animation on nodes ---
  function flashNodes(nodeIds, cls, durationMs) {
    const circles = container.querySelectorAll('.fed-node-circle');
    circles.forEach(el => {
      const id = parseInt(el.dataset.nodeId);
      if (nodeIds.includes(id)) {
        el.classList.add(cls);
      }
    });
    return delay(durationMs).then(() => {
      circles.forEach(el => el.classList.remove(cls));
    });
  }

  // --- Show consensus arrows as text in the consensus area ---
  function showConsensusFlow(containerId, text) {
    const el = document.getElementById(containerId);
    el.innerHTML = `<div class="fed-consensus-msg">${escapeHtml(text)}</div>`;
  }

  function clearConsensusFlow(containerId) {
    document.getElementById(containerId).innerHTML = '';
  }

  // --- Actions ---
  addBtn.addEventListener('click', () => {
    if (federationA.nodes.length >= 7) return;
    const node = createNode(federationA);
    federationA.nodes.push(node);
    updateUI();
    addTimelineEntry([{ text: `${node.name} joined Federation Alpha as ${node.role}`, type: 'info' }]);
  });

  removeBtn.addEventListener('click', async () => {
    if (animating) return;
    animating = true;

    const onlineNodes = federationA.nodes.filter(n => n.status === 'online');
    if (onlineNodes.length < 1) { animating = false; return; }

    // Take the last follower offline, or the last node if no followers
    const target = onlineNodes.filter(n => n.role === 'follower').pop() || onlineNodes.pop();
    target.status = 'offline';

    // If leader went offline, elect new leader
    const remainingOnline = federationA.nodes.filter(n => n.status === 'online');
    if (target.role === 'leader' && remainingOnline.length > 0) {
      remainingOnline[0].role = 'leader';
      addTimelineEntry([
        { text: `${target.name} went OFFLINE (crash simulated)`, type: 'warning' },
        { text: `${remainingOnline[0].name} elected as new leader`, type: 'info' },
      ]);
    } else {
      addTimelineEntry([{ text: `${target.name} went OFFLINE (crash simulated)`, type: 'warning' }]);
    }

    updateUI();
    animating = false;
  });

  proposeBtn.addEventListener('click', async () => {
    if (animating) return;
    animating = true;
    updateUI();

    const onlineNodes = federationA.nodes.filter(n => n.status === 'online');
    const leader = onlineNodes.find(n => n.role === 'leader');
    const followers = onlineNodes.filter(n => n.role === 'follower');
    const quorum = Math.floor(onlineNodes.length / 2) + 1;

    const entries = [];
    const blockData = `block:${federationA.height + 1}:${Date.now()}`;
    const blockHash = computeRoot([federationA.root, blockData]);

    // Phase 1: Leader proposes
    entries.push({ text: `[${leader.name}] Proposing block #${federationA.height + 1} (hash: ${blockHash.slice(0, 12)}...)`, type: 'info' });
    showConsensusFlow('fed-a-consensus', `${leader.name} -> all: PROPOSE block #${federationA.height + 1}`);
    updateUI();
    addTimelineEntry(entries);
    await delay(600);

    // Phase 2: Followers vote
    let votes = 1; // leader votes for itself
    for (const f of followers) {
      votes++;
      entries.push({ text: `[${f.name}] VOTE: accept block #${federationA.height + 1}`, type: 'info' });
      showConsensusFlow('fed-a-consensus', `${f.name} -> ${leader.name}: VOTE accept (${votes}/${quorum} for quorum)`);
      addTimelineEntry(entries);
      await delay(350);
    }

    // Phase 3: Quorum reached
    entries.push({ text: `Quorum reached (${votes}/${onlineNodes.length}). Block #${federationA.height + 1} FINALIZED.`, type: 'success' });
    showConsensusFlow('fed-a-consensus', `COMMIT: block #${federationA.height + 1} finalized`);

    federationA.height++;
    federationA.root = blockHash;
    onlineNodes.forEach(n => {
      n.height = federationA.height;
      n.root = blockHash;
      n.receipts.push({ height: federationA.height, root: blockHash });
    });

    // Add to global receipts
    state.receipts.push({ type: 'block', height: federationA.height, root: blockHash });

    addTimelineEntry(entries);
    await flashNodes(onlineNodes.map(n => n.id), 'finalized', 800);

    showExplainer({
      leftLabel: 'Leader',
      left: `${leader.name} proposed block #${federationA.height}\nBlock hash: ${blockHash}\nBroadcast to ${followers.length} followers`,
      centerLabel: 'Followers',
      center: `${followers.length} followers voted ACCEPT\nQuorum threshold: ${quorum}/${onlineNodes.length}\nAll votes received before timeout`,
      rightLabel: 'Result',
      right: `Block finalized at height ${federationA.height}\nNew attested root: ${blockHash}\nAll online nodes updated\nReceipt chain extended`,
    });

    await delay(400);
    clearConsensusFlow('fed-a-consensus');
    updateUI();
    animating = false;
  });

  turnBtn.addEventListener('click', async () => {
    if (animating) return;
    animating = true;
    updateUI();

    const onlineNodes = federationA.nodes.filter(n => n.status === 'online');
    const leader = onlineNodes.find(n => n.role === 'leader');
    const entries = [];

    // Create a turn
    const turnData = `turn:${Date.now()}:transfer:50`;
    const turnHash = fnvHash(turnData);
    entries.push({ text: `Turn submitted: transfer 50 tokens (hash: ${turnHash})`, type: 'info' });
    addTimelineEntry(entries);
    showConsensusFlow('fed-a-consensus', `Ordering turn ${turnHash.slice(0, 8)}...`);
    await delay(400);

    // Leader orders it
    entries.push({ text: `[${leader.name}] Ordered turn into block #${federationA.height + 1}`, type: 'info' });
    addTimelineEntry(entries);
    await delay(400);

    // Execute
    const newRoot = computeRoot([federationA.root, turnHash]);
    federationA.height++;
    federationA.root = newRoot;
    onlineNodes.forEach(n => {
      n.height = federationA.height;
      n.root = newRoot;
      n.receipts.push({ height: federationA.height, root: newRoot, turn: turnHash });
    });

    entries.push({ text: `Turn executed. State updated. Height: ${federationA.height}, Root: ${newRoot.slice(0, 12)}...`, type: 'success' });
    state.receipts.push({ type: 'turn', height: federationA.height, root: newRoot, turn: turnHash });

    addTimelineEntry(entries);
    showConsensusFlow('fed-a-consensus', `EXECUTED: turn ${turnHash.slice(0, 8)}... at height ${federationA.height}`);

    showExplainer({
      leftLabel: 'Submitter',
      left: `Submitted turn: transfer 50 tokens\nTurn hash: ${turnHash}\nTurn is content-addressed`,
      centerLabel: 'Consensus',
      center: `Leader ordered the turn\nIncluded in block #${federationA.height}\nAll nodes execute deterministically`,
      rightLabel: 'Execution',
      right: `State transition applied atomically\nNew root: ${newRoot}\nReceipt issued to all participants\nTurn cannot be replayed (nullified)`,
    });

    await delay(600);
    clearConsensusFlow('fed-a-consensus');
    updateUI();
    animating = false;
  });

  exitBtn.addEventListener('click', async () => {
    if (animating) return;
    animating = true;
    updateUI();

    const onlineNodes = federationA.nodes.filter(n => n.status === 'online');
    // Pick a follower to exit
    const follower = onlineNodes.filter(n => n.role === 'follower').pop();
    if (!follower) { animating = false; return; }

    const entries = [];
    entries.push({ text: `[${follower.name}] Requesting exit from Federation Alpha...`, type: 'warning' });
    addTimelineEntry(entries);
    showConsensusFlow('fed-a-consensus', `${follower.name}: EXIT REQUEST`);
    await delay(500);

    // Export receipt chain
    exitedReceipts = [...follower.receipts];
    entries.push({ text: `[${follower.name}] Receipt chain exported (${exitedReceipts.length} receipts)`, type: 'info' });
    addTimelineEntry(entries);
    await delay(400);

    // Remove from federation
    exitedNode = { ...follower };
    federationA.nodes = federationA.nodes.filter(n => n.id !== follower.id);
    entries.push({ text: `[${follower.name}] Exited Federation Alpha. Can prove history to any third party.`, type: 'success' });
    addTimelineEntry(entries);

    showExplainer({
      leftLabel: 'Exiting node',
      left: `${follower.name} requested exit\nExported ${exitedReceipts.length} receipts\nReceipt chain is self-proving\nNo ongoing obligation to Alpha`,
      centerLabel: 'Federation Alpha',
      center: `Acknowledged exit\nRemoved node from validator set\nQuorum requirement recalculated\nHistory remains in Alpha's chain`,
      rightLabel: 'Portability',
      right: `The receipt chain is a cryptographic proof of the node's participation history.\n\nAny federation can verify it without contacting Alpha.\n\nThis is the basis of cross-federation identity.`,
    });

    clearConsensusFlow('fed-a-consensus');
    updateUI();
    animating = false;
  });

  rejoinBtn.addEventListener('click', async () => {
    if (animating || !exitedNode) return;
    animating = true;
    updateUI();

    const entries = [];

    // Show federation B
    container.querySelector('#fed-group-b').classList.remove('hidden');

    entries.push({ text: `[${exitedNode.name}] Requesting join to Federation Beta...`, type: 'info' });
    addTimelineEntry(entries);
    await delay(400);

    // Verify receipt chain
    entries.push({ text: `[Beta] Verifying receipt chain (${exitedReceipts.length} receipts)...`, type: 'info' });
    showConsensusFlow('fed-b-consensus', `Verifying receipt chain from ${exitedNode.name}...`);
    addTimelineEntry(entries);
    await delay(600);

    // Verify each receipt
    let verified = 0;
    for (const receipt of exitedReceipts) {
      verified++;
      // Simulate WASM verification
      if (wasm && wasm.compute_merkle_root) {
        try { wasm.compute_merkle_root(JSON.stringify([receipt.root])); } catch {}
      }
    }
    entries.push({ text: `[Beta] All ${verified} receipts verified. History is valid.`, type: 'success' });
    addTimelineEntry(entries);
    await delay(400);

    // Add to federation B
    const newNode = {
      ...exitedNode,
      role: federationB.nodes.length === 0 ? 'leader' : 'follower',
      status: 'online',
      height: federationB.height,
      root: federationB.root,
      pending: [],
    };
    federationB.nodes.push(newNode);
    entries.push({ text: `[${newNode.name}] Joined Federation Beta as ${newNode.role}. Identity portable.`, type: 'success' });
    addTimelineEntry(entries);

    showExplainer({
      leftLabel: 'Joining node',
      left: `${newNode.name} presented receipt chain\n${exitedReceipts.length} receipts from Alpha\nProves participation without Alpha online`,
      centerLabel: 'Federation Beta',
      center: `Verified all receipts cryptographically\nNo communication with Alpha needed\nAccepted node with proven history\nAssigned role: ${newNode.role}`,
      rightLabel: 'Cross-federation',
      right: `This demonstrates portable identity.\n\nA node's history travels with it.\n\nFederations are sovereign but interoperable.\n\nThe receipt chain is the universal proof of work done.`,
    });

    clearConsensusFlow('fed-b-consensus');
    exitedNode = null;
    exitedReceipts = [];
    updateUI();
    animating = false;
  });

  resetBtn.addEventListener('click', () => {
    federationA = { nodes: [], height: 0, root: '0000000000000000', pending: [] };
    federationB = { nodes: [], height: 0, root: '0000000000000000', pending: [] };
    exitedNode = null;
    exitedReceipts = [];
    animating = false;
    nodeIdCounter = 0;
    timelineDiv.innerHTML = '';
    explainerDiv.innerHTML = '';
    clearConsensusFlow('fed-a-consensus');
    clearConsensusFlow('fed-b-consensus');
    container.querySelector('#fed-group-b').classList.add('hidden');
    updateUI();
  });

  // Initial render
  updateUI();
}

function escapeHtml(str) {
  return String(str).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/\n/g, '<br>');
}
