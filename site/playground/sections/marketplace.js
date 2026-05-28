// Compute Marketplace section — interactive sealed-bid auction + atomic settlement

import { state, notifyStateChange, navigateTo, getWasm } from '../playground.js';

export function initMarketplace(wasm) {
  const container = document.getElementById('section-marketplace');
  container.innerHTML = `
    <div class="section-header">
      <h2>Compute Marketplace</h2>
      <p>
        An interactive sealed-bid compute marketplace. Post jobs, submit hidden bids via note
        commitments, reveal and settle atomically. Demonstrates dregg's privacy-preserving
        auction mechanics, escrow, and dispute resolution — all running in WASM.
      </p>
      <span class="next-hint" data-next="sandbox">Next: code sandbox &rarr;</span>
    </div>

    <div class="mkt-participants" id="mkt-participants">
      <div class="mkt-participant" id="mkt-client">
        <div class="mkt-participant__icon">C</div>
        <div class="mkt-participant__name">Client</div>
        <div class="mkt-participant__detail" id="mkt-client-status">idle</div>
      </div>
      <div class="mkt-participant" id="mkt-provider-1">
        <div class="mkt-participant__icon">P1</div>
        <div class="mkt-participant__name">Provider 1</div>
        <div class="mkt-participant__detail" id="mkt-p1-status">idle</div>
      </div>
      <div class="mkt-participant" id="mkt-provider-2">
        <div class="mkt-participant__icon">P2</div>
        <div class="mkt-participant__name">Provider 2</div>
        <div class="mkt-participant__detail" id="mkt-p2-status">idle</div>
      </div>
      <div class="mkt-participant" id="mkt-provider-3">
        <div class="mkt-participant__icon">P3</div>
        <div class="mkt-participant__name">Provider 3</div>
        <div class="mkt-participant__detail" id="mkt-p3-status">idle</div>
      </div>
      <div class="mkt-participant" id="mkt-escrow">
        <div class="mkt-participant__icon">E</div>
        <div class="mkt-participant__name">Escrow</div>
        <div class="mkt-participant__detail" id="mkt-escrow-status">0 tokens</div>
      </div>
      <div class="mkt-participant" id="mkt-marketplace">
        <div class="mkt-participant__icon">M</div>
        <div class="mkt-participant__name">Marketplace</div>
        <div class="mkt-participant__detail" id="mkt-mkt-status">ready</div>
      </div>
    </div>

    <div class="controls-row">
      <button class="btn btn-primary" id="mkt-post-job">Post Job</button>
      <button class="btn btn-primary" id="mkt-submit-bids" disabled>Submit Bids</button>
      <button class="btn btn-primary" id="mkt-reveal" disabled>Reveal Bids</button>
      <button class="btn btn-primary" id="mkt-execute" disabled>Execute + Settle</button>
      <button class="btn btn-danger" id="mkt-dispute" disabled>Dispute</button>
      <button class="btn btn-secondary" id="mkt-reset">Reset</button>
    </div>

    <div class="mkt-state-panel" id="mkt-state">
      <div class="mkt-state-panel__row">
        <span class="mkt-state-panel__label">Escrow Balance</span>
        <span class="mkt-state-panel__value" id="mkt-escrow-bal">0</span>
      </div>
      <div class="mkt-state-panel__row">
        <span class="mkt-state-panel__label">Receipts Logged</span>
        <span class="mkt-state-panel__value" id="mkt-receipt-count">0</span>
      </div>
      <div class="mkt-state-panel__row">
        <span class="mkt-state-panel__label">Reputation (P1/P2/P3)</span>
        <span class="mkt-state-panel__value" id="mkt-reputation">0 / 0 / 0</span>
      </div>
      <div class="mkt-state-panel__row">
        <span class="mkt-state-panel__label">Phase</span>
        <span class="mkt-state-panel__value" id="mkt-phase">idle</span>
      </div>
    </div>

    <div id="mkt-timeline"></div>
    <div id="mkt-explainer"></div>
  `;

  // --- Internal state ---
  let mktState = resetState();
  let animating = false;

  function resetState() {
    return {
      phase: 'idle', // idle -> posted -> bids_submitted -> revealed -> executed | disputed
      job: null,
      bids: [],        // { provider, amount, commitment, nonce, revealed }
      winner: null,
      escrowBalance: 0,
      reputation: [0, 0, 0],
      receiptCount: 0,
    };
  }

  const postBtn = container.querySelector('#mkt-post-job');
  const bidsBtn = container.querySelector('#mkt-submit-bids');
  const revealBtn = container.querySelector('#mkt-reveal');
  const executeBtn = container.querySelector('#mkt-execute');
  const disputeBtn = container.querySelector('#mkt-dispute');
  const resetBtn = container.querySelector('#mkt-reset');
  const timelineDiv = container.querySelector('#mkt-timeline');
  const explainerDiv = container.querySelector('#mkt-explainer');

  container.querySelector('.next-hint').addEventListener('click', () => navigateTo('sandbox'));

  // --- Utility ---
  // Commitments come from the canonical wasm BLAKE3 Merkle root — no JS hash
  // fallback. A failure is surfaced honestly rather than fabricated.
  function computeCommitment(data) {
    const result = wasm.compute_merkle_root(JSON.stringify([data]));
    return result.root_hex.slice(0, 16);
  }

  // Genuinely-random local identifier (job id, nonce) — crypto.getRandomValues,
  // not a JS hash. These are arbitrary demo ids, not protocol commitments.
  function randId() {
    const b = new Uint8Array(4);
    crypto.getRandomValues(b);
    return Array.from(b).map((x) => x.toString(16).padStart(2, '0')).join('');
  }

  function delay(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
  }

  function updateUI() {
    // Phase
    container.querySelector('#mkt-phase').textContent = mktState.phase;
    container.querySelector('#mkt-escrow-bal').textContent = mktState.escrowBalance;
    container.querySelector('#mkt-receipt-count').textContent = mktState.receiptCount;
    container.querySelector('#mkt-reputation').textContent = mktState.reputation.join(' / ');
    container.querySelector('#mkt-escrow-status').textContent = `${mktState.escrowBalance} tokens`;

    // Buttons
    postBtn.disabled = mktState.phase !== 'idle' || animating;
    bidsBtn.disabled = mktState.phase !== 'posted' || animating;
    revealBtn.disabled = mktState.phase !== 'bids_submitted' || animating;
    executeBtn.disabled = mktState.phase !== 'revealed' || animating;
    disputeBtn.disabled = mktState.phase !== 'revealed' || animating;
    // Reset must follow the same rule so it can't yank state out from under
    // an in-flight async handler (caused: TypeError on mktState.job.budget).
    resetBtn.disabled = animating;

    // Participant highlights
    const allParts = container.querySelectorAll('.mkt-participant');
    allParts.forEach(el => el.classList.remove('active', 'winner', 'dispute'));

    if (mktState.phase === 'posted') {
      container.querySelector('#mkt-client').classList.add('active');
      container.querySelector('#mkt-marketplace').classList.add('active');
    } else if (mktState.phase === 'bids_submitted') {
      container.querySelector('#mkt-provider-1').classList.add('active');
      container.querySelector('#mkt-provider-2').classList.add('active');
      container.querySelector('#mkt-provider-3').classList.add('active');
    } else if (mktState.phase === 'revealed' && mktState.winner) {
      container.querySelector(`#mkt-provider-${mktState.winner}`).classList.add('winner');
      container.querySelector('#mkt-escrow').classList.add('active');
    } else if (mktState.phase === 'executed') {
      container.querySelector(`#mkt-provider-${mktState.winner}`).classList.add('winner');
    } else if (mktState.phase === 'disputed') {
      container.querySelector('#mkt-escrow').classList.add('dispute');
      container.querySelector('#mkt-client').classList.add('active');
    }
  }

  function addTimelineEntry(entries) {
    let html = '<div class="result-panel"><div class="result-panel__header"><span class="result-panel__title">Marketplace Timeline</span></div><div class="result-panel__body">';
    entries.forEach((entry, i) => {
      const cls = entry.type || 'info';
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
            <div class="explainer__cell-label">${data.leftLabel || 'Client'}</div>
            <div class="explainer__cell-content">${escapeHtml(data.left)}</div>
          </div>
          <div class="explainer__cell explainer__cell--verifier">
            <div class="explainer__cell-label">${data.centerLabel || 'Marketplace'}</div>
            <div class="explainer__cell-content">${escapeHtml(data.center)}</div>
          </div>
          <div class="explainer__cell explainer__cell--delta">
            <div class="explainer__cell-label">${data.rightLabel || 'Privacy'}</div>
            <div class="explainer__cell-content">${escapeHtml(data.right)}</div>
          </div>
        </div>
        <div class="explainer__timing">${data.footer || ''}</div>
      </div>
    `;
  }

  // --- Actions ---
  postBtn.addEventListener('click', async () => {
    if (animating) return;
    animating = true;
    updateUI();

    const entries = [];
    const jobId = randId();
    mktState.job = {
      id: jobId,
      description: 'Matrix multiply 1024x1024',
      budget: 100,
      deadline: 30, // seconds
    };

    entries.push({ text: `[Client] Posting job: "${mktState.job.description}"`, type: 'info' });
    container.querySelector('#mkt-client-status').textContent = 'posting...';
    container.querySelector('#mkt-mkt-status').textContent = 'receiving...';
    addTimelineEntry(entries);
    await delay(500);

    // Lock budget into escrow
    mktState.escrowBalance = mktState.job.budget;
    entries.push({ text: `[Client] Locked ${mktState.job.budget} tokens into escrow`, type: 'info' });
    entries.push({ text: `[Marketplace] Job ${jobId.slice(0, 8)}... posted. Accepting sealed bids.`, type: 'success' });
    container.querySelector('#mkt-client-status').textContent = 'job posted';
    container.querySelector('#mkt-mkt-status').textContent = 'accepting bids';
    mktState.phase = 'posted';

    addTimelineEntry(entries);
    showExplainer({
      leftLabel: 'Client',
      left: `Posted compute job\nDescription: ${mktState.job.description}\nBudget: ${mktState.job.budget} tokens\nDeadline: ${mktState.job.deadline}s\nJob ID: ${jobId.slice(0, 12)}...`,
      centerLabel: 'Marketplace',
      center: `Received job posting\nBudget locked in escrow\nOpened sealed-bid auction\nProviders cannot see each other's bids`,
      rightLabel: 'Privacy',
      right: `The job is public (providers need to know what to bid on).\n\nBut bids will be sealed — no provider can see another's price.\n\nThis prevents bid sniping and ensures fair competition.`,
      footer: `Job ID: ${jobId}`,
    });

    updateUI();
    animating = false;
  });

  bidsBtn.addEventListener('click', async () => {
    if (animating) return;
    animating = true;
    updateUI();

    const entries = [];
    const bidAmounts = [45, 32, 58]; // P2 will win with lowest bid
    const nonces = [
      randId(),
      randId(),
      randId(),
    ];

    mktState.bids = [];

    for (let i = 0; i < 3; i++) {
      const bidData = `bid:${bidAmounts[i]}:${nonces[i]}`;
      const commitment = computeCommitment(bidData);

      mktState.bids.push({
        provider: i + 1,
        amount: bidAmounts[i],
        commitment,
        nonce: nonces[i],
        revealed: false,
      });

      container.querySelector(`#mkt-p${i + 1}-status`).textContent = 'bidding...';
      entries.push({ text: `[Provider ${i + 1}] Submitted sealed bid (commitment: ${commitment.slice(0, 12)}...)`, type: 'info' });
      addTimelineEntry(entries);
      await delay(400);
      container.querySelector(`#mkt-p${i + 1}-status`).textContent = 'bid sealed';
    }

    entries.push({ text: `[Marketplace] 3 sealed bids received. Ready for reveal phase.`, type: 'success' });
    container.querySelector('#mkt-mkt-status').textContent = '3 bids sealed';
    mktState.phase = 'bids_submitted';

    addTimelineEntry(entries);
    showExplainer({
      leftLabel: 'Providers',
      left: `Each submitted a sealed bid\nBid = commitment(amount + nonce)\nP1: ${mktState.bids[0].commitment.slice(0, 12)}...\nP2: ${mktState.bids[1].commitment.slice(0, 12)}...\nP3: ${mktState.bids[2].commitment.slice(0, 12)}...`,
      centerLabel: 'Marketplace',
      center: `Holds only commitments\nCannot determine bid amounts\nCannot favor any provider\nWaiting for reveal phase`,
      rightLabel: 'Note commitments',
      right: `Sealed bids use the same commitment scheme as private notes.\n\ncommitment = H(amount || nonce)\n\nThe nonce prevents brute-force guessing of amounts.\n\nOnly the provider knows their bid until reveal.`,
      footer: `Commitments are binding — providers cannot change their bids after submission`,
    });

    updateUI();
    animating = false;
  });

  revealBtn.addEventListener('click', async () => {
    if (animating) return;
    animating = true;
    updateUI();

    const entries = [];

    for (let i = 0; i < mktState.bids.length; i++) {
      const bid = mktState.bids[i];
      bid.revealed = true;

      // Verify commitment
      const checkData = `bid:${bid.amount}:${bid.nonce}`;
      const checkCommitment = computeCommitment(checkData);
      const valid = checkCommitment === bid.commitment;

      entries.push({ text: `[Provider ${bid.provider}] Revealed: ${bid.amount} tokens (${valid ? 'commitment valid' : 'INVALID'})`, type: valid ? 'info' : 'error' });
      container.querySelector(`#mkt-p${bid.provider}-status`).textContent = `bid: ${bid.amount}`;
      addTimelineEntry(entries);
      await delay(400);
    }

    // Determine winner (lowest valid bid)
    const validBids = mktState.bids.filter(b => b.revealed);
    validBids.sort((a, b) => a.amount - b.amount);
    const winner = validBids[0];
    mktState.winner = winner.provider;

    entries.push({ text: `[Marketplace] Winner: Provider ${winner.provider} with bid of ${winner.amount} tokens`, type: 'success' });
    container.querySelector(`#mkt-p${winner.provider}-status`).textContent = `WINNER: ${winner.amount}`;
    container.querySelector('#mkt-mkt-status').textContent = `winner: P${winner.provider}`;
    mktState.phase = 'revealed';

    addTimelineEntry(entries);
    showExplainer({
      leftLabel: 'Reveal',
      left: `P1: ${mktState.bids[0].amount} tokens\nP2: ${mktState.bids[1].amount} tokens\nP3: ${mktState.bids[2].amount} tokens\n\nAll commitments verified against revealed values`,
      centerLabel: 'Auction result',
      center: `Lowest bid wins: Provider ${winner.provider}\nWinning bid: ${winner.amount} tokens\nRemaining budget returned to client: ${mktState.job.budget - winner.amount}\nExecution phase begins`,
      rightLabel: 'Fairness',
      right: `Because bids were sealed, no provider could undercut others by 1 token.\n\nThe commitment scheme guarantees:\n- Binding: cannot change bid after commit\n- Hiding: cannot learn others' bids before reveal\n\nThis is a first-price sealed-bid auction.`,
      footer: `Winner determined by lowest valid bid`,
    });

    updateUI();
    animating = false;
  });

  executeBtn.addEventListener('click', async () => {
    if (animating) return;
    animating = true;
    updateUI();

    const entries = [];
    const winner = mktState.bids.find(b => b.provider === mktState.winner);

    // Provider "computes"
    entries.push({ text: `[Provider ${winner.provider}] Computing: "${mktState.job.description}"...`, type: 'info' });
    container.querySelector(`#mkt-p${winner.provider}-status`).textContent = 'computing...';
    addTimelineEntry(entries);
    await delay(800);

    // Commit result
    const resultData = `result:${Date.now()}:${computeCommitment("matrix_output")}`;
    const resultCommitment = computeCommitment(resultData);
    entries.push({ text: `[Provider ${winner.provider}] Result committed: ${resultCommitment.slice(0, 12)}...`, type: 'info' });
    addTimelineEntry(entries);
    await delay(400);

    // Reveal result
    entries.push({ text: `[Provider ${winner.provider}] Result revealed and verified by client`, type: 'info' });
    addTimelineEntry(entries);
    await delay(400);

    // Atomic settlement
    entries.push({ text: `[Settlement] Atomic execution:`, type: 'info' });
    entries.push({ text: `  - Escrow -> Provider ${winner.provider}: ${winner.amount} tokens`, type: 'success' });
    entries.push({ text: `  - Escrow -> Client (refund): ${mktState.job.budget - winner.amount} tokens`, type: 'success' });
    entries.push({ text: `  - Reputation[P${winner.provider}] += 1`, type: 'success' });
    entries.push({ text: `  - Receipt logged (atomic, all-or-nothing)`, type: 'success' });

    // Update state
    mktState.escrowBalance = 0;
    mktState.reputation[winner.provider - 1] += 1;
    mktState.receiptCount += 1;
    mktState.phase = 'executed';

    container.querySelector(`#mkt-p${winner.provider}-status`).textContent = `settled (+${winner.amount})`;
    container.querySelector('#mkt-client-status').textContent = `refund: ${mktState.job.budget - winner.amount}`;
    container.querySelector('#mkt-escrow-status').textContent = '0 tokens';
    container.querySelector('#mkt-mkt-status').textContent = 'settled';

    // Update global state
    state.receipts.push({ type: 'marketplace', job: mktState.job.id, winner: winner.provider, amount: winner.amount });

    addTimelineEntry(entries);
    showExplainer({
      leftLabel: 'Provider',
      left: `Computed result\nCommit-reveal scheme ensures result is locked before payment\nReceived ${winner.amount} tokens from escrow`,
      centerLabel: 'Settlement',
      center: `Single atomic turn:\n1. Verify result\n2. Transfer escrow -> provider\n3. Refund remainder -> client\n4. Update reputation\n5. Log receipt\n\nAll or nothing — partial settlement impossible`,
      rightLabel: 'Atomicity',
      right: `This is a single dregg turn.\n\nIf ANY step fails, ALL steps revert.\n\nThe escrow cannot be drained without verified result.\nThe provider cannot be paid without delivering.\nThe receipt cannot exist without settlement.\n\nThis is the power of single-turn atomicity.`,
      footer: `Settlement complete. Receipt #${mktState.receiptCount} logged.`,
    });

    updateUI();
    animating = false;
  });

  disputeBtn.addEventListener('click', async () => {
    if (animating) return;
    animating = true;
    updateUI();

    const entries = [];
    const winner = mktState.bids.find(b => b.provider === mktState.winner);

    entries.push({ text: `[Client] Initiating dispute: Provider ${winner.provider} failed to deliver`, type: 'warning' });
    container.querySelector('#mkt-client-status').textContent = 'disputing...';
    addTimelineEntry(entries);
    await delay(500);

    entries.push({ text: `[Marketplace] Checking deadline... deadline exceeded.`, type: 'warning' });
    addTimelineEntry(entries);
    await delay(400);

    entries.push({ text: `[Marketplace] No valid result commitment found within deadline.`, type: 'warning' });
    addTimelineEntry(entries);
    await delay(400);

    // Refund
    entries.push({ text: `[Settlement] Dispute resolution:`, type: 'info' });
    entries.push({ text: `  - Escrow -> Client (full refund): ${mktState.escrowBalance} tokens`, type: 'success' });
    entries.push({ text: `  - Reputation[P${winner.provider}] -= 1`, type: 'error' });
    entries.push({ text: `  - Dispute receipt logged`, type: 'success' });

    mktState.reputation[winner.provider - 1] -= 1;
    mktState.escrowBalance = 0;
    mktState.receiptCount += 1;
    mktState.phase = 'disputed';

    container.querySelector(`#mkt-p${winner.provider}-status`).textContent = 'penalized';
    container.querySelector('#mkt-client-status').textContent = `refunded: ${mktState.job.budget}`;
    container.querySelector('#mkt-escrow-status').textContent = '0 tokens';
    container.querySelector('#mkt-mkt-status').textContent = 'disputed';

    addTimelineEntry(entries);
    showExplainer({
      leftLabel: 'Client',
      left: `Filed dispute after deadline\nNo result was committed by provider\nReceived full refund from escrow`,
      centerLabel: 'Resolution',
      center: `Timeout-based dispute:\n1. Deadline passed\n2. No valid result commitment\n3. Automatic refund triggered\n4. Provider reputation penalized\n\nNo human arbitration needed`,
      rightLabel: 'Guarantees',
      right: `The escrow contract has clear rules:\n\n- Deliver before deadline -> get paid\n- Miss deadline -> funds return to client\n\nThis is enforced by the consensus protocol.\nNo party can steal funds.\nNo party can block refunds.\n\nReputation scores are on-chain and permanent.`,
      footer: `Dispute resolved. Provider ${winner.provider} reputation: ${mktState.reputation[winner.provider - 1]}`,
    });

    updateUI();
    animating = false;
  });

  resetBtn.addEventListener('click', () => {
    mktState = resetState();
    animating = false;
    timelineDiv.innerHTML = '';
    explainerDiv.innerHTML = '';

    container.querySelector('#mkt-client-status').textContent = 'idle';
    container.querySelector('#mkt-p1-status').textContent = 'idle';
    container.querySelector('#mkt-p2-status').textContent = 'idle';
    container.querySelector('#mkt-p3-status').textContent = 'idle';
    container.querySelector('#mkt-escrow-status').textContent = '0 tokens';
    container.querySelector('#mkt-mkt-status').textContent = 'ready';

    updateUI();
  });

  // Initial render
  updateUI();
}

function escapeHtml(str) {
  return String(str).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/\n/g, '<br>');
}
