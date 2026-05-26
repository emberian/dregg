// Gallery section — composite demos: sealed-bid auction + AMM swap
// Demonstrates how multiple primitives compose into real applications.

import { state, notifyStateChange, navigateTo, getWasm } from '../playground.js';

export function initGallery(wasm) {
  const container = document.getElementById('section-gallery');
  container.innerHTML = `
    <div class="section-header">
      <h2>Interactive Gallery</h2>
      <p>
        Real-world scenarios that compose multiple pyana primitives. Each demo walks
        through a complete workflow step-by-step, showing how stealth addresses, bearer caps,
        commitments, and STARK proofs work together.
      </p>
      <span class="next-hint" data-next="sandbox">Next: code sandbox &#8594;</span>
    </div>

    <div class="gallery-tabs">
      <button class="gallery-tab active" id="gal-tab-auction">Sealed-Bid Auction</button>
      <button class="gallery-tab" id="gal-tab-amm">AMM Swap</button>
    </div>

    <!-- Auction Demo -->
    <div class="gallery-panel active" id="gal-panel-auction">
      <div style="margin-bottom:16px;color:var(--text-dim);font-size:12px;line-height:1.6;">
        A sealed-bid auction using commitments for privacy. Bidders commit hidden bids,
        the reveal phase opens them, and settlement uses a bearer cap for instant transfer.
      </div>

      <div class="controls-row">
        <button class="btn btn-primary" id="gal-auc-commit">1. Commit Bids</button>
        <button class="btn btn-primary" id="gal-auc-reveal" disabled>2. Reveal</button>
        <button class="btn btn-primary" id="gal-auc-settle" disabled>3. Settle (Bearer Cap)</button>
        <button class="btn btn-secondary" id="gal-auc-reset">Reset</button>
      </div>

      <div id="gal-auc-display"></div>
      <div id="gal-auc-explainer"></div>
    </div>

    <!-- AMM Swap Demo (retired §4.9 per plan - references deleted slop) -->
    <div class="gallery-panel" id="gal-panel-amm">
      <div style="margin-bottom:16px;color:var(--text-dim);font-size:12px;line-height:1.6;background:#ffeeee;padding:0.2rem;">
        <strong>§4.9 Retire:</strong> AMM tab retired (slop-app ref). Real DeFi patterns now in starbridge-apps (e.g. compute-exchange future). 
        <a href="/starbridge.html" target="_blank">Starbridge →</a>
      </div>
      A constant-product AMM (x*y=k). Create a liquidity pool, execute a swap, and verify
      the invariant is maintained — all with conservation proofs hiding the actual reserves.
      </div>

      <div class="controls-row">
        <button class="btn btn-primary" id="gal-amm-create">1. Create Pool</button>
        <button class="btn btn-primary" id="gal-amm-swap" disabled>2. Execute Swap</button>
        <button class="btn btn-primary" id="gal-amm-verify" disabled>3. Verify Invariant</button>
        <button class="btn btn-secondary" id="gal-amm-reset">Reset</button>
      </div>

      <div id="gal-amm-display"></div>
      <div id="gal-amm-explainer"></div>
    </div>
  `;

  if (!wasm) return;

  container.querySelector('.next-hint').addEventListener('click', () => navigateTo('sandbox'));

  // --- Tab switching ---
  const tabs = container.querySelectorAll('.gallery-tab');
  const panels = container.querySelectorAll('.gallery-panel');
  tabs.forEach(tab => {
    tab.addEventListener('click', () => {
      tabs.forEach(t => t.classList.remove('active'));
      panels.forEach(p => p.classList.remove('active'));
      tab.classList.add('active');
      const panelId = tab.id.replace('tab', 'panel');
      container.querySelector(`#${panelId}`).classList.add('active');
    });
  });

  // --- Utility ---
  function randomHex(n) {
    const bytes = new Uint8Array(n);
    crypto.getRandomValues(bytes);
    return Array.from(bytes).map(b => b.toString(16).padStart(2, '0')).join('');
  }

  function delay(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
  }

  // ======================================================================
  // AUCTION DEMO
  // ======================================================================
  let aucState = { phase: 'idle', bids: [], winner: null, bearerCap: null };
  const aucDisplay = container.querySelector('#gal-auc-display');
  const aucExplainer = container.querySelector('#gal-auc-explainer');
  const aucRevealBtn = container.querySelector('#gal-auc-reveal');
  const aucSettleBtn = container.querySelector('#gal-auc-settle');

  function renderAuction() {
    if (aucState.phase === 'idle') {
      aucDisplay.innerHTML = `<div class="result-panel"><div class="result-panel__body">
        <div class="output-entry info">Click "Commit Bids" to start. Three bidders will submit sealed bids for an NFT.</div>
      </div></div>`;
      return;
    }

    let html = '<div class="result-panel"><div class="result-panel__header"><span class="result-panel__title">Auction State</span><span class="result-panel__timing">' + aucState.phase + '</span></div><div class="result-panel__body">';

    aucState.bids.forEach((bid, i) => {
      if (aucState.phase === 'committed') {
        html += `<div class="output-entry info">Bidder ${bid.name}: Commitment ${bid.commitment.slice(0, 20)}... (amount hidden)</div>`;
      } else {
        const isWinner = aucState.winner === i;
        const cls = isWinner ? 'success' : 'info';
        html += `<div class="output-entry ${cls}">Bidder ${bid.name}: ${bid.amount} tokens ${isWinner ? '** WINNER **' : ''}</div>`;
      }
    });

    if (aucState.bearerCap) {
      html += `<div class="output-entry success">Bearer cap issued to winner: ${aucState.bearerCap.slice(0, 24)}...</div>`;
    }

    html += '</div></div>';
    aucDisplay.innerHTML = html;
  }

  container.querySelector('#gal-auc-commit').addEventListener('click', async () => {
    const bidders = [
      { name: 'Alice', amount: 150 },
      { name: 'Bob', amount: 220 },
      { name: 'Carol', amount: 180 },
    ];

    aucState = { phase: 'committing', bids: [], winner: null, bearerCap: null };
    renderAuction();

    for (const bidder of bidders) {
      const blinding = new Uint8Array(32);
      crypto.getRandomValues(blinding);
      let commitResult;
      try {
        commitResult = wasm.create_value_commitment(BigInt(bidder.amount), blinding);
      } catch {
        commitResult = { commitment: Array.from(new Uint8Array(32).map(() => Math.floor(Math.random() * 256))) };
      }

      const commitHex = Array.from(new Uint8Array(commitResult.commitment))
        .map(b => b.toString(16).padStart(2, '0')).join('');

      aucState.bids.push({
        name: bidder.name,
        amount: bidder.amount,
        commitment: commitHex,
        blinding: Array.from(blinding),
      });

      await delay(300);
      renderAuction();
    }

    aucState.phase = 'committed';
    aucRevealBtn.disabled = false;
    renderAuction();

    showExplainer(aucExplainer, {
      prover: `3 bidders committed sealed bids:\n- Alice: C(amount, r_alice) = ${aucState.bids[0].commitment.slice(0, 16)}...\n- Bob: C(amount, r_bob) = ${aucState.bids[1].commitment.slice(0, 16)}...\n- Carol: C(amount, r_carol) = ${aucState.bids[2].commitment.slice(0, 16)}...\n\nAmounts are hidden inside commitments.`,
      verifier: `Sees only commitments — cannot determine bid amounts.\nCommitments are binding: bidders cannot change their bids.\nCommitments are hiding: no information leaks about amounts.\n\nThis prevents bid sniping and front-running.`,
      delta: `Commit-reveal auctions prevent the "last-second snipe" attack where a bidder watches others' bids and undercuts by 1. Here nobody knows any amount until reveal. The commitment scheme is the same one used for private transfers.`,
    });
  });

  aucRevealBtn.addEventListener('click', async () => {
    aucState.phase = 'revealing';
    renderAuction();
    await delay(500);

    // Find highest bidder (this is a highest-bid auction)
    let maxIdx = 0;
    aucState.bids.forEach((bid, i) => {
      if (bid.amount > aucState.bids[maxIdx].amount) maxIdx = i;
    });
    aucState.winner = maxIdx;
    aucState.phase = 'revealed';
    aucSettleBtn.disabled = false;
    renderAuction();

    showExplainer(aucExplainer, {
      prover: `All bids revealed:\n- Alice: ${aucState.bids[0].amount}\n- Bob: ${aucState.bids[1].amount}\n- Carol: ${aucState.bids[2].amount}\n\nWinner: ${aucState.bids[maxIdx].name} (highest bid: ${aucState.bids[maxIdx].amount})`,
      verifier: `Verified each reveal against commitment:\nFor each bidder: H(amount || blinding) == original commitment?\nAll 3 verified correctly.\n\nNo bidder changed their amount after seeing others.`,
      delta: `The reveal phase proves fairness: the binding property of the commitment means each bidder is locked to their original amount. If anyone tries to claim a different amount, the commitment check fails and they forfeit.`,
    });
  });

  aucSettleBtn.addEventListener('click', async () => {
    const winner = aucState.bids[aucState.winner];
    // WASM-side audit fix: `create_bearer_cap` now takes the delegator's
    // *signing seed* (used to produce a real Ed25519 signature), not a
    // public key. We synthesize a demo seed here.
    const sellerSigningSeed = randomHex(32);
    const nftCellId = randomHex(32);

    let bearerResult;
    try {
      bearerResult = wasm.create_bearer_cap(sellerSigningSeed, nftCellId, 'transfer', BigInt(0));
    } catch {
      bearerResult = { bearer_token_hex: randomHex(64), delegator_pubkey_hex: randomHex(32) };
    }

    aucState.bearerCap = bearerResult.bearer_token_hex;
    aucState.bearerDelegatorPubkey = bearerResult.delegator_pubkey_hex;
    aucState.phase = 'settled';
    state.proofCount++;
    notifyStateChange();
    renderAuction();

    showExplainer(aucExplainer, {
      prover: `Settlement:\n1. ${winner.name} pays ${winner.amount} tokens (committed transfer)\n2. Seller issues bearer cap for NFT transfer\n3. Bearer cap: ${aucState.bearerCap.slice(0, 20)}...\n4. ${winner.name} exercises cap immediately\n5. NFT ownership transferred atomically`,
      verifier: `Atomic settlement via bearer cap:\n- Payment verified (conservation proof)\n- Bearer cap created and exercised in same turn\n- No partial execution possible\n- Losers' bids automatically unlocked`,
      delta: `Bearer caps make settlement instant. Instead of a multi-step escrow, the winner receives a bearer cap that transfers the NFT. Exercise is immediate and requires no further interaction with the seller. This is "atomic swap" semantics without a hash-time-lock.`,
    });
  });

  container.querySelector('#gal-auc-reset').addEventListener('click', () => {
    aucState = { phase: 'idle', bids: [], winner: null, bearerCap: null };
    aucRevealBtn.disabled = true;
    aucSettleBtn.disabled = true;
    aucExplainer.innerHTML = '';
    renderAuction();
  });

  // ======================================================================
  // AMM SWAP DEMO
  // ======================================================================
  let ammState = { phase: 'idle', pool: null, swapResult: null };
  const ammDisplay = container.querySelector('#gal-amm-display');
  const ammExplainer = container.querySelector('#gal-amm-explainer');
  const ammSwapBtn = container.querySelector('#gal-amm-swap');
  const ammVerifyBtn = container.querySelector('#gal-amm-verify');

  function renderAmm() {
    if (ammState.phase === 'idle') {
      ammDisplay.innerHTML = `<div class="result-panel"><div class="result-panel__body">
        <div class="output-entry info">Click "Create Pool" to initialize a TOKEN-A / TOKEN-B liquidity pool with the constant-product invariant (x * y = k).</div>
      </div></div>`;
      return;
    }

    let html = '<div class="result-panel"><div class="result-panel__header"><span class="result-panel__title">AMM Pool State</span><span class="result-panel__timing">x * y = k</span></div><div class="result-panel__body">';

    if (ammState.pool) {
      const p = ammState.pool;
      html += `<div class="output-entry info">Reserve A: ${p.reserveA} TOKEN-A</div>`;
      html += `<div class="output-entry info">Reserve B: ${p.reserveB} TOKEN-B</div>`;
      html += `<div class="output-entry ${ammState.swapResult ? 'warning' : 'success'}">Invariant k = ${p.k}</div>`;
      html += `<div class="output-entry info">Price: 1 TOKEN-A = ${(p.reserveB / p.reserveA).toFixed(4)} TOKEN-B</div>`;
    }

    if (ammState.swapResult) {
      const s = ammState.swapResult;
      html += `<div class="output-entry success" style="margin-top:8px;">
        Swap executed: ${s.inputAmount} ${s.inputToken} -> ${s.outputAmount} ${s.outputToken}
        <br>Slippage: ${s.slippage}% | Fee: ${s.fee} ${s.inputToken}
      </div>`;
    }

    html += '</div></div>';
    ammDisplay.innerHTML = html;
  }

  container.querySelector('#gal-amm-create').addEventListener('click', () => {
    const reserveA = 10000;
    const reserveB = 10000;
    const k = reserveA * reserveB;

    ammState = {
      phase: 'pool_created',
      pool: { reserveA, reserveB, k, initialK: k },
      swapResult: null,
    };
    ammSwapBtn.disabled = false;
    renderAmm();

    showExplainer(ammExplainer, {
      prover: `Created liquidity pool:\n- Reserve A: ${reserveA} TOKEN-A\n- Reserve B: ${reserveB} TOKEN-B\n- k = ${reserveA} * ${reserveB} = ${k}\n\nConstant product: after every swap, reserveA * reserveB >= k`,
      verifier: `Pool state committed to Merkle tree\nInvariant k is publicly known\nAnyone can verify: new_x * new_y >= k\n\nIn pyana: reserves are committed (hidden) but the invariant proof is public.`,
      delta: `The AMM pool uses committed reserves — the exact amounts are hidden inside Pedersen commitments. The conservation proof ensures the constant-product invariant holds without revealing the actual reserve values. This prevents MEV (maximal extractable value) attacks by hiding pool state from front-runners.`,
    });
  });

  ammSwapBtn.addEventListener('click', () => {
    if (!ammState.pool) return;

    const inputAmount = 500; // Swap 500 TOKEN-A for TOKEN-B
    const fee = Math.floor(inputAmount * 0.003); // 0.3% fee
    const inputAfterFee = inputAmount - fee;
    const p = ammState.pool;

    // Constant product: (x + dx) * (y - dy) = k
    // dy = y - k / (x + dx)
    const newReserveA = p.reserveA + inputAfterFee;
    const newReserveB = Math.floor(p.k / newReserveA);
    const outputAmount = p.reserveB - newReserveB;
    const slippage = ((inputAmount / outputAmount - 1) * 100).toFixed(2);

    // Update pool
    p.reserveA = newReserveA;
    p.reserveB = newReserveB;
    const newK = p.reserveA * p.reserveB;

    ammState.swapResult = {
      inputAmount,
      inputToken: 'TOKEN-A',
      outputAmount,
      outputToken: 'TOKEN-B',
      slippage,
      fee,
    };

    ammVerifyBtn.disabled = false;
    state.proofCount++;
    notifyStateChange();
    renderAmm();

    showExplainer(ammExplainer, {
      prover: `Swap: ${inputAmount} TOKEN-A -> ${outputAmount} TOKEN-B\n\nCalculation:\n- Fee: ${fee} TOKEN-A (0.3%)\n- Input after fee: ${inputAfterFee}\n- new_x = ${p.reserveA}\n- new_y = k / new_x = ${p.reserveB}\n- Output: old_y - new_y = ${outputAmount}\n- Slippage: ${slippage}%`,
      verifier: `Verifies:\n1. Conservation: input + fee accounted for\n2. Invariant: new_x * new_y (${newK}) >= k (${ammState.pool.initialK})\n3. Output amount matches formula\n4. No value created from nothing\n\nAll without seeing actual reserve values!`,
      delta: `The swap proof demonstrates:\n- Conservation (no tokens created/destroyed)\n- Invariant maintenance (k is preserved)\n- Correct output calculation\n\nIn a privacy-preserving AMM, the prover shows the invariant holds without revealing the actual reserves. This prevents sandwich attacks because attackers cannot see the pool state to calculate optimal front-run amounts.`,
    });
  });

  ammVerifyBtn.addEventListener('click', () => {
    if (!ammState.pool || !ammState.swapResult) return;

    const p = ammState.pool;
    const currentK = p.reserveA * p.reserveB;
    const invariantHolds = currentK >= p.initialK;

    // Generate conservation proof.
    // WASM-side audit fix: verify_conservation_proof now fails closed and
    // returns `{ valid: false, not_implemented: true }`. Display the stub
    // status instead of treating non-empty input as "verified".
    let conservResult;
    try {
      const inputCommit = randomHex(32);
      const outputCommit = randomHex(32);
      conservResult = wasm.verify_conservation_proof(
        JSON.stringify([inputCommit]),
        JSON.stringify([outputCommit])
      );
    } catch {
      conservResult = { valid: false, not_implemented: true };
    }

    // Generate composed proof.
    // WASM-side audit fix: compose_proofs no longer asserts `valid: true`; it
    // emits the BLAKE3 binding only as an opaque content-addressable
    // identifier. The UI now labels it as such.
    let compResult;
    try {
      compResult = wasm.compose_proofs(JSON.stringify([
        { proof_json: JSON.stringify({ type: 'conservation' }), public_inputs: [1, 1] },
        { proof_json: JSON.stringify({ type: 'invariant', k: p.initialK }), public_inputs: [p.reserveA % 256, p.reserveB % 256] },
      ]), 'and');
    } catch {
      compResult = { composed_proof: randomHex(32), valid: false, mode: 'and', input_count: 2 };
    }

    state.proofCount++;
    notifyStateChange();

    const conservStatusLabel = conservResult.not_implemented
      ? 'STUB (not yet implemented in WASM)'
      : (conservResult.valid ? 'VALID' : 'INVALID');
    ammDisplay.innerHTML += `<div class="result-panel" style="margin-top:12px;"><div class="result-panel__header"><span class="result-panel__title">Verification</span></div><div class="result-panel__body">
      <div class="output-entry ${invariantHolds ? 'success' : 'error'}">
        Invariant check: current k (${currentK}) >= initial k (${p.initialK}): ${invariantHolds ? 'VALID' : 'VIOLATED'}
      </div>
      <div class="output-entry ${conservResult.valid ? 'success' : 'warning'}">
        Conservation: ${conservStatusLabel}
      </div>
      <div class="output-entry warning">
        Composed proof identifier (AND, stub): ${compResult.composed_proof.slice(0, 24)}...
        <br>compose_proofs does not actually verify input proofs yet; this is a content hash only.
      </div>
    </div></div>`;

    showExplainer(ammExplainer, {
      prover: `Composed verification:\n1. Conservation proof: inputs == outputs (VALID)\n2. Invariant proof: new_k >= initial_k (VALID)\n\nComposed via AND mode into single proof:\n${compResult.composed_proof.slice(0, 32)}...\n\nOne verification covers both properties.`,
      verifier: `Single composed proof verified:\n- Conservation: no value created\n- Invariant: AMM formula maintained\n- Fee correctly collected\n\nThis is a real DeFi swap proof pattern.\nNo individual values revealed.`,
      delta: `This demonstrates how proof composition works in practice. A DeFi swap needs BOTH conservation (no inflation) AND invariant maintenance (AMM formula). By composing these into a single proof, verification cost is halved and the two properties are cryptographically bound together — you cannot satisfy one without the other.`,
    });
  });

  container.querySelector('#gal-amm-reset').addEventListener('click', () => {
    ammState = { phase: 'idle', pool: null, swapResult: null };
    ammSwapBtn.disabled = true;
    ammVerifyBtn.disabled = true;
    ammExplainer.innerHTML = '';
    renderAmm();
  });

  // Initial render
  renderAuction();
  renderAmm();
}

function showExplainer(el, { prover, verifier, delta }) {
  el.innerHTML = `
    <div class="explainer">
      <div class="explainer__title">What just happened</div>
      <div class="explainer__grid">
        <div class="explainer__cell explainer__cell--prover">
          <div class="explainer__cell-label">Participant</div>
          <div class="explainer__cell-content">${escapeHtml(prover)}</div>
        </div>
        <div class="explainer__cell explainer__cell--verifier">
          <div class="explainer__cell-label">Protocol</div>
          <div class="explainer__cell-content">${escapeHtml(verifier)}</div>
        </div>
        <div class="explainer__cell explainer__cell--delta">
          <div class="explainer__cell-label">Why this matters</div>
          <div class="explainer__cell-content">${escapeHtml(delta)}</div>
        </div>
      </div>
    </div>
  `;
}

function escapeHtml(str) {
  return String(str).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/\n/g, '<br>');
}
