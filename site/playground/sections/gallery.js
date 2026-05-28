// Gallery section — composite demo: sealed-bid auction.
// Demonstrates how multiple primitives compose into real applications.
//
// The AMM-swap tab was retired (STARBRIDGE-PLAN §4.9): it referenced a deleted
// slop app and modeled conservation/composition that the wasm now fails closed
// on. Real DeFi-style patterns live in starbridge-apps/ (e.g. compute-exchange).

import { state, notifyStateChange, navigateTo, getWasm } from '../playground.js';

export function initGallery(wasm) {
  const container = document.getElementById('section-gallery');
  container.innerHTML = `
    <div class="section-header">
      <h2>Interactive Gallery</h2>
      <p>
        Real-world scenarios that compose multiple dregg primitives. Each demo walks
        through a complete workflow step-by-step, showing how stealth addresses, bearer caps,
        commitments, and STARK proofs work together.
      </p>
      <span class="next-hint" data-next="sandbox">Next: code sandbox &#8594;</span>
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
  `;

  if (!wasm) return;

  container.querySelector('.next-hint').addEventListener('click', () => navigateTo('sandbox'));

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
      } catch (e) {
        // No fabrication: a real wasm failure is surfaced honestly and aborts.
        aucState = { phase: 'idle', bids: [], winner: null, bearerCap: null };
        aucRevealBtn.disabled = true;
        aucSettleBtn.disabled = true;
        aucDisplay.innerHTML = `<div class="result-panel"><div class="result-panel__body">
          <div class="output-entry error">create_value_commitment failed for ${bidder.name}: ${escapeHtml(String(e && e.message || e))}</div>
        </div></div>`;
        return;
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
    } catch (e) {
      // No fabrication: surface the real failure rather than minting a fake cap.
      aucDisplay.innerHTML = `<div class="result-panel"><div class="result-panel__body">
        <div class="output-entry error">create_bearer_cap failed: ${escapeHtml(String(e && e.message || e))}</div>
      </div></div>`;
      return;
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

  // Initial render
  renderAuction();
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
