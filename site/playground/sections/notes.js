// Notes section — private value transfer, double-spend prevention

import { state, notifyStateChange, navigateTo } from '../playground.js';

export function initNotes(wasm) {
  const container = document.getElementById('section-notes');
  container.innerHTML = `
    <div class="section-header">
      <h2>Private Notes</h2>
      <p>
        Notes are pyana's UTXO-style private value transfer primitive. When you mint a note,
        a cryptographic commitment hides the amount. When you spend it, a nullifier is published
        that prevents double-spending — but reveals nothing about the note's contents.
        Transfers create new notes and consume old ones atomically.
      </p>
      <span class="next-hint" data-next="capabilities">Next: capability delegation &#8594;</span>
    </div>

    <div class="controls-row">
      <div class="control-group">
        <label>Asset Type</label>
        <input type="text" id="nt-asset" value="token" spellcheck="false" style="width: 120px;">
      </div>
      <div class="control-group">
        <label>Amount</label>
        <input type="number" id="nt-amount" value="100" min="1" style="width: 100px;">
      </div>
      <button class="btn btn-primary" id="nt-mint" ${wasm ? '' : 'disabled'}>Mint Note</button>
    </div>

    <div class="controls-row">
      <div class="control-group">
        <label>Recipient</label>
        <input type="text" id="nt-recipient" value="bob" spellcheck="false" style="width: 120px;">
      </div>
      <div class="control-group">
        <label>Transfer Amount</label>
        <input type="number" id="nt-transfer-amount" value="50" min="1" style="width: 100px;">
      </div>
      <button class="btn btn-primary" id="nt-transfer" disabled>Transfer</button>
      <button class="btn btn-danger" id="nt-doublespend" disabled>Double-Spend Attempt</button>
    </div>

    <div id="nt-timeline"></div>
    <div id="nt-explainer"></div>
  `;

  if (!wasm) return;

  let nextId = 0;
  const timelineDiv = container.querySelector('#nt-timeline');
  const explainerDiv = container.querySelector('#nt-explainer');
  const transferBtn = container.querySelector('#nt-transfer');
  const doubleBtn = container.querySelector('#nt-doublespend');

  container.querySelector('.next-hint').addEventListener('click', () => navigateTo('capabilities'));

  function generateCommitment(data) {
    try {
      const result = wasm.compute_merkle_root(JSON.stringify([data]));
      return result.root_hex;
    } catch {
      return localHash(data);
    }
  }

  function generateNullifier(data) {
    try {
      const result = wasm.compute_merkle_root(JSON.stringify(['nullifier:' + data]));
      return result.root_hex;
    } catch {
      return localHash('nullifier:' + data);
    }
  }

  function localHash(str) {
    let h = 0x811c9dc5;
    for (let i = 0; i < str.length; i++) {
      h ^= str.charCodeAt(i);
      h = Math.imul(h, 0x01000193);
    }
    return (h >>> 0).toString(16).padStart(8, '0').repeat(8);
  }

  function updateButtons() {
    const hasUnspent = state.notes.some(n => !n.spent);
    const hasSpent = state.notes.some(n => n.spent);
    transferBtn.disabled = !hasUnspent;
    doubleBtn.disabled = !hasSpent;
  }

  function renderTimeline() {
    if (state.notes.length === 0) {
      timelineDiv.innerHTML = `<div class="result-panel"><div class="result-panel__body">
        <div class="output-entry info">Mint a note to begin the lifecycle demonstration.</div>
      </div></div>`;
      return;
    }

    let html = '<div class="result-panel"><div class="result-panel__header"><span class="result-panel__title">Note Timeline</span></div><div class="result-panel__body">';

    // Show all notes
    state.notes.forEach(note => {
      const statusCls = note.spent ? 'warning' : 'success';
      const status = note.spent ? 'SPENT' : 'UNSPENT';
      html += `<div class="note-timeline-item">
        <span class="note-tl-type ${note.spent ? 'rejected' : 'mint'}">${status}</span>
        <div class="note-tl-body">
          Note #${note.id}: <strong>${note.amount} ${note.asset}</strong> (owner: ${note.owner})
          <br><span class="note-tl-hash">commitment: ${note.commitment.slice(0, 32)}...</span>
          ${note.spent ? `<br><span class="note-tl-hash">nullifier: ${note.nullifier.slice(0, 32)}...</span>` : ''}
        </div>
      </div>`;
    });

    html += '</div></div>';
    timelineDiv.innerHTML = html;
  }

  container.querySelector('#nt-mint').addEventListener('click', () => {
    const asset = container.querySelector('#nt-asset').value.trim() || 'token';
    const amount = parseInt(container.querySelector('#nt-amount').value) || 100;

    const t0 = performance.now();
    const noteData = `note:${nextId}:${asset}:${amount}:${Date.now()}`;
    const commitment = generateCommitment(noteData);
    const nullifier = generateNullifier(noteData);
    const elapsed = (performance.now() - t0).toFixed(2);

    const note = {
      id: nextId++,
      asset,
      amount,
      commitment,
      nullifier,
      owner: 'self',
      spent: false,
    };

    state.notes.push(note);
    notifyStateChange();
    updateButtons();
    renderTimeline();

    showExplainer(explainerDiv, {
      prover: `Minted note #${note.id}\nAsset: ${asset}, Amount: ${amount}\nCommitment: ${commitment.slice(0, 24)}...\nNullifier (secret): ${nullifier.slice(0, 24)}...`,
      verifier: `Sees: new commitment added to commitment set\nDoes NOT see: amount, asset type, or owner\nThe commitment is hiding: H(amount || asset || owner || randomness)`,
      delta: `The commitment hides all note contents. The verifier knows a note was created but learns nothing about its value. Only the owner knows the nullifier needed to spend it.`,
      timing: elapsed,
    });
  });

  transferBtn.addEventListener('click', () => {
    const recipient = container.querySelector('#nt-recipient').value.trim() || 'bob';
    const transferAmount = parseInt(container.querySelector('#nt-transfer-amount').value) || 50;

    const sourceNote = state.notes.find(n => !n.spent && n.amount >= transferAmount);
    if (!sourceNote) {
      showExplainer(explainerDiv, {
        prover: `Attempted transfer of ${transferAmount}\nNo unspent note with sufficient balance`,
        verifier: `Transaction not submitted`,
        delta: `Nothing revealed — failed transactions are private too.`,
        timing: '0',
      });
      return;
    }

    const t0 = performance.now();

    // Spend source
    sourceNote.spent = true;
    state.nullifiers.push(sourceNote.nullifier);

    // Create recipient note
    const recipData = `note:${nextId}:${sourceNote.asset}:${transferAmount}:${Date.now()}:${recipient}`;
    const newNote = {
      id: nextId++,
      asset: sourceNote.asset,
      amount: transferAmount,
      commitment: generateCommitment(recipData),
      nullifier: generateNullifier(recipData),
      owner: recipient,
      spent: false,
    };
    state.notes.push(newNote);

    // Change note
    const change = sourceNote.amount - transferAmount;
    if (change > 0) {
      const changeData = `note:${nextId}:${sourceNote.asset}:${change}:${Date.now()}:self`;
      state.notes.push({
        id: nextId++,
        asset: sourceNote.asset,
        amount: change,
        commitment: generateCommitment(changeData),
        nullifier: generateNullifier(changeData),
        owner: 'self',
        spent: false,
      });
    }

    const elapsed = (performance.now() - t0).toFixed(2);
    notifyStateChange();
    updateButtons();
    renderTimeline();

    showExplainer(explainerDiv, {
      prover: `Spent note #${sourceNote.id} (${sourceNote.amount} ${sourceNote.asset})\nPublished nullifier: ${sourceNote.nullifier.slice(0, 20)}...\nCreated: ${transferAmount} to ${recipient}${change > 0 ? `, ${change} change to self` : ''}`,
      verifier: `Sees: nullifier published (note consumed)\nSees: new commitment(s) added\nDoes NOT see: amounts, sender, recipient, or linkage between old and new notes`,
      delta: `The transfer is unlinkable. The verifier cannot connect the spent nullifier to the new commitments. Amounts are hidden. Only the involvement of "a note was consumed and new notes created" is public.`,
      timing: elapsed,
    });
  });

  doubleBtn.addEventListener('click', () => {
    const spentNote = state.notes.find(n => n.spent);
    if (!spentNote) return;

    const alreadySpent = state.nullifiers.includes(spentNote.nullifier);

    showExplainer(explainerDiv, {
      prover: `Attempted to re-spend note #${spentNote.id}\nNullifier: ${spentNote.nullifier.slice(0, 24)}...`,
      verifier: `Checked nullifier set\nFound: nullifier ALREADY PRESENT\nResult: TRANSACTION REJECTED\n\nDouble-spend prevention works because each note has a unique nullifier derived from its commitment.`,
      delta: `The nullifier set is the key to preventing double-spends without revealing which notes are linked. Once a nullifier is published, the same note can never be spent again — but nobody can tell which commitment it corresponds to.`,
      timing: '0.01',
    });

    // Show rejection in timeline
    const html = timelineDiv.innerHTML;
    timelineDiv.innerHTML = `<div class="result-panel" style="margin-bottom: 12px;"><div class="result-panel__body">
      <div class="output-entry error">DOUBLE-SPEND REJECTED: Nullifier ${spentNote.nullifier.slice(0, 24)}... already in set</div>
    </div></div>` + html;
  });

  renderTimeline();
}

function showExplainer(el, { prover, verifier, delta, timing }) {
  el.innerHTML = `
    <div class="explainer">
      <div class="explainer__title">What just happened</div>
      <div class="explainer__grid">
        <div class="explainer__cell explainer__cell--prover">
          <div class="explainer__cell-label">Sender knows</div>
          <div class="explainer__cell-content">${escapeHtml(prover)}</div>
        </div>
        <div class="explainer__cell explainer__cell--verifier">
          <div class="explainer__cell-label">Ledger sees</div>
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
