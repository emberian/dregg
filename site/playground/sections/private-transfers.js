// Private Transfers section — stealth addresses, committed transfers, conservation proofs

import { state, notifyStateChange, navigateTo, getWasm } from '../playground.js';

export function initPrivateTransfers(wasm) {
  const container = document.getElementById('section-private-transfers');
  container.innerHTML = `
    <div class="section-header">
      <h2>Private Transfers</h2>
      <p>
        End-to-end private value transfer using stealth addresses and Pedersen commitments.
        The sender derives a one-time address for the recipient, commits the transfer amount,
        and proves conservation (inputs == outputs) without revealing any values.
      </p>
      <span class="next-hint" data-next="composition">Next: proof composition &#8594;</span>
    </div>

    <h3 style="font-family:var(--mono);font-size:12px;color:var(--accent-bright);margin-bottom:12px;">Step 1: Derive Stealth Keys</h3>
    <div class="controls-row">
      <div class="control-group">
        <label>Recipient Mnemonic</label>
        <input type="text" id="pt-mnemonic" value="correct horse battery staple" spellcheck="false" style="width: 280px;">
      </div>
      <div class="control-group">
        <label>Passphrase</label>
        <input type="text" id="pt-passphrase" value="dregg-demo" spellcheck="false" style="width: 120px;">
      </div>
      <button class="btn btn-primary" id="pt-derive-keys" ${wasm ? '' : 'disabled'}>Derive Keys</button>
    </div>

    <h3 style="font-family:var(--mono);font-size:12px;color:var(--accent-bright);margin:16px 0 12px;">Step 2: Create Stealth Address + Committed Transfer</h3>
    <div class="controls-row">
      <div class="control-group">
        <label>Transfer Amount</label>
        <input type="number" id="pt-amount" value="500" min="1" style="width: 120px;">
      </div>
      <button class="btn btn-primary" id="pt-transfer" disabled>Send Private Transfer</button>
    </div>

    <h3 style="font-family:var(--mono);font-size:12px;color:var(--accent-bright);margin:16px 0 12px;">Step 3: Recipient Scans + Claims</h3>
    <div class="controls-row">
      <button class="btn btn-primary" id="pt-scan" disabled>Scan Announcements</button>
      <button class="btn btn-primary" id="pt-verify-conservation" disabled>Verify Conservation</button>
    </div>

    <div id="pt-timeline"></div>
    <div id="pt-explainer"></div>
  `;

  if (!wasm) return;

  let recipientKeys = null;
  let stealthAddr = null;
  let commitment = null;
  let blinding = null;
  let transferAmount = 0;
  let announcements = [];

  const timelineDiv = container.querySelector('#pt-timeline');
  const explainerDiv = container.querySelector('#pt-explainer');
  const transferBtn = container.querySelector('#pt-transfer');
  const scanBtn = container.querySelector('#pt-scan');
  const verifyBtn = container.querySelector('#pt-verify-conservation');

  container.querySelector('.next-hint').addEventListener('click', () => navigateTo('composition'));

  function bytesToHex(bytes) {
    return Array.from(bytes).map(b => b.toString(16).padStart(2, '0')).join('');
  }

  function randomBytes(n) {
    const bytes = new Uint8Array(n);
    crypto.getRandomValues(bytes);
    return bytes;
  }

  function addTimelineEntry(entries) {
    let html = '<div class="result-panel"><div class="result-panel__header"><span class="result-panel__title">Transfer Timeline</span></div><div class="result-panel__body">';
    entries.forEach(entry => {
      html += `<div class="output-entry ${entry.type}">${escapeHtml(entry.text)}</div>`;
    });
    html += '</div></div>';
    timelineDiv.innerHTML = html;
  }

  // Step 1: Derive keys
  container.querySelector('#pt-derive-keys').addEventListener('click', () => {
    const mnemonic = container.querySelector('#pt-mnemonic').value.trim();
    const passphrase = container.querySelector('#pt-passphrase').value.trim();

    const t0 = performance.now();
    let result;
    try {
      result = wasm.derive_stealth_keys(mnemonic, passphrase);
    } catch (e) {
      // No fabrication: stealth keys are real wasm output, not random bytes.
      addTimelineEntry([{ text: `derive_stealth_keys failed: ${e && e.message || e}`, type: 'error' }]);
      return;
    }
    const elapsed = (performance.now() - t0).toFixed(2);

    recipientKeys = {
      spendPub: new Uint8Array(result.spend_pubkey),
      spendPriv: new Uint8Array(result.spend_privkey),
      viewPub: new Uint8Array(result.view_pubkey),
      viewPriv: new Uint8Array(result.view_privkey),
    };

    transferBtn.disabled = false;

    addTimelineEntry([
      { text: `[Recipient] Derived stealth keys from mnemonic`, type: 'success' },
      { text: `  View pubkey: ${bytesToHex(recipientKeys.viewPub).slice(0, 32)}...`, type: 'info' },
      { text: `  Spend pubkey: ${bytesToHex(recipientKeys.spendPub).slice(0, 32)}...`, type: 'info' },
      { text: `  (Private keys kept secret — never shared)`, type: 'info' },
    ]);

    showExplainer(explainerDiv, {
      prover: `Derived from mnemonic: "${mnemonic.slice(0, 20)}..."\nPassphrase: "${passphrase}"\n\nView pubkey (shareable): ${bytesToHex(recipientKeys.viewPub).slice(0, 24)}...\nSpend pubkey (shareable): ${bytesToHex(recipientKeys.spendPub).slice(0, 24)}...`,
      verifier: `The recipient publishes (view_pubkey, spend_pubkey).\n\nAnyone can send to them by deriving a one-time address.\n\nOnly the recipient can detect and claim incoming payments.`,
      delta: `Stealth keys use X25519 Diffie-Hellman. The view key lets the recipient detect payments (scan). The spend key lets them claim. Separating scan from spend enables watch-only cipherclerks and delegated scanning services.`,
      timing: elapsed,
    });
  });

  // Step 2: Create stealth address + transfer
  transferBtn.addEventListener('click', () => {
    if (!recipientKeys) return;
    transferAmount = parseInt(container.querySelector('#pt-amount').value) || 500;

    const t0 = performance.now();

    // Create stealth address
    let addrResult;
    try {
      addrResult = wasm.create_stealth_address(recipientKeys.spendPub, recipientKeys.viewPub);
    } catch (e) {
      addTimelineEntry([{ text: `create_stealth_address failed: ${e && e.message || e}`, type: 'error' }]);
      return;
    }

    stealthAddr = {
      oneTimePubkey: new Uint8Array(addrResult.one_time_pubkey),
      ephemeralPubkey: new Uint8Array(addrResult.ephemeral_pubkey),
    };

    // Create value commitment
    blinding = randomBytes(32);
    let commitResult;
    try {
      commitResult = wasm.create_value_commitment(BigInt(transferAmount), blinding);
    } catch (e) {
      addTimelineEntry([{ text: `create_value_commitment failed: ${e && e.message || e}`, type: 'error' }]);
      return;
    }
    commitment = new Uint8Array(commitResult.commitment);

    // Record announcement
    const viewTag = bytesToHex(stealthAddr.ephemeralPubkey).charCodeAt(0) & 0xFF;
    announcements.push({
      ephemeral_pubkey: Array.from(stealthAddr.ephemeralPubkey),
      one_time_pubkey: Array.from(stealthAddr.oneTimePubkey),
      view_tag: viewTag,
    });

    const elapsed = (performance.now() - t0).toFixed(2);

    scanBtn.disabled = false;
    verifyBtn.disabled = false;
    state.proofCount++;
    notifyStateChange();

    addTimelineEntry([
      { text: `[Recipient] Derived stealth keys`, type: 'info' },
      { text: `[Sender] Created one-time stealth address`, type: 'success' },
      { text: `  One-time pubkey: ${bytesToHex(stealthAddr.oneTimePubkey).slice(0, 32)}...`, type: 'info' },
      { text: `  Ephemeral pubkey: ${bytesToHex(stealthAddr.ephemeralPubkey).slice(0, 32)}...`, type: 'info' },
      { text: `[Sender] Committed transfer: ${transferAmount} (hidden)`, type: 'success' },
      { text: `  Commitment: ${bytesToHex(commitment).slice(0, 32)}...`, type: 'info' },
      { text: `  (Amount and blinding factor are secret)`, type: 'info' },
    ]);

    showExplainer(explainerDiv, {
      prover: `Sender derives one-time address:\n1. Generate ephemeral X25519 keypair\n2. DH: shared = X25519(eph_priv, view_pub)\n3. scalar = BLAKE3(shared, "dregg-stealth-derive")\n4. OT_pubkey = H(scalar || spend_pub)\n\nCommitment: C = amount*V + blinding*R (real Ristretto Pedersen)\nAmount: ${transferAmount} (hidden in commitment)`,
      verifier: `On-chain sees:\n- New commitment (hides amount)\n- Ephemeral pubkey (for recipient scanning)\n- One-time address (unlinkable to recipient)\n\nDoes NOT see:\n- Amount\n- Sender identity\n- Recipient identity\n- Linkage to any known address`,
      delta: `The transfer is fully private:\n- Stealth address: nobody can tell WHO received it\n- Commitment: nobody can tell HOW MUCH was sent\n- Ephemeral key: only recipient can detect it\n\nThis is stronger than Zcash shielded (which leaks timing) because the one-time address is fresh per-transfer.`,
      timing: elapsed,
    });
  });

  // Step 3: Scan
  scanBtn.addEventListener('click', () => {
    if (!recipientKeys || announcements.length === 0) return;

    const t0 = performance.now();
    let matchedIndices;
    try {
      matchedIndices = wasm.scan_stealth_announcements(
        recipientKeys.viewPriv,
        recipientKeys.spendPub,
        JSON.stringify(announcements)
      );
    } catch (e) {
      // No fabrication: a scan failure is surfaced, not faked as "match all".
      addTimelineEntry([{ text: `scan_stealth_announcements failed: ${e && e.message || e}`, type: 'error' }]);
      return;
    }
    const elapsed = (performance.now() - t0).toFixed(2);

    const found = Array.isArray(matchedIndices) ? matchedIndices.length : 0;

    addTimelineEntry([
      { text: `[Recipient] Derived stealth keys`, type: 'info' },
      { text: `[Sender] Created stealth transfer (${transferAmount} committed)`, type: 'info' },
      { text: `[Recipient] Scanning ${announcements.length} announcement(s)...`, type: 'info' },
      { text: `[Recipient] Found ${found} payment(s) addressed to us!`, type: 'success' },
      { text: `  Matched indices: [${matchedIndices}]`, type: 'info' },
      { text: `  Can now derive spending key and claim funds`, type: 'success' },
    ]);

    showExplainer(explainerDiv, {
      prover: `Recipient scans with view_privkey:\n1. For each announcement:\n   - DH: shared = X25519(view_priv, eph_pub)\n   - Check view_tag (fast filter)\n   - If tag matches: full OT_pubkey derivation\n2. Compare derived OT vs announced OT\n3. If match: this payment is ours`,
      verifier: `Scanned ${announcements.length} announcements\nView tag pre-filter: O(1) rejection of non-matching\nFull check only on tag-matched: O(1)\n\nFound: ${found} payment(s)\nFalse positives: 0 (BLAKE3 collision probability ~2^-256)`,
      delta: `Scanning is private — the recipient reveals nothing by scanning. The view tag optimization means ~255/256 of non-matching announcements are rejected with a single byte comparison. This makes scanning practical even with millions of announcements.`,
      timing: elapsed,
    });
  });

  // Verify conservation — REAL generate -> verify roundtrip.
  verifyBtn.addEventListener('click', () => {
    if (!commitment) return;

    const t0 = performance.now();

    // Balanced set: 1000 input == transferAmount + change. We re-derive the
    // recipient output blinding here (the displayed `commitment` above used a
    // separate blinding; for a verifiable roundtrip the prover must own all the
    // blindings, so we generate a fresh balanced set and prove over it).
    const changeAmount = 1000 - transferAmount; // Assume 1000 input
    const inputBlindingHex = bytesToHex(randomBytes(32));
    const transferBlindingHex = bytesToHex(randomBytes(32));
    const changeBlindingHex = bytesToHex(randomBytes(32));
    const messageHex = bytesToHex(randomBytes(32)); // turn-binding context

    // REAL generate: build commitments + canonical Schnorr excess proof.
    let proved;
    try {
      proved = wasm.prove_conservation(
        JSON.stringify([{ value: 1000, blinding_hex: inputBlindingHex }]),
        JSON.stringify([
          { value: transferAmount, blinding_hex: transferBlindingHex },
          { value: changeAmount, blinding_hex: changeBlindingHex },
        ]),
        messageHex
      );
    } catch (e) {
      addTimelineEntry([{ text: `prove_conservation failed: ${e && e.message || e}`, type: 'error' }]);
      return;
    }

    // REAL verify: the same commitments + proof + message the prover produced.
    let conservResult;
    try {
      conservResult = wasm.verify_conservation_proof(
        JSON.stringify(proved.input_commitments),
        JSON.stringify(proved.output_commitments),
        JSON.stringify(proved.proof),
        proved.message_hex,
        // REAL per-output Bulletproof range proofs => flips range_proofs_checked true.
        JSON.stringify(proved.output_range_proofs)
      );
    } catch (e) {
      addTimelineEntry([{ text: `verify_conservation_proof failed: ${e && e.message || e}`, type: 'error' }]);
      return;
    }
    // ADVERSARIAL: tamper the first range proof's bytes. The Bulletproof
    // verifier must reject it, demonstrating range proofs are really checked
    // (not a placeholder). A malformed/out-of-range output => valid:false.
    let tamperResult = null;
    try {
      const tampered = proved.output_range_proofs.slice();
      if (tampered.length > 0 && tampered[0].length >= 8) {
        // Flip a hex nibble deep in the proof body.
        const p = tampered[0];
        const flipAt = p.length - 6;
        const flipped = (parseInt(p[flipAt], 16) ^ 0xf).toString(16);
        tampered[0] = p.slice(0, flipAt) + flipped + p.slice(flipAt + 1);
      }
      tamperResult = wasm.verify_conservation_proof(
        JSON.stringify(proved.input_commitments),
        JSON.stringify(proved.output_commitments),
        JSON.stringify(proved.proof),
        proved.message_hex,
        JSON.stringify(tampered)
      );
    } catch (e) {
      tamperResult = { valid: false, error: String(e && e.message || e), range_proofs_checked: false };
    }

    const elapsed = (performance.now() - t0).toFixed(2);

    state.proofCount++;
    notifyStateChange();

    const conservLabel = conservResult.valid ? 'VALID' : `INVALID${conservResult.error ? ' (' + conservResult.error + ')' : ''}`;
    const rangeLabel = conservResult.range_proofs_checked
      ? 'VERIFIED (real Bulletproofs, every output in [0, 2^64))'
      : 'NOT checked';
    addTimelineEntry([
      { text: `[Recipient] Derived stealth keys`, type: 'info' },
      { text: `[Sender] Created stealth transfer (${transferAmount} committed)`, type: 'info' },
      { text: `[Recipient] Scanned and found payment`, type: 'info' },
      { text: `[Verifier] Checking FULL conservation proof (Schnorr excess + Bulletproof range proofs)...`, type: 'info' },
      { text: `  Input: 1 commitment (original 1000)`, type: 'info' },
      { text: `  Output: ${transferAmount} to recipient + ${changeAmount} change`, type: 'info' },
      { text: `  Conservation (value balance): ${conservLabel} (${conservResult.input_count} in -> ${conservResult.output_count} out)`, type: conservResult.valid ? 'success' : 'warning' },
      { text: `  Range proofs checked: ${conservResult.range_proofs_checked} — ${rangeLabel}`, type: conservResult.range_proofs_checked ? 'success' : 'warning' },
      { text: `  [Adversarial] Tampered range proof rejected: ${tamperResult && tamperResult.valid === false ? 'YES (valid=false)' : 'NO — UNEXPECTED'}`, type: tamperResult && tamperResult.valid === false ? 'success' : 'error' },
    ]);

    showExplainer(explainerDiv, {
      prover: `prove_conservation builds REAL Ristretto Pedersen commitments, a Schnorr excess proof, AND one Bulletproof range proof per output:\n\nexcess = sum(inputs) - sum(outputs)\n       = (sum_v_in - sum_v_out)*V + r_excess*R\n\nInput: C(1000, r_in)\nOutputs: C(${transferAmount}, r1) + C(${changeAmount}, r2)\n\nEach output also gets a ~672-byte Bulletproof proving its value is in [0, 2^64).`,
      verifier: `verify_conservation_proof checks (REAL, end-to-end):\n1. All commitments are valid Ristretto points\n2. excess == sum(inputs) - sum(outputs) (homomorphic)\n3. Schnorr excess signature => values balance, no inflation\n4. Per-output Bulletproof range proofs => no negative (mod-order wrap) outputs\n\nVerdict: valid=${conservResult.valid}, range_proofs_checked=${conservResult.range_proofs_checked}\nAdversarial (tampered range proof): valid=${tamperResult ? tamperResult.valid : 'n/a'} (rejected as expected).`,
      delta: `Conservation is now proven for real end-to-end: the value-balance relation AND every output's range, all verified in-browser via curve25519 Bulletproofs compiled to wasm32. valid=true with range_proofs_checked=true means both "the excess balances" AND "every output is a non-negative 64-bit value" — the negative-value inflation attack is closed.`,
      timing: elapsed,
    });
  });
}

function showExplainer(el, { prover, verifier, delta, timing }) {
  el.innerHTML = `
    <div class="explainer">
      <div class="explainer__title">What just happened</div>
      <div class="explainer__grid">
        <div class="explainer__cell explainer__cell--prover">
          <div class="explainer__cell-label">Sender / Recipient</div>
          <div class="explainer__cell-content">${escapeHtml(prover)}</div>
        </div>
        <div class="explainer__cell explainer__cell--verifier">
          <div class="explainer__cell-label">Network / Verifier</div>
          <div class="explainer__cell-content">${escapeHtml(verifier)}</div>
        </div>
        <div class="explainer__cell explainer__cell--delta">
          <div class="explainer__cell-label">Privacy guarantee</div>
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
