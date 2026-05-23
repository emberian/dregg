const statusDot = document.getElementById('statusDot');
const statusText = document.getElementById('statusText');
const tokenCount = document.getElementById('tokenCount');
const chainLength = document.getElementById('chainLength');
const logContainer = document.getElementById('logContainer');
const lockBtn = document.getElementById('lockBtn');
const backupBtn = document.getElementById('backupBtn');
const recoverBtn = document.getElementById('recoverBtn');
const managePermsBtn = document.getElementById('managePermsBtn');
const passphraseSection = document.getElementById('passphraseSection');
const passphraseInput = document.getElementById('passphraseInput');
const passphraseSetupSection = document.getElementById('passphraseSetupSection');
const newPassphraseInput = document.getElementById('newPassphraseInput');
const confirmPassphraseInput = document.getElementById('confirmPassphraseInput');
const setPassphraseBtn = document.getElementById('setPassphraseBtn');
const mnemonicDisplay = document.getElementById('mnemonicDisplay');
const mnemonicWarning = document.getElementById('mnemonicWarning');
const permissionsSection = document.getElementById('permissionsSection');
const permissionsContainer = document.getElementById('permissionsContainer');

async function sendMessage(type, extra) {
  const id = `popup_${Date.now()}`;
  const response = await chrome.runtime.sendMessage({ type, id, ...extra });
  return response?.result;
}

async function refresh() {
  const state = await sendMessage('pyana:getState');
  if (!state) return;
  if (state.locked) {
    statusDot.classList.add('locked');
    statusText.textContent = 'Locked';
    lockBtn.textContent = 'Unlock Wallet';
    lockBtn.classList.add('locked');
    passphraseSection.classList.remove('hidden');
    passphraseSetupSection.classList.add('hidden');
    backupBtn.style.display = 'none';
    mnemonicDisplay.style.display = 'none';
    mnemonicWarning.style.display = 'none';
    permissionsSection.style.display = 'none';
  } else {
    statusDot.classList.remove('locked');
    statusText.textContent = 'Connected';
    lockBtn.textContent = 'Lock Wallet';
    lockBtn.classList.remove('locked');
    passphraseSection.classList.add('hidden');
    backupBtn.style.display = state.hasMnemonic ? 'block' : 'none';
    // Show passphrase setup prompt if needed.
    if (state.needsPassphraseSetup) {
      passphraseSetupSection.classList.remove('hidden');
    } else {
      passphraseSetupSection.classList.add('hidden');
    }
  }
  tokenCount.textContent = String(state.tokenCount);
  chainLength.textContent = String(state.chainLength);
}

function escapeHtml(str) {
  return String(str).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

async function loadLog() {
  const stored = await chrome.storage.local.get('pyana_wallet');
  const wallet = stored['pyana_wallet'];
  if (!wallet || !wallet.log || wallet.log.length === 0) {
    logContainer.innerHTML = '<div class="empty">No recent authorizations</div>';
    return;
  }
  const entries = wallet.log.slice(-5).reverse();
  logContainer.innerHTML = entries.map(entry => {
    const time = new Date(entry.timestamp).toLocaleTimeString();
    const icon = entry.allowed ? '&#x2713;' : '&#x2717;';
    return `<div class="log-entry"><span>${icon} ${escapeHtml(entry.action)} on ${escapeHtml(entry.resource)}</span><div class="time">${escapeHtml(time)}</div></div>`;
  }).join('');
}

lockBtn.addEventListener('click', async () => {
  const state = await sendMessage('pyana:getState');
  if (!state) return;
  if (state.locked) {
    const passphrase = passphraseInput.value;
    const result = await sendMessage('pyana:unlock', { passphrase });
    if (result && !result.success) {
      passphraseInput.style.borderColor = '#f87171';
      passphraseInput.value = '';
      passphraseInput.placeholder = 'Invalid passphrase - try again';
      return;
    }
    passphraseInput.value = '';
    passphraseInput.style.borderColor = '';
    passphraseInput.placeholder = 'Enter passphrase to unlock';
  } else {
    await sendMessage('pyana:lock');
  }
  await refresh();
});

// Passphrase setup handler (for new wallets).
setPassphraseBtn.addEventListener('click', async () => {
  const newPass = newPassphraseInput.value;
  const confirmPass = confirmPassphraseInput.value;
  if (!newPass) {
    newPassphraseInput.style.borderColor = '#f87171';
    newPassphraseInput.placeholder = 'Passphrase is required';
    return;
  }
  if (newPass !== confirmPass) {
    confirmPassphraseInput.style.borderColor = '#f87171';
    confirmPassphraseInput.value = '';
    confirmPassphraseInput.placeholder = 'Passphrases do not match';
    return;
  }
  await sendMessage('pyana:setPassphrase', { passphrase: newPass });
  newPassphraseInput.value = '';
  confirmPassphraseInput.value = '';
  newPassphraseInput.style.borderColor = '';
  confirmPassphraseInput.style.borderColor = '';
  passphraseSetupSection.classList.add('hidden');
  await refresh();
});

// Manage permissions.
managePermsBtn.addEventListener('click', async () => {
  if (permissionsSection.style.display === 'none') {
    permissionsSection.style.display = 'block';
    managePermsBtn.textContent = 'Hide Permissions';
    await loadPermissions();
  } else {
    permissionsSection.style.display = 'none';
    managePermsBtn.textContent = 'Manage Permissions';
  }
});

async function loadPermissions() {
  const perms = await sendMessage('pyana:getOriginPermissions');
  if (!perms || perms.length === 0) {
    permissionsContainer.innerHTML = '<div class="empty">No origins approved</div>';
    return;
  }
  permissionsContainer.innerHTML = perms.map(p => {
    const expiresIn = p.expiresIn ? Math.round(p.expiresIn / 60000) : 0;
    const expiresStr = expiresIn > 60 ? `${Math.round(expiresIn / 60)}h` : `${expiresIn}m`;
    return `<div class="log-entry" style="display:flex;justify-content:space-between;align-items:center;">
      <div>
        <div style="font-size:11px;color:#fbbf24;word-break:break-all;">${escapeHtml(p.origin)}</div>
        <div class="time">${escapeHtml(p.methods.join(', '))} - expires in ${expiresStr}</div>
      </div>
      <button class="revoke-btn" data-origin="${escapeHtml(p.origin)}" style="flex-shrink:0;padding:4px 8px;font-size:11px;background:#7f1d1d;color:#fca5a5;border:none;border-radius:4px;cursor:pointer;">Revoke</button>
    </div>`;
  }).join('');
  // Attach revoke handlers.
  permissionsContainer.querySelectorAll('.revoke-btn').forEach(btn => {
    btn.addEventListener('click', async () => {
      await sendMessage('pyana:revokeOriginPermission', { origin: btn.dataset.origin });
      await loadPermissions();
    });
  });
}

backupBtn.addEventListener('click', async () => {
  const state = await sendMessage('pyana:getState');
  if (state && state.locked) {
    alert('Unlock your wallet first to view the recovery phrase.');
    return;
  }
  const mnemonic = await sendMessage('pyana:getMnemonic');
  if (!mnemonic) {
    alert('No recovery phrase available for this wallet.');
    return;
  }
  // Toggle display.
  if (mnemonicDisplay.style.display === 'block') {
    mnemonicDisplay.style.display = 'none';
    mnemonicWarning.style.display = 'none';
    backupBtn.textContent = 'Backup (Show Recovery Phrase)';
  } else {
    // Format words in a numbered grid.
    const words = mnemonic.split(' ');
    mnemonicDisplay.innerHTML = words.map((w, i) =>
      `<span>${String(i + 1).padStart(2, '0')}. ${w}</span>`
    ).join('&nbsp;&nbsp;');
    mnemonicDisplay.style.display = 'block';
    mnemonicWarning.style.display = 'block';
    backupBtn.textContent = 'Hide Recovery Phrase';
  }
});

recoverBtn.addEventListener('click', () => {
  // Open recovery page in a new tab.
  chrome.tabs.create({ url: chrome.runtime.getURL('recovery.html') });
});

// Settings button — opens node configuration page.
const settingsBtn = document.getElementById('settingsBtn');
settingsBtn.addEventListener('click', () => {
  chrome.tabs.create({ url: chrome.runtime.getURL('settings.html') });
});

// ---------------------------------------------------------------------------
// Intents fulfillment UI
// ---------------------------------------------------------------------------

const intentsBtn = document.getElementById('intentsBtn');
const intentsSection = document.getElementById('intentsSection');
const intentsContainer = document.getElementById('intentsContainer');

intentsBtn.addEventListener('click', async () => {
  if (intentsSection.style.display === 'none') {
    intentsSection.style.display = 'block';
    intentsBtn.textContent = 'Hide Intents';
    await loadFulfillableIntents();
  } else {
    intentsSection.style.display = 'none';
    intentsBtn.textContent = 'Fulfill Intents';
  }
});

async function loadFulfillableIntents() {
  const intents = await sendMessage('pyana:getFulfillableIntents');
  if (!intents || intents.length === 0) {
    intentsContainer.innerHTML = '<div class="empty">No fulfillable intents available</div>';
    return;
  }
  intentsContainer.innerHTML = intents.map(item => {
    const actions = item.grantedActions ? item.grantedActions.join(', ') : 'any';
    const expiresIn = Math.max(0, Math.round((item.expiry - Date.now()) / 60000));
    const expiresStr = expiresIn > 60 ? `${Math.round(expiresIn / 60)}h` : `${expiresIn}m`;
    const shortId = item.intentId.slice(0, 12) + '...';
    return `<div class="log-entry" style="display:flex;justify-content:space-between;align-items:center;">
      <div>
        <div style="font-size:11px;color:#a78bfa;word-break:break-all;" title="${escapeHtml(item.intentId)}">${escapeHtml(shortId)}</div>
        <div class="time">${escapeHtml(actions)} on ${escapeHtml(item.resource)} - expires in ${expiresStr}</div>
      </div>
      <button class="fulfill-btn" data-intent-id="${escapeHtml(item.intentId)}" data-token-id="${escapeHtml(item.matchedTokenId)}" style="flex-shrink:0;padding:4px 8px;font-size:11px;background:#065f46;color:#6ee7b7;border:none;border-radius:4px;cursor:pointer;">Fulfill</button>
    </div>`;
  }).join('');

  // Attach fulfill handlers.
  intentsContainer.querySelectorAll('.fulfill-btn').forEach(btn => {
    btn.addEventListener('click', async () => {
      btn.disabled = true;
      btn.textContent = '...';
      const result = await sendMessage('pyana:fulfillIntent', {
        intentId: btn.dataset.intentId,
        tokenId: btn.dataset.tokenId,
      });
      if (result && result.fulfilled) {
        btn.textContent = 'Done';
        btn.style.background = '#064e3b';
        // Refresh the list after a brief delay.
        setTimeout(() => loadFulfillableIntents(), 1000);
      } else {
        btn.textContent = 'Failed';
        btn.style.background = '#7f1d1d';
        btn.style.color = '#fca5a5';
        btn.disabled = false;
        setTimeout(() => {
          btn.textContent = 'Fulfill';
          btn.style.background = '#065f46';
          btn.style.color = '#6ee7b7';
        }, 3000);
      }
    });
  });
}

// ---------------------------------------------------------------------------
// WASM availability check
// ---------------------------------------------------------------------------

async function checkWasmStatus() {
  // The background script sets wasmLoaded. We detect WASM issues by checking
  // if getState works but the extension has a degraded crypto capability.
  // Send a lightweight message to check WASM status.
  try {
    const response = await chrome.runtime.sendMessage({
      type: 'pyana:isConnected',
      id: 'wasm_check',
    });
    // If we get here, background is alive. Check for WASM error indicator
    // by trying canAuthorize which requires WASM — if it throws, show the error.
    const canAuth = await sendMessage('pyana:canAuthorize', {
      request: { action: '__wasm_check__', resource: '__probe__' }
    });
    // If canAuthorize returns false (no token), WASM is working fine.
    // If it returns an error about WASM, show the warning.
    if (canAuth && canAuth.error && canAuth.error.includes('Cryptographic module')) {
      document.getElementById('wasmError').style.display = 'block';
    }
  } catch (e) {
    // Background not available or WASM issue.
    if (e.message && e.message.includes('WASM')) {
      document.getElementById('wasmError').style.display = 'block';
    }
  }
}

refresh();
loadLog();
checkWasmStatus();
