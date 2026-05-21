const statusDot = document.getElementById('statusDot');
const statusText = document.getElementById('statusText');
const tokenCount = document.getElementById('tokenCount');
const chainLength = document.getElementById('chainLength');
const logContainer = document.getElementById('logContainer');
const lockBtn = document.getElementById('lockBtn');
const backupBtn = document.getElementById('backupBtn');
const recoverBtn = document.getElementById('recoverBtn');
const passphraseSection = document.getElementById('passphraseSection');
const passphraseInput = document.getElementById('passphraseInput');
const mnemonicDisplay = document.getElementById('mnemonicDisplay');
const mnemonicWarning = document.getElementById('mnemonicWarning');

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
    backupBtn.style.display = 'none';
    mnemonicDisplay.style.display = 'none';
    mnemonicWarning.style.display = 'none';
  } else {
    statusDot.classList.remove('locked');
    statusText.textContent = 'Connected';
    lockBtn.textContent = 'Lock Wallet';
    lockBtn.classList.remove('locked');
    passphraseSection.classList.add('hidden');
    backupBtn.style.display = state.hasMnemonic ? 'block' : 'none';
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
    // If no passphrase is set yet, prompt for one before locking.
    if (!state.hasPassphrase) {
      const passphrase = prompt('Set a passphrase to protect your wallet (leave empty for no encryption):');
      if (passphrase !== null && passphrase.length > 0) {
        await sendMessage('pyana:setPassphrase', { passphrase });
      }
    }
    await sendMessage('pyana:lock');
  }
  await refresh();
});

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

refresh();
loadLog();
