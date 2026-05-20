const statusDot = document.getElementById('statusDot');
const statusText = document.getElementById('statusText');
const tokenCount = document.getElementById('tokenCount');
const chainLength = document.getElementById('chainLength');
const logContainer = document.getElementById('logContainer');
const lockBtn = document.getElementById('lockBtn');

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
  } else {
    statusDot.classList.remove('locked');
    statusText.textContent = 'Connected';
    lockBtn.textContent = 'Lock Wallet';
    lockBtn.classList.remove('locked');
  }
  tokenCount.textContent = String(state.tokenCount);
  chainLength.textContent = String(state.chainLength);
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
    const icon = entry.allowed ? '✓' : '✗';
    return `<div class="log-entry"><span>${icon} ${entry.action} on ${entry.resource}</span><div class="time">${time}</div></div>`;
  }).join('');
}

lockBtn.addEventListener('click', async () => {
  const state = await sendMessage('pyana:getState');
  if (!state) return;
  if (state.locked) {
    await sendMessage('pyana:unlock', { passphrase: '' });
  } else {
    await sendMessage('pyana:lock');
  }
  await refresh();
});

refresh();
loadLog();
