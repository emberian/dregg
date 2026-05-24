// Origin-permission popup — nonce-bound.
// P0-1: decision includes the nonce so the background can validate the
// sender against the popup window it created.

function parseNonce() {
  const hash = window.location.hash || '';
  const m = hash.match(/(?:^#|&)nonce=([0-9a-f]+)/);
  return m ? m[1] : null;
}

const NONCE = parseNonce();

const originEl = document.getElementById('origin');
const methodEl = document.getElementById('method');
const allowBtn = document.getElementById('allowBtn');
const denyBtn = document.getElementById('denyBtn');

let initialized = false;

async function init() {
  if (!NONCE) {
    originEl.textContent = 'Error: no nonce.';
    allowBtn.disabled = true;
    return;
  }
  try {
    const resp = await chrome.runtime.sendMessage({
      type: 'pyana:getPendingDecision',
      nonce: NONCE,
    });
    if (resp && resp.result && resp.result.payload) {
      originEl.textContent = resp.result.payload.origin || 'unknown';
      methodEl.textContent = resp.result.payload.method || 'unknown';
      initialized = true;
    } else {
      originEl.textContent = 'Error: pending decision not found.';
      allowBtn.disabled = true;
    }
  } catch (_e) {
    originEl.textContent = 'Error: failed to load request.';
    allowBtn.disabled = true;
  }
}

function sendDecision(granted) {
  if (!NONCE) return;
  chrome.runtime.sendMessage({
    type: 'pyana:originPermissionDecision',
    nonce: NONCE,
    granted,
  });
}

allowBtn.addEventListener('click', () => {
  sendDecision(true);
  window.close();
});

denyBtn.addEventListener('click', () => {
  sendDecision(false);
  window.close();
});

window.addEventListener('beforeunload', () => {
  if (initialized) sendDecision(false);
});

init();
