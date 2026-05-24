// Confirm-intent popup — nonce-bound.
// P0-1/P0-2: payload (action, spec, options, origin) fetched via background
// using the per-popup nonce. Decision message includes the nonce so the
// background can validate it came from this popup window.

function parseNonce() {
  const hash = window.location.hash || '';
  const m = hash.match(/(?:^#|&)nonce=([0-9a-f]+)/);
  return m ? m[1] : null;
}

const NONCE = parseNonce();

const actionEl = document.getElementById('action');
const specEl = document.getElementById('spec');
const optionsEl = document.getElementById('options');
const originEl = document.getElementById('origin');
const acceptBtn = document.getElementById('acceptBtn');
const rejectBtn = document.getElementById('rejectBtn');

let initialized = false;

async function init() {
  if (!NONCE) {
    actionEl.textContent = 'Error: no nonce — cannot display intent.';
    acceptBtn.disabled = true;
    return;
  }
  try {
    const resp = await chrome.runtime.sendMessage({
      type: 'pyana:getPendingDecision',
      nonce: NONCE,
    });
    if (resp && resp.result && resp.result.payload) {
      const p = resp.result.payload;
      actionEl.textContent = p.action || 'unknown';
      specEl.textContent = JSON.stringify(p.matchSpec || {}, null, 2);
      optionsEl.textContent = JSON.stringify(p.options || {}, null, 2);
      if (originEl) originEl.textContent = p.origin || 'unknown';
      initialized = true;
    } else {
      actionEl.textContent = 'Error: pending decision not found.';
      acceptBtn.disabled = true;
    }
  } catch (_e) {
    actionEl.textContent = 'Error: failed to load intent.';
    acceptBtn.disabled = true;
  }
}

function sendDecision(confirmed) {
  if (!NONCE) return;
  chrome.runtime.sendMessage({
    type: 'pyana:intentConfirmation',
    nonce: NONCE,
    confirmed,
  });
}

acceptBtn.addEventListener('click', () => {
  sendDecision(true);
  window.close();
});

rejectBtn.addEventListener('click', () => {
  sendDecision(false);
  window.close();
});

window.addEventListener('beforeunload', () => {
  if (initialized) sendDecision(false);
});

init();
