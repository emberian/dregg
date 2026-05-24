// Provision popup script — nonce-bound.
// P0-1/P0-2: token data is no longer in the URL; it's fetched from the
// background via pyana:getPendingDecision using the per-popup nonce
// passed in the URL hash. The decision message must include the nonce.

function parseNonce() {
  const hash = window.location.hash || '';
  const m = hash.match(/(?:^#|&)nonce=([0-9a-f]+)/);
  return m ? m[1] : null;
}

const NONCE = parseNonce();

const issuerEl = document.getElementById('issuer');
const resourceEl = document.getElementById('resource');
const actionsEl = document.getElementById('actions');
const expiryEl = document.getElementById('expiry');
const warningEl = document.getElementById('warning');
const acceptBtn = document.getElementById('acceptBtn');
const rejectBtn = document.getElementById('rejectBtn');

let tokenData = {};
let initialized = false;

function setActionTags(actions) {
  // P2-3: avoid innerHTML; build DOM nodes for each tag.
  while (actionsEl.firstChild) actionsEl.removeChild(actionsEl.firstChild);
  for (const a of actions) {
    const tag = document.createElement('span');
    tag.className = 'action-tag';
    tag.textContent = String(a);
    actionsEl.appendChild(tag);
  }
}

function render() {
  issuerEl.textContent = tokenData.issuer || 'Unknown';
  resourceEl.textContent = tokenData.resource || '*';

  if (Array.isArray(tokenData.actions) && tokenData.actions.length > 0) {
    setActionTags(tokenData.actions);
  } else {
    setActionTags(['all']);
    warningEl.textContent = 'Warning: This token grants ALL actions. Only accept if you trust the issuer.';
    warningEl.style.display = 'block';
  }

  if (tokenData.expiry) {
    const expiryDate = new Date(tokenData.expiry);
    if (expiryDate < new Date()) {
      // P2-3 (P3): build the expired span via textContent.
      while (expiryEl.firstChild) expiryEl.removeChild(expiryEl.firstChild);
      const span = document.createElement('span');
      span.className = 'expired';
      span.textContent = 'Expired: ' + expiryDate.toLocaleString();
      expiryEl.appendChild(span);
      warningEl.textContent = 'Warning: This token is already expired.';
      warningEl.style.display = 'block';
    } else {
      expiryEl.textContent = expiryDate.toLocaleString();
    }
  } else {
    expiryEl.textContent = 'Never';
  }

  if (tokenData.resource === '*' || !tokenData.resource) {
    if (!warningEl.textContent) {
      warningEl.textContent = 'Warning: This token applies to ALL resources.';
      warningEl.style.display = 'block';
    }
  }
}

async function init() {
  if (!NONCE) {
    issuerEl.textContent = 'Error: no nonce — cannot display token.';
    acceptBtn.disabled = true;
    return;
  }
  try {
    const resp = await chrome.runtime.sendMessage({
      type: 'pyana:getPendingDecision',
      nonce: NONCE,
    });
    if (resp && resp.result && resp.result.payload && resp.result.payload.tokenData) {
      tokenData = resp.result.payload.tokenData;
      initialized = true;
      render();
    } else {
      issuerEl.textContent = 'Error: pending decision not found.';
      acceptBtn.disabled = true;
    }
  } catch (_e) {
    issuerEl.textContent = 'Error: failed to load token data.';
    acceptBtn.disabled = true;
  }
}

function sendDecision(accepted) {
  if (!NONCE) return;
  chrome.runtime.sendMessage({
    type: 'pyana:provisionDecision',
    nonce: NONCE,
    accepted,
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

// If the popup is closed without clicking, treat as rejection.
window.addEventListener('beforeunload', () => {
  if (initialized) sendDecision(false);
});

init();
