// Share-capability popup script — nonce-bound. The bearer URI is no longer
// embedded in the URL; it's fetched from the background via
// getPendingDecision so that other extensions / chrome internals don't see
// the secret on the URL.

function parseNonce() {
  const hash = window.location.hash || '';
  const m = hash.match(/(?:^#|&)nonce=([0-9a-fA-F]+)/);
  return m ? m[1] : null;
}

const NONCE = parseNonce();

const cellIdInput = document.getElementById('cellIdInput');
const generateBtn = document.getElementById('generateBtn');
const inputSection = document.getElementById('inputSection');
const resultSection = document.getElementById('resultSection');
const uriDisplay = document.getElementById('uriDisplay');
const copyBtn = document.getElementById('copyBtn');
const closeBtn = document.getElementById('closeBtn');
const errorMsg = document.getElementById('errorMsg');

async function init() {
  if (!NONCE) return;
  try {
    const resp = await chrome.runtime.sendMessage({
      type: 'pyana:getPendingDecision',
      nonce: NONCE,
    });
    if (resp && resp.result && resp.result.payload) {
      const { uri, cellId } = resp.result.payload;
      if (uri) {
        cellIdInput.value = cellId || '';
        uriDisplay.textContent = uri;
        inputSection.classList.add('hidden');
        resultSection.classList.remove('hidden');
      } else if (cellId) {
        cellIdInput.value = cellId;
      }
    }
  } catch (_e) {
    // No pending data → show empty input form.
  }
}

generateBtn.addEventListener('click', async () => {
  const cellId = cellIdInput.value.trim();
  if (!cellId || !/^[0-9a-fA-F]{64}$/.test(cellId)) {
    errorMsg.textContent = 'Please enter a valid 64-character hex cell ID.';
    errorMsg.classList.remove('hidden');
    return;
  }
  errorMsg.classList.add('hidden');
  generateBtn.textContent = 'Generating...';
  generateBtn.disabled = true;

  const response = await chrome.runtime.sendMessage({
    type: 'pyana:shareCapability',
    id: `share_${Date.now()}`,
    cellId,
  });

  generateBtn.textContent = 'Generate Shareable URI';
  generateBtn.disabled = false;

  if (response && response.result && response.result.uri) {
    uriDisplay.textContent = response.result.uri;
    inputSection.classList.add('hidden');
    resultSection.classList.remove('hidden');
  } else {
    const err = response?.result?.error || response?.error || 'Failed to generate URI';
    errorMsg.textContent = err;
    errorMsg.classList.remove('hidden');
  }
});

copyBtn.addEventListener('click', () => {
  navigator.clipboard.writeText(uriDisplay.textContent).then(() => {
    copyBtn.textContent = 'Copied!';
    setTimeout(() => { copyBtn.textContent = 'Copy URI to Clipboard'; }, 2000);
  });
});

closeBtn.addEventListener('click', () => {
  window.close();
});

init();
