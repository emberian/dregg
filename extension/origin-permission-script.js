function escapeHtml(str) {
  return String(str).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

const params = new URLSearchParams(window.location.search);
const origin = params.get('origin') || 'unknown';
const method = params.get('method') || 'unknown';

document.getElementById('origin').textContent = origin;
document.getElementById('method').textContent = method;

document.getElementById('allowBtn').addEventListener('click', () => {
  chrome.runtime.sendMessage({
    type: 'pyana:originPermissionDecision',
    granted: true,
    origin,
  });
  window.close();
});

document.getElementById('denyBtn').addEventListener('click', () => {
  chrome.runtime.sendMessage({
    type: 'pyana:originPermissionDecision',
    granted: false,
    origin,
  });
  window.close();
});

window.addEventListener('beforeunload', () => {
  chrome.runtime.sendMessage({
    type: 'pyana:originPermissionDecision',
    granted: false,
    origin,
  });
});
