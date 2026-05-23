function escapeHtml(str) {
  return String(str).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

const params = new URLSearchParams(window.location.search);

const action = params.get('action') || 'unknown';
let spec = {};
let options = {};
try { spec = JSON.parse(decodeURIComponent(params.get('spec') || '{}')); } catch (e) {}
try { options = JSON.parse(decodeURIComponent(params.get('options') || '{}')); } catch (e) {}

document.getElementById('action').textContent = action;
document.getElementById('spec').textContent = JSON.stringify(spec, null, 2);
document.getElementById('options').textContent = JSON.stringify(options, null, 2);

document.getElementById('acceptBtn').addEventListener('click', () => {
  chrome.runtime.sendMessage({
    type: 'pyana:intentConfirmation',
    confirmed: true,
  });
  window.close();
});

document.getElementById('rejectBtn').addEventListener('click', () => {
  chrome.runtime.sendMessage({
    type: 'pyana:intentConfirmation',
    confirmed: false,
  });
  window.close();
});

window.addEventListener('beforeunload', () => {
  chrome.runtime.sendMessage({
    type: 'pyana:intentConfirmation',
    confirmed: false,
  });
});
