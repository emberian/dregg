// Content script: bridges page.js (window.pyana) ↔ background service worker.

const script = document.createElement('script');
script.src = chrome.runtime.getURL('page.js');
script.type = 'module';
(document.head || document.documentElement).appendChild(script);
script.onload = () => script.remove();

window.addEventListener('pyana:request', async (event) => {
  const detail = event.detail;
  const response = await chrome.runtime.sendMessage(detail);
  window.dispatchEvent(new CustomEvent('pyana:response', { detail: response }));
});
