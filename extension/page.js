// Injected into page context. Defines window.pyana API.

const pending = new Map();
let idCounter = 0;

function sendMessage(type, payload) {
  return new Promise((resolve, reject) => {
    const id = `pyana_${Date.now()}_${idCounter++}`;
    pending.set(id, { resolve, reject });
    window.dispatchEvent(new CustomEvent('pyana:request', {
      detail: { type, id, ...payload },
    }));
    setTimeout(() => {
      if (pending.has(id)) {
        pending.delete(id);
        reject(new Error('Pyana: request timed out'));
      }
    }, 30000);
  });
}

window.addEventListener('pyana:response', (event) => {
  const detail = event.detail;
  const resolver = pending.get(detail.id);
  if (!resolver) return;
  pending.delete(detail.id);
  if (detail.error) {
    resolver.reject(new Error(detail.error));
  } else {
    resolver.resolve(detail.result);
  }
});

const pyana = {
  authorize(request) {
    return sendMessage('pyana:authorize', { request });
  },
  isConnected() {
    return sendMessage('pyana:isConnected').then(() => true).catch(() => false);
  },
  getCapabilities() {
    return sendMessage('pyana:getCapabilities');
  },
};

Object.defineProperty(window, 'pyana', {
  value: Object.freeze(pyana),
  writable: false,
  configurable: false,
});

window.dispatchEvent(new Event('pyana:ready'));
