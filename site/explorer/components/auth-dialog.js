/**
 * Admin auth dialog.
 *
 * Listens for `pyana:auth-required` events emitted by app.js when a view's
 * fetch threw `AuthRequired`. Opens the <dialog id="auth-dialog">, prompts
 * for the admin bearer token, stores it in `sessionStorage` (NEVER
 * localStorage), and re-emits `pyana:auth-token-saved` so the requesting
 * view can retry.
 *
 * Accessibility:
 *  - native <dialog>.showModal() traps focus + handles Esc.
 *  - Enter submits via form `method="dialog"`.
 *  - On Cancel or Esc, we emit `pyana:auth-cancelled` so the requestor can
 *    surface "request aborted" rather than re-prompting in a loop.
 *
 * "Clear admin token" link in the header is also wired here: it appears only
 * while a token is set, and clicking it wipes the token.
 */

import { setAdminToken, clearAdminToken, getAdminToken } from '../api.js';

let dialog = null;
let input = null;
let cancelBtn = null;
let submitBtn = null;
let descEl = null;
let clearBtn = null;
let lastReason = null; // 'initial' | 'rejected'

export function init() {
  dialog = document.getElementById('auth-dialog');
  input = document.getElementById('auth-dialog-input');
  cancelBtn = document.getElementById('auth-dialog-cancel');
  submitBtn = document.getElementById('auth-dialog-submit');
  descEl = document.getElementById('auth-dialog-desc');
  clearBtn = document.getElementById('admin-token-clear');
  if (!dialog) return;

  // Form submit (Enter or "Save & retry"):
  dialog.addEventListener('submit', (e) => {
    e.preventDefault();
    const token = (input.value || '').trim();
    if (!token) { input.focus(); return; }
    setAdminToken(token);
    input.value = '';
    dialog.close('ok');
    window.dispatchEvent(new CustomEvent('pyana:auth-token-saved'));
  });

  // Cancel button:
  cancelBtn?.addEventListener('click', () => {
    dialog.close('cancel');
  });

  // Native close event covers Esc + cancel + submit:
  dialog.addEventListener('close', () => {
    if (dialog.returnValue !== 'ok') {
      window.dispatchEvent(new CustomEvent('pyana:auth-cancelled'));
    }
  });

  // Header "Clear admin token" link:
  clearBtn?.addEventListener('click', () => {
    clearAdminToken();
  });

  // React to token presence changes (storage events from other tabs, or
  // local set/clear): keep the header chip in sync.
  window.addEventListener('pyana:admin-token-changed', updateClearVisibility);
  window.addEventListener('storage', (e) => {
    if (e.key === 'pyana_admin_token') updateClearVisibility();
  });
  updateClearVisibility();

  // Listen for auth-required from any view.
  window.addEventListener('pyana:auth-required', (e) => {
    openDialog(e.detail || {});
  });
}

function updateClearVisibility() {
  if (!clearBtn) return;
  const hasTok = !!getAdminToken();
  clearBtn.hidden = !hasTok;
}

function openDialog({ reason } = {}) {
  if (!dialog) return;
  lastReason = reason || 'initial';
  if (descEl) {
    descEl.textContent = reason === 'rejected'
      ? 'The previous token was rejected (401/403). Paste a fresh admin bearer token. The token is held only in sessionStorage.'
      : 'This view calls an authenticated endpoint. Paste an admin bearer token to continue. The token is held in sessionStorage and is wiped when this tab closes.';
  }
  if (typeof dialog.showModal === 'function') {
    if (!dialog.open) dialog.showModal();
  } else {
    // Fallback for very old browsers: show as a regular block + add the
    // [open] attribute. We pair this with a simple Esc handler.
    dialog.setAttribute('open', '');
    document.addEventListener('keydown', escFallback);
  }
  // Focus the input on next frame (after browser's own focus management).
  requestAnimationFrame(() => input?.focus());
}

function escFallback(e) {
  if (e.key === 'Escape') {
    dialog.removeAttribute('open');
    document.removeEventListener('keydown', escFallback);
    window.dispatchEvent(new CustomEvent('pyana:auth-cancelled'));
  }
}

/**
 * Helper for view code that wants to make an authed call with auto-prompt:
 *
 *   await runWithAuth(() => api.getInboxQueueEntries('mail'));
 *
 * Opens the dialog if needed and retries once after the token is saved.
 * Throws on cancel.
 */
export function runWithAuth(thunk) {
  return new Promise(async (resolve, reject) => {
    const attempt = async () => {
      try { resolve(await thunk()); }
      catch (e) {
        if (e && e.name === 'AuthRequired') {
          const onSaved = () => { cleanup(); attempt(); };
          const onCancel = () => { cleanup(); reject(new Error('auth cancelled')); };
          const cleanup = () => {
            window.removeEventListener('pyana:auth-token-saved', onSaved);
            window.removeEventListener('pyana:auth-cancelled', onCancel);
          };
          window.addEventListener('pyana:auth-token-saved', onSaved, { once: true });
          window.addEventListener('pyana:auth-cancelled', onCancel, { once: true });
          window.dispatchEvent(new CustomEvent('pyana:auth-required', {
            detail: { reason: getAdminToken() ? 'initial' : 'initial' },
          }));
        } else { reject(e); }
      }
    };
    attempt();
  });
}
