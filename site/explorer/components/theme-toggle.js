/**
 * Theme toggle — light / dark.
 *
 * Reads + writes the SAME `localStorage` key Builder A's playground uses
 * (`pyana_theme`), so a user who toggles in the playground sees the same
 * theme in the explorer.
 *
 * The initial theme is also applied inline in index.html's <head> to avoid
 * a flash; this module just owns the toggle button + storage event sync.
 */

const KEY = 'pyana_theme';

function currentTheme() {
  const root = document.documentElement;
  return root.dataset.theme === 'light' ? 'light' : 'dark';
}

function setTheme(t) {
  const next = t === 'light' ? 'light' : 'dark';
  if (next === 'dark') {
    delete document.documentElement.dataset.theme;
  } else {
    document.documentElement.dataset.theme = 'light';
  }
  try { localStorage.setItem(KEY, next); } catch {}
  window.dispatchEvent(new CustomEvent('pyana:theme-changed', { detail: { theme: next } }));
}

export function init() {
  const btn = document.getElementById('theme-toggle');
  if (!btn) return;
  // Reflect current theme in aria
  syncBtn(btn);
  btn.addEventListener('click', () => {
    setTheme(currentTheme() === 'light' ? 'dark' : 'light');
    syncBtn(btn);
  });
  // Sync if another tab changes it (or playground does).
  window.addEventListener('storage', (e) => {
    if (e.key === KEY) {
      if (e.newValue === 'light' || e.newValue === 'dark') {
        if (e.newValue === 'dark') delete document.documentElement.dataset.theme;
        else document.documentElement.dataset.theme = 'light';
        syncBtn(btn);
      }
    }
  });
}

function syncBtn(btn) {
  const theme = currentTheme();
  btn.dataset.theme = theme;
  btn.setAttribute('aria-pressed', theme === 'light' ? 'true' : 'false');
  btn.title = theme === 'light' ? 'Switch to dark theme' : 'Switch to light theme';
}
