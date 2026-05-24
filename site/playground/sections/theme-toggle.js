// Nav-bar theme toggle. Persists choice in localStorage; the inline script in
// `<head>` honors that choice on first paint (preventing flash). Default is
// `prefers-color-scheme`.

const KEY = 'pyana_theme';

function currentTheme() {
  return document.documentElement.getAttribute('data-theme') === 'light' ? 'light' : 'dark';
}

function applyTheme(theme) {
  if (theme === 'light') {
    document.documentElement.setAttribute('data-theme', 'light');
  } else {
    document.documentElement.removeAttribute('data-theme');
  }
  try { localStorage.setItem(KEY, theme); } catch (_) { /* ignore */ }
  renderSlots(theme);
}

function renderSlots(active) {
  document.querySelectorAll('#pg-theme-toggle .pg-theme-toggle__slot').forEach(el => {
    el.dataset.active = (el.dataset.slot === active) ? 'true' : 'false';
  });
}

export function initThemeToggle() {
  const btn = document.getElementById('pg-theme-toggle');
  if (!btn) return;
  // Sync visible state with whatever the inline boot script chose.
  renderSlots(currentTheme());

  btn.addEventListener('click', () => {
    applyTheme(currentTheme() === 'light' ? 'dark' : 'light');
  });

  // Honor system changes if the user hasn't expressed a preference.
  try {
    const mql = matchMedia('(prefers-color-scheme: light)');
    mql.addEventListener('change', e => {
      if (localStorage.getItem(KEY)) return; // user override wins
      applyTheme(e.matches ? 'light' : 'dark');
    });
  } catch (_) { /* old browser; safe to ignore */ }
}
