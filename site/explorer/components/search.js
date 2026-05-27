/**
 * Search component — global search for cells, turns, blocks, notes.
 */

import { bus, navigateTo } from '../app.js';
import * as api from '../api.js';

export function init() {
  const input = document.getElementById('search-input');

  // Focus on '/' key
  document.addEventListener('keydown', (e) => {
    if (e.key === '/' && !isInputFocused()) {
      e.preventDefault();
      input.focus();
    }
  });

  input.addEventListener('keydown', (e) => {
    if (e.key === 'Enter') {
      handleSearch(input.value.trim());
    }
    if (e.key === 'Escape') {
      input.blur();
    }
  });
}

async function handleSearch(query) {
  if (!query) return;

  if (/^dregg:\/\//i.test(query)) {
    window.location.href = `../starbridge/?at=${encodeURIComponent(query)}&runtime=remote`;
    return;
  }

  // Block height (pure number)
  if (/^\d+$/.test(query)) {
    navigateTo('blocks');
    bus.emit('search:block', parseInt(query));
    return;
  }

  // Full hex hash (64 chars) — could be cell, turn hash, or block root
  if (query.length === 64 && /^[0-9a-fA-F]+$/.test(query)) {
    navigateTo('cells');
    bus.emit('search:hash', query);
    try {
      const cell = await api.getCell(query);
      if (cell && cell.found) {
        bus.emit('cell:detail', cell);
      }
    } catch { /* not found, try other types */ }
    return;
  }

  // Partial hex hash
  if (query.length > 8 && /^[0-9a-fA-F]+$/.test(query)) {
    navigateTo('cells');
    bus.emit('search:hash', query);
    try {
      const cell = await api.getCell(query.padEnd(64, '0'));
      if (cell && cell.found) {
        bus.emit('cell:detail', cell);
      }
    } catch { /* ignore */ }
    return;
  }

  // Named search (page names)
  const pageNames = ['blocks', 'cells', 'turns', 'receipts', 'capabilities',
                     'proofs', 'intents', 'federation', 'notes', 'apps',
                     'blocklace', 'effects', 'overview'];
  const match = pageNames.find(p => p.startsWith(query.toLowerCase()));
  if (match) {
    navigateTo(match);
  }
}

function isInputFocused() {
  const tag = document.activeElement?.tagName?.toLowerCase();
  return tag === 'input' || tag === 'textarea' || tag === 'select';
}
