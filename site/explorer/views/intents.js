/**
 * Intents view — active intents pool and pending conditionals.
 */

import { bus, state } from '../app.js';
import * as api from '../api.js';

export const name = 'intents';

export function init(el) {
  bus.on('intents:updated', ({ intents, conditionals }) => {
    if (state.currentPage === 'intents') {
      renderActiveIntents(intents);
      renderConditionals(conditionals);
    }
  });
}

export function update(appState) {
  if (appState.intents) renderActiveIntents(appState.intents);
  if (appState.conditionals) renderConditionals(appState.conditionals);
}

export function destroy() {}

function starbridgeHref(uri) {
  return `../starbridge/?at=${encodeURIComponent(uri)}&runtime=remote`;
}

function renderActiveIntents(intents) {
  const container = document.getElementById('intents-active');
  document.getElementById('intents-count-badge').textContent = intents?.length || 0;

  if (!intents || !intents.length) {
    container.innerHTML = '<div class="empty-state">No active intents in pool</div>';
    return;
  }
  container.innerHTML = intents.map(entry => {
    const intent = entry.intent || entry;
    const id = entry.id || intent.id;
    const kind = intent.kind ?? intent.type;
    const kindLabel = kind !== undefined ? `kind:${kind}` : 'unknown';
    return `
      <div class="intent-item">
        <div class="intent-item__header">
          <span class="intent-item__id">${api.shortHash(id, 8, 4)}</span>
          <span class="intent-item__kind">${kindLabel}</span>
        </div>
        <div class="intent-item__details">
          expiry: ${intent.expiry || '--'}${intent.matcher ? ` | actions: ${intent.matcher.actions?.length || 0}` : ''}
        </div>
        ${id ? `<div class="intent-item__actions"><a class="ex-starbridge-link" href="${starbridgeHref(`dregg://intent/${id}`)}">Open intent in Starbridge</a></div>` : ''}
      </div>
    `;
  }).join('');
}

function renderConditionals(conditionals) {
  const container = document.getElementById('intents-conditionals');
  document.getElementById('conditionals-count-badge').textContent = conditionals?.length || 0;

  if (!conditionals || !conditionals.length) {
    container.innerHTML = '<div class="empty-state">No pending conditionals</div>';
    return;
  }
  container.innerHTML = conditionals.map(c => `
    <div class="conditional-item">
      <div class="conditional-item__header">
        <span class="conditional-item__hash">${api.shortHash(c.hash, 8, 4)}</span>
        <span class="conditional-item__type">${c.condition_type}</span>
      </div>
      <div class="conditional-item__meta">
        timeout: height ${api.formatNumber(c.timeout_height)} | submitted: height ${api.formatNumber(c.submitted_at)}
      </div>
      ${c.hash ? `<div class="intent-item__actions"><a class="ex-starbridge-link" href="${starbridgeHref(`dregg://turn/${c.hash}`)}">Debug turn in Starbridge</a></div>` : ''}
    </div>
  `).join('');
}
