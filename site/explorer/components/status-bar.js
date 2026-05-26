/**
 * Status bar component — connection status, block height, settings modal.
 */

import { bus, state, updateState, refresh, startAutoRefresh, stopAutoRefresh } from '../app.js';
import * as api from '../api.js';

export function init() {
  initSettings();
  initConnectionDisplay();
}

function initConnectionDisplay() {
  bus.on('connection:changed', (connected) => {
    const el = document.getElementById('connection-status');
    const label = el.querySelector('.ex-connection__label');
    el.classList.toggle('connected', connected);
    el.classList.toggle('error', !connected);
    label.textContent = connected ? 'connected' : 'disconnected';
  });

  bus.on('status:updated', (status) => {
    const el = document.getElementById('nav-height-value');
    if (status && el) {
      el.textContent = api.formatNumber(api.statusHeight(status));
    }
  });
}

function initSettings() {
  const modal = document.getElementById('settings-modal');
  const btn = document.getElementById('settings-btn');
  const cancel = document.getElementById('settings-cancel');
  const save = document.getElementById('settings-save');
  const backdrop = modal.querySelector('.ex-modal__backdrop');
  const urlInput = document.getElementById('node-url-input');
  const autoRefreshToggle = document.getElementById('auto-refresh-toggle');

  urlInput.value = api.getNodeUrl();
  autoRefreshToggle.checked = state.autoRefresh;

  btn.addEventListener('click', () => modal.hidden = false);
  cancel.addEventListener('click', () => modal.hidden = true);
  backdrop.addEventListener('click', () => modal.hidden = true);

  save.addEventListener('click', () => {
    api.setNodeUrl(urlInput.value.trim() || 'http://localhost:8420');
    const autoRefresh = autoRefreshToggle.checked;
    updateState({ autoRefresh });
    localStorage.setItem('dregg_auto_refresh', autoRefresh);
    modal.hidden = true;
    refresh();
    if (autoRefresh) startAutoRefresh();
    else stopAutoRefresh();
  });
}
