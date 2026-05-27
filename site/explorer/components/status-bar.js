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
  const test = document.getElementById('settings-test');
  const backdrop = modal.querySelector('.ex-modal__backdrop');
  const urlInput = document.getElementById('node-url-input');
  const autoRefreshToggle = document.getElementById('auto-refresh-toggle');

  urlInput.value = api.getNodeUrl();
  autoRefreshToggle.checked = state.autoRefresh;

  btn.addEventListener('click', () => modal.hidden = false);
  cancel.addEventListener('click', () => modal.hidden = true);
  backdrop.addEventListener('click', () => modal.hidden = true);

  test.addEventListener('click', async () => {
    api.setNodeUrl(urlInput.value.trim() || 'http://localhost:8420');
    await refresh();
  });

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

  bus.on('diagnostics:updated', renderDiagnostics);
  if (state.diagnostics) renderDiagnostics(state.diagnostics);
}

function renderDiagnostics(diagnostic) {
  const endpoint = document.getElementById('diag-endpoint');
  const http = document.getElementById('diag-http');
  const cors = document.getElementById('diag-cors');
  const latency = document.getElementById('diag-latency');
  const message = document.getElementById('diag-message');
  if (!endpoint || !http || !cors || !latency || !message || !diagnostic) return;

  endpoint.textContent = diagnostic.url || diagnostic.path || '/status';
  http.textContent = diagnostic.status ? `${diagnostic.status} ${diagnostic.statusText || ''}`.trim() : diagnostic.statusText || 'no response';
  cors.textContent = diagnostic.cors || (diagnostic.ok ? 'ok' : 'unknown');
  latency.textContent = Number.isFinite(diagnostic.latencyMs) ? `${diagnostic.latencyMs} ms` : '--';
  message.textContent = diagnostic.ok
    ? `Last checked ${api.formatTime(Date.parse(diagnostic.checkedAt) / 1000)}.`
    : diagnostic.errorMessage || 'The browser could not read /status. Check that the node is running and allows this origin.';
  message.classList.toggle('node-diagnostics__message--error', !diagnostic.ok);
}
