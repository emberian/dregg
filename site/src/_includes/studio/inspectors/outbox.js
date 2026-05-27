/**
 * <dregg-outbox uri="dregg://outbox/queue"> — Cipherclerk extension durable submission queue.
 */

import { parseRef } from '../uri.js';
import { InspectorBase, emptyState, renderParseError, shortHex } from './_base.js';

function statusCounts(entries) {
  const now = Date.now();
  const counts = { pending: 0, submitting: 0, failed: 0, submitted: 0, due: 0, blocked: 0, total: entries.length };
  for (const entry of entries) {
    const key = entry?.status || 'pending';
    if (counts[key] == null) counts[key] = 0;
    counts[key] += 1;
    if (key !== 'submitted' && Number(entry?.nextAttemptAt || 0) <= now) counts.due += 1;
    if (key === 'failed') counts.blocked += 1;
  }
  return counts;
}

function fmtTime(ms) {
  const n = Number(ms || 0);
  if (!n) return 'never';
  try { return new Date(n).toLocaleTimeString(); } catch { return String(ms); }
}

function fmtDelay(ms) {
  const n = Number(ms || 0);
  if (!n) return 'now';
  const delta = n - Date.now();
  if (delta <= 0) return 'now';
  const seconds = Math.ceil(delta / 1000);
  if (seconds < 60) return `${seconds}s`;
  const minutes = Math.ceil(seconds / 60);
  if (minutes < 60) return `${minutes}m`;
  return `${Math.ceil(minutes / 60)}h`;
}

function prettyEndpoint(entry) {
  const endpoint = entry?.endpoint || '';
  const node = entry?.nodeUrl || '';
  if (!node) return endpoint;
  return `${node.replace(/\/$/, '')}${endpoint}`;
}

function authHint(entry) {
  const headers = entry?.headers || {};
  const keys = Object.keys(headers);
  if (!keys.length) return 'none';
  const authKey = keys.find(k => k.toLowerCase() === 'authorization');
  if (authKey && headers[authKey]) return 'authorization header present';
  const nodeKey = keys.find(k => k.toLowerCase().includes('dregg') || k.toLowerCase().includes('devnet'));
  return nodeKey ? `${nodeKey} header present` : `${keys.length} header${keys.length === 1 ? '' : 's'}`;
}

function statusMessage(counts, status) {
  if (status?.message) return status.message;
  if (!counts.total) return 'No queued extension submissions.';
  if (counts.due) return `${counts.due} queued submission${counts.due === 1 ? '' : 's'} ready to replay.`;
  if (counts.failed) return `${counts.failed} submission${counts.failed === 1 ? '' : 's'} blocked until manual retry or drop.`;
  return 'Queued submissions are waiting for retry backoff.';
}

function statusTone(status) {
  const state = status?.state || 'idle';
  if (state === 'ok') return 'ok';
  if (state === 'warn' || state === 'error' || state === 'unavailable') return 'warn';
  return '';
}

function endpointGroups(entries) {
  const groups = new Map();
  for (const entry of entries) {
    let key = 'local extension';
    try {
      const endpoint = prettyEndpoint(entry);
      key = endpoint ? new URL(endpoint, window.location.origin).host : key;
    } catch {}
    groups.set(key, (groups.get(key) || 0) + 1);
  }
  return Array.from(groups, ([host, count]) => ({ host, count }))
    .sort((a, b) => b.count - a.count || a.host.localeCompare(b.host));
}

function payloadHint(entry) {
  const body = entry?.body || entry?.payload || entry?.request || null;
  if (!body || typeof body !== 'object') return entry?.method || 'submission';
  const keys = Object.keys(body).slice(0, 4);
  return keys.length ? keys.join(', ') : 'empty payload';
}

class DreggOutbox extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri') || 'dregg://outbox/queue';
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    let parsed = null;
    try { parsed = parseRef(refAttr); } catch {}
    if (renderParseError(this, refAttr, parsed, 'outbox')) return;

    const outboxSignal = this._runtime.getOutbox ? this._runtime.getOutbox() : null;
    const outboxStatusSignal = this._runtime.getOutboxStatus ? this._runtime.getOutboxStatus() : null;
    const root = document.createElement('div');
    this.appendChild(root);

    const flush = async () => {
      if (this._runtime.flushOutbox) await this._runtime.flushOutbox();
    };
    const drop = async (id) => {
      if (id && this._runtime.dropOutboxEntry) await this._runtime.dropOutboxEntry(id);
    };

    const Component = () => {
      if (!outboxSignal) {
        return emptyState(
          html,
          'No extension outbox in this runtime',
          'Switch to the Cipherclerk extension runtime to inspect durable offline submissions.',
        );
      }
      const entries = Array.isArray(outboxSignal.value) ? outboxSignal.value : [];
      const outboxStatus = outboxStatusSignal?.value || null;
      const counts = statusCounts(entries);
      const pending = counts.pending + counts.submitting;
      const groups = endpointGroups(entries);
      const canFlush = !!this._runtime.flushOutbox && entries.some(entry => entry.status !== 'submitted');
      const noticeClass = `dregg-inspector__notice${statusTone(outboxStatus) ? ` dregg-inspector__notice--${statusTone(outboxStatus)}` : ''}`;

      if (mode === 'compact') {
        return html`
          <div class="dregg-inspector dregg-outbox dregg-outbox--compact">
            <div class="dregg-outbox__summary">
              <span><strong>${counts.total}</strong> total</span>
              <span><strong>${pending}</strong> pending</span>
              <span><strong>${counts.failed}</strong> failed</span>
            </div>
            <button type="button" class="dregg-outbox__btn" disabled=${!canFlush} onClick=${flush}>Replay</button>
          </div>`;
      }

      if (!entries.length) {
        return html`
          <div class="dregg-inspector dregg-outbox">
            <header class="dregg-outbox__head">
              <div>
                <span class="dregg-inspector__kind">outbox</span>
                <code class="dregg-inspector__id">queue</code>
              </div>
              <button type="button" class="dregg-outbox__btn" disabled=${!this._runtime.flushOutbox} onClick=${flush}>Replay queue</button>
            </header>
            ${emptyState(html, 'Outbox empty', 'Signed submissions are reaching the node or no offline work has been queued yet.')}
          </div>`;
      }

      return html`
        <div class="dregg-inspector dregg-outbox">
          <header class="dregg-outbox__head">
            <div>
              <span class="dregg-inspector__kind">outbox</span>
              <code class="dregg-inspector__id">queue</code>
              <span class="dregg-inspector__meta">${counts.total} entries · ${pending} pending · ${counts.failed} failed</span>
            </div>
            <button type="button" class="dregg-outbox__btn" disabled=${!canFlush} onClick=${flush}>Replay / flush</button>
          </header>
          <div class=${noticeClass}>
            ${statusMessage(counts, outboxStatus)}
            ${outboxStatus?.updatedAt ? html`<span class="dregg-outbox__notice-time"> Updated ${fmtTime(outboxStatus.updatedAt)}.</span>` : null}
          </div>
          <div class="dregg-inspector__summary">
            <div><span>Due Now</span><strong>${String(counts.due)}</strong></div>
            <div><span>Pending</span><strong>${String(pending)}</strong></div>
            <div><span>Failed</span><strong>${String(counts.failed)}</strong></div>
            <div><span>Submitted</span><strong>${String(counts.submitted)}</strong></div>
          </div>
          <div class="dregg-outbox__routes">
            ${groups.map(group => html`
              <span><strong>${String(group.count)}</strong> ${group.host}</span>
            `)}
          </div>
          <div class="dregg-outbox__cards">
            ${entries.map((entry) => {
              const id = entry.id || '';
              const status = entry.status || 'pending';
              const statusClass = `dregg-outbox__status dregg-outbox__status--${status}`;
              return html`
                <article class="dregg-outbox__entry">
                  <div class="dregg-outbox__entry-head">
                    <div>
                      <span class=${statusClass}>${status}</span>
                      <strong>${entry.label || entry.kind || 'submission'}</strong>
                    </div>
                    <div class="dregg-outbox__entry-actions">
                      <span title=${entry.nextAttemptAt ? `Next retry: ${fmtTime(entry.nextAttemptAt)}` : ''}>retry ${fmtDelay(entry.nextAttemptAt)}</span>
                      <button type="button" class="dregg-outbox__drop" disabled=${!this._runtime.dropOutboxEntry} onClick=${() => drop(id)}>Drop local</button>
                    </div>
                  </div>
                  <dl class="dregg-inspector__kv dregg-outbox__kv">
                    <dt>id</dt><dd><code title=${id}>${shortHex(id, 18)}</code></dd>
                    <dt>kind</dt><dd>${entry.kind || 'unknown'}</dd>
                    <dt>node target</dt><dd><code title=${prettyEndpoint(entry)}>${prettyEndpoint(entry)}</code></dd>
                    <dt>auth</dt><dd>${authHint(entry)}</dd>
                    <dt>turn</dt><dd>${entry.turnId ? html`<code title=${entry.turnId}>${shortHex(entry.turnId, 18)}</code>` : 'n/a'}</dd>
                    <dt>payload</dt><dd><code>${payloadHint(entry)}</code></dd>
                    <dt>attempts</dt><dd>${String(entry.attempts ?? 0)}</dd>
                    <dt>next retry</dt><dd>${fmtTime(entry.nextAttemptAt)}</dd>
                    <dt>updated</dt><dd>${fmtTime(entry.updatedAt)}</dd>
                    <dt>last error</dt><dd>${entry.lastError || 'none'}</dd>
                  </dl>
                </article>`;
            })}
          </div>
        </div>`;
    };

    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}

if (!customElements.get('dregg-outbox')) customElements.define('dregg-outbox', DreggOutbox);
