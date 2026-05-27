/**
 * <dregg-outbox uri="dregg://outbox/queue"> — Cipherclerk extension durable submission queue.
 */

import { parseRef } from '../uri.js';
import { InspectorBase, emptyState, renderParseError, shortHex } from './_base.js';

function statusCounts(entries) {
  const counts = { pending: 0, submitting: 0, failed: 0, submitted: 0, total: entries.length };
  for (const entry of entries) {
    const key = entry?.status || 'pending';
    if (counts[key] == null) counts[key] = 0;
    counts[key] += 1;
  }
  return counts;
}

function fmtTime(ms) {
  const n = Number(ms || 0);
  if (!n) return 'never';
  try { return new Date(n).toLocaleTimeString(); } catch { return String(ms); }
}

function prettyEndpoint(entry) {
  const endpoint = entry?.endpoint || '';
  const node = entry?.nodeUrl || '';
  if (!node) return endpoint;
  return `${node.replace(/\/$/, '')}${endpoint}`;
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
      const counts = statusCounts(entries);
      const pending = counts.pending + counts.submitting;

      if (mode === 'compact') {
        return html`
          <div class="dregg-inspector dregg-outbox dregg-outbox--compact">
            <div class="dregg-outbox__summary">
              <span><strong>${counts.total}</strong> total</span>
              <span><strong>${pending}</strong> pending</span>
              <span><strong>${counts.failed}</strong> failed</span>
            </div>
            <button type="button" class="dregg-outbox__btn" disabled=${!this._runtime.flushOutbox || !entries.length} onClick=${flush}>Flush</button>
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
              <button type="button" class="dregg-outbox__btn" disabled=${!this._runtime.flushOutbox} onClick=${flush}>Flush</button>
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
            <button type="button" class="dregg-outbox__btn" disabled=${!this._runtime.flushOutbox} onClick=${flush}>Flush due now</button>
          </header>
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
                    <button type="button" class="dregg-outbox__drop" disabled=${!this._runtime.dropOutboxEntry} onClick=${() => drop(id)}>Drop</button>
                  </div>
                  <dl class="dregg-inspector__kv dregg-outbox__kv">
                    <dt>id</dt><dd><code title=${id}>${shortHex(id, 18)}</code></dd>
                    <dt>kind</dt><dd>${entry.kind || 'unknown'}</dd>
                    <dt>target</dt><dd><code title=${prettyEndpoint(entry)}>${prettyEndpoint(entry)}</code></dd>
                    <dt>turn</dt><dd>${entry.turnId ? html`<code title=${entry.turnId}>${shortHex(entry.turnId, 18)}</code>` : 'n/a'}</dd>
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
