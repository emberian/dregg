/**
 * CipherclerkExtensionRuntime — Starbridge viewport over the browser extension.
 *
 * This runtime treats `window.dregg` as the authority boundary. It does not
 * recreate node state in JS; it surfaces extension-backed federation status,
 * known federations, and activity feed so Starbridge can inspect real
 * devnet/testnet/mainnet activity through the user's configured Cipherclerk.
 */

import { attachRuntimeObjectAdapter } from './runtime-object-adapter.js';

const CAPS = Object.freeze({
  read: true,
  mutate: false,
  debug: true,
  timeTravel: false,
});

function notPermitted(op) {
  return () => {
    throw new Error(`NotPermitted: CipherclerkExtensionRuntime does not expose ${op}; use window.dregg signing APIs from an app surface.`);
  };
}

function whenDregg() {
  return new Promise((resolve, reject) => {
    if (window.dregg) return resolve(window.dregg);
    window.addEventListener('dregg:ready', () => resolve(window.dregg), { once: true });
    setTimeout(() => reject(new Error('Cipherclerk extension window.dregg API not detected')), 4000);
  });
}

export async function createExtensionRuntime({ signals }) {
  if (!signals || typeof signals.signal !== 'function') {
    throw new Error('createExtensionRuntime: signals.signal is required');
  }
  const { signal, computed } = signals;
  const dregg = await whenDregg();

  const version = signal(0);
  const cursor = signal(0);
  const events = new EventTarget();
  const cellsSignal = signal([]);
  const knownFedsSignal = signal([]);
  const statusSignal = signal(null);
  const outboxStatusSignal = signal({ state: 'idle', message: 'Outbox idle', updatedAt: 0 });
  const traceEventsSignal = signal({ schema_version: 1, event_count: 0, events: [] });
  const balanceSignal = signal(null);
  const outboxSignal = signal([]);
  let destroyed = false;

  function bump() { version.value = version.value + 1; }
  function fire(type, detail) {
    events.dispatchEvent(new CustomEvent(type, { detail }));
  }

  function setOutboxStatus(state, message, extra = {}) {
    outboxStatusSignal.value = { state, message, updatedAt: Date.now(), ...extra };
    bump();
  }

  function pushEvent(kind, payload) {
    const cur = traceEventsSignal.value || { schema_version: 1, event_count: 0, events: [] };
    const event = {
      kind,
      payload,
      source: 'cipherclerk-extension',
      timestamp_ms: Date.now(),
    };
    const nextEvents = [...(cur.events || []), event].slice(-300);
    traceEventsSignal.value = {
      schema_version: cur.schema_version || 1,
      event_count: nextEvents.length,
      events: nextEvents,
    };
    bump();
    fire('activity', event);
  }

  async function refresh() {
    if (destroyed) return;
    try {
      if (typeof dregg.federationStatus === 'function') {
        const status = await dregg.federationStatus();
        statusSignal.value = status || null;
        const height = Number(status?.height ?? 0);
        if (Number.isFinite(height)) cursor.value = height;
      }
    } catch (e) {
      statusSignal.value = { error: e?.message || String(e) };
    }
    try {
      if (typeof dregg.listKnownFederations === 'function') {
        knownFedsSignal.value = await dregg.listKnownFederations() || [];
      }
    } catch {
      knownFedsSignal.value = [];
    }
    try {
      if (typeof dregg.queryBalance === 'function') {
        balanceSignal.value = await dregg.queryBalance();
      }
    } catch {
      balanceSignal.value = null;
    }
    try {
      if (typeof dregg.getActivityFeed === 'function') {
        const feed = await dregg.getActivityFeed();
        if (feed && Array.isArray(feed.events)) traceEventsSignal.value = feed;
      }
    } catch {
      // Older extension builds still deliver live events through dregg.on().
    }
    try {
      if (typeof dregg.listOutbox === 'function') {
        const outbox = await dregg.listOutbox();
        outboxSignal.value = Array.isArray(outbox) ? outbox : [];
      }
    } catch {
      outboxSignal.value = [];
      setOutboxStatus('unavailable', 'Outbox unavailable from this extension build');
    }
    bump();
  }

  const listeners = [];
  if (typeof dregg.on === 'function') {
    for (const name of ['activity', 'receipt', 'root', 'intent', 'note_announcement', 'federation', 'outbox']) {
      const cb = (payload) => {
        if (name === 'outbox') refresh().catch(() => {});
        pushEvent(name === 'root' ? 'federation' : name, payload);
      };
      try {
        dregg.on(name, cb);
        listeners.push([name, cb]);
      } catch {}
    }
  }

  const timer = setInterval(refresh, 2500);
  await refresh();

  function getFederation(idOrIndex) {
    return computed(() => {
      version.value;
      const list = knownFedsSignal.value || [];
      const idx = Number(idOrIndex);
      return list.find(f => f.federationId === idOrIndex || f.id === idOrIndex)
        || (!Number.isNaN(idx) ? list[idx] : null)
        || null;
    });
  }

  function destroy() {
    destroyed = true;
    clearInterval(timer);
    if (typeof dregg.off === 'function') {
      for (const [name, cb] of listeners) {
        try { dregg.off(name, cb); } catch {}
      }
    }
  }

  return attachRuntimeObjectAdapter({
    caps: CAPS,
    source: { kind: 'extension', label: 'Cipherclerk extension' },
    version,
    cursor,
    events,

    listCells: () => cellsSignal,
    getCell: () => signal(null),
    listReceipts: () => computed(() => (traceEventsSignal.value.events || [])
      .filter(e => e.kind === 'receipt' || e.kind === 'turn_lifecycle')),
    getReceipt: () => signal(null),
    getTurn: () => signal(null),
    listIntents: () => computed(() => (traceEventsSignal.value.events || [])
      .filter(e => e.kind === 'intent').map(e => e.payload || e)),
    getIntent: () => signal(null),
    listCapabilities: () => signal(null),
    getCapability: () => signal(null),
    listKnownFederations: () => knownFedsSignal,
    getFederation,
    listBlocks: () => signal([]),
    getBlock: () => signal(null),
    getTraceEvents: () => traceEventsSignal,
    getExtensionStatus: () => statusSignal,
    getBalance: () => balanceSignal,
    getOutbox: () => outboxSignal,
    getOutboxStatus: () => outboxStatusSignal,
    flushOutbox: async () => {
      if (typeof dregg.flushOutbox !== 'function') throw new Error('Cipherclerk extension does not expose flushOutbox');
      setOutboxStatus('flushing', 'Retrying queued submissions against the configured node');
      try {
        const result = await dregg.flushOutbox();
        if (result && Array.isArray(result.entries)) outboxSignal.value = result.entries;
        await refresh();
        const submitted = Number(result?.submitted || 0);
        const failed = Number(result?.failed || 0);
        const pending = Number(result?.pending || 0);
        setOutboxStatus(
          failed ? 'warn' : 'ok',
          `Flush complete: ${submitted} replayed, ${failed} failed, ${pending} still pending`,
          { result },
        );
        return result;
      } catch (e) {
        const message = e?.message || String(e);
        setOutboxStatus('error', `Flush failed: ${message}`);
        throw e;
      }
    },
    dropOutboxEntry: async (id) => {
      if (typeof dregg.dropOutboxEntry !== 'function') throw new Error('Cipherclerk extension does not expose dropOutboxEntry');
      setOutboxStatus('dropping', 'Dropping queued submission');
      try {
        const result = await dregg.dropOutboxEntry(id);
        await refresh();
        setOutboxStatus(result?.dropped ? 'ok' : 'warn', result?.dropped ? 'Queued submission dropped' : 'No matching queued submission found', { result });
        return result;
      } catch (e) {
        const message = e?.message || String(e);
        setOutboxStatus('error', `Drop failed: ${message}`);
        throw e;
      }
    },

    createAgent: notPermitted('createAgent'),
    createCell: notPermitted('createCell'),
    executeTurn: notPermitted('executeTurn'),
    mintToken: notPermitted('mintToken'),
    advanceHeight: notPermitted('advanceHeight'),

    destroy,
  });
}
