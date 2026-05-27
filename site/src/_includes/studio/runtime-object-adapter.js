import { parseRef } from './uri.js';

const LIST_METHODS = Object.freeze({
  cell: 'listCells',
  receipt: 'listReceipts',
  turn: 'listReceipts',
  block: 'listBlocks',
  federation: 'listKnownFederations',
  intent: 'listIntents',
  outbox: 'getOutbox',
});

const GET_METHODS = Object.freeze({
  cell: 'getCell',
  receipt: 'getReceipt',
  turn: 'getTurn',
  block: 'getBlock',
  federation: 'getFederation',
  intent: 'getIntent',
  outbox: 'getOutbox',
});

export const RUNTIME_OBJECT_KINDS = Object.freeze(Object.keys(LIST_METHODS));

export function normalizeObjectKind(kind) {
  const k = String(kind || '').toLowerCase();
  if (k === 'cells') return 'cell';
  if (k === 'receipts') return 'receipt';
  if (k === 'turns') return 'turn';
  if (k === 'blocks') return 'block';
  if (k === 'federations') return 'federation';
  if (k === 'intents') return 'intent';
  return k;
}

export function attachRuntimeObjectAdapter(runtime) {
  if (!runtime || typeof runtime !== 'object') return runtime;
  if (typeof runtime.listObjects !== 'function') {
    runtime.listObjects = (kind, ...args) => listRuntimeObjects(runtime, kind, ...args);
  }
  if (typeof runtime.getObject !== 'function') {
    runtime.getObject = (refOrKind, id, ...args) => getRuntimeObject(runtime, refOrKind, id, ...args);
  }
  return runtime;
}

export function listRuntimeObjects(runtime, kind, ...args) {
  const normalized = normalizeObjectKind(kind);
  const method = LIST_METHODS[normalized];
  if (!method || typeof runtime?.[method] !== 'function') return null;
  return runtime[method](...args);
}

export function getRuntimeObject(runtime, refOrKind, id, ...args) {
  const ref = coerceObjectRef(refOrKind, id, args);
  const method = GET_METHODS[ref.kind];
  if (!method || typeof runtime?.[method] !== 'function') return null;
  if (ref.kind === 'block') return runtime[method](blockLookup(ref));
  if (ref.kind === 'outbox') return runtime[method]();
  return runtime[method](ref.id, ...ref.args);
}

export function coerceObjectRef(refOrKind, id, args = []) {
  if (typeof refOrKind === 'string' && refOrKind.startsWith('dregg://')) {
    const parsed = parseRef(refOrKind);
    return { kind: normalizeObjectKind(parsed.kind), id: parsed.id, sub: parsed.sub || [], args: [] };
  }
  if (refOrKind && typeof refOrKind === 'object' && refOrKind.kind) {
    return {
      kind: normalizeObjectKind(refOrKind.kind),
      id: refOrKind.id,
      sub: refOrKind.sub || [],
      args: refOrKind.args || [],
    };
  }
  return { kind: normalizeObjectKind(refOrKind), id, sub: [], args };
}

function blockLookup(ref) {
  if (ref.sub?.length) return { fedIndex: ref.id, height: ref.sub[0] };
  if (ref.id && typeof ref.id === 'object') return ref.id;
  return ref.id;
}
