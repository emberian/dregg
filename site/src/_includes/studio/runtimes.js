/**
 * Runtime registry — single source of truth mapping a runtime kind id to its
 * human-readable label and async factory.
 *
 * Surfaces (Playground, Explorer, Starbridge) import RUNTIME_KINDS to populate
 * runtime pickers and to instantiate by id. Adding a new runtime impl means
 * touching this file plus its own module — nothing else.
 */
import { createInMemoryRuntime } from './runtime-in-memory.js';
import { createRemoteRuntime } from './runtime-remote.js';
import { createExtensionRuntime } from './runtime-extension.js';

export const RUNTIME_KINDS = {
  'in-memory': { label: 'In-browser (wasm)', factory: createInMemoryRuntime },
  'extension': { label: 'Cipherclerk extension', factory: createExtensionRuntime },
  'remote': { label: 'Remote (live node)', factory: createRemoteRuntime },
};
