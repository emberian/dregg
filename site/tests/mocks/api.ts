/**
 * Mock API responses for offline testing.
 * Intercepts all fetch requests to the explorer API and returns deterministic data.
 */

import { Page } from '@playwright/test';

export const mockStatus = {
  height: 42,
  peer_count: 2,
  mode: 'blocklace',
  version: '0.1.0',
  node_id: 'abc123def456',
  uptime: 3600,
  revocations: 1,
  notes: 7,
  intent_pool_size: 3,
  pending_conditionals: 2,
};

export const mockBlocks = [
  { height: 42, root: 'aabbccdd11223344aabbccdd11223344aabbccdd11223344aabbccdd11223344', timestamp: 1700000042, signatures: 3, creator: 0 },
  { height: 41, root: '11223344aabbccdd11223344aabbccdd11223344aabbccdd11223344aabbccdd', timestamp: 1700000036, signatures: 3, creator: 1 },
  { height: 40, root: '5566778899001122556677889900112255667788990011225566778899001122', timestamp: 1700000030, signatures: 2, creator: 2 },
];

export const mockCells = [
  { id: 'abc123def456abc123def456abc123def456abc123def456abc123def456abc1', mode: 'sovereign', balance: 1000, nonce: 5 },
  { id: 'def456abc123def456abc123def456abc123def456abc123def456abc123def4', mode: 'hosted', balance: 500, nonce: 12 },
  { id: '789012345678901234567890123456789012345678901234567890123456789a', mode: 'factory', balance: 0, nonce: 0 },
];

export const mockReceipts = [
  { hash: 'receipt001', height: 42, turn_hash: 'turn001', effects: ['credit'], timestamp: 1700000042 },
  { hash: 'receipt002', height: 41, turn_hash: 'turn002', effects: ['transfer'], timestamp: 1700000036 },
];

export const mockTokens = [
  { id: 'cap001', service: 'ledger', actions: ['transfer', 'query'], attenuated: false, ttl: 99999 },
  { id: 'cap002', service: 'gallery', actions: ['bid'], attenuated: true, ttl: 3600 },
];

export const mockIntents = [
  { id: 'intent001', type: 'swap', status: 'pending', creator: 'abc123', amount: 100 },
  { id: 'intent002', type: 'limit_order', status: 'pending', creator: 'def456', amount: 50 },
];

export const mockConditionals = [
  { id: 'cond001', condition: 'height >= 50', action: 'release_funds', status: 'waiting' },
];

export const mockCheckpoint = {
  height: 42,
  merkle_root: 'aabb112233445566aabb112233445566aabb112233445566aabb112233445566',
  nullifier_root: 'ccdd778899001122ccdd778899001122ccdd778899001122ccdd778899001122',
  timestamp: 1700000042,
};

export const mockFederation = {
  height: 42,
  peer_count: 2,
  node_count: 3,
  roots: mockBlocks,
  checkpoint: mockCheckpoint,
  mode: 'blocklace',
};

export const mockDiscovery = {
  federation: [
    { id: 'node0', address: 'localhost:8420' },
    { id: 'node1', address: 'localhost:8421' },
    { id: 'node2', address: 'localhost:8422' },
  ],
  commit: 'deadbeef',
  gateway: { ws: 'ws://localhost:9000/ws' },
};

/**
 * Set up API route interception for the explorer.
 * Intercepts all requests to common API paths and returns mock data.
 */
export async function mockExplorerApi(page: Page) {
  // Intercept any external API calls
  await page.route('**/status', route => {
    return route.fulfill({ json: mockStatus });
  });

  await page.route('**/federation/roots', route => {
    return route.fulfill({ json: mockBlocks });
  });

  await page.route('**/api/cells', route => {
    return route.fulfill({ json: mockCells });
  });

  await page.route('**/api/cell/**', route => {
    return route.fulfill({ json: { found: true, ...mockCells[0] } });
  });

  await page.route('**/api/receipts', route => {
    return route.fulfill({ json: mockReceipts });
  });

  await page.route('**/api/tokens', route => {
    return route.fulfill({ json: mockTokens });
  });

  await page.route('**/api/intents', route => {
    return route.fulfill({ json: mockIntents });
  });

  await page.route('**/api/conditionals', route => {
    return route.fulfill({ json: mockConditionals });
  });

  await page.route('**/checkpoint/**', route => {
    return route.fulfill({ json: mockCheckpoint });
  });

  await page.route('**/pir/info', route => {
    return route.fulfill({ json: { backend: 'spiral', entries: 100 } });
  });

  await page.route('**/cipherclerk', route => {
    return route.fulfill({ json: { balance: 1000, tokens: 2 } });
  });
}

/**
 * Set up discovery.json mock for the playground.
 */
export async function mockPlaygroundDiscovery(page: Page) {
  await page.route('**/discovery.json', route => {
    return route.fulfill({ json: mockDiscovery });
  });
}

/**
 * Block WebSocket connections (prevent real network calls).
 */
export async function blockWebSockets(page: Page) {
  await page.route('**/ws', route => {
    return route.abort();
  });
  await page.route('wss://**', route => {
    return route.abort();
  });
}

/**
 * Block WASM loading and let the fallback path handle it.
 */
export async function blockWasm(page: Page) {
  await page.route('**/*.wasm', route => {
    return route.abort();
  });
  await page.route('**/pyana_wasm.js', route => {
    // Return a minimal module that immediately rejects init
    return route.fulfill({
      contentType: 'application/javascript',
      body: `export default function init() { return Promise.reject(new Error('WASM not available in test')); }`,
    });
  });
}
