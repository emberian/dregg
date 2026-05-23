/**
 * pyana explorer — API client module.
 *
 * Connects to a pyana node's HTTP API and provides typed accessor methods
 * for federation state queries. Node URL is configurable via localStorage.
 */

const STORAGE_KEY = 'pyana_node_url';
const DEFAULT_URL = 'https://devnet.pyana.fg-goose.online';

/** Get the configured node URL. */
export function getNodeUrl() {
  return localStorage.getItem(STORAGE_KEY) || DEFAULT_URL;
}

/** Set the node URL (persists to localStorage). */
export function setNodeUrl(url) {
  localStorage.setItem(STORAGE_KEY, url);
}

/** Make a GET request to the node API. */
async function get(path) {
  const base = getNodeUrl();
  const res = await fetch(`${base}${path}`, {
    headers: { 'Accept': 'application/json' },
  });
  if (!res.ok) {
    throw new Error(`GET ${path} returned ${res.status}`);
  }
  return res.json();
}

/** Make a POST request to the node API. */
async function post(path, body) {
  const base = getNodeUrl();
  const res = await fetch(`${base}${path}`, {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
      'Accept': 'application/json',
    },
    body: JSON.stringify(body),
  });
  if (!res.ok) {
    throw new Error(`POST ${path} returned ${res.status}`);
  }
  return res.json();
}

// =============================================================================
// Public API
// =============================================================================

/** Get node health and basic stats. */
export async function getStatus() {
  return get('/status');
}

/** Get federation attested roots (block list). */
export async function getBlocks() {
  return get('/federation/roots');
}

/** Get a single block (attested root) by height. */
export async function getBlock(height) {
  // The roots endpoint returns all; filter client-side.
  const roots = await getBlocks();
  return roots.find(r => r.height === height) || null;
}

/** Get the latest checkpoint. */
export async function getCheckpoint() {
  return get('/checkpoint/latest');
}

/** Get a checkpoint at a specific height. */
export async function getCheckpointAt(height) {
  return get(`/checkpoint/${height}`);
}

/** Get all cells in the ledger. */
export async function getCells() {
  return get('/api/cells');
}

/** Get a single cell by hex ID (detailed view). */
export async function getCell(id) {
  return get(`/api/cell/${id}`);
}

/** Get wallet tokens (capabilities). */
export async function getTokens() {
  return get('/api/tokens');
}

/** Get the receipt chain. */
export async function getReceipts() {
  return get('/api/receipts');
}

/** Get active intents in the pool. */
export async function getIntents() {
  return get('/api/intents');
}

/** Get pending conditional turns. */
export async function getPendingConditionals() {
  return get('/api/conditionals');
}

/** Get PIR index info. */
export async function getPirInfo() {
  return get('/pir/info');
}

/** Get wallet status. */
export async function getWallet() {
  return get('/wallet');
}

/** Ping the node to test connectivity. Returns true if reachable. */
export async function ping() {
  try {
    await getStatus();
    return true;
  } catch {
    return false;
  }
}

// =============================================================================
// Utility
// =============================================================================

/** Shorten a hex hash for display (first 8 + last 4 chars). */
export function shortHash(hash, prefixLen = 8, suffixLen = 4) {
  if (!hash || hash.length <= prefixLen + suffixLen + 2) return hash || '--';
  return `${hash.slice(0, prefixLen)}...${hash.slice(-suffixLen)}`;
}

/** Format a Unix timestamp as relative time. */
export function relativeTime(ts) {
  if (!ts) return '--';
  const now = Math.floor(Date.now() / 1000);
  const diff = now - ts;
  if (diff < 0) return 'in the future';
  if (diff < 60) return `${diff}s ago`;
  if (diff < 3600) return `${Math.floor(diff / 60)}m ago`;
  if (diff < 86400) return `${Math.floor(diff / 3600)}h ago`;
  return `${Math.floor(diff / 86400)}d ago`;
}

/** Format a Unix timestamp as ISO-like string. */
export function formatTime(ts) {
  if (!ts) return '--';
  return new Date(ts * 1000).toLocaleString();
}

/** Format large numbers with comma separators. */
export function formatNumber(n) {
  if (n === null || n === undefined) return '--';
  return n.toLocaleString();
}
