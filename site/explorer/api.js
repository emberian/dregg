/**
 * dregg explorer — API client module.
 *
 * Connects to a dregg node's HTTP API and provides typed accessor methods
 * for federation state queries. Node URL is configurable via localStorage.
 */

const STORAGE_KEY = 'dregg_node_url';
const ADMIN_TOKEN_KEY = 'dregg_admin_token';
const DEFAULT_URL = 'https://devnet.dregg.fg-goose.online';

/** Get the configured node URL. */
export function getNodeUrl() {
  return localStorage.getItem(STORAGE_KEY) || DEFAULT_URL;
}

/** Set the node URL (persists to localStorage). */
export function setNodeUrl(url) {
  localStorage.setItem(STORAGE_KEY, url);
}

/** Thrown when an authenticated endpoint is hit without a valid token. */
export class AuthRequired extends Error {
  constructor(path) { super(`AuthRequired: ${path}`); this.name = 'AuthRequired'; }
}

/** Get the admin bearer token (sessionStorage — wiped on tab close). */
export function getAdminToken() {
  return sessionStorage.getItem(ADMIN_TOKEN_KEY) || '';
}

/** Set the admin bearer token. Fires `dregg:admin-token-changed`. */
export function setAdminToken(token) {
  if (token) sessionStorage.setItem(ADMIN_TOKEN_KEY, token);
  else sessionStorage.removeItem(ADMIN_TOKEN_KEY);
  window.dispatchEvent(new CustomEvent('dregg:admin-token-changed'));
}

/** Clear the admin bearer token. */
export function clearAdminToken() {
  sessionStorage.removeItem(ADMIN_TOKEN_KEY);
  window.dispatchEvent(new CustomEvent('dregg:admin-token-changed'));
}

/** Make a GET request to the node API. */
async function get(path, { auth = false } = {}) {
  const base = getNodeUrl();
  const headers = { 'Accept': 'application/json' };
  if (auth) {
    const tok = getAdminToken();
    if (!tok) throw new AuthRequired(path);
    headers['Authorization'] = `Bearer ${tok}`;
  }
  const res = await fetch(`${base}${path}`, { headers });
  if (res.status === 401 || res.status === 403) throw new AuthRequired(path);
  if (!res.ok) {
    throw new Error(`GET ${path} returned ${res.status}`);
  }
  return res.json();
}

/** Fetch JSON with status, timing, and browser-visible network/CORS failure detail. */
async function probeJson(path, { auth = false } = {}) {
  const base = getNodeUrl();
  const url = `${base}${path}`;
  const startedAt = performance.now();
  const headers = { 'Accept': 'application/json' };
  if (auth) {
    const tok = getAdminToken();
    if (!tok) throw new AuthRequired(path);
    headers['Authorization'] = `Bearer ${tok}`;
  }

  try {
    const res = await fetch(url, { headers });
    const latencyMs = Math.round(performance.now() - startedAt);
    const contentType = res.headers.get('content-type') || '';
    const diagnostic = {
      ok: res.ok,
      url,
      path,
      status: res.status,
      statusText: res.statusText,
      latencyMs,
      contentType,
      cors: res.type,
      checkedAt: new Date().toISOString(),
    };
    if (!res.ok) {
      const err = new Error(`GET ${path} returned ${res.status}`);
      err.diagnostic = diagnostic;
      throw err;
    }
    return { data: await res.json(), diagnostic };
  } catch (error) {
    if (error.diagnostic) throw error;
    const diagnostic = {
      ok: false,
      url,
      path,
      status: null,
      statusText: 'Network/CORS failure',
      latencyMs: Math.round(performance.now() - startedAt),
      contentType: '',
      cors: 'blocked',
      checkedAt: new Date().toISOString(),
      errorName: error?.name || 'Error',
      errorMessage: error?.message || String(error),
    };
    const err = new Error(`GET ${path} failed before an HTTP response`);
    err.diagnostic = diagnostic;
    throw err;
  }
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

/** Probe /status and return both the payload and live connection diagnostics. */
export async function diagnoseStatus() {
  return probeJson('/status');
}

/** Get federation attested roots (block list). */
export async function getBlocks() {
  return get('/federation/roots');
}

/** Get a single block (attested root) by height. */
export async function getBlock(height) {
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

/** Get cipherclerk tokens (capabilities). */
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

/** Get cipherclerk status. */
export async function getCipherclerk() {
  return get('/cipherclerk');
}

/** Get federation status (combines status + roots + checkpoint). */
export async function getFederationStatus() {
  const [status, roots, checkpoint] = await Promise.all([
    getStatus(),
    getBlocks().catch(() => []),
    getCheckpoint().catch(() => null),
  ]);
  return { ...status, roots, checkpoint, node_count: (status.peer_count || 0) + 1 };
}

// =============================================================================
// Service / queue / name / delegation endpoints
//
// These hit the node's service-mesh / nameservice / delegation surface. The
// node implementations of these endpoints are in flight; until they ship, the
// views fall back to mock data when these throw.
// =============================================================================

/** List registered services. */
export async function listServices() {
  return get('/api/services');
}

/** Get programmable-queue summary (anonymous). */
export async function getProgrammableQueue(service) {
  return get(`/api/services/${encodeURIComponent(service)}/queue/programmable`);
}
/** Get blinded-queue summary (anonymous). */
export async function getBlindedQueue(service) {
  return get(`/api/services/${encodeURIComponent(service)}/queue/blinded`);
}
/** Get inbox-queue summary (anonymous). */
export async function getInboxQueue(service) {
  return get(`/api/services/${encodeURIComponent(service)}/queue/inbox`);
}

/** Get programmable-queue entries (admin). */
export async function getProgrammableQueueEntries(service) {
  return get(`/api/services/${encodeURIComponent(service)}/queue/programmable/entries`, { auth: true });
}
/** Get blinded-queue entries (admin). */
export async function getBlindedQueueEntries(service) {
  return get(`/api/services/${encodeURIComponent(service)}/queue/blinded/entries`, { auth: true });
}
/** Get inbox-queue entries (admin). */
export async function getInboxQueueEntries(service) {
  return get(`/api/services/${encodeURIComponent(service)}/queue/inbox/entries`, { auth: true });
}

/** List names matching an optional prefix + tag filter. */
export async function listNames({ prefix = '', tag = '' } = {}) {
  const qs = new URLSearchParams();
  if (prefix) qs.set('prefix', prefix);
  if (tag) qs.set('tag', tag);
  const suffix = qs.toString() ? `?${qs}` : '';
  return get(`/api/names${suffix}`);
}

/** Resolve a single name to its dregg:// URI + metadata. */
export async function resolveName(name) {
  return get(`/api/names/${encodeURIComponent(name)}`);
}

/** List known signed delegations matching an optional free-text query. */
export async function listDelegations({ q = '' } = {}) {
  const suffix = q ? `?q=${encodeURIComponent(q)}` : '';
  return get(`/api/delegations${suffix}`);
}

/** Get a single delegation envelope by id or envelope-hash. */
export async function getDelegation(idOrHash) {
  return get(`/api/delegations/${encodeURIComponent(idOrHash)}`);
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

function firstValue(obj, keys, fallback = undefined) {
  for (const key of keys) {
    const value = obj?.[key];
    if (value !== undefined && value !== null && value !== '') return value;
  }
  return fallback;
}

function asNumber(value, fallback = null) {
  if (value === null || value === undefined || value === '') return fallback;
  const n = Number(value);
  return Number.isFinite(n) ? n : fallback;
}

/** Latest committed height from current and older node status payloads. */
export function statusHeight(status) {
  return asNumber(firstValue(status, ['latest_height', 'height', 'block_height'], null));
}

/** Connected peers reported by the node. */
export function statusPeers(status) {
  return asNumber(firstValue(status, ['peer_count', 'peers'], 0), 0);
}

/** Revocation count from current and older node status payloads. */
export function statusRevocations(status) {
  return asNumber(firstValue(status, ['revocation_count', 'revocations'], 0), 0);
}

/** Note count from current and older node status payloads. */
export function statusNotes(status) {
  return asNumber(firstValue(status, ['note_count', 'notes'], 0), 0);
}

/** Attested-root hash from current and older root payloads. */
export function blockRoot(block) {
  return firstValue(block, ['merkle_root', 'root', 'ledger_state_root', 'hash'], null);
}

/** Human status for nodes that do not yet expose an explicit healthy flag. */
export function healthLabel(status) {
  if (!status) return 'unknown';
  if (status.healthy === true) return 'healthy';
  if (status.healthy === false) return 'degraded';
  if (typeof status.status === 'string') return status.status;
  if (statusHeight(status) !== null) return 'responding';
  return 'unknown';
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
