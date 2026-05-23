/**
 * Typed HTTP client helpers for communicating with the Pyana node.
 */

import type { NodeConfig, NodeRequestResult } from "./types";

const REQUEST_TIMEOUT_MS = 10000;

/**
 * Build HTTP headers for node API requests.
 */
export function getNodeHeaders(config: NodeConfig): Record<string, string> {
  const headers: Record<string, string> = { "Content-Type": "application/json" };
  if (config.devnetKey) {
    headers["X-Devnet-Key"] = config.devnetKey;
  }
  return headers;
}

/**
 * Make an HTTP request to the node API with proper error handling.
 */
export async function nodeRequest<T = unknown>(
  config: NodeConfig,
  path: string,
  options: RequestInit = {},
): Promise<NodeRequestResult<T>> {
  const url = config.nodeUrl.replace(/\/$/, "") + path;
  const baseHeaders = getNodeHeaders(config);
  const mergedHeaders = { ...baseHeaders, ...(options.headers as Record<string, string> || {}) };

  try {
    const resp = await fetch(url, {
      signal: AbortSignal.timeout(REQUEST_TIMEOUT_MS),
      ...options,
      headers: mergedHeaders,
    });

    if (resp.ok) {
      const data = (await resp.json().catch(() => null)) as T | null;
      return { ok: true, data: data ?? undefined, status: resp.status };
    } else {
      const errText = await resp.text().catch(() => "");
      return { ok: false, error: `HTTP ${resp.status}: ${errText}`, status: resp.status };
    }
  } catch (e: unknown) {
    const err = e as Error & { name?: string };
    if (err.name === "TimeoutError" || err.name === "AbortError") {
      return { ok: false, error: "Node request timed out. Is the node online?" };
    }
    return { ok: false, error: `Network error: ${err.message}` };
  }
}

/**
 * Fetch raw bytes from the node (for storage reads).
 */
export async function nodeRequestRaw(
  config: NodeConfig,
  path: string,
): Promise<{ ok: true; data: ArrayBuffer } | { ok: false; error: string }> {
  const url = config.nodeUrl.replace(/\/$/, "") + path;
  const headers = getNodeHeaders(config);

  try {
    const resp = await fetch(url, {
      signal: AbortSignal.timeout(15000),
      headers,
    });
    if (!resp.ok) {
      return { ok: false, error: `Storage read failed: HTTP ${resp.status}` };
    }
    const buffer = await resp.arrayBuffer();
    return { ok: true, data: buffer };
  } catch (e: unknown) {
    const err = e as Error;
    return { ok: false, error: `Storage read failed: ${err.message}` };
  }
}
