/**
 * Cross-browser compatibility layer for WebExtension APIs.
 *
 * Firefox MV3 background scripts do not support chrome.storage.session.
 * We fall back to chrome.storage.local with a "_sess_" prefix for
 * session-like data.  The prefix keeps fallback keys namespaced so they
 * do not collide with ordinary local-storage entries.
 */

const SESSION_PREFIX = "_sess_";

function sessionFallbackKey(key: string): string {
  return SESSION_PREFIX + key;
}

function hasSessionStorage(): boolean {
  try {
    return typeof chrome !== "undefined" && !!chrome.storage?.session;
  } catch {
    return false;
  }
}

/**
 * Session-compatible storage that prefers chrome.storage.session when
 * available (Chrome) and falls back to prefixed chrome.storage.local on
 * Firefox.
 */
export const compatSession = {
  async get(key: string): Promise<Record<string, unknown>> {
    if (hasSessionStorage()) {
      return chrome.storage.session.get(key);
    }
    const result = await chrome.storage.local.get(sessionFallbackKey(key));
    const value = result[sessionFallbackKey(key)];
    return value !== undefined ? { [key]: value } : {};
  },

  async set(items: Record<string, unknown>): Promise<void> {
    if (hasSessionStorage()) {
      return chrome.storage.session.set(items);
    }
    const prefixed: Record<string, unknown> = {};
    for (const [k, v] of Object.entries(items)) {
      prefixed[sessionFallbackKey(k)] = v;
    }
    return chrome.storage.local.set(prefixed);
  },
};

/**
 * The extension URL prefix for this browser.
 * Chrome:  "chrome-extension://<id>/"
 * Firefox: "moz-extension://<id>/"
 */
export const extensionPrefix: string = (() => {
  try {
    return chrome.runtime.getURL("");
  } catch {
    return "";
  }
})();

/**
 * Check if a URL belongs to this extension (popup page, options page,
 * etc.). Works for both Chrome and Firefox URL schemes.
 */
export function isExtensionPageUrl(url: string | undefined): boolean {
  if (!url) return false;
  return url.startsWith(extensionPrefix);
}
