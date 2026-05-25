/**
 * AgentCipherclerk: High-level wrapper for token minting, attenuation, and verification.
 *
 * Manages a root key and provides ergonomic methods for the macaroon-based
 * authorization token lifecycle.
 */

import type {
  MintResult,
  AttenuateResult,
  VerifyResult,
  KeyResult,
} from "./types";

/**
 * Options for attenuating a token.
 */
export interface AttenuateOptions {
  /** Service to restrict the token to. */
  service?: string;
  /** Comma-separated list of allowed actions. */
  actions?: string;
  /** Expiry in seconds from now. 0 means no expiry. */
  expiresSecs?: number;
}

/**
 * Options for verifying a token.
 */
export interface VerifyOptions {
  /** Application ID to verify against. */
  appId?: string;
  /** Action to verify. */
  action?: string;
}

/**
 * AgentCipherclerk wraps the pyana macaroon token operations into a stateful,
 * object-oriented interface. It holds a root key and provides methods for
 * the full token lifecycle: mint, attenuate, verify.
 *
 * @example
 * ```ts
 * import { AgentCipherclerk } from "@pyana/sdk";
 *
 * const cclerk = await AgentCipherclerk.create();
 * const token = await cclerk.mint("my-service");
 * const restricted = await cclerk.attenuate(token.token, {
 *   service: "my-service",
 *   actions: "read",
 *   expiresSecs: 3600,
 * });
 * const result = await cclerk.verify(restricted.token, { action: "read" });
 * console.log(result.allowed); // true
 * ```
 */
export class AgentCipherclerk {
  private rootKey: Uint8Array;
  private wasm: typeof import("pyana-wasm");

  private constructor(wasm: typeof import("pyana-wasm"), rootKey: Uint8Array) {
    this.wasm = wasm;
    this.rootKey = rootKey;
  }

  /**
   * Create a new AgentCipherclerk with a randomly generated root key.
   *
   * @param wasm - The initialized pyana-wasm module.
   * @returns A new AgentCipherclerk instance with a fresh root key.
   */
  static async create(wasm: typeof import("pyana-wasm")): Promise<AgentCipherclerk> {
    const keyResult: KeyResult = wasm.generate_root_key();
    const rootKey = new Uint8Array(keyResult.key_bytes);
    return new AgentCipherclerk(wasm, rootKey);
  }

  /**
   * Create an AgentCipherclerk from an existing root key.
   *
   * @param wasm - The initialized pyana-wasm module.
   * @param rootKey - A 32-byte root key (Uint8Array or hex string).
   * @returns A new AgentCipherclerk instance using the provided key.
   * @throws Error if the key is not exactly 32 bytes.
   */
  static fromKey(
    wasm: typeof import("pyana-wasm"),
    rootKey: Uint8Array | string
  ): AgentCipherclerk {
    const keyBytes =
      typeof rootKey === "string" ? hexToBytes(rootKey) : rootKey;
    if (keyBytes.length !== 32) {
      throw new Error(
        `Root key must be exactly 32 bytes, got ${keyBytes.length}`
      );
    }
    return new AgentCipherclerk(wasm, keyBytes);
  }

  /**
   * Get the root key as a hex string.
   */
  get keyHex(): string {
    return bytesToHex(this.rootKey);
  }

  /**
   * Get the raw root key bytes.
   */
  get keyBytes(): Uint8Array {
    return new Uint8Array(this.rootKey);
  }

  /**
   * Mint a new root token for the given service/location.
   *
   * This creates an unrestricted token that can later be attenuated.
   *
   * @param location - The service name or location identifier.
   * @returns The minted token result with the encoded token string.
   * @throws Error if the WASM call fails.
   */
  async mint(location: string): Promise<MintResult> {
    try {
      return this.wasm.mint_token(this.rootKey, location) as MintResult;
    } catch (e) {
      throw new Error(`Failed to mint token: ${extractError(e)}`);
    }
  }

  /**
   * Attenuate (restrict) an existing token with additional caveats.
   *
   * Attenuation is monotonic: you can only further restrict a token,
   * never broaden its permissions.
   *
   * @param tokenStr - The encoded token string to attenuate.
   * @param options - Restriction options (service, actions, expiry).
   * @returns The attenuated token result.
   * @throws Error if the token is invalid or the WASM call fails.
   */
  async attenuate(
    tokenStr: string,
    options: AttenuateOptions = {}
  ): Promise<AttenuateResult> {
    const service = options.service ?? "";
    const actions = options.actions ?? "";
    const expiresSecs = options.expiresSecs ?? 0;

    try {
      return this.wasm.attenuate_token(
        tokenStr,
        this.rootKey,
        service,
        actions,
        BigInt(expiresSecs)
      ) as AttenuateResult;
    } catch (e) {
      throw new Error(`Failed to attenuate token: ${extractError(e)}`);
    }
  }

  /**
   * Verify a token against a specific request.
   *
   * Checks all caveats (service, action, expiry) and returns whether
   * the token grants access.
   *
   * @param tokenStr - The encoded token string to verify.
   * @param options - The request to verify against.
   * @returns Verification result with allowed/denied status.
   * @throws Error if the token is malformed or the WASM call fails.
   */
  async verify(
    tokenStr: string,
    options: VerifyOptions = {}
  ): Promise<VerifyResult> {
    const appId = options.appId ?? "";
    const action = options.action ?? "";

    try {
      return this.wasm.verify_token(
        tokenStr,
        this.rootKey,
        appId,
        action
      ) as VerifyResult;
    } catch (e) {
      throw new Error(`Failed to verify token: ${extractError(e)}`);
    }
  }
}

// ============================================================================
// Hex utilities
// ============================================================================

function hexToBytes(hex: string): Uint8Array {
  if (hex.length % 2 !== 0) {
    throw new Error("Hex string must have even length");
  }
  const bytes = new Uint8Array(hex.length / 2);
  for (let i = 0; i < bytes.length; i++) {
    bytes[i] = parseInt(hex.substring(i * 2, i * 2 + 2), 16);
  }
  return bytes;
}

function bytesToHex(bytes: Uint8Array): string {
  return Array.from(bytes)
    .map((b) => b.toString(16).padStart(2, "0"))
    .join("");
}

function extractError(e: unknown): string {
  if (e instanceof Error) return e.message;
  return String(e);
}
