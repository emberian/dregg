/**
 * `NodeClient` (a node's HTTP surface) and `AgentRuntime` (an identity bound
 * to a node — the holder of `.turn()`).
 *
 * The Rust `AgentRuntime` executes in-process; the TS runtime is a remote
 * client over the node's signed-envelope ingress
 * (`POST /api/turns/submit-signed`, postcard `SignedTurn`). The shape is the
 * same: `Identity → .turn() → verbs → .sign() → .submit() → Receipt`.
 */

import { Identity } from "./identity";
import { NodeEvents, createSseParser } from "./events";
import { Receipt, TurnProof } from "./receipt";
import { TurnBuilder } from "./turns";
import { TrustlineClient } from "./trustline";
import { ChannelsClient } from "./channels";
import { ServiceEconomy } from "./service-economy";
import type { Bytes32, CellId } from "./internal/wire";
import { blake3 } from "./internal/blake3";
import { hexDecodeExact, hexEncode } from "./internal/bytes";
import type { Turn } from "./internal/wire";
import { turnHash } from "./internal/wire";

/**
 * The agent receipt head a cell view carries — strict, like the Rust
 * `agent_receipt_head`: `null` is "no turn committed yet", a string must be 32
 * hex bytes, and a view WITHOUT the field is an error (the head is unknown, and
 * guessing `undefined` would bind a first-turn claim the node then refuses).
 */
export function agentReceiptHeadOf(cell: CellDetail): Uint8Array | undefined {
  const head = cell.last_receipt_hash;
  if (head === null) return undefined;
  if (typeof head === "string") return hexDecodeExact(head, 32);
  if (head === undefined) {
    throw new Error(
      "the cell view carries no last_receipt_hash, so this agent's receipt head is unknown",
    );
  }
  throw new Error(`cell last_receipt_hash is not a hex string: ${JSON.stringify(head)}`);
}

export interface NodeClientOptions {
  /** Devnet gate key, sent as both `X-Devnet-Key` and `Authorization: Bearer`. */
  devnetKey?: string;
  /**
   * Pin the executor federation id (32 bytes or hex). When unset, it is
   * discovered: a configured federation's local id from `/api/federations`,
   * else `blake3(node operator pubkey)` — exactly
   * `node/src/executor_setup.rs::federation_id_for_executor`'s fallback for
   * an unconfigured solo node (the devnet shape).
   */
  federationId?: Uint8Array | string;
  /**
   * Pin the acting cell's turn nonce, for OFFLINE signing.
   *
   * `dregg-action-sig-v3` binds the submitting turn's nonce into every action
   * signature, so `TurnBuilder.sign()` must know it. Normally it is read from
   * the node (the cell's live replay counter); pinning it — the exact parallel
   * of [`federationId`] — lets `.sign()` produce a real, verifiable signature
   * with no node round trip.
   *
   * ⚠ The pin must be the nonce the turn will actually ride: a signature bound
   * to the wrong nonce verifies nowhere. `submit()` still re-reads the live
   * nonce and re-signs if it has moved, so an offline-signed turn submitted
   * later stays correct.
   */
  nonce?: bigint | number;
  /** Request timeout (ms). Default 15000. */
  timeoutMs?: number;
}

/** `GET /api/node/identity`. */
export interface NodeIdentity {
  public_key: string;
  agent_cell: string;
  unlocked: boolean;
  agent_balance: number | null;
  agent_nonce: number | null;
}

/** `GET /api/cell/{id}` (subset). */
export interface CellDetail {
  id: string;
  found: boolean;
  balance: number;
  nonce: number;
  public_key: string;
  fields: string[];
  /**
   * This cell's receipt-chain head AS AN AGENT: the `receipt_hash` of the last
   * turn it committed, `null` before its first. The node serves it for a
   * not-found cell too. See [`agentReceiptHeadOf`].
   */
  last_receipt_hash?: string | null;
  [extra: string]: unknown;
}

/** `POST /api/turns/submit-signed` response. */
export interface SubmitSignedTurnResponse {
  accepted?: boolean;
  turn_hash?: string | null;
  signer?: string | null;
  action_count?: number;
  proof_status?: string;
  has_witness?: boolean;
  witness_count?: number;
  error?: string | null;
}

/** `GET /api/receipts` entries. */
export interface ReceiptInfo {
  chain_index: number;
  chain_head: boolean;
  receipt_hash: string;
  turn_hash: string;
  agent: string;
  pre_state: string;
  post_state: string;
  timestamp: number;
  computrons_used: number;
  action_count: number;
  previous_receipt_hash: string | null;
  finality: string;
  was_encrypted: boolean;
  was_burn: boolean;
  has_proof: boolean;
  proof_status?: string;
}

/** The node rejected a request / a turn. */
export class NodeError extends Error {
  readonly status?: number;

  constructor(message: string, status?: number) {
    super(message);
    this.name = "NodeError";
    this.status = status;
  }
}

export class NodeClient {
  readonly baseUrl: string;
  private readonly opts: NodeClientOptions;
  private cachedFederationId: Uint8Array | undefined;
  private readonly noncePin: bigint | undefined;

  constructor(baseUrl: string, opts: NodeClientOptions = {}) {
    this.baseUrl = baseUrl.replace(/\/+$/, "");
    this.opts = opts;
    if (opts.federationId !== undefined) {
      this.cachedFederationId =
        typeof opts.federationId === "string"
          ? hexDecodeExact(opts.federationId, 32)
          : Uint8Array.from(opts.federationId);
    }
    this.noncePin = opts.nonce !== undefined ? BigInt(opts.nonce) : undefined;
  }

  /**
   * The pinned turn nonce, if the caller supplied one — see
   * [`NodeClientOptions.nonce`]. `undefined` means "read it from the node".
   */
  pinnedNonce(): bigint | undefined {
    return this.noncePin;
  }

  private headers(extra: Record<string, string> = {}): Record<string, string> {
    const h: Record<string, string> = { ...extra };
    if (this.opts.devnetKey) {
      h["X-Devnet-Key"] = this.opts.devnetKey;
      h["Authorization"] = `Bearer ${this.opts.devnetKey}`;
    }
    return h;
  }

  private async request<T>(path: string, init: RequestInit = {}): Promise<T> {
    const url = this.baseUrl + path;
    const resp = await fetch(url, {
      signal: AbortSignal.timeout(this.opts.timeoutMs ?? 15000),
      ...init,
      headers: this.headers((init.headers as Record<string, string>) ?? {}),
    });
    if (!resp.ok) {
      const body = await resp.text().catch(() => "");
      throw new NodeError(`HTTP ${resp.status} from ${path}: ${body.slice(0, 300)}`, resp.status);
    }
    return (await resp.json()) as T;
  }

  /**
   * `GET {path}` → parsed JSON. The generic read used by the organ clients
   * (trustline / channels / attested-query); carries the devnet headers and
   * timeout. Throws [`NodeError`] on a non-2xx.
   */
  getJson<T>(path: string): Promise<T> {
    return this.request<T>(path);
  }

  /**
   * `POST {path}` with a JSON body → parsed JSON. The generic write used by
   * the organ clients. Throws [`NodeError`] on a non-2xx.
   */
  postJson<T>(path: string, body: unknown): Promise<T> {
    return this.request<T>(path, {
      method: "POST",
      body: JSON.stringify(body),
      headers: { "Content-Type": "application/json" },
    });
  }

  /**
   * Subscribe to a node SSE route as a one-shot async iterable of parsed
   * `data:` JSON payloads (no reconnect — that lives in [`NodeEvents`] for
   * the receipt stream). Used by the channels message stream.
   */
  async *sseStream<T>(path: string): AsyncIterable<T> {
    const resp = await fetch(this.baseUrl + path, {
      headers: this.headers({ Accept: "text/event-stream" }),
    });
    if (!resp.ok || !resp.body) {
      const txt = resp.body ? await resp.text().catch(() => "") : "";
      throw new NodeError(`HTTP ${resp.status} from ${path}: ${txt.slice(0, 300)}`, resp.status);
    }
    const reader = resp.body.getReader();
    const decoder = new TextDecoder();
    const parser = createSseParser();
    for (;;) {
      const { value, done } = await reader.read();
      if (done) break;
      for (const evt of parser.feed(decoder.decode(value, { stream: true }))) {
        if (evt.data) yield JSON.parse(evt.data) as T;
      }
    }
  }

  /** `GET /api/node/identity` — the node operator's identity. */
  nodeIdentity(): Promise<NodeIdentity> {
    return this.request<NodeIdentity>("/api/node/identity");
  }

  /** The node operator's Ed25519 public key (hex). Falls back from
   * `/api/node/identity` to `/status` for older node builds. */
  async operatorPublicKeyHex(): Promise<string> {
    try {
      return (await this.nodeIdentity()).public_key;
    } catch (e) {
      if (e instanceof NodeError && e.status === 404) {
        const status = await this.request<{ public_key: string }>("/status");
        return status.public_key;
      }
      throw e;
    }
  }

  /**
   * The node's attested height (`GET /status` → `latest_height`): the height a
   * turn's `validUntil` — a block height, not a Unix timestamp — is counted
   * from. A status without the field is an error, never height 0.
   */
  async latestHeight(): Promise<bigint> {
    const status = await this.request<{ latest_height?: number }>("/status");
    if (typeof status.latest_height !== "number") {
      throw new Error("node /status carries no latest_height");
    }
    return BigInt(status.latest_height);
  }

  /** `GET /api/cell/{id}` — live cell state (balance, nonce, slots). */
  cell(cellId: Uint8Array | string): Promise<CellDetail> {
    const hex = typeof cellId === "string" ? cellId : hexEncode(cellId);
    return this.request<CellDetail>(`/api/cell/${hex}`);
  }

  /** `GET /api/receipts` — the node's recent committed receipts. */
  receipts(): Promise<ReceiptInfo[]> {
    return this.request<ReceiptInfo[]>("/api/receipts");
  }

  /**
   * `cellId`'s receipt-chain head AS AN AGENT (`GET /api/cell/{id}` →
   * `last_receipt_hash`), or `undefined` before its first committed turn.
   *
   * This is the value a turn whose `agent` is `cellId` must carry as
   * `previous_receipt_hash`: the node admits a signed turn only when that field
   * equals `agent_receipt_head_hash(turn.agent)`. There is deliberately no
   * node-wide "chain head" reader here — the unfiltered `/api/receipts` tip is
   * some other agent's receipt whenever another agent committed since, and
   * threading it refused every such turn (and its retry, which read the same
   * tip). Same read as the Rust `NodeHttpClient::fetch_agent_receipt_head`.
   */
  async agentReceiptHead(cellId: Uint8Array | string): Promise<Uint8Array | undefined> {
    return agentReceiptHeadOf(await this.cell(cellId));
  }

  /**
   * The federation id the node's EXECUTOR verifies action signatures
   * against. Explicit option wins; else discovered (see
   * [`NodeClientOptions.federationId`]) and cached.
   */
  async federationId(): Promise<Uint8Array> {
    if (this.cachedFederationId) return this.cachedFederationId;
    // A configured federation: the local entry in /api/federations with a
    // real committee. An unconfigured solo node (the devnet default) serves
    // a placeholder there, while its executor binds blake3(operator pubkey).
    try {
      const feds = await this.request<Array<{ federation_id: string; is_local: boolean; committee_epoch: number; member_count: number }>>(
        "/api/federations",
      );
      const local = feds.find((f) => f.is_local && f.member_count > 0 && f.committee_epoch > 0);
      if (local) {
        this.cachedFederationId = hexDecodeExact(local.federation_id, 32);
        return this.cachedFederationId;
      }
    } catch {
      // fall through to the solo-node derivation
    }
    const operatorPk = await this.operatorPublicKeyHex();
    this.cachedFederationId = blake3(hexDecodeExact(operatorPk, 32));
    return this.cachedFederationId;
  }

  /**
   * `POST /api/faucet` — devnet: materialize a hosted cell (`amount: 0`)
   * and/or claim computrons (max 10000 per request). Passing `publicKey`
   * lets the node install a canonical hosted cell with a real owner key —
   * REQUIRED before that cell can pass Ed25519 turn authorization.
   */
  async faucet(
    recipient: Uint8Array | string,
    amount: number,
    publicKey?: Uint8Array | string,
  ): Promise<{ success: boolean; turn_hash?: string | null; amount: number; error?: string | null }> {
    const body: Record<string, unknown> = {
      recipient: typeof recipient === "string" ? recipient : hexEncode(recipient),
      amount,
    };
    if (publicKey !== undefined) {
      body.public_key = typeof publicKey === "string" ? publicKey : hexEncode(publicKey);
    }
    return this.request("/api/faucet", {
      method: "POST",
      body: JSON.stringify(body),
      headers: { "Content-Type": "application/json" },
    });
  }

  /** Submit a postcard `SignedTurn` envelope (the signed-byte ingress). */
  submitSignedEnvelope(envelope: Uint8Array): Promise<SubmitSignedTurnResponse> {
    return this.request<SubmitSignedTurnResponse>("/api/turns/submit-signed", {
      method: "POST",
      body: envelope as unknown as BodyInit,
      headers: { "Content-Type": "application/octet-stream" },
    });
  }

  /**
   * Find the committed receipt for `turnHashHex`, polling briefly — commits
   * land synchronously but the receipt listing is a separate read.
   */
  async receiptForTurn(turnHashHex: string, attempts = 10, delayMs = 300): Promise<Receipt> {
    const want = turnHashHex.toLowerCase();
    for (let i = 0; i < attempts; i++) {
      const infos = await this.receipts();
      const hit = infos.find((r) => r.turn_hash.toLowerCase() === want);
      if (hit) {
        return new Receipt({
          turnHash: hit.turn_hash,
          receiptHash: hit.receipt_hash,
          agent: hit.agent,
          preStateHash: hit.pre_state,
          postStateHash: hit.post_state,
          timestamp: hit.timestamp,
          computronsUsed: hit.computrons_used,
          actionCount: hit.action_count,
          previousReceiptHash: hit.previous_receipt_hash ?? undefined,
          finality: hit.finality,
          wasEncrypted: hit.was_encrypted,
          wasBurn: hit.was_burn,
          chainIndex: hit.chain_index,
          hasProofHint: hit.has_proof,
          proofStatus: hit.proof_status,
        });
      }
      await new Promise((r) => setTimeout(r, delayMs));
    }
    // The turn committed (the submit response said so); return the minimal noun.
    return new Receipt({ turnHash: want });
  }

  /**
   * Fetch the persisted full-turn STARK for a committed turn
   * (`GET /api/turn/{hash}/proof`) — proofs land asynchronously from the
   * node's prove pool; `undefined` until then.
   */
  async turnProof(turnHashHex: string): Promise<TurnProof | undefined> {
    try {
      const res = await this.request<{ turn_hash: string; proof_hex: string | null; proof_status?: string }>(
        `/api/turn/${turnHashHex}/proof`,
      );
      if (res.proof_status === "not_required") {
        throw new NodeError("coordination turn: executor/committee attestation only; validity proof required by this caller");
      }
      if (res.proof_status !== "proved" || !res.proof_hex || !/^(?:[0-9a-fA-F]{2})+$/.test(res.proof_hex)) {
        throw new NodeError("node did not return a proved artifact");
      }
      const bytes = new Uint8Array(res.proof_hex.length / 2);
      for (let i = 0; i < bytes.length; i++) {
        bytes[i] = parseInt(res.proof_hex.slice(i * 2, i * 2 + 2), 16);
      }
      return new TurnProof(hexDecodeExact(res.turn_hash, 32), bytes);
    } catch (e) {
      if (e instanceof NodeError && e.status === 404) return undefined;
      throw e;
    }
  }

  /** The node's committed-receipt event stream (SSE). */
  events(): NodeEvents {
    return new NodeEvents(this.baseUrl, { devnetKey: this.opts.devnetKey });
  }

  /**
   * The **trustline** organ (`.docs-history-noclaude/ORGANS.md` §1) over this node's
   * operator-local trustline service. Operator-gated — pass a `devnetKey`.
   */
  trustline(): TrustlineClient {
    return new TrustlineClient(this);
  }

  /**
   * The **channels** organ (`.docs-history-noclaude/ORGANS.md` §4) over this node's channels
   * service. Operator-gated — pass a `devnetKey`.
   */
  channels(): ChannelsClient {
    return new ChannelsClient(this);
  }
}

/**
 * An identity bound to a node — the SDK's acting surface. Open the typed
 * turn builder with [`turn`]:
 *
 * ```ts
 * const runtime = new AgentRuntime(identity, "https://node.dregg.net");
 * const receipt = await (await runtime.turn().writeU64(0, 42).sign()).submit();
 * ```
 */
export class AgentRuntime {
  readonly identity: Identity;
  readonly node: NodeClient;

  constructor(identity: Identity, node: NodeClient | string, opts: NodeClientOptions = {}) {
    this.identity = identity;
    this.node = typeof node === "string" ? new NodeClient(node, opts) : node;
  }

  /** This identity's default agent cell (hex). */
  cellIdHex(): string {
    return this.identity.cellIdHex();
  }

  /**
   * Open the typed turn builder — the SDK's one public turn shape:
   * `runtime.turn().transfer(..).write(..).sign()` → `submit()` → `Receipt`.
   */
  turn(): TurnBuilder {
    return new TurnBuilder(this);
  }

  /**
   * Devnet bootstrap: materialize this identity's agent cell with its real
   * owner key and claim `amount` computrons.
   */
  async faucet(amount: number): Promise<void> {
    const res = await this.node.faucet(this.identity.cellId(), amount, this.identity.publicKey);
    if (!res.success) {
      throw new NodeError(`faucet refused: ${res.error ?? "unknown"}`);
    }
  }

  /** The **trustline** organ on this runtime's node ([`NodeClient.trustline`]). */
  trustline(): TrustlineClient {
    return this.node.trustline();
  }

  /** The **channels** organ on this runtime's node ([`NodeClient.channels`]). */
  channels(): ChannelsClient {
    return this.node.channels();
  }

  private serviceEconomy: ServiceEconomy | undefined;

  /**
   * The **service-economy** surface (`docs/guide/SERVICE-ECONOMY-SDK.md`) — the
   * TS twin of the Rust SDK facade. `runtime.services.invoke(...)`,
   * `runtime.execution.lease(...)`, `runtime.pay(...)`.
   */
  private econ(): ServiceEconomy {
    return (this.serviceEconomy ??= new ServiceEconomy(this));
  }

  /** Find + call a service (`econ.invoke`); `runtime.services.invoke(...)`. */
  get services(): ServiceEconomy {
    return this.econ();
  }

  /** Open a durable, metered execution lease (`econ.lease`);
   * `runtime.execution.lease(...)`. */
  get execution(): ServiceEconomy {
    return this.econ();
  }

  /**
   * **`pay`** — move `amount` of `asset` from this runtime's cell to `to`
   * through the canonical `Payable` `pay` desugar (one conserving
   * `Effect::Transfer`). The few-lines front door; mirrors Rust
   * `AgentRuntime::pay`.
   */
  pay(to: CellId, amount: number | bigint, asset: Bytes32): Promise<Receipt> {
    return this.econ().pay(to, amount, asset);
  }

  /**
   * The agent cell's current nonce (0 for a never-seen cell) — the value
   * `dregg-action-sig-v3` binds into the action signature.
   *
   * A pinned [`NodeClientOptions.nonce`] wins (the offline-signing path);
   * otherwise it is read from the node's live cell state.
   */
  async currentNonce(): Promise<bigint> {
    const pinned = this.node.pinnedNonce();
    if (pinned !== undefined) return pinned;
    try {
      const cell = await this.node.cell(this.identity.cellId());
      return cell.found ? BigInt(cell.nonce) : 0n;
    } catch (e) {
      if (e instanceof NodeError && e.status === 404) return 0n;
      throw e;
    }
  }

  /**
   * The two per-agent coordinates a submitted turn binds, from ONE read of
   * `GET /api/cell/{agent}` so they describe the same moment: the live nonce
   * (a pinned [`NodeClientOptions.nonce`] still wins) and this agent's own
   * receipt-chain head for `previous_receipt_hash`.
   */
  async chainBinding(): Promise<{ nonce: bigint; previousReceiptHash: Uint8Array | undefined }> {
    const cell = await this.node.cell(this.identity.cellId());
    const pinned = this.node.pinnedNonce();
    return {
      nonce: pinned ?? (cell.found ? BigInt(cell.nonce) : 0n),
      previousReceiptHash: agentReceiptHeadOf(cell),
    };
  }

  /**
   * Envelope-sign and submit a finished turn; resolve the committed
   * [`Receipt`]. Used by `AuthorizedTurn.submit()`.
   */
  async submitTurn(turn: Turn): Promise<Receipt> {
    const envelope = this.identity.signTurnEnvelope(turn);
    const res = await this.node.submitSignedEnvelope(envelope);
    const hashHex = res.turn_hash ?? hexEncode(turnHash(turn));
    if (!res.accepted) {
      throw new NodeError(`turn rejected: ${res.error ?? "unknown"} (turn ${hashHex})`);
    }
    return this.node.receiptForTurn(hashHex);
  }
}
