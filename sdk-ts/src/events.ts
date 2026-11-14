/**
 * `node.subscribe(filter)` — the SDK edge of the receipt nervous system.
 *
 * The node broadcasts every committed receipt at `GET /api/events/stream`
 * (SSE; node/src/events.rs). [`NodeEvents.subscribe`] turns that into a
 * reconnecting `AsyncIterable<Receipt>` of the public [`Receipt`] noun — the
 * same artifact `.turn()….sign().submit()` returns, so observation and
 * action speak one language.
 *
 * Delivery: exactly-once per connection (the node streams its receipt chain
 * by cursor), at-least-once across reconnects (`Last-Event-ID` resume; a
 * receipt interrupted mid-delivery may repeat — dedupe by `receiptHash` if
 * it matters). Receipts arrive proofless while the STARK is in the node's
 * async prove pool; fetch the attestation later via
 * `NodeClient.turnProof(..)`.
 *
 * ```ts
 * const events = new NodeEvents("https://node.dregg.net");
 * for await (const receipt of events.subscribe(new ReceiptFilter())) {
 *   console.log("committed:", receipt.turnHash);
 * }
 * ```
 *
 * The SSE parser subset mirrors `extension/src/sse.ts` (the extension lane's
 * consumer of the same stream): `event:` / `data:` (multi-line) / `id:` /
 * comment heartbeats / blank-line dispatch, CR/CRLF/LF tolerated.
 */

import { Receipt, type TurnReceiptJson } from "./receipt";
import { hexEncode } from "./internal/bytes";

/** Server-side stream filter (`?cell=…&kind=…`). */
export class ReceiptFilter {
  private cellHexValue: string | undefined;
  private kindValue: string | undefined;

  /**
   * Only receipts touching `cell` (the agent cell, an event-emitting cell,
   * or the commit record's cell).
   */
  cell(cell: Uint8Array): this {
    this.cellHexValue = hexEncode(cell);
    return this;
  }

  /** [`cell`] with a raw hex id (e.g. straight from an explorer URL). */
  cellHex(cell: string): this {
    this.cellHexValue = cell;
    return this;
  }

  /**
   * Only receipts whose commit record names this effect kind
   * (e.g. `set_field`, `transfer`, `turn_committed`).
   */
  kind(kind: string): this {
    this.kindValue = kind;
    return this;
  }

  query(): string {
    const q = new URLSearchParams();
    if (this.cellHexValue) q.set("cell", this.cellHexValue);
    if (this.kindValue) q.set("kind", this.kindValue);
    const s = q.toString();
    return s.length > 0 ? `?${s}` : "";
  }
}

interface SseEvent {
  event: string;
  data: string;
  id: string | null;
}

/** Incremental SSE parser (spec subset; see module docs). */
export function createSseParser(): { feed(chunk: string): SseEvent[] } {
  let buffer = "";
  let eventType = "";
  let dataLines: string[] = [];
  let id: string | null = null;

  function dispatch(out: SseEvent[]): void {
    if (dataLines.length === 0) {
      eventType = "";
      return;
    }
    out.push({ event: eventType || "message", data: dataLines.join("\n"), id });
    eventType = "";
    dataLines = [];
  }

  function processLine(line: string, out: SseEvent[]): void {
    if (line === "") {
      dispatch(out);
      return;
    }
    if (line.startsWith(":")) return; // comment / keep-alive
    const colon = line.indexOf(":");
    const field = colon === -1 ? line : line.slice(0, colon);
    let value = colon === -1 ? "" : line.slice(colon + 1);
    if (value.startsWith(" ")) value = value.slice(1);
    switch (field) {
      case "event":
        eventType = value;
        break;
      case "data":
        dataLines.push(value);
        break;
      case "id":
        if (!value.includes("\0")) id = value;
        break;
      default:
        break;
    }
  }

  return {
    feed(chunk: string): SseEvent[] {
      buffer += chunk;
      const out: SseEvent[] = [];
      let start = 0;
      for (let i = 0; i < buffer.length; i++) {
        const c = buffer[i];
        if (c === "\n" || c === "\r") {
          processLine(buffer.slice(start, i), out);
          if (c === "\r" && buffer[i + 1] === "\n") i++;
          start = i + 1;
        }
      }
      buffer = buffer.slice(start);
      return out;
    },
  };
}

/** The wire envelope of one SSE `receipt` event. */
interface WireReceiptEvent {
  chain_index: number;
  receipt_hash: string;
  turn_hash: string;
  cells: string[];
  kinds: string[];
  height: number;
  has_proof: boolean;
  proof_status?: string;
  finality: string;
  timestamp: number;
  receipt: TurnReceiptJson;
}

export interface NodeEventsOptions {
  devnetKey?: string;
  /** Initial reconnect backoff (ms). Doubles per failure, capped at 15 s. */
  initialBackoffMs?: number;
}

/**
 * The live receipt feed: an `AsyncIterable<Receipt>` (also consumable via
 * the inherent [`next`]). [`close`] (or breaking out of `for await`) ends
 * the subscription; it otherwise reconnects forever.
 */
export class ReceiptStream implements AsyncIterable<Receipt> {
  private queue: Receipt[] = [];
  private waiter: ((r: Receipt | null) => void) | undefined;
  private closed = false;
  private abort = new AbortController();

  constructor(
    private readonly url: string,
    private readonly headers: Record<string, string>,
    initialBackoffMs: number,
  ) {
    void this.run(initialBackoffMs);
  }

  private push(r: Receipt): void {
    const w = this.waiter;
    if (w) {
      this.waiter = undefined;
      w(r);
    } else {
      this.queue.push(r);
    }
  }

  private async run(initialBackoffMs: number): Promise<void> {
    let lastEventId: string | null = null;
    let backoff = initialBackoffMs;
    const decoder = new TextDecoder();
    while (!this.closed) {
      try {
        const headers: Record<string, string> = {
          accept: "text/event-stream",
          ...this.headers,
        };
        if (lastEventId !== null) headers["last-event-id"] = lastEventId;
        const resp = await fetch(this.url, { headers, signal: this.abort.signal });
        if (resp.ok && resp.body) {
          const parser = createSseParser();
          const reader = resp.body.getReader();
          for (;;) {
            const { done, value } = await reader.read();
            if (done || this.closed) break;
            for (const event of parser.feed(decoder.decode(value, { stream: true }))) {
              if (event.id !== null) lastEventId = event.id;
              if (event.event !== "receipt") continue;
              let wire: WireReceiptEvent;
              try {
                wire = JSON.parse(event.data) as WireReceiptEvent;
              } catch {
                continue;
              }
              this.push(
                Receipt.fromTurnReceipt(wire.receipt, {
                  turnHash: wire.turn_hash,
                  receiptHash: wire.receipt_hash,
                  chainIndex: wire.chain_index,
                  hasProofHint: wire.has_proof,
                  proofStatus: wire.proof_status,
                  finality: wire.finality,
                }),
              );
              backoff = initialBackoffMs;
            }
          }
        }
      } catch {
        // network error / aborted — fall through to backoff or exit
      }
      if (this.closed) break;
      await new Promise((r) => setTimeout(r, backoff));
      backoff = Math.min(backoff * 2, 15_000);
    }
    // Drain any waiter on close.
    const w = this.waiter;
    if (w) {
      this.waiter = undefined;
      w(null);
    }
  }

  /** The next committed receipt (`null` only after [`close`]). */
  next(): Promise<Receipt | null> {
    const head = this.queue.shift();
    if (head !== undefined) return Promise.resolve(head);
    if (this.closed) return Promise.resolve(null);
    return new Promise((resolve) => {
      this.waiter = resolve;
    });
  }

  /** End the subscription. */
  close(): void {
    this.closed = true;
    this.abort.abort();
    const w = this.waiter;
    if (w) {
      this.waiter = undefined;
      w(null);
    }
  }

  async *[Symbol.asyncIterator](): AsyncIterator<Receipt> {
    try {
      for (;;) {
        const r = await this.next();
        if (r === null) return;
        yield r;
      }
    } finally {
      this.close();
    }
  }
}

/** A node's event surface: subscribe to its committed-receipt stream. */
export class NodeEvents {
  private readonly baseUrl: string;
  private readonly opts: NodeEventsOptions;

  /** Point at a node's base URL (e.g. `https://node.dregg.net`). */
  constructor(baseUrl: string, opts: NodeEventsOptions = {}) {
    this.baseUrl = baseUrl.replace(/\/+$/, "");
    this.opts = opts;
  }

  /**
   * Subscribe to the node's committed receipts. Reconnects with exponential
   * backoff and `Last-Event-ID` resume; the stream ends only when closed.
   */
  subscribe(filter: ReceiptFilter = new ReceiptFilter()): ReceiptStream {
    const headers: Record<string, string> = {};
    if (this.opts.devnetKey) headers["X-Devnet-Key"] = this.opts.devnetKey;
    return new ReceiptStream(
      `${this.baseUrl}/api/events/stream${filter.query()}`,
      headers,
      this.opts.initialBackoffMs ?? 500,
    );
  }
}
