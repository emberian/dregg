/**
 * `Receipt` — the first of the SDK's two user-facing nouns.
 *
 * A `Receipt` is dregg's canonical proof-of-execution artifact: the committed
 * turn's hashes, the pre/post state roots, the agent cell, the federation
 * binding, and the receipt-chain link. Every authorized submission
 * (`AuthorizedTurn.submit()`) returns one, and the event stream
 * (`NodeEvents.subscribe`) yields the same noun — observation and action
 * speak one language.
 *
 * The proof is **lazily attached**: a `Receipt` is born proofless (the commit
 * decision is the executor's; the STARK is additive attestation) and a
 * [`TurnProof`] can be attached when the node's async prove pool produces one
 * (`fetchProof` pulls `/api/turn/{hash}/proof`).
 *
 * The second noun is `AttestedHistory` — the light-client whole-history
 * verdict. It is produced by verifying ONE succinct aggregate and is not yet
 * surfaced on the TS SDK (the verifier is Rust-side).
 */

import { bytesEqual, hexDecodeExact, hexEncode } from "./internal/bytes";

/** The wire-level canonical receipt as the node serializes it (serde JSON). */
export interface TurnReceiptJson {
  turn_hash: number[];
  forest_hash: number[];
  pre_state_hash: number[];
  post_state_hash: number[];
  timestamp: number;
  effects_hash: number[];
  computrons_used: number;
  action_count: number;
  previous_receipt_hash: number[] | null;
  agent: number[];
  federation_id?: number[];
  emitted_events?: unknown[];
  finality?: string;
  was_encrypted?: boolean;
  was_burn?: boolean;
  [extra: string]: unknown;
}

/**
 * The composed full-turn STARK attached to a receipt — opaque bytes bound to
 * the turn hash they attest (replay protection: a proof only attests the
 * turn it names). Verification happens Rust-side (`verify_full_turn`); the
 * TS SDK carries and transports the artifact.
 */
export class TurnProof {
  /** The turn hash this proof is bound to (32 bytes). */
  readonly turnHash: Uint8Array;
  /** The wire-serialized proof bytes. */
  readonly bytes: Uint8Array;

  constructor(turnHash: Uint8Array, bytes: Uint8Array) {
    if (turnHash.length !== 32) throw new Error("TurnProof: turnHash must be 32 bytes");
    this.turnHash = Uint8Array.from(turnHash);
    this.bytes = bytes;
  }

  get turnHashHex(): string {
    return hexEncode(this.turnHash);
  }
}

/** Thrown when an attachment names a different turn than the receipt. */
export class WrongTurnProofError extends Error {
  constructor(expectedHex: string, gotHex: string) {
    super(`proof is bound to turn ${gotHex}, receipt is turn ${expectedHex}`);
    this.name = "WrongTurnProofError";
  }
}

/** The normalized receipt fields every construction path can fill. */
export interface ReceiptFields {
  /** Hex turn hash (always present). */
  turnHash: string;
  /** Hex receipt hash, when the server reported it. */
  receiptHash?: string;
  /** Hex agent cell id. */
  agent?: string;
  preStateHash?: string;
  postStateHash?: string;
  timestamp?: number;
  computronsUsed?: number;
  actionCount?: number;
  previousReceiptHash?: string;
  finality?: string;
  wasEncrypted?: boolean;
  wasBurn?: boolean;
  /** Position in the node's receipt chain (SSE resume cursor). */
  chainIndex?: number;
  /** Whether the node reported an attached attestation at serve time. */
  hasProofHint?: boolean;
  /** Node policy hint, never proof verification. `not_required` means attestation only. */
  proofStatus?: string;
  /** The full canonical wire receipt, when available (SSE path). */
  raw?: TurnReceiptJson;
}

const num32ToHex = (a: number[] | null | undefined): string | undefined =>
  Array.isArray(a) ? hexEncode(Uint8Array.from(a)) : undefined;

/**
 * **The receipt noun.** A committed turn's proof-of-execution, with the
 * composed STARK proof lazily attached.
 */
export class Receipt {
  readonly turnHash: string;
  readonly receiptHash?: string;
  readonly agent?: string;
  readonly preStateHash?: string;
  readonly postStateHash?: string;
  readonly timestamp?: number;
  readonly computronsUsed?: number;
  readonly actionCount?: number;
  readonly previousReceiptHash?: string;
  readonly finality?: string;
  readonly wasEncrypted?: boolean;
  readonly wasBurn?: boolean;
  readonly chainIndex?: number;
  readonly hasProofHint?: boolean;
  readonly proofStatus?: string;
  readonly raw?: TurnReceiptJson;

  private attached: TurnProof | undefined;

  constructor(fields: ReceiptFields) {
    this.turnHash = fields.turnHash.toLowerCase();
    this.receiptHash = fields.receiptHash?.toLowerCase();
    this.agent = fields.agent?.toLowerCase();
    this.preStateHash = fields.preStateHash;
    this.postStateHash = fields.postStateHash;
    this.timestamp = fields.timestamp;
    this.computronsUsed = fields.computronsUsed;
    this.actionCount = fields.actionCount;
    this.previousReceiptHash = fields.previousReceiptHash;
    this.finality = fields.finality;
    this.wasEncrypted = fields.wasEncrypted;
    this.wasBurn = fields.wasBurn;
    this.chainIndex = fields.chainIndex;
    this.hasProofHint = fields.hasProofHint;
    this.proofStatus = fields.proofStatus;
    this.raw = fields.raw;
  }

  /** Build from the canonical wire receipt (the SSE `receipt` field). */
  static fromTurnReceipt(r: TurnReceiptJson, extra?: Partial<ReceiptFields>): Receipt {
    return new Receipt({
      turnHash: num32ToHex(r.turn_hash) ?? "",
      agent: num32ToHex(r.agent),
      preStateHash: num32ToHex(r.pre_state_hash),
      postStateHash: num32ToHex(r.post_state_hash),
      timestamp: r.timestamp,
      computronsUsed: r.computrons_used,
      actionCount: r.action_count,
      previousReceiptHash: num32ToHex(r.previous_receipt_hash) ?? undefined,
      finality: typeof r.finality === "string" ? r.finality.toLowerCase() : undefined,
      wasEncrypted: r.was_encrypted,
      wasBurn: r.was_burn,
      raw: r,
      ...extra,
    });
  }

  /** The attached proof, if one has been attached (receipts are born proofless). */
  proof(): TurnProof | undefined {
    return this.attached;
  }

  /** Whether a proof has been attached. */
  hasProof(): boolean {
    return this.attached !== undefined;
  }

  /**
   * Attach the composed turn proof. Idempotent-at-first-writer: returns
   * `false` if one was already attached (a receipt never silently swaps
   * attestations) and throws [`WrongTurnProofError`] if the proof names a
   * different turn (a mis-bound attachment is refused, not stored).
   */
  attachProof(proof: TurnProof): boolean {
    const expected = hexDecodeExact(this.turnHash, 32);
    if (!bytesEqual(proof.turnHash, expected)) {
      throw new WrongTurnProofError(this.turnHash, proof.turnHashHex);
    }
    if (this.attached !== undefined) return false;
    this.attached = proof;
    return true;
  }

  /**
   * Lazily attach: return the attached proof, producing it with `f` if none
   * is attached yet (mirrors `Receipt::proof_or_attach`). A produced proof
   * bound to the wrong turn is refused, never stored.
   */
  async proofOrAttach(f: () => Promise<TurnProof>): Promise<TurnProof> {
    if (this.attached === undefined) {
      const produced = await f();
      this.attachProof(produced); // throws on wrong turn; false on race is fine
    }
    const got = this.attached;
    if (got === undefined) throw new Error("unreachable: attached above");
    return got;
  }
}
