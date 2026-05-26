// ---------------------------------------------------------------------------
// Effects — All 18 effect types produced by turns
// ---------------------------------------------------------------------------

/**
 * The full union of effects that a turn can produce.
 * Each effect represents an atomic state change in the ledger.
 */
export type Effect =
  | { type: "transfer"; from: string; to: string; amount: number }
  | { type: "setField"; cell: string; field: number; value: number }
  | { type: "createCell"; owner: string; balance: number; factoryVk?: string }
  | { type: "destroyCell"; cell: string }
  | { type: "exportSturdyRef"; cell: string; permissions?: string }
  | { type: "enlivenRef"; swiss: string; federationId: string }
  | { type: "dropRef"; cell: string; holder: string }
  | { type: "validateHandoff"; certHash: string; recipientPk: string }
  | { type: "mountDirectory"; path: string; sturdyRef: string; kind: string }
  | { type: "unmountDirectory"; path: string }
  | { type: "storeData"; hash: string; size: number }
  | { type: "deleteData"; hash: string }
  | { type: "spliceData"; oldHash: string; newHash: string; offset: number }
  | { type: "amendRoutes"; commitment: string; description: string }
  | { type: "mintToken"; service: string; rootKeyHash: string }
  | { type: "attenuateToken"; parentId: string; restrictions: string }
  | { type: "delegateToken"; tokenId: string; recipientPk: string }
  | { type: "revokeToken"; tokenId: string }
  // Queue operations
  | { type: "queueAllocate"; capacity: number; programVk?: string }
  | { type: "queueEnqueue"; queue: string; messageHash: string; deposit: number }
  | { type: "queueDequeue"; queue: string }
  | { type: "queueResize"; queue: string; newCapacity: number }
  | { type: "queueAtomicTx"; operations: QueueTxOp[] }
  | { type: "queuePipelineStep"; pipelineId: string; source: string; sinks: string[] };

/**
 * An operation within an atomic queue transaction.
 */
export type QueueTxOp =
  | { type: "enqueue"; queue: string; messageHash: string; deposit: number }
  | { type: "dequeue"; queue: string };

/**
 * Status of a queue cell.
 */
export interface QueueStatus {
  /** Queue cell ID. */
  queueId: string;
  /** Current number of messages in the queue. */
  occupancy: number;
  /** Maximum capacity. */
  capacity: number;
  /** Owner cell ID. */
  owner: string;
  /** Optional program VK hash (for programmable queues). */
  programVk?: string;
}

/**
 * A turn receipt effect with full metadata.
 * This is the enriched form returned in turn receipts.
 */
export interface EffectReceipt {
  /** The effect that was applied. */
  effect: Effect;
  /** Index of this effect within the turn. */
  index: number;
  /** Whether the effect was successfully applied. */
  success: boolean;
  /** Error message if the effect failed. */
  error?: string;
}
