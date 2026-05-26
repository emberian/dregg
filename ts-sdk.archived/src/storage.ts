// ---------------------------------------------------------------------------
// Storage Types — Content-addressed file store
// ---------------------------------------------------------------------------

/** Quota usage for a storage allocation. */
export interface StorageQuota {
  /** Total computrons allocated to storage. */
  totalAllocated: number;
  /** Total computrons consumed so far. */
  totalConsumed: number;
  /** Total bytes currently stored. */
  bytesStored: number;
  /** Maximum bytes allowed (if quota-limited). */
  maxBytes?: number;
}

/** Result of a write (upload) operation. */
export interface WriteResult {
  /** Content hash of the stored object (hex). */
  hash: string;
  /** Size of the stored object in bytes. */
  size: number;
}

/** Result of an atomic splice operation. */
export interface SpliceResult {
  /** Content hash of the object before splice. */
  oldHash: string;
  /** Content hash of the object after splice. */
  newHash: string;
}

/** Result of a delete operation. */
export interface DeleteResult {
  /** Content hash of the deleted object. */
  hash: string;
  /** Computrons refunded by the deletion. */
  refund: number;
}
