// ---------------------------------------------------------------------------
// CapTP Types — Capability Transport Protocol
// ---------------------------------------------------------------------------

/** A durable, shareable reference to a cell capability (persists across sessions). */
export interface SturdyRef {
  /** The federation hosting the target cell. */
  federationId: string;
  /** The target cell identifier. */
  cellId: string;
  /** The bearer token (swiss number) proving granted access. */
  swiss: string;
}

/** A live (session-bound) reference to a remote cell obtained by enlivening a sturdy ref. */
export interface LiveRef {
  /** The CapTP session this reference is bound to. */
  sessionId: string;
  /** The export index in the remote's export table. */
  exportIdx: number;
  /** The cell this reference points to. */
  cellId: string;
}

/**
 * A handoff certificate for offline capability delegation.
 *
 * The introducer pre-registers a swiss entry at the target and signs a
 * certificate naming the recipient. The certificate can travel out-of-band
 * (QR code, email, BLE).
 */
export interface HandoffCertificate {
  /** Public key (hex) of the introducer who created the handoff. */
  introducer: string;
  /** Cell ID of the target being delegated. */
  target: string;
  /** Public key (hex) of the intended recipient. */
  recipient: string;
  /** Swiss number registered for this handoff. */
  swiss: string;
  /** Ed25519 signature from the introducer over the certificate payload. */
  signature: string;
  /** Optional expiration height (block number). */
  expires?: number;
}

/**
 * A capability reference — either durable (sturdy), session-bound (live),
 * or local (cell on this node).
 */
export type CapabilityRef =
  | { kind: "sturdy"; ref: SturdyRef }
  | { kind: "live"; ref: LiveRef }
  | { kind: "local"; cellId: string };

/** Result of exporting a cell as a sturdy reference. */
export interface ExportResult {
  /** The pyana:// URI string for the exported capability. */
  uri: string;
  /** The sturdy reference details. */
  sturdyRef: SturdyRef;
}

/** Result of enlivening a sturdy reference. */
export interface EnlivenResult {
  /** The live reference to the remote cell. */
  liveRef: LiveRef;
  /** Permissions granted by this reference. */
  permissions: string[];
}

/** Result of creating a handoff certificate. */
export interface HandoffResult {
  /** The handoff certificate. */
  certificate: HandoffCertificate;
}
