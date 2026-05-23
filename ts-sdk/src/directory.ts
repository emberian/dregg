// ---------------------------------------------------------------------------
// Directory / Namespace Types
// ---------------------------------------------------------------------------

/** Kind of service entry in the directory. */
export type ServiceKind =
  | "storage"
  | "compute"
  | "oracle"
  | "factory"
  | "sub-directory"
  | "custom";

/** A single entry in the structured directory. */
export interface DirectoryEntry {
  /** Human-readable name of this entry. */
  name: string;
  /** Sturdy reference URI (pyana://) for the entry. */
  sturdyRef: string;
  /** The kind of service this entry represents. */
  kind: ServiceKind;
  /** CAS version number (for compare-and-swap updates). */
  version: number;
  /** Discovery tags. */
  tags: string[];
  /** Human-readable description. */
  description: string;
  /** Optional expiration timestamp (unix seconds). */
  expiresAt?: number;
}

/** Request to mount a new entry in a directory. */
export interface MountRequest {
  /** Full directory path including name (e.g., "/services/oracle"). */
  path: string;
  /** The kind of service being mounted. */
  kind: ServiceKind;
  /** Sturdy reference URI or service address to mount. */
  sturdyRef: string;
  /** Discovery tags for this entry. */
  tags: string[];
  /** Human-readable description. */
  description: string;
}

/** Result of a mount operation. */
export interface MountResult {
  /** The path that was mounted. */
  path: string;
  /** The version assigned to this entry. */
  version: number;
}

/** Parameters for tag/kind-based discovery across directories. */
export interface DiscoverParams {
  /** Filter by tags (entries must match all tags). */
  tags?: string[];
  /** Filter by service kind. */
  kind?: ServiceKind;
}
