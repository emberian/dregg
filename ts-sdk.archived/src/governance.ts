// ---------------------------------------------------------------------------
// Governance Types — Federation constitution and proposals
// ---------------------------------------------------------------------------

/** The federation's constitution: participants, voting rules, routing. */
export interface Constitution {
  /** Public keys (hex) of federation participants. */
  participants: string[];
  /** Number of votes required to pass a proposal. */
  threshold: number;
  /** Number of timeout waves before a proposal expires. */
  timeoutWaves: number;
  /** Constitution version number. */
  version: number;
  /** BLAKE3 commitment of the current route table. */
  routesCommitment?: string;
}

/** A single vote on a proposal. */
export interface Vote {
  /** Public key (hex) of the voter. */
  voter: string;
  /** Whether this vote approves the proposal. */
  approve: boolean;
  /** Signature over the vote payload. */
  signature: string;
}

/** The kind of governance proposal. */
export type ProposalKind =
  | { type: "join"; nodeKey: string }
  | { type: "leave"; nodeKey: string }
  | { type: "amend-routes"; commitment: string; description: string }
  | { type: "amend-threshold"; newThreshold: number };

/** A governance proposal. */
export interface Proposal {
  /** Unique proposal identifier. */
  id: string;
  /** What this proposal is for. */
  kind: ProposalKind;
  /** Current status. */
  status: "pending" | "passed" | "rejected";
  /** Votes cast so far. */
  votes: Vote[];
}

/** Federation status summary. */
export interface FederationStatus {
  /** Current constitution. */
  constitution: Constitution;
  /** Current block height. */
  height: number;
  /** Number of connected peers. */
  peerCount: number;
  /** Federation operating mode. */
  mode: string;
  /** Active proposals. */
  proposals: Proposal[];
}
