// ---------------------------------------------------------------------------
// Routing Types — DFA route table
// ---------------------------------------------------------------------------

/** Where a route dispatches to. */
export type RouteTarget =
  | { kind: "cell"; cellId: string }
  | { kind: "handler"; name: string }
  | { kind: "federation"; id: string }
  | { kind: "drop" };

/** A single route entry in the DFA table. */
export interface RouteEntry {
  /** Pattern string (path prefix or regex). */
  pattern: string;
  /** Where matching requests are dispatched. */
  target: RouteTarget;
  /** Priority (higher = matched first). */
  priority?: number;
}

/** The full route table with its integrity commitment. */
export interface RouteTable {
  /** Ordered list of route entries. */
  routes: RouteEntry[];
  /** BLAKE3 commitment over the serialized route table. */
  commitment: string;
}

/** Result of classifying a path through the DFA. */
export interface ClassifyResult {
  /** The path that was classified. */
  path: string;
  /** The matching route entry (if any). */
  matched?: RouteEntry;
  /** The resolved target. */
  target?: RouteTarget;
}
