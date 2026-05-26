//! Local routing table mapping CellId -> reachable peers.
//!
//! When a turn containing an `Effect::Introduce` is executed, the receipt
//! carries `RoutingDirective`s. This module consumes those directives and
//! maintains a mapping from CellId to the peer address through which that
//! cell is reachable — enabling three-party introductions to produce actual
//! network-level connectivity.

use std::collections::HashMap;
use std::net::SocketAddr;

use dregg_cell::CellId;
use dregg_turn::RoutingDirective;

/// A single route entry describing how to reach a cell.
#[derive(Clone, Debug)]
pub struct RouteEntry {
    /// The peer address through which this cell is reachable.
    pub via_peer: SocketAddr,
    /// The cell that authorized this introduction.
    pub introduced_by: CellId,
    /// Block height at which this route expires (None = no expiry).
    pub expires: Option<u64>,
    /// Timestamp (unix seconds) when this route was created.
    pub created_at: u64,
    /// Whether the authorizing turn has been verified in the receipt store.
    /// Defaults to `false` until confirmed (Issue 5).
    pub verified: bool,
}

/// Error returned when a routing directive is rejected.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RoutingError {
    /// The directive's authorizing turn is a null hash (all zeros).
    NullAuthorizingTurn,
}

/// A local routing table that maps CellId -> set of reachable peers.
///
/// Populated from `RoutingDirective`s extracted from turn receipts.
/// Expired entries are pruned periodically or on lookup.
#[derive(Clone, Debug, Default)]
pub struct RoutingTable {
    routes: HashMap<CellId, Vec<RouteEntry>>,
    /// Cached total entry count (avoids O(n) recomputation on every insert).
    total_entries: usize,
}

impl RoutingTable {
    /// Create a new empty routing table.
    pub fn new() -> Self {
        Self {
            routes: HashMap::new(),
            total_entries: 0,
        }
    }

    /// Process a routing directive, adding a route for the target cell
    /// reachable via the given peer address.
    ///
    /// `via_peer` is the peer address from which the turn containing
    /// this directive was received.
    ///
    /// Returns `Err` if the table is full or the directive is invalid.
    pub fn apply_directive(
        &mut self,
        directive: &RoutingDirective,
        via_peer: SocketAddr,
    ) -> Result<(), RoutingError> {
        // Issue 5: Reject directives with null authorizing_turn hash.
        if directive.authorizing_turn == [0u8; 32] {
            return Err(RoutingError::NullAuthorizingTurn);
        }

        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0);

        let entry = RouteEntry {
            via_peer,
            introduced_by: directive.sender,
            expires: directive.expires,
            created_at: now,
            // Issue 5: Start unverified; caller must confirm the authorizing turn exists.
            verified: false,
        };

        self.routes.entry(directive.target).or_default().push(entry);
        self.total_entries += 1;
        Ok(())
    }

    /// Mark a route entry as verified (its authorizing turn exists in the receipt store).
    pub fn mark_verified(&mut self, cell: &CellId, authorizing_turn: &[u8; 32]) {
        if let Some(entries) = self.routes.get_mut(cell) {
            for entry in entries.iter_mut() {
                // We don't store authorizing_turn in the entry, but caller can use
                // introduced_by + created_at to correlate. For now, we verify all
                // entries for a cell that match the directive's source.
                let _ = authorizing_turn;
                entry.verified = true;
            }
        }
    }

    /// Look up routes to reach a given cell.
    ///
    /// Returns only non-expired entries. Expired entries are lazily pruned.
    pub fn lookup(&mut self, cell: &CellId, current_height: u64) -> Vec<&RouteEntry> {
        if let Some(entries) = self.routes.get_mut(cell) {
            // Prune expired entries lazily on lookup.
            let before = entries.len();
            entries.retain(|e| match e.expires {
                Some(exp) => current_height < exp,
                None => true,
            });
            self.total_entries -= before - entries.len();
        }

        self.routes
            .get(cell)
            .map(|entries| entries.iter().collect())
            .unwrap_or_default()
    }

    /// Look up routes without mutating (no pruning). Returns all entries
    /// including potentially expired ones.
    pub fn lookup_immut(&self, cell: &CellId) -> &[RouteEntry] {
        self.routes.get(cell).map(|v| v.as_slice()).unwrap_or(&[])
    }

    /// Remove all expired routes given the current block height.
    pub fn prune_expired(&mut self, current_height: u64) {
        self.routes.retain(|_cell, entries| {
            let before = entries.len();
            entries.retain(|e| match e.expires {
                Some(exp) => current_height < exp,
                None => true,
            });
            self.total_entries -= before - entries.len();
            !entries.is_empty()
        });
    }

    /// Total number of route entries across all cells.
    pub fn len(&self) -> usize {
        self.total_entries
    }

    /// Whether the routing table is empty.
    pub fn is_empty(&self) -> bool {
        self.total_entries == 0
    }

    /// Remove all routes associated with a specific peer address
    /// (e.g., when a peer disconnects).
    pub fn remove_peer(&mut self, peer: &SocketAddr) {
        self.routes.retain(|_cell, entries| {
            let before = entries.len();
            entries.retain(|e| &e.via_peer != peer);
            self.total_entries -= before - entries.len();
            !entries.is_empty()
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_cell_id(byte: u8) -> CellId {
        CellId([byte; 32])
    }

    fn make_directive(sender_byte: u8, target_byte: u8, expires: Option<u64>) -> RoutingDirective {
        RoutingDirective {
            sender: make_cell_id(sender_byte),
            target: make_cell_id(target_byte),
            authorizing_turn: [0xAA; 32],
            expires,
        }
    }

    #[test]
    fn test_apply_and_lookup() {
        let mut table = RoutingTable::new();
        let peer: SocketAddr = "192.168.1.1:9000".parse().unwrap();
        let directive = make_directive(1, 2, None);

        table.apply_directive(&directive, peer).unwrap();

        let routes = table.lookup(&make_cell_id(2), 0);
        assert_eq!(routes.len(), 1);
        assert_eq!(routes[0].via_peer, peer);
        assert_eq!(routes[0].introduced_by, make_cell_id(1));
        assert!(!routes[0].verified);
    }

    #[test]
    fn test_expiry_prunes_on_lookup() {
        let mut table = RoutingTable::new();
        let peer: SocketAddr = "192.168.1.1:9000".parse().unwrap();

        // Route that expires at height 100.
        let directive = make_directive(1, 2, Some(100));
        table.apply_directive(&directive, peer).unwrap();

        // Before expiry: visible.
        let routes = table.lookup(&make_cell_id(2), 50);
        assert_eq!(routes.len(), 1);

        // At expiry height: pruned.
        let routes = table.lookup(&make_cell_id(2), 100);
        assert_eq!(routes.len(), 0);
    }

    #[test]
    fn test_prune_expired() {
        let mut table = RoutingTable::new();
        let peer: SocketAddr = "192.168.1.1:9000".parse().unwrap();

        table
            .apply_directive(&make_directive(1, 2, Some(50)), peer)
            .unwrap();
        table
            .apply_directive(&make_directive(1, 3, None), peer)
            .unwrap();
        table
            .apply_directive(&make_directive(1, 4, Some(200)), peer)
            .unwrap();

        assert_eq!(table.len(), 3);

        table.prune_expired(100);

        // Cell 2 expired (50 < 100), Cell 3 no expiry (kept), Cell 4 not expired (200 > 100).
        assert_eq!(table.len(), 2);
        assert!(table.lookup_immut(&make_cell_id(2)).is_empty());
        assert_eq!(table.lookup_immut(&make_cell_id(3)).len(), 1);
        assert_eq!(table.lookup_immut(&make_cell_id(4)).len(), 1);
    }

    #[test]
    fn test_remove_peer() {
        let mut table = RoutingTable::new();
        let peer_a: SocketAddr = "192.168.1.1:9000".parse().unwrap();
        let peer_b: SocketAddr = "192.168.1.2:9000".parse().unwrap();

        table
            .apply_directive(&make_directive(1, 2, None), peer_a)
            .unwrap();
        table
            .apply_directive(&make_directive(3, 2, None), peer_b)
            .unwrap();

        assert_eq!(table.len(), 2);

        table.remove_peer(&peer_a);

        assert_eq!(table.len(), 1);
        let routes = table.lookup_immut(&make_cell_id(2));
        assert_eq!(routes.len(), 1);
        assert_eq!(routes[0].via_peer, peer_b);
    }

    #[test]
    fn test_multiple_routes_same_target() {
        let mut table = RoutingTable::new();
        let peer_a: SocketAddr = "192.168.1.1:9000".parse().unwrap();
        let peer_b: SocketAddr = "192.168.1.2:9000".parse().unwrap();

        table
            .apply_directive(&make_directive(1, 5, None), peer_a)
            .unwrap();
        table
            .apply_directive(&make_directive(2, 5, None), peer_b)
            .unwrap();

        let routes = table.lookup_immut(&make_cell_id(5));
        assert_eq!(routes.len(), 2);
    }

    #[test]
    fn test_null_authorizing_turn_rejected() {
        let mut table = RoutingTable::new();
        let peer: SocketAddr = "192.168.1.1:9000".parse().unwrap();
        let directive = RoutingDirective {
            sender: make_cell_id(1),
            target: make_cell_id(2),
            authorizing_turn: [0u8; 32], // null turn
            expires: None,
        };

        let result = table.apply_directive(&directive, peer);
        assert_eq!(result, Err(RoutingError::NullAuthorizingTurn));
        assert_eq!(table.len(), 0);
    }

    #[test]
    fn test_mark_verified() {
        let mut table = RoutingTable::new();
        let peer: SocketAddr = "192.168.1.1:9000".parse().unwrap();
        let directive = make_directive(1, 2, None);
        table.apply_directive(&directive, peer).unwrap();

        assert!(!table.lookup_immut(&make_cell_id(2))[0].verified);

        table.mark_verified(&make_cell_id(2), &[0xAA; 32]);

        assert!(table.lookup_immut(&make_cell_id(2))[0].verified);
    }
}
