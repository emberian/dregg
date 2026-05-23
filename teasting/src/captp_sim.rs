//! Simulated CapTP sessions between federations.
//!
//! Uses in-process message queues instead of TCP, but exercises real
//! `CapSession`, `SwissTable`, and GC logic. This catches logic bugs
//! without requiring actual networking.

use std::collections::VecDeque;

use pyana_captp::{
    CapSession, ExportGcManager, FederationId, ImportGcManager, PyanaUri, SwissTable,
};
use pyana_cell::AuthRequired;
use pyana_types::CellId;
use pyana_wire::message::WireMessage;

/// A simulated bilateral CapTP session between two federations.
///
/// Uses in-process VecDeque channels instead of TCP, but exercises real
/// CapSession, SwissTable, and GC logic.
pub struct SimCapTpSession {
    /// Identity of federation A.
    pub fed_a_id: FederationId,
    /// Identity of federation B.
    pub fed_b_id: FederationId,
    /// A's session state (A's view of the relationship with B).
    pub session_a: CapSession,
    /// B's session state (B's view of the relationship with A).
    pub session_b: CapSession,
    /// A's export GC manager (tracks who holds references to A's cells).
    pub export_gc_a: ExportGcManager,
    /// B's import GC manager (tracks what B holds from remote feds).
    pub import_gc_b: ImportGcManager,
    /// A's swiss table (for sturdy ref export/enliven).
    pub swiss_table_a: SwissTable,
    /// B's swiss table (for sturdy ref export/enliven).
    pub swiss_table_b: SwissTable,
    /// Message queue: messages from A destined for B.
    pub a_to_b: VecDeque<WireMessage>,
    /// Message queue: messages from B destined for A.
    pub b_to_a: VecDeque<WireMessage>,
    /// Whether the session is currently connected.
    pub connected: bool,
    /// Current simulated block height (for expiration checks).
    pub current_height: u64,
}

impl SimCapTpSession {
    /// Establish a new simulated CapTP session between two federations.
    ///
    /// This performs the CapHello handshake by placing CapHello messages in both
    /// directions and marking the session as connected.
    pub fn establish(fed_a_id: FederationId, fed_b_id: FederationId) -> Self {
        let session_a = CapSession::new(fed_b_id.0);
        let session_b = CapSession::new(fed_a_id.0);

        let mut sim = Self {
            fed_a_id,
            fed_b_id,
            session_a,
            session_b,
            export_gc_a: ExportGcManager::new(),
            import_gc_b: ImportGcManager::new(),
            swiss_table_a: SwissTable::new(),
            swiss_table_b: SwissTable::new(),
            a_to_b: VecDeque::new(),
            b_to_a: VecDeque::new(),
            connected: true,
            current_height: 0,
        };

        // Simulate the CapHello exchange
        sim.a_to_b.push_back(WireMessage::CapHello {
            federation_id: fed_a_id.0,
            initial_exports: vec![],
        });
        sim.b_to_a.push_back(WireMessage::CapHello {
            federation_id: fed_b_id.0,
            initial_exports: vec![],
        });

        sim
    }

    /// Send a wire message from A to B.
    ///
    /// Panics if the session is disconnected.
    pub fn send_a_to_b(&mut self, msg: WireMessage) {
        assert!(self.connected, "cannot send on disconnected session");
        self.a_to_b.push_back(msg);
    }

    /// Send a wire message from B to A.
    ///
    /// Panics if the session is disconnected.
    pub fn send_b_to_a(&mut self, msg: WireMessage) {
        assert!(self.connected, "cannot send on disconnected session");
        self.b_to_a.push_back(msg);
    }

    /// Deliver all pending messages in both directions.
    ///
    /// Processes CapTP-level messages (CapHello, CapGoodbye, DropRemoteRef,
    /// EnlivenSturdyRef) against the real session/GC state. Other message
    /// types are consumed from the queue but not automatically processed
    /// (the test must handle them).
    ///
    /// Returns the count of messages delivered in each direction: (a_to_b, b_to_a).
    pub fn deliver_pending(&mut self) -> (usize, usize) {
        let mut a_to_b_count = 0;
        let mut b_to_a_count = 0;

        // Deliver A -> B messages
        while let Some(msg) = self.a_to_b.pop_front() {
            a_to_b_count += 1;
            self.process_at_b(&msg);
        }

        // Deliver B -> A messages
        while let Some(msg) = self.b_to_a.pop_front() {
            b_to_a_count += 1;
            self.process_at_a(&msg);
        }

        (a_to_b_count, b_to_a_count)
    }

    /// Simulate a network disconnection.
    ///
    /// Marks the session as disconnected, sends CapGoodbye in both directions,
    /// and marks all imports as disconnected. Pending messages in the queues
    /// are dropped (simulating TCP reset).
    pub fn disconnect(&mut self) {
        self.connected = false;
        self.a_to_b.clear();
        self.b_to_a.clear();

        // Mark all imports in both sessions as disconnected
        let import_cells_a: Vec<CellId> = self.session_a.imports.keys().copied().collect();
        for cell_id in import_cells_a {
            self.session_a.disconnect_import(&cell_id);
        }

        let import_cells_b: Vec<CellId> = self.session_b.imports.keys().copied().collect();
        for cell_id in import_cells_b {
            self.session_b.disconnect_import(&cell_id);
        }
    }

    /// Export a cell from federation A, making it available to B via a sturdy ref.
    ///
    /// Returns the generated `PyanaUri` that B can use to enliven.
    pub fn export_from_a(&mut self, cell_id: CellId, permissions: AuthRequired) -> PyanaUri {
        // Register in A's swiss table
        let swiss =
            self.swiss_table_a
                .export(cell_id, permissions.clone(), self.current_height, None);

        // Register the export in A's session state
        self.session_a.export(cell_id, permissions);

        // Record in A's GC that B will hold a reference
        self.export_gc_a
            .record_export(cell_id, self.fed_b_id, self.current_height);

        // Build the URI
        PyanaUri {
            federation_id: self.fed_a_id.0,
            cell_id: cell_id.0,
            swiss,
        }
    }

    /// Export a cell from federation B, making it available to A via a sturdy ref.
    ///
    /// Returns the generated `PyanaUri` that A can use to enliven.
    pub fn export_from_b(&mut self, cell_id: CellId, permissions: AuthRequired) -> PyanaUri {
        let swiss =
            self.swiss_table_b
                .export(cell_id, permissions.clone(), self.current_height, None);
        self.session_b.export(cell_id, permissions);

        PyanaUri {
            federation_id: self.fed_b_id.0,
            cell_id: cell_id.0,
            swiss,
        }
    }

    /// Enliven a sturdy ref at federation A (B is presenting a URI that A exported).
    ///
    /// Returns the resolved `CellId` on success, or an error string on failure.
    pub fn enliven_at_a(&mut self, uri: &PyanaUri) -> Result<CellId, String> {
        // Validate the URI targets federation A
        if uri.federation_id != self.fed_a_id.0 {
            return Err("URI does not target federation A".to_string());
        }

        // Look up in A's swiss table
        let entry = self
            .swiss_table_a
            .enliven(&uri.swiss, self.current_height)
            .map_err(|e| e.to_string())?;

        // Record B's import
        self.session_b
            .import(entry.cell_id, entry.permissions.clone());
        self.import_gc_b.record_import(self.fed_a_id, entry.cell_id);

        Ok(entry.cell_id)
    }

    /// Enliven a sturdy ref at federation B (A is presenting a URI that B exported).
    ///
    /// Returns the resolved `CellId` on success, or an error string on failure.
    pub fn enliven_at_b(&mut self, uri: &PyanaUri) -> Result<CellId, String> {
        if uri.federation_id != self.fed_b_id.0 {
            return Err("URI does not target federation B".to_string());
        }

        let entry = self
            .swiss_table_b
            .enliven(&uri.swiss, self.current_height)
            .map_err(|e| e.to_string())?;

        self.session_a
            .import(entry.cell_id, entry.permissions.clone());

        Ok(entry.cell_id)
    }

    /// Advance the simulated block height.
    pub fn advance_height(&mut self, blocks: u64) {
        self.current_height += blocks;
    }

    /// Check whether the session is active (either side has live imports/exports).
    pub fn is_active(&self) -> bool {
        self.session_a.is_active() || self.session_b.is_active()
    }

    /// Process a message received at B (sent by A).
    fn process_at_b(&mut self, msg: &WireMessage) {
        match msg {
            WireMessage::CapGoodbye { .. } => {
                self.connected = false;
                let cells: Vec<CellId> = self.session_b.imports.keys().copied().collect();
                for cell_id in cells {
                    self.session_b.disconnect_import(&cell_id);
                }
            }
            WireMessage::DropRemoteRef {
                from_federation,
                cell_id,
                session_epoch: _,
            } => {
                let fed_id = FederationId(*from_federation);
                let cell = CellId(*cell_id);
                self.import_gc_b.local_ref_dropped(fed_id, cell);
                self.session_b.disconnect_import(&cell);
            }
            _ => {
                // Other messages are left for the test to inspect/handle
            }
        }
    }

    /// Process a message received at A (sent by B).
    fn process_at_a(&mut self, msg: &WireMessage) {
        match msg {
            WireMessage::CapGoodbye { .. } => {
                self.connected = false;
                let cells: Vec<CellId> = self.session_a.imports.keys().copied().collect();
                for cell_id in cells {
                    self.session_a.disconnect_import(&cell_id);
                }
            }
            WireMessage::DropRemoteRef {
                from_federation,
                cell_id,
                session_epoch: _,
            } => {
                let fed_id = FederationId(*from_federation);
                let cell = CellId(*cell_id);
                self.export_gc_a.process_drop(cell, fed_id);
                self.session_a.release_export(&cell);
            }
            _ => {
                // Other messages are left for the test to inspect/handle
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fed_a_id() -> FederationId {
        FederationId([0xAA; 32])
    }

    fn fed_b_id() -> FederationId {
        FederationId([0xBB; 32])
    }

    fn test_cell(n: u8) -> CellId {
        CellId([n; 32])
    }

    #[test]
    fn establish_creates_connected_session() {
        let session = SimCapTpSession::establish(fed_a_id(), fed_b_id());
        assert!(session.connected);
        // Both queues have the initial CapHello
        assert_eq!(session.a_to_b.len(), 1);
        assert_eq!(session.b_to_a.len(), 1);
    }

    #[test]
    fn export_and_enliven_roundtrip() {
        let mut session = SimCapTpSession::establish(fed_a_id(), fed_b_id());
        session.deliver_pending();

        let cell = test_cell(0x11);
        let uri = session.export_from_a(cell, AuthRequired::Signature);

        // B enlivens the URI
        let resolved = session.enliven_at_a(&uri).unwrap();
        assert_eq!(resolved, cell);

        // B now has an import
        assert!(session.session_b.imports.contains_key(&cell));
        assert!(session.is_active());
    }

    #[test]
    fn enliven_wrong_federation_fails() {
        let mut session = SimCapTpSession::establish(fed_a_id(), fed_b_id());
        session.deliver_pending();

        let cell = test_cell(0x22);
        let uri = session.export_from_a(cell, AuthRequired::Signature);

        // Try to enliven at B (but URI targets A)
        let result = session.enliven_at_b(&uri);
        assert!(result.is_err());
    }

    #[test]
    fn disconnect_marks_imports_dead() {
        let mut session = SimCapTpSession::establish(fed_a_id(), fed_b_id());
        session.deliver_pending();

        let cell = test_cell(0x33);
        let uri = session.export_from_a(cell, AuthRequired::None);
        session.enliven_at_a(&uri).unwrap();

        // Verify B has a live import
        assert!(session.session_b.imports[&cell].live);

        session.disconnect();

        assert!(!session.connected);
        assert!(!session.session_b.imports[&cell].live);
    }

    #[test]
    fn send_after_disconnect_panics() {
        let mut session = SimCapTpSession::establish(fed_a_id(), fed_b_id());
        session.disconnect();

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            session.send_a_to_b(WireMessage::Ping {
                seq: 1,
                timestamp: 0,
            });
        }));
        assert!(result.is_err());
    }

    #[test]
    fn gc_drop_releases_export() {
        let mut session = SimCapTpSession::establish(fed_a_id(), fed_b_id());
        session.deliver_pending();

        let cell = test_cell(0x44);
        let _uri = session.export_from_a(cell, AuthRequired::None);

        // B sends a DropRemoteRef to A
        session.send_b_to_a(WireMessage::DropRemoteRef {
            from_federation: fed_b_id().0,
            cell_id: cell.0,
            session_epoch: 0,
        });
        session.deliver_pending();

        // A's export should have been released
        assert!(!session.session_a.exports.contains_key(&cell));
    }
}
