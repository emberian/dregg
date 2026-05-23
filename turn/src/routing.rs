//! Routing directives emitted by three-party introductions.
//!
//! When a turn executes an `Effect::Introduce`, the executor emits a
//! `RoutingDirective` telling the network layer that a new communication
//! path is now valid. The node uses these to populate its routing table,
//! enabling direct message delivery between introduced parties.

use pyana_cell::CellId;
use serde::{Deserialize, Serialize};

/// A directive emitted by turn execution telling the network layer
/// that a new communication path is now valid.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RoutingDirective {
    /// Who can now send (the recipient of the introduction).
    pub sender: CellId,
    /// Who they can reach (the target of the introduction).
    pub target: CellId,
    /// The turn that authorized this route (turn hash).
    pub authorizing_turn: [u8; 32],
    /// Expiry (if the capability is time-limited).
    pub expires: Option<u64>,
}

impl RoutingDirective {
    /// Compute a BLAKE3 hash of this directive for inclusion in receipts.
    pub fn hash(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"pyana-routing-directive-v1");
        hasher.update(self.sender.as_bytes());
        hasher.update(self.target.as_bytes());
        hasher.update(&self.authorizing_turn);
        match self.expires {
            Some(t) => {
                hasher.update(&[1u8]);
                hasher.update(&t.to_le_bytes());
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
        *hasher.finalize().as_bytes()
    }
}

/// A record emitted by three-party introductions indicating that a new
/// GC-tracked export was created.
///
/// When `Effect::Introduce` grants `recipient` access to `target`, the target
/// cell's owning federation must track that `recipient` (or its federation) now
/// holds a reference. Without this, introduced capabilities leak forever because
/// no `DropRef` is ever sent for them.
///
/// The node/server layer consumes these records and registers them in the
/// `ExportGcManager`, enabling proper distributed garbage collection.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IntroductionExport {
    /// The cell being introduced (the capability target).
    /// The owning federation should track this as an export.
    pub target: CellId,
    /// The cell receiving access (the introduction recipient).
    /// Maps to a federation for GC tracking purposes.
    pub recipient: CellId,
    /// The turn that authorized this introduction.
    pub authorizing_turn: [u8; 32],
    /// Block height at which the introduced capability expires (if time-limited).
    pub expires: Option<u64>,
}
