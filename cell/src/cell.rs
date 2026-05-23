use serde::{Deserialize, Serialize};

use crate::capability::CapabilitySet;
use crate::delegation::DelegatedRef;
use crate::id::CellId;
use crate::permissions::Permissions;
use crate::program::CellProgram;
use crate::state::CellState;

/// Whether a cell's full state is stored by the federation or only a commitment.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CellMode {
    /// Federation stores full cell state (current behavior).
    Hosted,
    /// Federation stores only a 32-byte state commitment.
    /// The agent must provide cell state in each turn.
    Sovereign,
}

impl Default for CellMode {
    fn default() -> Self {
        CellMode::Hosted
    }
}

/// A verification key associated with a cell's proof circuit.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerificationKey {
    /// Hash of the verification key for cheap comparison.
    pub hash: [u8; 32],
    /// Serialized verification key data (opaque blob).
    pub data: Vec<u8>,
}

impl VerificationKey {
    /// Create a new verification key from raw data, computing its BLAKE3 hash.
    pub fn new(data: Vec<u8>) -> Self {
        let hash = *blake3::hash(&data).as_bytes();
        VerificationKey { hash, data }
    }

    /// Create a verification key with a pre-computed hash (e.g., from deserialization).
    pub fn from_parts(hash: [u8; 32], data: Vec<u8>) -> Self {
        VerificationKey { hash, data }
    }
}

/// A Cell is an isolated agent execution context.
/// This is the agent-model analog of a Mina zkApp account.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Cell {
    /// Content-addressed identity: BLAKE3(public_key || token_id).
    pub id: CellId,
    /// The cell's public key (Ed25519).
    pub public_key: [u8; 32],
    /// Mutable state: 8 fields + nonce + balance.
    pub state: CellState,
    /// Authorization requirements for each action type.
    pub permissions: Permissions,
    /// Optional verification key for ZK proof validation.
    pub verification_key: Option<VerificationKey>,
    /// Optional parent/supervisor cell. Planned for delegation chain walking
    /// (child inherits parent's capabilities). Not yet enforced by the executor.
    pub delegate: Option<CellId>,
    /// Rich delegation snapshot: point-in-time copy of the parent's c-list.
    /// Used for snapshot+refresh E-style delegation. The child acts using this
    /// snapshot; acceptors check freshness via `max_staleness`.
    pub delegation: Option<DelegatedRef>,
    /// Which token domain this cell belongs to.
    pub token_id: [u8; 32],
    /// The c-list: what other cells this cell can reference.
    pub capabilities: CapabilitySet,
    /// The cell's program: defines valid state transitions.
    /// If `CellProgram::None`, any authorized state change is valid (backward compat).
    pub program: CellProgram,
    /// Whether this cell is hosted (federation stores full state) or sovereign
    /// (federation stores only a 32-byte commitment). Defaults to Hosted for
    /// backward compatibility with existing serialized cells.
    #[serde(default)]
    pub mode: CellMode,
}

impl Cell {
    /// Create a new cell with default permissions and the given public key and token domain.
    pub fn new(public_key: [u8; 32], token_id: [u8; 32]) -> Self {
        let id = CellId::derive_raw(&public_key, &token_id);
        Cell {
            id,
            public_key,
            state: CellState::default(),
            permissions: Permissions::default(),
            verification_key: None,
            delegate: None,
            delegation: None,
            token_id,
            capabilities: CapabilitySet::new(),
            program: CellProgram::None,
            mode: CellMode::Hosted,
        }
    }

    /// Create a new cell with a specific initial balance.
    pub fn with_balance(public_key: [u8; 32], token_id: [u8; 32], balance: u64) -> Self {
        let id = CellId::derive_raw(&public_key, &token_id);
        Cell {
            id,
            public_key,
            state: CellState::new(balance),
            permissions: Permissions::default(),
            verification_key: None,
            delegate: None,
            delegation: None,
            token_id,
            capabilities: CapabilitySet::new(),
            program: CellProgram::None,
            mode: CellMode::Hosted,
        }
    }

    /// Compute the BLAKE3 commitment to this cell's current state.
    ///
    /// This is the 32-byte value stored by the federation for sovereign cells.
    /// It commits to the cell's identity, nonce, balance, fields, capabilities,
    /// and permissions — everything needed to verify a state transition.
    pub fn state_commitment(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-cell-state-v1");
        hasher.update(&self.id.0);
        hasher.update(&self.public_key);
        hasher.update(&self.token_id);
        hasher.update(&self.state.nonce.to_le_bytes());
        hasher.update(&self.state.balance.to_le_bytes());
        for field in &self.state.fields {
            hasher.update(field);
        }
        // Include capabilities count and content.
        let cap_count = self.capabilities.len() as u64;
        hasher.update(&cap_count.to_le_bytes());
        for cap in self.capabilities.iter() {
            hasher.update(cap.target.as_bytes());
            hasher.update(&cap.slot.to_le_bytes());
        }
        // Include permissions.
        let perm_fields = [
            &self.permissions.send,
            &self.permissions.receive,
            &self.permissions.set_state,
            &self.permissions.set_permissions,
            &self.permissions.set_verification_key,
            &self.permissions.increment_nonce,
            &self.permissions.delegate,
            &self.permissions.access,
        ];
        for perm in perm_fields {
            let perm_byte = match perm {
                crate::permissions::AuthRequired::None => 0u8,
                crate::permissions::AuthRequired::Signature => 1u8,
                crate::permissions::AuthRequired::Proof => 2u8,
                crate::permissions::AuthRequired::Either => 3u8,
                crate::permissions::AuthRequired::Impossible => 4u8,
            };
            hasher.update(&[perm_byte]);
        }
        // Include verification key hash if present.
        match &self.verification_key {
            Some(vk) => {
                hasher.update(&[1u8]);
                hasher.update(&vk.hash);
            }
            None => {
                hasher.update(&[0u8]);
            }
        }
        *hasher.finalize().as_bytes()
    }

    /// Create a child cell delegated to this cell.
    pub fn spawn_child(&self, child_public_key: [u8; 32], child_token_id: [u8; 32]) -> Cell {
        let id = CellId::derive_raw(&child_public_key, &child_token_id);
        Cell {
            id,
            public_key: child_public_key,
            state: CellState::default(),
            permissions: Permissions::default(),
            verification_key: None,
            delegate: Some(self.id),
            delegation: None,
            token_id: child_token_id,
            capabilities: CapabilitySet::new(),
            program: CellProgram::None,
            mode: CellMode::Hosted,
        }
    }

    /// Create a child cell with snapshot+refresh delegation from this cell.
    ///
    /// The child inherits a point-in-time snapshot of the parent's c-list.
    /// The snapshot epoch and refresh timestamp are set by the caller.
    pub fn spawn_child_with_delegation(
        &self,
        child_public_key: [u8; 32],
        child_token_id: [u8; 32],
        delegation_epoch: u64,
        refreshed_at: u64,
        max_staleness: u64,
    ) -> Cell {
        let id = CellId::derive_raw(&child_public_key, &child_token_id);
        let snapshot: Vec<crate::capability::CapabilityRef> =
            self.capabilities.iter().cloned().collect();
        Cell {
            id,
            public_key: child_public_key,
            state: CellState::default(),
            permissions: Permissions::default(),
            verification_key: None,
            delegate: Some(self.id),
            delegation: Some({
                let clist_bytes = postcard::to_allocvec(&snapshot).unwrap_or_default();
                let clist_commitment = DelegatedRef::compute_clist_commitment(&clist_bytes);
                DelegatedRef::new(
                    self.id,
                    id,
                    snapshot,
                    delegation_epoch,
                    refreshed_at,
                    max_staleness,
                    clist_commitment,
                    [0u8; 64], // Placeholder signature — spawn_child is a privileged internal op.
                )
            }),
            token_id: child_token_id,
            capabilities: CapabilitySet::new(),
            program: CellProgram::None,
            mode: CellMode::Hosted,
        }
    }
}
