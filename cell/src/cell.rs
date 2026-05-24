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
        CellMode::Sovereign
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
///
/// Audit P0-1 sealing: the identity-bearing fields `id`, `public_key`, and
/// `token_id` are `pub(crate)` rather than `pub` — external code must use the
/// accessors [`Cell::id`], [`Cell::public_key`], [`Cell::token_id`] for reads
/// and go through `Ledger::update_with` for mutations. This preserves the
/// content-address invariant `id == derive_raw(public_key, token_id)` (P2-3).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Cell {
    /// Content-addressed identity: BLAKE3(public_key || token_id).
    ///
    /// `pub(crate)`: external code must read via `Cell::id()` and cannot mutate
    /// without going through `Ledger::update_with` (which re-checks integrity).
    pub(crate) id: CellId,
    /// The cell's public key (Ed25519). See `id` for sealing rationale.
    pub(crate) public_key: [u8; 32],
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
    /// Which token domain this cell belongs to. See `id` for sealing rationale.
    pub(crate) token_id: [u8; 32],
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

/// Configuration for creating a new cell.
///
/// Allows choosing mode, initial balance, permissions, and program at creation time.
#[derive(Clone, Debug)]
pub struct CellConfig {
    /// Whether the cell is hosted or sovereign.
    pub mode: CellMode,
    /// Initial balance (computrons).
    pub balance: u64,
    /// Permissions (defaults to Permissions::default() if None).
    pub permissions: Option<Permissions>,
    /// Cell program (defaults to CellProgram::None if None).
    pub program: Option<CellProgram>,
    /// Verification key (optional).
    pub verification_key: Option<VerificationKey>,
}

impl Default for CellConfig {
    fn default() -> Self {
        CellConfig {
            mode: CellMode::Sovereign,
            balance: 0,
            permissions: None,
            program: None,
            verification_key: None,
        }
    }
}

impl CellConfig {
    /// Create a config for a hosted cell.
    pub fn hosted() -> Self {
        CellConfig {
            mode: CellMode::Hosted,
            ..Default::default()
        }
    }

    /// Create a config for a sovereign cell.
    pub fn sovereign() -> Self {
        CellConfig {
            mode: CellMode::Sovereign,
            ..Default::default()
        }
    }

    /// Set the initial balance.
    pub fn with_balance(mut self, balance: u64) -> Self {
        self.balance = balance;
        self
    }

    /// Set the permissions.
    pub fn with_permissions(mut self, permissions: Permissions) -> Self {
        self.permissions = Some(permissions);
        self
    }

    /// Set the cell program.
    pub fn with_program(mut self, program: CellProgram) -> Self {
        self.program = Some(program);
        self
    }

    /// Set the verification key.
    pub fn with_verification_key(mut self, vk: VerificationKey) -> Self {
        self.verification_key = Some(vk);
        self
    }
}

impl Cell {
    /// Create a new cell with default permissions and the given public key and token domain.
    ///
    /// Defaults to `CellMode::Sovereign` (Phase 4). Use `Cell::new_hosted()` for
    /// explicit hosted creation.
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
            mode: CellMode::Sovereign,
        }
    }

    /// Create a new hosted cell explicitly.
    ///
    /// This is the pre-Phase-4 behavior where the federation stores full cell state.
    pub fn new_hosted(public_key: [u8; 32], token_id: [u8; 32]) -> Self {
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
    ///
    /// Remains hosted for backward compatibility with existing tests.
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

    /// Create a new cell from a configuration.
    pub fn from_config(public_key: [u8; 32], token_id: [u8; 32], config: CellConfig) -> Self {
        let id = CellId::derive_raw(&public_key, &token_id);
        Cell {
            id,
            public_key,
            state: CellState::new(config.balance),
            permissions: config.permissions.unwrap_or_default(),
            verification_key: config.verification_key,
            delegate: None,
            delegation: None,
            token_id,
            capabilities: CapabilitySet::new(),
            program: config.program.unwrap_or(CellProgram::None),
            mode: config.mode,
        }
    }

    /// Read accessor for the content-addressed cell ID. Sealed for P0-1.
    ///
    /// External code cannot mutate this field directly — the following must
    /// not compile:
    /// ```compile_fail
    /// # use pyana_cell::Cell;
    /// let mut cell = Cell::new([0u8; 32], [0u8; 32]);
    /// cell.id = pyana_cell::CellId::derive_raw(&[1u8; 32], &[2u8; 32]);
    /// ```
    #[inline]
    pub fn id(&self) -> CellId {
        self.id
    }

    /// Read accessor for the cell's Ed25519 public key. Sealed for P0-1.
    ///
    /// External code cannot mutate this field directly:
    /// ```compile_fail
    /// # use pyana_cell::Cell;
    /// let mut cell = Cell::new([0u8; 32], [0u8; 32]);
    /// cell.public_key = [1u8; 32];
    /// ```
    #[inline]
    pub fn public_key(&self) -> &[u8; 32] {
        &self.public_key
    }

    /// Read accessor for the cell's token-domain ID. Sealed for P0-1.
    ///
    /// External code cannot mutate this field directly:
    /// ```compile_fail
    /// # use pyana_cell::Cell;
    /// let mut cell = Cell::new([0u8; 32], [0u8; 32]);
    /// cell.token_id = [1u8; 32];
    /// ```
    #[inline]
    pub fn token_id(&self) -> &[u8; 32] {
        &self.token_id
    }

    /// Compute the canonical commitment to this cell's current state.
    ///
    /// This is a thin wrapper around
    /// [`crate::commitment::compute_canonical_state_commitment`], the single
    /// source of truth for "what bytes commit to this cell." `Ledger::hash_cell`
    /// is also routed through the same function so the sovereign-witness check
    /// (which uses `state_commitment`) and the federation Merkle leaf (which
    /// uses `hash_cell`) agree byte-for-byte. See `cell/src/commitment.rs` for
    /// the full hash shape and the audit context (P0-2).
    pub fn state_commitment(&self) -> [u8; 32] {
        crate::commitment::compute_canonical_state_commitment(self)
    }

    /// Verify that `self.id` matches `derive_raw(public_key, token_id)`.
    ///
    /// Audit P2-3: the `id` field is content-addressed at construction but
    /// nothing in the type system maintains the invariant after construction.
    /// Authoritative call sites (sovereign-witness ingest, peer-exchange ingest,
    /// post-deserialization) should call this and reject cells that fail.
    pub fn verify_id_integrity(&self) -> bool {
        self.id == CellId::derive_raw(&self.public_key, &self.token_id)
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
    ///
    /// Audit P1-5: This constructor produces a `DelegatedRef` with a
    /// placeholder all-zero signature, which `verify_parent_signature` will
    /// reject. To prevent external code from minting forged delegations by
    /// calling this and then skipping verification, the function is now
    /// `pub(crate)` — only the cell crate (and downstream callers that
    /// re-export it deliberately) can invoke it. External orchestration
    /// should go through a signature-required constructor or
    /// `DelegatedRef::new` with a real signature.
    pub(crate) fn spawn_child_with_delegation(
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
