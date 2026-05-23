use std::collections::{BTreeMap, HashMap};

use serde::{Deserialize, Serialize};

use crate::capability::CapabilityRef;
use crate::cell::Cell;
use crate::id::CellId;
use crate::permissions::Permissions;
use crate::state::{FieldElement, STATE_SLOTS};

/// A delta to apply to a single cell's state.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CellStateDelta {
    /// Field updates: (slot_index, new_value).
    pub field_updates: Vec<(usize, FieldElement)>,
    /// Whether to increment the nonce.
    pub nonce_increment: bool,
    /// Balance change (can be negative).
    pub balance_change: i64,
    /// Optional complete permission replacement.
    pub permission_changes: Option<Permissions>,
    /// Capabilities to grant.
    pub capability_grants: Vec<CapabilityRef>,
    /// Capability slots to revoke.
    pub capability_revocations: Vec<u32>,
}

impl CellStateDelta {
    /// Create an empty delta (no changes).
    pub fn empty() -> Self {
        CellStateDelta {
            field_updates: Vec::new(),
            nonce_increment: false,
            balance_change: 0,
            permission_changes: None,
            capability_grants: Vec::new(),
            capability_revocations: Vec::new(),
        }
    }
}

/// A set of changes to apply atomically to the ledger.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LedgerDelta {
    /// Cells to create.
    pub created: Vec<Cell>,
    /// Cells to update: (cell_id, delta).
    pub updated: Vec<(CellId, CellStateDelta)>,
    /// Computron transfers: (from, to, amount).
    pub computron_transfers: Vec<(CellId, CellId, u64)>,
}

impl LedgerDelta {
    /// Create an empty delta.
    pub fn new() -> Self {
        LedgerDelta {
            created: Vec::new(),
            updated: Vec::new(),
            computron_transfers: Vec::new(),
        }
    }
}

impl Default for LedgerDelta {
    fn default() -> Self {
        Self::new()
    }
}

/// A Merkle membership proof for a cell in the ledger.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MembershipProof {
    /// The cell ID this proof is for.
    pub cell_id: CellId,
    /// Hash of the cell's state (leaf hash).
    pub leaf_hash: [u8; 32],
    /// Sibling hashes along the path to the root (from leaf to root).
    pub path: Vec<([u8; 32], Side)>,
    /// The Merkle root this proof validates against.
    pub root: [u8; 32],
}

/// Which side a sibling is on in a Merkle proof path.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Side {
    Left,
    Right,
}

impl MembershipProof {
    /// Verify this membership proof.
    pub fn verify(&self) -> bool {
        let mut current = self.leaf_hash;
        for (sibling, side) in &self.path {
            let mut hasher = blake3::Hasher::new();
            match side {
                Side::Left => {
                    hasher.update(sibling);
                    hasher.update(&current);
                }
                Side::Right => {
                    hasher.update(&current);
                    hasher.update(sibling);
                }
            }
            current = *hasher.finalize().as_bytes();
        }
        current == self.root
    }
}

/// Errors that can occur when applying a ledger delta.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LedgerError {
    /// Attempted to create a cell that already exists.
    CellAlreadyExists(CellId),
    /// Attempted to update a cell that doesn't exist.
    CellNotFound(CellId),
    /// Invalid field index in a state update.
    InvalidFieldIndex { cell_id: CellId, index: usize },
    /// Insufficient balance for a transfer or deduction.
    InsufficientBalance {
        cell_id: CellId,
        available: u64,
        required: u64,
    },
    /// Balance overflow.
    BalanceOverflow { cell_id: CellId },
    /// Transfer source cell not found.
    TransferSourceNotFound(CellId),
    /// Transfer destination cell not found.
    TransferDestNotFound(CellId),
    /// Attempted to operate on a sovereign cell without providing a witness.
    SovereignWitnessRequired(CellId),
    /// The provided sovereign witness commitment does not match the stored commitment.
    SovereignCommitmentMismatch {
        cell_id: CellId,
        expected: [u8; 32],
        got: [u8; 32],
    },
    /// Attempted to register a sovereign cell that already exists (hosted or sovereign).
    SovereignAlreadyExists(CellId),
    /// The cell is not sovereign.
    NotSovereign(CellId),
}

impl core::fmt::Display for LedgerError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            LedgerError::CellAlreadyExists(id) => write!(f, "cell already exists: {id}"),
            LedgerError::CellNotFound(id) => write!(f, "cell not found: {id}"),
            LedgerError::InvalidFieldIndex { cell_id, index } => {
                write!(f, "invalid field index {index} for cell {cell_id}")
            }
            LedgerError::InsufficientBalance {
                cell_id,
                available,
                required,
            } => {
                write!(
                    f,
                    "insufficient balance for cell {cell_id}: have {available}, need {required}"
                )
            }
            LedgerError::BalanceOverflow { cell_id } => {
                write!(f, "balance overflow for cell {cell_id}")
            }
            LedgerError::TransferSourceNotFound(id) => {
                write!(f, "transfer source not found: {id}")
            }
            LedgerError::TransferDestNotFound(id) => {
                write!(f, "transfer destination not found: {id}")
            }
            LedgerError::SovereignWitnessRequired(id) => {
                write!(f, "sovereign cell requires witness: {id}")
            }
            LedgerError::SovereignCommitmentMismatch {
                cell_id,
                expected,
                got,
            } => {
                write!(
                    f,
                    "sovereign commitment mismatch for cell {cell_id}: expected {:02x}{:02x}..., got {:02x}{:02x}...",
                    expected[0], expected[1], got[0], got[1]
                )
            }
            LedgerError::SovereignAlreadyExists(id) => {
                write!(f, "sovereign cell already exists: {id}")
            }
            LedgerError::NotSovereign(id) => {
                write!(f, "cell is not sovereign: {id}")
            }
        }
    }
}

impl std::error::Error for LedgerError {}

/// The world state: a collection of cells with a Merkle commitment.
///
/// Uses an incremental binary Merkle tree. On cell state updates, only the
/// O(log N) path from the affected leaf to the root is recomputed. Structural
/// changes (inserts/removes) rebuild the tree since they shift leaf positions.
///
/// The tree uses lazy rebuilding: mutations via `get_mut()`, `create_cell()`,
/// `insert_cell()`, and `remove()` mark the tree as dirty. The rebuild is
/// deferred until `root()` or `membership_proof()` is called. This avoids
/// O(N^2) costs when performing N sequential inserts or mutations.
#[derive(Clone, Debug)]
pub struct Ledger {
    cells: HashMap<CellId, Cell>,
    /// Sovereign cells: federation stores only a 32-byte state commitment.
    /// The agent must provide the full cell state in each turn as a witness.
    sovereign_commitments: HashMap<CellId, [u8; 32]>,
    /// Sorted leaf positions: CellId -> index in the leaf layer.
    leaf_positions: BTreeMap<[u8; 32], usize>,
    /// The Merkle tree nodes, indexed by level then position.
    /// Level 0 = leaves (padded to next power of two with zero hashes).
    /// Level N = root (single element).
    tree_levels: Vec<Vec<[u8; 32]>>,
    root: [u8; 32],
    /// When true, the cached root and tree_levels are stale and must be
    /// rebuilt before `root()` can return a valid value.
    dirty: bool,
}

impl Ledger {
    /// Create an empty ledger.
    pub fn new() -> Self {
        Ledger {
            cells: HashMap::new(),
            sovereign_commitments: HashMap::new(),
            leaf_positions: BTreeMap::new(),
            tree_levels: Vec::new(),
            root: Self::compute_empty_root(),
            dirty: false,
        }
    }

    /// Get an immutable reference to a cell.
    pub fn get(&self, id: &CellId) -> Option<&Cell> {
        self.cells.get(id)
    }

    /// Get a mutable reference to a cell.
    ///
    /// Marks the tree as dirty since the cell's state may change. The Merkle
    /// tree will be lazily rebuilt on the next call to `root()`.
    pub fn get_mut(&mut self, id: &CellId) -> Option<&mut Cell> {
        let result = self.cells.get_mut(id);
        if result.is_some() {
            self.dirty = true;
        }
        result
    }

    /// Number of cells in the ledger.
    pub fn len(&self) -> usize {
        self.cells.len()
    }

    /// Whether the ledger is empty.
    pub fn is_empty(&self) -> bool {
        self.cells.is_empty()
    }

    /// Create a new cell and insert it. Returns the CellId.
    ///
    /// The Merkle tree rebuild is deferred until `root()` is called, making
    /// sequential inserts O(N) total instead of O(N^2).
    pub fn create_cell(&mut self, public_key: [u8; 32], token_id: [u8; 32]) -> CellId {
        let cell = Cell::new(public_key, token_id);
        let id = cell.id;
        self.cells.insert(id, cell);
        self.dirty = true;
        id
    }

    /// Insert a pre-built cell. Returns Err if a cell with the same ID already exists.
    ///
    /// The Merkle tree rebuild is deferred until `root()` is called, making
    /// sequential inserts O(N) total instead of O(N^2).
    pub fn insert_cell(&mut self, cell: Cell) -> Result<CellId, LedgerError> {
        let id = cell.id;
        if self.cells.contains_key(&id) {
            return Err(LedgerError::CellAlreadyExists(id));
        }
        self.cells.insert(id, cell);
        self.dirty = true;
        Ok(id)
    }

    /// Apply a delta to the ledger atomically.
    /// If any operation fails, the ledger is left unchanged.
    pub fn apply_delta(&mut self, delta: &LedgerDelta) -> Result<(), LedgerError> {
        // Validate with cumulative balance tracking.
        self.validate_delta(delta)?;

        // Clone the cells map — all mutations go to the clone.
        let mut new_cells = self.cells.clone();

        // Apply creations.
        for cell in &delta.created {
            new_cells.insert(cell.id, cell.clone());
        }

        // Apply updates.
        for (cell_id, state_delta) in &delta.updated {
            let cell = new_cells
                .get_mut(cell_id)
                .ok_or(LedgerError::CellNotFound(*cell_id))?;
            Self::apply_cell_delta(cell, state_delta, cell_id)?;
        }

        // Apply transfers (on the already-modified clone).
        for &(from_id, to_id, amount) in &delta.computron_transfers {
            let from_balance = {
                let from_cell = new_cells
                    .get(&from_id)
                    .ok_or(LedgerError::TransferSourceNotFound(from_id))?;
                if from_cell.state.balance < amount {
                    return Err(LedgerError::InsufficientBalance {
                        cell_id: from_id,
                        available: from_cell.state.balance,
                        required: amount,
                    });
                }
                from_cell.state.balance - amount
            };
            new_cells.get_mut(&from_id).unwrap().state.balance = from_balance;

            let to_cell = new_cells
                .get_mut(&to_id)
                .ok_or(LedgerError::TransferDestNotFound(to_id))?;
            to_cell.state.balance = to_cell
                .state
                .balance
                .checked_add(amount)
                .ok_or(LedgerError::BalanceOverflow { cell_id: to_id })?;
        }

        // All succeeded — swap in the new state atomically.
        self.cells = new_cells;

        // If the tree was already dirty or there are structural changes, do a
        // full rebuild. Otherwise, incrementally update only the affected leaves.
        if self.dirty || !delta.created.is_empty() {
            self.rebuild_tree();
        } else {
            // Collect all cell IDs that were modified.
            let mut modified_ids: Vec<CellId> = delta.updated.iter().map(|(id, _)| *id).collect();
            for &(from_id, to_id, _) in &delta.computron_transfers {
                modified_ids.push(from_id);
                modified_ids.push(to_id);
            }
            modified_ids.sort_unstable_by(|a, b| a.0.cmp(&b.0));
            modified_ids.dedup();

            // Update each modified leaf incrementally.
            for cell_id in &modified_ids {
                self.update_leaf(cell_id);
            }
        }
        Ok(())
    }

    /// Validate that a delta can be applied without errors.
    /// Tracks cumulative balance effects across all operations so that a cell
    /// appearing in both `updated` and `computron_transfers` is checked correctly.
    fn validate_delta(&self, delta: &LedgerDelta) -> Result<(), LedgerError> {
        // Build a set of cells being created in this delta for reference.
        let mut created_cells: HashMap<CellId, &Cell> = HashMap::new();
        for cell in &delta.created {
            if self.cells.contains_key(&cell.id) {
                return Err(LedgerError::CellAlreadyExists(cell.id));
            }
            created_cells.insert(cell.id, cell);
        }

        // Helper: look up a cell in either the existing ledger or the delta's created set.
        let lookup = |id: &CellId| -> Option<&Cell> {
            self.cells
                .get(id)
                .or_else(|| created_cells.get(id).copied())
        };

        // Track running balances per cell (cumulative across all operations).
        // Initialized lazily from the cell's current balance on first access.
        let mut running_balances: HashMap<CellId, u64> = HashMap::new();

        let get_running_balance =
            |balances: &mut HashMap<CellId, u64>, id: &CellId| -> Option<u64> {
                if let Some(&b) = balances.get(id) {
                    Some(b)
                } else {
                    // Initialize from current state.
                    let cell = lookup(id)?;
                    balances.insert(*id, cell.state.balance);
                    Some(cell.state.balance)
                }
            };

        // Check updates reference existing cells and validate cumulative balance.
        for (cell_id, state_delta) in &delta.updated {
            let cell = lookup(cell_id).ok_or(LedgerError::CellNotFound(*cell_id))?;

            // Validate field indices.
            for &(index, _) in &state_delta.field_updates {
                if index >= STATE_SLOTS {
                    return Err(LedgerError::InvalidFieldIndex {
                        cell_id: *cell_id,
                        index,
                    });
                }
            }

            // Get or initialize running balance for this cell.
            let balance =
                get_running_balance(&mut running_balances, cell_id).unwrap_or(cell.state.balance);

            // Validate and apply balance change cumulatively.
            if state_delta.balance_change < 0 {
                let required = state_delta.balance_change.unsigned_abs();
                if balance < required {
                    return Err(LedgerError::InsufficientBalance {
                        cell_id: *cell_id,
                        available: balance,
                        required,
                    });
                }
                running_balances.insert(*cell_id, balance - required);
            } else {
                let add = state_delta.balance_change as u64;
                let new_balance = balance
                    .checked_add(add)
                    .ok_or(LedgerError::BalanceOverflow { cell_id: *cell_id })?;
                running_balances.insert(*cell_id, new_balance);
            }
        }

        // Check transfers using cumulative running balances.
        for &(from_id, to_id, amount) in &delta.computron_transfers {
            let from_balance = get_running_balance(&mut running_balances, &from_id)
                .ok_or(LedgerError::TransferSourceNotFound(from_id))?;
            if from_balance < amount {
                return Err(LedgerError::InsufficientBalance {
                    cell_id: from_id,
                    available: from_balance,
                    required: amount,
                });
            }
            running_balances.insert(from_id, from_balance - amount);

            let to_balance = get_running_balance(&mut running_balances, &to_id)
                .ok_or(LedgerError::TransferDestNotFound(to_id))?;
            let new_to = to_balance
                .checked_add(amount)
                .ok_or(LedgerError::BalanceOverflow { cell_id: to_id })?;
            running_balances.insert(to_id, new_to);
        }

        Ok(())
    }

    /// Apply a CellStateDelta to a cell (assumes validation passed).
    fn apply_cell_delta(
        cell: &mut Cell,
        delta: &CellStateDelta,
        cell_id: &CellId,
    ) -> Result<(), LedgerError> {
        // Field updates.
        for &(index, ref value) in &delta.field_updates {
            if index >= STATE_SLOTS {
                return Err(LedgerError::InvalidFieldIndex {
                    cell_id: *cell_id,
                    index,
                });
            }
            cell.state.fields[index] = *value;
        }

        // Nonce.
        if delta.nonce_increment {
            cell.state.increment_nonce();
        }

        // Balance.
        if !cell.state.apply_balance_change(delta.balance_change) {
            if delta.balance_change < 0 {
                return Err(LedgerError::InsufficientBalance {
                    cell_id: *cell_id,
                    available: cell.state.balance,
                    required: delta.balance_change.unsigned_abs(),
                });
            } else {
                return Err(LedgerError::BalanceOverflow { cell_id: *cell_id });
            }
        }

        // Permissions.
        if let Some(ref new_perms) = delta.permission_changes {
            cell.permissions = new_perms.clone();
        }

        // Capability grants (preserving all fields including expires_at).
        for cap_ref in &delta.capability_grants {
            cell.capabilities.grant_full(
                cap_ref.target,
                cap_ref.permissions.clone(),
                cap_ref.breadstuff,
                cap_ref.expires_at,
            );
        }

        // Capability revocations.
        for &slot in &delta.capability_revocations {
            cell.capabilities.revoke(slot);
        }

        Ok(())
    }

    /// Get the current Merkle root.
    ///
    /// If the tree has been marked dirty (due to mutations via `get_mut()`,
    /// `create_cell()`, or `insert_cell()`), this will rebuild the tree first.
    /// The rebuild is O(N) but happens at most once per batch of mutations.
    pub fn root(&mut self) -> [u8; 32] {
        if self.dirty {
            self.rebuild_tree();
        }
        self.root
    }

    /// Get the current Merkle root without triggering a rebuild.
    ///
    /// WARNING: This may return a stale root if mutations have occurred since
    /// the last rebuild. Use only when you know the tree is up-to-date (e.g.,
    /// immediately after construction or after calling `root()`).
    pub fn root_cached(&self) -> [u8; 32] {
        self.root
    }

    /// Generate a membership proof for a cell using the stored tree.
    ///
    /// Triggers a tree rebuild if the ledger is dirty.
    pub fn membership_proof(&mut self, id: &CellId) -> Option<MembershipProof> {
        if !self.cells.contains_key(id) {
            return None;
        }

        if self.dirty {
            self.rebuild_tree();
        }

        let cell = self.cells.get(id).unwrap();
        let leaf_hash = Self::hash_cell(cell);

        // Look up position from stored leaf_positions.
        let pos = *self.leaf_positions.get(&id.0)?;

        // If tree is trivial (single leaf), no path needed.
        if self.tree_levels.len() <= 1 {
            return Some(MembershipProof {
                cell_id: *id,
                leaf_hash,
                path: Vec::new(),
                root: self.root,
            });
        }

        // Extract the authentication path from the stored tree levels.
        let mut path = Vec::new();
        let mut idx = pos;
        for level in 0..self.tree_levels.len() - 1 {
            let sibling_idx = if idx % 2 == 0 { idx + 1 } else { idx - 1 };
            let sibling_hash = self.tree_levels[level]
                .get(sibling_idx)
                .copied()
                .unwrap_or([0u8; 32]);
            let side = if idx % 2 == 0 {
                Side::Right
            } else {
                Side::Left
            };
            path.push((sibling_hash, side));
            idx /= 2;
        }

        Some(MembershipProof {
            cell_id: *id,
            leaf_hash,
            path,
            root: self.root,
        })
    }

    /// Incrementally update a single leaf and propagate changes to the root.
    /// O(log N) operation.
    fn update_leaf(&mut self, cell_id: &CellId) {
        let pos = match self.leaf_positions.get(&cell_id.0) {
            Some(&p) => p,
            None => return, // cell not in tree (shouldn't happen on hot path)
        };

        let cell = match self.cells.get(cell_id) {
            Some(c) => c,
            None => return,
        };

        let leaf_hash = Self::hash_cell(cell);
        self.tree_levels[0][pos] = leaf_hash;

        // Walk up the tree recomputing only affected parent nodes.
        let mut current_pos = pos;
        for level in 0..self.tree_levels.len() - 1 {
            let parent_pos = current_pos / 2;
            let left_child = current_pos & !1; // round down to even
            let right_child = left_child + 1;

            let left_hash = self.tree_levels[level][left_child];
            let right_hash = self.tree_levels[level]
                .get(right_child)
                .copied()
                .unwrap_or([0u8; 32]);

            let mut hasher = blake3::Hasher::new();
            hasher.update(&left_hash);
            hasher.update(&right_hash);
            self.tree_levels[level + 1][parent_pos] = *hasher.finalize().as_bytes();

            current_pos = parent_pos;
        }

        // Update cached root.
        self.root = *self.tree_levels.last().unwrap().first().unwrap();
    }

    /// Full rebuild of the Merkle tree from scratch.
    /// Called on structural changes (insert/remove) that alter leaf positions.
    /// Also clears the dirty flag.
    fn rebuild_tree(&mut self) {
        self.dirty = false;

        if self.cells.is_empty() {
            self.leaf_positions.clear();
            self.tree_levels.clear();
            self.root = Self::compute_empty_root();
            return;
        }

        // Collect and sort all cells by CellId bytes for deterministic ordering.
        let mut sorted_cells: Vec<(&CellId, &Cell)> = self.cells.iter().collect();
        sorted_cells.sort_by(|a, b| a.0.0.cmp(&b.0.0));

        // Build leaf_positions map and leaf hashes.
        self.leaf_positions.clear();
        let mut leaves: Vec<[u8; 32]> = Vec::with_capacity(sorted_cells.len());
        for (i, (cid, cell)) in sorted_cells.iter().enumerate() {
            self.leaf_positions.insert(cid.0, i);
            leaves.push(Self::hash_cell(cell));
        }

        let n_leaves = leaves.len();
        if n_leaves == 1 {
            // Single leaf IS the root.
            self.tree_levels = vec![leaves.clone()];
            self.root = leaves[0];
            return;
        }

        // Pad to next power of two with zero hashes.
        let next_pow2 = n_leaves.next_power_of_two();
        leaves.resize(next_pow2, [0u8; 32]);

        // Build levels bottom-up.
        let mut levels: Vec<Vec<[u8; 32]>> = Vec::new();
        levels.push(leaves);

        loop {
            let current = levels.last().unwrap();
            if current.len() == 1 {
                break;
            }
            let mut next_level = Vec::with_capacity(current.len() / 2);
            for chunk in current.chunks(2) {
                let mut hasher = blake3::Hasher::new();
                hasher.update(&chunk[0]);
                hasher.update(&chunk[1]);
                next_level.push(*hasher.finalize().as_bytes());
            }
            levels.push(next_level);
        }

        self.root = levels.last().unwrap()[0];
        self.tree_levels = levels;
    }

    /// Full recompute of the Merkle root (validation/fallback).
    /// Equivalent to rebuild_tree but only returns the root without storing levels.
    #[cfg(test)]
    pub(crate) fn recompute_root_standalone(&self) -> [u8; 32] {
        if self.cells.is_empty() {
            return Self::compute_empty_root();
        }

        let mut all_hashes: Vec<(CellId, [u8; 32])> = self
            .cells
            .iter()
            .map(|(cid, c)| (*cid, Self::hash_cell(c)))
            .collect();
        all_hashes.sort_by(|a, b| a.0.0.cmp(&b.0.0));

        let leaves: Vec<[u8; 32]> = all_hashes.iter().map(|(_, h)| *h).collect();
        Self::merkle_root(&leaves)
    }

    /// Compute Merkle root from a list of leaf hashes (used by standalone recompute).
    #[cfg(test)]
    fn merkle_root(leaves: &[[u8; 32]]) -> [u8; 32] {
        if leaves.is_empty() {
            return Self::compute_empty_root();
        }
        if leaves.len() == 1 {
            return leaves[0];
        }

        // Pad to power of two.
        let mut padded = leaves.to_vec();
        let next_pow2 = padded.len().next_power_of_two();
        padded.resize(next_pow2, [0u8; 32]);

        let mut current_level = padded;
        while current_level.len() > 1 {
            let mut next_level = Vec::new();
            for chunk in current_level.chunks(2) {
                let mut hasher = blake3::Hasher::new();
                hasher.update(&chunk[0]);
                hasher.update(&chunk[1]);
                next_level.push(*hasher.finalize().as_bytes());
            }
            current_level = next_level;
        }
        current_level[0]
    }

    /// Hash a cell for Merkle tree inclusion.
    ///
    /// ALL security-relevant fields are included in the hash to ensure the Merkle
    /// tree commits to the complete cell state. Omitting any field would allow an
    /// attacker to present a valid Merkle proof for a cell with tampered fields.
    fn hash_cell(cell: &Cell) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-cell:merkle-leaf v2");

        // Identity fields
        hasher.update(cell.id.as_bytes());
        hasher.update(&cell.public_key);
        hasher.update(&cell.token_id);

        // Core state: nonce, balance, fields
        hasher.update(&cell.state.nonce.to_le_bytes());
        hasher.update(&cell.state.balance.to_le_bytes());
        for field in &cell.state.fields {
            hasher.update(field);
        }

        // Field visibility and commitments
        for vis in &cell.state.field_visibility {
            let vis_byte = match vis {
                crate::state::FieldVisibility::Public => 0u8,
                crate::state::FieldVisibility::Committed => 1u8,
                crate::state::FieldVisibility::SelectivelyDisclosable => 2u8,
            };
            hasher.update(&[vis_byte]);
        }
        for commitment in &cell.state.commitments {
            match commitment {
                Some(hash) => {
                    hasher.update(&[1u8]);
                    hasher.update(hash);
                }
                None => {
                    hasher.update(&[0u8]);
                }
            }
        }

        // proved_state flag
        hasher.update(&[cell.state.proved_state as u8]);

        // delegation_epoch
        hasher.update(&cell.state.delegation_epoch.to_le_bytes());

        // Permissions (hash each field's AuthRequired variant)
        let perms = &cell.permissions;
        let perm_fields = [
            &perms.send,
            &perms.receive,
            &perms.set_state,
            &perms.set_permissions,
            &perms.set_verification_key,
            &perms.increment_nonce,
            &perms.delegate,
            &perms.access,
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

        // Capabilities (c-list)
        // ALL security-relevant capability fields are included: target, slot,
        // permissions, breadstuff, and expires_at. Omitting any field would allow
        // two capabilities with different security properties to hash identically.
        let cap_count = cell.capabilities.len() as u64;
        hasher.update(&cap_count.to_le_bytes());
        for cap in cell.capabilities.iter() {
            hasher.update(cap.target.as_bytes());
            hasher.update(&cap.slot.to_le_bytes());
            let perm_byte = match &cap.permissions {
                crate::permissions::AuthRequired::None => 0u8,
                crate::permissions::AuthRequired::Signature => 1u8,
                crate::permissions::AuthRequired::Proof => 2u8,
                crate::permissions::AuthRequired::Either => 3u8,
                crate::permissions::AuthRequired::Impossible => 4u8,
            };
            hasher.update(&[perm_byte]);
            if let Some(ref bs) = cap.breadstuff {
                hasher.update(&[1u8]);
                hasher.update(bs);
            } else {
                hasher.update(&[0u8]);
            }
            match cap.expires_at {
                Some(h) => {
                    hasher.update(&[1u8]);
                    hasher.update(&h.to_le_bytes());
                }
                None => {
                    hasher.update(&[0u8]);
                }
            }
        }

        // Program
        match &cell.program {
            crate::program::CellProgram::None => {
                hasher.update(&[0u8]);
            }
            crate::program::CellProgram::Predicate(constraints) => {
                hasher.update(&[1u8]);
                // Hash serialized constraints for determinism
                let serialized = postcard::to_allocvec(constraints).unwrap_or_default();
                hasher.update(&(serialized.len() as u64).to_le_bytes());
                hasher.update(&serialized);
            }
            crate::program::CellProgram::Circuit { circuit_hash } => {
                hasher.update(&[2u8]);
                hasher.update(circuit_hash);
            }
        }

        // Verification key
        match &cell.verification_key {
            Some(vk) => {
                hasher.update(&[1u8]);
                hasher.update(&vk.hash);
            }
            None => {
                hasher.update(&[0u8]);
            }
        }

        // Delegate
        match &cell.delegate {
            Some(delegate_id) => {
                hasher.update(&[1u8]);
                hasher.update(delegate_id.as_bytes());
            }
            None => {
                hasher.update(&[0u8]);
            }
        }

        // Delegation (snapshot+refresh)
        match &cell.delegation {
            Some(deleg) => {
                hasher.update(&[1u8]);
                hasher.update(deleg.source.as_bytes());
                hasher.update(&deleg.delegation_epoch.to_le_bytes());
                hasher.update(&deleg.refreshed_at.to_le_bytes());
                hasher.update(&deleg.max_staleness.to_le_bytes());
                let snap_count = deleg.snapshot.len() as u64;
                hasher.update(&snap_count.to_le_bytes());
                for cap in &deleg.snapshot {
                    hasher.update(cap.target.as_bytes());
                    hasher.update(&cap.slot.to_le_bytes());
                }
            }
            None => {
                hasher.update(&[0u8]);
            }
        }

        *hasher.finalize().as_bytes()
    }

    /// Hash a single state constraint into the hasher for deterministic program hashing.
    fn hash_constraint(hasher: &mut blake3::Hasher, constraint: &crate::program::StateConstraint) {
        use crate::program::StateConstraint;
        match constraint {
            StateConstraint::FieldEquals { index, value } => {
                hasher.update(&[0u8]);
                hasher.update(&[*index]);
                hasher.update(value);
            }
            StateConstraint::FieldGte { index, value } => {
                hasher.update(&[1u8]);
                hasher.update(&[*index]);
                hasher.update(value);
            }
            StateConstraint::FieldLte { index, value } => {
                hasher.update(&[2u8]);
                hasher.update(&[*index]);
                hasher.update(value);
            }
            StateConstraint::SumEquals { indices, value } => {
                hasher.update(&[3u8]);
                hasher.update(&(indices.len() as u64).to_le_bytes());
                for &idx in indices {
                    hasher.update(&[idx]);
                }
                hasher.update(value);
            }
            StateConstraint::Immutable { index } => {
                hasher.update(&[4u8]);
                hasher.update(&[*index]);
            }
            StateConstraint::Custom { constraint_hash } => {
                hasher.update(&[5u8]);
                hasher.update(constraint_hash);
            }
        }
    }

    /// The root of an empty tree.
    fn compute_empty_root() -> [u8; 32] {
        *blake3::hash(b"pyana-cell:empty-ledger").as_bytes()
    }

    /// Iterate over all cells.
    pub fn iter(&self) -> impl Iterator<Item = (&CellId, &Cell)> {
        self.cells.iter()
    }

    /// Check if a cell exists.
    pub fn contains(&self, id: &CellId) -> bool {
        self.cells.contains_key(id)
    }

    /// Remove a cell from the ledger. Returns the removed cell if it existed.
    ///
    /// The Merkle tree rebuild is deferred until `root()` is called.
    pub fn remove(&mut self, id: &CellId) -> Option<Cell> {
        let cell = self.cells.remove(id);
        if cell.is_some() {
            self.dirty = true;
        }
        cell
    }

    // =========================================================================
    // Sovereign cell support (Phase 1a)
    // =========================================================================

    /// Register a cell as sovereign, storing only its initial state commitment.
    ///
    /// The cell must not already exist in either the hosted cells or the sovereign
    /// commitments map.
    pub fn register_sovereign_cell(
        &mut self,
        id: CellId,
        initial_commitment: [u8; 32],
    ) -> Result<(), LedgerError> {
        if self.cells.contains_key(&id) || self.sovereign_commitments.contains_key(&id) {
            return Err(LedgerError::SovereignAlreadyExists(id));
        }
        self.sovereign_commitments.insert(id, initial_commitment);
        Ok(())
    }

    /// Get the stored commitment for a sovereign cell.
    pub fn get_sovereign_commitment(&self, id: &CellId) -> Option<&[u8; 32]> {
        self.sovereign_commitments.get(id)
    }

    /// Update the stored commitment for a sovereign cell after a verified transition.
    pub fn update_sovereign_commitment(
        &mut self,
        id: &CellId,
        new_commitment: [u8; 32],
    ) -> Result<(), LedgerError> {
        if !self.sovereign_commitments.contains_key(id) {
            return Err(LedgerError::NotSovereign(*id));
        }
        self.sovereign_commitments.insert(*id, new_commitment);
        Ok(())
    }

    /// Check whether a cell ID refers to a sovereign cell.
    pub fn is_sovereign(&self, id: &CellId) -> bool {
        self.sovereign_commitments.contains_key(id)
    }

    /// Move a hosted cell to sovereign mode. Stores only the state commitment
    /// and removes the full cell state from the hosted store.
    ///
    /// Returns the removed cell on success.
    pub fn make_sovereign(&mut self, id: &CellId) -> Result<Cell, LedgerError> {
        let cell = self.cells.remove(id).ok_or(LedgerError::CellNotFound(*id))?;
        let commitment = cell.state_commitment();
        self.sovereign_commitments.insert(*id, commitment);
        self.dirty = true;
        Ok(cell)
    }
}

impl Default for Ledger {
    fn default() -> Self {
        Self::new()
    }
}
