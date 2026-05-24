//! Strategies for building cells and ledgers the executor will accept.
//!
//! The generators here produce a "wide-open" ledger: every cell has
//! `AuthRequired::None` for every permission slot and holds capabilities to
//! every other cell. This is deliberately permissive — it lets the
//! invariant tests focus on *outcomes* (does balance balance? does the
//! receipt chain link?) rather than spending their generator budget on
//! arranging authorization to succeed.
//!
//! Invariants that specifically test authorization (`capability_attenuation`,
//! `permission_enforcement`) build narrower ledgers from primitives in
//! `capability.rs`.

use pyana_cell::{AuthRequired, Cell, CellId, Ledger, Permissions};

/// A description of the cells to seed a ledger with.
#[derive(Clone, Debug)]
pub struct LedgerSpec {
    /// Number of cells to create. Each gets a deterministic public key
    /// derived from its index.
    pub n_cells: u8,
    /// Starting balance for every cell.
    pub balance_each: u64,
    /// If true, set every permission slot to `AuthRequired::None` and grant
    /// every-cell-to-every-other-cell capabilities.
    pub wide_open: bool,
}

impl Default for LedgerSpec {
    fn default() -> Self {
        Self {
            n_cells: 3,
            balance_each: 10_000,
            wide_open: true,
        }
    }
}

/// Build a cell with a deterministic public key derived from `seed`.
///
/// The same `seed` always produces the same `CellId` so tests can reason
/// about cells by index without re-deriving keys each time.
pub fn make_cell(seed: u8, balance: u64) -> Cell {
    let mut pk = [0u8; 32];
    // Spread the seed across two bytes so neighbouring seeds aren't
    // accidentally hash-adjacent in any one-byte-prefix lookups.
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(7);
    let token_id = [0u8; 32];
    Cell::with_balance(pk, token_id, balance)
}

/// Build a ledger from a `LedgerSpec`. Returns the ledger and the ordered
/// list of `CellId`s so tests can refer to cells by index.
pub fn build_open_ledger(spec: &LedgerSpec) -> (Ledger, Vec<CellId>) {
    let mut ledger = Ledger::new();
    let mut ids = Vec::with_capacity(spec.n_cells as usize);
    for i in 0..spec.n_cells {
        let cell = make_cell(i, spec.balance_each);
        let id = cell.id();
        ledger.insert_cell(cell).unwrap();
        ids.push(id);
    }

    if spec.wide_open {
        let permissive = Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        };

        for i in 0..ids.len() {
            // Set permissive permissions on every cell.
            let cell = ledger.get_mut(&ids[i]).unwrap();
            cell.permissions = permissive.clone();
            // Grant capabilities to every other cell (transfer endpoint).
            for j in 0..ids.len() {
                if i != j {
                    cell.capabilities.grant(ids[j], AuthRequired::None);
                }
            }
        }
    }

    (ledger, ids)
}
