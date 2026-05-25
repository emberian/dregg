//! Randomized turn generation: stress-tests the executor with random effect sequences.
//!
//! Generates random turns with random effects, executes them through the harness,
//! and verifies all invariants after each turn.

use std::collections::HashMap;

use pyana_cell::state::{FieldElement, STATE_SLOTS};
use pyana_cell::{Cell, CellId, CellStateDelta, Ledger, LedgerDelta, Nullifier, NullifierSet};
use pyana_teasting::assertions::{
    assert_conservation_invariant, assert_no_double_spend, assert_nonce_monotonicity,
};

// =============================================================================
// Deterministic PRNG (xorshift64)
// =============================================================================

struct Rng {
    state: u64,
}

impl Rng {
    fn from_seed(seed: &str) -> Self {
        let hash = blake3::hash(seed.as_bytes());
        let bytes: [u8; 8] = hash.as_bytes()[..8].try_into().unwrap();
        let state = u64::from_le_bytes(bytes) | 1;
        Rng { state }
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.state = x;
        x
    }

    fn next_u32(&mut self) -> u32 {
        (self.next_u64() >> 16) as u32
    }

    fn gen_range(&mut self, lo: u64, hi: u64) -> u64 {
        if hi <= lo {
            return lo;
        }
        lo + self.next_u64() % (hi - lo)
    }

    fn gen_bytes(&mut self) -> [u8; 32] {
        let mut out = [0u8; 32];
        for chunk in out.chunks_exact_mut(8) {
            chunk.copy_from_slice(&self.next_u64().to_le_bytes());
        }
        out
    }

    fn gen_field_element(&mut self) -> FieldElement {
        self.gen_bytes()
    }
}

// =============================================================================
// Random Effect Types (ledger-level)
// =============================================================================

#[derive(Debug, Clone)]
enum FuzzEffect {
    Transfer {
        from: usize,
        to: usize,
        amount: u64,
    },
    SetField {
        cell: usize,
        index: usize,
        value: FieldElement,
    },
    IncrementNonce {
        cell: usize,
    },
    CreateCell {
        balance: u64,
    },
    BalanceChange {
        cell: usize,
        delta: i64,
    },
}

impl std::fmt::Display for FuzzEffect {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FuzzEffect::Transfer { from, to, amount } => {
                write!(
                    f,
                    "Transfer(cell[{}] -> cell[{}], amount={})",
                    from, to, amount
                )
            }
            FuzzEffect::SetField { cell, index, value } => {
                write!(
                    f,
                    "SetField(cell[{}], slot={}, value={:02x}{:02x}...)",
                    cell, index, value[0], value[1]
                )
            }
            FuzzEffect::IncrementNonce { cell } => {
                write!(f, "IncrementNonce(cell[{}])", cell)
            }
            FuzzEffect::CreateCell { balance } => {
                write!(f, "CreateCell(balance={})", balance)
            }
            FuzzEffect::BalanceChange { cell, delta } => {
                write!(f, "BalanceChange(cell[{}], delta={})", cell, delta)
            }
        }
    }
}

fn generate_random_effect(rng: &mut Rng, num_cells: usize) -> FuzzEffect {
    if num_cells == 0 {
        return FuzzEffect::CreateCell {
            balance: rng.gen_range(0, 1000),
        };
    }

    match rng.next_u32() % 5 {
        0 => {
            let from = rng.gen_range(0, num_cells as u64) as usize;
            let to = rng.gen_range(0, num_cells as u64) as usize;
            let amount = rng.gen_range(0, 200);
            FuzzEffect::Transfer { from, to, amount }
        }
        1 => {
            let cell = rng.gen_range(0, num_cells as u64) as usize;
            let index = rng.gen_range(0, STATE_SLOTS as u64) as usize;
            let value = rng.gen_field_element();
            FuzzEffect::SetField { cell, index, value }
        }
        2 => {
            let cell = rng.gen_range(0, num_cells as u64) as usize;
            FuzzEffect::IncrementNonce { cell }
        }
        3 => {
            let balance = rng.gen_range(0, 500);
            FuzzEffect::CreateCell { balance }
        }
        _ => {
            // Balance change that stays within bounds (add small amounts for safety).
            let cell = rng.gen_range(0, num_cells as u64) as usize;
            let delta = rng.gen_range(0, 100) as i64;
            FuzzEffect::BalanceChange { cell, delta }
        }
    }
}

// =============================================================================
// Test: Fuzz Turns with All Invariant Checks
// =============================================================================

/// Run 500 random turns and verify conservation + nonce monotonicity after each.
#[test]
fn test_fuzz_turns_conservation_and_nonce() {
    let mut rng = Rng::from_seed("fuzz_turns_conservation_and_nonce");
    let mut ledger = Ledger::new();
    let mut cell_ids: Vec<CellId> = Vec::new();
    let mut observed_nonces: HashMap<CellId, u64> = HashMap::new();
    let mut expected_total: u64 = 0;

    // Seed with a few cells.
    for i in 0..4 {
        let pk = {
            let mut b = [0u8; 32];
            b[0] = i;
            b[1] = 0xFD;
            b
        };
        let token_id = [0xBB; 32];
        let mut cell = Cell::new_hosted(pk, token_id);
        cell.state.set_balance(500);
        let id = ledger.insert_cell(cell).unwrap();
        cell_ids.push(id);
        expected_total += 500;
    }

    for _turn_idx in 0..500 {
        let effect = generate_random_effect(&mut rng, cell_ids.len());

        let apply_result = match &effect {
            FuzzEffect::Transfer { from, to, amount } => {
                if *from == *to || *amount == 0 {
                    continue;
                }
                let from_id = cell_ids[*from];
                let to_id = cell_ids[*to];
                let from_balance = ledger.get(&from_id).unwrap().state.balance();
                if from_balance < *amount {
                    continue; // skip invalid transfers
                }
                let delta = LedgerDelta {
                    created: Vec::new(),
                    updated: Vec::new(),
                    computron_transfers: vec![(from_id, to_id, *amount)],
                };
                ledger.apply_delta(&delta)
            }
            FuzzEffect::SetField { cell, index, value } => {
                let cell_id = cell_ids[*cell];
                let delta = LedgerDelta {
                    created: Vec::new(),
                    updated: vec![(
                        cell_id,
                        CellStateDelta {
                            field_updates: vec![(*index, *value)],
                            nonce_increment: false,
                            balance_change: 0,
                            permission_changes: None,
                            capability_grants: Vec::new(),
                            capability_revocations: Vec::new(),
                        },
                    )],
                    computron_transfers: Vec::new(),
                };
                ledger.apply_delta(&delta)
            }
            FuzzEffect::IncrementNonce { cell } => {
                let cell_id = cell_ids[*cell];
                let delta = LedgerDelta {
                    created: Vec::new(),
                    updated: vec![(
                        cell_id,
                        CellStateDelta {
                            field_updates: Vec::new(),
                            nonce_increment: true,
                            balance_change: 0,
                            permission_changes: None,
                            capability_grants: Vec::new(),
                            capability_revocations: Vec::new(),
                        },
                    )],
                    computron_transfers: Vec::new(),
                };
                ledger.apply_delta(&delta)
            }
            FuzzEffect::CreateCell { balance } => {
                let pk = rng.gen_bytes();
                let token_id = rng.gen_bytes();
                let mut cell = Cell::new_hosted(pk, token_id);
                cell.state.set_balance(*balance);
                expected_total += *balance;
                let id = ledger.insert_cell(cell).unwrap();
                cell_ids.push(id);
                Ok(())
            }
            FuzzEffect::BalanceChange { cell, delta } => {
                let cell_id = cell_ids[*cell];
                // Only apply positive balance changes (mint) to keep conservation simple.
                let delta_val = *delta;
                if delta_val <= 0 {
                    continue;
                }
                expected_total += delta_val as u64;
                let ldelta = LedgerDelta {
                    created: Vec::new(),
                    updated: vec![(
                        cell_id,
                        CellStateDelta {
                            field_updates: Vec::new(),
                            nonce_increment: false,
                            balance_change: delta_val,
                            permission_changes: None,
                            capability_grants: Vec::new(),
                            capability_revocations: Vec::new(),
                        },
                    )],
                    computron_transfers: Vec::new(),
                };
                ledger.apply_delta(&ldelta)
            }
        };

        if apply_result.is_err() {
            // Some operations legitimately fail (e.g., insufficient balance).
            // That's fine -- just skip and verify invariants still hold.
            continue;
        }

        // Verify invariants after every successful turn.
        assert_conservation_invariant(&ledger, expected_total);
        assert_nonce_monotonicity(&ledger, &mut observed_nonces);
    }
}

/// Fuzz with only transfers to stress conservation.
#[test]
fn test_fuzz_transfers_only() {
    let mut rng = Rng::from_seed("fuzz_transfers_only");
    let mut ledger = Ledger::new();
    let mut cell_ids: Vec<CellId> = Vec::new();

    let initial_per_cell = 10_000u64;
    let num_cells = 8;

    for i in 0..num_cells {
        let pk = {
            let mut b = [0u8; 32];
            b[0] = i as u8;
            b[2] = 0xCC;
            b
        };
        let token_id = [0x11; 32];
        let mut cell = Cell::new_hosted(pk, token_id);
        cell.state.set_balance(initial_per_cell);
        let id = ledger.insert_cell(cell).unwrap();
        cell_ids.push(id);
    }

    let expected_total = initial_per_cell * num_cells as u64;

    for _ in 0..1000 {
        let from_idx = rng.gen_range(0, num_cells as u64) as usize;
        let to_idx = rng.gen_range(0, num_cells as u64) as usize;
        if from_idx == to_idx {
            continue;
        }

        let from_id = cell_ids[from_idx];
        let to_id = cell_ids[to_idx];
        let from_balance = ledger.get(&from_id).unwrap().state.balance();
        if from_balance == 0 {
            continue;
        }

        let amount = rng.gen_range(1, from_balance.min(1000) + 1);
        let delta = LedgerDelta {
            created: Vec::new(),
            updated: Vec::new(),
            computron_transfers: vec![(from_id, to_id, amount)],
        };

        if ledger.apply_delta(&delta).is_ok() {
            assert_conservation_invariant(&ledger, expected_total);
        }
    }
}

/// Fuzz nonce increments: nonce must never go backward even with interleaved operations.
#[test]
fn test_fuzz_nonce_never_decreases() {
    let mut rng = Rng::from_seed("fuzz_nonce_never_decreases");
    let mut ledger = Ledger::new();
    let mut cell_ids: Vec<CellId> = Vec::new();
    let mut observed_nonces: HashMap<CellId, u64> = HashMap::new();

    for i in 0..6 {
        let pk = {
            let mut b = [0u8; 32];
            b[0] = i;
            b[3] = 0xDD;
            b
        };
        let token_id = [0x22; 32];
        let cell = Cell::new_hosted(pk, token_id);
        let id = ledger.insert_cell(cell).unwrap();
        cell_ids.push(id);
    }

    for _ in 0..500 {
        // Randomly pick a cell and increment its nonce.
        let idx = rng.gen_range(0, cell_ids.len() as u64) as usize;
        let cell_id = cell_ids[idx];

        let delta = LedgerDelta {
            created: Vec::new(),
            updated: vec![(
                cell_id,
                CellStateDelta {
                    field_updates: Vec::new(),
                    nonce_increment: true,
                    balance_change: 0,
                    permission_changes: None,
                    capability_grants: Vec::new(),
                    capability_revocations: Vec::new(),
                },
            )],
            computron_transfers: Vec::new(),
        };

        ledger.apply_delta(&delta).unwrap();
        assert_nonce_monotonicity(&ledger, &mut observed_nonces);
    }
}

/// Fuzz nullifier uniqueness: inserting the same nullifier twice must always fail.
#[test]
fn test_fuzz_nullifier_uniqueness() {
    let mut rng = Rng::from_seed("fuzz_nullifier_uniqueness");
    let mut nullifier_set = NullifierSet::new();
    let mut all_nullifiers: Vec<[u8; 32]> = Vec::new();

    for _ in 0..200 {
        let nullifier = rng.gen_bytes();
        nullifier_set.insert(Nullifier(nullifier)).unwrap();
        all_nullifiers.push(nullifier);
    }

    // Try to insert each one again -- must fail.
    for nullifier in &all_nullifiers {
        let result = nullifier_set.insert(Nullifier(*nullifier));
        assert!(
            result.is_err(),
            "Double-spend should be rejected for nullifier {:02x}{:02x}...",
            nullifier[0],
            nullifier[1],
        );
    }

    // Verify no double-spend in history.
    assert_no_double_spend(&all_nullifiers, &nullifier_set);
}

/// Mixed fuzz: all effect types interleaved.
#[test]
fn test_fuzz_mixed_effects_500_turns() {
    let mut rng = Rng::from_seed("fuzz_mixed_effects_500");
    let mut ledger = Ledger::new();
    let mut cell_ids: Vec<CellId> = Vec::new();
    let mut observed_nonces: HashMap<CellId, u64> = HashMap::new();
    let mut expected_total = 0u64;

    // Start with 3 cells.
    for i in 0..3 {
        let pk = {
            let mut b = [0u8; 32];
            b[0] = i;
            b[4] = 0xEE;
            b
        };
        let token_id = [0x33; 32];
        let mut cell = Cell::new_hosted(pk, token_id);
        cell.state.set_balance(2000);
        let id = ledger.insert_cell(cell).unwrap();
        cell_ids.push(id);
        expected_total += 2000;
    }

    let mut successful_turns = 0;

    for _ in 0..500 {
        let effect = generate_random_effect(&mut rng, cell_ids.len());

        let result = match &effect {
            FuzzEffect::Transfer { from, to, amount } => {
                if *from == *to || *amount == 0 || cell_ids.is_empty() {
                    continue;
                }
                let from_id = cell_ids[*from];
                let to_id = cell_ids[*to];
                let from_balance = ledger.get(&from_id).unwrap().state.balance();
                if from_balance < *amount {
                    continue;
                }
                ledger.apply_delta(&LedgerDelta {
                    created: Vec::new(),
                    updated: Vec::new(),
                    computron_transfers: vec![(from_id, to_id, *amount)],
                })
            }
            FuzzEffect::SetField { cell, index, value } => {
                let cell_id = cell_ids[*cell];
                ledger.apply_delta(&LedgerDelta {
                    created: Vec::new(),
                    updated: vec![(
                        cell_id,
                        CellStateDelta {
                            field_updates: vec![(*index, *value)],
                            nonce_increment: false,
                            balance_change: 0,
                            permission_changes: None,
                            capability_grants: Vec::new(),
                            capability_revocations: Vec::new(),
                        },
                    )],
                    computron_transfers: Vec::new(),
                })
            }
            FuzzEffect::IncrementNonce { cell } => {
                let cell_id = cell_ids[*cell];
                ledger.apply_delta(&LedgerDelta {
                    created: Vec::new(),
                    updated: vec![(
                        cell_id,
                        CellStateDelta {
                            field_updates: Vec::new(),
                            nonce_increment: true,
                            balance_change: 0,
                            permission_changes: None,
                            capability_grants: Vec::new(),
                            capability_revocations: Vec::new(),
                        },
                    )],
                    computron_transfers: Vec::new(),
                })
            }
            FuzzEffect::CreateCell { balance } => {
                let pk = rng.gen_bytes();
                let token_id = rng.gen_bytes();
                let mut cell = Cell::new_hosted(pk, token_id);
                cell.state.set_balance(*balance);
                expected_total += *balance;
                let id = ledger.insert_cell(cell).unwrap();
                cell_ids.push(id);
                Ok(())
            }
            FuzzEffect::BalanceChange { cell, delta } => {
                if *delta <= 0 {
                    continue;
                }
                let cell_id = cell_ids[*cell];
                expected_total += *delta as u64;
                ledger.apply_delta(&LedgerDelta {
                    created: Vec::new(),
                    updated: vec![(
                        cell_id,
                        CellStateDelta {
                            field_updates: Vec::new(),
                            nonce_increment: false,
                            balance_change: *delta,
                            permission_changes: None,
                            capability_grants: Vec::new(),
                            capability_revocations: Vec::new(),
                        },
                    )],
                    computron_transfers: Vec::new(),
                })
            }
        };

        if result.is_ok() {
            successful_turns += 1;
            assert_conservation_invariant(&ledger, expected_total);
            assert_nonce_monotonicity(&ledger, &mut observed_nonces);
        }
    }

    // Ensure we actually tested something meaningful.
    assert!(
        successful_turns > 50,
        "Too few successful turns ({}); test is not exercising the system",
        successful_turns,
    );
}
