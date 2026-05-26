//! Cell lifecycle checks: hosted, sovereign, factory creation.

use dregg_cell::{Cell, CellId, CellMode, Ledger};

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("hosted", check_hosted_cell),
        run_check("sovereign", check_sovereign_cell),
    ]
}

fn check_hosted_cell() -> Result<(), String> {
    let mut ledger = Ledger::new();
    let key = *blake3::hash(b"hosted-cell-owner").as_bytes();
    let token_id = [0u8; 32];

    let cell = Cell::with_balance(key, token_id, 1000);
    let id = cell.id();

    // Verify cell starts in hosted mode
    if cell.mode != CellMode::Hosted {
        return Err(format!("expected Hosted mode, got {:?}", cell.mode));
    }

    ledger.insert_cell(cell).map_err(|e| format!("{e:?}"))?;

    // Verify cell is in ledger
    let retrieved = ledger.get(&id).ok_or("cell not found in ledger")?;
    if retrieved.state.balance() != 1000 {
        return Err(format!(
            "expected balance 1000, got {}",
            retrieved.state.balance()
        ));
    }

    Ok(())
}

fn check_sovereign_cell() -> Result<(), String> {
    let mut ledger = Ledger::new();
    let key = *blake3::hash(b"sovereign-cell-owner").as_bytes();
    let token_id = [0u8; 32];

    let cell_id = CellId::derive_raw(&key, &token_id);

    // Register sovereign commitment directly
    let commitment = *blake3::hash(b"sovereign-state-commitment").as_bytes();
    ledger
        .register_sovereign_cell(cell_id, commitment)
        .map_err(|e| format!("{e:?}"))?;

    // Verify cell is sovereign
    if !ledger.is_sovereign(&cell_id) {
        return Err("cell should be sovereign after registration".into());
    }

    // Verify commitment stored
    let stored = ledger
        .get_sovereign_commitment(&cell_id)
        .ok_or("no sovereign commitment")?;
    if *stored != commitment {
        return Err("sovereign commitment mismatch".into());
    }

    Ok(())
}
