//! Cell lifecycle checks: hosted, sovereign, factory creation.

use pyana_cell::{
    Cell, CellId, CellMode, ChildVkStrategy, FactoryDescriptor, FactoryRegistry, FieldConstraint,
    Ledger,
};

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("hosted", check_hosted_cell),
        run_check("sovereign", check_sovereign_cell),
        run_check("factory", check_factory_cell),
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

fn check_factory_cell() -> Result<(), String> {
    let mut registry = FactoryRegistry::new();

    let factory_vk = *blake3::hash(b"factory-vk").as_bytes();
    let descriptor = FactoryDescriptor {
        factory_vk,
        child_program_vk: None,
        child_vk_strategy: Some(ChildVkStrategy::Derived {
            base_vk: factory_vk,
        }),
        allowed_cap_templates: vec![],
        field_constraints: vec![FieldConstraint::Range {
            field_index: 0,
            min: 0,
            max: 1000,
        }],
        state_constraints: vec![],
        default_mode: CellMode::Hosted,
        creation_budget: Some(100),
    };

    let deployed_vk = registry.deploy(descriptor);
    if deployed_vk != factory_vk {
        return Err("deployed VK should match descriptor".into());
    }

    // Verify factory is registered
    let retrieved = registry.get(&factory_vk).ok_or("factory not in registry")?;
    if retrieved.factory_vk != factory_vk {
        return Err("factory VK mismatch in registry".into());
    }

    // Record a creation
    registry
        .record_creation(&factory_vk)
        .map_err(|e| format!("{e:?}"))?;

    // Verify VK derivation for child
    let params_hash = *blake3::hash(b"child-params").as_bytes();
    let child_vk = ChildVkStrategy::derive_child_vk(&factory_vk, &params_hash);
    if child_vk == factory_vk {
        return Err("child VK should differ from factory VK".into());
    }
    if child_vk == [0u8; 32] {
        return Err("child VK should not be zero".into());
    }

    Ok(())
}
