//! Boot checks: verify the DreggEngine starts and is operational.

use dregg_sdk::{DreggEngine, EngineConfig};

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![run_check("height_advances", check_height_advances)]
}

fn check_height_advances() -> Result<(), String> {
    let mut engine = DreggEngine::new(EngineConfig::for_testing());
    engine.set_block_height(0);

    // Simulate block advancement
    engine.set_block_height(1);
    engine.set_block_height(2);
    engine.set_block_height(3);

    // Verify via executor
    if engine.executor().block_height != 3 {
        return Err(format!(
            "expected block height 3, got {}",
            engine.executor().block_height
        ));
    }
    Ok(())
}
