//! Bridge checks: Mina state advance submission + verification, EVM interface (if available).

use dregg_bridge::mina::{
    MinaBridgeState, StateAdvance, submit_state_advance, verify_mina_inclusion,
};

use crate::report::{CheckResult, run_check};

pub fn run() -> Vec<CheckResult> {
    vec![
        run_check("mina_state_advance", check_mina_state_advance),
        run_check("mina_verification", check_mina_verification),
    ]
}

fn check_mina_state_advance() -> Result<(), String> {
    // Create a bridge state with genesis root.
    let genesis_root = *blake3::hash(b"dregg-genesis-state").as_bytes();
    let mut state = MinaBridgeState::new(genesis_root);

    // Verify initial state.
    if state.proven_root != genesis_root {
        return Err("initial proven_root should match genesis".into());
    }
    if state.proven_height != 0 {
        return Err("initial proven_height should be 0".into());
    }

    // Create a state advance.
    let new_root = *blake3::hash(b"dregg-state-at-height-1").as_bytes();
    let advance = StateAdvance {
        old_root: genesis_root,
        new_root,
        height: 1,
        stark_proof: vec![0xAA; 64], // mock proof data
        pickles_proof: None,         // not yet wrapped for Mina
        submitted_at: None,
    };

    // Submit the state advance.
    let _ = submit_state_advance(&mut state, advance.clone());

    // Verify it's pending.
    if state.pending_advances.is_empty() {
        return Err("state advance should be in pending_advances".into());
    }
    if state.pending_advances[0].height != 1 {
        return Err("pending advance should have height 1".into());
    }
    if state.pending_advances[0].old_root != genesis_root {
        return Err("pending advance old_root should match genesis".into());
    }
    if state.pending_advances[0].new_root != new_root {
        return Err("pending advance new_root should match target".into());
    }

    Ok(())
}

fn check_mina_verification() -> Result<(), String> {
    // Test the inclusion verification path.
    let genesis_root = *blake3::hash(b"mina-verify-genesis").as_bytes();
    let state = MinaBridgeState::new(genesis_root);

    // Height 0 should be verifiable (it's the genesis).
    // verify_mina_inclusion checks if a given height has been proven.
    let result = verify_mina_inclusion(&state, 0);
    // At height 0 with genesis, the proven_height is 0, so inclusion should pass.
    if !result {
        return Err("genesis height 0 should be verifiable".into());
    }

    // Height 1 should NOT be verifiable (no advance confirmed yet).
    let result = verify_mina_inclusion(&state, 1);
    if result {
        return Err("unproven height 1 should not be verifiable".into());
    }

    Ok(())
}
