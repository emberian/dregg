//! # THE DEPLOYED BRIDGE-MINT TUPLE PUBLICATION (the RIGHT 26-felt design, real proof).
//!
//! A real `BridgeMint` turn is minted on the WIDENED narrow `mintVmDescriptor2R24` leg (857-wide /
//! 72-PI). The leg's proof SELF-VERIFIES inside the minter, and this test asserts that its public
//! inputs PUBLISH the bridge-action tuple `(nullifier, recipient, dest_federation, amount)` at
//! PI [46..72) — the ACTUAL payment fields, not a compressed `mint_hash`. That is the RIGHT design's
//! load-bearing property: the deployed descriptor emits the tuple, verified by a genuine STARK proof.
//!
//! The per-turn FOLD that binds this into the recursion tree a light client folds — the
//! `bridge_witness` branch in `prove_chain_core_rotated` (`prove_descriptor_leaf_dual_expose_at(46,26)`
//! + `prove_bridge_leaf_tuple_claim` + `prove_bridge_binding_node_segmented`) — is exercised as a
//! mechanism by `bridge_binding_mechanism.rs` (honest + forged poles) and is a term-for-term mirror of
//! the deployed custom binding (`custom_binding_deployed_tooth.rs`). The full multi-turn deployed
//! chain-fold e2e needs a 2-turn chain whose narrow-path state roots (which include the nonce) link —
//! a test-harness continuity detail tracked as a follow-on.
//!
//! Real STARK prove, so `#[ignore]`. Run with:
//!   cargo test -p dregg-circuit-prove --test bridge_mint_deployed_tooth -- --ignored --nocapture

use dregg_circuit::bridge_action_air::BridgeActionWitness;
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::joint_turn_aggregation::BridgeWitnessBundle;
use dregg_turn::rotation_witness::mint_bridge_rotated_participant_leg;

fn open_permissions() -> dregg_cell::Permissions {
    use dregg_cell::AuthRequired;
    dregg_cell::Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn producer_cell(balance: i64, nonce: u64) -> dregg_cell::Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

/// A typed foreign-payment binding: distinct 32-byte nullifier/recipient/dest_federation and a value.
fn backing(amount: u64) -> BridgeActionWitness {
    BridgeActionWitness {
        nullifier: [0x11; 32],
        recipient: [0x22; 32],
        destination_federation: [0x33; 32],
        amount,
    }
}

/// The widened bridge-mint leg mints + self-verifies, and its real proof PUBLISHES the 26-felt
/// bridge-action tuple at PI [46..72) — the ACTUAL payment fields.
#[test]
#[ignore = "SLOW: real STARK prove of the widened bridge-mint leg (~seconds); run with --ignored"]
fn deployed_bridge_mint_leg_publishes_tuple() {
    let amount = 900u64;
    let state = CellState::new(1000, 0);
    let before_cell = producer_cell(1000, 0);
    let after_cell = producer_cell(1000 + amount as i64, 0);
    let effect = Effect::BridgeMint {
        value_lo: BabyBear::new(amount as u32),
        mint_hash: BabyBear::new(0x31D6),
        value_full: amount,
    };
    let b = backing(amount);
    let tuple = b.public_inputs(); // 26 felts: nullifier[8] ++ recipient[8] ++ dest_federation[8] ++ [lo, hi]
    let bundle = BridgeWitnessBundle {
        public_inputs: tuple.clone(),
        backing: b,
    };

    // Mints the widened mintVmDescriptor2R24 leg + SELF-VERIFIES the STARK inside the minter.
    let leg = mint_bridge_rotated_participant_leg(
        &state,
        &[effect],
        &before_cell,
        &after_cell,
        &[0u8; 32],
        &[0u8; 32],
        &[[1u8; 32], [2u8; 32]],
        None,
        bundle,
    )
    .expect("the widened bridge-mint leg mints + self-verifies (publishes the tuple at PI [46..72))");

    // The deployed descriptor is the WIDENED mintVmDescriptor2R24 (72 PIs).
    assert_eq!(
        leg.descriptor.public_input_count, 72,
        "the deployed bridge-mint descriptor publishes 72 PIs (46 rotated + 26 tuple)"
    );
    assert_eq!(leg.public_inputs.len(), 72, "the leg's PI vector carries 72 slots");

    // THE LOAD-BEARING PROPERTY: the leg's self-verified proof PUBLISHES the ACTUAL 26-felt tuple at
    // PI [46..72) — not a compressed mint_hash. A pure light client folding the tree reads these fields.
    assert_eq!(
        &leg.public_inputs[46..72],
        &tuple[..],
        "the widened leg publishes the (nullifier, recipient, dest_federation, amount) tuple at PI [46..72)"
    );

    eprintln!(
        "DEPLOYED bridge-mint: the widened leg's SELF-VERIFIED proof PUBLISHES the 26-felt payment \
         tuple (nullifier, recipient, dest_federation, amount) at PI [46..72) — the ACTUAL fields."
    );
}
