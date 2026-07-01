//! # THE DEPLOYED BRIDGE-MINT PAYMENT-BINDING TOOTH (the RIGHT 26-felt design, end-to-end).
//!
//! The bridge twin of `custom_binding_deployed_tooth.rs`: a real `BridgeMint` turn is minted on the
//! WIDENED narrow `mintVmDescriptor2R24` leg (855-wide / 72-PI) that PUBLISHES the bridge-action tuple
//! `(nullifier, recipient, dest_federation, amount)` at PI [46..72), folded through the DEPLOYED chain
//! prover (`prove_turn_chain_recursive` → `prove_chain_core_rotated`, the `bridge_witness` branch:
//! `prove_descriptor_leaf_dual_expose_at(46,26)` + `prove_bridge_leaf_tuple_claim` +
//! `prove_bridge_binding_node_segmented`), and verified by the light client
//! (`verify_turn_chain_recursive`). The ACTUAL payment fields are bound in the recursion tree a pure
//! light client folds — no compressed `mint_hash`, no hash-gadget seam.
//!
//! Real recursion (minutes), so `#[ignore]`. Run with:
//!   cargo test -p dregg-circuit-prove --test bridge_mint_deployed_tooth -- --ignored --nocapture

use dregg_circuit::bridge_action_air::BridgeActionWitness;
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, prove_turn_chain_recursive, verify_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::{
    BridgeWitnessBundle, DescriptorParticipant,
};
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

/// POSITIVE POLE — an honest `BridgeMint` turn whose widened leg publishes the tuple folds through the
/// DEPLOYED chain prover and the LIGHT CLIENT ACCEPTS: the payment fields are bound in the recursion
/// tree, witnessed by a pure light client.
#[test]
#[ignore = "SLOW: real deployed bridge-mint payment-binding recursion fold (~minutes); run with --ignored"]
fn deployed_bridge_mint_honest_accepts() {
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
    let bundle = BridgeWitnessBundle {
        public_inputs: b.public_inputs(),
        backing: b,
    };

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

    let turns = vec![FinalizedTurn::new(DescriptorParticipant::rotated(leg))];

    let whole = prove_turn_chain_recursive(&turns)
        .expect("the bridge-mint chain must fold through the deployed prover (bridge branch fires)");
    let vk = whole.root_vk_fingerprint();
    verify_turn_chain_recursive(&whole, &vk)
        .expect("the light client must ACCEPT the payment-bound whole-chain artifact");
    eprintln!(
        "DEPLOYED bridge-mint binding: honest payment tuple FOLDED + light-client VERIFIED (the \
         ACTUAL (nullifier, recipient, dest_federation, amount) bound in the recursion tree)."
    );
}
