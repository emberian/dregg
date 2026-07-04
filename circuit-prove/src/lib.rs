//! `dregg-circuit-prove`: the HEAVY PROVE surface for dregg circuits.
//!
//! This crate is the prover-only half of the `dregg-circuit` split. It hosts the
//! items that need the three RECURSION-ONLY Plonky3 crates (`p3-recursion`,
//! `p3-circuit`, `p3-circuit-prover`) — the IVC turn chain, joint-turn recursive
//! aggregation, the recursive witness bundle, the custom proof-bind engine, the
//! effect-VM `p3-air` recursion bridge, the LogUp lookup AIR, and the shielded-
//! action prover.
//!
//! The VERIFY floor — descriptor parsing/verification (`verify_vm_descriptor2`),
//! the AIRs, the PI-reconstruction trace generators the executor needs, and the
//! prove_batch-based (recursion-free) provers — lives in [`dregg_circuit`]. That
//! partition is what keeps `cargo tree -p dregg-circuit` free of the recursion
//! prover: a verify-only consumer depends on `dregg-circuit` alone; a producer
//! depends on this crate.
//!
//! Everything here was previously `#[cfg(feature = "prover")]` inside
//! `dregg-circuit`; the gate is gone because this whole crate IS the prover.

pub mod accumulator;
pub mod bridge_leaf_adapter;
pub mod carrier_pin_twin;
pub mod custom_leaf_adapter;
pub mod custom_proof_bind;
pub mod deco_leaf_adapter;
pub mod dsl_leaf_adapter;
pub mod effect_vm_p3_air;
pub mod factory_leaf_adapter;
pub mod hatchery_leaf_adapter;
pub mod ivc_turn_chain;
pub mod joint_turn_aggregation;
pub mod joint_turn_recursive;
pub mod lean_lookup_air;
pub mod membership_leaf_adapter;
pub mod merge_pool;
pub mod note_spend_leaf_adapter;
pub mod plonky3_recursion_impl;
pub mod recursive_witness_bundle;
pub mod shielded;
pub mod sovereign_leaf_adapter;
