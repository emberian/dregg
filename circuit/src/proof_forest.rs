//! Cutover-ready selector set for the proof-carrying effect-VM lane.
//!
//! The original bespoke-`EffectVmAir` proof FOREST (`ForestNode` / `ProofForest` /
//! `verify_forest` — the v1 Proof-Carrying-Data-minus-recursion realization of
//! `.docs-history-noclaude/rebuild/archived-2026-06-06/PHASE-PROOF-CARRYING.md`) is RETIRED with the v1 hand-AIR. The
//! recursion tower folds the rotated leaf in `crate::ivc_turn_chain` /
//! `crate::joint_turn_recursive` instead. What remains here is the shared
//! [`CUTOVER_READY_SELECTORS`] set the joint-turn aggregation reads.

/// The cutover-ready selectors whose descriptors the differential harness has
/// GRADUATED (descriptor ⟺ hand-AIR proven IDENTICAL on the real witness +
/// anti-ghost, AND each carries the Lean `selectorGate s` binding tooth). Mirror
/// of `sdk::full_turn_proof::CUTOVER_READY_SELECTORS` and the harness's
/// `descriptor_proof_binds_to_its_selector` cutover set.
pub const CUTOVER_READY_SELECTORS: &[usize] = &[
    crate::effect_vm::columns::sel::TRANSFER,
    crate::effect_vm::columns::sel::NOTE_SPEND,
    crate::effect_vm::columns::sel::NOTE_CREATE,
    crate::effect_vm::columns::sel::EMIT_EVENT,
    crate::effect_vm::columns::sel::BRIDGE_MINT,
    crate::effect_vm::columns::sel::BURN,
    crate::effect_vm::columns::sel::CELL_SEAL,
    crate::effect_vm::columns::sel::CELL_DESTROY,
    crate::effect_vm::columns::sel::REFUSAL,
    crate::effect_vm::columns::sel::SET_VERIFICATION_KEY,
    crate::effect_vm::columns::sel::SET_PERMISSIONS,
    crate::effect_vm::columns::sel::EXERCISE_VIA_CAPABILITY,
    crate::effect_vm::columns::sel::PIPELINED_SEND,
    crate::effect_vm::columns::sel::INCREMENT_NONCE,
    crate::effect_vm::columns::sel::REFRESH_DELEGATION,
    crate::effect_vm::columns::sel::REVOKE_DELEGATION,
    crate::effect_vm::columns::sel::INTRODUCE,
    // CUSTOM (8): bound in the recursion tree a pure light client folds. The leg carries a
    // `CustomWitnessBundle`; `ivc_turn_chain::prove_chain_core_rotated` folds the dual-expose leaf
    // against the re-proven custom sub-proof leaf via
    // `joint_turn_recursive::prove_custom_binding_node_segmented`, and a forged commitment makes the
    // aggregate UNSAT (`custom_binding_deployed_tooth.rs`, both poles). This is the UNIVERSAL
    // sub-proof-folding primitive — the same one bridge / factory / hatchery / DSL / membership /
    // sovereign-transition ride: every off-AIR carrier becomes a recursion-tree leaf so the light
    // client witnesses what a re-executing validator does. The production minters populate the
    // witness bundle from the turn's bound sub-proof.
    crate::effect_vm::columns::sel::CUSTOM,
    // CREATE_CELL_FROM_FACTORY (the v12 carrier epoch): the committed `factoryVmDescriptor2R24`
    // row is the STEP-3 `factoryV3Carriers` (child_vk8 PI 47..54 + contract_hash8 PI 55..62 +
    // the dsl rc tail), the producer emits the full 67-PI vector, and the recursion tower's
    // Factory/Hatchery fold arms (`ivc_turn_chain::prove_chain_core_rotated`) bind the octet
    // claims in-circuit (`{factory,hatchery}_binding_deployed_tooth.rs`, both poles). Admitting
    // the selector here lets the deployed joint/chain host gate accept the rotated factory leg
    // it re-verifies in-circuit anyway.
    crate::effect_vm::columns::sel::CREATE_CELL_FROM_FACTORY,
    // MAKE_SOVEREIGN (the v12 carrier epoch): the committed `makeSovereignVmDescriptor2R24` row
    // is live (record-pin8 + rc); the Sovereign fold arm binds the KEY_COMMIT claim pins
    // (`sovereign_binding_deployed_tooth.rs`). Same host-admission rationale as factory.
    crate::effect_vm::columns::sel::MAKE_SOVEREIGN,
    // SET_FIELD (2): graduated 2026-11-06 (initiative 10) so a grain session's legs, which are all
    // setField, can be admitted to the whole-history fold. The evidence the other members carry:
    // every per-slot member `setFieldVmDescriptor2-{0..7}R24` carries exactly ONE appended
    // `selectorGate SET_FIELD` (`effect_vm_selector_gate_forgery.rs`
    // `every_setfield_slot_member_carries_exactly_one_selector_gate`, both registries), the
    // foreign-selector-tail forgery is UNSAT under it with the gate as the sole refuser
    // (`foreign_selector_tail_is_refused_by_the_gate_alone`), and a real grain session folds
    // and a forged post-state does not (`grain-turn/tests/r3_grain_adapter.rs`). SetField is keyed
    // PER SLOT, so `joint_turn_aggregation::rotated_descriptor_selector` resolves it through
    // `rotated_set_field_descriptor_name` rather than the selector's own wire name.
    crate::effect_vm::columns::sel::SET_FIELD,
];
