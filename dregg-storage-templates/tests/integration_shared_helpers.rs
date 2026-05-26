//! Cross-template integration test: shared scaffolding patterns + factory
//! descriptor contract verifications.
//!
//! The five templates share an identical high-level scaffold:
//!   - a `<name>_factory_descriptor()` that is deterministically hashable.
//!   - a `child_program_vk` that equals `canonical_program_vk(<name>_program())`.
//!   - a `CellProgram::Cases` with at least one `Always` case + one `MethodIs` case
//!     per operation.
//!   - `ChildVkStrategy::Fixed(Some(…))` or `Derived { param_hash }` binding the VK.
//!   - A stable set of `Immutable` constraints on identity slots.
//!
//! Rather than repeating identical assertions 5× in separate modules, this file
//! extracts the shared helper as a generic function applied to all five
//! templates in parameterized sub-tests. This is the "dedup / helper extraction"
//! deliverable.

use dregg_app_framework::canonical_program_vk;
use dregg_cell::StateConstraint;
use dregg_cell::program::{CellProgram, TransitionGuard};
use dregg_storage_templates::{
    all_storage_template_descriptors, blinded_queue, cap_inbox, programmable_queue, pubsub_topic,
    relay_operator,
};

// ── shared assertion helper (the dedup target) ───────────────────────────────

/// Assert the universal contract every storage-template factory descriptor must satisfy.
///
/// This replaces the formerly-5x-repeated pattern:
/// ```rust
/// let h1 = xxx_factory_descriptor().hash();
/// let h2 = xxx_factory_descriptor().hash();
/// assert_eq!(h1, h2);
/// assert_eq!(d.child_program_vk, Some(xxx_child_program_vk()));
/// assert_eq!(canonical_program_vk(&xxx_program()), xxx_child_program_vk());
/// ```
fn assert_descriptor_contract(
    descriptor: &dregg_app_framework::FactoryDescriptor,
    expected_child_vk: [u8; 32],
    program: &CellProgram,
    template_name: &str,
) {
    // 1. Hash is deterministic.
    let h1 = descriptor.hash();
    let h2 = descriptor.hash();
    assert_eq!(
        h1, h2,
        "{template_name}: descriptor.hash() must be deterministic"
    );

    // 2. child_program_vk matches the canonical VK derived from the program.
    let canonical = canonical_program_vk(program);
    assert_eq!(
        canonical, expected_child_vk,
        "{template_name}: canonical_program_vk(program) must match child_program_vk()"
    );
    assert_eq!(
        descriptor.child_program_vk,
        Some(expected_child_vk),
        "{template_name}: descriptor.child_program_vk must equal child_program_vk()"
    );

    // 3. ChildVkStrategy is set (Fixed or Derived — not None).
    assert!(
        descriptor.child_vk_strategy.is_some(),
        "{template_name}: child_vk_strategy must be set (not None)"
    );

    // 4. Program is CellProgram::Cases.
    assert!(
        matches!(program, CellProgram::Cases(_)),
        "{template_name}: program must be CellProgram::Cases"
    );

    // 5. At least one Always case exists.
    if let CellProgram::Cases(cases) = program {
        let has_always = cases
            .iter()
            .any(|c| matches!(c.guard, TransitionGuard::Always));
        assert!(
            has_always,
            "{template_name}: program must have at least one Always case for lifetime invariants"
        );
    }

    // 6. creation_budget is set (every template has an epoch budget).
    assert!(
        descriptor.creation_budget.is_some(),
        "{template_name}: creation_budget must be set"
    );
    assert!(
        descriptor.creation_budget.unwrap() > 0,
        "{template_name}: creation_budget must be > 0"
    );

    // 7. At least one allowed_cap_template exists.
    assert!(
        !descriptor.allowed_cap_templates.is_empty(),
        "{template_name}: allowed_cap_templates must not be empty"
    );

    // 8. factory_vk is non-zero.
    assert_ne!(
        descriptor.factory_vk, [0u8; 32],
        "{template_name}: factory_vk must be non-zero"
    );
}

fn assert_flat_descriptor_does_not_order_roots(
    descriptor: &dregg_app_framework::FactoryDescriptor,
    template_name: &str,
    root_slots: &[u8],
) {
    for constraint in &descriptor.state_constraints {
        match constraint {
            StateConstraint::Monotonic { index } | StateConstraint::StrictMonotonic { index }
                if root_slots.contains(index) =>
            {
                panic!(
                    "{template_name}: root slot {index} must be treated as an opaque commitment, not an ordered counter"
                );
            }
            StateConstraint::MonotonicSequence { seq_index } if root_slots.contains(seq_index) => {
                panic!("{template_name}: root slot {seq_index} must not use MonotonicSequence");
            }
            _ => {}
        }
    }
}

fn assert_flat_descriptor_has_no_method_scoped_sequence(
    descriptor: &dregg_app_framework::FactoryDescriptor,
    template_name: &str,
) {
    assert!(
        descriptor
            .state_constraints
            .iter()
            .all(|c| !matches!(c, StateConstraint::MonotonicSequence { .. })),
        "{template_name}: exact +1 sequence checks belong in CellProgram::Cases, not flat descriptor constraints"
    );
}

fn assert_method_case_has_sequence(
    program: &CellProgram,
    template_name: &str,
    method_name: &str,
    slot: u8,
) {
    let CellProgram::Cases(cases) = program else {
        panic!("{template_name}: expected CellProgram::Cases");
    };
    let method = dregg_app_framework::symbol(method_name);
    let case = cases
        .iter()
        .find(|case| matches!(&case.guard, TransitionGuard::MethodIs { method: m } if *m == method))
        .unwrap_or_else(|| panic!("{template_name}: missing method case {method_name}"));
    assert!(
        case.constraints.iter().any(
            |c| matches!(c, StateConstraint::MonotonicSequence { seq_index } if *seq_index == slot)
        ),
        "{template_name}: {method_name} must enforce MonotonicSequence on slot {slot}"
    );
}

// ── per-template contract application ────────────────────────────────────────

#[test]
fn cap_inbox_descriptor_contract() {
    let d = cap_inbox::cap_inbox_factory_descriptor();
    let vk = cap_inbox::cap_inbox_child_program_vk();
    let prog = cap_inbox::cap_inbox_program();
    assert_descriptor_contract(&d, vk, &prog, "CapInbox");
}

#[test]
fn programmable_queue_descriptor_contract() {
    let d = programmable_queue::programmable_queue_factory_descriptor();
    let vk = programmable_queue::programmable_queue_child_program_vk();
    let prog = programmable_queue::programmable_queue_program();
    assert_descriptor_contract(&d, vk, &prog, "ProgrammableQueue");
}

#[test]
fn pubsub_topic_descriptor_contract() {
    let d = pubsub_topic::pubsub_topic_factory_descriptor();
    let vk = pubsub_topic::pubsub_topic_child_program_vk();
    let prog = pubsub_topic::pubsub_topic_program();
    assert_descriptor_contract(&d, vk, &prog, "PubSubTopic");
}

#[test]
fn blinded_queue_descriptor_contract() {
    let d = blinded_queue::blinded_queue_factory_descriptor();
    let vk = blinded_queue::blinded_queue_child_program_vk();
    let prog = blinded_queue::blinded_queue_program();
    assert_descriptor_contract(&d, vk, &prog, "BlindedQueue");
}

#[test]
fn relay_operator_descriptor_contract() {
    let d = relay_operator::relay_operator_factory_descriptor();
    let vk = relay_operator::relay_operator_child_program_vk();
    let prog = relay_operator::relay_operator_program();
    assert_descriptor_contract(&d, vk, &prog, "RelayOperator");
}

// ── cross-template invariants ─────────────────────────────────────────────────

#[test]
fn all_five_factory_vks_are_distinct() {
    let all = all_storage_template_descriptors();
    let vks: Vec<[u8; 32]> = all.iter().map(|d| d.factory_vk).collect();
    for (i, vi) in vks.iter().enumerate() {
        for (j, vj) in vks.iter().enumerate() {
            if i != j {
                assert_ne!(
                    vi, vj,
                    "templates #{i} and #{j} must have distinct factory_vks"
                );
            }
        }
    }
}

#[test]
fn all_five_child_program_vks_are_distinct() {
    let all = all_storage_template_descriptors();
    let child_vks: Vec<[u8; 32]> = all.iter().filter_map(|d| d.child_program_vk).collect();
    assert_eq!(
        child_vks.len(),
        5,
        "all 5 templates must declare a child_program_vk"
    );
    for (i, vi) in child_vks.iter().enumerate() {
        for (j, vj) in child_vks.iter().enumerate() {
            if i != j {
                assert_ne!(
                    vi, vj,
                    "templates #{i} and #{j} must have distinct child_program_vks"
                );
            }
        }
    }
}

#[test]
fn every_template_has_immutable_identity_slot() {
    // Every template must have at least one Immutable constraint on an
    // identity/ownership slot. This is the cross-template version of the
    // "owner/consumer_pk cannot be overwritten" property.
    let programs = vec![
        ("CapInbox", cap_inbox::cap_inbox_program()),
        (
            "ProgrammableQueue",
            programmable_queue::programmable_queue_program(),
        ),
        ("PubSubTopic", pubsub_topic::pubsub_topic_program()),
        ("BlindedQueue", blinded_queue::blinded_queue_program()),
        ("RelayOperator", relay_operator::relay_operator_program()),
    ];

    for (name, prog) in programs {
        let has_immutable = if let CellProgram::Cases(cases) = &prog {
            cases.iter().any(|c| {
                c.constraints
                    .iter()
                    .any(|x| matches!(x, StateConstraint::Immutable { .. }))
            })
        } else {
            false
        };
        assert!(
            has_immutable,
            "{name}: program must declare at least one Immutable constraint"
        );
    }
}

#[test]
fn flat_descriptor_constraints_do_not_order_opaque_roots() {
    let cases = vec![
        (
            "CapInbox",
            cap_inbox::cap_inbox_factory_descriptor(),
            vec![
                cap_inbox::SENDER_SET_ROOT_SLOT,
                cap_inbox::MESSAGE_ROOT_SLOT,
            ],
        ),
        (
            "ProgrammableQueue",
            programmable_queue::programmable_queue_factory_descriptor(),
            vec![
                programmable_queue::SENDER_SET_ROOT_SLOT,
                programmable_queue::CONTENT_PATTERN_ROOT_SLOT,
                programmable_queue::RING_ROOT_SLOT,
            ],
        ),
        (
            "PubSubTopic",
            pubsub_topic::pubsub_topic_factory_descriptor(),
            vec![
                pubsub_topic::SUBSCRIBER_CURSORS_ROOT_SLOT,
                pubsub_topic::SUBSCRIBER_SET_ROOT_SLOT,
                pubsub_topic::EVENT_ROOT_SLOT,
                pubsub_topic::TOPIC_FILTER_ROOT_SLOT,
                pubsub_topic::DEDUP_ROOT_SLOT,
            ],
        ),
        (
            "BlindedQueue",
            blinded_queue::blinded_queue_factory_descriptor(),
            vec![
                blinded_queue::COMMITMENTS_ROOT_SLOT,
                blinded_queue::NULLIFIER_ROOT_SLOT,
            ],
        ),
        (
            "RelayOperator",
            relay_operator::relay_operator_factory_descriptor(),
            vec![
                relay_operator::HOSTED_INBOX_ROOT_SLOT,
                relay_operator::ROUTE_TABLE_ROOT_SLOT,
            ],
        ),
    ];

    for (name, descriptor, root_slots) in cases {
        assert_flat_descriptor_does_not_order_roots(&descriptor, name, &root_slots);
    }
}

#[test]
fn exact_sequence_checks_are_operation_scoped_cases() {
    let cap_inbox_descriptor = cap_inbox::cap_inbox_factory_descriptor();
    assert_flat_descriptor_has_no_method_scoped_sequence(&cap_inbox_descriptor, "CapInbox");
    let cap_inbox_program = cap_inbox::cap_inbox_program();
    assert_method_case_has_sequence(
        &cap_inbox_program,
        "CapInbox",
        "send",
        cap_inbox::HEAD_SEQ_SLOT,
    );
    assert_method_case_has_sequence(
        &cap_inbox_program,
        "CapInbox",
        "dequeue",
        cap_inbox::TAIL_SEQ_SLOT,
    );

    let programmable_queue_descriptor = programmable_queue::programmable_queue_factory_descriptor();
    assert_flat_descriptor_has_no_method_scoped_sequence(
        &programmable_queue_descriptor,
        "ProgrammableQueue",
    );
    let programmable_queue_program = programmable_queue::programmable_queue_program();
    assert_method_case_has_sequence(
        &programmable_queue_program,
        "ProgrammableQueue",
        "enqueue",
        programmable_queue::HEAD_SEQ_SLOT,
    );
    assert_method_case_has_sequence(
        &programmable_queue_program,
        "ProgrammableQueue",
        "dequeue",
        programmable_queue::TAIL_SEQ_SLOT,
    );

    let pubsub_descriptor = pubsub_topic::pubsub_topic_factory_descriptor();
    assert_flat_descriptor_has_no_method_scoped_sequence(&pubsub_descriptor, "PubSubTopic");
    let pubsub_program = pubsub_topic::pubsub_topic_program();
    assert_method_case_has_sequence(
        &pubsub_program,
        "PubSubTopic",
        "publish",
        pubsub_topic::HEAD_SEQ_SLOT,
    );

    let blinded_descriptor = blinded_queue::blinded_queue_factory_descriptor();
    assert_flat_descriptor_has_no_method_scoped_sequence(&blinded_descriptor, "BlindedQueue");
    let blinded_program = blinded_queue::blinded_queue_program();
    assert_method_case_has_sequence(
        &blinded_program,
        "BlindedQueue",
        "add",
        blinded_queue::COMMITMENT_COUNT_SLOT,
    );
    assert_method_case_has_sequence(
        &blinded_program,
        "BlindedQueue",
        "consume",
        blinded_queue::NULLIFIER_COUNT_SLOT,
    );

    let relay_descriptor = relay_operator::relay_operator_factory_descriptor();
    assert_flat_descriptor_has_no_method_scoped_sequence(&relay_descriptor, "RelayOperator");
}

#[test]
fn programmable_queue_param_hash_changes_with_config() {
    // Verify the `ProgrammableQueueConfig::param_hash` method produces
    // different values for different constraint sets — ensuring that
    // distinct factory configurations produce distinct child VKs.
    use programmable_queue::ProgrammableQueueConfig;

    let c1 = ProgrammableQueueConfig::work_queue_default(8);
    let c2 = ProgrammableQueueConfig::work_queue_default(16);
    // Different capacity → different param_hash.
    assert_ne!(
        c1.param_hash(),
        c2.param_hash(),
        "different capacities must produce different param_hashes"
    );

    // Same capacity → same hash (deterministic).
    let c3 = ProgrammableQueueConfig::work_queue_default(8);
    assert_eq!(
        c1.param_hash(),
        c3.param_hash(),
        "identical configs must produce identical param_hashes"
    );
}

#[test]
fn blinded_queue_sovereign_vs_hosted_only_mode_differs() {
    let hosted = blinded_queue::blinded_queue_factory_descriptor();
    let sovereign = blinded_queue::blinded_queue_factory_descriptor_sovereign();

    // Only `default_mode` should differ.
    assert_ne!(hosted.default_mode, sovereign.default_mode);
    assert_eq!(hosted.factory_vk, sovereign.factory_vk);
    assert_eq!(hosted.child_program_vk, sovereign.child_program_vk);
    assert_eq!(hosted.state_constraints, sovereign.state_constraints);
    assert_eq!(hosted.field_constraints, sovereign.field_constraints);
    assert_eq!(hosted.creation_budget, sovereign.creation_budget);
}
