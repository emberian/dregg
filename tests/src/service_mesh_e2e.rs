//! End-to-end service mesh integration tests.
//!
//! Tests the full service mesh pipeline:
//! 1. ContentStore: nameless write -> verify hash = address (CAS)
//! 2. Splice: modify blob -> verify new hash, old hash nullified
//! 3. Mount service entry: CAS -> resolve -> get back sturdy ref
//! 4. Governance vote -> route table changes -> verify new commitment
//!
//! All operations are proven via the Effect VM STARK. No mocks.

use dregg_circuit::effect_vm::{
    self, CellState, Effect, EffectVmAir, EffectVmContext, compute_effects_hash_4,
    extract_net_delta, generate_effect_vm_trace, generate_effect_vm_trace_ext,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::{hash_2_to_1, hash_4_to_1, hash_many};
use dregg_circuit::stark::{self, StarkProof};

// =============================================================================
// Content-Addressable Store (CAS) Primitives
// =============================================================================

/// Compute the content address (hash) of a blob.
/// In the circuit, content is represented as a sequence of BabyBear elements.
fn content_address(data: &[BabyBear]) -> BabyBear {
    hash_many(data)
}

/// Compute a nullifier for a content address (proves the old content was consumed/replaced).
fn content_nullifier(address: BabyBear, owner_key: BabyBear) -> BabyBear {
    hash_2_to_1(address, owner_key)
}

/// Compute a service entry commitment: hash(service_name, content_address, version).
fn service_entry_commitment(
    service_name: BabyBear,
    content_address: BabyBear,
    version: u32,
) -> BabyBear {
    hash_4_to_1(&[
        service_name,
        content_address,
        BabyBear::new(version),
        BabyBear::ZERO,
    ])
}

/// Compute a governance vote commitment: hash(voter, proposal_hash, vote_weight).
fn vote_commitment(voter: BabyBear, proposal: BabyBear, weight: u32) -> BabyBear {
    hash_4_to_1(&[voter, proposal, BabyBear::new(weight), BabyBear::ZERO])
}

// =============================================================================
// Helper
// =============================================================================

/// Prove effects and return the STARK proof.
fn prove_effects(initial_state: &CellState, effects: &[Effect]) -> StarkProof {
    let mut ctx = EffectVmContext::default();
    ctx.actor_nonce = initial_state.nonce as u64;
    prove_effects_ext(initial_state, effects, ctx)
}

/// Prove effects with an explicit context and return the STARK proof.
fn prove_effects_ext(
    initial_state: &CellState,
    effects: &[Effect],
    ctx: EffectVmContext,
) -> StarkProof {
    let (trace, public_inputs) = generate_effect_vm_trace_ext(initial_state, effects, ctx);
    let air = EffectVmAir::new(trace.len());
    let proof = stark::prove(&air, &trace, &public_inputs);
    let result = stark::verify(&air, &proof, &public_inputs);
    assert!(
        result.is_ok(),
        "STARK verification failed: {:?}",
        result.err()
    );
    proof
}

// =============================================================================
// Test 1: ContentStore — nameless write -> verify hash = address
// =============================================================================

/// Write content to the store (content-addressed). The "address" is the
/// Poseidon2 hash of the content. Prove via STARK that the stored commitment
/// matches the content hash.
#[test]
fn test_content_store_nameless_write() {
    // Simulate writing a blob: content = [0x48, 0x65, 0x6C, 0x6C, 0x6F] ("Hello" as field elements)
    let content: Vec<BabyBear> = vec![
        BabyBear::new(0x48),
        BabyBear::new(0x65),
        BabyBear::new(0x6C),
        BabyBear::new(0x6C),
        BabyBear::new(0x6F),
    ];
    let address = content_address(&content);

    // The content store records: field[0] = content_address (the CAS key).
    // We prove this write via a SetField effect.
    let initial_state = CellState::new(1000, 0);

    let effects = vec![Effect::SetField {
        field_idx: 0,
        value: address,
    }];

    let (trace, _public_inputs) = generate_effect_vm_trace(&initial_state, &effects);

    // Verify the content address is correctly stored.
    let row = &trace[0];
    let stored_value = row[effect_vm::STATE_AFTER_BASE + effect_vm::state::FIELD_BASE + 0];
    assert_eq!(
        stored_value, address,
        "Stored value should equal content hash (CAS property)"
    );

    // Verify content-addressability: same content always produces same address.
    let content2 = content.clone();
    let address2 = content_address(&content2);
    assert_eq!(address, address2, "CAS: same content -> same address");

    // Different content -> different address.
    let different_content = vec![
        BabyBear::new(0x42),
        BabyBear::new(0x79),
        BabyBear::new(0x65),
    ];
    let different_address = content_address(&different_content);
    assert_ne!(
        address, different_address,
        "CAS: different content -> different address"
    );

    // Prove and verify via STARK.
    let proof = prove_effects(&initial_state, &effects);
    assert!(proof.trace_len >= 2);
    assert!(!proof.query_proofs.is_empty());
}

// =============================================================================
// Test 2: Splice — modify blob -> verify new hash, old hash nullified
// =============================================================================

/// Splice a content blob: write new content, nullify old content address.
/// Proves:
///   - New content address is correctly computed
///   - Old content address is nullified (via nullifier derivation)
///   - Both operations happen atomically in one STARK proof
#[test]
fn test_content_splice_nullifies_old() {
    let owner_key = BabyBear::new(0xCAFE_BABE);

    // Original content and its address.
    let old_content = vec![BabyBear::new(1), BabyBear::new(2), BabyBear::new(3)];
    let old_address = content_address(&old_content);

    // New content (spliced) and its address.
    let new_content = vec![
        BabyBear::new(1),
        BabyBear::new(2),
        BabyBear::new(99), // changed byte
    ];
    let new_address = content_address(&new_content);
    assert_ne!(old_address, new_address, "splice should change address");

    // Compute nullifier for the old content (proves old was consumed).
    let nullifier = content_nullifier(old_address, owner_key);

    // Initial state: field[0] = old_address (content store), field[1] = 0 (no nullifier yet).
    let mut initial_state = CellState::new(5000, 0);
    initial_state.fields[0] = old_address;
    initial_state.refresh_commitment();

    // Splice = two effects:
    //   1. SetField[0] = new_address (update content)
    //   2. SetField[1] = nullifier (record that old was consumed)
    let effects = vec![
        Effect::SetField {
            field_idx: 0,
            value: new_address,
        },
        Effect::SetField {
            field_idx: 1,
            value: nullifier,
        },
    ];

    let (trace, public_inputs) = generate_effect_vm_trace(&initial_state, &effects);

    // After effect 1 (row 0): field[0] = new_address.
    let row0 = &trace[0];
    let after_splice_field0 = row0[effect_vm::STATE_AFTER_BASE + effect_vm::state::FIELD_BASE + 0];
    assert_eq!(
        after_splice_field0, new_address,
        "field[0] should be updated to new content address"
    );

    // After effect 2 (row 1): field[1] = nullifier.
    let row1 = &trace[1];
    let after_nullify_field1 = row1[effect_vm::STATE_AFTER_BASE + effect_vm::state::FIELD_BASE + 1];
    assert_eq!(
        after_nullify_field1, nullifier,
        "field[1] should contain the nullifier of old content"
    );

    // Verify nullifier binds to old_address: nullifier = hash(old_address, owner_key).
    let recomputed_nullifier = hash_2_to_1(old_address, owner_key);
    assert_eq!(
        nullifier, recomputed_nullifier,
        "nullifier should be deterministically derived from old address + owner"
    );

    // Prove atomically with single STARK.
    let proof = prove_effects(&initial_state, &effects);
    assert!(proof.trace_len >= 2);

    // The old_commitment != new_commitment (state changed).
    assert_ne!(
        public_inputs[0], public_inputs[1],
        "state commitment should change after splice"
    );
}

// =============================================================================
// Test 3: Mount service entry with CAS -> resolve -> get sturdy ref
// =============================================================================

/// Mount a service entry in the CAS namespace, then prove the resolution
/// yields a sturdy ref (via ExportSturdyRef). The sequence:
///   1. SetField[0] = service_entry_commitment (mounts the service)
///   2. ExportSturdyRef (exports the service cell as a sturdy ref)
///
/// A resolver can then look up the service entry, verify the proof,
/// and obtain the swiss number for enlivening.
#[test]
fn test_mount_service_entry_and_export() {
    let service_name = BabyBear::new(0x53_56_43); // "SVC"
    let blob_content = vec![
        BabyBear::new(0x77),
        BabyBear::new(0x61),
        BabyBear::new(0x73),
        BabyBear::new(0x6D),
    ];
    let blob_address = content_address(&blob_content);

    // Service entry: binds name + content address + version.
    let version = 1u32;
    let entry_commitment = service_entry_commitment(service_name, blob_address, version);

    // Cell state: this is the service registry cell.
    let initial_state = CellState::new(20_000, 0);

    let cell_id = BabyBear::new(0x5E12);
    let permissions = BabyBear::new(0x01); // read-only
    let random_seed = BabyBear::new(0xABCD);
    let export_counter = 0u32;

    let effects = vec![
        // Step 1: Mount service entry (store the commitment in field[0]).
        Effect::SetField {
            field_idx: 0,
            value: entry_commitment,
        },
        // Step 2: Export the service cell as a sturdy ref.
        Effect::ExportSturdyRef {
            cell_id,
            permissions,
            random_seed,
            export_counter,
        },
    ];

    let (trace, _public_inputs) = generate_effect_vm_trace(&initial_state, &effects);

    // Verify: field[0] = service_entry_commitment after mount.
    let mount_row = &trace[0];
    let mounted = mount_row[effect_vm::STATE_AFTER_BASE + effect_vm::state::FIELD_BASE + 0];
    assert_eq!(
        mounted, entry_commitment,
        "service entry should be mounted in field[0]"
    );

    // Verify: export produced correct swiss number.
    let export_row = &trace[1];
    let swiss_aux = export_row[effect_vm::AUX_BASE + 0];
    let inner_hash = hash_2_to_1(random_seed, BabyBear::new(export_counter));
    let expected_swiss = hash_2_to_1(cell_id, inner_hash);
    assert_eq!(
        swiss_aux, expected_swiss,
        "exported swiss number should be derivable from cell_id + seed + counter"
    );

    // Verify: field[7] (export counter) incremented.
    let post_export_f7 = export_row[effect_vm::STATE_AFTER_BASE + effect_vm::state::FIELD_BASE + 7];
    assert_eq!(
        post_export_f7,
        BabyBear::ONE,
        "export counter should be 1 after first export"
    );

    // Prove and verify the combined mount+export as single STARK.
    let proof = prove_effects(&initial_state, &effects);
    assert!(proof.trace_len >= 2);

    // A resolver can verify:
    // 1. The proof is valid (STARK verification passes)
    // 2. The service_entry_commitment in field[0] matches the expected service
    // 3. The swiss number in the proof binds to the exported cell
    // This constitutes a verifiable resolution from service name to capability.
}

// =============================================================================
// Test 4: Governance vote -> route table changes -> verify new commitment
// =============================================================================

/// Simulate a governance vote that updates the routing table:
///   1. Record vote commitment in cell state (via SetField)
///   2. After quorum: update route table commitment (via SetField)
///   3. Validate the handoff for new routing entry (via ValidateHandoff)
///   4. Single STARK proof covers vote + route update + handoff
#[test]
fn test_governance_vote_updates_route_table() {
    let voter1 = BabyBear::new(0x1001);
    let voter2 = BabyBear::new(0x1002);
    let proposal_hash = BabyBear::new(0x9909);

    // Compute vote commitments.
    let vote1 = vote_commitment(voter1, proposal_hash, 100); // weight 100
    let vote2 = vote_commitment(voter2, proposal_hash, 150); // weight 150
    // Combined vote root (simplified: hash both vote commitments).
    let vote_root = hash_2_to_1(vote1, vote2);

    // New route table commitment after governance passes.
    // old_route_table XOR new_route = new_route_table
    let old_route_table = BabyBear::new(0xAAAA);
    let new_route_entry = BabyBear::new(0xBBBB); // the new route being added
    let new_route_table = hash_2_to_1(old_route_table, new_route_entry);

    // Handoff: create a routing entry for a new federation peer.
    let certificate_hash = hash_2_to_1(proposal_hash, new_route_entry);
    let recipient_pk = BabyBear::new(0xCC01);
    let introducer_pk = BabyBear::new(0xDD02);

    // Compute the Merkle root that the trace generator will actually use.
    //
    // The trace generator hard-codes sibling = BabyBear::ZERO (no federation
    // mirror oracle in tests). The AIR constraint requires:
    //   leaf = hash(cert_hash, hash(recipient_pk, introducer_pk))
    //   chosen = hash(leaf, sibling)
    //   chosen == approved_set_root == PI[APPROVED_HANDOFFS_BASE]
    //
    // For the STARK to verify, all three values must agree. We compute the
    // expected leaf/chosen here and thread `chosen` into both the Effect and
    // the EffectVmContext so the trace, PI, and AIR constraint all match.
    let pks = hash_2_to_1(recipient_pk, introducer_pk);
    let handoff_leaf = hash_2_to_1(certificate_hash, pks);
    let handoff_sibling = BabyBear::ZERO; // matches the trace generator's hardcoded value
    let approved_set_root = hash_2_to_1(handoff_leaf, handoff_sibling);

    // Initial state: field[0] = old_route_table, field[1] = previous vote root.
    let mut initial_state = CellState::new(100_000, 0);
    initial_state.fields[0] = old_route_table;
    initial_state.fields[1] = BabyBear::ZERO; // no previous votes
    initial_state.refresh_commitment();

    let effects = vec![
        // Step 1: Record the vote root (quorum reached).
        Effect::SetField {
            field_idx: 1,
            value: vote_root,
        },
        // Step 2: Update route table commitment.
        Effect::SetField {
            field_idx: 0,
            value: new_route_table,
        },
        // Step 3: Validate handoff for the new routing entry.
        // approved_set_root is ignored by the trace generator (it reads from
        // context.approved_handoffs_root[0] instead). We pass the computed
        // chosen value here for documentation clarity.
        Effect::ValidateHandoff {
            certificate_hash,
            recipient_pk,
            introducer_pk,
            approved_set_root,
        },
    ];

    // Use generate_effect_vm_trace_ext to supply the correct approved_handoffs_root.
    // The trace generator writes context.approved_handoffs_root[0] into the PI and
    // into the PARAM slot; the AIR then enforces chosen == approved_root == PI value.
    let mut ctx = EffectVmContext::default();
    ctx.actor_nonce = initial_state.nonce as u64;
    ctx.approved_handoffs_root[0] = approved_set_root;
    let (trace, public_inputs) = generate_effect_vm_trace_ext(&initial_state, &effects, ctx);

    // Verify step 1: vote_root stored in field[1].
    let vote_row = &trace[0];
    let stored_vote = vote_row[effect_vm::STATE_AFTER_BASE + effect_vm::state::FIELD_BASE + 1];
    assert_eq!(stored_vote, vote_root, "vote root should be stored");

    // Verify step 2: new_route_table stored in field[0].
    let route_row = &trace[1];
    let stored_route = route_row[effect_vm::STATE_AFTER_BASE + effect_vm::state::FIELD_BASE + 0];
    assert_eq!(
        stored_route, new_route_table,
        "route table commitment should be updated"
    );

    // Verify step 3: handoff updated cap_root.
    let handoff_row = &trace[2];
    let old_cap = handoff_row[effect_vm::STATE_BEFORE_BASE + effect_vm::state::CAP_ROOT];
    let new_cap = handoff_row[effect_vm::STATE_AFTER_BASE + effect_vm::state::CAP_ROOT];
    let routing_entry = hash_2_to_1(recipient_pk, certificate_hash);
    let expected_new_cap = hash_2_to_1(old_cap, routing_entry);
    assert_eq!(
        new_cap, expected_new_cap,
        "cap_root should incorporate routing entry from handoff"
    );
    assert_ne!(old_cap, new_cap, "cap_root must change after handoff");

    // Verify the net balance delta is 0 (governance doesn't move funds).
    let net_delta = extract_net_delta(&public_inputs);
    assert_eq!(net_delta, Some(0), "governance should not change balance");

    // Verify the effects hash binds all three operations.
    // Stage 1 PI layout: EFFECTS_HASH is at indices [8..12] (4 felts).
    // The trace generator writes compute_effects_hash_4 here; position 1 is
    // an independent squeeze, not the legacy synthetic hi value.
    let expected_effects_hash = compute_effects_hash_4(&effects);
    assert_eq!(
        &public_inputs[effect_vm::pi::EFFECTS_HASH_BASE
            ..effect_vm::pi::EFFECTS_HASH_BASE + effect_vm::pi::EFFECTS_HASH_LEN],
        expected_effects_hash.as_slice(),
        "effects hash mismatch"
    );

    // Prove all three effects in a single STARK.
    // Must use prove_effects_ext with the same context (approved_handoffs_root[0] = approved_set_root)
    // so the STARK proof's public inputs agree with the trace's PI binding.
    let proof = prove_effects_ext(&initial_state, &effects, ctx);
    assert_eq!(proof.trace_len, trace.len());
    assert!(!proof.query_proofs.is_empty());

    // Verify the state commitment changed.
    // Stage 1 PI layout: OLD_COMMIT at [0..4], NEW_COMMIT at [4..8].
    // Compare pi[OLD_COMMIT] vs pi[NEW_COMMIT] (position-0 of each 4-felt block).
    assert_ne!(
        public_inputs[effect_vm::pi::OLD_COMMIT],
        public_inputs[effect_vm::pi::NEW_COMMIT],
        "governance should change state commitment"
    );

    // Tamper test: change one public input -> fails.
    // Tamper NEW_COMMIT[0] (index 4) — the continuation binding felt.
    let air = EffectVmAir::new(proof.trace_len);
    let mut tampered_pi = public_inputs.clone();
    tampered_pi[effect_vm::pi::NEW_COMMIT] = BabyBear::new(0xBAD); // wrong new_commitment
    let tampered_result = stark::verify(&air, &proof, &tampered_pi);
    assert!(
        tampered_result.is_err(),
        "Wrong public inputs should fail verification"
    );
}
