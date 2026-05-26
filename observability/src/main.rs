//! `dregg-observability` — Studio-shape trace event tour.
//!
//! Constructs and executes a tour scenario that exercises every event
//! variant the Studio inspector cares about: every `Authorization` kind,
//! sovereign-witness verification (both with and without STARK proof),
//! a sample of `StateConstraint` evaluation outcomes (accept and reject),
//! γ.2 bilateral receipts for a Transfer + a Grant + an Introduce, and
//! Federation id-derivation / join / leave / attestation events.
//!
//! The output is a single JSON document on stdout containing the full
//! event log in emission order — the wire shape a Studio Inspector
//! consumes. Pipe through `jq` or redirect to a file.

use std::time::{SystemTime, UNIX_EPOCH};

use dregg_captp::{HandoffCertificate, HandoffPresentation};
use dregg_cell::program::field_from_u64_be;
use dregg_cell::program::{ReadSet, StateConstraint};
use dregg_cell::state::{CellState, FIELD_ZERO, FieldElement};
use dregg_cell::{AuthRequired, Cell, CellProgram, Ledger, Permissions};
use dregg_circuit::field::BabyBear;
use dregg_federation::{Federation, LocalSeat};
use dregg_observability::Emitter;
use dregg_observability::events::{
    AuthorizationPayload, BearerDelegationSummary, BilateralReceiptPayload, BilateralRollupPayload,
    EventBody, EventEnvelope, FederationPayload, SovereignWitnessPayload, StateConstraintPayload,
    TraceEvent, TurnLifecyclePayload,
};
use dregg_turn::action::{Authorization, BearerCapProof, DelegationProofData};
use dregg_turn::bilateral_schedule::{
    BilateralCounts, BilateralRoots, ExpectedBilateral, GrantEntry, IntroduceEntry, TransferEntry,
};
use dregg_turn::builder::ActionBuilder;
use dregg_turn::{ComputronCosts, DelegationMode, TurnBuilder, TurnExecutor, TurnResult};
use dregg_types::{FederationId, generate_keypair, sign};

fn unix_millis_now() -> i64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_millis() as i64)
        .unwrap_or(0)
}

fn open_permissions() -> Permissions {
    Permissions {
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

fn make_cell(seed: u8, balance: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    let token_id = [0u8; 32];
    let mut cell = Cell::with_balance(pk, token_id, balance);
    cell.permissions = open_permissions();
    cell
}

fn main() {
    let em = Emitter::new();
    em.set_clock(unix_millis_now);

    // ------------------------------------------------------------------
    // 1. Build a federation and emit id-derivation + join + attestation
    //    events.
    // ------------------------------------------------------------------
    emit_federation_tour(&em);

    // ------------------------------------------------------------------
    // 2. Build a real Turn, execute it, emit lifecycle + bilateral events.
    // ------------------------------------------------------------------
    let turn_hash = emit_turn_lifecycle(&em);

    // ------------------------------------------------------------------
    // 3. Synthesize one of every Authorization variant and emit each.
    //    These are decorative: they share the turn_hash from §2 so a
    //    Studio timeline groups them with the executed turn.
    // ------------------------------------------------------------------
    emit_authorization_tour(&em, &turn_hash);

    // ------------------------------------------------------------------
    // 4. Sovereign-witness events: one with STARK, one without.
    // ------------------------------------------------------------------
    emit_sovereign_witness_tour(&em, &turn_hash);

    // ------------------------------------------------------------------
    // 5. Slot-caveat evaluation: accept + reject.
    // ------------------------------------------------------------------
    emit_state_constraint_tour(&em, &turn_hash);

    // ------------------------------------------------------------------
    // 6. Emit the JSON event stream.
    // ------------------------------------------------------------------
    let snapshot = em.snapshot();
    println!("{}", snapshot.to_pretty_string());
}

// =========================================================================
// Federation tour
// =========================================================================

fn emit_federation_tour(em: &Emitter) {
    // Build a two-member federation deterministically. We use
    // `verifier_only` because that constructor doesn't pull the BLS
    // setup (heavyweight + needs trusted setup state).
    let (sk_a, pk_a) = generate_keypair();
    let (_sk_b, pk_b) = generate_keypair();
    let fed_initial = Federation::verifier_only(vec![pk_a, pk_b], 0, 2);
    let fed_id_initial = fed_initial.id_bytes();

    let (seq, ts) = em.next_envelope_seed();
    em.emit(TraceEvent::Federation(EventBody {
        envelope: EventEnvelope::new(seq, ts).with_federation_id(&fed_id_initial),
        payload: FederationPayload::IdDerived {
            federation_id: hex32(&fed_id_initial),
            epoch: fed_initial.epoch(),
            threshold: fed_initial.threshold(),
            member_count: fed_initial.members().len(),
            members: fed_initial.members().iter().map(|m| hex32(&m.0)).collect(),
        },
    }));

    // Add a third member, simulating a committee rotation.
    let (_sk_c, pk_c) = generate_keypair();
    let mut sorted = vec![pk_a, pk_b, pk_c];
    sorted.sort_by(|a, b| a.0.cmp(&b.0));
    let fed_after = Federation::verifier_only(sorted, 1, 2);
    let fed_id_after = fed_after.id_bytes();

    let (seq, ts) = em.next_envelope_seed();
    em.emit(TraceEvent::Federation(EventBody {
        envelope: EventEnvelope::new(seq, ts).with_federation_id(&fed_id_after),
        payload: FederationPayload::MemberJoined {
            federation_id_before: hex32(&fed_id_initial),
            federation_id_after: hex32(&fed_id_after),
            epoch_after: fed_after.epoch(),
            member_pk: hex32(&pk_c.0),
        },
    }));

    // Simulate a member leaving (back to the original committee, but
    // epoch advanced).
    let fed_post_leave = Federation::verifier_only(vec![pk_a, pk_b], 2, 2);
    let fed_id_post_leave = fed_post_leave.id_bytes();

    let (seq, ts) = em.next_envelope_seed();
    em.emit(TraceEvent::Federation(EventBody {
        envelope: EventEnvelope::new(seq, ts).with_federation_id(&fed_id_post_leave),
        payload: FederationPayload::MemberLeft {
            federation_id_before: hex32(&fed_id_after),
            federation_id_after: hex32(&fed_id_post_leave),
            epoch_after: fed_post_leave.epoch(),
            member_pk: hex32(&pk_c.0),
        },
    }));

    // Attestation event: the original federation signs a message.
    let message = b"observability-tour-attestation";
    let sig = sign(&sk_a, message);
    let message_hash = blake3::hash(message);
    // We're modelling "one Ed25519 voter" here. A real `ReceiptQc::Votes`
    // would carry several `(pubkey, sig)` pairs; the Studio displays the
    // signer count.
    let _ = sig; // sig is verifiable but the trace doesn't carry it
    let (seq, ts) = em.next_envelope_seed();
    em.emit(TraceEvent::Federation(EventBody {
        envelope: EventEnvelope::new(seq, ts).with_federation_id(&fed_id_initial),
        payload: FederationPayload::Attestation {
            federation_id: hex32(&fed_id_initial),
            epoch: 0,
            message_hash: hex32(message_hash.as_bytes()),
            signer_count: 1,
            attestation_kind: "ed25519",
        },
    }));
}

// =========================================================================
// Turn lifecycle + bilateral tour
// =========================================================================

fn emit_turn_lifecycle(em: &Emitter) -> [u8; 32] {
    // ------------------------------------------------------------------
    // Build a real ledger and execute a Turn.
    // ------------------------------------------------------------------
    let mut ledger = Ledger::new();
    let agent_cell = make_cell(1, 1_000);
    let recipient_cell = make_cell(2, 500);
    let agent_id = agent_cell.id();
    let recipient_id = recipient_cell.id();

    let mut agent_with_cap = agent_cell;
    agent_with_cap
        .capabilities
        .grant(recipient_id, AuthRequired::None);
    ledger.insert_cell(agent_with_cap).expect("insert agent");
    ledger
        .insert_cell(recipient_cell)
        .expect("insert recipient");

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let transfer_amount: u64 = 100;
    let fee: u64 = 50;

    let mut builder = TurnBuilder::new(agent_id, 0);
    let action = ActionBuilder::new_unchecked_for_tests(agent_id, "transfer", agent_id)
        .effect_transfer(agent_id, recipient_id, transfer_amount)
        .delegation(DelegationMode::ParentsOwn)
        .build();
    builder.add_action(action);
    let turn = builder.fee(fee).build();
    let turn_hash = turn.hash();

    // Emit `Submitted`.
    let (seq, ts) = em.next_envelope_seed();
    em.emit(TraceEvent::TurnLifecycle(EventBody {
        envelope: EventEnvelope::new(seq, ts)
            .with_turn_hash(&turn_hash)
            .with_actor(&agent_id),
        payload: TurnLifecyclePayload::Submitted {
            nonce: turn.nonce,
            fee: turn.fee,
            action_count: turn.action_count(),
            valid_until: turn.valid_until,
            previous_receipt_hash: turn.previous_receipt_hash.as_ref().map(hex32),
        },
    }));

    // Execute and emit lifecycle outcome.
    match executor.execute(&turn, &mut ledger) {
        TurnResult::Committed {
            ledger_delta: _,
            receipt,
            computrons_used,
        } => {
            let (seq, ts) = em.next_envelope_seed();
            em.emit(TraceEvent::TurnLifecycle(EventBody {
                envelope: EventEnvelope::new(seq, ts)
                    .with_turn_hash(&turn_hash)
                    .with_actor(&agent_id),
                payload: TurnLifecyclePayload::Committed {
                    receipt_hash: hex32(&receipt.receipt_hash()),
                    forest_hash: hex32(&receipt.forest_hash),
                    pre_state_hash: hex32(&receipt.pre_state_hash),
                    post_state_hash: hex32(&receipt.post_state_hash),
                    effects_hash: hex32(&receipt.effects_hash),
                    timestamp: receipt.timestamp,
                    action_count: receipt.action_count as usize,
                    computrons_used,
                    finality: format!("{:?}", receipt.finality),
                },
            }));
        }
        TurnResult::Rejected { reason, at_action } => {
            let (seq, ts) = em.next_envelope_seed();
            em.emit(TraceEvent::TurnLifecycle(EventBody {
                envelope: EventEnvelope::new(seq, ts)
                    .with_turn_hash(&turn_hash)
                    .with_actor(&agent_id),
                payload: TurnLifecyclePayload::Rejected {
                    reason: reason.to_string(),
                    at_action,
                },
            }));
        }
        TurnResult::Expired => {
            let (seq, ts) = em.next_envelope_seed();
            em.emit(TraceEvent::TurnLifecycle(EventBody {
                envelope: EventEnvelope::new(seq, ts)
                    .with_turn_hash(&turn_hash)
                    .with_actor(&agent_id),
                payload: TurnLifecyclePayload::Expired,
            }));
        }
        TurnResult::Pending => {
            let (seq, ts) = em.next_envelope_seed();
            em.emit(TraceEvent::TurnLifecycle(EventBody {
                envelope: EventEnvelope::new(seq, ts)
                    .with_turn_hash(&turn_hash)
                    .with_actor(&agent_id),
                payload: TurnLifecyclePayload::Pending {
                    waiting_on: "sovereign-witness".to_string(),
                },
            }));
        }
    }

    // ------------------------------------------------------------------
    // Bilateral receipts. We construct a richer synthetic schedule to
    // cover all three entry kinds (Transfer/Grant/Introduce) — the
    // executor-run turn above only contains a Transfer.
    // ------------------------------------------------------------------
    let bystander_cell = make_cell(3, 0);
    let bystander_id = bystander_cell.id();

    let transfers = vec![TransferEntry {
        from: agent_id,
        to: recipient_id,
        amount: transfer_amount,
    }];
    let grants = vec![GrantEntry {
        from: agent_id,
        to: recipient_id,
        cap_entry_hash: blake3::hash(b"observability-tour-grant").into(),
    }];
    let introduces = vec![IntroduceEntry {
        introducer: agent_id,
        recipient: recipient_id,
        target: bystander_id,
        permissions: AuthRequired::Signature,
    }];
    let sched = ExpectedBilateral {
        transfers: transfers.clone(),
        grants: grants.clone(),
        introduces: introduces.clone(),
        // No cell in this tour produces a sovereign-witness self-attestation;
        // the schedule still requires the field as of the γ.2 unilateral
        // binding work.
        unilateral_attestations: std::collections::BTreeMap::new(),
    };

    let actor_nonce = turn.nonce;

    // Walk the schedule and emit one BilateralReceipt event per side. We
    // recompute the rolling accumulator using the same per-cell roots
    // helper the AIR uses; the post-fold root for each entry is the
    // value `BilateralRoots` carries after that entry has been absorbed.
    //
    // We emit them per-cell so a Studio inspector can render each cell's
    // timeline as the rolling per-direction accumulator.
    for cell_id in [&agent_id, &recipient_id, &bystander_id] {
        let counts = sched.counts_for(cell_id);
        let roots = sched.roots_for(cell_id, actor_nonce);

        // Per-entry emission.
        for entry in &transfers {
            if &entry.from == cell_id {
                emit_bilateral(
                    em,
                    cell_id,
                    &turn_hash,
                    dregg_observability::events::transfer_entry_outbound(
                        entry,
                        actor_nonce,
                        &roots.outgoing_transfer,
                    ),
                );
            }
            if &entry.to == cell_id {
                emit_bilateral(
                    em,
                    cell_id,
                    &turn_hash,
                    dregg_observability::events::transfer_entry_inbound(
                        entry,
                        actor_nonce,
                        &roots.incoming_transfer,
                    ),
                );
            }
        }
        for entry in &grants {
            if &entry.from == cell_id {
                emit_bilateral(
                    em,
                    cell_id,
                    &turn_hash,
                    dregg_observability::events::grant_entry_outbound(
                        entry,
                        actor_nonce,
                        &roots.outgoing_grant,
                    ),
                );
            }
            if &entry.to == cell_id {
                emit_bilateral(
                    em,
                    cell_id,
                    &turn_hash,
                    dregg_observability::events::grant_entry_inbound(
                        entry,
                        actor_nonce,
                        &roots.incoming_grant,
                    ),
                );
            }
        }
        for entry in &introduces {
            if &entry.introducer == cell_id {
                emit_bilateral(
                    em,
                    cell_id,
                    &turn_hash,
                    dregg_observability::events::intro_entry_introducer(
                        entry,
                        actor_nonce,
                        &roots.intro_as_introducer,
                    ),
                );
            }
            if &entry.recipient == cell_id {
                emit_bilateral(
                    em,
                    cell_id,
                    &turn_hash,
                    dregg_observability::events::intro_entry_recipient(
                        entry,
                        actor_nonce,
                        &roots.intro_as_recipient,
                    ),
                );
            }
            if &entry.target == cell_id {
                emit_bilateral(
                    em,
                    cell_id,
                    &turn_hash,
                    dregg_observability::events::intro_entry_target(
                        entry,
                        actor_nonce,
                        &roots.intro_as_target,
                    ),
                );
            }
        }

        // Per-cell rollup at end-of-turn.
        let (seq, ts) = em.next_envelope_seed();
        em.emit(TraceEvent::BilateralRollup(EventBody {
            envelope: EventEnvelope::new(seq, ts)
                .with_turn_hash(&turn_hash)
                .with_cell_id(cell_id),
            payload: BilateralRollupPayload {
                counts: counts.into(),
                roots: roots.into(),
            },
        }));
    }

    turn_hash
}

fn emit_bilateral(
    em: &Emitter,
    cell_id: &dregg_cell::CellId,
    turn_hash: &[u8; 32],
    payload: BilateralReceiptPayload,
) {
    let (seq, ts) = em.next_envelope_seed();
    em.emit(TraceEvent::BilateralReceipt(EventBody {
        envelope: EventEnvelope::new(seq, ts)
            .with_turn_hash(turn_hash)
            .with_cell_id(cell_id),
        payload,
    }));
}

// =========================================================================
// Authorization tour
// =========================================================================

fn emit_authorization_tour(em: &Emitter, turn_hash: &[u8; 32]) {
    // 1. Signature
    let auth_sig = Authorization::Signature([0xAB; 32], [0xCD; 32]);
    emit_auth_event(em, turn_hash, &auth_sig);

    // 2. Proof (synthetic — the proof bytes are opaque to the trace).
    let auth_proof = Authorization::Proof {
        proof_bytes: vec![0u8; 256],
        bound_action: "transfer".to_string(),
        bound_resource: "agent-cell".to_string(),
    };
    emit_auth_event(em, turn_hash, &auth_proof);

    // 3. Breadstuff
    let token: [u8; 32] = blake3::hash(b"observability-tour-breadstuff").into();
    let auth_bs = Authorization::Breadstuff(token);
    emit_auth_event(em, turn_hash, &auth_bs);

    // 4. Bearer (signed delegation)
    let mut target_bytes = [0u8; 32];
    target_bytes[0] = 9;
    let target_cell = dregg_cell::CellId(target_bytes);
    let mut delegator_pk = [0u8; 32];
    delegator_pk[0] = 7;
    let mut bearer_pk = [0u8; 32];
    bearer_pk[0] = 8;
    let auth_bearer_signed = Authorization::Bearer(BearerCapProof {
        target: target_cell,
        permissions: AuthRequired::Signature,
        delegation_proof: DelegationProofData::SignedDelegation {
            delegator_pk,
            signature: [0x44; 64],
            bearer_pk,
        },
        expires_at: 1_000_000,
        revocation_channel: Some([0x55; 32]),
        allowed_effects: Some(0b1010u32),
    });
    emit_auth_event(em, turn_hash, &auth_bearer_signed);

    // 4b. Bearer (STARK delegation)
    let auth_bearer_stark = Authorization::Bearer(BearerCapProof {
        target: target_cell,
        permissions: AuthRequired::Proof,
        delegation_proof: DelegationProofData::StarkDelegation {
            proof_bytes: vec![0u8; 512],
            root_issuer_commitment: [0x66; 32],
        },
        expires_at: 2_000_000,
        revocation_channel: None,
        allowed_effects: None,
    });
    emit_auth_event(em, turn_hash, &auth_bearer_stark);

    // 5. Unchecked
    emit_auth_event(em, turn_hash, &Authorization::Unchecked);

    // 6. CapTpDelivered — construct a real HandoffCertificate so the
    //    payload reflects the on-wire shape Studio will see.
    let auth_captp = build_captp_authorization();
    emit_auth_event(em, turn_hash, &auth_captp);
}

fn emit_auth_event(em: &Emitter, turn_hash: &[u8; 32], auth: &Authorization) {
    let (seq, ts) = em.next_envelope_seed();
    em.emit(TraceEvent::Authorization(EventBody {
        envelope: EventEnvelope::new(seq, ts).with_turn_hash(turn_hash),
        payload: AuthorizationPayload::from_authorization(auth),
    }));
}

fn build_captp_authorization() -> Authorization {
    let (introducer_key, introducer_pubkey) = generate_keypair();
    let (recipient_key, recipient_pubkey) = generate_keypair();

    let introducer_fed = FederationId(introducer_pubkey.0);
    let target_fed = FederationId(blake3::hash(b"target-federation").into());
    let mut target_cell_bytes = [0u8; 32];
    target_cell_bytes[0] = 0xAB;
    let target_cell = dregg_cell::CellId(target_cell_bytes);
    let swiss: [u8; 32] = blake3::hash(b"observability-tour-swiss").into();

    let cert = HandoffCertificate::create(
        &introducer_key,
        introducer_fed,
        target_fed,
        target_cell,
        recipient_pubkey.0,
        AuthRequired::Signature,
        Some(0b0011u32),
        Some(2_000_000),
        Some(3),
        swiss,
    );

    // The sender (= recipient) signs the `captp_delivered_signing_message`.
    // For the trace we use a synthetic empty effect set + nonce 0; in
    // production the wire layer fills these in.
    let mut agent_bytes = [0u8; 32];
    agent_bytes[0] = 0xCD;
    let agent_cell = dregg_cell::CellId(agent_bytes);
    let federation_id = [0u8; 32];
    let msg = Authorization::captp_delivered_signing_message_for_federation(
        &federation_id,
        &cert.nonce,
        &agent_cell,
        &target_cell,
        0,
        &[],
    );
    let sig = sign(&recipient_key, &msg);

    Authorization::CapTpDelivered {
        handoff_cert: cert,
        introducer_pk: introducer_pubkey.0,
        sender_pk: recipient_pubkey.0,
        sender_signature: sig.0,
    }
}

// =========================================================================
// Sovereign witness tour
// =========================================================================

fn emit_sovereign_witness_tour(em: &Emitter, turn_hash: &[u8; 32]) {
    let mut sov_cell = make_cell(0x10, 1_000);
    sov_cell.permissions = open_permissions();
    let cell_id = sov_cell.id();
    let old_commit = sov_cell.state_commitment();

    // Witness 1: no STARK proof (the executor would re-execute).
    let witness_no_stark = dregg_turn::SovereignCellWitness {
        cell_id,
        old_commitment: old_commit,
        new_commitment: [0xAA; 32],
        effects_hash: [0xBB; 32],
        timestamp: 1_779_494_400, // 2026-05-24T00:00:00Z
        sequence: 1,
        signature: [0; 64],
        cell_state: sov_cell.clone(),
        transition_proof: None,
    };
    emit_witness_event(em, turn_hash, &witness_no_stark);

    // Witness 2: with STARK proof.
    let witness_with_stark = dregg_turn::SovereignCellWitness {
        cell_id,
        old_commitment: [0xAA; 32],
        new_commitment: [0xCC; 32],
        effects_hash: [0xDD; 32],
        timestamp: 1_779_494_401,
        sequence: 2,
        signature: [0; 64],
        cell_state: sov_cell,
        transition_proof: Some(vec![0u8; 4096]),
    };
    emit_witness_event(em, turn_hash, &witness_with_stark);
}

fn emit_witness_event(
    em: &Emitter,
    turn_hash: &[u8; 32],
    witness: &dregg_turn::SovereignCellWitness,
) {
    let (seq, ts) = em.next_envelope_seed();
    em.emit(TraceEvent::SovereignWitnessVerified(EventBody {
        envelope: EventEnvelope::new(seq, ts)
            .with_turn_hash(turn_hash)
            .with_cell_id(&witness.cell_id),
        payload: SovereignWitnessPayload::from_witness(witness),
    }));
}

// =========================================================================
// Slot caveat tour
// =========================================================================

fn emit_state_constraint_tour(em: &Emitter, turn_hash: &[u8; 32]) {
    // Build a tiny CellState pair so we can really evaluate a constraint
    // and surface a real reason.
    let mut old_state = CellState::default();
    old_state.fields[3] = field_from_u64_be(5);
    let mut new_state_ok = old_state.clone();
    new_state_ok.fields[3] = field_from_u64_be(10);
    let mut new_state_bad = old_state.clone();
    new_state_bad.fields[3] = field_from_u64_be(3); // decrease

    // Constraint: Monotonic on slot 3.
    let constraint = StateConstraint::Monotonic { index: 3 };
    let program = CellProgram::Predicate(vec![constraint.clone()]);

    let result_ok = program.evaluate_static(&new_state_ok, Some(&old_state));
    let (seq, ts) = em.next_envelope_seed();
    em.emit(TraceEvent::StateConstraintEvaluated(EventBody {
        envelope: EventEnvelope::new(seq, ts).with_turn_hash(turn_hash),
        payload: StateConstraintPayload::from_evaluation(&constraint, result_ok.is_ok(), None),
    }));

    let result_bad = program.evaluate_static(&new_state_bad, Some(&old_state));
    let reason = match &result_bad {
        Err(e) => Some(format!("{}", e)),
        Ok(()) => None,
    };
    let (seq, ts) = em.next_envelope_seed();
    em.emit(TraceEvent::StateConstraintEvaluated(EventBody {
        envelope: EventEnvelope::new(seq, ts).with_turn_hash(turn_hash),
        payload: StateConstraintPayload::from_evaluation(&constraint, result_bad.is_ok(), reason),
    }));

    // Also exercise a multi-slot constraint for shape coverage.
    let sum_constraint = StateConstraint::SumEquals {
        indices: vec![0, 1, 2],
        value: field_from_u64_be(0),
    };
    let mut s = CellState::default();
    s.fields[0] = FIELD_ZERO;
    s.fields[1] = FIELD_ZERO;
    s.fields[2] = FIELD_ZERO;
    let program2 = CellProgram::Predicate(vec![sum_constraint.clone()]);
    let result_sum = program2.evaluate_static(&s, None);
    let (seq, ts) = em.next_envelope_seed();
    em.emit(TraceEvent::StateConstraintEvaluated(EventBody {
        envelope: EventEnvelope::new(seq, ts).with_turn_hash(turn_hash),
        payload: StateConstraintPayload::from_evaluation(
            &sum_constraint,
            result_sum.is_ok(),
            result_sum.err().map(|e| format!("{}", e)),
        ),
    }));
}

// =========================================================================
// Helpers
// =========================================================================

fn hex32(bytes: &[u8; 32]) -> String {
    let mut out = String::with_capacity(64);
    for b in bytes {
        out.push_str(&format!("{b:02x}"));
    }
    out
}

// Silence unused-import warnings the IDE pulls in for the future-extension
// types. These are intentionally re-exported even when this binary doesn't
// reach them today.
#[allow(dead_code)]
fn _api_surface_anchor() {
    let _ = HandoffPresentation::presentation_message;
    // `LocalSeat::bls_secret` is gated on `dregg-federation/runtime`,
    // a feature observability does not enable. We anchor the type but
    // do not construct it here (the constructor shape differs between
    // feature configurations). The type reference suffices to keep
    // it linked into the binary's API surface.
    let _: Option<LocalSeat> = None;
    let _: BabyBear = BabyBear::ZERO;
    let _ = BilateralCounts::default();
    let _ = BilateralRoots::default();
    let _ = ReadSet {
        new_slots: vec![],
        old_slots: vec![],
        ..Default::default()
    };
    let _ = BearerDelegationSummary::SignedDelegation {
        delegator_pk: String::new(),
        bearer_pk: String::new(),
        signature_prefix: String::new(),
    };
    let _: FieldElement = FIELD_ZERO;
}
