//! # R3 ADAPTER — a live grain turn → ONE foldable `FinalizedTurn`.
//!
//! The R2 weld ([`crate::ToolGatewayMinter`]) commits every admitted agent action as a
//! genuine executor turn on the grain worker cell, and records it
//! ([`crate::GrainTurnRecord`]). R3 ([`grain_verify::r3_verify`]) folds a chain of
//! [`FinalizedTurn`]s — each a rotated wide-anchored EffectVM leg — into one recursive
//! STARK aggregate the Lean-proven verifier decides. This module is the SEAM between
//! them: [`finalize_grain_turn`] mints the rotated leg for a committed grain turn from its
//! REAL captured data (pre-cell, effects, post-cell) through the same recipe the
//! whole-history demo uses ([`mint_rotated_participant_leg`]).
//!
//! ## One executor turn = one leg (the single-tick grain member)
//!
//! A grain turn is ONE executor turn on the worker cell: PHASE 1 debits `turn.fee` and ticks
//! the nonce ONCE (`turn/src/executor/execute.rs`), and the body writes slots 4
//! (`calls_made`, gateway-prepended), 3 (`history_root`), 5 (`consumed`), 6 (`heap_root`) and
//! 7 (`action`). The single-tick grain member `grainTurnVmDescriptor2R24` (Lean
//! `Dregg2.Circuit.Emit.EffectVmEmitGrainTurnRotated`, selector `sel::GRAIN_TURN = 6`) proves
//! exactly that as ONE row: the five slots written, the fee debited from `bal_lo` and
//! PUBLISHED at PI `ROT_FEE_PI`, the nonce ticked once (Lean `grainTurn_row_agrees_executor`,
//! `carries_ticks_once`). So each committed turn is one leg over its REAL pre-cell and REAL
//! post-cell, and consecutive legs meet at the ledger (turn `t+1`'s pre-cell IS turn `t`'s
//! post-cell): the folded head is the executor's on-ledger grain-cell head.
//! `grain-session/SINGLE-TICK-DESCRIPTOR.md` is the design note.

use dregg_circuit::effect_vm::{CellState, Effect as VmEffect};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::empty_heap_root_8;
use dregg_circuit_prove::ivc_turn_chain::FinalizedTurn;
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_sdk::{AgentCipherclerk, RotationTurnWitness};
use dregg_turn::rotation_witness::{empty_revoked_root_8, produce};
use dregg_turn_prover::rotation_witness::mint_rotated_participant_leg;

use crate::GrainTurnRecord;

/// The grain write set, in the executor's commit order (`calls_made` first).
pub const GRAIN_WRITE_ORDER: [usize; 5] = [4, 3, 5, 6, 7];

/// **Coalesce a committed grain turn into its ONE EffectVM row** — `VmEffect::GrainTurn`.
///
/// The executor's own marshaller (`AgentCipherclerk::try_convert_effects_to_vm`, unchanged:
/// it keeps projecting the effect list one-to-one) gives the five lane-0 values; this function
/// is the grain-specific coalescing and FAILS CLOSED on any other shape: a write set that is not
/// exactly slots `{4, 3, 5, 6, 7}` in commit order (so an attested turn, which also writes slot 8,
/// is refused), a write to a cell other than the worker, or a post-cell whose balance did not
/// move by a non-negative fee. The fee is read off the ledger cells (`before − after`); the leg
/// then FORCES the debit to equal the fee it publishes, so a verifier compares that PI with
/// `turn.fee`.
pub fn grain_turn_vm_effect(record: &GrainTurnRecord) -> Result<VmEffect, String> {
    let actor = record.before_cell.id();
    for e in &record.effects {
        match e {
            dregg_sdk::Effect::SetField { cell, .. } if *cell == actor => {}
            other => {
                return Err(format!(
                    "grain_turn_vm_effect: a grain turn writes only SetFields on the worker cell; \
                     got {other:?}"
                ));
            }
        }
    }
    let vm = AgentCipherclerk::try_convert_effects_to_vm(&actor, &record.effects)
        .map_err(|e| format!("grain_turn_vm_effect: {e}"))?;
    let slots: Vec<usize> = vm
        .iter()
        .map(|e| match e {
            VmEffect::SetField { field_idx, .. } => Ok(*field_idx as usize),
            other => Err(format!(
                "grain_turn_vm_effect: unexpected projected effect {other:?}"
            )),
        })
        .collect::<Result<_, _>>()?;
    if slots != GRAIN_WRITE_ORDER {
        return Err(format!(
            "grain_turn_vm_effect: the write set {slots:?} is not the grain write set \
             {GRAIN_WRITE_ORDER:?} (the single-tick grain member writes exactly slots 3..=7; an \
             attested turn's slot 8 has no AIR lane)"
        ));
    }
    let mut values = [BabyBear::ZERO; 5];
    for e in &vm {
        if let VmEffect::SetField { field_idx, value } = e {
            values[*field_idx as usize - 3] = *value;
        }
    }
    let (b, a) = (
        record.before_cell.state.balance(),
        record.after_cell.state.balance(),
    );
    if a > b {
        return Err(format!(
            "grain_turn_vm_effect: the worker balance rose ({b} -> {a}); a grain turn only debits \
             its fee"
        ));
    }
    Ok(VmEffect::GrainTurn {
        values,
        fee: (b - a) as u64,
    })
}

/// **Mint the ONE rotated leg for a committed grain turn** over its REAL pre- and post-cells.
///
/// `receipt_log` is the leg's receipt context (the wide anchors absorb its root as `iroot`):
/// `[turn_hash]` for a lone turn, the session's ordered turn hashes for a session fold, so the
/// context is the same on both sides of every turn boundary.
///
/// COST: one IR-v2 batch prove per turn (the leg self-verifies before it is returned).
pub fn finalize_grain_turn_in(
    record: &GrainTurnRecord,
    receipt_log: &[[u8; 32]],
) -> Result<FinalizedTurn, String> {
    mint_grain_leg_with(record, receipt_log, grain_turn_vm_effect(record)?)
}

/// Mint the grain leg for `record` over a GIVEN EffectVM row — the honest caller passes
/// [`grain_turn_vm_effect`]`(record)`. Public so a tamper test can present a row that disagrees
/// with the ledger cells (a fee that is not the debit) and observe the prover refuse it.
pub fn mint_grain_leg_with(
    record: &GrainTurnRecord,
    receipt_log: &[[u8; 32]],
    effect: VmEffect,
) -> Result<FinalizedTurn, String> {
    let nullifier_root = empty_heap_root_8();
    let commitments_root = empty_heap_root_8();
    // The EffectVM pre-state is the REAL pre-cell, decoded through the canonical welded-limb
    // reader (`RotationTurnWitness::before_cell_state`), against a single-cell ledger snapshot.
    let mut ledger = dregg_cell::Ledger::new();
    ledger
        .insert_cell(record.before_cell.clone())
        .map_err(|e| format!("finalize_grain_turn: ledger seed failed: {e:?}"))?;
    let material = dregg_cell::commitment::RotationCarrierMaterial::default();
    let witness = |cell: &dregg_cell::Cell| {
        produce(
            cell,
            &ledger,
            &nullifier_root,
            &commitments_root,
            &empty_revoked_root_8(),
            receipt_log,
            &material,
        )
    };
    let initial_state: CellState = RotationTurnWitness::for_effects(
        witness(&record.before_cell),
        witness(&record.after_cell),
        std::slice::from_ref(&effect),
    )
    .before_cell_state()
    .map_err(|e| format!("finalize_grain_turn: pre-state decode failed: {e}"))?;
    let leg = mint_rotated_participant_leg(
        &initial_state,
        std::slice::from_ref(&effect),
        &record.before_cell,
        &record.after_cell,
        &nullifier_root,
        &commitments_root,
        receipt_log,
    )
    .map_err(|e| format!("finalize_grain_turn: rotated-leg mint failed: {e}"))?;
    Ok(FinalizedTurn::new(DescriptorParticipant::rotated(leg)))
}

/// **Mint the rotated leg for a committed grain turn** under its own receipt context
/// (`[turn_hash]`). One executor turn is one leg; returned as a one-element `Vec` so a caller
/// concatenating turns keeps the chain shape.
pub fn finalize_grain_turn(record: &GrainTurnRecord) -> Result<Vec<FinalizedTurn>, String> {
    finalize_grain_turn_in(record, &[record.turn_hash]).map(|leg| vec![leg])
}

/// **Each committed turn as its own leg, under its own receipt context.** The legs meet at the
/// ledger cells, but each leg's anchors absorb a DIFFERENT context root (its own turn hash), so
/// the wide anchors differ across a turn boundary: this is the per-turn form, for a caller that
/// verifies turns one at a time. A session fold is [`finalize_session_threaded`].
pub fn finalize_session(records: &[GrainTurnRecord]) -> Result<Vec<FinalizedTurn>, String> {
    records
        .iter()
        .enumerate()
        .map(|(i, rec)| {
            finalize_grain_turn_in(rec, &[rec.turn_hash]).map_err(|e| {
                format!(
                    "finalize_session: turn {i} ({}): {e}",
                    hex_prefix(&rec.turn_hash)
                )
            })
        })
        .collect()
}

/// **A MULTI-turn session as ONE continuous chain of T legs over the REAL ledger cells.**
///
/// Every leg is minted over its record's real pre-cell and real post-cell under ONE receipt
/// context, the session's ordered turn hashes, so `leg_t.new_root == leg_{t+1}.old_root`
/// exactly when turn `t+1`'s pre-cell is turn `t`'s post-cell. That adjacency is CHECKED here
/// (a session whose records are not adjacent ledger states is refused, never silently
/// re-seeded), so the folded head is the executor's on-ledger head: [`session_head_openings`]
/// recomputes it from the last cell alone.
///
/// What each leg attests: the five grain slots written, the fee debited from the balance and
/// published (`ROT_FEE_PI`), the nonce ticked ONCE. What it does not: the receipt context's root
/// enters the anchors through `iroot`, which the rotation witness carries as ONE felt, so the
/// turn-hash list is bound at about 31 bits, not 124; and written slot values are published
/// full-width, so R3 binds the bytes chosen, not their BLAKE3 provenance.
pub fn finalize_session_threaded(
    records: &[GrainTurnRecord],
) -> Result<Vec<FinalizedTurn>, String> {
    let session_log: Vec<[u8; 32]> = records.iter().map(|r| r.turn_hash).collect();
    for (i, w) in records.windows(2).enumerate() {
        if w[0].after_cell != w[1].before_cell {
            return Err(format!(
                "finalize_session_threaded: turn {} does not start where turn {i} ended (the \
                 records are not adjacent ledger states)",
                i + 1
            ));
        }
    }
    records
        .iter()
        .enumerate()
        .map(|(i, rec)| {
            finalize_grain_turn_in(rec, &session_log).map_err(|e| {
                format!(
                    "finalize_session_threaded: turn {i} ({}): {e}",
                    hex_prefix(&rec.turn_hash)
                )
            })
        })
        .collect()
}

/// **Open the folded head.** The 8-felt commitment of the session's LAST committed grain cell
/// under the session receipt context [`finalize_session_threaded`] uses, as `u32` lanes — exactly
/// the AFTER anchor the last leg publishes, because the leg is minted over that very cell. A
/// verifier holding the published last cell and the ordered turn hashes recomputes it WITHOUT
/// proving and compares it to the aggregate's committed head: equality joins the head to that
/// cell's fields (the last action commit, the turn counter, the history root), its balance and
/// nonce (the ledger's, fee debited and ticked once per turn), and, through the context root, to
/// the exact ordered list of turn hashes.
pub fn session_head_openings(
    last_after_cell: &dregg_cell::Cell,
    turn_hashes: &[[u8; 32]],
) -> Result<[u32; 8], String> {
    // Exactly the witness the last leg's AFTER block is built from (`mint_rotated_participant_leg`:
    // `produce` over a single-cell ledger, the empty heap / commitments / revoked roots, the
    // session receipt context, zero carrier material), then the 8-felt chained commitment over
    // its limbs and context root.
    let mut ledger = dregg_cell::Ledger::new();
    ledger
        .insert_cell(last_after_cell.clone())
        .map_err(|e| format!("session_head_openings: ledger seed failed: {e:?}"))?;
    let w = produce(
        last_after_cell,
        &ledger,
        &empty_heap_root_8(),
        &empty_heap_root_8(),
        &empty_revoked_root_8(),
        turn_hashes,
        &dregg_cell::commitment::RotationCarrierMaterial::default(),
    );
    // The CHIP-faithful chained commitment: the byte-twin of the deployed wide trace's
    // `fill_wide_block` absorption, which is what the wide leg publishes as its anchors.
    let f8 = dregg_circuit::Faithful8::from_wire_commit_chip(&w.pre_limbs, w.iroot);
    let lanes: &[BabyBear; 8] = f8.as_ref();
    Ok(core::array::from_fn(|i| lanes[i].as_u32()))
}

fn hex_prefix(h: &[u8; 32]) -> String {
    h.iter().take(4).map(|b| format!("{b:02x}")).collect()
}
