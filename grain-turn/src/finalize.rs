//! # R3 ADAPTER — a live grain turn → foldable `FinalizedTurn`(s).
//!
//! The R2 weld ([`crate::ToolGatewayMinter`]) commits every admitted agent action as a
//! genuine executor turn on the grain worker cell, and records it
//! ([`crate::GrainTurnRecord`]). R3 ([`grain_verify::r3_verify`]) folds a chain of
//! [`FinalizedTurn`]s — each a rotated wide-anchored EffectVM leg — into one recursive
//! STARK aggregate the Lean-proven verifier decides. This module is the SEAM between
//! them: [`finalize_grain_turn`] mints the rotated leg(s) for a committed grain turn from
//! its REAL captured data (pre-cell, effects, post-cell), reusing the SAME recipe the
//! whole-history demo uses ([`dregg_turn_prover::rotation_witness::mint_rotated_participant_leg`]),
//! so R3 runs on a real driven session instead of a hand-minted fixture.
//!
//! ## A grain turn is HETEROGENEOUS → a cohort-run CHAIN, not one leg
//!
//! Every grain turn writes ≥4 DISTINCT field slots in ONE executor turn — `calls_made`
//! (slot 4, gateway-prepended), `history_root` (3, the per-grain CommitBindsMMR weld),
//! `consumed` (5), `heap_root` (6), `action` (7) — and each `SetField` slot resolves to
//! its own rotated descriptor (`setFieldVmDescriptor2-{3,4,5,6,7}R24`).
//! The wide producer proves ONE homogeneous cohort per leg (it refuses a "heterogeneous
//! multi-effect turn"), and a [`FinalizedTurn`] holds exactly ONE rotated leg. So one grain
//! turn maps to N `FinalizedTurn`s — a cohort-run chain (mirroring the executor's own
//! `prove_cohort_run_chain`): the runs are threaded so `leg_k.new_root == leg_{k+1}.old_root`
//! (the fold's temporal tooth), the chain genesis binds the real pre-cell, and the interior
//! states ride the per-effect welds.
//!
//! ## HONEST BOUNDARY — the head is the EffectVM head, not the on-ledger cell head
//!
//! The rotated EffectVM leg is the ONLY rotated-leg trace source, and it ticks the cell
//! nonce ONCE PER EFFECT (`generate_effect_vm_trace`); the executor ticks the worker cell
//! nonce ONCE PER TURN (`turn/src/executor/execute.rs` Phase 1, regardless of how many
//! fields the turn writes). So the folded chain's final head encodes `nonce = pre + N`
//! (N = number of field writes), while the executor committed `nonce = pre + 1`. The chain
//! is internally consistent and folds — but the head R3 binds is the **EffectVM-model
//! head**, which for a multi-field grain turn is NOT the executor's on-ledger
//! grain-cell head. Reconciling them needs a single-nonce-tick multi-field grain rotated
//! descriptor (a circuit/VK change) — see `finalize_session`'s doc for the precise gap.

use dregg_circuit::effect_vm::{CellState, Effect as VmEffect};
use dregg_circuit::heap_root::empty_heap_root_8;
use dregg_circuit_prove::ivc_turn_chain::FinalizedTurn;
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_sdk::full_turn_proof::split_into_cohort_runs;
use dregg_sdk::{AgentCipherclerk, RotationTurnWitness};
use dregg_turn::rotation_witness::{empty_revoked_root_8, produce};
use dregg_turn_prover::rotation_witness::mint_rotated_participant_leg;

use crate::GrainTurnRecord;

/// **Mint the rotated wide-anchored EffectVM leg(s) for a committed grain turn** — the
/// R3-foldable form of a real R2 turn.
///
/// Reconstructs the turn's EffectVM from the REAL captured data:
///   1. project the committed effects onto the actor cell (the SAME
///      `AgentCipherclerk::convert_effects_to_vm` marshaller the executor's proof uses);
///   2. seed the EffectVM pre-state from the REAL pre-cell via the canonical welded-limb
///      decode ([`RotationTurnWitness::before_cell_state`]) — so the chain's genesis
///      old-root binds the committed pre-cell, not a synthetic zero-field state;
///   3. split into maximal homogeneous cohort runs (a grain turn is heterogeneous, so N
///      runs), and for each run mint one [`dregg_turn_prover::rotation_witness::mint_rotated_participant_leg`]
///      over the threaded per-run pre-state `s_k`, wrapping it as a [`FinalizedTurn`].
///
/// The returned legs are a continuous sub-chain (`leg_k.new_root == leg_{k+1}.old_root`,
/// interior states threaded through the per-effect welds). Returns the legs in chain
/// order — one grain turn is generally several `FinalizedTurn`s.
///
/// Errors (as `String`) name the precise wall: an empty actor projection, a non-`SetField`
/// grain effect (the minter only writes `SetField`), a slot `>= 8` (folds into the
/// authority residue, not the 8-field state block the rotated leg carries), or a mint/
/// self-verify failure from the wide producer.
///
/// COST: each leg is a full IR-v2 batch prove (~tens of seconds); a grain turn's ~4 legs
/// prove independently. The FOLD over them is the expensive recursive step (see
/// [`grain_verify::r3_verify`]).
pub fn finalize_grain_turn(record: &GrainTurnRecord) -> Result<Vec<FinalizedTurn>, String> {
    finalize_grain_turn_from(record, None, None, None).map(|(legs, _)| legs)
}

/// [`finalize_grain_turn`] with an optional EffectVM pre-state override, returning the legs AND
/// the EffectVM state the last leg ends at. `None` seeds from the real pre-cell (the
/// single-turn recipe); `Some(s)` continues an EffectVM chain a previous turn ended at — the
/// seam [`finalize_session_threaded`] uses so a multi-turn session folds.
fn finalize_grain_turn_from(
    record: &GrainTurnRecord,
    initial_override: Option<CellState>,
    receipt_log_override: Option<&[[u8; 32]]>,
    model_balance: Option<i64>,
) -> Result<(Vec<FinalizedTurn>, CellState), String> {
    let actor = record.before_cell.id();
    // A continued chain carries the EffectVM's model nonce AND model balance, which the rotated
    // before-block must agree with on row 0 (measured on bb2: the real pre-cell fails constraints
    // #87-#93, #118). So a continued turn is witnessed over the real pre-cell with its nonce and
    // balance replaced by the carried model values; every other limb is the executor's committed
    // pre-state.
    let before_cell = match &initial_override {
        Some(s) => {
            let mut c = record.before_cell.clone();
            c.state.set_nonce(u64::from(s.nonce));
            // The per-slot setField members freeze the balance, while every executor grain turn
            // debits its fee from the worker cell: the carried model balance is turn 0's.
            c.state
                .set_balance(model_balance.unwrap_or_else(|| record.before_cell.state.balance()));
            c
        }
        None => record.before_cell.clone(),
    };

    // (1) Project the committed effects onto the actor cell — the executor's own marshaller.
    //
    // ⚑ CHECKED (#61/#62). The grain minter writes `ATTESTATION_SLOT = 8`, which is a legal
    // fixed cell (`STATE_SLOTS` = 16) with no AIR lane — exactly the band that produced the
    // reported panic. `apply_run` below already refuses it with a precise message; the
    // UNCHECKED projector now refuses it FIRST, and unchecked means `.expect`. Take the
    // checked door so the wall stays a `String` this function's contract promises, not a
    // panic through `finalize_grain_turn`'s caller.
    let vm_effects = AgentCipherclerk::try_convert_effects_to_vm(&actor, &record.effects)
        .map_err(|e| format!("finalize_grain_turn: {e}"))?;
    if vm_effects.is_empty() {
        return Err(
            "finalize_grain_turn: the committed effects project to an EMPTY actor transition \
             (nothing to rotate)"
                .to_string(),
        );
    }

    // The turn-invariant leg context. A grain SetField turn spends no note (empty nullifier
    // frontier), holds no note commitments, and binds its iroot to the real turn hash.
    let nullifier_root = empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log = match receipt_log_override {
        Some(log) => log.to_vec(),
        None => vec![record.turn_hash],
    };

    // (2) Seed the EffectVM pre-state from the REAL pre-cell (balance/nonce/fields/cap
    // root/authority residue) via the canonical welded-limb decode. Both blocks are
    // produced against a single-cell ledger snapshot (the same `cells_root` shape the
    // sovereign path uses); the decode reads `before.pre_limbs` in the Lean-pinned order.
    let mut ledger = dregg_cell::Ledger::new();
    ledger
        .insert_cell(before_cell.clone())
        .map_err(|e| format!("finalize_grain_turn: ledger seed failed: {e:?}"))?;
    let material = dregg_cell::commitment::RotationCarrierMaterial::default();
    let before_w = produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        // revoked_root (arg #5, added when cell-state roots retyped to Faithful8):
        // the EMPTY revocation accumulator — no live revoked root flows through a mint
        // recipe today (mirrors rotation_witness.rs's own produce() recipe wrappers).
        &empty_revoked_root_8(),
        &receipt_log,
        &material,
    );
    let after_w = produce(
        &record.after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        // revoked_root (arg #5, added when cell-state roots retyped to Faithful8):
        // the EMPTY revocation accumulator — no live revoked root flows through a mint
        // recipe today (mirrors rotation_witness.rs's own produce() recipe wrappers).
        &empty_revoked_root_8(),
        &receipt_log,
        &material,
    );
    let initial_state = RotationTurnWitness::for_effects(before_w, after_w, &vm_effects)
        .before_cell_state()
        .map_err(|e| format!("finalize_grain_turn: pre-state decode failed: {e}"))?;
    let initial_state = initial_override.unwrap_or(initial_state);

    // (3) Split into homogeneous cohort runs — one rotated leg per run.
    let runs = split_into_cohort_runs(&vm_effects);
    if runs.is_empty() {
        return Err("finalize_grain_turn: no cohort runs (non-cohort turn)".to_string());
    }
    let n_runs = runs.len();

    let mut legs = Vec::with_capacity(n_runs);
    let mut s_k = initial_state;
    for (i, run) in runs.iter().enumerate() {
        let run_effects = &vm_effects[run.clone()];
        // The after-block cell: the real pre-cell for INTERIOR runs (before == after, the
        // turn-invariant limbs; the state block rides the welds), the real POST-cell only
        // for the FINAL run (mirrors `prove_cohort_run_chain`). `cells_root` folds the cell
        // id alone and the grain SetFields to slots 3..7 leave the authority residue fixed,
        // so the interior after-block limbs equal the final-run old-block limbs — the chain
        // closes by construction.
        let after_cell = if i + 1 == n_runs {
            &record.after_cell
        } else {
            &before_cell
        };
        let leg = mint_rotated_participant_leg(
            &s_k,
            run_effects,
            &before_cell,
            after_cell,
            &nullifier_root,
            &commitments_root,
            &receipt_log,
        )
        .map_err(|e| format!("finalize_grain_turn: run {i} rotated-leg mint failed: {e}"))?;
        // Thread the interior pre-state for the next run.
        s_k = apply_run(&s_k, run_effects)
            .map_err(|e| format!("finalize_grain_turn: run {i} state threading: {e}"))?;
        legs.push(FinalizedTurn::new(DescriptorParticipant::rotated(leg)));
    }
    Ok((legs, s_k))
}

/// Thread the EffectVM pre-state across a cohort run — apply each `SetField` exactly as
/// `generate_effect_vm_trace` does (write the slot, TICK the nonce per effect), so the next
/// run's `s_k` equals the on-trace interior boundary the rotated welds carry.
///
/// The grain minter only writes `SetField`; a non-`SetField` effect, or a slot `>= 8`
/// (which folds into the authority residue `record_digest`, NOT the 8-field state block the
/// rotated leg carries), is the precise NAMED wall — an `Err`, never a silent skip.
fn apply_run(s: &CellState, run_effects: &[VmEffect]) -> Result<CellState, String> {
    let mut next = s.clone();
    for e in run_effects {
        match e {
            VmEffect::SetField { field_idx, value } => {
                let idx = *field_idx as usize;
                if idx >= next.fields.len() {
                    return Err(format!(
                        "SetField slot {idx} >= 8 folds into the authority residue, not the \
                         8-field state block the rotated leg models (needs setFieldDyn / a \
                         residue-carrying descriptor)"
                    ));
                }
                next.fields[idx] = *value;
                next.nonce += 1;
            }
            other => {
                return Err(format!(
                    "unexpected non-SetField grain effect {other:?} — the grain minter commits \
                     only SetField writes"
                ));
            }
        }
    }
    next.refresh_commitment();
    Ok(next)
}

/// **Collect a driven session's committed grain turns as one foldable `Vec<FinalizedTurn>`**
/// — ready to hand to [`grain_verify::r3_verify`] at the fold's own head.
///
/// Finalizes each captured [`GrainTurnRecord`] in commit order and concatenates the legs.
///
/// ## RESIDUAL GAP (precise, load-bearing — do NOT read a passing fold as "the real
/// on-ledger session R3-verifies")
///
/// A single grain turn's legs form a continuous sub-chain, and its genesis binds the real
/// committed pre-cell. But across a MULTI-turn session the chain does NOT close to the
/// executor's on-ledger heads:
///
///   * turn `t`'s final leg ends at the EffectVM head `nonce = pre_t + N_t` (N_t field
///     writes, per-effect tick), whereas the executor committed `pre_t + 1`;
///   * turn `t+1`'s genesis is its real committed pre-cell (`nonce = pre_t + 1`), which does
///     NOT equal turn `t`'s EffectVM head — so a naive concatenation breaks the fold's WIDE
///     temporal tooth between turns.
///
/// This is the SAME root cause both ways: the rotated EffectVM leg models one nonce tick
/// PER EFFECT, the grain executor turn commits one tick PER TURN. There is no faithful way
/// to express a multi-field single-executor-turn transition as either (a) one rotated leg
/// (heterogeneous — the wide producer refuses it) or (b) a chain of single-`SetField` legs
/// (N ticks, so the head diverges). Closing it needs a **single-nonce-tick multi-field
/// grain rotated descriptor** (write the 3–4 grain slots + tick the nonce once, in ONE
/// leg) — a new circuit descriptor + committed VK, ember-gated.
///
/// So this function returns the per-turn sub-chains concatenated; the caller who wants a
/// PASSING fold over a real session should drive a SINGLE grain turn (its sub-chain closes
/// internally, anchored at the EffectVM head) — which demonstrates R3 running on real
/// grain-derived legs while the multi-turn head-faithfulness stays the named gap above.
pub fn finalize_session(records: &[GrainTurnRecord]) -> Result<Vec<FinalizedTurn>, String> {
    let mut all = Vec::new();
    for (i, rec) in records.iter().enumerate() {
        let legs = finalize_grain_turn(rec).map_err(|e| {
            format!(
                "finalize_session: turn {i} ({}): {e}",
                hex_prefix(&rec.turn_hash)
            )
        })?;
        all.extend(legs);
    }
    Ok(all)
}

/// **Collect a MULTI-turn session as ONE continuous EffectVM chain** — the form
/// [`finalize_session`] cannot produce (see its RESIDUAL GAP).
///
/// Turn 0 seeds from its real committed pre-cell, exactly as [`finalize_grain_turn`] does.
/// Every later turn is seeded from the EffectVM state the previous turn's last leg ENDED at,
/// instead of from its real pre-cell, so `leg_k.new_root == leg_{k+1}.old_root` holds across
/// turn boundaries and the whole session folds.
///
/// ## What the folded head is, precisely
///
/// The EffectVM applies the projected `SetField` writes of every record, in commit order, to the
/// carried `CellState`; nothing else moves (balance, capability root and record digest stay at
/// turn 0's values, and fields no record writes stay as turn 0 found them). This function does NOT
/// check that the records are adjacent ledger states (turn t+1's `before_cell` == turn t's
/// `after_cell`); the minter produces them that way, a caller with other records gets no such
/// guarantee. Each field lane 0 is the EffectVM value (`field_limbs9(v)[0]`); the other limbs
/// come from the per-turn cell witnesses. The nonce is `pre_0 + (total field writes)`, while the
/// executor committed `pre_0 + (turns)`. The head this chain binds is therefore the
/// **EffectVM-model head** of the session, not the ledger head. Slot 8 (`ATTESTATION_SLOT`) has
/// no AIR lane: a record that wrote it is refused (fail-closed), so an attested-brain session
/// does not finalize here at all.
///
/// Every leg uses ONE receipt context, the ordered turn hashes of the whole session, so the
/// wide anchors' `iroot` is the same across every turn boundary.
/// The faithful fix is the single-nonce-tick multi-field grain descriptor named in
/// [`finalize_session`] (a circuit + VK change, ember-gated); this function does not claim it.
pub fn finalize_session_threaded(
    records: &[GrainTurnRecord],
) -> Result<Vec<FinalizedTurn>, String> {
    // ONE receipt context for the whole session: the ordered committed turn hashes. The wide
    // anchors absorb its root (`iroot`), so it must be the same on both sides of every turn
    // boundary, and it is what joins the folded history to the R2 links: a verifier that
    // recomputes the root over the receipts' `turn_receipt_hash`es recomputes the same `iroot`.
    let session_log: Vec<[u8; 32]> = records.iter().map(|r| r.turn_hash).collect();
    let balance0 = records
        .first()
        .map(|r| r.before_cell.state.balance())
        .unwrap_or(0);
    let mut all = Vec::new();
    let mut carry: Option<CellState> = None;
    for (i, rec) in records.iter().enumerate() {
        let (legs, end) =
            finalize_grain_turn_from(rec, carry.take(), Some(&session_log), Some(balance0))
                .map_err(|e| {
                    format!(
                        "finalize_session_threaded: turn {i} ({}): {e}",
                        hex_prefix(&rec.turn_hash)
                    )
                })?;
        all.extend(legs);
        carry = Some(end);
    }
    Ok(all)
}

/// **Open the folded head.** The 8-felt commitment of the session's LAST committed grain cell
/// under the session receipt context [`finalize_session_threaded`] uses, as `u32` lanes, for two
/// nonces: the ledger's (`.0`) and the EffectVM model's (`.1`: the first record's pre-nonce plus
/// the total number of field writes). A verifier holding the published last cell and the ordered
/// turn hashes recomputes these WITHOUT proving and compares them to the aggregate's committed
/// head: equality joins the head to that cell's fields (the last action commit, the turn counter,
/// the history root) and, through the context root, to the exact ordered list of turn hashes.
pub fn session_head_openings(
    last_after_cell: &dregg_cell::Cell,
    turn_hashes: &[[u8; 32]],
    model_nonce: u64,
) -> Result<([u32; 8], [u32; 8]), String> {
    let at = |cell: &dregg_cell::Cell| -> Result<[u32; 8], String> {
        let mut ledger = dregg_cell::Ledger::new();
        ledger
            .insert_cell(cell.clone())
            .map_err(|e| format!("session_head_openings: ledger seed failed: {e:?}"))?;
        let ctx = dregg_turn::rotation_witness::sovereign_turn_ctx(
            &ledger,
            turn_hashes,
            dregg_cell::commitment::RotationCarrierMaterial::default(),
        );
        let f8 = ctx.commitment_felt8(cell);
        let lanes: &[dregg_circuit::field::BabyBear; 8] = f8.as_ref();
        Ok(core::array::from_fn(|i| lanes[i].as_u32()))
    };
    let real = at(last_after_cell)?;
    let mut model = last_after_cell.clone();
    model.state.set_nonce(model_nonce);
    Ok((real, at(&model)?))
}

/// The EffectVM model nonce at the end of a session: the first record's pre-cell nonce plus the
/// number of projected field writes across all records (one tick per effect).
pub fn session_model_nonce(records: &[GrainTurnRecord]) -> Result<u64, String> {
    let first = records.first().ok_or("empty session")?;
    let mut n = first.before_cell.state.nonce();
    for r in records {
        let vm = AgentCipherclerk::try_convert_effects_to_vm(&r.before_cell.id(), &r.effects)
            .map_err(|e| format!("session_model_nonce: {e}"))?;
        n += vm.len() as u64;
    }
    Ok(n)
}

fn hex_prefix(h: &[u8; 32]) -> String {
    h.iter().take(4).map(|b| format!("{b:02x}")).collect()
}
