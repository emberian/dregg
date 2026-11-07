//! ⚑ **THE MEASUREMENT THAT DECIDES WHAT A PER-TURN ANCHOR CAN AND CANNOT BIND.**
//!
//! `docs/DESIGN-pi-authority.md` §4(a) proposed publishing "the canonical 8-felt
//! `old_commit`/`new_commit` for a turn (from the node's own committed state, which it has)" so
//! that `verify_full_turn_bound`'s two endpoint `CommitmentMismatch` teeth stop comparing
//! `x != x`. The node's committed state DOES hold a per-turn 8-felt commit pair — the receipt's
//! `pre_state_hash` / `post_state_hash`, which the committee's attestation signature transitively
//! covers via `receipt_stream_root`.
//!
//! **It is not the pair the full-turn proof publishes.** This file measures that, and isolates
//! the causes, each independently sufficient.
//!
//! ## ⚠ THERE ARE FOUR, NOT TWO — corrected 2026-08-07 by direct read of the producers
//!
//! Every doc in the tree that describes this divergence (this file's own header until now,
//! `federation/src/turn_anchor.rs`, `node/src/api.rs`'s `/anchor` docblock,
//! `discord-bot/src/commands/proof_verify.rs`, `docs/DESIGN-pi-authority.md` §4(a)) names TWO
//! causes. There are four fields of `V9RotationContext` on which the two sides disagree, and the
//! two that were missing are the ones that make the alignment cost what it costs:
//!
//! 1. **`iroot`.** `state_commit::consensus_ctx` pins `rotation_witness::empty_iroot_8()`
//!    deliberately (a receipt cannot bind a commitment its own hash is computed from). The
//!    proof side folds something — and **which** something is not one convention but THREE, see
//!    below.
//! 2. **`cells_root` (scope).** `consensus_ctx` folds `rotation_witness::cells_root(ledger)` over
//!    the WHOLE ledger. The proof-side builder
//!    (`node::turn_proving::rotation_witness_for_self_sovereign_impl`) folds a SINGLE-CELL context
//!    ledger holding only the actor.
//! 3. **`revoked_root`.** ⚑ NOT PREVIOUSLY NAMED ANYWHERE. `TurnExecutor::consensus_state_commitment`
//!    passes the executor's LIVE `note_revoked.lock().root8()`;
//!    `rotation_witness_for_self_sovereign_impl` passes
//!    `rotation_witness::empty_revoked_root_8()` **unconditionally** — there is no parameter for
//!    it and no call site can thread one. So the moment ONE credential is revoked anywhere in the
//!    federation, every proof's published commit diverges from the anchor for a third,
//!    independent reason.
//! 4. **`material`.** ⚑ NOT PREVIOUSLY NAMED ANYWHERE. `consensus_ctx` hardcodes
//!    `RotationCarrierMaterial::default()`; the proof-side builders put the installed
//!    `child_vk` on the AFTER block of a `CreateCellFromFactory` turn. This one does not merely
//!    diverge — it is the cause that **should not be aligned by moving the proving side**:
//!    `factoryV3Carriers` `.piBinding`s that octet as PI 47..54 precisely to EXPOSE the installed
//!    child VK, so zeroing it on the prover would blank a published surface rather than align one.
//!    Aligning it properly moves the SIGNED ANCHOR.
//!    ⓘ NOT established, and not to be relayed as if it were: whether any verifier ANCHORS those
//!    PIs from trusted state. `turn/src/executor/proof_verify.rs` constructs no
//!    `RotationCarrierMaterial` at all; if its reconstruction reaches the octet it does so through
//!    the trace generators, and that routing was not traced.
//!
//! ## ⚑ And the proof side's `iroot` is not one convention but three
//!
//! Measured at HEAD, the value fed to `iroot()` by each producer of a rotation witness:
//!
//! | producer | receipt log it folds |
//! |---|---|
//! | `blocklace_sync` non-spend / bearer arms (`:9239`, `:9319`) | `[receipt.receipt_hash()]` — THIS turn's receipt, a ONE-entry log |
//! | `turn_proving::rotation_witness_for_cap_less_turn` (`:1298`) | `[turn_hash]` — the TURN hash, not a receipt hash |
//! | `api.rs::…` HTTP witness route (`:4292`) | `[receipt_hash]` |
//! | `sdk::cipherclerk::prove_sovereign_turn_rotated` (`:5638`) | the agent's WHOLE prior receipt chain |
//! | `state_commit::consensus_ctx` | the EMPTY log, pinned |
//!
//! So "the proof folds the real receipt chain" — the phrasing in all four docblocks — is true of
//! exactly one of the four producers, and the one it is true of is the LEDGERLESS sovereign SDK
//! path, whose artifacts `/api/turn/{hash}/proof` never serves. The live node path folds a
//! one-entry log containing the current turn's receipt hash. `iroot` on the proof side is not a
//! commitment to a history; it is a free witness felt each producer fills differently.
//!
//! ## ⚑ WHY THAT IS ALLOWED: the AIR gates none of it
//!
//! `EffectVmEmitRotationV3.cellsRootGroupCol`'s own docstring (`metatheory/Dregg2/Circuit/Emit/
//! EffectVmEmitRotationV3.lean:2145-2155`): *"the createCell/factory/spawn trace generator still
//! OVERWRITES the whole group with its own in-circuit accounts tree, which is the object the two
//! map-ops below actually gate. **Only those three members constrain this group; on every other
//! member the lanes are absorbed by `wireCommitR` and gated by nothing.**"* And `B_IROOT` is
//! absorbed last and gated by nothing on ANY member. `trace_rotated::fill_block` copies both
//! straight out of the producer witness.
//!
//! So on 54 of the 57 registry members these limbs are **free witness values**, and the published
//! commit is whatever the producer chose to fold. That is what makes converging the PROVING side
//! onto the CONSENSUS context cost no VK rotation and no descriptor re-emit — and it is also why
//! the divergence was invisible: nothing refuses either value.
//!
//! So `dregg_federation::TurnAnchorV1` carries a committee-signed 8-felt pair that must be
//! REPORTED and must never be handed to `verify_full_turn_bound` as `expected_old_commit` — it
//! would refuse every honest proof. The anchor binds the **turn identity** instead, which every
//! effect-vm leg publishes and the verifier takes as a required argument.
//!
//! ## ⚠⚠ AND THERE ARE SIX, NOT FOUR — the last two are NOT context conventions
//!
//! Added 2026-08-07 by DERIVING what the code decides (`file:line` for each leg below; this file's
//! arms do not yet exhibit them, and building that gate is the first item of the follow-up — a
//! documented cause is not a detected one). The four above are fields of `V9RotationContext`, so
//! re-parameterising the context closes them. These two are not, and no context change reaches
//! them:
//!
//! 5. **The fee.** `TurnExecutor::execute` debits `turn.fee` from the agent in PHASE 1
//!    (`turn/src/executor/execute.rs:652-674`), BETWEEN the `pre_state_hash` snapshot (`:596-600`)
//!    and the `post_state_hash` one. The node's classical commit-path prover threads no fee at all
//!    (`node/src/turn_proving.rs` — the fee-aware wide route
//!    `prove_wide_umem_welded_staged_with_fee` is reached only from the SDK sovereign path), so a
//!    turn with `fee > 0` publishes an after-balance the executor's post-cell does not carry.
//! 6. **The nonce accounting.** The executor bumps the agent's nonce ONCE PER TURN (phase 1, the
//!    same block), and then again per `IncrementNonce` effect. The circuit VM ticks
//!    `new_state.nonce += 1` ONCE PER NON-PADDING ROW (`circuit/src/effect_vm/trace.rs:683-1035`,
//!    including its own `Effect::IncrementNonce` arm at `:811-814`). So an N-actor-effect turn
//!    publishes `pre + N` where the executor commits `pre + 1 + #IncrementNonce`.
//!
//! ⚑ **Why these reach the published pair at all**: the wide generator's `fill_block` does not
//! merely carry the producer's after-witness limbs — it OVERRIDES the AFTER block's welded
//! `r0..r10` / `cap_root` from that row's own v1 state block
//! (`circuit/src/effect_vm/trace_rotated.rs:2728-2736`), i.e. from `VM(pre, effects)`. The BEFORE
//! block has no such gap: `initial_vm_state` is decoded from the BEFORE witness's own limbs
//! (`RotationTurnWitness::before_cell_state`), so its weld is the identity and the published
//! BEFORE commit IS `wire_commit_8_chip` over the before-cell's limbs — the standing differential
//! `circuit/tests/effect_vm_wide_roundtrip.rs::assert_executor_anchor`.
//!
//! **Consequence for the alignment this file gates.** Converging the four fields makes the
//! published BEFORE anchor equal `receipt.pre_state_hash` exactly — one committee-signed
//! `expected_old_commit`. It does NOT make the AFTER anchor equal `receipt.post_state_hash`, and
//! binding it as if it did would REFUSE every honest fee-bearing or multi-effect turn. So the
//! endpoint serves the node's DERIVED pair for now
//! (`node/src/api.rs::get_turn_anchor`'s `proof_state_commits`, exhibited in
//! `node/tests/the_served_pair_binds_the_proofs_commitments.rs`), labelled as the node's claim
//! rather than the committee's, and closing causes 5–6 means putting the fee and the executor's
//! nonce rule INSIDE the proven transition — an AIR-level change, not a re-parameterisation.
//!
//! ## This test is a GATE, not a note
//!
//! It asserts the divergence, so aligning the two contexts (the real fix, priced in
//! `docs/DESIGN-pi-authority.md`) makes this file go RED and forces whoever does it to come here,
//! delete the divergence assertions, and open the endpoint binding this file's docs forbid. A
//! silent alignment is not possible.
//!
//! ⚠ And it now asserts the divergence **cause by cause**, so a partial alignment — three of the
//! four fields converged and `material` left behind, which is the shape the cheap version of this
//! work would take — goes red on the cause it left rather than staying green on the three it fixed.

use dregg_cell::commitment::{RotationCarrierMaterial, V9RotationContext};
use dregg_cell::{Cell, Ledger};
use dregg_circuit::Faithful8;
use dregg_turn::rotation_witness as rw;
use dregg_turn::state_commit;

fn cell_with(seed: u8, balance: u64) -> Cell {
    let mut c = Cell::new([seed; 32], [0u8; 32]);
    let _ = c.state.credit_balance(balance);
    c
}

/// The chip 8-felt commit of `cell` under an EXPLICIT context — the shared body of both sides, so
/// the only thing that varies between the arms below is one named field of the context. Uses
/// `rw::produce_in_ctx`, which is the same limb fill both `rw::produce` and
/// `state_commit::consensus_state_commitment` go through.
fn commit_under_ctx(cell: &Cell, ctx: &V9RotationContext) -> [u8; 32] {
    let w = rw::produce_in_ctx(cell, ctx);
    Faithful8::from_wire_commit_chip(&w.pre_limbs, w.iroot).to_bytes32()
}

/// The consensus context's shape with ONE field varied — every arm below is this call with a
/// different argument, so no arm can diverge for a reason it did not name.
fn ctx_with(
    ctx_ledger: &Ledger,
    receipt_hashes: &[[u8; 32]],
    revoked: Faithful8,
    material: RotationCarrierMaterial,
) -> V9RotationContext {
    V9RotationContext {
        cells_root: rw::cells_root(ctx_ledger),
        nullifier_root: rw::empty_nullifier_root_8(),
        commitments_root: rw::empty_commitments_root_8(),
        revoked_root: revoked,
        iroot: rw::iroot8(receipt_hashes),
        material,
    }
}

/// Shorthand for the arms that vary neither `revoked_root` nor `material`.
fn commit_under(
    cell: &Cell,
    ctx_ledger: &Ledger,
    receipt_hashes: &[[u8; 32]],
    revoked: &Faithful8,
) -> [u8; 32] {
    commit_under_ctx(
        cell,
        &ctx_with(
            ctx_ledger,
            receipt_hashes,
            *revoked,
            RotationCarrierMaterial::default(),
        ),
    )
}

#[test]
fn the_receipt_state_commit_is_not_the_proof_state_commit() {
    // A ledger with more than one cell — every devnet has many.
    let alice = cell_with(0xA1, 1000);
    let bob = cell_with(0xB2, 500);
    let alice_id = alice.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(alice.clone()).expect("insert alice");
    ledger.insert_cell(bob).expect("insert bob");

    // The proof-side builder's context ledger: the ACTOR ALONE.
    let mut ctx_ledger = Ledger::new();
    ctx_ledger.insert_cell(alice.clone()).expect("insert actor");

    let revoked = rw::empty_revoked_root_8();

    // ── THE RECEIPT SIDE — what the committee signs. ────────────────────────
    let exec_ctx = state_commit::consensus_ctx(
        &ledger,
        rw::empty_nullifier_root_8(),
        rw::empty_commitments_root_8(),
        revoked,
    );
    let receipt_commit = state_commit::consensus_state_commitment(&ledger, &alice_id, &exec_ctx);

    // CONTROL: reproducing the executor's context reproduces its commit exactly. Without this,
    // every `assert_ne!` below could be an artefact of a mis-built helper rather than a real
    // divergence.
    assert_eq!(
        receipt_commit,
        commit_under(&alice, &ledger, &[], &revoked),
        "CONTROL: the same context must reproduce the receipt's anchor"
    );

    // ── CAUSE 1: `iroot`, alone. ────────────────────────────────────────────
    // Same whole-ledger cells_root, same accumulator roots; only the receipt-chain fold differs.
    let a_receipt_hash = [0x7Eu8; 32];
    let iroot_only = commit_under(&alice, &ledger, &[a_receipt_hash], &revoked);
    assert_ne!(
        receipt_commit, iroot_only,
        "folding the real receipt chain into `iroot` must move the commit — if it does not, \
         `empty_iroot_8()` is aliasing a real fold and the anchor is weaker than documented"
    );

    // ── CAUSE 2: `cells_root`, alone. ───────────────────────────────────────
    // Same empty iroot, same accumulator roots; only the context ledger differs.
    let cells_only = commit_under(&alice, &ctx_ledger, &[], &revoked);
    assert_ne!(
        receipt_commit, cells_only,
        "a single-cell context ledger must move the commit — the whole-ledger `cells_root` is a \
         real component of the consensus anchor"
    );

    // ── CAUSE 3: `revoked_root`, alone. ⚑ NAMED NOWHERE BEFORE 2026-08-07. ──
    // `TurnExecutor::consensus_state_commitment` threads the executor's LIVE
    // `note_revoked.lock().root8()`. `rotation_witness_for_self_sovereign_impl` writes
    // `empty_revoked_root_8()` UNCONDITIONALLY — it takes `nullifier_root` and
    // `commitments_root` as parameters and has no parameter for this one, so no call site can
    // thread the live value even if it wanted to. The divergence is therefore dormant on a
    // federation that has revoked nothing and permanent from the first revocation onward.
    let mut revoked_set = dregg_cell::revoked_set::RevokedSet::new();
    revoked_set
        .insert([0x5Cu8; 32], 7)
        .expect("a fresh credential nullifier inserts");
    let live_revoked = revoked_set.root8();
    assert_ne!(
        live_revoked, revoked,
        "CONTROL: one revocation must move the accumulator root, or the arm below proves nothing"
    );
    let revoked_only = commit_under(&alice, &ledger, &[], &live_revoked);
    assert_ne!(
        receipt_commit, revoked_only,
        "the live revocation root must move the commit — the proof side pins the EMPTY root with \
         no parameter to thread the live one, so this is the third independent cause"
    );

    // ── CAUSE 4: `material`, alone. ⚑ NAMED NOWHERE BEFORE 2026-08-07, AND IT IS THE ONE
    //    THAT CANNOT BE FIXED BY MOVING THE PROVING SIDE. ─────────────────────
    // `consensus_ctx` hardcodes `RotationCarrierMaterial::default()`. The proof-side builders
    // (`turn_proving::rotation_witness_for_self_sovereign_impl`, `cipherclerk`) put the installed
    // `child_vk` on the AFTER block of a `CreateCellFromFactory` turn. Converging THIS field by
    // moving the proving side would mean zeroing a published surface: `factoryV3Carriers`
    // (`EffectVmEmitRotationV3.lean:6553`) `.piBinding`s that octet as PI 47..54 precisely to
    // EXPOSE the installed child VK, and the two `RotationCarrierMaterial` producers
    // (`turn_proving.rs:732`, `:885`) exist to fill it. ⓘ NOT ESTABLISHED HERE, and do not relay
    // it as if it were: whether any verifier ANCHORS those PIs from trusted state.
    // `turn/src/executor/proof_verify.rs` constructs no `RotationCarrierMaterial` at all, so if
    // its reconstruction reaches the octet it does so through the trace generators and that
    // routing was not traced. Either way the honest direction is the same — `consensus_ctx`
    // learns to carry the material, which moves the signed anchor and is the whole of the
    // re-genesis in the price.
    let factory_material = RotationCarrierMaterial {
        child_vk: Some([0xC1u8; 32]),
        contract_hash: None,
    };
    let material_only =
        commit_under_ctx(&alice, &ctx_with(&ledger, &[], revoked, factory_material));
    assert_ne!(
        receipt_commit, material_only,
        "a factory turn's AFTER carrier material must move the commit — if it does not, the \
         child-VK octet is not reaching `wireCommitR` and `factoryV3Carriers`' pins publish a \
         value the anchor does not bind"
    );

    // ── THE PROOF SIDE'S `iroot` IS NOT ONE CONVENTION BUT THREE. ───────────
    // Each live producer folds a different log, so "the proof's commit" is not even a single
    // value across the tree — it is per-producer. A stranger handed "the proof's pair" has to be
    // told which producer minted the artifact.
    let turn_hash = [0x3Au8; 32];
    let by_receipt_hash = commit_under(&alice, &ctx_ledger, &[a_receipt_hash], &revoked); // blocklace_sync
    let by_turn_hash = commit_under(&alice, &ctx_ledger, &[turn_hash], &revoked); // cap-less spend arm
    let by_prior_chain = commit_under(&alice, &ctx_ledger, &[[0x01u8; 32], [0x02u8; 32]], &revoked); // cipherclerk
    assert_ne!(
        by_receipt_hash, by_turn_hash,
        "the non-spend arm ([receipt_hash]) and the cap-less spend arm ([turn_hash]) publish \
         DIFFERENT commits for the same transition"
    );
    assert_ne!(
        by_receipt_hash, by_prior_chain,
        "…and the ledgerless sovereign path (the WHOLE prior receipt chain) a third"
    );

    // ── BOTH OF THE TWO ORIGINALLY-NAMED CAUSES, as the live paths differ. ──
    let proof_commit = by_receipt_hash;
    assert_ne!(
        receipt_commit, proof_commit,
        "⚑ if this passes, the receipt's committee-signed 8-felt pair HAS become the proof's \
         published pair. That is the alignment `docs/DESIGN-pi-authority.md` prices, and it is \
         GOOD NEWS — but it means `dregg_federation::turn_anchor`'s docs, and the endpoint's \
         refusal to publish `expected_old_commit`, are now wrong. Go update them. ⚠ And check the \
         OTHER TWO causes above went with it: three of four converged is a pair that agrees on \
         every turn until the first revocation or the first factory turn, which is the worst \
         possible failure shape."
    );
}
