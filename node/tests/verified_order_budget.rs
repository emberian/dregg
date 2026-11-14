//! THE VERIFIED-ORDER BUDGET — how far does the verified Lean τ-order FFI actually reach,
//! and do the two orders the node swaps between agree?
//!
//! ## The claim under test
//!
//! `node/src/blocklace_sync.rs` says the node "finalizes over the VERIFIED ordering": the
//! authoritative finalized order is `BlocklaceFinality.tauOrder`, reached through
//! `finality_gate::VerifiedFinality::compute_order` → `dregg_lean_ffi::verified_tau_order` →
//! the `@[export] dregg_tau_order`. That claim is **conditional on a per-poll wall-clock
//! budget** (`verified_order_ffi_timeout()`, default **2500 ms**). When the budget is missed
//! the poll does NOT use the verified order — it either runs the un-verified Rust
//! `ordering::tau` twin (`DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`, which is what
//! `scripts/federation-local.sh:86` sets) or finalizes NOTHING (a Lean-linked PoA node, which
//! `scripts/poa-devnet.sh` pins to `=0`).
//!
//! So "we finalize over the verified ordering" is really "we finalize over the verified
//! ordering **on polls where a 2500 ms budget is met**". This test measures where that budget
//! is met, and pins the two facts an operator has to be able to rely on.
//!
//! ## What is measured, and why it is measured this way
//!
//! Both sides run the REAL node code — `VerifiedFinality::compute_order` and
//! `blocklace_sync::build_ordering_blocklace` + `dregg_blocklace::ordering::tau`, the exact
//! pair `poll_finalized_blocks` runs each poll. Nothing here re-implements either; a mirror
//! would silently test itself (and the topological-insertion fix in
//! `build_ordering_blocklace` is exactly the part a mirror gets wrong).
//!
//! The lace is the shape a live federation produces: an `n`-validator committee, round-
//! synchronous, every round citing ALL of the previous round. That is the DAG
//! `scripts/federation-local.sh` builds, and the shape whose growth drove the observed
//! over-budget warnings at `lace_size` 773–981.
//!
//! ## ⚑ Status of that gate, measured 2026-11-13
//!
//! On an archive built from this checkout's Lean (hbox, Lean 4.35),
//! [`the_two_orders_the_node_swaps_between_agree_exactly`] is **RED** at n=3, rounds=6 — the
//! first lace where a second wave anchors — and it was red at `origin/main` too. It had not been
//! seen because the test self-skips without an archive. The two orders finalize the same SET;
//! the SEQUENCES differ inside each round, where every block is ready at once and the two
//! linearizers break the tie differently (OPEN-CM-XSORT: Rust pops the min block id, a blake3
//! hash; Lean pops the least `(round, id)`, and its `id` is the wire's `(seq, creator)` index).
//! So the over-budget fallback does substitute a different order. The gate is left as it is: it
//! states the property the fallback needs, and making it true means giving the two linearizers
//! one ready priority.
//!
//! ## ⚑ What the round-synchronous shape cannot see (dregg issue #100)
//!
//! A round-synchronous lace has two properties no real federation is guaranteed: every creator's
//! `seq` equals its DAG depth, and every block reaches its ancestors through enrolled blocks.
//! Two defects in the verified rule lived exactly in the complement:
//!
//! * **a late joiner** — a validator whose first block (`seq 0`) cites the current tips. The
//!   Lean round map folded blocks in `(seq, creator)` order and skipped predecessors it had not
//!   folded yet, so that block got round 1. [`late_joiner_lace`] makes the late joiner the
//!   leader of the wave it joins in: with the wrong round the wave never anchors and the
//!   verified rule finalizes one coordinate where `ordering::tau` finalizes ten.
//! * **an unenrolled relay** — a block that reaches a later round only through a
//!   non-participant's block keeps a low round, and the Lean `(round, id)` key sort emitted it
//!   BEFORE its own causal ancestors. [`relay_lace`] is that shape; the finalized SET was right
//!   and the ORDER was not a linear extension of the causal order.
//!
//! [`the_verified_order_survives_a_late_joiner_and_a_relay`] runs both. It asserts what both
//! orders must satisfy whatever the tie-break: the same finalized set, and each order a linear
//! extension of the lace's causal order. Run against the Lean of `origin/main` it fails on all
//! three counts (one coordinate instead of ten; different sets; a block ahead of an ancestor);
//! against this checkout's it passes.

use std::collections::{HashMap, HashSet};
use std::time::{Duration, Instant};

use dregg_blocklace::finality::{Block, BlockId, Blocklace, Payload};
use dregg_blocklace::signer::HybridBlockSigner;
use dregg_node::blocklace_sync::build_ordering_blocklace;
use dregg_node::finality_gate::VerifiedFinality;
use ed25519_dalek::SigningKey;

/// The default per-poll budget `blocklace_sync::verified_order_ffi_timeout()` enforces. Kept
/// here as a plain constant so the printed table can say "over/under" without importing a
/// private fn; if the default in `blocklace_sync.rs` changes, this comment is the only thing
/// that goes stale (the measurement itself does not depend on it).
const DEFAULT_PER_POLL_BUDGET: Duration = Duration::from_millis(2500);

/// Put THIS process in the same disposition as the deployed binary: verified PQ cores installed
/// before the first ML-DSA operation.
///
/// `HybridBlockSigner::new` derives an ML-DSA-65 key from the ed25519 seed, and `dregg_pq`'s audit
/// gate `process::abort()`s rather than answer that from the unaudited `fips204` crate. The five
/// callers of `install_verified_pq_cores` are all BINARY entry points, and `node/src/lib.rs`'s
/// `pq_test_bootstrap` initializer is `#[cfg(test)]` — so it covers the lib-test binary and NOT an
/// integration test in `node/tests/`, which is its own process. Without this call the first
/// `committee()` aborts the whole test binary with SIGABRT.
///
/// ⚠ The other way to make that abort go away is `DREGG_ALLOW_UNAUDITED_PQ=1`, which routes keygen
/// onto the unaudited crate — the exact substitution the gate exists to prevent, and a reason to
/// distrust every verdict obtained that way. This test asserts a property OF THE VERIFIED
/// consensus ordering; obtaining it on unaudited crypto would be self-defeating. Idempotent,
/// export-gated, once-per-process.
fn install_pq_cores_for_this_test_process() {
    dregg_node::install_verified_pq_cores();
}

/// An `n`-validator round-synchronous committee, built once (ML-DSA key derivation is per
/// signer, not per block — `Block::new` would re-derive on every call and dominate setup).
fn committee(n: usize) -> Vec<HybridBlockSigner> {
    install_pq_cores_for_this_test_process();
    (0..n)
        .map(|i| HybridBlockSigner::new(SigningKey::from_bytes(&[(i as u8) + 1; 32])))
        .collect()
}

/// Build a round-synchronous, fully cross-linked lace of `rounds` rounds over `signers`:
/// round 0 is the genesis cohort, and every later round's blocks cite ALL of the previous
/// round's. Total blocks = `signers.len() * rounds`. This is the live federation shape.
fn build_lace(signers: &[HybridBlockSigner], rounds: u64) -> (Blocklace, Vec<[u8; 32]>) {
    let participants: Vec<[u8; 32]> = signers.iter().map(|s| s.creator()).collect();
    let mut lace = Blocklace::new(
        SigningKey::from_bytes(&[1u8; 32]),
        // quorum threshold: the usual supermajority shape; irrelevant to `tau`/`tauOrder`,
        // which take the participant set explicitly.
        (signers.len() * 2) / 3 + 1,
    );

    let mut prev: Vec<BlockId> = Vec::new();
    for round in 0..rounds {
        let mut this_round = Vec::with_capacity(signers.len());
        for (i, s) in signers.iter().enumerate() {
            let b = Block::new_signed_by(
                s,
                round,
                // Turn payloads are CONSENSUS-ACTIONABLE — the same class the live producer
                // emits, so nothing here is dismissed as DAG plumbing.
                Payload::Turn(vec![(round as u8).wrapping_mul(7).wrapping_add(i as u8)]),
                prev.clone(),
            );
            this_round.push(b.id());
            lace.receive_block(b).expect("round insert");
        }
        prev = this_round;
    }
    (lace, participants)
}

/// The node's REAL Rust order for a lace: exactly what `poll_finalized_blocks` computes into
/// `rust_order` — `build_ordering_blocklace` (topological insert) then `ordering::tau`, then
/// map the ordering ids back to finality `BlockId`s.
fn node_rust_order(lace: &Blocklace, participants: &[[u8; 32]]) -> Vec<BlockId> {
    let (ordering_lace, id_map) = build_ordering_blocklace(lace);
    dregg_blocklace::ordering::tau(&ordering_lace, participants)
        .into_iter()
        .filter_map(|oid| id_map.get(&oid).copied())
        .collect()
}

/// `(creator, seq)` coordinates IN ORDER — the content-identical coordinate the two id schemes
/// (blake3 `BlockId` vs interned Lean `Nat`) share. NOT sorted: the sequence is the point.
fn coords_in_order(lace: &Blocklace, ids: &[BlockId]) -> Vec<([u8; 32], u64)> {
    ids.iter()
        .filter_map(|id| lace.get(id).map(|b| (b.creator, b.seq)))
        .collect()
}

/// ── THE GATE ────────────────────────────────────────────────────────────────────────────────
///
/// The verified Lean `dregg_tau_order` and the Rust `ordering::tau` the node SUBSTITUTES for it
/// on an over-budget poll must produce the **same sequence** of `(creator, seq)` coordinates.
///
/// This is the property the timeout fallback silently assumes. `blocklace_sync.rs` states it
/// ("the edge-faithful Rust `tau` order … == `tauOrder` after the topological build fix") and
/// then substitutes on that basis, but the differential guarding the claim SORTS before
/// comparing — so it checks the finalized SET and is blind to a pure reordering. If the two
/// ever disagree in ORDER, an over-budget poll changes the executed order of turns while every
/// existing check stays green. That is the finding this test exists to make impossible to miss.
///
/// Self-skips when the archive lacks the raw-order export (a stale/marshal-only build), unless
/// `DREGG_TEST_REQUIRE_LEAN=1`, under which the absent export PANICS — the same posture
/// `finality_gate.rs`'s gate tests take.
#[test]
fn the_two_orders_the_node_swaps_between_agree_exactly() {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::tau_order_available(),
        "the Lean raw tau-order export (tau_order_available()==false)",
    ) {
        return;
    }

    // Committee sizes and depths kept small enough to run inside a normal `cargo test` — the
    // ORDER-AGREEMENT property is not a function of scale, and the cost curve lives in the
    // #[ignore]d measurement below. n=4 is the observed federation; n=3 and n=5 bracket it
    // (n=3 is unanimity/zero-slack, n=5 has real supermajority slack).
    for n in [3usize, 4, 5] {
        let signers = committee(n);
        for rounds in [3u64, 6, 9] {
            let (lace, participants) = build_lace(&signers, rounds);
            let lean = VerifiedFinality::compute_order(&lace, &participants)
                .expect("raw-order gate ran (archive present + wire non-ERR)");
            let rust = node_rust_order(&lace, &participants);

            let lean_seq = coords_in_order(&lace, &lean);
            let rust_seq = coords_in_order(&lace, &rust);

            // ANTI-VACUITY: a comparison of two empty orders proves nothing, and an
            // un-super-ratified lace finalizes nothing. Require the verified rule to have
            // actually finalized something before reading the agreement as evidence.
            assert!(
                !lean_seq.is_empty(),
                "n={n} rounds={rounds}: the verified rule finalized NOTHING — the agreement \
                 assertion below would be vacuous. Increase the depth so a leader super-ratifies."
            );

            assert_eq!(
                lean_seq,
                rust_seq,
                "n={n} rounds={rounds} (lace={} blocks): the verified Lean `dregg_tau_order` \
                 and the Rust `ordering::tau` produced DIFFERENT SEQUENCES. The node SUBSTITUTES \
                 the Rust order for the verified one on any poll that misses the \
                 `DREGG_FINALITY_ORDER_TIMEOUT_MS` budget, so this is a live order divergence, \
                 not a lab curiosity. lean_len={} rust_len={}",
                lace.iter().count(),
                lean_seq.len(),
                rust_seq.len(),
            );

            // And the weaker property the NODE's own differential checks — pinned separately so
            // a future change that keeps the sets equal while breaking the order fails on the
            // assertion above and NOT on this one, making the distinction legible in the output.
            let mut lean_set = lean_seq.clone();
            let mut rust_set = rust_seq.clone();
            lean_set.sort_unstable();
            rust_set.sort_unstable();
            assert_eq!(
                lean_set, rust_set,
                "n={n} rounds={rounds}: finalized SETS differ (the node's own differential would \
                 have caught this one)"
            );
        }
    }
}

/// One block by `signer` at `seq` citing `preds`, received by `lace`. Returns its id.
fn put(lace: &mut Blocklace, signer: &HybridBlockSigner, seq: u64, preds: &[BlockId]) -> BlockId {
    let b = Block::new_signed_by(
        signer,
        seq,
        Payload::Turn(vec![seq as u8, preds.len() as u8]),
        preds.to_vec(),
    );
    let id = b.id();
    lace.receive_block(b).expect("causally closed insert");
    id
}

/// `rounds` round-synchronous layers over `signers`, the first layer citing `below`. Returns the
/// last layer's ids. `first_seq` is the `seq` of the first layer.
fn layers(
    lace: &mut Blocklace,
    signers: &[&HybridBlockSigner],
    first_seq: u64,
    rounds: u64,
    below: &[BlockId],
) -> Vec<BlockId> {
    let mut prev = below.to_vec();
    for r in 0..rounds {
        prev = signers
            .iter()
            .map(|s| put(lace, s, first_seq + r, &prev))
            .collect();
    }
    prev
}

/// **THE LATE-JOINER LACE** — `BlocklaceFinality.traceLateLeader`.
///
/// Four enrolled validators. Three of them run rounds 1–3 alone. The fourth JOINS at round 4:
/// its first block has `seq 0` and cites the three round-3 tips. From then on all four are an
/// ordinary fully connected committee through round 6. The participant order puts the late
/// joiner SECOND, so it is wave 1's round-robin leader (`participants[1 % 4]`, wavelength 3):
/// its round-4 block is the wave-1 leader block and the round-6 layer super-ratifies it.
///
/// Every block is honest. The only unusual thing is a `seq` that lags depth, which is what a
/// validator that joins late or falls behind produces.
fn late_joiner_lace(signers: &[HybridBlockSigner]) -> (Blocklace, Vec<[u8; 32]>) {
    assert_eq!(signers.len(), 4);
    let (early, late) = (&signers[..3], &signers[3]);
    let early: Vec<&HybridBlockSigner> = early.iter().collect();
    let participants = vec![
        early[0].creator(),
        late.creator(), // wave 1's leader
        early[1].creator(),
        early[2].creator(),
    ];
    let mut lace = Blocklace::new(SigningKey::from_bytes(&[1u8; 32]), 3);

    let r3 = layers(&mut lace, &early, 0, 3, &[]);
    // round 4: the three early validators' `seq 3`, and the late joiner's `seq 0`.
    let mut r4: Vec<BlockId> = early.iter().map(|s| put(&mut lace, s, 3, &r3)).collect();
    r4.push(put(&mut lace, late, 0, &r3));
    // rounds 5 and 6: everyone, fully connected.
    let mut prev = r4;
    for r in 0..2u64 {
        let mut next: Vec<BlockId> = early
            .iter()
            .map(|s| put(&mut lace, s, 4 + r, &prev))
            .collect();
        next.push(put(&mut lace, late, 1 + r, &prev));
        prev = next;
    }
    (lace, participants)
}

/// **THE RELAY LACE** — `BlocklaceFinality.traceRelayLift6`, the reporter's exhibit.
///
/// Four enrolled validators and one UNENROLLED relay. Three validators run rounds 1–3. The relay
/// cites the three round-3 tips. The fourth validator's only block cites the genesis layer AND
/// the relay — so it sits at round 2 (a non-participant contributes no depth) while the round-3
/// layer is in its causal past, through the relay. The three then cite it from round 4 and run
/// on to round 6, where wave 1's leader (the second participant's round-4 block) anchors.
///
/// Every block passes the admission checks; nothing here needs a Byzantine validator.
fn relay_lace(
    signers: &[HybridBlockSigner],
    relay: &HybridBlockSigner,
) -> (Blocklace, Vec<[u8; 32]>) {
    assert_eq!(signers.len(), 4);
    let core: Vec<&HybridBlockSigner> = signers[..3].iter().collect();
    let lifted = &signers[3];
    let participants: Vec<[u8; 32]> = signers.iter().map(|s| s.creator()).collect();
    assert!(
        !participants.contains(&relay.creator()),
        "the relay must not be enrolled — else this lace has no relay"
    );
    let mut lace = Blocklace::new(SigningKey::from_bytes(&[1u8; 32]), 3);

    let r1 = layers(&mut lace, &core, 0, 1, &[]);
    let r3 = layers(&mut lace, &core, 1, 2, &r1);
    let relay_id = put(&mut lace, relay, 0, &r3);
    let mut lifted_preds = r1.clone();
    lifted_preds.push(relay_id);
    let lifted_id = put(&mut lace, lifted, 0, &lifted_preds);
    let mut below = r3.clone();
    below.push(lifted_id);
    layers(&mut lace, &core, 3, 3, &below);
    (lace, participants)
}

/// Every block's inclusive causal past, by reachability over the predecessors the lace holds.
/// This is the DEFINITION the order is checked against, not a mirror of either implementation.
fn causal_pasts(lace: &Blocklace) -> HashMap<BlockId, HashSet<BlockId>> {
    let mut out = HashMap::new();
    for (id, _) in lace.iter() {
        let mut seen: HashSet<BlockId> = HashSet::new();
        let mut stack = vec![*id];
        while let Some(x) = stack.pop() {
            if !seen.insert(x) {
                continue;
            }
            if let Some(b) = lace.get(&x) {
                stack.extend(
                    b.predecessors
                        .iter()
                        .filter(|p| lace.get(p).is_some())
                        .copied(),
                );
            }
        }
        out.insert(*id, seen);
    }
    out
}

/// The first pair `(earlier, later)` in `order` where `later` is a causal ancestor of `earlier`
/// — i.e. the witness that `order` is NOT a linear extension of the causal order.
fn causal_inversion(
    lace: &Blocklace,
    pasts: &HashMap<BlockId, HashSet<BlockId>>,
    order: &[BlockId],
) -> Option<(([u8; 32], u64), ([u8; 32], u64))> {
    let coord = |id: &BlockId| lace.get(id).map(|b| (b.creator, b.seq)).expect("held id");
    for (i, x) in order.iter().enumerate() {
        for a in &order[i + 1..] {
            if a != x && pasts[x].contains(a) {
                return Some((coord(x), coord(a)));
            }
        }
    }
    None
}

/// ── THE SHAPES THE ROUND-SYNCHRONOUS GATE CANNOT SEE (dregg issue #100) ────────────────────
///
/// On a late-joiner lace and on a relay lace, the verified Lean order and the Rust
/// `ordering::tau` order must finalize the SAME SET, and EACH must be a linear extension of the
/// causal order (no block before one of its own ancestors).
///
/// Both halves are needed, and each catches one defect:
///
/// * the late joiner's wrong round changed WHICH wave anchors, so the two finalized SETS
///   differed (one coordinate against ten) — the set assertion;
/// * the relay left the set intact and put a block ahead of three of its ancestors — only the
///   linear-extension assertion sees that.
///
/// The sequences are deliberately NOT compared here; see the module header.
#[test]
fn the_verified_order_survives_a_late_joiner_and_a_relay() {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::tau_order_available(),
        "the Lean raw tau-order export (tau_order_available()==false)",
    ) {
        return;
    }

    let signers = committee(4);
    let relay = HybridBlockSigner::new(SigningKey::from_bytes(&[0x77; 32]));
    let cases: [(&str, (Blocklace, Vec<[u8; 32]>), usize); 2] = [
        // ten: the wave-0 anchor, then rounds 1-3 minus that anchor (eight) and the wave-1
        // leader block itself — the late joiner's.
        ("late joiner", late_joiner_lace(&signers), 10),
        // eleven: the wave-0 anchor, then rounds 1-3 minus it (eight), the lifted block, and the
        // wave-1 leader block. The relay's own block is not enrolled and is not ordered.
        ("relay", relay_lace(&signers, &relay), 11),
    ];

    // Every case runs and every violated property is collected, so one run names BOTH defects
    // rather than stopping at the first.
    let mut failures: Vec<String> = Vec::new();
    for (name, (lace, participants), expected_len) in cases {
        let lean = VerifiedFinality::compute_order(&lace, &participants)
            .expect("raw-order gate ran (archive present + wire non-ERR)");
        let rust = node_rust_order(&lace, &participants);
        let pasts = causal_pasts(&lace);

        // ANTI-VACUITY, and the late joiner's tooth: the wave the late joiner leads must anchor.
        if lean.len() != expected_len {
            failures.push(format!(
                "{name}: the verified rule finalized {} coordinates, expected {expected_len}. On \
                 the late-joiner lace a short order means the joiner's first block got the wrong \
                 round and its wave never anchored (the `(seq, creator)` fold of dregg issue #100).",
                lean.len(),
            ));
        }

        let mut lean_set = coords_in_order(&lace, &lean);
        let mut rust_set = coords_in_order(&lace, &rust);
        lean_set.sort_unstable();
        rust_set.sort_unstable();
        if lean_set != rust_set {
            failures.push(format!(
                "{name}: the verified Lean rule and `ordering::tau` finalized DIFFERENT SETS \
                 (lean_len={} rust_len={})",
                lean.len(),
                rust.len(),
            ));
        }

        // The relay's tooth: neither order may put a block before one of its own ancestors.
        if let Some((earlier, later)) = causal_inversion(&lace, &pasts, &lean) {
            failures.push(format!(
                "{name}: the verified Lean order is NOT a linear extension of the causal order — \
                 it emits (creator {:02x?}.., seq {}) before (creator {:02x?}.., seq {}), which \
                 is in its causal past",
                &earlier.0[..4],
                earlier.1,
                &later.0[..4],
                later.1,
            ));
        }
        if causal_inversion(&lace, &pasts, &rust).is_some() {
            failures.push(format!(
                "{name}: the Rust `ordering::tau` order is NOT a linear extension of the causal order"
            ));
        }

        // No unenrolled creator is ordered, on either side.
        if lean
            .iter()
            .chain(rust.iter())
            .any(|id| !participants.contains(&lace.get(id).expect("ordered id is held").creator))
        {
            failures.push(format!(
                "{name}: an unenrolled creator's block was finalized"
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "the verified order and its Rust twin disagree with the causal order or with each other:\n  - {}",
        failures.join("\n  - ")
    );
}

/// ── THE MEASUREMENT INSTRUMENT (not a gate) ─────────────────────────────────────────────────
///
/// Print the verified-Lean τ-order FFI cost against lace size, alongside the Rust `ordering::tau`
/// cost on the same lace, and mark where the per-poll budget is crossed.
///
/// `#[ignore]` because it asserts nothing about wall-clock (which prices the box and its load,
/// not the code) and because the large sizes take minutes. Run it explicitly, ON A QUIET BOX,
/// and read the table:
///
/// ```text
/// cargo test -p dregg-node --test verified_order_budget -- --ignored --nocapture
/// ```
///
/// Knobs: `ORDER_BUDGET_N` (committee size, default 4), `ORDER_BUDGET_ROUNDS`
/// (comma-separated round counts), `ORDER_BUDGET_CEILING_MS` (stop growing once one FFI call
/// exceeds this, default 120000).
///
/// Set agreement is asserted at EVERY size here too, and each row says whether the two SEQUENCES
/// agreed — so the agreement evidence is not confined to the small laces the gate above can
/// afford.
#[test]
#[ignore = "measurement instrument: wall-clock, minutes long, run explicitly on a quiet box"]
fn verified_order_cost_curve() {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::tau_order_available(),
        "the Lean raw tau-order export (tau_order_available()==false)",
    ) {
        return;
    }

    let n: usize = std::env::var("ORDER_BUDGET_N")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(4);
    let rounds_list: Vec<u64> = std::env::var("ORDER_BUDGET_ROUNDS")
        .ok()
        .map(|v| v.split(',').filter_map(|p| p.trim().parse().ok()).collect())
        .unwrap_or_else(|| vec![5, 10, 20, 40, 60, 80, 120, 160, 240]);
    let ceiling = Duration::from_millis(
        std::env::var("ORDER_BUDGET_CEILING_MS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(120_000),
    );

    let signers = committee(n);

    eprintln!(
        "# verified tau-order FFI cost curve  (committee n={n}, round-synchronous, fully cross-linked)"
    );
    eprintln!(
        "# per-poll budget = {} ms (blocklace_sync::verified_order_ffi_timeout default)",
        DEFAULT_PER_POLL_BUDGET.as_millis()
    );
    eprintln!("#");
    eprintln!(
        "#   blocks   lean_ms   rust_ms   lean/rust   vs_budget   growth_exp   finalized  sequence"
    );

    let mut prev: Option<(f64, f64)> = None; // (blocks, lean_ms)
    for rounds in rounds_list {
        let (lace, participants) = build_lace(&signers, rounds);
        let blocks = lace.iter().count();

        let t0 = Instant::now();
        let lean = VerifiedFinality::compute_order(&lace, &participants)
            .expect("raw-order gate ran (archive present + wire non-ERR)");
        let lean_ms = t0.elapsed().as_secs_f64() * 1000.0;

        let t1 = Instant::now();
        let rust = node_rust_order(&lace, &participants);
        let rust_ms = t1.elapsed().as_secs_f64() * 1000.0;

        // Agreement, re-checked at every measured size — at the level the two linearizers are
        // required to agree at: the finalized SET. The exact SEQUENCE is the gate above, and it
        // is RED as soon as a second wave anchors (OPEN-CM-XSORT: the two break ready ties
        // differently), so asserting it here made the instrument stop at its second row and
        // print no curve. `seq_agree` reports it instead.
        let lean_seq = coords_in_order(&lace, &lean);
        let rust_seq = coords_in_order(&lace, &rust);
        let seq_agree = lean_seq == rust_seq;
        let mut lean_set = lean_seq.clone();
        let mut rust_set = rust_seq.clone();
        lean_set.sort_unstable();
        rust_set.sort_unstable();
        assert_eq!(
            lean_set,
            rust_set,
            "blocks={blocks}: verified Lean order and Rust `ordering::tau` finalized DIFFERENT \
             SETS at scale (lean_len={} rust_len={})",
            lean_seq.len(),
            rust_seq.len()
        );

        // Local growth exponent between consecutive points: log(t2/t1) / log(n2/n1). A pure
        // O(n^k) shows k here; it is the only load-robust number in the table (a steady load
        // factor cancels in the ratio).
        let exp = match prev {
            Some((pb, pt)) if pt > 0.0 && pb > 0.0 && blocks as f64 > pb => {
                format!(
                    "{:>10.2}",
                    (lean_ms / pt).ln() / ((blocks as f64) / pb).ln()
                )
            }
            _ => format!("{:>10}", "-"),
        };
        let verdict = if lean_ms > DEFAULT_PER_POLL_BUDGET.as_millis() as f64 {
            "OVER"
        } else {
            "under"
        };
        eprintln!(
            "  {blocks:>8}  {lean_ms:>8.1}  {rust_ms:>8.2}  {:>9.1}x  {verdict:>9}  {exp}  {:>9}  {}",
            if rust_ms > 0.0 {
                lean_ms / rust_ms
            } else {
                0.0
            },
            lean_seq.len(),
            if seq_agree { "same-seq" } else { "SEQ-DIFFERS" },
        );
        prev = Some((blocks as f64, lean_ms));

        if t0.elapsed() > ceiling {
            eprintln!(
                "# stopping: a single FFI call exceeded the {} ms measurement ceiling",
                ceiling.as_millis()
            );
            break;
        }
    }
}
