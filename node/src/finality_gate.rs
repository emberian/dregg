//! Verified FINALITY GATE — gate the live commit on the Lean-exported finalization rule.
//!
//! # What this is
//!
//! `blocklace_sync::poll_finalized_blocks` computes the finalized total order with the Rust
//! `dregg_blocklace::ordering::tau` and serves the not-yet-executed blocks (tracked BY IDENTITY in
//! `crate::execution_cursor::ExecutionCursor`; see TauPrefixMonotone) to the executor. The
//! verified Lean model of that rule (`metatheory/Dregg2/Distributed/BlocklaceFinality.lean`:
//! `computeRounds`/`findAllFinalLeaders`/`tauOrder`) was, until now, only AGREEMENT-CHECKED in a
//! unit test (`ordering::tests::test_tau_differential_against_lean_model`). It did NOT gate the live
//! commit.
//!
//! This module converts "agreement-checked" into "Lean-gated". At commit time it:
//!   1. wire-encodes the SAME `(wavelength, participants, lace)` the Rust `tau` consumes, using the
//!      grammar `Dregg2.Distributed.FinalityGate.encodeLaceWire` mirrors byte-for-byte;
//!   2. calls the verified Lean rule via the FFI export `dregg_blocklace_finalize`
//!      (`dregg_lean_ffi::shadow_blocklace_finalize`), which runs `BlocklaceFinality.tauOrder` and
//!      returns the verified finalized order projected to `(creator, seq)` (the differential
//!      coordinate — the `BlockId` hash differs Rust↔Lean, but `(creator, seq)` is content-identical);
//!   3. exposes [`VerifiedFinality::admits`] — "the verified rule finalizes this `(creator, seq)`" —
//!      so `poll_finalized_blocks` admits a block to the executor ONLY when the verified rule
//!      finalizes it.
//!
//! The Lean theorem `gate_admits_iff_verified_finalizes` proves `admits` is EXACTLY membership in the
//! verified `tauGolden` order, so gating on it IS gating on the verified `BlocklaceFinality.tauOrder`.
//!
//! # Flag + fail-safety
//!
//! Gated by [`finality_gate_enabled`] (`DREGG_FINALITY_GATE`, **default ON**). When the archive HAS
//! the export and the rule disagrees with the Rust `tau` on a `(creator, seq)`, the gate REFUSES that
//! block (it is not sliced to the executor) and records the divergence — the verified rule wins.
//!
//! ⚑ **FAILS CLOSED when the gate cannot answer.** This is a CORRECTION: until
//! `blocklace_sync::finality_belt_disposition` landed, a missing export / `ERR` wire / panicked FFI
//! thread made the gate a NO-OP WITH A WARNING and the poll advanced finality over the **un-gated**
//! Rust tau order — the same fail-OPEN class as the conservation twin
//! (`turn/src/executor/atomic.rs`'s `ConservationGateUnavailable`). [`VerifiedFinality::compute`]
//! still collapses every failure to `None`; what changed is the CALLER's disposition: a `None` where
//! the belt is armed now REFUSES to advance finality (finalize nothing this poll, re-attempt later)
//! unless one of two DECLARED bypasses holds — no `dregg_blocklace_finalize` export linked at all, or
//! the operator's `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`. `DREGG_REQUIRE_LEAN=1` revokes both. The
//! bypasses are declared in `scripts/ci-invariants/gate-dataflow.tsv` (invariant 6), which slices
//! the disposition and reddens if the gate-absent path can admit.
//!
//! # ⚑ The enrollment repair — the rule now knows WHO IS ENROLLED
//!
//! [`VerifiedFinality::admits`] used to document that an unenrolled key "is never interned and
//! never admitted". Both halves were false, and
//! `tests::attacker_block_from_unenrolled_creator_is_refused_by_the_verified_rule` FAILED on it:
//! the verified rule finalized 100% of a 4-creator lace with 3 enrolled, including all three of
//! the unenrolled creator's blocks. The rule consulted `participants` for the round-robin leader
//! schedule and the supermajority count, and NEVER for who may be ordered at all.
//!
//! REACHABILITY — this was NOT only defence-in-depth. `receive_block_pinned`'s
//! `BlockError::UnenrolledCreator` is the sole enrollment filter on the live ingest path, and two
//! production paths get past it without any attack on it:
//!   * **rotation-out.** The pinned roster is INSERT-ONLY (`blocklace/src/finality.rs::enroll_pq`;
//!     `blocklace_sync.rs::apply_committee_change` says so outright) while
//!     `constitution.current.participants` SHRINKS on a passed membership proposal
//!     (`blocklace_sync.rs::apply_passed_proposal`). A removed validator's NEW blocks keep passing
//!     the pinned ingest while it is absent from the `participants` slice this gate is handed —
//!     the falsifier's exact configuration, reached by an ordinary governance action.
//!   * **restart.** `blocklace/src/finality.rs::from_checkpoint`, reached from
//!     `blocklace_sync.rs`'s boot `store.load_blocklace`, re-authenticates every block on restore
//!     (ed25519 signature + causal closure + equivocation re-derived, since 2026-08-08 — it was
//!     the verbatim `from_checkpoint_trusted` before that) but still enforces NO roster check:
//!     an unenrolled creator's validly-signed blocks come back.
//!
//! THE FIX is in the verified rule, in Lean, where the rule lives:
//! `BlocklaceFinality.enrolledId` + `tauOrder`/`tauOrderFast`/`tauOrderFastImpl`, with
//! `tauOrder_only_enrolled` (every finalized block's creator is a participant, NO hypothesis on
//! the lace) and `tauOrder_enrolled_eq_unfiltered` (on an all-enrolled lace the filter is the
//! identity — a pure subtraction, not a liveness trade). `blocklace/src/ordering.rs::tau` carries
//! the mirror so the live per-poll Rust↔Lean differential stays silent on an attacked lace.

use std::collections::HashMap;

use dregg_blocklace::finality::{Block, BlockId, Blocklace};

/// The Cordial-Miners wavelength `tau` uses (`ordering::OrderingConfig::default().wavelength`).
/// The Lean model is parameterized by wavelength and the node runs the default-3 ordering, so the
/// wire we hand the verified rule MUST carry 3 (the Lean `#guard`s also use wavelength 3).
const WAVELENGTH: u64 = 3;

/// Whether the live finality gate is enabled. **Default ON** (per the devnet-readiness directive: the
/// verified rule gates new state). `DREGG_FINALITY_GATE=0`/`false`/`off` opts OUT (keeps the legacy
/// un-gated path) for an operator who needs to bypass it.
pub fn finality_gate_enabled() -> bool {
    !matches!(
        std::env::var("DREGG_FINALITY_GATE").ok().as_deref(),
        Some("0") | Some("false") | Some("FALSE") | Some("off") | Some("OFF")
    )
}

/// The verified finalized order, as the set of `(creator_id, seq)` coordinates the verified Lean rule
/// finalizes, PLUS the creator-interning table used to encode the wire (so the caller can map a Rust
/// `Block` back to its `creator_id`). Construct via [`VerifiedFinality::compute`].
#[derive(Debug, Clone)]
pub struct VerifiedFinality {
    /// `(creator_id, seq)` pairs the verified rule finalized. `creator_id` is the participant index
    /// (the `AuthorId` the Lean wire used); a block whose `(creator_id, seq)` is in this set is
    /// admitted.
    finalized: std::collections::HashSet<(u64, u64)>,
    /// creator HYBRID id (`H(ed25519 ‖ ml_dsa)`, == `Block::creator`) -> the small `AuthorId`
    /// (participant index) used on the wire. Both the interned participant set and the block
    /// `creator`s are keyed by this hybrid id, so leader-matching is identity-consistent.
    creator_ids: HashMap<[u8; 32], u64>,
}

/// The wire-encoded lace + the interning tables the finality gates share. Produced once by
/// [`VerifiedFinality::build_wire`] and consumed by both the `(creator, seq)`-projection gate
/// (`compute`) and the RAW total-order gate (`compute_order`), so the two read the EXACT same wire.
struct LaceWire {
    /// The `"w=<W>;P=<...>;B=<...>"` wire the Lean rule consumes (the grammar `encodeLaceWire` mirrors).
    wire: String,
    /// creator pubkey -> the small `AuthorId` (participant index) used on the wire.
    creator_ids: HashMap<[u8; 32], u64>,
    /// the interned Lean `BlockId` (a `u64` index) -> the node's real `BlockId`. The inverse of the
    /// interning the wire uses, so the RAW-order export's `u64` ids map back to node blocks.
    id_to_block: HashMap<u64, BlockId>,
}

/// Canonical id ranking; a stable sort without the final comparison is insufficient for twins.
fn sort_wire_blocks(blocks: &mut [(&BlockId, &Block)]) {
    blocks.sort_by(|(ai, a), (bi, b)| {
        a.seq
            .cmp(&b.seq)
            .then_with(|| a.creator.cmp(&b.creator))
            .then_with(|| ai.cmp(bi))
    });
}

impl VerifiedFinality {
    /// Build the wire + interning tables ONCE — shared by `compute` (projection) and `compute_order`
    /// (raw total order), so both gates hand the verified rule byte-identical input. Interns creators
    /// to the participant index (the round-robin `participants[w % n]` leader, matching BOTH `tau` and
    /// the Lean `waveLeader`) and block ids to their index in a `(seq, creator, source id)` sort of the lace
    /// (so the wire's `BlockId`s are a faithful relabeling of it).
    ///
    /// ⚑ That sort is NOT a causal order — a late joiner's `seq 0` block precedes the blocks it
    /// cites — and the verified rule must not treat it as one. `BlocklaceFinality.computeRounds`
    /// did, until dregg issue #100; it now enumerates the wire's blocks with Kahn's algorithm and
    /// its rounds are proved independent of the listing (`roundOf_perm`). What the sort still
    /// decides is the Lean tie-break: `xsortBy` breaks ready ties by `(round, seq, id)`, and `id` is
    /// this canonical `(seq, creator bytes, source block id)` rank.
    fn build_wire(lace: &Blocklace, participants: &[[u8; 32]]) -> LaceWire {
        let mut creator_ids: HashMap<[u8; 32], u64> = HashMap::new();
        for (i, p) in participants.iter().enumerate() {
            creator_ids.entry(*p).or_insert(i as u64);
        }
        let mut next_extra = participants.len() as u64;

        let mut blocks: Vec<(&BlockId, &Block)> = lace.iter().collect();
        sort_wire_blocks(&mut blocks);

        let mut id_ids: HashMap<BlockId, u64> = HashMap::new();
        let mut id_to_block: HashMap<u64, BlockId> = HashMap::new();
        for (i, (id, _)) in blocks.iter().enumerate() {
            id_ids.insert(**id, i as u64);
            id_to_block.insert(i as u64, **id);
        }

        let participants_wire: Vec<String> =
            (0..participants.len()).map(|i| i.to_string()).collect();

        let mut block_wires: Vec<String> = Vec::with_capacity(blocks.len());
        for (id, b) in &blocks {
            let creator_id = *creator_ids.entry(b.creator).or_insert_with(|| {
                let v = next_extra;
                next_extra += 1;
                v
            });
            let id_id = *id_ids.get(*id).expect("interned above");
            // Only predecessors PRESENT in the lace are edges `tau`/`tauOrder` traverse.
            let preds: Vec<String> = b
                .predecessors
                .iter()
                .filter_map(|p| id_ids.get(p).map(|n| n.to_string()))
                .collect();
            block_wires.push(format!(
                "{id_id}:{creator_id}:{seq}:{preds}",
                seq = b.seq,
                preds = preds.join(".")
            ));
        }

        let wire = format!(
            "w={W};P={P};B={B}",
            W = WAVELENGTH,
            P = participants_wire.join(","),
            B = block_wires.join("|")
        );
        LaceWire {
            wire,
            creator_ids,
            id_to_block,
        }
    }

    /// The bare `"w=<W>;P=<...>;B=<...>"` lace wire, for gates that PREFIX it with their own
    /// fields (the ES round-advance gate `crate::round_advance_gate::advance_wire` prepends
    /// `r=<round>;t=<bit>;`). ONE encoder for every consensus gate — a second encoder is how two
    /// gates come to disagree about what the lace says.
    pub(crate) fn lace_wire(lace: &Blocklace, participants: &[[u8; 32]]) -> String {
        Self::build_wire(lace, participants).wire
    }

    /// Run the VERIFIED Lean RAW TOTAL-ORDER rule (`dregg_tau_order`, the export proved
    /// order-faithfully equal to `BlocklaceFinality.tauOrder` by `tau_order_export_eq`) over the lace
    /// and return the finalized total order as node `BlockId`s, in the verified order. `None` when the
    /// raw-order export is unavailable (stale archive) or the wire returns `ERR` (the caller falls back
    /// to the Rust `tau` order). Unlike [`Self::compute`] (the `(creator, seq)`-set projection used for
    /// per-block admission), this is the FULL ordered id list — the verified `tauOrder` itself.
    pub fn compute_order(lace: &Blocklace, participants: &[[u8; 32]]) -> Option<Vec<BlockId>> {
        let LaceWire {
            wire, id_to_block, ..
        } = Self::build_wire(lace, participants);
        // The raw-order export returns the verified `tauOrder` as the interned-`u64` id list. Map each
        // back to the node's `BlockId`; an id the wire never interned (impossible for a well-formed
        // `tauOrder`, which only emits present ids) is dropped fail-safe.
        let order = dregg_lean_ffi::verified_tau_order(&wire).ok()?;
        Some(
            order
                .into_iter()
                .filter_map(|u| id_to_block.get(&u).copied())
                .collect(),
        )
    }

    /// Run the VERIFIED Lean finalization rule over the lace and participants. `Some(_)` is the
    /// verified finalized set (the gate ran and produced a non-`ERR` order); `None` means THE GATE
    /// COULD NOT ANSWER — a missing export, an `ERR` wire, or an unparseable reply — and every failure
    /// mode collapses to it so the caller has ONE gate-absent branch.
    ///
    /// ⚑ `None` IS NOT A PERMISSION TO PROCEED. The caller
    /// (`blocklace_sync::finality_belt_disposition`) FAILS CLOSED on it: a poll that would advance
    /// finality over a non-Lean-produced order finalizes NOTHING instead, unless a declared bypass
    /// holds (no export linked at all / `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`, both revoked by
    /// `DREGG_REQUIRE_LEAN=1`). It used to fail OPEN here; that was the defect.
    pub fn compute(lace: &Blocklace, participants: &[[u8; 32]]) -> Option<VerifiedFinality> {
        let LaceWire {
            wire, creator_ids, ..
        } = Self::build_wire(lace, participants);

        // Call the verified Lean rule. On any error (archive missing the export, init failure) or the
        // `ERR` sentinel, return None — GATE UNAVAILABLE, which the caller fails CLOSED on.
        let out = match dregg_lean_ffi::shadow_blocklace_finalize(&wire) {
            Ok(s) => s,
            Err(_) => return None,
        };
        let body = out.strip_prefix("F=")?; // `ERR` (or anything else) -> None -> gate unavailable.

        let mut finalized = std::collections::HashSet::new();
        if !body.is_empty() {
            for pair in body.split(',') {
                let (c, s) = pair.split_once(':')?;
                let c: u64 = c.parse().ok()?;
                let s: u64 = s.parse().ok()?;
                finalized.insert((c, s));
            }
        }
        Some(VerifiedFinality {
            finalized,
            creator_ids,
        })
    }

    /// Whether the verified rule finalizes a block — by its `(creator hybrid id, seq)`. `creator` is
    /// the `Block::creator` hybrid id `H(ed25519 ‖ ml_dsa)`, the same key the participant set interns
    /// under. The node calls this per Rust-finalized block before slicing it to the executor:
    /// `true` ⇒ admit, `false` ⇒ REFUSE (the verified rule did not finalize it). Mirrors the Lean
    /// `gateAdmits` predicate.
    ///
    /// ⚑ CORRECTED. This used to read "an attacker key that does not match an enrolled hybrid
    /// participant is never interned and never admitted". BOTH clauses were false, and
    /// `tests::attacker_block_from_unenrolled_creator_is_refused_by_the_verified_rule` measured it:
    /// [`Self::build_wire`]'s `next_extra` DOES intern every creator it meets, and the verified
    /// `BlocklaceFinality.tauOrder` had NO identity filter — `leaderCoverage` (a def since deleted
    /// with the `d182d10fc` τ-CM rewrite) was the union of the
    /// causal pasts of the ratifying wave-end blocks, so an unenrolled creator's blocks were swept
    /// into the finalized order the moment one honest node acked them. On a 4-creator / 3-round
    /// lace with 3 enrolled, the verified rule finalized 12 of 12 coordinates, all three of the
    /// attacker's included.
    ///
    /// What is true NOW, and why the two clauses are different:
    ///   * INTERNED — YES, still, ON PURPOSE. `build_wire` puts the unenrolled creator on the wire
    ///     with an `AuthorId` past `participants.len()`. That is what makes a `false` here the
    ///     VERIFIED RULE declining, not a `HashMap` miss — the falsifier asserts the interning
    ///     explicitly so the refusal cannot be laundered into a lookup failure.
    ///   * NEVER ADMITTED — YES, and now by a theorem rather than a hope.
    ///     `BlocklaceFinality.enrolledId` filters the finalized order to enrolled creators and
    ///     `tauOrder_only_enrolled` proves every finalized block's creator is in `participants`,
    ///     with NO hypothesis on the lace. `tauOrder_enrolled_eq_unfiltered` proves the filter is
    ///     the identity on a lace whose every creator IS enrolled, so honest finality is unchanged.
    pub fn admits(&self, creator: &[u8; 32], seq: u64) -> bool {
        match self.creator_ids.get(creator) {
            Some(cid) => self.finalized.contains(&(*cid, seq)),
            // A creator the wire never interned (e.g. a non-participant / attacker hybrid id) cannot
            // have been finalized.
            None => false,
        }
    }

    /// Number of `(creator, seq)` coordinates the verified rule finalized (for diagnostics).
    pub fn len(&self) -> usize {
        self.finalized.len()
    }

    /// Whether the verified rule finalized nothing.
    pub fn is_empty(&self) -> bool {
        self.finalized.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_blocklace::finality::{Block, Payload};
    use ed25519_dalek::SigningKey;

    fn key(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    /// Two full waves at wavelength 3 — the shortest fully cross-linked lace whose order covers wave 0.
    ///
    /// Under Cordial Miners Def. 6 (`d182d10fc`) an anchor orders ITS OWN closure. The wave-0 anchor
    /// is a seq-0 block with no predecessors, so a three-round lace finalizes exactly that one block
    /// (Lean `trace3`); the rest of wave 0 is ordered one wave later by the wave-1 anchor
    /// `wave_leader(1)` at seq 3, once seq 5 super-ratifies it (Lean `trace6`, golden
    /// `[10, 20, 30, 11, 21, 31, 12, 22, 32, 23]`).
    const TWO_WAVES: u64 = 6;

    /// Build a `rounds`-round, fully cross-linked lace over `creators` — each round's blocks reference
    /// ALL of the previous round, the shape of the Lean `trace3`/`trace6`. Every block carries a Turn
    /// payload (actionable), matching what the live producer emits.
    ///
    /// `receive_block` (ed25519-only) is deliberate: it does NOT filter by enrollment, so a caller can
    /// put a non-participant's blocks into the lace and let the FINALITY GATE be the thing under test.
    /// The live wire uses `receive_block_pinned` — which refuses an unenrolled creator, but see the
    /// falsifier's HONEST SCOPE below for the two production paths that reach the same lace state
    /// (roster rotation-out, and the roster-blind `from_checkpoint` restore on restart) without
    /// that check applying.
    fn cross_linked_lace(creators: &[SigningKey], rounds: u64, quorum: usize) -> Blocklace {
        let mut lace = Blocklace::new(creators[0].clone(), quorum);
        let mut round_prev: Vec<BlockId> = Vec::new();
        for round in 0u64..rounds {
            let mut this_round = Vec::new();
            for (i, k) in creators.iter().enumerate() {
                let b = Block::new(
                    k,
                    round,
                    Payload::Turn(vec![(round * 10) as u8 + i as u8]),
                    round_prev.clone(),
                );
                this_round.push(b.id());
                lace.receive_block(b).expect("block insert");
            }
            round_prev = this_round;
        }
        lace
    }

    #[test]
    fn wire_ids_break_equivocating_twins_by_source_id() {
        crate::install_verified_pq_cores();
        let signer = key(73);
        let twins = [
            Block::new(&signer, 0, Payload::Turn(vec![1]), vec![]),
            Block::new(&signer, 0, Payload::Data(vec![1]), vec![]),
        ];
        let mut expected: Vec<_> = twins.iter().map(Block::id).collect();
        expected.sort();
        let ids: Vec<_> = twins.iter().map(Block::id).collect();
        let mut reversed: Vec<_> = ids.iter().zip(&twins).collect();
        reversed.sort_by_key(|(id, _)| std::cmp::Reverse(**id));
        sort_wire_blocks(&mut reversed);
        assert_eq!(
            reversed.iter().map(|(id, _)| **id).collect::<Vec<_>>(),
            expected
        );
        for reverse in [false, true] {
            for _ in 0..2 {
                let mut lace = Blocklace::new(signer.clone(), 1);
                for i in if reverse { [1, 0] } else { [0, 1] } {
                    // Equivocation may report an error, but both evidence blocks must be stored.
                    let _ = lace.receive_block(twins[i].clone());
                }
                let wire = VerifiedFinality::build_wire(&lace, &[twins[0].creator]);
                assert_eq!(wire.id_to_block.len(), 2);
                assert_eq!(wire.id_to_block[&0], expected[0]);
                assert_eq!(wire.id_to_block[&1], expected[1]);
                let (projection, mapping) = crate::blocklace_sync::build_ordering_blocklace(&lace);
                assert_eq!(
                    projection.len(),
                    2,
                    "distinct source blocks must not collapse"
                );
                for id in &expected {
                    assert_eq!(
                        mapping[&id.0], *id,
                        "projection must preserve source identity"
                    );
                    assert!(projection.get(&id.0).is_some());
                }
            }
        }
    }

    /// Exercise the production projection, including its causal insertion and source identities.
    fn rust_tau_order(lace: &Blocklace, participants: &[[u8; 32]]) -> Vec<([u8; 32], u64)> {
        let (ordering_lace, ids) = crate::blocklace_sync::build_ordering_blocklace(lace);
        dregg_blocklace::ordering::tau(&ordering_lace, participants)
            .iter()
            .map(|id| {
                let b = lace.get(&ids[id]).expect("ordered source block");
                (b.creator, b.seq)
            })
            .collect()
    }

    /// What a fully cross-linked TWO_WAVES lace over `participants` must finalize: every block of
    /// wave 0 (seqs 0..3) and the wave-1 anchor that orders them — `trace6`'s golden set.
    fn two_wave_finalized(participants: &[[u8; 32]]) -> std::collections::HashSet<([u8; 32], u64)> {
        let mut set: std::collections::HashSet<([u8; 32], u64)> = participants
            .iter()
            .flat_map(|p| (0u64..3).map(move |s| (*p, s)))
            .collect();
        set.insert((dregg_blocklace::ordering::wave_leader(1, participants), 3));
        set
    }

    /// **THE TOOTH — a REAL lace, a REAL attacker block, and the VERIFIED rule refuses it.**
    ///
    /// The adversary is a fourth node with a perfectly valid key that was never enrolled. It creates
    /// genuinely well-formed, correctly-hybrid-signed blocks at every round, fully cross-linked into
    /// the honest DAG (so they are causally indistinguishable from honest blocks to anything that does
    /// not check identity), and the honest nodes reference them back. The block passes
    /// `receive_block`'s own verification — this is not a malformed-input test.
    ///
    /// HONEST SCOPE — ⚑ CORRECTED, upward. This used to say "on the live wire the node ingests via
    /// `receive_block_pinned`, which ALSO refuses an unenrolled creator — so this gate is the second
    /// layer, not the only one." `receive_block_pinned` IS the only other enrollment filter on the
    /// live path, but it is not a layer this configuration has to defeat, because two ORDINARY
    /// production paths produce it without touching that check:
    ///   * ROTATION-OUT. The pinned roster is INSERT-ONLY (`blocklace/src/finality.rs::enroll_pq`;
    ///     `blocklace_sync.rs::apply_committee_change` states it) while
    ///     `constitution.current.participants` shrinks on a passed membership proposal
    ///     (`blocklace_sync.rs::apply_passed_proposal`), and `poll_finalized_blocks` re-reads the
    ///     constitution every poll. A removed validator's NEW blocks keep passing the pinned ingest
    ///     while it is absent from the `participants` this gate is handed — exactly the lace below,
    ///     produced by governance rather than by an attacker.
    ///   * RESTART. `blocklace/src/finality.rs::from_checkpoint` rebuilds the lace from redb —
    ///     re-authenticated since 2026-08-08 (signature + closure + equivocation), but still with
    ///     NO roster check: an unenrolled creator's validly-signed blocks come back.
    /// So this is not a spare tyre. `receive_block` (ed25519-only) is still the right ingest for the
    /// test — it puts the adversary in front of the rule under test rather than in front of a
    /// predecessor that, on these two paths, is not there.
    ///
    /// This is NOT a vacuous "unknown creator" lookup. `build_wire` DOES intern the attacker: its
    /// `next_extra` counter assigns every non-participant creator its own `AuthorId` past
    /// `participants.len()`, and the attacker's blocks ARE encoded onto the wire the verified rule
    /// reads. So `admits(attacker, seq)` resolves to `Some(cid)` and the refusal has to come from the
    /// verified rule declining to finalize an author outside `P` — not from a `HashMap` miss. If
    /// `BlocklaceFinality.tauOrder` ever finalized a non-participant's block, this test reddens.
    ///
    /// That is exactly what the deleted `admits_semantics` and
    /// `attacker_substituted_ml_dsa_key_is_refused_by_gate` could not witness: both hand-built a
    /// `VerifiedFinality` literal and then asserted `HashSet::contains` over it. They tested the
    /// standard library. Neither ever called `compute()`, so neither could tell a working verified
    /// rule from an absent one.
    ///
    /// Self-skips without the archive (or PANICS under `DREGG_TEST_REQUIRE_LEAN=1`) — the verified
    /// rule is genuinely unassertable on a fallback build, and reporting `ok` there would be the
    /// vacuity this test exists to remove.
    #[test]
    fn attacker_block_from_unenrolled_creator_is_refused_by_the_verified_rule() {
        if !dregg_lean_ffi::demand_lean(
            dregg_lean_ffi::finality_gate_available(),
            "the Lean finality-gate export (finality_gate_available()==false)",
        ) {
            return;
        }

        let honest_keys = [key(1), key(2), key(3)];
        let attacker = key(99);
        let participants: Vec<[u8; 32]> = honest_keys.iter().map(Block::hybrid_id).collect();
        let attacker_hybrid = Block::hybrid_id(&attacker);
        assert!(
            !participants.contains(&attacker_hybrid),
            "the attacker's hybrid id must not be enrolled — else this test has no adversary"
        );

        // The lace the gate sees: the 3 honest nodes AND the attacker, all cross-linked. The honest
        // nodes reference the attacker's blocks (it gossiped them), so they are load-bearing in the
        // causal past — the gate cannot refuse them by simply ignoring an unreferenced subgraph.
        let all_creators = [
            honest_keys[0].clone(),
            honest_keys[1].clone(),
            honest_keys[2].clone(),
            attacker.clone(),
        ];
        let lace = cross_linked_lace(&all_creators, TWO_WAVES, 3);
        let attacker_seqs: Vec<u64> = lace
            .iter()
            .filter(|(_, b)| b.creator == attacker_hybrid)
            .map(|(_, b)| b.seq)
            .collect();
        assert_eq!(
            attacker_seqs.len(),
            TWO_WAVES as usize,
            "the attacker must actually be in the lace at every round — else there is nothing to refuse"
        );

        // Run the REAL gate over the REAL lace, with only the 3 honest nodes enrolled.
        let vf = VerifiedFinality::compute(&lace, &participants)
            .expect("verified gate ran (archive present + wire non-ERR)");

        // ── HONEST POLE FIRST. The gate must admit the enrolled nodes' finalized blocks. Without
        //    this, "refuses the attacker" is satisfied by a gate that finalizes NOTHING — the vacuous
        //    pass, and the one a broken export would produce.
        assert!(
            !vf.is_empty(),
            "the verified rule finalized NOTHING on a clean cross-linked lace — the attacker-refusal \
             assertion below would then be vacuously true. The gate is broken, not strict."
        );
        let mut honest_admitted = 0usize;
        for (_, b) in lace.iter() {
            if participants.contains(&b.creator) && vf.admits(&b.creator, b.seq) {
                honest_admitted += 1;
            }
        }
        assert!(
            honest_admitted > 0,
            "no ENROLLED participant's block was admitted — the gate is refusing everyone, so its \
             refusal of the attacker carries no information about identity"
        );
        // ── LOAD-BEARING. The attacker's wave-0 blocks lie inside the closure of a block the gate
        //    FINALIZED: the wave-1 anchor references the attacker's seq-2 block. So the anchor's
        //    order covers them, and only the identity filter can keep them out. On a three-round
        //    lace the only finalized block is the predecessor-free wave-0 anchor, and the refusal
        //    below held for every creator, enrolled or not — it said nothing about identity.
        let anchor_creator = dregg_blocklace::ordering::wave_leader(1, &participants);
        assert!(
            vf.admits(&anchor_creator, 3),
            "the wave-1 anchor must be finalized — it is what orders the attacker's wave-0 blocks"
        );
        let attacker_seq2 = lace
            .iter()
            .find(|(_, b)| b.creator == attacker_hybrid && b.seq == 2)
            .map(|(id, _)| *id)
            .expect("the attacker has a seq-2 block");
        let anchor = lace
            .iter()
            .find(|(_, b)| b.creator == anchor_creator && b.seq == 3)
            .map(|(_, b)| b)
            .expect("the wave-1 anchor is in the lace");
        assert!(
            anchor.predecessors.contains(&attacker_seq2),
            "the finalized wave-1 anchor must reference the attacker's seq-2 block — else the \
             attacker's blocks are outside every finalized closure and their refusal is free"
        );
        for seq in 0u64..3 {
            for p in &participants {
                assert!(
                    vf.admits(p, seq),
                    "honest wave-0 block (seq {seq}) beside the attacker's must be finalized"
                );
            }
        }

        // ── THE REFUSAL. The attacker IS interned (build_wire's next_extra gives it an AuthorId and
        //    puts its blocks on the wire), so this is the verified rule declining to finalize an
        //    author outside the enrolled set — not a HashMap miss.
        assert!(
            vf.creator_ids.contains_key(&attacker_hybrid),
            "the attacker must be INTERNED on the wire (build_wire::next_extra) — if it were absent, \
             `admits` would return false via a HashMap miss and this test would assert nothing about \
             the verified rule"
        );
        for seq in &attacker_seqs {
            assert!(
                !vf.admits(&attacker_hybrid, *seq),
                "the VERIFIED rule FINALIZED a block (seq {seq}) created by an UNENROLLED identity — \
                 an unenrolled node can inject state transitions into the executor. The gate is OPEN."
            );
        }
        // And no finalized coordinate carries the attacker's AuthorId at all.
        let attacker_cid = vf.creator_ids[&attacker_hybrid];
        assert!(
            !vf.finalized.iter().any(|(c, _)| *c == attacker_cid),
            "the verified finalized set contains the unenrolled attacker's AuthorId {attacker_cid}"
        );
    }

    /// **THE KEY-SUBSTITUTION TOOTH, on a REAL lace.** The participant projection is keyed by the
    /// HYBRID id `H(ed25519 ‖ ml_dsa)`. An attacker who keeps an honest node's ed25519 half but
    /// substitutes its own ML-DSA key gets a DIFFERENT hybrid id, so it is not the enrolled identity.
    ///
    /// The predecessor test asserted that over a hand-built `VerifiedFinality` literal — i.e. it
    /// asserted that two hashes differ and that a `HashSet` does not contain a key it was never given.
    /// Here the honest node's blocks are put through the REAL gate and the substituted identity is
    /// checked against the REAL finalized set: the enrolled hybrid is admitted, the substituted one
    /// is not, and the honest pole proves the gate is live rather than empty.
    #[test]
    fn substituted_ml_dsa_identity_is_not_admitted_by_the_verified_rule() {
        if !dregg_lean_ffi::demand_lean(
            dregg_lean_ffi::finality_gate_available(),
            "the Lean finality-gate export (finality_gate_available()==false)",
        ) {
            return;
        }

        let keys = [key(1), key(2), key(3)];
        let participants: Vec<[u8; 32]> = keys.iter().map(Block::hybrid_id).collect();

        // Same ed25519 half as the honest node 0; a FOREIGN ML-DSA half. The commitment binds both,
        // so the resulting identity is not the enrolled one.
        let honest_ed: [u8; 32] = keys[0].verifying_key().to_bytes();
        let foreign_ml = dregg_blocklace::pq::public_from_ed25519_seed(&[42u8; 32]);
        let substituted = Block::hybrid_id_from_parts(&honest_ed, &foreign_ml);
        assert_ne!(
            substituted, participants[0],
            "substituting the ML-DSA half must change the hybrid id (the commitment binds both halves)"
        );

        let lace = cross_linked_lace(&keys, TWO_WAVES, 3);
        let vf = VerifiedFinality::compute(&lace, &participants)
            .expect("verified gate ran (archive present + wire non-ERR)");

        // HONEST POLE — the enrolled identity's blocks really are finalized by the verified rule.
        // Without this the refusal below is satisfied by an empty finalized set.
        let honest_finalized_seq = lace
            .iter()
            .filter(|(_, b)| b.creator == participants[0])
            .map(|(_, b)| b.seq)
            .find(|s| vf.admits(&participants[0], *s))
            .expect(
                "the enrolled node 0 must have at least one VERIFIED-finalized block on a clean \
                 3-node lace — else the substitution refusal below is vacuous",
            );

        // THE REFUSAL — at the SAME seq the enrolled identity is admitted at, the substituted
        // identity is not. This is the differential that matters: the only thing that changed is the
        // ML-DSA half of the identity.
        assert!(
            !vf.admits(&substituted, honest_finalized_seq),
            "a key-substitution identity (honest ed25519, foreign ML-DSA) was ADMITTED at seq \
             {honest_finalized_seq}, the same seq the enrolled identity is admitted at — the \
             executor's who-finalized projection is NOT bound to the hybrid commitment"
        );
    }

    /// THE LIVE-GATE DIFFERENTIAL — `VerifiedFinality::compute` (the verified Lean rule
    /// `BlocklaceFinality.tauOrder` via the `dregg_blocklace_finalize` FFI export) AGREES with the
    /// Rust `dregg_blocklace::ordering::tau` on a real 3-node lace, at the `(creator, seq)`
    /// coordinate — at three rounds (`trace3`: the wave-0 anchor alone) and at six (`trace6`: the
    /// nine wave-0 blocks plus the wave-1 anchor that orders them). This is the runtime face of the consensus-pillar differential
    /// (`blocklace::ordering::tests::test_tau_differential_against_lean_model`): the SAME verified
    /// rule that gates `poll_finalized_blocks` reproduces the order the Rust `tau` finalizes — so
    /// gating the live commit on it is transparent for honest traces and only bites on divergence.
    ///
    /// Self-skips when the Lean archive lacks the finality-gate export (a marshal-only / stale
    /// build) — UNLESS `DREGG_TEST_REQUIRE_LEAN=1`, under which the absent export PANICS instead of
    /// reporting a hollow `ok` (the scheduled hard-mode lane; see `dregg_lean_ffi::demand_lean`).
    #[test]
    fn verified_gate_agrees_with_rust_tau_three_node() {
        if !dregg_lean_ffi::demand_lean(
            dregg_lean_ffi::finality_gate_available(),
            "the Lean finality-gate export (finality_gate_available()==false)",
        ) {
            return;
        }

        let keys = [key(1), key(2), key(3)];
        let participants: Vec<[u8; 32]> = keys.iter().map(Block::hybrid_id).collect();
        let cid = |c: &[u8; 32]| participants.iter().position(|p| p == c).unwrap() as u64;

        // THREE ROUNDS — `trace3`. Wave 0's anchor super-ratifies but orders only its own closure,
        // which is itself. A rule that orders the RATIFIERS' pasts (pre-`d182d10fc`) gives nine here.
        let short = cross_linked_lace(&keys, 3, 3);
        let short_vf = VerifiedFinality::compute(&short, &participants)
            .expect("verified gate ran (archive present + wire non-ERR)");
        let short_rust: std::collections::HashSet<(u64, u64)> =
            rust_tau_order(&short, &participants)
                .iter()
                .map(|(c, s)| (cid(c), *s))
                .collect();
        assert_eq!(
            short_vf.finalized, short_rust,
            "trace3: verified gate must agree with Rust tau"
        );
        assert_eq!(
            short_vf.finalized,
            [(0u64, 0u64)].into_iter().collect(),
            "trace3: a three-round lace finalizes exactly the wave-0 anchor (CM Def. 6)"
        );

        // SIX ROUNDS — `trace6`.
        let lace = cross_linked_lace(&keys, TWO_WAVES, 3);
        let rust_finalized: std::collections::HashSet<(u64, u64)> =
            rust_tau_order(&lace, &participants)
                .iter()
                .map(|(c, s)| (cid(c), *s))
                .collect();

        // VERIFIED gate over the same lace, via the real node gate type.
        let vf = VerifiedFinality::compute(&lace, &participants)
            .expect("verified gate ran (archive present + wire non-ERR)");
        let verified: std::collections::HashSet<(u64, u64)> = vf.finalized.clone();

        assert_eq!(
            verified, rust_finalized,
            "verified finality gate must agree with Rust tau on the (creator, seq) finalized set"
        );
        let wave0: std::collections::HashSet<(u64, u64)> = (0u64..3)
            .flat_map(|c| (0u64..3).map(move |s| (c, s)))
            .collect();
        assert!(
            wave0.is_subset(&verified),
            "3-node lace finalizes all nine wave-0 (creator, seq) blocks; got {verified:?}"
        );
        let golden: std::collections::HashSet<(u64, u64)> = two_wave_finalized(&participants)
            .iter()
            .map(|(c, s)| (cid(c), *s))
            .collect();
        assert_eq!(
            verified, golden,
            "trace6: the nine wave-0 blocks plus the wave-1 anchor, and nothing else"
        );

        // The gate ADMITS each finalized block by its (pubkey, seq), exactly as
        // poll_finalized_blocks queries it.
        for (cid, seq) in &verified {
            let creator = participants[*cid as usize];
            assert!(
                vf.admits(&creator, *seq),
                "gate must admit a verified-finalized block"
            );
        }
    }

    /// THE RAW-ORDER GATE DIFFERENTIAL — `VerifiedFinality::compute_order` (the verified Lean
    /// `BlocklaceFinality.tauOrder` via the NEW `dregg_tau_order` export, proved order-faithfully
    /// equal to `tauOrder` by `tau_order_export_eq`) returns the FULL finalized TOTAL ORDER as node
    /// `BlockId`s. On the 3-node `trace6` lace this is the ten-block order (the nine wave-0 blocks,
    /// seq-major, then the wave-1 anchor that orders them) whose `(creator, seq)` projection
    /// is exactly the projection gate's finalized SET — so the raw-order export and the projection
    /// export agree, and the order is a permutation-free superset relationship: every block the
    /// projection finalizes appears in the raw order, IN the verified sequence.
    ///
    /// Self-skips when the archive lacks the raw-order export (a stale/marshal-only build) —
    /// unless `DREGG_TEST_REQUIRE_LEAN=1`, under which the absent export PANICS.
    #[test]
    fn raw_order_export_agrees_with_projection_three_node() {
        if !dregg_lean_ffi::demand_lean(
            dregg_lean_ffi::tau_order_available(),
            "the Lean raw tau-order export (tau_order_available()==false)",
        ) {
            return;
        }

        let keys = [key(1), key(2), key(3)];
        let participants: Vec<[u8; 32]> = keys.iter().map(Block::hybrid_id).collect();
        let lace = cross_linked_lace(&keys, TWO_WAVES, 3);

        // The verified RAW total order (node BlockIds), via the new export.
        let order = VerifiedFinality::compute_order(&lace, &participants)
            .expect("raw-order gate ran (archive present + wire non-ERR)");
        let order_blocks: Vec<&Block> = order
            .iter()
            .map(|id| lace.get(id).expect("ordered id is present"))
            .collect();
        // `trace6`'s golden shape: seq-major over wave 0, then the wave-1 anchor.
        assert_eq!(
            order_blocks.iter().map(|b| b.seq).collect::<Vec<_>>(),
            vec![0, 0, 0, 1, 1, 1, 2, 2, 2, 3],
            "3-node lace finalizes the nine wave-0 blocks seq-major, then the wave-1 anchor"
        );
        assert_eq!(
            order_blocks[9].creator,
            dregg_blocklace::ordering::wave_leader(1, &participants),
            "the order ends with the wave-1 anchor that orders wave 0"
        );
        assert_eq!(
            order_blocks
                .iter()
                .map(|b| (b.creator, b.seq))
                .collect::<std::collections::HashSet<_>>(),
            two_wave_finalized(&participants),
            "the raw order covers exactly trace6's golden set"
        );

        // Its (creator, seq) projection must EQUAL the projection gate's finalized set — the two
        // verified exports are consistent (one is the order, the other its set projection).
        let vf = VerifiedFinality::compute(&lace, &participants).expect("projection gate ran");
        let order_cs: std::collections::HashSet<(u64, u64)> = order
            .iter()
            .filter_map(|id| lace.get(id))
            .map(|b| {
                let cid = participants.iter().position(|p| p == &b.creator).unwrap() as u64;
                (cid, b.seq)
            })
            .collect();
        assert_eq!(
            order_cs, vf.finalized,
            "the raw tau-order export's (creator,seq) projection must equal the projection gate's set"
        );
        // Every block in the verified order is admitted by the projection gate (consistency both ways).
        for id in &order {
            let b = lace.get(id).expect("ordered id is present");
            assert!(
                vf.admits(&b.creator, b.seq),
                "ordered block must be projection-admitted"
            );
        }
    }

    /// THE MAKE-OR-BREAK (Path-B gate): does a turn SUPER-RATIFY under the gate-ON (verified Lean,
    /// memoized `tauOrderFast`) finalizer on an n=5-shaped cross-linked DAG (5 validators, the C3
    /// shape, supermajority threshold `supermajority_threshold(5) == 4`)? And does the gate-OFF
    /// (Rust `ordering::tau`) path do the SAME on the identical DAG?
    ///
    /// This is the local proof that GATES the live Path-B clean cut. It runs BOTH finalizers over one
    /// canonical DAG and reports each verdict:
    ///   * gate-ON  = `VerifiedFinality::compute_order` (the REAL node path: `dregg_tau_order` FFI =
    ///     the memoized verified `tauOrderFast`).
    ///   * gate-OFF = `dregg_blocklace::ordering::tau` (the Rust differential sibling the node runs
    ///     when `DREGG_FINALITY_GATE=0`).
    ///
    /// A finalized turn block = the consensus precondition `execute_finalized_turn` fires on (height
    /// 0 -> 1). The DAG is wavelength-3, rounds 1..3 = wave 0; the wave-0 leader is `participants[0]`
    /// at round 1, super-ratified once a supermajority (4 of 5) of round-3 blocks ratify it. Under
    /// CM Def. 6 that anchor orders only its own closure (itself), so the rest of wave 0 — the full
    /// coverage this test pins — is ordered by the wave-1 anchor `participants[1]` at round 4, which
    /// needs the second wave (rounds 4..6). Every block carries a `Turn` payload, so a non-empty
    /// finalized order == "a turn super-ratified".
    ///
    /// EXPECTED (and the finding to report): the two finalizers run the SAME rule (the Lean port is
    /// proved order-faithful to the Rust `tau`), so on a CLEAN round-synchronous DAG BOTH super-ratify
    /// and AGREE on the finalized `(creator, seq)` set. gate-ON finalizing here is the green light for
    /// the Path-B cut; the Rust↔Lean agreement means the live gate-OFF non-finalization was NOT a
    /// finalizer-RULE bug but a degenerate live DAG / the (now-fixed) FFI wedge — i.e. the fix is the
    /// clean cut + the memoization, not a different finalization rule.
    ///
    /// Self-skips when the archive lacks the raw-order export (a stale/marshal-only build) —
    /// unless `DREGG_TEST_REQUIRE_LEAN=1`, under which the absent export PANICS.
    #[test]
    fn gate_on_super_ratifies_n5_c3_shape() {
        if !dregg_lean_ffi::demand_lean(
            dregg_lean_ffi::tau_order_available(),
            "the Lean raw tau-order export (tau_order_available()==false) — the gate-ON finalizer \
             cannot be proven; rebuild with the verified archive",
        ) {
            return;
        }

        // n=5, threshold 4 (== supermajority_threshold(5)). The C3 shape: a fully cross-linked,
        // round-synchronous DAG, two waves (wavelength 3). Every block carries a Turn payload.
        let keys: Vec<SigningKey> = (1u8..=5).map(key).collect();
        let participants: Vec<[u8; 32]> = keys.iter().map(Block::hybrid_id).collect();
        assert_eq!(
            dregg_blocklace::ordering::supermajority_threshold(participants.len()),
            4,
            "n=5 supermajority threshold is 4 (the C3 quorum)"
        );
        let lace = cross_linked_lace(&keys, TWO_WAVES, 4);

        // ── gate-OFF: the Rust `ordering::tau` over the same lace, projected to (creator, seq). ──
        let gate_off_cs: std::collections::HashSet<([u8; 32], u64)> =
            rust_tau_order(&lace, &participants).into_iter().collect();

        // ── gate-ON: the REAL node path — verified Lean `tauOrderFast` via the FFI export. ──
        let gate_on_order = VerifiedFinality::compute_order(&lace, &participants)
            .expect("gate-ON verified raw-order ran (archive present + wire non-ERR)");
        let gate_on_cs: std::collections::HashSet<([u8; 32], u64)> = gate_on_order
            .iter()
            .filter_map(|id| lace.get(id).map(|b| (b.creator, b.seq)))
            .collect();

        eprintln!(
            "MAKE-OR-BREAK n=5/C3: gate-ON finalized {} turn-blocks; gate-OFF finalized {} turn-blocks",
            gate_on_cs.len(),
            gate_off_cs.len()
        );

        // VERDICT 1 — the make-or-break: a turn SUPER-RATIFIES under gate-ON (non-empty order ⇒ the
        // wave-0 leader super-ratified and its coverage finalized ⇒ execute_finalized_turn's
        // precondition is met, height 0 -> 1 can fire).
        assert!(
            !gate_on_cs.is_empty(),
            "gate-ON (verified Lean tauOrderFast) MUST super-ratify a turn on the n=5 C3 DAG — \
             this is the Path-B green light. EMPTY here ⇒ STOP the cut: the finalization-liveness \
             bug is in the finalizer/consensus itself (gate-independent)."
        );

        // VERDICT 2 — gate-ON and gate-OFF run the SAME rule: they finalize the IDENTICAL
        // (creator, seq) set on a clean DAG. (If they DIVERGED, gate-OFF would be a confirmed-buggy
        // finalizer; they do not — the live gate-OFF non-finalization is a degenerate-DAG / wedge
        // artifact, not a rule bug.)
        assert_eq!(
            gate_on_cs, gate_off_cs,
            "gate-ON (Lean) and gate-OFF (Rust tau) must finalize the same (creator, seq) set on the \
             clean n=5 C3 DAG — the Lean port is order-faithful to the Rust tau"
        );

        // The wave-0 leader (participants[0]) must be among the finalized creators (the super-ratified
        // anchor), and all 5 genesis turns finalize (full wave-0 coverage).
        assert!(
            gate_on_cs
                .iter()
                .any(|(c, s)| *c == participants[0] && *s == 0),
            "the super-ratified wave-0 leader's genesis turn must be finalized under gate-ON"
        );
        let golden = two_wave_finalized(&participants);
        assert_eq!(
            gate_on_cs.iter().filter(|(_, s)| *s < 3).count(),
            15,
            "the n=5 clean DAG finalizes all 15 wave-0 turn-blocks (wave-0 coverage)"
        );
        assert_eq!(
            gate_on_cs, golden,
            "the n=5 / two-wave clean DAG finalizes the 15 wave-0 turn-blocks plus the wave-1 anchor"
        );
    }

    /// THE WEDGE REGRESSION TEST — the verified Lean tau-ordering completes FAST on an n=5
    /// cross-linked multi-round DAG (the shape that wedged the node). Before the
    /// `BlocklaceFinality.tauOrderFast` memoization (the Lean parallel of the Rust `PastCache`), the
    /// Lean `dregg_tau_order` export RE-TRAVERSED each block's causal past an exponential number of
    /// times across the nested `ratifies`/`isSuperRatified`/`findAllFinalLeaders` loops — on a
    /// cross-linked DAG it blew up and (run inline on a tokio worker) starved the runtime. With the
    /// causal-past computed ONCE, the verified order is computed in milliseconds and AGREES with the
    /// memoized Rust `ordering::tau` on the `(creator, seq)` set. This test builds a 5-node /
    /// 6-round (30-block) fully cross-linked lace, runs the verified Lean export, and asserts it
    /// completes well under a generous wall-clock bound — a former-exponential computation now linear-ish.
    ///
    /// Self-skips when the archive lacks the raw-order export (a stale/marshal-only build) —
    /// unless `DREGG_TEST_REQUIRE_LEAN=1`, under which the absent export PANICS.
    #[test]
    fn lean_tau_order_fast_on_cross_linked_n5_dag() {
        if !dregg_lean_ffi::demand_lean(
            dregg_lean_ffi::tau_order_available(),
            "the Lean raw tau-order export (tau_order_available()==false)",
        ) {
            return;
        }

        // 5 nodes, 6 fully cross-linked rounds: each round's block references ALL of the previous
        // round (the dense cross-linking that explodes an un-memoized causal-past traversal).
        let keys: Vec<SigningKey> = (1u8..=5).map(key).collect();
        let participants: Vec<[u8; 32]> = keys.iter().map(Block::hybrid_id).collect();
        let lace = cross_linked_lace(&keys, TWO_WAVES, 3);

        // Run the VERIFIED Lean tau-order (the live `dregg_tau_order` FFI = `tauOrderFast`), timed.
        let t0 = std::time::Instant::now();
        let order = VerifiedFinality::compute_order(&lace, &participants)
            .expect("verified raw-order gate ran (archive present + wire non-ERR)");
        let elapsed = t0.elapsed();

        // The blow-up is gone: a former-exponential traversal now finishes near-instantly. The bound is
        // deliberately generous (the memoized path is milliseconds; the un-memoized path on this dense
        // 30-block DAG did not finish in any reasonable time).
        assert!(
            elapsed < std::time::Duration::from_secs(10),
            "verified Lean tau-order must complete fast on the n=5 cross-linked DAG (memoized \
             causal-past); took {elapsed:?} — the wedge is back"
        );

        // Two full waves (wavelength 3, rounds 1..6) finalize, so the order is non-empty.
        assert!(
            !order.is_empty(),
            "the n=5 / 6-round lace must finalize at least wave 1"
        );

        // DIFFERENTIAL: the verified Lean order AGREES with the memoized Rust `ordering::tau` on the
        // (creator, seq) set — the same path the live node cross-checks.
        let rust_cs: std::collections::HashSet<([u8; 32], u64)> =
            rust_tau_order(&lace, &participants).into_iter().collect();
        let lean_cs: std::collections::HashSet<([u8; 32], u64)> = order
            .iter()
            .filter_map(|id| lace.get(id).map(|b| (b.creator, b.seq)))
            .collect();
        assert_eq!(
            lean_cs, rust_cs,
            "verified Lean tau-order and memoized Rust tau must agree on the (creator, seq) set on \
             the n=5 cross-linked DAG"
        );
        assert_eq!(
            lean_cs,
            two_wave_finalized(&participants),
            "the n=5 two-wave lace finalizes wave 0 plus the wave-1 anchor"
        );
    }
}
