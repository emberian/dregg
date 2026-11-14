//! Cordial Miners total ordering (the tau function).
//!
//! Implements the consensus ordering from the Cordial Miners paper (arXiv:2205.09174).
//! The blocklace is divided into **waves** of fixed wavelength. Each wave has a
//! designated **leader** (round-robin). When the leader's block is **super-ratified**
//! by a supermajority chain at the wave's end, it becomes a final leader and
//! anchors a segment of the total order.
//!
//! The `tau` function (CM Def. 6 / Alg. 2:32,35,37,41–46) takes ONE head — the
//! DEEPEST final leader (`last_final_leader()`, Alg. 2:44–46) — and recurses
//! BACKWARD through `previous_ratified_leader` (Alg. 2:41–43), producing an
//! anchor chain `[b₁, …, b_k = head]`. Folding that chain left to right, each
//! anchor `l` contributes `xsort(l, [l] \ [prev])`: the blocks of the anchor's
//! OWN inclusive causal past `[l]` that the previous anchor's closure did not
//! already cover. **Finality is consulted exactly once — choosing the head — and
//! nowhere in the recursion** (CM Def. 6: "when τ′ is called with a leader b, it
//! makes a recursive call with a leader ratified by b, which is not necessarily
//! super-ratified").
//!
//! That single structural fact is what makes the history append-only. The
//! previous rule folded over `find_all_final_leaders` and gave each anchor a
//! *coverage* = the union of the causal pasts of every wave-END block **in the
//! live lace** that ratified it — a strict superset of `[anchor]` that GREW WITH
//! ARRIVALS, so a late honest wave-end ratifier for an already-final wave spliced
//! blocks MID-PREFIX. A closure is fixed forever by the anchor's own signed hash
//! pointers, so the new segments cannot move. The price is CM's real latency: a
//! block at round `r` is ordered by the first final leader that OBSERVES it,
//! which is at a strictly greater round — never by a ratifier at its own wave's
//! end. On a 3-round / one-wave lace `tau` therefore emits exactly the anchor.
//!
//! # Key Definitions
//!
//! - **Round**: the depth of a block in the DAG (longest path from any genesis).
//!   Genesis blocks are at round 1.
//! - **Wave**: a group of `wavelength` consecutive rounds. Wave 0 = rounds [1, w].
//! - **Leader**: the designated block creator for a wave (round-robin by index).
//! - **Approval**: block `b` approves leader `l` if `l` is in `b`'s causal past
//!   and no equivocation by `l.creator` is visible from `b`.
//! - **Ratification**: block `b` ratifies leader `l` if a supermajority of
//!   participants have blocks in `b`'s causal past that approve `l`.
//! - **Super-ratification**: a supermajority of blocks at the wave's last round
//!   ratify the leader.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;

use crate::{BlockId, Blocklace};

/// Per-`tau`-invocation memo of each block's inclusive causal past.
///
/// A block's causal past is a pure function of the (immutable, for the
/// duration of one ordering computation) blocklace topology, so memoizing it
/// is byte-identical to recomputing — `tau` previously recomputed the SAME
/// past many times over (`ratifies` over an observer's past calls `approves`
/// per past block, each recomputing a past; the leader loop recomputes again).
/// Created fresh per ordering call, so it never outlives an immutable borrow
/// of the blocklace (no cross-call staleness).
#[derive(Default)]
struct PastCache {
    inner: RefCell<HashMap<BlockId, Rc<HashSet<BlockId>>>>,
}

impl PastCache {
    fn new() -> Self {
        Self::default()
    }

    /// The inclusive causal past of `block_id`, computed once and reused.
    /// Identical value to `blocklace.causal_past(block_id)`.
    fn past(&self, blocklace: &Blocklace, block_id: &BlockId) -> Rc<HashSet<BlockId>> {
        if let Some(hit) = self.inner.borrow().get(block_id) {
            return Rc::clone(hit);
        }
        let computed = Rc::new(blocklace.causal_past(block_id));
        self.inner
            .borrow_mut()
            .insert(*block_id, Rc::clone(&computed));
        computed
    }
}

// ─── Configuration ───────────────────────────────────────────────────────────

/// Configuration for the Cordial Miners ordering protocol.
#[derive(Clone, Debug)]
pub struct OrderingConfig {
    /// Wavelength: number of rounds per wave. Default 3 (eventual synchrony mode).
    pub wavelength: u64,
}

impl Default for OrderingConfig {
    fn default() -> Self {
        Self { wavelength: 3 }
    }
}

// ─── Extended Blocklace Queries ──────────────────────────────────────────────

/// Compute the round (depth) of each block in the blocklace, OVER THE ENROLLED EDGE SET.
///
/// Round = 1 + max(rounds of the predecessors that are present AND created by a `participant`);
/// a block with no such predecessor has round 1. Returns a map from BlockId to round number, and
/// the maximum round seen.
///
/// ⚑ **Why it reads `participant_set`** (the residual HORIZONLOG B6 left open, closed here). It
/// used to max over EVERY present predecessor. Depth is the wave clock — `round_to_wave`, the
/// leader slot, the wave end, and `xsort`'s primary key are all read off it — so any creator who
/// could add depth could move the wave structure. A NON-PARTICIPANT chain that one honest block
/// acked did exactly that: two honest nodes holding the identical enrolled sub-lace and differing
/// only in whether they received two outsider blocks finalized the SAME enrolled coordinates in
/// DIFFERENT ORDERS (`ordering_forks_when_an_outsider_relay_shifts_the_wave_clock` in
/// `tests/consensus_fault_sim.rs` drives it through the real `finality::Blocklace`, and
/// `find_fork` — this repo's own safety checker — reports the fork). Non-participants are exactly
/// the creators dissemination does not guarantee every node sees, so the divergent view is the
/// ordinary case.
///
/// **The EDGES are filtered, not the NODES**, and that is deliberate: a non-participant's block
/// still RECEIVES the round its enrolled predecessors give it, so it still appears in a round set
/// and `ratifies_enrolled` (B6) is still what decides that it may not RATIFY. Dropping it from the
/// map entirely — what [`compute_rounds_filtered`] does for `tau_unified`, correctly, because
/// every read there is participant-restricted — would subsume the B6 gate on `tau`'s path and
/// silently retire its exhibits.
///
/// VERIFIED MODEL: `BlocklaceFinality.computeRounds` / `roundOfStep`; the pre-repair recurrence is
/// kept there as `computeRoundsPreParticipant`, the permanent falsification witness.
fn compute_rounds(
    blocklace: &Blocklace,
    participant_set: &HashSet<[u8; 32]>,
) -> (HashMap<BlockId, u64>, u64) {
    let mut rounds: HashMap<BlockId, u64> = HashMap::new();
    let mut max_round: u64 = 0;

    // We need topological order to compute rounds bottom-up.
    // Use Kahn's algorithm on the blocklace.
    let mut in_degree: HashMap<BlockId, usize> = HashMap::new();
    let mut successors: HashMap<BlockId, Vec<BlockId>> = HashMap::new();

    for (id, block) in &blocklace.blocks {
        let pred_count = block
            .predecessors
            .iter()
            .filter(|p| blocklace.blocks.contains_key(*p))
            .count();
        in_degree.insert(*id, pred_count);
        for pred in &block.predecessors {
            if blocklace.blocks.contains_key(pred) {
                successors.entry(*pred).or_default().push(*id);
            }
        }
    }

    let mut queue: VecDeque<BlockId> = in_degree
        .iter()
        .filter(|(_, deg)| **deg == 0)
        .map(|(id, _)| *id)
        .collect();

    while let Some(id) = queue.pop_front() {
        let block = &blocklace.blocks[&id];
        // Only a predecessor created by a PARTICIPANT contributes depth. An absent predecessor has
        // no entry in `rounds` either way, so the `None` arm of the enrollment test is inert here —
        // exactly as in `BlocklaceFinality.enrolledId`'s `none => true`.
        let round = 1 + block
            .predecessors
            .iter()
            .filter(|p| {
                blocklace
                    .get(p)
                    .map(|pb| participant_set.contains(&pb.creator))
                    .unwrap_or(true)
            })
            .filter_map(|p| rounds.get(p))
            .max()
            .copied()
            .unwrap_or(0);
        rounds.insert(id, round);
        if round > max_round {
            max_round = round;
        }

        if let Some(succs) = successors.get(&id) {
            for &succ in succs {
                if let Some(deg) = in_degree.get_mut(&succ) {
                    *deg -= 1;
                    if *deg == 0 {
                        queue.push_back(succ);
                    }
                }
            }
        }
    }

    (rounds, max_round)
}

/// Get the causal past of a block (inclusive of the block itself), memoized
/// for the duration of one ordering computation via `cache`.
fn causal_past_inclusive(
    cache: &PastCache,
    blocklace: &Blocklace,
    block_id: &BlockId,
) -> Rc<HashSet<BlockId>> {
    cache.past(blocklace, block_id)
}

/// Precomputed once per ordering call: every creator that equivocates *somewhere*
/// in the (rounded) blocklace, mapped to its conflicting-block groups.
///
/// A creator equivocates at a round when it has ≥2 distinct blocks assigned that
/// round; the group holds those block ids. A creator absent from the index never
/// equivocates anywhere, so any observer-visibility query for it is trivially
/// `false` — the common case, now one `HashMap` miss instead of re-scanning the
/// observer's whole causal past. The old `has_equivocation_in_past` rebuilt an
/// O(|past|) `round → Vec` map on *every* `approves` call, and `ratifies` /
/// `is_super_ratified` call `approves` O(waves·P·N²) times per `tau`, so this was
/// the dominant term in Rust `tau` finality.
///
/// `equivocates_in_past` is byte-identical to the previous per-observer scan: a
/// creator is a visible equivocator from an observer iff the observer's inclusive
/// causal past contains ≥2 of that creator's blocks at one round — i.e. ≥2 members
/// of one precomputed group.
struct EquivocationIndex {
    by_creator: HashMap<[u8; 32], Vec<Vec<BlockId>>>,
}

impl EquivocationIndex {
    /// Build the index from the round assignment used for this ordering call.
    /// Only blocks that received a round participate — matching the old scan,
    /// which skipped past blocks with no round (e.g. non-participant blocks under
    /// `compute_rounds_filtered`).
    fn build(blocklace: &Blocklace, rounds: &HashMap<BlockId, u64>) -> Self {
        let mut groups: HashMap<([u8; 32], u64), Vec<BlockId>> = HashMap::new();
        for (id, block) in &blocklace.blocks {
            if let Some(&round) = rounds.get(id) {
                groups.entry((block.creator, round)).or_default().push(*id);
            }
        }
        let mut by_creator: HashMap<[u8; 32], Vec<Vec<BlockId>>> = HashMap::new();
        for ((creator, _round), ids) in groups {
            if ids.len() > 1 {
                by_creator.entry(creator).or_default().push(ids);
            }
        }
        Self { by_creator }
    }

    /// Whether `creator` has an equivocation visible from `past` (an inclusive
    /// causal past): ≥2 blocks of some conflicting-block group lie in `past`.
    fn equivocates_in_past(&self, creator: &[u8; 32], past: &HashSet<BlockId>) -> bool {
        match self.by_creator.get(creator) {
            None => false,
            Some(groups) => groups
                .iter()
                .any(|group| group.iter().filter(|b| past.contains(*b)).count() > 1),
        }
    }
}

// ─── Wave / Leader helpers ───────────────────────────────────────────────────

/// Determine which wave a given round belongs to.
/// Rounds are 1-indexed. Wave 0 = rounds [1, w], Wave 1 = [w+1, 2w], etc.
///
/// `round == 0` is out of contract (rounds are 1-indexed); the `saturating_sub`
/// guards the `round - 1` against a debug panic / release wrap-to-`u64::MAX`,
/// mapping it to wave 0 rather than the far end of the round space.
fn round_to_wave(round: u64, wavelength: u64) -> u64 {
    round.saturating_sub(1) / wavelength
}

/// Get the first round of a wave.
fn wave_first_round(wave: u64, wavelength: u64) -> u64 {
    wave * wavelength + 1
}

/// Get the last round of a wave.
fn wave_last_round(wave: u64, wavelength: u64) -> u64 {
    (wave + 1) * wavelength
}

/// Determine the leader for a given wave (round-robin by participant index).
///
/// # Panics
///
/// Panics if `participants` is empty. The caller (`tau_with_config`) guards
/// against this by returning early when participants is empty.
pub fn wave_leader(wave: u64, participants: &[[u8; 32]]) -> [u8; 32] {
    assert!(!participants.is_empty(), "need at least one participant");
    participants[(wave as usize) % participants.len()]
}

/// THE canonical quorum formula for the whole system: the strict
/// SUPERMAJORITY threshold `⌊2n/3⌋ + 1` — the smallest vote count STRICTLY
/// greater than `2n/3`.
///
/// This is the quorum the Cordial-Miners / Stingray DAG semantics demand
/// (arXiv:2205.09174 §2: ratification requires blocks from "more than
/// two-thirds of the miners"), and it is the formula with UNCONDITIONAL
/// quorum intersection: any two quorums of this size share strictly more
/// than `n/3` members, which exceeds the Byzantine budget
/// `f = ⌊(n−1)/3⌋` for every `n ≥ 1` — no `n` caveat.
///
/// Equivalently `supermajority_threshold n = n − ⌊(n−1)/3⌋` for `n ≥ 1`.
///
/// The federation layer's `dregg_federation::quorum_threshold` DELEGATES
/// here — there is exactly ONE quorum formula in the system. (Its
/// historical formula `n − ⌊n/3⌋` agreed everywhere EXCEPT `3 ∣ n`, where
/// it admitted a quorum of exactly `2n/3`: at `n = 3f` two such quorums can
/// intersect in a single — possibly Byzantine — member. That is precisely
/// the `StrictBft` hole `metatheory/Dregg2/Distributed/BlsQuorumCert.lean`
/// carries as an explicit hypothesis; this formula closes it for all `n`.)
///
/// `n = 0` returns 1: an EMPTY committee can never certify anything
/// (fail-closed), rather than a vacuous threshold of 0 that an empty vote
/// set would satisfy.
pub fn supermajority_threshold(n: usize) -> usize {
    (n * 2 / 3) + 1
}

// ─── Approval / Ratification / Super-Ratification ────────────────────────────

/// Check if block `observer` approves leader block `leader_id`.
///
/// A block approves a leader block if:
/// 1. The leader block is in the observer's causal past.
/// 2. No equivocating block by the leader's creator is in the observer's causal past.
fn approves(
    cache: &PastCache,
    blocklace: &Blocklace,
    equiv: &EquivocationIndex,
    observer: &BlockId,
    leader_id: &BlockId,
    leader_creator: &[u8; 32],
) -> bool {
    let past = causal_past_inclusive(cache, blocklace, observer);

    // Leader must be visible from the observer.
    if !past.contains(leader_id) {
        return false;
    }

    // No equivocation by the leader's creator visible from the observer.
    !equiv.equivocates_in_past(leader_creator, &past)
}

/// Check if block `observer` ratifies leader block `leader_id`.
///
/// A block ratifies a leader if a supermajority (> 2n/3) of participants have
/// at least one block in the observer's causal past that approves the leader.
fn ratifies(
    cache: &PastCache,
    blocklace: &Blocklace,
    equiv: &EquivocationIndex,
    observer: &BlockId,
    leader_id: &BlockId,
    leader_creator: &[u8; 32],
    participants: &[[u8; 32]],
) -> bool {
    let supermajority = supermajority_threshold(participants.len());
    let past = causal_past_inclusive(cache, blocklace, observer);

    // Count how many distinct participants have at least one block in the
    // observer's past that approves the leader.
    let approving_count = participants
        .iter()
        .filter(|&&participant| {
            past.iter().any(|&bid| {
                if let Some(block) = blocklace.get(&bid) {
                    block.creator == participant
                        && approves(cache, blocklace, equiv, &bid, leader_id, leader_creator)
                } else {
                    false
                }
            })
        })
        .count();

    approving_count >= supermajority
}

/// Whether a wave-end block counts as a RATIFIER: its own creator is an enrolled participant AND
/// it `ratifies` the leader.
///
/// ⚑ THE RATIFIER-ENROLLMENT GATE (HORIZONLOG B6) — the differential mirror of the verified rule's
/// `BlocklaceFinality.ratifiesEnrolled`. `ratifies` above consults `participants` on the APPROVER
/// side (how many participants have an approving block in the observer's past) and never asks who
/// the OBSERVER is; `is_super_ratified` then collected `block.creator` from `end_round_blocks` with
/// no enrollment check at all, so a NON-PARTICIPANT's wave-end block contributed a distinct creator
/// to a count this function's own docstring calls "a supermajority of distinct participants".
///
/// The THRESHOLD is untouched — `supermajority_threshold` is the same formula and
/// `supermajority_threshold(3) == 3` still holds. What changed is WHO IS ELIGIBLE TO BE COUNTED.
///
/// The harm is SAFETY: an unenrolled creator's ordinary well-formed block SUBSTITUTES for a silent
/// honest validator and pushes a leader over the finality threshold the enrolled committee did not
/// reach — and in the limit a wave anchors with ZERO enrolled ratifiers. No attacker is required:
/// `finality.rs::enroll_pq` is INSERT-ONLY while `constitution.current.participants` SHRINKS on a
/// passed membership proposal, so a rotated-out validator keeps its ratifying power; and the
/// restart restore (`from_checkpoint`, authenticating since 2026-08-08) reloads the persisted DAG
/// with signatures/closure checked but still no roster check.
///
/// Applied at BOTH sites that map a wave-end block to a decision — `is_super_ratified` (does the
/// wave anchor?) and `tau_with_config`'s coverage loop (what does the anchor order?) — because an
/// unenrolled ack must neither decide finality nor decide WHERE an honest block lands in the total
/// order. On a lace where every creator IS a participant this is the identity
/// (`BlocklaceFinality.ratifiesEnrolled_eq_of_enrolled` /
/// `isSuperRatified_eq_pre_of_enrolled` prove exactly that).
#[allow(clippy::too_many_arguments)]
fn ratifies_enrolled(
    cache: &PastCache,
    blocklace: &Blocklace,
    equiv: &EquivocationIndex,
    observer: &BlockId,
    observer_creator: &[u8; 32],
    leader_id: &BlockId,
    leader_creator: &[u8; 32],
    participants: &[[u8; 32]],
) -> bool {
    participants.contains(observer_creator)
        && ratifies(
            cache,
            blocklace,
            equiv,
            observer,
            leader_id,
            leader_creator,
            participants,
        )
}

/// Check if a leader block is super-ratified (finalized).
///
/// Super-ratification: a supermajority of distinct ENROLLED participants have blocks at
/// the wave's last round that ratify the leader. The enrollment half is the B6 repair — see
/// [`ratifies_enrolled`].
fn is_super_ratified(
    cache: &PastCache,
    blocklace: &Blocklace,
    rounds: &HashMap<BlockId, u64>,
    equiv: &EquivocationIndex,
    leader_id: &BlockId,
    leader_creator: &[u8; 32],
    wave_end_round: u64,
    participants: &[[u8; 32]],
) -> bool {
    let supermajority = supermajority_threshold(participants.len());

    // Find all blocks at the wave's last round.
    let end_round_blocks: Vec<BlockId> = rounds
        .iter()
        .filter(|(_, r)| **r == wave_end_round)
        .map(|(id, _)| *id)
        .collect();

    // Count distinct participants with a block at the wave end that ratifies the leader.
    let ratifying_participants: HashSet<[u8; 32]> = end_round_blocks
        .iter()
        .filter_map(|block_id| {
            let block = blocklace.get(block_id)?;
            if ratifies_enrolled(
                cache,
                blocklace,
                equiv,
                block_id,
                &block.creator,
                leader_id,
                leader_creator,
                participants,
            ) {
                Some(block.creator)
            } else {
                None
            }
        })
        .collect();

    ratifying_participants.len() >= supermajority
}

// ─── Finding Final Leaders ───────────────────────────────────────────────────

/// Find all finalized leaders in the blocklace, in wave order.
fn find_all_final_leaders(
    cache: &PastCache,
    blocklace: &Blocklace,
    rounds: &HashMap<BlockId, u64>,
    equiv: &EquivocationIndex,
    max_round: u64,
    participants: &[[u8; 32]],
    config: &OrderingConfig,
) -> Vec<BlockId> {
    let wavelength = config.wavelength;
    let mut final_leaders = Vec::new();

    let mut wave = 0u64;
    loop {
        let wave_start = wave_first_round(wave, wavelength);
        let wave_end = wave_last_round(wave, wavelength);

        if wave_end > max_round {
            break;
        }

        let leader_key = wave_leader(wave, participants);

        // Find leader blocks: blocks by the designated leader at the wave's first round.
        let leader_blocks: Vec<BlockId> = rounds
            .iter()
            .filter(|(id, r)| {
                **r == wave_start
                    && blocklace
                        .get(id)
                        .map(|b| b.creator == leader_key)
                        .unwrap_or(false)
            })
            .map(|(id, _)| *id)
            .collect();

        // The leader must have exactly one block at the wave start (no equivocation).
        if leader_blocks.len() == 1 {
            let leader_id = leader_blocks[0];
            if is_super_ratified(
                cache,
                blocklace,
                rounds,
                equiv,
                &leader_id,
                &leader_key,
                wave_end,
                participants,
            ) {
                final_leaders.push(leader_id);
            }
        }

        wave += 1;
    }

    final_leaders
}

// ─── The Anchor Chain — CM Alg. 2 lines 32, 35, 41–46 ────────────────────────
//
// CM's τ does NOT fold over "every final leader in the live lace". It takes ONE head — the deepest
// final leader (`last_final_leader()`, Alg. 2:44–46) — and recurses backward through
// `previous_ratified_leader` (Alg. 2:41–43), a walk quantified entirely over the ANCHOR'S OWN
// CLOSURE `[b1]`:
//
//     41: procedure previous_ratified_leader(b1):
//     42:    return arg_{b∈R} max depth(b)
//     43:    where R = {b ∈ [b1] \ {b1} : b.creator = leader(depth(b)) ∧ ratifies([b1], b)}
//
// ⚑ CLOSURE-LOCALITY IN RUST. The Lean model evaluates depths, `approves`/`ratifies` and the
// equivocation guard against `closureLace B l.id` — the sub-lace induced by the anchor's inclusive
// causal past. Here the equivalent is: every read is restricted to that past, which is what these
// functions do (the candidate set is `causal_past_inclusive(b1)`, and `ratifies` with `b1` as the
// OBSERVER already ranges over exactly `[b1]`). Two facts make a second, closure-local round map
// unnecessary:
//   * `compute_rounds` over the closure gives the SAME depths as over the whole lace whenever the
//     lace is predecessor-closed, which the admission path guarantees
//     (`Blocklace::insert` rejects with `InsertError::MissingPredecessors`); and
//   * `EquivocationIndex` is queried as "≥2 members of a conflicting-block group lie in `past`",
//     and `past ⊆ closure`, so restricting the index to the closure cannot change the answer.
//
// VERIFIED MODEL: `BlocklaceFinality.isLeaderBlock` / `previousRatifiedLeader` /
// `ratifiedLeaderChain`.

/// **`is_leader_block`** — CM Def. 23 / Alg. 2:43,46 `b.creator = leader(depth(b))`: `b` sits at a
/// wave-START round AND its creator is that wave's round-robin leader.
///
/// A block with no round assignment (a non-participant under `compute_rounds_filtered`) is not a
/// leader block. Mirrors `BlocklaceFinality.isLeaderBlock`.
fn is_leader_block(
    blocklace: &Blocklace,
    rounds: &HashMap<BlockId, u64>,
    participants: &[[u8; 32]],
    config: &OrderingConfig,
    block_id: &BlockId,
) -> bool {
    let Some(block) = blocklace.get(block_id) else {
        return false;
    };
    let Some(&round) = rounds.get(block_id) else {
        return false;
    };
    let wave = round_to_wave(round, config.wavelength);
    round == wave_first_round(wave, config.wavelength)
        && wave_leader(wave, participants) == block.creator
}

/// **`previous_ratified_leader`** — CM Alg. 2:41–43. The DEEPEST leader block, other than `b1`
/// itself, that lies in `b1`'s closure `[b1]` AND is ratified by `b1`.
///
/// **Finality is not consulted**, exactly as in the paper: the recursion walks *ratified* leaders,
/// which need not be super-ratified. Only the head (`find_all_final_leaders().last()`) is final.
///
/// The argmax tie-break: two leader blocks at the same depth are by the same miner (same wave
/// slot), mutually non-observing, hence an equivocating pair — CM Prop. 9's `=` case, which its
/// proof discharges from "a supermajority of correct miners" (at most one of an equivocating pair
/// can hold supermajority approval, Lem. 31). We break by `id` so the function is total and
/// deterministic rather than leaving a `choice`; under the fault bound the tie cannot arise among
/// *ratified* candidates. The comparison is the lexicographic max of `(depth, id)` — an
/// order-independent fold, so iterating the closure as a `HashSet` stays deterministic.
///
/// ⚠ The tie-break direction is transcribed from `BlocklaceFinality.previousRatifiedLeader`, whose
/// fold `if dc < db || (dc == db && c.id < b.id) then b else c` keeps the LARGER id at equal depth.
///
/// # Panics
///
/// Panics if `participants` is empty (via [`wave_leader`]); both callers return early on that.
#[allow(clippy::too_many_arguments)]
fn previous_ratified_leader(
    cache: &PastCache,
    blocklace: &Blocklace,
    rounds: &HashMap<BlockId, u64>,
    equiv: &EquivocationIndex,
    participants: &[[u8; 32]],
    config: &OrderingConfig,
    b1: &BlockId,
) -> Option<BlockId> {
    // `[b1]` — the anchor's inclusive causal past IS the closure the paper quantifies over.
    let closure = causal_past_inclusive(cache, blocklace, b1);

    let mut best: Option<(u64, BlockId)> = None;
    for &candidate in closure.iter() {
        // `R = {b ∈ [b1] \ {b1} : …}`.
        if candidate == *b1 {
            continue;
        }
        if !is_leader_block(blocklace, rounds, participants, config, &candidate) {
            continue;
        }
        let Some(block) = blocklace.get(&candidate) else {
            continue;
        };
        // `ratifies([b1], b)` — `b1` is the observer, so this ranges over exactly `[b1]`.
        if !ratifies(
            cache,
            blocklace,
            equiv,
            b1,
            &candidate,
            &block.creator,
            participants,
        ) {
            continue;
        }
        let depth = rounds.get(&candidate).copied().unwrap_or(0);
        best = match best {
            None => Some((depth, candidate)),
            Some(cur) if cur < (depth, candidate) => Some((depth, candidate)),
            keep => keep,
        };
    }

    best.map(|(_, id)| id)
}

/// **`ratified_leader_chain`** — CM Alg. 2:33–36 walked backward from `head`, materialised
/// OLDEST-FIRST so the ordering fold reads left to right: `[b₁, …, b_k = head]`.
///
/// A pure function of `[head]`. The fuel bound is `|[head]|`: each step strictly shrinks the
/// closure (the predecessor lies in `[b] \ {b}`, and the lace is acyclic), so every chain element
/// is a distinct member of `[head]` — and being closure-local, that bound does not move when the
/// lace grows. Mirrors `BlocklaceFinality.ratifiedLeaderChain`.
fn ratified_leader_chain(
    cache: &PastCache,
    blocklace: &Blocklace,
    rounds: &HashMap<BlockId, u64>,
    equiv: &EquivocationIndex,
    participants: &[[u8; 32]],
    config: &OrderingConfig,
    head: BlockId,
) -> Vec<BlockId> {
    let fuel = causal_past_inclusive(cache, blocklace, &head).len();
    let mut chain = vec![head];
    let mut current = head;
    for _ in 0..fuel {
        match previous_ratified_leader(
            cache,
            blocklace,
            rounds,
            equiv,
            participants,
            config,
            &current,
        ) {
            None => break,
            Some(prev) => {
                chain.push(prev);
                current = prev;
            }
        }
    }
    chain.reverse();
    chain
}

// ─── xsort: Deterministic Topological Sort ───────────────────────────────────

/// Deterministic topological sort of a subset of blocks.
///
/// Respects causal order (if A is in B's causal past, A comes first).
/// For concurrent blocks (no causal relationship), ties are broken by block ID
/// (lexicographic byte comparison), giving a deterministic total order.
fn xsort(cache: &PastCache, blocklace: &Blocklace, blocks: &HashSet<BlockId>) -> Vec<BlockId> {
    if blocks.is_empty() {
        return vec![];
    }

    // Build the restricted subgraph: for each block in the set, find which
    // other blocks in the set are its ancestors.
    let mut local_predecessors: HashMap<BlockId, HashSet<BlockId>> = HashMap::new();

    for &block_id in blocks {
        let past = causal_past_inclusive(cache, blocklace, &block_id);
        let ancestors_in_set: HashSet<BlockId> = past
            .iter()
            .copied()
            .filter(|a| a != &block_id && blocks.contains(a))
            .collect();
        local_predecessors.insert(block_id, ancestors_in_set);
    }

    // Kahn's algorithm with deterministic tie-breaking by block ID.
    let mut in_degree: HashMap<BlockId, usize> = HashMap::new();
    let mut dependents: HashMap<BlockId, Vec<BlockId>> = HashMap::new();

    for (&block_id, ancestors) in &local_predecessors {
        in_degree.insert(block_id, ancestors.len());
        for &ancestor in ancestors {
            dependents.entry(ancestor).or_default().push(block_id);
        }
    }

    // Collect zero in-degree nodes, sorted by block ID for determinism.
    let mut ready: std::collections::BinaryHeap<std::cmp::Reverse<BlockId>> =
        std::collections::BinaryHeap::new();
    for (id, deg) in &in_degree {
        if *deg == 0 {
            ready.push(std::cmp::Reverse(*id));
        }
    }

    let mut result = Vec::with_capacity(blocks.len());

    while let Some(std::cmp::Reverse(block_id)) = ready.pop() {
        result.push(block_id);
        if let Some(deps) = dependents.get(&block_id) {
            for &dep in deps {
                if let Some(deg) = in_degree.get_mut(&dep) {
                    *deg -= 1;
                    if *deg == 0 {
                        ready.push(std::cmp::Reverse(dep));
                    }
                }
            }
        }
    }

    result
}

// ─── The Tau Function ────────────────────────────────────────────────────────

/// Extract the total order from the blocklace (the tau function, CM Def. 6).
///
/// Returns block IDs in their finalized total order. The rule takes ONE head — the DEEPEST final
/// leader (Alg. 2:44–46) — walks backward to the anchor chain `[b₁, …, b_k = head]` through
/// [`previous_ratified_leader`] (Alg. 2:41–43), and folds it left to right. **The per-anchor input
/// is the anchor's OWN inclusive causal past `[l]`** (Alg. 2:37, `xsort(l, [l] \ [b₂])`), minus the
/// previous anchor's closure, minus blocks whose creator equivocated as visible from `l` (CM Alg.
/// 1:17 `approves`), minus blocks whose creator is not in `participants` (the enrollment repair).
///
/// It is NOT a union of ratifier pasts. That is the whole point: a closure is fixed forever by the
/// anchor's own signed hash pointers, so a late-arriving wave-end ratifier can no longer splice
/// blocks into the middle of an already-emitted prefix.
///
/// A leader becomes the HEAD only when a supermajority of DISTINCT ENROLLED participants have
/// wave-end blocks ratifying it ([`ratifies_enrolled`], HORIZONLOG B6). Finality is consulted
/// there and NOWHERE ELSE — the chain walk accepts merely-ratified leaders, per CM Def. 6. A
/// non-participant cannot move the WAVE CLOCK either: [`compute_rounds`] maxes only over
/// predecessors created by `participants`.
///
/// Uses default configuration (wavelength = 3).
///
/// VERIFIED MODEL: this finalization rule is modeled faithfully and executably in Lean at
/// `metatheory/Dregg2/Distributed/BlocklaceFinality.lean` (`tauOrder`, built from `computeRounds`
/// / `findAllFinalLeaders` / `lastFinalLeader` / `ratifiedLeaderChain` / `anchorSegment`), which
/// proves single-leader-per-wave safety and wires the computed order into the verified executor.
/// The Rust↔Lean agreement is enforced by the differential tests
/// `tests::test_tau_differential_against_lean_model` / `test_tau_differential_equivocator_excluded`.
pub fn tau(blocklace: &Blocklace, participants: &[[u8; 32]]) -> Vec<BlockId> {
    tau_with_config(blocklace, participants, &OrderingConfig::default())
}

/// The ordering fold of CM Def. 6, written left to right over the anchor chain:
///
/// ```text
/// τ′(b) := xsort(b, [b])                     if [b] has no leader ratified by b, else
///          τ′(b′) · xsort(b, [b] \ [b′])     if b′ is the last leader ratified by b in [b]
/// ```
///
/// `prev` carries `[b′]`, the PREVIOUS anchor's inclusive causal past (empty for the first anchor)
/// — never a ratifier union. The per-block filter is CM Alg. 1:17's `approves(l, ·)`: membership in
/// `[l]` is automatic because the candidate set IS `[l]`, so what remains is the equivocation
/// clause, evaluated against `[l]`.
///
/// ⚑ THE ENROLLMENT FILTER SITS HERE, INSIDE THE SEGMENT, NOT ON THE FINISHED ORDER, and the Lean
/// puts it in the same place (`BlocklaceFinality.anchorSegmentWith`'s `keep`). [`xsort`] is a Kahn
/// sweep over the segment's own causal subgraph, so an extra element can change WHEN a block
/// becomes ready and therefore the relative order of the blocks around it. Leaving a
/// non-participant's block in the segment would let it reorder honest blocks even with the wave
/// clock filtered. Filtering before `xsort` makes the segment (and its `local_predecessors`)
/// identical on two nodes with identical enrolled sub-laces. The relay still constrains the order:
/// `local_predecessors` is read off the TRANSITIVE causal past, so a block waits for an ancestor
/// it reaches only through a filtered-out relay.
///
/// (Until dregg issue #100 the Lean filtered the finished order instead and linearized with a
/// `(round, id)` KEY sort, for which the two placements coincide. That key sort emitted a block
/// before its own causal ancestors whenever it reached them only through an unenrolled relay —
/// `BlocklaceFinality.traceRelayLift6`. This function never had that defect.)
///
/// ⚠ NAMED RESIDUAL, NOT closed: both linearizers are now ready-set sorts over the same causal
/// subgraph and both are linear extensions of it, but the READY PRIORITY differs — min block id
/// here, `(round, id)` in `xsortBy`, and the ids are different schemes besides (a blake3 hash
/// here, the wire's `(seq, creator)` index there). That is OPEN-CM-XSORT, named in the Lean
/// header, and it belongs in its own pass. It is not confined to sparse laces: measured
/// 2026-11-13, the two SEQUENCES already differ on a round-synchronous lace as soon as a second
/// wave anchors (`node/tests/verified_order_budget.rs`'s exact-sequence gate is red at n=3,
/// rounds=6), because inside one round every block is ready at once and the two priorities
/// order them differently. What both sides do satisfy, and what that file's second gate
/// asserts, is the same finalized set with each order a linear extension of the causal order.
///
/// VERIFIED MODEL: `BlocklaceFinality.anchorSegment` / `tauStep` / `tauOrder`.
fn order_over_anchor_chain(
    cache: &PastCache,
    blocklace: &Blocklace,
    equiv: &EquivocationIndex,
    participant_set: &HashSet<[u8; 32]>,
    chain: &[BlockId],
) -> Vec<BlockId> {
    let mut ordered = Vec::new();
    // `[b₂]` of CM Alg. 2:37 — empty before the first anchor.
    let mut prev: Rc<HashSet<BlockId>> = Rc::new(HashSet::new());

    for anchor in chain {
        let anchor_past = causal_past_inclusive(cache, blocklace, anchor);
        let segment: HashSet<BlockId> = anchor_past
            .iter()
            .copied()
            .filter(|bid| !prev.contains(bid))
            .filter(|bid| match blocklace.get(bid) {
                Some(block) => {
                    !equiv.equivocates_in_past(&block.creator, &anchor_past)
                        && participant_set.contains(&block.creator)
                }
                None => false,
            })
            .collect();

        ordered.extend(xsort(cache, blocklace, &segment));
        prev = anchor_past;
    }

    ordered
}

/// Like `tau`, but with explicit configuration.
///
/// CM Def. 6 / Alg. 2:32,35,37,41–46, in three steps: pick the head (`find_all_final_leaders`'
/// LAST entry — the wave loop runs in increasing wave order, so the last is the deepest — Alg.
/// 2:44–46), walk back to the anchor chain, fold the chain emitting each anchor's own closure
/// minus the previous anchor's. See [`tau`] and [`order_over_anchor_chain`].
///
/// ⚑ THIS IS THE DIFFERENTIAL SIBLING, NOT THE RULE. The authoritative order is the Lean
/// `BlocklaceFinality.tauOrder` via `@[export] dregg_tau_order`; this mirrors it so
/// `poll_finalized_blocks`' per-poll `coord(&lean_order) != coord(&rust_order)` check stays silent
/// on an attacked lace instead of alarming on a divergence that is the fix working.
pub fn tau_with_config(
    blocklace: &Blocklace,
    participants: &[[u8; 32]],
    config: &OrderingConfig,
) -> Vec<BlockId> {
    if participants.is_empty() || blocklace.blocks.is_empty() {
        return vec![];
    }

    let cache = PastCache::new();
    let participant_set: HashSet<[u8; 32]> = participants.iter().copied().collect();
    let (rounds, max_round) = compute_rounds(blocklace, &participant_set);
    let equiv = EquivocationIndex::build(blocklace, &rounds);
    let final_leaders = find_all_final_leaders(
        &cache,
        blocklace,
        &rounds,
        &equiv,
        max_round,
        participants,
        config,
    );

    // `last_final_leader()` (Alg. 2:44–46): the DEEPEST final leader, and the ONLY place finality
    // is consulted. No final leader ⇒ nothing is ordered.
    let Some(&head) = final_leaders.last() else {
        return vec![];
    };

    let chain = ratified_leader_chain(
        &cache,
        blocklace,
        &rounds,
        &equiv,
        participants,
        config,
        head,
    );

    order_over_anchor_chain(&cache, blocklace, &equiv, &participant_set, &chain)
}

// ─── Cordiality Check ────────────────────────────────────────────────────────

/// Check if a block is "cordial": acknowledges a supermajority of the previous round.
///
/// A cordial block has predecessors from > 2n/3 distinct participants at the
/// previous round. Genesis blocks (round 1) are trivially cordial.
pub fn is_cordial(blocklace: &Blocklace, block_id: &BlockId, participants: &[[u8; 32]]) -> bool {
    let participant_set: HashSet<[u8; 32]> = participants.iter().copied().collect();
    let (rounds, _) = compute_rounds(blocklace, &participant_set);

    let round = match rounds.get(block_id) {
        Some(r) => *r,
        None => return false,
    };

    if round <= 1 {
        return true;
    }

    let block = match blocklace.get(block_id) {
        Some(b) => b,
        None => return false,
    };

    let prev_round = round - 1;

    // Which participants have blocks at the previous round.
    let prev_round_creators: HashSet<[u8; 32]> = rounds
        .iter()
        .filter(|(_, r)| **r == prev_round)
        .filter_map(|(id, _)| blocklace.get(id).map(|b| b.creator))
        .collect();

    // How many distinct participants does this block's predecessors acknowledge
    // at the previous round.
    let acknowledged: HashSet<[u8; 32]> = block
        .predecessors
        .iter()
        .filter_map(|pred_id| {
            let pred_block = blocklace.get(pred_id)?;
            let pred_round = rounds.get(pred_id)?;
            if *pred_round == prev_round && prev_round_creators.contains(&pred_block.creator) {
                Some(pred_block.creator)
            } else {
                None
            }
        })
        .collect();

    // THE one quorum formula (#170): `> 2n/3` ⟺ `≥ ⌊2n/3⌋ + 1` — consume
    // `supermajority_threshold` instead of restating it inline.
    acknowledged.len() >= supermajority_threshold(participants.len())
}

// ─── Unified Blocklace: Reference Groups and Filtered Ordering ──────────────

/// A reference group: the set of strands (participants) whose blocks
/// are considered for ordering and finality. This is the unified-lace
/// equivalent of a "federation" — but it's a VIEW over the shared DAG,
/// not an isolated DAG.
///
/// Multiple ReferenceGroups can coexist over the same underlying blocklace --
/// they just look at different strand subsets.
#[derive(Clone, Debug)]
pub struct ReferenceGroup {
    /// The participant strands in this group.
    pub participants: Vec<[u8; 32]>,
    /// Threshold for finality (supermajority).
    pub threshold: usize,
    /// Timeout waves for activity detection.
    pub timeout_waves: u64,
    /// Optional routes commitment (governance).
    pub routes_commitment: Option<[u8; 32]>,
}

impl ReferenceGroup {
    /// Create a new reference group from a participant set.
    ///
    /// Threshold is automatically computed as the supermajority (2n/3 + 1).
    pub fn new(participants: Vec<[u8; 32]>, timeout_waves: u64) -> Self {
        let threshold = supermajority_threshold(participants.len());
        ReferenceGroup {
            participants,
            threshold,
            timeout_waves,
            routes_commitment: None,
        }
    }

    /// Create a reference group from an existing Constitution.
    ///
    /// This is the bridge from the current federation model to the unified model:
    /// a Constitution's participant set becomes a ReferenceGroup that can be used
    /// with `tau_unified`.
    pub fn from_constitution(constitution: &crate::constitution::Constitution) -> Self {
        ReferenceGroup {
            participants: constitution.participants.clone(),
            threshold: constitution.threshold,
            timeout_waves: constitution.timeout_waves,
            routes_commitment: constitution.routes_commitment,
        }
    }

    /// Compute a deterministic group ID from the participant set.
    /// Same participants (sorted) = same group ID, regardless of input order.
    pub fn compute_id(&self) -> [u8; 32] {
        let mut sorted = self.participants.clone();
        sorted.sort();
        let mut hasher = blake3::Hasher::new_derive_key("dregg-group-id-v1");
        for p in &sorted {
            hasher.update(p);
        }
        *hasher.finalize().as_bytes()
    }

    /// Check if a key is a member of this reference group.
    pub fn is_member(&self, key: &[u8; 32]) -> bool {
        self.participants.contains(key)
    }

    /// Number of members in this reference group.
    pub fn member_count(&self) -> usize {
        self.participants.len()
    }

    /// Run tau_unified over the given blocklace using this reference group.
    pub fn finalize(&self, blocklace: &Blocklace, config: &OrderingConfig) -> Vec<BlockId> {
        tau_unified(blocklace, self, config)
    }
}

/// Compute rounds considering only blocks from the reference group.
///
/// Blocks from non-members are assigned no round (effectively invisible).
/// Only blocks whose creator is in `group.participants` get real round numbers.
/// Non-member blocks that are predecessors of member blocks still exist in the
/// DAG but don't advance rounds.
fn compute_rounds_filtered(
    blocklace: &Blocklace,
    group: &ReferenceGroup,
) -> (HashMap<BlockId, u64>, u64) {
    let participant_set: HashSet<[u8; 32]> = group.participants.iter().copied().collect();
    let mut rounds: HashMap<BlockId, u64> = HashMap::new();
    let mut max_round: u64 = 0;

    // Collect only blocks from participants.
    let relevant_block_ids: HashSet<BlockId> = blocklace
        .blocks
        .iter()
        .filter(|(_, block)| participant_set.contains(&block.creator))
        .map(|(id, _)| *id)
        .collect();

    // Build in-degree map considering only edges between relevant blocks.
    let mut in_degree: HashMap<BlockId, usize> = HashMap::new();
    let mut successors: HashMap<BlockId, Vec<BlockId>> = HashMap::new();

    for &id in &relevant_block_ids {
        let block = &blocklace.blocks[&id];
        // Only count predecessors that are ALSO from participants.
        let pred_count = block
            .predecessors
            .iter()
            .filter(|p| relevant_block_ids.contains(*p))
            .count();
        in_degree.insert(id, pred_count);
        for pred in &block.predecessors {
            if relevant_block_ids.contains(pred) {
                successors.entry(*pred).or_default().push(id);
            }
        }
    }

    // Kahn's algorithm (same as compute_rounds, but restricted to participant blocks).
    let mut queue: VecDeque<BlockId> = in_degree
        .iter()
        .filter(|(_, deg)| **deg == 0)
        .map(|(id, _)| *id)
        .collect();

    while let Some(id) = queue.pop_front() {
        let block = &blocklace.blocks[&id];
        let round = if block
            .predecessors
            .iter()
            .all(|p| !relevant_block_ids.contains(p))
        {
            1 // No relevant predecessors = genesis round
        } else {
            1 + block
                .predecessors
                .iter()
                .filter(|p| relevant_block_ids.contains(*p))
                .filter_map(|p| rounds.get(p))
                .max()
                .copied()
                .unwrap_or(0)
        };
        rounds.insert(id, round);
        if round > max_round {
            max_round = round;
        }

        if let Some(succs) = successors.get(&id) {
            for &succ in succs {
                if let Some(deg) = in_degree.get_mut(&succ) {
                    *deg -= 1;
                    if *deg == 0 {
                        queue.push_back(succ);
                    }
                }
            }
        }
    }

    (rounds, max_round)
}

/// Compute total ordering over a SUBSET of strands in the blocklace.
///
/// # Why there are two orderings, and what each is for
///
/// `tau` is the FEDERATION ordering: one reference group, whose participant set the node reads
/// from the constitution each poll, over a lace that is supposed to hold only that group's blocks.
/// `tau_unified` is the UNIFIED-LACE ordering: several `ReferenceGroup`s coexisting as VIEWS over
/// one shared DAG, each finalizing its own strands and ignoring everyone else's. They are not two
/// implementations of one rule — `tau` has one participant set and no notion of an outsider,
/// `tau_unified` is parameterised by which view you are asking about. Neither replaces the other.
///
/// What DID change (the enrollment repairs, in two rounds): `tau`'s docstring used to carry
/// "assumes all blocks belong to participants" as an unchecked PRECONDITION, and the live path
/// cannot honour it — the pinned-ingest roster is insert-only while the constitution's participant
/// set shrinks, and the restart restore (`finality.rs::from_checkpoint`, authenticating since
/// 2026-08-08) reloads the persisted DAG with no ROSTER check. So `tau` enforces items (4) and (5)
/// below for itself:
///   * (5), the OUTPUT filter, closed by `enrolledId` / the `participant_set` filter in
///     `tau_with_config` — an unenrolled creator's state transition cannot reach the executor;
///   * (4), the RATIFIER filter, closed by [`ratifies_enrolled`] (HORIZONLOG B6) — an unenrolled
///     creator can no longer make up a supermajority that anchors a wave, nor shape which blocks a
///     wave's coverage orders. These are independent: (5) held of the pre-B6 rule too, because the
///     unenrolled creator's OWN blocks were dropped from the ORDER while its VOTE still finalized
///     the honest ones.
///   * (1) and (2), the WAVE CLOCK, closed by [`compute_rounds`] taking the participant set. A
///     non-participant's ack no longer adds depth, so a relay chain cannot move which round a
///     block sits at, which round is a wave start or wave end, or where `xsort` puts an honest
///     block. That was NOT merely wave timing, which is how it was written up when B6 left it
///     open: two honest nodes holding the IDENTICAL enrolled sub-lace and differing only in
///     whether they received the relay finalized the same coordinates in different orders
///     (`BlocklaceFinality.traceOrderFork`) or one of them finalized nothing at all
///     (`traceRelayStall`) — a fork and a stall, not a delay.
///
/// ⚑ **(3) is what remains** — leader selection is already participant-only in `tau`, but the two
/// functions' LINEARIZERS still differ: both are Kahn sweeps over the segment's causal subgraph,
/// but [`xsort`] pops the min block id and the Lean `xsortBy` pops the least `(round, id)`. That
/// is OPEN-CM-XSORT, named in the Lean header, and it is a different defect from this one.
///
/// The algorithm is the same as `tau_with_config` — CM Def. 6's head selection, backward anchor
/// chain and closure-difference fold, sharing [`ratified_leader_chain`] and
/// [`order_over_anchor_chain`] with it — but:
/// 1. `compute_rounds_filtered` only counts blocks from `reference_group.participants`
/// 2. Wave assignment uses filtered rounds
/// 3. Leader selection from reference group only
/// 4. Approval/ratification counts from reference group only (`tau` now does this too)
/// 5. Output only contains blocks from reference group participants (`tau` now does this too)
///
/// External blocks in the DAG are IGNORED (not counted for rounds, waves, or finality).
pub fn tau_unified(
    blocklace: &Blocklace,
    reference_group: &ReferenceGroup,
    config: &OrderingConfig,
) -> Vec<BlockId> {
    let participants = &reference_group.participants;
    if participants.is_empty() || blocklace.blocks.is_empty() {
        return vec![];
    }

    let participant_set: HashSet<[u8; 32]> = participants.iter().copied().collect();

    // Use filtered rounds (only participant blocks contribute to wave structure).
    let cache = PastCache::new();
    let (rounds, max_round) = compute_rounds_filtered(blocklace, reference_group);
    let equiv = EquivocationIndex::build(blocklace, &rounds);

    // Find finalized leaders using filtered rounds (only considers participant blocks).
    let final_leaders = find_all_final_leaders(
        &cache,
        blocklace,
        &rounds,
        &equiv,
        max_round,
        participants,
        config,
    );

    // `last_final_leader()` (Alg. 2:44–46) — the deepest final leader, and the only consultation of
    // finality. The chain walk below accepts merely-RATIFIED leaders (CM Def. 6).
    let Some(&head) = final_leaders.last() else {
        return vec![];
    };

    let chain = ratified_leader_chain(
        &cache,
        blocklace,
        &rounds,
        &equiv,
        participants,
        config,
        head,
    );

    order_over_anchor_chain(&cache, blocklace, &equiv, &participant_set, &chain)
}

// ─── Constitution-Aware Ordering ─────────────────────────────────────────────

/// Extract the total order from the blocklace using the constitution's participant set.
///
/// This is the constitution-integrated version of `tau`: it uses the constitution's
/// participant list for wave leader election and the constitution's threshold for
/// supermajority checks.
///
/// After ordering completes, the caller should:
/// 1. Scan the newly-ordered blocks for membership proposals that have passed.
/// 2. Apply those proposals to the constitution (via `ConstitutionManager::apply_if_passed`).
/// 3. Use the updated participant list for subsequent calls.
///
/// This ensures that membership changes take effect at well-defined wave boundaries.
pub fn tau_with_constitution(
    blocklace: &Blocklace,
    constitution: &crate::constitution::Constitution,
) -> Vec<BlockId> {
    tau_with_config(
        blocklace,
        &constitution.participants,
        &OrderingConfig::default(),
    )
}

/// Like `tau_with_constitution`, but with explicit ordering config.
pub fn tau_with_constitution_and_config(
    blocklace: &Blocklace,
    constitution: &crate::constitution::Constitution,
    config: &OrderingConfig,
) -> Vec<BlockId> {
    tau_with_config(blocklace, &constitution.participants, config)
}

/// Check cordiality using the constitution's participant set and threshold.
///
/// A block is cordial if it acknowledges blocks from `> constitution.threshold - 1`
/// distinct participants at the previous round.
pub fn is_cordial_with_constitution(
    blocklace: &Blocklace,
    block_id: &BlockId,
    constitution: &crate::constitution::Constitution,
) -> bool {
    is_cordial(blocklace, block_id, &constitution.participants)
}

// ─── Integration helpers ─────────────────────────────────────────────────────

/// Get the finalized total order of blocks with their payloads.
///
/// Returns (block_id, payload_bytes) pairs in finalized order.
/// Only includes blocks with non-empty payloads (i.e., actual turns/data,
/// not empty heartbeats).
pub fn finalized_turns(
    blocklace: &Blocklace,
    participants: &[[u8; 32]],
) -> Vec<(BlockId, Vec<u8>)> {
    tau(blocklace, participants)
        .into_iter()
        .filter_map(|id| {
            let block = blocklace.get(&id)?;
            if block.payload.is_empty() {
                None
            } else {
                Some((id, block.payload.clone()))
            }
        })
        .collect()
}

/// Check if a specific block has been finalized (appears in tau's output).
pub fn is_finalized(blocklace: &Blocklace, block_id: &BlockId, participants: &[[u8; 32]]) -> bool {
    tau(blocklace, participants).contains(block_id)
}

// ─── Tests ───────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Block;

    fn make_key(byte: u8) -> [u8; 32] {
        [byte; 32]
    }

    /// Create a block using the root-level Block type.
    fn make_block(
        creator: [u8; 32],
        sequence: u64,
        predecessors: Vec<BlockId>,
        payload: Vec<u8>,
    ) -> Block {
        Block::new(creator, sequence, predecessors, payload)
    }

    /// Build a fully-connected blocklace: n participants, each producing one block
    /// per round, referencing ALL blocks from the previous round.
    fn build_full_blocklace(
        participants: &[[u8; 32]],
        num_rounds: u64,
    ) -> (Blocklace, Vec<Vec<BlockId>>) {
        let mut bl = Blocklace::new();
        let mut blocks_by_round: Vec<Vec<BlockId>> = Vec::new();

        for round in 1..=num_rounds {
            let preds: Vec<BlockId> = if round == 1 {
                vec![]
            } else {
                blocks_by_round[(round - 2) as usize].clone()
            };

            let mut round_blocks = Vec::new();
            for (i, &participant) in participants.iter().enumerate() {
                let seq = (round - 1) as u64;
                let payload = vec![round as u8, i as u8];
                let block = make_block(participant, seq, preds.clone(), payload);
                let id = block.id();
                bl.insert_unverified(block).unwrap();
                round_blocks.push(id);
            }
            blocks_by_round.push(round_blocks);
        }

        (bl, blocks_by_round)
    }

    #[test]
    fn test_round_to_wave() {
        assert_eq!(round_to_wave(1, 3), 0);
        assert_eq!(round_to_wave(2, 3), 0);
        assert_eq!(round_to_wave(3, 3), 0);
        assert_eq!(round_to_wave(4, 3), 1);
        assert_eq!(round_to_wave(5, 3), 1);
        assert_eq!(round_to_wave(6, 3), 1);
        assert_eq!(round_to_wave(7, 3), 2);
    }

    #[test]
    fn round_to_wave_zero_does_not_underflow() {
        // Rounds are 1-indexed, so `round == 0` is out of contract — but it must
        // not underflow `round - 1` (debug panic / release wrap to u64::MAX).
        // The `saturating_sub` maps it to wave 0.
        for wl in [1u64, 2, 3, 5] {
            assert_eq!(
                round_to_wave(0, wl),
                0,
                "round_to_wave(0, {wl}) must be 0, not u64::MAX"
            );
        }
    }

    #[test]
    fn test_wave_helpers() {
        assert_eq!(wave_first_round(0, 3), 1);
        assert_eq!(wave_last_round(0, 3), 3);
        assert_eq!(wave_first_round(1, 3), 4);
        assert_eq!(wave_last_round(1, 3), 6);
    }

    #[test]
    fn test_wave_leader_round_robin() {
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        assert_eq!(wave_leader(0, &participants), make_key(1));
        assert_eq!(wave_leader(1, &participants), make_key(2));
        assert_eq!(wave_leader(2, &participants), make_key(3));
        assert_eq!(wave_leader(3, &participants), make_key(1)); // wraps
    }

    #[test]
    fn test_supermajority_threshold() {
        assert_eq!(supermajority_threshold(0), 1); // empty committee: fail-closed
        assert_eq!(supermajority_threshold(1), 1); // solo: own block suffices
        assert_eq!(supermajority_threshold(2), 2); // both
        assert_eq!(supermajority_threshold(3), 3); // 2*3/3 + 1 = 3 (NOT 2: n=3f)
        assert_eq!(supermajority_threshold(4), 3); // 2*4/3 + 1 = 3
        assert_eq!(supermajority_threshold(6), 5); // n=3f again: strictly > 2n/3
        assert_eq!(supermajority_threshold(7), 5); // 2*7/3 + 1 = 5
        assert_eq!(supermajority_threshold(10), 7); // 2*10/3 + 1 = 7
    }

    /// Unconditional quorum intersection: two quorums share STRICTLY more
    /// than the Byzantine budget `⌊(n−1)/3⌋` at every committee size — the
    /// property the federation's historical `n − ⌊n/3⌋` lacked at `3 ∣ n`.
    #[test]
    fn test_supermajority_quorum_intersection_unconditional() {
        for n in 1..=512usize {
            let q = supermajority_threshold(n);
            let f = (n - 1) / 3;
            assert!(q <= n, "quorum must be formable at n={n}");
            // |Q1 ∩ Q2| ≥ 2q − n must strictly exceed f.
            assert!(2 * q - n > f, "quorum intersection > fault budget at n={n}");
            // Equivalent closed form for n ≥ 1.
            assert_eq!(q, n - f, "supermajority = n - floor((n-1)/3) at n={n}");
        }
    }

    /// **THE ROUNDS LEAK, EXECUTED — and the repair, at the point of the fix.**
    ///
    /// `compute_rounds` used to max over EVERY present predecessor. Depth is the wave clock, so a
    /// NON-PARTICIPANT chain that one honest block acked moved the wave structure. This drives the
    /// module's own `compute_rounds` twice on ONE lace and changes exactly one thing: the
    /// participant set it is handed.
    ///
    /// **The second call IS the pre-repair recurrence, not a reimplementation of it.** Hand it a
    /// set containing every creator in the lace and the enrollment filter is the identity — which
    /// is precisely `BlocklaceFinality.computeRounds_eq_pre_of_enrolled` (on an `EnrolledLace` the
    /// filtered map is bit-identical to `computeRoundsPreParticipant`). So `pre` is what this
    /// function computed yesterday and `now` is what it computes today.
    ///
    /// Verified twin: `BlocklaceFinality.traceRelayStall` and its `#guard` red/green pair.
    #[test]
    fn compute_rounds_gives_a_nonparticipant_relay_no_depth() {
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        // Three outsiders, one block each, chained: r1 <- r2 <- r3. Three blocks, depth three.
        let outsiders = [make_key(7), make_key(8), make_key(9)];

        let mut bl = Blocklace::new();
        let push = |bl: &mut Blocklace, c: [u8; 32], seq: u64, preds: Vec<BlockId>, tag: u8| {
            let b = make_block(c, seq, preds, vec![tag]);
            let id = b.id();
            bl.insert_unverified(b).unwrap();
            id
        };
        let r1 = push(&mut bl, outsiders[0], 0, vec![], 0x71);
        let r2 = push(&mut bl, outsiders[1], 0, vec![r1], 0x72);
        let r3 = push(&mut bl, outsiders[2], 0, vec![r2], 0x73);

        let l1: Vec<BlockId> = participants
            .iter()
            .enumerate()
            .map(|(i, &p)| push(&mut bl, p, 0, vec![], 0x10 + i as u8))
            .collect();
        // ONE honest block acks the relay tip; the other two are ordinary.
        let c1 = push(
            &mut bl,
            participants[0],
            1,
            {
                let mut v = l1.clone();
                v.push(r3);
                v
            },
            0x20,
        );
        let c2 = push(&mut bl, participants[1], 1, l1.clone(), 0x21);
        let c3 = push(&mut bl, participants[2], 1, l1.clone(), 0x22);
        let l2 = vec![c1, c2, c3];
        let l3: Vec<BlockId> = participants
            .iter()
            .enumerate()
            .map(|(i, &p)| push(&mut bl, p, 2, l2.clone(), 0x30 + i as u8))
            .collect();

        let enrolled: HashSet<[u8; 32]> = participants.iter().copied().collect();
        let every_creator: HashSet<[u8; 32]> = participants
            .iter()
            .chain(outsiders.iter())
            .copied()
            .collect();

        let (pre, _) = compute_rounds(&bl, &every_creator); // == the pre-repair recurrence
        let (now, _) = compute_rounds(&bl, &enrolled);

        // ── (RED) THE WOUND: the relay is three levels deep and it LENDS them to an honest block.
        assert_eq!(pre[&r3], 3, "anti-vacuity: the relay really is three deep");
        assert_eq!(
            pre[&c1], 4,
            "the wound: an honest layer-2 block sits at round 4 because it acked an outsider chain"
        );
        assert_eq!(
            pre[&l3[0]], 5,
            "…and the whole layer above it moves with it"
        );
        // …so at the wave-end round of wave 0 (wavelength 3) there is NOT ONE enrolled block: the
        // committee's ratification is counted at a round only the outsider occupies.
        let pre_at_3: HashSet<BlockId> = pre
            .iter()
            .filter(|(_, r)| **r == 3)
            .map(|(id, _)| *id)
            .collect();
        assert_eq!(
            pre_at_3,
            HashSet::from([r3]),
            "the wound: the wave-END round holds only the relay tip"
        );

        // ── (GREEN) THE REPAIR: an outsider ack contributes no depth.
        assert_eq!(now[&r1], 1);
        assert_eq!(
            now[&r2], 1,
            "the relay's own depth collapses: its ancestry is all outsiders"
        );
        assert_eq!(now[&r3], 1);
        assert_eq!(
            now[&c1], 2,
            "the honest block is back where the committee put it"
        );
        assert_eq!(now[&c2], 2);
        assert_eq!(now[&l3[0]], 3);
        let now_at_3: HashSet<BlockId> = now
            .iter()
            .filter(|(_, r)| **r == 3)
            .map(|(id, _)| *id)
            .collect();
        assert_eq!(
            now_at_3,
            l3.iter().copied().collect::<HashSet<_>>(),
            "the wave-end round is the committee's own three blocks again"
        );

        // ── RE-ARMED AT WAVE 1. Under CM Def. 6 an anchor orders its OWN closure, so a one-wave
        //    (3-round) lace finalizes exactly the anchor and nothing else — the liveness pole has
        //    to be armed at the depth where the committee's rounds 1-3 are actually ORDERED, which
        //    is when wave 1's anchor appears at round 4 and observes them. Rounds 4-6, same shape.
        let mut prev_round = l3.clone();
        for round in 4..=6u64 {
            let this_round: Vec<BlockId> = participants
                .iter()
                .enumerate()
                .map(|(i, &p)| {
                    push(
                        &mut bl,
                        p,
                        round - 1,
                        prev_round.clone(),
                        0x40 + (round as u8) * 8 + i as u8,
                    )
                })
                .collect();
            prev_round = this_round;
        }

        // ── BOTH POLES ON THE ORDER ITSELF: the committee still finalizes everything it produced
        //    through round 3, and it finalizes IDENTICALLY to a node that never received the relay.
        let order = tau(&bl, &participants);
        assert_eq!(
            order.len(),
            10,
            "[LIVENESS] the honest committee still finalizes everything: 3 participants x rounds \
             1-3 ordered by wave 1's anchor, plus wave 0's anchor in its own segment"
        );
        let ordered: HashSet<BlockId> = order.iter().copied().collect();
        for id in l1.iter().chain(l2.iter()).chain(l3.iter()) {
            assert!(
                ordered.contains(id),
                "every enrolled block of rounds 1-3 must be finalized once wave 1 anchors"
            );
        }
        assert!(
            order.iter().all(|id| {
                let c = bl.get(id).unwrap().creator;
                participants.contains(&c)
            }),
            "no outsider coordinate may be finalized"
        );

        // ── THE LIVENESS POLE AT THE RECURRENCE: on an all-enrolled lace the filter is the
        //    IDENTITY, so no honest federation's clock moves by one tick
        //    (`BlocklaceFinality.computeRounds_eq_pre_of_enrolled`, executably).
        let (hon, _) = build_full_blocklace(&participants, 3);
        let (hon_now, hon_max) = compute_rounds(&hon, &enrolled);
        let (hon_pre, hon_pre_max) = compute_rounds(&hon, &every_creator);
        assert_eq!(
            hon_now, hon_pre,
            "all-enrolled lace: the filter must change nothing"
        );
        assert_eq!(hon_max, hon_pre_max);
    }

    /// ONE wave orders exactly its anchor; the wave's other blocks are ordered by the NEXT anchor
    /// that observes them.
    ///
    /// RE-ARMED for CM Def. 6. This used to assert "3 nodes x 3 rounds = 9 blocks finalized at one
    /// wave". That premise is gone with the τ re-authoring: an anchor's segment is its OWN closure
    /// `[l]`, and wave 0's anchor is a genesis block whose closure is just itself, so a one-wave
    /// lace orders ONE block. The nine only become ordered when wave 1's anchor observes them —
    /// that is CM's real latency, not a regression. Both depths are asserted here so the change is
    /// visible at the point where it happens.
    #[test]
    fn test_three_node_one_wave_finalized() {
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        let (bl, by_round) = build_full_blocklace(&participants, 3);

        let result = tau(&bl, &participants);

        // ONE wave: exactly the wave-0 anchor (creator 1's genesis, the round-robin leader).
        assert_eq!(
            result.len(),
            1,
            "one wave orders exactly its anchor's closure, got {}",
            result.len()
        );
        assert_eq!(
            bl.get(&result[0]).unwrap().creator,
            participants[0],
            "the ordered block is wave 0's round-robin leader"
        );
        assert!(by_round[0].contains(&result[0]));

        // Determinism check.
        let result2 = tau(&bl, &participants);
        assert_eq!(result, result2);

        // TWO waves: wave 1's anchor observes rounds 1-3, so all nine of them land, plus the
        // wave-1 anchor itself = 10.
        let (bl6, _) = build_full_blocklace(&participants, 6);
        let result6 = tau(&bl6, &participants);
        assert_eq!(
            result6.len(),
            10,
            "two waves: 3 nodes x 3 rounds ordered by wave 1's anchor, plus wave 0's anchor, got {}",
            result6.len()
        );
    }

    /// DIFFERENTIAL: the Rust `ordering::tau` finalization AGREES with the verified Lean model
    /// (`metatheory/Dregg2/Distributed/BlocklaceFinality.lean::tauGolden`) on this exact trace.
    ///
    /// The Lean module is a faithful, executable model of THIS function (`compute_rounds` /
    /// `find_all_final_leaders` / `last_final_leader` / `ratified_leader_chain` / `anchorSegment`).
    ///
    /// **DEEPENED TO SIX ROUNDS for CM Def. 6.** The fixture used to be the 3-node / 3-round
    /// fully-connected lace, whose Lean golden was all nine blocks. Under the re-authored τ that
    /// lace's golden is `[10]` — ONE block, wave 0's genesis anchor, whose closure is itself — so
    /// the 3-round differential would be trivial. Rounds 4-6 make wave 1 anchor (creator 2's block
    /// at round 4, Lean id `23`), and the Lean golden becomes the ten-block vector
    ///
    ///   tauOrder = [10, 20, 30, 11, 21, 31, 12, 22, 32, 23]
    ///
    /// i.e. wave 0's anchor alone, then wave 1's segment: everything in `[23]` that `[10]` did not
    /// cover, round-major. Projected to `(creator, seq)`:
    ///
    ///   tauGolden = [(1,0),(2,0),(3,0),(1,1),(2,1),(3,1),(1,2),(2,2),(3,2),(2,3)]
    ///
    /// The absolute `BlockId` differs (blake3 hash here vs. an abstract `Nat` in Lean), and the
    /// *within-cohort* tie-break is the named OPEN-CM-XSORT residual (Rust breaks by block-id, Lean
    /// by `(round,id)`), so the load-bearing differential is at the SEQ-COHORT level: the sequence
    /// of seq cohorts, and each cohort's `{creator}` set, must match the Lean golden exactly. Note
    /// the cohorts are no longer uniform — `[1] [3] [3] [3]` — which is itself the shape of the
    /// anchor-chain fold and would not survive a return to the coverage rule.
    #[test]
    fn test_tau_differential_against_lean_model() {
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        let (bl, _) = build_full_blocklace(&participants, 6);
        let result = tau(&bl, &participants);

        // Project the finalized order to (creator_byte, seq) — the differential coordinate.
        let projected: Vec<(u8, u64)> = result
            .iter()
            .filter_map(|id| bl.get(id).map(|b| (b.creator[0], b.sequence)))
            .collect();

        // The Lean golden vector for `trace3` grown by a full second wave.
        let lean_golden: Vec<(u8, u64)> = vec![
            (1, 0),
            (2, 0),
            (3, 0),
            (1, 1),
            (2, 1),
            (3, 1),
            (1, 2),
            (2, 2),
            (3, 2),
            (2, 3),
        ];

        assert_eq!(
            projected.len(),
            lean_golden.len(),
            "same number of finalized blocks as the Lean model, got {projected:?}"
        );

        // SET agreement first: exactly the Lean model's coordinates, no more, no fewer.
        let mut sorted_rust = projected.clone();
        sorted_rust.sort();
        let mut sorted_lean = lean_golden.clone();
        sorted_lean.sort();
        assert_eq!(
            sorted_rust, sorted_lean,
            "Rust tau must finalize exactly the Lean model's (creator, seq) coordinates"
        );

        // SEQ-COHORT agreement: group CONSECUTIVE equal-seq entries (a cohort is emitted
        // contiguously by both implementations) and compare the cohort sequence.
        let cohorts = |v: &[(u8, u64)]| -> Vec<(u64, Vec<u8>)> {
            let mut out: Vec<(u64, Vec<u8>)> = Vec::new();
            for &(creator, seq) in v {
                match out.last_mut() {
                    Some((s, creators)) if *s == seq => creators.push(creator),
                    _ => out.push((seq, vec![creator])),
                }
            }
            for (_, creators) in &mut out {
                creators.sort();
            }
            out
        };
        let rust_seqs: Vec<u64> = projected.iter().map(|(_, s)| *s).collect();
        assert!(
            rust_seqs.windows(2).all(|w| w[0] <= w[1]),
            "Rust tau is round-major (seq non-decreasing), matching the Lean model's order"
        );
        assert_eq!(
            cohorts(&projected),
            cohorts(&lean_golden),
            "Rust ordering::tau seq-cohorts must equal the verified Lean model's tauGolden cohorts \
             (consensus model⟺node differential)"
        );
        // The anchor-chain fold made visible: wave 0's anchor IS a segment of its own, so it leads
        // the order regardless of block-id. Under the coverage rule the first segment was the whole
        // wave-0 coverage in one `xsort`, whose leading element was whichever genesis block
        // happened to carry the smallest blake3 id.
        assert_eq!(
            projected[0],
            (1, 0),
            "wave 0's anchor must lead the order — it is a one-block segment, not the min-id \
             element of a coverage sweep"
        );
    }

    /// DIFFERENTIAL (negative tooth): the Rust `tau` EXCLUDES an equivocating leader, agreeing with
    /// the Lean model's `traceEquiv` `#guard` (`tauOrder traceEquiv … all creator ≠ 1`). When the
    /// wave-0 round-robin leader (creator 1) double-signs at the leader slot, NO block from creator 1
    /// is finalized — exactly the Lean model's equivocation-exclusion result on the matching trace.
    #[test]
    fn test_tau_differential_equivocator_excluded() {
        // creator 1 equivocates at round 1 (two genesis blocks), mirroring the Lean `traceEquiv`
        // and the existing `test_equivocating_block_excluded`.
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        let mut bl = Blocklace::new();

        let b1a = make_block(make_key(1), 0, vec![], vec![1]);
        let b1a_id = b1a.id();
        let b1b = make_block(make_key(1), 1, vec![], vec![2]);
        let b1b_id = b1b.id();
        let b2 = make_block(make_key(2), 0, vec![], vec![3]);
        let b2_id = b2.id();
        let b3 = make_block(make_key(3), 0, vec![], vec![4]);
        let b3_id = b3.id();
        bl.insert_unverified(b1a).unwrap();
        bl.insert_unverified(b1b).unwrap();
        bl.insert_unverified(b2).unwrap();
        bl.insert_unverified(b3).unwrap();

        let preds_r2 = vec![b1a_id, b1b_id, b2_id, b3_id];
        let r2_2 = make_block(make_key(2), 1, preds_r2.clone(), vec![6]);
        let r2_3 = make_block(make_key(3), 1, preds_r2.clone(), vec![7]);
        let r2_2_id = r2_2.id();
        let r2_3_id = r2_3.id();
        bl.insert_unverified(r2_2).unwrap();
        bl.insert_unverified(r2_3).unwrap();

        let preds_r3 = vec![r2_2_id, r2_3_id];
        bl.insert_unverified(make_block(make_key(2), 2, preds_r3.clone(), vec![9]))
            .unwrap();
        bl.insert_unverified(make_block(make_key(3), 2, preds_r3.clone(), vec![10]))
            .unwrap();

        let result = tau(&bl, &participants);
        // Agreeing with the Lean model: the equivocator (creator 1) contributes NO finalized block.
        for id in &result {
            let block = bl.get(id).unwrap();
            assert_ne!(
                block.creator,
                make_key(1),
                "equivocator excluded — matches Lean BlocklaceFinality traceEquiv #guard"
            );
        }
    }

    /// DIFFERENTIAL (the ENROLLMENT tooth): the Rust `tau` finalizes NO block from a creator that
    /// is not in `participants`, agreeing with the Lean model's `traceUnenrolled` `#guard`s
    /// (`tauOrder traceUnenrolled … all creator ≠ 9`, length 9, golden == `trace3`'s).
    ///
    /// This is the Rust face of the finding `node/src/finality_gate.rs:379` measured: a fourth
    /// creator with a perfectly valid key that was never enrolled produces well-formed blocks at
    /// every round, fully cross-linked into the honest DAG, and the honest nodes ack them back —
    /// so they sit in the honest leader's causal past and the per-anchor segment sweeps them into
    /// the finalized order (that site was `leaderCoverage`, since DELETED with the CM Def. 6 rewrite). Before the enrollment filter this lace finalized 12 of 12 blocks, all
    /// three of the unenrolled creator's included.
    ///
    /// BOTH HALVES, because a rule that refuses everyone is not a fix:
    ///   * the unenrolled creator contributes NOTHING, and
    ///   * every one of the three ENROLLED participants' nine blocks still finalizes, in the same
    ///     round-cohort order as the un-attacked 3-node lace.
    /// Plus the anti-vacuity check that the adversary is genuinely IN the lace and genuinely
    /// REFERENCED by honest blocks — otherwise "refused" would just mean "never present".
    #[test]
    fn test_tau_differential_unenrolled_creator_excluded() {
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        let unenrolled = make_key(9);
        assert!(
            !participants.contains(&unenrolled),
            "the unenrolled creator must not be enrolled — else this test has no adversary"
        );
        let all_creators = vec![make_key(1), make_key(2), make_key(3), unenrolled];
        // SIX rounds, not three: under CM Def. 6 an anchor orders its own closure, so the enrolled
        // committee's rounds 1-3 are ordered by wave 1's anchor at round 4. At three rounds the
        // refusal below would be satisfied by a τ that emits a single block, which proves nothing.
        let (bl, blocks_by_round) = build_full_blocklace(&all_creators, 6);

        // ANTI-VACUITY 1 — the adversary is genuinely in the lace, at every round.
        let unenrolled_in_lace = bl
            .blocks
            .values()
            .filter(|b| b.creator == unenrolled)
            .count();
        assert_eq!(
            unenrolled_in_lace, 6,
            "the unenrolled creator must have a block at every round — else nothing to refuse"
        );
        // ANTI-VACUITY 2 — honest blocks ACK it, so it is load-bearing in the causal past and
        // cannot be refused by ignoring an unreferenced subgraph.
        let unenrolled_r1: Vec<BlockId> = blocks_by_round[0]
            .iter()
            .copied()
            .filter(|id| bl.get(id).map(|b| b.creator) == Some(unenrolled))
            .collect();
        assert_eq!(unenrolled_r1.len(), 1);
        assert!(
            blocks_by_round[1]
                .iter()
                .filter(|id| bl.get(id).map(|b| b.creator) != Some(unenrolled))
                .all(|id| bl.get(id).unwrap().predecessors.contains(&unenrolled_r1[0])),
            "every honest round-2 block must ack the unenrolled creator's genesis — else the \
             adversary is not in the honest leader's causal past and the refusal is free"
        );

        let result = tau(&bl, &participants);

        // HALF 1 — THE REFUSAL. No finalized block is from the unenrolled creator.
        for id in &result {
            let block = bl.get(id).unwrap();
            assert_ne!(
                block.creator, unenrolled,
                "tau finalized a block from an UNENROLLED creator — an unenrolled node can inject \
                 state transitions into the executor (Lean: BlocklaceFinality traceUnenrolled #guard)"
            );
        }

        // HALF 2 — THE ENROLLED PARTICIPANTS STILL FINALIZE, all nine of them, in the same
        // round-cohort order as the clean 3-node lace. Without this, HALF 1 is satisfied by a
        // rule that finalizes nothing.
        assert_eq!(
            result.len(),
            10,
            "all NINE enrolled blocks of rounds 1-3 must still finalize, plus wave 1's anchor — a \
             rule that refuses everyone is not a fix"
        );
        let mut projected: Vec<(u8, u64)> = result
            .iter()
            .filter_map(|id| bl.get(id).map(|b| (b.creator[0], b.sequence)))
            .collect();
        let seqs: Vec<u64> = projected.iter().map(|(_, s)| *s).collect();
        assert!(
            seqs.windows(2).all(|w| w[0] <= w[1]),
            "the surviving order is still round-major, matching the Lean model"
        );
        projected.sort();
        assert_eq!(
            projected,
            vec![
                (1, 0),
                (1, 1),
                (1, 2),
                (2, 0),
                (2, 1),
                (2, 2),
                (2, 3),
                (3, 0),
                (3, 1),
                (3, 2)
            ],
            "the finalized (creator, seq) set must be exactly the three enrolled participants' \
             rounds 1-3 plus wave 1's anchor (creator 2, seq 3) — the Lean \
             `tauGolden traceUnenrolled == tauGolden trace3` guard"
        );
    }

    /// The enrollment filter is the IDENTITY on an ENROLLED lace — the Rust face of the Lean
    /// `tauOrder_enrolled_eq_unfiltered` theorem and its `#guard`s. Nothing an honest federation
    /// produces is dropped: same blocks, same order, same length as before the filter existed.
    /// This is the liveness half of the enrollment change, stated where it can fail.
    #[test]
    fn test_tau_enrollment_filter_is_identity_on_enrolled_lace() {
        for n in 3..=5usize {
            let participants: Vec<[u8; 32]> = (1..=n as u8).map(make_key).collect();
            // SIX rounds: CM Def. 6 orders a wave's blocks at the NEXT anchor that observes them,
            // so "every block still finalizes" is a claim about rounds 1-3 once wave 1 anchors.
            let (bl, _) = build_full_blocklace(&participants, 6);
            let result = tau(&bl, &participants);
            assert_eq!(
                result.len(),
                3 * n + 1,
                "on an ENROLLED lace every block of rounds 1-3 still finalizes at n={n} (plus \
                 wave 1's anchor) — the enrollment filter must be a pure subtraction of \
                 NON-participants, never a liveness trade"
            );
            // and every finalized creator is a participant (trivially, but it pins the direction).
            for id in &result {
                assert!(participants.contains(&bl.get(id).unwrap().creator));
            }
        }
    }

    /// Build a lace whose per-round creator sets are given EXPLICITLY (so a round can be missing a
    /// participant, or hold only non-participants), every block referencing ALL blocks of the
    /// previous round — the same fully-connected shape `build_full_blocklace` produces.
    fn build_lace_by_round(rounds_creators: &[Vec<[u8; 32]>]) -> (Blocklace, Vec<Vec<BlockId>>) {
        let mut bl = Blocklace::new();
        let mut by_round: Vec<Vec<BlockId>> = Vec::new();
        for (r, creators) in rounds_creators.iter().enumerate() {
            let preds: Vec<BlockId> = if r == 0 {
                vec![]
            } else {
                by_round[r - 1].clone()
            };
            let mut this_round = Vec::new();
            for (i, &creator) in creators.iter().enumerate() {
                let block = make_block(creator, r as u64, preds.clone(), vec![r as u8, i as u8]);
                let id = block.id();
                bl.insert_unverified(block).unwrap();
                this_round.push(id);
            }
            by_round.push(this_round);
        }
        (bl, by_round)
    }

    /// The distinct creators of wave-end blocks that `ratifies` the leader, split into ALL and
    /// ENROLLED.
    ///
    /// This is a MEASUREMENT, not a reimplementation of the fix: it drives the module's own
    /// `compute_rounds`, `EquivocationIndex` and `ratifies` — the exact primitives
    /// `is_super_ratified` composes — and the only thing it does differently is decline to apply
    /// the enrollment gate. So `all` IS the pre-B6 ratifier count and `enrolled` is the post-B6
    /// one, and asserting `all >= threshold > enrolled` executes the wound rather than describing
    /// it.
    fn wave_end_ratifier_creators(
        bl: &Blocklace,
        participants: &[[u8; 32]],
        leader_id: &BlockId,
        wave_end_round: u64,
    ) -> (HashSet<[u8; 32]>, HashSet<[u8; 32]>) {
        let cache = PastCache::new();
        let (rounds, _) = compute_rounds(bl, &participants.iter().copied().collect());
        let equiv = EquivocationIndex::build(bl, &rounds);
        let leader_creator = bl.get(leader_id).expect("leader in lace").creator;
        let all: HashSet<[u8; 32]> = rounds
            .iter()
            .filter(|(_, r)| **r == wave_end_round)
            .filter(|(id, _)| {
                ratifies(
                    &cache,
                    bl,
                    &equiv,
                    id,
                    leader_id,
                    &leader_creator,
                    participants,
                )
            })
            .filter_map(|(id, _)| bl.get(id).map(|b| b.creator))
            .collect();
        let enrolled: HashSet<[u8; 32]> = all
            .iter()
            .copied()
            .filter(|c| participants.contains(c))
            .collect();
        (all, enrolled)
    }

    /// The wave-0 leader block: the round-robin leader's block at the wave-start round.
    fn wave0_leader_block(bl: &Blocklace, by_round: &[Vec<BlockId>], leader: [u8; 32]) -> BlockId {
        by_round[0]
            .iter()
            .copied()
            .find(|id| bl.get(id).map(|b| b.creator) == Some(leader))
            .expect("the wave-0 leader must have a genesis block")
    }

    /// **HORIZONLOG B6 — A NON-PARTICIPANT'S BLOCK MUST NOT MAKE UP A SUPERMAJORITY.**
    ///
    /// The exhibit: 3 enrolled participants, one unenrolled creator, and the enrolled validator `3`
    /// is SILENT at the wave-end round. `supermajority_threshold(3) == 3`, so the enrolled
    /// committee is one short — and the unenrolled creator's wave-end block `ratifies` the leader
    /// on the merits (every enrolled participant has an approving round-2 block in its causal
    /// past), so before the ratifier gate it made the count up to three and ANCHORED THE WAVE.
    ///
    /// This is not an attacker-only shape. `finality.rs::enroll_pq` is INSERT-ONLY while
    /// `constitution.current.participants` shrinks on a passed membership proposal, so a
    /// ROTATED-OUT validator keeps producing exactly these blocks; and the restart restore
    /// (`finality.rs::from_checkpoint`, authenticating since 2026-08-08) reloads the persisted
    /// DAG with no roster check.
    ///
    /// BOTH POLES, because a rule that anchors nothing is not a fix:
    ///   * the Sybil cannot substitute for the silent validator — `tau` finalizes NOTHING; and
    ///   * put validator `3` back at the wave end, change nothing else, and the committee anchors
    ///     again, finalizing all NINE enrolled blocks.
    /// The Lean twin is `BlocklaceFinality.traceSybilRatify` (which IS `traceUnenrolled` minus that
    /// one block) and its `#guard` red/green pair on `isSuperRatifiedPreEnrollment`/
    /// `isSuperRatified`.
    #[test]
    fn test_unenrolled_ratifier_cannot_substitute_for_a_silent_participant() {
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        let unenrolled = make_key(9);
        assert!(
            !participants.contains(&unenrolled),
            "the unenrolled creator must not be enrolled — else this test has no adversary"
        );
        let threshold = supermajority_threshold(participants.len());
        assert_eq!(
            threshold, 3,
            "n=3 tolerates f=0: the committee is all three"
        );

        // Rounds 1-2 fully connected over all four creators; at the WAVE END (round 3) the enrolled
        // validator 3 is silent and the unenrolled creator is present.
        let (bl, by_round) = build_lace_by_round(&[
            vec![make_key(1), make_key(2), make_key(3), unenrolled],
            vec![make_key(1), make_key(2), make_key(3), unenrolled],
            vec![make_key(1), make_key(2), unenrolled],
        ]);
        let leader = wave0_leader_block(&bl, &by_round, participants[0]);

        let (all_ratifiers, enrolled_ratifiers) =
            wave_end_ratifier_creators(&bl, &participants, &leader, 3);

        // ANTI-VACUITY — the unenrolled creator really is a wave-end ratifier on the merits. If it
        // were not, "the Sybil does not count" would be true for a reason that has nothing to do
        // with enrollment.
        assert!(
            all_ratifiers.contains(&unenrolled),
            "the unenrolled creator must RATIFY the leader from a wave-end block — else there is \
             no ratifier to refuse and every assertion below is vacuous"
        );

        // THE WOUND, EXECUTED. Counting wave-end ratifiers WITHOUT the enrollment gate makes the
        // supermajority; counting only ENROLLED ones does not. The gap is exactly the Sybil.
        assert!(
            all_ratifiers.len() >= threshold,
            "the un-gated ratifier count must reach the supermajority ({} of {threshold}) — this \
             is the pre-B6 rule anchoring the wave",
            all_ratifiers.len()
        );
        assert!(
            enrolled_ratifiers.len() < threshold,
            "the ENROLLED committee must be SHORT at the wave end ({} of {threshold}) — otherwise \
             the wave would anchor honestly and the refusal below would prove nothing",
            enrolled_ratifiers.len()
        );

        // POLE 1 — THE REFUSAL. The rule declines the wave: a non-participant cannot make quorum.
        let result = tau(&bl, &participants);
        assert!(
            result.is_empty(),
            "tau ANCHORED a wave whose enrolled ratifiers were {} of {threshold} — an UNENROLLED \
             creator made up the supermajority and finalized the honest committee's blocks for it \
             (Lean: BlocklaceFinality.traceSybilRatify #guard). Finalized {} blocks.",
            enrolled_ratifiers.len(),
            result.len()
        );

        // POLE 2 — THE HONEST COMMITTEE STILL FINALIZES. Same lace, validator 3 back at the wave
        // end, nothing else changed: all nine enrolled blocks finalize, in round-major order.
        // RE-ARMED AT SIX ROUNDS for CM Def. 6 — an anchor orders its own closure, so rounds 1-3
        // are ordered by wave 1's anchor at round 4. At three rounds this pole would assert only
        // that the anchor itself survives, which does not distinguish a working committee from a
        // stalled one.
        let full_round = vec![make_key(1), make_key(2), make_key(3), unenrolled];
        let (bl_full, _) = build_lace_by_round(&vec![full_round; 6]);
        let live = tau(&bl_full, &participants);
        assert_eq!(
            live.len(),
            10,
            "with the full enrolled committee at the wave end, all NINE enrolled blocks of rounds \
             1-3 must still finalize (plus wave 1's anchor) — a ratifier gate that stops \
             everything anchoring is not a fix"
        );
        for id in &live {
            assert!(
                participants.contains(&bl_full.get(id).unwrap().creator),
                "only enrolled creators may be finalized"
            );
        }
        let seqs: Vec<u64> = live
            .iter()
            .filter_map(|id| bl_full.get(id).map(|b| b.sequence))
            .collect();
        assert!(
            seqs.windows(2).all(|w| w[0] <= w[1]),
            "the surviving order is still round-major, matching the Lean model"
        );
    }

    /// **THE EXTREME OF THE SAME DEFECT — a wave anchored with ZERO enrolled ratifiers.**
    ///
    /// Rounds 1-2 are the honest 3-node lace. The ENTIRE wave-end round is three DISTINCT
    /// unenrolled creators, each acking all three honest round-2 blocks, so each `ratifies` the
    /// leader on the merits and not one of them is a participant. Before the gate the rule counted
    /// `{7, 8, 9}` = 3 ≥ 3 and anchored wave 0: the "supermajority of the committee" was entirely
    /// OUTSIDE the committee.
    ///
    /// Lean twin: `BlocklaceFinality.traceSybilOnly`, and this is the trace that makes
    /// `superRatified_exists_enrolled_ratifier` non-vacuous — its conclusion is unreachable here.
    #[test]
    fn test_wave_cannot_anchor_on_zero_enrolled_ratifiers() {
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        let outsiders = [make_key(7), make_key(8), make_key(9)];
        let threshold = supermajority_threshold(participants.len());

        let (bl, by_round) = build_lace_by_round(&[
            participants.clone(),
            participants.clone(),
            outsiders.to_vec(),
        ]);
        let leader = wave0_leader_block(&bl, &by_round, participants[0]);

        let (all_ratifiers, enrolled_ratifiers) =
            wave_end_ratifier_creators(&bl, &participants, &leader, 3);

        // ANTI-VACUITY — all three outsiders genuinely ratify, and none is enrolled.
        for o in &outsiders {
            assert!(
                all_ratifiers.contains(o),
                "every outsider must ratify the leader from a wave-end block — else the wound is \
                 not the one being exhibited"
            );
            assert!(!participants.contains(o));
        }

        // THE WOUND — a full supermajority of ratifiers, ZERO of them enrolled.
        assert!(
            all_ratifiers.len() >= threshold,
            "the un-gated count must reach the supermajority with only outsiders present"
        );
        assert!(
            enrolled_ratifiers.is_empty(),
            "no enrolled participant has a wave-end block here — that is the point"
        );

        // THE REFUSAL — the rule cannot anchor a wave no member of the committee ratified.
        let result = tau(&bl, &participants);
        assert!(
            result.is_empty(),
            "tau ANCHORED a wave super-ratified by THREE UNENROLLED creators with ZERO enrolled \
             ratifiers — finality was decided entirely outside the committee. Finalized {} blocks.",
            result.len()
        );

        // THE HONEST POLE, same shape: put the committee at the wave end and it anchors.
        // Six rounds, because CM Def. 6 orders rounds 1-3 at wave 1's anchor (see the τ docstring).
        let (bl_ok, _) = build_lace_by_round(&vec![participants.clone(); 6]);
        assert_eq!(
            tau(&bl_ok, &participants).len(),
            10,
            "the honest 3-node lace must still finalize all nine of its rounds 1-3 blocks, plus \
             wave 1's anchor"
        );
    }

    /// **THE SYBIL STANDING IN FOR THE TOLERATED FAULT, at n=4.** `supermajority_threshold(4) == 3`
    /// (f=1), so two enrolled validators at the wave end are one short. An unenrolled creator makes
    /// it three — restoring exactly the voting power the committee's own fault budget withholds.
    /// This is the case that matters operationally: at n=4 a single crashed validator plus one
    /// rotated-out identity is enough, and neither is an attack.
    #[test]
    fn test_unenrolled_ratifier_cannot_replace_the_fault_budget_at_n4() {
        let participants = vec![make_key(1), make_key(2), make_key(3), make_key(4)];
        let unenrolled = make_key(9);
        let threshold = supermajority_threshold(participants.len());
        assert_eq!(threshold, 3, "n=4, f=1: three of four");

        let mut all_creators = participants.clone();
        all_creators.push(unenrolled);
        // Wave end: validators 3 and 4 are silent; 1, 2 and the unenrolled creator are present.
        let (bl, by_round) = build_lace_by_round(&[
            all_creators.clone(),
            all_creators.clone(),
            vec![make_key(1), make_key(2), unenrolled],
        ]);
        let leader = wave0_leader_block(&bl, &by_round, participants[0]);

        let (all_ratifiers, enrolled_ratifiers) =
            wave_end_ratifier_creators(&bl, &participants, &leader, 3);
        assert!(
            all_ratifiers.contains(&unenrolled),
            "anti-vacuity: it ratifies"
        );
        assert!(
            all_ratifiers.len() >= threshold && enrolled_ratifiers.len() < threshold,
            "the un-gated count reaches {threshold} only because of the unenrolled creator \
             (all={}, enrolled={})",
            all_ratifiers.len(),
            enrolled_ratifiers.len()
        );

        assert!(
            tau(&bl, &participants).is_empty(),
            "tau anchored a wave at n=4 on {} enrolled ratifiers of {threshold} — an unenrolled \
             identity supplied the committee's fault budget back to it",
            enrolled_ratifiers.len()
        );

        // THE HONEST POLE — the full committee at the wave end finalizes all TWELVE enrolled
        // blocks of rounds 1-3, plus wave 1's anchor. Six rounds, because CM Def. 6 orders a
        // wave's blocks at the next anchor that observes them.
        let (bl_full, _) = build_lace_by_round(&vec![all_creators.clone(); 6]);
        let live = tau(&bl_full, &participants);
        assert_eq!(
            live.len(),
            13,
            "4 enrolled participants x rounds 1-3 must still finalize (plus wave 1's anchor) with \
             the unenrolled creator present throughout"
        );
        for id in &live {
            assert_ne!(
                bl_full.get(id).unwrap().creator,
                unenrolled,
                "no unenrolled creator's block may be finalized"
            );
        }
    }

    #[test]
    fn test_equivocating_block_excluded() {
        // 3 nodes. Participant 1 equivocates at round 1 (produces two blocks at same round).
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        let mut bl = Blocklace::new();

        // Round 1: participant 1 equivocates (two blocks with different content), others produce one each.
        let b1a = make_block(make_key(1), 0, vec![], vec![1]);
        let b1a_id = b1a.id();
        let b1b = make_block(make_key(1), 1, vec![], vec![2]); // different seq but same round (genesis)
        let b1b_id = b1b.id();
        let b2 = make_block(make_key(2), 0, vec![], vec![3]);
        let b2_id = b2.id();
        let b3 = make_block(make_key(3), 0, vec![], vec![4]);
        let b3_id = b3.id();

        bl.insert_unverified(b1a).unwrap();
        bl.insert_unverified(b1b).unwrap();
        bl.insert_unverified(b2).unwrap();
        bl.insert_unverified(b3).unwrap();

        // Round 2: all see both equivocating blocks.
        let preds_r2 = vec![b1a_id, b1b_id, b2_id, b3_id];
        let r2_1 = make_block(make_key(1), 2, preds_r2.clone(), vec![5]);
        let r2_2 = make_block(make_key(2), 1, preds_r2.clone(), vec![6]);
        let r2_3 = make_block(make_key(3), 1, preds_r2.clone(), vec![7]);
        let r2_1_id = r2_1.id();
        let r2_2_id = r2_2.id();
        let r2_3_id = r2_3.id();
        bl.insert_unverified(r2_1).unwrap();
        bl.insert_unverified(r2_2).unwrap();
        bl.insert_unverified(r2_3).unwrap();

        // Round 3.
        let preds_r3 = vec![r2_1_id, r2_2_id, r2_3_id];
        let r3_1 = make_block(make_key(1), 3, preds_r3.clone(), vec![8]);
        let r3_2 = make_block(make_key(2), 2, preds_r3.clone(), vec![9]);
        let r3_3 = make_block(make_key(3), 2, preds_r3.clone(), vec![10]);
        bl.insert_unverified(r3_1).unwrap();
        bl.insert_unverified(r3_2).unwrap();
        bl.insert_unverified(r3_3).unwrap();

        let result = tau(&bl, &participants);

        // Blocks from the equivocator (participant 1) should be excluded.
        for &block_id in &result {
            let block = bl.get(&block_id).unwrap();
            assert_ne!(
                block.creator,
                make_key(1),
                "equivocator's blocks should be excluded from tau"
            );
        }
    }

    /// Concurrent blocks INSIDE one segment are linearized by block ID.
    ///
    /// RE-ARMED for CM Def. 6, and the cohort moved deliberately. This used to read the tie-break
    /// off the three GENESIS blocks, which no longer exhibits it: wave 0's anchor is a segment of
    /// its own, so creator 1's genesis is emitted first regardless of its id and its two concurrent
    /// siblings land in the NEXT segment. A segment boundary is not a tie-break. The round-2 cohort
    /// is three concurrent blocks that all sit inside wave 1's single segment, which is where
    /// `xsort`'s min-block-id ready heap actually decides.
    #[test]
    fn test_concurrent_blocks_deterministic_tiebreaker() {
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        let (bl, blocks_by_round) = build_full_blocklace(&participants, 6);

        let result = tau(&bl, &participants);
        let result2 = tau(&bl, &participants);
        assert_eq!(result, result2, "tau must be deterministic");

        // The three round-2 blocks are concurrent AND in one segment. Verify they appear in ID
        // order, consecutively.
        let cohort_ids = &blocks_by_round[1];
        let mut cohort_positions: Vec<(usize, BlockId)> = cohort_ids
            .iter()
            .filter_map(|id| result.iter().position(|x| x == id).map(|pos| (pos, *id)))
            .collect();

        assert_eq!(
            cohort_positions.len(),
            3,
            "all three round-2 blocks must be ordered"
        );
        cohort_positions.sort_by_key(|(pos, _)| *pos);

        for window in cohort_positions.windows(2) {
            assert!(
                window[0].0 < window[1].0,
                "concurrent blocks should maintain consistent order"
            );
            assert!(
                window[0].1 < window[1].1,
                "concurrent blocks should be sorted by block ID"
            );
        }
    }

    /// Two waves produce a two-anchor chain, and the SECOND anchor's segment is its own closure
    /// minus the first anchor's — not the union of its ratifiers' pasts.
    ///
    /// RE-ARMED for CM Def. 6: this asserted 18 (3 nodes x 6 rounds), which was the coverage rule
    /// reaching down from the round-6 ratifiers. An anchor now orders only what IT observes, so
    /// rounds 5-6 wait for wave 2's anchor and the six-round lace finalizes 10. The nine-round
    /// extension below shows the third anchor picking rounds 4-6 up.
    #[test]
    fn test_multiple_waves() {
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        let (bl, _) = build_full_blocklace(&participants, 6);

        let config = OrderingConfig { wavelength: 3 };
        let result = tau_with_config(&bl, &participants, &config);

        // Chain [wave-0 anchor, wave-1 anchor]: 1 + (rounds 1-3 minus the wave-0 anchor, plus the
        // wave-1 anchor) = 1 + 9.
        assert_eq!(result.len(), 10, "got {} blocks, expected 10", result.len());

        // Three waves: chain [wave-0, wave-1, wave-2], the last segment adding rounds 4-6.
        let (bl9, _) = build_full_blocklace(&participants, 9);
        let result9 = tau_with_config(&bl9, &participants, &config);
        assert_eq!(
            result9.len(),
            19,
            "got {} blocks, expected 19 (1 + 9 + 9)",
            result9.len()
        );
    }

    #[test]
    fn test_missing_leader_wave_skipped() {
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        let mut bl = Blocklace::new();

        // Round 1: only participants 2 and 3 produce blocks.
        let b2 = make_block(make_key(2), 0, vec![], vec![1]);
        let b3 = make_block(make_key(3), 0, vec![], vec![2]);
        let b2_id = b2.id();
        let b3_id = b3.id();
        bl.insert_unverified(b2).unwrap();
        bl.insert_unverified(b3).unwrap();

        // Round 2.
        let preds = vec![b2_id, b3_id];
        let r2_2 = make_block(make_key(2), 1, preds.clone(), vec![3]);
        let r2_3 = make_block(make_key(3), 1, preds.clone(), vec![4]);
        let r2_2_id = r2_2.id();
        let r2_3_id = r2_3.id();
        bl.insert_unverified(r2_2).unwrap();
        bl.insert_unverified(r2_3).unwrap();

        // Round 3.
        let preds3 = vec![r2_2_id, r2_3_id];
        let r3_2 = make_block(make_key(2), 2, preds3.clone(), vec![5]);
        let r3_3 = make_block(make_key(3), 2, preds3.clone(), vec![6]);
        bl.insert_unverified(r3_2).unwrap();
        bl.insert_unverified(r3_3).unwrap();

        let result = tau(&bl, &participants);
        assert!(
            result.is_empty(),
            "no blocks should be finalized when leader is absent"
        );
    }

    /// **PREFIX MONOTONICITY — the property the CM Def. 6 re-authoring exists to buy.**
    ///
    /// STRENGTHENED, and re-armed at a depth where it can fail. The old shape grew a 3-round lace
    /// to 6 and asserted only that the earlier blocks SURVIVED in the same relative order; at three
    /// rounds the earlier order is a single block, so the `windows(2)` loop had nothing to check.
    /// It also never asserted the real property. Under the coverage rule the old order was not even
    /// a PREFIX of the new one — a wave-end ratifier arriving for an already-final wave pulled its
    /// own past into that wave's segment, splicing blocks into the MIDDLE. An anchor's segment is
    /// now a function of its own signed hash pointers, so growing the lace can only APPEND.
    #[test]
    fn test_monotonicity() {
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        let (mut bl, blocks_by_round) = build_full_blocklace(&participants, 6);

        let order_at_6 = tau(&bl, &participants);
        assert_eq!(
            order_at_6.len(),
            10,
            "two waves must finalize the anchor chain's ten blocks — else the prefix below is \
             trivially preserved"
        );

        // Extend to 9 rounds (wave 2 anchors).
        let mut prev_round_blocks = blocks_by_round.last().unwrap().clone();
        for round in 7..=9u64 {
            let mut current_round_blocks = Vec::new();
            for (i, &participant) in participants.iter().enumerate() {
                let seq = round - 1;
                let payload = vec![round as u8, i as u8];
                let block = make_block(participant, seq, prev_round_blocks.clone(), payload);
                let id = block.id();
                bl.insert_unverified(block).unwrap();
                current_round_blocks.push(id);
            }
            prev_round_blocks = current_round_blocks;
        }

        let order_at_9 = tau(&bl, &participants);
        assert!(
            order_at_9.len() > order_at_6.len(),
            "the grown lace must finalize strictly more — else 'prefix' is vacuous"
        );

        // THE PROPERTY: not "still present in the same relative order", but a literal PREFIX.
        assert_eq!(
            &order_at_9[..order_at_6.len()],
            &order_at_6[..],
            "the finalized order must GROW BY APPENDING: the shorter order is a prefix of the \
             longer one, with nothing spliced into the middle"
        );
    }

    #[test]
    fn test_seven_node_same_order_all_nodes() {
        let participants: Vec<[u8; 32]> = (1..=7u8).map(make_key).collect();
        // SIX rounds: CM Def. 6 orders rounds 1-3 at wave 1's anchor, so a 3-round lace would have
        // every node agreeing on a single block.
        let (bl, _) = build_full_blocklace(&participants, 6);

        let results: Vec<Vec<BlockId>> = (0..7).map(|_| tau(&bl, &participants)).collect();

        for i in 1..7 {
            assert_eq!(
                results[0], results[i],
                "all nodes must compute the same total order"
            );
        }

        assert!(
            !results[0].is_empty(),
            "7-node system should finalize blocks"
        );
        assert_eq!(
            results[0].len(),
            22,
            "7 nodes * rounds 1-3 = 21 blocks, plus wave 1's anchor"
        );
    }

    #[test]
    fn test_is_cordial() {
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        let (bl, blocks_by_round) = build_full_blocklace(&participants, 2);

        // Genesis blocks are trivially cordial.
        for &id in &blocks_by_round[0] {
            assert!(is_cordial(&bl, &id, &participants));
        }

        // Round 2 blocks reference all of round 1 (3/3 > 2/3), so they're cordial.
        for &id in &blocks_by_round[1] {
            assert!(is_cordial(&bl, &id, &participants));
        }
    }

    #[test]
    fn test_is_cordial_insufficient_predecessors() {
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        let mut bl = Blocklace::new();

        // Empty payload = heartbeat equivalent.
        let a1 = make_block(make_key(1), 0, vec![], vec![]);
        let a1_id = a1.id();
        let b1 = make_block(make_key(2), 0, vec![], vec![]);
        let c1 = make_block(make_key(3), 0, vec![], vec![]);

        bl.insert_unverified(a1).unwrap();
        bl.insert_unverified(b1).unwrap();
        bl.insert_unverified(c1).unwrap();

        // Lazy block only references one predecessor.
        let lazy = make_block(make_key(1), 1, vec![a1_id], vec![]);
        let lazy_id = lazy.id();
        bl.insert_unverified(lazy).unwrap();

        // 1/3 is not > 2/3, so not cordial.
        assert!(!is_cordial(&bl, &lazy_id, &participants));
    }

    #[test]
    fn test_finalized_turns_filters_empty_payloads() {
        // Blocks with empty payloads should not appear in finalized_turns.
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        let mut bl = Blocklace::new();

        // Round 1: mix of non-empty and empty payloads.
        let a1 = make_block(make_key(1), 0, vec![], vec![1, 2, 3]);
        let a1_id = a1.id();
        let b1 = make_block(make_key(2), 0, vec![], vec![]); // "heartbeat" (empty)
        let b1_id = b1.id();
        let c1 = make_block(make_key(3), 0, vec![], vec![4, 5]);
        let c1_id = c1.id();
        bl.insert_unverified(a1).unwrap();
        bl.insert_unverified(b1).unwrap();
        bl.insert_unverified(c1).unwrap();

        // Round 2.
        let preds2 = vec![a1_id, b1_id, c1_id];
        let a2 = make_block(make_key(1), 1, preds2.clone(), vec![6]);
        let a2_id = a2.id();
        let b2 = make_block(make_key(2), 1, preds2.clone(), vec![7]);
        let b2_id = b2.id();
        let c2 = make_block(make_key(3), 1, preds2.clone(), vec![8]);
        let c2_id = c2.id();
        bl.insert_unverified(a2).unwrap();
        bl.insert_unverified(b2).unwrap();
        bl.insert_unverified(c2).unwrap();

        // Round 3.
        let preds3 = vec![a2_id, b2_id, c2_id];
        let a3 = make_block(make_key(1), 2, preds3.clone(), vec![9]);
        let a3_id = a3.id();
        let b3 = make_block(make_key(2), 2, preds3.clone(), vec![10]);
        let b3_id = b3.id();
        let c3 = make_block(make_key(3), 2, preds3.clone(), vec![11]);
        let c3_id = c3.id();
        bl.insert_unverified(a3).unwrap();
        bl.insert_unverified(b3).unwrap();
        bl.insert_unverified(c3).unwrap();

        // Rounds 4-6, all payloads non-empty. Needed because CM Def. 6 orders a wave's blocks at
        // the NEXT anchor that observes them: at three rounds `tau` emits only the wave-0 anchor,
        // and a one-block order cannot exhibit the empty-payload filter at all.
        let mut prev = vec![a3_id, b3_id, c3_id];
        for round in 4..=6u64 {
            let mut this = Vec::new();
            for (i, &p) in participants.iter().enumerate() {
                let block = make_block(p, round - 1, prev.clone(), vec![round as u8, i as u8 + 1]);
                this.push(block.id());
                bl.insert_unverified(block).unwrap();
            }
            prev = this;
        }

        let turns = finalized_turns(&bl, &participants);

        // The empty payload block (b1) should not appear.
        for (id, _payload) in &turns {
            assert_ne!(
                id, &b1_id,
                "empty-payload block should not appear in finalized_turns"
            );
        }

        // All non-empty payloads should appear.
        assert!(
            turns.len() >= 8,
            "expected at least 8 turns, got {}",
            turns.len()
        );
    }

    // ─── Unified Blocklace (tau_unified / ReferenceGroup) Tests ──────────────

    /// Build a blocklace with EXTRA non-member blocks mixed in.
    /// Returns (blocklace, member_blocks_by_round, external_block_ids).
    fn build_mixed_blocklace(
        members: &[[u8; 32]],
        externals: &[[u8; 32]],
        num_rounds: u64,
    ) -> (Blocklace, Vec<Vec<BlockId>>, Vec<BlockId>) {
        let mut bl = Blocklace::new();
        let mut member_blocks_by_round: Vec<Vec<BlockId>> = Vec::new();
        let mut external_ids = Vec::new();

        for round in 1..=num_rounds {
            // Member blocks reference all member blocks from previous round.
            let preds: Vec<BlockId> = if round == 1 {
                vec![]
            } else {
                member_blocks_by_round[(round - 2) as usize].clone()
            };

            let mut round_blocks = Vec::new();
            for (i, &participant) in members.iter().enumerate() {
                let seq = (round - 1) as u64;
                let payload = vec![round as u8, i as u8];
                let block = make_block(participant, seq, preds.clone(), payload);
                let id = block.id();
                bl.insert_unverified(block).unwrap();
                round_blocks.push(id);
            }

            // External blocks also reference member blocks (they can see them).
            for (j, &ext) in externals.iter().enumerate() {
                let seq = (round - 1) as u64;
                let payload = vec![0xFF, round as u8, j as u8];
                let ext_block = make_block(ext, seq, preds.clone(), payload);
                let ext_id = ext_block.id();
                bl.insert_unverified(ext_block).unwrap();
                external_ids.push(ext_id);
            }

            member_blocks_by_round.push(round_blocks);
        }

        (bl, member_blocks_by_round, external_ids)
    }

    #[test]
    fn test_tau_unified_backward_compat_members_only() {
        // When the blocklace contains ONLY member blocks, tau_unified should
        // produce the same result as tau.
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        // Six rounds so the two implementations are compared on a full anchor CHAIN, not on the
        // single-block order a one-wave lace produces under CM Def. 6.
        let (bl, _) = build_full_blocklace(&participants, 6);

        let config = OrderingConfig::default();
        let group = ReferenceGroup::new(participants.clone(), 10);

        let result_tau = tau_with_config(&bl, &participants, &config);
        let result_unified = tau_unified(&bl, &group, &config);

        assert_eq!(
            result_tau, result_unified,
            "tau_unified should produce identical output to tau when blocklace has only member blocks"
        );
        assert!(!result_tau.is_empty(), "should finalize blocks");
    }

    #[test]
    fn test_tau_unified_ignores_non_member_blocks() {
        // External strands produce blocks, but tau_unified should not include them
        // in the output and they should not affect the ordering of member blocks.
        let members = vec![make_key(1), make_key(2), make_key(3)];
        let externals = vec![make_key(10), make_key(11)];
        // Six rounds: CM Def. 6 orders rounds 1-3 at wave 1's anchor.
        let (bl, _, external_ids) = build_mixed_blocklace(&members, &externals, 6);

        let config = OrderingConfig::default();
        let group = ReferenceGroup::new(members.clone(), 10);

        let result = tau_unified(&bl, &group, &config);

        // Output should not contain any external blocks.
        for ext_id in &external_ids {
            assert!(
                !result.contains(ext_id),
                "tau_unified output should not contain external blocks"
            );
        }

        // All output blocks should be from members.
        for &block_id in &result {
            let block = bl.get(&block_id).unwrap();
            assert!(
                members.contains(&block.creator),
                "tau_unified output should only contain member blocks, got creator {:?}",
                block.creator[0]
            );
        }

        // Should still finalize member blocks.
        assert_eq!(
            result.len(),
            10,
            "3 members * rounds 1-3 = 9 member blocks, plus wave 1's anchor"
        );
    }

    #[test]
    fn test_tau_unified_finality_with_external_blocks_present() {
        // Finality still works correctly even when external blocks are in the DAG.
        let members = vec![make_key(1), make_key(2), make_key(3)];
        let externals = vec![make_key(20), make_key(21), make_key(22)];
        let (bl, _, _) = build_mixed_blocklace(&members, &externals, 6);

        let config = OrderingConfig::default();
        let group = ReferenceGroup::new(members.clone(), 10);

        let result = tau_unified(&bl, &group, &config);

        // Two waves ⇒ a two-anchor chain: wave 0's anchor alone, then everything wave 1's anchor
        // observes (rounds 1-3) plus itself. Rounds 5-6 wait for wave 2 — CM Def. 6's latency.
        assert_eq!(
            result.len(),
            10,
            "3 members * rounds 1-3 = 9 member blocks, plus wave 1's anchor, got {}",
            result.len()
        );
    }

    #[test]
    fn test_compute_rounds_filtered_ignores_non_members() {
        // Non-member blocks should not get round assignments in filtered computation.
        let members = vec![make_key(1), make_key(2), make_key(3)];
        let externals = vec![make_key(10)];
        let (bl, _, external_ids) = build_mixed_blocklace(&members, &externals, 3);

        let group = ReferenceGroup::new(members, 10);
        let (rounds, max_round) = compute_rounds_filtered(&bl, &group);

        // External blocks should not appear in the rounds map.
        for ext_id in &external_ids {
            assert!(
                !rounds.contains_key(ext_id),
                "external blocks should not have round assignments in filtered rounds"
            );
        }

        // Member blocks should all have rounds assigned.
        // 3 members * 3 rounds = 9 blocks.
        assert_eq!(
            rounds.len(),
            9,
            "9 member blocks should have round assignments"
        );
        assert_eq!(max_round, 3, "max round should be 3");
    }

    #[test]
    fn test_reference_group_from_constitution() {
        // ReferenceGroup::from_constitution should produce identical behavior
        // to using the constitution's participants directly.
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        let constitution = crate::constitution::Constitution::new(participants.clone(), 10);

        let group = ReferenceGroup::from_constitution(&constitution);

        assert_eq!(group.participants, constitution.participants);
        assert_eq!(group.threshold, constitution.threshold);
        assert_eq!(group.timeout_waves, constitution.timeout_waves);
        assert_eq!(group.routes_commitment, constitution.routes_commitment);

        // Build a blocklace and verify identical ordering. Six rounds so the comparison runs over
        // a full anchor chain rather than the single block a one-wave lace orders.
        let (bl, _) = build_full_blocklace(&constitution.participants, 6);
        let config = OrderingConfig::default();

        let result_constitution = tau_with_constitution(&bl, &constitution);
        let result_unified = tau_unified(&bl, &group, &config);

        assert_eq!(
            result_constitution, result_unified,
            "ReferenceGroup from Constitution should produce same ordering"
        );
    }

    #[test]
    fn test_multiple_reference_groups_same_blocklace() {
        // Two different reference groups operating on the same blocklace
        // should produce different orderings based on their member sets.
        let all_members = vec![
            make_key(1),
            make_key(2),
            make_key(3),
            make_key(4),
            make_key(5),
            make_key(6),
        ];
        // Six rounds: CM Def. 6 orders each group's rounds 1-3 at its own wave-1 anchor.
        let (bl, _) = build_full_blocklace(&all_members, 6);

        let config = OrderingConfig::default();

        // Group A: participants 1, 2, 3
        let group_a = ReferenceGroup::new(vec![make_key(1), make_key(2), make_key(3)], 10);
        // Group B: participants 4, 5, 6
        let group_b = ReferenceGroup::new(vec![make_key(4), make_key(5), make_key(6)], 10);

        let result_a = tau_unified(&bl, &group_a, &config);
        let result_b = tau_unified(&bl, &group_b, &config);

        // Both should produce finalized output.
        assert_eq!(result_a.len(), 10, "group A should finalize 10 blocks");
        assert_eq!(result_b.len(), 10, "group B should finalize 10 blocks");

        // The outputs should be completely disjoint (different members).
        let set_a: HashSet<BlockId> = result_a.iter().copied().collect();
        let set_b: HashSet<BlockId> = result_b.iter().copied().collect();
        let intersection: HashSet<&BlockId> = set_a.intersection(&set_b).collect();
        assert!(
            intersection.is_empty(),
            "two reference groups with disjoint members should produce disjoint orderings"
        );

        // Verify each output only has blocks from its own members.
        for &block_id in &result_a {
            let block = bl.get(&block_id).unwrap();
            assert!(
                group_a.is_member(&block.creator),
                "group A output should only have group A members"
            );
        }
        for &block_id in &result_b {
            let block = bl.get(&block_id).unwrap();
            assert!(
                group_b.is_member(&block.creator),
                "group B output should only have group B members"
            );
        }
    }

    #[test]
    fn test_tau_unified_external_blocks_dont_inflate_rounds() {
        // Verify that external blocks referencing deep chains don't inflate
        // member round numbers. Member rounds should be computed purely from
        // member-to-member references.
        let members = vec![make_key(1), make_key(2), make_key(3)];
        let mut bl = Blocklace::new();

        // First, create a deep external chain (10 blocks deep).
        let ext_key = make_key(99);
        let mut ext_prev = vec![];
        let mut ext_tip = [0u8; 32];
        for seq in 0..10u64 {
            let ext_block = make_block(ext_key, seq, ext_prev.clone(), vec![0xEE, seq as u8]);
            ext_tip = ext_block.id();
            bl.insert_unverified(ext_block).unwrap();
            ext_prev = vec![ext_tip];
        }

        // Now build the member blocklace (3 rounds).
        // Round 1: genesis blocks (no predecessors -- DO NOT reference external chain).
        let mut member_blocks_by_round: Vec<Vec<BlockId>> = Vec::new();
        let mut round_blocks = Vec::new();
        for (i, &participant) in members.iter().enumerate() {
            let block = make_block(participant, 0, vec![], vec![1, i as u8]);
            let id = block.id();
            bl.insert_unverified(block).unwrap();
            round_blocks.push(id);
        }
        member_blocks_by_round.push(round_blocks);

        // Round 2: reference previous round's member blocks + the deep external tip.
        let mut round_blocks = Vec::new();
        for (i, &participant) in members.iter().enumerate() {
            let mut preds = member_blocks_by_round[0].clone();
            preds.push(ext_tip); // Reference external deep chain
            let block = make_block(participant, 1, preds, vec![2, i as u8]);
            let id = block.id();
            bl.insert_unverified(block).unwrap();
            round_blocks.push(id);
        }
        member_blocks_by_round.push(round_blocks);

        // Round 3: reference previous round.
        let mut round_blocks = Vec::new();
        for (i, &participant) in members.iter().enumerate() {
            let preds = member_blocks_by_round[1].clone();
            let block = make_block(participant, 2, preds, vec![3, i as u8]);
            let id = block.id();
            bl.insert_unverified(block).unwrap();
            round_blocks.push(id);
        }
        member_blocks_by_round.push(round_blocks);

        // Rounds 4-6: needed because CM Def. 6 orders rounds 1-3 at wave 1's anchor. The external
        // chain is still referenced only from round 2, which is what the depth assertions read.
        for round in 4..=6u64 {
            let preds = member_blocks_by_round[(round - 2) as usize].clone();
            let mut round_blocks = Vec::new();
            for (i, &participant) in members.iter().enumerate() {
                let block = make_block(
                    participant,
                    round - 1,
                    preds.clone(),
                    vec![round as u8, i as u8],
                );
                let id = block.id();
                bl.insert_unverified(block).unwrap();
                round_blocks.push(id);
            }
            member_blocks_by_round.push(round_blocks);
        }

        // Verify filtered rounds are not inflated by the external chain.
        let group = ReferenceGroup::new(members.clone(), 10);
        let (rounds, max_round) = compute_rounds_filtered(&bl, &group);

        assert_eq!(
            max_round, 6,
            "max round should be 6 (not inflated by the 10-deep external chain)"
        );

        // Round 1 members should be at round 1.
        for &id in &member_blocks_by_round[0] {
            assert_eq!(rounds[&id], 1, "genesis member blocks should be at round 1");
        }
        // Round 2 members should be at round 2 (not 11+ from external chain).
        for &id in &member_blocks_by_round[1] {
            assert_eq!(
                rounds[&id], 2,
                "round 2 member blocks should be at round 2, not inflated by external chain"
            );
        }
        // Round 3 members should be at round 3.
        for &id in &member_blocks_by_round[2] {
            assert_eq!(rounds[&id], 3, "round 3 member blocks should be at round 3");
        }

        // tau_unified should still finalize correctly.
        let config = OrderingConfig::default();
        let result = tau_unified(&bl, &group, &config);
        assert_eq!(
            result.len(),
            10,
            "should finalize all 9 member blocks of rounds 1-3, plus wave 1's anchor"
        );

        // External blocks should not appear.
        for &block_id in &result {
            let block = bl.get(&block_id).unwrap();
            assert_ne!(
                block.creator, ext_key,
                "external blocks should not be in output"
            );
        }
    }

    #[test]
    fn test_constitution_manager_as_reference_group() {
        // Test the bridge method on ConstitutionManager.
        let participants = vec![make_key(1), make_key(2), make_key(3), make_key(4)];
        let mgr =
            crate::constitution::ConstitutionManager::from_participants(participants.clone(), 10);

        let group = mgr.as_reference_group();
        assert_eq!(group.member_count(), 4);
        assert_eq!(group.threshold, mgr.threshold());
        assert_eq!(group.timeout_waves, mgr.timeout_waves());

        // Use the group to finalize a blocklace.
        let (bl, _) = build_full_blocklace(&participants, 3);
        let config = OrderingConfig::default();
        let result = group.finalize(&bl, &config);
        assert!(
            !result.is_empty(),
            "should produce finalized output via reference group"
        );
    }
}
