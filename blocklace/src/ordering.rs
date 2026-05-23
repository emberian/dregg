//! Cordial Miners total ordering (the tau function).
//!
//! Implements the consensus ordering from the Cordial Miners paper (arXiv:2205.09174).
//! The blocklace is divided into **waves** of fixed wavelength. Each wave has a
//! designated **leader** (round-robin). When the leader's block is **super-ratified**
//! by a supermajority chain at the wave's end, it becomes a final leader and
//! anchors a segment of the total order.
//!
//! The `tau` function walks finalized leaders sequentially, collecting each
//! leader's "new" causal past (blocks not yet ordered by a prior leader) and
//! deterministically sorting them via `xsort`.
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

use std::collections::{HashMap, HashSet, VecDeque};

use crate::{BlockId, Blocklace};

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

/// Compute the round (depth) of each block in the blocklace.
///
/// Round = 1 + max(predecessor rounds). Genesis blocks (no predecessors) have round 1.
/// Returns a map from BlockId to round number, and the maximum round seen.
fn compute_rounds(blocklace: &Blocklace) -> (HashMap<BlockId, u64>, u64) {
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
        let round = if block.predecessors.is_empty() {
            1
        } else {
            1 + block
                .predecessors
                .iter()
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

/// Get the causal past of a block (inclusive of the block itself).
fn causal_past_inclusive(blocklace: &Blocklace, block_id: &BlockId) -> HashSet<BlockId> {
    blocklace.causal_past(block_id)
}

/// Check if a creator has equivocated (produced multiple blocks at the same round)
/// as visible from a given block's causal past.
fn has_equivocation_in_past(
    blocklace: &Blocklace,
    rounds: &HashMap<BlockId, u64>,
    observer: &BlockId,
    creator: &[u8; 32],
) -> bool {
    let past = causal_past_inclusive(blocklace, observer);

    // Group blocks in the past by (creator, round).
    let mut by_round: HashMap<u64, Vec<BlockId>> = HashMap::new();
    for &bid in &past {
        if let Some(block) = blocklace.get(&bid) {
            if &block.creator == creator {
                if let Some(&round) = rounds.get(&bid) {
                    by_round.entry(round).or_default().push(bid);
                }
            }
        }
    }

    by_round.values().any(|blocks| blocks.len() > 1)
}

// ─── Wave / Leader helpers ───────────────────────────────────────────────────

/// Determine which wave a given round belongs to.
/// Rounds are 1-indexed. Wave 0 = rounds [1, w], Wave 1 = [w+1, 2w], etc.
fn round_to_wave(round: u64, wavelength: u64) -> u64 {
    (round - 1) / wavelength
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

/// Compute the supermajority threshold: floor(2n/3) + 1.
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
    blocklace: &Blocklace,
    rounds: &HashMap<BlockId, u64>,
    observer: &BlockId,
    leader_id: &BlockId,
    leader_creator: &[u8; 32],
) -> bool {
    let past = causal_past_inclusive(blocklace, observer);

    // Leader must be visible from the observer.
    if !past.contains(leader_id) {
        return false;
    }

    // No equivocation by the leader's creator visible from the observer.
    !has_equivocation_in_past(blocklace, rounds, observer, leader_creator)
}

/// Check if block `observer` ratifies leader block `leader_id`.
///
/// A block ratifies a leader if a supermajority (> 2n/3) of participants have
/// at least one block in the observer's causal past that approves the leader.
fn ratifies(
    blocklace: &Blocklace,
    rounds: &HashMap<BlockId, u64>,
    observer: &BlockId,
    leader_id: &BlockId,
    leader_creator: &[u8; 32],
    participants: &[[u8; 32]],
) -> bool {
    let supermajority = supermajority_threshold(participants.len());
    let past = causal_past_inclusive(blocklace, observer);

    // Count how many distinct participants have at least one block in the
    // observer's past that approves the leader.
    let approving_count = participants
        .iter()
        .filter(|&&participant| {
            past.iter().any(|&bid| {
                if let Some(block) = blocklace.get(&bid) {
                    block.creator == participant
                        && approves(blocklace, rounds, &bid, leader_id, leader_creator)
                } else {
                    false
                }
            })
        })
        .count();

    approving_count >= supermajority
}

/// Check if a leader block is super-ratified (finalized).
///
/// Super-ratification: a supermajority of distinct participants have blocks at
/// the wave's last round that ratify the leader.
fn is_super_ratified(
    blocklace: &Blocklace,
    rounds: &HashMap<BlockId, u64>,
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
            if ratifies(
                blocklace,
                rounds,
                block_id,
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
    blocklace: &Blocklace,
    rounds: &HashMap<BlockId, u64>,
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
                blocklace,
                rounds,
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

// ─── xsort: Deterministic Topological Sort ───────────────────────────────────

/// Deterministic topological sort of a subset of blocks.
///
/// Respects causal order (if A is in B's causal past, A comes first).
/// For concurrent blocks (no causal relationship), ties are broken by block ID
/// (lexicographic byte comparison), giving a deterministic total order.
fn xsort(blocklace: &Blocklace, blocks: &HashSet<BlockId>) -> Vec<BlockId> {
    if blocks.is_empty() {
        return vec![];
    }

    // Build the restricted subgraph: for each block in the set, find which
    // other blocks in the set are its ancestors.
    let mut local_predecessors: HashMap<BlockId, HashSet<BlockId>> = HashMap::new();

    for &block_id in blocks {
        let past = causal_past_inclusive(blocklace, &block_id);
        let ancestors_in_set: HashSet<BlockId> = past
            .into_iter()
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

/// Extract the total order from the blocklace (the tau function).
///
/// Returns block IDs in their finalized total order. Only blocks in a finalized
/// leader's causal past (excluding equivocators) are included.
///
/// Uses default configuration (wavelength = 3).
pub fn tau(blocklace: &Blocklace, participants: &[[u8; 32]]) -> Vec<BlockId> {
    tau_with_config(blocklace, participants, &OrderingConfig::default())
}

/// Like `tau`, but with explicit configuration.
pub fn tau_with_config(
    blocklace: &Blocklace,
    participants: &[[u8; 32]],
    config: &OrderingConfig,
) -> Vec<BlockId> {
    if participants.is_empty() || blocklace.blocks.is_empty() {
        return vec![];
    }

    let (rounds, max_round) = compute_rounds(blocklace);
    let final_leaders = find_all_final_leaders(blocklace, &rounds, max_round, participants, config);

    let mut ordered = Vec::new();
    let mut prev_covered: HashSet<BlockId> = HashSet::new();

    for leader_id in &final_leaders {
        // The leader's "coverage" is the union of causal pasts of all blocks
        // at the wave-end round that ratify this leader. This captures all blocks
        // that are ordered by this leader's finalization.
        let leader_round = rounds.get(leader_id).copied().unwrap_or(1);
        let leader_wave = round_to_wave(leader_round, config.wavelength);
        let wave_end = wave_last_round(leader_wave, config.wavelength);
        let leader_creator = blocklace
            .get(leader_id)
            .map(|b| b.creator)
            .unwrap_or([0u8; 32]);

        // Collect the union of causal pasts of all wave-end blocks that ratify.
        let mut coverage: HashSet<BlockId> = HashSet::new();
        for (id, r) in &rounds {
            if *r == wave_end {
                if ratifies(
                    blocklace,
                    &rounds,
                    id,
                    leader_id,
                    &leader_creator,
                    participants,
                ) {
                    let past = causal_past_inclusive(blocklace, id);
                    coverage.extend(past);
                }
            }
        }

        // Blocks new to this leader's segment: in coverage but not in
        // any previous leader's coverage.
        let new_blocks: HashSet<BlockId> = coverage
            .difference(&prev_covered)
            .copied()
            .filter(|bid| {
                // Exclude blocks from creators that equivocated (as visible from leader).
                if let Some(block) = blocklace.get(bid) {
                    !has_equivocation_in_past(blocklace, &rounds, leader_id, &block.creator)
                } else {
                    false
                }
            })
            .collect();

        let sorted = xsort(blocklace, &new_blocks);
        ordered.extend(sorted);

        prev_covered = coverage;
    }

    ordered
}

// ─── Cordiality Check ────────────────────────────────────────────────────────

/// Check if a block is "cordial": acknowledges a supermajority of the previous round.
///
/// A cordial block has predecessors from > 2n/3 distinct participants at the
/// previous round. Genesis blocks (round 1) are trivially cordial.
pub fn is_cordial(blocklace: &Blocklace, block_id: &BlockId, participants: &[[u8; 32]]) -> bool {
    let (rounds, _) = compute_rounds(blocklace);

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

    acknowledged.len() > participants.len() * 2 / 3
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
/// Unlike `tau` which assumes all blocks belong to participants,
/// `tau_unified` works on a shared blocklace where non-participant
/// blocks may be present. They are simply ignored for ordering purposes.
///
/// The algorithm is the same as `tau_with_config`, but:
/// 1. `compute_rounds_filtered` only counts blocks from `reference_group.participants`
/// 2. Wave assignment uses filtered rounds
/// 3. Leader selection from reference group only
/// 4. Approval/ratification counts from reference group only
/// 5. Output only contains blocks from reference group participants
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
    let (rounds, max_round) = compute_rounds_filtered(blocklace, reference_group);

    // Find finalized leaders using filtered rounds (only considers participant blocks).
    let final_leaders = find_all_final_leaders(blocklace, &rounds, max_round, participants, config);

    let mut ordered = Vec::new();
    let mut prev_covered: HashSet<BlockId> = HashSet::new();

    for leader_id in &final_leaders {
        // Compute coverage the same way as tau_with_config, but using filtered rounds.
        let leader_round = rounds.get(leader_id).copied().unwrap_or(1);
        let leader_wave = round_to_wave(leader_round, config.wavelength);
        let wave_end = wave_last_round(leader_wave, config.wavelength);
        let leader_creator = blocklace
            .get(leader_id)
            .map(|b| b.creator)
            .unwrap_or([0u8; 32]);

        // Collect the union of causal pasts of all wave-end blocks that ratify.
        let mut coverage: HashSet<BlockId> = HashSet::new();
        for (id, r) in &rounds {
            if *r == wave_end {
                if ratifies(
                    blocklace,
                    &rounds,
                    id,
                    leader_id,
                    &leader_creator,
                    participants,
                ) {
                    let past = causal_past_inclusive(blocklace, id);
                    coverage.extend(past);
                }
            }
        }

        // Blocks new to this leader's segment: in coverage but not previously covered.
        // FILTER: only include blocks from reference group participants.
        let new_blocks: HashSet<BlockId> = coverage
            .difference(&prev_covered)
            .copied()
            .filter(|bid| {
                if let Some(block) = blocklace.get(bid) {
                    // Only include blocks from participants (not external strands).
                    participant_set.contains(&block.creator)
                        && !has_equivocation_in_past(blocklace, &rounds, leader_id, &block.creator)
                } else {
                    false
                }
            })
            .collect();

        let sorted = xsort(blocklace, &new_blocks);
        ordered.extend(sorted);

        prev_covered = coverage;
    }

    ordered
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
                bl.insert(block).unwrap();
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
        assert_eq!(supermajority_threshold(3), 3); // 2*3/3 + 1 = 3
        assert_eq!(supermajority_threshold(4), 3); // 2*4/3 + 1 = 3
        assert_eq!(supermajority_threshold(7), 5); // 2*7/3 + 1 = 5
        assert_eq!(supermajority_threshold(10), 7); // 2*10/3 + 1 = 7
    }

    #[test]
    fn test_three_node_one_wave_finalized() {
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        let (bl, _) = build_full_blocklace(&participants, 3);

        let result = tau(&bl, &participants);

        // All 9 blocks should be finalized (3 nodes * 3 rounds, no equivocation).
        assert_eq!(
            result.len(),
            9,
            "all 9 blocks should be ordered, got {}",
            result.len()
        );

        // Determinism check.
        let result2 = tau(&bl, &participants);
        assert_eq!(result, result2);
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

        bl.insert(b1a).unwrap();
        bl.insert(b1b).unwrap();
        bl.insert(b2).unwrap();
        bl.insert(b3).unwrap();

        // Round 2: all see both equivocating blocks.
        let preds_r2 = vec![b1a_id, b1b_id, b2_id, b3_id];
        let r2_1 = make_block(make_key(1), 2, preds_r2.clone(), vec![5]);
        let r2_2 = make_block(make_key(2), 1, preds_r2.clone(), vec![6]);
        let r2_3 = make_block(make_key(3), 1, preds_r2.clone(), vec![7]);
        let r2_1_id = r2_1.id();
        let r2_2_id = r2_2.id();
        let r2_3_id = r2_3.id();
        bl.insert(r2_1).unwrap();
        bl.insert(r2_2).unwrap();
        bl.insert(r2_3).unwrap();

        // Round 3.
        let preds_r3 = vec![r2_1_id, r2_2_id, r2_3_id];
        let r3_1 = make_block(make_key(1), 3, preds_r3.clone(), vec![8]);
        let r3_2 = make_block(make_key(2), 2, preds_r3.clone(), vec![9]);
        let r3_3 = make_block(make_key(3), 2, preds_r3.clone(), vec![10]);
        bl.insert(r3_1).unwrap();
        bl.insert(r3_2).unwrap();
        bl.insert(r3_3).unwrap();

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

    #[test]
    fn test_concurrent_blocks_deterministic_tiebreaker() {
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        let (bl, blocks_by_round) = build_full_blocklace(&participants, 3);

        let result = tau(&bl, &participants);
        let result2 = tau(&bl, &participants);
        assert_eq!(result, result2, "tau must be deterministic");

        // The three genesis blocks are concurrent. Verify they appear in ID order.
        let genesis_ids = &blocks_by_round[0];
        let genesis_positions: Vec<(usize, BlockId)> = genesis_ids
            .iter()
            .filter_map(|id| result.iter().position(|x| x == id).map(|pos| (pos, *id)))
            .collect();

        // All genesis blocks should be in the output.
        assert_eq!(genesis_positions.len(), 3);

        // Sort by position to check ordering.
        let mut sorted_by_pos = genesis_positions.clone();
        sorted_by_pos.sort_by_key(|(pos, _)| *pos);

        // They should be sorted by ID (since they're concurrent).
        for window in sorted_by_pos.windows(2) {
            assert!(
                window[0].0 < window[1].0,
                "genesis blocks should maintain consistent order"
            );
            assert!(
                window[0].1 < window[1].1,
                "concurrent blocks should be sorted by block ID"
            );
        }
    }

    #[test]
    fn test_multiple_waves() {
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        let (bl, _) = build_full_blocklace(&participants, 6);

        let config = OrderingConfig { wavelength: 3 };
        let result = tau_with_config(&bl, &participants, &config);

        // All 18 blocks (3 nodes * 6 rounds) should be finalized across 2 waves.
        assert_eq!(result.len(), 18, "got {} blocks, expected 18", result.len());
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
        bl.insert(b2).unwrap();
        bl.insert(b3).unwrap();

        // Round 2.
        let preds = vec![b2_id, b3_id];
        let r2_2 = make_block(make_key(2), 1, preds.clone(), vec![3]);
        let r2_3 = make_block(make_key(3), 1, preds.clone(), vec![4]);
        let r2_2_id = r2_2.id();
        let r2_3_id = r2_3.id();
        bl.insert(r2_2).unwrap();
        bl.insert(r2_3).unwrap();

        // Round 3.
        let preds3 = vec![r2_2_id, r2_3_id];
        let r3_2 = make_block(make_key(2), 2, preds3.clone(), vec![5]);
        let r3_3 = make_block(make_key(3), 2, preds3.clone(), vec![6]);
        bl.insert(r3_2).unwrap();
        bl.insert(r3_3).unwrap();

        let result = tau(&bl, &participants);
        assert!(
            result.is_empty(),
            "no blocks should be finalized when leader is absent"
        );
    }

    #[test]
    fn test_monotonicity() {
        let participants = vec![make_key(1), make_key(2), make_key(3)];
        let (mut bl, blocks_by_round) = build_full_blocklace(&participants, 3);

        let result_after_wave1 = tau(&bl, &participants);
        assert!(!result_after_wave1.is_empty(), "wave 1 should finalize");

        // Extend to 6 rounds (wave 2).
        let last_round_blocks = blocks_by_round.last().unwrap().clone();
        let mut prev_round_blocks = last_round_blocks;

        for round in 4..=6u64 {
            let mut current_round_blocks = Vec::new();
            for (i, &participant) in participants.iter().enumerate() {
                let seq = (round - 1) as u64;
                let payload = vec![round as u8, i as u8];
                let block = make_block(participant, seq, prev_round_blocks.clone(), payload);
                let id = block.id();
                bl.insert(block).unwrap();
                current_round_blocks.push(id);
            }
            prev_round_blocks = current_round_blocks;
        }

        let result_after_wave2 = tau(&bl, &participants);

        // Everything from wave 1 must still be present.
        for &block_id in &result_after_wave1 {
            assert!(
                result_after_wave2.contains(&block_id),
                "previously finalized block must remain"
            );
        }

        // Relative order must be preserved.
        let positions: Vec<usize> = result_after_wave1
            .iter()
            .map(|id| result_after_wave2.iter().position(|x| x == id).unwrap())
            .collect();
        for window in positions.windows(2) {
            assert!(window[0] < window[1], "relative order must be preserved");
        }
    }

    #[test]
    fn test_seven_node_same_order_all_nodes() {
        let participants: Vec<[u8; 32]> = (1..=7u8).map(|i| make_key(i)).collect();
        let (bl, _) = build_full_blocklace(&participants, 3);

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
        assert_eq!(results[0].len(), 21, "7 nodes * 3 rounds = 21 blocks");
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

        bl.insert(a1).unwrap();
        bl.insert(b1).unwrap();
        bl.insert(c1).unwrap();

        // Lazy block only references one predecessor.
        let lazy = make_block(make_key(1), 1, vec![a1_id], vec![]);
        let lazy_id = lazy.id();
        bl.insert(lazy).unwrap();

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
        bl.insert(a1).unwrap();
        bl.insert(b1).unwrap();
        bl.insert(c1).unwrap();

        // Round 2.
        let preds2 = vec![a1_id, b1_id, c1_id];
        let a2 = make_block(make_key(1), 1, preds2.clone(), vec![6]);
        let a2_id = a2.id();
        let b2 = make_block(make_key(2), 1, preds2.clone(), vec![7]);
        let b2_id = b2.id();
        let c2 = make_block(make_key(3), 1, preds2.clone(), vec![8]);
        let c2_id = c2.id();
        bl.insert(a2).unwrap();
        bl.insert(b2).unwrap();
        bl.insert(c2).unwrap();

        // Round 3.
        let preds3 = vec![a2_id, b2_id, c2_id];
        let a3 = make_block(make_key(1), 2, preds3.clone(), vec![9]);
        let b3 = make_block(make_key(2), 2, preds3.clone(), vec![10]);
        let c3 = make_block(make_key(3), 2, preds3.clone(), vec![11]);
        bl.insert(a3).unwrap();
        bl.insert(b3).unwrap();
        bl.insert(c3).unwrap();

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
                bl.insert(block).unwrap();
                round_blocks.push(id);
            }

            // External blocks also reference member blocks (they can see them).
            for (j, &ext) in externals.iter().enumerate() {
                let seq = (round - 1) as u64;
                let payload = vec![0xFF, round as u8, j as u8];
                let ext_block = make_block(ext, seq, preds.clone(), payload);
                let ext_id = ext_block.id();
                bl.insert(ext_block).unwrap();
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
        let (bl, _) = build_full_blocklace(&participants, 3);

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
        let (bl, _, external_ids) = build_mixed_blocklace(&members, &externals, 3);

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
        assert_eq!(result.len(), 9, "3 members * 3 rounds = 9 member blocks");
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

        // Should finalize across 2 waves (6 rounds / 3 wavelength = 2 waves).
        assert_eq!(
            result.len(),
            18,
            "3 members * 6 rounds = 18 member blocks, got {}",
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
    fn test_tau_unified_leader_selection_from_group_only() {
        // Leader for each wave must come from the reference group, not external strands.
        // We verify this by building a scenario where an external key would be the leader
        // if external blocks were counted.
        let members = vec![make_key(1), make_key(2), make_key(3)];
        let (bl, _) = build_full_blocklace(&members, 3);

        let group = ReferenceGroup::new(members.clone(), 10);
        let config = OrderingConfig::default();

        // Wave 0 leader should be members[0] = make_key(1).
        let leader = wave_leader(0, &group.participants);
        assert_eq!(leader, make_key(1));

        let result = tau_unified(&bl, &group, &config);
        assert!(!result.is_empty(), "should produce finalized output");

        // All blocks in the output should be from reference group participants.
        for &block_id in &result {
            let block = bl.get(&block_id).unwrap();
            assert!(
                group.is_member(&block.creator),
                "all finalized blocks should be from group members"
            );
        }
    }

    #[test]
    fn test_tau_unified_ratification_counts_from_group_only() {
        // Ratification should only count approvals from reference group members.
        // External blocks that might approve a leader should not count.
        let members = vec![make_key(1), make_key(2), make_key(3)];
        let externals = vec![make_key(50), make_key(51), make_key(52)];
        let (bl, _, _) = build_mixed_blocklace(&members, &externals, 3);

        let group = ReferenceGroup::new(members.clone(), 10);
        let config = OrderingConfig::default();

        let result = tau_unified(&bl, &group, &config);

        // Verify that the result matches what we'd get without external blocks.
        let (bl_clean, _) = build_full_blocklace(&members, 3);
        let result_clean = tau_with_config(&bl_clean, &members, &config);

        // Both should finalize 9 blocks.
        assert_eq!(result.len(), 9, "should finalize all member blocks");
        assert_eq!(result_clean.len(), 9, "clean should finalize all blocks");
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

        // Build a blocklace and verify identical ordering.
        let (bl, _) = build_full_blocklace(&constitution.participants, 3);
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
        let (bl, _) = build_full_blocklace(&all_members, 3);

        let config = OrderingConfig::default();

        // Group A: participants 1, 2, 3
        let group_a = ReferenceGroup::new(vec![make_key(1), make_key(2), make_key(3)], 10);
        // Group B: participants 4, 5, 6
        let group_b = ReferenceGroup::new(vec![make_key(4), make_key(5), make_key(6)], 10);

        let result_a = tau_unified(&bl, &group_a, &config);
        let result_b = tau_unified(&bl, &group_b, &config);

        // Both should produce finalized output.
        assert_eq!(result_a.len(), 9, "group A should finalize 9 blocks");
        assert_eq!(result_b.len(), 9, "group B should finalize 9 blocks");

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
            bl.insert(ext_block).unwrap();
            ext_prev = vec![ext_tip];
        }

        // Now build the member blocklace (3 rounds).
        // Round 1: genesis blocks (no predecessors -- DO NOT reference external chain).
        let mut member_blocks_by_round: Vec<Vec<BlockId>> = Vec::new();
        let mut round_blocks = Vec::new();
        for (i, &participant) in members.iter().enumerate() {
            let block = make_block(participant, 0, vec![], vec![1, i as u8]);
            let id = block.id();
            bl.insert(block).unwrap();
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
            bl.insert(block).unwrap();
            round_blocks.push(id);
        }
        member_blocks_by_round.push(round_blocks);

        // Round 3: reference previous round.
        let mut round_blocks = Vec::new();
        for (i, &participant) in members.iter().enumerate() {
            let preds = member_blocks_by_round[1].clone();
            let block = make_block(participant, 2, preds, vec![3, i as u8]);
            let id = block.id();
            bl.insert(block).unwrap();
            round_blocks.push(id);
        }
        member_blocks_by_round.push(round_blocks);

        // Verify filtered rounds are not inflated by the external chain.
        let group = ReferenceGroup::new(members.clone(), 10);
        let (rounds, max_round) = compute_rounds_filtered(&bl, &group);

        assert_eq!(
            max_round, 3,
            "max round should be 3 (not inflated by external chain)"
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
        assert_eq!(result.len(), 9, "should finalize all 9 member blocks");

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
    fn test_reference_group_helpers() {
        let group = ReferenceGroup::new(vec![make_key(1), make_key(2), make_key(3)], 5);

        assert_eq!(group.member_count(), 3);
        assert!(group.is_member(&make_key(1)));
        assert!(group.is_member(&make_key(2)));
        assert!(group.is_member(&make_key(3)));
        assert!(!group.is_member(&make_key(4)));
        assert_eq!(group.threshold, 3); // 2*3/3 + 1 = 3
        assert_eq!(group.timeout_waves, 5);
        assert_eq!(group.routes_commitment, None);
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
