//! Randomized governance fuzzer: tests constitution invariants under random proposals.
//!
//! Generates random governance proposals (join, leave, amend threshold, amend routes),
//! applies random voting patterns, and verifies constitution invariants after each round.

use pyana_teasting::assertions::assert_constitution_valid;

// =============================================================================
// Deterministic PRNG (xorshift64)
// =============================================================================

struct Rng {
    state: u64,
}

impl Rng {
    fn from_seed(seed: &str) -> Self {
        let hash = blake3::hash(seed.as_bytes());
        let bytes: [u8; 8] = hash.as_bytes()[..8].try_into().unwrap();
        let state = u64::from_le_bytes(bytes) | 1;
        Rng { state }
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.state = x;
        x
    }

    fn next_u32(&mut self) -> u32 {
        (self.next_u64() >> 16) as u32
    }

    fn gen_range(&mut self, lo: u64, hi: u64) -> u64 {
        if hi <= lo {
            return lo;
        }
        lo + self.next_u64() % (hi - lo)
    }

    fn gen_bytes(&mut self) -> [u8; 32] {
        let mut out = [0u8; 32];
        for chunk in out.chunks_exact_mut(8) {
            chunk.copy_from_slice(&self.next_u64().to_le_bytes());
        }
        out
    }

    fn gen_bool(&mut self, probability_percent: u32) -> bool {
        (self.next_u32() % 100) < probability_percent
    }
}

// =============================================================================
// Simulated Constitution
// =============================================================================

/// A simulated constitution for governance fuzz testing.
#[derive(Clone, Debug)]
struct SimConstitution {
    participants: Vec<[u8; 32]>,
    threshold: usize,
    version: u64,
    routes_commitment: Option<[u8; 32]>,
}

impl SimConstitution {
    fn new(initial_participants: Vec<[u8; 32]>, threshold: usize) -> Self {
        let mut participants = initial_participants;
        participants.sort();
        participants.dedup();
        SimConstitution {
            participants,
            threshold,
            version: 1,
            routes_commitment: None,
        }
    }

    fn verify_invariants(&self) {
        assert_constitution_valid(
            self.threshold,
            &self.participants,
            self.version,
            self.version,
        );
    }
}

// =============================================================================
// Governance Proposals
// =============================================================================

#[derive(Debug, Clone)]
enum Proposal {
    Join { new_participant: [u8; 32] },
    Leave { leaving_idx: usize },
    AmendThreshold { new_threshold: usize },
    AmendRoutes { new_commitment: [u8; 32] },
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum Vote {
    Approve,
    Reject,
    Abstain,
}

fn generate_random_proposal(rng: &mut Rng, constitution: &SimConstitution) -> Proposal {
    match rng.next_u32() % 4 {
        0 => Proposal::Join {
            new_participant: rng.gen_bytes(),
        },
        1 => {
            if constitution.participants.len() <= 1 {
                // Can't leave if only one participant.
                Proposal::AmendThreshold { new_threshold: 1 }
            } else {
                let idx = rng.gen_range(0, constitution.participants.len() as u64) as usize;
                Proposal::Leave { leaving_idx: idx }
            }
        }
        2 => {
            let max_threshold = constitution.participants.len();
            let new_threshold = rng.gen_range(1, max_threshold as u64 + 1) as usize;
            Proposal::AmendThreshold { new_threshold }
        }
        _ => Proposal::AmendRoutes {
            new_commitment: rng.gen_bytes(),
        },
    }
}

fn generate_votes(rng: &mut Rng, num_voters: usize) -> Vec<Vote> {
    (0..num_voters)
        .map(|_| match rng.next_u32() % 3 {
            0 => Vote::Approve,
            1 => Vote::Reject,
            _ => Vote::Abstain,
        })
        .collect()
}

fn count_approvals(votes: &[Vote]) -> usize {
    votes.iter().filter(|v| **v == Vote::Approve).count()
}

/// Apply a proposal if it passes the threshold vote.
/// Returns true if the proposal was applied.
fn try_apply_proposal(
    constitution: &mut SimConstitution,
    proposal: &Proposal,
    votes: &[Vote],
) -> bool {
    let approvals = count_approvals(votes);
    if approvals < constitution.threshold {
        return false; // Did not pass.
    }

    match proposal {
        Proposal::Join { new_participant } => {
            // Don't add duplicates.
            if constitution.participants.contains(new_participant) {
                return false;
            }
            constitution.participants.push(*new_participant);
            constitution.participants.sort();
            constitution.version += 1;
        }
        Proposal::Leave { leaving_idx } => {
            if *leaving_idx >= constitution.participants.len() {
                return false;
            }
            // Don't leave if it would make threshold impossible.
            if constitution.participants.len() - 1 < constitution.threshold {
                return false;
            }
            constitution.participants.remove(*leaving_idx);
            constitution.version += 1;
        }
        Proposal::AmendThreshold { new_threshold } => {
            if *new_threshold == 0 || *new_threshold > constitution.participants.len() {
                return false;
            }
            constitution.threshold = *new_threshold;
            constitution.version += 1;
        }
        Proposal::AmendRoutes { new_commitment } => {
            constitution.routes_commitment = Some(*new_commitment);
            constitution.version += 1;
        }
    }

    true
}

// =============================================================================
// Tests
// =============================================================================

/// Fuzz governance proposals with random voting. Verify constitution after each round.
#[test]
fn test_fuzz_governance_proposals_500_rounds() {
    let mut rng = Rng::from_seed("fuzz_governance_proposals_500");

    // Start with 4 participants, threshold 3.
    let initial_participants: Vec<[u8; 32]> = (0..4u8)
        .map(|i| {
            let mut b = [0u8; 32];
            b[0] = i;
            b
        })
        .collect();
    let mut constitution = SimConstitution::new(initial_participants, 3);
    constitution.verify_invariants();

    let mut applied_count = 0;

    for _ in 0..500 {
        let proposal = generate_random_proposal(&mut rng, &constitution);
        let votes = generate_votes(&mut rng, constitution.participants.len());

        if try_apply_proposal(&mut constitution, &proposal, &votes) {
            applied_count += 1;
            // Verify invariants after every successful proposal.
            constitution.verify_invariants();
        }
    }

    // Ensure we actually applied some proposals.
    assert!(
        applied_count > 10,
        "Too few proposals applied ({}); increase threshold approval probability",
        applied_count,
    );
}

/// Fuzz with high approval rate to ensure many proposals pass.
#[test]
fn test_fuzz_governance_high_approval_rate() {
    let mut rng = Rng::from_seed("fuzz_governance_high_approval");

    let initial_participants: Vec<[u8; 32]> = (0..5u8)
        .map(|i| {
            let mut b = [0u8; 32];
            b[0] = i + 10;
            b
        })
        .collect();
    let mut constitution = SimConstitution::new(initial_participants, 2);
    constitution.verify_invariants();

    let mut applied_count = 0;

    for _ in 0..300 {
        let proposal = generate_random_proposal(&mut rng, &constitution);
        // Bias votes towards approval (80% approve).
        let votes: Vec<Vote> = (0..constitution.participants.len())
            .map(|_| {
                if rng.gen_bool(80) {
                    Vote::Approve
                } else {
                    Vote::Reject
                }
            })
            .collect();

        if try_apply_proposal(&mut constitution, &proposal, &votes) {
            applied_count += 1;
            constitution.verify_invariants();
        }
    }

    assert!(
        applied_count > 50,
        "Expected many proposals to pass with 80% approval rate, got {}",
        applied_count
    );
}

/// Test partition detection: silencing >50% of nodes freezes membership.
#[test]
fn test_fuzz_partition_detection() {
    let mut rng = Rng::from_seed("fuzz_partition_detection");

    let initial_participants: Vec<[u8; 32]> = (0..7u8)
        .map(|i| {
            let mut b = [0u8; 32];
            b[0] = i + 20;
            b
        })
        .collect();
    // Threshold = 5 (majority of 7).
    let mut constitution = SimConstitution::new(initial_participants, 5);
    constitution.verify_invariants();

    // Simulate partition: silence 4 of 7 nodes (>50%).
    // Only 3 nodes can vote. Threshold is 5 -- no proposal should pass.
    let version_before = constitution.version;

    for _ in 0..100 {
        let proposal = generate_random_proposal(&mut rng, &constitution);
        // Only 3 nodes vote (all approve), others are silenced.
        let votes: Vec<Vote> = (0..constitution.participants.len())
            .map(|i| {
                if i < 3 {
                    Vote::Approve
                } else {
                    Vote::Abstain // silenced
                }
            })
            .collect();

        let applied = try_apply_proposal(&mut constitution, &proposal, &votes);
        assert!(
            !applied,
            "Proposal should NOT pass with only 3/7 approvals (threshold=5)"
        );
    }

    // Version should not have changed (membership frozen).
    assert_eq!(
        constitution.version, version_before,
        "Constitution version changed during partition -- membership should be frozen"
    );
}

/// Verify version increments exactly once per applied proposal.
#[test]
fn test_governance_version_increments_once_per_proposal() {
    let mut rng = Rng::from_seed("governance_version_increments");

    let initial_participants: Vec<[u8; 32]> = (0..3u8)
        .map(|i| {
            let mut b = [0u8; 32];
            b[0] = i + 30;
            b
        })
        .collect();
    let mut constitution = SimConstitution::new(initial_participants, 2);

    for _ in 0..200 {
        let version_before = constitution.version;
        let proposal = generate_random_proposal(&mut rng, &constitution);
        // All approve.
        let votes = vec![Vote::Approve; constitution.participants.len()];

        let applied = try_apply_proposal(&mut constitution, &proposal, &votes);

        if applied {
            assert_eq!(
                constitution.version,
                version_before + 1,
                "Version should increment by exactly 1 per applied proposal"
            );
            constitution.verify_invariants();
        } else {
            assert_eq!(
                constitution.version, version_before,
                "Version should not change when proposal is not applied"
            );
        }
    }
}

/// Threshold must always be >= 1 and <= participant count.
#[test]
fn test_governance_threshold_bounds() {
    let mut rng = Rng::from_seed("governance_threshold_bounds");

    let initial_participants: Vec<[u8; 32]> = (0..5u8)
        .map(|i| {
            let mut b = [0u8; 32];
            b[0] = i + 40;
            b
        })
        .collect();
    let mut constitution = SimConstitution::new(initial_participants, 3);

    for _ in 0..300 {
        let proposal = generate_random_proposal(&mut rng, &constitution);
        let votes = vec![Vote::Approve; constitution.participants.len()];
        try_apply_proposal(&mut constitution, &proposal, &votes);

        // After every mutation, threshold must be in valid range.
        assert!(
            constitution.threshold >= 1,
            "Threshold dropped below 1: {}",
            constitution.threshold,
        );
        assert!(
            constitution.threshold <= constitution.participants.len(),
            "Threshold {} exceeds participant count {}",
            constitution.threshold,
            constitution.participants.len(),
        );
    }
}
