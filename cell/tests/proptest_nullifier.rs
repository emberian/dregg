//! Property-based tests for nullifier uniqueness invariants.
//!
//! Property 3: After any random sequence of note create/spend operations:
//! - No nullifier appears twice in the nullifier set
//! - Every spent note has its nullifier in the set
//! - No unspent note has its nullifier in the set

use proptest::prelude::*;

use pyana_cell::note::Note;
use pyana_cell::nullifier_set::NullifierSet;

/// A note operation: either create a note or spend one.
#[derive(Clone, Debug)]
enum NoteOp {
    /// Create a note with the given seed parameters.
    Create { owner_seed: u8, amount: u64, randomness: [u8; 32] },
    /// Spend the note at the given index in our created-notes list.
    Spend { index: usize, spending_key: [u8; 32] },
}

/// Strategy for generating a random note operation.
fn arb_note_op(max_notes: usize) -> impl Strategy<Value = NoteOp> {
    prop_oneof![
        // Create: random owner, amount, randomness
        (any::<u8>(), 1u64..10_000u64, any::<[u8; 32]>()).prop_map(
            |(owner_seed, amount, randomness)| NoteOp::Create {
                owner_seed,
                amount,
                randomness,
            }
        ),
        // Spend: pick an index and a spending key
        (0..max_notes, any::<[u8; 32]>())
            .prop_map(|(index, spending_key)| NoteOp::Spend { index, spending_key }),
    ]
}

/// Strategy for generating a sequence of note operations.
fn arb_note_ops(n: usize) -> impl Strategy<Value = Vec<NoteOp>> {
    proptest::collection::vec(arb_note_op(20), 1..=n)
}

/// Tracked note state for verification.
#[derive(Clone)]
struct TrackedNote {
    note: Note,
    spending_key: [u8; 32],
    spent: bool,
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(200))]

    #[test]
    fn proptest_nullifier_uniqueness_holds(ops in arb_note_ops(50)) {
        let mut nullifier_set = NullifierSet::new();
        let mut created_notes: Vec<TrackedNote> = Vec::new();

        for op in &ops {
            match op {
                NoteOp::Create { owner_seed, amount, randomness } => {
                    let mut owner = [0u8; 32];
                    owner[0] = *owner_seed;
                    let fields = [1u64, *amount, 0, 0, 0, 0, 0, 0];
                    let note = Note::with_randomness(owner, fields, *randomness);
                    // Use a deterministic spending key derived from the owner
                    let mut spending_key = [0u8; 32];
                    spending_key[0] = owner_seed.wrapping_add(100);
                    spending_key[1] = 0xBB;
                    created_notes.push(TrackedNote {
                        note,
                        spending_key,
                        spent: false,
                    });
                }
                NoteOp::Spend { index, spending_key } => {
                    if created_notes.is_empty() {
                        continue;
                    }
                    let idx = *index % created_notes.len();
                    let tracked = &mut created_notes[idx];
                    if tracked.spent {
                        // Already spent; attempt should fail (double-spend).
                        let nullifier = tracked.note.nullifier(&tracked.spending_key);
                        let result = nullifier_set.insert(nullifier);
                        prop_assert!(result.is_err(),
                            "Double-spend should be rejected but was accepted");
                    } else {
                        // First spend; should succeed.
                        // Use the stored spending key (not the random one from the op,
                        // since the "real" owner uses their key).
                        let nullifier = tracked.note.nullifier(&tracked.spending_key);
                        let result = nullifier_set.insert(nullifier);
                        prop_assert!(result.is_ok(),
                            "First spend should succeed but was rejected: {:?}", result);
                        tracked.spent = true;

                        // Also try with the random spending key -- different nullifier, should also work
                        // unless it collides (astronomically unlikely).
                        let other_nullifier = tracked.note.nullifier(spending_key);
                        if other_nullifier != nullifier {
                            // This is a "different" nullifier, it should be insertable
                            // (it represents a different spending authority, not a double-spend).
                            // We don't insert it -- that would pollute the set for this test.
                        }
                    }
                }
            }
        }

        // INVARIANT 1: No nullifier appears twice in the nullifier set.
        // (Enforced by the insert logic above returning Err on duplicates.)
        // The set length should equal the number of unique spends.
        let spent_count = created_notes.iter().filter(|n| n.spent).count();
        prop_assert_eq!(nullifier_set.len(), spent_count,
            "Nullifier set size should equal number of spent notes");

        // INVARIANT 2: Every spent note has its nullifier in the set.
        for tracked in &created_notes {
            let nullifier = tracked.note.nullifier(&tracked.spending_key);
            if tracked.spent {
                prop_assert!(nullifier_set.contains(&nullifier),
                    "Spent note's nullifier should be in the set");
            } else {
                // INVARIANT 3: No unspent note has its nullifier in the set.
                prop_assert!(!nullifier_set.contains(&nullifier),
                    "Unspent note's nullifier should NOT be in the set");
            }
        }
    }

    /// Property: Different notes always produce different nullifiers (collision resistance).
    #[test]
    fn proptest_distinct_notes_produce_distinct_nullifiers(
        seeds in proptest::collection::vec(any::<(u8, [u8; 32], [u8; 32])>(), 2..20)
    ) {
        let mut nullifiers = std::collections::HashSet::new();
        for (owner_seed, randomness, spending_key) in &seeds {
            let mut owner = [0u8; 32];
            owner[0] = *owner_seed;
            let fields = [1u64, 100, 0, 0, 0, 0, 0, 0];
            let note = Note::with_randomness(owner, fields, *randomness);
            let nullifier = note.nullifier(spending_key);
            nullifiers.insert(nullifier.0);
        }
        // With distinct (owner, randomness, spending_key) tuples, we expect distinct nullifiers.
        // Note: owner_seed is only 1 byte so collisions in owner are possible, but
        // randomness is 32 bytes so the notes themselves will be distinct.
        // Actually: we can have identical notes if owner_seed AND randomness match.
        // So we just check: distinct notes => distinct nullifiers (no hash collision).
        // Since proptest may generate duplicate tuples, we compare note count vs nullifier count.
        let mut notes_set = std::collections::HashSet::new();
        for (owner_seed, randomness, spending_key) in &seeds {
            let mut owner = [0u8; 32];
            owner[0] = *owner_seed;
            let fields = [1u64, 100, 0, 0, 0, 0, 0, 0];
            let note = Note::with_randomness(owner, fields, *randomness);
            let commitment = note.commitment();
            // Use (commitment, spending_key) as the unique identifier.
            notes_set.insert((commitment.0, *spending_key));
        }
        // If all (note, key) pairs are distinct, all nullifiers must be distinct.
        // If some pairs collide, nullifiers for those will also collide (determinism).
        prop_assert_eq!(notes_set.len(), nullifiers.len(),
            "Distinct (note, key) pairs must produce distinct nullifiers");
    }
}
