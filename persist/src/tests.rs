//! Comprehensive tests for the persistent store.
//!
//! Tests cover: CRUD for each storage type, recovery after simulated restart,
//! concurrent access safety, edge cases, and integrity checking.

use crate::federation::{PublicKey, Signature, StoredAttestedRoot};
use crate::{PersistentStore, StoreError};

// The browser cannot link redb, so Starbridge carries a wasm-safe copy of the
// pure ledger-root function. Compile that copy in this native authority crate's
// test target and pin it byte-for-byte to the canonical implementation.
#[path = "../../starbridge-v2/src/persistence_wasm.rs"]
mod starbridge_wasm_persistence;

// =============================================================================
// Helpers
// =============================================================================

/// The per-turn value (v4) every finalization-quorum fixture in this module signs
/// alongside the ledger root. A stored root must CARRY it or its quorum does not
/// verify — that binding is the point of the v4 preimage.
const FIXTURE_STREAM_ROOT: [u8; 32] = [0x3D; 32];

fn new_store() -> PersistentStore {
    PersistentStore::open_in_memory().expect("failed to open in-memory store")
}

#[test]
fn config_batch_rollback_and_reopen_keep_related_keys_atomic() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("config-batch.redb");
    let store = PersistentStore::open(&path).unwrap();
    store.set_config("genesis-order", b"first").unwrap();
    store.set_config("first", b"original-cell").unwrap();

    // The first row has actually been inserted into the transaction when this
    // fault fires. Dropping that transaction must roll the row back as well.
    crate::FAIL_CONFIG_BATCH_AFTER.with(|fault| fault.set(Some(1)));
    let result =
        store.set_config_batch(&[("genesis-order", b"first,second"), ("second", b"new-cell")]);
    assert!(matches!(result, Err(StoreError::Database(message))
        if message.contains("after insert")));
    assert_eq!(
        store.get_config("genesis-order").unwrap(),
        Some(b"first".to_vec())
    );
    assert_eq!(store.get_config("second").unwrap(), None);
    drop(store);

    let store = PersistentStore::open(&path).unwrap();
    assert_eq!(
        store.get_config("genesis-order").unwrap(),
        Some(b"first".to_vec())
    );
    assert_eq!(store.get_config("second").unwrap(), None);
    store
        .set_config_batch(&[("genesis-order", b"first,second"), ("second", b"new-cell")])
        .unwrap();
    // Preserve the existing set_config overwrite contract on the same path.
    store.set_config("first", b"updated-cell").unwrap();
    drop(store);

    let reopened = PersistentStore::open(&path).unwrap();
    assert_eq!(
        reopened.get_config("genesis-order").unwrap(),
        Some(b"first,second".to_vec())
    );
    assert_eq!(
        reopened.get_config("first").unwrap(),
        Some(b"updated-cell".to_vec())
    );
    assert_eq!(
        reopened.get_config("second").unwrap(),
        Some(b"new-cell".to_vec())
    );
}

/// A fresh store is sealed to whatever `CANONICAL_STATE_SCHEMA_EPOCH` currently reads.
///
/// ⓘ This was called `..._epoch_11` until 2026-08-01, at which point the constant read **22**.
/// The assertion was always against the constant, so the number in the name was decoration that
/// had been wrong for nine epochs — renamed rather than re-pinned, because a name is a claim.
#[test]
fn fresh_store_is_sealed_to_the_canonical_state_epoch() {
    let store = new_store();
    let read = store.db.begin_read().unwrap();
    let metadata = read.open_table(crate::tables::METADATA).unwrap();
    assert_eq!(
        metadata
            .get(crate::tables::META_CANONICAL_STATE_SCHEMA_EPOCH)
            .unwrap()
            .map(|value| value.value()),
        Some(PersistentStore::CANONICAL_STATE_SCHEMA_EPOCH)
    );
}

/// The VK-REGEN log as text (compile-time: a missing log is a COMPILE error, not a skip).
const VK_REGEN_LOG: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../docs/VK-REGEN-LOG.md"
));

/// The last `epoch:N` an event row of `docs/VK-REGEN-LOG.md` records, with that row's timestamp.
///
/// PURE, and that is deliberate: it lets `schema_epoch_log_row_can_go_red` prove every refusal
/// on strings in memory, so this gate never needs a RED-PROOF SCAFFOLD in the shared tree — the
/// disarmed-guard class AGENTS.md documents (a lane broke `eval.rs` to prove a point, died
/// holding it, and misled three other lanes).
///
/// `Err` for every unreadable shape. Fail-closed is the whole design: a log with no parseable
/// epoch row is a FAILURE, because otherwise the first malformed row silently disables the
/// comparison — a class this repo has ~15 instances of.
fn last_logged_epoch(log: &str) -> Result<(u64, String), String> {
    let mut rows = 0usize;
    let mut last: Option<(u64, String)> = None;
    for line in log.lines() {
        let line = line.trim_end();
        // Event rows only: `| 2026-…Z | operator | … | epoch:N |`. Keyed on the full ISO
        // timestamp, not on a `| 20` prefix — the SCHEMA EPOCH LEDGER above the event table
        // has a row whose first cell is the bare number `20`, and a prefix test swallowed it.
        if !line.starts_with("| 20") || !line.ends_with('|') {
            continue;
        }
        let when = line.split('|').nth(1).unwrap_or("").trim().to_string();
        if when.len() != 20 || !when.ends_with('Z') || when.as_bytes()[10] != b'T' {
            continue;
        }
        rows += 1;
        let cell = line[..line.len() - 1]
            .rsplit('|')
            .next()
            .unwrap_or("")
            .trim();
        let Some(value) = cell.strip_prefix("epoch:") else {
            return Err(format!(
                "VK-REGEN-LOG row `{when}` ends in `{cell}`, which is not an `epoch:` cell. \
                 Unparseable is RED, never green — a log this cannot read is exactly how a gate \
                 gets switched off silently."
            ));
        };
        if value == "unchanged" || value == "unknown" {
            continue;
        }
        let Ok(n) = value.parse::<u64>() else {
            return Err(format!(
                "VK-REGEN-LOG row `{when}`: `epoch:{value}` is not a number, `unchanged` or \
                 `unknown`."
            ));
        };
        if let Some((prev, ref prev_when)) = last {
            if n < prev {
                return Err(format!(
                    "VK-REGEN-LOG row `{when}` records epoch {n} after `{prev_when}` recorded \
                     {prev}. The epoch only ratchets up."
                ));
            }
        }
        last = Some((n, when));
    }

    // FLOOR — a reader that harvests nothing must not read as clean.
    if rows < 40 {
        return Err(format!(
            "VK-REGEN-LOG: harvested only {rows} event rows; this reader is broken, not the log."
        ));
    }
    last.ok_or_else(|| {
        "VK-REGEN-LOG carries no `epoch:N` row, so there is nothing to compare the constant \
         against. That is a failure: the epoch history no longer reconstructs from the log."
            .to_string()
    })
}

/// ⚑ A SCHEMA EPOCH MOVED AND THE LOG DOES NOT SAY SO.
///
/// `docs/VK-REGEN-LOG.md` is how a reader reconstructs what each epoch re-genesised. On
/// 2026-08-01 its last row said "Schema epoch UNCHANGED at 20" while the constant twelve lines
/// above this test read **21**: `6441705e8` bumped it and ran no emit. The structural defect is
/// that **the epoch is a Rust constant any commit can bump, while only `emit_descriptors.py`
/// appends to that log** — so a check inside the emit path reproduces the blind spot exactly.
///
/// This test is the body of the gate that sits NEXT TO THE CONSTANT. `cargo test -p
/// dregg-persist` is what a lane editing `persist/src/lib.rs` runs anyway, and this reds there,
/// before any gate script or CI job is involved. `scripts/check-schema-epoch-log.py` is the
/// same comparison plus the ledger-vs-git-history leg, and it welds this test in place (its
/// TWIN-GONE finding fires if this function is deleted or stops naming the log).
///
/// `include_str!` on purpose: a missing log is a COMPILE error, not a skipped test.
///
/// ⚠ Never repair a red here by widening what is compared. The constant moving IS a re-genesis;
/// append the row (what re-genesised · what re-emits · what now refuses to load) and a ledger row.
#[test]
fn schema_epoch_log_row() {
    let (logged, when) = last_logged_epoch(VK_REGEN_LOG).expect("docs/VK-REGEN-LOG.md");
    assert_eq!(
        logged,
        PersistentStore::CANONICAL_STATE_SCHEMA_EPOCH,
        "CANONICAL_STATE_SCHEMA_EPOCH = {} but the last epoch-bearing row of \
         docs/VK-REGEN-LOG.md (`{when}`) reads {logged}. A schema epoch moved with no row. \
         Append an event row AND a ledger row saying what re-genesised, what must be re-emitted, \
         and what now refuses to load.",
        PersistentStore::CANONICAL_STATE_SCHEMA_EPOCH
    );
}

/// The `-red` half, and it is not optional: `schema_epoch_log_row` is a NEGATIVE assertion,
/// which passes just as happily when its own reader is broken. Everything here runs on strings
/// in memory, so the shared tree is never mutated and no window exists in which a sibling lane
/// can compile a disarmed guard.
///
/// An injection that matches NOTHING is itself a failure — each mutation asserts it bit.
#[test]
fn schema_epoch_log_row_can_go_red() {
    let real = VK_REGEN_LOG;
    let epoch = PersistentStore::CANONICAL_STATE_SCHEMA_EPOCH;
    let tag = format!("| epoch:{epoch} |");
    assert!(
        real.contains(&tag),
        "the real log no longer carries `{tag}`; this red-proof's injections would match nothing."
    );

    // CONTROL — the tree as it stands reads clean. Without this, every red below is meaningless.
    assert_eq!(last_logged_epoch(real).expect("control").0, epoch);

    // 1 · THE ORIGIN STORY, against the REAL constant. `6441705e8` moved the constant and wrote
    //     no row, so the log went on recording the epoch BEFORE the bump. Rewind the last row
    //     one epoch and the comparison `schema_epoch_log_row` makes stops holding.
    //
    // ⚑ THE INJECTION MUST REWIND **EVERY** ROW AT THE CURRENT EPOCH, not just the first.
    // This was `replacen(&tag, …, 1)`, which modelled the `6441705e8` shape only while the
    // current epoch appeared exactly ONCE in the log. Two rows at one epoch is ordinary (rows
    // 143/144 both read `epoch:22`; 147/148/149 all read `epoch:23`), and with a duplicate
    // present the mutation rewound a row `last_logged_epoch` does not read — leaving the
    // assertion below comparing 26 against 26 and this red-proof asserting NOTHING. Rewinding
    // one occurrence also breaks the reader's monotonicity leg (`the epoch only ratchets up`),
    // which is an Err rather than the value inequality this step is about. Rewinding all of
    // them is the actual `6441705e8` state: the constant moved, the log did not. Nothing is
    // widened — the comparison is untouched.
    let stale = real.replace(&tag, &format!("| epoch:{} |", epoch - 1));
    assert_ne!(stale, real, "stale-log injection matched nothing");
    assert_ne!(
        last_logged_epoch(&stale).expect("stale").0,
        epoch,
        "a constant that moved past the log's last row must NOT compare equal — this is the \
         6441705e8 shape, and it is the one thing this gate exists to refuse"
    );

    // 2 · ...and appending the row makes it agree again. A gate that cannot be satisfied is a
    //     wall, not a gate: the fix is a ROW, never a wider comparison.
    let rowed = format!(
        "{}\n| 2026-08-02T00:00:00Z | red-proof | in-memory | {} | {} | no | RED-PROOF | epoch:{epoch} |\n",
        stale.trim_end(),
        "0".repeat(40),
        "0".repeat(40),
    );
    assert_eq!(last_logged_epoch(&rowed).expect("rowed").0, epoch);

    // 3 · FAIL-CLOSED: truncated epoch cell.
    let trunc = real.replacen(&tag, "| epoch: |", 1);
    assert_ne!(trunc, real, "truncation injection matched nothing");
    assert!(
        last_logged_epoch(&trunc).is_err(),
        "a truncated epoch cell must be RED"
    );

    // 4 · FAIL-CLOSED: an epoch cell that is text but not an epoch.
    let garbled = real.replacen(&tag, "| epoch:twenty-two |", 1);
    assert_ne!(garbled, real, "garble injection matched nothing");
    assert!(
        last_logged_epoch(&garbled).is_err(),
        "a garbled epoch cell must be RED"
    );

    // 5 · FAIL-CLOSED, the whole column — the shape this gate exists to refuse. Every event row
    //     loses its trailing cell, so nothing is epoch-bearing and NOTHING may read as clean.
    let stripped: String = real
        .lines()
        .map(|l| match l.rfind("| epoch:") {
            Some(i) if l.starts_with("| 20") && l.trim_end().ends_with('|') => {
                format!("{} |\n", l[..i].trim_end())
            }
            _ => format!("{l}\n"),
        })
        .collect();
    assert_ne!(stripped, real, "column-strip injection matched nothing");
    assert!(
        last_logged_epoch(&stripped).is_err(),
        "a log that lost its epoch column must be RED, not green"
    );

    // 6 · FAIL-CLOSED: a BLIND reader harvests nothing and must not report clean.
    assert!(last_logged_epoch("").is_err(), "an empty log must be RED");
    assert!(
        last_logged_epoch("| when (UTC) | operator |\n|---|---|\n").is_err(),
        "a log with a header and no rows must be RED"
    );

    // 7 · the column made non-monotone.
    let back = real.replacen("| epoch:21 |", "| epoch:5 |", 1);
    assert_ne!(back, real, "monotonicity injection matched nothing");
    assert!(
        last_logged_epoch(&back).is_err(),
        "a decreasing epoch must be RED"
    );
}

/// F5: the durable receipt-index HEAD anchor `{ len, root }` round-trips and
/// SURVIVES a reopen (crash recovery), so boot can check the recovered chain
/// against the head served before restart. A fresh store has no anchor.
#[test]
fn receipt_index_head_anchor_round_trips_across_reopen() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("head.redb");
    let root1 = [0x42u8; 32];
    let root2 = [0x99u8; 32];
    {
        let store = PersistentStore::open(&path).expect("open");
        assert_eq!(
            store.load_receipt_index_head().unwrap(),
            None,
            "a fresh store has no receipt-index head anchor"
        );
        store
            .persist_receipt_index_head(7, &root1)
            .expect("persist");
        assert_eq!(store.load_receipt_index_head().unwrap(), Some((7, root1)));
        // Idempotent overwrite advances the anchor forward.
        store
            .persist_receipt_index_head(9, &root2)
            .expect("persist 2");
        assert_eq!(store.load_receipt_index_head().unwrap(), Some((9, root2)));
    }
    // Reopen the SAME file: the anchor survives the restart.
    let store = PersistentStore::open(&path).expect("reopen");
    assert_eq!(
        store.load_receipt_index_head().unwrap(),
        Some((9, root2)),
        "the receipt-index head anchor survives a restart"
    );
}

#[test]
fn canonical_state_epoch_refuses_populated_unmarked_pre_v11_store_on_reopen() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("pre-v11.redb");
    {
        let store = PersistentStore::open(&path).unwrap();
        let write = store.db.begin_write().unwrap();
        {
            let mut metadata = write.open_table(crate::tables::METADATA).unwrap();
            metadata
                .remove(crate::tables::META_CANONICAL_STATE_SCHEMA_EPOCH)
                .unwrap();
            drop(metadata);
            let mut log = write.open_table(crate::tables::COMMIT_LOG).unwrap();
            log.insert(0, b"pre-v11-authority".as_slice()).unwrap();
        }
        write.commit().unwrap();
    }

    let error = match PersistentStore::open(&path) {
        Ok(_) => panic!("populated unmarked pre-v11 store must be refused"),
        Err(error) => error,
    };
    assert!(matches!(error, StoreError::Integrity(message)
        if message.contains("re-genesis required")));
}

#[test]
fn canonical_state_epoch_refuses_populated_unmarked_cell_index_on_reopen() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("pre-v11-cell-index.redb");
    {
        let store = PersistentStore::open(&path).unwrap();
        let write = store.db.begin_write().unwrap();
        {
            let mut metadata = write.open_table(crate::tables::METADATA).unwrap();
            metadata
                .remove(crate::tables::META_CANONICAL_STATE_SCHEMA_EPOCH)
                .unwrap();
            drop(metadata);

            let mut cell_index = write.open_table(crate::tables::IDX_CELL_BY_ID).unwrap();
            cell_index
                .insert(&[7u8; 32], b"pre-v11-cell-snapshot".as_slice())
                .unwrap();
        }
        write.commit().unwrap();
    }

    let error = match PersistentStore::open(&path) {
        Ok(_) => panic!("unmarked pre-v11 cell index must be refused"),
        Err(error) => error,
    };
    assert!(matches!(error, StoreError::Integrity(message)
        if message.contains("re-genesis required")));
}

#[test]
fn mismatched_canonical_state_epoch_is_refused_on_reopen() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("wrong-epoch.redb");
    {
        let store = PersistentStore::open(&path).unwrap();
        let write = store.db.begin_write().unwrap();
        {
            let mut metadata = write.open_table(crate::tables::METADATA).unwrap();
            metadata
                .insert(crate::tables::META_CANONICAL_STATE_SCHEMA_EPOCH, 10)
                .unwrap();
        }
        write.commit().unwrap();
    }

    let error = match PersistentStore::open(&path) {
        Ok(_) => panic!("mismatched canonical-state epoch must be refused"),
        Err(error) => error,
    };
    assert!(matches!(error, StoreError::Integrity(message)
        if message.contains("epoch 10") && message.contains("re-genesis")));
}

#[test]
fn canonical_ledger_root_uses_v3_domain() {
    let leaves = vec![([1u8; 32], [2u8; 32])];
    let root = crate::canonical_ledger_root_from_leaves(&leaves);

    let mut v3 = blake3::Hasher::new_derive_key("dregg-ledger-root-v3");
    v3.update(&1u64.to_le_bytes());
    v3.update(&leaves[0].0);
    v3.update(&leaves[0].1);
    assert_eq!(root, *v3.finalize().as_bytes());

    let mut v2 = blake3::Hasher::new_derive_key("dregg-ledger-root-v2");
    v2.update(&1u64.to_le_bytes());
    v2.update(&leaves[0].0);
    v2.update(&leaves[0].1);
    assert_ne!(root, *v2.finalize().as_bytes());
}

#[test]
fn canonical_ledger_root_matches_starbridge_wasm_copy() {
    let empty = dregg_cell::Ledger::new();
    assert_eq!(
        crate::canonical_ledger_root(&empty),
        starbridge_wasm_persistence::canonical_ledger_root(&empty)
    );

    let mut populated = dregg_cell::Ledger::new();
    populated
        .insert_cell(dregg_cell::Cell::new([3u8; 32], [9u8; 32]))
        .unwrap();
    assert_eq!(
        crate::canonical_ledger_root(&populated),
        starbridge_wasm_persistence::canonical_ledger_root(&populated)
    );
}

// =============================================================================
// Durable receipt log
// =============================================================================

#[test]
fn receipt_log_append_is_dense_immutable_and_idempotent() {
    let store = new_store();
    let first = b"signed-receipt-zero";

    store.append_receipt_chain_entry(0, first).unwrap();
    store
        .append_receipt_chain_entry(0, first)
        .expect("byte-identical retry is idempotent");
    assert!(matches!(
        store.append_receipt_chain_entry(0, b"different-receipt"),
        Err(StoreError::Integrity(_))
    ));
    assert!(matches!(
        store.append_receipt_chain_entry(2, b"gap"),
        Err(StoreError::Integrity(_))
    ));
    assert_eq!(store.load_receipt_chain().unwrap(), vec![first.to_vec()]);
    assert_eq!(store.receipt_chain_len().unwrap(), 1);
}

#[test]
fn receipt_log_gap_is_boot_integrity_error_not_a_shorter_prefix() {
    let store = new_store();
    store
        .append_receipt_chain_entry(0, b"signed-receipt-zero")
        .unwrap();

    // Inject the exact durable corruption boot must refuse: index one is absent
    // while a later accepted receipt remains in the table.
    let txn = store.db.begin_write().unwrap();
    {
        let mut table = txn.open_table(crate::tables::RECEIPT_CHAIN).unwrap();
        table.insert(2, b"signed-receipt-two".as_slice()).unwrap();
    }
    txn.commit().unwrap();

    assert!(matches!(
        store.load_receipt_chain(),
        Err(StoreError::Integrity(_))
    ));
    assert!(matches!(
        store.receipt_chain_len(),
        Err(StoreError::Integrity(_))
    ));
    assert!(matches!(
        store.append_receipt_chain_entry(1, b"would-paper-over-gap"),
        Err(StoreError::Integrity(_))
    ));
}

fn sample_attested_root(height: u64) -> StoredAttestedRoot {
    StoredAttestedRoot {
        merkle_root: [height as u8; 32],
        note_tree_root: None,
        nullifier_set_root: None,
        height,
        timestamp: 1000 + height as i64 * 100,
        blocklace_block_id: None,
        finality_round: None,
        quorum_signatures: vec![
            (PublicKey([0x11; 32]), Signature([0x22; 64])),
            (PublicKey([0x33; 32]), Signature([0x44; 64])),
            (PublicKey([0x55; 32]), Signature([0x66; 64])),
        ],
        threshold_qc: None,
        threshold: 2,
        federation_id: dregg_types::FederationId::PLACEHOLDER,
        receipt_stream_root: None,
        finalization_quorum: Vec::new(),
    }
}

// =============================================================================
// Federation (Revocation) Tests
// =============================================================================

#[test]
fn revocation_store_and_check() {
    let store = new_store();

    assert!(!store.is_revoked("token-1").unwrap());
    store.store_revocation("token-1").unwrap();
    assert!(store.is_revoked("token-1").unwrap());
    assert!(!store.is_revoked("token-2").unwrap());
}

#[test]
fn revocation_idempotent() {
    let store = new_store();

    store.store_revocation("token-1").unwrap();
    store.store_revocation("token-1").unwrap(); // Should not error.
    assert_eq!(store.revocation_count().unwrap(), 1);
}

#[test]
fn revocation_count() {
    let store = new_store();

    assert_eq!(store.revocation_count().unwrap(), 0);
    store.store_revocation("a").unwrap();
    store.store_revocation("b").unwrap();
    store.store_revocation("c").unwrap();
    assert_eq!(store.revocation_count().unwrap(), 3);
}

#[test]
fn revocation_list() {
    let store = new_store();

    store.store_revocation("beta").unwrap();
    store.store_revocation("alpha").unwrap();
    store.store_revocation("gamma").unwrap();

    let mut list = store.list_revocations().unwrap();
    list.sort();
    assert_eq!(list, vec!["alpha", "beta", "gamma"]);
}

#[test]
fn revocation_batch() {
    let store = new_store();

    let count = store
        .store_revocations_batch(&["x", "y", "z", "x"])
        .unwrap();
    // "x" appears twice but should only be counted once.
    assert_eq!(count, 3);
    assert_eq!(store.revocation_count().unwrap(), 3);
    assert!(store.is_revoked("x").unwrap());
    assert!(store.is_revoked("y").unwrap());
    assert!(store.is_revoked("z").unwrap());
}

#[test]
fn revocation_time() {
    let store = new_store();

    store.store_revocation_at("token-1", 1234567890).unwrap();
    assert_eq!(store.revocation_time("token-1").unwrap(), Some(1234567890));
    assert_eq!(store.revocation_time("token-2").unwrap(), None);
}

// =============================================================================
// Federation (Attested Root) Tests
// =============================================================================

/// DIAGNOSIS — the N3 committee-restart hole (`node/src/blocklace_sync.rs`
/// full-mode commit path).
///
/// The commit path persists a full-mode attested root with only the LOCAL
/// node's single signature and `threshold = committee size`. On restart,
/// `verify_signed_anchor_and_rollback` (`node/src/state.rs`) calls
/// [`StoredAttestedRoot::verify_signatures`], which requires
/// `quorum_signatures.len() >= threshold` valid committee signatures over the
/// root's canonical `signing_message()`. A single-signature root therefore
/// fails and a full-mode committee node fail-closes after finalizing >=1
/// height (solo/threshold-1 is unaffected).
///
/// This test PINS both halves of the CORRECT recovery-anchor behavior so the
/// eventual fix is measured against the right bar (and so the anchor is never
/// silently weakened):
///   * a genuinely sub-quorum root (1 sig, threshold 3) is REFUSED — the
///     recovery anchor is correct security hardening and must stay strict;
///   * a genuine committee quorum (>=threshold valid sigs over the SAME
///     message) is ACCEPTED — exactly the record the persistence layer must
///     produce to close the hole WITHOUT relaxing the check;
///   * a quorum-COUNT of signatures that do not verify over this root's
///     message (they signed a different merkle_root) is still REFUSED — the
///     anchor binds the committed state root, not just a signature count.
#[test]
fn full_mode_single_sig_root_is_refused_genuine_quorum_accepted() {
    use dregg_types::{SigningKey, sign};

    // A 3-member committee (the N3 full-mode shape); threshold = 3.
    let sks: Vec<SigningKey> = (1u8..=3)
        .map(|s| SigningKey::from_bytes(&[s; 32]))
        .collect();
    let committee: Vec<PublicKey> = sks.iter().map(|k| k.public_key()).collect();

    // Build the attested root the way the full-mode commit path does.
    let mut root = StoredAttestedRoot {
        merkle_root: [0xAB; 32],
        note_tree_root: None,
        nullifier_set_root: None,
        height: 1,
        timestamp: 1_700_000_000,
        blocklace_block_id: Some([0xCD; 32]),
        finality_round: Some(1),
        quorum_signatures: Vec::new(),
        threshold_qc: None,
        threshold: 3,
        federation_id: dregg_types::FederationId::PLACEHOLDER,
        receipt_stream_root: Some([0xEF; 32]),
        finalization_quorum: Vec::new(),
    };
    let msg = root.signing_message();

    // ── THE BUG: full mode persists ONLY the local signature. 1 < 3. ──
    root.quorum_signatures = vec![(committee[0], sign(&sks[0], &msg))];
    assert!(
        !root.verify_signatures(&committee),
        "a single-signature full-mode root MUST be refused on restart — the \
         recovery anchor is correct; the persistence under-feeds it (N3 hole)"
    );

    // ── THE FIX TARGET: a genuine committee quorum over the SAME message. ──
    root.quorum_signatures = sks
        .iter()
        .map(|k| (k.public_key(), sign(k, &msg)))
        .collect();
    assert!(
        root.verify_signatures(&committee),
        "a genuine >=threshold committee quorum over the root's signing message \
         MUST be accepted — this is the record the commit path must persist"
    );

    // A quorum threshold counts distinct committee identities, not serialized
    // rows. Repeating one member's otherwise-valid signature must not inflate a
    // 1-of-3 observation into a 3-of-3 authority.
    let one_valid_signature = root.quorum_signatures[0].clone();
    root.quorum_signatures = vec![one_valid_signature; 3];
    assert!(
        !root.verify_signatures(&committee),
        "duplicating one valid committee signature must not manufacture quorum"
    );

    let mut zero_threshold = root.clone();
    zero_threshold.threshold = 0;
    zero_threshold.quorum_signatures.clear();
    assert!(
        !zero_threshold.verify_signatures(&committee),
        "a zero threshold is not a cryptographic authority"
    );

    // ── The anchor stays strict against forgery: >=threshold signatures that
    //    do NOT verify over THIS root's message (they signed a different
    //    merkle_root) are still refused. ──
    let other = StoredAttestedRoot {
        merkle_root: [0x00; 32],
        ..root.clone()
    };
    let other_msg = other.signing_message();
    root.quorum_signatures = sks
        .iter()
        .map(|k| (k.public_key(), sign(k, &other_msg)))
        .collect();
    assert!(
        !root.verify_signatures(&committee),
        "three signatures over a DIFFERENT merkle_root must NOT satisfy the \
         anchor — the check binds the committed state root, not just a count"
    );
}

/// REGRESSION — the N3 committee-restart hole is CLOSED by Fix B.
///
/// This reproduces the exact wedge and proves the fix, at the persistence
/// boundary a real restart crosses (`store_attested_root` → drop the store →
/// reopen → `latest_attested_root` → verify the anchor):
///
///   * PRE-FIX shape (the wedge): a full-mode root carrying only the local
///     node's single signature at `threshold = committee-size` CANNOT re-anchor
///     — neither the light-client `verify_signatures` nor the new
///     `verify_finalization_quorum` accepts it. This is the fail-close a
///     committee node hit after finalizing >=1 height.
///   * POST-FIX shape (Fix B): the same root, once the >=threshold committee
///     finalization-vote quorum has assembled into `finalization_quorum`,
///     survives the store/reload restart and `verify_finalization_quorum`
///     ACCEPTS it — the node re-anchors and keeps finalizing.
///   * SOUNDNESS held: a root whose `finalization_quorum` is a sub-threshold or
///     wrong-root set of signatures is still REFUSED after reload. No quorum,
///     no anchor.
#[test]
fn committee_node_restarts_cleanly_with_finalization_quorum() {
    use crate::federation::QuorumSignature;
    use dregg_federation::frost::MlDsaSigningKey;
    use dregg_types::{SigningKey, sign};

    // The ML-DSA-65 derivations below go through `dregg-pq`, which aborts the process with no
    // verified core installed — see `FaithfulNoteRootEnvelopeV1::verify_hybrid`.
    dregg_pq_testkit::install_or_panic();

    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("committee_restart.redb");

    // A 3-member full-mode committee; threshold = supermajority(3) = 3.
    let sks: Vec<SigningKey> = (1u8..=3)
        .map(|s| SigningKey::from_bytes(&[s; 32]))
        .collect();
    let committee: Vec<PublicKey> = sks.iter().map(|k| k.public_key()).collect();
    // The committee's ML-DSA-65 keypairs, derived from the SAME seed bytes as
    // the ed25519 keys (exactly the production derivation) — the PQ half.
    let pqs: Vec<(dregg_federation::frost::MlDsaPublicKey, MlDsaSigningKey)> = (1u8..=3)
        .map(|s| MlDsaSigningKey::from_seed(&[s; 32]))
        .collect();
    // The genesis-ENROLLED ML-DSA roster, aligned index-for-index with `committee`.
    let ml_dsa_committee: Vec<dregg_federation::frost::MlDsaPublicKey> =
        pqs.iter().map(|(pk, _)| pk.clone()).collect();

    let block_id = [0xCD; 32];
    let merkle_root = [0xAB; 32];

    // The record the FIXED commit path persists once the vote quorum assembles:
    // the local single sig stays in `quorum_signatures` (light-client
    // attestation), and the >=threshold committee HYBRID finalization-vote
    // signatures over `(block_id, merkle_root)` fill `finalization_quorum` — each
    // carrying BOTH halves and the voter's ML-DSA pubkey (option (a)).
    let receipt_stream_root = Some(FIXTURE_STREAM_ROOT);
    let vote_msg = dregg_types::finalization_vote_signing_message(
        &block_id,
        &merkle_root,
        receipt_stream_root,
    );
    let hybrid_quorum = |msg: &[u8]| -> Vec<QuorumSignature> {
        sks.iter()
            .zip(pqs.iter())
            .map(|(k, (pq_pk, pq_sk))| QuorumSignature {
                voter: k.public_key(),
                signature: sign(k, msg),
                ml_dsa_pubkey: pq_pk.0.to_vec(),
                pq_signature: pq_sk.sign(msg).expect("ml-dsa signing"),
            })
            .collect()
    };
    let quorum: Vec<QuorumSignature> = hybrid_quorum(&vote_msg);

    let base = StoredAttestedRoot {
        merkle_root,
        note_tree_root: None,
        nullifier_set_root: None,
        height: 1,
        timestamp: 1_700_000_000,
        blocklace_block_id: Some(block_id),
        finality_round: Some(1),
        // The single LOCAL signature over the full `signing_message()` — this is
        // all a full-mode node holds synchronously (1 < threshold 3).
        quorum_signatures: vec![(
            committee[0],
            sign(
                &sks[0],
                &StoredAttestedRoot {
                    merkle_root,
                    note_tree_root: None,
                    nullifier_set_root: None,
                    height: 1,
                    timestamp: 1_700_000_000,
                    blocklace_block_id: Some(block_id),
                    finality_round: Some(1),
                    quorum_signatures: Vec::new(),
                    threshold_qc: None,
                    threshold: 3,
                    federation_id: dregg_types::FederationId::PLACEHOLDER,
                    receipt_stream_root,
                    finalization_quorum: Vec::new(),
                }
                .signing_message(),
            ),
        )],
        threshold_qc: None,
        threshold: 3,
        federation_id: dregg_types::FederationId::PLACEHOLDER,
        receipt_stream_root,
        finalization_quorum: Vec::new(),
    };

    // ── THE WEDGE (pre-fix persisted shape): only the lone local sig. ──
    // Neither anchor path can re-verify it → the node fail-closes.
    assert!(
        !base.verify_signatures(&committee),
        "lone local sig (1 < 3) must NOT satisfy the light-client anchor"
    );
    assert!(
        !base.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "an empty finalization_quorum must NOT satisfy the restart anchor (the wedge)"
    );

    // ── FIX B (post-quorum-assembly persisted shape). ──
    let fixed = StoredAttestedRoot {
        finalization_quorum: quorum.clone(),
        ..base.clone()
    };

    // Persist it, then simulate a RESTART: drop the store, reopen from disk.
    {
        let store = PersistentStore::open(&path).unwrap();
        store.store_attested_root(&fixed).unwrap();
    }
    let reloaded = {
        let store = PersistentStore::open(&path).unwrap();
        store.latest_attested_root().unwrap().unwrap()
    };
    assert_eq!(reloaded.height, 1);
    assert!(
        reloaded.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "after restart, a genuine >=threshold committee finalization-vote quorum \
         over the finalized root MUST re-anchor — the committee node restarts cleanly"
    );

    // ── SOUNDNESS: a sub-threshold quorum is still refused after reload. ──
    let sub_quorum = StoredAttestedRoot {
        finalization_quorum: quorum[..2].to_vec(), // 2 < 3
        ..base.clone()
    };
    assert!(
        !sub_quorum.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "a sub-threshold finalization quorum must be refused — no weakening"
    );

    // ── SOUNDNESS: >=threshold signatures over a DIFFERENT root are refused. ──
    let wrong_msg =
        dregg_types::finalization_vote_signing_message(&block_id, &[0x00; 32], receipt_stream_root);
    let wrong_root_quorum = hybrid_quorum(&wrong_msg);
    let forged = StoredAttestedRoot {
        finalization_quorum: wrong_root_quorum,
        ..base.clone()
    };
    assert!(
        !forged.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "three sigs over a DIFFERENT merkle_root must NOT anchor THIS root — the \
         quorum binds the committed state, not just a count"
    );

    // ── SOUNDNESS: corrupting the PQ half alone makes restart REFUSE. Every
    // ed25519 half is untouched (still valid), yet the hybrid anchor fails —
    // the post-quantum half is load-bearing, not decorative. ──
    let mut pq_corrupt = quorum.clone();
    pq_corrupt[0].pq_signature[0] ^= 0xFF;
    let pq_forged = StoredAttestedRoot {
        finalization_quorum: pq_corrupt,
        ..base.clone()
    };
    assert!(
        !pq_forged.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "a corrupted ML-DSA half must refuse the restart anchor even though every \
         ed25519 half still verifies (classical ∧ pq)"
    );

    // ── SOUNDNESS: a MISSING PQ half (empty / wrong-length pubkey) is refused. ──
    let mut pq_missing = quorum.clone();
    pq_missing[0].pq_signature = Vec::new();
    let missing_sig = StoredAttestedRoot {
        finalization_quorum: pq_missing,
        ..base.clone()
    };
    assert!(
        !missing_sig.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "an empty ML-DSA signature cannot satisfy the hybrid anchor"
    );
    let mut pq_badkey = quorum.clone();
    pq_badkey[0].ml_dsa_pubkey = vec![0u8; 10]; // wrong length → undecodable
    let bad_key = StoredAttestedRoot {
        finalization_quorum: pq_badkey,
        ..base.clone()
    };
    assert!(
        !bad_key.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "an undecodable ML-DSA pubkey refuses the whole quorum — no silent skip"
    );

    // ── SOUNDNESS: an equivocating single voter cannot inflate the quorum. ──
    let inflated = StoredAttestedRoot {
        finalization_quorum: vec![quorum[0].clone(), quorum[0].clone(), quorum[0].clone()],
        ..base.clone()
    };
    assert!(
        !inflated.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "one voter repeated 3x is 1 distinct signer < threshold 3 — refused"
    );
}

/// Build a 3-member committee, its ed25519+ML-DSA keys, and a persisted attested
/// root carrying a genuine HYBRID finalization-vote quorum. Returns
/// `(committee, ml_dsa_committee, root, block_id, merkle_root)` for restart tests
/// below — the ML-DSA roster is the genesis-ENROLLED one, aligned with `committee`.
#[cfg(test)]
fn hybrid_quorum_fixture() -> (
    Vec<PublicKey>,
    Vec<dregg_federation::frost::MlDsaPublicKey>,
    StoredAttestedRoot,
    [u8; 32],
    [u8; 32],
) {
    use crate::federation::QuorumSignature;
    use dregg_federation::frost::MlDsaSigningKey;
    use dregg_types::{SigningKey, sign};

    // The ML-DSA-65 derivations below go through `dregg-pq`, which aborts the process with no
    // verified core installed — see `FaithfulNoteRootEnvelopeV1::verify_hybrid`. This is the same
    // install `committee_node_restarts_cleanly_with_finalization_quorum` already performs; the
    // four tests built on THIS fixture never did, so they SIGABRT'd before their first assertion.
    dregg_pq_testkit::install_or_panic();

    let sks: Vec<SigningKey> = (1u8..=3)
        .map(|s| SigningKey::from_bytes(&[s; 32]))
        .collect();
    let committee: Vec<PublicKey> = sks.iter().map(|k| k.public_key()).collect();
    let pqs: Vec<(dregg_federation::frost::MlDsaPublicKey, MlDsaSigningKey)> = (1u8..=3)
        .map(|s| MlDsaSigningKey::from_seed(&[s; 32]))
        .collect();
    let ml_dsa_committee: Vec<dregg_federation::frost::MlDsaPublicKey> =
        pqs.iter().map(|(pk, _)| pk.clone()).collect();

    let block_id = [0xCD; 32];
    let merkle_root = [0xAB; 32];
    // v4: the vote preimage absorbs the finalized block's receipt stream, so the
    // fixture's root must CARRY the value its quorum signed. A root whose
    // `receipt_stream_root` differs from what the members voted over simply has
    // no valid quorum — which is the binding, working.
    let receipt_stream_root = Some(FIXTURE_STREAM_ROOT);
    let vote_msg = dregg_types::finalization_vote_signing_message(
        &block_id,
        &merkle_root,
        receipt_stream_root,
    );
    let quorum: Vec<QuorumSignature> = sks
        .iter()
        .zip(pqs.iter())
        .map(|(k, (pq_pk, pq_sk))| QuorumSignature {
            voter: k.public_key(),
            signature: sign(k, &vote_msg),
            ml_dsa_pubkey: pq_pk.0.to_vec(),
            pq_signature: pq_sk.sign(&vote_msg).expect("ml-dsa signing"),
        })
        .collect();

    let root = StoredAttestedRoot {
        merkle_root,
        note_tree_root: None,
        nullifier_set_root: None,
        height: 1,
        timestamp: 1_700_000_000,
        blocklace_block_id: Some(block_id),
        finality_round: Some(1),
        quorum_signatures: Vec::new(),
        threshold_qc: None,
        threshold: 3,
        federation_id: dregg_types::FederationId::PLACEHOLDER,
        receipt_stream_root,
        finalization_quorum: quorum,
    };
    (committee, ml_dsa_committee, root, block_id, merkle_root)
}

/// A persisted HYBRID quorum re-verifies after a store/reload restart iff BOTH
/// halves are intact: the reloaded root re-anchors, and every signer's ed25519
/// AND ML-DSA-65 half verifies over the finalized `(block_id, merkle_root)`.
#[test]
fn restart_reverifies_hybrid_quorum() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("hybrid_restart.redb");
    let (committee, ml_dsa_committee, root, _block_id, _merkle_root) = hybrid_quorum_fixture();

    {
        let store = PersistentStore::open(&path).unwrap();
        store.store_attested_root(&root).unwrap();
    }
    // RESTART: reopen from disk (postcard round-trip of the widened field).
    let reloaded = {
        let store = PersistentStore::open(&path).unwrap();
        store.latest_attested_root().unwrap().unwrap()
    };
    assert_eq!(
        reloaded, root,
        "the widened hybrid quorum round-trips postcard"
    );
    assert!(
        reloaded.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "a persisted genuine hybrid quorum re-anchors on restart (classical ∧ pq)"
    );
}

/// Corrupting the POST-QUANTUM half of a persisted quorum makes restart REFUSE —
/// even though every ed25519 half is untouched. The persisted anchor now
/// re-verifies the FULL hybrid quorum, not just ed25519.
#[test]
fn restart_refuses_missing_pq_half() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("hybrid_restart_bad.redb");
    let (committee, ml_dsa_committee, mut root, _block_id, _merkle_root) = hybrid_quorum_fixture();

    // Corrupt one signer's ML-DSA signature; the ed25519 half stays valid.
    root.finalization_quorum[0].pq_signature[0] ^= 0xFF;

    {
        let store = PersistentStore::open(&path).unwrap();
        store.store_attested_root(&root).unwrap();
    }
    let reloaded = {
        let store = PersistentStore::open(&path).unwrap();
        store.latest_attested_root().unwrap().unwrap()
    };
    assert!(
        !reloaded.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "a broken ML-DSA half must make the restart anchor REFUSE — the persisted \
         quorum is hybrid, not ed25519-only"
    );

    // And a fully DROPPED pq half (empty signature) is equally refused.
    let (committee2, ml_dsa_committee2, mut root2, _b, _m) = hybrid_quorum_fixture();
    root2.finalization_quorum[0].pq_signature = Vec::new();
    assert!(
        !root2.verify_finalization_quorum(&committee2, &ml_dsa_committee2),
        "an empty ML-DSA signature cannot satisfy the hybrid restart anchor"
    );
}

/// **THE QUANTUM-FORGERY ADVERSARIAL TEST (persist restart anchor).** The exact
/// attack the enrolled-roster pin closes: a quantum adversary breaks ed25519 for
/// enrolled member `P` (we reuse P's real ed25519 key to stand in for the forged
/// classical half), generates its OWN fresh ML-DSA-65 keypair, and signs the PQ
/// half with it — carrying that attacker key in `ml_dsa_pubkey`. Before the pin,
/// the PQ half was checked against the self-carried key, so BOTH halves passed
/// and the restart re-anchored a FORGED root. With the pin, the self-carried key
/// ≠ P's enrolled key, so `verify_finalization_quorum` REJECTS the whole quorum.
/// The honest enrolled-key quorum still re-anchors, and an unconfigured (empty)
/// enrolled roster fails closed rather than downgrade to ed25519-only.
#[test]
fn quantum_forged_pq_key_is_rejected() {
    use dregg_federation::frost::MlDsaSigningKey;

    let (committee, ml_dsa_committee, root, block_id, merkle_root) = hybrid_quorum_fixture();
    let vote_msg = dregg_types::finalization_vote_signing_message(
        &block_id,
        &merkle_root,
        Some(FIXTURE_STREAM_ROOT),
    );

    // The HONEST persisted quorum re-anchors (baseline).
    assert!(
        root.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "the honest enrolled-key quorum re-anchors on restart"
    );

    // THE ATTACK: replace every signer's ML-DSA key + signature with a FRESH
    // attacker keypair (a quantum adversary that broke ed25519 keeps the ed25519
    // halves valid). Each PQ half verifies under the attacker's own key.
    let mut forged = root.clone();
    for (i, qs) in forged.finalization_quorum.iter_mut().enumerate() {
        let attacker = MlDsaSigningKey::from_seed(&[0xA0 + i as u8; 32]);
        qs.ml_dsa_pubkey = attacker.0.0.to_vec();
        qs.pq_signature = attacker.1.sign(&vote_msg).expect("ml-dsa sign");
    }
    assert!(
        !forged.verify_finalization_quorum(&committee, &ml_dsa_committee),
        "a self-carried attacker ML-DSA key (not the enrolled key) must be REJECTED \
         even though every ed25519 half and every PQ half verifies on its own terms"
    );

    // NO SILENT DOWNGRADE: an empty (misaligned) enrolled roster fails closed even
    // for the honest signers — never an ed25519-only re-anchor.
    assert!(
        !root.verify_finalization_quorum(&committee, &[]),
        "an unconfigured (empty) enrolled roster must fail closed"
    );

    // And the hybrid tamper-floor leg agrees: the forged lone entry is not a
    // committee binding.
    let lone_forged = StoredAttestedRoot {
        finalization_quorum: forged.finalization_quorum[..1].to_vec(),
        quorum_signatures: Vec::new(),
        ..root.clone()
    };
    assert!(
        !lone_forged.has_any_valid_committee_signature(&committee, &ml_dsa_committee),
        "a forged-PQ-key lone vote is not a committee binding"
    );
}

/// The LONE-SIGNATURE tamper floor is HYBRID on the vote leg: a single
/// `finalization_quorum` entry counts toward `has_any_valid_committee_signature`
/// only when BOTH halves verify. A lone signature whose ML-DSA half is forged,
/// empty, or rides an undecodable pubkey no longer counts — even though its
/// ed25519 half is perfectly valid — so there is no classical-only acceptance
/// surface left over `QuorumSignature`s (consistent with
/// `verify_finalization_quorum`'s per-signer bar).
#[test]
fn lone_signature_tamper_floor_is_hybrid() {
    let (committee, ml_dsa_committee, root, _block_id, _merkle_root) = hybrid_quorum_fixture();

    // A single GENUINE hybrid vote entry satisfies the floor (it is a
    // lone-signature check, not a quorum).
    let lone = StoredAttestedRoot {
        finalization_quorum: root.finalization_quorum[..1].to_vec(),
        ..root.clone()
    };
    assert!(
        lone.has_any_valid_committee_signature(&committee, &ml_dsa_committee),
        "one genuine hybrid committee vote binds the root (the tamper floor)"
    );

    // Forge the PQ half ONLY: the ed25519 half stays valid, yet the lone
    // signature must NOT count any more (classical ∧ pq).
    let mut pq_forged = lone.clone();
    pq_forged.finalization_quorum[0].pq_signature[0] ^= 0xFF;
    assert!(
        !pq_forged.has_any_valid_committee_signature(&committee, &ml_dsa_committee),
        "a lone signature with a FORGED ML-DSA half must not count — no \
         classical-only acceptance surface"
    );

    // An EMPTY PQ half is equally refused.
    let mut pq_missing = lone.clone();
    pq_missing.finalization_quorum[0].pq_signature = Vec::new();
    assert!(
        !pq_missing.has_any_valid_committee_signature(&committee, &ml_dsa_committee),
        "an empty ML-DSA signature cannot satisfy the hybrid tamper floor"
    );

    // An undecodable (wrong-length) carried ML-DSA pubkey is refused.
    let mut pq_badkey = lone.clone();
    pq_badkey.finalization_quorum[0].ml_dsa_pubkey = vec![0u8; 10];
    assert!(
        !pq_badkey.has_any_valid_committee_signature(&committee, &ml_dsa_committee),
        "an undecodable ML-DSA pubkey is not a committee binding"
    );

    // A voter outside the committee never counts, hybrid-valid or not.
    assert!(
        !lone.has_any_valid_committee_signature(&committee[1..], &ml_dsa_committee[1..]),
        "a non-member's signature is not a committee binding"
    );

    // The quorum_signatures leg (the node's OWN light-client self-signature,
    // structurally classical) still provides the floor when the vote leg is
    // empty — the trailing-head tamper-check the lone local signature exists for.
    use dregg_types::{SigningKey, sign};
    let sk = SigningKey::from_bytes(&[1u8; 32]);
    let mut self_signed = StoredAttestedRoot {
        quorum_signatures: Vec::new(),
        finalization_quorum: Vec::new(),
        ..root.clone()
    };
    let msg = self_signed.signing_message();
    self_signed.quorum_signatures = vec![(sk.public_key(), sign(&sk, &msg))];
    assert!(
        self_signed.has_any_valid_committee_signature(&committee, &ml_dsa_committee),
        "the local light-client self-signature still provides the tamper floor"
    );
}

/// **DUPLICATE-ENROLLED-ROSTER ADVERSARIAL TEST (persist restart anchor).**
///
/// A genesis that enrols the SAME ML-DSA-65 key at two committee positions (the
/// enrollment path checks only length alignment) must not let ONE holder of that
/// PQ key fill both slots. The threat is the quantum one the hybrid bar exists
/// for: an adversary who breaks ed25519 forges the classical halves, but cannot
/// forge the PQ half — so with a duplicate roster it reuses the ONE enrolled
/// key's signature at both positions and one PQ authority counts twice toward
/// the supermajority. The whole-roster distinctness check refuses the
/// duplicated roster outright.
///
/// n = 4 so the supermajority floor (`required_quorum` = 3) leaves one slot
/// out of the quorum: that is what lets the second arm show the WHOLE roster
/// is checked, not only the positions a quorum names. At n = 2 every slot is
/// in every quorum and that arm could not fail for the reason it names.
#[test]
fn duplicate_enrolled_pq_roster_cannot_inflate_finalization_quorum() {
    use crate::federation::QuorumSignature;
    use dregg_federation::frost::MlDsaSigningKey;
    use dregg_types::{SigningKey, sign};

    // The ML-DSA derivations below go through `dregg-pq`, which aborts the process with no
    // verified core installed — see `FaithfulNoteRootEnvelopeV1::verify_hybrid`.
    dregg_pq_testkit::install_or_panic();

    // Four DISTINCT classical committee members…
    let sks: Vec<SigningKey> = (1u8..=4)
        .map(|s| SigningKey::from_bytes(&[s; 32]))
        .collect();
    let committee: Vec<PublicKey> = sks.iter().map(|k| k.public_key()).collect();
    // …and four DISTINCT enrolled ML-DSA keys (the honest roster).
    let pqs: Vec<(dregg_federation::frost::MlDsaPublicKey, MlDsaSigningKey)> = (1u8..=4)
        .map(|s| MlDsaSigningKey::from_seed(&[s; 32]))
        .collect();
    let honest_roster: Vec<dregg_federation::frost::MlDsaPublicKey> =
        pqs.iter().map(|(pk, _)| pk.clone()).collect();
    // The duplicated roster: slot 3 enrols member 0's ML-DSA key.
    let dup_roster = vec![
        honest_roster[0].clone(),
        honest_roster[1].clone(),
        honest_roster[2].clone(),
        honest_roster[0].clone(),
    ];

    let block_id = [0xCD; 32];
    let merkle_root = [0xAB; 32];
    let vote_msg = dregg_types::finalization_vote_signing_message(&block_id, &merkle_root, None);

    let root_with = |quorum: Vec<QuorumSignature>| StoredAttestedRoot {
        merkle_root,
        note_tree_root: None,
        nullifier_set_root: None,
        height: 1,
        timestamp: 1_700_000_000,
        blocklace_block_id: Some(block_id),
        finality_round: Some(1),
        quorum_signatures: Vec::new(),
        threshold_qc: None,
        threshold: 3,
        federation_id: dregg_types::FederationId::PLACEHOLDER,
        receipt_stream_root: None,
        finalization_quorum: quorum,
    };
    // Member `i`'s vote, its PQ half signed by member `pq_of`'s ML-DSA key.
    let vote = |i: usize, pq_of: usize| QuorumSignature {
        voter: sks[i].public_key(),
        signature: sign(&sks[i], &vote_msg),
        ml_dsa_pubkey: pqs[pq_of].0.0.to_vec(),
        pq_signature: pqs[pq_of].1.sign(&vote_msg).expect("ml-dsa signing"),
    };

    // POSITIVE CONTROL: an honest DISTINCT roster, members 0..3 each signing
    // with their OWN PQ key, clears the n=4 supermajority (3).
    let honest: Vec<QuorumSignature> = (0..3).map(|i| vote(i, i)).collect();
    assert!(
        root_with(honest.clone()).verify_finalization_quorum(&committee, &honest_roster),
        "an honest DISTINCT enrolled roster must still verify at the n=4 supermajority"
    );

    // THE ATTACK: members 0, 1 and 3 vote, and member 3's PQ half is member 0's
    // REAL signature under the key slot 3 enrols (member 0's). Every half
    // verifies under the key it is pinned to, so only distinctness can refuse it.
    let aliased = vec![vote(0, 0), vote(1, 1), vote(3, 0)];
    for (qs, slot) in aliased.iter().zip([0usize, 1, 3]) {
        assert!(qs.voter.verify(&vote_msg, &qs.signature));
        assert_eq!(qs.ml_dsa_pubkey.as_slice(), dup_roster[slot].0.as_slice());
        assert!(dup_roster[slot].verify(&vote_msg, &qs.pq_signature));
    }
    assert!(
        !root_with(aliased).verify_finalization_quorum(&committee, &dup_roster),
        "a duplicate enrolled ML-DSA roster must not let one PQ authority fill two quorum slots"
    );

    // The WHOLE roster is checked (not just the positions a quorum names): the
    // honest quorum of members 0..3 never touches slot 3, yet the duplicated
    // enrollment there still refuses it.
    assert!(
        !root_with(honest).verify_finalization_quorum(&committee, &dup_roster),
        "a duplicate enrolled roster refuses even a quorum drawn only from distinct slots"
    );
}

/// **VACUOUS-QUORUM TEST (persist restart anchor).** `threshold == 0` is not an
/// authority: an EMPTY `finalization_quorum` must not re-anchor a stored root
/// whose (unsigned) `threshold` was zeroed. `required_quorum` floors the bar at
/// the committee's supermajority, so the zeroed field cannot lower it — this
/// pins that for the hybrid finalization quorum (the classical sibling is pinned
/// in `quorum_floor_tests`).
#[test]
fn zero_threshold_finalization_quorum_is_not_an_authority() {
    use crate::federation::QuorumSignature;
    use dregg_federation::frost::MlDsaSigningKey;
    use dregg_types::{SigningKey, sign};

    dregg_pq_testkit::install_or_panic();

    let sks: Vec<SigningKey> = (1u8..=2)
        .map(|s| SigningKey::from_bytes(&[s; 32]))
        .collect();
    let committee: Vec<PublicKey> = sks.iter().map(|k| k.public_key()).collect();
    let pqs: Vec<(dregg_federation::frost::MlDsaPublicKey, MlDsaSigningKey)> = (1u8..=2)
        .map(|s| MlDsaSigningKey::from_seed(&[s; 32]))
        .collect();
    let roster: Vec<dregg_federation::frost::MlDsaPublicKey> =
        pqs.iter().map(|(pk, _)| pk.clone()).collect();

    let block_id = [0xCD; 32];
    let merkle_root = [0xAB; 32];
    let vote_msg = dregg_types::finalization_vote_signing_message(&block_id, &merkle_root, None);

    let root_with = |threshold: usize, quorum: Vec<QuorumSignature>| StoredAttestedRoot {
        merkle_root,
        note_tree_root: None,
        nullifier_set_root: None,
        height: 1,
        timestamp: 1_700_000_000,
        blocklace_block_id: Some(block_id),
        finality_round: Some(1),
        quorum_signatures: Vec::new(),
        threshold_qc: None,
        threshold,
        federation_id: dregg_types::FederationId::PLACEHOLDER,
        receipt_stream_root: None,
        finalization_quorum: quorum,
    };

    // POSITIVE CONTROL: a genuine threshold-2 quorum still verifies.
    let honest: Vec<QuorumSignature> = sks
        .iter()
        .zip(pqs.iter())
        .map(|(k, (pq_pk, pq_sk))| QuorumSignature {
            voter: k.public_key(),
            signature: sign(k, &vote_msg),
            ml_dsa_pubkey: pq_pk.0.to_vec(),
            pq_signature: pq_sk.sign(&vote_msg).expect("ml-dsa signing"),
        })
        .collect();
    assert!(
        root_with(2, honest).verify_finalization_quorum(&committee, &roster),
        "a genuine threshold-2 hybrid quorum must still verify"
    );

    // A ZERO threshold with an EMPTY quorum must NOT anchor.
    assert!(
        !root_with(0, Vec::new()).verify_finalization_quorum(&committee, &roster),
        "threshold 0 is not an authority — an empty quorum must not anchor"
    );
}

#[test]
fn attested_root_store_and_load() {
    let store = new_store();

    let root = sample_attested_root(1);
    store.store_attested_root(&root).unwrap();

    let loaded = store.latest_attested_root().unwrap();
    assert_eq!(loaded, Some(root));
}

#[test]
fn attested_root_latest_tracks_highest() {
    let store = new_store();

    store.store_attested_root(&sample_attested_root(1)).unwrap();
    store.store_attested_root(&sample_attested_root(5)).unwrap();
    store.store_attested_root(&sample_attested_root(3)).unwrap();

    // Latest should be height 5 (highest stored).
    let latest = store.latest_attested_root().unwrap().unwrap();
    assert_eq!(latest.height, 5);
}

#[test]
fn attested_root_by_height() {
    let store = new_store();

    let root3 = sample_attested_root(3);
    store.store_attested_root(&root3).unwrap();

    let loaded = store.attested_root_at_height(3).unwrap();
    assert_eq!(loaded, Some(root3));
    assert_eq!(store.attested_root_at_height(99).unwrap(), None);
}

#[test]
fn attested_root_empty() {
    let store = new_store();
    assert_eq!(store.latest_attested_root().unwrap(), None);
    assert_eq!(store.attested_root_count().unwrap(), 0);
}

#[test]
fn attested_root_count() {
    let store = new_store();

    store.store_attested_root(&sample_attested_root(1)).unwrap();
    store.store_attested_root(&sample_attested_root(2)).unwrap();
    store.store_attested_root(&sample_attested_root(3)).unwrap();
    assert_eq!(store.attested_root_count().unwrap(), 3);
}

/// The summary equals the full-scan computation (latest by height + count) on
/// out-of-order inserts and after a prune, and never decodes a non-latest row:
/// an undecodable lower row breaks `all_attested_roots` but not the summary.
#[test]
fn attested_root_summary_matches_full_scan_without_decoding_it() {
    let store = new_store();
    assert_eq!(store.attested_root_summary().unwrap(), (None, 0));

    for h in [4, 9, 2, 7, 5] {
        store.store_attested_root(&sample_attested_root(h)).unwrap();
    }
    let full = |s: &PersistentStore| {
        let all = s.all_attested_roots().unwrap();
        (
            all.iter().max_by_key(|r| r.height).cloned(),
            all.len() as u64,
        )
    };
    assert_eq!(store.attested_root_summary().unwrap(), full(&store));
    assert_eq!(store.attested_root_summary().unwrap().0.unwrap().height, 9);

    store.prune_before(5).unwrap();
    assert_eq!(store.attested_root_summary().unwrap(), full(&store));
    assert_eq!(store.attested_root_summary().unwrap().1, 3);

    let write = store.db.begin_write().unwrap();
    write
        .open_table(crate::tables::ATTESTED_ROOTS)
        .unwrap()
        .insert(6u64, [0xFFu8; 3].as_slice())
        .unwrap();
    write.commit().unwrap();
    assert!(store.all_attested_roots().is_err());
    let (latest, count) = store.attested_root_summary().unwrap();
    assert_eq!((latest.unwrap().height, count), (9, 4));
}

#[test]
fn attested_root_all_ordered() {
    let store = new_store();

    store.store_attested_root(&sample_attested_root(3)).unwrap();
    store.store_attested_root(&sample_attested_root(1)).unwrap();
    store.store_attested_root(&sample_attested_root(2)).unwrap();

    let all = store.all_attested_roots().unwrap();
    assert_eq!(all.len(), 3);
    // Should be in height order (redb stores u64 keys in order).
    assert_eq!(all[0].height, 1);
    assert_eq!(all[1].height, 2);
    assert_eq!(all[2].height, 3);
}

#[test]
fn attested_root_validity() {
    let root = sample_attested_root(1);
    assert!(root.is_structurally_complete()); // 3 sigs >= threshold 2.

    let invalid = StoredAttestedRoot {
        threshold: 5,
        ..root
    };
    assert!(!invalid.is_structurally_complete()); // 3 sigs < threshold 5.
}

/// One committee finalization vote in the shape the node persists. The
/// signature bytes are never inspected by the count-only predicate under test;
/// what matters is the `voter` identity, which is what a quorum counts.
fn sample_finalization_vote(voter: u8) -> crate::federation::QuorumSignature {
    crate::federation::QuorumSignature {
        voter: PublicKey([voter; 32]),
        signature: Signature([voter; 64]),
        ml_dsa_pubkey: vec![voter; 8],
        pq_signature: vec![voter; 8],
    }
}

/// THE FULL-MODE SHAPE. A finalized root produced by a real committee node
/// carries exactly ONE local light-client signature (all a single process can
/// make synchronously) and a >=threshold `finalization_quorum` back-filled from
/// gossip. Before 2026-08-08 the predicate read only the first population, so
/// every such root — genuinely finalized, carrying 3 committee votes at
/// threshold 3 — reported `false`.
#[test]
fn a_full_mode_root_is_structurally_complete_on_its_committee_vote_quorum() {
    let base = sample_attested_root(7);
    let full_mode = StoredAttestedRoot {
        // A full-mode node holds ONE local signature, never `threshold` of them.
        quorum_signatures: vec![(PublicKey([0x11; 32]), Signature([0x22; 64]))],
        threshold: 3,
        finalization_quorum: vec![
            sample_finalization_vote(0xA1),
            sample_finalization_vote(0xA2),
            sample_finalization_vote(0xA3),
        ],
        ..base.clone()
    };
    assert_eq!(full_mode.distinct_local_signers(), 1);
    assert_eq!(full_mode.distinct_finalization_voters(), 3);
    assert!(full_mode.is_structurally_complete());

    // Below threshold on BOTH populations ⇒ not complete. This is the state a
    // freshly persisted head is in before its votes arrive, and the reason the
    // predicate must be able to say `false`.
    let gathering = StoredAttestedRoot {
        finalization_quorum: vec![sample_finalization_vote(0xA1)],
        ..full_mode.clone()
    };
    assert!(!gathering.is_structurally_complete());

    // DUPLICATES ARE NOT A QUORUM: one voter's row repeated three times counts
    // once, exactly as `verify_signatures` counts distinct identities.
    let duplicated = StoredAttestedRoot {
        finalization_quorum: vec![
            sample_finalization_vote(0xA1),
            sample_finalization_vote(0xA1),
            sample_finalization_vote(0xA1),
        ],
        ..full_mode.clone()
    };
    assert_eq!(duplicated.finalization_quorum.len(), 3);
    assert_eq!(duplicated.distinct_finalization_voters(), 1);
    assert!(!duplicated.is_structurally_complete());

    // A ZERO threshold is not an authority — the same refusal `verify_signatures`
    // already made. An empty-everything root used to answer `true` here.
    let zero_threshold = StoredAttestedRoot {
        quorum_signatures: Vec::new(),
        finalization_quorum: Vec::new(),
        threshold: 0,
        ..base
    };
    assert!(!zero_threshold.is_structurally_complete());
}

// =============================================================================
// Edge Cases
// =============================================================================

#[test]
fn many_revocations() {
    let store = new_store();

    let ids: Vec<String> = (0..1000).map(|i| format!("token-{i:05}")).collect();
    let refs: Vec<&str> = ids.iter().map(|s| s.as_str()).collect();
    store.store_revocations_batch(&refs).unwrap();

    assert_eq!(store.revocation_count().unwrap(), 1000);
    assert!(store.is_revoked("token-00500").unwrap());
    assert!(!store.is_revoked("token-01000").unwrap());
}

#[test]
fn store_root_hex() {
    let root = sample_attested_root(0xAB);
    // Height 0xAB = 171, so merkle_root = [171; 32].
    assert_eq!(root.root_hex(), "abababab");
}

// =============================================================================
// Note Tree & Nullifier Tests
// =============================================================================

#[test]
fn test_store_note_roundtrip() {
    use dregg_cell::note::Note;

    let store = new_store();

    // Create notes with deterministic randomness.
    let note1 = Note::with_randomness([1u8; 32], [1, 100, 0, 0, 0, 0, 0, 0], [10u8; 32]);
    let note2 = Note::with_randomness([2u8; 32], [1, 200, 0, 0, 0, 0, 0, 0], [20u8; 32]);
    let note3 = Note::with_randomness([3u8; 32], [2, 50, 0, 0, 0, 0, 0, 0], [30u8; 32]);

    let c1 = note1.commitment();
    let c2 = note2.commitment();
    let c3 = note3.commitment();

    // Store commitments.
    let pos1 = store.store_note_commitment(&c1).unwrap();
    let pos2 = store.store_note_commitment(&c2).unwrap();
    let pos3 = store.store_note_commitment(&c3).unwrap();

    assert_eq!(pos1, 0);
    assert_eq!(pos2, 1);
    assert_eq!(pos3, 2);
    assert_eq!(store.note_count().unwrap(), 3);

    // Recover and verify tree root matches.
    let commitments = store.load_all_note_commitments().unwrap();
    assert_eq!(commitments.len(), 3);
    assert_eq!(commitments[0], c1);
    assert_eq!(commitments[1], c2);
    assert_eq!(commitments[2], c3);

    // Rebuild tree and check root.
    let mut tree = crate::note_tree::NoteTree::from_commitments(commitments);
    let root = tree.root();
    let stored_root = store.note_tree_root().unwrap();
    assert_eq!(root, stored_root);
}

#[test]
fn test_nullifier_persistence() {
    use dregg_cell::note::{Note, Nullifier};

    let store = new_store();
    let note = Note::with_randomness([1u8; 32], [1, 100, 0, 0, 0, 0, 0, 0], [10u8; 32]);
    let spending_key = [0xBB; 32];
    let nullifier = note.nullifier(&spending_key);

    // Not spent initially.
    assert!(!store.is_nullifier_spent(&nullifier).unwrap());

    // Store it.
    store.store_nullifier(&nullifier).unwrap();

    // Now it's spent.
    assert!(store.is_nullifier_spent(&nullifier).unwrap());

    // Double-spend is rejected.
    let result = store.store_nullifier(&nullifier);
    assert!(matches!(result, Err(StoreError::Integrity(_))));

    // A different nullifier is not spent.
    let other_nullifier = Nullifier([0xFF; 32]);
    assert!(!store.is_nullifier_spent(&other_nullifier).unwrap());
}

#[test]
fn test_nullifier_persistence_across_restart() {
    use dregg_cell::note::Note;

    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("note_test.redb");
    let note = Note::with_randomness([1u8; 32], [1, 100, 0, 0, 0, 0, 0, 0], [10u8; 32]);
    let spending_key = [0xBB; 32];
    let nullifier = note.nullifier(&spending_key);

    // First session: store commitment and nullifier.
    {
        let store = PersistentStore::open(&path).unwrap();
        store.store_note_commitment(&note.commitment()).unwrap();
        store.store_nullifier(&nullifier).unwrap();
    }

    // Second session: verify persistence.
    {
        let store = PersistentStore::open(&path).unwrap();
        assert_eq!(store.note_count().unwrap(), 1);
        assert!(store.is_nullifier_spent(&nullifier).unwrap());

        let commitments = store.load_all_note_commitments().unwrap();
        assert_eq!(commitments[0], note.commitment());
    }
}

#[test]
fn test_spend_note_atomic() {
    use dregg_cell::note::Note;

    let store = new_store();

    let note1 = Note::with_randomness([1u8; 32], [1, 100, 0, 0, 0, 0, 0, 0], [10u8; 32]);
    let note2 = Note::with_randomness([2u8; 32], [1, 200, 0, 0, 0, 0, 0, 0], [20u8; 32]);
    let spending_key = [0xBB; 32];

    // First: store the original commitment for note1 (simulate issuance).
    store.store_note_commitment(&note1.commitment()).unwrap();
    assert_eq!(store.note_count().unwrap(), 1);

    // Spend note1 atomically: insert its nullifier + store the output commitment (note2).
    let nullifier1 = note1.nullifier(&spending_key);
    let pos = store
        .spend_note_atomic(&nullifier1, &note2.commitment())
        .unwrap();
    assert_eq!(pos, 1); // Second commitment is at position 1.

    // Verify both side effects occurred.
    assert!(store.is_nullifier_spent(&nullifier1).unwrap());
    assert_eq!(store.note_count().unwrap(), 2);

    // Double-spend is rejected atomically.
    let note3 = Note::with_randomness([3u8; 32], [2, 50, 0, 0, 0, 0, 0, 0], [30u8; 32]);
    let result = store.spend_note_atomic(&nullifier1, &note3.commitment());
    assert!(matches!(result, Err(StoreError::Integrity(_))));

    // The failed double-spend must not have added the commitment.
    assert_eq!(store.note_count().unwrap(), 2);
}

#[test]
fn test_spend_note_atomic_double_spend_no_side_effects() {
    use dregg_cell::note::Note;

    let store = new_store();

    let note1 = Note::with_randomness([1u8; 32], [1, 100, 0, 0, 0, 0, 0, 0], [10u8; 32]);
    let note2 = Note::with_randomness([2u8; 32], [1, 200, 0, 0, 0, 0, 0, 0], [20u8; 32]);
    let note3 = Note::with_randomness([3u8; 32], [2, 50, 0, 0, 0, 0, 0, 0], [30u8; 32]);
    let spending_key = [0xBB; 32];
    let nullifier1 = note1.nullifier(&spending_key);

    // Spend note1 successfully (creating note2 as output).
    let pos = store
        .spend_note_atomic(&nullifier1, &note2.commitment())
        .unwrap();
    assert_eq!(pos, 0);
    assert_eq!(store.note_count().unwrap(), 1);

    // Attempt double-spend: should fail AND not add note3's commitment.
    let result = store.spend_note_atomic(&nullifier1, &note3.commitment());
    assert!(result.is_err());
    assert_eq!(store.note_count().unwrap(), 1); // Still 1, not 2.
}

#[test]
fn test_attested_root_includes_note_tree() {
    use dregg_cell::note::Note;

    let store = new_store();

    // Add some notes.
    let note1 = Note::with_randomness([1u8; 32], [1, 100, 0, 0, 0, 0, 0, 0], [10u8; 32]);
    let note2 = Note::with_randomness([2u8; 32], [1, 200, 0, 0, 0, 0, 0, 0], [20u8; 32]);
    store.store_note_commitment(&note1.commitment()).unwrap();
    store.store_note_commitment(&note2.commitment()).unwrap();

    // Add a nullifier.
    let spending_key = [0xBB; 32];
    let nullifier = note1.nullifier(&spending_key);
    store.store_nullifier(&nullifier).unwrap();

    // Get the roots.
    let note_root = store.note_tree_root().unwrap();
    let nullifier_root = store.nullifier_set_root().unwrap();

    // Both should be non-zero (non-empty sets).
    assert_ne!(note_root, [0u8; 32]);
    assert_ne!(nullifier_root, [0u8; 32]);

    // Create an attested root that includes all three components.
    let attested = StoredAttestedRoot {
        merkle_root: [0xAB; 32], // Cell state root.
        note_tree_root: Some(note_root),
        nullifier_set_root: Some(nullifier_root),
        height: 1,
        timestamp: 1700000000,
        blocklace_block_id: None,
        finality_round: None,
        quorum_signatures: vec![(PublicKey([0x11; 32]), Signature([0x22; 64]))],
        threshold_qc: None,
        threshold: 1,
        federation_id: dregg_types::FederationId::PLACEHOLDER,
        receipt_stream_root: None,
        finalization_quorum: Vec::new(),
    };

    // Store and recover.
    store.store_attested_root(&attested).unwrap();
    let loaded = store.latest_attested_root().unwrap().unwrap();
    assert_eq!(loaded.note_tree_root, Some(note_root));
    assert_eq!(loaded.nullifier_set_root, Some(nullifier_root));
    assert_eq!(loaded.merkle_root, [0xAB; 32]);
}

// =============================================================================
// Forever-Digest Set Tests (restart-durable anti-replay carriers)
// =============================================================================

#[test]
fn forever_digests_survive_reopen() {
    use crate::tables::{NS_COURT_RESOLVED, NS_TRUSTLINE_DIGEST};

    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("forever.redb");

    let scope = [0x11; 32];
    let draw = [0x22; 32];
    let resolved = [0x33; 32];

    {
        let store = PersistentStore::open(&path).expect("open store");
        assert!(
            store
                .record_forever_digest(NS_TRUSTLINE_DIGEST, &scope, &draw)
                .unwrap(),
            "first burn is new"
        );
        assert!(
            !store
                .record_forever_digest(NS_TRUSTLINE_DIGEST, &scope, &draw)
                .unwrap(),
            "second burn is idempotent"
        );
        assert!(
            store
                .record_forever_digest(NS_COURT_RESOLVED, &[0u8; 32], &resolved)
                .unwrap()
        );
        // Drop: the simulated restart.
    }

    let store = PersistentStore::open(&path).expect("reopen store");
    assert!(
        store
            .forever_digest_seen(NS_TRUSTLINE_DIGEST, &scope, &draw)
            .unwrap(),
        "a burned draw digest survives the restart"
    );
    assert!(
        store
            .forever_digest_seen(NS_COURT_RESOLVED, &[0u8; 32], &resolved)
            .unwrap(),
        "a resolved-evidence digest survives the restart"
    );

    // Namespaces do not bleed: the same bytes under the other namespace are unseen.
    assert!(
        !store
            .forever_digest_seen(NS_COURT_RESOLVED, &scope, &draw)
            .unwrap()
    );
    assert!(
        !store
            .forever_digest_seen(NS_TRUSTLINE_DIGEST, &[0u8; 32], &resolved)
            .unwrap()
    );

    // Boot-time load returns exactly the namespace's pairs.
    let trustline_pairs = store.load_forever_digests(NS_TRUSTLINE_DIGEST).unwrap();
    assert_eq!(trustline_pairs, vec![(scope, draw)]);
    let court_pairs = store.load_forever_digests(NS_COURT_RESOLVED).unwrap();
    assert_eq!(court_pairs, vec![([0u8; 32], resolved)]);
}

#[test]
fn forever_digest_scopes_are_disjoint() {
    use crate::tables::NS_TRUSTLINE_DIGEST;

    let store = new_store();
    let digest = [0x77; 32];
    store
        .record_forever_digest(NS_TRUSTLINE_DIGEST, &[0xAA; 32], &digest)
        .unwrap();
    assert!(
        !store
            .forever_digest_seen(NS_TRUSTLINE_DIGEST, &[0xBB; 32], &digest)
            .unwrap(),
        "a digest burned against one trustline does not refuse another's"
    );
}

// =============================================================================
// Durable Channel Roster Tests (.docs-history-noclaude/PERSISTENCE.md §3, the roster caveat)
// =============================================================================

#[test]
fn channel_rosters_roundtrip_and_survive_reopen() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("rosters.redb");

    let channel_a = [0xA1; 32];
    let channel_b = [0xB2; 32];
    let roster_a = vec![1u8, 2, 3, 4];
    let roster_a2 = vec![9u8, 8, 7];
    let roster_b = vec![5u8, 6];

    {
        let store = PersistentStore::open(&path).expect("open store");
        store.store_channel_roster(&channel_a, &roster_a).unwrap();
        store.store_channel_roster(&channel_b, &roster_b).unwrap();
        // Upsert: a later epoch step overwrites.
        store.store_channel_roster(&channel_a, &roster_a2).unwrap();
        // Drop: the simulated restart.
    }

    let store = PersistentStore::open(&path).expect("reopen store");
    let mut loaded = store.load_channel_rosters().unwrap();
    loaded.sort();
    assert_eq!(
        loaded,
        vec![
            (channel_a, roster_a2.clone()),
            (channel_b, roster_b.clone())
        ]
    );

    // A stale roster's discard is durable.
    store.remove_channel_roster(&channel_a).unwrap();
    let loaded = store.load_channel_rosters().unwrap();
    assert_eq!(loaded, vec![(channel_b, roster_b)]);
}
