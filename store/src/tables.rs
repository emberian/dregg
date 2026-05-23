//! Table definitions for the redb database.
//!
//! Each table is defined as a constant with a fixed name and typed key/value pairs.
//! redb uses these definitions to enforce type safety at the database level.

use redb::TableDefinition;

/// Token chain storage: token_id (32 bytes) -> serialized TokenChain.
///
/// Key: 32-byte token identifier (fixed-size).
/// Value: postcard-serialized `TokenChain` struct.
pub const TOKEN_CHAINS: TableDefinition<&[u8; 32], &[u8]> = TableDefinition::new("token_chains");

/// Revocation set: token_id (string) -> revocation timestamp.
///
/// Key: token ID as a string (variable length).
/// Value: i64 timestamp when the revocation was recorded.
pub const REVOCATIONS: TableDefinition<&str, i64> = TableDefinition::new("revocations");

/// Attested roots: height (u64) -> serialized StoredAttestedRoot.
///
/// Key: block height (monotonically increasing).
/// Value: postcard-serialized `StoredAttestedRoot` struct.
pub const ATTESTED_ROOTS: TableDefinition<u64, &[u8]> = TableDefinition::new("attested_roots");

/// Signing keys (encrypted): name (string) -> encrypted key blob.
///
/// Key: human-readable key name.
/// Value: encrypted key blob (nonce || ciphertext || tag).
pub const SIGNING_KEYS: TableDefinition<&str, &[u8]> = TableDefinition::new("signing_keys");

/// Public keys: name (string) -> 32-byte public key.
///
/// Key: human-readable key name.
/// Value: 32-byte raw public key.
pub const PUBLIC_KEYS: TableDefinition<&str, &[u8; 32]> = TableDefinition::new("public_keys");

/// Audit log: sequence number (u64) -> serialized StoredAuditEvent.
///
/// Key: monotonically increasing sequence number (0-based).
/// Value: postcard-serialized `StoredAuditEvent` struct.
pub const AUDIT_LOG: TableDefinition<u64, &[u8]> = TableDefinition::new("audit_log");

/// Audit token index: composite key (token_id_hex + sequence) -> sequence number.
///
/// This is a secondary index for looking up audit events by token ID.
/// Key: "{token_id_hex}:{sequence}" (string for range scanning).
/// Value: the global sequence number in the audit log.
pub const AUDIT_TOKEN_INDEX: TableDefinition<&str, u64> = TableDefinition::new("audit_token_index");

/// Metadata table for store-level counters and configuration.
///
/// Key: metadata key name.
/// Value: u64 value (used for counters like audit_sequence).
pub const METADATA: TableDefinition<&str, u64> = TableDefinition::new("metadata");

/// Note commitment tree: position (u64) -> 32-byte commitment hash.
///
/// Key: position in the append-only tree (0-based, monotonically increasing).
/// Value: 32-byte note commitment.
pub const NOTE_COMMITMENTS: TableDefinition<u64, &[u8; 32]> =
    TableDefinition::new("note_commitments");

/// Nullifier set: nullifier hash (32 bytes) -> unit (presence = spent).
///
/// Key: 32-byte nullifier hash.
/// Value: empty (presence in the table means the note is spent).
pub const NULLIFIERS: TableDefinition<&[u8; 32], ()> = TableDefinition::new("nullifiers");

/// Checkpoints: height (u64) -> serialized Checkpoint.
///
/// Key: checkpoint height (always a multiple of the checkpoint interval).
/// Value: postcard-serialized `pyana_federation::Checkpoint` struct.
pub const CHECKPOINTS: TableDefinition<u64, &[u8]> = TableDefinition::new("checkpoints");

/// Byte-blob metadata table for values that don't fit in a u64.
///
/// Key: metadata key name.
/// Value: arbitrary byte blob (e.g., cached Merkle roots).
pub const METADATA_BYTES: TableDefinition<&str, &[u8]> = TableDefinition::new("metadata_bytes");

// Metadata key constants.

/// Key for the next audit sequence number.
pub const META_AUDIT_NEXT_SEQ: &str = "audit_next_sequence";

/// Key for the latest attested root height.
pub const META_LATEST_ROOT_HEIGHT: &str = "latest_root_height";

/// Key for the note tree size (number of commitments).
pub const META_NOTE_TREE_SIZE: &str = "note_tree_size";

/// Key for the cached note tree root (stored in METADATA_BYTES).
pub const META_NOTE_TREE_ROOT_CACHE: &str = "note_tree_root_cache";

/// Key for the cached Poseidon2 note tree root (stored in METADATA_BYTES).
///
/// Stored as 4 bytes (little-endian u32) representing the BabyBear field element.
/// Updated on every `store_note_commitment` / `spend_note_atomic` call.
pub const META_POSEIDON2_NOTE_TREE_ROOT_CACHE: &str = "poseidon2_note_tree_root_cache";

/// Key for the latest checkpoint height.
pub const META_LATEST_CHECKPOINT_HEIGHT: &str = "latest_checkpoint_height";

/// Ledger checkpoints: height (u64) -> serialized LedgerCheckpoint.
///
/// Key: block height at which the checkpoint was taken.
/// Value: postcard-serialized `LedgerCheckpoint` struct (full ledger state snapshot).
pub const LEDGER_CHECKPOINTS: TableDefinition<u64, &[u8]> =
    TableDefinition::new("ledger_checkpoints");

/// Key for the latest ledger checkpoint height.
pub const META_LATEST_LEDGER_CHECKPOINT_HEIGHT: &str = "latest_ledger_checkpoint_height";

// ─── Blocklace Tables ──────────────────────────────────────────────────────

/// Blocklace blocks: block_id (32 bytes) -> serialized Block.
///
/// Key: 32-byte block ID (blake3 hash of signed content + signature).
/// Value: postcard-serialized `Block` struct.
pub const BLOCKLACE_BLOCKS: TableDefinition<&[u8; 32], &[u8]> =
    TableDefinition::new("blocklace_blocks");

/// Blocklace metadata: key (string) -> arbitrary bytes.
///
/// Stores tips, equivocators, ordering state, and other blocklace metadata.
/// Key: metadata key name (e.g., "meta").
/// Value: postcard-serialized `BlocklaceMeta` struct.
pub const BLOCKLACE_META: TableDefinition<&str, &[u8]> = TableDefinition::new("blocklace_meta");

/// Key for the blocklace metadata blob in the BLOCKLACE_META table.
pub const BLOCKLACE_META_KEY: &str = "meta";

/// Key for the executed_up_to index in the BLOCKLACE_META table.
pub const BLOCKLACE_EXECUTED_UP_TO_KEY: &str = "executed_up_to";
