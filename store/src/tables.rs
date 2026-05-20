//! Table definitions for the redb database.
//!
//! Each table is defined as a constant with a fixed name and typed key/value pairs.
//! redb uses these definitions to enforce type safety at the database level.

use redb::TableDefinition;

/// Token chain storage: token_id (32 bytes) -> serialized TokenChain.
///
/// Key: 32-byte token identifier (fixed-size).
/// Value: postcard-serialized `TokenChain` struct.
pub const TOKEN_CHAINS: TableDefinition<&[u8; 32], &[u8]> =
    TableDefinition::new("token_chains");

/// Revocation set: token_id (string) -> revocation timestamp.
///
/// Key: token ID as a string (variable length).
/// Value: i64 timestamp when the revocation was recorded.
pub const REVOCATIONS: TableDefinition<&str, i64> =
    TableDefinition::new("revocations");

/// Attested roots: height (u64) -> serialized StoredAttestedRoot.
///
/// Key: block height (monotonically increasing).
/// Value: postcard-serialized `StoredAttestedRoot` struct.
pub const ATTESTED_ROOTS: TableDefinition<u64, &[u8]> =
    TableDefinition::new("attested_roots");

/// Signing keys (encrypted): name (string) -> encrypted key blob.
///
/// Key: human-readable key name.
/// Value: encrypted key blob (nonce || ciphertext || tag).
pub const SIGNING_KEYS: TableDefinition<&str, &[u8]> =
    TableDefinition::new("signing_keys");

/// Public keys: name (string) -> 32-byte public key.
///
/// Key: human-readable key name.
/// Value: 32-byte raw public key.
pub const PUBLIC_KEYS: TableDefinition<&str, &[u8; 32]> =
    TableDefinition::new("public_keys");

/// Audit log: sequence number (u64) -> serialized StoredAuditEvent.
///
/// Key: monotonically increasing sequence number (0-based).
/// Value: postcard-serialized `StoredAuditEvent` struct.
pub const AUDIT_LOG: TableDefinition<u64, &[u8]> =
    TableDefinition::new("audit_log");

/// Audit token index: composite key (token_id_hex + sequence) -> sequence number.
///
/// This is a secondary index for looking up audit events by token ID.
/// Key: "{token_id_hex}:{sequence}" (string for range scanning).
/// Value: the global sequence number in the audit log.
pub const AUDIT_TOKEN_INDEX: TableDefinition<&str, u64> =
    TableDefinition::new("audit_token_index");

/// Metadata table for store-level counters and configuration.
///
/// Key: metadata key name.
/// Value: u64 value (used for counters like audit_sequence).
pub const METADATA: TableDefinition<&str, u64> =
    TableDefinition::new("metadata");

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
pub const NULLIFIERS: TableDefinition<&[u8; 32], ()> =
    TableDefinition::new("nullifiers");

// Metadata key constants.

/// Key for the next audit sequence number.
pub const META_AUDIT_NEXT_SEQ: &str = "audit_next_sequence";

/// Key for the latest attested root height.
pub const META_LATEST_ROOT_HEIGHT: &str = "latest_root_height";

/// Key for the note tree size (number of commitments).
pub const META_NOTE_TREE_SIZE: &str = "note_tree_size";
