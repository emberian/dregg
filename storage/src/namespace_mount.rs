//! Namespace mount: mount storage endpoints (inboxes, queues, topics) in the
//! governed namespace.
//!
//! Each mount point binds a path in the namespace to a storage primitive,
//! with a fee policy and capacity limits.

use crate::multi_asset::FeePolicy;

/// Mount configuration for storage endpoints in the governed namespace.
#[derive(Debug, Clone)]
pub struct StorageMount {
    /// Path in the namespace (e.g., "/inboxes/alice").
    pub path: String,
    /// What kind of storage this is.
    pub kind: StorageMountKind,
    /// Fee policy for this mount point.
    pub fee_policy: FeePolicy,
    /// Capacity limit (max entries).
    pub max_capacity: usize,
    /// Who can write (None = anyone with deposit, Some = whitelist).
    pub write_acl: Option<Vec<[u8; 32]>>,
}

/// The kind of storage mounted at a namespace path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StorageMountKind {
    /// Single-owner inbox (only owner reads).
    Inbox { owner: [u8; 32] },
    /// Pub-sub topic (publisher writes, subscribers read).
    PubSub {
        publisher: [u8; 32],
        max_subscribers: usize,
    },
    /// Shared queue (multiple writers, single consumer).
    WorkQueue { consumer: [u8; 32] },
    /// Broadcast (write-once, read-many, no consumption).
    Bulletin { moderator: [u8; 32] },
}

/// Errors from mount operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MountError {
    /// Invalid path (must start with '/').
    InvalidPath(String),
    /// Capacity must be > 0.
    ZeroCapacity,
    /// Writer not in ACL.
    WriteNotAuthorized { writer: [u8; 32] },
}

impl StorageMount {
    /// Create a new inbox mount.
    pub fn inbox(path: String, owner: [u8; 32], fee_policy: FeePolicy, max_capacity: usize) -> Result<Self, MountError> {
        Self::validate_path(&path)?;
        Self::validate_capacity(max_capacity)?;
        Ok(Self {
            path,
            kind: StorageMountKind::Inbox { owner },
            fee_policy,
            max_capacity,
            write_acl: None, // Anyone can write to an inbox (sender pays deposit).
        })
    }

    /// Create a new pub-sub topic mount.
    pub fn pubsub(
        path: String,
        publisher: [u8; 32],
        max_subscribers: usize,
        fee_policy: FeePolicy,
        max_capacity: usize,
    ) -> Result<Self, MountError> {
        Self::validate_path(&path)?;
        Self::validate_capacity(max_capacity)?;
        Ok(Self {
            path,
            kind: StorageMountKind::PubSub {
                publisher,
                max_subscribers,
            },
            fee_policy,
            max_capacity,
            write_acl: Some(vec![publisher]), // Only publisher can write.
        })
    }

    /// Create a new work queue mount.
    pub fn work_queue(
        path: String,
        consumer: [u8; 32],
        fee_policy: FeePolicy,
        max_capacity: usize,
        writers: Option<Vec<[u8; 32]>>,
    ) -> Result<Self, MountError> {
        Self::validate_path(&path)?;
        Self::validate_capacity(max_capacity)?;
        Ok(Self {
            path,
            kind: StorageMountKind::WorkQueue { consumer },
            fee_policy,
            max_capacity,
            write_acl: writers,
        })
    }

    /// Create a new bulletin mount.
    pub fn bulletin(
        path: String,
        moderator: [u8; 32],
        fee_policy: FeePolicy,
        max_capacity: usize,
    ) -> Result<Self, MountError> {
        Self::validate_path(&path)?;
        Self::validate_capacity(max_capacity)?;
        Ok(Self {
            path,
            kind: StorageMountKind::Bulletin { moderator },
            fee_policy,
            max_capacity,
            write_acl: Some(vec![moderator]), // Only moderator can write.
        })
    }

    /// Check whether a writer is authorized for this mount.
    pub fn is_writer_authorized(&self, writer: &[u8; 32]) -> bool {
        match &self.write_acl {
            None => true, // Open to anyone.
            Some(acl) => acl.contains(writer),
        }
    }

    /// Add a writer to the ACL. Creates the ACL if it doesn't exist.
    pub fn add_writer(&mut self, writer: [u8; 32]) {
        match &mut self.write_acl {
            Some(acl) => {
                if !acl.contains(&writer) {
                    acl.push(writer);
                }
            }
            None => {
                self.write_acl = Some(vec![writer]);
            }
        }
    }

    /// Remove a writer from the ACL.
    pub fn remove_writer(&mut self, writer: &[u8; 32]) {
        if let Some(acl) = &mut self.write_acl {
            acl.retain(|w| w != writer);
        }
    }

    fn validate_path(path: &str) -> Result<(), MountError> {
        if path.is_empty() || !path.starts_with('/') {
            return Err(MountError::InvalidPath(
                "path must start with '/'".to_string(),
            ));
        }
        Ok(())
    }

    fn validate_capacity(capacity: usize) -> Result<(), MountError> {
        if capacity == 0 {
            return Err(MountError::ZeroCapacity);
        }
        Ok(())
    }
}

/// A mirrored queue: the same MerkleQueue replicated across N relay operators.
/// Any K-of-N can reconstruct the full queue (erasure coded).
/// Reader can verify any mirror has the correct root (Merkle root matches).
#[derive(Debug, Clone)]
pub struct MirroredQueue {
    /// The canonical queue root (all mirrors must match).
    pub canonical_root: [u8; 32],
    /// The relay operators hosting mirrors.
    pub mirrors: Vec<MirrorOperator>,
    /// Erasure coding parameters: N total shards.
    pub erasure_n: usize,
    /// Erasure coding parameters: K required for reconstruction.
    pub erasure_k: usize,
}

/// A mirror operator hosting a shard of the queue.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MirrorOperator {
    /// Operator identity.
    pub operator_id: [u8; 32],
    /// Which erasure shard(s) this operator holds.
    pub shard_indices: Vec<usize>,
    /// Last confirmed sync height.
    pub synced_to: u64,
}

impl MirroredQueue {
    /// Create a new mirrored queue with the given erasure parameters.
    pub fn new(erasure_n: usize, erasure_k: usize) -> Self {
        Self {
            canonical_root: [0u8; 32],
            mirrors: Vec::new(),
            erasure_n,
            erasure_k,
        }
    }

    /// Set the canonical root (updated when the queue state changes).
    pub fn set_root(&mut self, root: [u8; 32]) {
        self.canonical_root = root;
    }

    /// Add a mirror operator.
    pub fn add_mirror(&mut self, op: MirrorOperator) {
        self.mirrors.push(op);
    }

    /// Remove a mirror operator by ID.
    pub fn remove_mirror(&mut self, op_id: &[u8; 32]) {
        self.mirrors.retain(|m| &m.operator_id != op_id);
    }

    /// Verify that a mirror operator's claimed root matches the canonical root.
    pub fn verify_mirror_root(&self, op_id: &[u8; 32], claimed_root: &[u8; 32]) -> bool {
        // First, check the operator exists.
        let exists = self.mirrors.iter().any(|m| &m.operator_id == op_id);
        if !exists {
            return false;
        }
        // Root must match.
        claimed_root == &self.canonical_root
    }

    /// Check whether reconstruction is possible given a set of available operators.
    /// Requires that the available operators collectively hold at least K distinct shards.
    pub fn can_reconstruct(&self, available_ops: &[[u8; 32]]) -> bool {
        let mut available_shards = std::collections::HashSet::new();

        for op_id in available_ops {
            if let Some(op) = self.mirrors.iter().find(|m| &m.operator_id == op_id) {
                for &shard in &op.shard_indices {
                    available_shards.insert(shard);
                }
            }
        }

        available_shards.len() >= self.erasure_k
    }

    /// Number of mirror operators.
    pub fn mirror_count(&self) -> usize {
        self.mirrors.len()
    }

    /// Total number of shards covered by all mirrors.
    pub fn total_shards_covered(&self) -> usize {
        let mut shards = std::collections::HashSet::new();
        for op in &self.mirrors {
            for &shard in &op.shard_indices {
                shards.insert(shard);
            }
        }
        shards.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::multi_asset::FeePolicy;

    #[test]
    fn inbox_mount_configuration() {
        let owner = [0x01; 32];
        let mount = StorageMount::inbox(
            "/inboxes/alice".to_string(),
            owner,
            FeePolicy::computrons_only(),
            100,
        )
        .unwrap();

        assert_eq!(mount.path, "/inboxes/alice");
        assert_eq!(mount.kind, StorageMountKind::Inbox { owner });
        assert_eq!(mount.max_capacity, 100);
        assert!(mount.write_acl.is_none()); // Open writes.

        // Anyone can write to an inbox.
        let random_writer = [0xFF; 32];
        assert!(mount.is_writer_authorized(&random_writer));
    }

    #[test]
    fn pubsub_mount_with_acl() {
        let publisher = [0x02; 32];
        let mount = StorageMount::pubsub(
            "/topics/prices".to_string(),
            publisher,
            50,
            FeePolicy::computrons_only(),
            1000,
        )
        .unwrap();

        assert_eq!(
            mount.kind,
            StorageMountKind::PubSub {
                publisher,
                max_subscribers: 50,
            }
        );

        // Only publisher is authorized to write.
        assert!(mount.is_writer_authorized(&publisher));
        let non_publisher = [0xFF; 32];
        assert!(!mount.is_writer_authorized(&non_publisher));
    }

    #[test]
    fn work_queue_mount_with_writer_whitelist() {
        let consumer = [0x03; 32];
        let writer1 = [0x10; 32];
        let writer2 = [0x20; 32];
        let mount = StorageMount::work_queue(
            "/queues/jobs".to_string(),
            consumer,
            FeePolicy::computrons_only(),
            500,
            Some(vec![writer1, writer2]),
        )
        .unwrap();

        assert_eq!(mount.kind, StorageMountKind::WorkQueue { consumer });
        assert!(mount.is_writer_authorized(&writer1));
        assert!(mount.is_writer_authorized(&writer2));

        let unauthorized = [0x99; 32];
        assert!(!mount.is_writer_authorized(&unauthorized));
    }

    #[test]
    fn invalid_path_rejected() {
        let result = StorageMount::inbox(
            "no-leading-slash".to_string(),
            [0x01; 32],
            FeePolicy::computrons_only(),
            10,
        );
        assert!(matches!(
            result,
            Err(MountError::InvalidPath(_))
        ));
    }

    #[test]
    fn zero_capacity_rejected() {
        let result = StorageMount::inbox(
            "/inboxes/test".to_string(),
            [0x01; 32],
            FeePolicy::computrons_only(),
            0,
        );
        assert!(matches!(result, Err(MountError::ZeroCapacity)));
    }

    #[test]
    fn mirrored_queue_verify_root() {
        let mut mq = MirroredQueue::new(5, 3);
        let root = *blake3::hash(b"queue state").as_bytes();
        mq.set_root(root);

        let op1 = MirrorOperator {
            operator_id: [0x01; 32],
            shard_indices: vec![0, 1],
            synced_to: 100,
        };
        let op2 = MirrorOperator {
            operator_id: [0x02; 32],
            shard_indices: vec![2, 3],
            synced_to: 100,
        };

        mq.add_mirror(op1);
        mq.add_mirror(op2);

        // Correct root verifies.
        assert!(mq.verify_mirror_root(&[0x01; 32], &root));
        assert!(mq.verify_mirror_root(&[0x02; 32], &root));

        // Wrong root fails.
        let bad_root = [0xFF; 32];
        assert!(!mq.verify_mirror_root(&[0x01; 32], &bad_root));

        // Unknown operator fails.
        assert!(!mq.verify_mirror_root(&[0x99; 32], &root));
    }

    #[test]
    fn mirrored_queue_can_reconstruct_with_k_of_n() {
        let mut mq = MirroredQueue::new(5, 3); // Need 3 shards to reconstruct.

        // 3 operators each holding different shards.
        mq.add_mirror(MirrorOperator {
            operator_id: [0x01; 32],
            shard_indices: vec![0, 1],
            synced_to: 100,
        });
        mq.add_mirror(MirrorOperator {
            operator_id: [0x02; 32],
            shard_indices: vec![2],
            synced_to: 100,
        });
        mq.add_mirror(MirrorOperator {
            operator_id: [0x03; 32],
            shard_indices: vec![3, 4],
            synced_to: 100,
        });

        // All 3 available: shards 0,1,2,3,4 -> 5 >= 3. Can reconstruct.
        assert!(mq.can_reconstruct(&[[0x01; 32], [0x02; 32], [0x03; 32]]));

        // Only op1 + op2 available: shards 0,1,2 -> 3 >= 3. Can reconstruct.
        assert!(mq.can_reconstruct(&[[0x01; 32], [0x02; 32]]));

        // Only op2 available: shards 2 -> 1 < 3. Cannot reconstruct.
        assert!(!mq.can_reconstruct(&[[0x02; 32]]));

        // Only op1 available: shards 0,1 -> 2 < 3. Cannot reconstruct.
        assert!(!mq.can_reconstruct(&[[0x01; 32]]));

        // Op1 + op3 available: shards 0,1,3,4 -> 4 >= 3. Can reconstruct.
        assert!(mq.can_reconstruct(&[[0x01; 32], [0x03; 32]]));

        // No operators: 0 < 3. Cannot.
        assert!(!mq.can_reconstruct(&[]));
    }

    #[test]
    fn add_remove_writer() {
        let mut mount = StorageMount::inbox(
            "/inboxes/test".to_string(),
            [0x01; 32],
            FeePolicy::computrons_only(),
            10,
        )
        .unwrap();

        // Initially open (no ACL).
        assert!(mount.write_acl.is_none());

        // Add a writer creates the ACL.
        let writer = [0x10; 32];
        mount.add_writer(writer);
        assert!(mount.is_writer_authorized(&writer));

        // Now there's an ACL, so others are blocked.
        let other = [0x20; 32];
        assert!(!mount.is_writer_authorized(&other));

        // Remove the writer.
        mount.remove_writer(&writer);
        // ACL exists but is empty -> no one authorized.
        assert!(!mount.is_writer_authorized(&writer));
    }
}
