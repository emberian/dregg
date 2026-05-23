//! Write-Ahead Log for MerkleQueue durability.
//!
//! Every mutation is logged BEFORE being applied in-memory.
//! On crash recovery: replay the log to reconstruct state.

use std::fs::{self, File, OpenOptions};
use std::io::{self, BufRead, BufReader, BufWriter, Write};
use std::path::PathBuf;

/// Write-Ahead Log for MerkleQueue durability.
/// Every mutation is logged BEFORE being applied in-memory.
/// On crash recovery: replay the log to reconstruct state.
#[derive(Debug)]
pub struct WriteAheadLog {
    /// Path to the WAL file
    path: PathBuf,
    /// Buffered writer (fsync on commit)
    writer: Option<BufWriter<File>>,
    /// Sequence number (monotonically increasing)
    sequence: u64,
}

/// A single WAL entry representing a mutation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WalEntry {
    Enqueue {
        queue_id: [u8; 32],
        entry_hash: [u8; 32],
        data: Vec<u8>,
        sequence: u64,
    },
    Dequeue {
        queue_id: [u8; 32],
        position: usize,
        sequence: u64,
    },
    CreateQueue {
        queue_id: [u8; 32],
        capacity: usize,
        sequence: u64,
    },
    Checkpoint {
        queue_id: [u8; 32],
        root: [u8; 32],
        sequence: u64,
    },
}

impl WalEntry {
    /// Get the sequence number of this entry.
    pub fn sequence(&self) -> u64 {
        match self {
            WalEntry::Enqueue { sequence, .. } => *sequence,
            WalEntry::Dequeue { sequence, .. } => *sequence,
            WalEntry::CreateQueue { sequence, .. } => *sequence,
            WalEntry::Checkpoint { sequence, .. } => *sequence,
        }
    }

    /// Serialize to a line-based format with a checksum.
    /// Format: TYPE|hex_fields...|checksum\n
    fn serialize(&self) -> Vec<u8> {
        let payload = match self {
            WalEntry::Enqueue {
                queue_id,
                entry_hash,
                data,
                sequence,
            } => {
                format!(
                    "E|{}|{}|{}|{}",
                    hex_encode(queue_id),
                    hex_encode(entry_hash),
                    hex_encode(data),
                    sequence,
                )
            }
            WalEntry::Dequeue {
                queue_id,
                position,
                sequence,
            } => {
                format!("D|{}|{}|{}", hex_encode(queue_id), position, sequence,)
            }
            WalEntry::CreateQueue {
                queue_id,
                capacity,
                sequence,
            } => {
                format!("C|{}|{}|{}", hex_encode(queue_id), capacity, sequence,)
            }
            WalEntry::Checkpoint {
                queue_id,
                root,
                sequence,
            } => {
                format!(
                    "K|{}|{}|{}",
                    hex_encode(queue_id),
                    hex_encode(root),
                    sequence,
                )
            }
        };
        // Append a blake3 checksum of the payload for torn-write detection.
        let checksum = blake3::hash(payload.as_bytes());
        let line = format!("{}|{}\n", payload, hex_encode(checksum.as_bytes()));
        line.into_bytes()
    }

    /// Deserialize from a line. Returns None if the line is corrupt (bad checksum or parse error).
    fn deserialize(line: &str) -> Option<Self> {
        let line = line.trim_end_matches('\n');
        // Split off the last field as checksum.
        let last_pipe = line.rfind('|')?;
        let payload = &line[..last_pipe];
        let checksum_hex = &line[last_pipe + 1..];

        // Verify checksum.
        let expected_checksum = blake3::hash(payload.as_bytes());
        let expected_hex = hex_encode(expected_checksum.as_bytes());
        if checksum_hex != expected_hex {
            return None; // Torn write or corruption.
        }

        let parts: Vec<&str> = payload.split('|').collect();
        if parts.is_empty() {
            return None;
        }

        match parts[0] {
            "E" if parts.len() == 5 => {
                let queue_id = hex_decode_32(parts[1])?;
                let entry_hash = hex_decode_32(parts[2])?;
                let data = hex_decode_vec(parts[3])?;
                let sequence: u64 = parts[4].parse().ok()?;
                Some(WalEntry::Enqueue {
                    queue_id,
                    entry_hash,
                    data,
                    sequence,
                })
            }
            "D" if parts.len() == 4 => {
                let queue_id = hex_decode_32(parts[1])?;
                let position: usize = parts[2].parse().ok()?;
                let sequence: u64 = parts[3].parse().ok()?;
                Some(WalEntry::Dequeue {
                    queue_id,
                    position,
                    sequence,
                })
            }
            "C" if parts.len() == 4 => {
                let queue_id = hex_decode_32(parts[1])?;
                let capacity: usize = parts[2].parse().ok()?;
                let sequence: u64 = parts[3].parse().ok()?;
                Some(WalEntry::CreateQueue {
                    queue_id,
                    capacity,
                    sequence,
                })
            }
            "K" if parts.len() == 4 => {
                let queue_id = hex_decode_32(parts[1])?;
                let root = hex_decode_32(parts[2])?;
                let sequence: u64 = parts[3].parse().ok()?;
                Some(WalEntry::Checkpoint {
                    queue_id,
                    root,
                    sequence,
                })
            }
            _ => None,
        }
    }
}

impl WriteAheadLog {
    /// Open (or create) a WAL file at the given path.
    /// If the file already exists, the sequence number is derived from the last entry.
    pub fn open(path: PathBuf) -> io::Result<Self> {
        // Determine the current sequence from existing entries.
        let sequence = if path.exists() {
            let entries = Self::replay_from_path(&path)?;
            entries.last().map(|e| e.sequence() + 1).unwrap_or(0)
        } else {
            0
        };

        let file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&path)?;
        let writer = BufWriter::new(file);

        Ok(Self {
            path,
            writer: Some(writer),
            sequence,
        })
    }

    /// Append a WAL entry. The entry's sequence field is set by the WAL.
    pub fn append(&mut self, entry: &WalEntry) -> io::Result<()> {
        let writer = self
            .writer
            .as_mut()
            .ok_or_else(|| io::Error::other("WAL writer closed"))?;
        let serialized = entry.serialize();
        writer.write_all(&serialized)?;
        self.sequence += 1;
        Ok(())
    }

    /// Flush and fsync the WAL to durable storage.
    pub fn sync(&mut self) -> io::Result<()> {
        let writer = self
            .writer
            .as_mut()
            .ok_or_else(|| io::Error::other("WAL writer closed"))?;
        writer.flush()?;
        writer.get_ref().sync_all()
    }

    /// Replay all valid entries from the WAL file.
    /// Entries with bad checksums (torn writes) are skipped.
    pub fn replay(&self) -> io::Result<Vec<WalEntry>> {
        Self::replay_from_path(&self.path)
    }

    /// Truncate the WAL, removing all entries with sequence < the given value.
    /// This is called after a checkpoint to reclaim space.
    pub fn truncate_before(&mut self, sequence: u64) -> io::Result<()> {
        // Read all entries, keep only those with sequence >= the given value.
        let entries = self.replay()?;
        let kept: Vec<&WalEntry> = entries.iter().filter(|e| e.sequence() >= sequence).collect();

        // Close the writer, rewrite the file, reopen.
        self.writer = None;

        let file = OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(&self.path)?;
        let mut writer = BufWriter::new(file);

        for entry in &kept {
            let serialized = entry.serialize();
            writer.write_all(&serialized)?;
        }
        writer.flush()?;
        writer.get_ref().sync_all()?;

        // Reopen in append mode.
        drop(writer);
        let file = OpenOptions::new().append(true).open(&self.path)?;
        self.writer = Some(BufWriter::new(file));

        Ok(())
    }

    /// Write a checkpoint entry and return its sequence number.
    pub fn checkpoint(&mut self, queue_id: &[u8; 32], root: &[u8; 32]) -> io::Result<u64> {
        let seq = self.sequence;
        let entry = WalEntry::Checkpoint {
            queue_id: *queue_id,
            root: *root,
            sequence: seq,
        };
        self.append(&entry)?;
        self.sync()?;
        Ok(seq)
    }

    /// Get the next sequence number that will be assigned.
    pub fn next_sequence(&self) -> u64 {
        self.sequence
    }

    /// Replay from a given path (internal helper).
    fn replay_from_path(path: &PathBuf) -> io::Result<Vec<WalEntry>> {
        if !path.exists() {
            return Ok(Vec::new());
        }
        let file = File::open(path)?;
        let reader = BufReader::new(file);
        let mut entries = Vec::new();

        for line in reader.lines() {
            let line = line?;
            if line.is_empty() {
                continue;
            }
            // Skip corrupt/torn entries silently (they represent incomplete writes).
            if let Some(entry) = WalEntry::deserialize(&line) {
                entries.push(entry);
            }
        }

        Ok(entries)
    }

    /// Close the WAL (flush and drop writer).
    pub fn close(&mut self) -> io::Result<()> {
        if let Some(ref mut writer) = self.writer {
            writer.flush()?;
            writer.get_ref().sync_all()?;
        }
        self.writer = None;
        Ok(())
    }

    /// Delete the WAL file (for cleanup in tests).
    pub fn destroy(mut self) -> io::Result<()> {
        self.close()?;
        if self.path.exists() {
            fs::remove_file(&self.path)?;
        }
        Ok(())
    }
}

// ============================================================================
// Hex encoding helpers (no external dependency needed)
// ============================================================================

fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn hex_decode_32(s: &str) -> Option<[u8; 32]> {
    let bytes = hex_decode_vec(s)?;
    if bytes.len() != 32 {
        return None;
    }
    let mut arr = [0u8; 32];
    arr.copy_from_slice(&bytes);
    Some(arr)
}

fn hex_decode_vec(s: &str) -> Option<Vec<u8>> {
    if !s.len().is_multiple_of(2) {
        return None;
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).ok())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    fn temp_wal_path(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join("pyana_wal_tests");
        fs::create_dir_all(&dir).unwrap();
        dir.join(format!("{}.wal", name))
    }

    fn cleanup(path: &Path) {
        let _ = fs::remove_file(path);
    }

    #[test]
    fn wal_write_and_replay() {
        let path = temp_wal_path("write_replay");
        cleanup(&path);

        {
            let mut wal = WriteAheadLog::open(path.clone()).unwrap();
            let entry1 = WalEntry::CreateQueue {
                queue_id: [0xAA; 32],
                capacity: 100,
                sequence: wal.next_sequence(),
            };
            wal.append(&entry1).unwrap();

            let entry2 = WalEntry::Enqueue {
                queue_id: [0xAA; 32],
                entry_hash: [0xBB; 32],
                data: vec![1, 2, 3, 4, 5],
                sequence: wal.next_sequence(),
            };
            wal.append(&entry2).unwrap();
            wal.sync().unwrap();
        }
        // Writer dropped (simulates crash without close).

        // Replay should recover both entries.
        let wal = WriteAheadLog::open(path.clone()).unwrap();
        let entries = wal.replay().unwrap();
        assert_eq!(entries.len(), 2);

        match &entries[0] {
            WalEntry::CreateQueue {
                queue_id,
                capacity,
                sequence,
            } => {
                assert_eq!(queue_id, &[0xAA; 32]);
                assert_eq!(*capacity, 100);
                assert_eq!(*sequence, 0);
            }
            other => panic!("Expected CreateQueue, got {:?}", other),
        }

        match &entries[1] {
            WalEntry::Enqueue {
                queue_id,
                entry_hash,
                data,
                sequence,
            } => {
                assert_eq!(queue_id, &[0xAA; 32]);
                assert_eq!(entry_hash, &[0xBB; 32]);
                assert_eq!(data, &[1, 2, 3, 4, 5]);
                assert_eq!(*sequence, 1);
            }
            other => panic!("Expected Enqueue, got {:?}", other),
        }

        wal.destroy().unwrap();
    }

    #[test]
    fn wal_checkpoint_truncates_old_entries() {
        let path = temp_wal_path("checkpoint_truncate");
        cleanup(&path);

        let mut wal = WriteAheadLog::open(path.clone()).unwrap();

        // Write 5 entries.
        for i in 0..5u64 {
            let entry = WalEntry::Enqueue {
                queue_id: [0xAA; 32],
                entry_hash: [i as u8; 32],
                data: vec![i as u8],
                sequence: wal.next_sequence(),
            };
            wal.append(&entry).unwrap();
        }
        wal.sync().unwrap();

        // Checkpoint after sequence 3 (keep entries with seq >= 3).
        wal.truncate_before(3).unwrap();

        let entries = wal.replay().unwrap();
        assert_eq!(entries.len(), 2); // seq 3 and seq 4
        assert_eq!(entries[0].sequence(), 3);
        assert_eq!(entries[1].sequence(), 4);

        wal.destroy().unwrap();
    }

    #[test]
    fn wal_torn_write_recovery() {
        let path = temp_wal_path("torn_write");
        cleanup(&path);

        // Write a valid entry followed by a corrupt (torn) entry.
        {
            let mut wal = WriteAheadLog::open(path.clone()).unwrap();
            let entry = WalEntry::Enqueue {
                queue_id: [0x11; 32],
                entry_hash: [0x22; 32],
                data: vec![0xAA, 0xBB],
                sequence: wal.next_sequence(),
            };
            wal.append(&entry).unwrap();
            wal.sync().unwrap();
            wal.close().unwrap();
        }

        // Manually append a torn (incomplete) line to the file.
        {
            let mut file = OpenOptions::new().append(true).open(&path).unwrap();
            // This line has a bad checksum (simulates torn write).
            writeln!(file, "E|{0}|{0}|aabbcc|99|0000000000000000000000000000000000000000000000000000000000000000", hex_encode(&[0x33; 32])).unwrap();
        }

        // Replay should recover the valid entry and skip the torn one.
        let wal = WriteAheadLog::open(path.clone()).unwrap();
        let entries = wal.replay().unwrap();
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].sequence(), 0);

        wal.destroy().unwrap();
    }

    #[test]
    fn wal_dequeue_entry_serialization() {
        let path = temp_wal_path("dequeue_ser");
        cleanup(&path);

        let mut wal = WriteAheadLog::open(path.clone()).unwrap();
        let entry = WalEntry::Dequeue {
            queue_id: [0xCC; 32],
            position: 42,
            sequence: wal.next_sequence(),
        };
        wal.append(&entry).unwrap();
        wal.sync().unwrap();

        let entries = wal.replay().unwrap();
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0], entry);

        wal.destroy().unwrap();
    }

    #[test]
    fn wal_checkpoint_entry_serialization() {
        let path = temp_wal_path("checkpoint_ser");
        cleanup(&path);

        let mut wal = WriteAheadLog::open(path.clone()).unwrap();
        let seq = wal.next_sequence();
        let entry = WalEntry::Checkpoint {
            queue_id: [0xDD; 32],
            root: [0xEE; 32],
            sequence: seq,
        };
        wal.append(&entry).unwrap();
        wal.sync().unwrap();

        let entries = wal.replay().unwrap();
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0], entry);

        wal.destroy().unwrap();
    }
}
