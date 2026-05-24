//! Reed-Solomon erasure coding for data availability.
//!
//! Encode a blob into 2N chunks where any N suffice to reconstruct.
//! Light clients sample K random chunks. If all K are retrievable,
//! the full data is available with probability 1 - (1/2)^K.
//!
//! For pyana: when a blob is committed to the blocklace, it's erasure-encoded.
//! Phones (light clients) verify availability by sampling chunks from peers.
//! This proves "the data exists and is retrievable" without downloading it all.
//!
//! NOTE: This is a simplified prototype using XOR-based coding (not full Reed-Solomon).
//! Real deployment would use a proper RS library. The API is designed for the real thing.

use crate::ContentHash;

/// Encoder configuration.
#[derive(Debug, Clone)]
pub struct ErasureEncoder {
    /// Size of each data chunk in bytes.
    pub chunk_size: usize,
    /// Expansion factor: total_chunks = data_chunks * expansion_factor.
    /// With factor 2, any N of 2N chunks suffice.
    pub expansion_factor: usize,
}

/// A single erasure-coded chunk.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ErasureChunk {
    /// Index of this chunk in the encoded set.
    pub index: usize,
    /// The chunk data.
    pub data: Vec<u8>,
    /// Blake3 commitment of this chunk's data.
    pub commitment: [u8; 32],
    /// Whether this is an original data chunk or a parity chunk.
    pub is_parity: bool,
}

/// Error during reconstruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReconstructError {
    /// Not enough chunks to reconstruct.
    InsufficientChunks { have: usize, need: usize },
    /// Chunk data is corrupted (commitment mismatch).
    CorruptedChunk { index: usize },
    /// Invalid configuration.
    InvalidConfig(String),
}

impl ErasureEncoder {
    /// Create a new encoder with the given chunk size and expansion factor.
    pub fn new(chunk_size: usize, expansion_factor: usize) -> Self {
        Self {
            chunk_size,
            expansion_factor: expansion_factor.max(2),
        }
    }

    /// Encode data into erasure-coded chunks.
    /// Returns `data_chunks * expansion_factor` total chunks.
    pub fn encode(&self, data: &[u8]) -> Vec<ErasureChunk> {
        let mut chunks = Vec::new();

        // Split data into chunk_size pieces.
        let data_chunks: Vec<Vec<u8>> = data
            .chunks(self.chunk_size)
            .map(|c| {
                let mut v = c.to_vec();
                // Pad last chunk to chunk_size.
                v.resize(self.chunk_size, 0);
                v
            })
            .collect();

        let n_data = data_chunks.len();

        // Emit data chunks. Commitments route through the typed
        // Commitment<ErasureChunkMarker> framework (BLAKE3 + Poseidon2);
        // the on-disk wire form stays as a [u8; 32] BLAKE3 hash.
        for (i, chunk_data) in data_chunks.iter().enumerate() {
            let commitment = chunk_commitment_dual(chunk_data).blake3;
            chunks.push(ErasureChunk {
                index: i,
                data: chunk_data.clone(),
                commitment,
                is_parity: false,
            });
        }

        // Generate parity chunks (XOR-based for prototype).
        // For expansion_factor = 2, we generate N parity chunks.
        // Parity chunk i = XOR of all data chunks rotated by i positions.
        let n_parity = n_data * (self.expansion_factor - 1);
        for p in 0..n_parity {
            let mut parity = vec![0u8; self.chunk_size];
            // XOR scheme: parity[p] = XOR(data[j] for j where (j + p) % n_parity < n_data)
            // Simplified: each parity chunk XORs a different subset.
            for (j, data_chunk) in data_chunks.iter().enumerate() {
                // Use a rotation pattern to ensure recoverability.
                if (j + p) % self.expansion_factor == 0 || n_data <= 2 {
                    for (k, byte) in data_chunk.iter().enumerate() {
                        parity[k] ^= byte;
                    }
                }
            }
            let commitment = chunk_commitment_dual(&parity).blake3;
            chunks.push(ErasureChunk {
                index: n_data + p,
                data: parity,
                commitment,
                is_parity: true,
            });
        }

        chunks
    }

    /// Reconstruct original data from a subset of chunks.
    /// Requires at least `n_data_chunks` chunks (the number of original data chunks).
    pub fn reconstruct(
        &self,
        chunks: &[ErasureChunk],
        original_size: usize,
    ) -> Result<Vec<u8>, ReconstructError> {
        let n_data_chunks = original_size.div_ceil(self.chunk_size);

        // For prototype: we need all data chunks present.
        // A real RS implementation could reconstruct from any n_data of 2*n_data.
        // Here we check if we have enough data chunks directly.
        let mut data_chunks: Vec<Option<&ErasureChunk>> = vec![None; n_data_chunks];

        for chunk in chunks {
            if !chunk.is_parity && chunk.index < n_data_chunks {
                data_chunks[chunk.index] = Some(chunk);
            }
        }

        // Count available data chunks.
        let available_data: usize = data_chunks.iter().filter(|c| c.is_some()).count();
        let available_parity: usize = chunks.iter().filter(|c| c.is_parity).count();
        let total_available = available_data + available_parity;

        if total_available < n_data_chunks {
            return Err(ReconstructError::InsufficientChunks {
                have: total_available,
                need: n_data_chunks,
            });
        }

        // For prototype: if we have all data chunks, reconstruct directly.
        if available_data == n_data_chunks {
            let mut result = Vec::with_capacity(original_size);
            for opt_chunk in &data_chunks {
                let chunk = opt_chunk.unwrap();
                result.extend_from_slice(&chunk.data);
            }
            result.truncate(original_size);
            return Ok(result);
        }

        // Attempt XOR recovery for single missing chunk (prototype limitation).
        if available_data == n_data_chunks - 1 && available_parity >= 1 {
            // Find the missing chunk index.
            let missing_idx = data_chunks
                .iter()
                .position(|c| c.is_none())
                .unwrap();

            // XOR all available data chunks with the first parity chunk.
            let parity_chunk = chunks.iter().find(|c| c.is_parity).unwrap();
            let mut recovered = parity_chunk.data.clone();

            for chunk in data_chunks.iter().flatten() {
                for (k, byte) in chunk.data.iter().enumerate() {
                    recovered[k] ^= byte;
                }
            }

            // Assemble result.
            let mut result = Vec::with_capacity(original_size);
            for (i, opt_chunk) in data_chunks.iter().enumerate() {
                if i == missing_idx {
                    result.extend_from_slice(&recovered);
                } else {
                    result.extend_from_slice(&opt_chunk.unwrap().data);
                }
            }
            result.truncate(original_size);
            return Ok(result);
        }

        Err(ReconstructError::InsufficientChunks {
            have: total_available,
            need: n_data_chunks,
        })
    }
}

/// Verify that a chunk's data matches its commitment.
pub fn verify_chunk(chunk: &ErasureChunk) -> bool {
    chunk_commitment_dual(&chunk.data).blake3 == chunk.commitment
}

/// Dual-form commitment for a single erasure chunk's data.
pub fn chunk_commitment_dual(
    data: &[u8],
) -> crate::commitment::ErasureChunkCommitment {
    crate::commitment::Commitment::seal(data)
}

/// Compute the root commitment for a set of chunks.
///
/// Routes through Commitment<ErasureSetMarker>; returns the BLAKE3 form
/// wrapped in `ContentHash`. Dual-form via `root_commitment_dual`.
pub fn root_commitment(chunks: &[ErasureChunk]) -> ContentHash {
    ContentHash(root_commitment_dual(chunks).blake3)
}

/// Dual-form combined-root commitment for a set of erasure chunks.
pub fn root_commitment_dual(
    chunks: &[ErasureChunk],
) -> crate::commitment::ErasureSetCommitment {
    let mut canonical = Vec::with_capacity(chunks.len() * 32);
    for chunk in chunks {
        canonical.extend_from_slice(&chunk.commitment);
    }
    crate::commitment::Commitment::seal(&canonical[..])
}

/// Verify a chunk against a root commitment.
/// In a real implementation this would use a Merkle proof.
/// For prototype: just verify the chunk's own commitment is valid.
pub fn verify_chunk_against_root(chunk: &ErasureChunk, _root: &ContentHash) -> bool {
    // Prototype: just verify the chunk's own integrity.
    verify_chunk(chunk)
}

/// Calculate the probability that data is available given sampling results.
/// If we sample `sample_size` chunks from `total_chunks` and find `chunks_available`
/// of them present, what's the probability the full data is available?
///
/// Under the model: if >= 50% of chunks are available, data is reconstructable.
/// Probability that data is NOT available given all samples passed:
///   P(unavailable | all_samples_pass) ~ (available/total)^sample_size when available < threshold
///
/// Simplified: if all K sampled chunks are present, confidence = 1 - (1/2)^K
pub fn sample_availability(
    chunks_available: usize,
    total_chunks: usize,
    sample_size: usize,
) -> f64 {
    if total_chunks == 0 || sample_size == 0 {
        return 0.0;
    }
    if chunks_available >= total_chunks {
        return 1.0;
    }

    // The probability that a malicious actor hides >50% of data
    // but our K random samples all hit available chunks.
    // Worst case: exactly 50% available. Then P(all K hit available) = (1/2)^K.
    // Confidence = 1 - (1/2)^K assuming all samples passed.
    let availability_ratio = chunks_available as f64 / total_chunks as f64;
    if availability_ratio >= 0.5 {
        // If more than half are available, data is reconstructable (with RS codes).
        // Confidence based on sampling:
        1.0 - (1.0 - availability_ratio).powi(sample_size as i32)
    } else {
        // Less than half available — data is likely not reconstructable.
        availability_ratio.powi(sample_size as i32)
    }
}
