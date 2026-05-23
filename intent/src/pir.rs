//! Private Information Retrieval (PIR) for anonymous marketplace browsing.
//!
//! Enables private intent discovery: a client can query the intent pool's
//! inverted index (capability_tag -> [intent_ids]) without revealing which
//! capability tag they are looking for.
//!
//! # Modes
//!
//! Multiple PIR modes are supported for different deployment scenarios:
//!
//! - **TwoServer**: 2-server additive IT-PIR (information-theoretic, requires
//!   non-colluding servers). Post-quantum safe.
//! - **DownloadAll**: Client downloads the entire (encrypted) database and
//!   selects locally. Perfectly private, practical for small catalogs (<1000 items).
//! - **SingleServerPadded**: Single-server mode that pads the database and uses
//!   blinding to hide which item was queried. Weaker than IT-PIR but deployable
//!   without a second server.
//!
//! # Protocol (additive, 2-server)
//!
//! The intent pool is organized as an inverted index where rows are capability
//! tags and columns are intent IDs matching that tag. A querier wants row `i`
//! without either server learning `i`.
//!
//! 1. Client generates random vector `r` of length N (N = number of tags).
//! 2. Client sends `r` to Server A.
//! 3. Client sends `r XOR e_i` to Server B (e_i = unit vector with 1 at index i).
//! 4. Server A computes `response_a = Database^T * r` (matrix-vector product).
//! 5. Server B computes `response_b = Database^T * (r XOR e_i)`.
//! 6. Client computes `response_a XOR response_b = row_i` of the database.
//!
//! Since XOR over GF(2) doesn't work with BabyBear field arithmetic, we use
//! the additive variant: subtraction in BabyBear replaces XOR.
//!
//! # Size hiding
//!
//! The database is padded to the next power-of-2 number of rows before serving
//! queries. This prevents clients from learning the exact catalog size from the
//! `PirDatabaseInfo` metadata.
//!
//! # Batch queries
//!
//! Multiple items can be queried in a single PIR request via `BatchPirQuery`,
//! amortizing the per-query overhead for browsing use cases.
//!
//! # Security
//!
//! - Information-theoretic: each server sees a uniformly random vector.
//! - Requires non-collusion between the two servers (TwoServer mode).
//! - Post-quantum safe (no computational assumptions).
//! - Database size is hidden via power-of-2 padding.

use pyana_circuit::field::BabyBear;
use serde::{Deserialize, Serialize};

use crate::gossip::IntentPool;
use crate::{CommitmentId, Intent, MatchSpec};

// ---------------------------------------------------------------------------
// PIR mode selection
// ---------------------------------------------------------------------------

/// PIR operating mode, chosen based on deployment constraints.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum PirMode {
    /// 2-server information-theoretic PIR (existing protocol).
    /// Requires two non-colluding servers. Information-theoretically secure.
    TwoServer,
    /// Download the entire database encrypted and select locally.
    /// Perfectly private (server learns nothing, not even THAT you queried).
    /// Practical for small catalogs. `max_db_size` is the maximum number of
    /// rows the client is willing to download.
    DownloadAll { max_db_size: usize },
    /// Single-server mode with database padding and random blinding.
    /// The server learns that a query was made, but not which row was requested.
    /// Weaker than IT-PIR but avoids the two-server deployment constraint.
    SingleServerPadded,
}

impl Default for PirMode {
    fn default() -> Self {
        Self::TwoServer
    }
}

// ---------------------------------------------------------------------------
// Core PIR types
// ---------------------------------------------------------------------------

/// A PIR query vector sent to a single server.
///
/// For the 2-server additive IT-PIR protocol, the client generates two
/// complementary queries: one is a random vector `r`, the other is `e_i - r`
/// where `e_i` is the standard basis vector selecting the desired row.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PirQuery {
    /// The query vector (length = number of rows in the database).
    pub query_vector: Vec<BabyBear>,
}

/// A PIR response from a single server.
///
/// The server computes the inner product of each database column with the
/// query vector, producing one field element per column.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PirResponse {
    /// The server's response vector (length = number of columns per row).
    pub response: Vec<BabyBear>,
}

// ---------------------------------------------------------------------------
// Batch PIR types
// ---------------------------------------------------------------------------

/// A batch PIR query that retrieves multiple rows in a single request.
///
/// This amortizes the communication overhead when browsing multiple items
/// (e.g., "show me all items in category X" without revealing X).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BatchPirQuery {
    /// One query per requested row.
    pub queries: Vec<PirQuery>,
}

/// A batch PIR response containing multiple row results.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BatchPirResponse {
    /// One response per query in the batch.
    pub responses: Vec<PirResponse>,
}

// ---------------------------------------------------------------------------
// Single-server padded PIR types
// ---------------------------------------------------------------------------

/// A query for single-server padded PIR.
///
/// The client sends a query vector over the padded database. The server
/// computes the response over ALL rows (including padding) to prevent
/// timing side-channels. The blinding factor ensures the server cannot
/// distinguish real queries from noise.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SingleServerQuery {
    /// The query vector (length = padded database rows).
    pub query_vector: Vec<BabyBear>,
    /// A random blinding commitment. The client adds blinding to the query
    /// and subtracts it from the response, preventing the server from learning
    /// the raw result (which could reveal the query target via intersection
    /// attacks across multiple queries).
    pub blinding_commitment: [u8; 32],
}

/// Response to a single-server padded PIR query.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SingleServerResponse {
    /// The server's response (includes blinding contribution).
    pub response: Vec<BabyBear>,
}

// ---------------------------------------------------------------------------
// Download-all mode types
// ---------------------------------------------------------------------------

/// An encrypted snapshot of the entire database for download-all PIR.
///
/// The database is encrypted under a per-session key derived from a
/// Diffie-Hellman-like exchange (using BLAKE3 KDF), so the server cannot
/// observe which row the client reads after downloading.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EncryptedDatabase {
    /// The encrypted rows, each padded to uniform length.
    pub encrypted_rows: Vec<Vec<u8>>,
    /// The session nonce used for encryption (client and server both know this).
    pub session_nonce: [u8; 32],
    /// Number of real rows (the rest are padding). Deliberately NOT revealed
    /// to the client; all rows look identical after encryption.
    /// Only used server-side for bookkeeping.
    #[serde(skip)]
    pub real_row_count: usize,
}

// ---------------------------------------------------------------------------
// Inverted index over intent pool
// ---------------------------------------------------------------------------

/// Maximum number of intent IDs stored per tag bucket.
///
/// Rows are zero-padded to this width to prevent response-size leakage.
pub const MAX_INTENTS_PER_TAG: usize = 64;

/// Number of BabyBear field elements needed to encode one 32-byte intent ID.
///
/// We encode each byte as a separate field element (value 0..255, always < p)
/// to ensure lossless round-trip encoding/decoding. Using 4-byte packed encoding
/// (BabyBear::encode_hash) is lossy because values >= p get reduced mod p.
pub const ELEMENTS_PER_ID: usize = 32;

/// An inverted index over the intent pool, organized for PIR queries.
///
/// Each row corresponds to a capability tag (identified by a bucket index
/// derived from hashing the tag string). Each row contains up to
/// `MAX_INTENTS_PER_TAG` intent IDs (as `ELEMENTS_PER_ID` BabyBear field
/// elements each, one byte per element for lossless encoding).
#[derive(Clone, Debug)]
pub struct IntentIndex {
    /// The capability tag strings, in bucket order.
    pub tags: Vec<String>,
    /// Database matrix: `entries[row][col]` is a BabyBear field element.
    /// Each row has `MAX_INTENTS_PER_TAG * ELEMENTS_PER_ID` columns.
    pub entries: Vec<Vec<BabyBear>>,
}

/// The width of each row in the PIR database (in field elements).
/// Each intent ID is 32 bytes = 32 BabyBear elements (one byte per element),
/// times max intents per tag.
pub const ROW_WIDTH: usize = MAX_INTENTS_PER_TAG * ELEMENTS_PER_ID;

impl IntentIndex {
    /// Build an inverted index from the intent pool.
    ///
    /// Extracts capability tags from each intent's `MatchSpec` and organizes
    /// them into a fixed-width matrix suitable for PIR queries.
    pub fn build(pool: &IntentPool, now: u64) -> Self {
        // Collect all intents and extract their capability tags.
        let active = pool.active_intents(now);
        let mut tag_to_intents: std::collections::HashMap<String, Vec<[u8; 32]>> =
            std::collections::HashMap::new();

        for intent in &active {
            let tags = extract_capability_tags(&intent.matcher);
            for tag in tags {
                tag_to_intents.entry(tag).or_default().push(intent.id);
            }
        }

        // Sort tags for deterministic ordering.
        let mut tags: Vec<String> = tag_to_intents.keys().cloned().collect();
        tags.sort();

        // Build the matrix: each row is ROW_WIDTH field elements.
        let entries: Vec<Vec<BabyBear>> = tags
            .iter()
            .map(|tag| {
                let intent_ids = tag_to_intents.get(tag).unwrap();
                let mut row = vec![BabyBear::ZERO; ROW_WIDTH];
                for (idx, id) in intent_ids.iter().take(MAX_INTENTS_PER_TAG).enumerate() {
                    for (j, &byte) in id.iter().enumerate() {
                        row[idx * ELEMENTS_PER_ID + j] = BabyBear::new(byte as u32);
                    }
                }
                row
            })
            .collect();

        Self { tags, entries }
    }

    /// Build an index directly from a slice of intents (useful for testing
    /// and for nodes that maintain their own pool representation).
    pub fn build_from_intents(intents: &[Intent]) -> Self {
        let mut tag_to_intents: std::collections::HashMap<String, Vec<[u8; 32]>> =
            std::collections::HashMap::new();

        for intent in intents {
            let tags = extract_capability_tags(&intent.matcher);
            for tag in tags {
                tag_to_intents.entry(tag).or_default().push(intent.id);
            }
        }

        let mut tags: Vec<String> = tag_to_intents.keys().cloned().collect();
        tags.sort();

        let entries: Vec<Vec<BabyBear>> = tags
            .iter()
            .map(|tag| {
                let intent_ids = tag_to_intents.get(tag).unwrap();
                let mut row = vec![BabyBear::ZERO; ROW_WIDTH];
                for (idx, id) in intent_ids.iter().take(MAX_INTENTS_PER_TAG).enumerate() {
                    for (j, &byte) in id.iter().enumerate() {
                        row[idx * ELEMENTS_PER_ID + j] = BabyBear::new(byte as u32);
                    }
                }
                row
            })
            .collect();

        Self { tags, entries }
    }

    /// Get the number of rows (tags) in the index.
    pub fn num_rows(&self) -> usize {
        self.entries.len()
    }

    /// Get the row width (columns per row) in field elements.
    pub fn row_width(&self) -> usize {
        ROW_WIDTH
    }

    /// Look up the index of a tag in the index.
    /// Returns `None` if the tag is not present.
    pub fn tag_index(&self, tag: &str) -> Option<usize> {
        self.tags.iter().position(|t| t == tag)
    }
}

/// Extract capability tags from a MatchSpec.
///
/// Tags are derived from:
/// - Action patterns: each `action` field becomes a tag.
/// - Constraints: Service and Feature constraints become tags.
/// - Resource patterns become tags.
fn extract_capability_tags(spec: &MatchSpec) -> Vec<String> {
    let mut tags = Vec::new();

    for ap in &spec.actions {
        if let Some(ref action) = ap.action {
            tags.push(format!("action:{action}"));
        }
        if let Some(ref resource) = ap.resource {
            tags.push(format!("resource:{resource}"));
        }
    }

    for constraint in &spec.constraints {
        match constraint {
            crate::Constraint::Service(s) => tags.push(format!("service:{s}")),
            crate::Constraint::Feature(f) => tags.push(format!("feature:{f}")),
            crate::Constraint::AppId(a) => tags.push(format!("app:{a}")),
            crate::Constraint::OAuthProvider(p) => tags.push(format!("oauth:{p}")),
            _ => {}
        }
    }

    if let Some(ref pattern) = spec.resource_pattern {
        tags.push(format!("pattern:{pattern}"));
    }

    tags
}

// ---------------------------------------------------------------------------
// Client-side: query generation and response reconstruction
// ---------------------------------------------------------------------------

/// Generate a pair of PIR queries for the 2-server additive IT-PIR protocol.
///
/// Given the target row index `i` and the database size (number of rows),
/// produces two query vectors `(q_a, q_b)` such that:
/// - `q_a` is uniformly random.
/// - `q_b = e_i - q_a` (where e_i has BabyBear::ONE at position i, ZERO elsewhere).
/// - Neither vector alone reveals `i`.
///
/// # Panics
///
/// Panics if `index >= database_rows`.
pub fn generate_pir_queries(index: usize, database_rows: usize) -> (PirQuery, PirQuery) {
    assert!(
        index < database_rows,
        "PIR query index {index} out of bounds (database has {database_rows} rows)"
    );

    // Generate random vector r.
    let mut random_bytes = vec![0u8; database_rows * 4];
    crate::getrandom(&mut random_bytes);

    let r: Vec<BabyBear> = random_bytes
        .chunks(4)
        .map(|chunk| {
            let val = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
            BabyBear::new(val)
        })
        .collect();

    // Compute e_i - r: standard basis vector minus r.
    let mut q_b_vec: Vec<BabyBear> = r.iter().map(|&ri| BabyBear::ZERO - ri).collect();
    // Add 1 at position i: (e_i - r)[i] = 1 - r[i], others = 0 - r[j] = -r[j].
    q_b_vec[index] = q_b_vec[index] + BabyBear::ONE;

    let q_a = PirQuery { query_vector: r };
    let q_b = PirQuery {
        query_vector: q_b_vec,
    };

    (q_a, q_b)
}

/// Combine two PIR responses to reconstruct the queried database row.
///
/// The reconstruction is simply: `result = response_a + response_b` (addition
/// in BabyBear). This works because:
///
/// ```text
/// response_a = D^T * r
/// response_b = D^T * (e_i - r)
/// response_a + response_b = D^T * (r + e_i - r) = D^T * e_i = row_i
/// ```
pub fn combine_pir_responses(resp_a: &PirResponse, resp_b: &PirResponse) -> Vec<BabyBear> {
    assert_eq!(
        resp_a.response.len(),
        resp_b.response.len(),
        "PIR responses must have equal length"
    );

    resp_a
        .response
        .iter()
        .zip(resp_b.response.iter())
        .map(|(&a, &b)| a + b)
        .collect()
}

/// Decode a PIR result (vector of BabyBear elements) back into intent IDs.
///
/// Each intent ID is encoded as `ELEMENTS_PER_ID` (32) consecutive BabyBear
/// elements, one byte per element. Zero-padded entries (all-zero ID) are
/// filtered out.
pub fn decode_intent_ids(row: &[BabyBear]) -> Vec<[u8; 32]> {
    let mut ids = Vec::new();
    for chunk in row.chunks(ELEMENTS_PER_ID) {
        if chunk.len() < ELEMENTS_PER_ID {
            break;
        }
        let mut id = [0u8; 32];
        for (i, &elem) in chunk.iter().enumerate() {
            id[i] = elem.as_u32() as u8;
        }
        // Filter out zero-padded entries.
        if id != [0u8; 32] {
            ids.push(id);
        }
    }
    ids
}

// ---------------------------------------------------------------------------
// Server-side: PIR response computation
// ---------------------------------------------------------------------------

/// Compute a PIR response for a given query against a database (the intent index).
///
/// Performs the matrix-vector product: for each column j, compute
/// `response[j] = sum_i(query[i] * database[i][j])`.
///
/// This is the server's core computation. It must touch ALL rows to prevent
/// leaking information about which row the client wants.
pub fn compute_pir_response(query: &PirQuery, database: &[Vec<BabyBear>]) -> PirResponse {
    let num_rows = database.len();
    assert_eq!(
        query.query_vector.len(),
        num_rows,
        "Query vector length ({}) must match database rows ({num_rows})",
        query.query_vector.len()
    );

    if num_rows == 0 {
        return PirResponse {
            response: Vec::new(),
        };
    }

    let row_width = database[0].len();
    let mut response = vec![BabyBear::ZERO; row_width];

    // SECURITY: We must process ALL rows unconditionally to prevent timing
    // side-channels that would leak which row the client queried. Skipping
    // zero-valued query elements would allow an observer to infer the query
    // structure from response latency variations.
    for (row_idx, row) in database.iter().enumerate() {
        let qi = query.query_vector[row_idx];
        for (col_idx, &elem) in row.iter().enumerate() {
            response[col_idx] = response[col_idx] + qi * elem;
        }
    }

    PirResponse { response }
}

// ---------------------------------------------------------------------------
// Batch PIR: query multiple rows in one request
// ---------------------------------------------------------------------------

/// Generate a batch of PIR queries for multiple target rows (2-server mode).
///
/// Each row gets its own independent query pair. The batch amortizes the
/// communication setup overhead (one network round-trip for N rows).
pub fn generate_batch_pir_queries(
    indices: &[usize],
    database_rows: usize,
) -> (BatchPirQuery, BatchPirQuery) {
    let mut queries_a = Vec::with_capacity(indices.len());
    let mut queries_b = Vec::with_capacity(indices.len());

    for &idx in indices {
        let (q_a, q_b) = generate_pir_queries(idx, database_rows);
        queries_a.push(q_a);
        queries_b.push(q_b);
    }

    (
        BatchPirQuery {
            queries: queries_a,
        },
        BatchPirQuery {
            queries: queries_b,
        },
    )
}

/// Compute batch PIR responses (server-side).
pub fn compute_batch_pir_response(
    batch: &BatchPirQuery,
    database: &[Vec<BabyBear>],
) -> BatchPirResponse {
    let responses = batch
        .queries
        .iter()
        .map(|q| compute_pir_response(q, database))
        .collect();
    BatchPirResponse { responses }
}

/// Combine batch PIR responses to reconstruct multiple rows.
pub fn combine_batch_pir_responses(
    batch_a: &BatchPirResponse,
    batch_b: &BatchPirResponse,
) -> Vec<Vec<BabyBear>> {
    assert_eq!(
        batch_a.responses.len(),
        batch_b.responses.len(),
        "Batch response counts must match"
    );
    batch_a
        .responses
        .iter()
        .zip(batch_b.responses.iter())
        .map(|(a, b)| combine_pir_responses(a, b))
        .collect()
}

// ---------------------------------------------------------------------------
// Single-server padded PIR
// ---------------------------------------------------------------------------

/// Generate a single-server PIR query with blinding.
///
/// In single-server mode, the client adds a random blinding vector to the
/// standard basis vector, making the query look random to the server. The
/// client tracks the blinding locally and subtracts the server's contribution
/// from the blinding during reconstruction.
///
/// Security: This hides WHICH row was queried but does NOT provide
/// information-theoretic security. A computationally unbounded server could
/// potentially recover the query. It is suitable for deployments where a
/// second non-colluding server is unavailable.
///
/// Returns `(query, blinding_vector)` where the blinding_vector must be kept
/// secret by the client for response reconstruction.
pub fn generate_single_server_query(
    index: usize,
    padded_rows: usize,
) -> (SingleServerQuery, Vec<BabyBear>) {
    assert!(
        index < padded_rows,
        "PIR query index {index} out of bounds (padded database has {padded_rows} rows)"
    );

    // Generate random blinding vector.
    let mut random_bytes = vec![0u8; padded_rows * 4];
    crate::getrandom(&mut random_bytes);

    let blinding: Vec<BabyBear> = random_bytes
        .chunks(4)
        .map(|chunk| {
            let val = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
            BabyBear::new(val)
        })
        .collect();

    // Query = e_i + blinding (the server cannot distinguish from random).
    let mut query_vector = blinding.clone();
    query_vector[index] = query_vector[index] + BabyBear::ONE;

    // Commitment to the blinding (for the server to log/audit if needed).
    let blinding_bytes: Vec<u8> = blinding
        .iter()
        .flat_map(|e| e.as_u32().to_le_bytes())
        .collect();
    let blinding_commitment = *blake3::hash(&blinding_bytes).as_bytes();

    let query = SingleServerQuery {
        query_vector,
        blinding_commitment,
    };

    (query, blinding)
}

/// Compute a single-server PIR response.
///
/// The server computes `D^T * query_vector` over all rows (including padding)
/// to prevent timing leakage.
pub fn compute_single_server_response(
    query: &SingleServerQuery,
    database: &[Vec<BabyBear>],
) -> SingleServerResponse {
    let num_rows = database.len();
    assert_eq!(
        query.query_vector.len(),
        num_rows,
        "Query vector length ({}) must match database rows ({num_rows})",
        query.query_vector.len()
    );

    if num_rows == 0 {
        return SingleServerResponse {
            response: Vec::new(),
        };
    }

    let row_width = database[0].len();
    let mut response = vec![BabyBear::ZERO; row_width];

    for (row_idx, row) in database.iter().enumerate() {
        let qi = query.query_vector[row_idx];
        for (col_idx, &elem) in row.iter().enumerate() {
            response[col_idx] = response[col_idx] + qi * elem;
        }
    }

    SingleServerResponse { response }
}

/// Reconstruct the queried row from a single-server response.
///
/// The client subtracts the blinding contribution: `result = response - D^T * blinding`.
/// Since `response = D^T * (e_i + blinding) = row_i + D^T * blinding`, we get
/// `result = row_i`.
///
/// The client must supply the blinding vector AND the database entries to compute
/// `D^T * blinding`. In practice, the client requests a commitment to the database
/// state (Merkle root) and can verify consistency.
///
/// For efficiency, the client can precompute `D^T * blinding` if they have a local
/// copy of the database (which they might in download-all mode). Otherwise, this
/// function takes the server's response and the blinding contribution.
pub fn reconstruct_single_server(
    response: &SingleServerResponse,
    blinding_contribution: &[BabyBear],
) -> Vec<BabyBear> {
    assert_eq!(
        response.response.len(),
        blinding_contribution.len(),
        "Response and blinding contribution must have equal length"
    );
    response
        .response
        .iter()
        .zip(blinding_contribution.iter())
        .map(|(&r, &b)| r - b)
        .collect()
}

/// Compute the blinding contribution `D^T * blinding_vector`.
///
/// This is needed by the client to subtract the blinding from the server's response.
/// In the single-server model, the client computes this locally using a cached
/// or previously-downloaded copy of the database.
pub fn compute_blinding_contribution(
    blinding: &[BabyBear],
    database: &[Vec<BabyBear>],
) -> Vec<BabyBear> {
    let num_rows = database.len();
    assert_eq!(
        blinding.len(),
        num_rows,
        "Blinding vector length must match database rows"
    );
    if num_rows == 0 {
        return Vec::new();
    }
    let row_width = database[0].len();
    let mut contribution = vec![BabyBear::ZERO; row_width];
    for (row_idx, row) in database.iter().enumerate() {
        let bi = blinding[row_idx];
        for (col_idx, &elem) in row.iter().enumerate() {
            contribution[col_idx] = contribution[col_idx] + bi * elem;
        }
    }
    contribution
}

// ---------------------------------------------------------------------------
// Anonymous intent posting (unlinkable commitment IDs)
// ---------------------------------------------------------------------------

/// Generate a fresh, unlinkable `CommitmentId` for each intent.
///
/// Uses a monotonic nonce to derive unique commitment IDs from the same secret,
/// ensuring that multiple intents from the same wallet are not linkable.
///
/// The derivation is: `BLAKE3-derive-key("pyana-intent-commitment-{nonce}", secret)`.
pub fn derive_unlinkable_commitment(secret: &[u8], nonce: u64) -> CommitmentId {
    CommitmentId::derive(secret, &format!("pyana-intent-commitment-{nonce}"))
}

// ---------------------------------------------------------------------------
// Private marketplace browsing client
// ---------------------------------------------------------------------------

/// A listing commitment as stored in the PIR database.
/// This is an opaque identifier that can be resolved to listing details
/// via a separate (also private) lookup.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ListingCommitment {
    /// The content-addressed ID of the listing (BLAKE3 hash).
    pub id: [u8; 32],
}

/// An encrypted listing returned from a private detail lookup.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EncryptedListing {
    /// Ciphertext of the listing details, encrypted to the requester's
    /// ephemeral session key.
    pub ciphertext: Vec<u8>,
    /// Nonce used for the encryption.
    pub nonce: [u8; 32],
}

/// Client for private marketplace browsing using PIR.
///
/// Wraps the PIR primitives to provide a marketplace-oriented API.
/// Supports all three PIR modes and handles database padding transparently.
#[derive(Clone, Debug)]
pub struct PrivateBrowseClient {
    /// The PIR mode in use.
    pub mode: PirMode,
    /// Cached database info from the server.
    db_info: Option<PirDatabaseInfo>,
    /// For download-all mode: the locally-cached encrypted database.
    cached_db: Option<EncryptedDatabase>,
    /// Session secret for download-all decryption.
    session_secret: Option<[u8; 32]>,
    /// Nonce counter for unlinkable commitment generation.
    nonce_counter: u64,
    /// The client's browsing secret (for deriving unlinkable commitments).
    browsing_secret: [u8; 32],
}

impl PrivateBrowseClient {
    /// Create a new private browse client with the specified mode.
    pub fn new(mode: PirMode) -> Self {
        let mut browsing_secret = [0u8; 32];
        crate::getrandom(&mut browsing_secret);
        Self {
            mode,
            db_info: None,
            cached_db: None,
            session_secret: None,
            nonce_counter: 0,
            browsing_secret,
        }
    }

    /// Create a client with a known browsing secret (for deterministic testing).
    pub fn with_secret(mode: PirMode, secret: [u8; 32]) -> Self {
        Self {
            mode,
            db_info: None,
            cached_db: None,
            session_secret: None,
            nonce_counter: 0,
            browsing_secret: secret,
        }
    }

    /// Set the database info (received from server).
    pub fn set_db_info(&mut self, info: PirDatabaseInfo) {
        self.db_info = Some(info);
    }

    /// Set the cached encrypted database (for download-all mode).
    pub fn set_cached_db(&mut self, db: EncryptedDatabase, session_secret: [u8; 32]) {
        self.cached_db = Some(db);
        self.session_secret = Some(session_secret);
    }

    /// Look up a category in the database info and return the row index.
    /// The category is hashed to match against tag commitments.
    pub fn find_category(&self, category: &str) -> Option<usize> {
        self.db_info.as_ref()?.find_tag_index(category)
    }

    /// Browse a category: returns listing commitments for the given category hash.
    ///
    /// For download-all mode, decrypts locally. For other modes, returns None
    /// (the caller must use the PIR query functions and supply server responses).
    pub fn browse_category_local(&self, category: &str) -> Option<Vec<ListingCommitment>> {
        let info = self.db_info.as_ref()?;
        let row_idx = info.find_tag_index(category)?;

        match &self.mode {
            PirMode::DownloadAll { .. } => {
                let db = self.cached_db.as_ref()?;
                let secret = self.session_secret.as_ref()?;
                let row = db.decrypt_row(row_idx, secret)?;
                let ids = decode_intent_ids(&row);
                Some(ids.into_iter().map(|id| ListingCommitment { id }).collect())
            }
            _ => None, // Requires network interaction for TwoServer/SingleServerPadded
        }
    }

    /// Generate a fresh unlinkable commitment for posting an intent.
    pub fn next_commitment(&mut self) -> CommitmentId {
        let commitment =
            derive_unlinkable_commitment(&self.browsing_secret, self.nonce_counter);
        self.nonce_counter += 1;
        commitment
    }

    /// Get the current PIR mode.
    pub fn mode(&self) -> &PirMode {
        &self.mode
    }

    /// Check whether the download-all mode is practical for the given database.
    pub fn is_download_all_practical(info: &PirDatabaseInfo) -> bool {
        match &info.mode {
            PirMode::DownloadAll { max_db_size } => info.num_rows <= *max_db_size,
            _ => false,
        }
    }
}

// ---------------------------------------------------------------------------
// High-level discovery API
// ---------------------------------------------------------------------------

/// Metadata about the PIR database, shared with clients so they can construct
/// valid queries.
///
/// **Size hiding**: The `num_rows` field reports the *padded* size (a power of 2),
/// not the real number of tags. This prevents clients from learning exact catalog
/// size from metadata alone.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PirDatabaseInfo {
    /// Number of rows in the padded database (always a power of 2).
    /// This is >= the real number of tags.
    pub num_rows: usize,
    /// Number of columns per row (in BabyBear field elements).
    pub row_width: usize,
    /// BLAKE3 commitments of each tag, in bucket order, padded with random
    /// commitments for dummy rows.
    ///
    /// Instead of revealing plaintext tags (which leaks available capabilities to
    /// the server), we provide `BLAKE3(tag)` for each row. The client must know
    /// the tag they are looking for, hash it locally, and find the matching index.
    /// This prevents the server from learning which tags exist without already
    /// knowing them.
    ///
    /// Dummy rows have random commitments that will never match a real tag hash,
    /// making them indistinguishable from real rows to the client.
    pub tag_commitments: Vec<[u8; 32]>,
    /// The PIR mode this database is configured for.
    pub mode: PirMode,
}

impl PirDatabaseInfo {
    /// Find the row index for a known tag by hashing it and scanning commitments.
    ///
    /// The client must know the tag string they want to query. They hash it locally
    /// and compare against the committed list to find the index for PIR query
    /// generation. Returns `None` if the tag is not present.
    pub fn find_tag_index(&self, tag: &str) -> Option<usize> {
        let commitment = *blake3::hash(tag.as_bytes()).as_bytes();
        self.tag_commitments.iter().position(|c| *c == commitment)
    }
}

impl From<&IntentIndex> for PirDatabaseInfo {
    fn from(index: &IntentIndex) -> Self {
        let tag_commitments = index
            .tags
            .iter()
            .map(|tag| *blake3::hash(tag.as_bytes()).as_bytes())
            .collect();
        Self {
            num_rows: index.num_rows(),
            row_width: index.row_width(),
            tag_commitments,
            mode: PirMode::TwoServer,
        }
    }
}

/// Compute the next power of 2 >= n (minimum 1).
fn next_power_of_two(n: usize) -> usize {
    if n == 0 {
        return 1;
    }
    n.next_power_of_two()
}

/// A size-padded PIR database that hides the real number of rows.
///
/// Pads the database to a power-of-2 number of rows with zero-filled dummy
/// rows and random tag commitments. Queries against dummy rows return all-zero
/// results (which decode to no intent IDs).
#[derive(Clone, Debug)]
pub struct PaddedDatabase {
    /// The padded database entries (power-of-2 number of rows).
    pub entries: Vec<Vec<BabyBear>>,
    /// Tag commitments including random dummy commitments for padding rows.
    pub tag_commitments: Vec<[u8; 32]>,
    /// The padded row count (power of 2).
    pub padded_rows: usize,
    /// The PIR mode.
    pub mode: PirMode,
}

impl PaddedDatabase {
    /// Create a padded database from an IntentIndex.
    ///
    /// The database is padded to the next power of 2 with zero-filled rows
    /// and random tag commitments for the padding entries.
    pub fn from_index(index: &IntentIndex, mode: PirMode) -> Self {
        let real_rows = index.num_rows();
        let padded_rows = next_power_of_two(real_rows);

        let mut entries = index.entries.clone();
        let mut tag_commitments: Vec<[u8; 32]> = index
            .tags
            .iter()
            .map(|tag| *blake3::hash(tag.as_bytes()).as_bytes())
            .collect();

        // Pad with dummy rows.
        let padding_needed = padded_rows - real_rows;
        if padding_needed > 0 {
            // Generate random commitments for dummy rows.
            let mut random_bytes = vec![0u8; padding_needed * 32];
            crate::getrandom(&mut random_bytes);

            for i in 0..padding_needed {
                entries.push(vec![BabyBear::ZERO; ROW_WIDTH]);
                let mut commitment = [0u8; 32];
                commitment.copy_from_slice(&random_bytes[i * 32..(i + 1) * 32]);
                tag_commitments.push(commitment);
            }
        }

        Self {
            entries,
            tag_commitments,
            padded_rows,
            mode,
        }
    }

    /// Get the database info to share with clients.
    pub fn info(&self) -> PirDatabaseInfo {
        PirDatabaseInfo {
            num_rows: self.padded_rows,
            row_width: ROW_WIDTH,
            tag_commitments: self.tag_commitments.clone(),
            mode: self.mode.clone(),
        }
    }
}

// ---------------------------------------------------------------------------
// Encrypted database for download-all mode
// ---------------------------------------------------------------------------

impl EncryptedDatabase {
    /// Encrypt a padded database for download-all PIR mode.
    ///
    /// Each row is encrypted with a row-specific key derived from the session
    /// secret and row index. The client, knowing the session secret, can decrypt
    /// any row locally without the server learning which one was read.
    pub fn encrypt(db: &PaddedDatabase, session_secret: &[u8; 32]) -> Self {
        let mut nonce = [0u8; 32];
        crate::getrandom(&mut nonce);

        let encrypted_rows: Vec<Vec<u8>> = db
            .entries
            .iter()
            .enumerate()
            .map(|(row_idx, row)| {
                // Derive per-row key from session secret + row index.
                let row_key = blake3::derive_key(
                    "pyana-pir-download-all-row-key",
                    &[session_secret.as_slice(), &row_idx.to_le_bytes(), &nonce].concat(),
                );

                // XOR-encrypt the row data (each BabyBear element as 4 bytes).
                let row_bytes: Vec<u8> = row
                    .iter()
                    .flat_map(|elem| elem.as_u32().to_le_bytes())
                    .collect();

                // Generate keystream via BLAKE3 in keyed mode.
                let mut keystream = vec![0u8; row_bytes.len()];
                let mut hasher = blake3::Hasher::new_keyed(&row_key);
                hasher.update(b"keystream");
                let mut output = hasher.finalize_xof();
                output.fill(&mut keystream);

                // XOR encrypt.
                row_bytes
                    .iter()
                    .zip(keystream.iter())
                    .map(|(a, b)| a ^ b)
                    .collect()
            })
            .collect();

        Self {
            encrypted_rows,
            session_nonce: nonce,
            real_row_count: db.entries.len(),
        }
    }

    /// Decrypt a single row from the encrypted database.
    ///
    /// The client uses the session secret and row index to derive the same
    /// per-row key and decrypt locally.
    pub fn decrypt_row(
        &self,
        row_idx: usize,
        session_secret: &[u8; 32],
    ) -> Option<Vec<BabyBear>> {
        let encrypted_row = self.encrypted_rows.get(row_idx)?;

        let row_key = blake3::derive_key(
            "pyana-pir-download-all-row-key",
            &[
                session_secret.as_slice(),
                &row_idx.to_le_bytes(),
                &self.session_nonce,
            ]
            .concat(),
        );

        // Generate keystream.
        let mut keystream = vec![0u8; encrypted_row.len()];
        let mut hasher = blake3::Hasher::new_keyed(&row_key);
        hasher.update(b"keystream");
        let mut output = hasher.finalize_xof();
        output.fill(&mut keystream);

        // XOR decrypt.
        let decrypted: Vec<u8> = encrypted_row
            .iter()
            .zip(keystream.iter())
            .map(|(a, b)| a ^ b)
            .collect();

        // Decode BabyBear elements from 4-byte chunks.
        let elements: Vec<BabyBear> = decrypted
            .chunks(4)
            .map(|chunk| {
                let val = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
                BabyBear::new(val)
            })
            .collect();

        Some(elements)
    }

    /// Number of rows in the encrypted database (including padding).
    pub fn num_rows(&self) -> usize {
        self.encrypted_rows.len()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ActionPattern, CommitmentId, IntentKind, MatchSpec};

    /// Build a test index with known tags and intent IDs.
    fn build_test_index(num_tags: usize) -> IntentIndex {
        let mut intents = Vec::new();
        for tag_idx in 0..num_tags {
            let tag_name = format!("action:capability_{tag_idx}");
            // Each tag gets 2-3 intents.
            for intent_num in 0..((tag_idx % 3) + 1) {
                let spec = MatchSpec {
                    actions: vec![ActionPattern {
                        action: Some(format!("capability_{tag_idx}")),
                        resource: None,
                    }],
                    constraints: vec![],
                    min_budget: None,
                    resource_pattern: None,
                    compound: None,
                    predicate_requirements: vec![],
                    strict_resource_matching: false,
                };
                let mut creator_bytes = [0u8; 32];
                creator_bytes[0] = tag_idx as u8;
                creator_bytes[1] = intent_num as u8;
                let intent = Intent::new(
                    IntentKind::Need,
                    spec,
                    CommitmentId(creator_bytes),
                    9999,
                    None,
                );
                intents.push(intent);
            }
        }
        IntentIndex::build_from_intents(&intents)
    }

    #[test]
    fn test_pir_correctness_single_query() {
        let index = build_test_index(10);
        let target_idx = 5;

        // Generate queries.
        let (q_a, q_b) = generate_pir_queries(target_idx, index.num_rows());

        // Compute responses (as two independent servers would).
        let resp_a = compute_pir_response(&q_a, &index.entries);
        let resp_b = compute_pir_response(&q_b, &index.entries);

        // Combine.
        let result = combine_pir_responses(&resp_a, &resp_b);

        // The result should equal the target row exactly.
        assert_eq!(result.len(), index.entries[target_idx].len());
        for (j, (&got, &expected)) in result
            .iter()
            .zip(index.entries[target_idx].iter())
            .enumerate()
        {
            assert_eq!(
                got, expected,
                "mismatch at column {j}: got {got:?}, expected {expected:?}"
            );
        }
    }

    #[test]
    fn test_pir_correctness_all_rows() {
        let index = build_test_index(20);

        for target_idx in 0..index.num_rows() {
            let (q_a, q_b) = generate_pir_queries(target_idx, index.num_rows());
            let resp_a = compute_pir_response(&q_a, &index.entries);
            let resp_b = compute_pir_response(&q_b, &index.entries);
            let result = combine_pir_responses(&resp_a, &resp_b);

            assert_eq!(
                result, index.entries[target_idx],
                "PIR failed for row {target_idx}"
            );
        }
    }

    #[test]
    fn test_pir_privacy_query_looks_random() {
        // Verify that each server's query vector looks uniformly random:
        // No statistical test here, but we verify the basic structure.
        let index = build_test_index(100);
        let target_idx = 42;

        let (q_a, q_b) = generate_pir_queries(target_idx, index.num_rows());

        // q_a should be random (non-zero in general).
        let nonzero_a = q_a
            .query_vector
            .iter()
            .filter(|&&v| v != BabyBear::ZERO)
            .count();
        assert!(
            nonzero_a > index.num_rows() / 2,
            "q_a should have many non-zero entries (has {nonzero_a}/{})",
            index.num_rows()
        );

        // q_b should also look random (non-zero in general).
        let nonzero_b = q_b
            .query_vector
            .iter()
            .filter(|&&v| v != BabyBear::ZERO)
            .count();
        assert!(
            nonzero_b > index.num_rows() / 2,
            "q_b should have many non-zero entries (has {nonzero_b}/{})",
            index.num_rows()
        );

        // Neither q_a nor q_b should be e_i (the "obvious" query).
        let is_unit_a = q_a.query_vector.iter().enumerate().all(|(i, &v)| {
            if i == target_idx {
                v == BabyBear::ONE
            } else {
                v == BabyBear::ZERO
            }
        });
        assert!(!is_unit_a, "q_a should NOT be the unit vector e_i");

        let is_unit_b = q_b.query_vector.iter().enumerate().all(|(i, &v)| {
            if i == target_idx {
                v == BabyBear::ONE
            } else {
                v == BabyBear::ZERO
            }
        });
        assert!(!is_unit_b, "q_b should NOT be the unit vector e_i");
    }

    #[test]
    fn test_pir_neither_server_learns_index() {
        // The key privacy property: given just one server's query, the index
        // is information-theoretically hidden. We demonstrate this by showing
        // that for ANY target index, q_a alone is consistent (i.e., q_a is
        // uniformly random regardless of the target).
        let n = 50;
        let (q_a_for_10, _) = generate_pir_queries(10, n);
        let (q_a_for_42, _) = generate_pir_queries(42, n);

        // Both q_a vectors are independent random vectors. We can't distinguish
        // them from randomness. Just verify they're different (overwhelmingly
        // likely for random vectors).
        assert_ne!(
            q_a_for_10.query_vector, q_a_for_42.query_vector,
            "two independent random vectors should differ"
        );

        // Verify structural correctness: q_a + q_b = e_i for each case.
        let (q_a, q_b) = generate_pir_queries(10, n);
        for i in 0..n {
            let sum = q_a.query_vector[i] + q_b.query_vector[i];
            let expected = if i == 10 {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            };
            assert_eq!(sum, expected, "q_a + q_b should equal e_i at position {i}");
        }
    }

    #[test]
    fn test_decode_intent_ids() {
        // Encode some known IDs and verify round-trip.
        let id1 = [0xAA; 32];
        let id2 = [0xBB; 32];

        let mut row = vec![BabyBear::ZERO; ROW_WIDTH];
        // Encode id1 at position 0 (byte-per-element).
        for (j, &byte) in id1.iter().enumerate() {
            row[j] = BabyBear::new(byte as u32);
        }
        // Encode id2 at position 1 (offset by ELEMENTS_PER_ID).
        for (j, &byte) in id2.iter().enumerate() {
            row[ELEMENTS_PER_ID + j] = BabyBear::new(byte as u32);
        }

        let decoded = decode_intent_ids(&row);
        assert_eq!(decoded.len(), 2);
        assert_eq!(decoded[0], id1);
        assert_eq!(decoded[1], id2);
    }

    #[test]
    fn test_build_index_from_intents() {
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![crate::Constraint::Service("docs".into())],
            min_budget: None,
            resource_pattern: None,
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };
        let intent = Intent::new(IntentKind::Need, spec, CommitmentId([0x11; 32]), 9999, None);

        let index = IntentIndex::build_from_intents(&[intent.clone()]);

        // Should have two tags: "action:read" and "service:docs".
        assert_eq!(index.num_rows(), 2);
        assert!(index.tags.contains(&"action:read".to_string()));
        assert!(index.tags.contains(&"service:docs".to_string()));

        // Query the "action:read" tag via PIR and verify we get the intent ID back.
        let target = index.tag_index("action:read").unwrap();
        let (q_a, q_b) = generate_pir_queries(target, index.num_rows());
        let resp_a = compute_pir_response(&q_a, &index.entries);
        let resp_b = compute_pir_response(&q_b, &index.entries);
        let result = combine_pir_responses(&resp_a, &resp_b);
        let ids = decode_intent_ids(&result);

        assert_eq!(ids.len(), 1);
        assert_eq!(ids[0], intent.id);
    }

    #[test]
    fn test_pir_with_100_tags_query_42() {
        // The spec test: 100 tags, query index 42, get correct intent IDs.
        let index = build_test_index(100);
        let target_idx = 42;

        let (q_a, q_b) = generate_pir_queries(target_idx, index.num_rows());
        let resp_a = compute_pir_response(&q_a, &index.entries);
        let resp_b = compute_pir_response(&q_b, &index.entries);
        let result = combine_pir_responses(&resp_a, &resp_b);

        // Verify the result matches the expected row.
        assert_eq!(result, index.entries[target_idx]);

        // Decode and verify intent IDs are non-empty for this tag.
        let ids = decode_intent_ids(&result);
        assert!(!ids.is_empty(), "tag at index 42 should have intents");
    }

    #[test]
    fn test_empty_database() {
        let index = IntentIndex::build_from_intents(&[]);
        assert_eq!(index.num_rows(), 0);
    }

    #[test]
    #[should_panic(expected = "out of bounds")]
    fn test_query_out_of_bounds_panics() {
        let _ = generate_pir_queries(5, 3);
    }

    #[test]
    fn test_extract_capability_tags() {
        let spec = MatchSpec {
            actions: vec![
                ActionPattern {
                    action: Some("read".into()),
                    resource: Some("docs/*".into()),
                },
                ActionPattern {
                    action: Some("write".into()),
                    resource: None,
                },
            ],
            constraints: vec![
                crate::Constraint::Service("storage".into()),
                crate::Constraint::Feature("premium".into()),
            ],
            min_budget: None,
            resource_pattern: Some("api/v1/*".into()),
            compound: None,
            predicate_requirements: vec![],
            strict_resource_matching: false,
        };

        let tags = extract_capability_tags(&spec);
        assert!(tags.contains(&"action:read".to_string()));
        assert!(tags.contains(&"action:write".to_string()));
        assert!(tags.contains(&"resource:docs/*".to_string()));
        assert!(tags.contains(&"service:storage".to_string()));
        assert!(tags.contains(&"feature:premium".to_string()));
        assert!(tags.contains(&"pattern:api/v1/*".to_string()));
    }

    // =========================================================================
    // New tests for PIR improvements
    // =========================================================================

    #[test]
    fn test_padded_database_is_power_of_two() {
        // 10 real tags should pad to 16 rows.
        let index = build_test_index(10);
        let padded = PaddedDatabase::from_index(&index, PirMode::TwoServer);
        assert_eq!(padded.padded_rows, 16);
        assert_eq!(padded.entries.len(), 16);
        assert_eq!(padded.tag_commitments.len(), 16);
    }

    #[test]
    fn test_padded_database_preserves_real_data() {
        let index = build_test_index(10);
        let padded = PaddedDatabase::from_index(&index, PirMode::TwoServer);

        // Real rows should be preserved exactly.
        for i in 0..index.num_rows() {
            assert_eq!(padded.entries[i], index.entries[i]);
        }

        // Padding rows should be all zeros.
        for i in index.num_rows()..padded.padded_rows {
            assert!(
                padded.entries[i].iter().all(|&e| e == BabyBear::ZERO),
                "padding row {i} should be all zeros"
            );
        }
    }

    #[test]
    fn test_padded_database_hides_size() {
        // 5 tags and 7 tags both pad to 8, making them indistinguishable.
        let index_5 = build_test_index(5);
        let index_7 = build_test_index(7);
        let padded_5 = PaddedDatabase::from_index(&index_5, PirMode::TwoServer);
        let padded_7 = PaddedDatabase::from_index(&index_7, PirMode::TwoServer);

        assert_eq!(padded_5.padded_rows, 8);
        assert_eq!(padded_7.padded_rows, 8);
        assert_eq!(padded_5.info().num_rows, padded_7.info().num_rows);
    }

    #[test]
    fn test_padded_database_pir_correctness() {
        // PIR should still work correctly over padded database.
        let index = build_test_index(10);
        let padded = PaddedDatabase::from_index(&index, PirMode::TwoServer);

        for target_idx in 0..index.num_rows() {
            let (q_a, q_b) = generate_pir_queries(target_idx, padded.padded_rows);
            let resp_a = compute_pir_response(&q_a, &padded.entries);
            let resp_b = compute_pir_response(&q_b, &padded.entries);
            let result = combine_pir_responses(&resp_a, &resp_b);

            assert_eq!(
                result, index.entries[target_idx],
                "PIR over padded DB failed for row {target_idx}"
            );
        }
    }

    #[test]
    fn test_padded_database_dummy_rows_decode_empty() {
        // Querying a padding row should decode to no intent IDs.
        let index = build_test_index(5);
        let padded = PaddedDatabase::from_index(&index, PirMode::TwoServer);

        // Query a padding row (index >= 5, < 8).
        let padding_idx = 6;
        let (q_a, q_b) = generate_pir_queries(padding_idx, padded.padded_rows);
        let resp_a = compute_pir_response(&q_a, &padded.entries);
        let resp_b = compute_pir_response(&q_b, &padded.entries);
        let result = combine_pir_responses(&resp_a, &resp_b);
        let ids = decode_intent_ids(&result);
        assert!(ids.is_empty(), "padding row should decode to no intents");
    }

    #[test]
    fn test_batch_pir_queries() {
        let index = build_test_index(20);
        let targets = vec![3, 7, 15];

        let (batch_a, batch_b) = generate_batch_pir_queries(&targets, index.num_rows());
        let resp_a = compute_batch_pir_response(&batch_a, &index.entries);
        let resp_b = compute_batch_pir_response(&batch_b, &index.entries);
        let results = combine_batch_pir_responses(&resp_a, &resp_b);

        assert_eq!(results.len(), 3);
        for (i, &target) in targets.iter().enumerate() {
            assert_eq!(
                results[i], index.entries[target],
                "batch PIR failed for target {target}"
            );
        }
    }

    #[test]
    fn test_batch_pir_all_rows() {
        let index = build_test_index(8);
        let targets: Vec<usize> = (0..index.num_rows()).collect();

        let (batch_a, batch_b) = generate_batch_pir_queries(&targets, index.num_rows());
        let resp_a = compute_batch_pir_response(&batch_a, &index.entries);
        let resp_b = compute_batch_pir_response(&batch_b, &index.entries);
        let results = combine_batch_pir_responses(&resp_a, &resp_b);

        for (i, row) in results.iter().enumerate() {
            assert_eq!(*row, index.entries[i], "batch failed at row {i}");
        }
    }

    #[test]
    fn test_single_server_pir_correctness() {
        let index = build_test_index(10);
        let padded = PaddedDatabase::from_index(&index, PirMode::SingleServerPadded);
        let target_idx = 4;

        // Generate query with blinding.
        let (query, blinding) =
            generate_single_server_query(target_idx, padded.padded_rows);

        // Server computes response.
        let response = compute_single_server_response(&query, &padded.entries);

        // Client computes blinding contribution (using local copy of DB).
        let blinding_contrib = compute_blinding_contribution(&blinding, &padded.entries);

        // Reconstruct.
        let result = reconstruct_single_server(&response, &blinding_contrib);

        assert_eq!(
            result, padded.entries[target_idx],
            "single-server PIR failed for row {target_idx}"
        );
    }

    #[test]
    fn test_single_server_pir_all_rows() {
        let index = build_test_index(15);
        let padded = PaddedDatabase::from_index(&index, PirMode::SingleServerPadded);

        for target_idx in 0..index.num_rows() {
            let (query, blinding) =
                generate_single_server_query(target_idx, padded.padded_rows);
            let response = compute_single_server_response(&query, &padded.entries);
            let blinding_contrib =
                compute_blinding_contribution(&blinding, &padded.entries);
            let result = reconstruct_single_server(&response, &blinding_contrib);

            assert_eq!(
                result, padded.entries[target_idx],
                "single-server PIR failed for row {target_idx}"
            );
        }
    }

    #[test]
    fn test_single_server_query_looks_random() {
        let padded_rows = 64;
        let target_idx = 30;
        let (query, _blinding) = generate_single_server_query(target_idx, padded_rows);

        // The query vector should look random (many non-zero entries).
        let nonzero = query
            .query_vector
            .iter()
            .filter(|&&v| v != BabyBear::ZERO)
            .count();
        assert!(
            nonzero > padded_rows / 2,
            "single-server query should look random (has {nonzero}/{padded_rows} non-zero)"
        );

        // Should NOT be the unit vector.
        let is_unit = query.query_vector.iter().enumerate().all(|(i, &v)| {
            if i == target_idx {
                v == BabyBear::ONE
            } else {
                v == BabyBear::ZERO
            }
        });
        assert!(!is_unit, "query should NOT be the plain unit vector");
    }

    #[test]
    fn test_download_all_encrypt_decrypt_roundtrip() {
        let index = build_test_index(10);
        let padded = PaddedDatabase::from_index(&index, PirMode::DownloadAll { max_db_size: 1000 });

        let session_secret = [0x42u8; 32];
        let encrypted = EncryptedDatabase::encrypt(&padded, &session_secret);

        // Decrypt each row and verify it matches the original.
        for i in 0..padded.padded_rows {
            let decrypted = encrypted.decrypt_row(i, &session_secret).unwrap();
            assert_eq!(
                decrypted, padded.entries[i],
                "decrypt failed for row {i}"
            );
        }
    }

    #[test]
    fn test_download_all_wrong_secret_fails() {
        let index = build_test_index(5);
        let padded = PaddedDatabase::from_index(&index, PirMode::DownloadAll { max_db_size: 1000 });

        let session_secret = [0x42u8; 32];
        let wrong_secret = [0x99u8; 32];
        let encrypted = EncryptedDatabase::encrypt(&padded, &session_secret);

        // Decrypting with wrong secret should produce garbage (not match original).
        let decrypted = encrypted.decrypt_row(0, &wrong_secret).unwrap();
        assert_ne!(
            decrypted, padded.entries[0],
            "wrong secret should NOT decrypt correctly"
        );
    }

    #[test]
    fn test_download_all_out_of_bounds_returns_none() {
        let index = build_test_index(5);
        let padded = PaddedDatabase::from_index(&index, PirMode::DownloadAll { max_db_size: 1000 });

        let session_secret = [0x42u8; 32];
        let encrypted = EncryptedDatabase::encrypt(&padded, &session_secret);

        assert!(encrypted.decrypt_row(999, &session_secret).is_none());
    }

    #[test]
    fn test_unlinkable_commitments_are_unique() {
        let secret = b"my-wallet-secret";
        let c0 = derive_unlinkable_commitment(secret, 0);
        let c1 = derive_unlinkable_commitment(secret, 1);
        let c2 = derive_unlinkable_commitment(secret, 2);

        assert_ne!(c0, c1);
        assert_ne!(c1, c2);
        assert_ne!(c0, c2);
    }

    #[test]
    fn test_unlinkable_commitments_are_deterministic() {
        let secret = b"my-wallet-secret";
        let c1a = derive_unlinkable_commitment(secret, 42);
        let c1b = derive_unlinkable_commitment(secret, 42);
        assert_eq!(c1a, c1b);
    }

    #[test]
    fn test_unlinkable_commitments_different_secrets_differ() {
        let c1 = derive_unlinkable_commitment(b"secret-a", 0);
        let c2 = derive_unlinkable_commitment(b"secret-b", 0);
        assert_ne!(c1, c2);
    }

    #[test]
    fn test_private_browse_client_next_commitment_increments() {
        let mut client =
            PrivateBrowseClient::with_secret(PirMode::TwoServer, [0xAA; 32]);
        let c0 = client.next_commitment();
        let c1 = client.next_commitment();
        let c2 = client.next_commitment();

        // All should be different (unlinkable).
        assert_ne!(c0, c1);
        assert_ne!(c1, c2);
        assert_ne!(c0, c2);
    }

    #[test]
    fn test_private_browse_client_download_all_local() {
        let index = build_test_index(10);
        let padded = PaddedDatabase::from_index(&index, PirMode::DownloadAll { max_db_size: 1000 });
        let info = padded.info();

        let session_secret = [0x42u8; 32];
        let encrypted = EncryptedDatabase::encrypt(&padded, &session_secret);

        let mut client =
            PrivateBrowseClient::with_secret(PirMode::DownloadAll { max_db_size: 1000 }, [0xBB; 32]);
        client.set_db_info(info);
        client.set_cached_db(encrypted, session_secret);

        // Browse the first tag's category.
        let tag = &index.tags[0];
        let listings = client.browse_category_local(tag).unwrap();
        assert!(!listings.is_empty(), "should find listings for tag: {tag}");

        // Verify the listing IDs match what PIR would return.
        let ids = decode_intent_ids(&index.entries[0]);
        assert_eq!(listings.len(), ids.len());
        for (listing, expected_id) in listings.iter().zip(ids.iter()) {
            assert_eq!(listing.id, *expected_id);
        }
    }

    #[test]
    fn test_private_browse_client_nonexistent_category() {
        let index = build_test_index(5);
        let padded = PaddedDatabase::from_index(&index, PirMode::DownloadAll { max_db_size: 1000 });
        let info = padded.info();

        let session_secret = [0x42u8; 32];
        let encrypted = EncryptedDatabase::encrypt(&padded, &session_secret);

        let mut client =
            PrivateBrowseClient::with_secret(PirMode::DownloadAll { max_db_size: 1000 }, [0xBB; 32]);
        client.set_db_info(info);
        client.set_cached_db(encrypted, session_secret);

        // Nonexistent category should return None.
        let result = client.browse_category_local("action:nonexistent_xyz");
        assert!(result.is_none());
    }

    #[test]
    fn test_pir_mode_default_is_two_server() {
        assert_eq!(PirMode::default(), PirMode::TwoServer);
    }

    #[test]
    fn test_padded_database_power_of_two_already() {
        // 8 tags should still pad to 8 (already power of 2).
        let index = build_test_index(8);
        let padded = PaddedDatabase::from_index(&index, PirMode::TwoServer);
        assert_eq!(padded.padded_rows, 8);
        assert_eq!(padded.entries.len(), 8);
    }

    #[test]
    fn test_padded_database_single_row() {
        // 1 tag should pad to 1 (2^0 = 1).
        let index = build_test_index(1);
        let padded = PaddedDatabase::from_index(&index, PirMode::TwoServer);
        assert_eq!(padded.padded_rows, 1);
    }

    #[test]
    fn test_padded_database_info_tag_lookup() {
        let index = build_test_index(10);
        let padded = PaddedDatabase::from_index(&index, PirMode::TwoServer);
        let info = padded.info();

        // Should be able to find real tags.
        for tag in &index.tags {
            assert!(
                info.find_tag_index(tag).is_some(),
                "should find tag: {tag}"
            );
        }

        // Should NOT find fake tags.
        assert!(info.find_tag_index("action:definitely_not_here").is_none());
    }

    #[test]
    fn test_batch_pir_over_padded_database() {
        let index = build_test_index(10);
        let padded = PaddedDatabase::from_index(&index, PirMode::TwoServer);
        let targets = vec![0, 5, 9];

        let (batch_a, batch_b) =
            generate_batch_pir_queries(&targets, padded.padded_rows);
        let resp_a = compute_batch_pir_response(&batch_a, &padded.entries);
        let resp_b = compute_batch_pir_response(&batch_b, &padded.entries);
        let results = combine_batch_pir_responses(&resp_a, &resp_b);

        for (i, &target) in targets.iter().enumerate() {
            assert_eq!(results[i], index.entries[target]);
            let ids = decode_intent_ids(&results[i]);
            assert!(!ids.is_empty());
        }
    }

    #[test]
    fn test_is_download_all_practical() {
        let info_small = PirDatabaseInfo {
            num_rows: 64,
            row_width: ROW_WIDTH,
            tag_commitments: vec![[0u8; 32]; 64],
            mode: PirMode::DownloadAll { max_db_size: 1000 },
        };
        assert!(PrivateBrowseClient::is_download_all_practical(&info_small));

        let info_large = PirDatabaseInfo {
            num_rows: 2000,
            row_width: ROW_WIDTH,
            tag_commitments: vec![[0u8; 32]; 2000],
            mode: PirMode::DownloadAll { max_db_size: 1000 },
        };
        assert!(!PrivateBrowseClient::is_download_all_practical(&info_large));

        let info_two_server = PirDatabaseInfo {
            num_rows: 64,
            row_width: ROW_WIDTH,
            tag_commitments: vec![[0u8; 32]; 64],
            mode: PirMode::TwoServer,
        };
        assert!(!PrivateBrowseClient::is_download_all_practical(
            &info_two_server
        ));
    }
}
