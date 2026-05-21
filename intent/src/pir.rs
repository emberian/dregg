//! 2-Server Information-Theoretic Private Information Retrieval (IT-PIR).
//!
//! Enables private intent discovery: a client can query the intent pool's
//! inverted index (capability_tag -> [intent_ids]) without revealing which
//! capability tag they are looking for.
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
//! # Security
//!
//! - Information-theoretic: each server sees a uniformly random vector.
//! - Requires non-collusion between the two servers.
//! - Post-quantum safe (no computational assumptions).

use pyana_circuit::field::BabyBear;
use serde::{Deserialize, Serialize};

use crate::gossip::IntentPool;
use crate::{Intent, MatchSpec};

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
// High-level discovery API
// ---------------------------------------------------------------------------

/// Metadata about the PIR database, shared with clients so they can construct
/// valid queries.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PirDatabaseInfo {
    /// Number of rows (capability tags) in the index.
    pub num_rows: usize,
    /// Number of columns per row (in BabyBear field elements).
    pub row_width: usize,
    /// The ordered list of capability tags (so the client can find their target index).
    /// In production, this would be replaced by a committed hash table for privacy.
    pub tags: Vec<String>,
}

impl From<&IntentIndex> for PirDatabaseInfo {
    fn from(index: &IntentIndex) -> Self {
        Self {
            num_rows: index.num_rows(),
            row_width: index.row_width(),
            tags: index.tags.clone(),
        }
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
        };

        let tags = extract_capability_tags(&spec);
        assert!(tags.contains(&"action:read".to_string()));
        assert!(tags.contains(&"action:write".to_string()));
        assert!(tags.contains(&"resource:docs/*".to_string()));
        assert!(tags.contains(&"service:storage".to_string()));
        assert!(tags.contains(&"feature:premium".to_string()));
        assert!(tags.contains(&"pattern:api/v1/*".to_string()));
    }
}
