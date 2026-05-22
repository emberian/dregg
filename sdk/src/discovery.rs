//! Private intent discovery via 2-server IT-PIR.
//!
//! The [`PrivateDiscoveryClient`] enables agents to discover intents matching a
//! given capability tag without revealing which tag they are querying.
//!
//! The protocol requires two independent pyana nodes (non-colluding servers).
//! The client constructs two complementary PIR query vectors and sends one to each
//! node. Neither node can determine the target tag from its query alone.
//!
//! # HTTP Transport
//!
//! This module defines the discovery logic and an `HttpTransport` trait for the
//! actual HTTP calls. A default implementation is provided when the `reqwest`
//! feature is available; otherwise callers must supply their own transport.

use pyana_circuit::field::BabyBear;
use pyana_intent::pir::{
    PirResponse, combine_pir_responses, decode_intent_ids, generate_pir_queries,
};
use serde::{Deserialize, Serialize};

use crate::error::SdkError;

// ---------------------------------------------------------------------------
// HTTP transport trait (allows mocking and alternative HTTP clients)
// ---------------------------------------------------------------------------

/// Request/response types matching the node's `/pir/info` and `/pir/query` API.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PirInfoResponse {
    pub num_rows: usize,
    pub row_width: usize,
    pub tags: Vec<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PirQueryRequest {
    pub query_vector: Vec<u32>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PirQueryResponse {
    pub response: Vec<u32>,
}

/// Trait abstracting HTTP calls to a PIR-enabled pyana node.
///
/// Implementors handle the actual network transport (reqwest, hyper, etc.).
/// The default test implementation uses in-memory state.
#[async_trait::async_trait]
pub trait PirTransport: Send + Sync {
    /// Fetch PIR database metadata from the node.
    async fn get_pir_info(&self, base_url: &str) -> Result<PirInfoResponse, SdkError>;

    /// Send a PIR query to the node and receive the response vector.
    async fn post_pir_query(
        &self,
        base_url: &str,
        request: &PirQueryRequest,
    ) -> Result<PirQueryResponse, SdkError>;
}

// ---------------------------------------------------------------------------
// Default HTTP transport (uses reqwest if available, otherwise stub)
// ---------------------------------------------------------------------------

/// HTTP transport using `reqwest`.
///
/// This is the production transport. It issues real HTTP requests to pyana node
/// endpoints `/pir/info` (GET) and `/pir/query` (POST).
#[cfg(feature = "reqwest")]
pub struct ReqwestTransport {
    client: reqwest::Client,
}

#[cfg(feature = "reqwest")]
impl ReqwestTransport {
    pub fn new() -> Self {
        Self {
            client: reqwest::Client::new(),
        }
    }
}

#[cfg(feature = "reqwest")]
#[async_trait::async_trait]
impl PirTransport for ReqwestTransport {
    async fn get_pir_info(&self, base_url: &str) -> Result<PirInfoResponse, SdkError> {
        let url = format!("{base_url}/pir/info");
        let resp = self
            .client
            .get(&url)
            .send()
            .await
            .map_err(|e| SdkError::Wire(format!("GET /pir/info failed: {e}")))?;
        resp.json()
            .await
            .map_err(|e| SdkError::Wire(format!("deserialize /pir/info failed: {e}")))
    }

    async fn post_pir_query(
        &self,
        base_url: &str,
        request: &PirQueryRequest,
    ) -> Result<PirQueryResponse, SdkError> {
        let url = format!("{base_url}/pir/query");
        let resp = self
            .client
            .post(&url)
            .json(request)
            .send()
            .await
            .map_err(|e| SdkError::Wire(format!("POST /pir/query failed: {e}")))?;
        if !resp.status().is_success() {
            return Err(SdkError::Wire(format!(
                "POST /pir/query returned status {}",
                resp.status()
            )));
        }
        resp.json()
            .await
            .map_err(|e| SdkError::Wire(format!("deserialize /pir/query failed: {e}")))
    }
}

// ---------------------------------------------------------------------------
// PrivateDiscoveryClient
// ---------------------------------------------------------------------------

/// Client for private intent discovery using 2-server IT-PIR.
///
/// Queries two independent pyana nodes so that neither learns which capability
/// tag the agent is looking for. The two responses are combined locally to
/// reveal only the matching intent IDs.
///
/// # Security Properties
///
/// - **Information-theoretic privacy**: Each server sees a uniformly random
///   query vector. No computational assumption is needed.
/// - **Non-collusion requirement**: The two nodes must not collude. If they
///   share their query vectors, they can XOR them to discover `e_i`.
/// - **Post-quantum safe**: No lattice/discrete-log assumptions involved.
///
/// # Example
///
/// ```no_run
/// use pyana_sdk::discovery::PrivateDiscoveryClient;
///
/// # async fn example() -> Result<(), pyana_sdk::SdkError> {
/// // In production, use ReqwestTransport (with `reqwest` feature)
/// // let transport = pyana_sdk::discovery::ReqwestTransport::new();
/// // let client = PrivateDiscoveryClient::new("http://node-a:8080", "http://node-b:8080", transport);
/// // let ids = client.discover_intents("action:read").await?;
/// # Ok(())
/// # }
/// ```
pub struct PrivateDiscoveryClient<T: PirTransport> {
    /// URL of the first PIR server.
    node_a_url: String,
    /// URL of the second PIR server (must be a different, non-colluding node).
    node_b_url: String,
    /// The HTTP transport implementation.
    transport: T,
}

impl<T: PirTransport> PrivateDiscoveryClient<T> {
    /// Create a new private discovery client.
    ///
    /// # Arguments
    ///
    /// * `node_a` - Base URL of the first pyana node (e.g., `"http://localhost:8080"`).
    /// * `node_b` - Base URL of the second pyana node (must be different from `node_a`).
    /// * `transport` - The HTTP transport to use for requests.
    pub fn new(node_a: &str, node_b: &str, transport: T) -> Self {
        Self {
            node_a_url: node_a.to_string(),
            node_b_url: node_b.to_string(),
            transport,
        }
    }

    /// Discover intents matching a capability tag without revealing which tag.
    ///
    /// This executes the full 2-server IT-PIR protocol:
    /// 1. Fetch the PIR database metadata (tag list) from node A.
    /// 2. Find the index of `capability_tag` in the tag list.
    /// 3. Generate complementary PIR queries `(q_a, q_b)`.
    /// 4. Send `q_a` to node A and `q_b` to node B (in parallel).
    /// 5. Combine the responses locally to reconstruct the target row.
    /// 6. Decode the row into intent IDs.
    ///
    /// # Arguments
    ///
    /// * `capability_tag` - The tag to search for (e.g., `"action:read"`).
    ///
    /// # Returns
    ///
    /// A vector of 32-byte intent IDs matching the tag, or an error.
    ///
    /// # Errors
    ///
    /// - `SdkError::Wire` if either HTTP request fails.
    /// - `SdkError::TokenNotFound` if the capability tag is not in the index.
    pub async fn discover_intents(&self, capability_tag: &str) -> Result<Vec<[u8; 32]>, SdkError> {
        // Step 1: Get database metadata from BOTH nodes.
        // SECURITY: Fetching metadata from only one node leaks query intent to that
        // node (it knows a PIR query is about to come from this client). Fetching
        // from both nodes provides symmetry and allows consistency validation.
        let (info_a, info_b) = tokio::join!(
            self.transport.get_pir_info(&self.node_a_url),
            self.transport.get_pir_info(&self.node_b_url),
        );
        let info_a = info_a?;
        let info_b = info_b?;

        // Validate consistency between the two nodes' databases.
        // If they disagree on num_rows, the PIR protocol won't produce correct results
        // and may leak information through dimension mismatches.
        if info_a.num_rows != info_b.num_rows {
            return Err(SdkError::Wire(format!(
                "PIR database inconsistency: node A has {} rows, node B has {} rows",
                info_a.num_rows, info_b.num_rows
            )));
        }

        let info = info_a;

        if info.num_rows == 0 {
            return Ok(Vec::new());
        }

        // Step 2: Find the target tag's index.
        let target_index = info
            .tags
            .iter()
            .position(|t| t == capability_tag)
            .ok_or_else(|| {
                SdkError::TokenNotFound(format!(
                    "capability tag '{capability_tag}' not found in PIR index"
                ))
            })?;

        // Step 3: Generate complementary PIR queries.
        let (q_a, q_b) = generate_pir_queries(target_index, info.num_rows);

        // Step 4: Send queries to both nodes in parallel.
        // Add a small random delay to reduce timing correlation between metadata
        // fetch and the actual PIR query.
        let delay_ms = {
            let mut buf = [0u8; 2];
            getrandom::fill(&mut buf).unwrap_or(());
            u16::from_le_bytes(buf) % 50
        };
        tokio::time::sleep(std::time::Duration::from_millis(delay_ms as u64)).await;

        let req_a = PirQueryRequest {
            query_vector: q_a.query_vector.iter().map(|e| e.as_u32()).collect(),
        };
        let req_b = PirQueryRequest {
            query_vector: q_b.query_vector.iter().map(|e| e.as_u32()).collect(),
        };

        let (resp_a, resp_b) = tokio::join!(
            self.transport.post_pir_query(&self.node_a_url, &req_a),
            self.transport.post_pir_query(&self.node_b_url, &req_b),
        );

        let resp_a = resp_a?;
        let resp_b = resp_b?;

        // Step 5: Combine responses locally.
        let pir_resp_a = PirResponse {
            response: resp_a.response.iter().map(|&v| BabyBear::new(v)).collect(),
        };
        let pir_resp_b = PirResponse {
            response: resp_b.response.iter().map(|&v| BabyBear::new(v)).collect(),
        };

        let combined = combine_pir_responses(&pir_resp_a, &pir_resp_b);

        // Step 6: Decode intent IDs from the reconstructed row.
        let intent_ids = decode_intent_ids(&combined);

        Ok(intent_ids)
    }
}

// ---------------------------------------------------------------------------
// Integration with AgentWallet
// ---------------------------------------------------------------------------

impl crate::wallet::AgentWallet {
    /// Discover intents matching a capability using private information retrieval.
    ///
    /// This is a convenience method that creates a [`PrivateDiscoveryClient`] with
    /// the given transport and nodes, then performs the PIR query.
    ///
    /// # Arguments
    ///
    /// * `capability` - The capability tag to search for (e.g., `"action:read"`).
    /// * `nodes` - A pair of base URLs for the two non-colluding PIR servers.
    /// * `transport` - The HTTP transport implementation.
    ///
    /// # Returns
    ///
    /// A vector of 32-byte intent IDs matching the capability.
    pub async fn discover_matching_intents<T: PirTransport>(
        &self,
        capability: &str,
        nodes: (&str, &str),
        transport: T,
    ) -> Result<Vec<[u8; 32]>, SdkError> {
        let client = PrivateDiscoveryClient::new(nodes.0, nodes.1, transport);
        client.discover_intents(capability).await
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_intent::pir::{IntentIndex, PirQuery, compute_pir_response};
    use pyana_intent::{ActionPattern, CommitmentId, Intent, IntentKind, MatchSpec};
    use std::sync::Arc;
    use tokio::sync::Mutex;

    /// A mock PIR transport that holds an in-memory intent index and answers
    /// PIR queries directly, simulating two independent nodes with the same data.
    struct MockTransport {
        index: Arc<Mutex<IntentIndex>>,
        /// Track which queries each "node" receives, for privacy verification.
        node_a_queries: Arc<Mutex<Vec<Vec<u32>>>>,
        node_b_queries: Arc<Mutex<Vec<Vec<u32>>>>,
    }

    impl MockTransport {
        fn new(index: IntentIndex) -> Self {
            Self {
                index: Arc::new(Mutex::new(index)),
                node_a_queries: Arc::new(Mutex::new(Vec::new())),
                node_b_queries: Arc::new(Mutex::new(Vec::new())),
            }
        }
    }

    #[async_trait::async_trait]
    impl PirTransport for MockTransport {
        async fn get_pir_info(&self, _base_url: &str) -> Result<PirInfoResponse, SdkError> {
            let idx = self.index.lock().await;
            Ok(PirInfoResponse {
                num_rows: idx.num_rows(),
                row_width: idx.row_width(),
                tags: idx.tags.clone(),
            })
        }

        async fn post_pir_query(
            &self,
            base_url: &str,
            request: &PirQueryRequest,
        ) -> Result<PirQueryResponse, SdkError> {
            // Record the query for privacy verification.
            if base_url.contains("node-a") {
                self.node_a_queries
                    .lock()
                    .await
                    .push(request.query_vector.clone());
            } else {
                self.node_b_queries
                    .lock()
                    .await
                    .push(request.query_vector.clone());
            }

            let idx = self.index.lock().await;
            let query = PirQuery {
                query_vector: request
                    .query_vector
                    .iter()
                    .map(|&v| BabyBear::new(v))
                    .collect(),
            };
            let response = compute_pir_response(&query, &idx.entries);
            Ok(PirQueryResponse {
                response: response.response.iter().map(|e| e.as_u32()).collect(),
            })
        }
    }

    /// Build a test index with known tags and intents.
    fn build_test_index() -> (IntentIndex, Vec<Intent>) {
        let mut intents = Vec::new();
        for tag_idx in 0..10 {
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
            let intent = Intent::new(
                IntentKind::Need,
                spec,
                CommitmentId(creator_bytes),
                9999,
                None,
            );
            intents.push(intent);
        }
        let index = IntentIndex::build_from_intents(&intents);
        (index, intents)
    }

    #[tokio::test]
    async fn test_discover_intents_returns_correct_ids() {
        let (index, intents) = build_test_index();
        let transport = MockTransport::new(index.clone());

        let client =
            PrivateDiscoveryClient::new("http://node-a:8080", "http://node-b:8080", transport);

        // Query for "action:capability_5" — should find the intent with tag_idx=5.
        let ids = client
            .discover_intents("action:capability_5")
            .await
            .unwrap();

        assert!(!ids.is_empty(), "should find at least one intent");

        // The intent for tag_idx=5 should be in the results.
        let expected_id = intents[5].id;
        assert!(
            ids.contains(&expected_id),
            "result should contain intent ID for capability_5"
        );
    }

    #[tokio::test]
    async fn test_discover_intents_tag_not_found() {
        let (index, _) = build_test_index();
        let transport = MockTransport::new(index);

        let client =
            PrivateDiscoveryClient::new("http://node-a:8080", "http://node-b:8080", transport);

        let result = client.discover_intents("action:nonexistent").await;
        assert!(result.is_err());
        match result.unwrap_err() {
            SdkError::TokenNotFound(msg) => {
                assert!(msg.contains("nonexistent"));
            }
            other => panic!("expected TokenNotFound, got: {other:?}"),
        }
    }

    #[tokio::test]
    async fn test_discover_intents_empty_index() {
        let index = IntentIndex::build_from_intents(&[]);
        let transport = MockTransport::new(index);

        let client =
            PrivateDiscoveryClient::new("http://node-a:8080", "http://node-b:8080", transport);

        let ids = client.discover_intents("action:anything").await.unwrap();
        assert!(ids.is_empty());
    }

    #[tokio::test]
    async fn test_neither_node_learns_query_index() {
        let (index, _) = build_test_index();
        let transport = MockTransport::new(index.clone());
        let node_a_queries = transport.node_a_queries.clone();
        let node_b_queries = transport.node_b_queries.clone();

        let client =
            PrivateDiscoveryClient::new("http://node-a:8080", "http://node-b:8080", transport);

        // Query for tag at index 5.
        let _ids = client
            .discover_intents("action:capability_5")
            .await
            .unwrap();

        let a_queries = node_a_queries.lock().await;
        let b_queries = node_b_queries.lock().await;

        assert_eq!(a_queries.len(), 1);
        assert_eq!(b_queries.len(), 1);

        let q_a = &a_queries[0];
        let q_b = &b_queries[0];

        let num_rows = index.num_rows();
        let target_idx = 5;

        // Verify that q_a is NOT the trivial unit vector e_5 (which would reveal
        // the query target). A random vector over BabyBear will have many non-zero
        // entries with overwhelming probability.
        let is_unit_a = q_a
            .iter()
            .enumerate()
            .all(|(i, &v)| if i == target_idx { v == 1 } else { v == 0 });
        assert!(
            !is_unit_a,
            "query to node A must not be the unit vector e_i"
        );

        // Same check for node B.
        let is_unit_b = q_b
            .iter()
            .enumerate()
            .all(|(i, &v)| if i == target_idx { v == 1 } else { v == 0 });
        assert!(
            !is_unit_b,
            "query to node B must not be the unit vector e_i"
        );

        // Verify that q_a + q_b = e_target_idx in BabyBear arithmetic.
        // This confirms the protocol correctness without revealing the index
        // to either server individually.
        assert_eq!(q_a.len(), num_rows);
        assert_eq!(q_b.len(), num_rows);
        for i in 0..num_rows {
            let sum = BabyBear::new(q_a[i]) + BabyBear::new(q_b[i]);
            let expected = if i == target_idx {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            };
            assert_eq!(sum, expected, "q_a[{i}] + q_b[{i}] should equal e_i[{i}]");
        }
    }

    #[tokio::test]
    async fn test_wallet_discover_matching_intents() {
        let (index, intents) = build_test_index();
        let transport = MockTransport::new(index);

        let wallet = crate::wallet::AgentWallet::new();
        let ids = wallet
            .discover_matching_intents(
                "action:capability_3",
                ("http://node-a:8080", "http://node-b:8080"),
                transport,
            )
            .await
            .unwrap();

        let expected_id = intents[3].id;
        assert!(
            ids.contains(&expected_id),
            "wallet discovery should return intent for capability_3"
        );
    }
}
