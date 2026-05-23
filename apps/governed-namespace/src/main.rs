//! Governed Namespace — DAO-controlled file hosting with DFA-governed routing.
//!
//! A standalone HTTP server demonstrating three integrated capabilities:
//! 1. DFA-governed routing: URL-style routes controlled by constitutional vote
//! 2. VFS storage: capability-secure file storage with content-addressed (nameless) writes
//! 3. Route governance: propose/vote/amend the routing table democratically
//!
//! ## How it differs from traditional file hosting
//!
//! - **No filenames**: Files are addressed by their content hash (blake3). Knowledge
//!   of the hash IS authority to read — this is capability security.
//! - **No ACLs**: Access is determined by DFA route classification, not user/group/other.
//!   The routing table itself is a governed, committed data structure.
//! - **Provable**: Every operation (write, read, route change) can be expressed as a
//!   STARK statement. The route commitment binds proofs to the approved governance state.
//! - **Democratic**: Route changes require threshold voting. No single admin can
//!   unilaterally change access policy.
//!
//! ## DAO Use Case
//!
//! 1. DAO creates namespace with routes: /public/*, /treasury/*, /proposals/*, /members/*
//! 2. Member uploads file to /public/ (routed to public storage, anyone can read)
//! 3. Admin proposes adding /grants/* route → threshold vote → route goes live
//! 4. File shared via sturdy ref: pyana://federation/cell/swiss → recipient reads file
//!
//! ## Circuit Provability Mapping
//!
//! | Operation          | STARK Statement                                           |
//! |--------------------|---------------------------------------------------------|
//! | Upload             | "blake3(content) = H" (preimage knowledge)               |
//! | Read               | "I possess H" (capability presentation)                  |
//! | Splice             | "H_new = blake3(patch) AND H_old was live"              |
//! | Delete             | "nullifier = blake3(H ∥ 'nullify')"                    |
//! | Route classify     | "DFA(path) = class using table with commitment C"        |
//! | Governance vote    | "I am participant P AND I voted on proposal Q"           |
//! | Amendment enact    | "proposal Q reached threshold T, table C_old → C_new"  |

mod governance;
mod namespace;
mod registry;
mod routes;
mod storage;

use axum::body::Bytes;
use axum::extract::{Path, State};
use axum::http::StatusCode;
use axum::response::IntoResponse;
use axum::routing::{delete as delete_route, get, post, put};
use axum::{Json, Router};
use serde_json::json;

use pyana_app_framework::auth::{AdminToken, HasAdminToken};
use pyana_app_framework::server::{AppConfig, AppServer};

use governance::Participant;
use namespace::{AuthLevel, Namespace};
use registry::Registry;
use storage::hex;

// =============================================================================
// Application State
// =============================================================================

/// Shared application state for all handlers.
#[derive(Clone)]
struct AppState {
    /// The integrated namespace (router + storage + governance + capabilities).
    namespace: Namespace,
    /// The capability registry (service mesh overlay).
    registry: Registry,
    /// Admin token for protected endpoints.
    admin_token: AdminToken,
}

impl HasAdminToken for AppState {
    fn admin_token(&self) -> &AdminToken {
        &self.admin_token
    }
}

// =============================================================================
// Main
// =============================================================================

#[tokio::main]
async fn main() {
    let config = AppConfig::from_env();

    // Initialize participants from env or use defaults.
    let participants = load_participants();
    let federation_id = load_federation_id();

    let namespace = Namespace::new(participants, federation_id);

    let state = AppState {
        namespace,
        registry: Registry::new(),
        admin_token: config.admin_token.clone(),
    };

    let app_routes = app_router().with_state(state);

    AppServer::new(config)
        .service_name("governed-namespace")
        .with_health()
        .with_cors()
        .routes(app_routes)
        .serve()
        .await
        .unwrap();
}

/// Load participants from NAMESPACE_PARTICIPANTS env var (JSON array) or use defaults.
fn load_participants() -> Vec<Participant> {
    if let Ok(json_str) = std::env::var("NAMESPACE_PARTICIPANTS") {
        serde_json::from_str(&json_str).unwrap_or_else(|_| default_participants())
    } else {
        default_participants()
    }
}

/// Default participant set for development/demo.
fn default_participants() -> Vec<Participant> {
    vec![
        Participant {
            id: "alice".to_string(),
            name: Some("Alice".to_string()),
            weight: 1,
        },
        Participant {
            id: "bob".to_string(),
            name: Some("Bob".to_string()),
            weight: 1,
        },
        Participant {
            id: "carol".to_string(),
            name: Some("Carol".to_string()),
            weight: 1,
        },
        Participant {
            id: "dave".to_string(),
            name: Some("Dave".to_string()),
            weight: 1,
        },
        Participant {
            id: "eve".to_string(),
            name: Some("Eve".to_string()),
            weight: 1,
        },
    ]
}

/// Load federation ID from NAMESPACE_FEDERATION_ID env var or generate from hostname.
fn load_federation_id() -> [u8; 32] {
    if let Ok(hex_str) = std::env::var("NAMESPACE_FEDERATION_ID") {
        hex::decode(&hex_str)
            .unwrap_or_else(|_| *blake3::hash(b"governed-namespace-demo").as_bytes())
    } else {
        *blake3::hash(b"governed-namespace-demo").as_bytes()
    }
}

/// Build the application router.
fn app_router() -> Router<AppState> {
    Router::new()
        // File storage endpoints (nameless VFS)
        .route("/files", post(upload_file))
        .route("/files/{hash}", get(read_file))
        .route("/files/{hash}", put(splice_file))
        .route("/files/{hash}", delete_route(delete_file))
        // Route management
        .route("/routes", get(list_routes))
        .route("/routes/propose", post(propose_route))
        .route("/routes/vote", post(vote_route))
        .route("/routes/commitment", get(route_commitment))
        // Namespace (DFA-routed) access
        .route("/namespace/{*path}", get(namespace_read))
        .route("/namespace/{*path}", post(namespace_write))
        // Registry (capability service mesh)
        .route("/registry/mount", post(registry_mount))
        .route("/registry/unmount/{*path}", delete_route(registry_unmount))
        .route("/registry/discover", get(registry_discover))
        .route("/registry/resolve/{*path}", get(registry_resolve))
        .route("/registry/update/{*path}", put(registry_update))
        .route("/registry/health/{*path}", get(registry_health))
        // Governance
        .route("/governance/constitution", get(get_constitution))
        .route("/governance/proposals", get(get_proposals))
        // Sharing
        .route("/share/{hash}", post(share_file))
}

// =============================================================================
// File Storage Handlers
// =============================================================================

/// POST /files — Upload a file (nameless write, returns content hash).
///
/// The request body IS the file content. Returns the blake3 hash as the address.
/// Content-Type header is stored as metadata but not authoritative.
async fn upload_file(State(state): State<AppState>, body: Bytes) -> impl IntoResponse {
    let content = body.to_vec();
    if content.is_empty() {
        return (
            StatusCode::BAD_REQUEST,
            Json(json!({"error": "empty content"})),
        )
            .into_response();
    }

    match state.namespace.store.write(content, None, None).await {
        Ok(receipt) => (
            StatusCode::CREATED,
            Json(json!({
                "hash": receipt.hash,
                "size": receipt.size,
                "new": receipt.new,
            })),
        )
            .into_response(),
        Err(e) => (StatusCode::CONFLICT, Json(json!({"error": e.to_string()}))).into_response(),
    }
}

/// GET /files/:hash — Read a file by content hash.
///
/// Knowledge of the hash IS authority. If you can present the hash, you get the content.
async fn read_file(
    State(state): State<AppState>,
    Path(hash_hex): Path<String>,
) -> impl IntoResponse {
    let hash = match hex::decode(&hash_hex) {
        Ok(h) => h,
        Err(e) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": format!("invalid hash: {e}")})),
            )
                .into_response();
        }
    };

    match state.namespace.store.read(&hash).await {
        Ok((content, entry)) => {
            let content_type = entry
                .content_type
                .unwrap_or_else(|| "application/octet-stream".to_string());
            (
                StatusCode::OK,
                [(axum::http::header::CONTENT_TYPE, content_type)],
                content,
            )
                .into_response()
        }
        Err(e) => (StatusCode::NOT_FOUND, Json(json!({"error": e.to_string()}))).into_response(),
    }
}

/// PUT /files/:hash — Splice/update a file (returns new hash).
///
/// Consumes the old content at :hash, replaces with request body, returns new hash.
/// The old hash is nullified (cannot be re-uploaded).
async fn splice_file(
    State(state): State<AppState>,
    Path(hash_hex): Path<String>,
    body: Bytes,
) -> impl IntoResponse {
    let hash = match hex::decode(&hash_hex) {
        Ok(h) => h,
        Err(e) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": format!("invalid hash: {e}")})),
            )
                .into_response();
        }
    };

    let patch = body.to_vec();
    if patch.is_empty() {
        return (
            StatusCode::BAD_REQUEST,
            Json(json!({"error": "empty patch content"})),
        )
            .into_response();
    }

    match state.namespace.store.splice(&hash, &patch, true).await {
        Ok(receipt) => (
            StatusCode::OK,
            Json(json!({
                "old_hash": receipt.old_hash,
                "new_hash": receipt.new_hash,
                "new_size": receipt.new_size,
                "old_nullified": receipt.old_nullified,
            })),
        )
            .into_response(),
        Err(e) => {
            let status = match e {
                storage::StorageError::NotFound => StatusCode::NOT_FOUND,
                storage::StorageError::Nullified => StatusCode::CONFLICT,
                storage::StorageError::NoChange => StatusCode::UNPROCESSABLE_ENTITY,
            };
            (status, Json(json!({"error": e.to_string()}))).into_response()
        }
    }
}

/// DELETE /files/:hash — Delete a file (reveal nullifier).
///
/// Removes the content and records a nullifier, preventing re-insertion of identical content.
async fn delete_file(
    State(state): State<AppState>,
    Path(hash_hex): Path<String>,
) -> impl IntoResponse {
    let hash = match hex::decode(&hash_hex) {
        Ok(h) => h,
        Err(e) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": format!("invalid hash: {e}")})),
            )
                .into_response();
        }
    };

    match state.namespace.store.delete(&hash).await {
        Ok(nullifier) => (
            StatusCode::OK,
            Json(json!({
                "deleted": hash_hex,
                "nullifier": hex::encode(nullifier),
            })),
        )
            .into_response(),
        Err(e) => (StatusCode::NOT_FOUND, Json(json!({"error": e.to_string()}))).into_response(),
    }
}

// =============================================================================
// Route Management Handlers
// =============================================================================

/// GET /routes — List current routing table.
async fn list_routes(State(state): State<AppState>) -> impl IntoResponse {
    let table = state.namespace.routing_table.read().await;
    let entries: Vec<_> = table.entries().into_iter().cloned().collect();
    let commitment = hex::encode(table.commitment());
    let version = table.version;

    Json(json!({
        "routes": entries,
        "commitment": commitment,
        "version": version,
    }))
}

/// Request body for proposing a route amendment.
#[derive(serde::Deserialize)]
struct ProposeRequest {
    /// Participant ID of the proposer.
    proposer: String,
    /// The proposed new route table.
    routes: Vec<routes::RouteEntry>,
    /// Human-readable description.
    description: String,
}

/// POST /routes/propose — Propose a route amendment (requires authenticated participant).
async fn propose_route(
    State(state): State<AppState>,
    Json(req): Json<ProposeRequest>,
) -> impl IntoResponse {
    match state
        .namespace
        .governance
        .propose(req.proposer, req.routes, req.description)
        .await
    {
        Ok(proposal_id) => (
            StatusCode::CREATED,
            Json(json!({
                "proposal_id": proposal_id,
                "status": "pending",
            })),
        )
            .into_response(),
        Err(e) => {
            let status = match e {
                governance::GovernanceError::NotParticipant => StatusCode::FORBIDDEN,
                _ => StatusCode::BAD_REQUEST,
            };
            (status, Json(json!({"error": e.to_string()}))).into_response()
        }
    }
}

/// Request body for voting on a proposal.
#[derive(serde::Deserialize)]
struct VoteRequest {
    /// Participant ID of the voter.
    voter: String,
    /// Proposal ID to vote on.
    proposal_id: String,
    /// Whether to approve (true) or reject (false).
    approve: bool,
}

/// POST /routes/vote — Vote on a pending amendment.
async fn vote_route(
    State(state): State<AppState>,
    Json(req): Json<VoteRequest>,
) -> impl IntoResponse {
    match state
        .namespace
        .governance
        .vote(&req.proposal_id, req.voter, req.approve)
        .await
    {
        Ok(status) => {
            let commitment = state.namespace.route_commitment().await;
            (
                StatusCode::OK,
                Json(json!({
                    "proposal_status": status,
                    "routes_commitment": commitment,
                })),
            )
                .into_response()
        }
        Err(e) => {
            let status = match e {
                governance::GovernanceError::NotParticipant => StatusCode::FORBIDDEN,
                governance::GovernanceError::ProposalNotFound => StatusCode::NOT_FOUND,
                governance::GovernanceError::AlreadyVoted => StatusCode::CONFLICT,
                governance::GovernanceError::ProposalNotPending => StatusCode::GONE,
            };
            (status, Json(json!({"error": e.to_string()}))).into_response()
        }
    }
}

/// GET /routes/commitment — Get current DFA commitment hash.
async fn route_commitment(State(state): State<AppState>) -> impl IntoResponse {
    let table = state.namespace.routing_table.read().await;
    let commitment = hex::encode(table.commitment());
    let version = table.version;

    Json(json!({
        "commitment": commitment,
        "version": version,
    }))
}

// =============================================================================
// Namespace (DFA-Routed) Handlers
// =============================================================================

/// Determine auth level from request headers.
///
/// In a real system this would verify signatures/proofs. For the demo:
/// - Header `X-Auth-Level: admin` → AdminOnly
/// - Header `X-Auth-Level: member` → MembersOnly
/// - Header `X-Auth-Level: multisig:N` → Multisig(N)
/// - No header → Anonymous
fn extract_auth_level(headers: &axum::http::HeaderMap) -> AuthLevel {
    match headers.get("x-auth-level").and_then(|v| v.to_str().ok()) {
        Some("admin") => AuthLevel::Admin,
        Some("member") => AuthLevel::Member,
        Some(s) if s.starts_with("multisig:") => {
            let n = s[9..].parse::<u32>().unwrap_or(0);
            AuthLevel::Multisig(n)
        }
        _ => AuthLevel::Anonymous,
    }
}

/// GET /namespace/*path — DFA-routed read.
///
/// The path is classified by the DFA to determine access. The actual file hash
/// is passed via the `X-Content-Hash` header (since path = route, not file address).
async fn namespace_read(
    State(state): State<AppState>,
    Path(path): Path<String>,
    headers: axum::http::HeaderMap,
) -> impl IntoResponse {
    let auth = extract_auth_level(&headers);

    // The content hash must be provided (path = route classification, not file address).
    let hash_hex = match headers.get("x-content-hash").and_then(|v| v.to_str().ok()) {
        Some(h) => h.to_string(),
        None => {
            // Without a hash, just classify the path and return the classification.
            let table = state.namespace.routing_table.read().await;
            let classification = table.classify(&format!("/{path}"));
            return (
                StatusCode::OK,
                Json(json!({
                    "classification": classification,
                    "message": "provide X-Content-Hash header to read a file",
                })),
            )
                .into_response();
        }
    };

    let hash = match hex::decode(&hash_hex) {
        Ok(h) => h,
        Err(e) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": format!("invalid X-Content-Hash: {e}")})),
            )
                .into_response();
        }
    };

    match state
        .namespace
        .read(&format!("/{path}"), &hash, &auth)
        .await
    {
        Ok(result) => (
            StatusCode::OK,
            [(
                axum::http::header::CONTENT_TYPE,
                "application/octet-stream".to_string(),
            )],
            result.content,
        )
            .into_response(),
        Err(e) => {
            let status = match &e {
                namespace::NamespaceError::NoRoute(_) => StatusCode::NOT_FOUND,
                namespace::NamespaceError::Unauthorized { .. } => StatusCode::FORBIDDEN,
                namespace::NamespaceError::Storage(_) => StatusCode::NOT_FOUND,
            };
            (status, Json(json!({"error": e.to_string()}))).into_response()
        }
    }
}

/// POST /namespace/*path — DFA-routed write.
///
/// The path is classified to determine access. Request body is the file content.
async fn namespace_write(
    State(state): State<AppState>,
    Path(path): Path<String>,
    headers: axum::http::HeaderMap,
    body: Bytes,
) -> impl IntoResponse {
    let auth = extract_auth_level(&headers);
    let content = body.to_vec();

    if content.is_empty() {
        return (
            StatusCode::BAD_REQUEST,
            Json(json!({"error": "empty content"})),
        )
            .into_response();
    }

    let content_type = headers
        .get(axum::http::header::CONTENT_TYPE)
        .and_then(|v| v.to_str().ok())
        .map(|s| s.to_string());

    match state
        .namespace
        .write(&format!("/{path}"), content, content_type, &auth)
        .await
    {
        Ok(result) => (
            StatusCode::CREATED,
            Json(json!({
                "hash": result.hash,
                "size": result.size,
                "route_prefix": result.route_prefix,
                "route_class": result.route_class,
                "new": result.new,
            })),
        )
            .into_response(),
        Err(e) => {
            let status = match &e {
                namespace::NamespaceError::NoRoute(_) => StatusCode::NOT_FOUND,
                namespace::NamespaceError::Unauthorized { .. } => StatusCode::FORBIDDEN,
                namespace::NamespaceError::Storage(_) => StatusCode::CONFLICT,
            };
            (status, Json(json!({"error": e.to_string()}))).into_response()
        }
    }
}

// =============================================================================
// Registry Handlers (Capability Service Mesh)
// =============================================================================

/// Request body for mounting a service.
#[derive(serde::Deserialize)]
struct MountRequest {
    /// The mount path (e.g. "/public/services/alice/price-oracle").
    path: String,
    /// Service name.
    name: String,
    /// Service kind.
    kind: registry::ServiceKind,
    /// The sturdy reference URI.
    sturdy_ref: String,
    /// Owner identity (hex-encoded 32 bytes).
    #[serde(default)]
    owner: Option<String>,
    /// Expected version for CAS (0 for new mounts).
    #[serde(default)]
    expected_version: u64,
    /// Discovery tags.
    #[serde(default)]
    tags: Vec<String>,
    /// Human-readable description.
    #[serde(default)]
    description: String,
    /// Optional expiry timestamp.
    #[serde(default)]
    expires_at: Option<u64>,
    /// Optional health check endpoint.
    #[serde(default)]
    health_endpoint: Option<String>,
}

/// Request body for updating a service.
#[derive(serde::Deserialize)]
struct UpdateRequest {
    /// Service name.
    name: String,
    /// Service kind.
    kind: registry::ServiceKind,
    /// The sturdy reference URI.
    sturdy_ref: String,
    /// Owner identity (hex-encoded 32 bytes).
    #[serde(default)]
    owner: Option<String>,
    /// Expected version for CAS.
    expected_version: u64,
    /// Discovery tags.
    #[serde(default)]
    tags: Vec<String>,
    /// Human-readable description.
    #[serde(default)]
    description: String,
    /// Optional expiry timestamp.
    #[serde(default)]
    expires_at: Option<u64>,
    /// Optional health check endpoint.
    #[serde(default)]
    health_endpoint: Option<String>,
}

/// Query parameters for discovery.
#[derive(serde::Deserialize)]
struct DiscoverQuery {
    /// Tags to filter by (all must match). Passed as repeated `tag=X` params.
    #[serde(default)]
    tag: Vec<String>,
}

/// Parse owner hex string into 32-byte array, defaulting to zeros.
fn parse_owner(owner_hex: Option<&str>) -> [u8; 32] {
    match owner_hex {
        Some(s) => hex::decode(s).unwrap_or([0u8; 32]),
        None => [0u8; 32],
    }
}

/// POST /registry/mount -- Mount a service at a named path (CAS semantics).
async fn registry_mount(
    State(state): State<AppState>,
    headers: axum::http::HeaderMap,
    Json(req): Json<MountRequest>,
) -> impl IntoResponse {
    let auth = extract_auth_level(&headers);
    let owner = parse_owner(req.owner.as_deref());

    let entry = registry::ServiceEntry {
        name: req.name,
        kind: req.kind,
        sturdy_ref: req.sturdy_ref,
        owner,
        version: 0, // set by registry
        tags: req.tags,
        description: req.description,
        registered_at: 0, // set by registry
        expires_at: req.expires_at,
        health_endpoint: req.health_endpoint,
    };

    match state
        .registry
        .mount(
            &state.namespace,
            &req.path,
            entry,
            req.expected_version,
            &auth,
        )
        .await
    {
        Ok(mounted) => (
            StatusCode::CREATED,
            Json(json!({
                "path": mounted.path,
                "name": mounted.entry.name,
                "kind": mounted.entry.kind,
                "version": mounted.entry.version,
                "sturdy_ref": mounted.entry.sturdy_ref,
            })),
        )
            .into_response(),
        Err(e) => {
            let status = match &e {
                registry::RegistryError::VersionMismatch { .. } => StatusCode::CONFLICT,
                registry::RegistryError::NotFound(_) => StatusCode::NOT_FOUND,
                registry::RegistryError::Unauthorized(_) => StatusCode::FORBIDDEN,
                registry::RegistryError::InvalidPath(_) => StatusCode::BAD_REQUEST,
                registry::RegistryError::InvalidEntry(_) => StatusCode::BAD_REQUEST,
            };
            (status, Json(json!({"error": e.to_string()}))).into_response()
        }
    }
}

/// DELETE /registry/unmount/:path -- Remove a service entry.
async fn registry_unmount(
    State(state): State<AppState>,
    Path(path): Path<String>,
    headers: axum::http::HeaderMap,
) -> impl IntoResponse {
    let auth = extract_auth_level(&headers);
    let full_path = format!("/{path}");

    match state
        .registry
        .unmount(&state.namespace, &full_path, &auth)
        .await
    {
        Ok(removed) => (
            StatusCode::OK,
            Json(json!({
                "unmounted": full_path,
                "name": removed.entry.name,
                "version": removed.entry.version,
            })),
        )
            .into_response(),
        Err(e) => {
            let status = match &e {
                registry::RegistryError::NotFound(_) => StatusCode::NOT_FOUND,
                registry::RegistryError::Unauthorized(_) => StatusCode::FORBIDDEN,
                _ => StatusCode::BAD_REQUEST,
            };
            (status, Json(json!({"error": e.to_string()}))).into_response()
        }
    }
}

/// GET /registry/discover?tag=X&tag=Y -- Find services by tag (all must match).
async fn registry_discover(
    State(state): State<AppState>,
    headers: axum::http::HeaderMap,
    axum::extract::Query(query): axum::extract::Query<DiscoverQuery>,
) -> impl IntoResponse {
    let auth = extract_auth_level(&headers);

    let results = state
        .registry
        .discover(&state.namespace, &query.tag, &auth)
        .await;

    Json(json!({
        "services": results,
        "count": results.len(),
        "tags_filter": query.tag,
    }))
}

/// GET /registry/resolve/:path -- Resolve name to sturdy ref (the "introduction").
async fn registry_resolve(
    State(state): State<AppState>,
    Path(path): Path<String>,
    headers: axum::http::HeaderMap,
) -> impl IntoResponse {
    let auth = extract_auth_level(&headers);
    let full_path = format!("/{path}");

    match state
        .registry
        .resolve(&state.namespace, &full_path, &auth)
        .await
    {
        Ok(mounted) => (
            StatusCode::OK,
            Json(json!({
                "path": mounted.path,
                "sturdy_ref": mounted.entry.sturdy_ref,
                "name": mounted.entry.name,
                "kind": mounted.entry.kind,
                "version": mounted.entry.version,
                "tags": mounted.entry.tags,
                "description": mounted.entry.description,
                "health": mounted.health,
            })),
        )
            .into_response(),
        Err(e) => {
            let status = match &e {
                registry::RegistryError::NotFound(_) => StatusCode::NOT_FOUND,
                registry::RegistryError::Unauthorized(_) => StatusCode::FORBIDDEN,
                _ => StatusCode::BAD_REQUEST,
            };
            (status, Json(json!({"error": e.to_string()}))).into_response()
        }
    }
}

/// PUT /registry/update/:path -- Update a mounted service (version CAS).
async fn registry_update(
    State(state): State<AppState>,
    Path(path): Path<String>,
    headers: axum::http::HeaderMap,
    Json(req): Json<UpdateRequest>,
) -> impl IntoResponse {
    let auth = extract_auth_level(&headers);
    let full_path = format!("/{path}");
    let owner = parse_owner(req.owner.as_deref());

    let entry = registry::ServiceEntry {
        name: req.name,
        kind: req.kind,
        sturdy_ref: req.sturdy_ref,
        owner,
        version: 0, // set by registry
        tags: req.tags,
        description: req.description,
        registered_at: 0, // preserved from original
        expires_at: req.expires_at,
        health_endpoint: req.health_endpoint,
    };

    match state
        .registry
        .update(
            &state.namespace,
            &full_path,
            entry,
            req.expected_version,
            &auth,
        )
        .await
    {
        Ok(mounted) => (
            StatusCode::OK,
            Json(json!({
                "path": mounted.path,
                "name": mounted.entry.name,
                "kind": mounted.entry.kind,
                "version": mounted.entry.version,
                "sturdy_ref": mounted.entry.sturdy_ref,
            })),
        )
            .into_response(),
        Err(e) => {
            let status = match &e {
                registry::RegistryError::VersionMismatch { .. } => StatusCode::CONFLICT,
                registry::RegistryError::NotFound(_) => StatusCode::NOT_FOUND,
                registry::RegistryError::Unauthorized(_) => StatusCode::FORBIDDEN,
                _ => StatusCode::BAD_REQUEST,
            };
            (status, Json(json!({"error": e.to_string()}))).into_response()
        }
    }
}

/// GET /registry/health/:path -- Check if mounted service is alive.
async fn registry_health(
    State(state): State<AppState>,
    Path(path): Path<String>,
    headers: axum::http::HeaderMap,
) -> impl IntoResponse {
    let auth = extract_auth_level(&headers);
    let full_path = format!("/{path}");

    match state
        .registry
        .health(&state.namespace, &full_path, &auth)
        .await
    {
        Ok(status) => (
            StatusCode::OK,
            Json(json!({
                "path": full_path,
                "health": status,
            })),
        )
            .into_response(),
        Err(e) => {
            let status = match &e {
                registry::RegistryError::NotFound(_) => StatusCode::NOT_FOUND,
                registry::RegistryError::Unauthorized(_) => StatusCode::FORBIDDEN,
                _ => StatusCode::BAD_REQUEST,
            };
            (status, Json(json!({"error": e.to_string()}))).into_response()
        }
    }
}

// =============================================================================
// Governance Handlers
// =============================================================================

/// GET /governance/constitution — Current participants, threshold, routes_commitment.
async fn get_constitution(State(state): State<AppState>) -> impl IntoResponse {
    let constitution = state.namespace.governance.constitution().await;
    let threshold = state.namespace.governance.threshold().await;

    Json(json!({
        "participants": constitution.participants,
        "threshold": threshold,
        "threshold_formula": "2n/3 + 1",
        "routes_commitment": constitution.routes_commitment,
    }))
}

/// GET /governance/proposals — Pending proposals.
async fn get_proposals(State(state): State<AppState>) -> impl IntoResponse {
    let pending = state.namespace.governance.pending_proposals().await;
    let all = state.namespace.governance.all_proposals().await;
    let history = state.namespace.governance.amendment_history().await;

    Json(json!({
        "pending": pending,
        "all": all,
        "amendments": history,
    }))
}

// =============================================================================
// Sharing Handlers
// =============================================================================

/// POST /share/:hash — Export a file as a shareable pyana:// URI.
async fn share_file(
    State(state): State<AppState>,
    Path(hash_hex): Path<String>,
) -> impl IntoResponse {
    let hash = match hex::decode(&hash_hex) {
        Ok(h) => h,
        Err(e) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(json!({"error": format!("invalid hash: {e}")})),
            )
                .into_response();
        }
    };

    match state.namespace.share_file(&hash).await {
        Ok(uri) => (
            StatusCode::OK,
            Json(json!({
                "uri": uri,
                "hash": hash_hex,
                "note": "Share this URI with anyone who should access this file. The URI is a bearer capability — possession = authority.",
            })),
        )
            .into_response(),
        Err(e) => (
            StatusCode::NOT_FOUND,
            Json(json!({"error": e.to_string()})),
        )
            .into_response(),
    }
}

// =============================================================================
// Integration Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use axum::body::Body;
    use axum::http::Request;
    use tower::ServiceExt as _;

    fn test_app() -> Router {
        let participants = default_participants();
        let federation_id = *blake3::hash(b"test").as_bytes();
        let namespace = Namespace::new(participants, federation_id);
        let state = AppState {
            namespace,
            registry: Registry::new(),
            admin_token: AdminToken::open(),
        };
        app_router().with_state(state)
    }

    async fn request(
        app: &Router,
        method: &str,
        uri: &str,
        headers: &[(&str, &str)],
        body: impl Into<Body>,
    ) -> (StatusCode, serde_json::Value) {
        let mut builder = Request::builder().method(method).uri(uri);
        for (k, v) in headers {
            builder = builder.header(*k, *v);
        }
        let req = builder.body(body.into()).unwrap();
        let response = app.clone().oneshot(req).await.unwrap();
        let status = response.status();
        let body_bytes = axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap();
        let json = serde_json::from_slice(&body_bytes)
            .unwrap_or_else(|_| json!({"_raw": String::from_utf8_lossy(&body_bytes).to_string()}));
        (status, json)
    }

    #[tokio::test]
    async fn end_to_end_file_lifecycle() {
        let app = test_app();

        // 1. Upload a file.
        let (status, json) = request(&app, "POST", "/files", &[], "hello governed world").await;
        assert_eq!(status, StatusCode::CREATED);
        let hash = json["hash"].as_str().unwrap().to_string();
        assert_eq!(json["size"].as_u64().unwrap(), 20);
        assert!(json["new"].as_bool().unwrap());

        // 2. Read it back (returns raw bytes, not JSON).
        let req = Request::builder()
            .method("GET")
            .uri(format!("/files/{hash}"))
            .body(Body::empty())
            .unwrap();
        let response = app.clone().oneshot(req).await.unwrap();
        assert_eq!(response.status(), StatusCode::OK);
        let body = axum::body::to_bytes(response.into_body(), usize::MAX)
            .await
            .unwrap();
        assert_eq!(&body[..], b"hello governed world");

        // 3. Splice (update).
        let (status, json) = request(
            &app,
            "PUT",
            &format!("/files/{hash}"),
            &[],
            "updated content",
        )
        .await;
        assert_eq!(status, StatusCode::OK);
        assert!(json["old_nullified"].as_bool().unwrap());
        let new_hash = json["new_hash"].as_str().unwrap().to_string();

        // 4. Old hash is now gone.
        let (status, _) = request(&app, "GET", &format!("/files/{hash}"), &[], Body::empty()).await;
        assert_eq!(status, StatusCode::NOT_FOUND);

        // 5. Delete new file.
        let (status, json) = request(
            &app,
            "DELETE",
            &format!("/files/{new_hash}"),
            &[],
            Body::empty(),
        )
        .await;
        assert_eq!(status, StatusCode::OK);
        assert!(json["nullifier"].as_str().is_some());
    }

    #[tokio::test]
    async fn governance_propose_and_vote() {
        let app = test_app();

        // Propose adding a /grants/ route.
        let propose_body = serde_json::to_string(&json!({
            "proposer": "alice",
            "routes": [
                {"prefix": "/public/", "class": "public", "description": "Public files"},
                {"prefix": "/grants/", "class": "members_only", "description": "Grant applications"}
            ],
            "description": "Add grants route for the new program"
        }))
        .unwrap();

        let (status, json) = request(
            &app,
            "POST",
            "/routes/propose",
            &[("content-type", "application/json")],
            propose_body,
        )
        .await;
        assert_eq!(status, StatusCode::CREATED);
        let proposal_id = json["proposal_id"].as_str().unwrap().to_string();

        // Vote: alice, bob, carol, dave all approve (need 4 out of 5 for threshold).
        for voter in &["alice", "bob", "carol", "dave"] {
            let vote_body = serde_json::to_string(&json!({
                "voter": voter,
                "proposal_id": proposal_id,
                "approve": true
            }))
            .unwrap();

            let (status, _) = request(
                &app,
                "POST",
                "/routes/vote",
                &[("content-type", "application/json")],
                vote_body,
            )
            .await;
            assert_eq!(status, StatusCode::OK);
        }

        // Check that routes were updated.
        let (status, json) = request(&app, "GET", "/routes", &[], Body::empty()).await;
        assert_eq!(status, StatusCode::OK);
        let routes = json["routes"].as_array().unwrap();
        // Should have /grants/ and /public/ (the proposed table)
        assert_eq!(routes.len(), 2);
        assert_eq!(json["version"].as_u64().unwrap(), 1);
    }

    #[tokio::test]
    async fn namespace_dfa_routing() {
        let app = test_app();

        // Write to public route (anonymous).
        let (status, json) = request(
            &app,
            "POST",
            "/namespace/public/readme.txt",
            &[],
            "public file content",
        )
        .await;
        assert_eq!(status, StatusCode::CREATED);
        assert_eq!(json["route_class"].as_str().unwrap(), "public");
        assert_eq!(json["route_prefix"].as_str().unwrap(), "/public/");

        // Write to members route (anonymous -> denied).
        let (status, _) = request(
            &app,
            "POST",
            "/namespace/members/secret.txt",
            &[],
            "member content",
        )
        .await;
        assert_eq!(status, StatusCode::FORBIDDEN);

        // Write to members route (with member auth).
        let (status, json) = request(
            &app,
            "POST",
            "/namespace/members/secret.txt",
            &[("x-auth-level", "member")],
            "member content",
        )
        .await;
        assert_eq!(status, StatusCode::CREATED);
        assert_eq!(json["route_class"].as_str().unwrap(), "members_only");
    }

    #[tokio::test]
    async fn share_produces_pyana_uri() {
        let app = test_app();

        // Upload a file first.
        let (_, json) = request(&app, "POST", "/files", &[], "share me").await;
        let hash = json["hash"].as_str().unwrap().to_string();

        // Share it.
        let (status, json) =
            request(&app, "POST", &format!("/share/{hash}"), &[], Body::empty()).await;
        assert_eq!(status, StatusCode::OK);
        let uri = json["uri"].as_str().unwrap();
        assert!(uri.starts_with("pyana://"));
    }
}
