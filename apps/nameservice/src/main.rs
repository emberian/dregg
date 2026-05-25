//! Pyana Name Service — federation name directory server.
//!
//! Handles registration, resolution, delegation, anti-squatting (rent-based expiry),
//! reverse lookups, and cross-federation resolution.
//!
//! ## Endpoints
//!
//! - `POST /names/register` — register a name (pays rent)
//! - `DELETE /names/:name` — release a name
//! - `GET /names/resolve/:name` — resolve flat name → sturdy ref
//! - `GET /names/resolve/*path` — hierarchical resolution (dotted)
//! - `GET /names/whois/:cell_id` — reverse lookup
//! - `POST /names/delegate` — delegate sub-naming authority
//! - `POST /names/transfer` — transfer name ownership
//! - `GET /names/list` — list all registered names (paginated)
//! - `GET /names/search?prefix=X` — search by prefix
//! - `POST /names/dispute` — file a dispute
//! - `GET /names/rental/:name` — check rental status
//! - `POST /names/renew/:name` — pay rent to extend expiry

mod cross_fed;
mod delegation;
mod effects;
mod registry;
mod rental;
mod resolution;
mod reverse;

use axum::extract::{Path, Query, State};
use axum::http::StatusCode;
use axum::response::IntoResponse;
use axum::routing::{delete as delete_route, get, post};
use axum::{Json, Router};
use serde::Deserialize;
use serde_json::json;

use pyana_app_framework::cipherclerk::EmbeddedExecutor;
use pyana_app_framework::server::{AppConfig, AppServer};
use pyana_app_framework::{AgentCipherclerk, AppCipherclerk, CellId};

use cross_fed::MetaDirectory;
use registry::{DelegationAuthority, NameRegistry, RegistryError};
use rental::RentalPolicy;
use resolution::NameResolver;
use reverse::ReverseIndex;

// =============================================================================
// Application State
// =============================================================================

/// Shared application state for all handlers.
#[derive(Clone)]
struct AppState {
    /// The name registry.
    registry: NameRegistry,
    /// The name resolver.
    resolver: NameResolver,
    /// The reverse index.
    reverse_index: ReverseIndex,
    /// The rental policy.
    rental_policy: RentalPolicy,
    /// The meta-directory for cross-federation lookups.
    meta_directory: MetaDirectory,
    /// Current epoch (in a real system this comes from federation consensus).
    current_epoch: u64,
    /// Framework-issued cipherclerk handle. Used to sign on-ledger Actions
    /// emitted by the registry path (replaces the pre-framework
    /// `[0u8; 64]` placeholder signatures).
    cipherclerk: AppCipherclerk,
    /// Embedded executor closing `APPS-USERSPACE-GAPS.md` §Gap 4: the
    /// framework runs a private ledger + turn executor in-process, so
    /// the registration handler can actually submit its signed Action
    /// and observe the resulting `TurnReceipt` (instead of building the
    /// action and dropping it on the floor).
    executor: EmbeddedExecutor,
}

// =============================================================================
// Main
// =============================================================================

#[tokio::main]
async fn main() {
    let config = AppConfig::from_env();

    let registry = NameRegistry::new();
    let resolver = NameResolver::new(registry.clone());
    let reverse_index = ReverseIndex::new();
    let rental_policy = RentalPolicy::default();
    let meta_directory = MetaDirectory::new();

    // Build the framework cipherclerk. In a real deployment the seed comes
    // from key management (env-supplied mnemonic, HSM, etc.). For now a
    // fresh cipherclerk per process keeps the surface honest: signatures
    // verify against the cipherclerk's pubkey, no placeholders.
    let cipherclerk = AppCipherclerk::new(AgentCipherclerk::new(), nameservice_federation_id());

    // Build the embedded executor: a per-process Ledger + TurnExecutor
    // bound to the same cipherclerk identity (shared via the cipherclerk's inner
    // `Arc<RwLock<AgentCipherclerk>>` so signing handle and submission handle
    // see the same receipt chain). Closes APPS-USERSPACE-GAPS.md §Gap 4.
    let executor = EmbeddedExecutor::new(&cipherclerk, "nameservice");

    let state = AppState {
        registry,
        resolver,
        reverse_index,
        rental_policy,
        meta_directory,
        current_epoch: 1,
        cipherclerk: cipherclerk.clone(),
        executor: executor.clone(),
    };

    let app_routes = app_router().with_state(state);

    AppServer::new(config)
        .service_name("pyana-nameservice")
        .with_health()
        .with_cors()
        .with_cipherclerk(cipherclerk)
        .with_embedded_executor(executor)
        .routes(app_routes)
        .serve()
        .await
        .unwrap();
}

/// 32-byte federation identifier for the nameservice's signing-message
/// binding. Domain-tagged hash so every process in the same logical
/// federation derives the same id; swap in real federation config when
/// the discovery layer surfaces it.
fn nameservice_federation_id() -> [u8; 32] {
    *blake3::Hasher::new_derive_key("pyana-nameservice-federation-id-v1")
        .finalize()
        .as_bytes()
}

/// Build the application router.
fn app_router() -> Router<AppState> {
    Router::new()
        .route("/names/register", post(register_name))
        .route("/names/{name}", delete_route(release_name))
        .route("/names/resolve/{*path}", get(resolve_name_path))
        .route("/names/whois/{cell_id}", get(whois_lookup))
        .route("/names/delegate", post(delegate_subname))
        .route("/names/transfer", post(transfer_name))
        .route("/names/list", get(list_names))
        .route("/names/search", get(search_names))
        .route("/names/dispute", post(file_dispute))
        .route("/names/rental/{name}", get(rental_status))
        .route("/names/renew/{name}", post(renew_name))
}

// =============================================================================
// Request/Response Types
// =============================================================================

#[derive(Deserialize)]
struct RegisterRequest {
    /// Name to register.
    name: String,
    /// Target URI the name should resolve to.
    target: String,
    /// Owner public key (hex-encoded 32 bytes).
    owner: String,
    /// Number of epochs to prepay rent.
    #[serde(default = "default_rental_epochs")]
    rental_epochs: u64,
    /// Delegation authority.
    #[serde(default = "default_delegation")]
    delegation: DelegationAuthority,
}

fn default_rental_epochs() -> u64 {
    100
}
fn default_delegation() -> DelegationAuthority {
    DelegationAuthority::None
}

#[derive(Deserialize)]
struct DelegateRequest {
    /// Parent name to delegate under.
    parent_name: String,
    /// Child label for the sub-name.
    child_label: String,
    /// Target URI.
    target: String,
    /// Caller (owner of parent, hex-encoded).
    owner: String,
    /// Rental epochs for the sub-name.
    #[serde(default = "default_rental_epochs")]
    rental_epochs: u64,
}

#[derive(Deserialize)]
struct TransferRequest {
    /// Name to transfer.
    name: String,
    /// Current owner (hex-encoded).
    owner: String,
    /// New owner (hex-encoded).
    new_owner: String,
}

#[derive(Deserialize)]
struct ListQuery {
    #[serde(default)]
    offset: usize,
    #[serde(default = "default_limit")]
    limit: usize,
}

fn default_limit() -> usize {
    50
}

#[derive(Deserialize)]
struct SearchQuery {
    prefix: String,
}

#[derive(Deserialize)]
struct DisputeRequest {
    /// Name being disputed.
    name: String,
    /// Challenger (hex-encoded public key).
    challenger: String,
    /// Reason for the dispute.
    reason: String,
    /// Bond amount (computrons).
    bond: u64,
}

#[derive(Deserialize)]
struct RenewRequest {
    /// Owner (hex-encoded).
    owner: String,
    /// Additional epochs to pay for.
    additional_epochs: u64,
    /// Available computrons for payment.
    #[serde(default = "default_computrons")]
    available_computrons: u64,
}

fn default_computrons() -> u64 {
    u64::MAX
}

// =============================================================================
// Handlers
// =============================================================================

/// POST /names/register — register a name (pays rent).
async fn register_name(
    State(state): State<AppState>,
    Json(req): Json<RegisterRequest>,
) -> impl IntoResponse {
    let owner = match parse_owner_hex(&req.owner) {
        Ok(o) => o,
        Err(e) => return error_response(StatusCode::BAD_REQUEST, &e),
    };

    let rent_rate = state.rental_policy.rate_for_name(&req.name);

    match state
        .registry
        .register(
            &req.name,
            req.target,
            owner,
            req.delegation,
            state.current_epoch,
            req.rental_epochs,
            rent_rate,
        )
        .await
    {
        Ok(entry) => {
            state.reverse_index.on_register(&entry).await;

            // Emit a real, framework-signed on-ledger Action. The
            // action carries an EmitEvent + SetField pair. No
            // placeholder signatures — the framework cclerk binds the
            // signature to its federation_id.
            //
            // Userspace stance: name-registration policy lives here in
            // app code; the ledger sees only the two primitive effects
            // (EmitEvent + SetField). A dedicated `Effect::RegisterName`
            // variant would be a misuse of the Effect enum — apps are
            // userspace and should compose primitives, not extend the
            // kernel. Uniqueness enforcement (name not previously bound)
            // belongs in a cell-program caveat; see
            // `APPS-USERSPACE-GAPS.md` for the gap analysis on
            // expressing that caveat from userspace today.
            //
            // §Gap 4 closure: the signed action is submitted to the
            // framework's embedded executor (private per-process ledger)
            // and the resulting TurnReceipt is surfaced in the response.
            // The action is no longer authored-and-dropped.
            let registry_cell = registry_cell_id();
            let registration_action = effects::build_register_action(
                &state.cipherclerk,
                registry_cell,
                &entry.name,
                entry.owner,
            );

            // The action targets `registry_cell`, but the executor's
            // private ledger only knows about the cipherclerk's own cell.
            // Re-sign a self-targeted variant so the embedded turn lands
            // on the agent cell (the executor's seeded cell). The on-
            // ledger meaning is the same: an EmitEvent + SetField pair
            // proves the registration happened with this cipherclerk's
            // identity, bound to its federation_id and chain head.
            let self_action = state
                .cipherclerk
                .make_self_action("register_name", registration_action.effects.clone());
            let submission = state
                .executor
                .submit_action(&state.cipherclerk, self_action);

            match submission {
                Ok(receipt) => (
                    StatusCode::CREATED,
                    Json(json!({
                        "name": entry.name,
                        "target": entry.target,
                        "owner": reverse::hex_encode(&entry.owner),
                        "registered_at": entry.registered_at,
                        "expires_at": entry.expires_at,
                        "version": entry.version,
                        "rent_rate": entry.rent_rate,
                        "cost_total": rent_rate * req.rental_epochs,
                        // §Gap 4 evidence: a real receipt observed by
                        // the registration handler.
                        "turn_receipt": {
                            "turn_hash": reverse::hex_encode(&receipt.turn_hash),
                            "post_state_hash": reverse::hex_encode(&receipt.post_state_hash),
                            "events": receipt.emitted_events.len(),
                        },
                    })),
                )
                    .into_response(),
                Err(e) => {
                    // Surface the executor error but keep the registry
                    // entry committed — the off-chain side already
                    // accepted the registration. The ledger-side error
                    // is an integration signal (e.g., insufficient fee,
                    // precondition failure) the operator should see.
                    error_response(
                        StatusCode::INTERNAL_SERVER_ERROR,
                        &format!("on-ledger submission failed: {e}"),
                    )
                }
            }
        }
        Err(e) => registry_error_response(e),
    }
}

/// Deterministic `CellId` for the nameservice registry cell. In a real
/// federation deployment this comes from federation config; for now we
/// derive it from a domain-tagged hash so all instances agree.
fn registry_cell_id() -> CellId {
    let bytes = *blake3::Hasher::new_derive_key("pyana-nameservice-registry-cell-v1")
        .finalize()
        .as_bytes();
    CellId::from_bytes(bytes)
}

/// DELETE /names/:name — release a name.
async fn release_name(
    State(state): State<AppState>,
    Path(name): Path<String>,
    headers: axum::http::HeaderMap,
) -> impl IntoResponse {
    let owner_hex = headers
        .get("x-owner")
        .and_then(|v| v.to_str().ok())
        .unwrap_or("");

    let owner = match parse_owner_hex(owner_hex) {
        Ok(o) => o,
        Err(e) => return error_response(StatusCode::BAD_REQUEST, &e),
    };

    match state.registry.release(&name, &owner).await {
        Ok(entry) => {
            state.reverse_index.on_release(&entry).await;
            (
                StatusCode::OK,
                Json(json!({
                    "released": entry.name,
                    "previous_target": entry.target,
                })),
            )
                .into_response()
        }
        Err(e) => registry_error_response(e),
    }
}

/// GET /names/resolve/*path — resolve a name (flat or hierarchical).
///
/// Handles both "/names/resolve/alice" and "/names/resolve/oracle.alice".
/// Path segments separated by "/" are joined with dots for resolution.
async fn resolve_name_path(
    State(state): State<AppState>,
    Path(path): Path<String>,
) -> impl IntoResponse {
    // Normalize: if path contains slashes, convert to dots for hierarchical lookup.
    let name = if path.contains('/') {
        path.replace('/', ".")
    } else {
        path
    };

    match state.resolver.resolve(&name, state.current_epoch).await {
        Ok(resolved) => (
            StatusCode::OK,
            Json(json!({
                "name": resolved.name,
                "target": resolved.target,
                "provenance": resolved.provenance,
            })),
        )
            .into_response(),
        Err(_) => {
            // Try cross-federation resolution for dotted names.
            if name.contains('.') {
                match cross_fed::resolve_cross_federation(&state.meta_directory, &name).await {
                    Ok(cf) => (
                        StatusCode::OK,
                        Json(json!({
                            "name": cf.resolved.name,
                            "target": cf.resolved.target,
                            "provenance": cf.resolved.provenance,
                            "federation": cf.federation,
                            "via_nameservice": cf.via_nameservice,
                        })),
                    )
                        .into_response(),
                    Err(e) => error_response(StatusCode::NOT_FOUND, &e.to_string()),
                }
            } else {
                error_response(StatusCode::NOT_FOUND, &format!("name not found: {name}"))
            }
        }
    }
}

/// GET /names/whois/:cell_id — reverse lookup.
async fn whois_lookup(
    State(state): State<AppState>,
    Path(cell_id): Path<String>,
) -> impl IntoResponse {
    let results = reverse::whois(&state.registry, &cell_id).await;
    (
        StatusCode::OK,
        Json(json!({
            "cell_id": cell_id,
            "names": results,
            "count": results.len(),
        })),
    )
        .into_response()
}

/// POST /names/delegate — delegate sub-naming authority.
async fn delegate_subname(
    State(state): State<AppState>,
    Json(req): Json<DelegateRequest>,
) -> impl IntoResponse {
    let owner = match parse_owner_hex(&req.owner) {
        Ok(o) => o,
        Err(e) => return error_response(StatusCode::BAD_REQUEST, &e),
    };

    match delegation::register_subname(
        &state.registry,
        &req.parent_name,
        &req.child_label,
        req.target,
        &owner,
        state.current_epoch,
        req.rental_epochs,
        &state.rental_policy,
    )
    .await
    {
        Ok(entry) => {
            state.reverse_index.on_register(&entry).await;
            (
                StatusCode::CREATED,
                Json(json!({
                    "name": entry.name,
                    "target": entry.target,
                    "owner": reverse::hex_encode(&entry.owner),
                    "parent": req.parent_name,
                    "expires_at": entry.expires_at,
                    "version": entry.version,
                })),
            )
                .into_response()
        }
        Err(e) => registry_error_response(e),
    }
}

/// POST /names/transfer — transfer name ownership.
async fn transfer_name(
    State(state): State<AppState>,
    Json(req): Json<TransferRequest>,
) -> impl IntoResponse {
    let owner = match parse_owner_hex(&req.owner) {
        Ok(o) => o,
        Err(e) => return error_response(StatusCode::BAD_REQUEST, &e),
    };
    let new_owner = match parse_owner_hex(&req.new_owner) {
        Ok(o) => o,
        Err(e) => return error_response(StatusCode::BAD_REQUEST, &e),
    };

    match state.registry.transfer(&req.name, &owner, new_owner).await {
        Ok(entry) => (
            StatusCode::OK,
            Json(json!({
                "name": entry.name,
                "new_owner": reverse::hex_encode(&entry.owner),
                "version": entry.version,
            })),
        )
            .into_response(),
        Err(e) => registry_error_response(e),
    }
}

/// GET /names/list — list all registered names (paginated).
async fn list_names(
    State(state): State<AppState>,
    Query(query): Query<ListQuery>,
) -> impl IntoResponse {
    let entries = state.registry.list(query.offset, query.limit).await;
    let total = state.registry.count().await;
    (
        StatusCode::OK,
        Json(json!({
            "names": entries,
            "offset": query.offset,
            "limit": query.limit,
            "total": total,
        })),
    )
        .into_response()
}

/// GET /names/search?prefix=X — search by prefix.
async fn search_names(
    State(state): State<AppState>,
    Query(query): Query<SearchQuery>,
) -> impl IntoResponse {
    let results = state.registry.search_prefix(&query.prefix).await;
    (
        StatusCode::OK,
        Json(json!({
            "prefix": query.prefix,
            "results": results,
            "count": results.len(),
        })),
    )
        .into_response()
}

/// POST /names/dispute — file a dispute on a contested name.
async fn file_dispute(
    State(state): State<AppState>,
    Json(req): Json<DisputeRequest>,
) -> impl IntoResponse {
    // Verify the name exists.
    let entry = match state.registry.lookup(&req.name, state.current_epoch).await {
        Some(e) => e,
        None => return error_response(StatusCode::NOT_FOUND, "name not found"),
    };

    // Verify minimum bond (10% of annual rent).
    let min_bond = entry.rent_rate * 10; // 10 epochs worth
    if req.bond < min_bond {
        return error_response(
            StatusCode::BAD_REQUEST,
            &format!(
                "insufficient dispute bond: need at least {min_bond}, got {}",
                req.bond
            ),
        );
    }

    // Generate dispute ID.
    let dispute_id = *blake3::hash(
        format!("{}:{}:{}", req.name, req.challenger, state.current_epoch).as_bytes(),
    )
    .as_bytes();

    // Mark as disputed.
    let _ = state.registry.mark_disputed(&req.name, dispute_id).await;

    (
        StatusCode::CREATED,
        Json(json!({
            "dispute_id": reverse::hex_encode(&dispute_id),
            "name": req.name,
            "challenger": req.challenger,
            "current_owner": reverse::hex_encode(&entry.owner),
            "bond_locked": req.bond,
            "reason": req.reason,
            "status": "pending",
        })),
    )
        .into_response()
}

/// GET /names/rental/:name — check rental status.
async fn rental_status(
    State(state): State<AppState>,
    Path(name): Path<String>,
) -> impl IntoResponse {
    match state.registry.lookup(&name, state.current_epoch).await {
        Some(entry) => {
            let status = rental::rental_status(&entry, state.current_epoch, &state.rental_policy);
            (StatusCode::OK, Json(json!(status))).into_response()
        }
        None => error_response(StatusCode::NOT_FOUND, &format!("name not found: {name}")),
    }
}

/// POST /names/renew/:name — pay rent to extend expiry.
async fn renew_name(
    State(state): State<AppState>,
    Path(name): Path<String>,
    Json(req): Json<RenewRequest>,
) -> impl IntoResponse {
    let owner = match parse_owner_hex(&req.owner) {
        Ok(o) => o,
        Err(e) => return error_response(StatusCode::BAD_REQUEST, &e),
    };

    match rental::renew_name(
        &state.registry,
        &name,
        &owner,
        req.additional_epochs,
        req.available_computrons,
        &state.rental_policy,
    )
    .await
    {
        Ok(entry) => (
            StatusCode::OK,
            Json(json!({
                "name": entry.name,
                "expires_at": entry.expires_at,
                "rent_paid_until": entry.rent_paid_until,
                "version": entry.version,
            })),
        )
            .into_response(),
        Err(e) => registry_error_response(e),
    }
}

// =============================================================================
// Helpers
// =============================================================================

/// Parse a hex-encoded owner string into a 32-byte array.
fn parse_owner_hex(hex: &str) -> Result<[u8; 32], String> {
    if hex.len() != 64 {
        return Err(format!(
            "owner must be 64 hex characters (32 bytes), got {}",
            hex.len()
        ));
    }
    let mut bytes = [0u8; 32];
    for i in 0..32 {
        bytes[i] = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16)
            .map_err(|e| format!("invalid hex at position {}: {e}", i * 2))?;
    }
    Ok(bytes)
}

/// Create an error response.
fn error_response(status: StatusCode, msg: &str) -> axum::response::Response {
    (status, Json(json!({"error": msg}))).into_response()
}

/// Map registry errors to HTTP responses.
fn registry_error_response(err: RegistryError) -> axum::response::Response {
    let status = match &err {
        RegistryError::AlreadyRegistered { .. } => StatusCode::CONFLICT,
        RegistryError::NotFound(_) => StatusCode::NOT_FOUND,
        RegistryError::VersionMismatch { .. } => StatusCode::CONFLICT,
        RegistryError::Unauthorized(_) => StatusCode::FORBIDDEN,
        RegistryError::InvalidName(_) => StatusCode::BAD_REQUEST,
        RegistryError::InsufficientFunds { .. } => StatusCode::PAYMENT_REQUIRED,
        RegistryError::Disputed { .. } => StatusCode::CONFLICT,
    };
    (status, Json(json!({"error": err.to_string()}))).into_response()
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use axum::body::Body;
    use axum::http::Request;
    use tower::ServiceExt as _;

    fn test_app() -> Router {
        let registry = NameRegistry::new();
        let resolver = NameResolver::new(registry.clone());
        let reverse_index = ReverseIndex::new();
        let rental_policy = RentalPolicy::default();
        let meta_directory = MetaDirectory::new();
        let cipherclerk = AppCipherclerk::new(AgentCipherclerk::new(), nameservice_federation_id());
        let executor = EmbeddedExecutor::new(&cipherclerk, "nameservice");

        let state = AppState {
            registry,
            resolver,
            reverse_index,
            rental_policy,
            meta_directory,
            current_epoch: 100,
            cipherclerk,
            executor,
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

    fn alice_owner() -> String {
        "01".repeat(32)
    }

    fn bob_owner() -> String {
        "02".repeat(32)
    }

    /// §Gap 4 end-to-end closure: POST /names/register → signed action
    /// → embedded executor applies → real `TurnReceipt` returned in the
    /// HTTP response body. Proves the "action authored and dropped on
    /// the floor" seam is closed.
    #[tokio::test]
    async fn register_round_trip_returns_real_receipt() {
        let app = test_app();
        let body = serde_json::to_string(&json!({
            "name": "gap4-witness",
            "target": "pyana://fed/witness",
            "owner": alice_owner(),
            "rental_epochs": 25,
        }))
        .unwrap();

        let (status, json) = request(
            &app,
            "POST",
            "/names/register",
            &[("content-type", "application/json")],
            body,
        )
        .await;
        assert_eq!(
            status,
            StatusCode::CREATED,
            "register should succeed: {json}"
        );

        // The receipt block exists and carries real (non-zero) hashes.
        let receipt = &json["turn_receipt"];
        assert!(receipt.is_object(), "turn_receipt missing: {json}");
        let turn_hash = receipt["turn_hash"].as_str().expect("turn_hash present");
        assert_eq!(turn_hash.len(), 64, "turn_hash should be 32-byte hex");
        assert_ne!(
            turn_hash,
            &"00".repeat(32),
            "turn_hash must not be the zero hash — receipt is real"
        );

        // The events count surfaces the EmitEvent we asked for (1 event).
        assert_eq!(
            receipt["events"].as_u64(),
            Some(1),
            "exactly one EmitEvent expected: {json}"
        );
    }

    #[tokio::test]
    async fn register_and_resolve() {
        let app = test_app();

        // Register "alice"
        let body = serde_json::to_string(&json!({
            "name": "alice",
            "target": "pyana://fed/alice/swiss",
            "owner": alice_owner(),
            "rental_epochs": 50,
        }))
        .unwrap();

        let (status, json) = request(
            &app,
            "POST",
            "/names/register",
            &[("content-type", "application/json")],
            body,
        )
        .await;
        assert_eq!(status, StatusCode::CREATED);
        assert_eq!(json["name"], "alice");
        assert_eq!(json["version"], 1);

        // Resolve "alice"
        let (status, json) = request(&app, "GET", "/names/resolve/alice", &[], Body::empty()).await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(json["target"], "pyana://fed/alice/swiss");
    }

    #[tokio::test]
    async fn sub_delegation_owner_creates() {
        let app = test_app();

        // Register "alice" with sub-prefix delegation.
        let body = serde_json::to_string(&json!({
            "name": "alice",
            "target": "pyana://fed/alice/swiss",
            "owner": alice_owner(),
            "rental_epochs": 50,
            "delegation": {"type": "sub_prefix", "prefix": "alice"},
        }))
        .unwrap();

        let (status, _) = request(
            &app,
            "POST",
            "/names/register",
            &[("content-type", "application/json")],
            body,
        )
        .await;
        assert_eq!(status, StatusCode::CREATED);

        // Delegate "oracle.alice"
        let body = serde_json::to_string(&json!({
            "parent_name": "alice",
            "child_label": "oracle",
            "target": "pyana://fed/oracle/swiss",
            "owner": alice_owner(),
            "rental_epochs": 50,
        }))
        .unwrap();

        let (status, json) = request(
            &app,
            "POST",
            "/names/delegate",
            &[("content-type", "application/json")],
            body,
        )
        .await;
        assert_eq!(status, StatusCode::CREATED);
        assert_eq!(json["name"], "oracle.alice");
    }

    #[tokio::test]
    async fn sub_delegation_non_owner_blocked() {
        let app = test_app();

        // Register "alice" with delegation.
        let body = serde_json::to_string(&json!({
            "name": "alice",
            "target": "pyana://fed/alice/swiss",
            "owner": alice_owner(),
            "rental_epochs": 50,
            "delegation": {"type": "sub_prefix", "prefix": "alice"},
        }))
        .unwrap();
        request(
            &app,
            "POST",
            "/names/register",
            &[("content-type", "application/json")],
            body,
        )
        .await;

        // Bob tries to delegate under alice.
        let body = serde_json::to_string(&json!({
            "parent_name": "alice",
            "child_label": "evil",
            "target": "pyana://fed/evil/swiss",
            "owner": bob_owner(),
            "rental_epochs": 50,
        }))
        .unwrap();

        let (status, _) = request(
            &app,
            "POST",
            "/names/delegate",
            &[("content-type", "application/json")],
            body,
        )
        .await;
        assert_eq!(status, StatusCode::FORBIDDEN);
    }

    #[tokio::test]
    async fn transfer_changes_owner() {
        let app = test_app();

        // Register
        let body = serde_json::to_string(&json!({
            "name": "transferme",
            "target": "pyana://x",
            "owner": alice_owner(),
            "rental_epochs": 50,
        }))
        .unwrap();
        request(
            &app,
            "POST",
            "/names/register",
            &[("content-type", "application/json")],
            body,
        )
        .await;

        // Transfer
        let body = serde_json::to_string(&json!({
            "name": "transferme",
            "owner": alice_owner(),
            "new_owner": bob_owner(),
        }))
        .unwrap();

        let (status, json) = request(
            &app,
            "POST",
            "/names/transfer",
            &[("content-type", "application/json")],
            body,
        )
        .await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(json["new_owner"], bob_owner());
    }

    #[tokio::test]
    async fn list_and_search() {
        let app = test_app();

        // Register several names.
        for name in &["alpha", "alpha-two", "beta"] {
            let body = serde_json::to_string(&json!({
                "name": name,
                "target": format!("pyana://{name}"),
                "owner": alice_owner(),
                "rental_epochs": 50,
            }))
            .unwrap();
            request(
                &app,
                "POST",
                "/names/register",
                &[("content-type", "application/json")],
                body,
            )
            .await;
        }

        // List
        let (status, json) = request(
            &app,
            "GET",
            "/names/list?offset=0&limit=10",
            &[],
            Body::empty(),
        )
        .await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(json["total"], 3);

        // Search by prefix
        let (status, json) = request(
            &app,
            "GET",
            "/names/search?prefix=alpha",
            &[],
            Body::empty(),
        )
        .await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(json["count"], 2);
    }

    #[tokio::test]
    async fn reverse_lookup() {
        let app = test_app();

        // Register a name.
        let body = serde_json::to_string(&json!({
            "name": "findme",
            "target": "pyana://findme-target",
            "owner": alice_owner(),
            "rental_epochs": 50,
        }))
        .unwrap();
        request(
            &app,
            "POST",
            "/names/register",
            &[("content-type", "application/json")],
            body,
        )
        .await;

        // Whois by owner.
        let (status, json) = request(
            &app,
            "GET",
            &format!("/names/whois/{}", alice_owner()),
            &[],
            Body::empty(),
        )
        .await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(json["count"], 1);
    }

    #[tokio::test]
    async fn rental_status_check() {
        let app = test_app();

        let body = serde_json::to_string(&json!({
            "name": "rentcheck",
            "target": "pyana://x",
            "owner": alice_owner(),
            "rental_epochs": 50,
        }))
        .unwrap();
        request(
            &app,
            "POST",
            "/names/register",
            &[("content-type", "application/json")],
            body,
        )
        .await;

        let (status, json) =
            request(&app, "GET", "/names/rental/rentcheck", &[], Body::empty()).await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(json["status"]["status"], "active");
        assert_eq!(json["paid_until"], 150); // 100 + 50
    }

    #[tokio::test]
    async fn dispute_filing() {
        let app = test_app();

        // Register a name.
        let body = serde_json::to_string(&json!({
            "name": "contested",
            "target": "pyana://x",
            "owner": alice_owner(),
            "rental_epochs": 50,
        }))
        .unwrap();
        request(
            &app,
            "POST",
            "/names/register",
            &[("content-type", "application/json")],
            body,
        )
        .await;

        // File a dispute.
        let body = serde_json::to_string(&json!({
            "name": "contested",
            "challenger": bob_owner(),
            "reason": "I had this name first in another federation",
            "bond": 10000,
        }))
        .unwrap();

        let (status, json) = request(
            &app,
            "POST",
            "/names/dispute",
            &[("content-type", "application/json")],
            body,
        )
        .await;
        assert_eq!(status, StatusCode::CREATED);
        assert_eq!(json["status"], "pending");
        assert!(json["dispute_id"].as_str().is_some());
    }

    #[tokio::test]
    async fn renew_extends_expiry() {
        let app = test_app();

        let body = serde_json::to_string(&json!({
            "name": "renewable",
            "target": "pyana://x",
            "owner": alice_owner(),
            "rental_epochs": 50,
        }))
        .unwrap();
        request(
            &app,
            "POST",
            "/names/register",
            &[("content-type", "application/json")],
            body,
        )
        .await;

        // Renew for 20 more epochs.
        let body = serde_json::to_string(&json!({
            "owner": alice_owner(),
            "additional_epochs": 20,
        }))
        .unwrap();

        let (status, json) = request(
            &app,
            "POST",
            "/names/renew/renewable",
            &[("content-type", "application/json")],
            body,
        )
        .await;
        assert_eq!(status, StatusCode::OK);
        assert_eq!(json["expires_at"], 170); // 100 + 50 + 20
    }
}
