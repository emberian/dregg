//! Shared HTTP server infrastructure for pyana apps.
//!
//! Provides [`AppConfig`] for environment-based configuration, [`AppServer`] as a
//! builder for setting up standard middleware (health, admin auth, CORS), and common
//! handler implementations that every app needs.
//!
//! # Usage
//!
//! ```ignore
//! use pyana_app_framework::server::{AppConfig, AppServer};
//!
//! #[tokio::main]
//! async fn main() {
//!     let config = AppConfig::from_env();
//!     AppServer::new(config)
//!         .with_health()
//!         .with_cors()
//!         .routes(my_app_routes(state))
//!         .serve()
//!         .await
//!         .unwrap();
//! }
//! ```
//!
//! # What you get for free
//!
//! - `GET /health` — JSON health response with timestamp
//! - CORS headers (permissive by default, suitable for local dev and SPAs)
//! - Admin auth on `/admin/*` routes (reads `PYANA_ADMIN_TOKEN`)
//! - Environment-based listen address (`LISTEN` env var, default `0.0.0.0:3000`)
//! - Optional state file path (`PYANA_STATE_FILE` env var)
//! - Optional node URL (`PYANA_NODE_URL` env var)

use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

use axum::http::{HeaderValue, Method};
use axum::response::IntoResponse;
use axum::routing::get;
use axum::{Json, Router};
use serde_json::json;
use tokio::net::TcpListener;
use tower_http::cors::CorsLayer;

use crate::auth::AdminToken;
use crate::persistence::JsonPersistence;

// =============================================================================
// AppConfig
// =============================================================================

/// Standard application configuration read from environment variables.
///
/// All fields have sensible defaults for local development.
#[derive(Clone, Debug)]
pub struct AppConfig {
    /// Listen address (default: `0.0.0.0:3000`).
    /// Read from `LISTEN` env var.
    pub listen: String,

    /// Optional path to the state file for JSON persistence.
    /// Read from `PYANA_STATE_FILE` env var.
    pub state_file: Option<PathBuf>,

    /// Admin bearer token for `/admin/*` routes.
    /// Read from `PYANA_ADMIN_TOKEN` env var.
    pub admin_token: AdminToken,

    /// Optional pyana node URL for federation root sync.
    /// Read from `PYANA_NODE_URL` env var.
    pub node_url: Option<String>,
}

impl AppConfig {
    /// Read configuration from environment variables.
    pub fn from_env() -> Self {
        Self {
            listen: std::env::var("LISTEN").unwrap_or_else(|_| "0.0.0.0:3000".into()),
            state_file: std::env::var("PYANA_STATE_FILE").ok().map(PathBuf::from),
            admin_token: AdminToken::from_env(),
            node_url: std::env::var("PYANA_NODE_URL").ok(),
        }
    }

    /// Override the listen address.
    pub fn with_listen(mut self, addr: impl Into<String>) -> Self {
        self.listen = addr.into();
        self
    }

    /// Override the state file path.
    pub fn with_state_file(mut self, path: impl Into<PathBuf>) -> Self {
        self.state_file = Some(path.into());
        self
    }

    /// Override the admin token.
    pub fn with_admin_token(mut self, token: AdminToken) -> Self {
        self.admin_token = token;
        self
    }

    /// Get a [`JsonPersistence`] instance from the configured state file, or `None`.
    pub fn persistence(&self) -> Option<JsonPersistence> {
        self.state_file
            .as_ref()
            .map(|p| JsonPersistence::new(p.clone()))
    }
}

impl Default for AppConfig {
    fn default() -> Self {
        Self {
            listen: "0.0.0.0:3000".into(),
            state_file: None,
            admin_token: AdminToken::open(),
            node_url: None,
        }
    }
}

// =============================================================================
// AppServer builder
// =============================================================================

/// Builder for a standard pyana app HTTP server.
///
/// Provides a fluent API for adding common middleware and routes, then starting
/// the server with `serve()`.
pub struct AppServer {
    config: AppConfig,
    router: Router,
    service_name: String,
    /// Pending nameservice registration, set by `with_name`.
    /// Registered just before the server starts accepting connections.
    pending_registration: Option<crate::discovery::NameRegistration>,
    /// App wallet handle. When set, it is installed as an axum
    /// `Extension<AppWallet>` so handlers can sign actions through the
    /// framework.
    wallet: Option<crate::wallet::AppWallet>,
    /// Embedded executor handle. When set, it is installed as an axum
    /// `Extension<EmbeddedExecutor>` so handlers can submit signed turns
    /// to a private ledger and get back real `TurnReceipt`s.
    executor: Option<crate::wallet::EmbeddedExecutor>,
}

impl AppServer {
    /// Create a new server builder with the given configuration.
    pub fn new(config: AppConfig) -> Self {
        Self {
            config,
            router: Router::new(),
            service_name: "pyana-app".into(),
            pending_registration: None,
            wallet: None,
            executor: None,
        }
    }

    /// Install an [`AppWallet`](crate::wallet::AppWallet) as an axum
    /// `Extension<AppWallet>` layer.
    ///
    /// Handlers can then extract it via `axum::Extension<AppWallet>` and
    /// build signed actions/turns through it — no `[0u8; 64]` placeholder
    /// signatures, no direct `pyana_turn::builder::ActionBuilder` imports.
    pub fn with_wallet(mut self, wallet: crate::wallet::AppWallet) -> Self {
        self.router = self.router.layer(axum::Extension(wallet.clone()));
        self.wallet = Some(wallet);
        self
    }

    /// Get a reference to the installed wallet, if any. Useful for code
    /// that needs to capture the wallet *before* `serve()` consumes the
    /// builder (e.g. for shared state construction).
    pub fn wallet(&self) -> Option<&crate::wallet::AppWallet> {
        self.wallet.as_ref()
    }

    /// Install an embedded [`EmbeddedExecutor`](crate::wallet::EmbeddedExecutor)
    /// as an axum `Extension<EmbeddedExecutor>` layer.
    ///
    /// Handlers can then extract it via
    /// `axum::Extension<EmbeddedExecutor>` and submit signed actions/turns
    /// through it, getting back real `TurnReceipt`s — no more "action
    /// authored and dropped on the floor" pattern (closing
    /// `APPS-USERSPACE-GAPS.md` §Gap 4, the load-bearing one).
    ///
    /// Typical wiring in an app's `main.rs`:
    /// ```ignore
    /// let wallet = AppWallet::new(AgentWallet::new(), federation_id);
    /// let executor = EmbeddedExecutor::new(wallet.clone(), "my-domain");
    /// AppServer::new(config)
    ///     .with_wallet(wallet)
    ///     .with_embedded_executor(executor)
    ///     .routes(my_routes)
    ///     .serve()
    ///     .await
    /// ```
    pub fn with_embedded_executor(mut self, executor: crate::wallet::EmbeddedExecutor) -> Self {
        self.router = self.router.layer(axum::Extension(executor.clone()));
        self.executor = Some(executor);
        self
    }

    /// Get a reference to the installed embedded executor, if any.
    pub fn embedded_executor(&self) -> Option<&crate::wallet::EmbeddedExecutor> {
        self.executor.as_ref()
    }

    /// Set the service name (used in health responses and startup logging).
    pub fn service_name(mut self, name: impl Into<String>) -> Self {
        self.service_name = name.into();
        self
    }

    /// Merge application-specific routes into the server.
    ///
    /// Call this with your app's Router (which can use any state type -- the
    /// caller is responsible for calling `.with_state()` before passing it in,
    /// or passing a `Router<()>`).
    pub fn routes(mut self, router: Router) -> Self {
        self.router = self.router.merge(router);
        self
    }

    /// Add a standard health endpoint at `GET /health`.
    ///
    /// Returns JSON: `{"status": "ok", "service": "<name>", "timestamp": <unix_secs>}`
    pub fn with_health(mut self) -> Self {
        let name = self.service_name.clone();
        self.router = self
            .router
            .route("/health", get(move || health_handler(name.clone())));
        self
    }

    /// Add permissive CORS headers (suitable for SPAs and local development).
    ///
    /// Allows any origin, common methods, and common headers. For production,
    /// you may want to use [`Self::with_cors_origins`] instead.
    pub fn with_cors(mut self) -> Self {
        let cors = CorsLayer::new()
            .allow_origin(tower_http::cors::Any)
            .allow_methods([
                Method::GET,
                Method::POST,
                Method::PUT,
                Method::DELETE,
                Method::OPTIONS,
            ])
            .allow_headers(tower_http::cors::Any);
        self.router = self.router.layer(cors);
        self
    }

    /// Add CORS with specific allowed origins.
    pub fn with_cors_origins(mut self, origins: Vec<HeaderValue>) -> Self {
        let cors = CorsLayer::new()
            .allow_origin(origins)
            .allow_methods([
                Method::GET,
                Method::POST,
                Method::PUT,
                Method::DELETE,
                Method::OPTIONS,
            ])
            .allow_headers(tower_http::cors::Any);
        self.router = self.router.layer(cors);
        self
    }

    /// Nest additional routes under a path prefix.
    pub fn nest(mut self, path: &str, router: Router) -> Self {
        self.router = self.router.nest(path, router);
        self
    }

    /// Get a reference to the config.
    pub fn config(&self) -> &AppConfig {
        &self.config
    }

    // =========================================================================
    // New-world extension methods (Phase 1)
    // =========================================================================

    /// Nest a [`QueueEndpoint`] router at `path`.
    pub fn with_queue_endpoint(
        self,
        path: &str,
        endpoint: crate::queue_endpoint::QueueEndpoint,
    ) -> Self {
        self.nest(path, endpoint.router())
    }

    /// Nest a [`FairDistributionEndpoint`] router at `path`.
    pub fn with_blinded_endpoint(
        self,
        path: &str,
        endpoint: crate::blinded_endpoint::FairDistributionEndpoint,
    ) -> Self {
        self.nest(path, endpoint.router())
    }

    /// Nest an [`InboxEndpoint`] router at `path`.
    pub fn with_inbox(self, path: &str, endpoint: crate::inbox_endpoint::InboxEndpoint) -> Self {
        self.nest(path, endpoint.router())
    }

    /// Install a [`CapTpServer`] as an axum Extension layer.
    ///
    /// Handlers can extract it with `axum::Extension<CapTpServer>`.
    pub fn with_captp(self, server: crate::captp_server::CapTpServer) -> Self {
        let router = self.router.layer(axum::Extension(server));
        Self { router, ..self }
    }

    /// Install a [`FeePolicy`] as an axum Extension layer.
    ///
    /// Handlers can extract it with `axum::Extension<FeePolicy>`.
    pub fn with_fee_policy(self, policy: crate::fee_policy::FeePolicy) -> Self {
        let router = self.router.layer(axum::Extension(policy));
        Self { router, ..self }
    }

    /// Install a [`MultiGroupConfig`] as an axum Extension layer.
    ///
    /// Handlers can extract it with `axum::Extension<MultiGroupConfig>`.
    pub fn with_multi_group(self, config: crate::multi_group::MultiGroupConfig) -> Self {
        let router = self.router.layer(axum::Extension(config));
        Self { router, ..self }
    }

    /// Set the app's nameservice registration.
    ///
    /// Just before the server starts, it will POST to the nameservice
    /// (`PYANA_NAMESERVICE_URL`) to register under `name` with `tags`.
    /// Registration failure is logged but does NOT abort startup.
    pub fn with_name(mut self, name: impl Into<String>, tags: Vec<String>) -> Self {
        self.pending_registration = Some(crate::discovery::NameRegistration {
            name: name.into(),
            tags,
            target_uri: format!("http://{}", self.config.listen),
        });
        self
    }

    /// Start serving. Binds to the configured address and runs until shutdown.
    ///
    /// Prints the listen address to stderr on startup.
    /// If `with_name` was called, attempts nameservice registration after binding
    /// (failure is logged to stderr but does not abort startup).
    pub async fn serve(self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let listener = TcpListener::bind(&self.config.listen).await?;
        let addr = listener.local_addr()?;
        eprintln!("{} listening on http://{addr}", self.service_name);

        if let Some(reg) = &self.pending_registration {
            if let Err(e) = crate::discovery::NameserviceClient::from_env()
                .register(reg)
                .await
            {
                eprintln!("[nameservice] registration failed (non-fatal): {e}");
            }
        }

        axum::serve(listener, self.router).await?;
        Ok(())
    }

    /// Start serving and return the bound address (useful for tests).
    ///
    /// Spawns the server as a background tokio task and returns immediately.
    /// If `with_name` was called, attempts nameservice registration before spawning.
    pub async fn serve_background(
        self,
    ) -> Result<std::net::SocketAddr, Box<dyn std::error::Error + Send + Sync>> {
        let listener = TcpListener::bind(&self.config.listen).await?;
        let addr = listener.local_addr()?;
        eprintln!("{} listening on http://{addr}", self.service_name);

        if let Some(reg) = &self.pending_registration {
            if let Err(e) = crate::discovery::NameserviceClient::from_env()
                .register(reg)
                .await
            {
                eprintln!("[nameservice] registration failed (non-fatal): {e}");
            }
        }

        tokio::spawn(async move {
            axum::serve(listener, self.router)
                .await
                .expect("server error");
        });
        Ok(addr)
    }
}

// =============================================================================
// Standard handlers
// =============================================================================

/// Standard health handler response.
async fn health_handler(service_name: String) -> impl IntoResponse {
    let timestamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);

    Json(json!({
        "status": "ok",
        "service": service_name,
        "timestamp": timestamp,
    }))
}

/// Create a health handler that includes custom metadata.
///
/// Use this when your app wants to add extra fields to the health response
/// (e.g., block height, pool count, connection status).
///
/// ```ignore
/// use pyana_app_framework::server::health_with_metadata;
///
/// let handler = health_with_metadata("my-app", || async {
///     json!({"block_height": 42, "pools": 3})
/// });
/// ```
pub fn health_with_metadata<F, Fut>(
    service_name: impl Into<String>,
    metadata_fn: F,
) -> impl Fn() -> std::pin::Pin<Box<dyn std::future::Future<Output = serde_json::Value> + Send>>
+ Clone
+ Send
+ 'static
where
    F: Fn() -> Fut + Clone + Send + 'static,
    Fut: std::future::Future<Output = serde_json::Value> + Send + 'static,
{
    let name = service_name.into();
    move || {
        let name = name.clone();
        let metadata_fn = metadata_fn.clone();
        Box::pin(async move {
            let timestamp = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|d| d.as_secs())
                .unwrap_or(0);
            let extra = metadata_fn().await;
            let mut base = json!({
                "status": "ok",
                "service": name,
                "timestamp": timestamp,
            });
            if let (Some(base_obj), Some(extra_obj)) = (base.as_object_mut(), extra.as_object()) {
                for (k, v) in extra_obj {
                    base_obj.insert(k.clone(), v.clone());
                }
            }
            base
        })
    }
}

// =============================================================================
// Common error response type
// =============================================================================

/// Standard JSON error response used by all pyana app endpoints.
///
/// Serializes to `{"error": "<message>"}`.
#[derive(Clone, Debug, serde::Serialize)]
pub struct ErrorResponse {
    pub error: String,
}

impl ErrorResponse {
    /// Create a new error response.
    pub fn new(msg: impl Into<String>) -> Self {
        Self { error: msg.into() }
    }
}

/// Convenience: create an axum rejection from a status code and message.
pub fn api_error(
    status: axum::http::StatusCode,
    msg: impl Into<String>,
) -> (axum::http::StatusCode, Json<ErrorResponse>) {
    (status, Json(ErrorResponse::new(msg)))
}
