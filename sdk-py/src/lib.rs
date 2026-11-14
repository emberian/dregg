//! # `dregg` — the Python face of the dregg SDK's two-noun surface.
//!
//! ```python
//! import dregg
//!
//! ident = dregg.Identity.from_profile("ember")      # ~/.dregg/profiles, shared with the CLI
//! receipt = (ident.turn("http://localhost:8421")   # your local node — see QUICKSTART.md
//!                 .transfer("28c2cba0…", 100)
//!                 .sign()
//!                 .submit())
//! print(receipt.turn_hash, receipt.has_proof)
//!
//! for r in dregg.subscribe(node_url, kind="transfer"):
//!     print(r.turn_hash)
//! ```
//!
//! The shape is the Rust SDK's authorization-first surface, verbatim:
//! `Identity → .turn() → typed verbs → .sign() → .submit() → Receipt`.
//! An unauthorized act is inexpressible here — by the time anything leaves
//! `.sign()` it is a real Ed25519-signed canonical `SignedTurn`, and the
//! node ingress (`POST /api/turns/submit-signed`) verifies it.
//!
//! Refusals raise [`DreggRefused`] carrying the node's reason AND the
//! clerk's faithful explanation of what was signed — the system teaches
//! when it says no.

use std::collections::VecDeque;
use std::io::Read;
use std::time::Duration;

use pyo3::exceptions::{PyKeyError, PyTypeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyDict, PyList};

use std::sync::{Arc, RwLock};

use dregg_cell::interface::method_symbol;
use dregg_cell::program::{
    CellProgram, HashKind, SimpleStateConstraint, StateConstraint, TransitionCase, TransitionGuard,
};
use dregg_cell::state::FieldElement;
use dregg_cell::{AuthRequired, CapabilityRef, Cell, field_from_u64};
use dregg_sdk::cipherclerk::{
    AgentCipherclerk, AuthorizationPresentation, FactIndex, HeldToken, SignedTurn, VerificationMode,
};
use dregg_sdk::explain::{explain_action, explain_turn};
use dregg_sdk::profiles;
use dregg_sdk::{
    AgentRuntime as SdkRuntime, Attenuation, AuthRequest, ExecutionLease, InvokeAuthority,
    LeaseTerms, PayLeg, SubAgent,
};
use dregg_turn::Effect;
use dregg_turn::TurnReceipt;
use dregg_turn::action::Action;
use dregg_turn::action::{WitnessBlob, WitnessKind};
use dregg_types::CellId;

// ─── exceptions ───

pyo3::create_exception!(
    dregg,
    DreggError,
    pyo3::exceptions::PyException,
    "Base error for the dregg SDK (I/O, profile store, node transport)."
);
pyo3::create_exception!(
    dregg,
    DreggRefused,
    DreggError,
    "The system said no — a refusal from the signing surface or the node, \
     carrying the reason and the faithful explanation of what was attempted."
);

fn err(msg: impl Into<String>) -> PyErr {
    DreggError::new_err(msg.into())
}

fn refused(msg: impl Into<String>) -> PyErr {
    DreggRefused::new_err(msg.into())
}

// ─── small codecs ───

/// Accept a 32-byte identifier as a hex `str` or 32-byte `bytes`.
fn parse_32(obj: &Bound<'_, PyAny>, what: &str) -> PyResult<[u8; 32]> {
    if let Ok(s) = obj.extract::<&str>() {
        let bytes = hex::decode(s.trim())
            .map_err(|e| PyValueError::new_err(format!("{what}: invalid hex: {e}")))?;
        return bytes.as_slice().try_into().map_err(|_| {
            PyValueError::new_err(format!("{what}: expected 32 bytes, got {}", bytes.len()))
        });
    }
    if let Ok(b) = obj.extract::<&[u8]>() {
        return b.try_into().map_err(|_| {
            PyValueError::new_err(format!("{what}: expected 32 bytes, got {}", b.len()))
        });
    }
    Err(PyTypeError::new_err(format!(
        "{what}: expected a hex str or 32-byte bytes"
    )))
}

fn parse_cell(obj: &Bound<'_, PyAny>, what: &str) -> PyResult<CellId> {
    Ok(CellId(parse_32(obj, what)?))
}

fn parse_auth_required(s: &str) -> PyResult<AuthRequired> {
    match s.to_ascii_lowercase().as_str() {
        "none" => Ok(AuthRequired::None),
        "signature" => Ok(AuthRequired::Signature),
        "proof" => Ok(AuthRequired::Proof),
        "either" => Ok(AuthRequired::Either),
        "impossible" => Ok(AuthRequired::Impossible),
        other => Err(PyValueError::new_err(format!(
            "permissions: expected one of none/signature/proof/either/impossible, got {other:?}"
        ))),
    }
}

/// serde_json → Python objects (dicts/lists/str/int/float/bool/None).
fn json_to_py<'py>(py: Python<'py>, v: &serde_json::Value) -> PyResult<Bound<'py, PyAny>> {
    Ok(match v {
        serde_json::Value::Null => py.None().into_bound(py),
        serde_json::Value::Bool(b) => b.into_pyobject(py)?.to_owned().into_any(),
        serde_json::Value::Number(n) => {
            if let Some(i) = n.as_i64() {
                i.into_pyobject(py)?.into_any()
            } else if let Some(u) = n.as_u64() {
                u.into_pyobject(py)?.into_any()
            } else {
                n.as_f64().unwrap_or(f64::NAN).into_pyobject(py)?.into_any()
            }
        }
        serde_json::Value::String(s) => s.into_pyobject(py)?.into_any(),
        serde_json::Value::Array(items) => {
            let list = PyList::empty(py);
            for item in items {
                list.append(json_to_py(py, item)?)?;
            }
            list.into_any()
        }
        serde_json::Value::Object(map) => {
            let dict = PyDict::new(py);
            for (k, val) in map {
                dict.set_item(k, json_to_py(py, val)?)?;
            }
            dict.into_any()
        }
    })
}

// ─── blocking HTTP (the binding's own thin transport; no tokio) ───

fn http_agent() -> ureq::Agent {
    ureq::AgentBuilder::new()
        .timeout_connect(Duration::from_secs(10))
        .timeout(Duration::from_secs(30))
        .build()
}

fn get_json(url: &str) -> Result<serde_json::Value, String> {
    let resp = http_agent()
        .get(url)
        .call()
        .map_err(|e| format!("GET {url}: {e}"))?;
    resp.into_json().map_err(|e| format!("GET {url}: {e}"))
}

/// The devnet gate key (operator credential) → sent as both `X-Devnet-Key` and
/// `Authorization: Bearer`. Mirrors the TS `NodeClient.devnetKey`: the
/// signed-turn ingress and the operator-gated organ routes (trustline /
/// channels) are protected behind it on the shared devnet. Resolved from the
/// explicit argument, else `$DREGG_API_TOKEN`.
fn resolve_devnet_key(explicit: Option<&str>) -> Option<String> {
    explicit
        .map(str::to_string)
        .or_else(|| std::env::var("DREGG_API_TOKEN").ok())
        .map(|t| t.trim().to_string())
        .filter(|t| !t.is_empty())
}

fn apply_devnet_key(mut req: ureq::Request, key: Option<&str>) -> ureq::Request {
    if let Some(k) = key {
        req = req
            .set("x-devnet-key", k)
            .set("authorization", &format!("Bearer {k}"));
    }
    req
}

/// `GET {base}{path}` (devnet-keyed) → parsed JSON. The read used by the organ
/// status routes + attested-query.
fn http_get_json(base: &str, path: &str, key: Option<&str>) -> Result<serde_json::Value, String> {
    let url = format!("{}{}", base.trim_end_matches('/'), path);
    let req = apply_devnet_key(http_agent().get(&url), key);
    match req.call() {
        Ok(resp) => resp.into_json().map_err(|e| format!("GET {url}: {e}")),
        Err(ureq::Error::Status(code, resp)) => {
            let text = resp.into_string().unwrap_or_default();
            Err(format!("GET {url}: HTTP {code}: {text}"))
        }
        Err(e) => Err(format!("GET {url}: {e}")),
    }
}

/// `{method} {base}{path}` with a JSON body (devnet-keyed) → parsed JSON. The
/// generic write used by the organ clients (mirrors TS `NodeClient.postJson`).
fn http_send_json(
    method: &str,
    base: &str,
    path: &str,
    body: &serde_json::Value,
    key: Option<&str>,
) -> Result<serde_json::Value, String> {
    let url = format!("{}{}", base.trim_end_matches('/'), path);
    let req = apply_devnet_key(
        http_agent()
            .request(method, &url)
            .set("content-type", "application/json"),
        key,
    );
    let payload = serde_json::to_vec(body).map_err(|e| format!("encode body: {e}"))?;
    match req.send_bytes(&payload) {
        Ok(resp) => resp.into_json().map_err(|e| format!("{method} {url}: {e}")),
        Err(ureq::Error::Status(code, resp)) => {
            let text = resp.into_string().unwrap_or_default();
            Err(format!("{method} {url}: HTTP {code}: {text}"))
        }
        Err(e) => Err(format!("{method} {url}: {e}")),
    }
}

/// The node's executor federation id: `blake3(node operator pubkey)` on a
/// solo/unconfigured node — the same derivation `federation_id_for_executor`
/// uses (and the discord-bot's startup check asserts). Configured
/// multi-member federations pass `federation_id=` explicitly.
fn fetch_federation_id(node_url: &str) -> Result<[u8; 32], String> {
    let v = get_json(&format!("{node_url}/api/node/identity"))?;
    let pk_hex = v
        .get("public_key")
        .and_then(|p| p.as_str())
        .ok_or_else(|| "node identity response missing public_key".to_string())?;
    let pk: [u8; 32] = hex::decode(pk_hex)
        .map_err(|e| format!("node public_key: {e}"))?
        .as_slice()
        .try_into()
        .map_err(|_| "node public_key is not 32 bytes".to_string())?;
    Ok(*blake3::hash(&pk).as_bytes())
}

/// The agent cell's LIVE replay counter from the node — the nonce `.sign()`
/// stamps on the turn AND binds the action signature to.
///
/// FAILS LOUD. This used to `.unwrap_or(0)`: an unreachable node, a devnet-key
/// rejection, an unknown cell, or a renamed field all silently became "nonce 0",
/// so the SDK would confidently sign a turn bound to the wrong replay counter
/// and the citizen got an opaque refusal from the node instead of the real cause
/// (the node is down / this cell does not exist). A default of 0 is never a
/// safe guess for a value the signature commits to — the ONE nonce it is
/// accidentally right for is a brand-new cell's first turn, which is exactly the
/// case every test pinned. Pin `.nonce(n)` for offline construction.
fn fetch_cell_nonce(node_url: &str, cell_hex: &str) -> Result<u64, String> {
    let body = get_json(&format!("{node_url}/api/cell/{cell_hex}"))
        .map_err(|e| format!("could not read the acting cell's live nonce from {node_url}: {e}"))?;
    if body.get("found").and_then(|f| f.as_bool()) == Some(false) {
        return Err(format!(
            "the acting cell {cell_hex} does not exist on {node_url} — it has never been funded \
             or created, so it has no nonce to sign against"
        ));
    }
    body.get("nonce")
        .and_then(|n| n.as_u64())
        .ok_or_else(|| format!("node {node_url} returned no `nonce` for cell {cell_hex}"))
}

fn post_signed_turn(
    node_url: &str,
    body: &[u8],
    key: Option<&str>,
) -> Result<serde_json::Value, String> {
    let url = format!("{node_url}/api/turns/submit-signed");
    let req = apply_devnet_key(
        http_agent()
            .post(&url)
            .set("content-type", "application/octet-stream"),
        // The shared devnet protects the /api/turns/* ingress behind a bearer;
        // fall back to $DREGG_API_TOKEN when no key was pinned on .turn().
        resolve_devnet_key(key).as_deref(),
    );
    match req.send_bytes(body) {
        Ok(resp) => resp.into_json().map_err(|e| format!("POST {url}: {e}")),
        Err(ureq::Error::Status(code, resp)) => {
            let text = resp.into_string().unwrap_or_default();
            Err(format!("POST {url}: HTTP {code}: {text}"))
        }
        Err(e) => Err(format!("POST {url}: {e}")),
    }
}

/// The node's attested height, `GET /status` → `latest_height`: the height a turn's
/// `valid_until` (a block height) is counted from. Fails loud, like `fetch_cell_nonce`: a
/// guessed height would stamp a deadline the node refuses. Pin `.valid_until(h)` for offline
/// construction.
fn fetch_latest_height(node_url: &str) -> Result<u64, String> {
    let body = get_json(&format!("{node_url}/status"))
        .map_err(|e| format!("could not read the node's latest height from {node_url}: {e}"))?;
    body.get("latest_height")
        .and_then(|h| h.as_u64())
        .ok_or_else(|| format!("node {node_url} returned no unsigned `latest_height` on /status"))
}

// ─── Identity ───

/// A named local identity — an Ed25519 key from the shared `$DREGG_HOME`
/// profile store (`~/.dregg/profiles/<name>.json`, the same files
/// `dregg id create/use` and the Rust SDK read).
#[pyclass(unsendable, module = "dregg")]
struct Identity {
    clerk: AgentCipherclerk,
    name: Option<String>,
}

#[pymethods]
impl Identity {
    /// Load a named profile from the local store.
    #[staticmethod]
    fn from_profile(name: &str) -> PyResult<Self> {
        let clerk = profiles::load(name).map_err(|e| err(e.to_string()))?;
        Ok(Identity {
            clerk,
            name: Some(name.to_string()),
        })
    }

    /// Create a named profile with a fresh random seed (refuses an existing
    /// name) and return its identity. Does not change the active profile.
    #[staticmethod]
    fn create(name: &str) -> PyResult<Self> {
        profiles::create(name).map_err(|e| refused(e.to_string()))?;
        Self::from_profile(name)
    }

    /// The active profile (`DREGG_PROFILE` env override → the persistent
    /// `dregg id use` default). Raises DreggError when none is configured.
    #[staticmethod]
    fn active() -> PyResult<Self> {
        let name = profiles::active_name();
        match profiles::load_active().map_err(|e| err(e.to_string()))? {
            Some(clerk) => Ok(Identity { clerk, name }),
            None => Err(err(
                "no active profile configured — `dregg id create <name> && dregg id use <name>` \
                 (or dregg.Identity.create(name)), or set DREGG_PROFILE",
            )),
        }
    }

    /// The profile name this identity was loaded from (None for `active()`
    /// resolved purely from the env in an edge case, or future anonymous
    /// constructions).
    #[getter]
    fn name(&self) -> Option<String> {
        self.name.clone()
    }

    /// Hex Ed25519 public key.
    #[getter]
    fn public_key(&self) -> String {
        hex::encode(self.clerk.public_key().0)
    }

    /// Hex CellId in the default federation domain — the agent cell this
    /// identity acts and pays as (what the node derives from the signer key).
    #[getter]
    fn cell_id(&self) -> String {
        hex::encode(self.clerk.cell_id("default").0)
    }

    /// Open a turn builder against `node_url`.
    ///
    /// `federation_id` (hex str or 32 bytes) pins the signing domain
    /// explicitly; when omitted, `.sign()` fetches the node's identity and
    /// derives the solo-node executor domain `blake3(node_pubkey)`.
    ///
    /// `devnet_key` is the operator credential for the gated ingress (sent as
    /// `X-Devnet-Key` + `Authorization: Bearer`); when omitted, `.submit()`
    /// falls back to `$DREGG_API_TOKEN`.
    #[pyo3(signature = (node_url, federation_id=None, devnet_key=None))]
    fn turn(
        slf: &Bound<'_, Self>,
        node_url: &str,
        federation_id: Option<&Bound<'_, PyAny>>,
        devnet_key: Option<&str>,
    ) -> PyResult<TurnBuilder> {
        let federation_id = federation_id
            .map(|f| parse_32(f, "federation_id"))
            .transpose()?;
        Ok(TurnBuilder {
            identity: slf.clone().unbind(),
            node_url: node_url.trim_end_matches('/').to_string(),
            method: "execute".to_string(),
            effects: Vec::new(),
            target: None,
            witnesses: Vec::new(),
            fee: None,
            memo: None,
            nonce: None,
            valid_until: None,
            federation_id,
            devnet_key: devnet_key.map(str::to_string),
        })
    }

    /// The **trustline** organ (`.docs-history-noclaude/ORGANS.md` §1) bound to `node_url`,
    /// acting as the issuer under this identity's operator credential. See
    /// [`Trustline`].
    #[pyo3(signature = (node_url, devnet_key=None))]
    fn trustline(&self, node_url: &str, devnet_key: Option<&str>) -> Trustline {
        Trustline {
            node_url: node_url.trim_end_matches('/').to_string(),
            devnet_key: devnet_key.map(str::to_string),
        }
    }

    /// The **channels** organ (`.docs-history-noclaude/ORGANS.md` §4) bound to `node_url`. See
    /// [`Channels`].
    #[pyo3(signature = (node_url, devnet_key=None))]
    fn channels(&self, node_url: &str, devnet_key: Option<&str>) -> Channels {
        Channels {
            node_url: node_url.trim_end_matches('/').to_string(),
            devnet_key: devnet_key.map(str::to_string),
        }
    }

    /// This identity's **mailbox** (`.docs-history-noclaude/ORGANS.md` §2) on the relay at
    /// `relay_url`. Membership ops are Ed25519-signed by this identity. See
    /// [`Mailbox`].
    fn mailbox(slf: &Bound<'_, Self>, relay_url: &str) -> Mailbox {
        Mailbox {
            identity: slf.clone().unbind(),
            base_url: relay_url.trim_end_matches('/').to_string(),
        }
    }

    // ─── the token / presentation surface (macaroon-backed authorization) ───

    /// Mint a root authorization token for `service` under `root_key`
    /// (hex str or 32 bytes — the service's verification secret). Forwards
    /// to `AgentCipherclerk::mint_token`.
    fn mint_token(&mut self, root_key: &Bound<'_, PyAny>, service: &str) -> PyResult<Token> {
        let key = parse_32(root_key, "root_key")?;
        Ok(Token {
            inner: self.clerk.mint_token(&key, service),
        })
    }

    /// Attenuate `token` — narrowing only, never expanding (the core refuses
    /// an empty restriction set). Field names mirror the Rust `Attenuation`
    /// struct: `services`/`apps` are `(name, action_mask)` pairs (e.g.
    /// `("dns", "r")`), `not_after`/`not_before` unix seconds.
    #[pyo3(signature = (token, services=None, apps=None, features=None, not_after=None, not_before=None, confine_user=None))]
    #[allow(clippy::too_many_arguments)]
    fn attenuate(
        &mut self,
        token: &Token,
        services: Option<Vec<(String, String)>>,
        apps: Option<Vec<(String, String)>>,
        features: Option<Vec<String>>,
        not_after: Option<i64>,
        not_before: Option<i64>,
        confine_user: Option<String>,
    ) -> PyResult<Token> {
        let restrictions = Attenuation {
            services: services.unwrap_or_default(),
            apps: apps.unwrap_or_default(),
            features: features.unwrap_or_default(),
            not_after,
            not_before,
            confine_user,
            ..Attenuation::default()
        };
        let attenuated = self
            .clerk
            .attenuate(&token.inner, &restrictions)
            .map_err(|e| refused(e.to_string()))?;
        Ok(Token { inner: attenuated })
    }

    /// Authorize a request against `token`, producing a [`Presentation`].
    ///
    /// `mode` selects the Rust `VerificationMode`:
    /// - `"trusted"` — local Datalog evaluation, full clearance + trace
    ///   (for verifiers holding the root key).
    /// - `"selective"` — STARK proof with the facts at `reveal` indices
    ///   disclosed (committed via Poseidon2), the rest private witness.
    /// - `"private"` — STARK proof; the verifier learns only the conclusion.
    ///
    /// The request fields mirror the Rust `AuthRequest` (unset = unconstrained).
    #[pyo3(signature = (token, mode="trusted", reveal=None, service=None, action=None, app_id=None, user_id=None, features=None, now=None))]
    #[allow(clippy::too_many_arguments)]
    fn authorize(
        &self,
        token: &Token,
        mode: &str,
        reveal: Option<Vec<usize>>,
        service: Option<String>,
        action: Option<String>,
        app_id: Option<String>,
        user_id: Option<String>,
        features: Option<Vec<String>>,
        now: Option<i64>,
    ) -> PyResult<Presentation> {
        let request = AuthRequest {
            app_id,
            service,
            action,
            features: features.unwrap_or_default(),
            user_id,
            now,
            ..AuthRequest::default()
        };
        let mode = match mode.to_ascii_lowercase().as_str() {
            "trusted" => VerificationMode::Trusted,
            "selective" => VerificationMode::SelectiveDisclosure {
                reveal: reveal
                    .unwrap_or_default()
                    .into_iter()
                    .map(FactIndex)
                    .collect(),
            },
            "private" => VerificationMode::FullyPrivate,
            other => {
                return Err(PyValueError::new_err(format!(
                    "mode: expected one of trusted/selective/private, got {other:?}"
                )));
            }
        };
        let presentation = self
            .clerk
            .authorize(&token.inner, &request, mode)
            .map_err(|e| refused(e.to_string()))?;
        Ok(Presentation {
            inner: presentation,
        })
    }

    fn __repr__(&self) -> String {
        format!(
            "Identity(name={:?}, cell_id={:?})",
            self.name,
            self.cell_id()
        )
    }
}

// ─── the wire constructions (shared by the pymethods and the drift-killer) ───

/// The [`CapabilityRef`] `TurnBuilder.grant()` mints — the ONE construction that
/// path uses, extracted so the drift-killer can drive the SHIPPED code rather
/// than re-authoring it (a test that builds its own cap verifies only itself:
/// dropping `provenance` in `grant()` would leave such a test green, which is
/// how sdk-ts shipped a provenance-dropping encoder to npm under a passing
/// "byte-faithful" claim).
///
/// `provenance` is the canonical MINT-rooted derivation, identical to the
/// c-list's own `grant_with_breadstuff` (cell/src/capability.rs): parent =
/// `mint_provenance()` (a context-free grant is a root/mint), turn context =
/// `NO_TURN_CONTEXT` (`[0u8; 32]`). It is `#[serde(default)]` with NO
/// `skip_serializing_if`, so postcard emits its 32 bytes positionally — a
/// dropped field slides every subsequent field on the wire.
pub fn mint_cap_ref(
    target: CellId,
    slot: u32,
    permissions: AuthRequired,
    expires_at: Option<u64>,
) -> CapabilityRef {
    CapabilityRef {
        target,
        slot,
        permissions,
        breadstuff: None,
        expires_at,
        allowed_effects: None,
        stored_epoch: None,
        provenance: dregg_cell::derivation::cap_provenance(
            &target,
            slot,
            &dregg_cell::derivation::mint_provenance(),
            &[0u8; 32],
        ),
    }
}

// ─── the signing path (shared by `TurnBuilder.sign()` and the drift-killer) ───

/// Build the canonical [`SignedTurn`] for a staged turn — the ONE construction
/// `TurnBuilder.sign()` uses.
///
/// It is a free function (not a `#[pymethods]` body) precisely so the
/// executor-level drift-killer (`tests/wire_drift_killer.rs`) can drive the
/// REAL signing path instead of re-authoring a mirror of it. A mirror would
/// verify itself and pass while the shipped path stayed broken — which is
/// exactly how this function's own nonce bug survived undetected.
///
/// # The nonce bind (`dregg-action-sig-v3`)
///
/// The action signature covers the nonce of the turn it will RIDE
/// (`TurnExecutor::compute_signing_message` folds in `turn_nonce`), so the
/// action MUST be signed against the same `nonce` stamped on the turn below.
/// This path previously went through `AgentCipherclerk::make_action`, which
/// binds `next_turn_nonce()` = `receipt_chain.len()` — and sdk-py never
/// appends to the receipt chain, so that was ALWAYS 0. Every turn from an
/// agent whose on-ledger nonce had advanced past 0 carried a signature bound
/// to nonce 0 and was refused at commit. `sign_action_hybrid` with the live
/// nonce is the documented fix (see its rustdoc: "If the action will ride a
/// turn with a DIFFERENT nonce … use `sign_action_hybrid` with that nonce
/// explicitly — a mismatched nonce fails signature verification at commit").
/// # `action_target` / `witness_blobs`
///
/// `action_target` is the `.on(target)` verb: the action targets another cell
/// the identity administers (the executor verifies the signature against the
/// TARGET's owner — the builder does not pre-judge); `None` targets the acting
/// agent cell. `witness_blobs` is the `.reveal(preimage)` verb: the blobs are
/// attached to the unsigned action BEFORE signing so the signature covers them
/// (a blob attached after signing would be strippable in flight).
#[allow(clippy::too_many_arguments)]
pub fn build_signed_turn(
    clerk: &AgentCipherclerk,
    domain: &str,
    method: &str,
    effects: Vec<Effect>,
    action_target: Option<CellId>,
    witness_blobs: Vec<WitnessBlob>,
    federation_id: &[u8; 32],
    nonce: u64,
    fee: u64,
    memo: Option<String>,
    valid_until: i64,
) -> SignedTurn {
    let target = action_target.unwrap_or_else(|| clerk.cell_id(domain));
    let mut unsigned = dregg_sdk::raw::unsigned_action_named(target, method, effects);
    // Witnesses attach BEFORE signing so the signature covers them (the
    // `set_field_with_preimage` shape in the executor's coverage tests).
    unsigned.witness_blobs = witness_blobs;
    // Bind the action signature to the nonce the turn ACTUALLY carries.
    let action = clerk.sign_action_hybrid(unsigned, federation_id, nonce);
    let mut turn = clerk.make_turn_for(domain, action);
    turn.nonce = nonce;
    turn.fee = fee;
    turn.memo = memo;
    turn.valid_until = Some(valid_until);
    clerk.sign_turn(&turn)
}

// ─── TurnBuilder ───

/// The typed verb builder: stage effects, then `.sign()`.
///
/// Every verb returns the builder for chaining. There is no submit on this
/// type — only a signed turn can travel.
#[pyclass(unsendable, module = "dregg")]
struct TurnBuilder {
    identity: Py<Identity>,
    node_url: String,
    method: String,
    effects: Vec<Effect>,
    /// `.on(target)`: the action targets this administered cell instead of the
    /// acting agent cell (the Rust `TurnBuilder::on` shape).
    target: Option<CellId>,
    /// `.reveal(preimage)` witness blobs, attached under the signature.
    witnesses: Vec<WitnessBlob>,
    fee: Option<u64>,
    memo: Option<String>,
    nonce: Option<u64>,
    valid_until: Option<i64>,
    federation_id: Option<[u8; 32]>,
    devnet_key: Option<String>,
}

impl TurnBuilder {
    /// The cell whose authority this turn exercises — the default `from` /
    /// write target for the typed verbs (`.on(target)` when set, else the
    /// identity's agent cell; mirrors the Rust builder's `acting_cell`).
    fn acting_cell(&self, py: Python<'_>) -> CellId {
        self.target
            .unwrap_or_else(|| self.identity.borrow(py).clerk.cell_id("default"))
    }
}

#[pymethods]
impl TurnBuilder {
    /// Transfer `amount` computrons from the acting cell to `to`.
    fn transfer<'py>(
        mut slf: PyRefMut<'py, Self>,
        to: &Bound<'py, PyAny>,
        amount: u64,
    ) -> PyResult<PyRefMut<'py, Self>> {
        let to = parse_cell(to, "to")?;
        let from = slf.acting_cell(slf.py());
        slf.effects.push(Effect::Transfer { from, to, amount });
        Ok(slf)
    }

    /// Transfer with an explicit source cell (must still be within this
    /// identity's authority — the executor checks, not the builder).
    fn transfer_from<'py>(
        mut slf: PyRefMut<'py, Self>,
        from: &Bound<'py, PyAny>,
        to: &Bound<'py, PyAny>,
        amount: u64,
    ) -> PyResult<PyRefMut<'py, Self>> {
        let from = parse_cell(from, "from")?;
        let to = parse_cell(to, "to")?;
        slf.effects.push(Effect::Transfer { from, to, amount });
        Ok(slf)
    }

    /// Write state slot `index` of the acting cell. `value` is an int
    /// (encoded little-endian like the Rust `field_from_u64`) or 32 bytes /
    /// hex (a full field element).
    fn write<'py>(
        mut slf: PyRefMut<'py, Self>,
        index: u64,
        value: &Bound<'py, PyAny>,
    ) -> PyResult<PyRefMut<'py, Self>> {
        let value = if let Ok(n) = value.extract::<u64>() {
            field_from_u64(n)
        } else {
            parse_32(value, "value")?
        };
        let cell = slf.acting_cell(slf.py());
        slf.effects.push(Effect::SetField { cell, index, value });
        Ok(slf)
    }

    /// `write` with a numeric value (explicit-name twin of the Rust verb).
    fn write_u64(mut slf: PyRefMut<'_, Self>, index: u64, value: u64) -> PyRefMut<'_, Self> {
        let cell = slf.acting_cell(slf.py());
        slf.effects.push(Effect::SetField {
            cell,
            index,
            value: field_from_u64(value),
        });
        slf
    }

    /// Grant a capability from the acting cell to `to` (non-amplifying: the
    /// executor admits only grants within held authority). `target` is the
    /// cell the capability points at (defaults to the acting cell);
    /// `permissions` is one of none/signature/proof/either/impossible.
    #[pyo3(signature = (to, target=None, permissions="signature", slot=0, expires_at=None))]
    fn grant<'py>(
        mut slf: PyRefMut<'py, Self>,
        to: &Bound<'py, PyAny>,
        target: Option<&Bound<'py, PyAny>>,
        permissions: &str,
        slot: u32,
        expires_at: Option<u64>,
    ) -> PyResult<PyRefMut<'py, Self>> {
        let to = parse_cell(to, "to")?;
        let from = slf.acting_cell(slf.py());
        let target = target
            .map(|t| parse_cell(t, "target"))
            .transpose()?
            .unwrap_or(from);
        let cap = mint_cap_ref(target, slot, parse_auth_required(permissions)?, expires_at);
        slf.effects.push(Effect::GrantCapability { from, to, cap });
        Ok(slf)
    }

    /// Bump the acting cell's nonce (a deliberate no-op state advance).
    fn increment_nonce(mut slf: PyRefMut<'_, Self>) -> PyRefMut<'_, Self> {
        let cell = slf.acting_cell(slf.py());
        slf.effects.push(Effect::IncrementNonce { cell });
        slf
    }

    /// Target another cell this identity administers (the Rust
    /// `TurnBuilder::on` verb): the action targets `target`, this agent signs
    /// and pays, and the executor verifies the signature against `target`'s
    /// owner key. Call BEFORE staging verbs — the typed verbs capture the
    /// acting cell at call time (same as the Rust builder).
    fn on<'py>(
        mut slf: PyRefMut<'py, Self>,
        target: &Bound<'py, PyAny>,
    ) -> PyResult<PyRefMut<'py, Self>> {
        if !slf.effects.is_empty() {
            return Err(refused(
                ".on(target) must be called before staging verbs — the effects already staged \
                 were built against the previous acting cell",
            ));
        }
        slf.target = Some(parse_cell(target, "target")?);
        Ok(slf)
    }

    /// Exhibit a 32-byte preimage witness with this turn (the Rust
    /// `TurnBuilder::reveal` verb). The blob rides `Action::witness_blobs`
    /// UNDER the signature and is what `PreimageGate` cell programs verify
    /// against the committed digest (`dregg.program.preimage_gate`).
    fn reveal<'py>(
        mut slf: PyRefMut<'py, Self>,
        preimage: &Bound<'py, PyAny>,
    ) -> PyResult<PyRefMut<'py, Self>> {
        let preimage = parse_32(preimage, "preimage")?;
        slf.witnesses.push(WitnessBlob {
            kind: WitnessKind::Preimage32,
            bytes: preimage.to_vec(),
        });
        Ok(slf)
    }

    /// Set the action's method verb (default "execute").
    fn method<'py>(mut slf: PyRefMut<'py, Self>, name: &str) -> PyRefMut<'py, Self> {
        slf.method = name.to_string();
        slf
    }

    /// Set the turn fee (computron budget; default 10_000).
    fn fee(mut slf: PyRefMut<'_, Self>, fee: u64) -> PyRefMut<'_, Self> {
        slf.fee = Some(fee);
        slf
    }

    /// Attach a memo string.
    fn memo<'py>(mut slf: PyRefMut<'py, Self>, memo: &str) -> PyRefMut<'py, Self> {
        slf.memo = Some(memo.to_string());
        slf
    }

    /// Pin the turn nonce explicitly. When omitted, `.sign()` fetches the
    /// acting cell's live nonce from the node.
    fn nonce(mut slf: PyRefMut<'_, Self>, nonce: u64) -> PyRefMut<'_, Self> {
        slf.nonce = Some(nonce);
        slf
    }

    /// Pin the deadline: the last block height at which the node admits this turn. A
    /// BLOCK HEIGHT, not a Unix timestamp — a node refuses a deadline more than
    /// `MAX_TURN_VALIDITY_HORIZON_BLOCKS` past its height. Default: the node's
    /// `latest_height` (from `/status`) plus `DEFAULT_TURN_VALIDITY_HORIZON_BLOCKS`, the
    /// same stamp the node puts on turns it builds.
    fn valid_until(mut slf: PyRefMut<'_, Self>, height: i64) -> PyRefMut<'_, Self> {
        slf.valid_until = Some(height);
        slf
    }

    /// Number of staged effects.
    fn __len__(&self) -> usize {
        self.effects.len()
    }

    /// Sign the staged turn with this identity's Ed25519 key, yielding an
    /// AuthorizedTurn ready to `.submit()`. After this point the act is
    /// credentialed; there is no way back to an unauthorized shape.
    ///
    /// Refuses an empty turn. Fetches the federation id, live nonce and latest
    /// height from the node unless they were pinned (`federation_id=` on
    /// `.turn()`, `.nonce(n)`, `.valid_until(h)`) — pin all three for fully
    /// offline construction.
    fn sign(&self, py: Python<'_>) -> PyResult<AuthorizedTurn> {
        if self.effects.is_empty() {
            return Err(refused(
                "refusing to sign an empty turn (no effects staged) — stage a verb first \
                 (.transfer / .write / .grant / .increment_nonce)",
            ));
        }

        let node_url = self.node_url.clone();
        let federation_id = match self.federation_id {
            Some(fid) => fid,
            None => py.detach(|| fetch_federation_id(&node_url)).map_err(err)?,
        };

        let ident = self.identity.borrow(py);
        let agent_hex = hex::encode(ident.clerk.cell_id("default").0);
        let nonce = match self.nonce {
            Some(n) => n,
            None => py
                .detach(|| fetch_cell_nonce(&node_url, &agent_hex))
                .map_err(err)?,
        };

        let valid_until = match self.valid_until {
            Some(h) => h,
            None => dregg_turn::valid_until_at(
                py.detach(|| fetch_latest_height(&node_url)).map_err(err)?,
                dregg_turn::DEFAULT_TURN_VALIDITY_HORIZON_BLOCKS,
            ),
        };

        let signed = build_signed_turn(
            &ident.clerk,
            "default",
            &self.method,
            self.effects.clone(),
            self.target,
            self.witnesses.clone(),
            &federation_id,
            nonce,
            self.fee.unwrap_or(10_000),
            self.memo.clone(),
            valid_until,
        );
        Ok(AuthorizedTurn {
            signed,
            node_url: self.node_url.clone(),
            devnet_key: self.devnet_key.clone(),
        })
    }

    fn __repr__(&self, py: Python<'_>) -> String {
        format!(
            "TurnBuilder(agent={}, method={:?}, effects={})",
            hex::encode(self.acting_cell(py).0),
            self.method,
            self.effects.len()
        )
    }
}

// ─── AuthorizedTurn ───

/// A signed, ready-to-submit turn. Inspect with `.explain()` (the clerk's
/// faithful, total, anti-blind-signing rendering); execute with `.submit()`.
#[pyclass(unsendable, module = "dregg")]
struct AuthorizedTurn {
    signed: SignedTurn,
    node_url: String,
    devnet_key: Option<String>,
}

#[pymethods]
impl AuthorizedTurn {
    /// The clerk's faithful, total explanation of exactly what was signed.
    fn explain(&self) -> String {
        explain_turn(&self.signed.turn)
    }

    /// Hex hash of the signed turn (what the signature covers, and what the
    /// receipt will name).
    #[getter]
    fn turn_hash(&self) -> String {
        hex::encode(self.signed.turn.hash())
    }

    /// Hex signer public key.
    #[getter]
    fn signer(&self) -> String {
        hex::encode(self.signed.signer.0)
    }

    /// The canonical wire bytes (postcard `SignedTurn`) — exactly the body
    /// `.submit()` POSTs to `/api/turns/submit-signed`.
    fn to_bytes<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyBytes>> {
        let bytes = postcard::to_stdvec(&self.signed)
            .map_err(|e| err(format!("failed to encode signed turn: {e}")))?;
        Ok(PyBytes::new(py, &bytes))
    }

    /// Execute the turn on the node and return the Receipt.
    ///
    /// Raises DreggRefused when the node rejects — the message carries the
    /// node's reason and the faithful explanation of what was signed.
    fn submit(&self, py: Python<'_>) -> PyResult<Receipt> {
        let body = postcard::to_stdvec(&self.signed)
            .map_err(|e| err(format!("failed to encode signed turn: {e}")))?;
        let node_url = self.node_url.clone();
        let key = self.devnet_key.clone();
        let response = py
            .detach(|| post_signed_turn(&node_url, &body, key.as_deref()))
            .map_err(err)?;

        let accepted = response
            .get("accepted")
            .and_then(|a| a.as_bool())
            .unwrap_or(false);
        if !accepted {
            let reason = response
                .get("error")
                .and_then(|e| e.as_str())
                .unwrap_or("turn did not commit")
                .to_string();
            return Err(refused(format!(
                "{reason}\n\nwhat was signed:\n{}",
                self.explain()
            )));
        }
        Ok(Receipt {
            data: response,
            node_url: Some(self.node_url.clone()),
            proof: None,
        })
    }

    fn __repr__(&self) -> String {
        format!("AuthorizedTurn(turn_hash={:?})", self.turn_hash())
    }
}

// ─── Receipt ───

/// **The receipt noun** — proof-of-execution for one committed turn,
/// dict-like over the node's JSON, with the STARK proof lazily fetched
/// (receipts are born proofless; the proof is additive attestation).
#[pyclass(unsendable, module = "dregg")]
struct Receipt {
    data: serde_json::Value,
    node_url: Option<String>,
    proof: Option<serde_json::Value>,
}

impl Receipt {
    fn str_field(&self, key: &str) -> Option<String> {
        self.data
            .get(key)
            .and_then(|v| v.as_str())
            .map(str::to_string)
    }
}

#[pymethods]
impl Receipt {
    /// Hex hash of the committed turn.
    #[getter]
    fn turn_hash(&self) -> PyResult<String> {
        self.str_field("turn_hash")
            .ok_or_else(|| err("receipt carries no turn_hash"))
    }

    /// Hex receipt-chain hash, when the source surface carried one (the
    /// event stream does; the submit acknowledgement does not).
    #[getter]
    fn receipt_hash(&self) -> Option<String> {
        self.str_field("receipt_hash")
    }

    /// Node policy hint; not_required is signature attestation only.
    #[getter]
    fn proof_status(&self) -> Option<String> {
        self.data
            .get("proof_status")
            .and_then(|v| v.as_str())
            .map(str::to_owned)
    }

    /// Whether a proof was already attached at the time this receipt was
    /// observed (`.proof()` may still fetch one that landed later).
    #[getter]
    fn has_proof(&self) -> bool {
        self.data
            .get("has_proof")
            .and_then(|v| v.as_bool())
            .unwrap_or(false)
    }

    /// Lazily fetch the composed full-turn STARK for this receipt's turn
    /// from `GET /api/turn/{hash}/proof`. Returns a dict
    /// (`turn_hash` / `proof_len` / `proof_hex`) or None while the node's
    /// async prove pool hasn't attached one. The fetch is cached.
    #[pyo3(signature = (node_url=None))]
    fn proof<'py>(
        &mut self,
        py: Python<'py>,
        node_url: Option<&str>,
    ) -> PyResult<Option<Bound<'py, PyAny>>> {
        if self.proof.is_none() {
            let base = node_url
                .map(str::to_string)
                .or_else(|| self.node_url.clone())
                .ok_or_else(|| {
                    err("this receipt has no node_url; pass proof(node_url=...) explicitly")
                })?;
            let hash = self.turn_hash()?;
            let url = format!("{}/api/turn/{}/proof", base.trim_end_matches('/'), hash);
            let fetched = py.detach(move || match http_agent().get(&url).call() {
                Ok(resp) => resp
                    .into_json::<serde_json::Value>()
                    .map(Some)
                    .map_err(|e| format!("GET {url}: {e}")),
                Err(ureq::Error::Status(404, _)) => Ok(None),
                Err(e) => Err(format!("GET {url}: {e}")),
            });
            match fetched.map_err(err)? {
                Some(v) => {
                    if v["proof_status"] == "not_required" {
                        return Err(err(
                            "coordination turn has signature attestation only; no validity proof",
                        ));
                    }
                    if v["proof_status"] != "proved"
                        || v["proof_hex"].as_str().is_none_or(str::is_empty)
                    {
                        return Err(err("node returned no proved artifact"));
                    }
                    self.proof = Some(v);
                }
                None => return Ok(None),
            }
        }
        self.proof.as_ref().map(|v| json_to_py(py, v)).transpose()
    }

    /// The receipt's full JSON as a plain dict.
    fn to_dict<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        json_to_py(py, &self.data)
    }

    fn keys(&self) -> Vec<String> {
        match self.data.as_object() {
            Some(map) => map.keys().cloned().collect(),
            None => Vec::new(),
        }
    }

    #[pyo3(signature = (key, default=None))]
    fn get<'py>(
        &self,
        py: Python<'py>,
        key: &str,
        default: Option<Bound<'py, PyAny>>,
    ) -> PyResult<Bound<'py, PyAny>> {
        match self.data.get(key) {
            Some(v) => json_to_py(py, v),
            None => Ok(default.unwrap_or_else(|| py.None().into_bound(py))),
        }
    }

    fn __getitem__<'py>(&self, py: Python<'py>, key: &str) -> PyResult<Bound<'py, PyAny>> {
        match self.data.get(key) {
            Some(v) => json_to_py(py, v),
            None => Err(PyKeyError::new_err(key.to_string())),
        }
    }

    fn __contains__(&self, key: &str) -> bool {
        self.data.get(key).is_some()
    }

    fn __len__(&self) -> usize {
        self.data.as_object().map(|m| m.len()).unwrap_or(0)
    }

    fn __repr__(&self) -> String {
        format!(
            "Receipt(turn_hash={:?}, has_proof={})",
            self.str_field("turn_hash").unwrap_or_default(),
            self.has_proof()
        )
    }
}

// ─── subscribe: the receipt nervous system, blocking-iterator edition ───

#[derive(Default)]
struct SseEvent {
    id: Option<String>,
    name: Option<String>,
    data: String,
}

/// Minimal SSE parser (same field semantics as `sdk/src/events.rs`): splits
/// on blank lines, honors `id:` / `event:` / `data:`, ignores `:` heartbeats.
#[derive(Default)]
struct SseParser {
    buf: String,
    current: SseEvent,
}

impl SseParser {
    fn push(&mut self, chunk: &[u8]) -> Vec<SseEvent> {
        self.buf.push_str(&String::from_utf8_lossy(chunk));
        let mut done = Vec::new();
        while let Some(nl) = self.buf.find('\n') {
            let line: String = self.buf.drain(..=nl).collect();
            let line = line.trim_end_matches(['\n', '\r']);
            if line.is_empty() {
                let event = std::mem::take(&mut self.current);
                if !event.data.is_empty() {
                    done.push(event);
                }
                continue;
            }
            if line.starts_with(':') {
                continue; // heartbeat / comment
            }
            let (field, value) = match line.split_once(':') {
                Some((f, v)) => (f, v.strip_prefix(' ').unwrap_or(v)),
                None => (line, ""),
            };
            match field {
                "id" => self.current.id = Some(value.to_string()),
                "event" => self.current.name = Some(value.to_string()),
                "data" => {
                    if !self.current.data.is_empty() {
                        self.current.data.push('\n');
                    }
                    self.current.data.push_str(value);
                }
                _ => {}
            }
        }
        done
    }
}

/// The live receipt feed: a blocking iterator of Receipts over the node's
/// `GET /api/events/stream` SSE broadcast. Reconnects with exponential
/// backoff and `Last-Event-ID` resume; iterate forever or `break`.
/// Delivery is at-least-once across reconnects — dedupe by `receipt_hash`
/// if it matters.
#[pyclass(unsendable, module = "dregg")]
struct ReceiptStream {
    node_url: String,
    query: Vec<(String, String)>,
    last_event_id: Option<String>,
    reader: Option<Box<dyn Read + Send>>,
    parser: SseParser,
    pending: VecDeque<serde_json::Value>,
    backoff_ms: u64,
}

impl ReceiptStream {
    fn connect(&mut self) -> Result<(), String> {
        let agent = ureq::AgentBuilder::new()
            .timeout_connect(Duration::from_secs(10))
            // No overall timeout: the stream lives forever. The read timeout
            // sits just above the node's 30s heartbeat so a dead connection
            // is detected (and Ctrl-C is honored) within ~40s worst case.
            .timeout_read(Duration::from_secs(40))
            .build();
        let mut req = agent
            .get(&format!("{}/api/events/stream", self.node_url))
            .set("accept", "text/event-stream");
        for (k, v) in &self.query {
            req = req.query(k, v);
        }
        if let Some(id) = &self.last_event_id {
            req = req.set("last-event-id", id);
        }
        let resp = req.call().map_err(|e| e.to_string())?;
        self.reader = Some(Box::new(resp.into_reader()));
        Ok(())
    }
}

#[pymethods]
impl ReceiptStream {
    fn __iter__(slf: PyRef<'_, Self>) -> PyRef<'_, Self> {
        slf
    }

    fn __next__(&mut self, py: Python<'_>) -> PyResult<Receipt> {
        loop {
            py.check_signals()?;

            if let Some(value) = self.pending.pop_front() {
                return Ok(Receipt {
                    data: value,
                    node_url: Some(self.node_url.clone()),
                    proof: None,
                });
            }

            if self.reader.is_none() {
                let res = py.detach(|| self.connect());
                if res.is_err() {
                    let backoff = self.backoff_ms;
                    py.detach(|| std::thread::sleep(Duration::from_millis(backoff)));
                    self.backoff_ms = (self.backoff_ms * 2).min(15_000);
                    continue;
                }
            }

            let mut buf = [0u8; 8192];
            let reader = self.reader.as_mut().expect("connected above");
            let n = py.detach(|| reader.read(&mut buf));
            match n {
                Ok(0) | Err(_) => {
                    // EOF or transport error: reconnect with backoff.
                    self.reader = None;
                    let backoff = self.backoff_ms;
                    py.detach(|| std::thread::sleep(Duration::from_millis(backoff)));
                    self.backoff_ms = (self.backoff_ms * 2).min(15_000);
                    continue;
                }
                Ok(n) => {
                    for event in self.parser.push(&buf[..n]) {
                        if let Some(id) = &event.id {
                            self.last_event_id = Some(id.clone());
                        }
                        if event.name.as_deref() != Some("receipt") {
                            continue;
                        }
                        if let Ok(value) = serde_json::from_str(&event.data) {
                            self.pending.push_back(value);
                        }
                    }
                    if !self.pending.is_empty() {
                        self.backoff_ms = 500;
                    }
                }
            }
        }
    }

    fn __repr__(&self) -> String {
        format!("ReceiptStream(node_url={:?})", self.node_url)
    }
}

/// Subscribe to a node's committed-receipt broadcast as a blocking iterator
/// of Receipts. `cell` filters to receipts touching one cell; `kind` to one
/// effect kind (e.g. "transfer", "set_field").
#[pyfunction]
#[pyo3(signature = (node_url, cell=None, kind=None))]
fn subscribe(
    node_url: &str,
    cell: Option<&Bound<'_, PyAny>>,
    kind: Option<&str>,
) -> PyResult<ReceiptStream> {
    let mut query = Vec::new();
    if let Some(c) = cell {
        // Accept hex/bytes (validated) — straight from an explorer URL works.
        query.push(("cell".to_string(), hex::encode(parse_32(c, "cell")?)));
    }
    if let Some(k) = kind {
        query.push(("kind".to_string(), k.to_string()));
    }
    Ok(ReceiptStream {
        node_url: node_url.trim_end_matches('/').to_string(),
        query,
        last_event_id: None,
        reader: None,
        parser: SseParser::default(),
        pending: VecDeque::new(),
        backoff_ms: 500,
    })
}

// ─── explain ───

/// The clerk's faithful rendering of a turn: pass an AuthorizedTurn (exactly
/// what was signed) or a TurnBuilder (a DRAFT rendering of the staged
/// effects — not yet a credentialed act).
#[pyfunction]
fn explain(turn: &Bound<'_, PyAny>) -> PyResult<String> {
    if let Ok(authorized) = turn.cast::<AuthorizedTurn>() {
        return Ok(authorized.borrow().explain());
    }
    if let Ok(builder) = turn.cast::<TurnBuilder>() {
        let builder = builder.borrow();
        let py = turn.py();
        let ident = builder.identity.borrow(py);
        // Render the draft as the unsigned action it would become — the same
        // explain the signed turn will carry, marked as a draft. Honors
        // `.on(target)` so the draft names the cell the act will target.
        let action = dregg_sdk::raw::unsigned_action_named(
            builder
                .target
                .unwrap_or_else(|| ident.clerk.cell_id("default")),
            &builder.method,
            builder.effects.clone(),
        );
        return Ok(format!("DRAFT (unsigned):\n{}", explain_action(&action)));
    }
    Err(PyTypeError::new_err(
        "explain() takes an AuthorizedTurn or a TurnBuilder",
    ))
}

// ─── profiles listing ───

/// List the local profile store (name / public_key / created_at / active).
#[pyfunction]
fn list_profiles(py: Python<'_>) -> PyResult<Bound<'_, PyList>> {
    let infos = profiles::list().map_err(|e| err(e.to_string()))?;
    let out = PyList::empty(py);
    for p in infos {
        let d = PyDict::new(py);
        d.set_item("name", p.name)?;
        d.set_item("public_key", p.public_key_hex)?;
        d.set_item("created_at", p.created_at)?;
        d.set_item("active", p.active)?;
        out.append(d)?;
    }
    Ok(out)
}

// ─── program: the constraint language at the builder surface ───

/// One cell-program constraint atom (a `StateConstraint`). Compose lists of
/// these into a content-addressed factory descriptor via
/// `dregg.program.descriptor([...])`.
#[pyclass(
    unsendable,
    module = "dregg.program",
    name = "Constraint",
    from_py_object
)]
#[derive(Clone)]
struct PyConstraint {
    inner: StateConstraint,
}

#[pymethods]
impl PyConstraint {
    fn __repr__(&self) -> String {
        format!("Constraint({:?})", self.inner)
    }
}

fn parse_hash_kind(kind: &str) -> PyResult<HashKind> {
    match kind.to_ascii_lowercase().as_str() {
        "blake3" => Ok(HashKind::Blake3),
        "poseidon2" => Ok(HashKind::Poseidon2),
        other => Err(PyValueError::new_err(format!(
            "hash_kind: expected blake3 or poseidon2, got {other:?}"
        ))),
    }
}

/// The turn's sender must be exactly `pk` (actor binding; fail-closed).
#[pyfunction]
fn sender_is(pk: &Bound<'_, PyAny>) -> PyResult<PyConstraint> {
    Ok(PyConstraint {
        inner: dregg_sdk::program::sender_is(parse_32(pk, "pk")?),
    })
}

/// The sender must equal the 32-byte identity stored in slot `index` (the
/// dynamic-owner actor binding).
#[pyfunction]
fn sender_in_slot(index: u8) -> PyConstraint {
    PyConstraint {
        inner: dregg_sdk::program::sender_in_slot(index),
    }
}

/// Post-turn own-balance floor (`balance >= min`).
#[pyfunction]
fn balance_gte(min: u64) -> PyConstraint {
    PyConstraint {
        inner: dregg_sdk::program::balance_gte(min),
    }
}

/// Post-turn own-balance ceiling (`balance <= max`).
#[pyfunction]
fn balance_lte(max: u64) -> PyConstraint {
    PyConstraint {
        inner: dregg_sdk::program::balance_lte(max),
    }
}

/// Knowledge gate: the turn must exhibit a witness whose hash equals the
/// commitment stored in slot `commitment_index`.
#[pyfunction]
#[pyo3(signature = (commitment_index, hash_kind="blake3"))]
fn preimage_gate(commitment_index: u8, hash_kind: &str) -> PyResult<PyConstraint> {
    Ok(PyConstraint {
        inner: dregg_sdk::program::preimage_gate(commitment_index, parse_hash_kind(hash_kind)?),
    })
}

/// Slot `index` may never change once the cell is born.
#[pyfunction]
fn immutable(index: u8) -> PyConstraint {
    PyConstraint {
        inner: dregg_sdk::program::immutable(index),
    }
}

/// Slot `index` may be written at most once (from zero).
#[pyfunction]
fn write_once(index: u8) -> PyConstraint {
    PyConstraint {
        inner: dregg_sdk::program::write_once(index),
    }
}

/// Disjunction over simple atoms (sender_is / sender_in_slot / balance_gte /
/// balance_lte / preimage_gate / write_once / immutable).
#[pyfunction]
fn any_of(variants: Vec<PyConstraint>) -> PyResult<PyConstraint> {
    let simples = variants
        .into_iter()
        .map(|c| simple_of(&c.inner))
        .collect::<PyResult<Vec<_>>>()?;
    Ok(PyConstraint {
        inner: dregg_sdk::program::any_of(simples),
    })
}

fn simple_of(c: &StateConstraint) -> PyResult<SimpleStateConstraint> {
    Ok(match c {
        StateConstraint::SenderIs { pk } => SimpleStateConstraint::SenderIs { pk: *pk },
        StateConstraint::SenderInSlot { index } => {
            SimpleStateConstraint::SenderInSlot { index: *index }
        }
        StateConstraint::BalanceGte { min } => SimpleStateConstraint::BalanceGte { min: *min },
        StateConstraint::BalanceLte { max } => SimpleStateConstraint::BalanceLte { max: *max },
        StateConstraint::PreimageGate {
            commitment_index,
            hash_kind,
        } => SimpleStateConstraint::PreimageGate {
            commitment_index: *commitment_index,
            hash_kind: *hash_kind,
        },
        StateConstraint::WriteOnce { index } => SimpleStateConstraint::WriteOnce { index: *index },
        StateConstraint::Immutable { index } => SimpleStateConstraint::Immutable { index: *index },
        other => {
            return Err(PyTypeError::new_err(format!(
                "constraint {other:?} has no simple-atom form for any_of"
            )));
        }
    })
}

/// Publish a constraint list as a content-addressed factory descriptor:
/// returns `{"factory_vk": hex, "child_program_vk": hex, "constraints": n}`.
/// Anyone can recompute these from the published constraints and verify a
/// cell's law. (The safety is the executor's program gate, not this dict.)
#[pyfunction]
fn descriptor<'py>(
    py: Python<'py>,
    constraints: Vec<PyConstraint>,
) -> PyResult<Bound<'py, PyDict>> {
    let list: Vec<StateConstraint> = constraints.into_iter().map(|c| c.inner).collect();
    let n = list.len();
    let desc = dregg_sdk::program::programmed_cell_descriptor(list);
    let d = PyDict::new(py);
    d.set_item("factory_vk", hex::encode(desc.factory_vk))?;
    d.set_item("child_program_vk", desc.child_program_vk.map(hex::encode))?;
    d.set_item("constraints", n)?;
    Ok(d)
}

// ─── organs: the higher primitives (.docs-history-noclaude/ORGANS.md), as ergonomic HTTP faces ───
//
// Each organ is the Python face of a node service — the same routes the TS
// SDK's organ clients drive. The node computes the per-cell factory
// descriptors and seal fan-outs the wire layer does not carry; these clients
// drive them. The enforcement tooth is the executor-installed cell program
// either way (see each method's route). Operator-gated organs (trustline,
// channels) carry a devnet key; the relay (mailbox) is owner-signed.

/// **Trustline** — the bilateral line of credit (`.docs-history-noclaude/ORGANS.md` §1).
///
/// A line `issuer → holder` of N is an ATTENUATED CAPABILITY whose exercise
/// debits a shared counter; the executor-installed cell program enforces
/// `drawn ≤ ceiling` for life. The node operator IS the issuer — these routes
/// are operator-gated (pass `devnet_key=` on `Identity.trustline()`).
///
/// ```python
/// tl = ident.trustline("https://devnet.example", devnet_key="…")
/// line = tl.open(holder_cell_hex, 1000)        # four-turn funded birth
/// tl.draw(line["trustline"], 250)              # debit the shared counter
/// tl.repay(line["trustline"], 100)             # restore the line
/// tl.status(line["trustline"])                 # {line, drawn, remaining, escrow, open, …}
/// tl.settle(line["trustline"]); tl.close(line["trustline"])
/// ```
#[pyclass(module = "dregg")]
struct Trustline {
    node_url: String,
    devnet_key: Option<String>,
}

impl Trustline {
    fn post<'py>(
        &self,
        py: Python<'py>,
        path: &str,
        body: serde_json::Value,
    ) -> PyResult<Bound<'py, PyAny>> {
        let base = self.node_url.clone();
        let key = self.devnet_key.clone();
        let v = py
            .detach(|| http_send_json("POST", &base, path, &body, key.as_deref()))
            .map_err(refused)?;
        json_to_py(py, &v)
    }
}

#[pymethods]
impl Trustline {
    /// Open a directional line `operator → holder` of `line`, escrowed in full
    /// (`POST /trustline/open`; four-turn funded birth). `salt` disambiguates
    /// multiple lines to the same holder.
    #[pyo3(signature = (holder, line, salt=None))]
    fn open<'py>(
        &self,
        py: Python<'py>,
        holder: &Bound<'_, PyAny>,
        line: u64,
        salt: Option<&str>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let mut body =
            serde_json::json!({ "holder": hex::encode(parse_32(holder, "holder")?), "line": line });
        if let Some(s) = salt {
            body["salt"] = serde_json::Value::String(s.to_string());
        }
        self.post(py, "/trustline/open", body)
    }

    /// Draw `amount` against the line (`POST /trustline/draw`; one-shot per
    /// digest — supply `digest=` for client-side replay protection).
    #[pyo3(signature = (trustline, amount, digest=None))]
    fn draw<'py>(
        &self,
        py: Python<'py>,
        trustline: &Bound<'_, PyAny>,
        amount: u64,
        digest: Option<&str>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let mut body = serde_json::json!({ "trustline": hex::encode(parse_32(trustline, "trustline")?), "amount": amount });
        if let Some(d) = digest {
            body["digest"] = serde_json::Value::String(d.to_string());
        }
        self.post(py, "/trustline/draw", body)
    }

    /// Repay `amount`, restoring the line (`POST /trustline/repay`).
    fn repay<'py>(
        &self,
        py: Python<'py>,
        trustline: &Bound<'_, PyAny>,
        amount: u64,
    ) -> PyResult<Bound<'py, PyAny>> {
        let body = serde_json::json!({ "trustline": hex::encode(parse_32(trustline, "trustline")?), "amount": amount });
        self.post(py, "/trustline/repay", body)
    }

    /// Settle outstanding draws to the holders (`POST /trustline/settle`).
    fn settle<'py>(
        &self,
        py: Python<'py>,
        trustline: &Bound<'_, PyAny>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let body =
            serde_json::json!({ "trustline": hex::encode(parse_32(trustline, "trustline")?) });
        self.post(py, "/trustline/settle", body)
    }

    /// Close the line: settle outstanding to holder, residual to issuer
    /// (`POST /trustline/close`).
    fn close<'py>(
        &self,
        py: Python<'py>,
        trustline: &Bound<'_, PyAny>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let body =
            serde_json::json!({ "trustline": hex::encode(parse_32(trustline, "trustline")?) });
        self.post(py, "/trustline/close", body)
    }

    /// Live position (`GET /trustline/status/{cell}`):
    /// `{line, drawn, settled, remaining, escrow, open, coordinator_*}`.
    fn status<'py>(
        &self,
        py: Python<'py>,
        trustline: &Bound<'_, PyAny>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let cell = hex::encode(parse_32(trustline, "trustline")?);
        let base = self.node_url.clone();
        let key = self.devnet_key.clone();
        let path = format!("/trustline/status/{cell}");
        let v = py
            .detach(|| http_get_json(&base, &path, key.as_deref()))
            .map_err(err)?;
        json_to_py(py, &v)
    }

    fn __repr__(&self) -> String {
        format!("Trustline(node_url={:?})", self.node_url)
    }
}

/// **Channels** — the group-key epoch lift (`.docs-history-noclaude/ORGANS.md` §4).
///
/// A group is a CELL: membership root, key epoch, and key commitment live
/// on-cell. `remove(m)` darkens BOTH m's forward-read ability AND m's
/// group-held capabilities in ONE atomic epoch step (the `epochs_unified`
/// keystone). Message bodies never touch the chain — encrypt under the current
/// epoch key client-side and `post()` only ciphertext. Operator-gated.
///
/// ```python
/// ch = ident.channels("https://devnet.example", devnet_key="…")
/// g = ch.create(7, [{"cell": alice_hex, "seal_pk": alice_seal_hex}])
/// ch.join(g["channel"], {"cell": bob_hex, "seal_pk": bob_seal_hex})  # fresh fan_out
/// ch.post(g["channel"], g["epoch"], nonce_hex, ciphertext_hex)        # ciphertext only
/// ch.remove(g["channel"], bob_hex)                                    # bob darkened in ONE turn
/// for m in ch.messages(g["channel"]): ...                             # SSE delivery
/// ```
#[pyclass(module = "dregg")]
struct Channels {
    node_url: String,
    devnet_key: Option<String>,
}

/// Normalize a member spec (`{"cell": hex|bytes, "seal_pk": hex|bytes}`) to the
/// wire JSON `{cell, seal_pk}`.
fn member_json(m: &Bound<'_, PyAny>) -> PyResult<serde_json::Value> {
    let dict = m
        .cast::<PyDict>()
        .map_err(|_| PyTypeError::new_err("member: expected a dict {cell, seal_pk}"))?;
    let cell = dict
        .get_item("cell")?
        .ok_or_else(|| PyValueError::new_err("member: missing 'cell'"))?;
    let seal = dict
        .get_item("seal_pk")
        .ok()
        .flatten()
        .or(dict.get_item("sealPk").ok().flatten())
        .ok_or_else(|| PyValueError::new_err("member: missing 'seal_pk'"))?;
    let cell_hex = hex::encode(parse_32(&cell, "member.cell")?);
    let seal_hex = if let Ok(s) = seal.extract::<&str>() {
        s.trim().to_string()
    } else if let Ok(b) = seal.extract::<&[u8]>() {
        hex::encode(b)
    } else {
        return Err(PyTypeError::new_err(
            "member.seal_pk: expected hex str or bytes",
        ));
    };
    Ok(serde_json::json!({ "cell": cell_hex, "seal_pk": seal_hex }))
}

impl Channels {
    fn post<'py>(
        &self,
        py: Python<'py>,
        path: &str,
        body: serde_json::Value,
    ) -> PyResult<Bound<'py, PyAny>> {
        let base = self.node_url.clone();
        let key = self.devnet_key.clone();
        let v = py
            .detach(|| http_send_json("POST", &base, path, &body, key.as_deref()))
            .map_err(refused)?;
        json_to_py(py, &v)
    }
}

#[pymethods]
impl Channels {
    /// Birth the group at epoch 1 with `members` as founders (`POST
    /// /channels/create`). `tag` (u64) names the group among the operator's
    /// groups. Returns the first sealed key fan-out.
    fn create<'py>(
        &self,
        py: Python<'py>,
        tag: u64,
        members: Vec<Bound<'_, PyAny>>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let members = members
            .iter()
            .map(member_json)
            .collect::<PyResult<Vec<_>>>()?;
        self.post(
            py,
            "/channels/create",
            serde_json::json!({ "tag": tag, "members": members }),
        )
    }

    /// Add a member — one unified epoch step (`POST /channels/join`); returns
    /// the fresh fan-out.
    fn join<'py>(
        &self,
        py: Python<'py>,
        channel: &Bound<'_, PyAny>,
        member: &Bound<'_, PyAny>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let body = serde_json::json!({ "channel": hex::encode(parse_32(channel, "channel")?), "member": member_json(member)? });
        self.post(py, "/channels/join", body)
    }

    /// Remove a member — one unified epoch step that darkens both their
    /// forward-read ability and their group-held capabilities (`POST
    /// /channels/remove`). The removed member is absent from the returned
    /// fan-out.
    fn remove<'py>(
        &self,
        py: Python<'py>,
        channel: &Bound<'_, PyAny>,
        member: &Bound<'_, PyAny>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let body = serde_json::json!({ "channel": hex::encode(parse_32(channel, "channel")?), "member": hex::encode(parse_32(member, "member")?) });
        self.post(py, "/channels/remove", body)
    }

    /// Advance the epoch without a membership change (`POST /channels/rekey`;
    /// a fresh key fan-out).
    fn rekey<'py>(
        &self,
        py: Python<'py>,
        channel: &Bound<'_, PyAny>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let body = serde_json::json!({ "channel": hex::encode(parse_32(channel, "channel")?) });
        self.post(py, "/channels/rekey", body)
    }

    /// Post a message body (`POST /channels/post`). Encrypt client-side under
    /// the CURRENT epoch key, then pass only `nonce` + `ciphertext` (hex str or
    /// bytes). The body never touches the chain.
    #[pyo3(name = "post")]
    fn post_message<'py>(
        &self,
        py: Python<'py>,
        channel: &Bound<'_, PyAny>,
        epoch: u64,
        nonce: &Bound<'_, PyAny>,
        ciphertext: &Bound<'_, PyAny>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let body = serde_json::json!({
            "channel": hex::encode(parse_32(channel, "channel")?),
            "epoch": epoch,
            "nonce": hex_or_bytes(nonce, "nonce")?,
            "ciphertext": hex_or_bytes(ciphertext, "ciphertext")?,
        });
        self.post(py, "/channels/post", body)
    }

    /// Live group state (`GET /channels/status/{cell}`): epoch, roster
    /// commitment, and the `epochs_unified` invariant tooth.
    fn status<'py>(
        &self,
        py: Python<'py>,
        channel: &Bound<'_, PyAny>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let cell = hex::encode(parse_32(channel, "channel")?);
        let base = self.node_url.clone();
        let key = self.devnet_key.clone();
        let path = format!("/channels/status/{cell}");
        let v = py
            .detach(|| http_get_json(&base, &path, key.as_deref()))
            .map_err(err)?;
        json_to_py(py, &v)
    }

    /// Subscribe to the group's message stream (`GET /channels/messages/{cell}`,
    /// SSE) as a blocking iterator of ciphertext-envelope dicts
    /// (`{seq, epoch, nonce, ciphertext}`). Open each body with the epoch key
    /// you hold from the fan-out. Reconnects with backoff + `Last-Event-ID`.
    fn messages(&self, channel: &Bound<'_, PyAny>) -> PyResult<SseJsonStream> {
        let cell = hex::encode(parse_32(channel, "channel")?);
        Ok(SseJsonStream::open(
            &self.node_url,
            &format!("/channels/messages/{cell}"),
        ))
    }

    fn __repr__(&self) -> String {
        format!("Channels(node_url={:?})", self.node_url)
    }
}

/// A blocking iterator over a node SSE route, yielding each event's `data:`
/// JSON payload as a Python object. The generic twin of [`ReceiptStream`] (no
/// `event:` name filter) used by the channels message stream. Reconnects with
/// exponential backoff and `Last-Event-ID` resume.
#[pyclass(unsendable, module = "dregg")]
struct SseJsonStream {
    url: String,
    last_event_id: Option<String>,
    reader: Option<Box<dyn Read + Send>>,
    parser: SseParser,
    pending: VecDeque<serde_json::Value>,
    backoff_ms: u64,
}

impl SseJsonStream {
    fn open(base: &str, path: &str) -> Self {
        SseJsonStream {
            url: format!("{}{}", base.trim_end_matches('/'), path),
            last_event_id: None,
            reader: None,
            parser: SseParser::default(),
            pending: VecDeque::new(),
            backoff_ms: 500,
        }
    }

    fn connect(&mut self) -> Result<(), String> {
        let agent = ureq::AgentBuilder::new()
            .timeout_connect(Duration::from_secs(10))
            .timeout_read(Duration::from_secs(40))
            .build();
        let mut req = agent.get(&self.url).set("accept", "text/event-stream");
        if let Some(id) = &self.last_event_id {
            req = req.set("last-event-id", id);
        }
        let resp = req.call().map_err(|e| e.to_string())?;
        self.reader = Some(Box::new(resp.into_reader()));
        Ok(())
    }
}

#[pymethods]
impl SseJsonStream {
    fn __iter__(slf: PyRef<'_, Self>) -> PyRef<'_, Self> {
        slf
    }

    fn __next__(&mut self, py: Python<'_>) -> PyResult<Py<PyAny>> {
        loop {
            py.check_signals()?;
            if let Some(value) = self.pending.pop_front() {
                return Ok(json_to_py(py, &value)?.unbind());
            }
            if self.reader.is_none() {
                if py.detach(|| self.connect()).is_err() {
                    let backoff = self.backoff_ms;
                    py.detach(|| std::thread::sleep(Duration::from_millis(backoff)));
                    self.backoff_ms = (self.backoff_ms * 2).min(15_000);
                    continue;
                }
            }
            let mut buf = [0u8; 8192];
            let reader = self.reader.as_mut().expect("connected above");
            match py.detach(|| reader.read(&mut buf)) {
                Ok(0) | Err(_) => {
                    self.reader = None;
                    let backoff = self.backoff_ms;
                    py.detach(|| std::thread::sleep(Duration::from_millis(backoff)));
                    self.backoff_ms = (self.backoff_ms * 2).min(15_000);
                }
                Ok(n) => {
                    for event in self.parser.push(&buf[..n]) {
                        if let Some(id) = &event.id {
                            self.last_event_id = Some(id.clone());
                        }
                        if let Ok(value) = serde_json::from_str(&event.data) {
                            self.pending.push_back(value);
                        }
                    }
                    if !self.pending.is_empty() {
                        self.backoff_ms = 500;
                    }
                }
            }
        }
    }

    fn __repr__(&self) -> String {
        format!("SseJsonStream(url={:?})", self.url)
    }
}

/// Accept a hex `str` or `bytes`, returning a hex string (no length pin — used
/// for variable-length nonces/ciphertexts).
fn hex_or_bytes(obj: &Bound<'_, PyAny>, what: &str) -> PyResult<String> {
    if let Ok(s) = obj.extract::<&str>() {
        return Ok(s.trim().to_string());
    }
    if let Ok(b) = obj.extract::<&[u8]>() {
        return Ok(hex::encode(b));
    }
    Err(PyTypeError::new_err(format!(
        "{what}: expected hex str or bytes"
    )))
}

/// **Mailbox** — a hosted inbox over the relay (`.docs-history-noclaude/ORGANS.md` §2).
///
/// Store-and-forward: senders enqueue sealed bodies to your inbox; you drain
/// them with a custody proof. The relay sees only ciphertext. Membership ops
/// (`subscribe` / `unsubscribe` / `drain`) are Ed25519-signed by the inbox
/// OWNER (this client signs them); `send` is open.
///
/// Honest scope: sealing (X25519 → ChaCha20-Poly1305) and re-running the
/// dequeue Merkle verifier are NOT done here — bring already-sealed ciphertext
/// to `send()`, and recompute each drained body's `content_hash` before
/// trusting it.
///
/// ```python
/// mb = ident.mailbox("http://relay.example:3100")
/// mb.subscribe()                       # create your hosted inbox
/// # … a sender elsewhere: other.send(my_pubkey_hex, sealed_ciphertext, 100) …
/// out = mb.drain(50)                   # each carries a dequeue (custody) proof
/// mb.unsubscribe()
/// ```
#[pyclass(unsendable, module = "dregg")]
struct Mailbox {
    identity: Py<Identity>,
    base_url: String,
}

const RELAY_SUBSCRIBE_DOMAIN: &[u8] = b"dregg-relay-subscribe-v1";
const RELAY_UNSUBSCRIBE_DOMAIN: &[u8] = b"dregg-relay-unsubscribe-v1";
const RELAY_DRAIN_DOMAIN: &[u8] = b"dregg-relay-drain-v1";

impl Mailbox {
    fn owner_hex(&self, py: Python<'_>) -> String {
        hex::encode(self.identity.borrow(py).clerk.public_key().0)
    }

    /// Sign `domain || owner_pk || nonce [|| extra]` with the owner key,
    /// returning `(owner_hex, nonce_hex, signature_hex)`.
    fn signed_tuple(
        &self,
        py: Python<'_>,
        domain: &[u8],
        extra: &[u8],
    ) -> (String, String, String) {
        let ident = self.identity.borrow(py);
        let owner = ident.clerk.public_key().0;
        let mut nonce = [0u8; 8];
        getrandom_fill(&mut nonce);
        let mut msg = Vec::with_capacity(domain.len() + 32 + 8 + extra.len());
        msg.extend_from_slice(domain);
        msg.extend_from_slice(&owner);
        msg.extend_from_slice(&nonce);
        msg.extend_from_slice(extra);
        let sig = ident.clerk.sign_bytes(&msg);
        (hex::encode(owner), hex::encode(nonce), hex::encode(sig.0))
    }
}

#[pymethods]
impl Mailbox {
    /// The owner public key (hex) — the inbox id.
    #[getter]
    fn owner(&self, py: Python<'_>) -> String {
        self.owner_hex(py)
    }

    /// `GET /relay/status` — the relay operator's identity + bond.
    fn relay_status<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        let base = self.base_url.clone();
        let v = py
            .detach(|| http_get_json(&base, "/relay/status", None))
            .map_err(err)?;
        json_to_py(py, &v)
    }

    /// `POST /relay/subscribe` — create this owner's hosted inbox (owner-signed
    /// under `dregg-relay-subscribe-v1`).
    #[pyo3(signature = (capacity=None, min_deposit=None))]
    fn subscribe<'py>(
        &self,
        py: Python<'py>,
        capacity: Option<u64>,
        min_deposit: Option<u64>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let (owner, nonce, sig) = self.signed_tuple(py, RELAY_SUBSCRIBE_DOMAIN, &[]);
        let mut body = serde_json::json!({ "owner": owner, "nonce": nonce, "signature": sig });
        if let Some(c) = capacity {
            body["capacity"] = serde_json::json!(c);
        }
        if let Some(d) = min_deposit {
            body["min_deposit"] = serde_json::json!(d);
        }
        let base = self.base_url.clone();
        let v = py
            .detach(|| http_send_json("POST", &base, "/relay/subscribe", &body, None))
            .map_err(refused)?;
        json_to_py(py, &v)
    }

    /// `DELETE /relay/unsubscribe` — remove this owner's inbox (owner-signed
    /// under `dregg-relay-unsubscribe-v1`).
    fn unsubscribe<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        let (owner, nonce, sig) = self.signed_tuple(py, RELAY_UNSUBSCRIBE_DOMAIN, &[]);
        let body = serde_json::json!({ "owner": owner, "nonce": nonce, "signature": sig });
        let base = self.base_url.clone();
        let v = py
            .detach(|| http_send_json("DELETE", &base, "/relay/unsubscribe", &body, None))
            .map_err(refused)?;
        json_to_py(py, &v)
    }

    /// `POST /relay/send/{dest}` — enqueue an ALREADY-SEALED `ciphertext`
    /// (hex str or bytes) to `dest`'s inbox, paying `deposit`. Unauthenticated.
    fn send<'py>(
        &self,
        py: Python<'py>,
        dest: &Bound<'_, PyAny>,
        ciphertext: &Bound<'_, PyAny>,
        deposit: u64,
    ) -> PyResult<Bound<'py, PyAny>> {
        let dest_hex = hex::encode(parse_32(dest, "dest")?);
        use base64::Engine;
        let payload_b64 =
            base64::engine::general_purpose::STANDARD.encode(ciphertext_bytes(ciphertext)?);
        let body = serde_json::json!({ "sender": self.owner_hex(py), "payload": payload_b64, "deposit": deposit });
        let base = self.base_url.clone();
        let path = format!("/relay/send/{dest_hex}");
        let v = py
            .detach(|| http_send_json("POST", &base, &path, &body, None))
            .map_err(err)?;
        json_to_py(py, &v)
    }

    /// `GET /relay/drain` — drain up to `max` messages (owner-signed under
    /// `dregg-relay-drain-v1` over `owner || nonce || max_le(u64)`), each with
    /// its full dequeue (custody) proof. Recompute each body's `content_hash`
    /// before trusting it.
    #[pyo3(signature = (max=100))]
    fn drain<'py>(&self, py: Python<'py>, max: u64) -> PyResult<Bound<'py, PyAny>> {
        let (owner, nonce, sig) = self.signed_tuple(py, RELAY_DRAIN_DOMAIN, &max.to_le_bytes());
        let base = self.base_url.clone();
        let path = format!("/relay/drain?owner={owner}&nonce={nonce}&max={max}&signature={sig}");
        let v = py
            .detach(|| http_get_json(&base, &path, None))
            .map_err(err)?;
        json_to_py(py, &v)
    }

    /// `GET /relay/inbox/{id}/status` — this inbox's queue depth + root.
    fn inbox_status<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        let owner = self.owner_hex(py);
        let base = self.base_url.clone();
        let path = format!("/relay/inbox/{owner}/status");
        let v = py
            .detach(|| http_get_json(&base, &path, None))
            .map_err(err)?;
        json_to_py(py, &v)
    }

    fn __repr__(&self, py: Python<'_>) -> String {
        format!(
            "Mailbox(owner={:?}, relay={:?})",
            self.owner_hex(py),
            self.base_url
        )
    }
}

fn ciphertext_bytes(obj: &Bound<'_, PyAny>) -> PyResult<Vec<u8>> {
    if let Ok(b) = obj.extract::<&[u8]>() {
        return Ok(b.to_vec());
    }
    if let Ok(s) = obj.extract::<&str>() {
        return hex::decode(s.trim())
            .map_err(|e| PyValueError::new_err(format!("ciphertext: invalid hex: {e}")));
    }
    Err(PyTypeError::new_err(
        "ciphertext: expected bytes or hex str",
    ))
}

/// Minimal getrandom fill (the binding already pulls `rand` transitively via
/// the SDK; use the OS source directly to avoid a new dep surface).
fn getrandom_fill(buf: &mut [u8]) {
    // `ureq`/`rustls` already pull `getrandom`; reuse it.
    getrandom::getrandom(buf).expect("OS RNG unavailable");
}

/// **Attested query** — the light-client read surface (Noun 2's Python face).
///
/// No identity, no signing. Fetches the federation-attested state roots,
/// finalized checkpoints, and a committed turn's full-turn STARK so a caller
/// can hand them to a verifier or trust them under the federation's signature
/// threshold.
///
/// Honest scope: verifying a STARK or a threshold signature is a Rust/Lean
/// operation — this surfaces the artifacts to verify elsewhere, it does not
/// return a checked verdict on its own. (The `signatures` / `qc_votes` count is
/// the trust signal.)
///
/// ```python
/// aq = dregg.AttestedQuery("https://devnet.example")
/// aq.attested_roots()        # federation-signed state roots (+ signature count)
/// aq.checkpoint()            # latest finalized checkpoint (+ qc votes)
/// aq.turn_proof(turn_hash)   # full-turn STARK bytes (verify elsewhere) or None
/// ```
#[pyclass(module = "dregg")]
struct AttestedQuery {
    node_url: String,
}

#[pymethods]
impl AttestedQuery {
    #[new]
    fn new(node_url: &str) -> Self {
        AttestedQuery {
            node_url: node_url.trim_end_matches('/').to_string(),
        }
    }

    fn get<'py>(&self, py: Python<'py>, path: String) -> PyResult<Bound<'py, PyAny>> {
        let base = self.node_url.clone();
        let v = py
            .detach(move || http_get_json(&base, &path, None))
            .map_err(err)?;
        json_to_py(py, &v)
    }

    /// `GET /federation/roots` — the federation-attested state roots.
    fn attested_roots<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        self.get(py, "/federation/roots".to_string())
    }

    /// `GET /checkpoint/latest` — the latest finalized checkpoint.
    fn checkpoint<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        self.get(py, "/checkpoint/latest".to_string())
    }

    /// `GET /checkpoint/{height}` — the finalized checkpoint at `height`.
    fn checkpoint_at<'py>(&self, py: Python<'py>, height: u64) -> PyResult<Bound<'py, PyAny>> {
        self.get(py, format!("/checkpoint/{height}"))
    }

    /// `GET /api/turn/{hash}/proof` — the full-turn STARK for a committed turn,
    /// or `None` while the node's prove pool is still producing it. The proof
    /// is BYTES — verify it with the Rust/Lean `verify_full_turn`, not here.
    fn turn_proof<'py>(
        &self,
        py: Python<'py>,
        turn_hash: &str,
    ) -> PyResult<Option<Bound<'py, PyAny>>> {
        let base = self.node_url.clone();
        let url = format!(
            "{}/api/turn/{}/proof",
            base.trim_end_matches('/'),
            turn_hash.trim()
        );
        let fetched = py.detach(move || match http_agent().get(&url).call() {
            Ok(resp) => resp
                .into_json::<serde_json::Value>()
                .map(Some)
                .map_err(|e| format!("GET {url}: {e}")),
            Err(ureq::Error::Status(404, _)) => Ok(None),
            Err(e) => Err(format!("GET {url}: {e}")),
        });
        match fetched.map_err(err)? {
            Some(v) => Ok(Some(json_to_py(py, &v)?)),
            None => Ok(None),
        }
    }

    fn __repr__(&self) -> String {
        format!("AttestedQuery(node_url={:?})", self.node_url)
    }
}

/// Devnet faucet (`POST /api/faucet`): materialize a hosted cell and/or claim
/// computrons (max 10000 per request). Pass `public_key=` to install a
/// canonical hosted cell with a real owner key — REQUIRED before that cell can
/// pass Ed25519 turn authorization.
///
/// ```python
/// dregg.faucet(node_url, ident.cell_id, 2000, public_key=ident.public_key)
/// ```
#[pyfunction]
#[pyo3(signature = (node_url, recipient, amount, public_key=None, devnet_key=None))]
fn faucet<'py>(
    py: Python<'py>,
    node_url: &str,
    recipient: &Bound<'_, PyAny>,
    amount: u64,
    public_key: Option<&Bound<'_, PyAny>>,
    devnet_key: Option<&str>,
) -> PyResult<Bound<'py, PyAny>> {
    let recipient_hex = hex::encode(parse_32(recipient, "recipient")?);
    let mut body = serde_json::json!({ "recipient": recipient_hex, "amount": amount });
    if let Some(pk) = public_key {
        body["public_key"] = serde_json::Value::String(hex::encode(parse_32(pk, "public_key")?));
    }
    let base = node_url.trim_end_matches('/').to_string();
    let key = resolve_devnet_key(devnet_key);
    let v = py
        .detach(move || http_send_json("POST", &base, "/api/faucet", &body, key.as_deref()))
        .map_err(refused)?;
    json_to_py(py, &v)
}

// ─── kernel: which LOCAL EXECUTOR this module ships (pure-Rust, or the Lean kernel) ───
//
// The SDK ALWAYS has a local executor. The LIGHT (default) wheel ships the
// pure-Rust `TurnExecutor` (`dregg-turn`) — small, no `libleanshared`, at parity
// with the verified Lean spec (a dedicated lane strengthens + documents that
// Rust↔Lean parity; it is the justification for trusting the Rust producer). The
// VERIFIED Lean executor is the optional heavy `dregg[kernel]` build. Either way
// `dregg.kernel()` PROVES the active executor by running one real transfer
// through it.

/// The canonical mini-wire for the VERIFIED-Lean proof-of-execution probe: two
/// cells (1: balance 50, 2: balance 10), actor 1 transfers 5 from 1 to 2. The
/// proved `Exec.recKExec` must accept (`"ok":1`) and move the balances to 45/15.
/// The grammar is `Dregg2.Exec.FFI.parseInput`'s (the state-differential wire).
const KERNEL_PROBE_WIRE: &str = "{\"cells\":[[1,{\"rec\":[[\"balance\",{\"int\":50}]]}],\
                                 [2,{\"rec\":[[\"balance\",{\"int\":10}]]}]],\
                                 \"actor\":1,\"src\":1,\"dst\":2,\"amt\":5}";

/// Drive ONE real transfer through the pure-Rust executor (`dregg-turn`'s
/// `TurnExecutor`, via the wire-free `DreggEngine`) — the local executor the
/// LIGHT wheel ships. Two cells owned by one ephemeral key; a signed transfer of
/// 5 the executor authorizes + commits, landing the destination at 15. This is a
/// REAL execution (the Rust analog of the Lean `recKExec` probe), not a link bit.
/// Returns `(committed_and_landed, evidence_wire)`.
fn rust_executor_probe() -> Result<(bool, String), String> {
    use dregg_cell::Cell;
    use dregg_sdk::embed::{DreggEngine, EngineConfig};

    let fed = [0u8; 32];
    let clerk = AgentCipherclerk::from_seed([7u8; 64]);
    let pk = clerk.public_key().0;
    // `cell_id("default")` == derive_raw(pk, blake3("default")); fund the SAME id.
    let default_token = *blake3::hash(b"default").as_bytes();
    let dst_token = *blake3::hash(b"dregg-rust-probe-dst").as_bytes();
    let from = clerk.cell_id("default");
    let to = CellId::derive_raw(&pk, &dst_token);

    // EngineConfig::for_testing() runs federation [0;32] at timestamp 0 and height 0; the
    // deadline below is a block height, and a height-0 executor refuses every deadline, so
    // the probe runs at height 1.
    let mut engine = DreggEngine::new(EngineConfig::for_testing());
    engine.set_block_height(1);
    // Fund the source generously so the executor's fee/budget accounting cannot
    // underflow it; the DESTINATION (10 → 15) is the clean conservation witness.
    engine
        .ledger_mut()
        .insert_cell(Cell::with_balance(pk, default_token, 1_000_000))
        .map_err(|e| format!("fund src: {e:?}"))?;
    engine
        .ledger_mut()
        .insert_cell(Cell::with_balance(pk, dst_token, 10))
        .map_err(|e| format!("fund dst: {e:?}"))?;

    // Ride the SAME `build_signed_turn` the shipped `.sign()` uses — one signing
    // path in this crate, so the probe cannot certify a construction the SDK does
    // not actually ship. (This probe pinned nonce 0, the one value at which the
    // old `make_action` nonce bind was accidentally correct; it would have gone on
    // reporting a healthy executor while every real Python turn past the first was
    // refused.)
    let signed = build_signed_turn(
        &clerk,
        "default",
        "execute",
        vec![Effect::Transfer {
            from,
            to,
            amount: 5,
        }],
        None,
        Vec::new(),
        &fed,
        0,
        10_000,
        None,
        dregg_turn::valid_until_at(1, dregg_turn::DEFAULT_TURN_VALIDITY_HORIZON_BLOCKS),
    );

    engine
        .execute_turn(&signed.turn)
        .map_err(|e| format!("execute: {e:?}"))?;

    let src_bal = engine
        .ledger()
        .get(&from)
        .map(|c| c.state.balance())
        .unwrap_or(i64::MIN);
    let dst_bal = engine
        .ledger()
        .get(&to)
        .map(|c| c.state.balance())
        .unwrap_or(i64::MIN);
    let ok = dst_bal == 15;
    let out = format!(
        "{{\"executor\":\"rust\",\"cells\":[[\"src\",{src_bal}],[\"dst\",{dst_bal}]],\
         \"transferred\":5,\"ok\":{}}}",
        if ok { 1 } else { 0 }
    );
    Ok((ok, out))
}

/// Report which LOCAL EXECUTOR this module ships — and PROVE it by running one
/// real transfer through it.
///
/// Returns a dict:
///   * `"build"`            — `"light"` (the default kernel-free client wheel) or
///                            `"kernel"` (the `dregg[kernel]` heavy build).
///   * `"lean"`             — the verified Lean kernel is linked + its runtime
///                            initialized (links `libleanshared` + `libdregg_lean.a`).
///   * `"executor"`/`"producer"` — the ACTIVE local executor: `"lean"` when the
///                            verified executor is linked AND selected as producer
///                            (the SWAP default; `DREGG_LEAN_PRODUCER=0` opts out),
///                            else `"rust"` — the pure-Rust `TurnExecutor` the light
///                            client ships (at parity with the verified Lean spec).
///   * `"executor_present"` — always true: the SDK always has a local executor.
///   * `"executor_step_ok"` — a REAL execution: one transfer driven through the
///                            ACTIVE executor accepted and conserved balances.
///   * `"executor_step_out"`— the raw output wire from that execution (evidence).
///   * `"verified_step_ok"` — true ONLY when the executor that ran the step was the
///                            VERIFIED Lean executor (i.e. `executor=="lean"`); the
///                            Rust producer is at-parity, not itself the proved kernel.
#[pyfunction]
fn kernel(py: Python<'_>) -> PyResult<Bound<'_, PyDict>> {
    let d = PyDict::new(py);
    let build_mode = if cfg!(feature = "kernel") {
        "kernel"
    } else {
        "light"
    };
    d.set_item("build", build_mode)?;

    let lean = dregg_lean_ffi::lean_available();
    d.set_item("lean", lean)?;
    // The SDK ALWAYS carries a local executor: the verified Lean executor when it
    // is linked AND selected as the producer, else the pure-Rust TurnExecutor.
    let lean_producer = lean && dregg_sdk::runtime::lean_producer_env_enabled();
    let active = if lean_producer { "lean" } else { "rust" };
    d.set_item("executor", active)?;
    d.set_item("producer", active)?;
    d.set_item("executor_present", true)?;

    if lean_producer {
        // Drive the transfer through the VERIFIED Lean kernel (proved recKExec).
        match dregg_lean_ffi::shadow_record_kernel_step(KERNEL_PROBE_WIRE) {
            Ok(out) => {
                // Accept (`"ok":1`) AND the verified post-balances (45/15): a kernel
                // that answered but computed the wrong state must not read as ok.
                let ok = out.contains("\"ok\":1")
                    && out.contains("[\"balance\",{\"int\":45}]")
                    && out.contains("[\"balance\",{\"int\":15}]");
                d.set_item("verified_step_ok", ok)?;
                d.set_item("executor_step_ok", ok)?;
                d.set_item("executor_step_out", out)?;
            }
            Err(e) => {
                d.set_item("verified_step_ok", false)?;
                d.set_item("executor_step_ok", false)?;
                d.set_item("executor_step_out", format!("error: {e}"))?;
            }
        }
    } else {
        // The pure-Rust executor the LIGHT wheel ships. It is NOT itself the
        // verified-Lean step, so `verified_step_ok` is false; `executor_step_ok`
        // is the Rust executor's real commit (at parity with the verified spec).
        d.set_item("verified_step_ok", false)?;
        match rust_executor_probe() {
            Ok((ok, out)) => {
                d.set_item("executor_step_ok", ok)?;
                d.set_item("executor_step_out", out)?;
            }
            Err(e) => {
                d.set_item("executor_step_ok", false)?;
                d.set_item(
                    "executor_step_out",
                    format!("rust executor probe error: {e}"),
                )?;
            }
        }
    }
    Ok(d)
}

// ─── deploy: DreggDL, the checkable deployment spec (the REAL dregg-deploy) ───
//
// `dregg.deploy` is a thin binding over the `dregg-deploy` crate's REAL
// pipeline: `parse_toml`/`parse_json` → `Lowered::from_deployment` (name
// resolution + the ordered CallForest) → `dregg_userspace_verify::analyze`.
// No lowering, no CallForest construction, and no userspace-verify check is
// reimplemented in Python — these functions call the same `dregg_deploy`
// functions the `dregg-deploy check` CLI runs, so a deployment audited from
// Python is audited by the exact same code as from Rust.

use dregg_userspace_verify::{Assurance, Finding, Verdict};

/// Parse DreggDL surface text (TOML, or JSON when it starts with `{`/`[`) into
/// the real `Deployment`, calling the crate's own `parse_toml`/`parse_json`.
fn parse_deployment(text: &str) -> Result<dregg_deploy::Deployment, dregg_deploy::DeployError> {
    // A leading `{` is unambiguously JSON (a TOML document never starts with a
    // brace). Everything else is TOML — `[` opens a TOML table array, so it is
    // NOT treated as a JSON array. This matches the `dregg-deploy` CLI default.
    if text.trim_start().starts_with('{') {
        return dregg_deploy::parse_json(text);
    }
    dregg_deploy::parse_toml(text)
}

/// Render a `Finding` as a Python dict: `{guarantee, locus, message}`.
fn finding_to_py<'py>(py: Python<'py>, f: &Finding) -> PyResult<Bound<'py, PyDict>> {
    let d = PyDict::new(py);
    d.set_item("guarantee", &f.guarantee)?;
    d.set_item("message", &f.message)?;
    let locus = PyDict::new(py);
    locus.set_item("node_path", f.locus.node_path.clone())?;
    locus.set_item("effect_index", f.locus.effect_index)?;
    locus.set_item("asset", f.locus.asset.clone())?;
    locus.set_item("display", f.locus.to_string())?;
    d.set_item("locus", locus)?;
    Ok(d)
}

/// Render one `Verdict` (`Pass` | `Fail(findings)`) as a dict:
/// `{pass: bool, findings: [..]}`.
fn verdict_to_py<'py>(py: Python<'py>, v: &Verdict) -> PyResult<Bound<'py, PyDict>> {
    let d = PyDict::new(py);
    d.set_item("pass", v.is_pass())?;
    let findings = PyList::empty(py);
    for f in v.findings() {
        findings.append(finding_to_py(py, f)?)?;
    }
    d.set_item("findings", findings)?;
    Ok(d)
}

/// Render the four-check `Assurance` as a dict mirroring the Rust struct.
fn assurance_to_py<'py>(py: Python<'py>, a: &Assurance) -> PyResult<Bound<'py, PyDict>> {
    let d = PyDict::new(py);
    d.set_item("pass", a.pass())?;
    d.set_item("conservation", verdict_to_py(py, &a.conservation)?)?;
    d.set_item("no_amplification", verdict_to_py(py, &a.no_amplification)?)?;
    d.set_item("wellformed", verdict_to_py(py, &a.wellformed)?)?;
    d.set_item("ring_balance", verdict_to_py(py, &a.ring_balance)?)?;
    let all = PyList::empty(py);
    for f in a.all_findings() {
        all.append(finding_to_py(py, &f)?)?;
    }
    d.set_item("findings", all)?;
    Ok(d)
}

/// **`dregg.deploy.check(text, ring=False)`** — the synthesis: parse DreggDL →
/// lower to the real `CallForest` → run `dregg_userspace_verify::analyze` over
/// the whole declared authority layout → return the `DeployVerdict` as a dict.
///
/// This is exactly what `dregg-deploy check <file>` runs. Returns:
/// `{pass, assurance, factories, cells, turn_count}` where `assurance` carries
/// the four located checks (conservation, non-amplification, well-formedness,
/// ring-balance). On a parse / lowering error raises `DreggError` naming the
/// offending row (e.g. an unknown factory ref, a duplicate cell name).
///
/// `ring=True` also runs the ring-balance check (a settlement ring declared as
/// bare funding transfers must net to zero).
#[pyfunction]
#[pyo3(name = "check", signature = (text, ring=false))]
fn deploy_check<'py>(py: Python<'py>, text: &str, ring: bool) -> PyResult<Bound<'py, PyDict>> {
    let dep = parse_deployment(text).map_err(|e| err(e.to_string()))?;
    let verdict = dregg_deploy::check_deployment(&dep, ring).map_err(|e| err(e.to_string()))?;

    let d = PyDict::new(py);
    d.set_item("pass", verdict.pass())?;
    d.set_item("assurance", assurance_to_py(py, &verdict.assurance)?)?;
    d.set_item("turn_count", verdict.turn_count)?;

    let factories = PyList::empty(py);
    for (name, vk) in &verdict.factories {
        let row = PyDict::new(py);
        row.set_item("ref", name)?;
        row.set_item("factory_vk", vk)?;
        factories.append(row)?;
    }
    d.set_item("factories", factories)?;

    let cells = PyList::empty(py);
    for (name, id) in &verdict.cells {
        let row = PyDict::new(py);
        row.set_item("name", name)?;
        row.set_item("cell_id", id)?;
        cells.append(row)?;
    }
    d.set_item("cells", cells)?;

    Ok(d)
}

/// **`dregg.deploy.lower(text)`** — run only the real
/// `Lowered::from_deployment` lowering (no check) and return the resolved
/// artifact: `{forest, federation_id, factories, cells}`, where `forest` is the
/// ordered `CallForest` (births → funds → grants) the checker consumes, as JSON.
///
/// This is `dregg-deploy lower <file>` — the same lowering the SDK replays
/// through its own turn builders.
#[pyfunction]
#[pyo3(name = "lower")]
fn deploy_lower<'py>(py: Python<'py>, text: &str) -> PyResult<Bound<'py, PyAny>> {
    let dep = parse_deployment(text).map_err(|e| err(e.to_string()))?;
    let lowered = dregg_deploy::Lowered::from_deployment(&dep).map_err(|e| err(e.to_string()))?;

    let forest_json =
        serde_json::to_value(&lowered.forest).map_err(|e| err(format!("encode forest: {e}")))?;

    let d = PyDict::new(py);
    d.set_item("forest", json_to_py(py, &forest_json)?)?;
    d.set_item("federation_id", hex::encode(lowered.federation_id.0))?;

    let factories = PyList::empty(py);
    for (name, vk) in &lowered.factory_vks {
        let row = PyDict::new(py);
        row.set_item("ref", name)?;
        row.set_item("factory_vk", hex::encode(vk))?;
        factories.append(row)?;
    }
    d.set_item("factories", factories)?;

    let cells = PyList::empty(py);
    for (name, id) in &lowered.cell_ids {
        let row = PyDict::new(py);
        row.set_item("name", name)?;
        row.set_item("cell_id", hex::encode(id.0))?;
        cells.append(row)?;
    }
    d.set_item("cells", cells)?;

    Ok(d.into_any())
}

// ─── service economy (in-process, executor-backed) ───
//
// The Python face of the Rust SDK facade (`sdk/src/service_economy.rs`). Unlike
// the wire `Identity → turn(node) → submit` flow, these bindings FORWARD to the
// real in-process `dregg_sdk::AgentRuntime` + `ExecutionLease` — the genuine
// verified kernel executor — so `pay`/`lease` produce REAL committed
// `TurnReceipt`s and `invoke_service` returns the REAL verified desugar. No
// faking: every method is a thin forward to the now-existing Rust core.

/// `Effect` → a small Python dict (`kind` + the load-bearing fields).
fn effect_to_py<'py>(py: Python<'py>, e: &Effect) -> PyResult<Bound<'py, PyDict>> {
    let d = PyDict::new(py);
    match e {
        Effect::Transfer { from, to, amount } => {
            d.set_item("kind", "transfer")?;
            d.set_item("from", hex::encode(from.0))?;
            d.set_item("to", hex::encode(to.0))?;
            d.set_item("amount", *amount)?;
        }
        Effect::SetField { cell, index, value } => {
            d.set_item("kind", "set_field")?;
            d.set_item("cell", hex::encode(cell.0))?;
            d.set_item("index", *index)?;
            d.set_item("value", hex::encode(value))?;
        }
        other => {
            d.set_item("kind", "other")?;
            d.set_item("repr", format!("{other:?}"))?;
        }
    }
    Ok(d)
}

/// `Action` → a Python dict mirroring the TS `action()` shape
/// (`target`/`method`/`args`/`effects`, all hex).
fn action_to_py<'py>(py: Python<'py>, a: &Action) -> PyResult<Bound<'py, PyDict>> {
    let d = PyDict::new(py);
    d.set_item("target", hex::encode(a.target.0))?;
    d.set_item("method", hex::encode(a.method))?;
    let args = PyList::empty(py);
    for arg in &a.args {
        args.append(hex::encode(arg))?;
    }
    d.set_item("args", args)?;
    let effects = PyList::empty(py);
    for e in &a.effects {
        effects.append(effect_to_py(py, e)?)?;
    }
    d.set_item("effects", effects)?;
    Ok(d)
}

/// The `method`/`topic` symbol a name hashes to (`blake3(name)`), hex — the same
/// `dregg_cell::method_symbol` the executor routes on. Handy for asserting the
/// desugar's `method` field.
#[pyfunction]
#[pyo3(name = "method_symbol")]
fn method_symbol_py(name: &str) -> String {
    hex::encode(method_symbol(name))
}

/// A small receipt view over an in-process `TurnReceipt`.
#[pyclass(module = "dregg", name = "TxReceipt")]
struct TxReceipt {
    #[pyo3(get)]
    turn_hash: String,
    #[pyo3(get)]
    receipt_hash: String,
    #[pyo3(get)]
    post_state: String,
    #[pyo3(get)]
    computrons_used: u64,
    #[pyo3(get)]
    action_count: usize,
}

impl TxReceipt {
    fn from_receipt(r: &TurnReceipt) -> Self {
        TxReceipt {
            turn_hash: hex::encode(r.turn_hash),
            receipt_hash: hex::encode(r.receipt_hash()),
            post_state: hex::encode(r.post_state_hash),
            computrons_used: r.computrons_used,
            action_count: r.action_count,
        }
    }
}

#[pymethods]
impl TxReceipt {
    fn __repr__(&self) -> String {
        format!(
            "TxReceipt(turn_hash={:?}, computrons_used={})",
            self.turn_hash, self.computrons_used
        )
    }
}

/// A funded sub-agent worker (a payee or a lease funder) spawned by a
/// [`ServiceRuntime`]. Wraps a real `dregg_sdk::SubAgent`.
#[pyclass(unsendable, module = "dregg", name = "Worker")]
struct Worker {
    inner: SubAgent,
}

#[pymethods]
impl Worker {
    /// Hex cell id of this worker.
    #[getter]
    fn cell_id(&self) -> String {
        hex::encode(self.inner.cell_id().0)
    }

    fn __repr__(&self) -> String {
        format!("Worker(cell_id={:?})", self.cell_id())
    }
}

/// **A durable, metered execution lease** — the Python face of
/// `dregg_sdk::ExecutionLease`. `run` advances the durable checkpoint
/// (`step → step+1`) metered through the cap-gated worker on one turn; `fund`
/// moves value in with a conserving Transfer. The `FieldLte { step ≤ max_steps }
/// ∧ Monotonic { step }` meter is enforced by the REAL executor: a run past the
/// ceiling raises `DreggRefused`.
#[pyclass(unsendable, module = "dregg", name = "Lease")]
struct Lease {
    inner: ExecutionLease,
}

#[pymethods]
impl Lease {
    /// Hex id of the lease cell (carrying the checkpoint slot + meter program).
    #[getter]
    fn lease_cell(&self) -> String {
        hex::encode(self.inner.lease_cell().0)
    }

    /// Hex asset id the lease holds value in.
    #[getter]
    fn asset(&self) -> String {
        hex::encode(self.inner.asset())
    }

    /// The durable checkpoint index so far.
    #[getter]
    fn step(&self) -> i64 {
        self.inner.step()
    }

    /// The runs remaining (`max_steps - step`).
    #[getter]
    fn remaining(&self) -> i64 {
        self.inner.remaining()
    }

    /// Fund the lease — one conserving Transfer of `amount` from `funder` into
    /// the lease cell.
    fn fund(&self, funder: &Worker, amount: u64) -> PyResult<TxReceipt> {
        let r = self
            .inner
            .fund(&funder.inner, amount)
            .map_err(|e| refused(e.to_string()))?;
        Ok(TxReceipt::from_receipt(&r))
    }

    /// Advance the durable checkpoint (`step → step+1`), metered through the
    /// cap-gated worker. Raises `DreggRefused` when a run would exceed the
    /// capacity ceiling (the executor's `FieldLte` meter tooth).
    fn run(&mut self) -> PyResult<TxReceipt> {
        let step = self
            .inner
            .run(Vec::new())
            .map_err(|e| refused(e.to_string()))?;
        Ok(TxReceipt::from_receipt(&step.receipt))
    }

    fn __repr__(&self) -> String {
        format!(
            "Lease(lease_cell={:?}, step={}, remaining={})",
            self.lease_cell(),
            self.step(),
            self.remaining()
        )
    }
}

/// **An in-process service-economy runtime** — a real `dregg_sdk::AgentRuntime`
/// over the verified kernel executor, exposing the few-lines facade: `pay`,
/// `invoke_service`, and a durable, metered `lease`. The agent cell is
/// self-funded (1M computrons) for local use.
#[pyclass(unsendable, module = "dregg", name = "ServiceRuntime")]
struct ServiceRuntime {
    runtime: SdkRuntime,
    root: HeldToken,
    domain: String,
}

impl ServiceRuntime {
    /// Shared parse for the invoke surface: the arg field-elements, the optional
    /// `(provider, amount, asset)` pay leg, and the caller authority.
    fn parse_invoke(
        &self,
        args: Option<&Bound<'_, PyAny>>,
        pay: Option<&Bound<'_, PyAny>>,
        authority: &str,
    ) -> PyResult<(Vec<FieldElement>, Option<PayLeg>, InvokeAuthority)> {
        let mut arg_felts: Vec<FieldElement> = Vec::new();
        if let Some(args) = args {
            for item in args.try_iter()? {
                arg_felts.push(parse_32(&item?, "args[]")?);
            }
        }

        let pay_leg = match pay {
            None => None,
            Some(p) => {
                let (prov, amt, asset): (Bound<'_, PyAny>, u64, Bound<'_, PyAny>) =
                    p.extract().map_err(|_| {
                        PyTypeError::new_err("pay: expected a (provider, amount, asset) tuple")
                    })?;
                Some(PayLeg::new(
                    parse_cell(&prov, "pay.provider")?,
                    amt,
                    parse_32(&asset, "pay.asset")?,
                ))
            }
        };

        let authority = match authority.to_ascii_lowercase().as_str() {
            "none" => InvokeAuthority::None,
            "signature" => InvokeAuthority::Signature,
            "proof" => InvokeAuthority::Proof,
            other => {
                return Err(PyValueError::new_err(format!(
                    "authority: expected one of none/signature/proof, got {other:?}"
                )));
            }
        };

        Ok((arg_felts, pay_leg, authority))
    }
}

#[pymethods]
impl ServiceRuntime {
    /// A fresh in-process runtime (real cipherclerk + ledger + executor) in
    /// `domain` (the asset namespace; the agent's value is denominated in
    /// `blake3(domain)`).
    #[new]
    #[pyo3(signature = (domain="compute"))]
    fn new(domain: &str) -> PyResult<Self> {
        let mut clerk = AgentCipherclerk::new();
        let root = clerk.mint_token(&[7u8; 32], domain);
        let runtime = SdkRuntime::new(Arc::new(RwLock::new(clerk)), domain);
        Ok(ServiceRuntime {
            runtime,
            root,
            domain: domain.to_string(),
        })
    }

    /// Hex cell id of this runtime's agent cell (the payer / caller).
    #[getter]
    fn cell_id(&self) -> String {
        hex::encode(self.runtime.cell_id().0)
    }

    /// Hex id of this runtime's native asset (its agent cell's `token_id`).
    #[getter]
    fn native_asset(&self) -> String {
        hex::encode(self.runtime.native_asset())
    }

    /// The balance of `cell` in the ledger (0 for an unknown cell).
    fn balance(&self, cell: &Bound<'_, PyAny>) -> PyResult<i64> {
        let cell = parse_cell(cell, "cell")?;
        let ledger = self.runtime.ledger().lock().unwrap();
        Ok(ledger.get(&cell).map(|c| c.state.balance()).unwrap_or(0))
    }

    /// Spawn a funded sub-agent worker (a payee or a lease funder) in this
    /// runtime's domain, sharing the domain asset.
    fn spawn(&self) -> PyResult<Worker> {
        let w = self
            .runtime
            .spawn_sub_agent(&Attenuation::default(), &self.root)
            .map_err(|e| refused(e.to_string()))?;
        Ok(Worker { inner: w })
    }

    /// Install a service cell whose program dispatches `methods` (its derived
    /// interface exposes them, all Replayable), in this runtime's asset. Returns
    /// the cell id (hex). When `owned` is true the cell is owned by THIS runtime's
    /// key (in a distinct asset, so its id differs from the agent cell) —
    /// required for the submitting `invoke_service`, whose signature the executor
    /// verifies against the target's owner. A provisioning helper.
    #[pyo3(signature = (methods, owned=false))]
    fn install_service_cell(&self, methods: Vec<String>, owned: bool) -> PyResult<String> {
        let cases = methods
            .iter()
            .map(|m| TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: method_symbol(m),
                },
                constraints: Vec::new(),
            })
            .collect();
        let (pk, token) = if owned {
            let pk = self
                .runtime
                .cipherclerk()
                .read()
                .unwrap_or_else(|e| e.into_inner())
                .public_key();
            (
                pk.0,
                *blake3::hash(format!("{}:svc", self.domain).as_bytes()).as_bytes(),
            )
        } else {
            ([5u8; 32], *blake3::hash(self.domain.as_bytes()).as_bytes())
        };
        let mut cell = Cell::with_balance(pk, token, 0);
        cell.program = CellProgram::Cases(cases);
        let id = cell.id();
        let _ = self.runtime.ledger().lock().unwrap().insert_cell(cell);
        Ok(hex::encode(id.0))
    }

    /// **`pay`** — move `amount` of `asset` from this runtime's cell to `to`
    /// through the canonical `Payable` `pay` desugar (one conserving Transfer,
    /// per-asset Σδ=0). Forwards to `AgentRuntime::pay`. `asset` defaults to the
    /// native asset (an intra-domain payment).
    #[pyo3(signature = (to, amount, asset=None))]
    fn pay(
        &self,
        to: &Bound<'_, PyAny>,
        amount: u64,
        asset: Option<&Bound<'_, PyAny>>,
    ) -> PyResult<TxReceipt> {
        let to = parse_cell(to, "to")?;
        let receipt = match asset {
            Some(a) => {
                let a = parse_32(a, "asset")?;
                self.runtime.pay(to, amount, a)
            }
            None => self.runtime.pay_native(to, amount),
        }
        .map_err(|e| refused(e.to_string()))?;
        Ok(TxReceipt::from_receipt(&receipt))
    }

    /// **`resolve_invoke`** — route `method` against `target`'s interface through
    /// the verified DFA router, optionally PREPENDING the canonical `Payable`
    /// pay leg, and return the verified DESUGAR (the `Action` the executor would
    /// run) as a dict (`target`/`method`/`args`/`effects`) WITHOUT submitting.
    /// Forwards to `AgentRuntime::invoke_service_resolved` (the pure core). Fail-
    /// closed: an unknown method, a serviced seam, or an under-authority call
    /// raises `DreggRefused`.
    ///
    /// `pay` is a `(provider, amount, asset)` tuple; `authority` is one of
    /// `none`/`signature`/`proof`.
    #[pyo3(signature = (target, method, args=None, pay=None, authority="none"))]
    fn resolve_invoke<'py>(
        &self,
        py: Python<'py>,
        target: &Bound<'_, PyAny>,
        method: &str,
        args: Option<&Bound<'_, PyAny>>,
        pay: Option<&Bound<'_, PyAny>>,
        authority: &str,
    ) -> PyResult<Bound<'py, PyDict>> {
        let target = parse_cell(target, "target")?;
        let (arg_felts, pay_leg, authority) = self.parse_invoke(args, pay, authority)?;
        let (action, _sig) = self
            .runtime
            .invoke_service_resolved(target, method, arg_felts, Vec::new(), authority, pay_leg)
            .map_err(|e| refused(e.to_string()))?;
        action_to_py(py, &action)
    }

    /// **`invoke_service`** — route `method` against `target` (optionally
    /// prepending the canonical pay leg), SIGN it, and SUBMIT it to the
    /// in-process executor, returning the committed `TxReceipt`. Forwards to
    /// `AgentRuntime::invoke_service`. The executor verifies this runtime's
    /// signature against `target`'s owner, so it commits for a target this
    /// runtime administers (e.g. `install_service_cell(..., owned=True)`). Use
    /// `resolve_invoke` to inspect the desugar without submitting. Fail-closed:
    /// an unknown method / serviced seam / under-authority / executor refusal
    /// raises `DreggRefused`.
    #[pyo3(signature = (target, method, args=None, pay=None, authority="none"))]
    fn invoke_service(
        &self,
        target: &Bound<'_, PyAny>,
        method: &str,
        args: Option<&Bound<'_, PyAny>>,
        pay: Option<&Bound<'_, PyAny>>,
        authority: &str,
    ) -> PyResult<TxReceipt> {
        let target = parse_cell(target, "target")?;
        let (arg_felts, pay_leg, authority) = self.parse_invoke(args, pay, authority)?;
        let receipt = self
            .runtime
            .invoke_service(target, method, arg_felts, Vec::new(), authority, pay_leg)
            .map_err(|e| refused(e.to_string()))?;
        Ok(TxReceipt::from_receipt(&receipt))
    }

    /// **`lease`** — open a durable, metered execution lease admitting
    /// `max_steps` checkpoints. Forwards to `ExecutionLease::open` (spawns a
    /// cap-gated worker scoped to the run verb + installs the
    /// `FieldLte ∧ Monotonic` meter program on the lease cell).
    fn lease(&self, max_steps: i64) -> PyResult<Lease> {
        let inner = ExecutionLease::open(&self.runtime, &self.root, LeaseTerms::new(max_steps))
            .map_err(|e| refused(e.to_string()))?;
        Ok(Lease { inner })
    }

    fn __repr__(&self) -> String {
        format!(
            "ServiceRuntime(cell_id={:?}, domain={:?})",
            self.cell_id(),
            self.domain
        )
    }
}

// ─── tokens & presentations (the macaroon-backed authorization surface) ───

/// A held authorization token (the Rust `HeldToken`): macaroon-backed,
/// attenuable (narrowing only), presentable via [`Identity::authorize`].
#[pyclass(unsendable, module = "dregg", name = "Token")]
struct Token {
    inner: HeldToken,
}

#[pymethods]
impl Token {
    /// Human-readable label.
    #[getter]
    fn label(&self) -> String {
        self.inner.label().to_string()
    }

    /// The service this token grants access to.
    #[getter]
    fn service(&self) -> String {
        self.inner.service().to_string()
    }

    /// Unique local id (used by the clerk's revocation bookkeeping).
    #[getter]
    fn id(&self) -> String {
        self.inner.id().to_string()
    }

    /// The encoded token string (`em2_`-prefixed) — the portable form.
    #[getter]
    fn encoded(&self) -> String {
        self.inner.encoded().to_string()
    }

    fn __repr__(&self) -> String {
        format!(
            "Token(label={:?}, service={:?})",
            self.inner.label(),
            self.inner.service()
        )
    }
}

/// `dregg_trace::Term` → Python (hex str for symbols, int for integers).
fn term_to_py<'py>(py: Python<'py>, t: &dregg_trace::Term) -> PyResult<Bound<'py, PyAny>> {
    Ok(match t {
        dregg_trace::Term::Const(sym) => hex::encode(sym).into_pyobject(py)?.into_any(),
        dregg_trace::Term::Int(i) => i.into_pyobject(py)?.into_any(),
        // Facts are ground; a Var here would be a core invariant violation —
        // surface it visibly rather than silently rendering something.
        dregg_trace::Term::Var(v) => format!("var:{v}").into_pyobject(py)?.into_any(),
    })
}

/// An authorization presentation (the Rust `AuthorizationPresentation`) —
/// what a prover hands a verifier. Postcard-portable via
/// `to_bytes`/`from_bytes`.
#[pyclass(unsendable, module = "dregg", name = "Presentation")]
struct Presentation {
    inner: AuthorizationPresentation,
}

#[pymethods]
impl Presentation {
    /// `"trusted"` / `"selective"` / `"private"` — which Rust variant this is.
    #[getter]
    fn kind(&self) -> &'static str {
        match &self.inner {
            AuthorizationPresentation::Trusted { .. } => "trusted",
            AuthorizationPresentation::Selective { .. } => "selective",
            AuthorizationPresentation::Private { .. } => "private",
        }
    }

    /// Whether authorization was granted.
    ///
    /// SECURITY: for `"selective"`/`"private"` this is the PROVER's
    /// self-reported field (UX only — the Rust type says the same); a
    /// verifier must rely on proof verification, never this flag. For
    /// `"trusted"` it is the local Datalog conclusion.
    #[getter]
    fn conclusion(&self) -> bool {
        match &self.inner {
            AuthorizationPresentation::Trusted { trace, .. } => {
                matches!(trace.conclusion, dregg_trace::Conclusion::Allow { .. })
            }
            AuthorizationPresentation::Selective { conclusion, .. }
            | AuthorizationPresentation::Private { conclusion, .. } => *conclusion,
        }
    }

    /// The revealed facts of a `"selective"` presentation as dicts
    /// (`predicate` hex + `terms` list); `None` for other kinds.
    #[getter]
    fn revealed_facts<'py>(&self, py: Python<'py>) -> PyResult<Option<Bound<'py, PyList>>> {
        let AuthorizationPresentation::Selective { revealed_facts, .. } = &self.inner else {
            return Ok(None);
        };
        let out = PyList::empty(py);
        for fact in revealed_facts {
            let d = PyDict::new(py);
            d.set_item("predicate", hex::encode(fact.predicate))?;
            let terms = PyList::empty(py);
            for t in &fact.terms {
                terms.append(term_to_py(py, t)?)?;
            }
            d.set_item("terms", terms)?;
            out.append(d)?;
        }
        Ok(Some(out))
    }

    /// Canonical wire bytes (postcard `AuthorizationPresentation`).
    fn to_bytes<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyBytes>> {
        let bytes = postcard::to_stdvec(&self.inner)
            .map_err(|e| err(format!("failed to encode presentation: {e}")))?;
        Ok(PyBytes::new(py, &bytes))
    }

    /// Decode a presentation from its postcard wire bytes (fail-closed).
    #[staticmethod]
    fn from_bytes(data: &[u8]) -> PyResult<Presentation> {
        let inner: AuthorizationPresentation = postcard::from_bytes(data)
            .map_err(|e| refused(format!("presentation bytes do not decode: {e}")))?;
        Ok(Presentation { inner })
    }

    fn __repr__(&self) -> String {
        format!(
            "Presentation(kind={:?}, conclusion={})",
            self.kind(),
            self.conclusion()
        )
    }
}

/// Verify the revealed-facts half of a `"selective"` presentation — the exact
/// Rust `dregg_sdk::verify::verify_disclosure_presentation`, fail-closed:
/// `True` iff the Poseidon2 revealed-facts commitment matches the plaintext
/// revealed facts AND the presentation carries no predicate proofs (which
/// cannot be checked without trusted state). Any other kind → `False`.
/// It does NOT verify the STARK proof itself (that check is
/// `verify_authorization_proof`, which needs the federation root — unbound
/// here; see the named gaps in the module docs).
#[pyfunction]
fn verify_disclosure_presentation(presentation: &Presentation) -> bool {
    dregg_sdk::verify::verify_disclosure_presentation(&presentation.inner)
}

// ─── lightclient: the whole-history light-client verify ───

/// Verify a whole-history aggregate ENVELOPE (`WholeChainProofBytes`
/// postcard bytes) against the caller-held VK trust anchor (hex str or 32
/// bytes — the `RecursionVk` fingerprint pinned from configuration, NEVER
/// from the artifact). On success returns the attestation dict:
/// `{"genesis_root": [8 ints], "final_root": [8 ints],
///   "chain_digest": [8 ints], "num_turns": int}` — the Rust
/// `AttestedHistory`. Raises `DreggRefused` (fail-closed) on a malformed or
/// wrong-version envelope, a VK mismatch, or a failing STARK verify.
/// Forwards to `dregg_lightclient::verify_history_bytes`; cost is
/// independent of history length.
#[pyfunction]
#[pyo3(name = "verify_history")]
fn lightclient_verify_history<'py>(
    py: Python<'py>,
    envelope_bytes: &[u8],
    expected_vk: &Bound<'_, PyAny>,
) -> PyResult<Bound<'py, PyDict>> {
    let vk =
        dregg_circuit_prove::ivc_turn_chain::RecursionVk(parse_32(expected_vk, "expected_vk")?);
    let envelope = envelope_bytes.to_vec();
    let attested = py
        .detach(move || dregg_lightclient::verify_history_bytes(&envelope, &vk))
        .map_err(|e| refused(e.to_string()))?;
    let d = PyDict::new(py);
    d.set_item(
        "genesis_root",
        attested
            .genesis_root
            .iter()
            .map(|b| b.as_u32())
            .collect::<Vec<u32>>(),
    )?;
    d.set_item(
        "final_root",
        attested
            .final_root
            .iter()
            .map(|b| b.as_u32())
            .collect::<Vec<u32>>(),
    )?;
    d.set_item(
        "chain_digest",
        attested
            .chain_digest
            .iter()
            .map(|b| b.as_u32())
            .collect::<Vec<u32>>(),
    )?;
    d.set_item("num_turns", attested.num_turns)?;
    Ok(d)
}

// ─── module ───

#[pymodule]
fn dregg(py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    // Embedded-cdylib Lean runtime init: perform the one-time C-embedding ritual
    // (`lean_initialize_runtime_module` + the Dregg2 module initializers +
    // `lean_io_mark_end_initialization`, via the ffi crate's `dregg_ffi_init` under a
    // OnceLock) NOW, at `import dregg` on the importing thread — not lazily from
    // whichever thread first touches a verified path. A build without the kernel (or a
    // failed init) leaves the module importable; `kernel()` then reports the fallback.
    let _ = dregg_lean_ffi::lean_available();
    m.add_class::<Identity>()?;
    m.add_class::<TurnBuilder>()?;
    m.add_class::<AuthorizedTurn>()?;
    m.add_class::<Receipt>()?;
    m.add_class::<ReceiptStream>()?;
    m.add_class::<Trustline>()?;
    m.add_class::<Channels>()?;
    m.add_class::<Mailbox>()?;
    m.add_class::<AttestedQuery>()?;
    m.add_class::<SseJsonStream>()?;
    // The service-economy surface (in-process, executor-backed).
    m.add_class::<ServiceRuntime>()?;
    m.add_class::<Worker>()?;
    m.add_class::<Lease>()?;
    m.add_class::<TxReceipt>()?;
    // The token / presentation surface.
    m.add_class::<Token>()?;
    m.add_class::<Presentation>()?;
    m.add_function(wrap_pyfunction!(verify_disclosure_presentation, m)?)?;
    m.add_function(wrap_pyfunction!(method_symbol_py, m)?)?;
    m.add_function(wrap_pyfunction!(subscribe, m)?)?;
    m.add_function(wrap_pyfunction!(faucet, m)?)?;
    m.add_function(wrap_pyfunction!(explain, m)?)?;
    m.add_function(wrap_pyfunction!(list_profiles, m)?)?;
    m.add_function(wrap_pyfunction!(kernel, m)?)?;
    m.add("DreggError", py.get_type::<DreggError>())?;
    m.add("DreggRefused", py.get_type::<DreggRefused>())?;

    // dregg.program — the constraint-language atoms.
    let program = PyModule::new(py, "program")?;
    program.add_class::<PyConstraint>()?;
    program.add_function(wrap_pyfunction!(sender_is, &program)?)?;
    program.add_function(wrap_pyfunction!(sender_in_slot, &program)?)?;
    program.add_function(wrap_pyfunction!(balance_gte, &program)?)?;
    program.add_function(wrap_pyfunction!(balance_lte, &program)?)?;
    program.add_function(wrap_pyfunction!(preimage_gate, &program)?)?;
    program.add_function(wrap_pyfunction!(immutable, &program)?)?;
    program.add_function(wrap_pyfunction!(write_once, &program)?)?;
    program.add_function(wrap_pyfunction!(any_of, &program)?)?;
    program.add_function(wrap_pyfunction!(descriptor, &program)?)?;
    m.add_submodule(&program)?;
    // Make `import dregg.program` / `from dregg import program` resolve.
    py.import("sys")?
        .getattr("modules")?
        .set_item("dregg.program", &program)?;

    // dregg.deploy — DreggDL, the checkable deployment spec (the REAL
    // dregg-deploy parse → lower → userspace-verify pipeline).
    let deploy = PyModule::new(py, "deploy")?;
    deploy.add_function(wrap_pyfunction!(deploy_check, &deploy)?)?;
    deploy.add_function(wrap_pyfunction!(deploy_lower, &deploy)?)?;
    m.add_submodule(&deploy)?;
    py.import("sys")?
        .getattr("modules")?
        .set_item("dregg.deploy", &deploy)?;

    // dregg.lightclient — the whole-history light-client verify (bytes-level).
    let lightclient = PyModule::new(py, "lightclient")?;
    lightclient.add_function(wrap_pyfunction!(lightclient_verify_history, &lightclient)?)?;
    m.add_submodule(&lightclient)?;
    py.import("sys")?
        .getattr("modules")?
        .set_item("dregg.lightclient", &lightclient)?;

    Ok(())
}
