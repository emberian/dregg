//! **The authentic leg, run for real — vendored TLSNotary, live-local MPC-TLS.**
//!
//! Where [`dregg_zkoracle_prove::authentic`] MODELS the shape a verified `tlsn` presentation takes, THIS
//! module runs the genuine thing against an **Anthropic-shaped** endpoint: a real [`tlsn`]
//! Prover + a real local Notary perform the **MPC-TLS 2PC** handshake against a test HTTPS
//! server, the Prover **`POST`s `/v1/messages`** and **selectively discloses** the response
//! body while HIDING the `x-api-key` secret, the Notary signs a real `Attestation`, the
//! Prover builds a real `Presentation`, and `presentation.verify()` yields a real
//! `PresentationOutput`. The authenticated response body then drives the well-formed (CFG)
//! and injection-free legs unchanged.
//!
//! Gated behind the `tlsn-live` cargo feature (the heavy `mpz` 2PC + tokio + rustls
//! backend). Self-contained: server, Notary, and Prover all run in-process over
//! `tokio::io::duplex` — no external notary binary, no network. This is the exact
//! generalization of `deco-prove/src/tlsn_live.rs` (proven live-local for Stripe) with the
//! method flipped `GET`→`POST`, `Authorization`→`x-api-key`, and the response shaped as an
//! Anthropic messages object.
//!
//! ## What is REAL here vs the operational live-Anthropic remainder
//!
//! - **REAL:** the vendored tlsn stack, the MPC-TLS 2PC session (the Notary co-derives
//!   session keys and sees no plaintext), the signed `Attestation`, selective disclosure
//!   (x-api-key hidden), the `Presentation`, `presentation.verify()`, and the extracted
//!   body driving the CFG + injection legs. A tampered `Presentation` fails the real
//!   `verify()`.
//! - **Operational remainder (a deploy step, NOT built here):** pointing the Prover at the
//!   live `api.anthropic.com` (a real Anthropic TLS session with a real key, and a
//!   deployed/pinned notary). The machinery below is exactly that path with the server
//!   swapped: the local test server presents the `tlsn-server-fixture` cert
//!   (`test-server.io`), so the server pin here is that domain; live-Anthropic pins
//!   [`dregg_zkoracle_prove::authentic::ANTHROPIC_SERVER_NAME`] (`api.anthropic.com`).

use std::future::IntoFuture;
use std::sync::Arc;

use anyhow::{Context, Result, anyhow};
use futures::io::{AsyncReadExt as _, AsyncWriteExt as _};
use http_body_util::{BodyExt, Full};
use hyper::body::Bytes;
use hyper::{Request, Response, StatusCode};
use hyper_util::rt::TokioIo;
use tokio_util::compat::{FuturesAsyncReadCompatExt, TokioAsyncReadCompatExt};

use tlsn::{
    Session,
    attestation::{
        Attestation, AttestationConfig, CryptoProvider,
        presentation::{Presentation, PresentationOutput},
        request::{Request as AttestationRequest, RequestConfig},
        signing::{Secp256k1Signer, VerifyingKey},
    },
    config::{
        prove::ProveConfig, prover::ProverConfig, tls::TlsClientConfig,
        tls_commit::mpc::MpcTlsConfig, verifier::VerifierConfig,
    },
    connection::{CertBinding, ConnectionInfo, HandshakeData, ServerName, TranscriptLength},
    prover::ProverOutput,
    transcript::{ContentType, TranscriptCommitConfig},
    verifier::{ServerCertVerifier, VerifierCommitStart, VerifierOutput},
    webpki::{CertificateDer, RootCertStore},
};
use tlsn_formats::http::{DefaultHttpCommitter, HttpCommit, HttpTranscript};
use tlsn_server_fixture_certs::{CA_CERT_DER, SERVER_CERT_DER, SERVER_DOMAIN, SERVER_KEY_DER};

/// The `x-api-key` value the caller sends — a secret that MUST be redacted (never
/// authenticated) in the presentation. An obvious placeholder so no real-key shape lands
/// in the tree; the redaction is identical regardless of the token's contents.
const API_KEY_SECRET: &str = "sk-ant-MERCHANT-API-KEY-PLACEHOLDER";

// MPC-TLS preprocessing bounds (mirror `crates/examples`): the amount of data the 2PC
// preprocesses. The messages request/response are under these.
const MAX_SENT_DATA: usize = 1 << 12;
const MAX_RECV_DATA: usize = 1 << 14;

/// **The process-wide MPC-TLS session lock — a REAL constraint, not a test crutch.**
///
/// Each `*_roundtrip_blocking` below stands up its OWN `new_multi_thread` tokio runtime (default
/// worker count = `available_parallelism()`) and drives the `mpz` 2PC garbling stack, whose crates
/// in turn pull `rayon 1.12` — i.e. a **process-global**, fixed-size pool. So N concurrent sessions
/// in one process are N × cores tokio workers contending for that one pool, on top of N in-process
/// notary + server + prover triples.
///
/// MEASURED on persvati (24 cores, Linux, debug, 2026-07-27), `tests/tlsn_live_roundtrip.rs`:
///
/// | how it was run                        | outcome                                    |
/// |---------------------------------------|--------------------------------------------|
/// | `--test-threads=1` (all 3)            | 3 passed in **2.34 s**                     |
/// | one roundtrip alone (`--exact`)       | 1 passed in **0.70 s**                     |
/// | `--test-threads=4` (all 3)            | 2 pass, the third **NEVER RETURNS** (killed at 420 s) |
///
/// It is a genuine deadlock, not slowness: the box goes idle, and 420 s is two orders of
/// magnitude past the 2.34 s the same three tests take back to back. The defect is inside the
/// git-pinned TLSNotary/`mpz` stack, not here — but what INVITES it is here: one `#[test]` per
/// roundtrip in one binary, which libtest runs on parallel threads by default. This lock makes
/// "one MPC-TLS session at a time per process" structural instead of a property each caller has to
/// remember — the same shape `servo-render`'s `swgl_context::GL_LOCK` uses for the process-global
/// SWGL current-context pointer.
///
/// ⚠ HONEST LIMIT: this pins WHICH configurations deadlock, not WHICH lock deadlocks.
/// Serializing is therefore the containment that the measurements support, not a repair of the
/// vendored stack. Do not delete it on the grounds that "the tests pass now"; they pass BECAUSE
/// of it, and the `--test-threads=4` row above is the falsifier.
///
/// ── 2026-07-27, DURING THE CRATE SPLIT: A STACK WAS FINALLY CAPTURED, and it says two things.
/// `tests/model_provenance_fused.rs` wedged at `--test-threads=4` (macOS, 20+ min, 0:11 CPU —
/// parked, not working). `sample(1)` on the three live test threads:
///
/// | thread                                            | frames                                    |
/// |---------------------------------------------------|-------------------------------------------|
/// | `spliced_evidence_is_refused_even_with_a_real_live_leg` | `with_mpc_tls_session` → `prove_messages_presentation` → `mpz` → `rayon_core` → `crossbeam_utils::sync::Parker::park` |
/// | `stark_injection_leg_is_attached_…`               | `with_mpc_tls_session` → `Mutex` → `__psynch_mutexwait` |
/// | `tampered_real_presentation_is_refused_by_real_crypto` | `with_mpc_tls_session` → `Mutex` → `__psynch_mutexwait` |
///
/// 1. **THIS LOCK IS SOUND.** Exactly ONE thread is past it; the other two are queued on the
///    mutex with no `rayon`/`prove_messages_presentation` frames at all. The serialization does
///    what it claims — the earlier "N concurrent sessions" hypothesis is not what is firing.
/// 2. **THE RESIDUAL IS A SINGLE WEDGED SESSION**, inside the PROVER half
///    (`prove_messages_presentation`), parked under `rayon_core`. So one 2PC session can hang on
///    its own, and serializing cannot fix that — it only stops it taking siblings down. Which
///    means `--test-threads=4` is FLAKY, not fixed: the same binary passed 6/6 in 6.30 s earlier
///    the same day and wedged on the next run. At `--test-threads=1` the whole live suite is
///    green (6.24 s / 3.11 s / 0.01 s, measured after the split).
///
/// The next step for the owning lane is inside `mpz`/`rayon`, not here. `.config/nextest.toml`
/// bounds the blast radius by package name and NOW NAMES `dregg-zkoracle-live` as well as
/// `dregg-zkoracle-prove` — a bound that silently stopped covering these binaries when they
/// moved would have been a deleted gate wearing a rename.
static MPC_TLS_SESSION_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// Run one whole MPC-TLS roundtrip while holding [`MPC_TLS_SESSION_LOCK`], so at most one 2PC
/// session (and one dedicated multi-thread runtime) exists in this process at a time.
///
/// Poison-tolerant: a panic inside one roundtrip must not wedge every later one. The protected
/// data is `()` — the lock ORDERS sessions, it guards no invariant-bearing state.
fn with_mpc_tls_session<R>(f: impl FnOnce() -> R) -> R {
    let _guard = MPC_TLS_SESSION_LOCK
        .lock()
        .unwrap_or_else(|p| p.into_inner());
    f()
}

/// [`with_mpc_tls_session`] for sibling modules (the hop prover): the SAME process-wide lock.
pub(crate) fn with_mpc_tls_session_pub<R>(f: impl FnOnce() -> R) -> R {
    with_mpc_tls_session(f)
}

/// A canned endpoint exchange the test server answers. Endpoint-parameterized: the same
/// live MPC-TLS machinery drives an Anthropic `POST /v1/messages`, a public GitHub
/// `GET /repos/…/commits/…`, or a public Coinbase `GET /v2/prices/…/spot` — a new endpoint
/// is DATA (method + path + optional secret header + response body), not a fork.
#[derive(Clone, Debug)]
pub struct LiveExchange {
    /// The HTTP method (`POST` for Anthropic, `GET` for the public read-only endpoints).
    pub method: String,
    /// The request target path.
    pub path: String,
    /// A redacted secret request header `(name, value)`, or `None` for a public endpoint.
    pub secret_header: Option<(String, String)>,
    /// The request body (empty for the read-only GETs).
    pub request_body: String,
    /// The response body the server returns.
    pub response_body: String,
}

impl LiveExchange {
    /// A minimal well-formed Anthropic messages exchange over `text` (POST, `x-api-key`).
    pub fn messages(prompt: &str, reply: &str) -> Self {
        LiveExchange {
            method: "POST".to_string(),
            path: "/v1/messages".to_string(),
            secret_header: Some(("x-api-key".to_string(), API_KEY_SECRET.to_string())),
            request_body: format!(
                "{{\"model\":\"claude-opus-4-8\",\"max_tokens\":64,\
                 \"messages\":[{{\"role\":\"user\",\"content\":\"{prompt}\"}}]}}"
            ),
            response_body: format!(
                "{{\"id\":\"msg_live\",\"type\":\"message\",\"role\":\"assistant\",\
                 \"model\":\"claude-opus-4-8\",\
                 \"content\":[{{\"type\":\"text\",\"text\":\"{reply}\"}}],\
                 \"stop_reason\":\"end_turn\",\"stop_sequence\":null,\
                 \"usage\":{{\"input_tokens\":12,\"output_tokens\":5}}}}"
            ),
        }
    }

    /// A public GitHub commit lookup (GET, no secret) returning a commit-shaped body.
    pub fn github_commit(
        owner: &str,
        repo: &str,
        sha: &str,
        author: &str,
        date: &str,
        message: &str,
    ) -> Self {
        LiveExchange {
            method: "GET".to_string(),
            path: format!("/repos/{owner}/{repo}/commits/{sha}"),
            secret_header: None,
            request_body: String::new(),
            response_body: dregg_zkoracle_prove::endpoints::github::github_commit_body(
                sha, author, date, message,
            ),
        }
    }

    /// A public Coinbase spot quote (GET, no secret) returning a spot-price body.
    pub fn coinbase_spot(asset: &str, amount: &str) -> Self {
        LiveExchange {
            method: "GET".to_string(),
            path: format!("/v2/prices/{asset}/spot"),
            secret_header: None,
            request_body: String::new(),
            response_body: dregg_zkoracle_prove::endpoints::price::coinbase_spot_body(
                asset, amount,
            ),
        }
    }
}

/// The disclosed body + views a verified presentation yields.
#[derive(Clone, Debug)]
pub struct VerifiedResponse {
    /// The authenticated messages JSON response body (feed to the CFG + injection legs).
    pub response_body: Vec<u8>,
    /// The authenticated server identity (must be the pinned host).
    pub server_name: String,
    /// The session time (`connection_info.time`, unix seconds).
    pub connection_time: u64,
    /// The delivered *sent* (request) bytes, unauthenticated positions set to `X`.
    pub sent_redacted: Vec<u8>,
}

impl VerifiedResponse {
    /// Whether the `x-api-key` secret was hidden (selective disclosure worked).
    pub fn api_key_hidden(&self) -> bool {
        !contains_subslice(&self.sent_redacted, API_KEY_SECRET.as_bytes())
            && !contains_subslice(&self.sent_redacted, b"MERCHANT-API-KEY")
    }
}

/// A completed real roundtrip: the verified response + the raw `Presentation` bytes.
#[derive(Clone, Debug)]
pub struct LiveRoundtrip {
    /// The verified, extracted response.
    pub verified: VerifiedResponse,
    /// The bincode-serialized real `tlsn` `Presentation`.
    pub presentation_bytes: Vec<u8>,
    /// The server host the presentation was verified against (the local cert domain).
    pub pinned_server: String,
}

// ─────────────────────────────────────────────────────────────────────────────
// The test HTTPS server — a controllable server returning the Anthropic-shaped JSON over
// TLS, presenting the tlsn-server-fixture cert (domain test-server.io).
// ─────────────────────────────────────────────────────────────────────────────

async fn serve_messages_once<S>(server_socket: S, exchange: LiveExchange) -> Result<()>
where
    S: tokio::io::AsyncRead + tokio::io::AsyncWrite + Send + Unpin + 'static,
{
    use futures_rustls::TlsAcceptor;
    use futures_rustls::pki_types::{
        CertificateDer as RustlsCert, PrivateKeyDer as RustlsKey, PrivatePkcs8KeyDer,
    };
    use futures_rustls::rustls::{ServerConfig, crypto::ring, version::TLS12};

    let cert = RustlsCert::from(SERVER_CERT_DER);
    let key = RustlsKey::Pkcs8(PrivatePkcs8KeyDer::from(SERVER_KEY_DER));

    let config = ServerConfig::builder_with_provider(Arc::new(ring::default_provider()))
        .with_protocol_versions(&[&TLS12])
        .context("server: TLS1.2 provider")?
        .with_no_client_auth()
        .with_single_cert(vec![cert], key)
        .context("server: single cert")?;

    let acceptor = TlsAcceptor::from(Arc::new(config));
    let tls = acceptor.accept(server_socket.compat()).await?;
    let io = TokioIo::new(tls.compat());

    let body = exchange.response_body;
    let service = hyper::service::service_fn(move |_req: Request<hyper::body::Incoming>| {
        let body = body.clone();
        async move {
            Ok::<_, std::convert::Infallible>(
                Response::builder()
                    .status(StatusCode::OK)
                    .header("content-type", "application/json")
                    .header("connection", "close")
                    .body(Full::new(Bytes::from(body)))
                    .unwrap(),
            )
        }
    });

    hyper::server::conn::http1::Builder::new()
        .keep_alive(false)
        .serve_connection(io, service)
        .await
        .map_err(|e| anyhow!("server: serve_connection: {e}"))?;
    Ok(())
}

// ─────────────────────────────────────────────────────────────────────────────
// The Notary — a real local tlsn verifier that runs the MPC-TLS commitment protocol and
// signs an `Attestation` (secp256k1). Mirrors deco-prove's notary.
// ─────────────────────────────────────────────────────────────────────────────

async fn notary<S>(socket: S) -> Result<()>
where
    S: tokio::io::AsyncRead + tokio::io::AsyncWrite + Send + Sync + Unpin + 'static,
{
    let session = Session::new(socket.compat());
    let (driver, mut handle) = session.split();
    let driver_task = tokio::spawn(driver);

    let verifier_config = VerifierConfig::builder()
        .root_store(RootCertStore {
            roots: vec![CertificateDer(CA_CERT_DER.to_vec())],
        })
        .build()?;

    let verifier = match handle.new_verifier(verifier_config)?.commit().await? {
        VerifierCommitStart::Mpc(verifier) => verifier.accept().await?.run().await?,
        VerifierCommitStart::Proxy(verifier) => {
            verifier.reject(Some("expecting MPC-TLS")).await?;
            return Err(anyhow!("notary rejected non-MPC configuration"));
        }
    };

    let (
        VerifierOutput {
            transcript_commitments,
            ..
        },
        verifier,
    ) = verifier.verify().await?.accept().await?;

    let tls_transcript = verifier.tls_transcript().clone();
    verifier.close().await?;

    let sent_len: usize = tls_transcript
        .sent()
        .iter()
        .filter_map(|r| match r.typ {
            ContentType::ApplicationData => Some(r.ciphertext.len()),
            _ => None,
        })
        .sum();
    let recv_len: usize = tls_transcript
        .recv()
        .iter()
        .filter_map(|r| match r.typ {
            ContentType::ApplicationData => Some(r.ciphertext.len()),
            _ => None,
        })
        .sum();

    handle.close();
    let mut socket = driver_task.await??;

    let mut request_bytes = Vec::new();
    socket.read_to_end(&mut request_bytes).await?;
    let request: AttestationRequest = bincode::deserialize(&request_bytes)?;

    let signing_key = k256::ecdsa::SigningKey::from_bytes(&[1u8; 32].into())?;
    let signer = Box::new(Secp256k1Signer::new(&signing_key.to_bytes())?);
    let mut provider = CryptoProvider::default();
    provider.signer.set_signer(signer);

    let mut att_config_builder = AttestationConfig::builder();
    att_config_builder.supported_signature_algs(Vec::from_iter(provider.signer.supported_algs()));
    let att_config = att_config_builder.build()?;

    let CertBinding::V1_2(binding) = tls_transcript.certificate_binding() else {
        return Err(anyhow!("unsupported cert binding version"));
    };
    let mut builder = Attestation::builder(&att_config).accept_request(request)?;
    builder
        .connection_info(ConnectionInfo {
            time: tls_transcript.time(),
            version: tls_transcript.version(),
            transcript_length: TranscriptLength {
                sent: sent_len as u32,
                received: recv_len as u32,
            },
        })
        .server_ephemeral_key(binding.server_ephemeral_key.clone())
        .transcript_commitments(transcript_commitments);

    let attestation = builder.build(&provider)?;
    let attestation_bytes = bincode::serialize(&attestation)?;
    socket.write_all(&attestation_bytes).await?;
    socket.close().await?;
    Ok(())
}

// ─────────────────────────────────────────────────────────────────────────────
// The Prover — connects, runs MPC-TLS, POSTs /v1/messages, selectively discloses (hiding
// x-api-key), and builds a real `Presentation`.
// ─────────────────────────────────────────────────────────────────────────────

async fn prove_messages_presentation(exchange: &LiveExchange) -> Result<Vec<u8>> {
    let (notary_socket, prover_notary_socket) = tokio::io::duplex(1 << 23);
    let (server_socket, prover_server_socket) = tokio::io::duplex(1 << 16);

    let notary_task = tokio::spawn(notary(notary_socket));
    let server_task = tokio::spawn(serve_messages_once(server_socket, exchange.clone()));

    let session = Session::new(prover_notary_socket.compat());
    let (driver, mut handle) = session.split();
    let driver_task = tokio::spawn(driver);

    let prover = handle
        .new_prover(ProverConfig::builder().build()?)?
        .commit(
            MpcTlsConfig::builder()
                .max_sent_data(MAX_SENT_DATA)
                .max_recv_data(MAX_RECV_DATA)
                .build()?,
        )
        .await?;

    let (tls_connection, prover) = prover.connect(
        TlsClientConfig::builder()
            .server_name(ServerName::Dns(SERVER_DOMAIN.try_into()?))
            .root_store(RootCertStore {
                roots: vec![CertificateDer(CA_CERT_DER.to_vec())],
            })
            .build()?,
        prover_server_socket.compat(),
    )?;
    let tls_connection = TokioIo::new(tls_connection.compat());
    let prover_task = tokio::spawn(prover.into_future());

    let (mut request_sender, connection) =
        hyper::client::conn::http1::handshake(tls_connection).await?;
    tokio::spawn(connection);

    let mut request_builder = Request::builder()
        .uri(exchange.path.as_str())
        .method(exchange.method.as_str())
        .header("Host", SERVER_DOMAIN)
        .header("Accept", "*/*")
        .header("Accept-Encoding", "identity")
        .header("Connection", "close")
        .header("content-type", "application/json");
    if let Some((name, value)) = &exchange.secret_header {
        request_builder = request_builder.header(name.as_str(), value.as_str());
    }
    let request = request_builder.body(Full::<Bytes>::new(Bytes::from(
        exchange.request_body.clone(),
    )))?;
    let response = request_sender.send_request(request).await?;
    if response.status() != StatusCode::OK {
        return Err(anyhow!("server returned {}", response.status()));
    }
    // Drain the body so the transcript is complete before proving.
    let _ = response.into_body().collect().await?;

    let mut prover = prover_task.await??;

    let transcript = HttpTranscript::parse(prover.transcript())?;
    let mut commit_builder = TranscriptCommitConfig::builder(prover.transcript());
    DefaultHttpCommitter::default().commit_transcript(&mut commit_builder, &transcript)?;
    let transcript_commit = commit_builder.build()?;

    let mut req_cfg_builder = RequestConfig::builder();
    req_cfg_builder.transcript_commit(transcript_commit);
    let request_config = req_cfg_builder.build()?;

    let mut prove_builder = ProveConfig::builder(prover.transcript());
    if let Some(config) = request_config.transcript_commit() {
        prove_builder.transcript_commit(config.clone());
    }
    let disclosure_config = prove_builder.build()?;

    let ProverOutput {
        transcript_commitments,
        transcript_secrets,
        ..
    } = prover.prove(&disclosure_config).await?;

    let prover_transcript = prover.transcript().clone();
    let tls_transcript = prover.tls_transcript().clone();
    prover.close().await?;

    let mut att_req_builder = AttestationRequest::builder(&request_config);
    att_req_builder
        .server_name(ServerName::Dns(SERVER_DOMAIN.try_into()?))
        .handshake_data(HandshakeData {
            certs: tls_transcript
                .server_cert_chain()
                .context("server cert chain present")?
                .to_vec(),
            sig: tls_transcript
                .server_signature()
                .context("server signature present")?
                .clone(),
            binding: tls_transcript.certificate_binding().clone(),
        })
        .transcript(prover_transcript)
        .transcript_commitments(transcript_secrets, transcript_commitments);
    let (att_request, secrets) = att_req_builder.build(&CryptoProvider::default())?;

    handle.close();
    let mut socket = driver_task.await??;
    socket.write_all(&bincode::serialize(&att_request)?).await?;
    socket.close().await?;
    let mut attestation_bytes = Vec::new();
    socket.read_to_end(&mut attestation_bytes).await?;
    let attestation: Attestation = bincode::deserialize(&attestation_bytes)?;
    att_request.validate(&attestation, &CryptoProvider::default())?;

    // ── Build the PRESENTATION with selective disclosure.
    let http = HttpTranscript::parse(secrets.transcript())?;
    let mut builder = secrets.transcript_proof_builder();

    // Request: reveal structure + target + every header EXCEPT the x-api-key VALUE (the
    // killer property — prove the response without revealing your Anthropic key).
    let req = &http.requests[0];
    builder.reveal_sent(req.without_data())?;
    builder.reveal_sent(&req.request.target)?;
    let secret_name = exchange.secret_header.as_ref().map(|(n, _)| n.as_str());
    for header in &req.headers {
        // The declared secret header (if any) reveals only its NAME — the VALUE stays
        // hidden (selective disclosure). Public endpoints have no secret; reveal all.
        if secret_name.is_some_and(|n| header.name.as_str().eq_ignore_ascii_case(n)) {
            builder.reveal_sent(header.without_value())?;
        } else {
            builder.reveal_sent(header)?;
        }
    }

    // Response: reveal it entirely — the messages body is the disclosed public evidence.
    let resp = &http.responses[0];
    builder.reveal_recv(resp)?;
    let transcript_proof = builder.build()?;

    let provider = CryptoProvider::default();
    let mut pres_builder = attestation.presentation_builder(&provider);
    pres_builder
        .identity_proof(secrets.identity_proof())
        .transcript_proof(transcript_proof);
    let presentation: Presentation = pres_builder.build()?;

    let bytes = bincode::serialize(&presentation)?;

    notary_task.await??;
    server_task.await??;
    Ok(bytes)
}

/// **Verify a real `tlsn` presentation** and extract the authenticated messages response
/// body. Runs `presentation.verify()` (real crypto — a tampered presentation fails here),
/// pins the server host, and reads the response body out of the authenticated transcript.
pub fn verify_messages_presentation(
    presentation_bytes: &[u8],
    expected_server: &str,
) -> Result<VerifiedResponse> {
    let presentation: Presentation =
        bincode::deserialize(presentation_bytes).context("presentation does not deserialize")?;

    let root_cert_store = RootCertStore {
        roots: vec![CertificateDer(CA_CERT_DER.to_vec())],
    };
    let crypto_provider = CryptoProvider {
        cert: ServerCertVerifier::new(&root_cert_store)?,
        ..Default::default()
    };

    let PresentationOutput {
        server_name,
        connection_info,
        transcript,
        ..
    } = presentation
        .verify(&crypto_provider)
        .map_err(|e| anyhow!("presentation.verify() refused: {e}"))?;

    let server_name = server_name.context("presentation did not authenticate a server name")?;
    let ServerName::Dns(server_dns) = server_name;
    let server_name = server_dns.as_str().to_string();
    if server_name != expected_server {
        return Err(anyhow!(
            "server pin: got {server_name:?}, expected {expected_server:?}"
        ));
    }

    let mut partial = transcript.context("presentation revealed no transcript")?;
    partial.set_unauthed(b'X');
    let sent_redacted = partial.sent_unsafe().to_vec();
    let recv_redacted = partial.received_unsafe().to_vec();

    let body_start =
        find_subslice(&recv_redacted, b"\r\n\r\n").context("no header/body separator")? + 4;
    let response_body = recv_redacted[body_start..].to_vec();

    Ok(VerifiedResponse {
        response_body,
        server_name,
        connection_time: connection_info.time,
        sent_redacted,
    })
}

/// **Run the full REAL local MPC-TLS roundtrip** (server + notary + prover in-process),
/// producing a signed presentation, then verify it and extract the response body.
/// Blocking: stands up its own multi-thread tokio runtime, serialized against every other
/// session in this process by [`MPC_TLS_SESSION_LOCK`] (concurrent sessions DEADLOCK — see it).
pub fn run_local_roundtrip_blocking(exchange: &LiveExchange) -> Result<LiveRoundtrip> {
    with_mpc_tls_session(|| {
        let rt = tokio::runtime::Builder::new_multi_thread()
            .enable_all()
            .build()?;
        let presentation_bytes = rt.block_on(prove_messages_presentation(exchange))?;
        let verified = verify_messages_presentation(&presentation_bytes, SERVER_DOMAIN)?;
        Ok(LiveRoundtrip {
            verified,
            presentation_bytes,
            pinned_server: SERVER_DOMAIN.to_string(),
        })
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// THE REAL-HOST PATH — genuine MPC-TLS 2PC against LIVE api.coinbase.com:443.
//
// The SAME machinery as the fixture path above, with FOUR swaps (mirroring the proven
// `tlsn_bedrock` real-host adaptation):
//   1. the prover connects to a REAL `TcpStream` to `api.coinbase.com:443`, not a
//      `tokio::io::duplex` to an in-process test server;
//   2. the root store is the Mozilla/webpki set (`RootCertStore::mozilla()`), so Coinbase's
//      GENUINE cert chain verifies and the SNI/name pins `api.coinbase.com`
//      (`COINBASE_SERVER_NAME`) instead of the fixture `test-server.io` (`SERVER_DOMAIN`);
//   3. the notary is a SEPARATE hosted party (`notary_server::spawn_hosted_notary`, Mozilla
//      roots), reached only by socket address — the prover never holds its key;
//   4. the request is `GET /v2/prices/{asset}/spot` with NO secret header (a public,
//      read-only endpoint), so selective disclosure reveals EVERY request header + the whole
//      response body.
// Verification uses `ServerCertVerifier::mozilla()` and PINS the separate notary's key.
// ─────────────────────────────────────────────────────────────────────────────

use dregg_zkoracle_prove::endpoints::price::COINBASE_SERVER_NAME;

/// A completed real roundtrip against live `api.coinbase.com`: the verified response, the raw
/// `tlsn` `Presentation` bytes, and the SEPARATE notary's pin (socket + pinned verifying key)
/// the attestation binds to.
#[derive(Clone, Debug)]
pub struct CoinbaseRoundtrip {
    /// The verified, extracted response (the spot-price JSON body + session identity/time).
    pub verified: VerifiedResponse,
    /// The bincode-serialized real `tlsn` `Presentation`.
    pub presentation_bytes: Vec<u8>,
    /// The pinned host (`api.coinbase.com`).
    pub pinned_server: String,
    /// The separate hosted notary's pin — the verifying key a verifier pins out-of-band.
    pub notary_pin: crate::notary_server::NotaryPin,
}

/// **Run the REAL MPC-TLS 2PC prover against live `api.coinbase.com`**, connecting to a
/// SEPARATE hosted notary at `notary_addr` over a real TCP socket, and produce a signed `tlsn`
/// presentation of the `GET /v2/prices/{asset}/spot` session.
async fn prove_live_presentation(
    server_name: &str,
    path: &str,
    notary_addr: std::net::SocketAddr,
) -> Result<Vec<u8>> {
    // Prover ↔ SEPARATE notary over a real socket (not an in-process duplex).
    let prover_notary_socket = tokio::net::TcpStream::connect(notary_addr)
        .await
        .with_context(|| format!("connect to separate notary at {notary_addr}"))?;
    let session = Session::new(prover_notary_socket.compat());
    let (driver, mut handle) = session.split();
    let driver_task = tokio::spawn(driver);

    let prover = handle
        .new_prover(ProverConfig::builder().build()?)?
        .commit(
            MpcTlsConfig::builder()
                .max_sent_data(MAX_SENT_DATA)
                .max_recv_data(MAX_RECV_DATA)
                .build()?,
        )
        .await?;

    // The ONLY networking change vs the fixture path: a REAL TCP socket to Coinbase, with the
    // Mozilla roots + the pinned Coinbase SNI.
    let server_socket = tokio::net::TcpStream::connect((server_name, 443u16))
        .await
        .with_context(|| format!("TCP connect to {server_name}:443"))?;
    let (tls_connection, prover) = prover.connect(
        TlsClientConfig::builder()
            .server_name(ServerName::Dns(server_name.try_into()?))
            .root_store(RootCertStore::mozilla())
            .build()?,
        server_socket.compat(),
    )?;
    let tls_connection = TokioIo::new(tls_connection.compat());
    let prover_task = tokio::spawn(prover.into_future());

    let (mut request_sender, connection) =
        hyper::client::conn::http1::handshake(tls_connection).await?;
    tokio::spawn(connection);

    // GET /v2/prices/{asset}/spot — a public read-only quote (no auth, empty body). A
    // `User-Agent` is sent because Coinbase's edge rejects UA-less requests.
    let request = Request::builder()
        .uri(path)
        .method("GET")
        .header("Host", server_name)
        .header("User-Agent", "dregg-oracle/0.1")
        .header("Accept", "application/json")
        .header("Accept-Encoding", "identity")
        .header("Connection", "close")
        .body(Full::<Bytes>::new(Bytes::new()))?;
    let response = request_sender.send_request(request).await?;
    let status = response.status();
    // Drain the body so the transcript is complete before proving.
    let _ = response.into_body().collect().await?;
    if status != StatusCode::OK {
        return Err(anyhow!("{server_name} returned {status}"));
    }

    let mut prover = prover_task.await??;

    let transcript = HttpTranscript::parse(prover.transcript())?;
    let mut commit_builder = TranscriptCommitConfig::builder(prover.transcript());
    DefaultHttpCommitter::default().commit_transcript(&mut commit_builder, &transcript)?;
    let transcript_commit = commit_builder.build()?;

    let mut req_cfg_builder = RequestConfig::builder();
    req_cfg_builder.transcript_commit(transcript_commit);
    let request_config = req_cfg_builder.build()?;

    let mut prove_builder = ProveConfig::builder(prover.transcript());
    if let Some(config) = request_config.transcript_commit() {
        prove_builder.transcript_commit(config.clone());
    }
    let disclosure_config = prove_builder.build()?;

    let ProverOutput {
        transcript_commitments,
        transcript_secrets,
        ..
    } = prover.prove(&disclosure_config).await?;

    let prover_transcript = prover.transcript().clone();
    let tls_transcript = prover.tls_transcript().clone();
    prover.close().await?;

    let mut att_req_builder = AttestationRequest::builder(&request_config);
    att_req_builder
        .server_name(ServerName::Dns(server_name.try_into()?))
        .handshake_data(HandshakeData {
            certs: tls_transcript
                .server_cert_chain()
                .context("server cert chain present")?
                .to_vec(),
            sig: tls_transcript
                .server_signature()
                .context("server signature present")?
                .clone(),
            binding: tls_transcript.certificate_binding().clone(),
        })
        .transcript(prover_transcript)
        .transcript_commitments(transcript_secrets, transcript_commitments);
    let (att_request, secrets) = att_req_builder.build(&CryptoProvider::default())?;

    handle.close();
    let mut socket = driver_task.await??;
    socket.write_all(&bincode::serialize(&att_request)?).await?;
    socket.close().await?;
    let mut attestation_bytes = Vec::new();
    socket.read_to_end(&mut attestation_bytes).await?;
    let attestation: Attestation = bincode::deserialize(&attestation_bytes)?;
    att_request.validate(&attestation, &CryptoProvider::default())?;

    // Public read-only endpoint: NO secret to hide — reveal the request structure, the target,
    // and EVERY header, plus the whole response body (the disclosed price evidence).
    let http = HttpTranscript::parse(secrets.transcript())?;
    let mut builder = secrets.transcript_proof_builder();
    let req = &http.requests[0];
    builder.reveal_sent(req.without_data())?;
    builder.reveal_sent(&req.request.target)?;
    for header in &req.headers {
        builder.reveal_sent(header)?;
    }
    let resp = &http.responses[0];
    builder.reveal_recv(resp)?;
    let transcript_proof = builder.build()?;

    let provider = CryptoProvider::default();
    let mut pres_builder = attestation.presentation_builder(&provider);
    pres_builder
        .identity_proof(secrets.identity_proof())
        .transcript_proof(transcript_proof);
    let presentation: Presentation = pres_builder.build()?;
    Ok(bincode::serialize(&presentation)?)
}

async fn prove_coinbase_presentation(
    asset: &str,
    notary_addr: std::net::SocketAddr,
) -> Result<Vec<u8>> {
    prove_live_presentation(
        COINBASE_SERVER_NAME,
        &format!("/v2/prices/{asset}/spot"),
        notary_addr,
    )
    .await
}

/// **Verify a real Coinbase presentation** against the Mozilla roots, PIN the separate
/// notary's verifying key (reject any attestation not signed by the trusted notary), pin the
/// `api.coinbase.com` host, and extract the authenticated spot-price response body. Runs the
/// real `presentation.verify()` — a tampered/forged presentation fails here in genuine `tlsn`
/// crypto. (Same shape as `tlsn_bedrock::verify_bedrock_presentation`, host swapped.)
pub fn verify_coinbase_presentation(
    presentation_bytes: &[u8],
    expected_host: &str,
    expected_notary_key: &VerifyingKey,
) -> Result<VerifiedResponse> {
    let presentation: Presentation =
        bincode::deserialize(presentation_bytes).context("presentation does not deserialize")?;

    // PIN THE NOTARY: the embedded verifying key must be exactly the notary we trust.
    let presented_key = presentation.verifying_key().clone();
    if &presented_key != expected_notary_key {
        return Err(anyhow!(
            "notary pin: presentation signed by an untrusted notary key"
        ));
    }

    let crypto_provider = CryptoProvider {
        cert: ServerCertVerifier::mozilla(),
        ..Default::default()
    };

    let PresentationOutput {
        server_name,
        connection_info,
        transcript,
        attestation,
        ..
    } = presentation
        .verify(&crypto_provider)
        .map_err(|e| anyhow!("presentation.verify() refused: {e}"))?;

    // Defense in depth: after verify(), re-confirm the signature-checked key is the pin.
    if attestation.body.verifying_key() != expected_notary_key {
        return Err(anyhow!(
            "notary pin: verified attestation key does not match the pinned notary key"
        ));
    }

    let server_name = server_name.context("presentation did not authenticate a server name")?;
    let ServerName::Dns(server_dns) = server_name;
    let server_name = server_dns.as_str().to_string();
    if server_name != expected_host {
        return Err(anyhow!(
            "server pin: got {server_name:?}, expected {expected_host:?}"
        ));
    }

    let mut partial = transcript.context("presentation revealed no transcript")?;
    partial.set_unauthed(b'X');
    let sent_redacted = partial.sent_unsafe().to_vec();
    let recv_redacted = partial.received_unsafe().to_vec();

    let body_start =
        find_subslice(&recv_redacted, b"\r\n\r\n").context("no header/body separator")? + 4;
    let response_body = recv_redacted[body_start..].to_vec();

    Ok(VerifiedResponse {
        response_body,
        server_name,
        connection_time: connection_info.time,
        sent_redacted,
    })
}

/// The full REAL Coinbase MPC-TLS roundtrip against a SEPARATE hosted notary that owns
/// `notary_key`: spawn the notary as a distinct party on a real localhost socket (the prover
/// reaches it only by address and never learns its key), run the 2PC prover against
/// `api.coinbase.com`, then verify under the notary's PINNED public key and extract the body.
async fn run_coinbase_roundtrip_inner(
    asset: &str,
    notary_key: k256::ecdsa::SigningKey,
) -> Result<CoinbaseRoundtrip> {
    let notary = crate::notary_server::spawn_hosted_notary(notary_key, 1).await?;
    let pin = notary.pin().clone();
    let presentation_bytes = prove_coinbase_presentation(asset, pin.addr).await?;
    notary.join().await?;
    let verified = verify_coinbase_presentation(
        &presentation_bytes,
        COINBASE_SERVER_NAME,
        &pin.verifying_key,
    )?;
    Ok(CoinbaseRoundtrip {
        verified,
        presentation_bytes,
        pinned_server: COINBASE_SERVER_NAME.to_string(),
        notary_pin: pin,
    })
}

/// **Run the full REAL Coinbase MPC-TLS roundtrip** (EPHEMERAL notary key — a fresh key each
/// run). Blocking: stands up its own multi-thread runtime. Requires live network. For a stable,
/// re-pinnable notary anchor use [`run_coinbase_roundtrip_with_durable_notary`].
pub fn run_coinbase_roundtrip_blocking(asset: &str) -> Result<CoinbaseRoundtrip> {
    with_mpc_tls_session(|| {
        let notary_key = crate::notary_server::generate_notary_key()?;
        let rt = tokio::runtime::Builder::new_multi_thread()
            .enable_all()
            .build()?;
        rt.block_on(run_coinbase_roundtrip_inner(asset, notary_key))
    })
}

/// Generic real-host MPC-TLS roundtrip: spawn a local notary, prove a live
/// `GET {path}` against `server_name:443`, verify the presentation, return the
/// `CoinbaseRoundtrip` container (reused across endpoints).
async fn run_live_roundtrip_inner(
    server_name: &str,
    path: &str,
    notary_key: k256::ecdsa::SigningKey,
) -> Result<CoinbaseRoundtrip> {
    let notary = crate::notary_server::spawn_hosted_notary(notary_key, 1).await?;
    let pin = notary.pin().clone();
    let presentation_bytes = prove_live_presentation(server_name, path, pin.addr).await?;
    notary.join().await?;
    let verified =
        verify_coinbase_presentation(&presentation_bytes, server_name, &pin.verifying_key)?;
    Ok(CoinbaseRoundtrip {
        verified,
        presentation_bytes,
        pinned_server: server_name.to_string(),
        notary_pin: pin,
    })
}

/// Generic real-host MPC-TLS roundtrip: `GET https://{host}{path}`. The caller owns
/// the host pin + the path; the response body is disclosed whole.
pub fn run_url_roundtrip_blocking(host: &str, path: &str) -> Result<CoinbaseRoundtrip> {
    with_mpc_tls_session(|| {
        let notary_key = crate::notary_server::generate_notary_key()?;
        let rt = tokio::runtime::Builder::new_multi_thread()
            .enable_all()
            .build()?;
        rt.block_on(run_live_roundtrip_inner(host, path, notary_key))
    })
}

/// Real-host MPC-TLS roundtrip against `GET api.github.com/repos/{owner}/{repo}/commits/{sha}`.
pub fn run_github_roundtrip_blocking(
    owner: &str,
    repo: &str,
    sha: &str,
) -> Result<CoinbaseRoundtrip> {
    let path = dregg_zkoracle_prove::endpoints::github::github_commit_path(owner, repo, sha);
    with_mpc_tls_session(|| {
        let notary_key = crate::notary_server::generate_notary_key()?;
        let rt = tokio::runtime::Builder::new_multi_thread()
            .enable_all()
            .build()?;
        rt.block_on(run_live_roundtrip_inner(
            dregg_zkoracle_prove::endpoints::github::GITHUB_SERVER_NAME,
            &path,
            notary_key,
        ))
    })
}

/// **Run the roundtrip against a DURABLE hosted notary** whose signing key is persisted at
/// `key_path` ([`crate::notary_server::load_or_generate_notary_key`]): provisioned once, reused
/// every subsequent run, so [`CoinbaseRoundtrip::notary_pin`]'s verifying key is stable and a
/// verifier can pin it ONCE, out-of-band.
pub fn run_coinbase_roundtrip_with_durable_notary(
    asset: &str,
    key_path: &std::path::Path,
) -> Result<CoinbaseRoundtrip> {
    let notary_key = crate::notary_server::load_or_generate_notary_key(key_path)?;
    with_mpc_tls_session(|| {
        let rt = tokio::runtime::Builder::new_multi_thread()
            .enable_all()
            .build()?;
        rt.block_on(run_coinbase_roundtrip_inner(asset, notary_key))
    })
}

fn find_subslice(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    haystack.windows(needle.len()).position(|w| w == needle)
}

fn contains_subslice(haystack: &[u8], needle: &[u8]) -> bool {
    find_subslice(haystack, needle).is_some()
}
