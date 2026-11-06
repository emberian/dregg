//! **One attested HTTPS hop, any method, any host** — the transport the call-tree recorder
//! (`calltree/`, initiative 9) drives for every outbound request.
//!
//! This is [`crate::tlsn_bedrock`]'s prover generalized from "SigV4 POST to Bedrock" to a
//! [`HopRequest`]: any method, path, headers and body; any header listed in
//! [`HopRequest::redact_headers`] has its VALUE hidden from the presentation (name revealed);
//! the connect address may differ from the TLS server name (a tool server reached by IP); and
//! extra trust roots may be added to the Mozilla set (a self-signed tool server the verifier
//! pins out of band). The notary is reached by address only — it is a separate process
//! (`src/bin/tlsn-notary.rs`), never spawned here.
//!
//! [`extract_presentation`] is the verify side, and it deliberately decides NOTHING beyond
//! `presentation.verify()`: it returns the authenticated server name, the notary's verifying key,
//! the connection time and the authenticated sent/received bytes (unauthenticated positions set
//! to `X`). Pinning the notary, the host allowlist and every digest comparison belong to the
//! Lean checker (`metatheory/Dregg2/Lightclient/CallTreeDeploy.lean::deployedV`).

use std::future::IntoFuture;
use std::net::SocketAddr;

use anyhow::{Context, Result, anyhow};
use futures::io::{AsyncReadExt as _, AsyncWriteExt as _};
use http_body_util::{BodyExt, Full};
use hyper::Request;
use hyper::body::Bytes;
use hyper_util::rt::TokioIo;
use tokio_util::compat::{FuturesAsyncReadCompatExt, TokioAsyncReadCompatExt};

use tlsn::{
    Session,
    attestation::{
        Attestation, CryptoProvider,
        presentation::{Presentation, PresentationOutput},
        request::{Request as AttestationRequest, RequestConfig},
    },
    config::{
        prove::ProveConfig, prover::ProverConfig, tls::TlsClientConfig,
        tls_commit::mpc::MpcTlsConfig,
    },
    connection::{HandshakeData, ServerName},
    prover::ProverOutput,
    transcript::TranscriptCommitConfig,
    verifier::ServerCertVerifier,
    webpki::{CertificateDer, RootCertStore},
};
use tlsn_formats::http::{DefaultHttpCommitter, HttpCommit, HttpTranscript};

/// The 2PC preprocessing bounds for a hop. Cost scales ~linearly; a hop larger than these is
/// refused by the prover, never truncated. MEASURED 2026-11-06 on bb2: 8 KiB / 32 KiB fails in
/// preprocessing with `context mux error` against this alpha.15 notary; 4 KiB / 16 KiB (the
/// bounds every other live path here uses) is the working setting.
pub const HOP_MAX_SENT: usize = 1 << 12;
/// See [`HOP_MAX_SENT`].
pub const HOP_MAX_RECV: usize = 1 << 14;

/// One outbound HTTPS request to attest.
#[derive(Clone, Debug)]
pub struct HopRequest {
    /// The TLS server name (SNI and the certificate's DNS name).
    pub server_name: String,
    /// Where to connect (`host:port`); usually `server_name:443`.
    pub connect: String,
    /// `GET`, `POST`, ...
    pub method: String,
    /// The request target.
    pub path: String,
    /// Extra request headers (Host, Connection: close and Accept-Encoding: identity are added).
    pub headers: Vec<(String, String)>,
    /// The request body.
    pub body: Vec<u8>,
    /// Header names (case-insensitive) whose VALUES are hidden in the presentation.
    pub redact_headers: Vec<String>,
    /// Extra trust roots (DER) added to the Mozilla set.
    pub extra_roots: Vec<Vec<u8>>,
}

/// What the prover gets back from a hop.
#[derive(Clone, Debug)]
pub struct HopOutcome {
    /// The bincode-serialized `tlsn` `Presentation`.
    pub presentation: Vec<u8>,
    /// The HTTP status.
    pub status: u16,
    /// The response body as the prover's HTTP client decoded it (for the caller's own use; the
    /// attested bytes are in the presentation).
    pub body: Vec<u8>,
}

fn root_store(extra_roots: &[Vec<u8>]) -> RootCertStore {
    let mut roots = RootCertStore::mozilla();
    for der in extra_roots {
        roots.roots.push(CertificateDer(der.clone()));
    }
    roots
}

async fn prove_hop(req: &HopRequest, notary_addr: SocketAddr) -> Result<HopOutcome> {
    let notary_socket = tokio::net::TcpStream::connect(notary_addr)
        .await
        .with_context(|| format!("connect to notary at {notary_addr}"))?;
    let session = Session::new(notary_socket.compat());
    let (driver, mut handle) = session.split();
    let driver_task = tokio::spawn(driver);

    let prover = handle
        .new_prover(ProverConfig::builder().build()?)?
        .commit(
            MpcTlsConfig::builder()
                .max_sent_data(HOP_MAX_SENT)
                .max_recv_data(HOP_MAX_RECV)
                .build()?,
        )
        .await?;

    let server_socket = tokio::net::TcpStream::connect(req.connect.as_str())
        .await
        .with_context(|| format!("TCP connect to {}", req.connect))?;
    let (tls_connection, prover) = prover.connect(
        TlsClientConfig::builder()
            .server_name(ServerName::Dns(req.server_name.as_str().try_into()?))
            .root_store(root_store(&req.extra_roots))
            .build()?,
        server_socket.compat(),
    )?;
    let tls_connection = TokioIo::new(tls_connection.compat());
    let prover_task = tokio::spawn(prover.into_future());

    let (mut sender, connection) = hyper::client::conn::http1::handshake(tls_connection).await?;
    tokio::spawn(connection);

    let mut builder = Request::builder()
        .uri(req.path.as_str())
        .method(req.method.as_str())
        .header("Host", req.server_name.as_str())
        .header("Accept-Encoding", "identity")
        .header("Connection", "close");
    for (k, v) in &req.headers {
        builder = builder.header(k.as_str(), v.as_str());
    }
    let request = builder.body(Full::<Bytes>::new(Bytes::from(req.body.clone())))?;
    let response = sender.send_request(request).await?;
    let status = response.status().as_u16();
    let body = response.into_body().collect().await?.to_bytes().to_vec();

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
        .server_name(ServerName::Dns(req.server_name.as_str().try_into()?))
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
    let attestation: Attestation = bincode::deserialize(&attestation_bytes)
        .context("notary returned no attestation (did it refuse the session?)")?;
    att_request.validate(&attestation, &CryptoProvider::default())?;

    // Reveal the request line, the target, every header (redacted ones by NAME only) and the
    // request body; reveal the whole response.
    let http = HttpTranscript::parse(secrets.transcript())?;
    let mut proof_builder = secrets.transcript_proof_builder();
    let r = &http.requests[0];
    proof_builder.reveal_sent(r.without_data())?;
    proof_builder.reveal_sent(&r.request.target)?;
    for header in &r.headers {
        let hidden = req
            .redact_headers
            .iter()
            .any(|n| header.name.as_str().eq_ignore_ascii_case(n));
        if hidden {
            proof_builder.reveal_sent(header.without_value())?;
        } else {
            proof_builder.reveal_sent(header)?;
        }
    }
    if let Some(b) = &r.body {
        proof_builder.reveal_sent(b)?;
    }
    proof_builder.reveal_recv(&http.responses[0])?;
    let transcript_proof = proof_builder.build()?;

    let provider = CryptoProvider::default();
    let mut pres_builder = attestation.presentation_builder(&provider);
    pres_builder
        .identity_proof(secrets.identity_proof())
        .transcript_proof(transcript_proof);
    let presentation: Presentation = pres_builder.build()?;
    Ok(HopOutcome {
        presentation: bincode::serialize(&presentation)?,
        status,
        body,
    })
}

/// **Prove one hop** against the notary at `notary_addr` (a separate process). Blocking: one
/// MPC-TLS session at a time in this process (the same lock every roundtrip here takes).
pub fn prove_hop_blocking(req: &HopRequest, notary_addr: SocketAddr) -> Result<HopOutcome> {
    crate::tlsn_live::with_mpc_tls_session_pub(|| {
        let rt = tokio::runtime::Builder::new_multi_thread()
            .enable_all()
            .build()?;
        rt.block_on(prove_hop(req, notary_addr))
    })
}

/// What `presentation.verify()` returned for one presentation — no pin, no policy.
#[derive(Clone, Debug)]
pub struct HopExtract {
    /// The authenticated server name.
    pub server_name: String,
    /// The notary's verifying key the attestation was checked under: `"<alg>:<hex SEC1>"`.
    pub notary_key_hex: String,
    /// The connection time the notary attested (unix seconds).
    pub connection_time: u64,
    /// The authenticated sent bytes; positions the presentation did NOT authenticate are `0x00`.
    pub sent: Vec<u8>,
    /// The authenticated received bytes; unauthenticated positions are `0x00`.
    pub recv: Vec<u8>,
    /// The signed attestation's identity: hex of its bincode header (id, version, field root).
    /// Every presentation cut from one notarised session carries the same value.
    pub session: String,
}

/// **Extract** a presentation: run `presentation.verify()` with the Mozilla roots and return what
/// it authenticated. A forged or tampered presentation, trailing bytes after the encoding, or a
/// server certificate that chains to no root is refused here.
///
/// `scoped_roots` are `(server name, DER root)` pins for servers outside the WebPKI (the call-tree
/// tool server's self-signed root). A pinned root is HOST-SCOPED: it is tried only after the
/// Mozilla roots refuse, and a presentation it admits must authenticate exactly that server name
/// — so trusting the tool's root never lets it vouch for any other host.
pub fn extract_presentation(
    presentation_bytes: &[u8],
    scoped_roots: &[(String, Vec<u8>)],
) -> Result<HopExtract> {
    use bincode::Options as _;
    let decode = || -> Result<Presentation> {
        bincode::DefaultOptions::new()
            .with_fixint_encoding()
            .reject_trailing_bytes()
            .deserialize(presentation_bytes)
            .context("presentation does not deserialize exactly (trailing bytes are refused)")
    };
    match extract_with(decode()?, &[]) {
        Ok(ex) => Ok(ex),
        Err(mozilla_err) => {
            for (host, der) in scoped_roots {
                if let Ok(ex) = extract_with(decode()?, std::slice::from_ref(der)) {
                    if &ex.server_name == host {
                        return Ok(ex);
                    }
                    return Err(anyhow!(
                        "a host-scoped root for {host} admitted a presentation for {}",
                        ex.server_name
                    ));
                }
            }
            Err(mozilla_err)
        }
    }
}

fn extract_with(presentation: Presentation, extra_roots: &[Vec<u8>]) -> Result<HopExtract> {
    let key = presentation.verifying_key().clone();
    let crypto_provider = CryptoProvider {
        cert: ServerCertVerifier::new(&root_store(extra_roots))?,
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
    if attestation.body.verifying_key() != &key {
        return Err(anyhow!(
            "attestation key differs from the presentation's key"
        ));
    }
    let session = hex_lower(&bincode::serialize(&attestation.header)?);
    let ServerName::Dns(dns) = server_name.context("presentation authenticated no server name")?;
    let mut partial = transcript.context("presentation revealed no transcript")?;
    partial.set_unauthed(0);
    Ok(HopExtract {
        server_name: dns.as_str().to_string(),
        notary_key_hex: format!("{}:{}", key.alg, hex_lower(&key.data)),
        connection_time: connection_info.time,
        sent: partial.sent_unsafe().to_vec(),
        recv: partial.received_unsafe().to_vec(),
        session,
    })
}

fn hex_lower(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}
