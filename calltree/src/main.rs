//! `dregg-calltree` — record, serve and verify certified HTTPS call trees (initiative 9).
//!
//! ```text
//! dregg-calltree certgen   --name <dns> --out <dir>
//! dregg-calltree tool-serve --listen <addr> --certs <dir> --name <dns> --notary <addr> --store <dir>
//! dregg-calltree record    --notary <addr> --operator <str> --notary-key <pin>
//!                          --tool-connect <addr> --tool-name <dns> --tool-root <der> --tool-store <dir>
//!                          --mode glm|free [--zai-key-file <path>] --out <recording.json>
//! dregg-calltree verify    --recording <file> --policy <file> [--extra-root <der>]...
//!                          --checker <calltree-check> [--bundle-out <file>]
//! ```
//!
//! `verify` decides nothing about the tree: it runs `presentation.verify()` per hop (extraction
//! only), writes the bundle, runs the Lean checker and exits with ITS code. It separately reports
//! the grain anchor (the committed grain cell's ATTESTATION slot is the root, and the grain's
//! receipt history verifies, by `grain_turn::verify_grain_history`).

use std::collections::HashMap;
use std::net::SocketAddr;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Instant;

use anyhow::{Context, Result, anyhow, bail};
use dregg_agent::agent::GrainTurnMinter;
use dregg_calltree::*;
use dregg_zkoracle_live::tlsn_hop::{HopRequest, extract_presentation, prove_hop_blocking};
use serde_json::{Value, json};

struct Args(HashMap<String, Vec<String>>);
impl Args {
    fn parse(v: &[String]) -> Result<Args> {
        let mut m: HashMap<String, Vec<String>> = HashMap::new();
        let mut i = 0;
        while i < v.len() {
            let k = v[i]
                .strip_prefix("--")
                .ok_or_else(|| anyhow!("expected --flag, got {}", v[i]))?;
            let val = v.get(i + 1).ok_or_else(|| anyhow!("--{k} needs a value"))?;
            m.entry(k.to_string()).or_default().push(val.clone());
            i += 2;
        }
        Ok(Args(m))
    }
    fn one(&self, k: &str) -> Result<String> {
        self.0
            .get(k)
            .and_then(|v| v.last().cloned())
            .ok_or_else(|| anyhow!("--{k} required"))
    }
    fn opt(&self, k: &str) -> Option<String> {
        self.0.get(k).and_then(|v| v.last().cloned())
    }
    fn all(&self, k: &str) -> Vec<String> {
        self.0.get(k).cloned().unwrap_or_default()
    }
}

fn main() -> Result<()> {
    let argv: Vec<String> = std::env::args().collect();
    let cmd = argv.get(1).cloned().unwrap_or_default();
    let a = Args::parse(&argv[2.min(argv.len())..])?;
    match cmd.as_str() {
        "certgen" => certgen(&a),
        "tool-serve" => tool_serve(&a),
        "record" => record(&a),
        "verify" => std::process::exit(verify(&a)?),
        _ => bail!("usage: dregg-calltree certgen|tool-serve|record|verify ..."),
    }
}

// ───────────────────────────── certgen ─────────────────────────────

fn certgen(a: &Args) -> Result<()> {
    use rcgen::{BasicConstraints, CertificateParams, IsCa, Issuer, KeyPair};
    let name = a.one("name")?;
    let out = PathBuf::from(a.one("out")?);
    std::fs::create_dir_all(&out)?;
    let ca_key = KeyPair::generate()?;
    let mut ca_params = CertificateParams::new(Vec::<String>::new())?;
    ca_params.is_ca = IsCa::Ca(BasicConstraints::Unconstrained);
    ca_params.distinguished_name.push(
        rcgen::DnType::CommonName,
        format!("dregg-calltree root for {name}"),
    );
    let ca = ca_params.self_signed(&ca_key)?;
    let leaf_key = KeyPair::generate()?;
    let leaf_params = CertificateParams::new(vec![name.clone()])?;
    let issuer = Issuer::new(ca_params, ca_key);
    let leaf = leaf_params.signed_by(&leaf_key, &issuer)?;
    std::fs::write(out.join("root.der"), ca.der())?;
    std::fs::write(out.join("leaf.der"), leaf.der())?;
    std::fs::write(out.join("leaf.key.der"), leaf_key.serialize_der())?;
    println!(
        "wrote {}/{{root.der,leaf.der,leaf.key.der}} for {name}",
        out.display()
    );
    Ok(())
}

// ───────────────────────────── tool server ─────────────────────────────

/// The longest run of "safe" bytes (letters, digits, space, `.,:;()-'`) in `body`: the tool's
/// content is a VERBATIM span of the page it fetched, so the kind-1 edge can check it.
fn safe_span(body: &[u8]) -> Vec<u8> {
    let safe = |b: u8| b.is_ascii_alphanumeric() || b" .,:;()-'".contains(&b);
    let (mut best, mut cur) = ((0usize, 0usize), 0usize);
    for (i, b) in body.iter().enumerate() {
        if safe(*b) {
            cur += 1;
            if cur > best.1 - best.0 {
                best = (i + 1 - cur, i + 1);
            }
        } else {
            cur = 0;
        }
    }
    let s = &body[best.0..best.1];
    s.trim_ascii().to_vec()
}

fn split_url(url: &str) -> Result<(String, String)> {
    let rest = url
        .strip_prefix("https://")
        .ok_or_else(|| anyhow!("only https:// URLs"))?;
    let (host, path) = match rest.find('/') {
        Some(i) => (&rest[..i], &rest[i..]),
        None => (rest, "/"),
    };
    Ok((host.to_string(), path.to_string()))
}

/// One fetch: an attested GET of `url`, recorded as the tool's own subtree (one kind-1 hop).
fn tool_fetch(url: &str, notary: SocketAddr, store: &PathBuf) -> Result<Value> {
    let (host, path) = split_url(url)?;
    let t0 = Instant::now();
    let out = prove_hop_blocking(
        &HopRequest {
            server_name: host.clone(),
            connect: format!("{host}:443"),
            method: "GET".into(),
            path,
            headers: vec![("User-Agent".into(), "dregg-calltree-tool/0.1".into())],
            body: vec![],
            redact_headers: vec![],
            extra_roots: vec![],
        },
        notary,
    )?;
    let ms = t0.elapsed().as_millis() as u64;
    let ex = extract_presentation(&out.presentation, &[])?;
    let node = node_of(1, &out.presentation, &ex.server_name, &ex.sent, &ex.recv);
    let kids = vec![node];
    let sub_root = mroot(&[kids[0].commit()?]);
    // The span is taken from the AUTHENTICATED received bytes (after the header block), so the
    // kind-1 edge holds byte-for-byte even for a chunked response (chunk framing breaks a run).
    let body_at = ex
        .recv
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .map(|i| i + 4)
        .unwrap_or(0);
    let content = String::from_utf8(safe_span(&ex.recv[body_at..]))?;
    let rec = json!({
        "kids": kids,
        "presentations": [hex::encode(&out.presentation)],
        "hop_ms": [ms],
        "content": content,
    });
    std::fs::write(
        store.join(format!("{}.json", hex::encode(sub_root))),
        rec.to_string(),
    )?;
    Ok(json!({ "url": url, "content": content, "subtree_root": hex::encode(sub_root) }))
}

fn tool_serve(a: &Args) -> Result<()> {
    use futures_rustls::TlsAcceptor;
    use futures_rustls::pki_types::{CertificateDer, PrivateKeyDer, PrivatePkcs8KeyDer};
    use futures_rustls::rustls::{ServerConfig, crypto::ring, version::TLS12};
    use http_body_util::{BodyExt, Full};
    use hyper::body::Bytes;
    use hyper_util::rt::TokioIo;
    use tokio_util::compat::{FuturesAsyncReadCompatExt, TokioAsyncReadCompatExt};

    let certs = PathBuf::from(a.one("certs")?);
    let notary: SocketAddr = a.one("notary")?.parse()?;
    let store = PathBuf::from(a.one("store")?);
    std::fs::create_dir_all(&store)?;
    let listen = a.one("listen")?;
    let leaf = CertificateDer::from(std::fs::read(certs.join("leaf.der"))?);
    let key = PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(std::fs::read(
        certs.join("leaf.key.der"),
    )?));
    let config = ServerConfig::builder_with_provider(Arc::new(ring::default_provider()))
        .with_protocol_versions(&[&TLS12])?
        .with_no_client_auth()
        .with_single_cert(vec![leaf], key)?;
    let acceptor = TlsAcceptor::from(Arc::new(config));
    let rt = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()?;
    rt.block_on(async move {
        let listener = tokio::net::TcpListener::bind(listen.as_str()).await?;
        println!("tool-serve listening on {}", listener.local_addr()?);
        loop {
            let (sock, peer) = listener.accept().await?;
            let acceptor = acceptor.clone();
            let store = store.clone();
            tokio::spawn(async move {
                let res: Result<()> = async {
                    let tls = acceptor.accept(sock.compat()).await?;
                    let io = TokioIo::new(tls.compat());
                    let svc = hyper::service::service_fn(
                        move |req: hyper::Request<hyper::body::Incoming>| {
                            let store = store.clone();
                            async move {
                                let body = req.into_body().collect().await?.to_bytes();
                                let reply =
                                    tokio::task::spawn_blocking(move || -> Result<Value> {
                                        let v: Value = serde_json::from_slice(&body)?;
                                        let url = v["url"]
                                            .as_str()
                                            .context("body needs url")?
                                            .to_string();
                                        tool_fetch(&url, notary, &store)
                                    })
                                    .await
                                    .map_err(|e| anyhow!("join: {e}"))?;
                                let (status, text) = match reply {
                                    Ok(v) => (200, v.to_string()),
                                    Err(e) => {
                                        (502, json!({ "error": format!("{e:#}") }).to_string())
                                    }
                                };
                                Ok::<_, anyhow::Error>(
                                    hyper::Response::builder()
                                        .status(status)
                                        .header("content-type", "application/json")
                                        .header("connection", "close")
                                        .body(Full::new(Bytes::from(text)))?,
                                )
                            }
                        },
                    );
                    hyper::server::conn::http1::Builder::new()
                        .keep_alive(false)
                        .serve_connection(io, svc)
                        .await?;
                    Ok(())
                }
                .await;
                match res {
                    Ok(()) => println!("{peer}: served"),
                    Err(e) => println!("{peer}: error {e:#}"),
                }
            });
        }
        #[allow(unreachable_code)]
        Ok::<(), anyhow::Error>(())
    })
}

// ───────────────────────────── recorder ─────────────────────────────

fn node_of(kind: i64, presentation: &[u8], server: &str, sent: &[u8], recv: &[u8]) -> Node {
    Node {
        kind,
        att: hexd(&digest_bytes("att", presentation)),
        host: hexd(&digest_bytes("host", server.as_bytes())),
        req: hexd(&digest_bytes("req", sent)),
        resp: hexd(&digest_bytes("resp", recv)),
        kids: vec![],
    }
}

struct Rec {
    notary: SocketAddr,
    nodes: Vec<Node>,
    pres: Vec<String>,
    hop_ms: Vec<u64>,
    edges: Vec<Edge>,
    scoped_roots: Vec<(String, Vec<u8>)>,
}

struct Hop {
    att: String,
    recv: Vec<u8>,
    sent: Vec<u8>,
    body: Vec<u8>,
}

impl Rec {
    fn hop(&mut self, kind: i64, req: HopRequest) -> Result<Hop> {
        let t0 = Instant::now();
        let out = prove_hop_blocking(&req, self.notary)?;
        self.hop_ms.push(t0.elapsed().as_millis() as u64);
        if out.status != 200 {
            bail!(
                "{} {} returned {}: {}",
                req.method,
                req.server_name,
                out.status,
                String::from_utf8_lossy(&out.body)
                    .chars()
                    .take(300)
                    .collect::<String>()
            );
        }
        let ex = extract_presentation(&out.presentation, &self.scoped_roots)?;
        // No key material: every redacted header's value must be absent from what is disclosed.
        for (k, v) in &req.headers {
            if req.redact_headers.iter().any(|r| r.eq_ignore_ascii_case(k))
                && contains(&ex.sent, v.as_bytes())
            {
                bail!("redaction failed for header {k}");
            }
        }
        let node = node_of(kind, &out.presentation, &ex.server_name, &ex.sent, &ex.recv);
        let att = node.att.clone();
        self.nodes.push(node);
        self.pres.push(hex::encode(&out.presentation));
        Ok(Hop {
            att,
            recv: ex.recv,
            sent: ex.sent,
            body: out.body,
        })
    }
    fn edge(
        &mut self,
        kind: u8,
        from: &Hop,
        to_att: &str,
        to_bytes: &[u8],
        span: &[u8],
    ) -> Result<()> {
        if span.len() < 16 || !contains(&from.recv, span) || !contains(to_bytes, span) {
            bail!("edge span not present on both sides ({} bytes)", span.len());
        }
        self.edges.push(Edge {
            kind,
            from: from.att.clone(),
            to: to_att.to_string(),
            bytes: hex::encode(span),
        });
        Ok(())
    }
}

fn contains(h: &[u8], n: &[u8]) -> bool {
    !n.is_empty() && h.windows(n.len()).any(|w| w == n)
}

const ZAI_HOST: &str = "api.z.ai";
const ZAI_PATH: &str = "/api/coding/paas/v4/chat/completions";
const MODEL: &str = "glm-5.3-flash";

fn zai(key: &str, body: &Value) -> HopRequest {
    HopRequest {
        server_name: ZAI_HOST.into(),
        connect: format!("{ZAI_HOST}:443"),
        method: "POST".into(),
        path: ZAI_PATH.into(),
        headers: vec![
            ("Content-Type".into(), "application/json".into()),
            ("Authorization".into(), format!("Bearer {key}")),
        ],
        body: body.to_string().into_bytes(),
        redact_headers: vec!["Authorization".into()],
        extra_roots: vec![],
    }
}

fn tool_req(a: &Args, url: &str, roots: &[Vec<u8>]) -> Result<HopRequest> {
    Ok(HopRequest {
        server_name: a.one("tool-name")?,
        connect: a.one("tool-connect")?,
        method: "POST".into(),
        path: "/fetch".into(),
        headers: vec![("Content-Type".into(), "application/json".into())],
        body: json!({ "url": url }).to_string().into_bytes(),
        redact_headers: vec![],
        extra_roots: roots.to_vec(),
    })
}

/// Attach the tool's recorded subtree (fetched from its store; bound by the root it returned in
/// its attested response) under the tool hop.
fn attach_subtree(rec: &mut Rec, store: &PathBuf, tool_hop: &Hop) -> Result<(Value, Hop)> {
    let v: Value = serde_json::from_slice(&tool_hop.body)?;
    let root = v["subtree_root"]
        .as_str()
        .context("tool returned no subtree_root")?;
    let sub: Value = serde_json::from_slice(&std::fs::read(store.join(format!("{root}.json")))?)?;
    let kids: Vec<Node> = serde_json::from_value(sub["kids"].clone())?;
    let last = rec.nodes.last_mut().context("no tool node")?;
    last.kids = kids.clone();
    anyhow::ensure!(
        hex::encode(last.kids_root()?) == root,
        "subtree does not hash to its root"
    );
    for p in sub["presentations"].as_array().context("presentations")? {
        rec.pres.push(p.as_str().context("hex")?.to_string());
    }
    for m in sub["hop_ms"].as_array().context("hop_ms")? {
        rec.hop_ms.push(m.as_u64().unwrap_or(0));
    }
    let page_pres = hex::decode(sub["presentations"][0].as_str().context("hex")?)?;
    let ex = extract_presentation(&page_pres, &[])?;
    let page = Hop {
        att: kids[0].att.clone(),
        recv: ex.recv,
        sent: ex.sent,
        body: vec![],
    };
    Ok((v, page))
}

fn record(a: &Args) -> Result<()> {
    let notary: SocketAddr = a.one("notary")?.parse()?;
    let tool_root = std::fs::read(a.one("tool-root")?)?;
    let store = PathBuf::from(a.one("tool-store")?);
    let mode = a.one("mode")?;
    let mut rec = Rec {
        notary,
        nodes: vec![],
        pres: vec![],
        hop_ms: vec![],
        edges: vec![],
        scoped_roots: vec![(a.one("tool-name")?, tool_root.clone())],
    };
    let roots = vec![tool_root];
    let (prompt, answer);
    match mode.as_str() {
        "free" => {
            // No LLM: a direct public fetch, then the tool (which fetches its own page).
            prompt = "free-mode: fetch example.com directly and through the tool".to_string();
            let _direct = rec.hop(
                1,
                HopRequest {
                    server_name: "example.com".into(),
                    connect: "example.com:443".into(),
                    method: "GET".into(),
                    path: "/".into(),
                    headers: vec![("User-Agent".into(), "dregg-calltree/0.1".into())],
                    body: vec![],
                    redact_headers: vec![],
                    extra_roots: vec![],
                },
            )?;
            let url = "https://en.wikipedia.org/api/rest_v1/page/summary/Merkle_tree";
            let tool = rec.hop(2, tool_req(a, url, &roots)?)?;
            let (v, page) = attach_subtree(&mut rec, &store, &tool)?;
            let content = v["content"].as_str().unwrap_or("").as_bytes().to_vec();
            rec.edge(1, &page, &tool.att, &tool.recv, &content)?;
            answer = String::from_utf8_lossy(&content).to_string();
        }
        "glm" => {
            let key = std::fs::read_to_string(a.one("zai-key-file")?)?
                .trim()
                .to_string();
            prompt =
                "Use the fetch_page tool to read https://example.com/ and then tell me, in one \
                      short sentence, what that page says it is for."
                    .to_string();
            let tools = json!([{ "type": "function", "function": {
                "name": "fetch_page",
                "description": "Fetch an https URL and return a verbatim span of its text.",
                "parameters": { "type": "object",
                    "properties": { "url": { "type": "string" } }, "required": ["url"] } } }]);
            let msgs = json!([{ "role": "user", "content": prompt }]);
            let llm1 = rec.hop(
                1,
                zai(
                    &key,
                    &json!({
                "model": MODEL, "stream": false, "max_tokens": 300, "temperature": 0,
                "messages": msgs, "tools": tools, "tool_choice": "auto",
                "thinking": { "type": "disabled" } }),
                ),
            )?;
            let r1: Value = serde_json::from_slice(&llm1.body)?;
            let call = &r1["choices"][0]["message"]["tool_calls"][0];
            let call_id = call["id"]
                .as_str()
                .context("model made no tool call")?
                .to_string();
            let args: Value = serde_json::from_str(
                call["function"]["arguments"]
                    .as_str()
                    .context("arguments")?,
            )?;
            let url = args["url"].as_str().context("url")?.to_string();
            let tool = rec.hop(2, tool_req(a, &url, &roots)?)?;
            let (v, page) = attach_subtree(&mut rec, &store, &tool)?;
            let content = v["content"].as_str().unwrap_or("").to_string();
            let tool_att = tool.att.clone();
            let tool_sent = tool.sent.clone();
            rec.edge(0, &llm1, &tool_att, &tool_sent, url.as_bytes())?;
            rec.edge(1, &page, &tool_att, &tool.recv, content.as_bytes())?;
            let msgs2 = json!([
                { "role": "user", "content": prompt },
                r1["choices"][0]["message"].clone(),
                { "role": "tool", "tool_call_id": call_id, "content": content }
            ]);
            let llm2 = rec.hop(
                1,
                zai(
                    &key,
                    &json!({
                "model": MODEL, "stream": false, "max_tokens": 300, "temperature": 0,
                "messages": msgs2, "tools": tools, "thinking": { "type": "disabled" } }),
                ),
            )?;
            let att2 = llm2.att.clone();
            let sent2 = llm2.sent.clone();
            rec.edge(0, &tool, &att2, &sent2, content.as_bytes())?;
            let r2: Value = serde_json::from_slice(&llm2.body)?;
            answer = r2["choices"][0]["message"]["content"]
                .as_str()
                .unwrap_or("")
                .to_string();
        }
        m => bail!("unknown mode {m}"),
    }
    // The root: the local turn node over the hops, req/resp = the turn's prompt and answer.
    let root_node = Node {
        kind: 0,
        att: "0".into(),
        host: "0".into(),
        req: hexd(&digest_bytes("req", prompt.as_bytes())),
        resp: hexd(&digest_bytes("resp", answer.as_bytes())),
        kids: rec.nodes.clone(),
    };
    let root = root_node.commit()?;

    // Mint every node (post-order) as a grain turn through the existing ToolGatewayMinter: the
    // node's commitment at ATTESTATION_SLOT; the last turn carries the root.
    let mut minter = grain_turn::ToolGatewayMinter::open("calltree", 64)
        .map_err(|e| anyhow!("open grain: {e:?}"))?;
    let mut consumed = 0i64;
    let mut post: Vec<(String, D)> = vec![];
    fn walk(n: &Node, out: &mut Vec<(String, D)>) -> Result<()> {
        for k in &n.kids {
            walk(k, out)?;
        }
        out.push((
            format!("calltree:kind{}:{}", n.kind, &n.att[..n.att.len().min(16)]),
            n.commit()?,
        ));
        Ok(())
    }
    walk(&root_node, &mut post)?;
    for (label, c) in &post {
        minter.bind_attestation(*c);
        consumed += 1;
        minter
            .mint_turn(label, 1, consumed, ZERO)
            .map_err(|e| anyhow!("grain refused turn {label}: {e}"))?;
    }
    let cell = minter.committed_worker_cell().context("grain cell")?;
    let recording = Recording {
        root: hex::encode(root),
        tree: root_node,
        presentations: rec
            .pres
            .iter()
            .map(|p| Evidence {
                presentation: p.clone(),
            })
            .collect(),
        edges: rec.edges,
        notary_operator: a.one("operator")?,
        notary_key: a.one("notary-key")?,
        grain_cell: serde_json::to_value(&cell)?,
        grain_receipts: minter.receipt_log().iter().map(hex::encode).collect(),
        hop_ms: rec.hop_ms,
    };
    std::fs::write(a.one("out")?, serde_json::to_string_pretty(&recording)?)?;
    println!(
        "recorded root {} ({} hops, answer: {answer})",
        recording.root,
        recording.presentations.len()
    );
    Ok(())
}

// ───────────────────────────── verifier ─────────────────────────────

fn verify(a: &Args) -> Result<i32> {
    use std::io::Write as _;
    let t0 = Instant::now();
    let rec: Recording = serde_json::from_slice(&std::fs::read(a.one("recording")?)?)?;
    let policy: Value = serde_json::from_slice(&std::fs::read(a.one("policy")?)?)?;
    // The root the verifier TRUSTS comes from the command line (obtained out of band: a signed
    // commit, a published page). Without --root the recording's own root is checked and the
    // verdict says so.
    let (root, root_source) = match a.opt("root") {
        Some(r) => (r, "command line"),
        None => (rec.root.clone(), "recording (self-asserted)"),
    };
    // --extra-root host=path : a HOST-SCOPED pin for a server outside the WebPKI.
    let mut scoped = vec![];
    for spec in a.all("extra-root") {
        let (host, path) = spec
            .split_once('=')
            .context("--extra-root takes host=path")?;
        scoped.push((host.to_string(), std::fs::read(path)?));
    }
    let mut evidence = vec![];
    for p in &rec.presentations {
        let bytes = hex::decode(&p.presentation)?;
        match extract_presentation(&bytes, &scoped) {
            Ok(ex) => evidence.push(json!({
                "presentation": p.presentation,
                "server_name": ex.server_name,
                "notary_key": ex.notary_key_hex,
                "sent": hex::encode(&ex.sent),
                "recv": hex::encode(&ex.recv),
                "time": ex.connection_time,
                "session": ex.session,
            })),
            // A presentation tlsn refuses contributes no evidence: its hop then fails in Lean.
            Err(e) => eprintln!("presentation refused by tlsn: {e:#}"),
        }
    }
    let extract_ms = t0.elapsed().as_millis();
    let bundle = json!({
        "root": root,
        "policy": policy,
        "tree": rec.tree,
        "evidence": evidence,
        "edges": rec.edges,
    });
    if let Some(p) = a.opt("bundle-out") {
        std::fs::write(&p, bundle.to_string())?;
    }
    let t1 = Instant::now();
    let mut child = std::process::Command::new(a.one("checker")?)
        .arg("-")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()?;
    child
        .stdin
        .take()
        .context("stdin")?
        .write_all(bundle.to_string().as_bytes())?;
    let out = child.wait_with_output()?;
    let check_ms = t1.elapsed().as_millis();
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    print!("{stdout}");
    let lean_code = out.status.code().unwrap_or(2);
    // The checker must have judged THIS root.
    let judged: Value = serde_json::from_str(stdout.trim()).unwrap_or(Value::Null);
    let same_root = judged["root"].as_str() == Some(root.as_str());

    // The grain anchor, REPORTED and NOT part of the verdict: the cell comes from the recording,
    // i.e. from the host that ran the executor (R2 trust). It shows the root was minted into a
    // committed grain turn on that host; it does not authenticate the root to a stranger.
    let anchor = (|| -> Result<bool> {
        let cell: dregg_cell::Cell = serde_json::from_value(rec.grain_cell.clone())?;
        let log = rec
            .grain_receipts
            .iter()
            .map(|h| unhexd(h))
            .collect::<Result<Vec<_>>>()?;
        let slot = cell
            .state
            .fields
            .get(grain_turn::ATTESTATION_SLOT)
            .copied()
            .unwrap_or(ZERO);
        let bound = matches!(
            grain_turn::verify_grain_history(&cell, &log),
            grain_turn::GrainHistoryVerdict::Bound
        );
        Ok(hex::encode(slot) == root && bound)
    })()
    .unwrap_or(false);
    println!(
        "{{\"root_source\":{},\"host_asserted_grain_anchor\":{anchor},\"notary_operator\":{},\"extract_ms\":{extract_ms},\"lean_check_ms\":{check_ms}}}",
        serde_json::to_string(root_source)?,
        serde_json::to_string(&rec.notary_operator)?
    );
    Ok(if lean_code == 2 {
        2
    } else if lean_code == 0 && same_root {
        0
    } else {
        1
    })
}
