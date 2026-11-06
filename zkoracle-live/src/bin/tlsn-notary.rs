//! `tlsn-notary` — the MPC-TLS notary as its OWN process (initiative 9, call trees).
//!
//!     tlsn-notary --listen 0.0.0.0:7047 --key <path> [--extra-root <der>]... [--pin-out <path>]
//!
//! Loads (or creates once) the durable secp256k1 key at `--key`, prints and optionally writes
//! the pin (`k256:<hex SEC1>` — the string a call-tree verifier's policy lists), then serves one
//! notary session per connection, concurrently, forever. The prover reaches it only by address.
//! `--extra-root` adds a DER trust root for a server whose self-signed certificate verifiers pin.
//! Run it detached with a PID file; stop it by that PID.

use anyhow::{Context, Result, anyhow};
use dregg_zkoracle_live::notary_server::{
    load_or_generate_notary_key, run_notary_session_with_roots, verifying_key_of,
};

fn main() -> Result<()> {
    let mut listen = None;
    let mut key = None;
    let mut roots: Vec<Vec<u8>> = Vec::new();
    let mut pin_out = None;
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--listen" => listen = args.next(),
            "--key" => key = args.next(),
            "--extra-root" => {
                let p = args.next().context("--extra-root needs a path")?;
                roots.push(std::fs::read(&p).with_context(|| format!("read {p}"))?);
            }
            "--pin-out" => pin_out = args.next(),
            other => return Err(anyhow!("unknown argument {other}")),
        }
    }
    let listen = listen.context("--listen required")?;
    let key_path = key.context("--key required")?;
    let signing_key = load_or_generate_notary_key(std::path::Path::new(&key_path))?;
    let vk = verifying_key_of(&signing_key)?;
    let pin = format!(
        "{}:{}",
        vk.alg,
        vk.data
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>()
    );
    println!("tlsn-notary pin {pin}");
    if let Some(p) = pin_out {
        std::fs::write(&p, format!("{pin}\n"))?;
    }
    let rt = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()?;
    rt.block_on(async move {
        let listener = tokio::net::TcpListener::bind(listen.as_str()).await?;
        println!("tlsn-notary listening on {}", listener.local_addr()?);
        loop {
            let (socket, peer) = listener.accept().await?;
            let key = signing_key.clone();
            let roots = roots.clone();
            tokio::spawn(async move {
                match run_notary_session_with_roots(socket, &key, &roots).await {
                    Ok(()) => println!("session {peer}: attestation signed"),
                    Err(e) => println!("session {peer}: refused: {e:#}"),
                }
            });
        }
        #[allow(unreachable_code)]
        Ok::<(), anyhow::Error>(())
    })
}
