//! `dregg-calltree-verify` — verify a recorded call tree, offline.
//!
//! ```text
//! dregg-calltree-verify --recording <file> --policy <file> --root <hex>
//!                       [--extra-root <host>=<der>]... --checker <calltree-check> [--bundle-out <file>]
//! ```
//!
//! For each presentation it runs `presentation.verify()` (tlsn alpha.15) and passes on ONLY what it
//! authenticated; it decides nothing. The bundle goes over stdin to the Lean checker
//! (`lake exe calltree-check`), whose verdict is `CallTreeDeploy.deployedVerify`; this binary exits 0
//! only if the checker accepted AND echoed the root given on the command line. No network is used.

use std::io::Write as _;
use std::time::Instant;

use anyhow::{Context, Result, anyhow};
use dregg_zkoracle_live::tlsn_hop::extract_presentation;
use serde_json::{Value, json};

fn main() -> Result<()> {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    let mut kv: Vec<(String, String)> = vec![];
    let mut i = 0;
    while i < argv.len() {
        let k = argv[i]
            .strip_prefix("--")
            .ok_or_else(|| anyhow!("expected --flag"))?;
        kv.push((
            k.to_string(),
            argv.get(i + 1).context("flag needs a value")?.clone(),
        ));
        i += 2;
    }
    let one = |k: &str| {
        kv.iter()
            .rev()
            .find(|(a, _)| a == k)
            .map(|(_, v)| v.clone())
            .ok_or_else(|| anyhow!("--{k} required"))
    };
    let t0 = Instant::now();
    let rec: Value = serde_json::from_slice(&std::fs::read(one("recording")?)?)?;
    let policy: Value = serde_json::from_slice(&std::fs::read(one("policy")?)?)?;
    let root = one("root")?;
    let mut scoped = vec![];
    for (k, spec) in &kv {
        if k == "extra-root" {
            let (host, path) = spec
                .split_once('=')
                .context("--extra-root takes host=path")?;
            scoped.push((host.to_string(), std::fs::read(path)?));
        }
    }
    let mut evidence = vec![];
    for p in rec["presentations"].as_array().context("presentations")? {
        let h = p["presentation"].as_str().context("presentation hex")?;
        match extract_presentation(&hex::decode(h)?, &scoped) {
            Ok(ex) => evidence.push(json!({
                "presentation": h, "server_name": ex.server_name, "notary_key": ex.notary_key_hex,
                "sent": hex::encode(&ex.sent), "recv": hex::encode(&ex.recv),
                "time": ex.connection_time, "session": ex.session,
            })),
            Err(e) => eprintln!("presentation refused by tlsn: {e:#}"),
        }
    }
    let extract_ms = t0.elapsed().as_millis();
    let bundle = json!({ "root": root, "policy": policy, "tree": rec["tree"],
                         "evidence": evidence, "edges": rec["edges"] });
    if let Some((_, p)) = kv.iter().find(|(k, _)| k == "bundle-out") {
        std::fs::write(p, bundle.to_string())?;
    }
    let t1 = Instant::now();
    let mut child = std::process::Command::new(one("checker")?)
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
    let judged: Value = serde_json::from_str(stdout.trim()).unwrap_or(Value::Null);
    let ok = out.status.code() == Some(0) && judged["root"].as_str() == Some(root.as_str());
    println!(
        "{{\"accepted\":{ok},\"notary_operator\":{},\"extract_ms\":{extract_ms},\"lean_check_ms\":{check_ms}}}",
        rec["notary_operator"]
    );
    std::process::exit(if ok {
        0
    } else if out.status.code() == Some(2) {
        2
    } else {
        1
    });
}
