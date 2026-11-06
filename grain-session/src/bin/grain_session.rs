//! `grain-session`: produce, countersign and verify a Claude Code session bundle.
//!
//! Stranger side (no session material, no host trust in the decision):
//!   grain-session keygen  <renter.key>                      # prints your pubkey and nonce
//!   grain-session setup <n_windows>                         # mint the R3 VK yourself
//!   grain-session countersign <renter.key> <vk> <bundle.json>   # acknowledge what you checked
//!   grain-session verify <bundle.json> <renter_pub> <nonce> <vk>
//!   grain-session tamper <bundle.json> <renter_pub> <nonce> <vk>   # the tamper classes
//! Producer side (holds the cv exports and the owner secret):
//!   grain-session produce <export_dir> <session_id> <owner.secret> <window> <nonce> <out bundle.json>
//!   grain-session project <export_dir> <owner.secret> <out calls.json>

use std::path::Path;
use std::process::ExitCode;

use grain_session::{Bundle, CallPublic, countersign, parse32, verify_bundle};

fn usage() -> ExitCode {
    eprintln!(
        "{}",
        include_str!("grain_session.rs")
            .lines()
            .take(13)
            .collect::<Vec<_>>()
            .join("\n")
    );
    ExitCode::from(2)
}

fn read_secret(p: &str) -> Result<[u8; 32], String> {
    parse32(&std::fs::read_to_string(p).map_err(|e| format!("{p}: {e}"))?)
}

fn random32() -> [u8; 32] {
    let mut b = [0u8; 32];
    getrandom::fill(&mut b).expect("OS randomness");
    b
}

fn report_accept(a: &grain_session::Accepted) {
    println!("ACCEPT");
    println!(
        "  R0  {} receipts, one signer, chained, budget-consistent",
        a.ladder.base.actions
    );
    println!(
        "  R1  your countersigned checkpoint covers all {} receipts; genesis nonce is yours and sits in receipt 0",
        a.windows
    );
    println!(
        "  R2  {} receipts link committed executor turns in the manifest",
        a.ladder.linked
    );
    println!(
        "  N   {} calls, each a leaf of exactly one receipted window, in order",
        a.calls
    );
    println!(
        "  R3  {} folded legs; aggregate head == your anchored head in all 8 lanes; decided by Lean r3VerifyCore",
        a.r3.num_turns
    );
}

fn run(args: &[String]) -> Result<ExitCode, String> {
    match args.first().map(String::as_str) {
        Some("keygen") if args.len() == 2 => {
            let seed = random32();
            let nonce = random32();
            std::fs::write(
                &args[1],
                format!("{}\n{}\n", hex::encode(seed), hex::encode(nonce)),
            )
            .map_err(|e| e.to_string())?;
            let public = dregg_agent::receipt::ReceiptSigner::from_seed(seed).public();
            println!("renter_pub {}", hex::encode(public));
            println!("nonce      {}", hex::encode(nonce));
            Ok(ExitCode::SUCCESS)
        }
        Some("countersign") if args.len() == 4 => {
            let key = std::fs::read_to_string(&args[1]).map_err(|e| e.to_string())?;
            let mut lines = key.lines();
            let seed = parse32(lines.next().unwrap_or(""))?;
            let nonce = parse32(lines.next().unwrap_or(""))?;
            let mut b = Bundle::load(Path::new(&args[3]))?;
            let public = countersign(&mut b, seed, &nonce, &parse32(&args[2])?)?;
            b.save(Path::new(&args[3]))?;
            println!("countersigned by {}", hex::encode(public));
            Ok(ExitCode::SUCCESS)
        }
        Some("verify") if args.len() == 5 => {
            let b = Bundle::load(Path::new(&args[1]))?;
            let vk = parse32(&args[4])?;
            match verify_bundle(&b, &parse32(&args[2])?, &parse32(&args[3])?, &vk) {
                Ok(a) => {
                    report_accept(&a);
                    Ok(ExitCode::SUCCESS)
                }
                Err(r) => {
                    println!("{r}");
                    Ok(ExitCode::from(1))
                }
            }
        }
        Some("tamper") if args.len() == 5 => {
            let b = Bundle::load(Path::new(&args[1]))?;
            let (rp, n) = (parse32(&args[2])?, parse32(&args[3])?);
            let vk = parse32(&args[4])?;
            if let Err(r) = verify_bundle(&b, &rp, &n, &vk) {
                println!(
                    "the untampered bundle is itself refused, so no tamper result means anything: {r}"
                );
                return Ok(ExitCode::from(1));
            }
            let mut all_refused = true;
            for (name, t) in grain_session::tamper::cases(&b) {
                let out = verify_bundle(&t, &rp, &n, &vk);
                let line = match &out {
                    Ok(_) => {
                        all_refused = false;
                        "ACCEPTED (a tamper got through)".to_string()
                    }
                    Err(r) => r.to_string(),
                };
                println!("{name:<28} {line}");
            }
            Ok(if all_refused {
                ExitCode::SUCCESS
            } else {
                ExitCode::from(1)
            })
        }
        #[cfg(feature = "prover")]
        Some("setup") if args.len() == 2 => {
            let n: usize = args[1].parse().map_err(|e| format!("{e}"))?;
            println!(
                "{}",
                hex::encode(grain_session::produce::synthetic_setup(n)?)
            );
            Ok(ExitCode::SUCCESS)
        }
        Some("project") if args.len() == 4 => {
            let mut calls = grain_session::project_exports(Path::new(&args[1]))?;
            grain_session::commit_calls(&mut calls, &read_secret(&args[2])?);
            let public: Vec<CallPublic> = calls.into_iter().map(|c| c.public).collect();
            std::fs::write(
                &args[3],
                serde_json::to_string(&public).map_err(|e| e.to_string())?,
            )
            .map_err(|e| e.to_string())?;
            println!("{} calls", public.len());
            Ok(ExitCode::SUCCESS)
        }
        #[cfg(feature = "prover")]
        Some("produce") if args.len() == 7 => {
            let mut calls = grain_session::project_exports(Path::new(&args[1]))?;
            grain_session::commit_calls(&mut calls, &read_secret(&args[3])?);
            let public: Vec<CallPublic> = calls.into_iter().map(|c| c.public).collect();
            let w: usize = args[4].parse().map_err(|e| format!("{e}"))?;
            let (b, stats) =
                grain_session::produce::produce(&args[2], public, w, parse32(&args[5])?)?;
            b.save(Path::new(&args[6]))?;
            println!("{stats:?}");
            Ok(ExitCode::SUCCESS)
        }
        _ => Ok(usage()),
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::from(2)
        }
    }
}
