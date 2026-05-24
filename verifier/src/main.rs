//! `pyana-verifier`: Standalone Effect VM proof verifier.
//!
//! # Usage
//!
//! ## CLI mode
//! ```text
//! pyana-verifier \
//!   --proof /path/to/proof.bin \
//!   --pi /path/to/pi.json \
//!   --vk-hash 8b80e1cf7b0a04e74e7d7bfb9c7a11e37c1d0bb1a5edae8e3b92c9e9b6d5f42a
//! ```
//!
//! ## stdin (JSON) mode
//! ```text
//! echo '{"proof_hex":"...","public_inputs":[...],"vk_hash":"auto"}' | pyana-verifier
//! ```
//!
//! ## Exit codes
//! - 0 — proof verified
//! - 1 — proof rejected (cryptographically invalid)
//! - 2 — error (bad inputs, unknown VK, deserialisation failure)
//!
//! # Isolation guarantee
//! This binary imports ONLY `pyana-circuit` and `pyana-types`. It carries no
//! prover state, no ledger, no executor, no program registry. The only
//! dependencies on shared context are the bytes it reads from disk / stdin.

use pyana_verifier::{
    CommitteeDescriptor, JsonRequest, ReplayEntry, VerifierOutput, exit_code,
    parse_public_inputs_json, replay_chain, verify_bilateral_bundle_json, verify_cross_fed_bundle,
    verify_effect_vm_proof,
};
use std::{
    env,
    io::{self, Read},
    process,
};

fn main() {
    let args: Vec<String> = env::args().collect();

    // Subcommand dispatch.
    if args.len() >= 2 && args[1] == "replay-chain" {
        run_replay_chain(&args[2..]);
    }
    if args.len() >= 2 && (args[1] == "verify-cross-fed-bundle" || args[1] == "cross-fed") {
        run_verify_cross_fed_bundle(&args[2..]);
    }
    if args.len() >= 2 && (args[1] == "bilateral-pair" || args[1] == "bilateral-bundle") {
        run_bilateral_pair(&args[2..]);
    }

    // Detect JSON-stdin mode: no args, or stdin is not a tty.
    // We use the simple heuristic: if no flags given, read stdin.
    let (proof_bytes, pi_u32, vk_hash) = if args.len() == 1 {
        match read_json_stdin() {
            Ok(t) => t,
            Err(e) => {
                let out = VerifierOutput::reject(format!("stdin read error: {}", e));
                print_and_exit(out, exit_code::ERROR);
            }
        }
    } else {
        match parse_cli(&args[1..]) {
            Ok(t) => t,
            Err(e) => {
                eprintln!("Usage: pyana-verifier --proof <file> --pi <file> --vk-hash <hex>");
                eprintln!("       pyana-verifier  (reads JSON from stdin)");
                eprintln!("Error: {}", e);
                process::exit(exit_code::ERROR);
            }
        }
    };

    let (output, code) = verify_effect_vm_proof(&proof_bytes, &pi_u32, &vk_hash);
    print_and_exit(output, code);
}

fn print_and_exit(output: VerifierOutput, code: i32) -> ! {
    let json = serde_json::to_string(&output)
        .unwrap_or_else(|_| r#"{"verified":false,"reason":"serialisation error"}"#.to_string());
    println!("{}", json);
    process::exit(code);
}

// ---------------------------------------------------------------------------
// CLI argument parsing (no external parser dep)
// ---------------------------------------------------------------------------

fn parse_cli(args: &[String]) -> Result<(Vec<u8>, Vec<u32>, String), String> {
    let mut proof_path: Option<&str> = None;
    let mut pi_path: Option<&str> = None;
    let mut vk_hash: Option<&str> = None;

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--proof" => {
                i += 1;
                proof_path = Some(args.get(i).ok_or("--proof requires a value")?);
            }
            "--pi" => {
                i += 1;
                pi_path = Some(args.get(i).ok_or("--pi requires a value")?);
            }
            "--vk-hash" => {
                i += 1;
                vk_hash = Some(args.get(i).ok_or("--vk-hash requires a value")?);
            }
            other => return Err(format!("unknown flag: {}", other)),
        }
        i += 1;
    }

    let proof_path = proof_path.ok_or("--proof is required")?;
    let pi_path = pi_path.ok_or("--pi is required")?;
    let vk_hash = vk_hash.ok_or("--vk-hash is required")?;

    let proof_bytes =
        std::fs::read(proof_path).map_err(|e| format!("cannot read proof file: {}", e))?;
    let pi_json =
        std::fs::read_to_string(pi_path).map_err(|e| format!("cannot read pi file: {}", e))?;
    let pi_u32 = parse_public_inputs_json(&pi_json)?;

    Ok((proof_bytes, pi_u32, vk_hash.to_string()))
}

// ---------------------------------------------------------------------------
// JSON stdin mode
// ---------------------------------------------------------------------------

fn read_json_stdin() -> Result<(Vec<u8>, Vec<u32>, String), String> {
    let mut buf = String::new();
    io::stdin()
        .read_to_string(&mut buf)
        .map_err(|e| format!("stdin read error: {}", e))?;
    let req = JsonRequest::parse(&buf)?;
    let proof_bytes = req.proof_bytes()?;
    Ok((proof_bytes, req.public_inputs, req.vk_hash))
}

// ---------------------------------------------------------------------------
// replay-chain subcommand
// ---------------------------------------------------------------------------

/// `pyana-verifier replay-chain <path-to-chain.json>`
///
/// Reads a JSON array of `WitnessedReceipt` entries (the on-disk shape
/// produced by `pyana_turn::WitnessedReceipt::chain_to_json`), runs the
/// v1 replay loop (proof verify + trace re-check + witness_hash binding),
/// and prints a JSON verdict object. Exit code matches the chain-level
/// verdict (0 = all verified, 1 = at least one rejection, 2 = read/parse error).
fn run_replay_chain(args: &[String]) -> ! {
    let path = match args.first() {
        Some(p) => p,
        None => {
            eprintln!("Usage: pyana-verifier replay-chain <path-to-chain.json>");
            process::exit(exit_code::ERROR);
        }
    };

    let text = match std::fs::read_to_string(path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("cannot read {}: {}", path, e);
            process::exit(exit_code::ERROR);
        }
    };

    let entries: Vec<ReplayEntry> = match serde_json::from_str(&text) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("cannot parse chain JSON: {}", e);
            process::exit(exit_code::ERROR);
        }
    };

    let output = replay_chain(&entries);
    let json = serde_json::to_string_pretty(&output).unwrap_or_else(|_| {
        r#"{"overall_verified":false,"summary":"serialisation error"}"#.to_string()
    });
    println!("{}", json);

    let code = if output.overall_verified {
        exit_code::VERIFIED
    } else {
        exit_code::REJECTED
    };
    process::exit(code);
}

// ---------------------------------------------------------------------------
// verify-cross-fed-bundle subcommand
// ---------------------------------------------------------------------------

/// `pyana-verifier verify-cross-fed-bundle --bundle <path> --known-issuer <path> --known-recipient <path>`
///
/// Reads a JSON-encoded `pyana_federation::CrossFedReceiptBundle` and two
/// committee descriptors (issuing + receiving federation), runs the 8-step
/// cross-federation verification from `SILVER-VISION-E2E-VERIFICATION.md`
/// §1 Step 6, and prints a `CrossFedVerdict` JSON to stdout. Exit code
/// matches the verdict (0 = overall_verified, 1 = at least one check
/// failed, 2 = parse / IO error).
fn run_verify_cross_fed_bundle(args: &[String]) -> ! {
    let mut bundle_path: Option<String> = None;
    let mut issuer_path: Option<String> = None;
    let mut recipient_path: Option<String> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--bundle" => {
                i += 1;
                bundle_path = args.get(i).cloned();
            }
            "--known-issuer" | "--known-F1" => {
                i += 1;
                issuer_path = args.get(i).cloned();
            }
            "--known-recipient" | "--known-F2" => {
                i += 1;
                recipient_path = args.get(i).cloned();
            }
            other => {
                eprintln!("unknown flag: {other}");
                eprintln!(
                    "Usage: pyana-verifier verify-cross-fed-bundle --bundle <path> \
                     --known-issuer <path> --known-recipient <path>"
                );
                process::exit(exit_code::ERROR);
            }
        }
        i += 1;
    }
    let bundle_path = match bundle_path {
        Some(p) => p,
        None => {
            eprintln!("--bundle is required");
            process::exit(exit_code::ERROR);
        }
    };
    let issuer_path = match issuer_path {
        Some(p) => p,
        None => {
            eprintln!("--known-issuer is required");
            process::exit(exit_code::ERROR);
        }
    };
    let recipient_path = match recipient_path {
        Some(p) => p,
        None => {
            eprintln!("--known-recipient is required");
            process::exit(exit_code::ERROR);
        }
    };

    let bundle_text = match std::fs::read_to_string(&bundle_path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("cannot read bundle file {bundle_path}: {e}");
            process::exit(exit_code::ERROR);
        }
    };
    let bundle: pyana_federation::CrossFedReceiptBundle = match serde_json::from_str(&bundle_text) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("cannot parse bundle JSON ({bundle_path}): {e}");
            process::exit(exit_code::ERROR);
        }
    };
    let issuer: CommitteeDescriptor = match std::fs::read_to_string(&issuer_path).and_then(|t| {
        serde_json::from_str(&t).map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
    }) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("cannot read issuer descriptor {issuer_path}: {e}");
            process::exit(exit_code::ERROR);
        }
    };
    let recipient: CommitteeDescriptor =
        match std::fs::read_to_string(&recipient_path).and_then(|t| {
            serde_json::from_str(&t).map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
        }) {
            Ok(d) => d,
            Err(e) => {
                eprintln!("cannot read recipient descriptor {recipient_path}: {e}");
                process::exit(exit_code::ERROR);
            }
        };

    let verdict = verify_cross_fed_bundle(&bundle, &issuer, &recipient);
    let json = serde_json::to_string_pretty(&verdict).unwrap_or_else(|_| {
        r#"{"overall_verified":false,"summary":"serialisation error"}"#.to_string()
    });
    println!("{}", json);
    let code = if verdict.overall_verified {
        exit_code::VERIFIED
    } else {
        exit_code::REJECTED
    };
    process::exit(code);
}

// ---------------------------------------------------------------------------
// bilateral-pair subcommand (Stage 7-γ.2 Phase 1)
// ---------------------------------------------------------------------------

/// `pyana-verifier bilateral-pair <bundle.json>`
///
/// Reads a JSON-encoded `BilateralBundle` (the on-disk shape produced by
/// `pyana_verifier::BilateralBundle`), runs the off-AIR bilateral
/// cross-cell consistency check from `STAGE-7-GAMMA-2-PI-DESIGN.md` §4,
/// and prints a `BilateralVerdict` JSON to stdout.
///
/// Exit code: 0 = verified, 1 = rejected, 2 = read / parse error.
///
/// The bundle JSON shape:
/// ```json
/// {
///   "turn": <Turn>,
///   "entries": [
///     {"cell_id": "<32-byte hex>", "witnessed_receipt": <WitnessedReceipt>},
///     ...
///   ]
/// }
/// ```
fn run_bilateral_pair(args: &[String]) -> ! {
    let path = match args.first() {
        Some(p) => p,
        None => {
            eprintln!("Usage: pyana-verifier bilateral-pair <bundle.json>");
            process::exit(exit_code::ERROR);
        }
    };

    let text = match std::fs::read_to_string(path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("cannot read {}: {}", path, e);
            process::exit(exit_code::ERROR);
        }
    };

    let verdict = verify_bilateral_bundle_json(&text);
    let json = serde_json::to_string_pretty(&verdict)
        .unwrap_or_else(|_| r#"{"verified":false,"reason":"serialisation error"}"#.to_string());
    println!("{}", json);
    let code = if verdict.verified {
        exit_code::VERIFIED
    } else {
        exit_code::REJECTED
    };
    process::exit(code);
}
