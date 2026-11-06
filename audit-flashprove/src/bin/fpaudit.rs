//! `fpaudit`: the commit-then-audit auditor over FlashProve's `cp_verify`.
//!
//!   fpaudit experiment --stored DIR --cp-verify BIN --build HEX --work DIR --out FILE
//!                      --p-ppm N --seeds N --base-round R --drand-cache FILE
//!                      [--strategy rate:F | burst:F:K] [--arm closed|open|peek]
//!                      [--horizon-mult M] [--threads T] [--timeout-s S] [--mem-gib G]
//!   fpaudit live --stored DIR --cp-verify BIN --build HEX --out DIR --p-ppm N --n N
//!                [--requester-key FILE] [--false-at T]
//!   fpaudit exact-live --requests FILE --recompute "CMD ARGS" --spec HEX --params HEX
//!                      --weights HEX --out DIR --p-ppm N [--timeout-s S] [--mem-gib G]
//!   fpaudit recheck --pins FILE RECEIPT... [--rerun BIN --files DIR --stored DIR]
//!                   [--recompute "CMD ARGS" --files DIR]
//!
//! `live` serves `n` requests from the stored proof (the one at position `--false-at`, default the
//! last, with a false next token), has a requester countersign each commitment with the latest
//! drand round it has seen (refusing a stale or late round by the beacon schedule), waits for round
//! seen + 2, and audits: receipts and the pins a re-checker needs are written under `--out`. It is a
//! single-process demonstration: the requester key is generated here (from the OS random source)
//! unless `--requester-key` names a 32-byte secret held by someone else.
//!
//! `exact-live` does the same over an exact recompute of gptoss-int v0: each entry of `--requests`
//! (`[{"label", "prompt": [ids], "output": [ids]}]`) is committed as a prompt file and an output
//! file, and a fired audit runs the recompute command on the staged copies.

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use audit_flashprove::beacon::{self, DrandRound};
use audit_flashprove::decide;
use audit_flashprove::experiment::{self, Arm, Config, Stored, Strategy};
use audit_flashprove::receipt::{self, Ledger, Pins, Receipt};
use audit_flashprove::record::{self, Checker, Policy, RequestRecord};
use audit_flashprove::runner::{self, CallFiles};
use dregg_query::mmr::RangeOpening;
use ed25519_dalek::SigningKey;

fn args() -> (String, HashMap<String, String>, Vec<String>) {
    let mut it = std::env::args().skip(1);
    let cmd = it.next().unwrap_or_default();
    let mut kv = HashMap::new();
    let mut pos = Vec::new();
    while let Some(a) = it.next() {
        if let Some(k) = a.strip_prefix("--") {
            kv.insert(k.to_string(), it.next().unwrap_or_default());
        } else {
            pos.push(a);
        }
    }
    (cmd, kv, pos)
}

fn need<'a>(kv: &'a HashMap<String, String>, k: &str) -> &'a str {
    kv.get(k).map(String::as_str).unwrap_or_else(|| {
        eprintln!("fpaudit: missing --{k}");
        std::process::exit(2)
    })
}

fn num<T: std::str::FromStr>(kv: &HashMap<String, String>, k: &str, d: T) -> T {
    kv.get(k).map_or(d, |v| {
        v.parse().unwrap_or_else(|_| panic!("--{k}: not a number"))
    })
}

fn drand_rounds(cache: &PathBuf, base: u64, n: u64) -> Vec<DrandRound> {
    let mut have: HashMap<u64, DrandRound> = std::fs::read(cache)
        .ok()
        .and_then(|b| serde_json::from_slice::<Vec<DrandRound>>(&b).ok())
        .unwrap_or_default()
        .into_iter()
        .map(|r| (r.round, r))
        .collect();
    let mut out = Vec::new();
    for r in base..base + n {
        let d = match have.get(&r) {
            Some(d) => {
                d.verify()
                    .unwrap_or_else(|e| panic!("cached drand round {r}: {e}"));
                d.clone()
            }
            None => {
                let d = beacon::fetch(Some(r)).unwrap_or_else(|e| panic!("drand round {r}: {e}"));
                have.insert(r, d.clone());
                d
            }
        };
        out.push(d);
    }
    let mut all: Vec<_> = have.into_values().collect();
    all.sort_by_key(|d| d.round);
    std::fs::write(cache, serde_json::to_vec(&all).unwrap()).expect("write drand cache");
    out
}

fn experiment(kv: &HashMap<String, String>) {
    let stored = Stored::load(&PathBuf::from(need(kv, "stored"))).expect("stored proof");
    let p_ppm: u64 = num(kv, "p-ppm", 10_000);
    let p_num = decide::p_num_of_ppm(p_ppm).unwrap_or_else(|| {
        eprintln!("fpaudit: --p-ppm must be in 1..=999999");
        std::process::exit(2)
    });
    let seeds: u64 = num(kv, "seeds", 100);
    let strategy = {
        let s = kv.get("strategy").map_or("rate:0.25", String::as_str);
        let parts: Vec<&str> = s.split(':').collect();
        match parts.as_slice() {
            ["rate", f] => Strategy::Rate(f.parse().unwrap()),
            ["burst", f, k] => Strategy::Burst(f.parse().unwrap(), k.parse().unwrap()),
            _ => panic!("--strategy rate:F | burst:F:K"),
        }
    };
    let arm = match kv.get("arm").map_or("closed", String::as_str) {
        "closed" => Arm::Closed,
        "open" => Arm::Open,
        "peek" => Arm::Peek,
        a => panic!("--arm {a}"),
    };
    let horizon = num(kv, "horizon-mult", 20u64) * 1_000_000 / p_ppm;
    let cfg = Arc::new(Config {
        cp_verify: PathBuf::from(need(kv, "cp-verify")),
        stored,
        build: need(kv, "build").to_string(),
        work: PathBuf::from(need(kv, "work")),
        p_num,
        strategy: strategy.clone(),
        arm,
        horizon,
        timeout: Duration::from_secs(num(kv, "timeout-s", 20)),
        mem_bytes: num(kv, "mem-gib", 8u64) << 30,
    });
    let rounds = drand_rounds(
        &PathBuf::from(need(kv, "drand-cache")),
        num(kv, "base-round", 1_000_000),
        seeds,
    );
    let threads: usize = num(kv, "threads", 8);
    let queue = Arc::new(Mutex::new((0..seeds).collect::<Vec<u64>>()));
    let results = Arc::new(Mutex::new(Vec::new()));
    let rounds = Arc::new(rounds);
    let mut hs = Vec::new();
    for _ in 0..threads {
        let (cfg, queue, results, rounds) =
            (cfg.clone(), queue.clone(), results.clone(), rounds.clone());
        hs.push(std::thread::spawn(move || {
            loop {
                let Some(s) = queue.lock().unwrap().pop() else {
                    break;
                };
                let r = experiment::run_seed(&cfg, s, &rounds[s as usize]);
                results.lock().unwrap().push(r);
            }
        }));
    }
    for h in hs {
        h.join().expect("worker");
    }
    let mut res = results.lock().unwrap().clone();
    res.sort_by_key(|r| r.seed);
    let out = PathBuf::from(need(kv, "out"));
    let mut lines = String::new();
    for r in &res {
        lines.push_str(&serde_json::to_string(r).unwrap());
        lines.push('\n');
    }
    std::fs::write(&out, lines).expect("write results");
    let n = res.len() as f64;
    let total_c: u64 = res.iter().map(|r| r.corrupt_before_alarm).sum();
    let mean = total_c as f64 / n;
    let var = res
        .iter()
        .map(|r| (r.corrupt_before_alarm as f64 - mean).powi(2))
        .sum::<f64>()
        / (n - 1.0).max(1.0);
    let p = p_num as f64 / 18_446_744_073_709_551_616.0;
    let summary = serde_json::json!({
        "p_ppm": p_ppm, "p_num": p_num, "ideal_one_over_p": 1.0 / p,
        "note": "historical-beacon simulation of fresh coins; ideal 1/p is the Lean bound at eps_beacon = 0 without its n*(delta_chk + delta_bind) term; censored seeds hit the horizon", "strategy": format!("{strategy:?}"),
        "arm": format!("{arm:?}"), "seeds": res.len(), "horizon": horizon,
        "mean_corrupt_before_alarm": mean, "stderr": (var / n).sqrt(),
        "sum_corrupt": total_c,
        "alarmed": res.iter().filter(|r| r.alarmed).count(),
        "hit_horizon": res.iter().filter(|r| r.hit_horizon).count(),
        "calls": res.iter().map(|r| r.calls).sum::<u64>(),
        "fired_corrupt_accepted": res.iter().map(|r| r.fired_corrupt_accepted).sum::<u64>(),
        "fired_honest_not_accepted": res.iter().map(|r| r.fired_honest_not_accepted).sum::<u64>(),
        "call_seconds": res.iter().map(|r| r.call_millis).sum::<u64>() as f64 / 1000.0,
        "openings_failed": res.iter().map(|r| r.openings_failed).sum::<u64>(),
        "faults": res.iter().fold(std::collections::BTreeMap::<String, u64>::new(), |mut m, r| {
            for (k, v) in &r.faults { *m.entry(k.clone()).or_default() += v; } m }),
        "verdicts": res.iter().fold(std::collections::BTreeMap::<String, u64>::new(), |mut m, r| {
            for (k, v) in &r.verdicts { *m.entry(k.clone()).or_default() += v; } m }),
        "calls_by_exit": res.iter().fold(std::collections::BTreeMap::<String, u64>::new(), |mut m, r| {
            for (k, v) in &r.calls_by_exit { *m.entry(k.clone()).or_default() += v; } m }),
        "decide_src_sha256": audit_flashprove::DECIDE_SRC_SHA256,
    });
    println!("{}", serde_json::to_string(&summary).unwrap());
}

/// The commitment step of one position: fetch the latest drand round, build the record with it,
/// refuse a stale round or a countersignature too close to round seen + 2 (`None`: retry), append
/// to the ledger, and wait for the audit round. Returns the record, root, opening,
/// countersignature and audit round.
fn commit_position(
    ledger: &mut Ledger,
    pins: &Pins,
    sk: &SigningKey,
    t: u64,
    make: impl FnOnce(u64) -> RequestRecord,
) -> Option<(RequestRecord, [u8; 32], RangeOpening, String, DrandRound)> {
    let seen = beacon::fetch(None).expect("latest drand round");
    let rec = make(seen.round);
    // Freshness by the schedule: `seen` must be the current round (not a stale response) and the
    // countersignature must be made before round seen + 2 is emitted, with a second spare.
    let deadline = seen.emitted_at() + beacon::AUDIT_ROUND_MARGIN * beacon::QUICKNET_PERIOD;
    let now = beacon::now_unix();
    if now >= seen.emitted_at() + beacon::QUICKNET_PERIOD + 1 || now + 1 >= deadline {
        eprintln!(
            "position {t}: round {} is stale or the deadline is too close; fetching again",
            seen.round
        );
        return None;
    }
    let mut probe = Ledger::default();
    for r in &ledger.records {
        probe.append(r.clone());
    }
    let (_, root_probe, _) = probe.append(rec.clone());
    let cs = record::countersign(
        sk,
        &record::countersign_msg(&pins.policy, t, &rec.digest(), &root_probe, seen.round),
    );
    if beacon::now_unix() + 1 >= deadline {
        eprintln!(
            "position {t}: countersigned too late for round {}; discarding",
            seen.round + 2
        );
        return None;
    }
    let (pos, root, opening) = ledger.append(rec.clone());
    assert_eq!((pos, root), (t, root_probe));
    let target = seen.round + beacon::AUDIT_ROUND_MARGIN;
    let audit_round = loop {
        match beacon::fetch(Some(target)) {
            Ok(r) => break r,
            Err(_) => std::thread::sleep(Duration::from_millis(1500)),
        }
    };
    Some((rec, root, opening, cs, audit_round))
}

fn requester(kv: &HashMap<String, String>) -> SigningKey {
    let secret: [u8; 32] = match kv.get("requester-key") {
        Some(p) => std::fs::read(p)
            .expect("requester key")
            .try_into()
            .expect("32-byte requester key"),
        None => record::os_random32().expect("OS random source"),
    };
    SigningKey::from_bytes(&secret)
}

fn live(kv: &HashMap<String, String>) {
    let stored = Stored::load(&PathBuf::from(need(kv, "stored"))).expect("stored proof");
    let out = PathBuf::from(need(kv, "out"));
    std::fs::create_dir_all(&out).unwrap();
    let n: u64 = num(kv, "n", 4);
    let false_at: u64 = num(kv, "false-at", n.saturating_sub(1));
    let p_num = decide::p_num_of_ppm(num(kv, "p-ppm", 500_000)).unwrap_or_else(|| {
        eprintln!("fpaudit: --p-ppm must be in 1..=999999");
        std::process::exit(2)
    });
    let sk = requester(kv);
    let session = hex::encode(record::os_random32().expect("OS random source"));
    let pins = Pins {
        policy: Policy {
            session: session.clone(),
            checker: Checker::CpVerify,
            commitment_id: stored.id.clone(),
            build: need(kv, "build").to_string(),
            accept_work: true,
            p_num,
        },
        requester_pk: hex::encode(sk.verifying_key().to_bytes()),
    };
    std::fs::write(
        out.join("pins.json"),
        serde_json::to_vec_pretty(&pins).unwrap(),
    )
    .unwrap();
    let mut ledger = Ledger::default();
    let bin = PathBuf::from(need(kv, "cp-verify"));
    let mut t = 0u64;
    while t < n {
        let false_claim = t == false_at;
        let dir = out.join(format!("files-{t}"));
        std::fs::create_dir_all(&dir).unwrap();
        let mut y = stored.y;
        if false_claim {
            y = (y + 1) % 512;
        }
        std::fs::copy(stored.dir.join("example.req"), dir.join("example.req")).unwrap();
        std::fs::write(dir.join("example.y"), y.to_le_bytes()).unwrap();
        std::fs::copy(stored.dir.join("example.proof"), dir.join("example.proof")).unwrap();
        let (rec, root, opening, cs, audit_round) =
            match commit_position(&mut ledger, &pins, &sk, t, |seen| RequestRecord {
                session: session.clone(),
                position: t,
                nonce: hex::encode(record::os_random32().expect("OS random source")),
                commitment_id: stored.id.clone(),
                r: stored.r,
                e: stored.e,
                req_sha256: record::sha256_file(&dir.join("example.req")).unwrap(),
                y_sha256: record::sha256_file(&dir.join("example.y")).unwrap(),
                proof_sha256: Some(record::sha256_file(&dir.join("example.proof")).unwrap()),
                seen_round: seen,
            }) {
                Some(v) => v,
                None => continue,
            };
        let seen = rec.seen_round;
        let files = CallFiles {
            config: stored.dir.join("config"),
            ivk: stored.dir.join("ivk"),
            req: dir.join("example.req"),
            y: dir.join("example.y"),
            proof: dir.join("example.proof"),
        };
        let scratch = out.join("staging");
        let rc = receipt::audit(&rec, root, opening, cs, audit_round, &pins, || {
            let (sf, st) = runner::stage(&files, &scratch);
            let c = match sf {
                Some(sf) => {
                    runner::run_cp_verify(&bin, &sf, &stored.id, Duration::from_secs(120), 8 << 30)
                }
                None => runner::CallOutcome::not_made(st.fault.clone().unwrap_or_default()),
            };
            (st, c, None)
        })
        .expect("admission");
        let path = out.join(format!("receipt-{t}.json"));
        std::fs::write(&path, serde_json::to_vec_pretty(&rc).unwrap()).unwrap();
        println!(
            "position {t}: seen {} audit round {} coin {:016x} fired {} verdict {:?} alarm {} false-claim {false_claim} -> {}",
            seen,
            rc.beacon.round,
            rc.coin,
            rc.fired,
            rc.verdict,
            rc.alarm,
            path.display()
        );
        t += 1;
    }
}

#[derive(serde::Deserialize)]
struct ExactRequest {
    label: String,
    prompt: Vec<u32>,
    output: Vec<u32>,
}

fn tokens_text(v: &[u32]) -> String {
    v.iter().map(u32::to_string).collect::<Vec<_>>().join(",")
}

fn recompute_argv(kv: &HashMap<String, String>) -> Vec<String> {
    need(kv, "recompute")
        .split_whitespace()
        .map(String::from)
        .collect()
}

fn exact_files(dir: &std::path::Path) -> CallFiles {
    CallFiles {
        config: dir.join("prompt.txt"),
        ivk: dir.join("prompt.txt"),
        req: dir.join("prompt.txt"),
        y: dir.join("output.txt"),
        proof: dir.join("no-proof"),
    }
}

fn exact_live(kv: &HashMap<String, String>) {
    let reqs: Vec<ExactRequest> =
        serde_json::from_slice(&std::fs::read(need(kv, "requests")).expect("requests file"))
            .expect("requests json");
    let out = PathBuf::from(need(kv, "out"));
    std::fs::create_dir_all(&out).unwrap();
    let p_num = decide::p_num_of_ppm(num(kv, "p-ppm", 999_999)).unwrap_or_else(|| {
        eprintln!("fpaudit: --p-ppm must be in 1..=999999");
        std::process::exit(2)
    });
    let argv = recompute_argv(kv);
    let limit = Duration::from_secs(num(kv, "timeout-s", 1800));
    let mem = num(kv, "mem-gib", 192u64) << 30;
    let sk = requester(kv);
    let session = hex::encode(record::os_random32().expect("OS random source"));
    let weights = need(kv, "weights").to_string();
    let pins = Pins {
        policy: Policy {
            session: session.clone(),
            checker: Checker::Exact {
                spec: need(kv, "spec").to_string(),
                params: need(kv, "params").to_string(),
            },
            commitment_id: weights.clone(),
            build: String::new(),
            accept_work: false,
            p_num,
        },
        requester_pk: hex::encode(sk.verifying_key().to_bytes()),
    };
    std::fs::write(
        out.join("pins.json"),
        serde_json::to_vec_pretty(&pins).unwrap(),
    )
    .unwrap();
    let mut ledger = Ledger::default();
    let mut t = 0u64;
    while (t as usize) < reqs.len() {
        let q = &reqs[t as usize];
        let dir = out.join(format!("files-{t}"));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("prompt.txt"), tokens_text(&q.prompt)).unwrap();
        std::fs::write(dir.join("output.txt"), tokens_text(&q.output)).unwrap();
        let (rec, root, opening, cs, audit_round) =
            match commit_position(&mut ledger, &pins, &sk, t, |seen| RequestRecord {
                session: session.clone(),
                position: t,
                nonce: hex::encode(record::os_random32().expect("OS random source")),
                commitment_id: weights.clone(),
                r: q.prompt.len() as u32,
                e: (q.prompt.len() + q.output.len()) as u32,
                req_sha256: record::sha256_file(&dir.join("prompt.txt")).unwrap(),
                y_sha256: record::sha256_file(&dir.join("output.txt")).unwrap(),
                proof_sha256: None,
                seen_round: seen,
            }) {
                Some(v) => v,
                None => continue,
            };
        let files = exact_files(&dir);
        let scratch = out.join("staging");
        let rc = receipt::audit(&rec, root, opening, cs, audit_round, &pins, || {
            let (sf, st) = runner::stage(&files, &scratch);
            match sf {
                Some(sf) => {
                    let o = std::fs::read_to_string(&sf.y).ok();
                    (st, runner::run_recompute(&argv, &sf, limit, mem), o)
                }
                None => {
                    let c = runner::CallOutcome::not_made(st.fault.clone().unwrap_or_default());
                    (st, c, None)
                }
            }
        })
        .expect("admission");
        let path = out.join(format!("receipt-{t}.json"));
        std::fs::write(&path, serde_json::to_vec_pretty(&rc).unwrap()).unwrap();
        println!(
            "position {t} [{}]: seen {} audit round {} coin {:016x} fired {} verdict {:?} alarm {} recompute {:.1}s -> {}",
            q.label,
            rec.seen_round,
            rc.beacon.round,
            rc.coin,
            rc.fired,
            rc.verdict,
            rc.alarm,
            rc.call.as_ref().map_or(0.0, |c| c.millis as f64 / 1000.0),
            path.display()
        );
        t += 1;
    }
}

fn recheck(kv: &HashMap<String, String>, pos: &[String]) {
    let pins: Pins =
        serde_json::from_slice(&std::fs::read(need(kv, "pins")).unwrap()).expect("pins");
    let rerun = match (kv.get("rerun"), kv.get("files"), kv.get("stored")) {
        (Some(b), Some(f), Some(s)) => Some((PathBuf::from(b), PathBuf::from(f), PathBuf::from(s))),
        (None, None, _) | (None, Some(_), None) => None,
        _ => {
            eprintln!("fpaudit recheck: --rerun needs --files and --stored");
            std::process::exit(2)
        }
    };
    let recompute = kv
        .get("recompute")
        .map(|_| (recompute_argv(kv), PathBuf::from(need(kv, "files"))));
    let mut bad = 0;
    let mut seen_positions: HashMap<u64, String> = HashMap::new();
    for p in pos {
        let r: Receipt = serde_json::from_slice(&std::fs::read(p).unwrap()).expect("receipt json");
        if let Some(prev) = seen_positions.insert(r.record.position, r.record_digest.clone())
            && prev != r.record_digest
        {
            println!(
                "{p}: FAIL two receipts open position {} to different records",
                r.record.position
            );
            bad += 1;
            continue;
        }
        match receipt::recheck(&r, &pins) {
            Ok(rep) => {
                print!("{p}: OK {}", serde_json::to_string(&rep).unwrap());
                if let Some((bin, files, stored)) = &rerun {
                    let dir = files.join(format!("files-{}", r.record.position));
                    let f = CallFiles {
                        config: stored.join("config"),
                        ivk: stored.join("ivk"),
                        req: dir.join("example.req"),
                        y: dir.join("example.y"),
                        proof: dir.join("example.proof"),
                    };
                    match receipt::rerun(
                        &r,
                        &pins,
                        receipt::RerunWith::CpVerify(bin),
                        &f,
                        &std::env::temp_dir().join("fpaudit-rerun"),
                    ) {
                        Ok(v) if !r.fired || Some(v) == r.verdict => print!(" rerun {v:?}"),
                        Ok(v) => {
                            print!(" RERUN DISAGREES {v:?}");
                            bad += 1;
                        }
                        Err(e) => {
                            print!(" rerun failed: {e}");
                            bad += 1;
                        }
                    }
                }
                if let Some((argv, files)) = &recompute {
                    let f = exact_files(&files.join(format!("files-{}", r.record.position)));
                    match receipt::rerun(
                        &r,
                        &pins,
                        receipt::RerunWith::Recompute(argv),
                        &f,
                        &std::env::temp_dir().join("fpaudit-rerun"),
                    ) {
                        Ok(v) if !r.fired || Some(v) == r.verdict => print!(" recompute {v:?}"),
                        Ok(v) => {
                            print!(" RECOMPUTE DISAGREES {v:?}");
                            bad += 1;
                        }
                        Err(e) => {
                            print!(" recompute failed: {e}");
                            bad += 1;
                        }
                    }
                }
                println!();
            }
            Err(e) => {
                println!("{p}: FAIL {e}");
                bad += 1;
            }
        }
    }
    std::process::exit(if bad == 0 { 0 } else { 1 });
}

fn main() {
    let (cmd, kv, pos) = args();
    match cmd.as_str() {
        "experiment" => experiment(&kv),
        "live" => live(&kv),
        "exact-live" => exact_live(&kv),
        "recheck" => recheck(&kv, &pos),
        _ => {
            eprintln!(
                "usage: fpaudit experiment|live|exact-live|recheck ... (see the source header)"
            );
            std::process::exit(2);
        }
    }
}
