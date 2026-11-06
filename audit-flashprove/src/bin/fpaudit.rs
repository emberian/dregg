//! `fpaudit`: the commit-then-audit auditor over FlashProve's `cp_verify`.
//!
//!   fpaudit experiment --stored DIR --cp-verify BIN --build HEX --work DIR --out FILE
//!                      --p-ppm N --seeds N --base-round R --drand-cache FILE
//!                      [--strategy rate:F | burst:F:K] [--arm closed|open|peek]
//!                      [--horizon-mult M] [--threads T] [--timeout-s S] [--mem-gib G]
//!   fpaudit live --stored DIR --cp-verify BIN --build HEX --out DIR --p-ppm N --n N
//!   fpaudit recheck --pins FILE RECEIPT... [--rerun BIN --stored DIR]
//!
//! `live` serves `n` requests from the stored proof (the last one with a false next token), has a
//! requester countersign each commitment with the latest drand round it has seen, waits for round
//! seen + 2, and audits: receipts and the pins a re-checker needs are written under `--out`.

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use audit_flashprove::beacon::{self, DrandRound};
use audit_flashprove::experiment::{self, Arm, Config, Stored, Strategy};
use audit_flashprove::receipt::{self, Ledger, Pins, Receipt};
use audit_flashprove::record::{self, RequestRecord};
use audit_flashprove::runner::{self, CallFiles};

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
    let p_num = beacon::p_num_ppm(p_ppm);
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
        "p_ppm": p_ppm, "p_num": p_num, "one_over_q": 1.0 / p, "strategy": format!("{strategy:?}"),
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
        "verdicts": res.iter().fold(std::collections::BTreeMap::<String, u64>::new(), |mut m, r| {
            for (k, v) in &r.verdicts { *m.entry(k.clone()).or_default() += v; } m }),
        "calls_by_exit": res.iter().fold(std::collections::BTreeMap::<String, u64>::new(), |mut m, r| {
            for (k, v) in &r.calls_by_exit { *m.entry(k.clone()).or_default() += v; } m }),
        "decide_src_sha256": audit_flashprove::DECIDE_SRC_SHA256,
    });
    println!("{}", serde_json::to_string(&summary).unwrap());
}

fn live(kv: &HashMap<String, String>) {
    use ed25519_dalek::SigningKey;
    let stored = Stored::load(&PathBuf::from(need(kv, "stored"))).expect("stored proof");
    let out = PathBuf::from(need(kv, "out"));
    std::fs::create_dir_all(&out).unwrap();
    let n: u64 = num(kv, "n", 4);
    let p_num = beacon::p_num_ppm(num(kv, "p-ppm", 500_000));
    let mut seed = [0u8; 32];
    let now = format!("{:?}", std::time::SystemTime::now());
    seed.copy_from_slice(blake3::hash(now.as_bytes()).as_bytes());
    let sk = SigningKey::from_bytes(&seed);
    let pins = Pins {
        commitment_id: stored.id.clone(),
        build: need(kv, "build").to_string(),
        accept_work: true,
        p_num,
        requester_pk: hex::encode(sk.verifying_key().to_bytes()),
    };
    std::fs::write(
        out.join("pins.json"),
        serde_json::to_vec_pretty(&pins).unwrap(),
    )
    .unwrap();
    let mut ledger = Ledger::default();
    let bin = PathBuf::from(need(kv, "cp-verify"));
    for t in 0..n {
        let false_claim = t == n - 1;
        let dir = out.join(format!("files-{t}"));
        std::fs::create_dir_all(&dir).unwrap();
        let mut y = stored.y;
        if false_claim {
            y = (y + 1) % 512;
        }
        std::fs::copy(stored.dir.join("example.req"), dir.join("example.req")).unwrap();
        std::fs::write(dir.join("example.y"), y.to_le_bytes()).unwrap();
        std::fs::copy(stored.dir.join("example.proof"), dir.join("example.proof")).unwrap();
        let seen = beacon::fetch(None).expect("latest drand round");
        let rec = RequestRecord {
            position: t,
            nonce: hex::encode(blake3::hash(format!("{now}/{t}").as_bytes()).as_bytes()),
            commitment_id: stored.id.clone(),
            r: stored.r,
            e: stored.e,
            req_sha256: record::sha256_file(&dir.join("example.req")).unwrap(),
            y_sha256: record::sha256_file(&dir.join("example.y")).unwrap(),
            proof_sha256: Some(record::sha256_file(&dir.join("example.proof")).unwrap()),
            seen_round: seen.round,
        };
        let (pos, root, opening) = ledger.append(rec.clone());
        let digest = rec.digest();
        let cs = record::countersign(
            &sk,
            &record::countersign_msg(pos, &digest, &root, seen.round),
        );
        // wait for the audit round, which did not exist when the requester countersigned
        let target = seen.round + beacon::AUDIT_ROUND_MARGIN;
        let audit_round = loop {
            match beacon::fetch(Some(target)) {
                Ok(r) => break r,
                Err(_) => std::thread::sleep(Duration::from_millis(1500)),
            }
        };
        let files = CallFiles {
            config: stored.dir.join("config"),
            ivk: stored.dir.join("ivk"),
            req: dir.join("example.req"),
            y: dir.join("example.y"),
            proof: dir.join("example.proof"),
        };
        let staged_dir = out.join(format!("staged-{t}"));
        let rc = receipt::audit(&rec, root, opening, cs, audit_round, &pins, || {
            let (sf, st) = runner::stage(&files, &staged_dir).expect("stage files");
            (
                st,
                runner::run_cp_verify(&bin, &sf, &stored.id, Duration::from_secs(120), 8 << 30),
            )
        });
        let path = out.join(format!("receipt-{t}.json"));
        std::fs::write(&path, serde_json::to_vec_pretty(&rc).unwrap()).unwrap();
        println!(
            "position {t}: seen {} audit round {} coin {:016x} fired {} verdict {:?} alarm {} false-claim {false_claim} -> {}",
            seen.round,
            rc.beacon.round,
            rc.coin,
            rc.fired,
            rc.verdict,
            rc.alarm,
            path.display()
        );
    }
}

fn recheck(kv: &HashMap<String, String>, pos: &[String]) {
    let pins: Pins =
        serde_json::from_slice(&std::fs::read(need(kv, "pins")).unwrap()).expect("pins");
    let mut bad = 0;
    for p in pos {
        let r: Receipt = serde_json::from_slice(&std::fs::read(p).unwrap()).expect("receipt json");
        match receipt::recheck(&r, &pins) {
            Ok(rep) => {
                print!("{p}: OK {}", serde_json::to_string(&rep).unwrap());
                if let (Some(bin), Some(dir)) = (kv.get("rerun"), kv.get("files")) {
                    let dir = PathBuf::from(dir).join(format!("files-{}", r.record.position));
                    let stored = PathBuf::from(need(kv, "stored"));
                    let f = CallFiles {
                        config: stored.join("config"),
                        ivk: stored.join("ivk"),
                        req: dir.join("example.req"),
                        y: dir.join("example.y"),
                        proof: dir.join("example.proof"),
                    };
                    match receipt::rerun(&r, &pins, &PathBuf::from(bin), &f) {
                        Ok(v) if Some(v) == r.verdict || !r.fired => print!(" rerun {v:?}"),
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
        "recheck" => recheck(&kv, &pos),
        _ => {
            eprintln!("usage: fpaudit experiment|live|recheck ... (see the source header)");
            std::process::exit(2);
        }
    }
}
