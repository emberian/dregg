//! The measurement: corrupt rounds before the first alarm, against `1/q`, over real `cp_verify`
//! calls on FlashProve's stored exact-match proof.
//!
//! Every fired audit is a real call on real files; nothing is cached. The population is replays
//! of one stored proof made distinct by nonce and position (we hold two exact-match proofs and no
//! H100 to make more). A corrupt round serves a FALSE claim (another next token, or another
//! checked reply token) with the honest proof, no proof, or a hostile proof file; altering proof
//! bytes alone never counts as corruption, because FlashProve's verifier may accept proof
//! alterations that leave the claim true (their `lean/THEOREM.md`, "Altered proof files").
//!
//! The coin of position `t` in seed `s` is `beacon::coin(session_s, sig_s, t)` under one
//! HISTORICAL drand round per seed: this is a simulation of fresh coins, not a deployment. Every
//! coin of a seed is computable from its one public signature; the closed-arm schedules never read
//! it (they read separate-domain hashes and the past fire decisions), the `peek` arm reads exactly
//! the current coin, as the ordering falsifier. The `live` path of the binary uses one future round
//! per request. The mean count is reported against the ideal `1/p`, which is the bound of
//! `Selvage/AuditFlashProve.lean` with `εbeacon = 0` and its `n·(δchk + δbind)` correction (not
//! estimated here: no false claim is ever accepted in these runs, which is a count, not a bound
//! on `δ`); a seed that reaches the horizon is censored and counted as such.

use std::path::{Path, PathBuf};
use std::time::Duration;

use serde::{Deserialize, Serialize};

use crate::beacon::{self, DrandRound};
use crate::decide::{self, Expect, Verdict};
use crate::receipt::{self, Ledger};
use crate::record::RequestRecord;
use crate::runner::{self, CallFiles};

/// The stored proof the population replays.
#[derive(Clone, Debug)]
pub struct Stored {
    pub dir: PathBuf,
    pub id: String,
    pub r: u32,
    pub e: u32,
    pub req_words: Vec<u32>,
    pub y: u32,
    pub proof_sha256: String,
}

impl Stored {
    pub fn load(dir: &Path) -> Result<Stored, String> {
        let rd = |n: &str| std::fs::read(dir.join(n)).map_err(|e| format!("{n}: {e}"));
        let words = |b: Vec<u8>| -> Vec<u32> {
            b.chunks_exact(4)
                .map(|c| u32::from_le_bytes(c.try_into().unwrap()))
                .collect()
        };
        let req = words(rd("example.req")?);
        let y = words(rd("example.y")?);
        let n = req.len();
        if n < 3 || y.len() != 1 {
            return Err("unexpected request/token file shape".into());
        }
        let id = String::from_utf8_lossy(&rd("ID.txt")?).trim().to_string();
        let proof_sha256 =
            crate::record::sha256_file(&dir.join("example.proof")).map_err(|e| e.to_string())?;
        Ok(Stored {
            dir: dir.into(),
            id,
            r: req[n - 2],
            e: req[n - 1],
            req_words: req,
            y: y[0],
            proof_sha256,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Kind {
    Honest,
    /// Another next token than the model's.
    YToken,
    /// Another token at a checked reply position.
    ReplyToken,
    /// A false claim (another next token) and no proof.
    Withheld,
    /// A false claim (another next token) committed with the honest proof's digest, but at audit
    /// time the provider hands a symlink to /dev/zero: an equivocation the opening check catches.
    Equivocate,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Arm {
    /// The exported fail-closed `alarm`.
    Closed,
    /// The fail-open falsifier `alarmOpen`; corruptions are only `withheld`.
    Open,
    /// Fail-closed, but the adversary reads the current round's coin before committing
    /// (commit after the beacon): the ordering falsifier.
    Peek,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Strategy {
    /// Corrupt iff BLAKE3(seed, t) < f: a schedule fixed in advance.
    Rate(f64),
    /// Rate `f`, plus: corrupt the next `k` rounds after any round whose audit fired (a gambler
    /// betting that audits do not come in pairs).
    Burst(f64, u32),
}

#[derive(Clone, Debug)]
pub struct Config {
    pub cp_verify: PathBuf,
    pub stored: Stored,
    pub build: String,
    pub work: PathBuf,
    pub p_num: u64,
    pub strategy: Strategy,
    pub arm: Arm,
    pub horizon: u64,
    pub timeout: Duration,
    pub mem_bytes: u64,
}

/// One seed's outcome.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct SeedResult {
    pub seed: u64,
    pub drand_round: u64,
    pub rounds: u64,
    pub corrupt_before_alarm: u64,
    pub alarmed: bool,
    pub hit_horizon: bool,
    pub fired: u64,
    pub calls: u64,
    pub calls_by_exit: std::collections::BTreeMap<String, u64>,
    pub fired_corrupt_accepted: u64,
    pub fired_honest_not_accepted: u64,
    pub alarm_kind: Option<Kind>,
    pub call_millis: u64,
    pub openings_failed: u64,
    /// `kind/verdict` counts over fired audits.
    pub verdicts: std::collections::BTreeMap<String, u64>,
    pub faults: std::collections::BTreeMap<String, u64>,
}

fn unit_hash(seed: u64, t: u64, tag: &str) -> f64 {
    let mut h = blake3::Hasher::new_derive_key("dregg audit-flashprove 2026-11-06 adversary v1");
    h.update(tag.as_bytes());
    h.update(&seed.to_le_bytes());
    h.update(&t.to_le_bytes());
    let x = u64::from_le_bytes(h.finalize().as_bytes()[..8].try_into().unwrap());
    (x as f64) / (u64::MAX as f64 + 1.0)
}

fn pick_kind(arm: Arm, seed: u64, t: u64) -> Kind {
    let u = unit_hash(seed, t, "kind");
    match arm {
        Arm::Open => Kind::Withheld,
        _ => {
            if u < 0.4 {
                Kind::YToken
            } else if u < 0.8 {
                Kind::ReplyToken
            } else if u < 0.9 {
                Kind::Withheld
            } else {
                Kind::Equivocate
            }
        }
    }
}

/// The bytes of one round's request and token files.
fn payload(s: &Stored, kind: Kind, seed: u64, t: u64) -> (Vec<u8>, Vec<u8>) {
    let mut req = s.req_words.clone();
    let mut y = s.y;
    let other = |v: u32| -> u32 { (v + 1 + (unit_hash(seed, t, "tok") * 400.0) as u32) % 512 };
    match kind {
        Kind::YToken | Kind::Withheld | Kind::Equivocate => y = other(y),
        Kind::ReplyToken => {
            // a checked reply position r+1 ..= e-1 (request word indices)
            let lo = s.r as usize + 1;
            let hi = s.e as usize - 1;
            let span = (hi - lo + 1) as f64;
            let i = lo + ((unit_hash(seed, t, "pos") * span) as usize).min(hi - lo);
            req[i] = other(req[i]);
        }
        Kind::Honest => {}
    }
    let enc = |w: &[u32]| w.iter().flat_map(|x| x.to_le_bytes()).collect::<Vec<u8>>();
    (enc(&req), enc(&[y]))
}

fn sha(b: &[u8]) -> String {
    use sha2::{Digest, Sha256};
    hex::encode(Sha256::digest(b))
}

/// The record the provider commits to for this round (before the coin).
fn commit(
    s: &Stored,
    session: &str,
    kind: Kind,
    seed: u64,
    t: u64,
    seen_round: u64,
) -> RequestRecord {
    let (req, y) = payload(s, kind, seed, t);
    RequestRecord {
        session: session.to_string(),
        position: t,
        nonce: format!("{seed}/{t}"),
        commitment_id: s.id.clone(),
        r: s.r,
        e: s.e,
        req_sha256: sha(&req),
        y_sha256: sha(&y),
        proof_sha256: if kind == Kind::Withheld {
            None
        } else {
            Some(s.proof_sha256.clone())
        },
        seen_round,
    }
}

/// Write the files the provider hands over at audit time under `dir`.
fn hand_over(s: &Stored, kind: Kind, dir: &Path, seed: u64, t: u64) -> std::io::Result<CallFiles> {
    std::fs::create_dir_all(dir)?;
    let (req, y) = payload(s, kind, seed, t);
    let reqp = dir.join("example.req");
    let yp = dir.join("example.y");
    std::fs::write(&reqp, req)?;
    std::fs::write(&yp, y)?;
    let proof = dir.join("example.proof");
    let _ = std::fs::remove_file(&proof);
    match kind {
        Kind::Withheld => {}
        Kind::Equivocate => std::os::unix::fs::symlink("/dev/zero", &proof)?,
        _ => std::os::unix::fs::symlink(s.dir.join("example.proof"), &proof)?,
    }
    Ok(CallFiles {
        config: s.dir.join("config"),
        ivk: s.dir.join("ivk"),
        req: reqp,
        y: yp,
        proof,
    })
}

/// Run one seed to its first alarm or the horizon.
pub fn run_seed(cfg: &Config, seed: u64, beacon: &DrandRound) -> SeedResult {
    let mut res = SeedResult {
        seed,
        drand_round: beacon.round,
        ..Default::default()
    };
    let expect = Expect {
        id: cfg.stored.id.clone(),
        build: cfg.build.clone(),
        r: cfg.stored.r,
        e: cfg.stored.e,
        accept_work: true,
    };
    let dir = cfg.work.join(format!("seed-{seed}"));
    let session = hex::encode(
        blake3::hash(format!("experiment seed {seed} round {}", beacon.round).as_bytes())
            .as_bytes(),
    );
    let mut ledger = Ledger::default();
    let mut burst_left = 0u32;
    for t in 0..cfg.horizon {
        res.rounds = t + 1;
        let coin = beacon::coin(&session, &beacon.signature, t).expect("verified drand signature");
        let fired = decide::fires(coin, cfg.p_num);
        let corrupt = match cfg.arm {
            // commits AFTER seeing the coin: cheats exactly when the audit will not fire
            Arm::Peek => !fired,
            _ => match cfg.strategy {
                Strategy::Rate(f) => unit_hash(seed, t, "corrupt") < f,
                Strategy::Burst(f, _) => burst_left > 0 || unit_hash(seed, t, "corrupt") < f,
            },
        };
        burst_left = burst_left.saturating_sub(1);
        let kind = if corrupt {
            pick_kind(cfg.arm, seed, t)
        } else {
            Kind::Honest
        };
        let rec = commit(
            &cfg.stored,
            &session,
            kind,
            seed,
            t,
            beacon.round - beacon::AUDIT_ROUND_MARGIN,
        );
        let (_, root, opening) = ledger.append(rec.clone());
        if corrupt {
            res.corrupt_before_alarm += 1;
        }
        if !fired {
            continue;
        }
        res.fired += 1;
        if let Strategy::Burst(_, k) = cfg.strategy {
            burst_left = k;
        }
        let handed =
            hand_over(&cfg.stored, kind, &dir.join("handed"), seed, t).unwrap_or_else(|e| {
                panic!("seed {seed} round {t}: cannot write the handed files: {e}")
            });
        let (files, staged) = runner::stage(&handed, &dir.join("staged"));
        let open_ok = receipt::opening_ok(&rec, &staged, &root, &opening);
        if !open_ok {
            res.openings_failed += 1;
        }
        let call = match files {
            Some(f) => runner::run_cp_verify(
                &cfg.cp_verify,
                &f,
                &cfg.stored.id,
                cfg.timeout,
                cfg.mem_bytes,
            ),
            None => runner::CallOutcome::not_made(staged.fault.clone().unwrap_or_default()),
        };
        if let Some(f) = &call.fault {
            *res.faults.entry(f.chars().take(60).collect()).or_default() += 1;
        }
        res.calls += 1;
        res.call_millis += call.millis;
        let key = call.exit.map_or_else(
            || {
                if call.killed_for_time {
                    "timeout".into()
                } else {
                    "signal".into()
                }
            },
            |c| c.to_string(),
        );
        *res.calls_by_exit.entry(key).or_default() += 1;
        let v = decide::verdict(open_ok, call.stdout.as_bytes(), call.exit, &expect);
        *res.verdicts.entry(format!("{kind:?}/{v:?}")).or_default() += 1;
        if corrupt && v == Verdict::Accept {
            res.fired_corrupt_accepted += 1;
        }
        if !corrupt && v != Verdict::Accept {
            res.fired_honest_not_accepted += 1;
        }
        let alarm = match cfg.arm {
            Arm::Open => decide::alarm_open(true, v),
            _ => decide::alarm(true, v),
        };
        if alarm {
            res.alarmed = true;
            res.alarm_kind = Some(kind);
            break;
        }
    }
    res.hit_horizon = !res.alarmed;
    let _ = std::fs::remove_dir_all(&dir);
    res
}
