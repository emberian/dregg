//! The audit receipt and its offline re-check.
//!
//! What a receipt establishes offline, with no trust in the auditor's host: the record opens at its
//! position under the root; the requester countersigned the policy, the position, the record, the
//! root and the round it had seen; the audit round is that round plus two and carries a valid drand
//! signature; the coin, the fire decision, the opening check, the verdict and the alarm follow from
//! those through the same compiled Lean. What it does NOT establish: that the stored `cp_verify`
//! output is what `cp_verify` printed (an auditor can fabricate an accepting transcript; acceptance
//! evidence is [`rerun`] on the committed files), and that the requester countersigned before the
//! audit round was published (a historical round verifies as well as a fresh one; ordering needs a
//! timestamp or publication witness, and is the `εbeacon` residual of the Lean instance).

use dregg_query::mmr::{Blake3Mmr, Mmr, RangeOpening, verify_range};
use serde::{Deserialize, Serialize};

use crate::beacon::{self, DrandRound};
use crate::decide::{self, ExactExpect, Expect, Verdict};
use crate::record::{self, Checker, Policy, RequestRecord};
use crate::runner::{self, CallFiles, CallOutcome, Staged};

pub const RECEIPT_VERSION: &str = "fpaudit-receipt-v3";

/// What a re-checker pins for itself, never taking it from the receipt.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Pins {
    pub policy: Policy,
    pub requester_pk: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Receipt {
    pub version: String,
    pub decide_src_sha256: String,
    pub record: RequestRecord,
    pub record_digest: String,
    /// The MMR root right after this record was appended; it pins the log length position + 1.
    pub mmr_root: String,
    pub opening: RangeOpening,
    pub countersig: String,
    pub beacon: DrandRound,
    pub coin: u64,
    pub fired: bool,
    pub expect: Expect,
    /// The digests of the files the auditor staged (when fired).
    pub staged: Option<Staged>,
    /// The Lean opening check (when fired).
    pub open_ok: Option<bool>,
    pub call: Option<CallOutcome>,
    /// Exact checker: the committed output tokens as staged (when fired and staged); its SHA-256
    /// is the staged token digest the opening check compared with the record.
    pub committed_output: Option<String>,
    pub verdict: Option<Verdict>,
    pub alarm: bool,
}

/// The auditor's state: the MMR of record digests and the records.
pub struct Ledger {
    pub mmr: Mmr<Blake3Mmr>,
    pub records: Vec<RequestRecord>,
}

impl Default for Ledger {
    fn default() -> Self {
        Ledger {
            mmr: Mmr::new(Blake3Mmr),
            records: Vec::new(),
        }
    }
}

impl Ledger {
    /// The commitment step: append, and return (position, root, opening).
    pub fn append(&mut self, rec: RequestRecord) -> (u64, [u8; 32], RangeOpening) {
        assert_eq!(
            rec.position,
            self.mmr.len(),
            "record position must be the next MMR slot"
        );
        let pos = self.mmr.push(rec.digest());
        self.records.push(rec);
        let root = self.mmr.root();
        let (_, opening) = self.mmr.open_range(pos, pos);
        (pos, root, opening)
    }
}

/// Positions are bounded well below `u64::MAX` so no MMR arithmetic can overflow.
pub const MAX_POSITION: u64 = 1 << 48;

fn mmr_ok(rec: &RequestRecord, root: &[u8; 32], opening: &RangeOpening) -> bool {
    rec.position < MAX_POSITION
        && verify_range(
            &Blake3Mmr,
            root,
            rec.position,
            rec.position,
            &[rec.digest()],
            opening,
        )
        .is_ok_and(|len| len == rec.position + 1)
}

/// The Lean opening check over a stage outcome.
pub fn opening_ok(
    rec: &RequestRecord,
    staged: &Staged,
    root: &[u8; 32],
    opening: &RangeOpening,
) -> bool {
    decide::opening_ok(
        staged.fault.is_none(),
        mmr_ok(rec, root, opening),
        &rec.req_sha256,
        &rec.y_sha256,
        staged.req_sha256.as_deref().unwrap_or(""),
        staged.y_sha256.as_deref().unwrap_or(""),
        rec.proof_sha256.as_deref(),
        staged.proof_sha256.as_deref(),
    )
}

fn expect_of(pins: &Pins, rec: &RequestRecord) -> Expect {
    Expect {
        id: pins.policy.commitment_id.clone(),
        build: pins.policy.build.clone(),
        r: rec.r,
        e: rec.e,
        accept_work: pins.policy.accept_work,
    }
}

/// The checker's verdict through the compiled Lean the policy names.
fn verdict_of(
    pins: &Pins,
    rec: &RequestRecord,
    open_ok: bool,
    c: &CallOutcome,
    committed_output: Option<&str>,
) -> Verdict {
    match &pins.policy.checker {
        Checker::CpVerify => {
            decide::verdict(open_ok, c.stdout.as_bytes(), c.exit, &expect_of(pins, rec))
        }
        Checker::Exact { spec, params } => decide::exact_verdict(
            open_ok,
            c.stdout.as_bytes(),
            c.exit,
            &ExactExpect {
                spec: spec.clone(),
                params: params.clone(),
                weights: pins.policy.commitment_id.clone(),
                prompt_len: rec.r,
                output: committed_output.unwrap_or("").to_string(),
            },
        ),
    }
}

fn sha256_hex(b: &[u8]) -> String {
    use sha2::{Digest, Sha256};
    hex::encode(Sha256::digest(b))
}

fn ensure(cond: bool, what: &str) -> Result<(), String> {
    if cond {
        Ok(())
    } else {
        Err(format!("recheck: {what}"))
    }
}

/// The checks that precede a decision, shared by [`audit`] and [`recheck`]: the record belongs to
/// the pinned session and commitment, the countersignature verifies, the round is seen + 2 and its
/// signature verifies. Returns the coin.
fn admit(
    rec: &RequestRecord,
    root: &[u8; 32],
    countersig: &str,
    b: &DrandRound,
    pins: &Pins,
) -> Result<u64, String> {
    ensure(
        rec.session == pins.policy.session,
        "the record is not of the pinned session",
    )?;
    ensure(
        rec.commitment_id == pins.policy.commitment_id,
        "the record names another commitment ID",
    )?;
    ensure(rec.position < MAX_POSITION, "position out of range")?;
    record::verify_countersign(
        &pins.requester_pk,
        &record::countersign_msg(
            &pins.policy,
            rec.position,
            &rec.digest(),
            root,
            rec.seen_round,
        ),
        countersig,
    )
    .map_err(|e| format!("countersignature: {e}"))?;
    ensure(
        decide::round_ok(rec.seen_round, b.round),
        "the beacon round is not the requester's seen round + 2",
    )?;
    b.verify()?;
    beacon::coin(&pins.policy.session, &b.signature, rec.position)
}

/// Decide one audit and build its receipt. `run` is called only if the audit fires; it stages the
/// provider's files and, if staging succeeded, calls the checker on the staged copies. It returns
/// the staged token file's contents too (the exact checker compares the recompute with them).
pub fn audit(
    rec: &RequestRecord,
    root: [u8; 32],
    opening: RangeOpening,
    countersig: String,
    beacon: DrandRound,
    pins: &Pins,
    run: impl FnOnce() -> (Staged, CallOutcome, Option<String>),
) -> Result<Receipt, String> {
    let coin = admit(rec, &root, &countersig, &beacon, pins)?;
    let fired = decide::fires(coin, pins.policy.p_num);
    let expect = expect_of(pins, rec);
    let (staged, open_ok, call, committed_output, verdict) = if fired {
        let (st, c, out) = run();
        // The output the exact checker compares against is the staged one, and only if its digest
        // is the staged digest the opening check compares with the record.
        let out = out.filter(|o| st.y_sha256.as_deref() == Some(sha256_hex(o.as_bytes()).as_str()));
        let ok = opening_ok(rec, &st, &root, &opening);
        let v = verdict_of(pins, rec, ok, &c, out.as_deref());
        (Some(st), Some(ok), Some(c), out, Some(v))
    } else {
        (None, None, None, None, None)
    };
    let alarm = decide::alarm(fired, verdict.unwrap_or(Verdict::NoVerdict));
    Ok(Receipt {
        version: RECEIPT_VERSION.into(),
        decide_src_sha256: crate::DECIDE_SRC_SHA256.into(),
        record: rec.clone(),
        record_digest: hex::encode(rec.digest()),
        mmr_root: hex::encode(root),
        opening,
        countersig,
        beacon,
        coin,
        fired,
        expect,
        staged,
        open_ok,
        call,
        committed_output,
        verdict,
        alarm,
    })
}

/// Everything [`recheck`] established.
#[derive(Debug, Serialize)]
pub struct RecheckReport {
    pub position: u64,
    pub audit_round: u64,
    pub fired: bool,
    pub open_ok: Option<bool>,
    pub verdict: Option<Verdict>,
    pub alarm: bool,
}

/// Re-derive every field of the receipt offline. Any disagreement is an error.
pub fn recheck(r: &Receipt, pins: &Pins) -> Result<RecheckReport, String> {
    ensure(r.version == RECEIPT_VERSION, "unknown receipt version")?;
    ensure(
        r.decide_src_sha256 == crate::DECIDE_SRC_SHA256,
        "the receipt was decided by another Lean decision source than this binary was built from",
    )?;
    let digest = r.record.digest();
    ensure(hex::encode(digest) == r.record_digest, "record digest")?;
    let root: [u8; 32] = hex::decode(&r.mmr_root)
        .map_err(|e| e.to_string())?
        .try_into()
        .map_err(|_| "root length".to_string())?;
    ensure(
        mmr_ok(&r.record, &root, &r.opening),
        "the record does not open at its position under the root",
    )?;
    let coin = admit(&r.record, &root, &r.countersig, &r.beacon, pins)?;
    ensure(coin == r.coin, "coin")?;
    let fired = decide::fires(coin, pins.policy.p_num);
    ensure(fired == r.fired, "fire decision")?;
    let expect = expect_of(pins, &r.record);
    ensure(
        expect == r.expect,
        "the receipt's expectations are not the pinned ones",
    )?;
    let (open_ok, verdict) = match (&r.call, &r.staged, fired) {
        (Some(c), Some(st), true) => {
            ensure(
                !(c.killed_for_time && c.exit.is_some()),
                "a call killed for time cannot carry an exit status",
            )?;
            ensure(
                st.fault.is_none() || c.exit.is_none(),
                "a failed stage cannot carry a call result",
            )?;
            if let Some(o) = &r.committed_output {
                ensure(
                    st.y_sha256.as_deref() == Some(sha256_hex(o.as_bytes()).as_str()),
                    "the committed output is not the staged token file",
                )?;
            }
            let ok = opening_ok(&r.record, st, &root, &r.opening);
            (
                Some(ok),
                Some(verdict_of(
                    pins,
                    &r.record,
                    ok,
                    c,
                    r.committed_output.as_deref(),
                )),
            )
        }
        (None, None, false) => {
            ensure(
                r.committed_output.is_none(),
                "an unfired audit carries no output",
            )?;
            (None, None)
        }
        _ => {
            return Err(
                "recheck: a call and staged digests are present iff the audit fired".into(),
            );
        }
    };
    ensure(open_ok == r.open_ok, "opening check")?;
    ensure(verdict == r.verdict, "verdict")?;
    let alarm = decide::alarm(fired, verdict.unwrap_or(Verdict::NoVerdict));
    ensure(alarm == r.alarm, "alarm")?;
    Ok(RecheckReport {
        position: r.record.position,
        audit_round: r.beacon.round,
        fired,
        open_ok,
        verdict,
        alarm,
    })
}

/// How a re-checker calls the checker again: `cp_verify` at a path, or the recompute command.
pub enum RerunWith<'a> {
    CpVerify(&'a std::path::Path),
    Recompute(&'a [String]),
}

/// Acceptance evidence: stage the files the re-checker holds, check them against the record, call
/// the checker again, and return the verdict the compiled Lean gives on the fresh output.
pub fn rerun(
    r: &Receipt,
    pins: &Pins,
    with: RerunWith<'_>,
    f: &CallFiles,
    scratch: &std::path::Path,
) -> Result<Verdict, String> {
    let root: [u8; 32] = hex::decode(&r.mmr_root)
        .map_err(|e| e.to_string())?
        .try_into()
        .map_err(|_| "root".to_string())?;
    let (files, st) = runner::stage(f, scratch);
    let ok = opening_ok(&r.record, &st, &root, &r.opening);
    let out = files
        .as_ref()
        .and_then(|sf| std::fs::read_to_string(&sf.y).ok())
        .filter(|o| st.y_sha256.as_deref() == Some(sha256_hex(o.as_bytes()).as_str()));
    let c = match (files, with) {
        (Some(sf), RerunWith::CpVerify(bin)) => runner::run_cp_verify(
            bin,
            &sf,
            &pins.policy.commitment_id,
            std::time::Duration::from_secs(600),
            16 << 30,
        ),
        (Some(sf), RerunWith::Recompute(argv)) => {
            runner::run_recompute(argv, &sf, std::time::Duration::from_secs(1800), 192 << 30)
        }
        (None, _) => CallOutcome::not_made(st.fault.clone().unwrap_or_default()),
    };
    Ok(verdict_of(pins, &r.record, ok, &c, out.as_deref()))
}
