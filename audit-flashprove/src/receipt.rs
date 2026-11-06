//! The audit receipt and its offline re-check.
//!
//! A receipt is checkable with no trust in the auditor's host: the MMR opening pins the record
//! under the root, the requester's countersignature pins the root and the round it had seen, the
//! drand signature pins the coin, and the fire decision, the verdict and the alarm are re-derived
//! from the stored `cp_verify` output through the same compiled Lean. What a re-checker takes on
//! the auditor's word is only that the stored output is what `cp_verify` printed; with the files
//! (whose SHA-256 the record commits to) [`rerun`] calls `cp_verify` again.

use dregg_query::mmr::{Blake3Mmr, Mmr, RangeOpening, verify_range};
use serde::{Deserialize, Serialize};

use crate::beacon::{self, DrandRound};
use crate::decide::{self, Expect, Verdict};
use crate::record::{self, RequestRecord};
use crate::runner::{self, CallFiles, CallOutcome, Staged};

pub const RECEIPT_VERSION: &str = "fpaudit-receipt-v1";

/// What a re-checker pins for itself, never taking it from the receipt.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Pins {
    pub commitment_id: String,
    pub build: String,
    pub accept_work: bool,
    pub p_num: u64,
    pub requester_pk: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Receipt {
    pub version: String,
    pub decide_src_sha256: String,
    pub p_num: u64,
    pub record: RequestRecord,
    pub record_digest: String,
    /// The MMR root right after this record was appended, and the log length it pins.
    pub mmr_root: String,
    pub mmr_len: u64,
    pub opening: RangeOpening,
    pub countersig: String,
    pub beacon: DrandRound,
    pub coin: u64,
    pub fired: bool,
    pub expect: Expect,
    /// The digests of the files the auditor staged and handed to `cp_verify` (when fired).
    pub staged: Option<Staged>,
    /// The auditor's opening check: the staged digests are the record's, and the record opens at
    /// its position under the root.
    pub open_ok: Option<bool>,
    pub call: Option<CallOutcome>,
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

/// The commitment step: append, and return (position, root, opening).
impl Ledger {
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

/// The opening check: the staged digests are the committed record's, and the record opens at its
/// position under the root.
pub fn opening_ok(
    rec: &RequestRecord,
    staged: &Staged,
    root: &[u8; 32],
    opening: &RangeOpening,
) -> bool {
    staged.req_sha256 == rec.req_sha256
        && staged.y_sha256 == rec.y_sha256
        && staged.proof_sha256 == rec.proof_sha256
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

/// Decide one audit and build its receipt. `run` is called only if the audit fires; it stages the
/// provider's files and calls `cp_verify` on the staged copies.
#[allow(clippy::too_many_arguments)]
pub fn audit(
    rec: &RequestRecord,
    root: [u8; 32],
    opening: RangeOpening,
    countersig: String,
    beacon: DrandRound,
    pins: &Pins,
    run: impl FnOnce() -> (Staged, CallOutcome),
) -> Receipt {
    let coin = beacon::coin(&beacon.signature, rec.position);
    let fired = decide::fires(coin, pins.p_num);
    let expect = Expect {
        id: pins.commitment_id.clone(),
        build: pins.build.clone(),
        r: rec.r,
        e: rec.e,
        accept_work: pins.accept_work,
    };
    let (staged, open_ok, call, verdict) = if fired {
        let (st, c) = run();
        let ok = opening_ok(rec, &st, &root, &opening);
        let v = decide::verdict(ok, c.stdout.as_bytes(), c.exit, &expect);
        (Some(st), Some(ok), Some(c), Some(v))
    } else {
        (None, None, None, None)
    };
    let alarm = decide::alarm(fired, verdict.unwrap_or(Verdict::NoVerdict));
    Receipt {
        version: RECEIPT_VERSION.into(),
        decide_src_sha256: crate::DECIDE_SRC_SHA256.into(),
        p_num: pins.p_num,
        record: rec.clone(),
        record_digest: hex::encode(rec.digest()),
        mmr_root: hex::encode(root),
        mmr_len: rec.position + 1,
        opening,
        countersig,
        beacon,
        coin,
        fired,
        expect,
        staged,
        open_ok,
        call,
        verdict,
        alarm,
    }
}

/// Everything [`recheck`] established.
#[derive(Debug, Serialize)]
pub struct RecheckReport {
    pub position: u64,
    pub audit_round: u64,
    pub fired: bool,
    pub verdict: Option<Verdict>,
    pub alarm: bool,
}

fn ensure(cond: bool, what: &str) -> Result<(), String> {
    if cond {
        Ok(())
    } else {
        Err(format!("recheck: {what}"))
    }
}

/// Re-derive every field of the receipt offline. Any disagreement is an error.
pub fn recheck(r: &Receipt, pins: &Pins) -> Result<RecheckReport, String> {
    ensure(r.version == RECEIPT_VERSION, "unknown receipt version")?;
    ensure(
        r.decide_src_sha256 == crate::DECIDE_SRC_SHA256,
        "the receipt was decided by another Lean decision source than this binary was built from",
    )?;
    ensure(
        r.p_num == pins.p_num,
        "the receipt's rate is not the pinned rate",
    )?;
    let digest = r.record.digest();
    ensure(hex::encode(digest) == r.record_digest, "record digest")?;
    let root: [u8; 32] = hex::decode(&r.mmr_root)
        .map_err(|e| e.to_string())?
        .try_into()
        .map_err(|_| "root length".to_string())?;
    let pos = r.record.position;
    let len = verify_range(&Blake3Mmr, &root, pos, pos, &[digest], &r.opening)
        .map_err(|e| format!("MMR opening: {e}"))?;
    ensure(
        len == r.mmr_len && len == pos + 1,
        "the opening's log length is not position + 1",
    )?;
    record::verify_countersign(
        &pins.requester_pk,
        &record::countersign_msg(pos, &digest, &root, r.record.seen_round),
        &r.countersig,
    )
    .map_err(|e| format!("countersignature: {e}"))?;
    ensure(
        r.beacon.round == r.record.seen_round + beacon::AUDIT_ROUND_MARGIN,
        "the beacon round is not the requester's seen round + 2",
    )?;
    r.beacon.verify()?;
    let coin = beacon::coin(&r.beacon.signature, pos);
    ensure(coin == r.coin, "coin")?;
    let fired = decide::fires(coin, pins.p_num);
    ensure(fired == r.fired, "fire decision")?;
    let expect = Expect {
        id: pins.commitment_id.clone(),
        build: pins.build.clone(),
        r: r.record.r,
        e: r.record.e,
        accept_work: pins.accept_work,
    };
    ensure(
        expect == r.expect,
        "the receipt's expectations are not the pinned ones",
    )?;
    ensure(
        r.record.commitment_id == pins.commitment_id,
        "the record names another commitment ID",
    )?;
    let verdict = match (&r.call, &r.staged, fired) {
        (Some(c), Some(st), true) => {
            let ok = opening_ok(&r.record, st, &root, &r.opening);
            ensure(Some(ok) == r.open_ok, "opening check")?;
            Some(decide::verdict(ok, c.stdout.as_bytes(), c.exit, &expect))
        }
        (None, None, false) => None,
        _ => {
            return Err("recheck: a call and staged digests are present iff the audit fired".into());
        }
    };
    ensure(verdict == r.verdict, "verdict")?;
    let alarm = decide::alarm(fired, verdict.unwrap_or(Verdict::NoVerdict));
    ensure(alarm == r.alarm, "alarm")?;
    Ok(RecheckReport {
        position: pos,
        audit_round: r.beacon.round,
        fired,
        verdict,
        alarm,
    })
}

/// Re-run `cp_verify` on files the re-checker holds (checked against the record's digests) and
/// return the verdict the compiled Lean gives on the fresh output.
pub fn rerun(
    r: &Receipt,
    pins: &Pins,
    bin: &std::path::Path,
    f: &CallFiles,
) -> Result<Verdict, String> {
    let dir = std::env::temp_dir().join(format!(
        "fpaudit-rerun-{}-{}",
        std::process::id(),
        r.record.position
    ));
    let (sf, st) = runner::stage(f, &dir).map_err(|e| format!("staging: {e}"))?;
    let root: [u8; 32] = hex::decode(&r.mmr_root)
        .map_err(|e| e.to_string())?
        .try_into()
        .map_err(|_| "root".to_string())?;
    let ok = opening_ok(&r.record, &st, &root, &r.opening);
    let c = runner::run_cp_verify(
        bin,
        &sf,
        &pins.commitment_id,
        std::time::Duration::from_secs(600),
        16 << 30,
    );
    let _ = std::fs::remove_dir_all(&dir);
    let expect = Expect {
        id: pins.commitment_id.clone(),
        build: pins.build.clone(),
        r: r.record.r,
        e: r.record.e,
        accept_work: pins.accept_work,
    };
    Ok(decide::verdict(ok, c.stdout.as_bytes(), c.exit, &expect))
}
