//! The compiled Lean decision (minidregg `Selvage/AuditFlashProveDecide.lean`), behind safe
//! wrappers. This module holds no decision logic: each function marshals its arguments and returns
//! what the exported Lean function returned.

use std::sync::{Mutex, Once};

unsafe extern "C" {
    fn fpaudit_init() -> i32;
    fn fpaudit_fires(coin: u64, p_num: u64) -> u8;
    #[allow(clippy::too_many_arguments)]
    fn fpaudit_verdict(
        open_ok: u8,
        out: *const u8,
        out_len: usize,
        has_exit: u8,
        exit_code: u32,
        id: *const u8,
        id_len: usize,
        build: *const u8,
        build_len: usize,
        r: u32,
        e: u32,
        accept_work: u8,
    ) -> u8;
    fn fpaudit_alarm(fired: u8, verdict: u8) -> u8;
    fn fpaudit_alarm_open(fired: u8, verdict: u8) -> u8;
    #[allow(clippy::too_many_arguments)]
    fn fpaudit_opening_ok(
        stage_ok: u8,
        mmr_ok: u8,
        req_c: *const u8,
        req_c_len: usize,
        y_c: *const u8,
        y_c_len: usize,
        req_s: *const u8,
        req_s_len: usize,
        y_s: *const u8,
        y_s_len: usize,
        has_proof_c: u8,
        proof_c: *const u8,
        proof_c_len: usize,
        has_proof_s: u8,
        proof_s: *const u8,
        proof_s_len: usize,
    ) -> u8;
    fn fpaudit_round_ok(seen: u64, round: u64) -> u8;
    fn fpaudit_pnum_of_ppm(ppm: u64) -> u64;
}

static INIT: Once = Once::new();
/// Every call into the Lean runtime goes through this lock: the auditor is multi-threaded and
/// the runtime is initialized on one thread only.
static LEAN: Mutex<()> = Mutex::new(());

fn init() {
    INIT.call_once(|| {
        let rc = unsafe { fpaudit_init() };
        assert_eq!(rc, 0, "Lean decision module failed to initialize");
    });
}

/// The checker's verdict, as the Lean `Verdict`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum Verdict {
    Accept,
    Reject,
    NoVerdict,
}

impl Verdict {
    fn code(self) -> u8 {
        match self {
            Verdict::Accept => 0,
            Verdict::Reject => 1,
            Verdict::NoVerdict => 2,
        }
    }
    fn of_code(c: u8) -> Verdict {
        match c {
            0 => Verdict::Accept,
            1 => Verdict::Reject,
            _ => Verdict::NoVerdict,
        }
    }
}

/// What the auditor holds before the call (Lean `Expect`).
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Expect {
    pub id: String,
    pub build: String,
    pub r: u32,
    pub e: u32,
    pub accept_work: bool,
}

/// Lean `fires coin pNum`.
pub fn fires(coin: u64, p_num: u64) -> bool {
    init();
    let _g = LEAN.lock().unwrap_or_else(|e| e.into_inner());
    unsafe { fpaudit_fires(coin, p_num) != 0 }
}

/// Lean `auditVerdict openOk stdout exit expect`: a failed opening of the committed files is a
/// rejection, otherwise `verdictOf`.
pub fn verdict(open_ok: bool, stdout: &[u8], exit: Option<u32>, x: &Expect) -> Verdict {
    init();
    let _g = LEAN.lock().unwrap_or_else(|e| e.into_inner());
    let c = unsafe {
        fpaudit_verdict(
            u8::from(open_ok),
            stdout.as_ptr(),
            stdout.len(),
            u8::from(exit.is_some()),
            exit.unwrap_or(0),
            x.id.as_ptr(),
            x.id.len(),
            x.build.as_ptr(),
            x.build.len(),
            x.r,
            x.e,
            u8::from(x.accept_work),
        )
    };
    Verdict::of_code(c)
}

/// Lean `alarm` (fail-closed).
pub fn alarm(fired: bool, v: Verdict) -> bool {
    init();
    let _g = LEAN.lock().unwrap_or_else(|e| e.into_inner());
    unsafe { fpaudit_alarm(u8::from(fired), v.code()) != 0 }
}

/// Lean `alarmOpen`: the fail-open falsifier. Used only by the experiment's falsifier arm.
pub fn alarm_open(fired: bool, v: Verdict) -> bool {
    init();
    let _g = LEAN.lock().unwrap_or_else(|e| e.into_inner());
    unsafe { fpaudit_alarm_open(u8::from(fired), v.code()) != 0 }
}

/// Lean `openingOk`: staging succeeded, the MMR opening verified, and the staged digests are
/// well-formed and equal the committed ones.
#[allow(clippy::too_many_arguments)]
pub fn opening_ok(
    stage_ok: bool,
    mmr_ok: bool,
    req_c: &str,
    y_c: &str,
    req_s: &str,
    y_s: &str,
    proof_c: Option<&str>,
    proof_s: Option<&str>,
) -> bool {
    init();
    let _g = LEAN.lock().unwrap_or_else(|e| e.into_inner());
    let (pc, ps) = (proof_c.unwrap_or(""), proof_s.unwrap_or(""));
    unsafe {
        fpaudit_opening_ok(
            u8::from(stage_ok),
            u8::from(mmr_ok),
            req_c.as_ptr(),
            req_c.len(),
            y_c.as_ptr(),
            y_c.len(),
            req_s.as_ptr(),
            req_s.len(),
            y_s.as_ptr(),
            y_s.len(),
            u8::from(proof_c.is_some()),
            pc.as_ptr(),
            pc.len(),
            u8::from(proof_s.is_some()),
            ps.as_ptr(),
            ps.len(),
        ) != 0
    }
}

/// Lean `auditRoundOk`: the audit round is the seen round plus two.
pub fn round_ok(seen: u64, round: u64) -> bool {
    init();
    let _g = LEAN.lock().unwrap_or_else(|e| e.into_inner());
    unsafe { fpaudit_round_ok(seen, round) != 0 }
}

/// Lean `pNumOfPpm`: `None` outside `0 < ppm < 10^6`.
pub fn p_num_of_ppm(ppm: u64) -> Option<u64> {
    init();
    let _g = LEAN.lock().unwrap_or_else(|e| e.into_inner());
    let v = unsafe { fpaudit_pnum_of_ppm(ppm) };
    (v != 0).then_some(v)
}
