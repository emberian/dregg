//! The compiled Lean decision against real `cp_verify` runs on FlashProve's stored exact-match
//! proof. Needs FPAUDIT_CP_VERIFY (a built cp_verify), FPAUDIT_STORED (examples/accepted-proof)
//! and FPAUDIT_BUILD (the build= digest); without them the real-run tests say so and pass vacuously
//! only in name: `lean_decision_linked` always runs.

use std::path::PathBuf;
use std::time::Duration;

use audit_flashprove::decide::{self, Expect, Verdict};
use audit_flashprove::runner::{self, CallFiles};

#[test]
fn lean_decision_linked() {
    // fires is `coin < pNum`, decided in Lean
    assert!(decide::fires(4, 5));
    assert!(!decide::fires(5, 5));
    assert!(decide::alarm(true, Verdict::NoVerdict));
    assert!(!decide::alarm_open(true, Verdict::NoVerdict));
    assert!(!decide::alarm(false, Verdict::Reject));
    let x = Expect {
        id: "A".into(),
        build: "B".into(),
        r: 60,
        e: 64,
        accept_work: true,
    };
    assert_eq!(decide::verdict(true, b"", None, &x), Verdict::NoVerdict);
    assert_eq!(
        decide::verdict(true, b"NO: x\n", Some(1), &x),
        Verdict::Reject
    );
    assert_eq!(
        decide::verdict(true, b"YES\n", Some(0), &x),
        Verdict::Reject
    );
    assert_eq!(decide::verdict(false, b"", Some(5), &x), Verdict::Reject);
    assert_eq!(audit_flashprove::DECIDE_SRC_SHA256.len(), 64);
}

fn env() -> Option<(PathBuf, PathBuf, String)> {
    Some((
        PathBuf::from(std::env::var("FPAUDIT_CP_VERIFY").ok()?),
        PathBuf::from(std::env::var("FPAUDIT_STORED").ok()?),
        std::env::var("FPAUDIT_BUILD").ok()?,
    ))
}

#[test]
fn real_cp_verify_verdicts() {
    let Some((bin, st, build)) = env() else {
        eprintln!("real_cp_verify_verdicts: FPAUDIT_* not set; nothing checked");
        return;
    };
    let id = std::fs::read_to_string(st.join("ID.txt"))
        .unwrap()
        .trim()
        .to_string();
    let x = Expect {
        id: id.clone(),
        build: build.clone(),
        r: 60,
        e: 64,
        accept_work: true,
    };
    let tmp = std::env::temp_dir().join(format!("fpaudit-test-{}", std::process::id()));
    std::fs::create_dir_all(&tmp).unwrap();
    let files = |y: Option<&[u8]>, proof: Option<PathBuf>| {
        let yp = match y {
            Some(b) => {
                let p = tmp.join("alt.y");
                std::fs::write(&p, b).unwrap();
                p
            }
            None => st.join("example.y"),
        };
        CallFiles {
            config: st.join("config"),
            ivk: st.join("ivk"),
            req: st.join("example.req"),
            y: yp,
            proof: proof.unwrap_or_else(|| st.join("example.proof")),
        }
    };
    let run = |f: &CallFiles, id: &str| {
        runner::run_cp_verify(&bin, f, id, Duration::from_secs(60), 8 << 30)
    };
    // honest
    let c = run(&files(None, None), &id);
    assert_eq!(
        decide::verdict(true, c.stdout.as_bytes(), c.exit, &x),
        Verdict::Accept,
        "{}",
        c.stdout
    );
    // wrong build pin, wrong range, wrong ID: the same YES is not accepted
    assert_eq!(
        decide::verdict(
            true,
            c.stdout.as_bytes(),
            c.exit,
            &Expect {
                build: "0".repeat(64),
                ..x.clone()
            }
        ),
        Verdict::Reject
    );
    assert_eq!(
        decide::verdict(
            true,
            c.stdout.as_bytes(),
            c.exit,
            &Expect { e: 63, ..x.clone() }
        ),
        Verdict::Reject
    );
    assert_eq!(
        decide::verdict(
            true,
            c.stdout.as_bytes(),
            c.exit,
            &Expect {
                accept_work: false,
                ..x.clone()
            }
        ),
        Verdict::Reject
    );
    // false next token
    let c = run(&files(Some(&200u32.to_le_bytes()), None), &id);
    assert_eq!(c.exit, Some(1));
    assert_eq!(
        decide::verdict(true, c.stdout.as_bytes(), c.exit, &x),
        Verdict::Reject
    );
    // withheld proof: exit 2, no verdict
    let c = run(&files(None, Some(tmp.join("absent.proof"))), &id);
    assert_eq!(c.exit, Some(2));
    assert_eq!(
        decide::verdict(true, c.stdout.as_bytes(), c.exit, &x),
        Verdict::NoVerdict
    );
    // a call killed for time: no verdict
    let c = runner::run_cp_verify(
        &bin,
        &files(None, None),
        &id,
        Duration::from_millis(200),
        8 << 30,
    );
    assert!(c.killed_for_time && c.exit.is_none());
    assert_eq!(
        decide::verdict(true, c.stdout.as_bytes(), c.exit, &x),
        Verdict::NoVerdict
    );
    let _ = std::fs::remove_dir_all(&tmp);
}

#[test]
fn codex_round2_teeth() {
    use audit_flashprove::runner::{CallFiles, stage};
    // the rate endpoints are refused by the Lean rule, not wrapped
    assert_eq!(decide::p_num_of_ppm(1_000_000), None);
    assert_eq!(decide::p_num_of_ppm(0), None);
    assert_eq!(decide::p_num_of_ppm(10_000), Some(184_467_440_737_095_516));
    // an empty digest never matches, even an empty committed one
    assert!(!decide::opening_ok(true, true, "", "", "", "", None, None));
    let d = "a".repeat(64);
    assert!(decide::opening_ok(true, true, &d, &d, &d, &d, None, None));
    assert!(!decide::opening_ok(false, true, &d, &d, &d, &d, None, None));
    assert!(!decide::opening_ok(
        true,
        true,
        &d,
        &d,
        &d,
        &d,
        Some(&d),
        None
    ));
    assert!(decide::round_ok(5, 7) && !decide::round_ok(5, 6));
    // staging refuses a FIFO without blocking, and a missing request file
    let tmp = std::env::temp_dir().join(format!("fpaudit-stage-{}", std::process::id()));
    std::fs::create_dir_all(&tmp).unwrap();
    std::fs::write(tmp.join("req"), b"r").unwrap();
    std::fs::write(tmp.join("y"), b"y").unwrap();
    let fifo = tmp.join("proof.fifo");
    let c = std::ffi::CString::new(fifo.to_str().unwrap()).unwrap();
    assert_eq!(unsafe { libc::mkfifo(c.as_ptr(), 0o600) }, 0);
    let f = |req: &str, proof: PathBuf| CallFiles {
        config: tmp.clone(),
        ivk: tmp.clone(),
        req: tmp.join(req),
        y: tmp.join("y"),
        proof,
    };
    let (files, st) = stage(&f("req", fifo.clone()), &tmp.join("s"));
    assert!(
        files.is_none()
            && st
                .fault
                .as_deref()
                .is_some_and(|m| m.contains("not a regular file"))
    );
    let (files, st) = stage(&f("absent", tmp.join("none")), &tmp.join("s"));
    assert!(files.is_none() && st.fault.is_some());
    let (files, st) = stage(&f("req", tmp.join("none")), &tmp.join("s"));
    assert!(files.is_some() && st.fault.is_none() && st.proof_sha256.is_none());
    let _ = std::fs::remove_dir_all(&tmp);
}
