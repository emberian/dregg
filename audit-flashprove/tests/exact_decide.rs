//! The exact-recompute verdict goes through the compiled Lean of `Selvage/AuditExactDecide.lean`.
//! These cases need no recompute: they feed the decision the report a recompute prints.

use audit_flashprove::decide::{self, ExactExpect, Verdict};

const D: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";

fn x(output: &str) -> ExactExpect {
    ExactExpect {
        spec: D.into(),
        params: D.into(),
        weights: D.into(),
        prompt_len: 5,
        output: output.into(),
    }
}

fn report(toks: &str) -> String {
    format!(
        "pins spec={D} params={D} weights={D}\nshape prompt=5 output=3\nargmax tokens={toks}\nDONE\n"
    )
}

#[test]
fn exact_verdict_compiled_lean() {
    let v = |out: &str, exit, committed: &str| {
        decide::exact_verdict(true, out.as_bytes(), exit, &x(committed))
    };
    assert_eq!(v(&report("12,0,7"), Some(0), "12,0,7"), Verdict::Accept);
    // the committed transcript differs from the integer model's argmax at one position
    assert_eq!(v(&report("12,0,7"), Some(0), "12,0,8"), Verdict::Reject);
    // a malformed report, a non-zero exit, no exit, an unreadable committed output: no verdict
    assert_eq!(v(&report("12,0"), Some(0), "12,0,7"), Verdict::NoVerdict);
    assert_eq!(v(&report("12,0,7"), Some(3), "12,0,7"), Verdict::NoVerdict);
    assert_eq!(v(&report("12,0,7"), None, "12,0,7"), Verdict::NoVerdict);
    assert_eq!(v(&report("12,0,7"), Some(0), "12, 0,7"), Verdict::NoVerdict);
    // a failed opening rejects whatever the recompute printed
    assert_eq!(
        decide::exact_verdict(false, report("12,0,7").as_bytes(), Some(0), &x("12,0,7")),
        Verdict::Reject
    );
    // and every non-accept alarms when fired
    assert!(decide::alarm(true, Verdict::NoVerdict) && decide::alarm(true, Verdict::Reject));
    assert!(!decide::alarm(true, Verdict::Accept));
}
