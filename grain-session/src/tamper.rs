//! The tamper classes a stranger's verify must refuse, each applied to a real bundle the way a
//! host would apply it: the host can rewrite anything it holds (calls, receipts it re-signs only
//! if it holds the receipt key, which it does), but not the renter's signatures.

use crate::{Bundle, CallPublic};

/// A host-consistent truncation of the receipt chain: drop the last window's receipt AND its
/// calls, and fix the report's totals so the shorter chain is self-consistent.
fn drop_last_window(b: &Bundle) -> Bundle {
    let mut t = b.clone();
    let w = t.window as usize;
    let n = t.calls.len();
    let last = (n - 1) / w * w;
    t.calls.truncate(last);
    let r = &mut t.attestation.report;
    r.receipts.pop();
    let consumed = r.receipts.last().map(|x| x.consumed_after).unwrap_or(0);
    r.consumed = consumed;
    r.headroom = (r.budget - consumed).max(0);
    r.admitted = r.receipts.len() as u64;
    t.manifest.pop();
    t
}

fn with_calls(b: &Bundle, f: impl FnOnce(&mut Vec<CallPublic>)) -> Bundle {
    let mut t = b.clone();
    f(&mut t.calls);
    t
}

/// Every tamper class, named. Each must be REFUSED.
pub fn cases(b: &Bundle) -> Vec<(&'static str, Bundle)> {
    let n = b.calls.len();
    let mid = n / 2;
    let mut out = vec![
        ("truncate: last window", drop_last_window(b)),
        (
            "truncate: last call",
            with_calls(b, |c| {
                c.pop();
            }),
        ),
        (
            "rewrite: a call's tool",
            with_calls(b, |c| {
                c[mid].tool = if c[mid].tool == "Bash" {
                    "Read".into()
                } else {
                    "Bash".into()
                };
            }),
        ),
        (
            "rewrite: a call's commitment",
            with_calls(b, |c| {
                let mut x = crate::parse32(&c[mid].commit).unwrap_or([0; 32]);
                x[0] ^= 1;
                c[mid].commit = hex::encode(x);
            }),
        ),
        (
            "reorder: two adjacent calls",
            with_calls(b, |c| c.swap(mid, mid + 1)),
        ),
        (
            "unreceipted: a call inserted",
            with_calls(b, |c| {
                let mut x = c[mid].clone();
                x.use_id = "toolu_unreceipted".into();
                c.insert(mid, x);
            }),
        ),
        (
            "unreceipted: a call appended",
            with_calls(b, |c| {
                let mut x = c[n - 1].clone();
                x.use_id = "toolu_unreceipted".into();
                x.seq += 1;
                c.push(x);
            }),
        ),
    ];
    let mut t = b.clone();
    let k = t.attestation.report.receipts.len() / 2;
    t.attestation.report.receipts.swap(k, k + 1);
    out.push(("reorder: two receipts", t));
    let mut t = b.clone();
    t.attestation.report.receipts[k].action.push('x');
    out.push(("rewrite: a receipt label", t));
    let mut t = b.clone();
    // Flip one byte deep inside the aggregate (past the envelope header).
    let mut agg = hex::decode(&t.aggregate).unwrap_or_default();
    let at = agg.len() / 2;
    if let Some(x) = agg.get_mut(at) {
        *x ^= 0x01;
    }
    t.aggregate = hex::encode(agg);
    out.push(("R3: aggregate byte flipped", t));
    let mut t = b.clone();
    if let Some(r) = t.executor_receipts.last_mut() {
        r.post_state_hash[0] ^= 1;
    }
    out.push(("executor: last receipt forged", t));
    let mut t = b.clone();
    if let Some(r) = t.executor_receipts.last_mut() {
        r.executor_signature = None;
    }
    out.push(("executor: last receipt unsigned", t));
    out
}
