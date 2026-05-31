//! state_differential.rs — the SWAP-ENABLER differential: marshalling REAL record
//! cell-state (not scalars) across the Lean↔Rust FFI and diffing the verified Lean
//! `recKExec` against a Rust reference.
//!
//! The scalar `differential.rs` round-trips only `UInt64` over the toy kernel. For the
//! cascade SWAP (the node calls the dregg2 kernel instead of dregg1's executor), the FFI
//! must marshal a real `Value` record `RecordKernelState`. This harness exercises exactly
//! that boundary:
//!
//!   * Lean side: `@[export] dregg_record_kernel_step (input : String) : String` over the
//!     PROVED `Exec.recKExec` (conservation/authority/fail-closed all proved in
//!     `Dregg2/Exec/RecordKernel.lean`). We drive it through the C bridge
//!     `dregg_record_kernel_step_str` (src/lean_init.c).
//!   * Rust side: a zero-dependency `Value` model + a codec for the SAME canonical JSON
//!     wire grammar the Lean `encodeValue`/`parseInput` use, plus a Rust reference
//!     `rec_k_exec` re-stating the record-cell transition.
//!
//! We generate random record cell-states (single-field `balance`, then multi-field
//! `balance`+`nonce`+`owner`), run BOTH, and assert agreement on the decoded output state
//! AND a wire round-trip. Agreement is the cross-validation certificate for the
//! marshalling boundary (it is cross-validation, NOT certification — the codec is TCB).

use std::ffi::CString;
use std::os::raw::c_char;
use std::process::ExitCode;

// --- The C bridge over the Lean record-kernel step (src/lean_init.c). ---
extern "C" {
    fn dregg_ffi_init() -> i32;
    /// Boxes `in_utf8`, calls the verified `dregg_record_kernel_step`, writes the result
    /// (NUL-terminated, truncated to `out_cap-1`) into `out`, returns the full byte length.
    fn dregg_record_kernel_step_str(
        in_utf8: *const c_char,
        out: *mut c_char,
        out_cap: usize,
    ) -> usize;
    /// The CAPS-bearing analog: the input wire also carries the held-cap table, so the
    /// cross-vat / held-cap branch of `authorizedB` is exercised across the FFI.
    fn dregg_record_kernel_step_caps_str(
        in_utf8: *const c_char,
        out: *mut c_char,
        out_cap: usize,
    ) -> usize;
}

/// Call the Lean record-kernel step with a wire string, returning the result wire string.
fn lean_step(wire: &str) -> String {
    let c_in = CString::new(wire).expect("wire has interior NUL");
    // The kernel echoes/extends the input; a 4x+slack buffer always suffices for our cases,
    // but we honor the returned full length and grow on truncation to be safe.
    let mut cap = wire.len() * 2 + 256;
    loop {
        let mut buf = vec![0u8; cap];
        let full = unsafe {
            dregg_record_kernel_step_str(
                c_in.as_ptr(),
                buf.as_mut_ptr() as *mut c_char,
                cap,
            )
        };
        if full == usize::MAX {
            panic!("dregg_record_kernel_step_str: unusable output buffer");
        }
        if full < cap {
            let nul = buf.iter().position(|&b| b == 0).unwrap_or(full);
            return String::from_utf8(buf[..nul].to_vec()).expect("result not UTF-8");
        }
        cap = full + 1; // grew past the buffer; retry exact.
    }
}

/// Call the Lean CAPS-bearing record-kernel step with a wire string. Same growth discipline
/// as `lean_step`, driving the caps export.
fn lean_step_caps(wire: &str) -> String {
    let c_in = CString::new(wire).expect("wire has interior NUL");
    let mut cap = wire.len() * 2 + 256;
    loop {
        let mut buf = vec![0u8; cap];
        let full = unsafe {
            dregg_record_kernel_step_caps_str(c_in.as_ptr(), buf.as_mut_ptr() as *mut c_char, cap)
        };
        if full == usize::MAX {
            panic!("dregg_record_kernel_step_caps_str: unusable output buffer");
        }
        if full < cap {
            let nul = buf.iter().position(|&b| b == 0).unwrap_or(full);
            return String::from_utf8(buf[..nul].to_vec()).expect("result not UTF-8");
        }
        cap = full + 1;
    }
}

// =============================================================================
// The Rust `Value` model — a faithful mirror of `Dregg2.Exec.Value`.
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
enum Value {
    Int(i64),
    Dig(u64),
    Sym(u64),
    Record(Vec<(String, Value)>),
}

impl Value {
    /// Read the `balance` field as an Int (default 0) — mirror of `RecordKernel.balOf`.
    fn bal_of(&self) -> i64 {
        match self {
            Value::Record(fs) => fs
                .iter()
                .find(|(k, _)| k == "balance")
                .and_then(|(_, v)| match v {
                    Value::Int(i) => Some(*i),
                    _ => None,
                })
                .unwrap_or(0),
            _ => 0,
        }
    }

    /// Overwrite the `balance` field to `v` — mirror of `RecordKernel.setBalance`.
    fn set_balance(&self, v: i64) -> Value {
        match self {
            Value::Record(fs) => {
                let mut out = Vec::with_capacity(fs.len() + 1);
                let mut found = false;
                for (k, x) in fs {
                    if k == "balance" {
                        out.push(("balance".to_string(), Value::Int(v)));
                        found = true;
                    } else {
                        out.push((k.clone(), x.clone()));
                    }
                }
                if !found {
                    out.push(("balance".to_string(), Value::Int(v)));
                }
                Value::Record(out)
            }
            _ => Value::Record(vec![("balance".to_string(), Value::Int(v))]),
        }
    }
}

// =============================================================================
// The canonical JSON codec — the SAME grammar as Dregg2.Exec.FFI.encode*/parse*.
//   VALUE  := {"int":N} | {"dig":N} | {"sym":N} | {"rec":FIELDS}
//   FIELDS := [] | [["NAME",VALUE](,["NAME",VALUE])*]
//   CELLS  := [] | [[ID,VALUE](,[ID,VALUE])*]
//   state  := {"cells":CELLS,"actor":N,"src":N,"dst":N,"amt":N}
//   out    := {"cells":CELLS,"ok":B}
// =============================================================================

fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            _ => out.push(c),
        }
    }
    out
}

fn encode_value(v: &Value) -> String {
    match v {
        Value::Int(i) => format!("{{\"int\":{i}}}"),
        Value::Dig(d) => format!("{{\"dig\":{d}}}"),
        Value::Sym(s) => format!("{{\"sym\":{s}}}"),
        Value::Record(fs) => {
            let mut inner = String::new();
            for (i, (n, val)) in fs.iter().enumerate() {
                if i > 0 {
                    inner.push(',');
                }
                inner.push_str(&format!("[\"{}\",{}]", json_escape(n), encode_value(val)));
            }
            format!("{{\"rec\":[{inner}]}}")
        }
    }
}

fn encode_cells(cells: &[(u64, Value)]) -> String {
    let mut inner = String::new();
    for (i, (id, v)) in cells.iter().enumerate() {
        if i > 0 {
            inner.push(',');
        }
        inner.push_str(&format!("[{id},{}]", encode_value(v)));
    }
    format!("[{inner}]")
}

/// Encode a full input state (cells + turn) into the wire grammar.
fn encode_input(cells: &[(u64, Value)], actor: u64, src: u64, dst: u64, amt: i64) -> String {
    format!(
        "{{\"cells\":{},\"actor\":{actor},\"src\":{src},\"dst\":{dst},\"amt\":{amt}}}",
        encode_cells(cells)
    )
}

// --- A strict recursive-descent decoder mirroring Dregg2.Exec.FFI.parse*. ---

struct P<'a> {
    s: &'a [u8],
    i: usize,
}

impl<'a> P<'a> {
    fn new(s: &'a str) -> Self {
        P { s: s.as_bytes(), i: 0 }
    }
    fn lit(&mut self, lit: &str) -> Result<(), String> {
        let b = lit.as_bytes();
        if self.i + b.len() <= self.s.len() && &self.s[self.i..self.i + b.len()] == b {
            self.i += b.len();
            Ok(())
        } else {
            Err(format!("expected `{lit}` at {}", self.i))
        }
    }
    fn peek(&self) -> Option<u8> {
        self.s.get(self.i).copied()
    }
    fn int(&mut self) -> Result<i64, String> {
        let start = self.i;
        if self.peek() == Some(b'-') {
            self.i += 1;
        }
        while matches!(self.peek(), Some(c) if c.is_ascii_digit()) {
            self.i += 1;
        }
        let txt = std::str::from_utf8(&self.s[start..self.i]).map_err(|e| e.to_string())?;
        txt.parse::<i64>().map_err(|e| format!("bad int `{txt}`: {e}"))
    }
    fn nat(&mut self) -> Result<u64, String> {
        let v = self.int()?;
        if v < 0 {
            return Err(format!("negative nat {v}"));
        }
        Ok(v as u64)
    }
    fn string(&mut self) -> Result<String, String> {
        self.lit("\"")?;
        let mut out = String::new();
        loop {
            match self.peek() {
                Some(b'"') => {
                    self.i += 1;
                    return Ok(out);
                }
                Some(b'\\') => {
                    self.i += 1;
                    match self.peek() {
                        Some(b'"') => out.push('"'),
                        Some(b'\\') => out.push('\\'),
                        other => return Err(format!("bad escape {other:?}")),
                    }
                    self.i += 1;
                }
                Some(c) => {
                    out.push(c as char);
                    self.i += 1;
                }
                None => return Err("unterminated string".into()),
            }
        }
    }
    fn value(&mut self) -> Result<Value, String> {
        if self.lit("{\"int\":").is_ok() {
            let i = self.int()?;
            self.lit("}")?;
            Ok(Value::Int(i))
        } else if self.lit("{\"dig\":").is_ok() {
            let d = self.nat()?;
            self.lit("}")?;
            Ok(Value::Dig(d))
        } else if self.lit("{\"sym\":").is_ok() {
            let s = self.nat()?;
            self.lit("}")?;
            Ok(Value::Sym(s))
        } else if self.lit("{\"rec\":").is_ok() {
            let fs = self.fields()?;
            self.lit("}")?;
            Ok(Value::Record(fs))
        } else {
            Err(format!("unknown value at {}", self.i))
        }
    }
    fn fields(&mut self) -> Result<Vec<(String, Value)>, String> {
        if self.lit("[]").is_ok() {
            return Ok(vec![]);
        }
        self.lit("[")?;
        let mut out = Vec::new();
        loop {
            self.lit("[")?;
            let name = self.string()?;
            self.lit(",")?;
            let v = self.value()?;
            self.lit("]")?;
            out.push((name, v));
            match self.peek() {
                Some(b',') => self.i += 1,
                Some(b']') => {
                    self.i += 1;
                    break;
                }
                _ => return Err(format!("expected , or ] in fields at {}", self.i)),
            }
        }
        Ok(out)
    }
    fn cells(&mut self) -> Result<Vec<(u64, Value)>, String> {
        if self.lit("[]").is_ok() {
            return Ok(vec![]);
        }
        self.lit("[")?;
        let mut out = Vec::new();
        loop {
            self.lit("[")?;
            let id = self.nat()?;
            self.lit(",")?;
            let v = self.value()?;
            self.lit("]")?;
            out.push((id, v));
            match self.peek() {
                Some(b',') => self.i += 1,
                Some(b']') => {
                    self.i += 1;
                    break;
                }
                _ => return Err(format!("expected , or ] in cells at {}", self.i)),
            }
        }
        Ok(out)
    }
}

/// Decode the output wire `{"cells":CELLS,"ok":B}` into (cells, ok).
fn decode_out(wire: &str) -> Result<(Vec<(u64, Value)>, bool), String> {
    let mut p = P::new(wire);
    p.lit("{\"cells\":")?;
    let cells = p.cells()?;
    p.lit(",\"ok\":")?;
    let ok = p.nat()?;
    p.lit("}")?;
    if p.i != p.s.len() {
        return Err(format!("trailing bytes at {}", p.i));
    }
    Ok((cells, ok == 1))
}

/// Decode a VALUE wire on its own (used by the codec round-trip check).
fn decode_value(wire: &str) -> Result<Value, String> {
    let mut p = P::new(wire);
    let v = p.value()?;
    if p.i != p.s.len() {
        return Err(format!("trailing bytes at {}", p.i));
    }
    Ok(v)
}

// =============================================================================
// The CAP model + caps codec — a faithful mirror of Dregg2.Authority.{Auth,Cap} and the
// caps wire grammar in Dregg2.Exec.FFI:
//   CAP     := {"null":0} | {"node":N} | {"ep":[N,AUTHS]}
//   AUTHS   := [] | [A(,A)*]            A := 0=read 1=write 2=grant 3=call 4=reply 5=reset 6=control
//   CAPLIST := [] | [CAP(,CAP)*]
//   CAPS    := [] | [[HOLDER,CAPLIST](,[HOLDER,CAPLIST])*]
//   state   := {"cells":CELLS,"caps":CAPS,"actor":N,"src":N,"dst":N,"amt":N}
// =============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Auth {
    Read = 0,
    Write = 1,
    Grant = 2,
    Call = 3,
    Reply = 4,
    Reset = 5,
    Control = 6,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Cap {
    Null,
    Node(u64),
    Endpoint(u64, Vec<Auth>),
}

fn auth_tag(a: Auth) -> u64 {
    a as u64
}

fn encode_auths(auths: &[Auth]) -> String {
    let mut inner = String::new();
    for (i, a) in auths.iter().enumerate() {
        if i > 0 {
            inner.push(',');
        }
        inner.push_str(&auth_tag(*a).to_string());
    }
    format!("[{inner}]")
}

fn encode_cap(c: &Cap) -> String {
    match c {
        Cap::Null => "{\"null\":0}".to_string(),
        Cap::Node(t) => format!("{{\"node\":{t}}}"),
        Cap::Endpoint(t, r) => format!("{{\"ep\":[{t},{}]}}", encode_auths(r)),
    }
}

fn encode_cap_list(cl: &[Cap]) -> String {
    let mut inner = String::new();
    for (i, c) in cl.iter().enumerate() {
        if i > 0 {
            inner.push(',');
        }
        inner.push_str(&encode_cap(c));
    }
    format!("[{inner}]")
}

fn encode_caps(caps: &[(u64, Vec<Cap>)]) -> String {
    let mut inner = String::new();
    for (i, (h, cl)) in caps.iter().enumerate() {
        if i > 0 {
            inner.push(',');
        }
        inner.push_str(&format!("[{h},{}]", encode_cap_list(cl)));
    }
    format!("[{inner}]")
}

/// Encode a full CAPS-bearing input state (cells + caps + turn) into the wire grammar.
fn encode_input_caps(
    cells: &[(u64, Value)],
    caps: &[(u64, Vec<Cap>)],
    actor: u64,
    src: u64,
    dst: u64,
    amt: i64,
) -> String {
    format!(
        "{{\"cells\":{},\"caps\":{},\"actor\":{actor},\"src\":{src},\"dst\":{dst},\"amt\":{amt}}}",
        encode_cells(cells),
        encode_caps(caps)
    )
}

/// The Rust mirror of `Kernel.authorizedB` over the marshalled caps table: authorized over
/// `src` iff the actor owns it (`actor == src`) OR holds a discharging cap (a `node src` cap,
/// or an `endpoint src` cap carrying `write`).
fn ref_authorized(caps: &[(u64, Vec<Cap>)], actor: u64, src: u64) -> bool {
    if actor == src {
        return true;
    }
    let slot = caps.iter().find(|(h, _)| *h == actor).map(|(_, cl)| cl);
    match slot {
        None => false,
        Some(cl) => cl.iter().any(|c| match c {
            Cap::Node(t) => *t == src,
            Cap::Endpoint(t, r) => *t == src && r.contains(&Auth::Write),
            Cap::Null => false,
        }),
    }
}

// =============================================================================
// The Rust reference `recKExec` — re-states Dregg2.Exec.recKExec.
//
// Authority: empty cap table, so authorizedB(turn) == (actor == src) (ownership).
// Commit gate: authorized ∧ 0 <= amt <= balOf(src) ∧ src != dst ∧ src,dst ∈ accounts.
// On commit: debit src.balance by amt, credit dst.balance by amt, others untouched.
// On reject: state unchanged. accounts = the set of listed cell ids.
// =============================================================================

fn ref_rec_k_exec(
    cells: &[(u64, Value)],
    actor: u64,
    src: u64,
    dst: u64,
    amt: i64,
) -> (Vec<(u64, Value)>, bool) {
    let accounts: Vec<u64> = cells.iter().map(|(id, _)| *id).collect();
    let lookup = |c: u64| -> Value {
        cells
            .iter()
            .find(|(id, _)| *id == c)
            .map(|(_, v)| v.clone())
            .unwrap_or_else(|| Value::Record(vec![("balance".to_string(), Value::Int(0))]))
    };
    let authorized = actor == src;
    let src_bal = lookup(src).bal_of();
    let committed = authorized
        && amt >= 0
        && amt <= src_bal
        && src != dst
        && accounts.contains(&src)
        && accounts.contains(&dst);

    // Output cells in the SAME id order as the input (the Lean side does `cellsOfState ids`).
    let out: Vec<(u64, Value)> = accounts
        .iter()
        .map(|&c| {
            let base = lookup(c);
            if committed && c == src {
                (c, base.set_balance(base.bal_of() - amt))
            } else if committed && c == dst {
                (c, base.set_balance(base.bal_of() + amt))
            } else {
                (c, base)
            }
        })
        .collect();
    (out, committed)
}

/// The CAPS-aware reference: identical to `ref_rec_k_exec` except the authority check consults
/// the marshalled cap table (`ref_authorized`) rather than ownership alone — so it admits the
/// cross-vat / held-cap case. This is the Rust golden-reference for the caps differential.
fn ref_rec_k_exec_caps(
    cells: &[(u64, Value)],
    caps: &[(u64, Vec<Cap>)],
    actor: u64,
    src: u64,
    dst: u64,
    amt: i64,
) -> (Vec<(u64, Value)>, bool) {
    let accounts: Vec<u64> = cells.iter().map(|(id, _)| *id).collect();
    let lookup = |c: u64| -> Value {
        cells
            .iter()
            .find(|(id, _)| *id == c)
            .map(|(_, v)| v.clone())
            .unwrap_or_else(|| Value::Record(vec![("balance".to_string(), Value::Int(0))]))
    };
    let authorized = ref_authorized(caps, actor, src);
    let src_bal = lookup(src).bal_of();
    let committed = authorized
        && amt >= 0
        && amt <= src_bal
        && src != dst
        && accounts.contains(&src)
        && accounts.contains(&dst);

    let out: Vec<(u64, Value)> = accounts
        .iter()
        .map(|&c| {
            let base = lookup(c);
            if committed && c == src {
                (c, base.set_balance(base.bal_of() - amt))
            } else if committed && c == dst {
                (c, base.set_balance(base.bal_of() + amt))
            } else {
                (c, base)
            }
        })
        .collect();
    (out, committed)
}

// --- A tiny self-contained PRNG (xorshift64*), no extra crates. ---
struct Rng(u64);
impl Rng {
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    /// A balance bounded to 2^40 so totals stay exact and well within i64.
    fn bal(&mut self) -> i64 {
        (self.next_u64() % (1u64 << 40)) as i64
    }
}

const N: usize = 10_000;

/// Build a random record cell-state + turn. `multi` toggles single-field vs multi-field
/// records (balance + nonce + owner).
fn random_case(rng: &mut Rng, multi: bool) -> (Vec<(u64, Value)>, u64, u64, u64, i64) {
    let make = |rng: &mut Rng| -> Value {
        if multi {
            Value::Record(vec![
                ("balance".to_string(), Value::Int(rng.bal())),
                ("nonce".to_string(), Value::Int((rng.next_u64() % 1000) as i64)),
                ("owner".to_string(), Value::Dig(rng.next_u64() % 1_000_000)),
            ])
        } else {
            Value::Record(vec![("balance".to_string(), Value::Int(rng.bal()))])
        }
    };
    // Two live cells, ids 0 and 1.
    let cells = vec![(0u64, make(rng)), (1u64, make(rng))];
    // amt spans both available (<= balA) and over-draw regimes.
    let amt = rng.bal();
    // Actor 0 ~1/2 the time (authorized over src 0), else arbitrary.
    let actor = if rng.next_u64() % 2 == 0 { 0 } else { rng.next_u64() };
    (cells, actor, 0, 1, amt)
}

/// Build a random CAPS-bearing case (two cells, ids 0/1) exercising every authority regime:
/// owner, held write-endpoint, held node cap, held read-only endpoint (no write), wrong-target
/// cap, and no cap at all. Returns (cells, caps, actor, src, dst, amt).
fn random_caps_case(rng: &mut Rng) -> (Vec<(u64, Value)>, Vec<(u64, Vec<Cap>)>, u64, u64, u64, i64) {
    let cells = vec![
        (0u64, Value::Record(vec![("balance".to_string(), Value::Int(rng.bal()))])),
        (1u64, Value::Record(vec![("balance".to_string(), Value::Int(rng.bal()))])),
    ];
    let amt = rng.bal();
    // A non-owner actor (distinct from src 0). Pick a small label so holder/actor align.
    let actor: u64 = 2 + (rng.next_u64() % 16);
    // src is 0 (the owner is label 0; `actor` is deliberately != 0 so ownership never applies).
    let src = 0u64;
    // Choose one of 7 cap regimes for `actor`'s slot.
    let regime = rng.next_u64() % 7;
    let caps: Vec<(u64, Vec<Cap>)> = match regime {
        0 => vec![],                                              // no caps at all
        1 => vec![(actor, vec![])],                              // empty slot
        2 => vec![(actor, vec![Cap::Endpoint(0, vec![Auth::Write])])], // write on src ⇒ authz
        3 => vec![(actor, vec![Cap::Endpoint(0, vec![Auth::Read])])],  // read-only on src ⇒ deny
        4 => vec![(actor, vec![Cap::Node(0)])],                  // node cap on src ⇒ authz
        5 => vec![(actor, vec![Cap::Endpoint(1, vec![Auth::Write])])], // write on WRONG target ⇒ deny
        _ => vec![(actor, vec![Cap::Null, Cap::Endpoint(0, vec![Auth::Read, Auth::Write])])], // mixed ⇒ authz
    };
    (cells, caps, actor, src, 1, amt)
}

fn main() -> ExitCode {
    let rc = unsafe { dregg_ffi_init() };
    if rc != 0 {
        eprintln!("FATAL: Lean module initialization failed (rc={rc})");
        return ExitCode::FAILURE;
    }

    let mut rng = Rng(0x1234_5678_9ABC_DEF0);
    let mut agreed = 0usize;
    let mut diverged = 0usize;
    let mut roundtrip_ok = 0usize;

    // Two phases: single-field `balance` records (the concrete swap-enabler), then
    // multi-field records (balance + nonce + owner — non-balance fields must survive).
    for phase in 0..2 {
        let multi = phase == 1;
        let label = if multi { "multi-field" } else { "single-field balance" };
        let mut phase_agreed = 0usize;

        for i in 0..N {
            let (cells, actor, src, dst, amt) = random_case(&mut rng, multi);

            // (1) Wire round-trip check: encode each cell value, decode it, must equal.
            for (_, v) in &cells {
                let w = encode_value(v);
                match decode_value(&w) {
                    Ok(d) if &d == v => roundtrip_ok += 1,
                    Ok(d) => {
                        eprintln!("ROUND-TRIP MISMATCH @{label} case {i}: {v:?} != {d:?}");
                        diverged += 1;
                    }
                    Err(e) => {
                        eprintln!("ROUND-TRIP DECODE ERR @{label} case {i}: {e}");
                        diverged += 1;
                    }
                }
            }

            // (2) Differential: Lean FFI vs Rust reference on the full step.
            let wire_in = encode_input(&cells, actor, src, dst, amt);
            let lean_wire = lean_step(&wire_in);
            let (lean_cells, lean_ok) = match decode_out(&lean_wire) {
                Ok(x) => x,
                Err(e) => {
                    eprintln!("LEAN OUTPUT DECODE ERR @{label} case {i}: {e}\n  wire={lean_wire}");
                    diverged += 1;
                    continue;
                }
            };
            let (rust_cells, rust_ok) = ref_rec_k_exec(&cells, actor, src, dst, amt);

            if lean_ok == rust_ok && lean_cells == rust_cells {
                agreed += 1;
                phase_agreed += 1;
            } else {
                diverged += 1;
                eprintln!(
                    "DIVERGENCE @{label} case {i}: in={wire_in}\n  lean ok={lean_ok} cells={lean_cells:?}\n  rust ok={rust_ok} cells={rust_cells:?}"
                );
            }
        }
        println!("  [{label}] {phase_agreed}/{N} step cases agree");
    }

    // =========================================================================================
    // PHASE 3 — the HELD-CAP authority differential: marshal the `Caps` table too, and exercise
    // the cross-vat branch of `authorizedB` (actor != owner but holds a discharging cap).
    // Lean `dregg_record_kernel_step_caps` (over the PROVED `recKExec`) vs `ref_rec_k_exec_caps`.
    // =========================================================================================
    let mut caps_agreed = 0usize;
    let mut caps_authz_commits = 0usize; // committed turns where actor != owner (held-cap authz)
    let mut caps_rejects = 0usize; // non-owner, no discharging cap ⇒ fail-closed
    for i in 0..N {
        let (cells, caps, actor, src, dst, amt) = random_caps_case(&mut rng);
        let wire_in = encode_input_caps(&cells, &caps, actor, src, dst, amt);
        let lean_wire = lean_step_caps(&wire_in);
        let (lean_cells, lean_ok) = match decode_out(&lean_wire) {
            Ok(x) => x,
            Err(e) => {
                eprintln!("LEAN CAPS OUTPUT DECODE ERR case {i}: {e}\n  wire={lean_wire}");
                diverged += 1;
                continue;
            }
        };
        let (rust_cells, rust_ok) = ref_rec_k_exec_caps(&cells, &caps, actor, src, dst, amt);

        if lean_ok == rust_ok && lean_cells == rust_cells {
            caps_agreed += 1;
            if lean_ok {
                // actor is never the owner (actor >= 2, src == 0): a commit here is HELD-CAP authz.
                caps_authz_commits += 1;
            } else if !ref_authorized(&caps, actor, src) {
                caps_rejects += 1;
            }
        } else {
            diverged += 1;
            eprintln!(
                "CAPS DIVERGENCE case {i}: in={wire_in}\n  lean ok={lean_ok} cells={lean_cells:?}\n  rust ok={rust_ok} cells={rust_cells:?}"
            );
        }
    }
    println!("  [held-cap authority] {caps_agreed}/{N} caps step cases agree");
    println!(
        "    ({caps_authz_commits} held-cap-authorized commits, {caps_rejects} fail-closed rejects)"
    );

    // Explicit, named WITNESSES for the report (the two boundary cases the mission calls out):
    // (A) actor 9 (!= owner 0) holds a `write` endpoint on src 0 ⇒ COMMITS.
    let wa_cells = vec![
        (0u64, Value::Record(vec![("balance".to_string(), Value::Int(100))])),
        (1u64, Value::Record(vec![("balance".to_string(), Value::Int(5))])),
    ];
    let wa_caps = vec![(9u64, vec![Cap::Endpoint(0, vec![Auth::Write])])];
    let wa_in = encode_input_caps(&wa_cells, &wa_caps, 9, 0, 1, 30);
    let (wa_cells_out, wa_ok) = decode_out(&lean_step_caps(&wa_in)).expect("witness A decodes");
    let (wa_ref_cells, wa_ref_ok) = ref_rec_k_exec_caps(&wa_cells, &wa_caps, 9, 0, 1, 30);
    let witness_a_ok = wa_ok && wa_ref_ok && wa_cells_out == wa_ref_cells;
    println!(
        "    WITNESS A (held-cap authorized, actor 9 holds write-ep on src 0): lean ok={wa_ok} \
         ref ok={wa_ref_ok} cells_match={} -> {}",
        wa_cells_out == wa_ref_cells,
        if witness_a_ok { "COMMIT (cross-vat held-cap authz round-trips)" } else { "FAIL" }
    );

    // (B) actor 9 holds only a READ endpoint on src 0 (no write), not owner ⇒ REJECTS.
    let wb_caps = vec![(9u64, vec![Cap::Endpoint(0, vec![Auth::Read])])];
    let wb_in = encode_input_caps(&wa_cells, &wb_caps, 9, 0, 1, 30);
    let (wb_cells_out, wb_ok) = decode_out(&lean_step_caps(&wb_in)).expect("witness B decodes");
    let (wb_ref_cells, wb_ref_ok) = ref_rec_k_exec_caps(&wa_cells, &wb_caps, 9, 0, 1, 30);
    let witness_b_ok = !wb_ok && !wb_ref_ok && wb_cells_out == wb_ref_cells;
    println!(
        "    WITNESS B (no discharging cap, actor 9 read-only on src 0): lean ok={wb_ok} \
         ref ok={wb_ref_ok} cells_unchanged={} -> {}",
        wb_cells_out == wb_ref_cells,
        if witness_b_ok { "REJECT (fail-closed)" } else { "FAIL" }
    );
    if !witness_a_ok || !witness_b_ok {
        eprintln!("WITNESS FAILURE — held-cap authorization boundary not as proved");
        diverged += 1;
    }

    let total = 3 * N;
    let all_agreed = agreed + caps_agreed;
    if diverged == 0 {
        println!(
            "{all_agreed}/{total} record-state step cases agree (+{roundtrip_ok} value round-trips) \
             — Lean recKExec \u{2261} Rust reference over the marshalled record cell + cap table"
        );
        ExitCode::SUCCESS
    } else {
        eprintln!("{diverged} divergences — Lean recKExec \u{2262} Rust reference");
        ExitCode::FAILURE
    }
}
