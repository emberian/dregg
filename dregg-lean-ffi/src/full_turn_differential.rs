//! full_turn_differential.rs — the E6 / Path A swap-enabler differential + adversarial fuzzer.
//!
//! The state/caps differentials run ONE `recKExec` step (single transfer) ± caps. This harness
//! drives the WHOLE turn decision: `TurnExecutorFull.execFullTurn` — the ALL-OR-NOTHING
//! transaction over a `List FullAction` (balance / delegate / revoke / mint / burn) that is the
//! executor destined to replace dregg1's `authorize.rs`.
//!
//!   * Lean side: `@[export] dregg_exec_full_turn (input : String) : String` over the PROVED
//!     `execFullTurn` (ledger/conservation/step-completeness all proved in
//!     `Dregg2/Exec/TurnExecutorFull.lean`). Driven via the C bridge `dregg_exec_full_turn_str`.
//!   * Rust side: a faithful reference reimplementation of `execFull`/`execFullTurn` over the same
//!     content-addressed record world, plus a codec for the full-turn wire grammar.
//!
//! Two regimes:
//!   1. STRUCTURED differential — fixed-seed random multi-action turns (including a deliberately
//!      failing middle action), asserting Lean ≡ Rust on the post-state cells, the post-state caps,
//!      the commit bit, the receipt-log length, AND the all-or-nothing ROLLBACK (a turn that fails
//!      mid-way leaves state UNCHANGED in both — verified positionally).
//!   2. ADVERSARIAL FUZZER (proptest) — generates adversarial turns (over/underflowing amounts,
//!      unauthorized delegates, double-mints, empty/huge lists, malformed orderings, wrong-target
//!      caps) and asserts the Lean FFI and Rust reference AGREE on accept/reject + final state
//!      across many minimized cases. This replaces the fixed-seed harness's blind spot.
//!
//! HONESTY: agreement CROSS-VALIDATES the codec (TCB) and the Rust reference against the proved
//! Lean oracle on the SAMPLED domain. It does NOT certify the Rust reference (only the Lean term
//! carries proofs) and it does NOT prove the codec — a codec bug that corrupts BOTH sides
//! identically would pass. What it buys: every adversarial input where Lean and Rust disagree is
//! surfaced and minimized, hardening the one piece of Path A that is TCB (the marshalling).

use proptest::prelude::*;
use proptest::test_runner::{Config, TestRunner};
use std::collections::BTreeSet;
use std::ffi::CString;
use std::os::raw::c_char;
use std::process::ExitCode;

// --- The C bridge over the Lean full-turn executor (src/lean_init.c). ---
extern "C" {
    fn dregg_ffi_init() -> i32;
    /// Boxes `in_utf8`, calls the verified `dregg_exec_full_turn`, writes the result
    /// (NUL-terminated, truncated to `out_cap-1`) into `out`, returns the full byte length.
    fn dregg_exec_full_turn_str(in_utf8: *const c_char, out: *mut c_char, out_cap: usize) -> usize;
}

/// Call the Lean full-turn executor with a wire string, returning the result wire string.
/// Grows the output buffer on truncation (the kernel echoes/extends the input).
fn lean_full_turn(wire: &str) -> String {
    let c_in = CString::new(wire).expect("wire has interior NUL");
    let mut cap = wire.len() * 2 + 512;
    loop {
        let mut buf = vec![0u8; cap];
        let full = unsafe {
            dregg_exec_full_turn_str(c_in.as_ptr(), buf.as_mut_ptr() as *mut c_char, cap)
        };
        if full == usize::MAX {
            panic!("dregg_exec_full_turn_str: unusable output buffer");
        }
        if full < cap {
            let nul = buf.iter().position(|&b| b == 0).unwrap_or(full);
            return String::from_utf8(buf[..nul].to_vec()).expect("result not UTF-8");
        }
        cap = full + 1;
    }
}

// =============================================================================
// The Rust `Value` model — a faithful mirror of `Dregg2.Exec.Value` (balance-field subset).
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
enum Value {
    Int(i128),
    Dig(u64),
    Sym(u64),
    Record(Vec<(String, Value)>),
}

impl Value {
    /// Read the `balance` field as an Int (default 0) — mirror of `RecordKernel.balOf`.
    fn bal_of(&self) -> i128 {
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
    /// Overwrite the `balance` field to `v` — mirror of `RecordKernel.setBalance`
    /// (`setBalanceList`: replace the FIRST `balance` field in place; append if absent;
    /// a non-record becomes a singleton `balance` record).
    fn set_balance(&self, v: i128) -> Value {
        match self {
            Value::Record(fs) => {
                let mut out = Vec::with_capacity(fs.len() + 1);
                let mut found = false;
                for (k, x) in fs {
                    if !found && k == "balance" {
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
// The CAP model — a faithful mirror of Dregg2.Authority.{Auth,Cap}.
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

// =============================================================================
// The Rust kernel STATE: cells (id-ordered) + a caps table (holder -> cap list).
// `caps` is the finite list of holders with a slot; an absent holder => [] (matching
// `capsOfEntries`). The reference threads a receipt-log LENGTH (we don't model the
// Turn payload, only its count, which is what the wire carries).
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
struct State {
    cells: Vec<(u64, Value)>,
    caps: Vec<(u64, Vec<Cap>)>,
    log_len: usize,
}

impl State {
    fn lookup(&self, c: u64) -> Value {
        self.cells
            .iter()
            .find(|(id, _)| *id == c)
            .map(|(_, v)| v.clone())
            .unwrap_or_else(|| Value::Record(vec![("balance".to_string(), Value::Int(0))]))
    }
    fn account_ids(&self) -> BTreeSet<u64> {
        self.cells.iter().map(|(id, _)| *id).collect()
    }
    /// Read a holder's cap list (absent => &[]).
    fn caps_of(&self, holder: u64) -> &[Cap] {
        self.caps
            .iter()
            .find(|(h, _)| *h == holder)
            .map(|(_, cl)| cl.as_slice())
            .unwrap_or(&[])
    }
    /// Set a cell's balance, preserving id-order; absent ids are left absent (the executor only
    /// touches live cells, and the wire echoes the listed ids).
    fn set_balance(&mut self, c: u64, v: i128) {
        for (id, val) in self.cells.iter_mut() {
            if *id == c {
                *val = val.set_balance(v);
                return;
            }
        }
    }
    /// `Caps.grant holder cap`: prepend `cap` to `holder`'s slot (`fun l => if l=holder then
    /// cap :: caps l else caps l`). Creates the slot if absent.
    fn grant(&mut self, holder: u64, cap: Cap) {
        for (h, cl) in self.caps.iter_mut() {
            if *h == holder {
                cl.insert(0, cap);
                return;
            }
        }
        self.caps.push((holder, vec![cap]));
    }
    /// `recKRevokeTarget holder t`: filter out every cap in `holder`'s slot conferring an edge to
    /// `t` (`confersEdgeTo`). Other holders untouched.
    fn revoke_target(&mut self, holder: u64, t: u64) {
        for (h, cl) in self.caps.iter_mut() {
            if *h == holder {
                cl.retain(|cap| !confers_edge_to(t, cap));
            }
        }
    }
}

// --- Authority gates (faithful mirrors). ---

/// `Kernel.authorizedB`: actor owns src (`actor == src`) OR holds a `node src` cap OR an
/// `endpoint src` cap carrying `write`.
fn authorized_b(s: &State, actor: u64, src: u64) -> bool {
    if actor == src {
        return true;
    }
    s.caps_of(actor).iter().any(|c| match c {
        Cap::Node(t) => *t == src,
        Cap::Endpoint(t, r) => *t == src && r.contains(&Auth::Write),
        Cap::Null => false,
    })
}

/// `Generators.mintAuthorizedB`: actor holds a `node cell` cap OR an `endpoint cell` cap carrying
/// `control`. Bare ownership is deliberately NOT enough.
fn mint_authorized_b(s: &State, actor: u64, cell: u64) -> bool {
    s.caps_of(actor).iter().any(|c| match c {
        Cap::Node(t) => *t == cell,
        Cap::Endpoint(t, r) => *t == cell && r.contains(&Auth::Control),
        Cap::Null => false,
    })
}

/// `AuthTurn.confersEdgeTo t cap`: `cap == node t` OR `endpoint t` carrying `write`.
fn confers_edge_to(t: u64, cap: &Cap) -> bool {
    match cap {
        Cap::Node(tt) => *tt == t,
        Cap::Endpoint(tt, r) => *tt == t && r.contains(&Auth::Write),
        Cap::Null => false,
    }
}

// =============================================================================
// FullAction + the reference executor — mirror of `Dregg2.Exec.TurnExecutorFull`.
// =============================================================================

#[derive(Debug, Clone, PartialEq, Eq)]
enum FullAction {
    /// (method, effect_tag, actor, src, dst, amt). The balance branch runs `recCexec s.move` and
    /// is INDIFFERENT to method/effect — we round-trip them but they do not affect the result.
    Balance { method: u64, effect: u64, actor: u64, src: u64, dst: u64, amt: i128 },
    Delegate { delegator: u64, recipient: u64, t: u64 },
    Revoke { holder: u64, t: u64 },
    Mint { actor: u64, cell: u64, amt: i128 },
    Burn { actor: u64, cell: u64, amt: i128 },
}

/// `execFull s fa` — the reference single-action executor. Returns Some(new state) on commit,
/// None on fail-closed reject. Each commit appends exactly one receipt (log_len += 1).
fn ref_exec_full(s: &State, fa: &FullAction) -> Option<State> {
    match fa {
        // .balance a => recCexec s a.move : recKExec gate (authority + availability + liveness).
        FullAction::Balance { actor, src, dst, amt, .. } => {
            let accounts = s.account_ids();
            let src_bal = s.lookup(*src).bal_of();
            let ok = authorized_b(s, *actor, *src)
                && *amt >= 0
                && *amt <= src_bal
                && src != dst
                && accounts.contains(src)
                && accounts.contains(dst);
            if !ok {
                return None;
            }
            let mut ns = s.clone();
            ns.set_balance(*src, s.lookup(*src).bal_of() - *amt);
            ns.set_balance(*dst, s.lookup(*dst).bal_of() + *amt);
            ns.log_len += 1;
            Some(ns)
        }
        // .delegate del rec t => recKDelegate: commits iff delegator holds a t-conferring cap;
        // on commit grant rec a `node t` cap. Balances/accounts untouched.
        FullAction::Delegate { delegator, recipient, t } => {
            let grounded = s.caps_of(*delegator).iter().any(|c| confers_edge_to(*t, c));
            if !grounded {
                return None;
            }
            let mut ns = s.clone();
            ns.grant(*recipient, Cap::Node(*t));
            ns.log_len += 1;
            Some(ns)
        }
        // .revoke holder t => recKRevokeTarget: ALWAYS commits; drop holder's t-conferring caps.
        FullAction::Revoke { holder, t } => {
            let mut ns = s.clone();
            ns.revoke_target(*holder, *t);
            ns.log_len += 1;
            Some(ns)
        }
        // .mint actor cell amt => recKMint: mintAuthorizedB ∧ 0<=amt ∧ cell live.
        FullAction::Mint { actor, cell, amt } => {
            let accounts = s.account_ids();
            let ok = mint_authorized_b(s, *actor, *cell) && *amt >= 0 && accounts.contains(cell);
            if !ok {
                return None;
            }
            let mut ns = s.clone();
            ns.set_balance(*cell, s.lookup(*cell).bal_of() + *amt);
            ns.log_len += 1;
            Some(ns)
        }
        // .burn actor cell amt => recKBurn: mintAuthorizedB ∧ 0<=amt ∧ amt<=balOf cell ∧ cell live.
        FullAction::Burn { actor, cell, amt } => {
            let accounts = s.account_ids();
            let cell_bal = s.lookup(*cell).bal_of();
            let ok = mint_authorized_b(s, *actor, *cell)
                && *amt >= 0
                && *amt <= cell_bal
                && accounts.contains(cell);
            if !ok {
                return None;
            }
            let mut ns = s.clone();
            ns.set_balance(*cell, s.lookup(*cell).bal_of() - *amt);
            ns.log_len += 1;
            Some(ns)
        }
    }
}

/// `execFullTurn s actions` — the ALL-OR-NOTHING transaction fold. Any None aborts the whole turn
/// to None (rollback: the caller keeps the pre-state).
fn ref_exec_full_turn(s0: &State, actions: &[FullAction]) -> Option<State> {
    let mut s = s0.clone();
    for fa in actions {
        match ref_exec_full(&s, fa) {
            Some(ns) => s = ns,
            None => return None,
        }
    }
    Some(s)
}

// =============================================================================
// The canonical JSON codec — the SAME grammar as Dregg2.Exec.FFI (full-turn additions).
//   turn   := {"cells":CELLS,"caps":CAPS,"actions":ACTIONS}
//   out    := {"cells":CELLS,"caps":CAPS,"loglen":N,"ok":B}
//   ACTION := {"bal":[M,E,actor,src,dst,amt]} | {"del":[d,r,t]} | {"rev":[h,t]}
//           | {"mint":[a,c,amt]} | {"burn":[a,c,amt]}
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

fn encode_action(a: &FullAction) -> String {
    match a {
        FullAction::Balance { method, effect, actor, src, dst, amt } => {
            format!("{{\"bal\":[{method},{effect},{actor},{src},{dst},{amt}]}}")
        }
        FullAction::Delegate { delegator, recipient, t } => {
            format!("{{\"del\":[{delegator},{recipient},{t}]}}")
        }
        FullAction::Revoke { holder, t } => format!("{{\"rev\":[{holder},{t}]}}"),
        FullAction::Mint { actor, cell, amt } => format!("{{\"mint\":[{actor},{cell},{amt}]}}"),
        FullAction::Burn { actor, cell, amt } => format!("{{\"burn\":[{actor},{cell},{amt}]}}"),
    }
}
fn encode_actions(actions: &[FullAction]) -> String {
    let mut inner = String::new();
    for (i, a) in actions.iter().enumerate() {
        if i > 0 {
            inner.push(',');
        }
        inner.push_str(&encode_action(a));
    }
    format!("[{inner}]")
}

fn encode_turn(s: &State, actions: &[FullAction]) -> String {
    format!(
        "{{\"cells\":{},\"caps\":{},\"actions\":{}}}",
        encode_cells(&s.cells),
        encode_caps(&s.caps),
        encode_actions(actions)
    )
}

// --- A strict recursive-descent decoder mirroring the Lean output parser. ---

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
    fn int(&mut self) -> Result<i128, String> {
        let start = self.i;
        if self.peek() == Some(b'-') {
            self.i += 1;
        }
        while matches!(self.peek(), Some(c) if c.is_ascii_digit()) {
            self.i += 1;
        }
        let txt = std::str::from_utf8(&self.s[start..self.i]).map_err(|e| e.to_string())?;
        txt.parse::<i128>().map_err(|e| format!("bad int `{txt}`: {e}"))
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
    fn auths(&mut self) -> Result<Vec<Auth>, String> {
        if self.lit("[]").is_ok() {
            return Ok(vec![]);
        }
        self.lit("[")?;
        let mut out = Vec::new();
        loop {
            let tag = self.nat()?;
            let a = match tag {
                0 => Auth::Read,
                1 => Auth::Write,
                2 => Auth::Grant,
                3 => Auth::Call,
                4 => Auth::Reply,
                5 => Auth::Reset,
                6 => Auth::Control,
                _ => return Err(format!("bad auth tag {tag}")),
            };
            out.push(a);
            match self.peek() {
                Some(b',') => self.i += 1,
                Some(b']') => {
                    self.i += 1;
                    break;
                }
                _ => return Err(format!("expected , or ] in auths at {}", self.i)),
            }
        }
        Ok(out)
    }
    fn cap(&mut self) -> Result<Cap, String> {
        if self.lit("{\"null\":0}").is_ok() {
            Ok(Cap::Null)
        } else if self.lit("{\"node\":").is_ok() {
            let t = self.nat()?;
            self.lit("}")?;
            Ok(Cap::Node(t))
        } else if self.lit("{\"ep\":[").is_ok() {
            let t = self.nat()?;
            self.lit(",")?;
            let r = self.auths()?;
            self.lit("]")?;
            self.lit("}")?;
            Ok(Cap::Endpoint(t, r))
        } else {
            Err(format!("unknown cap at {}", self.i))
        }
    }
    fn cap_list(&mut self) -> Result<Vec<Cap>, String> {
        if self.lit("[]").is_ok() {
            return Ok(vec![]);
        }
        self.lit("[")?;
        let mut out = Vec::new();
        loop {
            out.push(self.cap()?);
            match self.peek() {
                Some(b',') => self.i += 1,
                Some(b']') => {
                    self.i += 1;
                    break;
                }
                _ => return Err(format!("expected , or ] in cap list at {}", self.i)),
            }
        }
        Ok(out)
    }
    fn caps(&mut self) -> Result<Vec<(u64, Vec<Cap>)>, String> {
        if self.lit("[]").is_ok() {
            return Ok(vec![]);
        }
        self.lit("[")?;
        let mut out = Vec::new();
        loop {
            self.lit("[")?;
            let h = self.nat()?;
            self.lit(",")?;
            let cl = self.cap_list()?;
            self.lit("]")?;
            out.push((h, cl));
            match self.peek() {
                Some(b',') => self.i += 1,
                Some(b']') => {
                    self.i += 1;
                    break;
                }
                _ => return Err(format!("expected , or ] in caps at {}", self.i)),
            }
        }
        Ok(out)
    }
}

/// Decode the full-turn output `{"cells":CELLS,"caps":CAPS,"loglen":N,"ok":B}`.
fn decode_full_out(wire: &str) -> Result<(Vec<(u64, Value)>, Vec<(u64, Vec<Cap>)>, usize, bool), String> {
    let mut p = P::new(wire);
    p.lit("{\"cells\":")?;
    let cells = p.cells()?;
    p.lit(",\"caps\":")?;
    let caps = p.caps()?;
    p.lit(",\"loglen\":")?;
    let loglen = p.nat()? as usize;
    p.lit(",\"ok\":")?;
    let ok = p.nat()?;
    p.lit("}")?;
    if p.i != p.s.len() {
        return Err(format!("trailing bytes at {}", p.i));
    }
    Ok((cells, caps, loglen, ok == 1))
}

// =============================================================================
// The observable readout: the Lean side emits post-caps at the OBSERVED label set
// (sorted, deduped: input cap holders ∪ input cell ids ∪ every action label). We
// reproduce that set so we can compare the Rust reference's caps positionally.
// =============================================================================

fn action_labels(a: &FullAction) -> Vec<u64> {
    match a {
        FullAction::Balance { actor, src, dst, .. } => vec![*actor, *src, *dst],
        FullAction::Delegate { delegator, recipient, t } => vec![*delegator, *recipient, *t],
        FullAction::Revoke { holder, t } => vec![*holder, *t],
        FullAction::Mint { actor, cell, .. } => vec![*actor, *cell],
        FullAction::Burn { actor, cell, .. } => vec![*actor, *cell],
    }
}

fn observed_labels(s: &State, actions: &[FullAction]) -> Vec<u64> {
    let mut set: BTreeSet<u64> = BTreeSet::new();
    for (h, _) in &s.caps {
        set.insert(*h);
    }
    for (id, _) in &s.cells {
        set.insert(*id);
    }
    for a in actions {
        for l in action_labels(a) {
            set.insert(l);
        }
    }
    set.into_iter().collect()
}

/// The Rust reference's caps readout at the observed labels (matching `capsOfState`).
fn ref_caps_readout(s: &State, labels: &[u64]) -> Vec<(u64, Vec<Cap>)> {
    labels.iter().map(|&l| (l, s.caps_of(l).to_vec())).collect()
}

/// The Rust reference's cells readout in input id-order (matching `cellsOfState ids`).
fn ref_cells_readout(s: &State) -> Vec<(u64, Value)> {
    s.cells.iter().map(|(id, _)| (*id, s.lookup(*id))).collect()
}

// =============================================================================
// The COMPARISON: run Lean + Rust on (state, actions), assert agreement on the full
// observable (cells, caps@labels, loglen, ok). Returns Ok(()) on agreement; Err with a
// detailed message on divergence. This is the single oracle both the structured
// differential and the proptest fuzzer call.
// =============================================================================

fn compare(s0: &State, actions: &[FullAction]) -> Result<bool, String> {
    let wire = encode_turn(s0, actions);
    let lean_wire = lean_full_turn(&wire);
    let (lean_cells, lean_caps, lean_loglen, lean_ok) =
        decode_full_out(&lean_wire).map_err(|e| format!("lean decode err: {e}\n  wire={lean_wire}"))?;

    let labels = observed_labels(s0, actions);
    let (rust_cells, rust_caps, rust_loglen, rust_ok) = match ref_exec_full_turn(s0, actions) {
        Some(s1) => (ref_cells_readout(&s1), ref_caps_readout(&s1, &labels), s1.log_len, true),
        // Rollback: pre-state echoed, loglen 0 (matching the Lean side's none branch).
        None => (ref_cells_readout(s0), ref_caps_readout(s0, &labels), 0, false),
    };

    if lean_ok == rust_ok
        && lean_cells == rust_cells
        && lean_caps == rust_caps
        && lean_loglen == rust_loglen
    {
        Ok(lean_ok)
    } else {
        Err(format!(
            "DIVERGENCE:\n  in={wire}\n  lean: ok={lean_ok} loglen={lean_loglen} cells={lean_cells:?} caps={lean_caps:?}\n  rust: ok={rust_ok} loglen={rust_loglen} cells={rust_cells:?} caps={rust_caps:?}"
        ))
    }
}

// =============================================================================
// A tiny self-contained PRNG (xorshift64*) for the STRUCTURED differential.
// =============================================================================
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
    fn bal(&mut self) -> i128 {
        (self.next_u64() % (1u64 << 40)) as i128
    }
}

// =============================================================================
// PHASE 1 — STRUCTURED differential: random multi-action turns over a 3-cell world with a
// privileged minter (label 9 holds `node 0` and `node 1`) and a connectivity holder (label 0
// holds `node 7`). Includes turns engineered to fail mid-way to exercise rollback.
// =============================================================================

const N_STRUCTURED: usize = 5_000;

fn base_state(rng: &mut Rng) -> State {
    State {
        cells: vec![
            (0u64, Value::Record(vec![("balance".to_string(), Value::Int(rng.bal()))])),
            (1u64, Value::Record(vec![("balance".to_string(), Value::Int(rng.bal()))])),
            (2u64, Value::Record(vec![("balance".to_string(), Value::Int(rng.bal()))])),
        ],
        // 9 can mint/burn cells 0 and 1 (node caps); 0 can delegate connectivity to 7.
        caps: vec![
            (9u64, vec![Cap::Node(0), Cap::Node(1)]),
            (0u64, vec![Cap::Node(7)]),
        ],
        log_len: 0,
    }
}

/// A random single action over the structured world (sometimes deliberately unauthorized).
fn random_action(rng: &mut Rng) -> FullAction {
    match rng.next_u64() % 6 {
        0 => FullAction::Balance {
            method: rng.next_u64() % 8,
            effect: rng.next_u64() % 2,
            // actor 0 owns src 0 ~half the time; else arbitrary (often unauthorized).
            actor: if rng.next_u64() % 2 == 0 { 0 } else { rng.next_u64() % 20 },
            src: 0,
            dst: 1,
            amt: rng.bal(),
        },
        1 => FullAction::Mint {
            actor: if rng.next_u64() % 2 == 0 { 9 } else { rng.next_u64() % 20 },
            cell: rng.next_u64() % 3,
            amt: rng.bal(),
        },
        2 => FullAction::Burn {
            actor: if rng.next_u64() % 2 == 0 { 9 } else { rng.next_u64() % 20 },
            cell: rng.next_u64() % 3,
            amt: rng.bal(),
        },
        3 => FullAction::Delegate {
            delegator: if rng.next_u64() % 2 == 0 { 0 } else { rng.next_u64() % 20 },
            recipient: rng.next_u64() % 20,
            t: 7,
        },
        4 => FullAction::Revoke { holder: rng.next_u64() % 20, t: 7 },
        _ => FullAction::Balance {
            method: 0,
            effect: 1,
            actor: 1,
            src: 1,
            dst: 2,
            amt: rng.bal(),
        },
    }
}

fn run_structured() -> (usize, usize, usize) {
    let mut rng = Rng(0x0BAD_C0DE_F00D_1234);
    let mut agreed = 0usize;
    let mut diverged = 0usize;
    let mut rollbacks = 0usize;

    for i in 0..N_STRUCTURED {
        let s0 = base_state(&mut rng);
        let len = (rng.next_u64() % 5) as usize; // 0..4 actions
        let mut actions: Vec<FullAction> = (0..len).map(|_| random_action(&mut rng)).collect();
        // ~1/4 of non-empty turns: force a guaranteed-failing action in the MIDDLE to exercise
        // all-or-nothing rollback (an unauthorized mint by a label with no node cap).
        if !actions.is_empty() && rng.next_u64() % 4 == 0 {
            let mid = actions.len() / 2;
            actions.insert(mid, FullAction::Mint { actor: 13, cell: 0, amt: 5 });
        }
        match compare(&s0, &actions) {
            Ok(committed) => {
                agreed += 1;
                if !committed {
                    rollbacks += 1;
                }
            }
            Err(msg) => {
                diverged += 1;
                eprintln!("[structured #{i}] {msg}");
            }
        }
    }
    (agreed, diverged, rollbacks)
}

// =============================================================================
// PHASE 2 — explicit ROLLBACK + per-kind WITNESSES (the boundary cases the mission calls out).
// =============================================================================

fn run_witnesses() -> bool {
    let mut ok = true;
    let st = || State {
        cells: vec![
            (0u64, Value::Record(vec![("balance".to_string(), Value::Int(100))])),
            (1u64, Value::Record(vec![("balance".to_string(), Value::Int(5))])),
        ],
        caps: vec![(9u64, vec![Cap::Node(0)]), (0u64, vec![Cap::Node(7)])],
        log_len: 0,
    };

    // W1 — mixed turn nets to 0, all commit, log grows by 3.
    let mixed = vec![
        FullAction::Mint { actor: 9, cell: 0, amt: 50 },
        FullAction::Balance { method: 0, effect: 1, actor: 0, src: 0, dst: 1, amt: 30 },
        FullAction::Burn { actor: 9, cell: 0, amt: 50 },
    ];
    match compare(&st(), &mixed) {
        Ok(true) => println!("    W1 mixed (mint+transfer+burn, net 0): COMMIT, agree"),
        Ok(false) => {
            println!("    W1 FAIL: expected commit");
            ok = false;
        }
        Err(e) => {
            println!("    W1 DIVERGE: {e}");
            ok = false;
        }
    }

    // W2 — ROLLBACK: 2nd action unauthorized (actor 0 cannot mint) ⇒ whole turn rejects,
    // state UNCHANGED in both. The all-or-nothing case the mission requires.
    let bad = vec![
        FullAction::Mint { actor: 9, cell: 0, amt: 50 },
        FullAction::Mint { actor: 0, cell: 0, amt: 50 }, // 0 has no node-0 cap ⇒ fail
    ];
    match compare(&st(), &bad) {
        Ok(false) => println!("    W2 rollback (2nd action unauthorized): REJECT, state unchanged, agree"),
        Ok(true) => {
            println!("    W2 FAIL: expected rollback");
            ok = false;
        }
        Err(e) => {
            println!("    W2 DIVERGE: {e}");
            ok = false;
        }
    }

    // W3 — delegate then revoke: caps mutate, balances fixed; both commit.
    let dr = vec![
        FullAction::Delegate { delegator: 0, recipient: 1, t: 7 },
        FullAction::Revoke { holder: 0, t: 7 },
    ];
    match compare(&st(), &dr) {
        Ok(true) => println!("    W3 delegate+revoke (cap mutation): COMMIT, agree"),
        Ok(false) => {
            println!("    W3 FAIL: expected commit");
            ok = false;
        }
        Err(e) => {
            println!("    W3 DIVERGE: {e}");
            ok = false;
        }
    }

    // W4 — empty turn commits trivially.
    match compare(&st(), &[]) {
        Ok(true) => println!("    W4 empty turn: COMMIT (loglen 0), agree"),
        Ok(false) => {
            println!("    W4 FAIL: expected commit");
            ok = false;
        }
        Err(e) => {
            println!("    W4 DIVERGE: {e}");
            ok = false;
        }
    }

    ok
}

// =============================================================================
// PHASE 3 — the REAL ADVERSARIAL FUZZER (proptest). Generates adversarial states + turns and
// asserts Lean ≡ Rust on the full observable. The strategies deliberately oversample the edge
// regimes the fixed-seed harness avoids.
// =============================================================================

fn auth_strategy() -> impl Strategy<Value = Auth> {
    prop_oneof![
        Just(Auth::Read),
        Just(Auth::Write),
        Just(Auth::Grant),
        Just(Auth::Call),
        Just(Auth::Reply),
        Just(Auth::Reset),
        Just(Auth::Control),
    ]
}

fn cap_strategy() -> impl Strategy<Value = Cap> {
    prop_oneof![
        Just(Cap::Null),
        (0u64..6).prop_map(Cap::Node),
        (0u64..6, prop::collection::vec(auth_strategy(), 0..4)).prop_map(|(t, r)| Cap::Endpoint(t, r)),
    ]
}

/// Adversarial amounts: small, around-balance, negative, and near i64/i128 overflow boundaries.
fn amt_strategy() -> impl Strategy<Value = i128> {
    prop_oneof![
        -5i128..50,                                  // small incl. negative (under-flow)
        Just(0i128),
        Just(i64::MAX as i128),                      // i64 overflow boundary
        Just(i64::MAX as i128 + 1),
        Just(i64::MIN as i128),
        (i64::MAX as i128 - 100..i64::MAX as i128 + 100), // straddle the i64 boundary
        -3i128..1_000_000,                           // wide range
    ]
}

/// Adversarial cells: 0..4 cells, ids in 0..6 (allows duplicate-id and absent-id shapes), each a
/// record with a possibly-absent/ill-typed balance field.
fn cells_strategy() -> impl Strategy<Value = Vec<(u64, Value)>> {
    let one_value = prop_oneof![
        (-5i128..1_000_000).prop_map(|b| Value::Record(vec![("balance".to_string(), Value::Int(b))])),
        (-5i128..100, 0u64..1000).prop_map(|(b, n)| Value::Record(vec![
            ("balance".to_string(), Value::Int(b)),
            ("nonce".to_string(), Value::Int(n as i128)),
        ])),
        Just(Value::Record(vec![])),                          // no balance field (balOf => 0)
        Just(Value::Record(vec![("balance".to_string(), Value::Dig(7))])), // ill-typed balance
    ];
    prop::collection::vec((0u64..6, one_value), 0..4)
}

fn caps_strategy() -> impl Strategy<Value = Vec<(u64, Vec<Cap>)>> {
    prop::collection::vec((0u64..8, prop::collection::vec(cap_strategy(), 0..3)), 0..4)
}

fn action_strategy() -> impl Strategy<Value = FullAction> {
    prop_oneof![
        (0u64..8, 0u64..2, 0u64..8, 0u64..6, 0u64..6, amt_strategy()).prop_map(
            |(method, effect, actor, src, dst, amt)| FullAction::Balance {
                method, effect, actor, src, dst, amt
            }
        ),
        (0u64..8, 0u64..8, 0u64..6).prop_map(|(delegator, recipient, t)| FullAction::Delegate {
            delegator, recipient, t
        }),
        (0u64..8, 0u64..6).prop_map(|(holder, t)| FullAction::Revoke { holder, t }),
        (0u64..8, 0u64..6, amt_strategy()).prop_map(|(actor, cell, amt)| FullAction::Mint {
            actor, cell, amt
        }),
        (0u64..8, 0u64..6, amt_strategy()).prop_map(|(actor, cell, amt)| FullAction::Burn {
            actor, cell, amt
        }),
    ]
}

/// Turns: 0..8 actions (empty + multi-action + "huge"-ish), adversarial orderings (e.g. two
/// mints in a row = double-mint; revoke-before-delegate = malformed ordering — all emerge from
/// the free generation).
fn actions_strategy() -> impl Strategy<Value = Vec<FullAction>> {
    prop::collection::vec(action_strategy(), 0..8)
}

const N_FUZZ: u32 = 4_000;

fn run_fuzzer() -> (u64, u64) {
    let cases = std::cell::Cell::new(0u64);
    let mut runner = TestRunner::new(Config {
        cases: N_FUZZ,
        max_shrink_iters: 4096,
        // The FFI is single-threaded (one Lean runtime, brought up once in main); the fuzzer
        // must drive it serially.
        ..Config::default()
    });

    let strat = (cells_strategy(), caps_strategy(), actions_strategy());
    let result = runner.run(&strat, |(cells, caps, actions)| {
        cases.set(cases.get() + 1);
        let s0 = State { cells, caps, log_len: 0 };
        match compare(&s0, &actions) {
            Ok(_) => Ok(()),
            Err(msg) => Err(TestCaseError::fail(msg)),
        }
    });

    match result {
        Ok(()) => (cases.get(), 0),
        Err(e) => {
            eprintln!("FUZZER FOUND A DIVERGENCE (minimized):\n{e}");
            (cases.get(), 1)
        }
    }
}

fn main() -> ExitCode {
    let rc = unsafe { dregg_ffi_init() };
    if rc != 0 {
        eprintln!("FATAL: Lean module initialization failed (rc={rc})");
        return ExitCode::FAILURE;
    }

    println!("=== E6 full-turn differential (execFullTurn over the Lean FFI) ===");

    let (s_agreed, s_diverged, rollbacks) = run_structured();
    println!(
        "  [structured] {s_agreed}/{N_STRUCTURED} multi-action turns agree ({rollbacks} all-or-nothing rollbacks observed)"
    );

    println!("  [witnesses]");
    let witnesses_ok = run_witnesses();

    let (fuzz_cases, fuzz_diverged) = run_fuzzer();
    println!("  [adversarial fuzzer] {fuzz_cases} proptest cases ran, {fuzz_diverged} divergences (after minimization)");

    let total_diverged = s_diverged as u64 + fuzz_diverged + (if witnesses_ok { 0 } else { 1 });
    if total_diverged == 0 {
        println!(
            "ALL AGREE — Lean execFullTurn \u{2261} Rust reference over {} structured + {fuzz_cases} adversarial turns \
             (incl. {rollbacks} rollbacks); the proved turn-decision runs from Rust.",
            s_agreed
        );
        ExitCode::SUCCESS
    } else {
        eprintln!("{total_diverged} divergence sources — Lean execFullTurn \u{2262} Rust reference");
        ExitCode::FAILURE
    }
}
