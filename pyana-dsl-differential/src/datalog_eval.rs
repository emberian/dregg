//! Mini Datalog evaluator for the rules emitted by `gen_datalog`.
//!
//! `gen_datalog` emits a *single* rule per predicate of the form:
//!
//! ```text
//! foo_satisfied :- param0(P0), param1(P1), ..., predicate0, predicate1, ...
//! ```
//!
//! Where each `predicateN` is one of:
//!
//! - `Lhs <= Rhs`           — u64 ≤
//! - `Lhs >= Rhs`           — u64 ≥
//! - `Lhs == Rhs`           — equality
//! - `Lhs != Rhs`           — non-equality
//! - `member_of(E, S)`      — `E` is in the set named `S`
//! - `bit_range(V, N)`      — `V < 2^N` (not exercised by this crate's
//!   predicate suite, but accepted by the parser for forward compatibility)
//!
//! This evaluator parses the rule string, binds the capitalised identifiers
//! to the values supplied in [`Bindings`], and returns whether the rule
//! body is satisfied. It does NOT implement Datalog's full deductive
//! closure — pyana caveats are a single conjunctive rule.

use std::collections::HashSet;

use crate::predicates::Requirement;

/// Captured input bindings for the rule. Identifier names in the rule are
/// case-folded; we look up by lower-cased identifier.
pub struct Bindings {
    pub u64_vars: Vec<(String, u64)>,
    pub bytes_vars: Vec<(String, [u8; 32])>,
    pub sets: Vec<(String, HashSet<u64>)>,
}

impl Bindings {
    pub fn new() -> Self {
        Self {
            u64_vars: Vec::new(),
            bytes_vars: Vec::new(),
            sets: Vec::new(),
        }
    }

    pub fn with_u64(mut self, name: &str, value: u64) -> Self {
        self.u64_vars.push((name.to_lowercase(), value));
        self
    }
    pub fn with_bytes(mut self, name: &str, value: [u8; 32]) -> Self {
        self.bytes_vars.push((name.to_lowercase(), value));
        self
    }
    pub fn with_set(mut self, name: &str, value: HashSet<u64>) -> Self {
        self.sets.push((name.to_lowercase(), value));
        self
    }
}

impl Default for Bindings {
    fn default() -> Self {
        Self::new()
    }
}

/// Parse the emitted rule body into a list of `(lhs, op, rhs)` triples and
/// `member_of(E, S)` calls. Returns `Err` on a body the evaluator doesn't
/// recognise so we don't silently miss new IR shapes.
fn parse_body(rule: &str) -> Result<Vec<Predicate>, String> {
    let body = rule
        .split_once(":-")
        .map(|(_head, body)| body.trim())
        .ok_or_else(|| format!("rule has no `:-`: {rule}"))?;
    let body = body.trim_end_matches('.').trim();
    let mut out = Vec::new();
    for raw in split_top_level_commas(body) {
        let chunk = raw.trim();
        if chunk.is_empty() {
            continue;
        }
        out.push(parse_predicate(chunk)?);
    }
    Ok(out)
}

/// Split on commas not inside `(...)` so `member_of(X, S)` survives.
fn split_top_level_commas(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut buf = String::new();
    for ch in s.chars() {
        match ch {
            '(' => {
                depth += 1;
                buf.push(ch);
            }
            ')' => {
                depth -= 1;
                buf.push(ch);
            }
            ',' if depth == 0 => {
                if !buf.is_empty() {
                    out.push(buf.clone());
                    buf.clear();
                }
            }
            _ => buf.push(ch),
        }
    }
    if !buf.trim().is_empty() {
        out.push(buf);
    }
    out
}

#[derive(Debug)]
enum Predicate {
    /// A `name(Var)` fact-lookup binding — emitted by gen_datalog for every
    /// param. We accept-and-ignore: the value is already in the bindings.
    FactLookup { name: String, var: String },
    /// `Lhs OP Rhs` arithmetic constraint.
    BinaryOp { lhs: String, op: BinOp, rhs: String },
    /// `member_of(Element, Set)`.
    Member { element: String, set: String },
    /// `bit_range(V, N)` — value fits in N bits.
    BitRange { var: String, bits: u32 },
}

#[derive(Debug)]
enum BinOp {
    Le,
    Ge,
    Eq,
    Ne,
}

fn parse_predicate(s: &str) -> Result<Predicate, String> {
    let s = s.trim();
    // member_of(E, S)
    if let Some(rest) = s.strip_prefix("member_of(") {
        let rest = rest.trim_end_matches(')').trim();
        let (e, sname) = rest
            .split_once(',')
            .ok_or_else(|| format!("malformed member_of: {s}"))?;
        return Ok(Predicate::Member {
            element: e.trim().to_string(),
            set: sname.trim().to_string(),
        });
    }
    // bit_range(V, N)
    if let Some(rest) = s.strip_prefix("bit_range(") {
        let rest = rest.trim_end_matches(')').trim();
        let (v, n) = rest
            .split_once(',')
            .ok_or_else(|| format!("malformed bit_range: {s}"))?;
        let bits: u32 = n
            .trim()
            .parse()
            .map_err(|e| format!("bit_range N parse: {e}"))?;
        return Ok(Predicate::BitRange {
            var: v.trim().to_string(),
            bits,
        });
    }
    // Arithmetic op: try longest operators first
    for (sep, op) in [
        ("<=", BinOp::Le),
        (">=", BinOp::Ge),
        ("==", BinOp::Eq),
        ("!=", BinOp::Ne),
    ] {
        if let Some((l, r)) = s.split_once(sep) {
            return Ok(Predicate::BinaryOp {
                lhs: l.trim().to_string(),
                op,
                rhs: r.trim().to_string(),
            });
        }
    }
    // Otherwise treat as `name(Var)` fact lookup.
    if let Some((name, rest)) = s.split_once('(') {
        let var = rest.trim_end_matches(')').trim();
        return Ok(Predicate::FactLookup {
            name: name.trim().to_string(),
            var: var.to_string(),
        });
    }
    Err(format!("unrecognised Datalog atom: {s}"))
}

/// Evaluate the rule against the bindings. Returns `Ok(true)` if every
/// arithmetic / membership predicate is satisfied.
pub fn evaluate(rule: &str, bindings: &Bindings) -> Result<bool, String> {
    let preds = parse_body(rule)?;
    for pred in &preds {
        match pred {
            Predicate::FactLookup { .. } => {
                // Fact-lookups just bind variables; they always succeed.
            }
            Predicate::BinaryOp { lhs, op, rhs } => {
                let lv = resolve(lhs, bindings)?;
                let rv = resolve(rhs, bindings)?;
                let ok = match (lv, rv, op) {
                    (Value::U64(l), Value::U64(r), BinOp::Le) => l <= r,
                    (Value::U64(l), Value::U64(r), BinOp::Ge) => l >= r,
                    (Value::U64(l), Value::U64(r), BinOp::Eq) => l == r,
                    (Value::U64(l), Value::U64(r), BinOp::Ne) => l != r,
                    (Value::Bytes(l), Value::Bytes(r), BinOp::Eq) => l == r,
                    (Value::Bytes(l), Value::Bytes(r), BinOp::Ne) => l != r,
                    (l, r, _) => {
                        return Err(format!(
                            "Datalog op type mismatch: {l:?} vs {r:?} for {op:?}"
                        ));
                    }
                };
                if !ok {
                    return Ok(false);
                }
            }
            Predicate::Member { element, set } => {
                let e = match resolve(element, bindings)? {
                    Value::U64(v) => v,
                    other => {
                        return Err(format!("member_of element must be u64, got {other:?}"));
                    }
                };
                let set_name = set.to_lowercase();
                let set_val = bindings
                    .sets
                    .iter()
                    .find(|(n, _)| n == &set_name)
                    .map(|(_, v)| v)
                    .ok_or_else(|| {
                        format!("Datalog set `{set}` not bound (lower-cased to `{set_name}`)")
                    })?;
                if !set_val.contains(&e) {
                    return Ok(false);
                }
            }
            Predicate::BitRange { var, bits } => {
                let v = match resolve(var, bindings)? {
                    Value::U64(v) => v,
                    other => return Err(format!("bit_range variable must be u64, got {other:?}")),
                };
                if *bits >= 64 {
                    continue; // u64 always fits in 64 bits
                }
                let bound = 1u128 << *bits;
                if (v as u128) >= bound {
                    return Ok(false);
                }
            }
        }
    }
    Ok(true)
}

#[derive(Debug)]
enum Value {
    U64(u64),
    Bytes([u8; 32]),
}

fn resolve(name: &str, bindings: &Bindings) -> Result<Value, String> {
    // Numeric literal?
    if let Ok(v) = name.parse::<u64>() {
        return Ok(Value::U64(v));
    }
    let key = name.to_lowercase();
    if let Some((_, v)) = bindings.u64_vars.iter().find(|(n, _)| n == &key) {
        return Ok(Value::U64(*v));
    }
    if let Some((_, v)) = bindings.bytes_vars.iter().find(|(n, _)| n == &key) {
        return Ok(Value::Bytes(*v));
    }
    Err(format!("unbound Datalog variable `{name}`"))
}

/// Build bindings from the IR-level `Requirement` list. The DSL emits each
/// `require!()` with positional placeholders, so we synthesize names that
/// match what `gen_datalog` produced (which mirrors the original Rust
/// parameter names). The harness in `tests/differential.rs` is responsible
/// for providing the exact name mapping per predicate.
pub fn bindings_for_requirements(
    requirements: &[Requirement],
    param_names: &[&str],
) -> Result<Bindings, String> {
    let mut b = Bindings::new();
    let mut u64_idx = 0usize;
    let mut bytes_idx = 0usize;
    let mut set_idx = 0usize;
    for req in requirements {
        match req {
            Requirement::LessEqualU64(l, r)
            | Requirement::GreaterEqualU64(l, r)
            | Requirement::EqualU64(l, r)
            | Requirement::NotEqualU64(l, r) => {
                if u64_idx + 1 >= param_names.len() {
                    return Err(format!(
                        "not enough param names for u64 pair; have {}, need at least {}",
                        param_names.len(),
                        u64_idx + 2,
                    ));
                }
                b = b.with_u64(param_names[u64_idx], *l);
                b = b.with_u64(param_names[u64_idx + 1], *r);
                u64_idx += 2;
            }
            Requirement::EqualBytes32(l, r) | Requirement::NotEqualBytes32(l, r) => {
                if bytes_idx + 1 >= param_names.len() {
                    return Err(format!(
                        "not enough param names for bytes pair; have {}, need at least {}",
                        param_names.len(),
                        bytes_idx + 2,
                    ));
                }
                b = b.with_bytes(param_names[bytes_idx], *l);
                b = b.with_bytes(param_names[bytes_idx + 1], *r);
                bytes_idx += 2;
            }
            Requirement::Membership { set, element } => {
                if set_idx + u64_idx + 1 >= param_names.len() {
                    return Err(format!(
                        "not enough param names for membership; have {}",
                        param_names.len()
                    ));
                }
                b = b.with_set(param_names[set_idx], set.clone());
                b = b.with_u64(param_names[set_idx + 1], *element);
                set_idx += 2;
            }
        }
    }
    Ok(b)
}
