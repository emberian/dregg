//! absence-receipt's policy leg: the interim policy syntax and the absence table it compiles to.
//!
//! Policy lines `forbid <pattern>`; the pattern subset is literal bytes, `\\x` escapes, `.`,
//! `[..]` classes with ranges, and the postfix operators `* + ? {n}` on one atom. The absence table
//! is `~(any* · (P1 | P2 | ...) · any*)` compiled by `dregg_dfa::Re::compile` (derivatives over the
//! crate's ACI canonical form) and `dregg_dfa::Dfa::minimize`. The table is differential-tested,
//! not proved: `tests/differential.rs` checks it against the demo's former interim compiler and a
//! hand-written scanner. The policy grammar here is a second grammar outside Lean, kept until lane
//! B's `policyc compile --absence` emits the table.

use dregg_dfa::{ByteClass, Dfa, Re};

pub fn parse_class(p: &[u8], i: &mut usize) -> Result<ByteClass, String> {
    let mut ranges = Vec::new();
    let negate = p.get(*i) == Some(&b'^');
    if negate {
        *i += 1;
    }
    loop {
        let Some(&c) = p.get(*i) else {
            return Err("unterminated [".into());
        };
        *i += 1;
        if c == b']' {
            break;
        }
        let lo = if c == b'\\' {
            let e = *p.get(*i).ok_or("dangling \\")?;
            *i += 1;
            e
        } else {
            c
        };
        if p.get(*i) == Some(&b'-') && p.get(*i + 1).is_some_and(|&n| n != b']') {
            let hi = p[*i + 1];
            *i += 2;
            ranges.push((lo, hi));
        } else {
            ranges.push((lo, lo));
        }
    }
    let class = ByteClass::from_ranges(ranges);
    Ok(if negate { class.complement() } else { class })
}

pub fn parse_pattern(p: &[u8]) -> Result<Re, String> {
    let mut i = 0;
    let mut seq = Re::epsilon();
    while i < p.len() {
        let atom = match p[i] {
            b'[' => {
                i += 1;
                Re::sym(parse_class(p, &mut i)?)
            }
            b'.' => {
                i += 1;
                Re::any_byte()
            }
            b'\\' => {
                let e = *p.get(i + 1).ok_or("dangling \\")?;
                i += 2;
                Re::byte(e)
            }
            b'(' | b')' | b'|' => {
                return Err("groups and alternation are not in the interim subset".into());
            }
            c => {
                i += 1;
                Re::byte(c)
            }
        };
        let atom = match p.get(i) {
            Some(b'*') => {
                i += 1;
                atom.star()
            }
            Some(b'+') => {
                i += 1;
                atom.clone().then(atom.star())
            }
            Some(b'?') => {
                i += 1;
                atom.or(Re::epsilon())
            }
            Some(b'{') => {
                let close = p[i..]
                    .iter()
                    .position(|&c| c == b'}')
                    .ok_or("unterminated {")?
                    + i;
                let n: usize = std::str::from_utf8(&p[i + 1..close])
                    .ok()
                    .and_then(|s| s.parse().ok())
                    .ok_or("bad {n}")?;
                i = close + 1;
                (0..n).fold(Re::epsilon(), |acc, _| acc.then(atom.clone()))
            }
            _ => atom,
        };
        seq = seq.then(atom);
    }
    Ok(seq)
}

pub fn policy_patterns(policy: &str) -> Result<Vec<String>, String> {
    let mut pats = Vec::new();
    for line in policy.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let rest = line
            .strip_prefix("forbid ")
            .ok_or_else(|| format!("not a forbid line: {line}"))?;
        pats.push(rest.to_owned());
    }
    if pats.is_empty() {
        return Err("policy forbids nothing".into());
    }
    Ok(pats)
}

/// `~(any* · (P1 | P2 | ...) · any*)` for the policy's patterns, uncompiled.
pub fn absence_re(policy: &str) -> Result<Re, String> {
    let mut union = Re::empty();
    for pat in policy_patterns(policy)? {
        union = union.or(parse_pattern(pat.as_bytes())?);
    }
    Ok(Re::top().then(union).then(Re::top()).not())
}

/// The absence table: the crate's derivative compiler, then Moore minimization (canonical
/// numbering: dead 0, start 1, breadth-first over bytes).
pub fn absence_table(policy: &str) -> Result<Dfa, String> {
    Ok(absence_re(policy)?.compile().minimize())
}
