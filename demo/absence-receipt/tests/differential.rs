//! Differential test: the demo's absence table (`dregg_dfa::Re::compile` + `Dfa::minimize`) against
//! the demo's former interim compiler, kept here verbatim as the differential partner, and against
//! a hand-written scanner for the two policy patterns.
//!
//! The interim compiler (commit ddb1cba92, `src/main.rs`) normalized to its own ACI form before
//! each lookup, derived over all 256 bytes, and Moore-minimized. It ran on the crate's derivative
//! as it stood then (top-pair-only `or`/`and`, left-nested `then`), so that derivative and its
//! smart constructors are frozen below too: the partner shares no normalization code with the
//! crate as it is now.
//!
//! ```text
//! cargo test --manifest-path demo/absence-receipt/Cargo.toml --release --test differential
//! ```

use std::collections::{BTreeSet, HashMap, VecDeque};

use absence_receipt::{absence_re, absence_table};
use dregg_dfa::{Dfa, Re};

const POLICY: &str = include_str!("../policy.txt");

// ---------------------------------------------------------------------------------------------
// The frozen partner: the crate's derivative before the ACI canonical form, and the interim
// compiler's norm / determinize / minimize.
// ---------------------------------------------------------------------------------------------

fn old_then(l: Re, r: Re) -> Re {
    match (l, r) {
        (Re::Empty, _) | (_, Re::Empty) => Re::Empty,
        (Re::Epsilon, r) => r,
        (l, Re::Epsilon) => l,
        (l, r) => Re::Cat(Box::new(l), Box::new(r)),
    }
}

fn old_or(l: Re, r: Re) -> Re {
    match (l, r) {
        (Re::Empty, r) => r,
        (l, Re::Empty) => l,
        (l, r) if l == r => l,
        (l, r) => {
            let (a, b) = if l <= r { (l, r) } else { (r, l) };
            Re::Alt(Box::new(a), Box::new(b))
        }
    }
}

fn old_and(l: Re, r: Re) -> Re {
    match (l, r) {
        (Re::Empty, _) | (_, Re::Empty) => Re::Empty,
        (l, r) if l == r => l,
        (l, r) => {
            let (a, b) = if l <= r { (l, r) } else { (r, l) };
            Re::Inter(Box::new(a), Box::new(b))
        }
    }
}

fn old_not(r: Re) -> Re {
    match r {
        Re::Neg(inner) => *inner,
        r => Re::Neg(Box::new(r)),
    }
}

fn old_star(r: Re) -> Re {
    match r {
        Re::Empty | Re::Epsilon => Re::Epsilon,
        Re::Star(_) => r,
        r => Re::Star(Box::new(r)),
    }
}

fn old_nullable(r: &Re) -> bool {
    match r {
        Re::Empty | Re::Sym(_) => false,
        Re::Epsilon | Re::Star(_) => true,
        Re::Cat(l, r) | Re::Inter(l, r) => old_nullable(l) && old_nullable(r),
        Re::Alt(l, r) => old_nullable(l) || old_nullable(r),
        Re::Neg(r) => !old_nullable(r),
    }
}

fn old_derive(re: &Re, b: u8) -> Re {
    match re {
        Re::Empty | Re::Epsilon => Re::Empty,
        Re::Sym(class) => {
            if class.contains(b) {
                Re::Epsilon
            } else {
                Re::Empty
            }
        }
        Re::Cat(l, r) => {
            let dl = old_then(old_derive(l, b), (**r).clone());
            if old_nullable(l) {
                old_or(dl, old_derive(r, b))
            } else {
                dl
            }
        }
        Re::Alt(l, r) => old_or(old_derive(l, b), old_derive(r, b)),
        Re::Inter(l, r) => old_and(old_derive(l, b), old_derive(r, b)),
        Re::Neg(r) => old_not(old_derive(r, b)),
        Re::Star(r) => old_then(old_derive(r, b), re.clone()),
    }
}

fn flatten(r: Re, alt: bool, out: &mut Vec<Re>) {
    match r {
        Re::Alt(l, rr) if alt => {
            flatten(*l, alt, out);
            flatten(*rr, alt, out);
        }
        Re::Inter(l, rr) if !alt => {
            flatten(*l, alt, out);
            flatten(*rr, alt, out);
        }
        other => out.push(other),
    }
}

fn flatten_cat(r: Re, out: &mut Vec<Re>) {
    match r {
        Re::Cat(l, rr) => {
            flatten_cat(*l, out);
            flatten_cat(*rr, out);
        }
        other => out.push(other),
    }
}

fn norm(r: Re) -> Re {
    match r {
        Re::Alt(..) | Re::Inter(..) => {
            let alt = matches!(r, Re::Alt(..));
            let mut parts = Vec::new();
            flatten(r, alt, &mut parts);
            let mut parts: Vec<Re> = parts.into_iter().map(norm).collect();
            let mut flat = Vec::new();
            for p in parts.drain(..) {
                flatten(p, alt, &mut flat);
            }
            flat.sort();
            flat.dedup();
            if alt {
                flat.retain(|p| !matches!(p, Re::Empty));
            } else if flat.iter().any(|p| matches!(p, Re::Empty)) {
                return Re::Empty;
            }
            let Some(last) = flat.pop() else {
                return Re::Empty;
            };
            flat.into_iter().rev().fold(last, |acc, p| {
                if alt {
                    Re::Alt(Box::new(p), Box::new(acc))
                } else {
                    Re::Inter(Box::new(p), Box::new(acc))
                }
            })
        }
        Re::Cat(..) => {
            let mut parts = Vec::new();
            flatten_cat(r, &mut parts);
            let parts: Vec<Re> = parts.into_iter().map(norm).collect();
            parts
                .into_iter()
                .rev()
                .fold(Re::Epsilon, |acc, p| old_then(p, acc))
        }
        Re::Neg(x) => old_not(norm(*x)),
        Re::Star(x) => old_star(norm(*x)),
        leaf => leaf,
    }
}

fn interim_determinize(re: Re) -> Dfa {
    let start = norm(re);
    let mut ids: HashMap<Re, u32> = HashMap::new();
    let mut order: Vec<Re> = vec![Re::Empty];
    ids.insert(Re::Empty, 0);
    let mut transitions: Vec<u32> = vec![0; 256];
    let mut accepting = BTreeSet::new();
    order.push(start.clone());
    ids.entry(start.clone()).or_insert(1);
    transitions.extend(std::iter::repeat_n(0, 256));
    if old_nullable(&start) {
        accepting.insert(1u32);
    }
    let mut i = 1usize;
    while i < order.len() {
        let cur = order[i].clone();
        for b in 0..=255u8 {
            let next = norm(old_derive(&cur, b));
            let id = if let Some(&id) = ids.get(&next) {
                id
            } else {
                let id = order.len() as u32;
                ids.insert(next.clone(), id);
                if old_nullable(&next) {
                    accepting.insert(id);
                }
                order.push(next);
                transitions.extend(std::iter::repeat_n(0, 256));
                id
            };
            transitions[i * 256 + b as usize] = id;
        }
        i += 1;
    }
    Dfa {
        num_states: order.len() as u32,
        transitions,
        start: 1,
        accepting,
    }
}

fn interim_minimize(d: &Dfa) -> Dfa {
    let n = d.num_states as usize;
    let mut class: Vec<u32> = (0..n)
        .map(|s| u32::from(d.accepting.contains(&(s as u32))))
        .collect();
    loop {
        let mut sig: HashMap<(u32, Vec<u32>), u32> = HashMap::new();
        let mut next = vec![0u32; n];
        for s in 0..n {
            let row: Vec<u32> = (0..256)
                .map(|b| class[d.transitions[s * 256 + b] as usize])
                .collect();
            let k = (class[s], row);
            let len = sig.len() as u32;
            next[s] = *sig.entry(k).or_insert(len);
        }
        let before = class.iter().collect::<BTreeSet<_>>().len();
        let after = sig.len();
        class = next;
        if after == before {
            break;
        }
    }
    let mut map: HashMap<u32, u32> = HashMap::new();
    map.insert(class[0], 0);
    let start_class = class[d.start as usize];
    let mut reps: Vec<usize> = vec![0];
    let mut queue = VecDeque::new();
    if let std::collections::hash_map::Entry::Vacant(e) = map.entry(start_class) {
        e.insert(1);
        reps.push(d.start as usize);
    }
    queue.push_back(d.start as usize);
    let mut seen = BTreeSet::new();
    seen.insert(d.start as usize);
    while let Some(s) = queue.pop_front() {
        for b in 0..256 {
            let t = d.transitions[s * 256 + b] as usize;
            if let std::collections::hash_map::Entry::Vacant(e) = map.entry(class[t]) {
                e.insert(reps.len() as u32);
                reps.push(t);
            }
            if seen.insert(t) {
                queue.push_back(t);
            }
        }
    }
    let mut transitions = Vec::with_capacity(reps.len() * 256);
    let mut accepting = BTreeSet::new();
    for (new, &old) in reps.iter().enumerate() {
        for b in 0..256 {
            transitions.push(map[&class[d.transitions[old * 256 + b] as usize]]);
        }
        if d.accepting.contains(&(old as u32)) {
            accepting.insert(new as u32);
        }
    }
    let start = if class[d.start as usize] == class[0] {
        0
    } else {
        1
    };
    Dfa {
        num_states: reps.len() as u32,
        transitions,
        start,
        accepting,
    }
}

/// The interim pipeline on the raw (uncanonicalized) policy term, as the demo built it then.
fn interim_table() -> (Dfa, Dfa) {
    let pats = absence_receipt::policy_patterns(POLICY).unwrap();
    let mut union = Re::Empty;
    for p in pats {
        union = old_or(
            union,
            raw(absence_receipt::parse_pattern(p.as_bytes()).unwrap()),
        );
    }
    let any = old_star(Re::Sym(dregg_dfa::ByteClass::full()));
    let re = old_not(old_then(old_then(any.clone(), union), any));
    let det = interim_determinize(re);
    let min = interim_minimize(&det);
    (det, min)
}

/// The parser now builds through the canonical smart constructors; re-associate its
/// concatenations to the left, as the old left-folding `then` produced them, so the partner sees
/// the term it saw then (`norm` re-associates anyway; this only keeps the input honest).
fn raw(r: Re) -> Re {
    let mut parts = Vec::new();
    flatten_cat(r, &mut parts);
    parts.into_iter().fold(Re::Epsilon, old_then)
}

// ---------------------------------------------------------------------------------------------
// The independent oracle: a direct scan for the two policy patterns.
// ---------------------------------------------------------------------------------------------

fn contains_aws_key(w: &[u8]) -> bool {
    (0..w.len()).any(|i| {
        w[i..].starts_with(b"AKIA")
            && w.len() >= i + 20
            && w[i + 4..i + 20]
                .iter()
                .all(|c| c.is_ascii_digit() || c.is_ascii_uppercase())
    })
}

fn contains_pem_header(w: &[u8]) -> bool {
    let open = b"-----BEGIN ";
    let close = b"PRIVATE KEY-----";
    (0..w.len()).any(|i| {
        if !w[i..].starts_with(open) {
            return false;
        }
        let mut k = i + open.len();
        loop {
            if w[k..].starts_with(close) {
                return true;
            }
            match w.get(k) {
                Some(c) if c.is_ascii_uppercase() || *c == b' ' => k += 1,
                _ => return false,
            }
        }
    })
}

fn oracle_accepts(w: &[u8]) -> bool {
    !contains_aws_key(w) && !contains_pem_header(w)
}

// ---------------------------------------------------------------------------------------------
// Words: controls, and 10,000 seeded random strings biased toward the patterns.
// ---------------------------------------------------------------------------------------------

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

fn pem(kind: &str) -> Vec<u8> {
    // Built from parts: the repository's secret scanner refuses PEM-header literals.
    format!("{}BEGIN {kind}{}{}", "-----", "PRIVATE KEY", "-----").into_bytes()
}

fn controls() -> Vec<(Vec<u8>, bool)> {
    vec![
        (
            std::fs::read(concat!(env!("CARGO_MANIFEST_DIR"), "/controls/aws-key.txt")).unwrap(),
            false,
        ),
        (
            std::fs::read(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/controls/near-miss.txt"
            ))
            .unwrap(),
            true,
        ),
        (b"AKIAIOSFODNN7EXAMPLE".to_vec(), false),
        (b"AKIAIOSFODNN7EXAMPL".to_vec(), true),
        (b"AKIAiosfodnn7example".to_vec(), true),
        (pem("RSA "), false),
        (pem("OPENSSH "), false),
        (pem(""), false),
        (
            format!("{}BEGIN PUBLIC KEY{}", "-----", "-----").into_bytes(),
            true,
        ),
        (b"{\"name\":\"serde\",\"vers\":\"1.0.0\"}".to_vec(), true),
        (Vec::new(), true),
    ]
}

fn random_words() -> Vec<Vec<u8>> {
    let fragments: [&[u8]; 5] = [
        b"AKIA",
        b"AKIAIOSFODNN7EXAMPLE",
        b"-----BEGIN ",
        b"RSA ",
        b"PRIVATE KEY-----",
    ];
    let mut rng = Rng(0xab5e_9ce1);
    (0..10_000)
        .map(|i| {
            let len = rng.below(64);
            let mut w = Vec::new();
            if i % 4 == 0 {
                w.extend((0..len).map(|_| rng.next() as u8));
            } else {
                while w.len() < len {
                    match rng.below(5) {
                        0 => w.push(rng.next() as u8),
                        1 | 2 => w.push(b"0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ "[rng.below(37)]),
                        _ => {
                            let f = fragments[rng.below(fragments.len())];
                            let a = rng.below(f.len());
                            let b = a + 1 + rng.below(f.len() - a);
                            w.extend_from_slice(if rng.below(3) == 0 { &f[a..b] } else { f });
                        }
                    }
                }
            }
            w
        })
        .collect()
}

#[test]
fn crate_compiler_agrees_with_the_interim_compiler_and_the_scanner() {
    let table = absence_table(POLICY).unwrap();
    let unminimized = absence_re(POLICY).unwrap().compile();
    let (interim_det, interim_min) = interim_table();
    eprintln!(
        "crate: {} states, {} minimized; interim: {} states, {} minimized",
        unminimized.num_states, table.num_states, interim_det.num_states, interim_min.num_states
    );
    assert_eq!(
        interim_det.num_states, 9_153,
        "the interim compiler's pinned size"
    );
    assert_eq!(interim_min.num_states, 129);
    assert_eq!(table.num_states, 129);
    assert_eq!(unminimized.minimize().transitions, table.transitions);
    // Same minimal automaton up to numbering; both number canonically, so the tables are equal.
    assert_eq!(table.transitions, interim_min.transitions);
    assert_eq!(table.accepting, interim_min.accepting);

    for (w, want) in controls() {
        assert_eq!(oracle_accepts(&w), want, "oracle on control {w:?}");
        assert_eq!(table.matches(&w), want, "crate table on control {w:?}");
        assert_eq!(
            interim_min.matches(&w),
            want,
            "interim table on control {w:?}"
        );
    }
    let mut rejected = 0usize;
    for w in random_words() {
        let want = oracle_accepts(&w);
        assert_eq!(table.matches(&w), want, "crate table vs scanner on {w:?}");
        assert_eq!(
            unminimized.matches(&w),
            want,
            "unminimized crate table on {w:?}"
        );
        assert_eq!(interim_min.matches(&w), want, "interim table on {w:?}");
        rejected += usize::from(!want);
    }
    eprintln!("random words rejected: {rejected} of 10000");
    assert!(
        rejected > 500 && rejected < 9_500,
        "both verdicts exercised: {rejected}"
    );
}

// ---------------------------------------------------------------------------------------------
// The third partner: lane B's `policyc compile --absence` (Lean, `absence_decides`), on the
// pattern it compiles in reasonable time. Its tables are checked in under `policyc/`.
// ---------------------------------------------------------------------------------------------

fn policyc_table(name: &str) -> Dfa {
    let path = format!("{}/policyc/{name}", env!("CARGO_MANIFEST_DIR"));
    serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap()
}

/// The crate's minimized absence table for one interim-syntax pattern.
fn crate_absence(pattern: &[u8]) -> Dfa {
    let p = absence_receipt::parse_pattern(pattern).unwrap();
    Re::top().then(p).then(Re::top()).not().compile().minimize()
}

/// Product automaton accepting the intersection (test-only; both tables have dead state 0).
fn product(a: &Dfa, b: &Dfa) -> Dfa {
    let mut ids: HashMap<(u32, u32), u32> = HashMap::new();
    let mut order = vec![(0u32, 0u32), (a.start, b.start)];
    ids.insert((0, 0), 0);
    ids.entry((a.start, b.start)).or_insert(1);
    let mut transitions = Vec::new();
    let mut accepting = BTreeSet::new();
    let mut i = 0;
    while i < order.len() {
        let (p, q) = order[i];
        if a.accepting.contains(&p) && b.accepting.contains(&q) {
            accepting.insert(i as u32);
        }
        for byte in 0..256 {
            let mut t = (
                a.transitions[p as usize * 256 + byte],
                b.transitions[q as usize * 256 + byte],
            );
            if t.0 == 0 || t.1 == 0 {
                t = (0, 0);
            }
            let next = order.len() as u32;
            let id = *ids.entry(t).or_insert_with(|| {
                order.push(t);
                next
            });
            transitions.push(id);
        }
        i += 1;
    }
    Dfa {
        num_states: order.len() as u32,
        transitions,
        start: 1,
        accepting,
    }
}

#[test]
fn policyc_tables_minimize_to_the_crate_tables() {
    let pem = policyc_table("pem-absence.json");
    let aws = policyc_table("aws-absence.json");
    let crate_pem = crate_absence(b"-----BEGIN [A-Z ]*PRIVATE KEY-----");
    let crate_aws = crate_absence(b"AKIA[0-9A-Z]{16}");
    for (name, lean, ours) in [("PEM", &pem, &crate_pem), ("AWS", &aws, &crate_aws)] {
        let min = lean.minimize();
        eprintln!(
            "{name} absence: policyc {} states ({} minimized), crate {} minimized",
            lean.num_states, min.num_states, ours.num_states
        );
        assert_eq!(min.transitions, ours.transitions, "{name}");
        assert_eq!(min.accepting, ours.accepting, "{name}");
    }
    // The two Lean tables jointly are the policy: their product minimizes to the demo's table.
    let joint = product(&aws, &pem).minimize();
    let table = absence_table(POLICY).unwrap();
    assert_eq!(joint.num_states, 129);
    assert_eq!(joint.transitions, table.transitions);
    assert_eq!(joint.accepting, table.accepting);
    for w in random_words()
        .iter()
        .chain(controls().iter().map(|(w, _)| w))
    {
        assert_eq!(
            pem.matches(w),
            !contains_pem_header(w),
            "policyc PEM vs scanner on {w:?}"
        );
        assert_eq!(
            aws.matches(w),
            !contains_aws_key(w),
            "policyc AWS vs scanner on {w:?}"
        );
    }
}

// ---------------------------------------------------------------------------------------------
// The receipt's table is policyc's output for the whole policy (`policy.policy`, one pattern
// `secrets` with both alternatives). It must be the crate's table up to state numbering: its
// minimization equals `absence_table(POLICY)` cell for cell, and it agrees with the scanner.
// ---------------------------------------------------------------------------------------------

#[test]
fn receipt_table_is_the_crate_table_after_minimize() {
    let path = format!("{}/absence-table.json", env!("CARGO_MANIFEST_DIR"));
    let receipt: Dfa = serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
    let table = absence_table(POLICY).unwrap();
    assert_eq!(receipt.num_states, 129, "policyc emits the minimal table");
    let min = receipt.minimize();
    assert_eq!(min.num_states, table.num_states);
    assert_eq!(min.start, table.start);
    assert_eq!(min.transitions, table.transitions);
    assert_eq!(min.accepting, table.accepting);
    for (w, expect) in random_words()
        .into_iter()
        .map(|w| {
            let e = oracle_accepts(&w);
            (w, e)
        })
        .chain(controls())
    {
        assert_eq!(
            receipt.matches(&w),
            expect,
            "receipt table vs scanner on {w:?}"
        );
    }
}
