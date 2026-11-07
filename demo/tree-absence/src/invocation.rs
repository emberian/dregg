//! Query (B): `pkill -f` at command position. Same expression three ways: the policy-language
//! source `query-invocation.policy` (documentation, and where the pattern's limits are stated),
//! the dregg-dfa derivative expression `invocation_re` (compiled and minimized into the table the
//! certificate commits), and the `regex` crate oracle `invocation_oracle` (the differential).
//!
//!   any* · BOUNDARY · [ \t]* · (WRAP [ \t]+)* · "pkill" ([ \t]+ "-" [A-Za-z0-9]+)* [ \t]+ "-" [A-Za-z0-9]* "f" · any*
//!
//! BOUNDARY is start-of-string or one of `\n ; & | ( \`` (`$(` ends in `(`); query (C) drops the
//! backtick (`backtick = false`), so it misses `` `pkill -f x` `` substitution and does not
//! over-count prose code spans. WRAP is one of
//! `sudo env xargs nohup exec command time`, or `timeout` [ \t]+ [0-9]+ [smh]?.

use dregg_dfa::Re;

const WRAPS: [&str; 7] = ["sudo", "env", "xargs", "nohup", "exec", "command", "time"];

fn alt(rs: impl IntoIterator<Item = Re>) -> Re {
    rs.into_iter().fold(Re::empty(), Re::or)
}

fn plus(r: Re) -> Re {
    r.clone().then(r.star())
}

fn opt(r: Re) -> Re {
    Re::epsilon().or(r)
}

/// The whole-string expression (search semantics written out with `any*` on both sides).
pub fn invocation_re(backtick: bool) -> Re {
    let ws = || alt([Re::byte(b' '), Re::byte(b'\t')]);
    let alnum = || alt([Re::range(b'A', b'Z'), Re::range(b'a', b'z'), Re::range(b'0', b'9')]);
    let bytes: &[u8] = if backtick { b"\n;&|(`" } else { b"\n;&|(" };
    let boundary = alt(bytes.iter().map(|&b| Re::byte(b)));
    let start = opt(Re::top().then(boundary));
    let timeout = Re::word(b"timeout")
        .then(plus(ws()))
        .then(plus(Re::range(b'0', b'9')))
        .then(opt(alt([Re::byte(b's'), Re::byte(b'm'), Re::byte(b'h')])));
    let wrap = alt(WRAPS.iter().map(|w| Re::word(w.as_bytes()))).or(timeout);
    let flag = plus(ws()).then(Re::byte(b'-')).then(plus(alnum()));
    start
        .then(ws().star())
        .then(wrap.then(plus(ws())).star())
        .then(Re::word(b"pkill"))
        .then(flag.star())
        .then(plus(ws()))
        .then(Re::byte(b'-'))
        .then(alnum().star())
        .then(Re::byte(b'f'))
        .then(Re::top())
}

/// The same pattern for the `regex` crate (bytes, search semantics).
pub fn invocation_oracle(backtick: bool) -> regex::bytes::Regex {
    let b = if backtick { "`" } else { "" };
    regex::bytes::Regex::new(&format!(
        r"(?-u)(?:^|[\n;&|({b}])[ \t]*(?:(?:sudo|env|xargs|nohup|exec|command|time|timeout[ \t]+[0-9]+[smh]?)[ \t]+)*pkill(?:[ \t]+-[A-Za-z0-9]+)*[ \t]+-[A-Za-z0-9]*f"
    ))
    .expect("oracle regex")
}

/// Hand-written cases: (command, (B) matches, (C) matches).
pub const CASES: &[(&str, bool, bool)] = &[
    ("pkill -f x", true, true),
    ("pkill -f", true, true),
    ("  pkill -f x", true, true),
    ("ls; pkill -fl x", true, true),
    ("ls;pkill -f x", true, true),
    ("make && pkill -f x", true, true),
    ("a || pkill -f x", true, true),
    ("cat x | xargs pkill -f", true, true),
    ("sudo pkill -9 -f x", true, true),
    ("sudo env nohup pkill -f x", true, true),
    ("echo $(pkill -f x)", true, true),
    ("echo `pkill -f x`", true, false),
    ("`pkill -f x`", true, false),
    ("(pkill -f x)", true, true),
    ("timeout 5 pkill -f x", true, true),
    ("timeout 5s pkill -f x", true, true),
    ("exec pkill -fx node", true, true),
    ("command pkill -f x", true, true),
    ("time pkill -f x", true, true),
    ("ls\npkill -f x", true, true),
    ("pkill -u ember -f x", false, false), // `-u ember`: the argument is not a flag; stated limit
    ("pkill\t-f\tx", true, true),
    ("echo \"pkill -f\"", false, false),
    ("# pkill -f", false, false),
    ("rg 'pkill -f'", false, false),
    ("grep -n \"pkill -f\" notes.md", false, false),
    ("pkill x", false, false),
    ("pkill -9 x", false, false),
    ("pkill --full x", false, false),
    ("xpkill -f x", false, false),
    ("ls pkill -f x", false, false),
    ("timeout pkill -f x", false, false),
    ("kill $(pgrep -f x)", false, false),
    ("bash -c 'pkill -f x'", false, false),
    ("cat <<EOF\npkill -f x\nEOF", true, true), // over-counted: a heredoc line is not a command
    ("", false, false),
];
