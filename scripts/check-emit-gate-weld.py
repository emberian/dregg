#!/usr/bin/env python3
"""check-emit-gate-weld.py — THE CROSS-LANGUAGE WELD GATE for the emit-gate pairs.

Each `circuit-prove/tests/*_emit_gate.rs` embeds a GOLDEN_JSON string literal that is
DOCUMENTED as byte-identical to a `#guard emitVmJson2 <desc> == "..."` (or v1
`emitJson`/`emitVmJson`) string in a `metatheory/Dregg2/Circuit/Emit/*.lean` file.
The Lean `#guard` pins the Lean side (checked at `lake build` time); the Rust test
pins the Rust side (checked at `cargo test` time). But NOTHING EXECUTABLE compared
the two literals to each other: each side is welded only to itself, so the pair can
drift while both stay green — a gate comparing two checked-in copies of the same
claim validates nothing about their agreement.

This script closes that seam STATICALLY (no lake, no cargo, <1s):
  1. For every emit-gate Rust file, extract each raw-string descriptor literal
     (r#"{"name":...}"#) and parse its "name".
  2. Collect the AUTHORITATIVE pins: every #guard-pinned JSON string in the Lean
     tree (Lean escaped string literals whose payload parses as a descriptor with
     a "name"), plus every `circuit/descriptors/**.json` artifact (those are
     generate-fresh-gated by scripts/check-descriptor-drift.sh, so byte-equality
     to one of them inherits that gate).
  3. For each Rust golden, find a pin with the same descriptor name and require
     BYTE EQUALITY.

Exit 0 = every Rust golden is byte-identical to an authoritative pin.
Exit 1 = a drifted pair (named on both sides, bytes differ) or a Rust golden with
         no pin anywhere (an unwelded golden — its gate certifies only itself).

A drifted pair means one side moved and the other kept certifying the old bytes —
exactly the silent divergence the emit gates claim ("neither can silently diverge")
but could not themselves enforce.

Also prints (informational, non-gating) the reverse gap: Lean #guard-pinned
descriptor names with NO Rust-side counterpart at all (neither a test golden nor
a checked-in artifact) — Lean-emitted descriptors nothing on the Rust side
validates against.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GATES_DIR = ROOT / "circuit-prove" / "tests"
LEAN_DIRS = [ROOT / "metatheory" / "Dregg2" / "Circuit" / "Emit", ROOT / "metatheory"]

# ── SCOPE ─ this pair is the ONLY copy; it prints on every run, pass or fail. ─────────
SCOPE_ANSWERS = (
    "is every r#\"{...}\"# descriptor literal in circuit-prove/tests/*.rs and in every .rs "
    "under a src/ tree byte-identical to a same-NAMED string literal sitting in a "
    "metatheory/*.lean or metatheory/Dregg2/Circuit/Emit/*.lean file that contains the word "
    "#guard (those two directories, NOT recursive), or to a same-named circuit/descriptors "
    "artifact; is every `\"trace_width\":N` spelled inside a Rust string a width one of those "
    "pins carries; and is the count of unpinned src/ literals still at or below 66?"
)
SCOPE_DOES_NOT_ANSWER = (
    "whether EITHER side matches what Lean actually emits. This runs no lake and no cargo — it "
    "compares checked-in copies against checked-in copies, and inherits all of its authority "
    "from check-descriptor-drift.sh, which is the leg that re-derives. The src/ arm is a "
    "RATCHET, so green there means no NEW unpinned golden, not that the 66 already counted "
    "reproduce anything; and a golden byte-equal to its pin is still only byte-equal — nothing "
    "here says the descriptor is sound or that any test using it asserts something."
)

# ⚑ 2026-08-06 — THE SCAN WAS TEST-ONLY, AND THE COPY THAT WAS ACTUALLY BROKEN WAS IN `src/`.
# `zkoracle-prove/src/zk_leg.rs` carries an inline `dfa-routing-injection-3state::poseidon2-v1`
# golden on the PRODUCTION injection-leg path (`injection_descriptor()` -> `.expect(…)`), and the
# `challenges` flag day left it stale — so `prove_injection_leg`/`verify_injection_leg` PANIC at
# HEAD. This gate could not see it (`GATES_DIR` only), and its own INFO block therefore listed that
# descriptor as having "NO Rust-side counterpart" while a Rust-side counterpart was panicking two
# directories away. A weld gate that scans only tests measures where the goldens are TIDY, not
# where they are LOAD-BEARING. Every `.rs` under a `src/` tree is scanned now, on the same terms.
SRC_SKIP_DIRS = {"target", ".git", "node_modules", "vendor", "docs", ".cache", ".lake", "metatheory"}

# Rust raw-string literals that look like a descriptor JSON object.
RUST_RAW = re.compile(r'r#"(\{.*?\})"#', re.DOTALL)

# `include_str!("…json")` — a golden that is not a COPY at all. These need no weld: the file they
# name IS an authoritative pin (a `circuit/descriptors/**` artifact, drift-gated against Lean), so
# there are not two bytes to disagree. Counted and printed so a SHRINKING `checked` number cannot
# read as lost coverage — the population moves from "checked copies" to "no copy to check", which
# is the direction of the fix.
RUST_INCLUDE = re.compile(r'include_str!\(\s*"([^"]+\.json)"\s*\)')

# How many descriptor literals under a `src/` tree currently have NO authoritative pin. MEASURED
# 2026-08-06 at 66 the hour the src/ scan was added: 58 in `circuit/src/lean_descriptor_air.rs`
# (synthetic `#[cfg(test)]` descriptors — `dregg-dropRefA-v2`, `dregg-boundary-decode-v0`, … — that
# exercise the interpreter and are not emitted by anything), 3 in `circuit/src/descriptor_ir2.rs`
# (`demo-exact-public`, `batch-exact-a/b`), 2 in `descriptor_ir2_canonical.rs`, 3 in
# `dregg-lean-ffi/src/circuit_differential.rs`. It is a RATCHET, not an amnesty: it may shrink and
# may not grow.
SRC_UNPINNED_BASELINE = 66

# A Lean string literal (double-quoted, backslash escapes), possibly spanning lines.
LEAN_STR = re.compile(r'"((?:[^"\\]|\\.)*)"', re.DOTALL)

# ⚑⚑ 2026-08-06 — THE FRAGMENT PIN. Everything above matches a WHOLE descriptor object in a RAW
# string. That is not the only way a geometry number gets typed into Rust, and it is not the way
# that broke: `turn-prover/src/faithful_note_spend_exact_v3_verifier.rs` carried
#
#     const HEADER: &str = concat!(
#         "{\"name\":\"faithful-note-spend-v3-plan::exact-aafi-fns3-rotated-wide-state\",",
#         "\"ir\":2,\"trace_width\":3804,\"public_input_count\":76,"
#     );
#
# — a `concat!` of ESCAPED fragments, not a raw string; a PREFIX, not a parseable object. Every one
# of this gate's three structural requirements missed it (`r#"…"#`, starts with `{`, survives
# `json.loads`), and so did `mirror_gates.py` and `classify_descriptor_drift.py`, for the same
# reason. HEAD emitted 3826 after the 2026-08-01 KEY NONET; the literal said 3804; `strip_prefix`
# returned `None`; the test panicked at RUN TIME while `cargo check --all-targets` stayed green for
# five days. A number inside a string literal is invisible to every type check we have.
#
# So: find EVERY `trace_width` / `public_input_count` spelled with a number in Rust source,
# however it is quoted or concatenated, and require the number to be one an authoritative pin
# actually carries — by descriptor name where the fragment names one, by existence otherwise.
# ⚑ THE QUOTE IS LOAD-BEARING. `\"trace_width\":1811` is a number inside a STRING (invisible to
# every type check); `trace_width: 1811,` is a TYPED STRUCT FIELD (`umem_weld_generated.rs`'s 58
# rows), which is the shape we WANT and must never flag. Requiring the quote is the whole
# distinction, and dropping it made this leg 58/58 false-positive on its first run.
FRAGMENT_PIN = re.compile(r'\\?"trace_width\\?"\s*:\s*(\d+)')
PIN_WIDTH = re.compile(r'"trace_width"\s*:\s*(\d+)')


def lean_unescape(s: str) -> str:
    # Lean string escapes relevant here: \" \\ \n \t (descriptor JSON uses only \" and \\).
    out = []
    i = 0
    while i < len(s):
        c = s[i]
        if c == "\\" and i + 1 < len(s):
            n = s[i + 1]
            out.append({"n": "\n", "t": "\t", '"': '"', "\\": "\\"}.get(n, n))
            i += 2
        else:
            out.append(c)
            i += 1
    return "".join(out)


def descriptor_name(payload: str) -> str | None:
    if not payload.lstrip().startswith("{"):
        return None
    try:
        v = json.loads(payload)
    except json.JSONDecodeError:
        return None
    if isinstance(v, dict) and isinstance(v.get("name"), str) and "constraints" in v:
        return v["name"]
    return None


def collect_lean_pins() -> dict[str, list[tuple[Path, str]]]:
    pins: dict[str, list[tuple[Path, str]]] = {}
    seen: set[Path] = set()
    for d in LEAN_DIRS:
        for f in sorted(d.glob("*.lean")):
            if f in seen:
                continue
            seen.add(f)
            text = f.read_text(encoding="utf-8", errors="replace")
            if "#guard" not in text:
                continue
            for m in LEAN_STR.finditer(text):
                payload = lean_unescape(m.group(1))
                name = descriptor_name(payload)
                if name:
                    pins.setdefault(name, []).append((f, payload))
    return pins


def collect_artifact_pins() -> dict[str, list[tuple[Path, str]]]:
    """Every circuit/descriptors/**.json artifact, keyed by descriptor name.

    These are drift-gated by scripts/check-descriptor-drift.sh (generate-fresh
    from Lean), so a golden byte-equal to one of them inherits that gate. A
    trailing newline on the artifact is tolerated (the directory's convention is
    mixed and FP-pinned; a Rust golden never carries it).
    """
    pins: dict[str, list[tuple[Path, str]]] = {}
    desc_dir = ROOT / "circuit" / "descriptors"
    for f in sorted(desc_dir.rglob("*.json")):
        text = f.read_text(encoding="utf-8", errors="replace")
        name = descriptor_name(text)
        if name:
            pins.setdefault(name, []).append((f, text.rstrip("\n")))
    # The staged registries are TSVs of `key<TAB>name<TAB>json` rows — same authority
    # (emitted + drift-gated), just packed.
    for f in sorted(desc_dir.rglob("*.tsv")):
        for line in f.read_text(encoding="utf-8", errors="replace").splitlines():
            parts = line.split("\t")
            for cell in parts:
                name = descriptor_name(cell)
                if name:
                    pins.setdefault(name, []).append((f, cell))
    return pins


def _short(v: object, width: int = 96) -> str:
    s = json.dumps(v, sort_keys=True) if not isinstance(v, str) else repr(v)
    return s if len(s) <= width else s[: width - 1] + "…"


def drift_cause(rust_payload: str, pin_payload: str) -> str:
    """A one-line, GROUPABLE key for why a pair drifted — the set of differing top-level fields."""
    try:
        rj, pj = json.loads(rust_payload), json.loads(pin_payload)
    except json.JSONDecodeError:
        return "unparseable"
    if not (isinstance(rj, dict) and isinstance(pj, dict)):
        return "not-objects"
    ks = sorted(k for k in set(rj) | set(pj) if rj.get(k) != pj.get(k))
    return ", ".join(f"`{k}`" for k in ks) if ks else "serialisation only (same parsed object)"


def drift_detail(rust_payload: str, pin_payload: str) -> str:
    """Name WHAT differs, not how many constraints each side has.

    ⚑ 2026-08-05 — THE REPORT WAS UNREADABLE AND READ AS A BUG IN THE GATE. It printed
    `(Rust: 5 constraints / pin: 5 constraints)` — the SAME number twice, on all 15 drifted
    pairs — because the comparison is BYTE equality and the constraint count is a coarse
    summary that agrees right up until it does not. A reader sees two identical numbers under
    the word DRIFTED and concludes the reporter is printing one side twice; the actual finding
    (all 15 differ by ONE top-level field, `challenges`, which the Lean emission gained and the
    Rust goldens have not) was invisible in the output and took a hand-written differ to see.

    A gate must state the fact it reds on. This walks the two objects and names the first
    structural difference: keys only one side has, then the first field whose value differs.
    """
    try:
        rj, pj = json.loads(rust_payload), json.loads(pin_payload)
    except json.JSONDecodeError:
        return (
            f"    bytes differ and at least one side is not parseable JSON "
            f"(Rust {len(rust_payload)} B / pin {len(pin_payload)} B).\n"
        )
    if not (isinstance(rj, dict) and isinstance(pj, dict)):
        return "    bytes differ; the payloads are not both JSON objects.\n"

    lines: list[str] = []
    only_pin = sorted(set(pj) - set(rj))
    only_rust = sorted(set(rj) - set(pj))
    if only_pin:
        lines.append(
            f"    FIELD(S) THE PIN HAS AND THE RUST GOLDEN DOES NOT: {', '.join(only_pin)}\n"
            f"      -> the Lean emission GAINED a wire field; the golden predates it.\n"
        )
    if only_rust:
        lines.append(
            f"    FIELD(S) THE RUST GOLDEN HAS AND THE PIN DOES NOT: {', '.join(only_rust)}\n"
            f"      -> the Lean emission DROPPED a wire field; the golden still carries it.\n"
        )
    changed = [k for k in sorted(set(rj) & set(pj)) if rj[k] != pj[k]]
    for k in changed[:3]:
        if k == "constraints" and isinstance(rj[k], list) and isinstance(pj[k], list):
            lines.append(
                f"    `constraints` differ: {len(rj[k])} (Rust) vs {len(pj[k])} (pin)"
                + ("; SAME COUNT, so the difference is INSIDE a constraint\n"
                   if len(rj[k]) == len(pj[k]) else "\n")
            )
            continue
        lines.append(
            f"    `{k}` differs:\n"
            f"      Rust: {_short(rj[k])}\n"
            f"      pin : {_short(pj[k])}\n"
        )
    if len(changed) > 3:
        lines.append(f"    …and {len(changed) - 3} further differing field(s).\n")
    if not lines:
        # Same parsed object, different bytes: key ORDER, whitespace, or number formatting.
        lines.append(
            "    the two parse to the SAME object — the difference is purely serialisation\n"
            "    (key order, whitespace, or number formatting). Re-copy the emitted bytes.\n"
        )
    return "".join(lines)


def src_tree_files() -> list[Path]:
    """Every TRACKED `.rs` under a `src/` tree in the repo — the load-bearing half of the scan.

    Same skip list as the law-#1 ratchet's walker, and the same reason: `target/`, the vendored
    forks and the `docs/` byte-copies hold no first-party compiled Rust, and `metatheory/` is the
    authoring language rather than a consumer of its own bytes.

    ⚑ TRACKED ONLY (2026-11-06). This was a filesystem walk, so a gitignored side checkout in the
    working tree (`headver/`, a second copy of the repo) doubled the unpinned src/ population to
    132 and held this gate red at "66 NEW unpinned golden(s)" for files no commit contains. The
    question is about committed production Rust, so the population is `git ls-files`."""
    import subprocess
    out = subprocess.run(["git", "-C", str(ROOT), "ls-files", "-z", "--", "*.rs"],
                         capture_output=True, text=True)
    if out.returncode != 0:
        sys.exit("check-emit-gate-weld: `git ls-files` failed; the tracked population is the "
                 "question, so there is no honest fallback to a filesystem walk.")
    files: list[Path] = []
    for rel in out.stdout.split("\0"):
        if not rel or "/src/" not in "/" + rel:
            continue
        parts = rel.split("/")
        if any(seg in SRC_SKIP_DIRS or seg.startswith(".") for seg in parts[:-1]):
            continue
        files.append(ROOT / rel)
    return sorted(files)


def check_fragment_pins(
    scanned: list[Path],
    lean_pins: dict[str, list[tuple[Path, str]]],
    artifact_pins: dict[str, list[tuple[Path, str]]],
) -> tuple[int, int, list[str]]:
    """A geometry number typed into a Rust STRING must be one an authoritative pin carries.

    Returns `(resolved, unresolved, failures)`. See FRAGMENT_PIN for why this exists and what it
    caught."""
    by_name: dict[str, set[int]] = {}
    every_width: set[int] = set()
    for src in (lean_pins, artifact_pins):
        for name, entries in src.items():
            for _, payload in entries:
                for w in PIN_WIDTH.findall(payload):
                    by_name.setdefault(name, set()).add(int(w))
                    every_width.add(int(w))
    # Longest first, so `pasta-rcb-sg-slice-0-of-4-w8` wins over `pasta-rcb-sg-slice-0-of-4`.
    known = sorted(by_name, key=len, reverse=True)
    resolved = 0
    unresolved: list[str] = []
    failures: list[str] = []
    for rf in scanned:
        text = rf.read_text(encoding="utf-8", errors="replace")
        # Blank out the whole-object raw goldens: those are welded byte-for-byte above, and their
        # widths would otherwise be re-counted here.
        masked = RUST_RAW.sub(lambda m: " " * len(m.group(0)), text)
        for m in FRAGMENT_PIN.finditer(masked):
            width = int(m.group(1))
            line = masked.count("\n", 0, m.start()) + 1
            try:
                rel = f"{rf.relative_to(ROOT)}:{line}"
            except ValueError:  # a self-test fixture outside the tree
                rel = f"{rf.name}:{line}"
            # Which descriptor is this fragment about? Match by NAME appearing in the surrounding
            # literal — robust to `concat!`, to `\"` escaping, and to key reordering, all three of
            # which defeated the whole-object matcher.
            # ⚑ A MUTATION PROBE's SECOND argument is DELIBERATELY not a real width
            # (`good.replacen("\"trace_width\":181", "\"trace_width\":182", 1)`). The FIRST is
            # the one that must still exist, or the mutation silently becomes a no-op and the
            # adversary dies while the gate stays green — the falsifier-that-stopped-falsifying
            # class. So on a replace line, only the first width is checked.
            line_text = masked.splitlines()[line - 1] if line - 1 < len(masked.splitlines()) else ""
            if ("replacen(" in line_text or ".replace(" in line_text) and m.start() > (
                masked.rfind("\n", 0, m.start()) + 1 + line_text.find('"trace_width"')
            ):
                continue
            ctx = masked[max(0, m.start() - 600) : m.end() + 600]
            name = next((n for n in known if n in ctx), None)
            if name is None:
                # ⚑ NOT a failure. `circuit/src/lean_descriptor_air.rs`'s 58 synthetic interpreter
                # fixtures and the `demo-*` probes name descriptors no emitter produces; demanding
                # a pin for them would make this leg RED as its steady state, which is how a REAL
                # drift stops being read. Counted and printed instead — the same discipline as
                # SRC_UNPINNED_BASELINE.
                unresolved.append(f'  {rel}: `"trace_width":{width}` names no pinned descriptor')
                continue
            resolved += 1
            if width not in by_name[name]:
                failures.append(
                    f"  {rel}: a STRING pins "
                    f'`"trace_width":{width}` for `{name}`, whose authoritative pin(s) carry '
                    f"{sorted(by_name[name])}.\n"
                    "    A geometry number inside a string literal is invisible to every type\n"
                    "    check we have — it panics at run time and `cargo check` stays green.\n"
                    "    Do not retype the digits: INTERPOLATE the crate's typed constant\n"
                    '    (`format!("…\\"trace_width\\":{EXPECTED_TRACE_WIDTH}…")`), which\n'
                    "    `concat!` cannot do and which is exactly how this one rotted."
                )
    return resolved, len(unresolved), failures


# ⚑ THE FRAGMENT LEG'S OWN FALSIFIER, RUN EVERY TIME — not a test that can be forgotten.
# A gate whose adversary quietly stops being adversarial is the class this repo has already paid
# for: a mutation probe became a no-op because the string it replaced had left the fixture, the
# adversary died, and the gate stayed green. So this reconstructs the EXACT pre-fix
# `turn-prover` header — the shape that sat stale for five days — and REFUSES TO REPORT ANYTHING
# unless the leg still goes red on it, and still stays green on a typed struct field.
SELF_TEST_NAME = "faithful-note-spend-v3-plan::exact-aafi-fns3-rotated-wide-state"
SELF_TEST_DRIFTED = (
    "    const HEADER: &str = concat!(\n"
    '        "{\\"name\\":\\"' + SELF_TEST_NAME + '\\",",\n'
    '        "\\"ir\\":2,\\"trace_width\\":3804,\\"public_input_count\\":76,"\n'
    "    );\n"
)
SELF_TEST_TYPED = (
    "    UMemWeldRow {\n"
    "        trace_width: 9999,\n"
    "        name: \"dregg-effectvm-transfer-v1-avail-rot24-v3-staged-gentian-deployed"
    "-bare-refuse-umem-wide-welded-staged\",\n"
    "    },\n"
)



def self_test_fragment_leg(
    lean_pins: dict[str, list[tuple[Path, str]]],
    artifact_pins: dict[str, list[tuple[Path, str]]],
) -> str | None:
    """Return an error string if the fragment leg has stopped falsifying."""
    import tempfile

    with tempfile.TemporaryDirectory() as td:
        drifted = Path(td) / "selftest_drifted.rs"
        drifted.write_text(SELF_TEST_DRIFTED, encoding="utf-8")
        _, _, f = check_fragment_pins([drifted], lean_pins, artifact_pins)
        if len(f) != 1:
            return (
                "SELF-TEST FAILED: the fragment leg did NOT go red on the verbatim pre-fix\n"
                "  `turn-prover` header (a `concat!` pinning \"trace_width\":3804 for a\n"
                f"  descriptor pinned at 3826). Got {len(f)} failure(s), expected 1. Either the\n"
                "  descriptor was renamed/unpinned or FRAGMENT_PIN stopped matching — in both\n"
                "  cases this leg is now decoration and the PASS below would be a lie."
            )
        typed = Path(td) / "selftest_typed.rs"
        typed.write_text(SELF_TEST_TYPED, encoding="utf-8")
        _, _, f = check_fragment_pins([typed], lean_pins, artifact_pins)
        if f:
            return (
                "SELF-TEST FAILED: the fragment leg flagged a TYPED struct field\n"
                "  (`trace_width: 9999,`), which is the shape we WANT. The quote requirement in\n"
                "  FRAGMENT_PIN has been lost and the leg is now 58/58 false-positive."
            )
    return None


def main() -> int:
    print(f"ANSWERS:         {SCOPE_ANSWERS}", flush=True)
    print(f"DOES NOT ANSWER: {SCOPE_DOES_NOT_ANSWER}", flush=True)
    lean_pins = collect_lean_pins()
    artifact_pins = collect_artifact_pins()
    if (err := self_test_fragment_leg(lean_pins, artifact_pins)) is not None:
        print(err)
        print("\ncheck-emit-gate-weld: FAIL — the fragment leg no longer falsifies.")
        return 1
    failures: list[str] = []
    drift_causes: dict[str, int] = {}
    checked = 0
    unpinned: list[str] = []
    unpinned_src: list[str] = []
    rust_names: set[str] = set()

    # EVERY test in the directory, not just `*_emit_gate.rs` — the `*_audit_extra` /
    # `*_audit_*` teeth embed the same goldens and rot identically (found: the fold
    # audit-extra still carried the pre-fix 17-constraint descriptor after the gate
    # itself was re-welded).
    scanned = sorted(GATES_DIR.glob("*.rs")) + src_tree_files()
    include_backed: list[str] = []
    for rf in scanned:
        text = rf.read_text(encoding="utf-8", errors="replace")
        for m in RUST_INCLUDE.finditer(text):
            target = (rf.parent / m.group(1)).resolve()
            if target.is_file() and descriptor_name(
                target.read_text(encoding="utf-8", errors="replace")
            ):
                include_backed.append(
                    f"  {rf.relative_to(ROOT)} -> {target.relative_to(ROOT)}"
                )
        for m in RUST_RAW.finditer(text):
            payload = m.group(1)
            name = descriptor_name(payload)
            if not name:
                continue
            checked += 1
            rust_names.add(name)
            rel = rf.relative_to(ROOT)
            pins = lean_pins.get(name, []) + artifact_pins.get(name, [])
            if not pins:
                line = (
                    f"  {rel}: `{name}` has NO pin anywhere (no Lean #guard, no "
                    f"circuit/descriptors artifact) — the gate certifies only itself"
                )
                (unpinned if rf.parent == GATES_DIR else unpinned_src).append(line)
                continue
            if any(payload == p for _, p in pins):
                continue
            # Named on both sides but the bytes differ: the drifted pair.
            lf = pins[0][0].relative_to(ROOT)
            pin_payload = pins[0][1]
            cause = drift_cause(payload, pin_payload)
            drift_causes[cause] = drift_causes.get(cause, 0) + 1
            failures.append(
                f"  DRIFTED: `{name}`\n"
                f"    Rust golden: {rel}\n"
                f"    Pin:         {lf}\n"
                + drift_detail(payload, pin_payload)
                + "    The Rust gate is green against STALE bytes — it certifies a descriptor\n"
                  "    the Lean emission no longer produces."
            )

    print(f"check-emit-gate-weld: {checked} Rust goldens checked against "
          f"{sum(len(v) for v in lean_pins.values())} Lean #guard pins + "
          f"{sum(len(v) for v in artifact_pins.values())} descriptor artifacts "
          f"({len(scanned)} .rs files: {len(list(GATES_DIR.glob('*.rs')))} in "
          f"{GATES_DIR.relative_to(ROOT)} + the repo's src/ trees).")
    if include_backed:
        print(f"\n{len(include_backed)} golden(s) are `include_str!` of an emitted artifact — NO "
              f"copy exists, so there is nothing to weld:")
        for line in include_backed:
            print(line)

    # ARM THE GATE. If the extraction found ZERO Rust goldens there is nothing to weld,
    # and every check below vacuously "passes" — the gate would print PASS having verified
    # NOTHING. That happens on a silent drift of the harness itself: GATES_DIR renamed, or
    # the raw-string convention changing from `r#"…"#` to `r##"…"##` (needed when a golden
    # contains `"#`) so RUST_RAW stops matching. A weld gate that welds nothing is exactly
    # the "mechanism that cannot tell you it did nothing" — fail LOUD instead of green.
    if checked == 0:
        print(
            "\ncheck-emit-gate-weld: FATAL — found ZERO Rust emit-gate goldens to weld.\n"
            f"  Scanned {GATES_DIR.relative_to(ROOT)}/*.rs with the r#\"…\"# extractor and\n"
            "  extracted no descriptor literals. The harness has drifted out from under this\n"
            "  gate (tests moved, or the raw-string delimiter changed) — it is NOT a clean\n"
            "  tree with nothing to check. Re-point GATES_DIR / RUST_RAW.",
            file=sys.stderr,
        )
        return 2

    # The reverse gap (informational): Lean #guard-pinned descriptors nothing Rust-side touches.
    artifact_names = set(artifact_pins)
    orphans = sorted(n for n in lean_pins if n not in rust_names and n not in artifact_names)
    if orphans:
        print(f"\nINFO — {len(orphans)} Lean #guard-pinned descriptor(s) with NO Rust-side "
              f"counterpart (no test golden, no checked-in artifact):")
        for n in orphans:
            src = lean_pins[n][0][0].relative_to(ROOT)
            print(f"  {n}  ({src})")

    if unpinned:
        print("\nUNPINNED goldens:")
        print("\n".join(unpinned))
    # ⚑ THE `src/` UNPINNED POPULATION IS RATCHETED, NOT FAILED — and the reason is not mercy.
    # Widening the scan to `src/` (above) surfaced 66 of these, 58 of them synthetic
    # `#[cfg(test)]` fixtures in `circuit/src/lean_descriptor_air.rs` with names like
    # `dregg-dropRefA-v2` that no emitter ever produced and none should. Failing on them would
    # make this gate RED as its steady state, which is how the thing it is actually watching for
    # — a DRIFTED pair, named on both sides, bytes apart — stops being read. Drift in `src/` fails
    # exactly like drift in `tests/`; an unpinned `src/` literal is counted, printed, and may not
    # GROW. A new one is a new golden nothing authoritative backs, and that is the wound.
    if len(unpinned_src) > SRC_UNPINNED_BASELINE:
        print(
            f"\nUNPINNED goldens in src/ trees: {len(unpinned_src)}, ABOVE the ratchet of "
            f"{SRC_UNPINNED_BASELINE}:"
        )
        print("\n".join(unpinned_src))
        print(
            f"\ncheck-emit-gate-weld: FAIL — {len(unpinned_src) - SRC_UNPINNED_BASELINE} NEW "
            f"unpinned golden(s) under a src/ tree.\n"
            "  A descriptor literal in production Rust that no Lean #guard and no checked-in\n"
            "  artifact reproduces certifies only itself. Emit it and `include_str!` the artifact,\n"
            "  or byte-copy the Lean #guard. Lower the ratchet when you retire one."
        )
        return 1
    if unpinned_src:
        print(
            f"\nINFO — {len(unpinned_src)} unpinned golden(s) under src/ trees "
            f"(ratchet {SRC_UNPINNED_BASELINE}, may not grow); mostly `#[cfg(test)]` fixtures:"
        )
        for line in unpinned_src:
            print(line)
    # ⚑ THE FRAGMENT-PIN LEG (see FRAGMENT_PIN). Runs on the same scan set.
    frag_resolved, frag_unresolved, frag_failures = check_fragment_pins(
        scanned, lean_pins, artifact_pins
    )
    print(
        f"\nfragment pins (geometry numbers typed inside Rust STRINGS): {frag_resolved} resolved "
        f"to a named descriptor and checked, {frag_unresolved} name no pinned descriptor, "
        f"{len(frag_failures)} DRIFTED"
    )
    if frag_failures:
        print("\nFRAGMENT-PIN FAILURES:")
        print("\n".join(frag_failures))
        print(
            f"\ncheck-emit-gate-weld: FAIL — {len(frag_failures)} geometry number(s) typed into a "
            "Rust string with no authoritative pin behind them."
        )
        return 1
    if failures:
        print("\nWELD FAILURES:")
        print("\n\n".join(failures))
        # ⚑ ONE CAUSE OR MANY — say which, on the same screen as the verdict. 15 pairs drifting for
        # 15 reasons is 15 pieces of work; 15 drifting for ONE reason is one flag day whose Rust
        # side was not re-copied, and the two read identically in a list of 15 blocks.
        if len(drift_causes) == 1 and sum(drift_causes.values()) == len(failures):
            cause, n = next(iter(drift_causes.items()))
            print(
                f"\ncheck-emit-gate-weld: FAIL — {n} drifted pair(s), ALL {n} differing in exactly "
                f"the same field(s): {cause}.\n"
                f"  That is ONE flag day whose Rust goldens were not re-copied, not {n} separate\n"
                f"  regressions. Re-emit the Lean and paste the bytes into the goldens."
            )
        else:
            spread = ", ".join(f"{c} x{n}" for c, n in sorted(drift_causes.items()))
            print(
                f"\ncheck-emit-gate-weld: FAIL — {len(failures)} drifted pair(s) across "
                f"{len(drift_causes)} distinct cause(s): {spread}."
            )
        return 1
    if unpinned:
        return 1
    print("check-emit-gate-weld: PASS — every Rust golden is byte-identical to an authoritative pin.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
