#!/usr/bin/env bash
# automata-check.sh: the automata family gate (docs/automata/SUBSTRATE-DECISION.md §5 item 4, §6).
#
# What it does, in order:
#   1. deps:  `lake build` of every module the family files import (Dregg2.* and Mathlib.*), so the
#             oleans the per-file check loads are current: a `lake env lean` against a stale olean
#             can go green on an import that no longer typechecks, and an olean written by another
#             Lean version fails with "incompatible header". A no-op on a warm, unchanged tree.
#   2. check: `lake env lean <file>` on each family file, N at a time. A file passes when lean exits 0
#             with no `error:` line and no `declaration uses 'sorry'` warning. `#guard` is silent on
#             success, so the GUARDS column is the number of `#guard` commands in the file that ran
#             and held; KEYSTONES is the sum of the `#assert_all_clean: N keystones` reports plus the
#             file's single-name `#assert_clean`/`#assert_axioms` pins; any `#print axioms` output
#             naming `sorryAx` fails the file.
#   3. table: file, status, seconds, guards, keystones (or JSON with --json); exit 1 on any failure.
#
# The family list: the gate list from the automata program brief, plus every `.lean` file under
# `Dregg2/Datalog/`, `Dregg2/Policy/` (lanes A and B add files there), `Dregg2/Sat/` (lane E) and
# `Dregg2/Automata/` (the `dfa-run` table runner) and `Dregg2/Tree/` (initiative 12, `tree-check`). `--files` replaces it.
#
# Usage (from anywhere; the script cds to metatheory/):
#   scripts/automata-check.sh                  # Mac: -j 4, deps then check, table on stdout
#   scripts/automata-check.sh -j 8 --json      # machine output (one JSON object on stdout)
#   scripts/automata-check.sh --files Dregg2/Crypto/Dfa.lean,Dregg2/Datalog/FixpointCert.lean
#   scripts/automata-check.sh --no-deps        # skip step 1 (only when you know the oleans are current)
#   scripts/automata-check.sh --list           # print the resolved file list and exit
#   scripts/automata-check.sh --statements-only # all review identities + warm audit modules, no deps build
#
# hbox: `scripts/automata-check.sh --hbox [other flags]` re-executes the same script inside
# `swarm-build` (cgroup memory cap `SWARM_MEM_MAX`, default 12G here; taskset + nice inside), so
# the whole gate, deps build included, is contained. Run it from a clone whose `.lake` is warm
# (docs/automata/BUILD.md says how; on hbox the clone is ~/lanes/automata/bs). Never a bare
# `lake build` on the Mac: the default targets rebuild Metatheory/Polis/Market/Bfv and the guard libs.
#
# Logs: each file's full lean output is kept under $AUTOMATA_CHECK_LOGDIR (default: a fresh
# mktemp dir, printed at the end) as <module>.out.
set -uo pipefail

JOBS=4
JSON=0
DEPS=1
HBOX=0
LIST=0
FILES_OVERRIDE=""
ARGS_ORIG=("$@")

usage() { sed -n '2,32p' "$0" | sed 's/^# \{0,1\}//'; }

while [ $# -gt 0 ]; do
  case "$1" in
    -j) JOBS="$2"; shift 2 ;;
    -j*) JOBS="${1#-j}"; shift ;;
    --jobs) JOBS="$2"; shift 2 ;;
    --json) JSON=1; shift ;;
    --no-deps) DEPS=0; shift ;;
    --statements-only) DEPS=0; FILES_OVERRIDE="Dregg2/Automata/StatementAudit.lean,Dregg2/Automata/DfaBoundReference.lean,Dregg2/Automata/CertificateStatementAudit.lean,Dregg2/Automata/EmitterStatementAudit.lean"; shift ;;
    --hbox) HBOX=1; shift ;;
    --list) LIST=1; shift ;;
    --files) FILES_OVERRIDE="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "automata-check: unknown argument: $1" >&2; usage >&2; exit 2 ;;
  esac
done

case "$JOBS" in ''|*[!0-9]*) echo "automata-check: -j needs a positive integer" >&2; exit 2 ;; esac
[ "$JOBS" -ge 1 ] || JOBS=1

if [ "$HBOX" = 1 ] && [ -z "${SWARM_BUILD_INNER:-}" ]; then
  command -v swarm-build >/dev/null || { echo "automata-check: --hbox needs swarm-build on PATH" >&2; exit 2; }
  # drop --hbox from the re-exec; everything else passes through unchanged
  REEXEC=()
  for a in "${ARGS_ORIG[@]+"${ARGS_ORIG[@]}"}"; do [ "$a" = "--hbox" ] || REEXEC+=("$a"); done
  export SWARM_MEM_MAX="${SWARM_MEM_MAX:-12G}"
  exec swarm-build "$0" "${REEXEC[@]+"${REEXEC[@]}"}"
fi

MT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$MT" || exit 2

GATE_FILES="
Dregg2/Crypto/Dfa.lean
Dregg2/Crypto/DfaAcceptanceAir.lean
Dregg2/Crypto/Deriv/Core.lean
Dregg2/Crypto/Deriv/Correctness.lean
Dregg2/Crypto/Deriv/Finiteness.lean
Dregg2/Crypto/Deriv/Thompson.lean
Dregg2/Crypto/Deriv/SymbolicEquivalence.lean
Dregg2/Crypto/Deriv/BisimCert.lean
Dregg2/Crypto/Cfg.lean
Dregg2/Crypto/CfgCompact.lean
Dregg2/Circuit/Emit/DfaRoutingTableEmit.lean
Dregg2/Circuit/Emit/DfaRoutingGeneralEmit.lean
Dregg2/Circuit/Emit/DyckStackEmit.lean
Dregg2/Circuit/Emit/DyckStackReplay.lean
Dregg2/Circuit/Emit/AttestedAutomatonWeld8.lean
Dregg2/Circuit/Emit/AttestedAutomatonLanes8.lean
Dregg2/Circuit/Emit/AttestedAutomatonBound.lean
Dregg2/Circuit/Emit/DfaRoutingChainBound.lean
Dregg2/Circuit/Emit/DfaRoutingTableBound.lean
Dregg2/Circuit/Emit/DyckStackBound.lean
Dregg2/Circuit/Emit/RouteChain8.lean
Dregg2/Circuit/Emit/RouteChain8Binding.lean
Dregg2/Circuit/Emit/RouteChain8Refine.lean
Dregg2/Circuit/Emit/RouteChain8Canonical.lean
Dregg2/Circuit/Emit/DfaRoutingTableRoute8.lean
Dregg2/Circuit/Emit/DfaRoutingTableRoute8Bound.lean
Dregg2/Circuit/Emit/AttestedAutomatonRoute8.lean
Dregg2/Circuit/Emit/AttestedAutomatonRoute8Witness.lean
Dregg2/Circuit/Emit/SolvencyLeafEmit.lean
Dregg2/Circuit/Emit/TupleBindingEmit.lean
Dregg2/Circuit/Emit/BoundedFactEmit.lean
Dregg2/Circuit/Emit/BorrowChainEmit.lean
Dregg2/Circuit/Emit/CaveatAdmissionEmit.lean
Dregg2/Circuit/Emit/DecoLeafEmit.lean
Dregg2/Circuit/Emit/NoteSpendingLeafServed.lean
Dregg2/Circuit/Emit/BinaryMembershipEmit.lean
Dregg2/Circuit/Emit/BinaryMembershipRefine.lean
Dregg2/Circuit/Emit/BinaryMembershipWitness.lean
Dregg2/Logic/DirectLogicProgramIR2.lean
Dregg2/Circuit/Emit/TinyAutomataLanesK.lean
Dregg2/Circuit/Emit/DerivationEmit.lean
Dregg2/Datalog/FixpointCert.lean
"

if [ -n "$FILES_OVERRIDE" ]; then
  FILES=$(printf '%s\n' "$FILES_OVERRIDE" | tr ', ' '\n\n' | sed '/^$/d')
else
  FILES=$( { printf '%s\n' $GATE_FILES; find Dregg2/Datalog Dregg2/Policy Dregg2/Automata Dregg2/Sat Dregg2/Tree -name '*.lean' 2>/dev/null | sort; } | awk 'NF && !seen[$0]++')
fi

MISSING=0
for f in $FILES; do
  [ -f "$f" ] || { echo "automata-check: no such file: $MT/$f" >&2; MISSING=1; }
done
[ "$MISSING" = 0 ] || exit 2

if [ "$LIST" = 1 ]; then printf '%s\n' $FILES; exit 0; fi

# Human statement review is bound to source identity; Lean below checks its exact axiom pins.
# Keep diagnostics off stdout so --json remains one JSON object.
python3 "$MT/../scripts/check-automata-statements.py" >&2 || exit 1

LOGDIR="${AUTOMATA_CHECK_LOGDIR:-$(mktemp -d "${TMPDIR:-/tmp}/automata-check.XXXXXX")}"
mkdir -p "$LOGDIR"
now() { perl -MTime::HiRes=time -e 'printf "%.2f\n", time'; }
say() { [ "$JSON" = 1 ] && echo "$*" >&2 || echo "$*"; }

T0=$(now)

# ---- step 1: deps ---------------------------------------------------------------------------
DEPS_RC=0
DEPS_SECS=0
if [ "$DEPS" = 1 ]; then
  # Toolchain modules (Init, Std, Lean, Lake) ship with Lean and are not lake targets.
  MODS=$(for f in $FILES; do sed -n 's/^\(public \)\{0,1\}import \([A-Z][A-Za-z0-9_.]*\).*/\2/p' "$f"; done \
    | grep -Ev '^(Init|Std|Lean|Lake)(\.|$)' | sort -u)
  if [ -n "$MODS" ]; then
    say "automata-check: deps: lake build of $(printf '%s\n' $MODS | wc -l | tr -d ' ') imported modules (log $LOGDIR/deps.log)"
    D0=$(now)
    # shellcheck disable=SC2086
    lake build $MODS > "$LOGDIR/deps.log" 2>&1
    DEPS_RC=$?
    D1=$(now)
    DEPS_SECS=$(echo "$D0 $D1" | awk '{printf "%.1f", $2-$1}')
    if [ "$DEPS_RC" != 0 ]; then
      say "automata-check: deps build FAILED (rc $DEPS_RC); per-file results below may load stale oleans"
      grep -E 'error' "$LOGDIR/deps.log" | head -20 >&2
    fi
  fi
fi

# ---- step 2: per-file check ------------------------------------------------------------------
export LOGDIR
check_one() {
  f="$1"
  key=$(printf '%s' "$f" | sed 's#/#.#g; s#\.lean$##')
  s0=$(perl -MTime::HiRes=time -e 'printf "%.2f", time')
  lake env lean "$f" > "$LOGDIR/$key.out" 2>&1
  rc=$?
  s1=$(perl -MTime::HiRes=time -e 'printf "%.2f", time')
  printf '%s\t%s\t%s\t%s\n' "$f" "$rc" "$s0" "$s1" > "$LOGDIR/$key.res"
}
export -f check_one

say "automata-check: checking $(printf '%s\n' $FILES | wc -l | tr -d ' ') files, -j $JOBS (logs $LOGDIR)"
printf '%s\n' $FILES | xargs -P "$JOBS" -I{} bash -c 'check_one "$1"' _ {}

T1=$(now)

# ---- step 3: report --------------------------------------------------------------------------
python3 - "$LOGDIR" "$JSON" "$DEPS" "$DEPS_RC" "$DEPS_SECS" "$T0" "$T1" "$JOBS" "$(hostname -s 2>/dev/null || hostname)" $FILES <<'PY'
import json, os, re, sys
logdir, as_json, deps, deps_rc, deps_secs, t0, t1, jobs, host = sys.argv[1:10]
files = sys.argv[10:]
rows, failed = [], 0
for f in files:
    key = f.replace("/", ".")[:-len(".lean")]
    out = open(os.path.join(logdir, key + ".out"), errors="replace").read() if os.path.exists(os.path.join(logdir, key + ".out")) else ""
    res = os.path.join(logdir, key + ".res")
    if os.path.exists(res):
        _, rc, s0, s1 = open(res).read().strip().split("\t")
        rc, secs = int(rc), float(s1) - float(s0)
    else:
        rc, secs = -1, 0.0
    src = open(f, errors="replace").read()
    guards = len(re.findall(r"(?m)^\s*#guard(?![_\w])", src))
    single = len(re.findall(r"(?m)^\s*#assert_(?:clean|axioms)\s", src))
    # Exact axiom reports count only when not already included in this file's assertion macro.
    asserted = set(re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", " ".join(
        re.findall(r"#assert_all_clean\s*\[([^]]*)\]", src))))
    asserted.update(re.findall(r"(?m)^\s*#assert_(?:clean|axioms)\s+([\w.]+)", src))
    exact_pins = re.findall(r"(?m)^#guard_msgs in\n#print axioms ([\w.]+)", src)
    single += sum(name not in asserted for name in exact_pins)
    reported = sum(int(n) for n in re.findall(r"#assert_all_clean: (\d+) keystones pinned kernel-clean", out))
    errors = [l for l in out.splitlines() if re.search(r":\d+:\d+: error", l) or l.startswith("error:")]
    sorry = [l for l in out.splitlines() if "declaration uses 'sorry'" in l]
    axiom_lines = [l for l in out.splitlines() if "depends on axioms" in l]
    sorry_ax = [l for l in axiom_lines if "sorryAx" in l]
    if rc != 0 or errors:
        status = "FAIL"
    elif sorry or sorry_ax:
        status = "SORRY"
    else:
        status = "ok"
    if status != "ok":
        failed += 1
    rows.append(dict(file=f, status=status, rc=rc, seconds=round(secs, 1), guards=guards,
                     keystones=reported + single, axiom_reports=axiom_lines,
                     first_error=(errors + sorry + sorry_ax + [""])[0][:300],
                     log=os.path.join(logdir, key + ".out")))
wall = float(t1) - float(t0)
summary = dict(host=host, jobs=int(jobs), wall_seconds=round(wall, 1), files=len(rows), failed=failed,
               deps=dict(ran=deps == "1", rc=int(deps_rc), seconds=float(deps_secs)),
               guards=sum(r["guards"] for r in rows), keystones=sum(r["keystones"] for r in rows),
               logdir=logdir, rows=rows)
if as_json == "1":
    print(json.dumps(summary, indent=1))
else:
    w = max(len(r["file"]) for r in rows)
    print(f"{'file':<{w}}  {'status':<6} {'secs':>7} {'guards':>6} {'keystones':>9}")
    for r in rows:
        print(f"{r['file']:<{w}}  {r['status']:<6} {r['seconds']:>7.1f} {r['guards']:>6} {r['keystones']:>9}")
        for a in r["axiom_reports"]:
            print(f"    axioms: {a}")
        if r["status"] != "ok":
            print(f"    first: {r['first_error']}")
            print(f"    log:   {r['log']}")
    d = summary["deps"]
    dline = f"deps rc {d['rc']} in {d['seconds']:.1f}s" if d["ran"] else "deps skipped"
    print(f"{len(rows)} files, {failed} failed, {summary['guards']} guards, {summary['keystones']} keystones; "
          f"{dline}; wall {wall:.1f}s at -j {jobs} on {host}; logs {logdir}")
sys.exit(1 if failed or int(deps_rc) != 0 else 0)
PY
