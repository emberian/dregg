#!/usr/bin/env bash
# One-command synthetic demo. Default: reproduce both variants in a fresh directory, then
# compare their checked tuples with the ORIGINAL signed receipts. No signing keys required.
# ./run.sh verify skips generation and verifies the checked-in certificates.
# WORK=/fresh/output ./run.sh keeps reproducible outputs there; never use a checked-in data dir.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
META="$HERE/../../metatheory"
CHECK="${CHECK:-$META/.lake/build/bin/datalog-check}"
[[ -x "$CHECK" ]] || (cd "$META" && lake build datalog-check)
MODE="${1:-reproduce}"
case "$MODE" in verify|reproduce|--real) ;; *) echo 'usage: ./run.sh [verify|reproduce|--real]' >&2; exit 2 ;; esac
WORK="${WORK:-$(mktemp -d "${TMPDIR:-/tmp}/datalog-governance.XXXXXX")}"
mkdir -p "$WORK"
# Refuse existing output files instead of replacing a prior run or repository artifacts.
[[ -z "$(ls -A "$WORK")" ]] || { echo "WORK must be an empty directory: $WORK" >&2; exit 2; }
echo "output: $WORK"

verify_one() {
  python3 -I "$HERE/verify_receipt.py" "$1" "$2" --checker "$CHECK"
}
falsifiers() {
  local out="$WORK/falsifiers"
  mkdir -p "$out"
  python3 -I "$HERE/forge.py" "$HERE/program.json" "$1" "$out"
  local f rc
  for f in open-lower wrong-count dropped-fact; do
    rc=0
    "$CHECK" "$out/$f.json" > "$out/$f.out" || rc=$?
    [[ "$rc" = 1 ]] && grep -q '^verdict        : REFUSE (' "$out/$f.out" || {
      echo "FAIL: $f must be REFUSED, not accepted or malformed (exit $rc)" >&2; exit 1;
    }
    echo "$f: $(grep '^verdict' "$out/$f.out")"
  done
  "$CHECK" --weaker-no-lower-closure "$out/open-lower.json" > "$out/weak.out"
  grep -q '^WEAKER checker (closure at the top stratum only, NOT the statement.s checker): ACCEPT$' "$out/weak.out" || { echo 'FAIL: weak checker did not ACCEPT' >&2; exit 1; }
  echo 'weak checker: ACCEPT (open-lower separation)'
  # Both inputs independently verify; their signed statement tuples must still agree.
  if verify_one "$1" "$HERE/data/synthetic/violating/receipt.txt" > "$out/swapped-receipt.out" 2>&1; then
    echo 'FAIL: a valid signature for a different tuple was accepted' >&2; exit 1
  fi
  grep -q 'signed receipt differs from checked certificate: count, root' "$out/swapped-receipt.out" || {
    echo 'FAIL: swapped receipt did not reach tuple comparison' >&2; exit 1;
  }
  echo 'swapped valid receipt: REFUSE (count, root differ)'
}

if [[ "$MODE" = --real ]]; then
  # Local opt-in; no export, signing, or mutation of the historical artifacts.
  verify_one "$HERE/data/certificate.json" "$HERE/data/receipt.txt"
  exit 0
fi
for v in violating fixed; do
  original="$HERE/data/synthetic/$v"
  if [[ "$MODE" = verify ]]; then
    verify_one "$original/certificate.json" "$original/receipt.txt"
  else
    out="$WORK/$v"
    mkdir -p "$out"
    python3 -I "$HERE/synth_transcript.py" "$v" "$out/transcript.json"
    python3 -I "$HERE/extract_edb.py" "$out/transcript.json" "$HERE/program.json" "$out/edb.json"
    python3 -I "$HERE/prove.py" "$HERE/program.json" "$out/edb.json" "$out/certificate.json"
    verify_one "$out/certificate.json" "$original/receipt.txt" | tee "$out/check.out"
  fi
done
if [[ "$MODE" = reproduce ]]; then falsifiers "$WORK/fixed/certificate.json"; fi
