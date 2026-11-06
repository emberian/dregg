#!/usr/bin/env bash
# Demo (b): a governance question over an agent session forest, answered by a stratified Datalog
# certificate, checked by the extracted Lean checker, receipt signed with ssh-keygen.
#
#   ./run.sh          DEFAULT: the SYNTHETIC forest (synth_transcript.py, seeded), two variants:
#                     data/synthetic/violating (count 2) and data/synthetic/fixed (count 0)
#   ./run.sh --real   the real-session run from the local data/transcript.json, if present. It is
#                     never re-exported. Its outputs go to $REAL_OUT (default data/), and those
#                     session-derived artifacts are under ember's decision.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
META="$HERE/../../metatheory"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
TIMEFORMAT='%R s'
cd "$HERE"

CHECK="$META/.lake/build/bin/datalog-check"
[[ -x "$CHECK" ]] || (cd "$META" && lake build datalog-check)

mkdir -p keys
if [[ ! -f keys/receipt_ed25519 ]]; then
  ssh-keygen -q -t ed25519 -N '' -C datalog-governance@dregg -f keys/receipt_ed25519
  echo "datalog-governance@dregg namespaces=\"dregg-datalog-receipt\" $(cut -d' ' -f1,2 keys/receipt_ed25519.pub)" > allowed_signers
fi

# run_one <transcript.json> <out dir>: extract, prove, check, sign, verify.
run_one() {
  local tr="$1" out="$2"
  mkdir -p "$out"
  echo "== extract ($out)"; time python3 -I extract_edb.py "$tr" program.json "$out/edb.json"
  echo "== prove";          time python3 -I prove.py program.json "$out/edb.json" "$out/certificate.json"
  rm -f "$out/certificate.json.violations"
  echo "== check"
  time "$CHECK" "$out/certificate.json" | tee "$out/check.out"
  grep -q '^verdict        : ACCEPT' "$out/check.out"
  local digest root pred count
  digest=$(awk '/^program digest/ {print $4}' "$out/check.out")
  root=$(awk '/^  root/ {print $3}' "$out/check.out")
  pred=$(awk '/^  pred/ {print $3}' "$out/check.out")
  count=$(awk '/^  claimed count/ {print $3}' "$out/check.out")
  [[ -n "$digest" && -n "$root" && -n "$pred" && -n "$count" ]] || { echo "receipt field missing"; exit 1; }
  printf 'dregg datalog receipt v1\nprogram_digest=%s\nroot=%s\npred=%s\ncount=%s\nchecker=lake exe datalog-check (metatheory/DatalogCheck.lean)\n' \
    "$digest" "$root" "$pred" "$count" > "$out/receipt.txt"
  rm -f "$out/receipt.txt.sig"
  ssh-keygen -q -Y sign -f keys/receipt_ed25519 -n dregg-datalog-receipt "$out/receipt.txt"
  echo "== verify receipt signature"
  time ssh-keygen -Y verify -f allowed_signers -I datalog-governance@dregg -n dregg-datalog-receipt \
    -s "$out/receipt.txt.sig" < "$out/receipt.txt"
}

# falsifiers <certificate.json>: each forgery must be REFUSED; the weaker checker must ACCEPT open-lower.
falsifiers() {
  echo "== falsifiers on $1 (each must be REFUSED)"
  python3 -I forge.py program.json "$1" "$TMP"
  for f in open-lower wrong-count dropped-fact; do
    if "$CHECK" "$TMP/$f.json" > "$TMP/$f.out"; then echo "FAIL: $f was accepted"; exit 1; fi
    echo "$f: $(grep '^verdict' "$TMP/$f.out")"
  done
  echo "== the weaker checker on the open-lower forgery (must ACCEPT: that is the falsifier)"
  "$CHECK" --weaker-no-lower-closure "$TMP/open-lower.json" | tail -1
}

if [[ "${1:-}" == "--real" ]]; then
  [[ -f data/transcript.json ]] || { echo "no local data/transcript.json"; exit 2; }
  out="${REAL_OUT:-data}"
  run_one data/transcript.json "$out"
  falsifiers "$out/certificate.json"
else
  for v in violating fixed; do
    mkdir -p "data/synthetic/$v"
    python3 -I synth_transcript.py "$v" "data/synthetic/$v/transcript.json"
    run_one "data/synthetic/$v/transcript.json" "data/synthetic/$v"
  done
  falsifiers data/synthetic/fixed/certificate.json
fi
