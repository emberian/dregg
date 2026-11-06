#!/usr/bin/env bash
# Demo (b): a governance question over a Claude Code session forest, answered by a stratified
# Datalog certificate, checked by the extracted Lean checker, receipt signed with ssh-keygen.
#
#   ./run.sh            use the checked-in data/transcript.json
#   ./run.sh --export   re-export the session with `cv` first (needs the session on this machine)
#
# Everything a stranger needs is checked in under data/; only keys/ (the signing key) is not.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
META="$HERE/../../metatheory"
DATA="$HERE/data"
SESSION=e3ba49ed-a526-4ecd-8807-58b73757aaca
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
TIMEFORMAT='%R s'
cd "$HERE"

if [[ "${1:-}" == "--export" ]]; then
  command -v cv >/dev/null || { echo "cv not found"; exit 2; }
  mkdir -p "$TMP/export/sub"
  cv export "$SESSION" --format json --redact > "$TMP/export/root.json"
  for f in "$HOME/.claude/projects/-Users-ember-dev-aidev/$SESSION/subagents/"agent-*.jsonl; do
    id="$(basename "$f" .jsonl)"
    cv export "$id" --format json --redact > "$TMP/export/sub/$id.json" 2>>"$TMP/redact.log"
  done
  python3 -I project_transcript.py "$TMP/export" "$SESSION" "$DATA/transcript.json"
fi

echo "== extract";  time python3 -I extract_edb.py "$DATA/transcript.json" program.json "$DATA/edb.json"
echo "== prove";    time python3 -I prove.py program.json "$DATA/edb.json" "$DATA/certificate.json"
rm -f "$DATA/certificate.json.violations"

CHECK="$META/.lake/build/bin/datalog-check"
[[ -x "$CHECK" ]] || (cd "$META" && lake build datalog-check)
echo "== check"
time "$CHECK" "$DATA/certificate.json" | tee "$DATA/check.out"

# The receipt: (program digest, root, pred, count) as the checker printed them.
digest=$(awk '/^program digest/ {print $4}' "$DATA/check.out")
root=$(awk '/^  root/ {print $3}' "$DATA/check.out")
pred=$(awk '/^  pred/ {print $3}' "$DATA/check.out")
count=$(awk '/^  claimed count/ {print $3}' "$DATA/check.out")
[[ -n "$digest" && -n "$root" && -n "$pred" && -n "$count" ]] || { echo "receipt field missing"; exit 1; }
grep -q '^verdict        : ACCEPT' "$DATA/check.out"
printf 'dregg datalog receipt v1\nprogram_digest=%s\nroot=%s\npred=%s\ncount=%s\nchecker=lake exe datalog-check (metatheory/DatalogCheck.lean)\n' \
  "$digest" "$root" "$pred" "$count" > "$DATA/receipt.txt"

mkdir -p keys
if [[ ! -f keys/receipt_ed25519 ]]; then
  ssh-keygen -q -t ed25519 -N '' -C datalog-governance@dregg -f keys/receipt_ed25519
  echo "datalog-governance@dregg namespaces=\"dregg-datalog-receipt\" $(cut -d' ' -f1,2 keys/receipt_ed25519.pub)" > allowed_signers
fi
rm -f "$DATA/receipt.txt.sig"
ssh-keygen -q -Y sign -f keys/receipt_ed25519 -n dregg-datalog-receipt "$DATA/receipt.txt"
echo "== verify receipt signature"
time ssh-keygen -Y verify -f allowed_signers -I datalog-governance@dregg -n dregg-datalog-receipt \
  -s "$DATA/receipt.txt.sig" < "$DATA/receipt.txt"

echo "== falsifiers (each must be REFUSED)"
python3 -I forge.py program.json "$DATA/certificate.json" "$TMP"
for f in open-lower wrong-count dropped-fact; do
  if "$CHECK" "$TMP/$f.json" > "$TMP/$f.out"; then
    echo "FAIL: $f was accepted"; exit 1
  fi
  echo "$f: $(grep '^verdict' "$TMP/$f.out")"
done
echo "== the weaker checker on the open-lower forgery (must ACCEPT: that is the falsifier)"
"$CHECK" --weaker-no-lower-closure "$TMP/open-lower.json" | tail -1
