#!/usr/bin/env bash
# tree-absence, end to end: export the demo session, project tool calls to records, build the
# query tables, hold the Rust projection to Lean's, produce corpus / field / schema certificates,
# and have the Lean checker `tree-check verify` decide them (plus tampered copies it must refuse).
#
#   ./run.sh            reuse corpus/exports if present
#   EXPORT=1 ./run.sh   re-export with `cv export --redact`
#
# Rust produces; Lean decides. Needs metatheory/.lake/build/bin/{tree-check,policyc} (built by
# `lake build tree-check policyc` in metatheory/, one lake process at a time). Everything that
# contains tool inputs lands in corpus/ (gitignored) or cert-full.json (gitignored).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
cd "$here"
meta="$here/../../metatheory"
TC="$meta/.lake/build/bin/tree-check"
PC="$meta/.lake/build/bin/policyc"
T="$here/target/release/tree-cert"
for b in "$TC" "$PC"; do [ -x "$b" ] || { echo "missing $b (lake build in metatheory/)"; exit 2; }; done
mkdir -p corpus
now() { python3 -I -c 'import time; print(time.time())'; }
elapsed() { python3 -I -c "import sys; print(round(float(sys.argv[2]) - float(sys.argv[1]), 2))" "$1" "$2"; }

echo "== build"
cargo build --release --quiet

echo "== corpus"
if [ "${EXPORT:-0}" = 1 ] || [ ! -f corpus/exports/root.json ]; then ./export_corpus.sh; fi
python3 -I project_records.py corpus/exports corpus/records-real.jsonl corpus/sources.json
cat corpus/records-real.jsonl controls.jsonl > corpus/records-full.jsonl

echo "== tables"
"$PC" compile query.policy --pattern bash > tables/bash.policyc.json
"$PC" compile query.policy --pattern pkill_absent --absence > tables/pkill-absence.policyc.json
"$T" table-contains "pkill -f" tables/pkill.json
python3 -I tables/equiv.py tables/pkill.json tables/pkill-absence.policyc.json complement
"$PC" check query-invocation.policy
"$T" table-invocation tables/invocation.json
"$T" diff-invocation tables/invocation.json corpus/records-full.jsonl | tee corpus/diff-invocation.json
"$T" table-invocation --no-backtick tables/invocation-nobacktick.json
"$T" diff-invocation --no-backtick tables/invocation-nobacktick.json corpus/records-full.jsonl | tee corpus/diff-invocation-nobacktick.json

echo "== conformance (Rust projection vs tree-check project)"
"$T" conform --edges --tmp corpus/conform-tmp | tee corpus/conform-edges.json
"$T" conform corpus/records-real.jsonl --tmp corpus/conform-tmp | tee corpus/conform-records.json

echo "== corpus certificates: (A) mention, (B) invocation, (C) invocation without the backtick boundary"
"$T" corpus corpus/records-real.jsonl query.json corpus/cert-real.json > corpus/produce-real.json
"$T" corpus corpus/records-full.jsonl query.json cert-full.json > corpus/produce-full.json
"$T" corpus corpus/records-real.jsonl query-invocation.json corpus/cert-invocation-real.json > corpus/produce-invocation-real.json
"$T" corpus corpus/records-full.jsonl query-invocation.json cert-invocation-full.json > corpus/produce-invocation-full.json
"$T" corpus corpus/records-real.jsonl query-invocation-nobacktick.json corpus/cert-invocation-nobacktick-real.json > corpus/produce-invocation-nobacktick-real.json
"$T" corpus corpus/records-full.jsonl query-invocation-nobacktick.json cert-invocation-nobacktick-full.json > corpus/produce-invocation-nobacktick-full.json
"$T" flat-scan corpus/records-real.jsonl "pkill -f" > corpus/flat-scan-real.json
"$T" flat-scan corpus/records-full.jsonl "pkill -f" > corpus/flat-scan.json

count_of() { python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["count"])' "$1"; }
expect_count() { # expect_count <produce.json> <n>
  local c; c=$(count_of "$1"); [ "$c" = "$2" ] || { echo "FAIL: $1 count $c, expected $2" >&2; exit 1; }
}
expect_count corpus/produce-real.json 13
expect_count corpus/produce-full.json 15
expect_count corpus/produce-invocation-real.json 7
expect_count corpus/produce-invocation-full.json 9
expect_count corpus/produce-invocation-nobacktick-real.json 0
expect_count corpus/produce-invocation-nobacktick-full.json 2

echo "== verify (Lean)"
verify() { # verify <cert> <tag> <expected exit>: 0 for honest certificates, 1 for tampered ones.
  # Any other exit (2 = malformed) or an unexpected accept/refuse fails the run.
  local s e code=0
  s=$(now); "$TC" verify "$1" > "corpus/verify-$2.out" 2>&1 || code=$?; e=$(now)
  echo "$2 exit=$code $(tail -1 "corpus/verify-$2.out") $(elapsed "$s" "$e")s" | tee -a corpus/verify.log
  if [ "$code" != "$3" ]; then
    echo "FAIL: $2 exited $code, expected $3 (corpus/verify-$2.out)" >&2
    exit 1
  fi
}
: > corpus/verify.log
verify corpus/cert-real.json real 0
verify cert-full.json full 0
verify corpus/cert-invocation-real.json invocation-real 0
verify cert-invocation-full.json invocation-full 0
verify corpus/cert-invocation-nobacktick-real.json invocation-nobacktick-real 0
verify cert-invocation-nobacktick-full.json invocation-nobacktick-full 0
for q in full invocation-full invocation-nobacktick-full; do
  src=cert-full.json; [ "$q" = full ] || src="cert-$q.json"
  for k in count+1 count-1 swap-records refute-wrong-path swap-table-digests drop-record; do
    python3 -I tamper.py "$src" "$k" "corpus/tampered-$q-$k.json"
    verify "corpus/tampered-$q-$k.json" "tampered-$q-$k" 1
  done
done

echo "== one record: field and schema certificates"
# record 2580 (0-based), the corpus's shortest Bash command naming no path or project:
#   cv recipes 2>&1 | head -80; cv schema 2>&1 | head -80
# (the corpus has no git-only command). Its field certificate for (B)'s conjunct 1 opens only the
# `input.command` string plus sibling keys and digests; verdict reject.
REC=2580
sed -n "$((REC + 1))p" corpus/records-real.jsonl > corpus/record-$REC.json
"$T" field corpus/record-$REC.json '["input","command"]' tables/invocation.json field-cert-$REC.json
verify field-cert-$REC.json field-$REC 0
"$T" field corpus/record-$REC.json '["input","command"]' tables/invocation-nobacktick.json field-cert-$REC-c.json
verify field-cert-$REC-c.json field-$REC-c 0
"$T" schema corpus/record-$REC.json schema-bash-call.json corpus/schema-cert-$REC.json
verify corpus/schema-cert-$REC.json schema-$REC 0

echo "== summary"
python3 -I summarize.py corpus summary.json "$REC" field-cert-$REC.json field-cert-$REC-c.json
cat summary.json
