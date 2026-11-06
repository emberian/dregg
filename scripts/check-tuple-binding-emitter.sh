#!/usr/bin/env bash
# Check the Lean tuple generator and prove its semantic gate rejects two mutations.
# Mutations are made only in a fresh temporary directory, never the shared tree.
set -euo pipefail
repo=$(cd "$(dirname "$0")/.." && pwd)
scratch=$(mktemp -d "${TMPDIR:-/tmp}/tuple-air.XXXXXX")
trap 'rm -rf "$scratch"' EXIT
source_file="$repo/metatheory/Dregg2/Circuit/Emit/TupleBindingEmit.lean"
cd "$repo/metatheory"
lake env lean "$source_file"
python3 - "$source_file" "$scratch" <<'PY'
from pathlib import Path
import sys
source = Path(sys.argv[1]).read_text()
out = Path(sys.argv[2])
mutations = {
    "public_pin": (".base (.piBinding .first c c)", ".base (.piBinding .first c 0)"),
    "copy_window": (".add (.nxt c) (.mul (.const (-1)) (.loc c))",
                    ".add (.loc c) (.mul (.const (-1)) (.loc c))"),
}
for name, (old, new) in mutations.items():
    if source.count(old) != 1:
        raise SystemExit(f"{name}: expected exactly one generator site")
    (out / f"{name}.lean").write_text(source.replace(old, new, 1))
PY
for mutation in public_pin copy_window; do
  if lake env lean "$scratch/$mutation.lean" >"$scratch/$mutation.log" 2>&1; then
    echo "FAIL: tuple generator admitted $mutation mutation" >&2
    exit 1
  fi
  # Require the semantic theorem's axiom pin to fail, not merely an import error.
  theorem=tuple_semantics
  if [[ "$mutation" == copy_window ]]; then theorem=copy_semantics; fi
  if ! rg -q "TupleBindingEmit\.$theorem.*depends on axioms" "$scratch/$mutation.log" ||
     ! rg -q 'sorryAx' "$scratch/$mutation.log"; then
    cat "$scratch/$mutation.log" >&2
    echo "FAIL: $mutation failed outside its semantic gate" >&2
    exit 1
  fi
  echo "PASS: $mutation refused by $theorem"
done
echo 'PASS: tuple binding emitter and mutation gates'
