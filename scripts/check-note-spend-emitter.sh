#!/usr/bin/env bash
# Narrow proof + consumed artifact check, using a warm Lean environment.
set -euo pipefail
repo=$(cd "$(dirname "$0")/.." && pwd)
scratch=$(mktemp -d "${TMPDIR:-/tmp}/note-spend-air.XXXXXX")
trap 'rm -rf "$scratch"' EXIT
cd "$repo/metatheory"
lake env lean Dregg2/Circuit/Emit/NoteSpendingLeafServed.lean
cat > "$scratch/Emit.lean" <<'LEAN'
import Dregg2.Circuit.Emit.NoteSpendingLeafEmit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.NoteSpendingLeafEmit
def main : IO Unit := IO.println (emitVmJson2 noteSpendLeafDescFixed)
LEAN
lake env lean --run "$scratch/Emit.lean" > "$scratch/emitted.json"
cmp "$scratch/emitted.json" "$repo/circuit/descriptors/by-name/note-spend-leaf.json"
python3 - "$repo" "$scratch/emitted.json" <<'PY'
from pathlib import Path
import json, re, sys
root = Path(sys.argv[1])
d = json.loads(Path(sys.argv[2]).read_text())
assert (d['trace_width'], d['public_input_count'], len(d['constraints'])) == (149, 7, 33)
assert sum(c['t'] == 'boundary' and c['row'] == 'last' for c in d['constraints']) == 6
route = (root / 'metatheory/EmitByName.lean').read_text()
assert re.search(r'\("note-spend-leaf.json",\s*Dregg2.Circuit.Emit.NoteSpendingLeafEmit.noteSpendLeafDescFixed\)', route)
print('PASS: repaired note-spend proof, exact consumed bytes, six last-row boundaries and route')
PY
