# Initiative 1 — public demo delivery

| # | Initiative | Owner lane | Repo | Rung | Bar | Next gate | Last report |
|---|---|---|---|---|---|---|---|
| 1 | Parser/language excellence (policy language, demos, perf, Lean-first AIR generator, build) | parser deputy + 4 sub-lanes | breadstuffs | L2-L3 | policy language elab+compile proved; two public demos; generator kills hand-written AIR; `make check-fast` < 2 min | demo (a) corpus receipt; policyc | 2026-11-06 |

## Governance: ready for public delivery

[MEASURED] `demo/datalog-governance/run.sh` regenerates both invented variants in a fresh output
directory and checks them against the original signed receipts, without signing a replacement.
`run.sh verify` checks the original two certificates directly. `verify_receipt.py` verifies the
original trust anchor and compares the complete accepted tuple `(program_digest, root, pred,
count)` and checker identifier. Both variants pass: counts 2 and 0; final databases 966 and 973
facts. Signature verification alone would not establish this association.

[MEASURED] All three forged certificates are refused as well-formed inputs: unfinished lower
stratum, changed count, and dropped input fact. The deliberately weaker checker accepts the
unfinished-lower-stratum forgery. A separately valid signed receipt paired with the other valid
certificate is refused specifically at the count/root comparison. A nonempty output directory
is refused. The trusted signer and original artifacts are unchanged.

Counts, checker binary identity, and this run's native verification timings are in
`demo/datalog-governance/benchmarks/2026-11-06-signed-replay.json`. No STARK is claimed.

[READ] The final governance microsite contains only invented/public data, no transcript text,
no real-session metrics, and no links to real-session artifacts. The homepage now links both
demos. [MEASURED] Desktop 1280×960 and mobile 390×844 rendering checked; no document overflow
or external resource requests. Existing unpushed microsite history must not be published:
publication uses a fresh clone of public main and only the reviewed final files, preserving the
original local history intact. Root owns commits and publication.

## Absence: signed tuple and safe reruns

[MEASURED] `demo/absence-receipt/run.sh replay` reproduced the original public-corpus tuple:
100,000 documents, 1,770,996,081 bytes, Lean count 0, Rust count 0. Selection/hash list, 129-state
Rust baseline table, and legacy record descriptor matched the original artifacts byte-for-byte.
All three controls were enforced: AWS and PEM examples reject; near miss accepts. The complete
signed tuple comparison passed. Per-leg timings and runner identity are in
`demo/absence-receipt/benchmarks/2026-11-06-signed-replay.json` (explicitly the Rust compiler
baseline; the completed certified replacement is documented below).

The default replay can fetch the pinned public corpus into its new output directory; `INDEX`
reuses an existing checkout. `verify` authenticates stored metadata only and explicitly says no
corpus computation ran. Neither mode signs or replaces artifacts. `generate` writes unsigned
candidates for maintainers. Empty `WORK` is required; trusted signer identity is preserved.

[MEASURED] `python3 -I demo/absence-receipt/tests/receipt_binding.py` passes the honest tuple and
rejects an internally consistent changed count, same-semantics/different-bytes table, and wrong
signer. This exercises receipt association independently of the old shell greps.

## Certified compilation and the final corpus tuple

[MEASURED] The final native compiler succeeds in 28.858509 s: 129 states, 128 accepting states,
33,024 transitions, 200,146 JSON bytes, start state 64 and rejecting sink 0. Twelve semantic
cross-checks pass. The compiler's generic derivative normalization cache fixes counted repeats;
certified union composition and checked trimming reduce 638 possible state pairs to 49 reachable
pairs before minimization. The factor successor routine's old nested linked-list lookup was cubic
per byte. Hoisting active targets removes that repeated work; `nextSet_spec` proves exact equality
for every table, bitmap and byte. The existing factor correctness proof remains in force.

[MEASURED] With the JSON table exported by the native benchmark, the full public corpus was selected and hashed again,
then scanned by Lean (33.908 s) and Rust (25.907 s): 100,000 documents, 1,770,996,081 bytes, count 0
in both. Every control passed. The complete new tuple was signed with the existing local demo key
and verified against the unchanged original `allowed_signers`. The metadata verifier and all
three receipt-association regressions pass again. The corpus hash list and MMR root are unchanged.

`benchmarks/2026-11-06-certified-replay.json` under the absence demo records the exact source/table
hashes, counts, signed tuple and timings. The native compiler ran on bb2. The local `generate`
command used an explicit precompiled-table compiler override after byte comparison of the source;
loading that output is labelled separately from compilation. The default stranger command builds
and runs the native compiler itself. No Mac whole-tree or native library build was used by this lane.

[MEASURED] The two SHA-256 values describe different serialized inputs. The complete exported
`absence-table.json` is 200,146 bytes (including final newline) and hashes to
`f03425bde3de6748203d4daf4e3a3a16bf6687beabf68231e5fc1cd53093f03e`. The compact sorted-key JSON
projection to `num_states`, `transitions`, `start`, and `accepting` is 99,887 bytes, has no newline,
and hashes to `e61f7621be8f2ce4f019dfd57b73613fb79bb2f0abb261a1c9f65569d8a0adca`, matching the
native policy benchmark. Both were recomputed from the checked-in file. The demo benchmark now
calls these `table_file_sha256` and `table_layout_sha256` and records both input conventions.
The native benchmark exports parsed output by JSON reserialization; no independently retained
raw stdout byte digest is claimed. The layout digest preserves state numbering and array order.

The old Rust grammar (`policy.txt`) and differential regression material are retained. The active
pipeline now compiles `policy.policy` through the certified Lean path. The new signed source/table
Blake3 digests are `9ed0fa106e4b3e1804757f6ce55c451101294c09127ea5b17e3636d78b68d4fe` and
`21d0cd70c028d2bd2e86fb57e2295044fab4271498804f85b60bad1de723a9bd` respectively.

## Ordered record binding

[MEASURED] The final new route-bound record now has a passing native real-served proof verdict.
Full-crate bootstrap and the unsplit default replay remain a separate pending gate.

[MEASURED] The one-record descriptor is emitted by the warm Lean source and independently
reproduced by the full generation run: 2,048 rows, 20 columns, 11 public inputs, 32 constraints,
two declared tables, start/final state 64. The 2 KiB `record-1598.jsonl` fixture is copied from the
public corpus; replay compares it with the selected corpus file. No transcript data is involved.

[MEASURED, final served run] The Rust test checks each transition against the selected policy table, bounds the state
space below the field modulus, and derives its start and acceptance from that table. It constructs
the route with the shared helper and calls `verify_route8_record`, which recomputes the ordered
route from explicit record bytes before verifying the STARK with actual-height admission. Changed
final state, route root, length, and a changed record under identical proof/public inputs all fail.
The link to the corpus Blake3 leaf/MMR root is checked externally by replay; it is not a subproof
inside this STARK.

## Served proof result and remaining integration gate

[MEASURED] The final artifact pair passed on bb2 in the pinned `nightly-2026-06-21` real-served
harness against the normal circuit library (nextest 0.9.151, 4 GiB cap): 2,048 rows, 20 columns,
32 constraints, two tables, three proof instances, final state 64; prove 12,371 ms, verify 26 ms,
147,909 proof bytes. All seven selected table/weld/Dyck/absence tests passed. The test source
SHA-256 was `b53c7a3b91eb519e10ef7788ad24b7387e00c345468b479f8a59bc9126e98d47`; the final table
and descriptor matched their recorded hashes. Build-integration evidence is
`/home/build/astra-integration-control/rust-served3.sh` and its `.log`, source `9773903d3` plus
named final absence files. The earlier memory-pressure stop was superseded by this passing run.

The remaining integration gate is the full-crate bootstrap and unsplit default replay. The
standalone real-served proof establishes the native prover/verifier result for the final fixture;
it does not establish that the full-crate command builds. That command is:

```sh
cargo nextest run -p dregg-circuit --release --test absence_receipt_record \
  -E 'test(absence_record_proves_and_verifies)' --success-output immediate
```

The default replay includes this filtered test after reproducing the descriptor and comparing
every signed tuple field. No unsplit full replay verdict is claimed yet. The revised page's
one-record proof claim now has supporting measured evidence; root owns publication from the
clean clone and final commits. No new permission decision is required from ember.
