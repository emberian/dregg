# Absence receipt: 100,000 public documents, two patterns, zero rejections

Demo (a) of initiative 1. The signed receipt names the policy source, its compiled table, an MMR
root of 100,000 public document hashes, the public corpus commit, document count, and rejection
count. The computational claim is reproducible; the signature authenticates the original tuple
under a demo key. It is not an attestation of the executable or a proof about the entire corpus.

**Validation status:** [MEASURED] Certified compilation, full corpus scans, controls, signed
receipt checks, and the new route-bound one-record STARK pass. The proof ran in the pinned-nightly
real-served harness against the normal circuit library. **Full-crate bootstrap and an unsplit
`run.sh replay` verdict remain pending.** The harness result does not establish those build steps.

## Run it

From the repository root, with Git, Rust, cargo-nextest, Python 3, OpenSSH supporting `-Y`, and
the pinned Lean toolchain installed:

```sh
demo/absence-receipt/run.sh replay
```

The first run builds the native tools and emitter and fetches the pinned public corpus. It
selects and hashes the 100,000 files, compiles the policy in Lean, runs both Lean and Rust scans,
checks the controls, regenerates the one-record descriptor, compares every signed receipt field,
and runs the filtered one-record STARK test. Counts and timings go to the printed output path.
Set `INDEX=/path/to/index` to reuse the corpus; `WORK=/empty/directory` chooses the output location.
Nonempty destinations are refused. Original artifacts, signatures, and trust anchors are preserved.

```sh
demo/absence-receipt/run.sh verify  # signature + stored metadata; no fresh corpus computation
python3 -I demo/absence-receipt/tests/receipt_binding.py
cargo nextest run -p dregg-circuit --release --test absence_receipt_record \
  -E 'test(absence_record_proves_and_verifies)' --success-output immediate
```

`verify` explicitly labels its limited scope. `generate` is a maintainer mode: unsigned candidates
only, no signing or installation. An explicit `POLICYC` executable override lets an isolated
builder supply the certified compiler; the default refreshes the native targets with Lake.

## What runs and what its proof says

[READ] These are the active source definitions and theorems.

| Leg | Artifact and scope |
|---|---|
| Public input | The first 100,000 paths, sorted bytewise, in `rust-lang/crates.io-index` at `681f94fc638e5a7639aa410c34b984a12bcd8dfe`; dot entries and root `config.json` excluded. A document is one file's bytes. |
| Commitment | `dregg-query`'s `Mmr<Blake3Mmr>` over `blake3(document)`, with its domain-separated leaf/node/bag/empty tags. `documents.tsv.gz` records the hashes so the root can be recomputed without fetching the corpus. This is the Rust mirror of `Dregg2.Lightclient.MMR`. |
| Policy → table | `policy.policy` is parsed and compiled by `policyc compile … --pattern secrets --absence`. `certifySurface` in `Policy/Compositional.lean` compiles alternatives independently and combines their `Certified.hdec` proofs with `Certified.union` in `Policy/Union.lean`; checked minimization preserves that field. `certifyAbsenceFrom` then constructs and checks the factor automaton, whose `absence_decides` theorem means that no substring matches the pattern. |
| Table → verdicts | Native Lean `dfa-run` executes the emitted byte table on every document. `TableRunSpec.accepts_iff` equates the runner with `TableDfa.accepts`; `rejectCount_eq_zero_iff` states what rejection count zero means. Rust independently executes the same table, and every count/rejected index must agree. |
| One served record | `EmitRecord.lean` emits record 1598 (`3/c/cxr`, 2,048 bytes) using `DfaRoutingTableRoute8.tableRoutingBoundDesc`. The shared eight-lane route helper constructs its witness; the served assembly prover/verifier checks it with actual-height admission. The final fixture passed in the pinned-nightly real-served harness; full-crate bootstrap remains pending. |
| Signed tuple | `verify_receipt.py` authenticates `receipt.json.sig` against the checked-in `allowed_signers` and compares every signed field with the recomputed artifacts. It never replaces the signer. |

The policy detects `AKIA` followed by 16 uppercase letters/digits and uppercase PEM private-key
headers. Parser/printing and regex elaboration have their own Lean theorems (`parse_print_roundtrip`,
`elabRe_semantics`, `absenceOf_semantics`). Every table returned by the compiler carries its semantic proof in
Lean. JSON rendering, CLI argument handling, compilation to native code, and filesystem I/O remain
outside those kernel statements; the JSON does not serialize a proof term.

## Counts and evidence

[MEASURED] The public corpus has 371,277 eligible files. The selection is 100,000 files
(`1/a` through `er/rn/errno-codes`), totaling 1,770,996,081 bytes. The MMR has 199,994 nodes and six
peaks, with root `17d69bbfa284b201d354dc3c9ae35a291d79d291c0bcfb78364e62fefcf2d6b7`.
The Lean and Rust counts are both zero. AWS and PEM controls reject; the 19-character near miss
accepts.

[MEASURED] The certified table has 129 states (128 accepting), 33,024 transitions, and a
200,146-byte JSON representation including both flat and row layouts. State 0 is the rejecting
sink; the start state is 64. Native certified compilation on bb2 took 28.858509 s, with 12 semantic
cross-checks. The complete new-table corpus scans took 33.908 s in Lean and 25.907 s in Rust on
the shared Mac. The exact tuple, file digests, compiler profile, and per-leg timings are in
`benchmarks/2026-11-06-certified-replay.json`. Compiler execution and local loading of its output
are explicitly separate timings. Its two SHA-256 conventions are also separate:
`table_file_sha256` (`f03425bd…`) hashes all 200,146 exported file bytes, including the final newline;
`table_layout_sha256` (`e61f7621…`) hashes the 99,887-byte compact, sorted-key JSON projection to
`num_states`, `transitions`, `start`, and `accepting`, with no newline. The latter matches the native
policy benchmark's `table_sha256` field. State numbering is preserved; this is not a canonical
language-equivalence digest. The benchmark export reserializes parsed native JSON, so the complete
file digest is not presented as a separately verified digest of raw native stdout.

[MEASURED] The final route-bound record passed the real-served harness on bb2 with
`nightly-2026-06-21`, nextest 0.9.151, and a 4 GiB memory cap. It has 2,048 rows, 20 columns,
11 public inputs, 32 constraints, two declared tables, and three proof instances. Proving took
12,371 ms; verification took 26 ms; the serialized proof was 147,909 bytes. The complete selected
served suite passed 7/7. These are measurements of the final certified table and descriptor,
not the historical Rust-table proof.

The first two public inputs are start/final states; eight bind the ordered route, and the last
binds its length. The test checks each declared transition and accepting endpoint against the
selected policy table. Changed final state, route root, length, and an explicit changed record
under the same proof and inputs are refused. The family-level order-splice test separately
exercises both orders of the same edge multiset. Full-crate Cargo bootstrap and the unsplit
one-command replay still require their own passing verdict; the standalone harness is not a
substitute for that integration gate.

The historical Rust-compiler replay is recorded in `benchmarks/2026-11-06-signed-replay.json`.
It predates the certified compiler and route-bound proof; its timings must not be relabeled as
measurements of the new construction. The receipt-association regressions reject an internally
consistent changed count, changed serialized table bytes, and an untrusted signer while leaving
the original trust anchor unchanged.

## Limits of the statement

- **The corpus verdicts are native re-execution.** There is no STARK over all 100,000 documents.
  The one-record STARK exercises the served path; it does not cover the other 99,999 documents.
- **The one-record route is not the corpus MMR leaf.** Under the eight-lane hash assumption, the
  public route binds the ordered transition path and its length. The STARK itself does not establish
  equality between that route and the named document's Blake3 leaf or the corpus root. The record
  verifier recomputes its route from the actual public bytes and the selected table, and rejects a
  changed record under the same proof and inputs. Full replay checks those bytes against the
  selected corpus file; the hashing/MMR linkage is checked externally.
- **Selection has no non-omission theorem.** The root binds the ordered document hashes. The
  assertion that they are the first 100,000 files at the pin is checked by rerunning selection.
- **Zero rejections is not zero secrets.** Only these two byte-pattern families are scanned.
  Other formats, encoded secrets, credential validity, and semantic confidentiality are outside
  the policy.
- **A demo key is not a personal identity.** Its signature binds the tuple, not the checker
  executable, its execution, or the origin of bytes supplied to it.

## Compiler history

[READ, historical measurements] The original Rust derivative compiler did not terminate promptly even for an absence pattern
with one four-letter literal: its alternation smart constructor omitted associativity, so
semantically identical derivatives kept different shapes. The interim normalizer reached 9,153
states; the repaired `dregg_dfa::Re::compile` reached 4,577. Both minimized to the same 129-state
table. The old `policy.txt` and differential test remain as historical regression material; the
active pipeline uses the Lean policy source and certified compiler.

A second bottleneck was Lean's repeated normalization during similarity checks. Caching the
normal forms while preserving the exact worklist/table result fixed counted-repeat compilation.
The two-pattern raw union still exceeded 180 seconds. Compiling its alternatives separately
and composing their certified tables avoids that raw-union expansion. The 638-state product is
trimmed to 49 reachable pairs using a checked reverse simulation before minimization. Factor
successor computation now precomputes active targets once; `nextSet_spec` proves exact equality
with the earlier cubic linked-list formula. No regex semantics is changed and no unproved product,
trim, or minimizer is inserted into the acceptance path.
