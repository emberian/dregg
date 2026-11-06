## Lane B (policy language)

Owner files: `metatheory/Dregg2/Policy/` (Syntax, Lexer, Pretty, Parser, ParseRoundTrip,
LexRoundTrip, Theorems, Elab, Compile, Factor, README.md, examples/*.policy),
`metatheory/Policyc.lean`, the `policyc` block in `metatheory/lakefile.toml`, the Policy import
lines in `metatheory/Dregg2.lean`, and `docs/automata/POLICY-LANGUAGE.md` (EBNF, examples,
theorem statements, counts, what is not claimed).

Landed:
- `2053d0a9d`: the language and `parse_print_roundtrip : p.wf = true → parse (print p) = .ok p`
  for the whole AST (`print_injective`, located-error `#guard`s).
- `ca181466a`: `elabRe_semantics`, `absenceOf_semantics`, `elabGrammar_rules`/`dyck_derives`,
  `elabProgram`/`strataOf`, `compiled_decides`, checked minimization (`simCheck_verdict`), the
  checked factor construction for absence (`absence_decides`), `lake exe policyc`, the note.
- No later lane B commits. The working tree holds no uncommitted lane B work.
  (`demo/absence-receipt/policyc/` is untracked and belongs to another lane, not B.)

Known slow: counted repeats such as `"sk-" \w{20,64}`. Measured costs: `\w{16}` 1.5 s,
`\w{32}` 21.7 s, `\w{20,64}` over 120 s, all on the whole-word table. The cost is
`Crypto/Deriv/AciComplete.lean` `simDecide R S := reEq (nrm R) (nrm S)`. It is called from
`SymbolicFixpoint.seenSim` (inside `reachFixAux`) and from `GuardAut.idxOf` (filling the table,
memoized once per state × cover symbol in `Compile.lean` `Compiled.memo`). It normalizes BOTH
sides on every comparison against every seen state.

Proposed fix, in `Dregg2/Policy/Compile.lean` only: a Policy-local worklist that stores `(s, nrm s)`
pairs and compares `reEq (nrm t) n_u` against the cached normal forms. Prove its closure lemma by
copying `reachFixAux_closed` (a draft `reachN` that pushed `nrm (der a s)` was written and
removed; it was slower, because it still re-normalized in `simDecide`). Then build `GuardAut`
directly; the fields are `root_rep`, `closed` and `states_rig`. Pushing nrm'd states is NOT the fix.

Next steps:
```
cd /Users/ember/dev/breadstuffs/metatheory
lake build Dregg2.Policy.Theorems Dregg2.Policy.Factor policyc     # gate; never a bare lake build
./.lake/build/bin/policyc check   Dregg2/Policy/examples/absence.policy
./.lake/build/bin/policyc compile Dregg2/Policy/examples/absence.policy --pattern delim --absence
./.lake/build/bin/policyc rules   Dregg2/Policy/examples/revocation.policy
```
Follow-up theorems:
- `parse s = .ok p → p.wf`
- named pattern references (`pattern b = a & ~c`)

JSON shapes:
- `policyc compile <file> --pattern NAME [--absence]`:
  ```
  {pattern, absence, source, states, alphabet: 256, delta: [[256 ints] per state], start,
   accept: [...], num_states, transitions: [flat, s*256+b], accepting}
  ```
  A non-accepting sink is relabelled to state 0. The dfa-crate fields
  (`num_states`/`transitions`/`start`/`accepting`) are what lane C's `lake exe dfa-run` reads,
  unchanged (checked on `"{{"` and `"-----BEGIN"`). Lane D / F consume the same table as the
  absence automaton. Correctness of the printed table is `Certified.hdec`.
- `policyc rules <file>`:
  ```
  {program: [{head: {pred, args: [{var: i} | {const: z}]}, body: [{pos: ATOM} | {neg: ATOM}]}],
   strata: [[rule idx]] | null, stratified, positive, predNames}
  ```
  This is the `statement.program`/`strata` shape of lane A's `datalog-check`. The EDB, root and
  count are the caller's.
## Lane C (build, counts, demo a)

2026-11-06. Lane C of the automata program (Opus). Tags: [MEASURED] run today; [READ] seen in the file.

### Files lane C owns

- `metatheory/scripts/automata-check.sh`: the family gate. Deps build, then `lake env lean` per file at
  `-j N`, then a table (status, seconds, `#guard` count, kernel-clean keystones); `--json`, `--files`,
  `--list`, `--no-deps`, `--hbox` (re-exec inside `swarm-build`, `SWARM_MEM_MAX=12G`). Lanes A, B and E
  have appended family directories to it; append, do not rewrite.
- `docs/automata/BUILD.md`: Mac and hbox commands, timings, the warm-checkout recipe, the Mac mathlib
  finding.
- `docs/automata/COUNTS.md`: GENERATED. Do not hand-edit. Generator: zkml-research
  `notes/construction-search/space.py --certs --markdown` (branch `dev`); `--check-pins` re-reads every
  cited `#guard` line under `$BREADSTUFFS_MT` (default `~/dev/breadstuffs/metatheory`) and refuses on drift.
- `metatheory/Dregg2/Crypto/Deriv/README.md`, `metatheory/Dregg2/Circuit/Emit/README-automata.md`.
- `demo/absence-receipt/*` (crate, `run.sh`, `README.md`, `EmitRecord.lean`, receipt artifacts),
  `metatheory/Dregg2/Automata/TableRun.lean`, `metatheory/Dregg2/Automata/TableRunSpec.lean`,
  `metatheory/DfaRun.lean` (`[[lean_exe]] dfa-run`), `circuit/tests/absence_receipt_record.rs`.
  Since lane C's last commit the demo was moved onto one compiler by another lane (`922eb8407`,
  `db844d64e`); read its README as current, not this section, for the compiler leg.

### What landed

breadstuffs `main`: `19f0b7d49` (gate script, BUILD.md), `80765ed8e` (COUNTS.md, hbox timings, the two
READMEs), `d22b8f76f` (hub and note 01: served toggle vs injection object, Weld8 by-name route),
`8707087b5` (gate: toolchain imports filtered, `Dregg2/Automata` in the list), `ddb1cba92` (demo (a):
receipt over 100,000 crates.io-index documents, count 0, signed; `dfa-run`; TableRunSpec; the one STARK).
zkml-research `dev`: `a596bdb2`, `b7232389`, `c1b29704` (the counts model). dregg-microsites: `3735989`
(`absence-receipt/index.html`), LOCAL ONLY, held for ember to publish.

### Half-built, and where

- Item 5 of the lane brief, the `dfa` conformance suite (a planned `lean_conformance` test target of the `dfa` crate): NOT started.
  It waits on a Lean-compiled byte table (lane B's `policyc compile`). When written, its header must say:
  regression evidence only, it does not discharge `tableDfa_faithful`'s agreement premise, and the
  runtime routes by longest-prefix acceptance while the certificate binds the whole word (codex round 3,
  finding 6).
- Count via lane A's `datalog-check`: not wired; the receipt's `count` is the `dfa-run` count, and
  `TableRunSpec.rejectCount_eq_zero_iff` states its meaning.
- The proved record binds nothing to the corpus root: the route-commitment conjunct for table routing is
  the program's open milestone (SUBSTRATE-DECISION §5 item 2).

### Next steps (commands)

```
cd /Users/ember/dev/breadstuffs/metatheory
scripts/automata-check.sh                       # the gate; never a bare `lake build` on the Mac
cd /Users/ember/dev/zkml-research
python3 notes/construction-search/space.py --check-pins
python3 notes/construction-search/space.py --certs --markdown > /Users/ember/dev/breadstuffs/docs/automata/COUNTS.md
cd /Users/ember/dev/breadstuffs/demo/absence-receipt
./run.sh verify                                 # signature, corpus root from documents.tsv.gz, digests; no clone
INDEX=<crates.io-index checkout at 681f94fc638e5a7639aa410c34b984a12bcd8dfe> ./run.sh   # full pipeline
cargo test -p dregg-circuit --release --test absence_receipt_record -- --nocapture       # the one STARK
```

When `policyc compile --absence` lands: produce the table with it, re-run `run.sh` (the receipt's
`table_blake3` changes and is re-signed with `keys/receipt_ed25519`, which is gitignored and exists only
on ember's Mac in `demo/absence-receipt/keys/`), then write item 5 against that table.

### Machines and disk

- hbox: the breadstuffs clone is now `/tank/dregg-build/automata` (moved there by another lane; lane C
  created it at `~/lanes/automata/bs`). Gate runs only (`metatheory/scripts/automata-check.sh --hbox`); do not grow
  it. `/` had 57 GB free at this writing [MEASURED].
- Mac scratchpad corpus clone (crates.io-index at the pin, 7.3 GB, deletable):
  `/private/tmp/claude-501/-Users-ember-dev-aidev/78fef112-a52f-425f-8503-f3fa24ff087c/scratchpad/corpus/idx`,
  work files beside it in `.../scratchpad/work` and `.../scratchpad/run1`.

### Limitations a successor must know

- The v2 assembly requires a power-of-two trace height ("base trace height 1724 must be a power of two"
  [MEASURED]), and an exact-public table pins the height to the run length, so a served table-routing
  proof exists only for power-of-two-length records. Demo (a) proves document 1598 (2048 bytes) for that
  reason.
- The Mac's shared mathlib (`~/dev/breadstuffs-codex/metatheory/.lake/packages/mathlib`) holds 5,969
  oleans with a Lean 4.35 header against a 4.30 toolchain; the gate's deps step rebuilds the ones a family
  file needs. A whole re-fetch is ember's decision (the directory is shared).
- `dregg_dfa::Re::compile` did not terminate on `~(any* · AKIA · any*)` at lane C's time (no associativity
  in `Re::or`); another lane has since changed the crate (`922eb8407`); re-measure before relying on either
  statement.

### Uncommitted in the tree under lane C's directories (not lane C's; listed, not committed)

- `demo/absence-receipt/tests/differential.rs` (modified), `demo/absence-receipt/policyc/` (untracked).
