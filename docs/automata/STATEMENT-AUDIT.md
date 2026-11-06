# Statement audit gate — 2026-11-06

Initiative register row **1**, parser/language excellence (policy language, demos, perf,
Lean-first AIR generator, build), breadstuffs, L2–L3. Register acceptance remains: policy
language elaboration and compilation proved; two public demos; generator replaces handwritten
AIR; `make check-fast` under two minutes. This gate advances proof engineering without declaring
the whole initiative complete.

[READ] The manifest covers the Datalog exact-count/stratified/join/safe/budget statements, generic
content-bound DFA kernel, table interpretation boundaries, committed LRAT and bisimulation,
full-width route binding, the **actual table/weld/Dyck record consumers**, cached compilation,
certified union, the actual whole-word/absence compiler wrappers, and generated range, borrow, tuple, solvency, caveat and payment AIR, plus the served note-spend wrapper. Each scoped review names its
statement, witness, falsifier and limitations. All local module roots participate in dependency
identity checks, including `Metatheory`; a dependency hash does **not** claim a semantic review of
every theorem in that file.

The approach follows forensics' separation of mechanical extraction from source-bound statement
judgment, and the certificate statement audit's distinction between a well-typed proposition, an
inhabited conditional theorem, and an implemented cryptographic claim. The machine gate checks
identity and evidence coverage; Lean checks exact axiom sets; reviewers check what consumers can
actually conclude.

## Running the gates

```sh
python3 scripts/check-automata-statements.py --self-test
bash metatheory/scripts/automata-check.sh --statements-only
# Optional negative kernel check: inject an axiom into a temporary copy of one proof.
python3 scripts/check-automata-statements.py --kernel-self-test
# Actual consumer compiler execution; outputs are checked, and returned tables carry hdec.
cd metatheory && lake env lean --run scripts/automata-compiler-smoke.lean
```

`--statements-only` checks all review identities and the four small audit modules on warm imports;
it does not rebuild every imported family. The full family gate builds dependencies and checks the
owning modules' exact axiom pins. After shared Lean interface changes, the designated-host whole-tree
build remains required. The presentation-type kernel change is such an interface change.

[MEASURED] The initial one-module gate passed with 23 exact pins, zero guards and zero failures in
34.5 seconds on a warm Mac. Its copy-only tests rejected changed source, removed axiom pin (even
with that copy's digest refreshed), missing falsifier and changed toolchain identity. The direct
kernel mutation was rejected specifically because the unchanged `#guard_msgs` report detected the
injected custom axiom. The expanded four-module gate passed in **26.2 seconds** at four jobs on the warm Mac:
52 checked axiom pins, zero guards, zero failures. Its source preflight covered 25 reviews and
172 exact pins; the later note-spend review adds one review and eight owning-module pins without
changing those four audit modules. Five copy-only mutations now pass, including removal of an
owning-family pin after refreshing the copy's digest. The final injected-axiom check also passed.

## Evidence and repairs

- Positive Datalog now has `honest_verifies` and `open_trace_separation`: the complete three-round
  path certificate accepts; removing only closure accepts the partial database at its own count,
  while the real checker refuses that same statement/certificate.
- `StatementAudit.runStrataJ_domain_congr` proves membership-equivalent domains give identical
  optimized replay. Positive join and budget witnesses use this general fact instead of trying
  to kernel-evaluate the well-founded sorting implementation. The budget separation preserves the
  accepted EDB and tampers only with the accumulator.
- `DfaBoundVerifierKernel` separates executable input presentation from its interpretation as a
  `BoundStatement`. `DfaBoundReference` supplies an actual Boolean-table checker, proves extraction,
  and instantiates **the generic theorem** on two symbols. Identity commitment rules out its exact
  collision branch. A wrong record is refused, and a rejecting word has no accepting trace. No
  classical decision oracle is presented as executable verification.
- The table examples expose the empty-word boundary, missing-table validation, and omission of a
  rejected record. They are deliberately small semantic counterexamples, not compiler outputs.
- The committed LRAT evidence includes an accepted PHP certificate and a false-UNSAT separator
  with a concrete satisfying assignment. The bisimulation separator targets a false inclusion
  with an explicit violating word, plus independent root-membership/closure comparators.
- Table and weld route consumers use eight-lane commitments and public lengths. Their residuals
  name distinct **canonical arity-16 inputs on the actual two routes**. Full descriptor witnesses
  instantiate the respective soundness statements and refute their exact residuals. The weld
  review caught a remaining opening-inequality-only falsifier; it was repaired with generic
  `WeakAccepts`/`StrongAccepts`, a soundness theorem consuming the latter, and refusal on the same
  proof, endpoints and substituted record.
- Dyck's record wrapper fixes the word-derived padded route and row count. Its full witness
  includes the chip table, canonicality and initial grammar symbol; first-done/live conditions are
  derived rather than supplied as an honest reference trace.
- Compiler review covers exact cached-worklist equivalence and proof-carrying union/absence
  construction. `compiler-wrapper-smoke.json` records execution of the actual `certifySurface` and
  `certifySurfaceAbsence` wrappers on `byte7|byte9`, with five words each. Every returned table has
  `Certified.hdec`; successful wrapper execution is labelled runtime evidence, not a theorem
  proved by a native evaluator. The code and result are both source-bound in the manifest.
  Reachable trimming treats its BFS as an untrusted candidate builder: reverse simulation is
  checked before restriction. Its named three-row/six-row embedding and rejected shifted embedding
  exercise that checker; failure retains the original certified table.

- Generated arithmetic review invokes the actual range and borrow theorems and the full-premise
  solvency commitment, caveat public-operand and payment identity theorems. Reconstruction and
  final-borrow counterexamples execute the generated expressions. Consumer falsifiers retain the
  old modular insolvency acceptance and final-row range bypass. The tuple generator binds rows
  modulo the field; canonical integer equality remains a separate premise.

- The served note-spend wrapper retains the earlier proof envelopes and adds a joint full-premise
  witness invoking its member theorem. The same one-row forge accepts under the old descriptor
  and is refused by the consumed fixed descriptor. Its positive path has depth zero; the abstract
  permutation and scalar Merkle fold are not a deployed Faithful8-tree security claim.

## Boundaries retained

[READ] These are scoped review verdicts, not automatic semantic guarantees.

1. Datalog's unrestricted coincidence requires dense range restriction. Counts are by predicate,
   budgets use signed mathematical integers with missing arguments contributing zero, and
   independence from another valid stratification is not proved.
2. The generic DFA reference is a public-trace checker with identity commitments. It does not
   instantiate production STARK extraction, hiding, or a deployed hash-security bound.
3. Table agreement does not establish intended policy language, table validation, external corpus
   coverage or provenance. The compiler's certificate and the caller's corpus obligations are
   separate.
4. Route proofs retain their explicit canonicality, chip soundness and height-admission premises.
   A raw descriptor verifier does not by itself perform the record-opening comparison. Row-heap
   existence in the weld is denotational, not a proved efficient extraction algorithm.
5. Dyck's route remains a **single 31-bit field element**, not the eight-lane security claim of the
   new table/weld variants. Its abstract collision residual and native codec/extraction bridges
   must be priced and instantiated accordingly.
6. LRAT is RUP-only; its Std checker is a cross-check. Bisimulation admits its specified decidable
   predicate fragment, with encoding injectivity over integers rather than a proved deployed
   byte/felt codec.
7. Generated payment identity proves arithmetic and chip-output wiring, not external transcript
   authentication. Solvency and payment interfaces retain scalar hash heads; these statements do
   not confer the eight-lane route binding claim.
8. The manifest reviews named claims and consumers, not every helper theorem in every dependency.
   New consumers need their own scoped entry and actual premise/falsifier evidence.

## Updating a stale review

A changed reviewed source, imported local definition, toolchain, package manifest, or execution
artifact invalidates the snapshot. Inspect the diff and its semantic effect through the named
statement and evidence; update scope, pins and digests together. Do not refresh hashes merely to
make the gate green. The JSON has no automatic approval operation. Comment-only edits still
invalidate byte identity; a reviewer can record why the previous semantic judgment survives.

Exact axiom pins may live in the family that owns the theorem rather than being duplicated in a
central import-heavy module. The targeted warm audit gate and full dependency-building family gate
have distinct coverage, stated above. This keeps ordinary checks cheap without claiming that
source inspection executes Lean or that compilation determines statement meaning.
