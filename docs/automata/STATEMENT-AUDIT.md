# Statement audit gate — 2026-11-06

Initiative register row **1**, parser/language excellence (policy language, demos, perf,
Lean-first AIR generator, build), breadstuffs, L2–L3. Register acceptance remains: policy
language elaboration and compilation proved; two public demos; generator replaces handwritten
AIR; `make check-fast` under two minutes. This audit advances its proof-engineering gate; it does
not mark that whole initiative complete.

[READ] `statement-audit.json` records **eight scoped reviews** of the positive exact-count,
stratified receipt, optimized join, safe unrestricted receipt, integer budget, content-bound DFA,
table count, and table validation statements. Each names its statement, positive witness,
falsifier and limitations. The reviewer followed the actual predicates and the named collision
pair, not just theorem names or compilation. The local import closure is hashed to detect changed
definitions; hashing a dependency does **not** claim its entire contents were semantically audited.
The review approach follows the existing forensics distinction between mechanical extraction and
source-bound statement judgment, and the certificate statement audit's distinction between a
well-typed proposition, an inhabited conditional theorem, and an implemented cryptographic claim.

[MEASURED] The targeted gate passed on a warm Mac: **one file, 23 exact axiom pins, zero guards,
zero failures**, 34.5 seconds for its Lean/report phase. Source identity checks add approximately a
second, not a dependency build. Exact axiom output is checked with `#guard_msgs`; no new proof uses
`native_decide`. The standalone Python gate rejected all four copy-only mutations: changed reviewed
source, removed pin (even after refreshing that copy's digest), missing falsifier, and changed
Lean toolchain identity. Run from the repository root:

```sh
python3 scripts/check-automata-statements.py --self-test
bash metatheory/scripts/automata-check.sh --statements-only
# Optional direct negative check: inject an axiom into a temporary copy of one proof.
python3 scripts/check-automata-statements.py --kernel-self-test
```

`--statements-only` deliberately uses existing dependency artifacts; it does not establish that
all imports were rebuilt. The full family gate still builds dependencies before checking Lean.
After shared Lean interface changes, the whole-tree build on the designated build host remains
required. This change adds proofs only and does not change a shared structure.

## Evidence added

- `FixpointCert.Reference.honest_verifies` inhabits the exact-count premise with the complete
  three-round path certificate. `open_trace_separation` proves the same statement/certificate is
  accepted without closure and refused with closure. The false count is the partial database's
  own count, so the separator isolates closure rather than a mismatched count.
- `StatementAudit.runStrataJ_domain_congr` proves that membership-equivalent domains give the same
  optimized replay. The join and optimized-budget acceptance witnesses use it to avoid evaluating
  well-founded sorting during kernel reduction. This is a general theorem, not a new trusted
  evaluator or an assumption about a particular domain.
- The budget witnesses include a refunded charge and a positive sum. The weak comparator accepts
  the tampered final accumulator; the real verifier rejects it.
- The table evidence covers the empty-word boundary and supplies a tiny explicit malformed-table
  counterexample: the total runner accepts while `wellFormed` refuses. A separate omission example
  changes the count when a rejected record is removed. Neither is advertised as compiler output.

## Remaining boundaries

[READ] No new false core soundness theorem was identified in the reviewed statements. That is a
scoped review verdict, not an automatic semantic guarantee.

1. `Dfa.dfa_bound_identifies_record_or_collides` is conditional on a verifier kernel's extraction
   obligation. Its `aab_accepts` witness inhabits the language relation, **not all kernel premises**.
   The manifest labels this `relation-only`; a concrete full-premise bound kernel remains open.
2. Positive/stratified Datalog use active-domain semantics. Unrestricted coincidence requires dense
   range restriction, which `verifyJ` enforces. Counts are by predicate, not predicate-and-arity;
   budget values are signed mathematical integers, and missing arguments contribute zero.
3. The exact stratified model is for the strata named in the statement. Independence from another
   valid stratification is not proved here. Collision alternatives name the two participating EDBs
   through `mrootFind`; they do not prove collision resistance of the toy reference hash.
4. Table agreement does not prove the table is well formed, denotes the intended policy, or covers
   an external corpus. Those are separate consumer obligations.
5. This first manifest covers the named core statements above. It does not silently certify every
   automata-family theorem, the emitter families, LRAT/bisimulation, policy compilation, a compiler
   extraction pipeline, or any deployed hash implementation. Those reviews should be added with
   their actual positive premises and falsifiers as their owning lanes land them.

## Updating a stale review

A changed source, local imported definition, toolchain, or Lake package manifest makes the gate
fail. Inspect the diff and follow its semantic effect through the named statement and evidence;
then update the review scope, pins and source digests together. Do not refresh hashes merely to
make the gate green. The JSON has no automatic approval operation. Proof refactors and comment-only
edits still invalidate byte identity; reviewers may record why the prior semantic judgment survives.

The Python gate checks identity and evidence coverage. Lean checks the evidence and exact transitive
axiom reports. A human/model review still checks whether the theorem says what its consumer needs.
