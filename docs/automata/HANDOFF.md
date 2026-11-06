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
