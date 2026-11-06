# Policy compiler normalization cache

Initiative register row **#1 — Parser/language excellence (policy language, demos, perf,
Lean-first AIR generator, build)**. This change addresses counted-repeat compilation, not
completion of the other obligations in the row.

[READ] Grounding: `Policy/Compile.lean` already produces a `Certified R`; its derivative
worklist is `Crypto/Deriv/SymbolicFixpoint.reachFixAux`, and `GuardAut.ofFix` supplies the
closure and semantic proof. `AciComplete.simDecide` computes `reEq (nrm R) (nrm S)`.
Both `seenSim` and `GuardAut.idxOf` invoke it for each state comparison. The previous
memoized table avoids repeated cover-symbol lookup per byte, but it does not cache the
normal forms inside a lookup. The predecessor's measured `"sk-" \w{20,64}` compilation
exceeded 120 seconds (see `POLICY-LANGUAGE.md`).

The replacement retains the original representatives, their order, the same derivative
successors and the same fuel accounting. Each pending state is normalized once per pop;
seen states carry their cached normal forms with an equality proof. `reachCached_eq`
proves exact equality to the old worklist after projecting away the cache, for arbitrary
seen states, pending states, covers and fuel. It covers failure as well as success.
`cachedIdx_eq` proves exact first-match lookup equality. `Compiled.memo_eq` transports
that equality to every table entry. Existing `GuardAut.ofFix`, `compiled_decides`,
`Certified.hdec`, checked minimization and checked absence construction are reused.

This is normalization caching, not a new regex equivalence or canonical-form claim.
In particular, no commutativity law is added to the existing `Sim` relation.

[INFERRED] Counts before clocks: let `U` be unique frontier states, `K` cover symbols,
`P` worklist pops, and `C` the number of state comparisons. Previously the worklist
performed `2C` calls to `nrm`; it now performs `P`. A successful complete run has
`P = 1 + UK`, because exactly `K` successors are queued per newly added state.
The table previously normalized both operands per comparison; the new table uses
`U + UK` normalizations (one per state, one per state/symbol query). The number and
order of comparisons are unchanged. These are algorithmic call counts, not machine
instruction counts; normalization cost still depends on regex size.

Reproduce the native benchmark after building `policyc` on a build host:

```sh
python3 scripts/benchmarks/policy-compile.py metatheory/.lake/build/bin/policyc \
  --baseline /path/to/baseline-policyc --output /tmp/policy-compile.json
```

The driver reports DFA state/transition counts before wall time, compares exact canonical
table digests, and exercises accepted lengths, both count boundaries, missing prefixes,
case-changed prefixes and suffix contamination. Its inputs are synthetic. Timeout
results are explicit and never treated as a compiled table. The timed subprocess's PID
is recorded, and only that recorded child is stopped on timeout.

## Native results (bb2, 2026-11-06)

[MEASURED] Both binaries built successfully under `swarm-build`, 8 GiB cap, two
Lean threads. The first native executable closure comprised 6,238 Lake jobs;
the revised Compile/Factor/Policyc rebuild then took approximately ten seconds.
`Compile.lean` checks 15 kernel-clean keystones; its new general equalities have
explicit `#guard_msgs` axiom pins. Mac single-file Lean and Linux native builds pass.

| repeat after `"sk-"` | states | transitions | baseline wall s | cached wall s |
|---|---:|---:|---:|---:|
| `\w{4}` | 9 | 2,304 | 0.520 | 0.068 |
| `\w{8}` | 13 | 3,328 | 0.164 | 0.117 |
| `\w{16}` | 21 | 5,376 | 1.176 | 0.164 |
| `\w{32}` | 37 | 9,472 | 24.359 | 0.781 |
| `\w{64}` | 69 | 17,664 | >180 (timeout) | 8.740 |
| `\w{20,64}` | 69 | 17,664 | >180 (timeout) | 3.101 |

Raw results: `policy-compile-benchmark-2026-11-06.json`. All completed baseline/cached
pairs have identical canonical table SHA-256 digests. All cached cases passed their
nine or ten byte-language/boundary checks. The larger baseline timeouts do **not**
supply baseline table digests. These are single wall-clock samples including process
startup on a shared host, not isolated steady-state latency estimates. The improvement
at 32 repetitions is about 31×; the formerly >120-second bounded-repeat case finishes
in 3.1 seconds here. Normalization caching does not eliminate the remaining linear
state search or the dependence on regex-term size.

[MEASURED] A separate demo union (`"AKIA" [0-9A-Z]{16} | "-----BEGIN " [A-Z ]*
"PRIVATE KEY-----"`, absence mode) still exceeded 180 seconds with the cached compiler.
That is a separate open construction cost, not hidden by the repeat result.
