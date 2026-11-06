# Initiative 1 — parser/language excellence

Codex gpt-6-astra deputy, 2026-11-06. **In progress; integration checkpoint at 20:18 UTC.**
The register is `/Users/ember/dev/whatember/INITIATIVES.md`; its row at takeover is:

| # | Initiative | Owner lane | Repo | Rung | Bar | Next gate | Last report |
|---|---|---|---|---|---|---|---|
| 1 | Parser/language excellence (policy language, demos, perf, Lean-first AIR generator, build) | parser deputy + 4 sub-lanes | breadstuffs | L2-L3 | policy language elab+compile proved; two public demos; generator kills hand-written AIR; `make check-fast` < 2 min | demo (a) corpus receipt; policyc | 2026-11-06 |

## Grounding and ownership

[READ] The deputy handoff and all five sub-lane sections A/B/C/E/F have arrived and were read.
The register's next-gate text predates the landed corpus receipt and `policyc`. The handoff's
historical approval holds do not override the current task: publication of the synthetic
governance demo and the three content-binding shape changes are authorized. The existing
session-derived artifacts remain untouched pending ember's decision.

[READ] Grounding includes the substrate decision and ceremony review, all thirteen family notes,
semantic ceiling, counts, four audit rounds, actual compiler and bound-statement sources,
the two demo pipelines, the AIR census and the last 36 hours of commits. The standalone
certificate-statement audit remains the statement standard. The active work is:

| lane | responsibility |
|---|---|
| policy_performance | cache normal forms in state discovery and table lookup; prove exact equality to existing algorithms; native counts and timings |
| demo_delivery | synthetic governance publication, signed-tuple verification, safe stranger reruns, Lean compiler as absence demo table source |
| dyck_binding | canonical entry fields, final-row pins, record binding and named collision; served witness/test integration |
| table_binding | shared full-width route-chain decorator, public length, bound table-routing descriptor and consumer |
| weld_binding | repair row-specific collision residual first; consume the common decorator for the attested bound descriptor |
| certificate_falsifiers | isolated LRAT freshness/hint and bisimulation root/closure/false-inclusion counterexamples |
| lean_air_generator | classify actual AIR producers; replace solvency constraints with a Lean generator; reuse emitted zkOracle artifact |
| tuple_air_generator | one Lean generator replacing repeated PI-pinned tuple producers and their actual consumers |
| statement_gate | named premise witnesses, remaining Datalog separation, review evidence bound to source, standing gate integration |

Each lane owns disjoint files. The deputy commits named files on shared `main`, integrates
generated artifacts, updates counts from the existing `space.py --certs` model, and runs the
whole-tree bb2 check after shared-interface changes converge. No other initiative's source
ownership changes.

## Findings and decisions

[READ] `f476bd3e0` repairs round 4 items 1/3/5 for the hash-chained DFA, including the impossible
all-statements injectivity premise and the deterministic chain collision extractor. The weld
row-residual blocker, Dyck obligations and LRAT/bisimulation examples remain work at takeover.

[MEASURED] The first cached compiler implementation passes a single-file Lean check with
15 clean keystones. Native performance comparison is pending. An olean-warm bb2 checkout still
needs thousands of native C objects before linking `policyc`; this is relevant to initiative 7's
cache design, rather than a reason to build another independent native closure.

[READ] The original AIR census counts signatures as literals. Structural inspection finds 55
actual descriptor literals in 26 files before this deputy's edits, still including tests and
interpreters. `zk_leg.rs` already uses inline Lean-emitted JSON. The solvency producer really
constructs constraints in Rust, and its difference-only range check admits modular wrap:
`R = 0`, `L = 2^30 - 1` gives `(R-L) mod 2013265921 = 939524098 < 2^30` despite insolvency.
The replacement keeps the full advertised 30-bit amount range with two 15-bit borrow limbs.

[INFERRED from the emitted gates] The two approved Dyck selector gates alone leave the final
row free: transition gates skip it, but hash lookups consume it. Four terminal field pins are
also necessary. The lane is checking the resulting six-constraint change against full witnesses.

[DESIGN] Table and weld binding will share one Lean route-chain decorator. Its wide chip absorbs
domain, index, current, symbol, next and the previous eight lanes, padded with three zeros
to the chip's admitted arity 16, in one permutation. A public
length and canonical index envelope close wrap/length ambiguity. New served bound variants
must be selected by consumers before this counts as complete; retaining a legacy unbound
descriptor is not itself a repaired path.

## Build coordination for initiatives 6 and 7

[MEASURED] The predecessor's bb2 chain is still running in `/home/build/automata/bs`, pinned at
`609ae705400dd4636a39d5a5acac9138a6e192f8`; PID file `/home/build/automata/chain.pid`.
At 19:54 UTC its peak file reports `MinaBodyPreimageBitsAir`, 25,952,960 KiB, rc 0, 448 seconds.
**Attribution limitation:** the sampler selects the largest Lean process on the whole box, not
the module's cgroup, so this is not yet an independently attributed per-module peak. The new
Mina rescue change `7c90a9b60` postdates that pinned source. A final stamp must follow both the
Mina rescue and these automata emitter changes; the old stamp cannot certify them.

[MEASURED] Around 19:58 UTC bb2 summed process RSS was 60.7 GiB, while the enforced swarm slice
held 86.6 GiB of its 100 GiB allowance. Concurrent declared caps already greatly exceed the
budget (stamp, Mina rescue, iteration and other initiatives). Only the already-started 8 GiB
policy native build is running from this deputy; additional deputy remote builds are held
until capacity is available. Single-file warm Mac checks and source work continue.

The requested iteration-speed note and Mina rescue note were absent at their supplied paths
when checked; their active commits are being followed instead. `BUILD.md` now corrects the
older branch/rebase recipe and points new builds to owned bb2 clones. No build is started in
another lane's clone, and no inherited process is stopped.

## Remaining work and ember-only decisions

All active lane items above remain to be built, reviewed, integrated and published as applicable.
The C9 inventory must distinguish retired production producers from interpreters and genuinely
unmigrated constraints; no claim of whole-repository completion follows from a raw grep count.
The final report will name landed SHAs, actual checks, generated-source provenance and the exact
remaining continuation.

Only ember can decide the disposition of the already-committed real-session governance files,
and deletion of the predecessor's hbox data or shared caches. None blocks the synthetic demos
or current implementation work. No new request for permission is needed for the authorized work.

## Landings and integration checkpoint (20:18 UTC)

[MEASURED] `fbfe63c51` fixes the weld row-residual blocker with indexed opening heaps, and
repairs LRAT freshness/hint and bisimulation root/closure/false-inclusion falsifiers. Warm
single-file checks passed 21 + 28 + 46 clean keystones and exact axiom pins.
`4afe19bef` makes governance reproduction preserve original signatures and compare all signed
fields with the checked certificate; both synthetic counts (2 and 0), three forged certificates,
the weak-closure separation and swapped-valid-receipt refusal pass.

[MEASURED] The counted-repeat cache passes exact algorithm-equality proofs and native tests:
repeat 32 improves 24.359 s to 0.781 s; repeat 64 exceeds 180 s before and takes 8.740 s after;
`\w{20,64}` exceeds 180 s before and takes 3.101 s after (69 states, 17,664 transitions).
Completed baseline cases produce identical tables. The combined demo policy still exceeds
180 s: its two branches separately take 0.276 s and 1.283 s. A kernel-proved table-union
constructor is ready; the compiler lane is integrating it through the certified pipeline.

[READ, MEASURED] Microsites commit `3702f886013582cb837a293a1e71b3fc3bb1551e` has been pushed
from `/Users/ember/dev/astra-microsites-publish-20261106`, a fresh checkout of public main.
The inherited local history contains session-derived data in intermediate unpushed commits;
pushing its final synthetic tree would still publish that history. The old checkout is untouched.
Only the final synthetic page and public homepage links were copied into the fresh checkout.
GitHub Pages deployment is queued; live verification is still pending. Future page edits must
use this publication checkout or similarly preserve the privacy boundary.

[MEASURED] The initial generator closure has 16 clean solvency keystones and a fully inhabited
borrow witness, plus one generic tuple generator replacing five production constructors.
New solvency: 118 columns, 106 constraints; old shape: 51 columns, 36 constraints. Native
Rust integration remains pending. DECO and caveat admission are the next grounded static
producers, sharing range/fact-opening and bounded-borrow generators. Parameterized producers
and other AIR dialects remain explicit C9 work; no whole-repository closure is claimed.

### Coordination needed from the root's other initiatives

[MEASURED] `/home/build/astra-integration` is prepared with independent 8.9 GiB Lean and
1.8 GiB Rust caches, without a build. At 20:14 UTC bb2 RSS was 54.2 GiB, but twelve live
scopes reserve approximately 496 GiB in caps against the 100 GiB shared slice. Three old
48 GiB integration scopes hold less than 1 GiB each. The machine rules require summed caps
within budget; this prevents any new deputy allocation until owning lanes release or rebudget
them. No other lane is stopped. The iteration build is near completion (10,374/10,616 tasks),
and session-receipt bootstrap is generating the missing Lean FFI archive. Their completed
artifacts can avoid duplicate work. Persvati timed out both directly and via workhorse.

Initiative 14 currently owns unrelated uncommitted edits in `space.py`; our automata counts
update will preserve those and needs a serialized file landing. The requested iteration-speed
note remains absent. The Mina rescue note has arrived and is read: body preimage is down to
5.6 GB / 50 s; wrap stages rescue continues. A fresh full-tree build and provenance stamp must
use the integrated source after those changes.

### Answers for downstream consumers

[READ] Streaming's `docs/stream/GROUNDING.md` correctly treats a finite liveness counter as
an approximant, with unbounded counters characterizing infinite acceptance. Its same-raw-bytes
classification and leaf hashing is the essential content binding. The new routed weld retains
all eight map-root lanes and adds a full-width route plus exact length; the legacy weld remains
unbound to the word. At 4 KiB its binary representation costs 32,768 rows, 524,288 map-path
permutations and 32,768 additional route permutations: 557,056 total before other proof costs.
The initial executable route wrapper requires power-of-two row counts and rejects other heights;
canonical inactive padding is further work, not implicit support for arbitrary record lengths.

For streaming/tree public demos, new publication should use synthetic or independently public
data, as this initiative does. No session content or derived artifact is authorized for new
public publication by this parser task. These notes do not change another initiative's source
ownership. The theorem's exact codec, row-length and root-opening premises must travel with
any consumer; an unrelated valid table or certificate is not enough.
