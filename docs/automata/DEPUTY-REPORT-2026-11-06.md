# Initiative 1 — parser/language excellence

Codex gpt-6-astra deputy, 2026-11-06. **In progress; integration checkpoint at 21:55 UTC.**
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

## Integration checkpoint, 20:55 UTC

Register row remains **#1** above. Landed locally: `7f0c7efae` repeat-cache improvement;
`635b3b3d8` initial statement gate; `8eab9c5d8` static-source/provenance phase repair;
`bf583f317` ordered table/weld routes, Dyck canonical record verifier, shared DECO/caveat
generators and current counts. The initial 21-file solvency/tuple/injection set was accidentally
included by another lane in `a63744ae4` (stream commit); its subject/author do not describe those
files. Preserve the useful changes; their checks and construction are recorded in the AIR reports.
The counts model landed on zkml-research dev in `2fcf3c5d` plus pin follow-up `a77ab620`, both pushed.

The predecessor chain completed at 20:36:15 UTC, emit exit 0: all 247 descriptor files matched
source `609ae705400dd4636a39d5a5acac9138a6e192f8`, one missing stamp row repaired, only
PROVENANCE changed. The two peaks above are its complete over-12-GiB list, with the sampler
limitation unchanged. Its stamp is not installed as evidence for our newer source. Mina rescue
`e4919780a` now reduces wrap stages to 9.4 GB / 1:53; body rescue was `7c90a9b60`.

### Current coordination and verification

The push gate's missing grain-session manifest was repaired by its owner in `1f0c4a331`.
The next push was blocked by a different lane's documentation reference:
`metatheory/Dregg2/Tree/Cert.lean:14` names the Spec module with a path the reference checker
does not resolve. The Tree owner should use its full Dregg2-relative path; this deputy does not
edit Tree-owned source. No gate bypass is used. SSH keepalives now cover long pre-push scans.

Native Rust compilation reached the real Lean FFI under an 8 GiB cap; when aggregate box RSS
rose to 94.09 GiB, only our PID-file-owned process group was stopped. Result: RESOURCE
INTERRUPTION, no test verdict. Its cached dependencies survive. Retry uses completed independent
iteration/stamp artifacts, one Rust/Lean/C worker and a launch threshold of 50 GiB summed RSS.
Long-lived idle controller scopes make the old sum-of-declared-caps rule unusable on this box;
current scheduling follows the task's explicit summed-RSS plus 40-GiB headroom criterion and the
enforced 100-GiB aggregate slice. No foreign process or cache is changed.

The composed compiler still needed work after the first union proof: 638 product states trim to
49 reachable states, but the absence constructor's linked-list indexing repeated inside nested
loops remains cubic. The lane is replacing that loop with an exactly equivalent precomputed
successor set. No final absence table or newly signed receipt is published before it runs.

The next C9 consolidation is grounded, not speculative: both note-spend constructors are fixed
zero-argument Rust lowerers despite the original census calling them parameterized. A routed
Lean emitter and refinement already exist, including a stronger descriptor that closes six
last-row freedoms. The lane is connecting those existing proofs and bytes to both consumers.
The deeper path-shape premise remains explicit until actually enforced.


## Integration checkpoint, 21:30 UTC

Register row remains **#1** above. Source batch `9773903d3` is now on public main. It adds
certified union, checked reachable-state trimming, exact factor successor optimization,
the executable bound-DFA reference instance, 26 scoped statement reviews / 180 exact pins /
228 source identities, and the shared fixed note-spend artifact. The latter removes two
more Rust lowerers (ten production constructors removed in this cycle), retains all actual
path/canonicality/chip premises, and has a jointly inhabited member theorem plus same-trace
old-accept/new-refuse separation. The umbrella imports the new modules.

[MEASURED] Native absence compilation now completes in 28.858509 s with 129 states and
33,024 transitions; all 12 controls pass. Product size 638 trims to 49 reachable states,
then 48 whole-word states; checked factor construction produces the final 129-state table.
The new table was replayed over all 100,000 public corpus documents: 1,770,996,081 bytes,
Lean and Rust count 0, all three controls pass. A new tuple is signed with the unchanged demo
key. The demo source/artifacts are coherent but await their named landing and native proof
verification; no final route-bound proof timing is claimed yet.

The served Rust harness reached production-library compilation but first missed a harness-only
`postcard` dependency. That setup was repaired and the workspace nightly pinned; its next
run was stopped by our own resource monitor at two global-RSS samples above 84 GiB, before
any tests ran. These are setup/resource outcomes, not a proof-test green. The next build uses
a 50-GiB launch threshold, one compiler and 4-GiB cap. The actual full-crate command remains
required, because the stranger's default replay invokes it; a standalone harness cannot replace
that bootstrap check. Whole-tree Lean and current-source provenance are pending.

[READ] The iteration-speed note has now arrived at
`/Users/ember/dev/redregg/landscape/ITERATION-SPEED-2026-11-06.md`. Its cold breadstuffs build
was deliberately stopped after 2,115 modules; borrowed artifacts are cache, not a complete green.
Its snapshots carry `.c` as well as oleans/IR, and it reports keyed read-only package tooling
and `make check-fast` / `check-full`. The two-minute bar is not yet measured here.
`LEAN_NUM_THREADS` alone does not cap Lake's concurrent module processes; our full-tree job
needs admission control. Use `/usr/bin/flock`: the bb2 PATH version is an unrelated shim.

The Mina lane additionally landed `e601f3b13`, taking wrap stages to the import floor with
compiled block-data facts. This changes the evidence class of those facts; do not repeat the
earlier rescue's unchanged-axiom claim for this newer step. The final emitter run must include
the latest committed Mina source and state its actual source revision.

C9 remains open beyond these static leaves. `AIR-REMAINING-DEBT.md` separates interpreters,
test scaffolds, live generators and composition transformations. Two further grounded cuts
are underway: UMem cohort staging can carry domains directly instead of constructing a discarded
descriptor; the binary membership block is depth-uniform and can be generated with a real
actual-height SAT-to-path theorem. Its depth label currently does not enforce proof height,
and the existing 4-ary functional theorem cannot serve as that bridge. The direct-logic,
custom-leaf, zkOracle and live composition compiler obligations remain explicit work, with no
private information or permission needed from Ember.

The synthetic governance source is public in microsites `3702f886`; a later public-main
commit contains it. GitHub Pages build succeeded, but deployment remains queued. Neither
page is reported live until its actual HTTP content is checked. No old local microsite history
was pushed. Another initiative's session-derived Tree demo is outside this deputy's publication
scope; this initiative's demos and new fixtures use synthetic or independently public data.


## Integration checkpoint, 21:55 UTC

Register row remains **#1**. `9773903d3`, `000ce3b99`, `4b0146d52` and `247ebb4b9` are now
confirmed ancestors of public main: certified compiler/audit/note-spend, UMem metadata staging,
certified public-corpus demo, and generated binary membership respectively. The statement gate
is now 27 reviews / 192 exact pins / 235 source identities. Eleven production constructors have
been removed; generic compiler and weld debt remains in `AIR-REMAINING-DEBT.md`.

[MEASURED] The final served harness passed all seven selected table/weld/Dyck/absence tests
(21 filtered out). The actual 2,048-byte public absence record uses 20 columns, 32 constraints,
two tables and three proof instances; 147,909 proof bytes, 12,371 ms prove, 26 ms verify.
Changed actual record, final state, route and length are refused. The full-crate bootstrap is
still a separate gate. Corpus replay and signed-tuple checks passed before the source landing.

[READ, MEASURED] Root note `dcd045cd2` reports the whole-tree floor gate red on four declarations:
`DfaRoutingRung2.collisionFree_of_injective`, `wtTrace_rung2_fires`,
`DfaRoutingTableBound.trail_unique`, and `word_public_of_functional`. Exact diagnostics were
recovered from `/home/build/stream/build.log`; this deputy owns their repair. No baseline
increase is planned: generic algebra, actual reference premises and executable finite-table
functionality validation supply more useful interfaces. The current controlled whole build is
also diagnosing the full source; a final green follows the repair. No other lane's clone is built in.

The std-only native AIR gate exposed three syntax-classification defects: nested tuple and
trailing-comma patterns in the flat interpreter and Mina consumers were counted as authored
constraints. The classifier repair is underway with positive-constructor counterexamples;
production source and baseline limits will not be weakened to clear these rows. Actual native
counts confirm the generated binary membership consumer authors zero constraint sites.

[MEASURED] A separate sparse Mac clone at `bac75df74` uses verified read-only package key
`856c40722ebb` and 21,824 independent cache files (no shared live inodes). Its meaningful
`make check-fast FILES=Dregg2/Policy/Compositional.lean` run refused seven stale imports in
14.50 s; an external wrapper prevented its automatic dependency build. This is a refusal,
not the two-minute green bar. Refreshing from the current validated host artifacts and repeating
that command is still required. No Mac whole-tree/native build ran.

Microsites `cb912f51c021271a9f76fd7f1019700e8161beba` publishes the revised public absence
page; it includes the prior synthetic governance page. GitHub Pages run `42298535049` is queued
for an ubuntu-latest runner. Previous builds succeeded but their deploy jobs were cancelled by
newer Pages requests. Neither page is called live yet; further content pushes restart that queue.
The original local microsite history remains untouched and unpushed by this deputy.

Publication now uses a clean separate clone, not a worktree, with the same pre-push hooks.
A clean clone exposed a historical audit link to untracked Foundry output. `8ed9ce062` preserves
the historical observation but correctly distinguishes it from checked-in deployment evidence;
its tracked script reference replaces the dead artifact link. No hook bypass is used. Remote
merges can now happen in that owned clone without touching the shared dirty tree.
