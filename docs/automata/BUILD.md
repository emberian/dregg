# Building and checking the automata families

2026-11-06, lane C of the automata program (`SUBSTRATE-DECISION.md` §5 item 4, §6). Tags:
[READ] seen at the cited file; [MEASURED] a run on the named machine today; [INFERRED] derived.

## The gate: one script, both machines

```
cd /Users/ember/dev/breadstuffs/metatheory
scripts/automata-check.sh            # Mac: -j 4, table on stdout, exit 1 on any red
scripts/automata-check.sh --json     # one JSON object (rows, guards, keystones, timings)
scripts/automata-check.sh --files Dregg2/Crypto/Dfa.lean,Dregg2/Datalog/FixpointCert.lean
scripts/automata-check.sh --list     # the resolved family list
```

`metatheory/scripts/automata-check.sh` does three things [READ, its header]:

1. **deps**: `lake build` of every module the family files import (Dregg2 and Mathlib alike). On a
   warm, unchanged tree it is a no-op (6 s on the Mac [MEASURED]). It is there because
   `lake env lean` loads whatever olean is on disk: a stale Dregg2 olean can go green on an import
   that no longer typechecks, and an olean written by another Lean version fails with
   `incompatible header` (see "The Mac's mathlib" below).
2. **check**: `lake env lean <file>` on each family file, `-j N` at a time. Green means exit 0, no
   `error:` line, no `declaration uses 'sorry'`, and no `sorryAx` in any `#print axioms` output.
3. **table**: file, status, seconds, guards, keystones. `#guard` is silent when it holds, so GUARDS
   is the number of `#guard` commands in the file (all of which ran and held if the file is green);
   KEYSTONES is the sum of the `#assert_all_clean: N keystones pinned kernel-clean` reports plus the
   file's single-name `#assert_clean`/`#assert_axioms` pins.

The family list is the program's gate list plus every `.lean` file under `metatheory/Dregg2/Datalog/`
and `metatheory/Dregg2/Policy/` (lanes A and B add files there; they are picked up without editing
the script). Each file's full Lean output stays in the log directory the script prints.

## On the Mac

Only these two forms, from `metatheory/`:

```
lake env lean Dregg2/Datalog/FixpointCert.lean     # check one file against the warm oleans
lake build Dregg2.Datalog.FixpointCert             # build one module's import closure + its olean
```

**Never a bare `lake build` on the Mac.** `lakefile.toml`'s `defaultTargets` is fourteen libraries
(`Dregg2`, `Metatheory`, `Polis`, `Market`, `Bfv`, `PicklesSynthesis` and eight guard libs) [READ
`metatheory/lakefile.toml:2`]; a bare `lake build` elaborates all of them, which is hours of CPU [INFERRED]
and the RAM the Mac's other lanes are using. Name the module.

### Timings, Mac and hbox [MEASURED, 2026-11-06, warm `.lake`, `-j 4`]

Mac: Apple M2 Max, 12 cores, other lanes running. Two runs, 20 files (the 18 gate files plus lane A's `StratifiedCert.lean` and lane B's
`Policy/Syntax.lean`), all green: 147 guards, 302 keystones. hbox: i9-12900, `--hbox`
(inside `swarm-build`, `SWARM_MEM_MAX=12G`), clone at `39ec5e45a`: 19 files (lane B's `Policy/` was not
committed yet; Weld8 before its graduation commit), all green, 146 guards, 291 keystones. An earlier hbox
run at `c9205e769` (18 files) took 20.5 s wall.

| file | Mac secs (run 2) | Mac secs (run 3) | hbox secs | guards | keystones |
|---|---:|---:|---:|---:|---:|
| `Dregg2/Crypto/Dfa.lean` | 11.8 | 14.8 | 2.3 | 0 | 11 |
| `Dregg2/Crypto/DfaAcceptanceAir.lean` | 12.8 | 16.1 | 2.6 | 0 | 19 |
| `Dregg2/Crypto/Deriv/Core.lean` | 13.7 | 15.1 | 2.5 | 24 | 11 |
| `Dregg2/Crypto/Deriv/Correctness.lean` | 11.3 | 14.1 | 2.2 | 0 | 13 |
| `Dregg2/Crypto/Deriv/Finiteness.lean` | 15.5 | 14.7 | 2.8 | 0 | 5 |
| `Dregg2/Crypto/Deriv/Thompson.lean` | 15.3 | 15.0 | 2.8 | 0 | 9 |
| `Dregg2/Crypto/Deriv/SymbolicEquivalence.lean` | 13.6 | 12.4 | 2.3 | 2 | 7 |
| `Dregg2/Crypto/Cfg.lean` | 14.2 | 11.5 | 2.4 | 0 | 2 |
| `Dregg2/Crypto/CfgCompact.lean` | 13.8 | 14.8 | 2.2 | 0 | 6 |
| `Dregg2/Circuit/Emit/DfaRoutingTableEmit.lean` | 18.1 | 28.7 | 3.5 | 8 | 15 |
| `Dregg2/Circuit/Emit/DfaRoutingGeneralEmit.lean` | 17.9 | 27.8 | 3.6 | 12 | 3 |
| `Dregg2/Circuit/Emit/DyckStackEmit.lean` | 17.6 | 24.3 | 3.6 | 28 | 6 |
| `Dregg2/Circuit/Emit/DyckStackReplay.lean` | 13.8 | 26.7 | 3.9 | 3 | 27 |
| `Dregg2/Circuit/Emit/AttestedAutomatonWeld8.lean` | 12.8 | 29.5 | 3.7 | 10 | 32 |
| `Dregg2/Circuit/Emit/AttestedAutomatonLanes8.lean` | 12.9 | 22.5 | 3.6 | 0 | 25 |
| `Dregg2/Circuit/Emit/TinyAutomataLanesK.lean` | 12.3 | 28.5 | 3.7 | 6 | 48 |
| `Dregg2/Circuit/Emit/DerivationEmit.lean` | 12.1 | 26.1 | 3.7 | 11 | 1 |
| `Dregg2/Datalog/FixpointCert.lean` | 11.6 | 24.5 | 3.7 | 18 | 28 |
| `Dregg2/Datalog/StratifiedCert.lean` | 14.2 | 26.2 | 4.0 | 25 | 34 |
| `Dregg2/Policy/Syntax.lean` | 3.6 | 8.7 | - | 0 | 0 |
| **deps step** | 19.2 (rebuilt 4 Mathlib modules) | 5.9 (no-op) | 1.4 (no-op) | | |
| **wall, whole gate** | **91.6** | **116.2** | **17.8** | | |

Per-file seconds are dominated by loading the import closure (a lone `lake env lean` of
`SymbolicEquivalence.lean` is 17 s wall with 2 s user), so they rise with `-j` and with the other
lanes' load; the wall is what to compare. Target was under five minutes; both runs are under two.

### The Mac's mathlib [MEASURED, 2026-11-06]

`metatheory/.lake/packages/mathlib` is a symlink to `~/src/mathlib4`, itself a symlink to
`~/dev/breadstuffs-codex/metatheory/.lake/packages/mathlib` (rev `1c2b90b1`). Of its 8,776 oleans,
**5,969 carry a Lean 4.35.0 header** (written 2026-10-30 08:15-08:18) and 2,807 carry 4.30.0. The
toolchain here is v4.30.0, so any family file whose Mathlib closure touches a 4.35 olean fails with
`incompatible header`; today that was `Deriv/Thompson.lean` (four stale modules in its closure:
`Mathlib.Computability.{NFA,DFA,EpsilonNFA}`, `Mathlib.Data.List.ReduceOption`). The gate's deps
step rebuilt those four at 4.30 in 19 s, which is lake's normal behaviour for a 4.30 workspace.
The other 5,965 are untouched; a new family file importing more of Mathlib will pay for its own
stale modules the same way. Re-fetching the whole cache is the clean fix, but the directory is
shared with `breadstuffs-codex`, so that is ember's call, not a lane's.

## On hbox

The clone is `~/lanes/automata/bs` (from `git@github.com:emberian/dregg.git`, `--filter=blob:none`;
hbox's default GitHub key reads it). Everything runs under `swarm-build`:

```
ssh hbox
cd ~/lanes/automata/bs && git pull --ff-only
cd metatheory
scripts/automata-check.sh --hbox          # re-executes itself inside swarm-build, SWARM_MEM_MAX=12G default
SWARM_MEM_MAX=12G swarm-build lake build Dregg2.Datalog.FixpointCert   # one module, contained
```

`--hbox` drops itself from the argument list and re-executes the script as
`SWARM_MEM_MAX=${SWARM_MEM_MAX:-12G} swarm-build <script> <args>`; `SWARM_BUILD_INNER` (set by
`swarm-build`) stops a second re-exec. The deps step therefore also runs inside the cgroup.

hbox is about 6x faster per file than the Mac under today's load; the whole gate is under 20 s there.

## What `.lake` must contain

- `.lake/packages/` at the revisions in `metatheory/lake-manifest.json`: mathlib `1c2b90b1`, plus
  batteries, aesop, Qq, proofwidgets, plausible, importGraph, LeanSearchClient, Cli.
- Mathlib oleans for toolchain `leanprover/lean4:v4.30.0` (`metatheory/lean-toolchain`). An olean's
  first 16 bytes name the Lean version that wrote it (`olean..4.30.0`); a mismatch is the
  `incompatible header` error above.
- `.lake/build/lib/lean/Dregg2/**` for the family closure. `.lake` is per-machine and gitignored;
  never copy or hard-link one tree's `.lake` into another (`~/swarm/RULES.md`).

## Warming a fresh checkout

```
git clone --filter=blob:none git@github.com:emberian/dregg.git bs
cd bs/metatheory
lake exe cache get                    # Mathlib oleans for the pinned rev (hbox: under swarm-build)
lake build Dregg2.Datalog.FixpointCert Dregg2.Crypto.Dfa \
  Dregg2.Circuit.Emit.AttestedAutomatonLanes8 Dregg2.Circuit.Emit.DyckStackReplay \
  Dregg2.Crypto.Deriv.SymbolicEquivalence      # the family closure, NOT a bare lake build
scripts/automata-check.sh             # its deps step builds whatever else the family imports
```

On hbox [MEASURED, 2026-11-06, `SWARM_MEM_MAX=12G` for both steps]:

| stage | finished (UTC) | `/` free after |
|---|---|---:|
| start | 17:27:53 | 46 GB |
| clone (`c9205e769`) | 17:28:23 | 45 GB |
| `lake exe cache get` | 17:29:43 | 38 GB |
| closure build (3,113 jobs) | 17:32:13 | 37 GB |

About 9 GB in all: 7.5 GB of packages, 0.3 GB of Dregg2 build output, 0.9 GB of checkout (`du`, ZFS).

<!-- ===== Emit and stamp (C2) — appended by lane C2, 2026-11-06; edit only this section ===== -->
## Emit and stamp (C2)

**Current host and ownership (2026-11-06, Codex deputy).** New builds run on bb2 in the
builder's own clone, under `swarm-build`; `/tank` on hbox receives no new data. The predecessor's
`/home/build/automata/bs` is occupied by the detached stamp chain (`chain.pid` and `chain.log`
in its parent directory). Read its results; do not start another build there. The successor's
integration clone is `/home/build/astra-integration`. Keep at least 40 GiB beyond summed
process RSS, accounting for the unused memory allowance of already running capped jobs before
starting another. The gate is `metatheory/scripts/automata-check.sh`; this document is
`docs/automata/BUILD.md` (the build guide lives under the automata documentation).

`scripts/emit_descriptors.py` has no acknowledgement step (SUBSTRATE-DECISION §9 row 4, as amended
by codex round 3). It refuses (exit 3) when any file in the emitters' transitive Lean closure or
the lake configuration is uncommitted, and with `--rev <sha>` it also refuses unless the checkout
IS that commit. Otherwise it builds the emitter modules, emits, installs, and writes
`circuit/descriptors/PROVENANCE.json` (tree hash, repo HEAD, toolchain, emitter list,
`emitter_closure_clean`, per-file sha256) with no environment variable and no operator.

The canonical emission input is a clean clone at a committed revision with its own `.lake`.
Do not run the full emit on the Mac. The shared working tree is never
clean, and on 2026-11-06 about 91 emitter-closure modules were out of date in the Mac's `.lake`.

```
ssh bb2
cd /home/build/astra-integration
# Prepare this dedicated clone at the intended committed revision before launching.
# Never switch, reset, stash or rebase the shared Mac checkout.
test -z "$(git status --porcelain)" || { echo "clone not clean"; exit 1; }
REV=$(git rev-parse HEAD)
nohup env SWARM_MEM_MAX=12G swarm-build python3 scripts/emit_descriptors.py --rev "$REV" \
  > ../astra-integration-emit.log 2>&1 &
echo $! > ../astra-integration-emit.pid # stop your own job only by this PID
# when it exits:
tail -5 ../astra-integration-emit.log   # NO-OP / STAMP-ONLY REGEN / REGEN line
git status --porcelain                   # expected: only circuit/descriptors/PROVENANCE.json
```

If `git status` lists any other file (a descriptor, a `*_FP` source, a `*_generated.rs`), the
checked-in artifacts were stale relative to Lean at `$REV`. That is drift: report it with the
log, and do not commit only the stamp. If only the stamp moved, copy that named artifact back to
the shared Mac checkout, inspect its diff, verify it against the current committed emitter
closure, and commit only that file on `main`. No branch or rebase is part of this procedure:

```
python3 scripts/emit_descriptors.py --verify-provenance --rev HEAD   # must PASS before push
git add circuit/descriptors/PROVENANCE.json
git -c commit.gpgsign=false commit -F /path/to/prepared-message -- circuit/descriptors/PROVENANCE.json
git push origin main
```

The verification is required: a stamp from the predecessor's older revision does not certify
subsequent emitter changes. Sequence the final emission after the Mina rescue and automata
shape changes have landed. If emission changes descriptors as well, review and land that full
generated delta with its source; a stamp-only commit would hide drift.
<!-- ===== end Emit and stamp (C2) ===== -->

### hbox memory for the emitter closure (deputy, 2026-11-06, [MEASURED])

The automatic stamp needs every emitter's Lean closure built. Under `swarm-build` at `SWARM_MEM_MAX=12G`
the default `lake build` parallelism was OOM-killed three times (`run-u75145`, `u75156`, `u75280`), and
building the modules ONE AT A TIME at 12G still died on single Mina modules: `lake` has no `--jobs`
option in this toolchain (Lake 5.0.0 / Lean 4.30.0), and one `lean` process compiling
`Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir` reaches a **peak RSS of 24.7 GB** (sampled every 5 s; built
in 5 min 8 s at a one-time `SWARM_MEM_MAX=32G`, granted by the root with the box checked first: summed
process RSS, not `free`, and no tenant peaking). `Dregg2.Circuit.Emit.MinaWrapCommitStages` also exceeds 12G
(killed at 12G, `run-u79764`; its peak is not yet measured). Everything else in the 174-module emitter
closure builds under 12G. The clone lives at `/tank/dregg-build/automata/bs` (ZFS, 4.4 GB; a no-op
`lake build` of the automata closure replays 3,034 jobs in 4 s after the move from `/home`).
