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

### Mac timings [MEASURED, Apple M2 Max, 12 cores, warm `.lake`, other lanes running]

Two runs at `-j 4`, 20 files (the 18 gate files plus lane A's `StratifiedCert.lean` and lane B's
`Policy/Syntax.lean`), all green: 147 guards, 302 keystones.

| file | secs (run 2) | secs (run 3) | guards | keystones |
|---|---:|---:|---:|---:|
| `Dregg2/Crypto/Dfa.lean` | 11.8 | 14.8 | 0 | 11 |
| `Dregg2/Crypto/DfaAcceptanceAir.lean` | 12.8 | 16.1 | 0 | 19 |
| `Dregg2/Crypto/Deriv/Core.lean` | 13.7 | 15.1 | 24 | 11 |
| `Dregg2/Crypto/Deriv/Correctness.lean` | 11.3 | 14.1 | 0 | 13 |
| `Dregg2/Crypto/Deriv/Finiteness.lean` | 15.5 | 14.7 | 0 | 5 |
| `Dregg2/Crypto/Deriv/Thompson.lean` | 15.3 | 15.0 | 0 | 9 |
| `Dregg2/Crypto/Deriv/SymbolicEquivalence.lean` | 13.6 | 12.4 | 2 | 7 |
| `Dregg2/Crypto/Cfg.lean` | 14.2 | 11.5 | 0 | 2 |
| `Dregg2/Crypto/CfgCompact.lean` | 13.8 | 14.8 | 0 | 6 |
| `Dregg2/Circuit/Emit/DfaRoutingTableEmit.lean` | 18.1 | 28.7 | 8 | 15 |
| `Dregg2/Circuit/Emit/DfaRoutingGeneralEmit.lean` | 17.9 | 27.8 | 12 | 3 |
| `Dregg2/Circuit/Emit/DyckStackEmit.lean` | 17.6 | 24.3 | 28 | 6 |
| `Dregg2/Circuit/Emit/DyckStackReplay.lean` | 13.8 | 26.7 | 3 | 27 |
| `Dregg2/Circuit/Emit/AttestedAutomatonWeld8.lean` | 12.8 | 29.5 | 10 | 32 |
| `Dregg2/Circuit/Emit/AttestedAutomatonLanes8.lean` | 12.9 | 22.5 | 0 | 25 |
| `Dregg2/Circuit/Emit/TinyAutomataLanesK.lean` | 12.3 | 28.5 | 6 | 48 |
| `Dregg2/Circuit/Emit/DerivationEmit.lean` | 12.1 | 26.1 | 11 | 1 |
| `Dregg2/Datalog/FixpointCert.lean` | 11.6 | 24.5 | 18 | 28 |
| `Dregg2/Datalog/StratifiedCert.lean` | 14.2 | 26.2 | 25 | 34 |
| `Dregg2/Policy/Syntax.lean` | 3.6 | 8.7 | 0 | 0 |
| **deps step** | 19.2 (rebuilt 4 Mathlib modules) | 5.9 (no-op) | | |
| **wall, whole gate** | **91.6** | **116.2** | | |

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

### hbox timings

(filled in when the hbox run lands; see below)

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
