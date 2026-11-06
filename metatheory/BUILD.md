# Building and checking metatheory: the lane loop

How a lane edits one Lean file, checks it, runs its guards and lands, without rebuilding what another
machine already built and without fighting other lanes over a shared tree. Measured 2026-11-06; the
numbers and the reasoning behind each rule are in redregg-notes
`landscape/ITERATION-SPEED-2026-11-06.md`.

## Rule 1: never run `lake` in a shared tree

`/Users/ember/dev/breadstuffs/metatheory` (and `/Users/ember/dev/minidregg`) are shared by every lane on
the Mac. Any `lake` command there (`lake build`, `lake env lean`, `lake lean`, `lake update`) may check
out the manifest's package revisions. As of 2026-11-06 the Mac minidregg tree's `.lake/packages` are symlinks
into breadstuffs' packages (the switch to the keyed directories below waits on ember), so a minidregg `lake` run checks breadstuffs' Mathlib (v4.30) out to
minidregg's rev (v4.35), and the next breadstuffs run checks it back. The reflogs show this on
10-30 (5,964 v4.35 oleans unpacked into the v4.30 Mathlib), 11-05 and 11-06. While that goes on,
every single-file check in either tree is unreliable.

A lane works in its own clone or worktree and links it to the read-only packages directory for its
manifest:

    git clone --filter=blob:none --sparse git@github.com:emberian/dregg.git <your-dir>/bs
    git -C <your-dir>/bs sparse-checkout set metatheory scripts
    ~/tools/lean-packages/lean-packages ensure <your-dir>/bs/metatheory   # once per manifest, ~2.5 min
    ~/tools/lean-packages/lean-packages link   <your-dir>/bs/metatheory --mine

The packages directory is `~/tools/lean-packages/<key>`, where key =
`cat lake-manifest.json lean-toolchain | sha256sum | cut -c1-12`. metatheory today is 856c40722ebb
(v4.30.0, Mathlib 1c2b90b1); the boxes use the same key scheme for minidregg's pool. The directory is
read-only, so a `lake` run with the wrong manifest fails with "Permission denied" instead of moving
the checkout. A manifest bump needs a new key: run `ensure` and then `link`. Never edit a packages
directory in place.

On the build boxes the same rule holds: a lane builds in its own pool tree
(`lane-tree acquire`) or its own clone under its own directory.

## Rule 2: start warm. Fetch oleans, do not rebuild them

A fresh clone has no oleans for metatheory's ~2,700 modules. A cold build of the default
targets is over an hour on bb2. Instead, fetch the snapshot of the nearest ancestor commit that a build box
published:

    scripts/iter-check fetch            # from bb2 (--box hbox for hbox's store)

Lake's traces are content hashes, not paths, so a `.lake/build/lib` copied from another clone at
the same commit is up to date. Tested 2026-11-06: hbox published the closure of
`Dregg2.Crypto.HierarchicalGraphCommitment` at a0a8cd4c6 (324 MB) and the Mac fetched it. After
that, `lake build --no-build` on the Mac reported "All targets up-to-date (3006 jobs)". The
generated C under `.lake/build/ir` has to travel with the oleans: a module's trace lists its `.c`
as an output, and without it Lake rebuilds the module. Modules your
branch changed, and their dependents, still rebuild as usual. Boxes publish with
`scripts/iter-check publish` in a tree that is green at HEAD. A snapshot is
`~/olean-store/metatheory/<commit>/{lib,ir}`: read-only, hard-linked against the previous snapshot,
never linked into a live tree (a Lean `.lake` must never share inodes with another tree).

## Rule 3: concrete data by the compiler, general theorems by the kernel

Ember, 2026-11-06: "we DO trust the lean system ... later on when assurance is more important
than iteration time, THEN someone can go ahead and rerun the entire proof process on a verified
lean kernel; this present hybrid is the worst of both tradeoffs." So:

- **Facts about concrete data** are checked by compiled evaluation: hashes, codec outputs on a
  sample, big tables, demo states, test vectors. That means `#guard`, a `lean_exe`, or
  `native_decide` when a downstream theorem needs the fact as a proof.
- **Concrete data is never checked by the kernel.** No `decide`, `decide +kernel` or `rfl`
  through an encoder, a hash or a long table: that made the kernel evaluate cSHAKE (16.5 GB,
  81 s in minidregg's Kernel.ObjectLaw) or unfold a codec (13 GB).
- **General theorems** (quantified statements) stay kernel-proved.

In this toolchain a `native_decide` does not rest on `Lean.ofReduceBool`. Each use mints its own
axiom, named exactly

    <theorem>._native.native_decide.ax_1_1

(`Lean.Meta.nativeEqTrue`: its type is `<closed Bool expr> = true`), and every theorem that uses
the fact inherits that axiom. The pin rules:

- A theorem proved by `native_decide`, or resting on one, is pinned with `#assert_compiled <theorem>`
  (`Dregg2/Tactics.lean`). It re-runs the claim and refuses any other axiom. Never pin it with
  `#assert_axioms`, which refuses compiler trust by design.
- A `#guard_msgs in #print axioms <theorem>` pin names the `_native` axiom in its expected
  message. Update it in the same commit that changes the axiom.
- Any `#guard_msgs` over `#assert_axioms_tree`'s "N rest on the compiler trust" count is updated
  in the same commit when the count changes.
- breadstuffs' `orb/Hygiene.lean` admits the axiom only when the theorem's pin lists the
  `nativeDecide` set.

When several facts share an expensive input (a large literal
or jam), prove their conjunction with ONE `native_decide` and take each
named fact as a projection. The input is then evaluated once, and every fact pins the one shared
`<conjunction>._native.native_decide.ax_1_1`.

## The loop

    make check-fast                   # here (the Mac): each changed .lean file
    make check-full                   # on the least-loaded box: changed modules + every module importing them
    make check-umbrella               # the lakefile's defaultTargets, bb2 only
    make boxes                        # what check-full would choose, and why

`FILES="Kernel/Job.lean"` restricts either check. All of them drive `scripts/iter-check` (python3,
no dependencies).

- **check-fast** finds the changed `.lean` files: the diff against the merge base with
  `origin/main` plus untracked files. It runs `lake build --no-build` over their in-tree imports. If
  the imports are stale and the stale set is small (40 jobs; `ITER_FAST_MAX_STALE`), it builds them
  here; otherwise it stops and tells you to use check-full. It then runs `lake lean FILE` per file,
  so the file's `#guard`, `#guard_msgs` and `#assert_axioms` lines run, and times each file.
  It uses `lake lean`, not `lake env lean`: only `lake lean` passes the lakefile's options, so
  it checks exactly what `lake build` checks. `scripts/automata-check.sh` is still the automata
  family's gate.
- **check-full** rsyncs the tracked and untracked-not-ignored files to a persistent clone on the
  chosen box. It then builds the changed modules and every in-tree module that imports them.
  Per-file green hides a red umbrella, so the reverse dependents are part of the check. The build
  runs detached under the box's memory containment with a PID file, and the log comes back to
  `.iter-check/<run>/build.log`. `scripts/iter-check status|wait|log|stop [RUN]` manage a run;
  `stop` kills only the PID in that run's PID file, after re-reading its command line.

## Which box (policy of 2026-11-06)

check-full scores every box that answers as `load1/ncpu + used_rss/total_ram` and takes the lowest.
A box is skipped when it:

- has less free memory than the job's cap plus headroom (40 GB on bb2 and hbox, 4 GB on forge,
  which is a 32 GB machine);
- is in a pause window (forge: 10:00-11:00 UTC, fn2's nightly);
- already holds a live run of this lane (one `lake` per lane per box).

| box | job | cap | LEAN_NUM_THREADS | containment | clone |
|---|---|---|---|---|---|
| bb2 (`ssh bb2`) | umbrella, 32G jobs, medium | 32G | 8 | `swarm-build` | `/home/build/iter-check/<repo>-<lane>` |
| hbox (`ssh hbox`) | medium (12G, < ~10 min) | 12G | 6 | `swarm-build` | `/home/hbox/iter-check/...` (nvme root, never `/tank`) |
| dregg-forge | medium | 12G | 6 | `systemd-run --scope -p MemoryMax=12G nice -n 15` | `/srv/lanes/iter-check/...` (own elan) |

Umbrella builds and 32G jobs go to bb2 only. Never touch forge's `demo`, `nano` or `composed`
containers, fn2's `/build`, or its certify lock.

**On bb2, `flock` on the `build` user's PATH is not util-linux.** `/home/build/.elan/bin/flock` is an
obend shim. It ignores the lock for most commands and wraps `lake env lean` in `timeout 60s`. Scripts
that need a real lock there call `/usr/bin/flock` by absolute path.

## Memory: what a module costs

Peak RSS per module, from a cold bb2 build of 274f65a80 (2,115 of the default targets' modules
measured; the build was stopped there): 88 modules over 4 GiB, 4 over 12 GiB. The automata
deputy measured the Mina emitters at up to 25.9 GB, and the Mina lane brought
MinaBodyPreimageBitsAir down to 5.6 GB by replacing a large `decide` with a direct proof. The
patterns to look for, and the table, are in the notes.
