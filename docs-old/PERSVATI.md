# Persvati — remote build offload

`persvati.local` is a Linux box (x86_64 Ubuntu, Ryzen, 83 GB RAM, 1.9 TB
disk, nightly Rust 1.96.0) on the LAN. It exists so workspace-wide cargo
verification doesn't fight local `target/` locks when many agents are in
flight.

## Setup (already done — for reference)

**SSH config** (~/.ssh/config, may be a symlink into Mackup):

```
Host persvati persvati.local
    User ember
    Hostname persvati.local
    IdentityFile ~/.ssh/id_aws
```

**Persvati side** — `/home/ember/dev/breadstuffs` is a non-bare git
repo with `receive.denyCurrentBranch = updateInstead`, so pushing to
`main` updates the working tree atomically.

**Local side** — git remote `persvati` points at
`persvati:dev/breadstuffs`.

## Usage idioms

### Verify a commit workspace-wide

```bash
git push persvati main
ssh persvati 'cd ~/dev/breadstuffs && cargo check --workspace 2>&1 | tail -50'
```

### Run a specific crate's tests remotely

```bash
git push persvati main
ssh persvati 'cd ~/dev/breadstuffs && cargo test -p dregg-cell --lib 2>&1 | tail -30'
```

### Smoke test before running full workspace

```bash
ssh persvati 'cd ~/dev/breadstuffs && cargo check -p dregg-types --quiet'
```

## Discipline for agents

When you need workspace-wide cargo verification:

1. **Commit locally** (`git -c commit.gpgsign=false commit`)
2. **Push to persvati**: `git push persvati main` (or your branch)
3. **Run build remotely**: `ssh persvati 'cd ~/dev/breadstuffs && cargo check --workspace 2>&1 | tail -50'`
4. **Iterate locally** based on remote output

This avoids:
- Local `target/` lock contention from 60+ parallel agents
- Local CPU saturation from concurrent rustc invocations
- Slow rebuilds when one agent's edits invalidate another's `target/`

### When *not* to use persvati

- **Single-crate `cargo check -p X`** locally is faster than a round-trip
- **`cargo run`** locally for development iteration
- **Edit-compile-test loops** on one crate

Use persvati for the *workspace-wide verification* step.

## Pushing branches

If you're on a non-`main` branch, push it specifically:

```bash
git push persvati feature/foo
ssh persvati 'cd ~/dev/breadstuffs && git checkout feature/foo && cargo check --workspace'
```

(Persvati's `updateInstead` is configured for `main`; non-main branches
need an explicit checkout on the remote side.)

## Troubleshooting

**Permission denied on ssh** — check `~/.ssh/config` has the `IdentityFile
~/.ssh/id_aws` line (the iCloud-mirrored config may not have been synced).

**Push rejected** — if you're not on `main` locally, push your branch
explicitly: `git push persvati <branch>`.

**Stale build cache** — `ssh persvati 'cd ~/dev/breadstuffs && cargo
clean'` and rebuild.

**Resource saturation on persvati** — `ssh persvati 'htop'` to inspect;
persvati has 83 GB RAM so usually fine, but parallel `cargo build`s can
spike.

## History

Set up 2026-05-24 after the 5-hour session limit reset, in response to
local cargo contention from many parallel agents.
