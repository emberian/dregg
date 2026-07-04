# HANDOFF — v13-geom VK epoch: the human-go package

**Grounded at** `HEAD = 29ab74bc1` (v13-complete tip). Every command below is
**local-prep only**. Nothing here pushes, deploys, or wipes a key. The three
ember-decision items are each reduced to *one command* or *one read*. This doc
orients; the two sibling docs carry the detail:

- `docs/HANDOFF-lassie-lean-seed.md` — the seed recipe opus-driver runs on lassie.
- `docs/HANDOFF-committee-restart-fix.md` — the N3 committee-restart A/B decision.

---

## 1. The origin push + re-genesis

### 1a. Push state (ground truth)

```
origin/main tip   746435722  docs(weld): BANG WAVE 1 stop-condition …
HEAD              29ab74bc1  fix(node/consensus): diagnose N3 committee-restart hole …
HEAD is ahead of origin/main by 91 commits
origin/main is a STRICT ANCESTOR of HEAD  →  a clean fast-forward
```

- **No collaborator reconcile is needed.** Keemin Lee's contributions (PRs
  #24/#25/#26, merges `5fcf1590b` / `e5f29a983` / `c6601e5f6`) are already merged
  into `origin/main` and therefore already in HEAD's history. There are **no
  unmerged keeminlee remote branches** and **no divergence** — the last 30 commits
  are all `ember arlynx`.
- The working tree has uncommitted, **unrelated** edits (`Cargo.lock`,
  `deos-hermes/{Cargo.toml,src/brain.rs,src/main.rs}`). These are **not** part of
  the v13 handoff — leave them, or stage them separately. The docs commit below
  touches only `docs/`.

### 1b. The exact push sequence

Because origin/main is a strict ancestor, this is a plain fast-forward — **no
branch, no PR, no force**:

```bash
git push origin main
```

Optional mirrors (each is its own fast-forward-or-not; check before pushing):

```bash
git push hbox main        # hbox tip is 42daaded9 (v12-era) — will fast-forward
git push persvati main    # persvati/main is 13f65ae5a — verify ancestry first
```

> `origin` = `git@github.com:emberian/dregg.git`. The `devnetbox` remote
> (`ubuntu@34.224.208.52:/opt/dregg`) is the live AWS box — **do not** push to it;
> the box pulls from origin via `deploy/aws/update.sh`.

### 1c. What the push carries to light clients (the "VK distribute" step, grounded)

The v12→v13-geom epoch **regenerated the circuit descriptors** — the
Lean-authoritative light-client verification artifacts in
`circuit/descriptors/*.json` (regen path: `scripts/emit-descriptors.sh` →
`scripts/emit_descriptors.py`). Commits touching them since origin include
`a6e78ee27` (STEP 4 REGEN, N=169/227) and `be732a9dd`. **These descriptors are
committed in-repo**, so "distributing the new VK to light clients" is simply the
`git push origin main` above plus a client rebuild against HEAD — it is **not** a
genesis step and is **not** carried in `genesis.json`.

> Precise note on `genesis.json` and VKs: the genesis file carries only per-app
> **factory** VKs (`starbridge_cells[].factory_vk_hex` — name / issuer /
> subscription / governance, deterministic constants baked in
> `node/src/genesis.rs:365-383`). It does **not** carry the circuit
> recursion/light-client VK. Re-genesis (below) changes neither.

### 1d. AWS devnet re-genesis — what it does, precisely

There are **two** genesis paths; they are different and must not be confused:

| Path | Script | Where it writes | Used for |
|------|--------|-----------------|----------|
| **Repo/local** | `deploy/genesis/generate.sh` | into `deploy/genesis/` (repo tree) | producing the checked-in devnet artifact |
| **On-instance** | `deploy/aws/federation-keygen.sh` | into `/etc/dregg/federation/` + each data dir | the live N3 federation (keys never leave the box) |

The N3 live federation uses the **on-instance** path
(`deploy/aws/N3-RUNBOOK.md` §3). The repo path is what `deploy/genesis/README.md`
documents.

**`./deploy/genesis/generate.sh --force` (repo path) — DESTROYS then regenerates:**

Wipes (`generate.sh:41-42`): `genesis.json`, `.devnet`, `node-*.key`,
`node-*.env`, and the `keys/` + `secrets/` dirs. Then runs
`cargo run --release -p dregg-node -- genesis --validators 3 --epoch-length 100
--checkpoint-interval 10 --output deploy/genesis` — minting **fresh** Ed25519
validator keys, faucet/agent keys, and a **new `federation_id`**.

**⚠ The chain resets.** `federation_id = derive_federation_id_with_epoch(sorted
committee pubkeys, epoch)` (`node/src/operator_join.rs:167`,
`dregg_federation::derive_federation_id_with_epoch`) is a **commitment to the
committee pubkeys**. New keys ⇒ new `federation_id` ⇒ a fresh chain: prior
explorer history does not carry forward (the old data dir is archived, not
deleted — `N3-RUNBOOK.md` §2). Anything pinning `FEDERATION_ID` (e.g. the Discord
bot env, `N3-RUNBOOK.md` §7) must be re-pointed.

**Do NOT run `generate.sh --force` from this handoff** — it wipes keys. It is
ember's eyes-open call. The dry-run below previews it without touching a live key.

### 1e. The genesis dry-run preview (done — no live key touched)

Generated into a throwaway scratch dir with the debug binary
(`target/debug/dregg-node`, no `--release` build needed), `--output` pointed away
from the repo, so **no live key was written or wiped**:

```bash
target/debug/dregg-node genesis --validators 3 --epoch-length 100 \
  --checkpoint-interval 10 --output /tmp/scratch/gen-a
```

Result of two independent runs:

```
run A  Federation ID: 0bf14b90c32aba678765d7d55f58442b7626fe85f82a378443236353de1d8f87
run B  Federation ID: 81348de64212e1c2b1748b0af8253fa8ce33b8478ba7c8067801d81237c3de17
```

**Key finding: the `federation_id` is NON-deterministic across regenerations.**
Each `--force` mints a *fresh random committee*, and `federation_id` commits to
those pubkeys — so there is **no single "new federation_id" to preview**; every
regen yields a different one. (The per-app `factory_vk_hex` values, by contrast,
are deterministic circuit-derived constants and are unchanged.) The committed
`deploy/genesis/genesis.json` currently reads `federation_id
a17b9247…`/`threshold 2`; a fresh `--validators 3` regen produces `threshold 3`
(the supermajority of 3 — `blocklace/src/ordering.rs:236`,
`⌊2n/3⌋+1`). Ember should expect a brand-new `federation_id` on every regen and
re-pin all consumers accordingly.

---

## 2. The lassie Lean-seed recipe

→ **`docs/HANDOFF-lassie-lean-seed.md`.** Grounded HEAD provenance opus-driver
copy-pastes on lassie:

```
LEAN_TOOLCHAIN = leanprover/lean4:v4.30.0
MATHLIB_REV    = 1c2b90b13009c65b090d95a83c98e248deafb6f1
DREGG_TREE_HASH = 3eb066d27dd64d2759204bc9b00090740324c3ac   (git HEAD:metatheory/Dregg2)
```

⚠ The committed pin (`dregg-lean-ffi/lean-seed.pin`) is **stale + unpublished**:
`TAG=` (empty) and `DREGG_TREE_HASH=b5c88ddd…` (predates HEAD's `3eb066d2…`). A
seed release has never been cut. That is exactly the job handed to opus-driver.

---

## 3. The committee-restart A/B decision

→ **`docs/HANDOFF-committee-restart-fix.md`.** The N3 run caught full-mode
committee nodes fail-closing on restart (diagnosed at `29ab74bc1`, pinned by
`dregg_persist::tests::full_mode_single_sig_root_is_refused_genuine_quorum_accepted`).
Two sound fixes are laid out with exact files, wire-format deltas, and the
async-window liveness tradeoff. **Recommendation: Fix B** (extend
`FinalizationVote` — smaller blast radius, rides the existing proven vote
machinery). See the doc for the reasoning and the one shared prerequisite.

---

## The single docs-commit (the only write this handoff makes)

```bash
git add docs/HANDOFF-v13-VK-EPOCH.md \
        docs/HANDOFF-lassie-lean-seed.md \
        docs/HANDOFF-committee-restart-fix.md
git commit -m "docs(handoff): v13 VK-epoch human-go package — push/re-genesis, lassie seed recipe, committee-restart A/B"
```

Then, at ember's discretion and in this order: **(3)** pick A or B and land it →
**(1b)** `git push origin main` → **(2)** hand the seed recipe to opus-driver →
**(1d)** run the on-instance re-genesis eyes-open.
