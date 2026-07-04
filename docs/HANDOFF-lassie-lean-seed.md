# HANDOFF — cut the HEAD-matching Lean seed on lassie

**For:** opus-driver, running the cold bootstrap on **lassie** (dual-EPYC, 128
threads). ember hands this recipe; there is no cross-team access, so everything
below runs entirely on lassie from a fresh-ish `breadstuffs` checkout at the
target commit.

**Why this exists:** `dregg-lean-ffi/libdregg_lean.a` is a ~180 MB native static
archive of the compiled verified executor + its entire mathlib/batteries/aesop/Qq
closure (~6000 objects). It is gitignored (a per-arch Mach-O/ELF blob — never a
repo blob). A fresh clone that builds without it silently degrades to
**marshal-only** (the un-verified Rust executor). Rebuilding it from source is an
hours-long cold `lake` bootstrap that compiles mathlib. Publishing a HEAD-matching
seed as a GitHub release asset turns that into a **minutes-long download** for
everyone else (`scripts/fetch-lean-seed.sh`). Background:
`docs/LEAN-SEED-ARTIFACT.md`.

---

## The key shape (grounded at `HEAD = 29ab74bc1`)

A seed is valid only for a specific **platform · lean-toolchain · mathlib-rev ·
Dregg2-tree-hash**. `scripts/lean-seed-key.sh` hashes exactly those four into a
short key and names the asset:

```
libdregg_lean-<os>-<arch>-<lean-tag>-<key>.a.zst
```

**Platform-independent provenance at HEAD** (identical on lassie):

```
LEAN_TOOLCHAIN  = leanprover/lean4:v4.30.0          (metatheory/lean-toolchain)
MATHLIB_REV     = 1c2b90b13009c65b090d95a83c98e248deafb6f1
DREGG_TREE_HASH = 3eb066d27dd64d2759204bc9b00090740324c3ac   (git HEAD:metatheory/Dregg2)
```

**Platform-dependent (lassie is Linux/x86_64, so it differs from ember's macOS
box):** the `<os>-<arch>`, the final 16-hex `<key>`, and thus the asset name are
computed **on lassie** — do not copy ember's macOS key. On lassie:

```bash
scripts/lean-seed-key.sh            # prints KEY / PLATFORM / provenance / ASSET
scripts/lean-seed-key.sh --asset    # e.g. libdregg_lean-Linux-x86_64-v4.30.0-<key>.a.zst
```

> For reference, ember's macOS run computed
> `KEY=848f1265c98f9030`,
> `ASSET=libdregg_lean-Darwin-arm64-v4.30.0-848f1265c98f9030.a.zst`.
> lassie's `<key>` will differ (different platform string in the hash) — that is
> correct and expected. Same provenance triple ⇒ the seeds are interchangeable
> *within a platform*.

---

## The recipe (copy-paste on lassie, at the target commit)

```bash
# 0. be at HEAD (or the exact commit ember names) on lassie:
git rev-parse HEAD          # expect 29ab74bc1… (or the handed commit)
scripts/lean-seed-key.sh    # sanity: MATHLIB_REV + DREGG_TREE_HASH match the values above

# 1. (re)seed a HEAD-matching libdregg_lean.a — the hours-long cold bootstrap
#    (128 threads help here; compiles mathlib once into a warm .lake):
./scripts/bootstrap.sh

# 2. compress with the canonical settings (~180 MB → ~20 MB, ≈8.6×):
asset="$(scripts/lean-seed-key.sh --asset)"
zstd -q -19 --long=27 -T0 dregg-lean-ffi/libdregg_lean.a -o "$asset"
sha256sum "$asset" > "$asset.sha256"

# 3. publish the asset + checksum sidecar to a dated release:
tag="lean-seed-$(date +%Y-%m-%d)"
gh release create "$tag" --title "Lean seed $(date +%Y-%m-%d)" \
   --notes "seed for $(git rev-parse --short HEAD)" || true
gh release upload  "$tag" "$asset" "$asset.sha256" --clobber
```

### 4. Bump the committed pin

Rewrite `dregg-lean-ffi/lean-seed.pin` so `fetch-lean-seed.sh` serves it:

```
TAG=lean-seed-YYYY-MM-DD
LEAN_TOOLCHAIN=leanprover/lean4:v4.30.0
MATHLIB_REV=1c2b90b13009c65b090d95a83c98e248deafb6f1
DREGG_TREE_HASH=3eb066d27dd64d2759204bc9b00090740324c3ac
GENERATED_UTC=<date -u +%Y-%m-%dT%H:%M:%SZ>
NOTE=published on lassie for <commit>
```

Then commit + push the pin. From that point, on any matching platform:

```bash
./scripts/fetch-lean-seed.sh                                   # minutes, not hours
DREGG_REQUIRE_LEAN=1 cargo build -p dregg-node --release       # fails loud, never silent-degrades
```

The preferred alternative to the by-hand path is the workflow
(`Actions → Publish Lean seed → Run workflow`, self-hosted `runner` label) —
`.github/workflows/lean-seed.yml` runs steps 1-4 and commits the pin bump. Run it
**once per platform** you want to serve (each self-hosted host contributes its own
native asset to the same tag).

---

## Grounded caveats

- **Current pin is unpublished + stale.** `dregg-lean-ffi/lean-seed.pin` has
  `TAG=` (empty) and `DREGG_TREE_HASH=b5c88ddd…`, which predates HEAD's
  `3eb066d2…`. No seed release has ever been cut — this recipe cuts the first.
  Until then, `fetch-lean-seed.sh` fails loud and the only verified path is a
  local `./scripts/bootstrap.sh`.
- **mathlib pin is an absolute local path.** `metatheory/lakefile.toml` pins
  mathlib as `/Users/ember/src/mathlib4`. lassie must have the mathlib checkout at
  that path (or a `DREGG_METATHEORY_DIR`/symlink workaround) for the bootstrap to
  resolve. This is a known rough edge; making it relative is tracked separately.
- **The seed is a build accelerator, not a trust root.** Its guarantee is the
  Lean proofs compiled in; the same source rebuilds it deterministically.
  `fetch-lean-seed.sh` refuses any archive whose sha256 mismatches the published
  sidecar or that lacks the `dregg_exec_full_forest_auth` export.
- lassie is Linux → it serves the `Linux-x86_64` asset. ember's macOS box needs a
  `Darwin-arm64` asset cut separately (same tag, its own native run).
