# pack-deos — package the current checkout, on whatever host you're on

`scripts/pack-deos.sh` is the local, no-CI-required codification of the two
packaging recipes in `.github/workflows/starbridge-v2-installers.yml`. It
detects the host OS and produces the same artifacts the workflow would, from
binaries **you already built** — it never invokes cargo (a missing binary fails
fast with the exact `cargo build` command to run).

```
scripts/pack-deos.sh                # package for the host OS → starbridge-v2/dist/
scripts/pack-deos.sh --dry-run      # print the resolved plan, touch nothing
scripts/pack-deos.sh --no-selfcheck # skip the `--headless` boot gate
scripts/pack-deos.sh --with-vessel  # (mac) bundle the self-describing vessel too
scripts/pack-deos.sh --with-node    # (mac) bundle dregg-node too
```

## Why it exists

The installers workflow's Linux leg was first proven **by hand** on hbox
(2026-07-03 ~05:14, DEOS-NIGHT-SHIFT.md "FIRST LINUX AppImage EVER BUILT"), and
the hand-run hit a real divergence: the CI recipe predates the elephant
absorption and reads the cockpit from `starbridge-v2/target/release/`, but on
this checkout starbridge-v2 is a **root-workspace member** (root Cargo.toml
~L76), so the binary lands in the ROOT `target/release/`. pack-deos encodes
that fix: it resolves the cockpit ROOT-first, falls back to the legacy
standalone path, and warns loudly if the path it did *not* pick holds a fresher
binary. `CARGO_TARGET_DIR` is honored.

## What each OS gets (with the installers.yml line ranges mirrored)

| host | artifact | recipe mirrored |
|---|---|---|
| macOS | `Starbridge v2.app` (per-arch, single-arch asserted via `lipo`) | L202-213, L226-257 |
| macOS | ad-hoc `codesign --sign -` (no notarization) | L258-262 |
| macOS | `starbridge-v2-macos-<arch>.dmg` (hdiutil UDZO) + cockpit-only `.tar.gz` | L264-267 |
| Linux | AppImage: cockpit + dregg-node + `--run-node`/`deos-node` AppRun dispatcher + the self-describing vessel at `usr/share/dregg-src/` | L404-537 |
| Linux | two-binary `.tar.gz` (cockpit + node) | L518-524 |
| both | `--headless` boot gate before packaging (skippable) | L215-220 / L412-414 |
| Linux | post-pack smoke: extract, assert both binaries + the vessel (CONSTRUCTIVE-KNOWLEDGE.md canary) | L526-537 |

Outputs land in `starbridge-v2/dist/` (same home as CI and the hbox hand-run).
Ephemeral staging (AppDir, vessel payload, the cached linuxdeploy, smoke
extraction) lives in `target/pack-deos/` — gitignored, so re-runs are
clobber-safe and `git status` stays quiet.

## Honest gaps (also in the script header)

- **mac default = CI parity = cockpit only.** The CI mac job never bundled
  dregg-node or the vessel; only the Linux AppImage is the
  one-download-is-a-whole-node image. `--with-node` / `--with-vessel` close
  the gap but are **unproven shapes** — the vessel goes to
  `Contents/share/dregg-src/`, which the existing executable-relative probe
  (`starbridge-v2/src/source_vessel.rs` L135-141, `exe_dir/../share/dregg-src`)
  should find from `Contents/MacOS/`, but no runtime witness exists yet; the
  node has no mac launcher story (invoke it by path inside the .app).
- **mac signing is ad-hoc**: right-click → Open past Gatekeeper; notarization
  is future work.
- **No universal mac binary, by design** — the Lean archive
  (`libdregg_lean.a`) is arch-native, so each arch needs its own native
  build+pack run (installers.yml L57-75 has the full rationale).
- **Linux is x86_64 only** — nothing aarch64-linux has ever been built or
  packaged here; the script hard-stops rather than guessing.
- **linuxdeploy comes from its `continuous` tag** (as in CI); the copy cached
  in `target/pack-deos/` pins it per-checkout until deleted.
- **Windows is refused, not faked** — `dregg-lean-ffi/build.rs` hard-skips
  `target_os = "windows"`, so a "native-full" Windows binary would silently
  ship marshal-only stubs instead of the verified executor. Blocker + precise
  enable path: installers.yml L560-609.

## Verification status (2026-07-03)

- Linted: `bash -n` + `shellcheck -S warning` clean.
- macOS path exercised end-to-end on an arm64 host against a stand-in Mach-O
  (this lane cannot build the real cockpit): lipo assertions, .app assembly,
  vessel pack (19.5 MB @ 5.2x — matching the hbox milestone's numbers),
  ad-hoc codesign (`codesign --verify --deep --strict` green), hdiutil .dmg,
  cockpit-only tar.gz, idempotent re-run (a rerun without `--with-node`
  correctly clobbered the .app back to cockpit-only), and the stale-pick
  mtime warning.
- Linux path: plan branch exercised via a `uname` shim; the packaging body is
  a line-mirror of the recipe the hbox hand-run proved (DEOS-NIGHT-SHIFT.md
  L90-96) with the root-target fix applied. Not yet run on a real Linux host
  by this script — first hbox run is the remaining witness.
