#!/usr/bin/env bash
# pack-deos.sh — package the CURRENT checkout's deos desktop (the starbridge-v2
# cockpit) into the host OS's native installer, WITHOUT building anything.
#
# WHAT IT IS: the local, reproducible codification of the two packaging recipes
# in `.github/workflows/starbridge-v2-installers.yml` — the workflow whose Linux
# leg was first proven BY HAND on hbox (2026-07-03 ~05:14, see DEOS-NIGHT-SHIFT.md
# "FIRST LINUX AppImage EVER BUILT"). Detects the host OS and runs the matching
# recipe:
#
#   macOS  → per-arch `Starbridge v2.app` + ad-hoc codesign + hdiutil .dmg +
#            raw-binary .tar.gz            (mirrors installers.yml L202-268)
#   Linux  → AppImage carrying BOTH binaries (cockpit + dregg-node), the
#            `--run-node` AppRun dispatcher, and the self-describing vessel
#            (dregg-src.tar.zst), + a two-binary .tar.gz
#                                          (mirrors installers.yml L404-537)
#
# THE GOTCHA THIS SCRIPT EXISTS TO ENCODE: the CI recipe predates the elephant
# absorption — it assumes starbridge-v2 is a STANDALONE workspace and reads the
# cockpit from `starbridge-v2/target/release/`. On THIS checkout starbridge-v2
# is a root-workspace MEMBER (root Cargo.toml ~L76: "starbridge-v2 … is now a
# workspace MEMBER"), so `cargo build --release -p starbridge-v2` lands the
# binary in the ROOT `target/release/`. The hand-run hit exactly this
# (DEOS-NIGHT-SHIFT.md L93-95: "cockpit binary lives in the ROOT workspace
# target/ on this checkout … noted for the workflow fix"). This script resolves
# ROOT-first, falls back to the legacy standalone path, and warns loudly if the
# fallback is fresher than the pick.
#
# NO BUILDING: this script only PACKAGES. It never invokes cargo — a missing
# binary fails fast with the exact build command to run. (The build itself needs
# the Lean archive + plonky3 fork preconditions; see installers.yml L107-183 and
# scripts/bootstrap.sh — out of scope here, on purpose.)
#
# USAGE:
#   scripts/pack-deos.sh                  package for the host OS
#   scripts/pack-deos.sh --dry-run        print the resolved plan, touch nothing
#   scripts/pack-deos.sh --no-selfcheck   skip the `--headless` boot gate
#   scripts/pack-deos.sh --with-vessel    (macOS only) also bundle the
#                                         self-describing vessel into the .app
#   scripts/pack-deos.sh --with-node      (macOS only) also bundle dregg-node
#                                         into the .app
#
# OUTPUTS (same home as CI + the hand-run): starbridge-v2/dist/
#   macOS:  Starbridge v2.app · starbridge-v2-macos-<arch>.dmg · …-<arch>.tar.gz
#   Linux:  starbridge-v2-linux-x86_64.AppImage · …-x86_64.tar.gz
# Ephemeral staging (AppDir, vessel payload, linuxdeploy cache, smoke
# extraction) lives under target/pack-deos/ — gitignored, unlike CI's
# in-crate-cwd AppDir, so a dev checkout stays clean. Re-runs clobber their own
# outputs (rm -rf staging, `hdiutil -ov`, `zstd -f`): idempotent.
#
# ── HONEST PER-OS GAPS ───────────────────────────────────────────────────────
# macOS:
#   • The CI-parity .app carries the COCKPIT ONLY — no dregg-node, no vessel
#     (the CI mac job never bundled them; only the Linux AppImage is the
#     one-download-is-a-whole-node image). `--with-node` / `--with-vessel`
#     close the parity gap but are UNPROVEN shapes (no runtime witness yet):
#     the vessel lands at Contents/share/dregg-src/, which the EXISTING
#     executable-relative probe (starbridge-v2/src/source_vessel.rs L135-141,
#     exe_dir/../share/dregg-src) should find from Contents/MacOS/ — should,
#     not witnessed. The node lands at Contents/MacOS/dregg-node with NO
#     launcher story (no AppRun analogue on mac; users invoke it by path).
#   • Ad-hoc codesign only (`--sign -`): no Developer ID, no notarization.
#     Downloads may need right-click→Open past Gatekeeper. Same as CI (L258-262).
#   • NO universal binary, by design — CI ships one .dmg per arch (L57-75) and
#     this script packages the host arch only. The other arch needs its own
#     native build+pack run (the Lean archive is arch-native; cross is a trap).
#   • The .tar.gz stays cockpit-only even under --with-node (exact CI parity).
# Linux:
#   • x86_64 only — the linuxdeploy download and every proven artifact are
#     x86_64; aarch64-linux has never been packaged (or built) here. Hard stop.
#   • Vulkan/GPU userspace is HOST-provided; the AppImage deliberately does not
#     bundle drivers (installers.yml L499-503).
#   • linuxdeploy is fetched from its `continuous` tag (mirrors CI L504) — a
#     moving upstream; the cached copy in target/pack-deos/ pins it per-checkout
#     until you delete it.
# Windows:
#   • Not packaged, deliberately — dregg-lean-ffi/build.rs hard-skips
#     target_os=windows (no Windows libdregg_lean.a), so a "native-full"
#     Windows build would silently degrade to marshal-only stubs and NOT embed
#     the verified executor. Full blocker + precise enable path: installers.yml
#     L560-609. This script refuses on unrecognized hosts rather than faking.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SB2="$ROOT/starbridge-v2"
DIST="$SB2/dist"
WORK="$ROOT/target/pack-deos"

note() { printf 'pack-deos: %s\n' "$*"; }
warn() { printf 'pack-deos: WARNING: %s\n' "$*" >&2; }
die()  { printf 'pack-deos: ERROR: %s\n' "$*" >&2; exit 1; }

usage() {
  sed -n 's/^# \{0,1\}//p' "${BASH_SOURCE[0]}" | sed -n '1,50p'
}

# ── flags ─────────────────────────────────────────────────────────────────────
DRY_RUN=0
SELFCHECK=1
WITH_VESSEL=0
WITH_NODE=0
while [ $# -gt 0 ]; do
  case "$1" in
    --dry-run)      DRY_RUN=1 ;;
    --no-selfcheck) SELFCHECK=0 ;;
    --with-vessel)  WITH_VESSEL=1 ;;
    --with-node)    WITH_NODE=1 ;;
    -h|--help)      usage; exit 0 ;;
    *)              die "unknown flag: $1 (see --help)" ;;
  esac
  shift
done

# ── host detection ────────────────────────────────────────────────────────────
HOST_ARCH="$(uname -m)"
case "$(uname -s)" in
  Darwin) OS=macos ;;
  Linux)  OS=linux ;;
  *)
    # Windows (MSYS/Cygwin) and anything else: honest refusal, not a fake
    # artifact. See the Windows gap block in this header + installers.yml
    # L560-609 for the real blocker and the precise enable path.
    die "unsupported host '$(uname -s)' — only macOS and Linux have proven packaging recipes (Windows: see installers.yml L560-609)"
    ;;
esac

# stat portability (same probe trick as scripts/pack-dregg-src.sh L59-67):
# GNU stat wants -c, BSD/macOS stat wants -f. Probe once, not `||`-fallback.
if stat -c '%s' "${BASH_SOURCE[0]}" >/dev/null 2>&1; then
  STAT_MTIME=(stat -c '%Y')
else
  STAT_MTIME=(stat -f '%m')
fi

# ── input resolution — THE root-workspace gotcha, encoded ────────────────────
# ROOT target first (this checkout: starbridge-v2 is a root-workspace member,
# root Cargo.toml ~L76); legacy standalone-workspace path second (the shape the
# CI recipe assumed). CARGO_TARGET_DIR, if set, relocates the root candidate.
COCKPIT_CANDIDATES=(
  "${CARGO_TARGET_DIR:-$ROOT/target}/release/starbridge-v2"
  "$SB2/target/release/starbridge-v2"
)
COCKPIT=""
for c in "${COCKPIT_CANDIDATES[@]}"; do
  if [ -x "$c" ]; then COCKPIT="$c"; break; fi
done
# If BOTH exist and the one we did NOT pick is fresher, say so loudly — a stale
# root binary shadowing a fresh standalone build (or vice versa) is exactly the
# kind of silent wrongness the hand-run note warns about.
if [ -n "$COCKPIT" ]; then
  for c in "${COCKPIT_CANDIDATES[@]}"; do
    if [ "$c" != "$COCKPIT" ] && [ -x "$c" ] \
       && [ "$("${STAT_MTIME[@]}" "$c")" -gt "$("${STAT_MTIME[@]}" "$COCKPIT")" ]; then
      warn "picked $COCKPIT but $c is NEWER — is the pick stale? (rm the stale one, or rebuild)"
    fi
  done
fi
COCKPIT_BUILD_HINT="(cd $ROOT && cargo build --release -p starbridge-v2)"

# dregg-node has always been a root-workspace member; one candidate.
NODE="${CARGO_TARGET_DIR:-$ROOT/target}/release/dregg-node"
NODE_BUILD_HINT="(cd $ROOT && cargo build --release -p dregg-node)"

ICON="$ROOT/assets/starbridge-v2.png"

present() { if [ -e "$1" ]; then echo "OK"; else echo "MISSING — build: $2"; fi; }

# ── the plan (always printed; --dry-run stops after it) ──────────────────────
note "host: $OS/$HOST_ARCH · checkout: $ROOT"
note "outputs → $DIST · staging → $WORK"
selfcheck_line() {
  if [ "$SELFCHECK" = 1 ]; then
    echo "    2. headless self-check: cockpit --headless boots the embedded executor + killer demo ($1)"
  else
    echo "    2. headless self-check: SKIPPED (--no-selfcheck)"
  fi
}
if [ "$OS" = macos ]; then
  echo "pack-deos plan (macos, $HOST_ARCH):"
  echo "  inputs:"
  echo "    cockpit : ${COCKPIT:-${COCKPIT_CANDIDATES[0]}} [$(present "${COCKPIT:-/nonexistent}" "$COCKPIT_BUILD_HINT")]"
  [ "$WITH_NODE" = 1 ] && echo "    node    : $NODE [$(present "$NODE" "$NODE_BUILD_HINT")]"
  echo "  steps:"
  echo "    1. assert the binary is a single-arch $HOST_ARCH Mach-O via lipo   (installers.yml L202-213)"
  selfcheck_line "L215-220"
  echo "    3. assemble 'Starbridge v2.app' (Contents/MacOS + Info.plist)      (L226-257)"
  [ "$WITH_NODE" = 1 ]   && echo "    3n. + dregg-node into Contents/MacOS/ [UNPROVEN mac shape — see header gaps]"
  [ "$WITH_VESSEL" = 1 ] && echo "    3v. + self-describing vessel into Contents/share/dregg-src/ [UNPROVEN mac shape — probe: source_vessel.rs L135-141]"
  cat <<PLAN
    4. ad-hoc codesign (--sign -; no notarization)                     (L258-262)
    5. hdiutil UDZO .dmg                                               (L264-265)
    6. raw-binary .tar.gz (cockpit only, exact CI parity)              (L267)
  outputs:
    $DIST/Starbridge v2.app
    $DIST/starbridge-v2-macos-$HOST_ARCH.dmg
    $DIST/starbridge-v2-macos-$HOST_ARCH.tar.gz
PLAN
else
  echo "pack-deos plan (linux, $HOST_ARCH):"
  echo "  inputs:"
  echo "    cockpit : ${COCKPIT:-${COCKPIT_CANDIDATES[0]}} [$(present "${COCKPIT:-/nonexistent}" "$COCKPIT_BUILD_HINT")]"
  echo "    node    : $NODE [$(present "$NODE" "$NODE_BUILD_HINT")]"
  echo "    icon    : $ICON [$(present "$ICON" "git checkout assets/starbridge-v2.png")]"
  echo "  steps:"
  echo "    1. assert dregg-node present                                       (installers.yml L404-410)"
  selfcheck_line "L412-414"
  cat <<PLAN
    3. pack the dregg source payload (self-describing vessel), staged outside dist (L421-427)
    4. assemble AppDir: BOTH binaries + vessel + icon + .desktop + AppRun
       dispatcher (--run-node / deos-node argv0) + deos-node symlink   (L429-497)
    5. linuxdeploy → AppImage (extract-and-run; bundles non-glibc gpui deps;
       Vulkan stays host-provided)                                     (L499-516)
    6. two-binary .tar.gz (cockpit + node, staged into one dir)        (L518-524)
    7. smoke: extract the AppImage; assert both binaries + the vessel
       (incl. metatheory/CONSTRUCTIVE-KNOWLEDGE.md inside the tarball) (L526-537)
  outputs:
    $DIST/starbridge-v2-linux-x86_64.AppImage
    $DIST/starbridge-v2-linux-x86_64.tar.gz
PLAN
fi

if [ "$DRY_RUN" = 1 ]; then
  note "--dry-run: plan printed, nothing touched."
  exit 0
fi

# ── real run: fail fast on missing inputs ─────────────────────────────────────
[ -n "$COCKPIT" ] || die "cockpit binary not found (looked: ${COCKPIT_CANDIDATES[*]}). Build it: $COCKPIT_BUILD_HINT"

mkdir -p "$DIST" "$WORK"

# ── the self-describing vessel (linux always; macOS under --with-vessel) ─────
# Staged OUTSIDE dist because packaging clobbers dist — same reason CI stages
# to $GITHUB_WORKSPACE/dregg-src-payload (installers.yml L421-427); ours lives
# under target/pack-deos/ so the checkout stays clean.
pack_vessel() {
  command -v zstd >/dev/null || die "zstd not found (the vessel is a .tar.zst). macOS: brew install zstd · debian: apt-get install zstd"
  # pack-dregg-src.sh needs bash>=4.4 (mapfile -d); stock macOS bash is 3.2.
  [ "$(bash -c 'echo "${BASH_VERSINFO[0]}"')" -ge 4 ] \
    || die "PATH bash is <4; scripts/pack-dregg-src.sh needs bash>=4.4 (macOS: brew install bash)"
  rm -rf "$WORK/dregg-src-payload"
  mkdir -p "$WORK/dregg-src-payload"
  bash "$ROOT/scripts/pack-dregg-src.sh" "$WORK/dregg-src-payload/dregg-src.tar.zst"
}

# ══ macOS — mirrors installers.yml L202-268 ═══════════════════════════════════
pack_macos() {
  # Single-arch assertion (L202-213): the Lean archive is arch-native, so a
  # fat/wrong-arch binary here means a broken build path upstream. Loud stop.
  local GOT ARCH="$HOST_ARCH"
  GOT="$(lipo -archs "$COCKPIT")"
  note "built arch(s): $GOT (expected $ARCH)"
  case "$ARCH" in
    arm64)  echo "$GOT" | grep -qw arm64  || die "expected arm64 Mach-O, got '$GOT'" ;;
    x86_64) echo "$GOT" | grep -qw x86_64 || die "expected x86_64 Mach-O, got '$GOT'" ;;
    *)      die "unexpected mac host arch '$ARCH'" ;;
  esac

  # Headless self-check (L215-220): boots the live image, runs the four-surface
  # killer demo, exits non-zero on a headline-contract regression. No display.
  if [ "$SELFCHECK" = 1 ]; then
    note "headless self-check…"
    "$COCKPIT" --headless
  else
    warn "selfcheck skipped (--no-selfcheck) — packaging an unwitnessed binary"
  fi

  # .app assembly (L226-257). Idempotent: rm -rf the previous .app first.
  local APP="Starbridge v2.app"
  cd "$SB2"
  mkdir -p dist
  rm -rf "dist/$APP"
  mkdir -p "dist/$APP/Contents/MacOS" "dist/$APP/Contents/Resources"
  cp "$COCKPIT" "dist/$APP/Contents/MacOS/starbridge-v2"

  # Re-assert the PACKAGED binary is exactly single-arch (L237-240): the copy
  # must stay the one arch we verified, never a fat artifact.
  local PKG_ARCHS
  PKG_ARCHS="$(lipo -archs "dist/$APP/Contents/MacOS/starbridge-v2")"
  note "packaged arch(s): $PKG_ARCHS (expected exactly: $ARCH)"
  [ "$PKG_ARCHS" = "$ARCH" ] || die "packaged binary is not single-arch $ARCH (got '$PKG_ARCHS')"

  # Info.plist — byte-for-byte the CI plist (L241-257), version hardcoded 0.1.0
  # exactly as CI hardcodes it.
  cat > "dist/$APP/Contents/Info.plist" <<'PLIST'
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
  <key>CFBundleName</key><string>Starbridge v2</string>
  <key>CFBundleDisplayName</key><string>Starbridge v2</string>
  <key>CFBundleIdentifier</key><string>dev.dregg.starbridge-v2</string>
  <key>CFBundleVersion</key><string>0.1.0</string>
  <key>CFBundleShortVersionString</key><string>0.1.0</string>
  <key>CFBundleExecutable</key><string>starbridge-v2</string>
  <key>CFBundlePackageType</key><string>APPL</string>
  <key>LSMinimumSystemVersion</key><string>13.0</string>
  <key>NSHighResolutionCapable</key><true/>
</dict>
</plist>
PLIST

  # ── parity extensions (OFF by default; both UNPROVEN shapes, see header) ──
  if [ "$WITH_NODE" = 1 ]; then
    [ -x "$NODE" ] || die "dregg-node not found at $NODE. Build it: $NODE_BUILD_HINT"
    cp "$NODE" "dist/$APP/Contents/MacOS/dregg-node"
    note "+ dregg-node → Contents/MacOS/dregg-node (no launcher; invoke by path)"
  fi
  if [ "$WITH_VESSEL" = 1 ]; then
    pack_vessel
    # Contents/MacOS/../share/dregg-src == Contents/share/dregg-src — the
    # exe-relative probe source_vessel.rs L135-141 already looks exactly there.
    mkdir -p "dist/$APP/Contents/share/dregg-src"
    cp "$WORK/dregg-src-payload/dregg-src.tar.zst" "dist/$APP/Contents/share/dregg-src/dregg-src.tar.zst"
    note "+ vessel → Contents/share/dregg-src/dregg-src.tar.zst (exe-relative probe target; unwitnessed on mac)"
  fi

  # Ad-hoc sign (L258-262) — the minimum that lets a local user open the .app
  # without the "damaged" Gatekeeper refusal. Runs AFTER the parity extras so
  # the signature seals everything in the bundle.
  codesign --force --deep --sign - "dist/$APP" || \
    echo "ad-hoc codesign unavailable; shipping unsigned .app (user may need to allow it in System Settings)."

  # .dmg via hdiutil (L264-265); -ov makes re-runs clobber-safe.
  hdiutil create -volname "Starbridge v2" -srcfolder "dist/$APP" \
    -ov -format UDZO "dist/starbridge-v2-macos-$ARCH.dmg"

  # Raw single-arch binary tarball (L267) — cockpit only, exact CI parity,
  # taken from wherever the binary actually resolved (root target/, not the
  # CI-assumed standalone target/).
  tar -C "$(dirname "$COCKPIT")" -czf "dist/starbridge-v2-macos-$ARCH.tar.gz" starbridge-v2

  ls -la dist
  note "macOS packaging complete → $DIST"
}

# ══ Linux — mirrors installers.yml L404-537 ═══════════════════════════════════
pack_linux() {
  # x86_64 only: every proven artifact (and the linuxdeploy download) is
  # x86_64; an aarch64 AppImage has never been built here. Honest stop.
  [ "$HOST_ARCH" = x86_64 ] || die "linux packaging is proven for x86_64 only (host: $HOST_ARCH) — see header gaps"

  # Tool preflight — the packaging subset of CI's apt install (L301-312). The
  # BUILD-time gpui deps are out of scope (we don't build); these are what the
  # package step itself touches.
  local missing=()
  for t in file zstd patchelf; do command -v "$t" >/dev/null || missing+=("$t"); done
  [ -x "$WORK/linuxdeploy" ] || command -v wget >/dev/null || missing+=(wget)
  [ "${#missing[@]}" -eq 0 ] || die "missing tools: ${missing[*]} — apt-get install ${missing[*]} (CI's full list: installers.yml L301-312)"
  command -v desktop-file-validate >/dev/null || warn "desktop-file-utils absent; linuxdeploy skips .desktop validation"

  # Assert dregg-node (L404-410): one image = cockpit + a node you can init+run.
  [ -x "$NODE" ] || die "dregg-node not found at $NODE — the AppImage cannot bundle the node. Build it: $NODE_BUILD_HINT"
  [ -f "$ICON" ] || die "icon missing at $ICON (the real 256x256 committed icon, not a stub)"

  # Headless self-check (L412-414).
  if [ "$SELFCHECK" = 1 ]; then
    note "headless self-check…"
    "$COCKPIT" --headless
  else
    warn "selfcheck skipped (--no-selfcheck) — packaging an unwitnessed binary"
  fi

  # The vessel (L421-427), staged under $WORK (outside dist — dist gets rm -rf'd).
  pack_vessel

  # AppDir assembly (L429-497). Staging under $WORK keeps the checkout clean
  # (CI builds AppDir in the crate cwd; locally that would litter git status).
  local APPDIR="$WORK/AppDir"
  rm -rf "$APPDIR" "$WORK/squashfs-root"
  rm -f "$WORK"/*-x86_64.AppImage
  mkdir -p "$APPDIR/usr/bin" "$APPDIR/usr/share/icons/hicolor/256x256/apps"
  rm -rf "$DIST"
  mkdir -p "$DIST"

  # BOTH binaries — one download = cockpit + a local node (L441-445). The
  # cockpit resolves from the ROOT workspace target/ (THE gotcha, see header).
  cp "$COCKPIT" "$APPDIR/usr/bin/starbridge-v2"
  cp "$NODE"    "$APPDIR/usr/bin/dregg-node"

  # THE SOURCE PAYLOAD (L447-454) — the self-describing vessel's carrier, at
  # usr/share/dregg-src/ where SourceVessel's executable-relative search
  # (AppDir/usr/bin → ../share/dregg-src) finds it.
  mkdir -p "$APPDIR/usr/share/dregg-src"
  cp "$WORK/dregg-src-payload/dregg-src.tar.zst" "$APPDIR/usr/share/dregg-src/dregg-src.tar.zst"

  # The real committed icon, both places linuxdeploy reads (L456-460).
  cp "$ICON" "$APPDIR/starbridge-v2.png"
  cp "$ICON" "$APPDIR/usr/share/icons/hicolor/256x256/apps/starbridge-v2.png"

  # .desktop (L462-471) — byte-for-byte the CI entry.
  cat > "$APPDIR/starbridge-v2.desktop" <<'DESK'
[Desktop Entry]
Type=Application
Name=Starbridge v2
Comment=The dregg master interface — a live verified ocap world (bundles a local dregg-node)
Exec=starbridge-v2
Icon=starbridge-v2
Categories=Development;
Terminal=false
DESK

  # AppRun dispatcher (L473-495) — byte-for-byte. Default = cockpit; the node
  # runs via `--run-node <args>` or an ARGV0=deos-node symlink. NOTE the token
  # is `--run-node`, NOT `--node`: the cockpit's own `--node <url>` (attach to
  # a REMOTE node) must pass through untouched.
  cat > "$APPDIR/AppRun" <<'RUN'
#!/bin/sh
HERE="$(dirname "$(readlink -f "$0")")"
export PATH="$HERE/usr/bin:$PATH"
export LD_LIBRARY_PATH="$HERE/usr/lib:${LD_LIBRARY_PATH:-}"
# Node entrypoint via a deos-node argv0 (symlink) or a leading --run-node flag.
case "${ARGV0:-$(basename "$0")}" in
  deos-node|dregg-node) exec "$HERE/usr/bin/dregg-node" "$@" ;;
esac
if [ "${1:-}" = "--run-node" ]; then
  shift
  exec "$HERE/usr/bin/dregg-node" "$@"
fi
exec "$HERE/usr/bin/starbridge-v2" "$@"
RUN
  chmod +x "$APPDIR/AppRun"
  # deos-node convenience launcher inside the image (argv0 → node path, L497).
  ln -sf AppRun "$APPDIR/deos-node"

  # linuxdeploy (L499-516): bundles the transitive non-glibc native deps the
  # gpui stack pulls; GPU/Vulkan userspace deliberately NOT bundled (host's).
  # Cached in $WORK across runs; delete it to re-fetch `continuous`.
  if [ ! -x "$WORK/linuxdeploy" ]; then
    note "fetching linuxdeploy (continuous)…"
    wget -q https://github.com/linuxdeploy/linuxdeploy/releases/download/continuous/linuxdeploy-x86_64.AppImage -O "$WORK/linuxdeploy"
    chmod +x "$WORK/linuxdeploy"
  fi
  # FUSE is flaky/absent in many environments; extract-and-run sidesteps it
  # for both linuxdeploy and any AppImage we invoke below (L507).
  export APPIMAGE_EXTRACT_AND_RUN=1
  ( cd "$WORK" && ./linuxdeploy \
      --appdir AppDir \
      --executable AppDir/usr/bin/starbridge-v2 \
      --executable AppDir/usr/bin/dregg-node \
      --desktop-file AppDir/starbridge-v2.desktop \
      --icon-file AppDir/starbridge-v2.png \
      --output appimage )
  # linuxdeploy emits Starbridge_v2-x86_64.AppImage in ITS cwd; normalize (L515-516).
  mv "$WORK"/*-x86_64.AppImage "$DIST/starbridge-v2-linux-x86_64.AppImage"

  # Two-binary .tar.gz (L518-524): stage both into one dir so a single archive
  # holds both (you can't append to a gzip'd tar).
  local STAGE
  STAGE="$(mktemp -d)"
  cp "$COCKPIT" "$STAGE/starbridge-v2"
  cp "$NODE"    "$STAGE/dregg-node"
  tar -C "$STAGE" -czf "$DIST/starbridge-v2-linux-x86_64.tar.gz" starbridge-v2 dregg-node
  rm -rf "$STAGE"
  ls -la "$DIST"

  # Smoke (L526-537): the image must contain BOTH binaries AND the vessel, and
  # the vessel must hold the real source (CONSTRUCTIVE-KNOWLEDGE.md is the
  # canary member). Extraction happens in $WORK, cleaned after.
  ( cd "$WORK" && rm -rf squashfs-root \
    && "$DIST/starbridge-v2-linux-x86_64.AppImage" --appimage-extract >/dev/null 2>&1 || true )
  test -x "$WORK/squashfs-root/usr/bin/starbridge-v2" || die "smoke: AppImage lacks the cockpit binary"
  test -x "$WORK/squashfs-root/usr/bin/dregg-node"    || die "smoke: AppImage lacks dregg-node"
  note "AppImage contains BOTH binaries: starbridge-v2 + dregg-node"
  test -f "$WORK/squashfs-root/usr/share/dregg-src/dregg-src.tar.zst" || die "smoke: AppImage lacks the source payload"
  zstd -dc "$WORK/squashfs-root/usr/share/dregg-src/dregg-src.tar.zst" \
    | tar -tf - dregg-src/metatheory/CONSTRUCTIVE-KNOWLEDGE.md >/dev/null \
    || die "smoke: vessel tarball lacks metatheory/CONSTRUCTIVE-KNOWLEDGE.md"
  note "AppImage carries the dregg source payload (self-describing vessel)"
  rm -rf "$WORK/squashfs-root"

  note "linux packaging complete → $DIST"
}

case "$OS" in
  macos)
    if [ "$WITH_VESSEL$WITH_NODE" != "00" ]; then
      note "parity extensions requested: vessel=$WITH_VESSEL node=$WITH_NODE (unproven mac shapes — see header)"
    fi
    pack_macos
    ;;
  linux)
    # --with-vessel/--with-node are mac parity flags; the linux image ALWAYS
    # carries both (that IS the proven recipe). No-op with a note.
    [ "$WITH_VESSEL$WITH_NODE" = "00" ] || note "--with-vessel/--with-node are no-ops on linux (the AppImage always carries both)"
    pack_linux
    ;;
esac
