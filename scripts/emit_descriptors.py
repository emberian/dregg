#!/usr/bin/env python3
"""emit_descriptors.py — regenerate every circuit descriptor JSON from the Lean
emit (the SOURCE OF TRUTH) and re-pin the sha256 fingerprints in the Rust registry.

Lean is authoritative: the `circuit/descriptors/*.json` files and the `*_FP`
fingerprint constants are MACHINE-GENERATED projections of the verified Lean
`EffectVmDescriptor` objects. This script is the ONE command that closes the
Lean->JSON->FP loop, so the checked-in artifacts can never silently drift from
the Lean emission.

Pipeline:
  1. Run each Lean emitter executable (`lake env lean --run <file>`), capturing
     its `key<TAB>name<TAB>json` (or manifest) TSV stdout.
  2. Split each emitter's stdout into `circuit/descriptors/<file>.json` via the
     per-emitter routing below. The routing is reconstructed from the Rust
     registry tables (so it stays in lockstep with how the prover consumes them).
  3. Recompute sha256 of every emitted file and rewrite the matching `*_FP`
     constant in the Rust sources.
  4. Normalize the WHOLE Lean-authored Rust modules (`circuit/src/effect_vm/
     *_generated.rs`) through the pinned rustfmt, so the generator's bytes equal
     the bytes `scripts/git-hooks/pre-commit` and `cargo fmt --all -- --check`
     produce — the two producers cannot disagree (see normalize_generated_rust).

Idempotent: on a freshly-emitted AND fully-stamped tree it is a NO-OP (nothing is
written). "Byte-identical" alone is not enough for that — a descriptor whose bytes
already equal the emission but which PROVENANCE.json does not COVER still gets
stamped (see provenance_stamp_gap). Run `scripts/check-descriptor-drift.sh` to GATE
on drift.

AUTOMATIC PROVENANCE (2026-11-06, SUBSTRATE-DECISION §9 row 4 as amended by codex
round 3): there is no human acknowledgement step. The emit REFUSES (exit 3, tree
untouched) when any `.lean` file in the emitters' transitive in-tree import closure,
or the lake configuration, has uncommitted or untracked edits — so every stamp is
minted from committed source by construction, and `source_dirty` can no longer be
true. Every byte-changing or stamp-short emission then writes
circuit/descriptors/PROVENANCE.json (Lean source tree hash, repo HEAD, toolchain,
emitter list, per-file sha256) with no environment variable and no operator. The
ack env vars, the ALLOW_DIRTY override, `--stamp-existing` (a disk re-hash with no
Lean witness) and `--strict` were deleted; see docs/VK-REGEN-CONTROLS.md.

Modes:
  (default)              emit from Lean (committed closure only), install, stamp.
                         `--rev <sha>` additionally requires the checkout to BE that
                         commit (the canonical host is a clean clone; see
                         docs/automata/BUILD.md "Emit and stamp (C2)")
  --verify-provenance    recompute hashes vs the stamp, and refuse a stamp that
                         records source_dirty=true. `--rev <rev>` grades that
                         REVISION in a detached, `git status`-clean worktree
                         instead of whatever is lying around (the churn-safe form;
                         this is the one a shared tree can always answer). A stamp
                         whose `mode` is not "emit" (a disk re-hash, not a Lean
                         witness) is refused. No Lean needed.
  --self-test-provenance drive --verify-provenance RED and GREEN on scratch copies
                         (mutated byte, dropped stamp row, source_dirty stamp,
                         plus the clean control). Touches nothing shared.
  --verify-by-name-routing
                         reconcile `EmitByName.lean`'s routing table against the
                         checked-in by-name/ set and the stamp, BOTH directions.
                         Static parse of the .lean — no Lean run, no cargo, seconds
                         — so it still works while the emit is blocked (which is
                         exactly when a routing gap can sit unnoticed). ALSO runs
                         all three other doors on ONE class — a COMMITTED reference
                         to an UNCOMMITTED target, which is green for its author and
                         red for every fresh checkout: every literal `include_str!`/
                         `include_bytes!` target in tracked Rust (verify_include_
                         targets), every first-party Lean `import` (verify_lean_
                         imports), and every repo path a tracked
                         `.github/workflows/*.yml` invokes (verify_workflow_refs)
                         must EXIST and be TRACKED.
  --list-emitter-modules print the Lean modules the emitters import (one per line)
                         — the set that must be `lake build`-ed for the emit to run
                         on a cold checkout. Derived from the emitters' own imports;
                         no Lean run. `check-descriptor-drift.sh` builds this.
  --list-guarded-paths   print the repo-relative paths this driver can REWRITE (one
                         per line) — `install_and_stamp`'s whole change-set: the
                         descriptor dir, the `*_FP`-bearing Rust sources, and the
                         Lean-authored `*_generated.rs` modules. No Lean run.
                         `check-descriptor-drift.sh` snapshots exactly this instead
                         of transcribing it.

Exit codes: 0 = ok/no-op · 1 = routing/verify failure · 2 = emitter failed ·
3 = EMIT REFUSED (the emitters' source closure is not committed; tree left untouched).
"""
from __future__ import annotations

import contextlib
import datetime
import getpass
import hashlib
import io
import json
import os
import re
import shlex
import shutil
import socket
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
META = ROOT / "metatheory"
DESC = ROOT / "circuit" / "descriptors"

# The regen-control surface (docs/VK-REGEN-CONTROLS.md).
PROVENANCE_FILE = "PROVENANCE.json"                # lives inside circuit/descriptors/

# Artifacts under circuit/descriptors/ that this driver does NOT own — each is regenerated AND
# drift-checked by its OWN pipeline, so requiring an emitter here would be a false routing gap.
# Every entry MUST have a co-located regen/check that keeps it fresh (never a silent exemption):
#   * dregg-cert-qp-portfolio6-s3-ir2.json — regenerated + `--check`ed by regen-cert-qp.sh
#     (`lake env lean --run EmitCertQpDescriptor.lean`, deliberately outside this driver's EMITTERS).
#   * regen-cert-qp.sh — the regen SCRIPT itself (not a descriptor; it has no emitter by construction).
# The SeamSpec / PiPort registry used to be exempt while `EmitSeamSpecs.lean` was untracked and
# red on an in-flight rename. That condition ended when the module landed green. It is routed below
# now, so a flag day re-emits the seam ends in the same buffered, all-or-nothing pass as the
# descriptors they name; keeping the exemption would preserve two ceremonies for one object.
COVERAGE_EXEMPT = frozenset({
    "dregg-cert-qp-portfolio6-s3-ir2.json",
    "regen-cert-qp.sh",
})
AUDIT_LOG_REL = Path("docs") / "VK-REGEN-LOG.md"   # git-tracked append-only regen log
EXIT_REFUSED = 3

# The Rust sources that carry `include_str!(...descriptors/<file>)` + a matching
# `*_FP` sha256 constant for it.
RUST_FP_FILES = [
    ROOT / "circuit" / "src" / "effect_vm_descriptors.rs",
    ROOT / "circuit" / "src" / "cap_delegation_nonamp_descriptor.rs",
    ROOT / "circuit" / "src" / "cap_reshape_descriptor.rs",
    ROOT / "circuit" / "src" / "bilateral_aggregation_air.rs",
    ROOT / "circuit" / "src" / "lean_descriptor_air.rs",
]

# The Lean emitter executables (run via `lake env lean --run`), in a stable order.
EMITTERS = [
    "Dregg2/Circuit/Emit/EmitAllJson.lean",  # v1: name-keyed
    "EmitAllJsonV2.lean",                    # ir2: defName-keyed (V2_DESCRIPTORS)
    "EmitRotationV3.lean",                   # rotation v3-staged artifacts + registry tsv
    "EmitWideRegistryProbe.lean",            # ADDITIVE: the 57-member faithful 8-felt wide registry (covers live V3)
    "EmitBilateralLegs.lean",                # bilateral-aggregation legs
    "EmitCrossCellConservation.lean",        # turn-wide cross-cell Σδ=0 conservation AIR (foolable gap #6)
    "EmitWideUMemWeldRegistryProbe.lean",    # ADDITIVE/STAGED: the WIDE+umem welded registry (covers wide V3)
    "EmitLayoutManifest.lean",               # the rotated COLUMN LAYOUT, exported from Lean AS RUST
    "EmitByName.lean",                       # the by-name/ dispatch surface descriptor_by_name() serves
    "EmitSeamSpecs.lean",                    # recursion SeamSpec / declared PiPort registry
    "EmitTableAirs.lean",                    # the table-airs/ SHARED table AIRs (see below)
    "EmitCertF.lean",                        # the ring-3 Cert-F IR2 descriptor (cert_f_air.rs include_str!s it)
    "EmitCertFMarket4.lean",                 # the market4 (3-asset/4-order, ε>0) Cert-F IR2 descriptor
]

# The checked-in artifact `circuit-prove/src/cert_f_air.rs:297` include_str!s. It was the ONLY flat
# descriptor no emitter reproduced (tracked in GOAL-STARK-KILL.md) — include_str!'d into a live AIR
# yet outside the re-derivation, so the drift gate could not see it move.
CERT_F_FILE = "dregg-cert-f-ir2.json"

# The market4 registered Cert-F program (the first REAL market shape past the ring-3 toy;
# authored as `certFDescriptorOf market4Prog` in Market/CertFDescriptor.lean §4b).
CERT_F_MARKET4_FILE = "dregg-cert-f-market4-ir2.json"

# The by-name descriptors that are checked in WITH a trailing newline.
#
# ⚑⚑ THIS SET'S STATED JUSTIFICATION IS FALSE, AND THE SET IS SCHEDULED FOR DELETION.
#
# It used to read: "it is purely cosmetic — JSON does not care — but the bytes are FP/VK-pinned, so
# NORMALIZING the convention would re-key those 5 descriptors for a whitespace change."
#
# A descriptor's semantic fingerprint — the thing a `vk_pin` names and the thing that feeds the
# recursive VK hash — is `effect_vm_descriptor2_semantic_fingerprint(&EffectVmDescriptor2)`: it
# canonically re-encodes the PARSED descriptor and never hashes the file bytes. A trailing newline is
# discarded by the parser before the fingerprint is taken.
#
# PROVED over all 158 served descriptors, both directions (add to bare, strip from terminated), by
#   circuit/tests/vk_pin_closure_over_the_served_tree.rs
#     ::a_trailing_newline_does_not_move_a_descriptors_fingerprint
#
# So normalising the convention is a PROVENANCE RE-STAMP, not a re-key: it moves each file's sha256
# and moves no `vk_pin`, no VK and no federation key. The cost estimate that froze this set was
# pricing a flag day that does not exist.
#
# Why it must go rather than stay correct-but-cosmetic: while it stands, ONE object has TWO byte
# streams. `metatheory/MinaChainEmit.lean:48` writes `emitVmJson2 chainDesc ++ "\n"`;
# `metatheory/EmitByName.lean:788` writes the same descriptor with no trailing byte; and this table
# reconciles them per-filename. Determinism that is restored by a hand-maintained lookup of 30 names
# is not determinism, and it is the precondition for descriptors becoming build artifacts at all —
# a generated file cannot be reproducible if its producer's byte stream depends on which driver ran.
#
# THE MOVE (not done here — it needs a full regen, and this must not fire while sibling lanes hold
# `circuit/descriptors/` open):
#   1. make the payload newline-terminated UNIFORMLY at the writer in `install_and_stamp`;
#   2. drop the `blob += "\n"` special-case below and delete this frozenset;
#   3. give `EmitByName` and `MinaChainEmit` one shared writer so neither decides the convention;
#   4. re-stamp PROVENANCE.json. No VK rotation, no re-emit of any consumer.
#
# ⚠ The census in the old comment was itself stale — it said "21 bare, 5 newline-terminated"; the
# directory is 94 bare and 37 newline-terminated. A transcribed count went stale inside the comment
# explaining why a transcribed convention had to be preserved.
BY_NAME_NEWLINE_TERMINATED = frozenset({
    # The Lean-authored Pasta AIRs. Emitted by `lake env lean --run … > file`, so newline-
    # terminated like every other redirect-emitted artifact. Declared here because omitting a
    # newline-terminated file from this set makes the emit STRIP a byte and re-key the descriptor
    # for a whitespace change — the exact re-keying this set exists to prevent.
    "pasta-rcb-windowed.json",
    "pasta-rcb-sg-slice-0-of-4.json",
    "pasta-rcb-sg-slice-1-of-4.json",
    "pasta-rcb-sg-slice-2-of-4.json",
    "pasta-rcb-sg-slice-3-of-4.json",
    "pasta-rcb-sg-slice-0-of-4-w8.json",
    "pasta-rcb-sg-slice-1-of-4-w8.json",
    "pasta-rcb-sg-slice-2-of-4-w8.json",
    "pasta-rcb-sg-slice-3-of-4-w8.json",
    # …and the six FELT-SOUND replacements (`PastaFieldSound` / `PastaAddSubSound`), emitted the
    # same way.
    "pasta-fpmul-sound.json",
    "pasta-fqmul-sound.json",
    "pasta-fpadd-sound.json",
    "pasta-fpsub-sound.json",
    "pasta-fqadd-sound.json",
    "pasta-fqsub-sound.json",
    # ⚑ The eight-block phase-2 chain link (routed 2026-08-05). Emitted by redirect out of
    # `EmitPastaAlu.lean fqchain` before it was routed here, so it carries the trailing newline
    # every redirect-emitted artifact carries.
    "pasta-fq-chainlink.json",
    "dark-bazaar-private-n4k4.json",
    "faithful-note-spend-v2.json",
    "field-delta-result-range.json",
    "poseidon2-hash-arity2.json",
    "private-preference-n4k4.json",
    "private-preference-cell-n4k4.json",
    "private-graph-rewrite-4x2.json",
    "private-graph-rewrite-cell-4x2.json",
    "private-quest-graph-4x2.json",
    "private-raid-assignment-n4.json",
    "private-shuffle-n8.json",
    "private-shuffle-fair-n8.json",
    "private-book-bfv-odd-ntt-butterfly-q0-n8.json",
    "private-book-bfv-odd-ntt-butterfly-q0-n4096.json",
    "private-book-bfv-odd-intt-butterfly-q0-n4096.json",
    "private-book-bfv-odd-ntt-butterfly-q0-n8-stage0-exact-public.json",
    "private-book-bfv-odd-ntt-butterfly-q0-n8-stage1-exact-public.json",
    "private-book-bfv-odd-ntt-butterfly-q0-n8-stage2-exact-public.json",
    "turn-chain-binding.json",
    "descent-custody-census-fixed8-v1.json",
    "shielded-whole-note-swap-substrate-v1.json",
})


def run(cmd, **kw):
    return subprocess.run(cmd, check=True, capture_output=True, text=True, **kw)


def emitter_modules() -> list[str]:
    """The Lean library modules that must be BUILT for `emit()` to run at all.

    `lake env lean --run <emitter>` loads its imports from COMPILED oleans; it does not
    build them. So the emit only works where something already warmed those oleans —
    and `lake build` (default targets: Dregg2/Metatheory/Polis/Market) does NOT warm all
    of them. Measured at the time of writing: 17 of `EmitByName.lean`'s 26 imports are
    reachable from NO default target (the `Dregg2.Circuit.Emit.*Emit` authors under
    DfaRouting/Predicates/Presentation/… — nothing in the `Dregg2` root import closure
    pulls them in). On a cold checkout the by-name emit therefore died with 'object file
    does not exist' and `emit_descriptors.py` exited 2 — i.e. the drift gate was green
    only where an EARLIER build step, outside the gate, happened to warm the cache. The
    emitters the gate RAN were not the emitters the gate BUILT.

    This DERIVES the build set from the emitters' own `import` lines rather than pinning
    a hand-written list, so adding an emitter (or an import to one) cannot silently
    reintroduce the hole. Direct imports suffice: `lake build M` builds M's deps too.
    Imports with no in-tree source file are dependencies of the toolchain/mathlib and are
    dropped — `lake build` cannot take them as targets.
    """
    mods: list[str] = []
    dropped: list[str] = []
    for lean_file in EMITTERS:
        path = META / lean_file
        if not path.exists():
            sys.exit(f"emit_descriptors: emitter source missing: {path}")
        for line in path.read_text().splitlines():
            m = re.match(r"^import\s+([A-Za-z0-9_.]+)", line)
            if not m:
                continue
            mod = m.group(1)
            if (META / (mod.replace(".", "/") + ".lean")).exists():
                if mod not in mods:
                    mods.append(mod)
            elif mod not in dropped:
                dropped.append(mod)
    # A dropped import is normally a mathlib/toolchain dep (`lake build` cannot take
    # it as a target, and it is built transitively via the in-tree modules that use
    # it). But dropping is the same "built set != run set" shape the derived list
    # exists to prevent, so REPORT the drops rather than swallowing them silently: a
    # future emitter whose only imports are out-of-tree would otherwise contribute
    # nothing to the build set with no word said. Visible + auditable, behaviour
    # unchanged.
    if dropped:
        print(
            "emit_descriptors: derived build set drops "
            f"{len(dropped)} out-of-tree import(s) (toolchain/mathlib deps, built "
            f"transitively): {', '.join(sorted(dropped))}",
            file=sys.stderr,
        )
    if not mods:
        sys.exit(
            "emit_descriptors: derived build set is EMPTY — every emitter import was "
            "dropped as out-of-tree. Refusing to build nothing and re-depend on a warm "
            "cache (the exact hole this derivation closes)."
        )
    return mods


def build_emitter_modules() -> None:
    """⚑ **BUILD THE EMITTERS' IMPORTS BEFORE RUNNING THEM. THE SOURCE OF TRUTH IS THE `.lean`, NOT
    WHATEVER `.olean` HAPPENS TO BE ON DISK.**

    `lake env lean --run <emitter>` compiles the EMITTER SCRIPT fresh and then resolves its imports
    from COMPILED oleans — it does not rebuild them. So on a tree whose Lean sources are ahead of
    `.lake`, this driver silently emits the OLD descriptors while
    `install_and_stamp` records the CURRENT `HEAD:metatheory/Dregg2` tree hash in
    `PROVENANCE.json` and appends an audit row saying so. Nothing goes red: the emitters exit 0, the
    bytes are self-consistent, and the stamp claims a source tree that did not mint them.

    Measured 2026-08-08. A ninth-lane repair to `Emit/CarrierOctetGates.quadIdx` was elaborated,
    proved and its 12 dependents built — in a scratch clone. The shared `metatheory/.lake` was a day
    stale, so the authorized regen installed a `layout_generated.rs` carrying the RETIRED `[0,4,2,6]`
    interleave and reported `1 changed descriptor file`, having "emitted" 208 from the old tree. The
    only reason it was caught is that the emitted table was small enough to read.

    `check-descriptor-drift.sh` already builds `--list-emitter-modules` before comparing, i.e. the
    DRIFT gate knew this and the INSTALL driver did not — the more dangerous half was the unguarded
    one. Exits 2 (the emitter-failure code) on a red build: a regen off an incoherent Lean tree must
    not proceed."""
    mods = emitter_modules()
    print(f"emit_descriptors: building {len(mods)} emitter modules (oleans must match the sources)...")
    r = subprocess.run(["lake", "build", *mods], cwd=META, capture_output=True, text=True)
    if r.returncode != 0:
        errs = [ln for ln in (r.stdout + r.stderr).splitlines() if ln.startswith("error")]
        sys.stderr.write(
            "\nEMIT REFUSED: `lake build` of the emitter modules failed, so the oleans "
            "`lake env lean --run` would load do NOT correspond to the Lean sources this run would "
            "stamp as their origin. Fix the Lean build; do not emit from stale oleans.\n"
            "--- first errors ---\n" + "\n".join(errs[:20]) + "\n"
        )
        sys.exit(2)


def emit(lean_file: str) -> str:
    """Run a Lean emitter, return its raw stdout.

    Retries on TRANSIENT failures. On a co-tenant build box (multiple agents running `lake`
    concurrently) a `lake env lean --run` can fail through no fault of the emitter: a concurrent
    `lake` reconfigure holds the exclusive configuration lock ("could not acquire an exclusive
    configuration lock"), or a background rebuild clobbers an olean mid-read (a bare non-zero exit
    with empty stderr). The emitters are deterministic, so a REAL error fails every attempt and still
    exits 2; a transient one clears on retry. Without this, a single unlucky moment aborts the whole
    (~10 min) regen."""
    import time
    attempts = 4
    for i in range(attempts):
        r = subprocess.run(
            ["lake", "env", "lean", "--run", lean_file],
            cwd=META, capture_output=True, text=True,
        )
        if r.returncode == 0:
            return r.stdout
        transient = (
            "configuration lock" in r.stderr
            or "reconfiguring the package" in r.stderr
            or r.stderr.strip() == ""  # a bare kill (concurrent olean clobber / OOM signal)
        )
        if transient and i < attempts - 1:
            sys.stderr.write(
                f"emit_descriptors: transient failure on {lean_file} "
                f"(attempt {i + 1}/{attempts}, rc={r.returncode}); retrying after backoff...\n"
            )
            time.sleep(5 * (i + 1))
            continue
        sys.stderr.write(
            f"\nEMIT FAILED: lake env lean --run {lean_file}\n"
            f"--- stderr ---\n{r.stderr}\n"
        )
        sys.exit(2)
    # unreachable (loop either returns or exits)
    sys.exit(2)


# ---- defName/const routing reconstructed from the Rust registry -------------

def const_to_file(rust_text: str) -> dict[str, str]:
    """`pub const NAME: &str = include_str!("../descriptors/FILE");` -> {NAME: FILE}."""
    out = {}
    for m in re.finditer(
        r'pub const (\w+):\s*&str\s*=\s*\n?\s*include_str!\("\.\./descriptors/([^"]+)"\)',
        rust_text,
    ):
        out[m.group(1)] = m.group(2)
    return out


def ir2_defname_to_file(rust_text: str, c2f: dict[str, str]) -> dict[str, str]:
    """V2_DESCRIPTORS: (defName, CONST_JSON, CONST_FP) -> {defName: file}."""
    out = {}
    block = re.search(r'V2_DESCRIPTORS:\s*&\[.*?\];', rust_text, re.S)
    if not block:
        sys.exit("emit_descriptors: V2_DESCRIPTORS table not found in effect_vm_descriptors.rs")
    for dn, cj, _cfp in re.findall(
        r'\(\s*"([^"]+)",\s*(\w+),\s*(\w+),?\s*\)', block.group(0)
    ):
        if cj in c2f:
            out[dn] = c2f[cj]
    return out


# ---- Lean-authored Rust modules ---------------------------------------------
# Unlike the FP constants (which are REWRITTEN in place inside hand-written .rs files), these are
# WHOLE modules whose every byte comes from Lean. The layout module is the single source for the
# rotated column geometry that the producer writes, the descriptors read, and the gates audit.

LAYOUT_RS = ROOT / "circuit" / "src" / "effect_vm" / "layout_generated.rs"
S2_COMPACT_RS = ROOT / "circuit" / "src" / "effect_vm" / "s2_compact_generated.rs"
E1_COMPACT_RS = ROOT / "circuit" / "src" / "effect_vm" / "e1_compact_generated.rs"
UMEM_WELD_RS = ROOT / "circuit" / "src" / "effect_vm" / "umem_weld_generated.rs"

# THE DECLARED generated-module set. `GENERATED_RS` below is filled at EMIT time, so nothing
# static can read it — and `scripts/check-descriptor-drift.sh` has to know this driver's whole
# change-set BEFORE the emit, to snapshot it. That set used to be transcribed into the shell as
# a `GUARDED=(…)` array; the header of that script records what a transcription costs here (the
# `*_generated.rs` modules were missing from it, so a generated-Rust-only change took the
# non-ack install path, the gate diffed nothing, and it reported PASS while the tree had just
# been rewritten underneath it). The shell now DERIVES its guarded set from
# `--list-guarded-paths`, which reads this tuple, so there is exactly ONE authority.
#
# `assert_generated_declared()` is the tooth that keeps this tuple honest: a future emitter that
# buffers a FOURTH module into `GENERATED_RS` without listing it here FAILS the emit, instead of
# silently reopening the same hole one module wider.
GENERATED_RS_PATHS: tuple[Path, ...] = (LAYOUT_RS, S2_COMPACT_RS, E1_COMPACT_RS, UMEM_WELD_RS)

GENERATED_RS: dict[Path, str] = {}


def assert_generated_declared() -> None:
    """Every buffered generated module must be DECLARED in `GENERATED_RS_PATHS`.

    Undeclared means `check-descriptor-drift.sh` never snapshots it, so a re-emit that rewrites
    it is invisible to the drift gate — the exact hole that script's header records."""
    undeclared = sorted(str(p) for p in GENERATED_RS if p not in GENERATED_RS_PATHS)
    if undeclared:
        sys.exit(
            "emit_descriptors: these generated modules are buffered for install but NOT "
            "declared in GENERATED_RS_PATHS:\n  " + "\n  ".join(undeclared)
            + "\n  Add them there. Until you do, scripts/check-descriptor-drift.sh does not "
              "snapshot them and cannot see a re-emit rewrite them."
        )


# Directories a source scan must not walk: build output, vendored trees, and the mirror-gate
# canary, which holds DELIBERATE copies of descriptor-bearing sources (a scan that took those for
# real consumers would red on the fixtures whose whole job is to look real).
_SCAN_SKIP_DIRS = frozenset({
    ".git", ".lake", "target", "vendor", "node_modules", "tmp", "old-docs",
    "ts-sdk.archived", "mirror-gates",
})


def fp_bearing_sources() -> list[Path]:
    """Every Rust source that carries the FP CONVENTION: a `pub const X_{JSON,TSV}: &str =
    include_str!("../descriptors/…")` together with the paired `pub const X_FP: &str =
    "<sha256>"` that `compute_fp_rewrites` rewrites.

    A file with that convention and NO row in `RUST_FP_FILES` gets its FP constant left stale by
    the emit, is absent from the stamp's `fp_file_sha256`, and is not snapshotted by
    `check-descriptor-drift.sh` — three gates blind at once, silently."""
    fp_const = re.compile(r'pub const (\w+)_FP:\s*&str\s*=\s*"[0-9a-f]{64}"')
    found: list[Path] = []
    # `os.walk` with in-place pruning, NOT `rglob` — rglob enumerates every skipped tree before
    # the filter sees it, and `target/` alone makes that a minutes-long walk.
    for dirpath, dirnames, filenames in os.walk(ROOT):
        dirnames[:] = [d for d in dirnames if d not in _SCAN_SKIP_DIRS and not d.startswith(".")]
        for fn in filenames:
            if not fn.endswith(".rs"):
                continue
            path = Path(dirpath) / fn
            try:
                text = path.read_text()
            except (OSError, UnicodeDecodeError):
                continue
            if "descriptors/" not in text:
                continue
            bases = {
                c[:-5] if c.endswith("_JSON") else c[:-4]
                for c in const_to_file(text) if c.endswith(("_JSON", "_TSV"))
            }
            if bases & set(fp_const.findall(text)):
                found.append(path)
    return _drop_git_ignored(found)


def _drop_git_ignored(paths: list[Path]) -> list[Path]:
    """Filter out paths git IGNORES — one batched `git check-ignore`, no per-file subprocess.

    ⚑ IGNORED, not merely UNTRACKED. An FP-bearing source a lane has written but not yet `git
    add`-ed is exactly the case `assert_fp_files_declared` must still catch, so untracked files stay
    in. What must go are scratch checkouts that are ignored BY THE REPO'S OWN RULES: a lane parked a
    full second checkout at `headver/` (`.gitignore:147`), whose three FP-bearing sources wedged the
    whole ack-gated emit — a flag day blocked by another lane's scratch, with nothing wrong in the
    repo. An ignored tree is not part of the change-set this driver guards; `--list-guarded-paths`
    never names it and the provenance stamp never covers it.

    If `git` is unavailable the list is returned unfiltered — the gate stays STRICT on failure."""
    if not paths:
        return paths
    try:
        proc = subprocess.run(
            ["git", "-C", str(ROOT), "check-ignore", "--stdin"],
            input="\n".join(str(p) for p in paths),
            capture_output=True,
            text=True,
            check=False,
        )
    except OSError:
        return paths
    # exit 0 = some ignored, 1 = none ignored, 128 = not a repo / error -> keep everything.
    if proc.returncode not in (0, 1):
        return paths
    ignored = {line.strip() for line in proc.stdout.splitlines() if line.strip()}
    return [p for p in paths if str(p) not in ignored]


def assert_fp_files_declared() -> None:
    """Every FP-bearing Rust source must be DECLARED in `RUST_FP_FILES`.

    The twin of `assert_generated_declared`, on the other half of the change-set. `RUST_FP_FILES`
    is a hand list over a set that GROWS every time a descriptor gets a new Rust consumer, and a
    hand list over a growing set cannot go red — it just quietly covers less."""
    undeclared = sorted(
        str(p.relative_to(ROOT)) for p in fp_bearing_sources() if p not in RUST_FP_FILES
    )
    if undeclared:
        sys.exit(
            "emit_descriptors: these Rust sources carry the `*_FP` sha256 convention but are NOT "
            "declared in RUST_FP_FILES:\n  " + "\n  ".join(undeclared)
            + "\n  Add them there. Until you do, the emit never rewrites their FP constants, the "
              "PROVENANCE stamp does not cover them, and scripts/check-descriptor-drift.sh does "
              "not snapshot them — their pins can go stale with nothing red."
        )


def guarded_paths() -> list[str]:
    """The repo-relative paths this driver can REWRITE — `install_and_stamp`'s whole change-set:
    the descriptor directory, the Rust sources carrying generated `*_FP` constants, and the
    Lean-authored `*_generated.rs` modules. `check-descriptor-drift.sh` snapshots exactly this."""
    return [str(DESC.relative_to(ROOT))] + [
        str(p.relative_to(ROOT)) for p in (*RUST_FP_FILES, *GENERATED_RS_PATHS)
    ]


# ---- rustfmt normalization of the generated modules --------------------------
# The generated `.rs` files have TWO producers: this script (which writes them) and
# `scripts/git-hooks/pre-commit` (which rustfmt's every STAGED `.rs` on its way into a commit,
# `@generated` header or not — and CI's `cargo fmt --all -- --check` demands the same shape).
# While the two disagreed, the committed bytes were rustfmt's and the emitted bytes were ours,
# so `scripts/check-descriptor-drift.sh` could NEVER go green for such a file — a gate stuck red
# cannot catch the next real break. We converge here, at the generator: every generated module is
# emitted through rustfmt, so generator output == post-hook bytes == what `cargo fmt --check`
# accepts, BY CONSTRUCTION rather than by line-length luck.
#
# rustfmt is version-PINNED repo-wide (`rust-toolchain.toml`, `channel = nightly-2026-06-21`,
# `components = [… "rustfmt"]`), so this is as reproducible across machines as the `cargo fmt
# --check` gate already is. Missing rustfmt is a HARD FAILURE, never a silent skip: emitting
# unformatted bytes would make the drift gate report a fake drift.

def _rust_edition_for(path: Path) -> str:
    """The rustfmt edition for `path` — resolved EXACTLY as `scripts/git-hooks/pre-commit` and
    `cargo fmt` resolve it: nearest ancestor `Cargo.toml` with a `[package]` table, honouring
    `edition.workspace = true` against the root `[workspace.package]`. Hardcoding one edition
    would silently mis-format a module emitted into an edition-2021 crate (rustfmt's macro and
    `use` layout differ per edition), reopening the same two-producers disagreement."""
    import tomllib  # local: keeps --verify-provenance / --list-emitter-modules usable pre-3.11

    ws_edition = "2024"
    try:
        ws = tomllib.loads((ROOT / "Cargo.toml").read_text())
        ws_edition = str(ws.get("workspace", {}).get("package", {}).get("edition", ws_edition))
    except (OSError, tomllib.TOMLDecodeError):
        pass

    for d in path.resolve().parents:
        toml = d / "Cargo.toml"
        if not toml.is_file():
            continue
        try:
            pkg = tomllib.loads(toml.read_text()).get("package")
        except (OSError, tomllib.TOMLDecodeError):
            continue
        if pkg is None:
            continue
        ed = pkg.get("edition")
        if isinstance(ed, str):
            return ed
        if isinstance(ed, dict) and ed.get("workspace") is True:
            return ws_edition
        return "2015"  # a [package] with no edition — cargo's default
    return ws_edition


def normalize_generated_rust() -> None:
    """Run every buffered generated module through the pinned rustfmt, IN PLACE in GENERATED_RS.

    Single choke point on purpose: a future emitter that adds a module to `GENERATED_RS` cannot
    forget to format it. Runs before the install/no-op comparison so the bytes we diff against
    disk are the bytes we would write."""
    if not GENERATED_RS:
        return
    for path in list(GENERATED_RS):
        edition = _rust_edition_for(path)
        try:
            proc = subprocess.run(
                ["rustfmt", "--edition", edition, "--emit", "stdout"],
                input=GENERATED_RS[path],
                capture_output=True,
                text=True,
                cwd=str(path.parent if path.parent.is_dir() else ROOT),
            )
        except FileNotFoundError:
            sys.exit(
                "emit_descriptors: rustfmt NOT FOUND, but the generated Rust modules must be "
                "rustfmt-normalized to match the bytes the pre-commit hook and `cargo fmt --all "
                "-- --check` produce. Emitting unformatted bytes here would make the descriptor "
                "drift gate report a FAKE drift. Install the pinned toolchain "
                "(`rustup toolchain install \"$(grep -m1 '^channel' rust-toolchain.toml | "
                "cut -d'\"' -f2)\" --component rustfmt`) and re-run."
            )
        if proc.returncode != 0:
            sys.exit(
                f"emit_descriptors: rustfmt failed on the generated module "
                f"{path.relative_to(ROOT)} (edition {edition}) — the emitted Rust does not parse, "
                f"so it must not be installed.\n{proc.stderr.strip()}"
            )
        out = proc.stdout
        GENERATED_RS[path] = out if out.endswith("\n") else out + "\n"


def split_layout(stdout: str, _written):
    """The layout emitter prints a COMPLETE Rust module on stdout. Route it verbatim (it is the
    file's exact bytes). Sanity-gate the shape so a broken emit cannot silently install an empty
    or non-Rust layout module — this file is load-bearing for soundness, not decoration."""
    if (
        "@generated" not in stdout
        or "pub const EFFECT_VM_WIDTH" not in stdout
        or "pub const NUM_PRE_LIMBS" not in stdout
        or "pub const ROTATED_GROUP_TABLE" not in stdout
    ):
        sys.exit(
            "emit_descriptors: layout emitter output does not look like the generated Rust layout "
            "module (missing header, scalar spine, or verified group table)"
        )
    GENERATED_RS[LAYOUT_RS] = stdout if stdout.endswith("\n") else stdout + "\n"


def write_file(name: str, content: str, written: dict[str, str]):
    """BUFFER content for circuit/descriptors/<name>, asserting no two emitters
    disagree on a shared file (the attenuate fan-out emits the same bytes N times).
    Nothing touches disk until the install phase — a byte-CHANGING install is
    ack-gated there (see the module docstring)."""
    if name in written and written[name] != content:
        sys.exit(f"emit_descriptors: CONFLICT — two emissions disagree on {name}")
    written[name] = content


# ---- regen gate + provenance stamp + audit trail -----------------------------
# (docs/VK-REGEN-CONTROLS.md — controls 1–3)

def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_out(*args: str) -> str:
    return run(["git", *args], cwd=ROOT).stdout.strip()


def dregg2_tree_hash() -> str:
    """The git tree hash of the committed Lean source of truth."""
    return git_out("rev-parse", "HEAD:metatheory/Dregg2")


def dregg2_source_dirty() -> bool:
    """True when metatheory/Dregg2 has uncommitted or untracked edits — i.e. the
    emitting source is NOT the reviewed committed tree the hash names."""
    return bool(git_out("status", "--porcelain", "--", "metatheory/Dregg2"))


def emitter_source_closure() -> set[Path]:
    """Every in-tree `.lean` file the emitters import, TRANSITIVELY, plus the emitters themselves.

    `emitter_modules` stops at direct imports because `lake build` follows the rest; the
    cleanliness question cannot stop there, since a weakened lemma three imports down changes
    the emitted bytes as surely as an edit to the emitter. Out-of-tree imports (Mathlib, the
    toolchain) are pinned by `lake-manifest.json` / `lean-toolchain`, which `emit_source_dirt`
    checks directly."""
    seen: set[Path] = set()
    stack = [META / e for e in EMITTERS]
    while stack:
        path = stack.pop()
        if path in seen or not path.exists():
            continue
        seen.add(path)
        for line in path.read_text(errors="replace").splitlines():
            m = re.match(r"^import\s+([A-Za-z0-9_.]+)", line)
            if m:
                dep = META / (m.group(1).replace(".", "/") + ".lean")
                if dep.exists():
                    stack.append(dep)
    return seen


LAKE_CONFIG_FILES = ("lakefile.lean", "lakefile.toml", "lean-toolchain", "lake-manifest.json")


def emit_source_dirt() -> list[str]:
    """The uncommitted or untracked files that could change what the emitters print: members of
    `emitter_source_closure()` and the lake configuration. Empty means the emission is a function
    of committed source, which is the property the stamp claims."""
    closure = {p.resolve() for p in emitter_source_closure()}
    closure |= {(META / f).resolve() for f in LAKE_CONFIG_FILES}
    out = run(["git", "status", "--porcelain", "--untracked-files=all", "--", "metatheory"],
              cwd=ROOT).stdout
    dirt: list[str] = []
    for line in out.splitlines():
        rel = line[3:].split(" -> ")[-1].strip().strip('"')
        if (ROOT / rel).resolve() in closure:
            dirt.append(rel)
    return sorted(dirt)


def require_committed_emit_source(what: str) -> dict:
    """THE AUTOMATIC GATE: the emission must be a function of COMMITTED source.

    Codex round 3 (finding 8) named the attack the deleted ack was standing in front of: emit from
    an uncommitted, weakened Lean source, restore the source, commit only the generated bytes. Git
    then records bytes no committed source produces. Refusing to emit while any file that can
    reach the emitters is uncommitted closes that by construction, with no environment variable
    and no human: the stamp's tree hash names the source that minted the bytes. Returns the stamp's
    authorship record; exits EXIT_REFUSED (tree untouched) otherwise."""
    dirt = emit_source_dirt()
    if dirt:
        sys.stderr.write(
            f"\nemit_descriptors: EMIT REFUSED — {what}: {len(dirt)} file(s) in the emitters' "
            "source closure are uncommitted or untracked, so the emitted bytes would not be a "
            "function of committed source and the PROVENANCE stamp could not name what minted "
            "them:\n"
            + "".join(f"    {d}\n" for d in dirt[:20])
            + (f"    … and {len(dirt) - 20} more\n" if len(dirt) > 20 else "")
            + "\n  Commit the Lean first. There is no override. The tree was left UNTOUCHED.\n"
        )
        sys.exit(EXIT_REFUSED)
    return {"tree": dregg2_tree_hash(), "dirty": False, "head": git_out("rev-parse", "HEAD"),
            "closure_files": len(emitter_source_closure())}


def require_checkout_at(rev: str) -> None:
    """`--rev <rev>` on the EMIT path: the operator names the committed revision being stamped,
    and the checkout must BE that revision. The canonical emit host is a clean clone at a
    committed revision with its own warm `.lake` (docs/automata/BUILD.md, "Emit and stamp (C2)");
    a detached worktree of a shared tree has no `.lake`, and pointing one at a sibling's would
    rewrite oleans under it. So this does not create a tree; it refuses to stamp the wrong one."""
    try:
        want = git_out("rev-parse", "--verify", f"{rev}^{{commit}}")
    except subprocess.CalledProcessError:
        sys.exit(f"emit_descriptors: --rev '{rev}' does not resolve to a commit.")
    have = git_out("rev-parse", "HEAD")
    if want != have:
        sys.stderr.write(
            f"\nemit_descriptors: EMIT REFUSED — --rev {rev} is {want[:12]} but this checkout's "
            f"HEAD is {have[:12]}. Check out the revision you mean to stamp (a clean clone at "
            "that commit) and re-run. The tree was left UNTOUCHED.\n")
        sys.exit(EXIT_REFUSED)


def subdir_hash_legs(desc_hashes: dict[str, str]) -> dict[str, dict[str, str]]:
    """Every `<subdir>/<file>` key of the emission, split into its own `<subdir>_sha256` leg.

    ⚑ THE WRITE SIDE'S COUNTERPART TO `verify_provenance`'S DISCOVERY WALK (2026-08-01). The verify
    leg was taught to walk EVERY subdirectory of `circuit/descriptors/` by discovery — but
    `build_provenance` still special-cased `by-name/` alone, so the six tracked
    `circuit/descriptors/table-airs/*.json` landed in `descriptor_sha256` under a `table-airs/…`
    key while `table-airs_sha256` came out `null`. `--verify-provenance` then reported them BOTH
    ways at once: "recorded in the stamp but MISSING on disk" (the flat walk cannot find a
    slash-keyed name) and "on disk but NOT covered by the stamp". A stamp that cannot be verified
    attests nothing, so the two sides are made symmetric here: discovery on both.

    `by-name` is returned like any other subdirectory; `build_provenance` lifts it into its
    historical `by_name_sha256` key."""
    legs: dict[str, dict[str, str]] = {}
    for name, h in sorted(desc_hashes.items()):
        if "/" in name:
            sub, base = name.split("/", 1)
            legs.setdefault(sub, {})[base] = h
    return legs


def by_name_hashes_of(desc_hashes: dict[str, str]) -> dict[str, str]:
    """The by-name leg of the provenance stamp, sourced from the EMITTED content (via
    `desc_hashes`, which `install_and_stamp` computes over `written`) — NOT from disk.

    This used to be `collect_by_name_hashes()`, which read the bytes FROM DISK and stored them as
    `by_name_sha256`; `verify_provenance` then compared disk against a stamp computed from that same
    disk. Pure self-consistency, sold under a PASS that claimed Lean agreement — the exact fallacy
    `check-descriptor-drift.sh`'s own header disowns ("a `sha256(bytes) == committed-FP` rehash
    proves only that a file matches the hash committed beside it ... Re-deriving from Lean is the
    whole point"). Now that `EmitByName.lean` genuinely re-derives the by-name surface, the stamp is
    minted from Lean bytes and the verify leg stops being self-referential."""
    return {
        name.split("/", 1)[1]: h
        for name, h in sorted(desc_hashes.items())
        if name.startswith("by-name/")
    }


def build_provenance(mode: str, auth: dict,
                     desc_hashes: dict[str, str],
                     fp_hashes: dict[str, str]) -> dict:
    toolchain_file = META / "lean-toolchain"
    return {
        "version": 1,
        "mode": mode,  # always "emit": the hashes come from the Lean emitters, never from disk
        "dregg2_tree_hash": auth["tree"],
        "repo_head": auth["head"],
        "source_dirty": auth["dirty"],
        # The emitters' transitive in-tree Lean closure, checked clean before the emit and again
        # at install (`require_committed_emit_source`); the count is how many files that covered.
        "emitter_closure_clean": not auth["dirty"],
        "emitter_closure_files": auth.get("closure_files"),
        "lean_toolchain": (
            toolchain_file.read_text().strip() if toolchain_file.exists() else None
        ),
        "emitters": EMITTERS,
        "generated_utc": datetime.datetime.now(datetime.timezone.utc)
            .strftime("%Y-%m-%dT%H:%M:%SZ"),
        "operator": f"{getpass.getuser()}@{socket.gethostname()}",
        # The stamp keeps the two legs separate (flat basenames each), as it always has; the
        # SOURCE of the by-name leg is what changed — emitted Lean bytes, not a disk re-hash.
        "descriptor_sha256": {
            name: h for name, h in sorted(desc_hashes.items()) if "/" not in name
        },
        "by_name_sha256": by_name_hashes_of(desc_hashes),
        # every OTHER descriptor subdirectory, by DISCOVERY — the mirror of `verify_provenance`'s
        # own discovery walk, so a new subdirectory is stamped the day it appears.
        **{
            f"{sub}_sha256": leg
            for sub, leg in subdir_hash_legs(desc_hashes).items()
            if sub != "by-name"
        },
        "fp_file_sha256": dict(sorted(fp_hashes.items())),
    }


def write_provenance(prov: dict) -> None:
    (DESC / PROVENANCE_FILE).write_text(json.dumps(prov, indent=2) + "\n")


def provenance_stamp_gap(written: dict[str, str]) -> list[str]:
    """Why `PROVENANCE.json` does NOT already attest THIS emission — empty when it does.

    The stamp is an artifact this driver owns, and its obligation is not a byte diff: a descriptor
    can be byte-for-byte the Lean emission and still have NO row attesting it, which is the whole
    state PROVENANCE.json exists to make impossible. `install_and_stamp`'s `changed` list compares
    emitted bytes against disk and is structurally blind to that — so a byte-identical emission
    returned NO-OP and left the stamp short, permanently, with the ONLY escape being the
    since-deleted `--stamp-existing` (which re-stamped every file as a DISK re-hash, demoting
    `mode` from a Lean witness to a self-consistency check).
    MEASURED 2026-07-26: five tracked by-name descriptors — the four light-client verifiers and the
    DFA routing table, every one of them a live `include_str!` target in `descriptor_by_name.rs` —
    shipped unstamped while this driver printed NO-OP and exited 0.

    Compared against the EMISSION, not against disk, so a clean answer means "the stamp covers what
    Lean just emitted" rather than "the stamp is consistent with itself".

    The two DESCRIPTOR legs ONLY. `fp_file_sha256` pins SOURCE files (`effect_vm_descriptors.rs`
    among them) that legitimately change on any edit to their hand-written prose; folding that leg
    in here would demand an ack — and therefore RED the no-ack drift gate — after every unrelated
    source edit. It is a provenance snapshot, not a stable invariant, and the Rust mirror test
    (`provenance_json_pins_match_checked_in_descriptor_bytes`) excludes it for the same reason."""
    stamp_path = DESC / PROVENANCE_FILE
    if not stamp_path.exists():
        return [f"no {PROVENANCE_FILE} on disk — the descriptor set is UNSTAMPED"]
    try:
        prov = json.loads(stamp_path.read_text())
    except json.JSONDecodeError as exc:
        return [f"{PROVENANCE_FILE} does not parse ({exc}) — it attests nothing"]

    emitted = {name: sha256_hex(content.encode()) for name, content in written.items()}
    expected = {
        "descriptor_sha256": {
            name: h for name, h in emitted.items() if "/" not in name
        },
        "by_name_sha256": by_name_hashes_of(emitted),
        **{
            f"{sub}_sha256": leg
            for sub, leg in subdir_hash_legs(emitted).items()
            if sub != "by-name"
        },
    }
    findings: list[str] = []
    for leg, expect in expected.items():
        have = prov.get(leg)
        if not isinstance(have, dict):
            findings.append(f"{leg}: absent from the stamp (or not an object)")
            continue
        findings += [
            f"{leg}: `{n}` was emitted but has NO row in the stamp"
            for n in sorted(set(expect) - set(have))
        ]
        findings += [
            f"{leg}: `{n}` is pinned by the stamp but NO emitter produces it"
            for n in sorted(set(have) - set(expect))
        ]
        findings += [
            f"{leg}: `{n}` pin does not equal the emitted bytes"
            for n in sorted(set(expect) & set(have))
            if have[n] != expect[n]
        ]
    return findings


def current_schema_epoch() -> str:
    """`CANONICAL_STATE_SCHEMA_EPOCH` as the audit row's machine-readable trailer.

    ⚑ THIS SCRIPT IS NOT THE GATE, and must never become it. The epoch is a Rust constant ANY
    COMMIT CAN BUMP while only this function appends to the log, so a check placed here is blind
    to exactly the case that motivated it (`6441705e8` bumped 20 → 21 and ran no emit). The gate
    is `scripts/check-schema-epoch-log.py` + `dregg_persist::schema_epoch_log_row`, both keyed on
    the CONSTANT. All this does is stop an emit row from being the malformed one that trips them.
    """
    src = ROOT / "persist" / "src" / "lib.rs"
    hits = re.findall(r"^\s*pub const CANONICAL_STATE_SCHEMA_EPOCH: u64 = (\d+);",
                      src.read_text(errors="replace"), re.M) if src.exists() else []
    if len(hits) != 1:
        sys.exit(
            f"emit_descriptors: persist/src/lib.rs carries {len(hits)} definitions of "
            f"CANONICAL_STATE_SCHEMA_EPOCH; the audit row's `epoch:` trailer has no single value "
            f"to record. Refusing to append a row this repo's own gate cannot parse."
        )
    return f"epoch:{hits[0]}"


def append_audit(mode: str, auth: dict, changed: list[str]) -> None:
    """The AUDIT TRAIL: one git-tracked row per applied regen/stamp."""
    log = ROOT / AUDIT_LOG_REL
    if not log.exists():
        log.parent.mkdir(parents=True, exist_ok=True)
        log.write_text(
            "# VK-REGEN LOG — append-only audit trail of descriptor regen events\n"
            "\n"
            "Every authorized descriptor install / provenance stamp appends one row\n"
            "(written by `scripts/emit_descriptors.py`; see docs/VK-REGEN-CONTROLS.md).\n"
            "Rows are never edited or removed; git history is the tamper-evidence.\n"
            "\n"
            "## SCHEMA EPOCH LEDGER\n"
            "\n"
            "| epoch | set by | when (UTC) | what it re-genesised |\n"
            "|---|---|---|---|\n"
            "\n"
            "## EVENT ROWS\n"
            "\n"
            "| when (UTC) | operator | mode | HEAD:metatheory/Dregg2 | repo HEAD | source dirty "
            "| changed | epoch |\n"
            "|---|---|---|---|---|---|---|---|\n"
        )
    when = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    operator = f"{getpass.getuser()}@{socket.gethostname()}"
    shown = ", ".join(changed[:6]) + (f", … +{len(changed) - 6}" if len(changed) > 6 else "")
    # A BARE `|` inside a cell is not a column — it silently ends one. Four rows written before
    # 2026-08-01 carried unescaped pipes out of code spans (`d8 || iroot`, `lo | mid1<<8`) and
    # had therefore never rendered as table rows at all, in any reader.
    shown = shown.replace("|", r"\|")
    with log.open("a") as fh:
        fh.write(
            f"| {when} | {operator} | {mode} | {auth['tree']} | {auth['head']} "
            f"| {'YES' if auth['dirty'] else 'no'} | {shown or '(stamp only)'} "
            f"| {current_schema_epoch()} |\n"
        )


@contextlib.contextmanager
def rooted_at(new_root: Path):
    """Run a check body against a DIFFERENT checkout of this repo.

    ⚑ ONE BODY OF CHECK LOGIC, pointed somewhere else — never a second copy of it. `--rev` and
    the red-proof both need to grade a tree that is not the working tree, and the alternative
    (a parallel "read it out of git instead" implementation) is two readers of one question,
    which is the shape this whole file keeps finding bugs in. `ROOT`/`META`/`DESC`/
    `RUST_FP_FILES` are the only path anchors any verify leg consults, so rebinding those four
    moves every leg at once and a leg added later inherits it for free."""
    global ROOT, META, DESC, RUST_FP_FILES
    saved = (ROOT, META, DESC, RUST_FP_FILES)
    ROOT = new_root
    META = new_root / "metatheory"
    DESC = new_root / "circuit" / "descriptors"
    RUST_FP_FILES = [new_root / p.relative_to(saved[0]) for p in saved[3]]
    try:
        yield
    finally:
        ROOT, META, DESC, RUST_FP_FILES = saved


@contextlib.contextmanager
def detached_worktree(rev: str, label: str):
    """A DETACHED, `git status`-clean worktree at `rev`. Yields its path.

    ⚑ THIS IS THE ANSWER TO "THE ONLY CORRECT INVOCATION IS IMPOSSIBLE". Graded against the
    working tree, a provenance verify is at the mercy of ~10 co-tenant lanes: any sibling's
    in-flight descriptor emission reds it, and `metatheory/` is never clean in a live swarm, so
    the honest move was always to decline to run it. A gate whose only correct invocation is
    impossible under the conditions the repo actually operates in does not get fixed — it gets
    routed around, which is how the ten table-AIR stamps stayed wrong through two separate
    lanes noticing.

    So the churn-safe question is asked instead: are the COMMITTED bytes what the COMMITTED
    stamp pins? That is HEAD-vs-HEAD, always answerable, and it is the leg that catches drift.
    `scripts/check-descriptor-drift.sh --rev` and `scripts/check-guard-modules.py --rev` are the
    in-repo precedents; this mirrors the former (a worktree, not a `git archive` extract,
    because every verify leg here runs `git ls-files`/`git show HEAD:` and an archive extract
    has no `.git` — those legs would "degrade cleanly", i.e. silently stop being gates)."""
    try:
        sha = git_out("rev-parse", "--verify", f"{rev}^{{commit}}")
    except subprocess.CalledProcessError:
        sys.exit(f"{label}: FATAL — '{rev}' does not resolve to a commit.")
    # ⚠ `.resolve()` IS LOAD-BEARING, not tidiness. macOS hands out `/var/folders/...` temp dirs
    # and `/var` is a symlink to `/private/var`, so an unresolved ROOT compares unequal to every
    # `Path.resolve()`d child of itself — and `verify_workflow_refs`'s containment test then
    # reports that EVERY workflow-invoked path "resolves OUTSIDE this repository". Measured: 20
    # false WORKFLOW-ESCAPES-REPO findings on a worktree of a tree that has none. A `--rev` run
    # that manufactures its own reds is worse than one that does not run.
    holder = Path(tempfile.mkdtemp(prefix="verify-provenance-rev-")).resolve()
    wt = holder / "tree"
    try:
        add = subprocess.run(["git", "-C", str(ROOT), "worktree", "add", "--detach",
                              str(wt), sha], capture_output=True, text=True)
        if add.returncode != 0:
            sys.exit(f"{label}: FATAL — could not create a detached worktree at {wt}\n"
                     f"{add.stderr.strip()}")
        # ⚠ VERIFY the clean guarantee rather than assuming it. A worktree that is somehow
        # dirty is a `--rev` run grading churn again, which is the whole thing this stops.
        dirt = subprocess.run(["git", "-C", str(wt), "status", "--porcelain"],
                              capture_output=True, text=True).stdout.strip()
        if dirt:
            sys.exit(f"{label}: FATAL — the fresh worktree is NOT clean; refusing to grade "
                     f"it.\n" + "\n".join(dirt.splitlines()[:10]))
        yield wt, sha
    finally:
        subprocess.run(["git", "-C", str(ROOT), "worktree", "remove", "--force", str(wt)],
                       capture_output=True, text=True)
        shutil.rmtree(holder, ignore_errors=True)


def verify_provenance(rev: str | None = None) -> None:
    """--verify-provenance [--rev <rev>]: the PROVENANCE check a consumer runs before trusting the
    descriptor set.

    Recomputes every hash against the stamp and refuses a stamp minted from an uncommitted
    source or not witnessed by the emitters. `--rev` grades that revision in a clean detached
    worktree (see `detached_worktree`)."""
    if rev is None:
        _verify_provenance_body(where="the working tree")
        return
    with detached_worktree(rev, "verify-provenance") as (wt, sha):
        print(f"verify-provenance: grading {rev} ({sha[:12]}) in a detached worktree "
              f"(the shared working tree is NOT read)")
        with rooted_at(wt):
            _verify_provenance_body(where=f"{rev} ({sha[:12]})")


def _verify_provenance_body(where: str) -> None:
    """Compute, report, and turn into an exit code."""
    failures, checked = _verify_provenance_findings()
    if failures:
        sys.stderr.write(f"verify-provenance: FAIL ({where})\n")
        for f in failures:
            sys.stderr.write(f"  - {f}\n")
        sys.exit(1)
    legs = " + ".join(f"{n} {kind}" for kind, n in sorted(checked.items()) if n)
    print(
        f"verify-provenance: PASS — {sum(checked.values())} artifacts match the stamp "
        f"[{legs}] over {where} (mode={_LAST_MODE[0]}, "
        f"tree {_LAST_TREE[0][:12]}…, source_dirty={_LAST_DIRTY[0]})."
    )


# The stamp fields the PASS line reports. Held beside the findings rather than returned with
# them so the self-test — which compares FINDING SETS — is not coupled to the report's shape.
_LAST_MODE: list = [None]
_LAST_TREE: list = [""]
_LAST_DIRTY: list = ["?"]


def _verify_provenance_findings(doors: bool = True) -> tuple[list[str], dict[str, int]]:
    """The whole check as DATA: (findings, per-leg counts). Empty findings == clean.

    Split out from the reporting so the red-proof can compare finding SETS rather than exit
    codes. That is not a convenience — it is what keeps the red-proof runnable. ~10 lanes share
    this tree, HEAD carries whatever they landed in the last hour, and a red-proof phrased as
    "clean tree goes GREEN, mutated tree goes RED" is hostage to every one of them: at the time
    of writing a sibling's `EmitByName.lean` routes an artifact nobody committed, which is a real
    finding and would fail the CONTROL case of a green/red proof through no fault of the subject.
    A red-proof that a co-tenant can disable is furniture within the hour.
    So the proof measures the DELTA the injected fault causes against whatever the baseline is —
    which is strictly sharper anyway: it pins the exact finding to the exact mutation, instead of
    accepting any red at all as evidence."""
    stamp_path = DESC / PROVENANCE_FILE
    if not stamp_path.exists():
        sys.exit(f"verify-provenance: FAIL — no {stamp_path} (unstamped descriptor set)")
    prov = json.loads(stamp_path.read_text())
    failures: list[str] = []
    # Per-leg tallies, so the PASS line reports what was actually CHECKED. It used to add
    # `descriptor_sha256` + `by_name_sha256` and print that as the whole number — which is how
    # `table-airs/` managed to be simultaneously covered by this function (the discovery walk
    # below reaches it) and INVISIBLE in its own PASS line: eleven shared table AIRs, the
    # Poseidon2 chip every descriptor's hash sites lower into among them, checked and unreported.
    # A gate that under-reports its own coverage cannot be audited for the coverage it lacks.
    checked: dict[str, int] = {}
    # ⚑ THE SNAPSHOT LEG, held apart from the invariant legs. See `_FP_LEG_NOTE` below.
    snapshot: list[str] = []

    def check_set(kind: str, recorded: dict[str, str],
                  on_disk: dict[str, Path], sink: list[str] | None = None) -> None:
        sink = failures if sink is None else sink
        checked[kind] = len(set(recorded) | set(on_disk))
        for name, want in recorded.items():
            p = on_disk.get(name)
            if p is None:
                sink.append(f"{kind}: {name} recorded in the stamp but MISSING on disk")
            elif sha256_hex(p.read_bytes()) != want:
                sink.append(f"{kind}: {name} does NOT match its stamped sha256")
        for name in on_disk:
            if name not in recorded:
                sink.append(f"{kind}: {name} on disk but NOT covered by the stamp")

    check_set("descriptor", prov.get("descriptor_sha256", {}), {
        p.name: p for p in DESC.iterdir()
        if p.is_file() and p.name != PROVENANCE_FILE and p.name not in COVERAGE_EXEMPT
    })
    by_name = DESC / "by-name"
    check_set("by-name", prov.get("by_name_sha256", {}), {
        p.name: p for p in by_name.iterdir() if p.is_file()
    } if by_name.is_dir() else {})

    # ⚑ EVERY OTHER SUBDIRECTORY, BY DISCOVERY — not by name.
    #
    # The two walks above are a top-level `iterdir()` plus ONE hardcoded subdirectory, so a new
    # descriptor subdirectory is invisible to the provenance stamp until somebody remembers to add a
    # line here. `table-airs/` (the Lean-emitted shared table AIRs, first consumer: the deployed
    # double-spend gate) landed 2026-08-01 and was exactly that — constraints of a live gate sitting
    # in a JSON the stamp did not hash.
    #
    # ⚠ This is the same shape as the hole that once let `by-name/predicate-arith.json` drift. Fixed
    # by DISCOVERY: anything under `circuit/descriptors/` that is not already covered above is walked.
    # A future subdirectory is stamped the day it appears, with nobody needing to remember.
    covered_dirs = {"by-name"}
    for sub in sorted(d for d in DESC.iterdir() if d.is_dir() and d.name not in covered_dirs):
        key = f"{sub.name}_sha256"
        check_set(sub.name, prov.get(key, {}), {
            p.name: p for p in sub.iterdir() if p.is_file()
        })
    check_set("fp-file", prov.get("fp_file_sha256", {}), {
        str(p.relative_to(ROOT)): p for p in RUST_FP_FILES if p.exists()
    }, sink=snapshot)

    # NON-VACUITY FLOOR, and it runs HERE — before the routing leg, before any verdict. Every
    # count above is derived from a directory walk and a JSON object, and both can come back
    # empty (a moved descriptor dir, a stamp whose legs are `{}`), in which case the loops above
    # iterate over nothing and this function reports PASS. That is the one way it goes green
    # while checking air, so it is refused explicitly rather than left to be noticed.
    if not any(checked.get(k) for k in ("descriptor", "by-name")):
        sys.exit(
            "verify-provenance: FATAL — the descriptor and by-name legs BOTH derived empty "
            f"(checked={checked}). Nothing was compared; this would have been a vacuous PASS. "
            f"The walk is broken (is {DESC} the descriptor directory?), not the stamp."
        )

    # The ROUTING leg (static; no Lean run). The three checks above all start from a file
    # that EXISTS and ask whether the stamp covers it — so a name the Lean routing table
    # authors with no artifact behind it is invisible to every one of them.
    #
    # ⚠ `doors=False` IS FOR THE RED-PROOF ONLY, and it is safe there for a stated reason, not a
    # hopeful one: these legs read `metatheory/*.lean` (2300 files), tracked `*.rs` (4344) and
    # `.github/workflows/*.yml` — and the red-proof mutates NONE of those. It touches exactly
    # three things: descriptor bytes under a subdirectory, a `<subdir>_sha256` row, and
    # `source_dirty`. No door leg reads any of the three (`verify_by_name_routing`'s stamp read is
    # `by_name_sha256`, which the proof never edits). Re-running them once per injected fault cost
    # ~25s each and measured nothing — 8 identical scans — which is how a red-proof grows past its
    # budget and starts reporting TIMEOUT, and a timeout is not a verdict. The proof still makes
    # ONE full-path run (doors on) so this argument cannot silently become false.
    if doors:
        failures.extend(verify_by_name_routing())

    # ⚑ `source_dirty` is a property of the COMMITTED STAMP: always answerable, at any revision,
    # by reading one boolean. The emit can no longer write `true` (it refuses an uncommitted
    # closure, `require_committed_emit_source`), so a `true` here is a stamp from before
    # 2026-11-06 or a hand edit, and either way it attests a source nobody can reconstruct.
    if prov.get("source_dirty"):
        failures.append(
            "the stamp records source_dirty=true — these artifacts were minted from an "
            "uncommitted Lean tree, so the stamp attests a source nobody can reconstruct. "
            "Re-emit from a committed closure (`scripts/emit_descriptors.py` refuses otherwise)."
        )
    # ⚑ A stamp must be a LEAN WITNESS. `mode` other than "emit" was the deleted
    # `--stamp-existing` path: a re-hash of whatever bytes were on disk, which attests only that
    # the files match themselves. It is refused here so its deletion loses no detection.
    if prov.get("mode") != "emit":
        failures.append(
            f"the stamp records mode={prov.get('mode')!r}, not 'emit' — its hashes were read off "
            "disk rather than produced by the Lean emitters, so it attests nothing about Lean. "
            "Re-emit (`scripts/emit_descriptors.py`)."
        )

    # The tree-hash ceremony clause (stamp tree == this checkout's HEAD:metatheory/Dregg2) was
    # `--strict`-only and is deleted with `--strict` (2026-11-06): that tree hash moves on any
    # commit to any Lean module, so it was never a standing gate. Staleness w.r.t. Lean is
    # answered by RE-DERIVING (`scripts/check-descriptor-drift.sh`), not by comparing hashes.

    # ⚑ THE SNAPSHOT LEG IS A CEREMONY CLAUSE, not a standing one — and this is a CORRECTION of a
    # misclassification, not a relaxation. `fp_file_sha256` pins whole SOURCE files. The repo had
    # already settled what that means, in the docstring of the one provenance check that runs:
    #
    #     "`fp_file_sha256` is deliberately NOT checked here: it pins SOURCE files (this file
    #      among them) that change on every legitimate edit, so it is a provenance SNAPSHOT, not
    #      a stable invariant — rigging it would make the test red on every source change."
    #      — effect_vm_descriptors.rs, provenance_json_pins_match_checked_in_descriptor_bytes
    #
    # `provenance_stamp_gap` excludes it for the same reason, in the same words. This function was
    # the third reader and the only one that hard-failed on it. MEASURED 2026-08-02:
    # `effect_vm_descriptors.rs` took SIXTEEN commits in seven days — it is the hottest file in
    # the set — so as a standing gate this clause is red after essentially any Rust edit, until
    # somebody re-stamps. Found the honest way: the first run of this gate from a clean detached
    # checkout reported it against the very commit that wired the gate in.
    #
    # ⚠ NOTHING IS LESS COVERED. The substantive invariant those files carry — that each `*_FP`
    # constant equals the sha256 of the descriptor JSON it pins — is NOT this leg; it is
    # `every_descriptor_fp_matches_its_json_bytes`, which runs on every `cargo test -p
    # dregg-circuit`, cannot rot, and is untouched. This leg answers a different question ("is the
    # stamp's snapshot of these five source files current?"), which is a RE-STAMP obligation and
    # is a re-stamp obligation (the next emit rewrites it automatically). It is never SILENT.
    if snapshot:
        print("verify-provenance: fp-file SNAPSHOT is stale (a re-stamp obligation the next emit "
              "discharges, NOT descriptor drift; the *_FP↔JSON invariant is gated by "
              "`every_descriptor_fp_matches_its_json_bytes` on every cargo test):")
        for s in snapshot:
            print(f"  · {s}")

    _LAST_MODE[0] = prov.get("mode")
    _LAST_TREE[0] = str(prov.get("dregg2_tree_hash"))
    _LAST_DIRTY[0] = "true" if prov.get("source_dirty") else "false"
    return failures, checked


# ---- the by-name ROUTING round-trip (STATIC — no Lean run) -------------------
#
# `EmitByName.lean`'s `byNameDescriptors` is the routing table for the whole
# `circuit/descriptors/by-name/` surface. Until this check, only ONE of its two
# directions was gated, and only by machinery that needs a full Lean emit:
#
#   * file-on-disk -> table: the coverage check in `main()` fails on a by-name file no
#     emitter reproduces. Needs the emit (hours of `lake build`) to say anything.
#   * table -> file-on-disk: NOTHING. A name added to the table whose artifact was never
#     committed is a GHOST — the emit would mint it, but until the emit runs the routing
#     table advertises a descriptor that does not exist, `descriptor_by_name.rs` cannot
#     serve it, and no byte-pin covers it. The `#guard byNameDescriptors.length == N` in
#     the Lean file counts the ghost as a member, so it passes. `--verify-provenance` and
#     the derived-coverage test in `circuit/src/effect_vm_descriptors.rs` both start from
#     files that EXIST, so a ghost gives them nothing to notice.
#
# This closes it from the OTHER end: parse the table's name literals out of the .lean
# source (they are string literals — no Lean toolchain needed) and reconcile them against
# the tracked/on-disk directory and the PROVENANCE stamp. It therefore keeps working while
# the emit is blocked, which is exactly when a routing gap can sit unnoticed.
#
# The parse is STRUCTURE-CHECKED, never best-effort: it must find the decl, must find the
# terminator, must produce one name per list opener, and must agree with the Lean file's
# own machine-checked `#guard byNameDescriptors.length == N`. Any of those failing is a
# loud FATAL ("the table's shape moved; re-point this parser"), never a quiet pass — same
# rule the COVERAGE_EXEMPT mirror in `circuit/src/effect_vm_descriptors.rs` follows.
BY_NAME_ROUTER = "EmitByName.lean"                     # relative to META
BY_NAME_TABLE_DECL = "def byNameDescriptors : List (String × EffectVmDescriptor2) :="
_BY_NAME_TERM = re.compile(r"^[ \t]*\][ \t]*$", re.M)
_BY_NAME_OPENER = re.compile(r"^[ \t]*[\[,][ \t]*\(", re.M)
_BY_NAME_NAMED = re.compile(r"^[ \t]*[\[,][ \t]*\(\s*\"([^\"\n]*)\"\s*,", re.M)
# The table's own machine-checked length pin, in EITHER form. It was a `#guard` and is now a NAMED
# THEOREM (`byNameDescriptors_length`, `EmitByName.lean`) per the repo's guard discipline — a
# `#guard` leaves no term, so the pin this parser leans on had no reusable content and was invisible
# to axiom accounting. Both spellings are accepted so the reader does not become the reason the
# conversion cannot happen; the theorem form is the one to write.
_BY_NAME_GUARD = re.compile(
    r"#guard\s+byNameDescriptors\.length\s*==\s*(\d+)"
    r"|theorem\s+byNameDescriptors_length\s*:\s*byNameDescriptors\.length\s*=\s*(\d+)"
)


def parse_by_name_routing() -> list[str]:
    """The filenames `EmitByName.lean`'s routing table claims to author, in table order.

    A STATIC parse of the .lean source. Fails loudly (never silently returns a short or
    empty list) if the table's shape has moved past what this parser understands."""
    path = META / BY_NAME_ROUTER
    fatal = (
        f"emit_descriptors: {path} — the by-name routing table's shape moved past this "
        "parser. Re-point it (do NOT hand-copy the filename list); a routing check that "
        "cannot read the table must not report a pass."
    )
    if not path.exists():
        sys.exit(f"emit_descriptors: by-name router missing: {path}")
    src = path.read_text()
    start = src.find(BY_NAME_TABLE_DECL)
    if start < 0:
        sys.exit(f"{fatal}\n  (declaration `{BY_NAME_TABLE_DECL}` not found)")
    rest = src[start + len(BY_NAME_TABLE_DECL):]
    term = _BY_NAME_TERM.search(rest)
    if not term:
        sys.exit(f"{fatal}\n  (the table literal is unterminated — no closing `]` line)")
    body = rest[: term.start()]

    names = _BY_NAME_NAMED.findall(body)
    openers = len(_BY_NAME_OPENER.findall(body))
    if openers != len(names):
        sys.exit(
            f"{fatal}\n  ({openers} list entries but {len(names)} parsed filename "
            "literals — an entry's first component is not a plain string literal)"
        )
    if not names:
        sys.exit(f"{fatal}\n  (parsed ZERO entries — this check would be vacuous)")

    dupes = sorted({n for n in names if names.count(n) > 1})
    if dupes:
        sys.exit(
            f"emit_descriptors: {path} routes duplicate filename(s) {dupes} — two table "
            "entries claim sole authorship of the same artifact"
        )
    bad = sorted(n for n in names if not n.endswith(".json"))
    if bad:
        sys.exit(f"emit_descriptors: {path} routes non-.json key(s) {bad}")

    # Cross-check against the table's OWN machine-checked length guard. Lean verifies that
    # literal at build time, so it is independent ground truth for "how many entries are
    # there" — agreeing with it is what proves this parse saw all of them and no more.
    guard = _BY_NAME_GUARD.search(src)
    if not guard:
        sys.exit(
            f"{fatal}\n  (no `theorem byNameDescriptors_length : byNameDescriptors.length = N` "
            "and no legacy `#guard` — the parse has nothing independent to check itself against)"
        )
    pinned = guard.group(1) or guard.group(2)
    if int(pinned) != len(names):
        sys.exit(
            f"emit_descriptors: {path} — parsed {len(names)} routing entries but the "
            f"file's own length pin says {pinned}. Either the pin is stale (Lean would catch "
            "that at build time) or this parser is missing entries. Refusing to report on a "
            "table it may be reading wrong."
        )
    return names


def by_name_present() -> tuple[set[str], str]:
    """The by-name artifacts that count as CHECKED IN, plus a label for which set it is.

    TRACKED (`git ls-files`) by preference, matching the choice made in
    `circuit/src/effect_vm_descriptors.rs`: ~10 lanes share this tree, so `by-name/`
    routinely holds another lane's untracked scratch emission, and an untracked file is not
    yet a claim about what ships. Falls back to the on-disk listing where there is no git
    index (a vendored export, or the rsync'd remote build lane `scripts/pbuild`, which
    excludes `.git/`) — STRICTER, never weaker — and the label says which, so a red in a
    `.git`-less tree is never mistaken for a red in the repo."""
    try:
        out = subprocess.run(
            ["git", "-C", str(ROOT), "ls-files", "-z", "--", "circuit/descriptors/by-name"],
            capture_output=True, text=True,
        )
        if out.returncode == 0:
            tracked = {p.rsplit("/", 1)[-1] for p in out.stdout.split("\0") if p}
            if tracked:
                return tracked, "tracked by git"
    except OSError:
        pass
    return by_name_on_disk(), "present on disk (NO git index here — untracked files count too)"


def by_name_on_disk() -> set[str]:
    d = DESC / "by-name"
    return {p.name for p in d.iterdir() if p.is_file()} if d.is_dir() else set()


def verify_by_name_routing() -> list[str]:
    """The ROUND TRIP, both directions: every name the Lean routing table authors lands as
    a checked-in file carrying a provenance row, and every checked-in by-name file is
    routed. Returns the finding lines (empty == clean); prints a one-line summary."""
    routed = parse_by_name_routing()
    routed_set = set(routed)
    present, source = by_name_present()
    on_disk = by_name_on_disk()
    stamp_path = DESC / PROVENANCE_FILE
    pinned: set[str] | None = None
    if stamp_path.exists():
        pinned = set(json.loads(stamp_path.read_text()).get("by_name_sha256", {}))

    findings: list[str] = []

    # (1) THE GHOST: routed, but no such file exists anywhere. The class nothing else can
    # see — every other gate starts from a file and asks whether it is covered.
    for n in sorted(routed_set - on_disk):
        findings.append(
            f"GHOST: {BY_NAME_ROUTER} routes `{n}`, which exists NOWHERE under "
            f"circuit/descriptors/by-name/ — the table advertises a descriptor nobody "
            f"committed. Either commit the artifact (re-run the emit ceremony) or drop "
            f"the routing entry; this is the routing entry's AUTHOR's call."
        )

    # (2) routed + on disk + not tracked: a lane mid-flight. Reported, not failed — the
    # file is not yet a claim (same reasoning as by_name_present). Silence here is how a
    # scratch emission graduates to HEAD via a co-tenant `commit -a` with nobody looking.
    inflight = sorted((routed_set & on_disk) - present)

    # (3) the other direction: a checked-in by-name file the table does not author. The
    # emit's coverage check catches this too — but only by RUNNING the emit.
    for n in sorted(present - routed_set):
        findings.append(
            f"UNROUTED: circuit/descriptors/by-name/{n} is checked in ({source}) but no "
            f"{BY_NAME_ROUTER} entry authors it — its bytes are not re-derivable from Lean "
            f"(the ungated hand-transcription hop `predicate-arith.json` drifted through)."
        )

    # (4) the third leg: routed AND checked in, but no provenance row — nothing
    # operator-facing attests those bytes.
    if pinned is not None:
        for n in sorted((routed_set & present) - pinned):
            findings.append(
                f"UNSTAMPED: circuit/descriptors/by-name/{n} is routed and checked in "
                f"({source}) but has no PROVENANCE.json `by_name_sha256` row — it landed "
                f"without re-stamping. Fix at the SOURCE (the emit/stamp ceremony, see "
                f"docs/VK-REGEN-CONTROLS.md); do NOT hand-add rows."
            )

    print(
        f"verify-by-name-routing: {len(routed)} routed / {len(present)} checked in "
        f"({source}) / {len(pinned) if pinned is not None else 0} stamped"
        + (f" · {len(inflight)} routed-but-untracked (in flight): {', '.join(inflight)}"
           if inflight else "")
    )

    # THE SECOND DOOR — see verify_include_targets. The Lean table is one way an artifact gets
    # claimed; a Rust `include_str!` is the other, and the four legs above cannot see it.
    findings.extend(verify_include_targets())
    # ...and the same door one language over: a committed `import` of an uncommitted module.
    findings.extend(verify_lean_imports())
    # ...and THE FOURTH: a committed workflow step that runs an uncommitted script. Wired HERE,
    # into the leg that already owns "a committed reference to an uncommitted target", rather than
    # as a fifth CI job — this one invocation is what `scripts/check-descriptor-drift.sh` runs as
    # its ~1s preflight and what the `descriptor-by-name-routing` job runs, so the fourth medium
    # inherits both positions the moment it is added and nothing has to remember to call it.
    findings.extend(verify_workflow_refs())

    sys.stdout.flush()  # so the summary precedes the findings this returns (stderr)
    return findings


# ---- THE SECOND DOOR: `include_str!` / `include_bytes!` of an artifact -------------------
#
# `verify_by_name_routing` above reconciles the LEAN routing table against the checked-in
# by-name set. It cannot see the other way an artifact gets claimed: a Rust
# `include_str!("../descriptors/by-name/X.json")`. That macro is resolved by rustc at COMPILE
# time, so an absent or untracked target is not a soft drift — the crate does not build, and
# every crate downstream of it does not build. Both directions of that were live at once:
#
#   * INCLUDE-GHOST — the target exists NOWHERE. An unconditional compile break for everyone.
#   * INCLUDE-UNTRACKED — the target exists on the author's disk but is not tracked by git.
#     Green for the lane that emitted it, RED for every co-tenant and every fresh clone. This
#     is the direction nothing else in the tree can see: the Lean door treats an on-disk
#     untracked artifact as "in flight" and (correctly, for ITS question) stays quiet, the
#     emit's coverage check walks files that exist, and `cargo check` on the author's box
#     passes. It shipped exactly this way — `descriptor_by_name.rs` include_str'd
#     `dfa-routing-table-exact-public-v1.json` while the artifact was uncommitted.
#
# Deliberately NOT scoped to descriptors. An absent `include_str!` target is a compile break
# whatever the file is, and scoping the class to `circuit/descriptors/` would have made the
# check a description of the one instance we happened to find rather than of the shape.
#
# Reads the WORKING TREE of tracked `*.rs` (not `HEAD:`) on purpose: the ~1s preflight in
# `scripts/check-descriptor-drift.sh` is meant to catch this BEFORE the commit lands. In CI the
# two are the same bytes.
_INCLUDE_MACRO = re.compile(r'\binclude_(?:str|bytes)!\s*\(\s*"((?:[^"\\]|\\.)*)"\s*,?\s*\)')
# Non-literal forms (`concat!(env!("OUT_DIR"), ..)`, a macro-built path). Nothing here can
# resolve those, so they are COUNTED and reported rather than silently dropped — a growing
# count is the signal that this check's coverage is shrinking.
_INCLUDE_MACRO_ANY = re.compile(r'\binclude_(?:str|bytes)!\s*\(')

INCLUDE_SCAN_EXCLUDED_DIRS = (
    # `scripts/mirror-gates/canary/` is the mirror gate's OWN falsification corpus: hand-written
    # .rs fixtures that must EXHIBIT the flaw shapes `scripts/mirror-gates/mirror_gates.py`
    # hunts for, so that a gate which stopped detecting them reds. No cargo target compiles
    # them (they are not in any crate), and `A2__circuit-prove__tests__self_golden.rs`
    # include_str's a `canary.json` that deliberately does not exist. Named here, with the
    # reason, rather than skipped by some generic "looks like a fixture" rule — an exclusion
    # from a build gate is a decision that belongs on the record.
    "scripts/mirror-gates/canary/",
)


def _rust_comment_spans(text: str, path: str) -> tuple[list[tuple[int, int]], list[tuple[int, int]]]:
    """Lex `text` as Rust far enough to return (comment spans, string spans).

    Needed because a regex alone cannot tell code from prose: `hints/benches/criterion.rs:11`
    carries a COMMENTED-OUT `include_str!("big_committee.json")` whose target is genuinely
    absent, and a check that reds on it is a check people learn to ignore. Handles line and
    (nested) block comments, plain/byte/raw strings, and the char-literal-vs-lifetime
    ambiguity (`'a'` vs `'static`).

    FATAL on an unterminated comment or string: that is a real syntax error, and a lexer that
    guessed past it would be reporting on a file it read wrong."""
    comments: list[tuple[int, int]] = []
    strings: list[tuple[int, int]] = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == "/" and i + 1 < n and text[i + 1] == "/":
            j = text.find("\n", i)
            j = n if j < 0 else j
            comments.append((i, j))
            i = j
        elif c == "/" and i + 1 < n and text[i + 1] == "*":
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/*", j):
                    depth += 1; j += 2
                elif text.startswith("*/", j):
                    depth -= 1; j += 2
                else:
                    j += 1
            if depth:
                sys.exit(
                    f"emit_descriptors: {path} — unterminated /* block comment (depth "
                    f"{depth} at EOF). This lexer will not report on a file it cannot read."
                )
            comments.append((i, j))
            i = j
        elif c == "r" or (c == "b" and text.startswith("br", i)):
            # raw string: r"..", r#".."#, br"..", br#".."#  — else an ordinary identifier
            k = i + (2 if c == "b" else 1)
            h = 0
            while k + h < n and text[k + h] == "#":
                h += 1
            if k + h < n and text[k + h] == '"':
                close = '"' + "#" * h
                j = text.find(close, k + h + 1)
                if j < 0:
                    sys.exit(f"emit_descriptors: {path} — unterminated raw string literal.")
                strings.append((i, j + len(close)))
                i = j + len(close)
            else:
                i += 1
        elif c == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                elif text[j] == '"':
                    break
                else:
                    j += 1
            if j >= n:
                sys.exit(f"emit_descriptors: {path} — unterminated string literal.")
            strings.append((i, j + 1))
            i = j + 1
        elif c == "'":
            # char literal (`'a'`, `'\n'`, `'\u{1F600}'`) vs lifetime/label (`'a`, `'static:`).
            if i + 1 < n and text[i + 1] == "\\":
                # An escape's LENGTH is decided by its FORM, never by scanning for the next
                # `'`: in `b'\\'` the char after the backslash IS a backslash, and a scanner
                # that treats it as opening another escape steps OVER the closing quote and
                # swallows the file to the next tick — which is how this lexer read
                # `circuit-prove/tests/law1_enforcement_gate.rs` as an unterminated string and
                # FATALed the whole descriptor gate. `\u{..}` is the one variable-length form.
                if text.startswith("u{", i + 2):
                    j = text.find("}", i + 4)
                    end = j + 2 if j >= 0 else -1
                else:
                    end = i + 4  # `'` `\` <one escape char> `'`
                if end < 0 or end > n or text[end - 1] != "'":
                    sys.exit(
                        f"emit_descriptors: {path} — unterminated char literal at offset {i} "
                        f"({text[i:i + 12]!r}). This lexer will not report on a file it cannot read."
                    )
                strings.append((i, end))
                i = end
            elif i + 2 < n and text[i + 2] == "'":
                strings.append((i, i + 3))
                i += 3
            else:
                i += 1  # a lifetime — consume only the tick
        else:
            i += 1
    return comments, strings


def _tracked_rust_files() -> tuple[list[str], bool]:
    """Tracked `*.rs` paths (repo-relative), and whether a git index answered.

    Without a git index (a vendored export, or the rsync'd remote build lane `scripts/pbuild`,
    which excludes `.git/`) the UNTRACKED leg is not computable — the caller degrades that leg
    and says so, same label discipline as `by_name_present`."""
    try:
        out = subprocess.run(
            ["git", "-C", str(ROOT), "ls-files", "-z", "--", "*.rs"],
            capture_output=True, text=True,
        )
        if out.returncode == 0:
            files = [p for p in out.stdout.split("\0") if p]
            if files:
                return files, True
    except OSError:
        pass
    return sorted(
        p.relative_to(ROOT).as_posix()
        for p in ROOT.rglob("*.rs")
        if p.is_file() and ".git/" not in p.as_posix() and "/target/" not in p.as_posix()
    ), False


def _reference_is_committed(path: str, needle: str) -> bool:
    """Does HEAD's version of `path` already contain `needle`?

    The three-way split both doors below use — and the one `verify_by_name_routing` already
    used for artifacts (its `inflight` list) — turns on this. A reference to an untracked file
    is a BROKEN HEAD if the reference itself is committed, and a lane MID-AUTHORING if it is
    not. Conflating them either lets a real break pass or reds every lane that is writing a new
    module, and a gate that cries wolf during normal authoring is a gate people route around.

    In CI nothing is uncommitted, so working tree == HEAD and every finding is a real break:
    the distinction costs the gate no teeth where it matters."""
    out = subprocess.run(
        ["git", "-C", str(ROOT), "show", f"HEAD:{path}"],
        capture_output=True, text=True,
    )
    if out.returncode != 0:
        return False  # not in HEAD at all -> the reference cannot be committed
    return needle in out.stdout


def verify_include_targets() -> list[str]:
    """Every literal `include_str!`/`include_bytes!` target in tracked Rust must EXIST, and must
    be TRACKED wherever the include itself is already committed. Returns finding lines (empty ==
    clean); prints a one-line summary naming any in-flight (uncommitted-include) pairs."""
    files, have_index = _tracked_rust_files()
    tracked_paths: set[str] = set()
    if have_index:
        out = subprocess.run(
            ["git", "-C", str(ROOT), "ls-files", "-z"], capture_output=True, text=True
        )
        tracked_paths = {p for p in out.stdout.split("\0") if p}

    # Narrow to the files that can possibly matter BEFORE reading any. This is not a weaker
    # filter — it is the SAME predicate ("the source contains the literal token `include_str!`
    # or `include_bytes!`") that the per-file skip below applied, evaluated by git instead of by
    # reading all ~3900 tracked .rs. `-a` keeps a NUL-bearing source in the candidate set so the
    # unreadable-source tooth below still fires on it rather than the file being silently dropped.
    candidates = set(files)
    if have_index:
        g = subprocess.run(
            ["git", "-C", str(ROOT), "grep", "-l", "-a", "-z", "-F",
             "-e", "include_str!", "-e", "include_bytes!", "--", "*.rs"],
            capture_output=True, text=True,
        )
        if g.returncode in (0, 1):  # 1 == no matches, a legitimate (if surprising) answer
            candidates = {p for p in g.stdout.split("\0") if p} & candidates

    findings: list[str] = []
    inflight_includes: list[str] = []
    n_sites = n_nonliteral = 0
    excluded = 0
    for rel in sorted(candidates):
        if rel.startswith(INCLUDE_SCAN_EXCLUDED_DIRS):
            excluded += 1
            continue
        p = ROOT / rel
        try:
            text = p.read_text()
        except (OSError, UnicodeDecodeError) as e:
            sys.exit(
                f"emit_descriptors: cannot read tracked Rust source {rel} ({e}). Refusing to "
                "report a pass over a file this check could not scan."
            )
        if "include_str!" not in text and "include_bytes!" not in text:
            continue
        comments, strings = _rust_comment_spans(text, rel)
        blanked = list(text)
        for a, b in comments:
            for k in range(a, b):
                if blanked[k] != "\n":
                    blanked[k] = " "
        blanked = "".join(blanked)
        # A match must not itself sit inside a string literal (a test that embeds Rust source
        # as a string is not a compile-time include).
        in_string = [(a, b) for a, b in strings]

        def quoted(off: int) -> bool:
            return any(a < off < b for a, b in in_string)

        literal_starts = set()
        for m in _INCLUDE_MACRO.finditer(blanked):
            if quoted(m.start()):
                continue
            literal_starts.add(m.start())
            n_sites += 1
            line = blanked.count("\n", 0, m.start()) + 1
            target = (p.parent / m.group(1)).resolve()
            # Both sides are fully resolved (ROOT is `.resolve()`d at import), so this is a
            # symlink-stable comparison. A target OUTSIDE the repo gets its own class rather than
            # being mislabelled UNTRACKED with a "commit it alongside" instruction that cannot
            # apply — nothing in this repo can make a path outside it tracked.
            inside = True
            try:
                trel = target.relative_to(ROOT).as_posix()
            except ValueError:
                inside = False
                trel = target.as_posix()
            if not inside:
                findings.append(
                    f"INCLUDE-ESCAPES-REPO: {rel}:{line} `include_str!/include_bytes!` of "
                    f"`{m.group(1)}` resolves to {trel}, OUTSIDE this repository. The build then "
                    f"depends on a path no checkout can reproduce. Vendor the file in-tree."
                )
                continue
            if not target.exists():
                findings.append(
                    f"INCLUDE-GHOST: {rel}:{line} `include_str!/include_bytes!` of "
                    f"`{m.group(1)}` -> {trel}, which does not exist. `include_*!` is resolved "
                    f"by rustc at COMPILE time, so this crate and everything downstream of it "
                    f"CANNOT BUILD. Commit the artifact (re-run its emit ceremony) or drop the "
                    f"include and its dispatch arm — do NOT `#[cfg]`-gate the include away."
                )
            elif have_index and trel not in tracked_paths:
                if _reference_is_committed(rel, m.group(1)):
                    findings.append(
                        f"INCLUDE-UNTRACKED: {rel}:{line} `include_str!/include_bytes!` of "
                        f"`{m.group(1)}` -> {trel}, which exists ON DISK but is NOT tracked by "
                        f"git — and the include IS committed. So HEAD is broken RIGHT NOW: it "
                        f"compiles for whoever emitted the artifact and reds for every "
                        f"co-tenant and every fresh clone. `git add` the artifact."
                    )
                else:
                    inflight_includes.append(f"{rel}:{line} -> {trel}")
        for m in _INCLUDE_MACRO_ANY.finditer(blanked):
            if m.start() not in literal_starts and not quoted(m.start()):
                n_nonliteral += 1

    leg = "exists+tracked" if have_index else "exists ONLY (NO git index here — untracked leg unavailable)"
    print(
        f"verify-include-targets: {n_sites} literal include_str!/include_bytes! site(s) over "
        f"{len(files)} tracked .rs · checked {leg}"
        + (f" · {n_nonliteral} non-literal (macro-built path) site(s) NOT checkable" if n_nonliteral else "")
        + (f" · {excluded} candidate file(s) in named exclusions" if excluded else "")
        + (f"\n  IN FLIGHT (untracked target, include NOT yet committed — `git add` the artifact "
           f"IN THE SAME COMMIT or HEAD breaks): {', '.join(inflight_includes)}"
           if inflight_includes else "")
    )
    return findings


# ---- the SAME door, one language over: a committed `import` of an uncommitted module -----
#
# `20b9d9a20f` is titled "repairs a committed tree that imported untracked files": a committed
# .lean imported `Dregg2.Circuit.Emit.GuardedHidingSpanWideBlindRefine`, which was left untracked,
# so a fresh checkout could not build it. Identical shape to INCLUDE-UNTRACKED — green for the
# author, red for everyone else — and worth checking here rather than waiting for the next
# multi-hour `lake build` to discover it, since this driver's whole point is that the emit's Lean
# corpus builds.
#
# Only `Dregg2.*` / `Polis.*` are resolved: Mathlib/Std/Lean/Batteries live in `.lake/packages`,
# which is not this repo's to track. That scope is a decision, not an oversight — a mis-typed
# Mathlib import is Lean's error to give, an untracked FIRST-PARTY module is ours.
LEAN_FIRST_PARTY_ROOTS = ("Dregg2", "Polis")
_LEAN_IMPORT = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)", re.M)


def verify_lean_imports() -> list[str]:
    """Every first-party `import` in a tracked metatheory/*.lean must name a TRACKED module.

    Returns finding lines (empty == clean); prints a one-line summary. Skipped entirely with a
    stated reason where there is no git index, since "tracked" is the whole question."""
    out = subprocess.run(
        ["git", "-C", str(ROOT), "ls-files", "-z", "--", "metatheory/*.lean"],
        capture_output=True, text=True,
    )
    if out.returncode != 0:
        print("verify-lean-imports: SKIPPED — no git index here, and `tracked` is the question.")
        return []
    files = [p for p in out.stdout.split("\0") if p]
    if not files:
        sys.exit(
            "emit_descriptors: `git ls-files metatheory/*.lean` returned NOTHING. A scan that "
            "sees zero modules would report a vacuous pass; re-point it."
        )
    pre = len("metatheory/")
    tracked_mods = {f[pre:-len(".lean")].replace("/", ".") for f in files}
    on_disk_mods = {
        p.relative_to(ROOT / "metatheory").as_posix()[:-len(".lean")].replace("/", ".")
        for p in (ROOT / "metatheory").rglob("*.lean")
        if ".lake" not in p.relative_to(ROOT / "metatheory").parts
    }

    findings: list[str] = []
    inflight: list[str] = []
    n_imports = 0
    for f in files:
        text = (ROOT / f).read_text(errors="replace")
        for m in _LEAN_IMPORT.finditer(text):
            mod = m.group(1)
            if not mod.startswith(LEAN_FIRST_PARTY_ROOTS):
                continue
            n_imports += 1
            if mod in tracked_mods:
                continue
            line = text.count("\n", 0, m.start()) + 1
            if mod not in on_disk_mods:
                # GHOST fails unconditionally: nobody is mid-authoring a file that does not exist,
                # so there is no in-flight reading of this. `lake build` cannot resolve it, and
                # every theorem citing that module is UNBUILT rather than proven.
                findings.append(
                    f"LEAN-IMPORT-GHOST: {f}:{line} imports `{mod}`, whose module file exists "
                    f"NOWHERE — no file, no git history. A fresh checkout cannot `lake build` "
                    f"this, and every theorem downstream of it is unbuilt rather than proven. "
                    f"Commit the module, or drop the import and whatever it was carrying."
                )
            elif _reference_is_committed(f, f"import {mod}"):
                findings.append(
                    f"LEAN-IMPORT-UNTRACKED: {f}:{line} imports `{mod}`, whose module file exists "
                    f"ON DISK but is NOT tracked — and the import IS committed. HEAD is broken "
                    f"RIGHT NOW: it builds for whoever wrote the module and reds for every fresh "
                    f"checkout (this is the wound `20b9d9a20f` repaired). `git add` the module."
                )
            else:
                inflight.append(f"{f}:{line} -> {mod}")
    print(
        f"verify-lean-imports: {n_imports} first-party import(s) over {len(files)} tracked "
        f"metatheory/*.lean ({len(tracked_mods)} modules) · checked exists+tracked"
        + (f"\n  IN FLIGHT (untracked module, import NOT yet committed — `git add` the module IN "
           f"THE SAME COMMIT or HEAD breaks): {', '.join(inflight)}" if inflight else "")
    )
    return findings


# ---- THE FOURTH DOOR: a workflow that runs a script nobody committed ---------------------
#
# Same class as the two above, third medium. A `.github/workflows/*.yml` step whose `run:`
# invokes `bash scripts/x.sh` is a COMMITTED reference; if `scripts/x.sh` is untracked the job
# dies with `No such file or directory` on every runner and every fresh clone while the author's
# box is green. Nothing else could see it: the routing preflight covered Lean imports and
# `include_str!` targets, `actionlint` (not run here) type-checks workflow SYNTAX and does not
# resolve invoked paths against the index, and the job itself only reds AFTER it lands.
#
# Live instance the night this leg was written: `scripts/check-ratchet-darkness.sh` sat untracked
# while an uncommitted ci.yml hunk added a `ratchet-darkness` job running it. It landed correctly
# (7f52c1fac0 committed all three files) — by the author's diligence, not by detection. This is
# the detection.
#
# PARSER SHAPE, and why it is built the way it is. Workflow `run:` bodies are SHELL, so the
# question "which repo paths does this workflow execute" cannot be answered by a regex over the
# YAML: `#`-comments (both YAML and shell) carry prose full of sentence-final periods and words
# like `bash to`, heredoc bodies carry foreign languages, and half the real invocations are
# spelled across a `\` continuation. Every one of those produced a false hit on the first pass.
# So: strip comments, join continuations, drop heredoc bodies, then extract only COMMAND-POSITION
# invocations, and classify each one:
#
#   * CHECKED — a statically resolvable in-repo path. Must exist and be tracked.
#   * NOT-CHECKABLE — reported with a count and a reason, never guessed at. Five reasons, each
#     one a thing this parser genuinely cannot resolve rather than a thing it declines to look at:
#     a `$VAR`/`${{ }}`/glob in the path, a non-static `working-directory:`, a `cd` earlier in the
#     block, an absolute host/runner path (`/usr/bin/...` is not ours to track), a path the
#     workflow PRODUCES at runtime (`curl -o elan-init.sh` then `bash elan-init.sh`), a path git
#     itself declares generated (`.gitignore`d — `./target/release/dregg-node`), or a block whose
#     shell would not lex.
#
# The `include_str!` lexer's failure mode is the one to avoid here: it `sys.exit`ed on a char
# literal it misread, so two CI jobs were dying BEFORE reporting anything and looked like they
# were checking. This leg is FATAL only where a fatality is the honest answer (an unterminated
# heredoc means the block boundaries this parser computed are wrong), and every other
# can't-tell is a NAMED, COUNTED line in the summary.
_WF_BLOCK_OPEN = re.compile(
    r"^(?P<pre>\s*(?:-\s+)?)(?P<key>[A-Za-z_][\w.-]*)\s*:\s*(?P<style>[|>][-+]?\d*)\s*(?:#.*)?$"
)
_WF_INLINE = re.compile(r"^\s*(?:-\s+)?(?P<key>run|uses|working-directory)\s*:\s*(?P<val>\S.*?)\s*$")
_HEREDOC = re.compile(r"<<-?\s*(?P<q>['\"]?)(?P<word>[A-Za-z_]\w*)(?P=q)")
_ENV_ASSIGN = re.compile(r"^[A-Za-z_]\w*=")
_REDIRECT = re.compile(r"^\d*(?:>>|>|&>)(.*)$")

# Command-position heads whose first non-flag operand IS a repo script, mapped to the flags that
# mean "the script is INLINE or on stdin, there is no path operand". Per-interpreter on purpose:
# `-e` is eval for perl/node/ruby but errexit for a SHELL, so one shared flag set would silently
# skip a real `bash -e scripts/x.sh` site — the quiet kind of coverage loss this whole leg exists
# to prevent. `sh -s -- -y` (the elan/rustup pipe-to-shell idiom) is the live case for `-s`.
WF_INTERPRETERS: dict[str, frozenset[str]] = {
    "bash": frozenset({"-c", "-s"}),
    "sh": frozenset({"-c", "-s"}),
    "zsh": frozenset({"-c", "-s"}),
    "dash": frozenset({"-c", "-s"}),
    "ksh": frozenset({"-c", "-s"}),
    "python": frozenset({"-c", "-m"}),
    "python2": frozenset({"-c", "-m"}),
    "python3": frozenset({"-c", "-m"}),
    "ruby": frozenset({"-e"}),
    "perl": frozenset({"-e", "-E"}),
    "node": frozenset({"-e", "--eval", "-p", "--print"}),
    "deno": frozenset({"-e", "--eval"}),
    "pwsh": frozenset({"-c", "-Command", "-EncodedCommand"}),
    "powershell": frozenset({"-c", "-Command", "-EncodedCommand"}),
}
WF_SOURCERS = frozenset({"source", "."})
# Transparent prefixes — strip and look at what they wrap.
WF_PREFIX_CMDS = frozenset({"sudo", "time", "exec", "env", "nice", "ionice", "nohup",
                            "command", "builtin", "stdbuf"})
# Commands whose LAST operand is a file they create, and commands ALL of whose operands are.
WF_DEST_LAST = frozenset({"mv", "cp", "install", "ln", "rsync"})
WF_DEST_ALL = frozenset({"mkdir", "tee", "touch"})
WF_DEST_FLAGS = frozenset({"-o", "-O", "--output", "--output-document", "-d", "-C", "--directory"})
# A character that makes a path un-resolvable at scan time.
WF_DYNAMIC_CHARS = frozenset("$`*?[]~{}")


def _wf_scan_line(line: str, q: str | None) -> tuple[str, str | None, list[str]]:
    """ONE shell pass over `line`, entered in quote state `q` (None / `'` / `"`).

    Returns (line with any trailing `#` comment removed, quote state at end of line, heredoc
    opener words seen). All three answers have to come from the SAME walk, because each one is
    only correct relative to the quote state the others compute:

      * a `#` starts a comment only OUTSIDE quotes — `echo 'a#b'` keeps its hash;
      * a `<<WORD` opens a heredoc only OUTSIDE quotes — Actions' multiline-output idiom is
        literally `echo 'verdict<<CANARY_EOF'`, and reading that as a heredoc opener made this
        parser swallow the rest of the workflow and then FATAL on a heredoc that never existed;
      * `\\` escapes the next character outside quotes and inside `"` but NOT inside `'` — and
        getting that wrong is what made `discovery.yml`'s `echo "{\\"node_id\\":..."` read as an
        unbalanced quote, which silently dropped that whole block from the scan.

    The returned quote state is what lets a quote SPAN LINES, which a `run: |` block is one shell
    script and therefore allowed to do (`gh release create --notes "…` over four lines)."""
    out: list[str] = []
    heredocs: list[str] = []
    i, n = 0, len(line)
    while i < n:
        c = line[i]
        if q == "'":
            out.append(c)
            if c == "'":
                q = None
            i += 1
            continue
        if q == '"':
            if c == "\\" and i + 1 < n:
                out.append(c); out.append(line[i + 1]); i += 2; continue
            out.append(c)
            if c == '"':
                q = None
            i += 1
            continue
        if c in "'\"":
            q = c; out.append(c); i += 1; continue
        if c == "\\" and i + 1 < n:
            out.append(c); out.append(line[i + 1]); i += 2; continue
        if c == "#" and (i == 0 or line[i - 1] in " \t;&|("):
            break
        if c == "<" and line.startswith("<<", i):
            m = _HEREDOC.match(line, i)
            if m:
                heredocs.append(m.group("word"))
                # DROP THE OPENER TOKEN, not just the body. `<<WORD` is a REDIRECTION operator;
                # the program it feeds is the heredoc BODY, which the caller already discards. Left
                # in the stream it lexes as a bare word and lands in COMMAND-OPERAND position, so
                # `python3 - <<'PY'` read as "run the file `<<'PY'`" and raised a WORKFLOW-GHOST
                # for a token that is not a path and can never be committed — a red no fix could
                # clear. Dropping it costs no coverage: an operand IN FRONT of the redirect
                # (`python3 scripts/x.py <<'PY'`) is still the first operand and still checked,
                # and `python3 -`/`bash` with the script on stdin correctly resolves to no operand
                # at all. The match spans balanced quotes (`<<'PY'`), so skipping it cannot leave
                # the quote state open.
                i = m.end()
                continue
        out.append(c); i += 1
    return "".join(out), q, heredocs


def _wf_logical_lines(body: list[tuple[int, str]], where: str) -> list[tuple[int, str]]:
    """Block body -> logical shell lines: comments stripped, `\\` continuations JOINED, heredoc
    bodies dropped. Returns (first lineno, code).

    Continuations matter for correctness in BOTH directions: unjoined, `sudo rm -rf ... \\` +
    `/usr/local/lib/android` reads as an absolute-path invocation (a false hit), and
    `curl -sSfL URL \\` + `-o elan-init.sh` hides the `-o` that makes the NEXT line's
    `bash elan-init.sh` a runtime-produced file rather than a ghost (a false RED).

    FATAL on an unterminated heredoc: the block boundaries would then be wrong, and this refuses
    to report on a body it read wrong (the one place where silence would be worse than noise)."""
    out: list[tuple[int, str]] = []
    pending: list[tuple[str, int]] = []
    acc: list[str] = []
    acc_line = 0
    q: str | None = None
    for lineno, raw in body:
        if pending:
            if raw.strip() == pending[0][0]:
                pending.pop(0)
            continue
        code, q, heredocs = _wf_scan_line(raw, q)
        pending.extend((w, lineno) for w in heredocs)
        stripped = code.rstrip()
        if not acc:
            acc_line = lineno
        # Two ways one shell command spans lines, and BOTH have to be joined: a trailing `\`, and
        # a quote still open at end of line.
        if q is not None or (stripped.endswith("\\") and not stripped.endswith("\\\\")):
            acc.append(stripped[:-1] if q is None else stripped)
            continue
        acc.append(stripped)
        out.append((acc_line, " ".join(s.strip() for s in acc if s.strip())))
        acc = []
    if acc:
        out.append((acc_line, " ".join(s.strip() for s in acc if s.strip())))
    if pending:
        w, ln = pending[0]
        sys.exit(
            f"emit_descriptors: {where}:{ln} — heredoc `<<{w}` is never terminated inside this "
            f"`run:` block. This parser will not report on a block whose boundaries it read wrong."
        )
    return out


def _wf_segments(code: str) -> list[str]:
    """Split one logical shell line into command segments at `;`, `&&`, `||`, `|`, `(`, `)`.

    Same escape rules as `_wf_scan_line` (`\\` escapes inside `"` but not inside `'`), so a
    separator buried in `"…\\"…;…"` does not split a command in two."""
    segs: list[str] = []
    cur: list[str] = []
    i, n, q = 0, len(code), None
    while i < n:
        c = code[i]
        if q == "'":
            cur.append(c)
            if c == "'":
                q = None
            i += 1
            continue
        if q == '"':
            if c == "\\" and i + 1 < n:
                cur.append(c); cur.append(code[i + 1]); i += 2; continue
            cur.append(c)
            if c == '"':
                q = None
            i += 1
            continue
        if c in "'\"":
            q = c; cur.append(c); i += 1; continue
        if c == "\\" and i + 1 < n:
            cur.append(c); cur.append(code[i + 1]); i += 2; continue
        if code.startswith("&&", i) or code.startswith("||", i):
            segs.append("".join(cur)); cur = []; i += 2; continue
        if c in ";&|()":
            segs.append("".join(cur)); cur = []; i += 1; continue
        cur.append(c); i += 1
    segs.append("".join(cur))
    return [s.strip() for s in segs if s.strip()]


def _wf_unquote(t: str) -> str:
    return t[1:-1] if len(t) >= 2 and t[0] == t[-1] and t[0] in "'\"" else t


def _wf_norm(p: str) -> str:
    p = p.strip()
    while p.startswith("./"):
        p = p[2:]
    return p


def _wf_head(tokens: list[str]) -> list[str]:
    """Drop leading `FOO=bar` env assignments and transparent prefixes (`sudo`, `time`, ...)."""
    t = list(tokens)
    while t and (_ENV_ASSIGN.match(t[0]) or _wf_unquote(t[0]) in WF_PREFIX_CMDS):
        t = t[1:]
    return t


def _wf_first_operand(tokens: list[str]) -> str | None:
    for a in tokens:
        if a.startswith("-"):
            continue
        return _wf_unquote(a)
    return None


def _wf_produced(logical: list[tuple[int, str]]) -> set[str]:
    """Paths this workflow CREATES at runtime — redirect targets, `-o`/`-O`/`-d`/`-C` operands,
    and the destinations of `mv`/`cp`/`install`/`ln`/`rsync`/`mkdir`/`tee`/`touch`/`git clone`.

    Collected per FILE, not per block, deliberately: a step that builds `dist/x` and a later step
    that runs `./dist/x` are different blocks, and the conservative direction for a gate is to
    call that NOT-CHECKABLE rather than to red on it. It costs this leg nothing on the class it
    exists for — nothing in any workflow PRODUCES a `scripts/*.sh` it then runs, so an untracked
    one is still caught. `chmod` is deliberately NOT here: `chmod +x scripts/x.sh` does not create
    the file, and treating it as a producer would have exempted exactly the wound."""
    made: set[str] = set()
    for _, code in logical:
        for seg in _wf_segments(code):
            try:
                t = shlex.split(seg, posix=False)
            except ValueError:
                continue
            if not t:
                continue
            for k, tok in enumerate(t):
                m = _REDIRECT.match(tok)
                if m:
                    tgt = m.group(1) or (t[k + 1] if k + 1 < len(t) else "")
                    if tgt:
                        made.add(_wf_norm(_wf_unquote(tgt)))
            for k in range(len(t) - 1):
                if t[k] in WF_DEST_FLAGS:
                    made.add(_wf_norm(_wf_unquote(t[k + 1])))
            t = _wf_head(t)
            if not t:
                continue
            base = _wf_unquote(t[0]).rsplit("/", 1)[-1]
            operands = [_wf_unquote(a) for a in t[1:] if not a.startswith("-")]
            if base in WF_DEST_ALL:
                made.update(_wf_norm(o) for o in operands)
            elif base in WF_DEST_LAST and operands:
                made.add(_wf_norm(operands[-1]))
            elif base == "git" and operands[:1] == ["clone"] and len(operands) >= 3:
                made.add(_wf_norm(operands[-1]))
    return made


def _wf_parse(path: Path, rel: str) -> list[tuple[int, str, str, list[tuple[int, str]]]]:
    """Workflow file -> [(lineno, kind, working_directory, body)] for kind in {run, uses}.

    A hand-rolled YAML SUBSET on purpose: PyYAML is not a dependency of this repo and the
    `descriptor-by-name-routing` job runs a bare `python3` with no pip step, so importing it would
    make this leg's coverage depend on whatever the runner image happens to ship. Only three keys
    are read (`run`, `uses`, `working-directory`) and only two node shapes (a `|`/`>` block scalar,
    and a plain inline scalar), which is the whole grammar GitHub's step syntax uses for them.

    `working-directory:` RELOCATES every relative path in a step, so it has to be honoured:
    `extension.yml`'s `./build.sh` under `working-directory: extension` is `extension/build.sh`,
    which is tracked — reading the key turns two would-be false hits into two real passes.

    ⚑ AND ITS SCOPE IS THE WHOLE CORRECTNESS OF THIS LEG. Measured 2026-08-01: it LEAKED. The
    old rule reset the key at any `- ` item "at or above the step's indent", with the baseline
    indent taken from the FIRST `- ` anywhere in the file — which in `ci.yml` is `- cron: '0 6 *
    * *'` at indent 4, under `on: schedule:`. Every real step is at indent 6, so `6 <= 4` never
    held and **the key was never reset again in that file**. One `working-directory: metatheory`
    at line 1471 therefore relocated EVERY subsequent step, which is where the eight
    `WORKFLOW-GHOST` findings against `metatheory/scripts/*` came from: not eight broken steps,
    one broken parser. The leak cut BOTH ways and the quiet half was worse — a
    `working-directory: ${{ matrix.dir }}` at line 442 leaked forward too, so FIFTEEN static,
    checkable invocations (`scripts/ci-mathlib-cache.sh`, `scripts/check-dark-modules.py`,
    `scripts/axiom-hygiene-guard.sh`, …) were deferred as "not static" and never checked at all.
    A permanently-noisy check trains readers to skip it, and a deferral is how it goes blind
    without ever printing a red.

    The scope is now modelled properly, in the two shapes GitHub actually has:

      * STEP level — `working-directory:` inside a step's mapping, scoped to THAT list item.
      * JOB level — `defaults: → run: → working-directory:`, which applies to every `run` step
        of the job (`extension.yml`, `forge.yml`) and dies at the next job.

    ⚠ AND IT IS RESOLVED PER ITEM, NOT IN READING ORDER. A YAML mapping is unordered and this
    repo writes it both ways — `ci.yml:192` is `- run: cargo test` with `working-directory:
    solana-lock` on the line BELOW, while `ci.yml:298` puts the key first. A parser that
    attributes the key only forwards silently drops the first shape, so the item's whole extent
    is scanned before its `run:` steps are resolved.

    `uses:` steps get NEITHER: `working-directory` is a `run` key, and `uses: ./x` resolves
    against the workspace root however the cwd was set."""
    lines = path.read_text(errors="replace").splitlines()
    n = len(lines)
    # (lineno, kind, item_key, job_key, body) — wd is resolved after the walk, per item.
    raw_steps: list[tuple[int, str, object, object, list[tuple[int, str]]]] = []
    item_wd: dict[object, str] = {}
    job_wd: dict[object, str] = {}
    stack: list[tuple[int, int]] = []     # open `- ` items: (indent, start line)
    defaults_ind: int | None = None       # the innermost open `defaults:` key
    job_key: object = None                # the current job's key line, or None outside `jobs:`
    jobs_ind: int | None = None           # indent of the `jobs:` key
    steps_in_job = 0
    i = 0
    while i < n:
        raw = lines[i]
        stripped = raw.strip()
        if not stripped or stripped.startswith("#"):
            i += 1
            continue
        ind = len(raw) - len(raw.lstrip())
        is_item = stripped.startswith("- ") or stripped == "-"

        # Close every list item we have dedented out of. A sibling `- ` at indent d ends the
        # previous item at d; a mapping key at indent k ends every item at indent >= k.
        while stack and (stack[-1][0] >= ind if is_item else stack[-1][0] >= ind):
            stack.pop()
        if is_item:
            stack.append((ind, i + 1))
        if defaults_ind is not None and ind <= defaults_ind:
            defaults_ind = None
        key0 = stripped.split(":", 1)[0].strip() if not is_item else ""
        if key0 == "jobs" and stripped.rstrip().endswith(":"):
            jobs_ind = ind
        elif jobs_ind is not None and not is_item and ind == jobs_ind + 2 and stripped.endswith(":"):
            job_key, steps_in_job = i + 1, 0          # a new job: its defaults start over
            defaults_ind = None
        if key0 == "defaults":
            defaults_ind = ind

        mb = _WF_BLOCK_OPEN.match(raw)
        if mb:
            keyind = len(mb.group("pre"))
            body: list[tuple[int, str]] = []
            j = i + 1
            while j < n:
                b = lines[j]
                if not b.strip():
                    body.append((j + 1, "")); j += 1; continue
                if len(b) - len(b.lstrip()) <= keyind:
                    break
                body.append((j + 1, b)); j += 1
            if mb.group("key") == "run":
                raw_steps.append((i + 1, "run", stack[-1][1] if stack else None, job_key, body))
                steps_in_job += 1
            i = j
            continue
        mi = _WF_INLINE.match(raw)
        if mi:
            val = re.sub(r"\s+#.*$", "", mi.group("val")).strip()
            key = mi.group("key")
            if key == "working-directory":
                if defaults_ind is not None and ind > defaults_ind:
                    if steps_in_job:
                        sys.exit(
                            f"emit_descriptors: {rel}:{i + 1} declares a job-level "
                            f"`defaults.run.working-directory` AFTER that job's steps. This "
                            f"parser resolves job defaults in reading order, so it would apply "
                            f"the key to none of them and report on a cwd it read wrong. Move "
                            f"the `defaults:` block above `steps:`, or teach this parser to "
                            f"resolve job defaults per job — do not leave it silently wrong."
                        )
                    job_wd[job_key] = _wf_unquote(val)
                elif stack:
                    item_wd[stack[-1][1]] = _wf_unquote(val)
            elif key == "run":
                raw_steps.append((i + 1, "run", stack[-1][1] if stack else None, job_key,
                                  [(i + 1, val)]))
                steps_in_job += 1
            elif key == "uses":
                raw_steps.append((i + 1, "uses", None, None, [(i + 1, val)]))
        i += 1

    steps: list[tuple[int, str, str, list[tuple[int, str]]]] = []
    for lineno, kind, item, job, body in raw_steps:
        wd = "" if kind == "uses" else (item_wd.get(item) or job_wd.get(job, ""))
        steps.append((lineno, kind, wd, body))
    return steps


def verify_workflow_refs() -> list[str]:
    """Every repo path a tracked `.github/workflows/*.yml` INVOKES must exist and be tracked.

    Returns finding lines (empty == clean); prints a one-line summary with the checked and
    NOT-CHECKABLE counts. Skipped with a stated reason where there is no git index."""
    wf_dir = ROOT / ".github" / "workflows"
    out = subprocess.run(
        ["git", "-C", str(ROOT), "ls-files", "-z", "--", ".github/workflows"],
        capture_output=True, text=True,
    )
    if out.returncode != 0:
        print("verify-workflow-refs: SKIPPED — no git index here, and `tracked` is the question.")
        return []
    wfs = sorted(p for p in out.stdout.split("\0") if p.endswith((".yml", ".yaml")))
    if not wfs:
        sys.exit(
            "emit_descriptors: `git ls-files .github/workflows` returned NO workflow files. A "
            "scan that sees zero workflows would report a vacuous pass; re-point it."
        )
    tracked = {p for p in subprocess.run(
        ["git", "-C", str(ROOT), "ls-files", "-z"], capture_output=True, text=True
    ).stdout.split("\0") if p}

    # THE SCOPE, made a TOOTH instead of a footnote. This leg reads `.github/workflows/*` and
    # nothing else. A LOCAL COMPOSITE ACTION (`.github/**/action.yml`) also carries `run:` steps
    # that invoke repo paths — the identical wound in the identical medium — but its relative-path
    # resolution is NOT the same (a composite action's `uses:` is relative to the ACTION dir while
    # its `run:` cwd is the workspace root), so scanning one with this file's resolution model
    # would report on a semantics it does not implement. There are ZERO composite actions in the
    # tree, which is what makes the scope claim above exhaustive TODAY. The moment that stops
    # being true this must fail, because the alternative is a checker that silently stops covering
    # a medium it never announced it had dropped — the exact way a gate becomes decoration.
    composite = sorted(p for p in tracked
                       if p.startswith(".github/") and not p.startswith(".github/workflows/")
                       and p.rsplit("/", 1)[-1] in ("action.yml", "action.yaml"))

    # (lineno, kind, token, resolved_rel) for the sites that survive to the exists+tracked test,
    # and a reason-tagged bucket for every site that does not.
    findings: list[str] = []

    # ── ⚑ COMPOSITE ACTIONS ARE SCANNED (2026-11-06) ──────────────────────────────────────
    # From 2026-08-07 (`.github/actions/lean-seed/action.yml`) to 2026-11-06 this leg reported a
    # standing "COVERAGE GAP" finding instead of scanning them, which kept every caller of this
    # leg red for a reason unrelated to its subject. A composite action's `run:` steps execute
    # with the WORKSPACE ROOT as cwd (exactly a workflow step's default), so they are scanned with
    # the identical resolution model below. Its `uses: ./x` sites are NOT resolved here (their
    # base directory differs from a workflow's); each one is DEFERRED with that reason, by name,
    # rather than silently skipped or checked against the wrong base.
    inflight: list[str] = []
    notcheckable: dict[str, list[str]] = {}
    unlexable: list[str] = []
    n_sites = n_checked = 0
    candidates: list[tuple[str, int, str, str]] = []   # (rel_wf, lineno, token, resolved_rel)

    def defer(reason: str, where: str) -> None:
        notcheckable.setdefault(reason, []).append(where)

    for wf in wfs + composite:
        is_composite = wf in composite
        p = ROOT / wf
        if not p.exists():   # tracked but deleted in the working tree
            continue
        produced_in_file: set[str] = set()
        parsed = _wf_parse(p, wf)
        for lineno, kind, wd, body in parsed:
            if kind == "run":
                produced_in_file |= _wf_produced(_wf_logical_lines(body, wf))

        for lineno, kind, wd, body in parsed:
            raw_sites: list[tuple[int, str, str, bool]] = []   # (line, what, token, cwd_static)
            if kind == "uses":
                v = _wf_unquote(body[0][1])
                if v.startswith("./") and is_composite:
                    defer("`uses: ./` inside a composite action (base directory not modelled)",
                          f"{wf}:{lineno} ({v})")
                elif v.startswith("./"):
                    # A LOCAL composite action: `uses: ./x` resolves `x/action.yml` OR
                    # `x/action.yaml` — either spelling satisfies it, so a site is raised only
                    # when NEITHER is tracked, and it names the `.yml` one. No instance in the
                    # tree today; the class arrives the first time someone factors a step out.
                    stem = v.rstrip("/") + "/action."
                    if not any(_wf_norm(stem + e) in tracked for e in ("yml", "yaml")):
                        raw_sites.append((lineno, "uses (local action)", stem + "yml", True))
            else:
                logical = _wf_logical_lines(body, wf)
                block_ok = True
                for ln, code in logical:
                    for seg in _wf_segments(code):
                        try:
                            shlex.split(seg, posix=False)
                        except ValueError:
                            block_ok = False
                if not block_ok:
                    unlexable.append(f"{wf}:{lineno}")
                    continue
                cwd_static = True
                for ln, code in logical:
                    for seg in _wf_segments(code):
                        t = _wf_head(shlex.split(seg, posix=False))
                        if not t:
                            continue
                        head = _wf_unquote(t[0])
                        base = head.rsplit("/", 1)[-1]
                        if base == "cd":
                            cwd_static = False
                            continue
                        what, tok = None, None
                        if base in WF_INTERPRETERS:
                            if any(a in WF_INTERPRETERS[base] for a in t[1:]):
                                continue          # inline script / stdin: no path operand at all
                            what, tok = f"{base} <script>", _wf_first_operand(t[1:])
                        elif head in WF_SOURCERS:
                            what, tok = "source", _wf_first_operand(t[1:])
                        elif head.startswith(("./", "../", "/")):
                            what, tok = "direct exec", head
                        if what and tok:
                            raw_sites.append((ln, what, tok, cwd_static))

            for ln, what, tok, cwd_static in raw_sites:
                n_sites += 1
                where = f"{wf}:{ln} ({what} `{tok}`)"
                if any(c in tok for c in WF_DYNAMIC_CHARS):
                    defer("path built from a variable / `${{ }}` / glob", where); continue
                if tok.startswith("/"):
                    abs_p = Path(tok)
                    try:
                        rel = abs_p.resolve().relative_to(ROOT).as_posix()
                    except ValueError:
                        defer("absolute host/runner-image path (not this repo's to track)", where)
                        continue
                elif not cwd_static:
                    defer("a `cd` earlier in the block moved the working directory", where); continue
                elif any(c in wd for c in WF_DYNAMIC_CHARS):
                    defer("step `working-directory:` is not static", where); continue
                else:
                    base_dir = (ROOT / wd) if wd else ROOT
                    try:
                        rel = (base_dir / _wf_norm(tok)).resolve().relative_to(ROOT).as_posix()
                    except ValueError:
                        findings.append(
                            f"WORKFLOW-ESCAPES-REPO: {wf}:{ln} ({what}) `{tok}`"
                            + (f" (working-directory `{wd}`)" if wd else "")
                            + " resolves OUTSIDE this repository. The job then depends on a "
                            "path no checkout can reproduce. Vendor it in-tree, or fetch it in an "
                            "explicit step so the dependency is on the record."
                        )
                        continue
                if _wf_norm(tok) in produced_in_file or rel in produced_in_file:
                    defer("produced by the workflow at runtime (download/redirect/copy)", where)
                    continue
                candidates.append((wf, ln, what, tok, rel))

    # `.gitignore` is the repo's OWN declaration of what is generated, so a build output
    # (`./target/release/dregg-node`) is separated from a wound by asking git, not by pattern-
    # matching directory names. One batched call.
    ignored: set[str] = set()
    if candidates:
        probe = sorted({c[4] for c in candidates})
        ci = subprocess.run(
            ["git", "-C", str(ROOT), "check-ignore", "--stdin", "-z"],
            input="\0".join(probe) + "\0", capture_output=True, text=True,
        )
        if ci.returncode not in (0, 1):
            sys.exit(
                f"emit_descriptors: `git check-ignore` failed (rc={ci.returncode}): "
                f"{ci.stderr.strip()!r}. Refusing to report a pass while the generated-vs-wound "
                f"split is unanswered."
            )
        ignored = {q for q in ci.stdout.split("\0") if q}

    for wf, ln, what, tok, rel in candidates:
        if rel in ignored:
            defer("git itself calls this path generated (`.gitignore`d build output)",
                  f"{wf}:{ln} ({tok})")
            continue
        n_checked += 1
        if rel in tracked:
            continue
        if not (ROOT / rel).exists():
            findings.append(
                f"WORKFLOW-GHOST: {wf}:{ln} ({what}) `{tok}` -> {rel}, which exists NOWHERE — no "
                f"file, no git history, and nothing in this workflow produces it. The step cannot "
                f"resolve on ANY runner or ANY fresh checkout. Commit the target, or drop the step."
            )
        elif _reference_is_committed(wf, tok):
            findings.append(
                f"WORKFLOW-UNTRACKED: {wf}:{ln} ({what}) `{tok}` -> {rel}, which exists ON DISK "
                f"but is NOT tracked by git — and the step IS committed. So HEAD is broken RIGHT "
                f"NOW: the job passes for whoever wrote the target and fails for every runner and "
                f"every fresh checkout. `git add` the target."
            )
        else:
            inflight.append(f"{wf}:{ln} -> {rel}")

    nc_total = sum(len(v) for v in notcheckable.values())
    print(
        f"verify-workflow-refs: {n_sites} invocation site(s) over {len(wfs)} tracked workflow(s) "
        f"+ {len(composite)} composite action(s) "
        f"· {n_checked} checked exists+tracked · {nc_total} NOT-CHECKABLE"
        + ("".join(f"\n  NOT-CHECKABLE ({len(v)}) — {r}: {', '.join(sorted(v))}"
                   for r, v in sorted(notcheckable.items())) if notcheckable else "")
        + (f"\n  NOT-CHECKABLE ({len(unlexable)}) — `run:` block whose shell would not lex "
           f"(quotes unbalanced per logical line): {', '.join(unlexable)}" if unlexable else "")
        + (f"\n  IN FLIGHT (untracked script, step NOT yet committed — `git add` the script IN "
           f"THE SAME COMMIT or HEAD breaks): {', '.join(inflight)}" if inflight else "")
    )
    return findings


def split_v1(stdout: str, written):
    # key\tname\tjson  ->  <name>.json  (the .name IS the wire identity / filename)
    for line in stdout.splitlines():
        p = line.split("\t")
        if len(p) < 3:
            continue
        write_file(p[1] + ".json", p[2], written)


def split_ir2(stdout: str, dn2file, written):
    # key\tname\tjson  ->  file via V2_DESCRIPTORS (defName-keyed; .name collides)
    for line in stdout.splitlines():
        p = line.split("\t")
        if len(p) < 3:
            continue
        f = dn2file.get(p[0])
        if not f:
            sys.exit(f"emit_descriptors: ir2 defName {p[0]!r} has no V2_DESCRIPTORS entry")
        write_file(f, p[2], written)


# rotation routing: key -> (column index of payload, target file).
# Manifest lines are `key\tjson` (payload col 1); probe lines `key\tname\tjson` (col 2).
ROTATION_SINGLE = {
    "rotationLayoutManifest": (1, "rotation-layout-v3-staged.json"),
    "rotationCaveatLayoutManifest": (1, "rotation-caveat-layout-v3-staged.json"),
    "rotationProbeVmDescriptor2": (2, "dregg-effectvm-rotation-state-v3-staged.json"),
    "rotationProbeVmDescriptorR24": (2, "dregg-effectvm-rotation-state-v3-staged-r24.json"),
    "rotationProbeVmDescriptorR32": (2, "dregg-effectvm-rotation-state-v3-staged-r32.json"),
    "rotationCaveatProbeVmDescriptor2": (2, "dregg-effectvm-rotation-caveat-v3-staged-r24.json"),
}
ROTATION_TSV = "rotation-v3-staged-registry.tsv"
# ⚑ DELETED 2026-07-31: `WIDE_TRANSFER_TSV` / `rotation-wide-transfer-staged.tsv` and its driver
# `EmitWideTransferProbe.lean`. The single-line probe was a diverged fork of `WIDE_REGISTRY_TSV`
# row 0 (no availability hardening, no membership-claim PIs, no gentian floor refuse, never
# E1-compacted) with no production consumer.
# ADDITIVE: the 57-member faithful 8-felt wide registry, a member-for-member name-stable cover of the
# live V3 registry (`key\tname\tjson` per line, `EmitWideRegistryProbe.lean`, trailing newline). The
# per-family wide-roundtrip slice consumes it.
# Beside the live 1-felt registry — the live TSV / FP / VK are untouched.
WIDE_REGISTRY_TSV = "rotation-wide-registry-staged.tsv"


def split_rotation(stdout: str, written):
    v3rot = []
    for line in stdout.splitlines():
        p = line.split("\t")
        key = p[0]
        if key == "v3rot":
            # v3rot\tkey\tname\tjson  ->  tsv line is `key\tname\tjson`
            v3rot.append("\t".join(p[1:]))
        elif key in ROTATION_SINGLE:
            col, f = ROTATION_SINGLE[key]
            write_file(f, p[col], written)
        else:
            sys.exit(f"emit_descriptors: rotation key {key!r} has no routing")
    # the registry tsv is the v3rot cohort, one line each, trailing newline.
    write_file(ROTATION_TSV, "\n".join(v3rot) + "\n", written)


def _parse_e1_intervals(spec: str) -> list[tuple[int, int]]:
    """Parse an `e1compact` payload (`a-b,c-d,...`, ascending half-open runs; possibly empty)
    into `[(a, b), ...]`. Validates ascending, non-overlapping, well-formed."""
    if spec == "":
        return []
    out: list[tuple[int, int]] = []
    prev_end = 0
    for chunk in spec.split(","):
        a_s, _, b_s = chunk.partition("-")
        a, b = int(a_s), int(b_s)
        if not (a < b and a >= prev_end):
            sys.exit(
                f"emit_descriptors: e1compact interval {chunk!r} not a well-formed ascending "
                f"non-overlapping half-open run (a<b, a>=prev_end={prev_end})"
            )
        out.append((a, b))
        prev_end = b
    return out


def split_wide_registry(stdout: str, written):
    """The wide-registry emitter prints one `key\tname\tjson` line per wide member, in the LIVE
    `rotation-v3-staged-registry.tsv` order — a member-for-member, name-stable COVER of the live V3
    registry (57 members): the 45 emit-source members (`v3RegistryCapOpenWide`) + the live-only
    `transferCapOpenTB` / `heapWrite` + the 9 WRITE-bearing cap-open tail members
    (`v3RegistryCapOpenWriteWide`, §10, MINUS `grantCapWriteCapOpen` — not a live member) + the
    live-only `supplyMint`, each made 8-felt-wide AND S2-COMPACTED (the two rotated 1-felt chains
    deleted, 960 columns removed, gated per member by the Lean `compactOk` falsifier) = 57 lines.

    Each member line is followed by an `s2compact\t<key>\t<bb>\t<lane_base>` companion line — the
    per-member deletion geometry, routed into `circuit/src/effect_vm/s2_compact_generated.rs` so
    the Rust trace producer compacts EXACTLY the columns the Lean emit deleted (single source)."""
    lines = [ln for ln in stdout.splitlines() if ln.strip()]
    members = [
        ln for ln in lines
        if not ln.startswith("s2compact\t") and not ln.startswith("e1compact\t")
    ]
    geo = [ln for ln in lines if ln.startswith("s2compact\t")]
    e1 = [ln for ln in lines if ln.startswith("e1compact\t")]
    if len(members) != 57:
        sys.exit(
            f"emit_descriptors: wide registry emitter produced {len(members)} member lines "
            "(expected 57)"
        )
    if len(geo) != 57:
        sys.exit(
            f"emit_descriptors: wide registry emitter produced {len(geo)} s2compact lines "
            "(expected 57)"
        )
    if len(e1) != 57:
        sys.exit(
            f"emit_descriptors: wide registry emitter produced {len(e1)} e1compact lines "
            "(expected 57)"
        )
    for ln in members:
        if ln.count("\t") != 2:
            sys.exit(f"emit_descriptors: wide registry line malformed: {ln[:80]!r}")
    write_file(WIDE_REGISTRY_TSV, "\n".join(members) + "\n", written)

    rows = []
    for ln in geo:
        _tag, key, bb, lane = ln.split("\t")
        rows.append(f'    ("{key}", {int(bb)}, {int(lane)}),')
    module = (
        "// @generated by metatheory/EmitWideRegistryProbe.lean via scripts/emit_descriptors.py"
        " — DO NOT EDIT BY HAND.\n"
        "//\n"
        "// THE S2 DELETION GEOMETRY (Epoch 1): per wide-registry member, the block base `bb`\n"
        "// (the face width the rotated BEFORE limbs sit at) and the graduated S2 lane base.\n"
        "// The deleted columns of a member are exactly the three bands\n"
        "//   [bb+S2_CARRIER_OFF, bb+B_SPAN) ∪ [bb+B_SPAN+S2_CARRIER_OFF, bb+2*B_SPAN)\n"
        "//     ∪ [lane_base, lane_base+S2_LANE_SPAN)\n"
        "// — the two rotated 1-felt Merkle–Damgård chain carrier/digest bands plus their\n"
        "// graduated chip-lane columns. The Lean emit deleted these from the committed wide\n"
        "// descriptors (`RotWideCompactS2.compactS2`, gated per member by `compactOk`); the Rust\n"
        "// trace producer must drop the SAME columns from its old-geometry rows\n"
        "// (`trace_rotated::compact_s2_columns`). One source: this table.\n"
        "//\n"
        "// ⚑ THE THREE BAND CONSTANTS ARE NOT DECLARED HERE. They used to be — as PYTHON STRING\n"
        "// LITERALS in `scripts/emit_descriptors.py` (`179` / `60` / `840`) inside a module whose\n"
        "// own header says DO NOT EDIT BY HAND. Only the per-member table came from Lean, so the\n"
        "// 178 -> 184 flag day moved the table and left the bands three columns' worth of a\n"
        "// geometry that no longer existed. They are now emitted from `RotWideCompactS2`'s own\n"
        "// spec lists via `EmitLayoutManifest.lean` and re-exported below: ONE source, in Lean.\n"
        "\n"
        "pub use super::layout_generated::{S2_CARRIER_OFF, S2_CARRIER_SPAN, S2_LANE_SPAN};\n"
        "\n"
        "/// Total deleted columns per member.\n"
        "pub const S2_DELETED_COLS: usize = 2 * S2_CARRIER_SPAN + S2_LANE_SPAN;\n"
        "\n"
        "/// `(registry key, bb, lane_base)` per wide member, in registry order.\n"
        "pub const S2_COMPACT_TABLE: &[(&str, usize, usize)] = &[\n"
        + "\n".join(rows)
        + "\n];\n"
    )
    GENERATED_RS[S2_COMPACT_RS] = module

    # THE E1 DELETION GEOMETRY (Epoch-1 SECOND flag-day): per wide-registry member, the DERIVED
    # kill-set of dead v1-face columns (POST-S2 coords), as ascending half-open runs. The Rust trace
    # producer drops EXACTLY these columns (`trace_rotated::compact_e1_columns`) so its rows match the
    # E1-compacted committed descriptor. One source: this table (from the Lean `deadColsE1`).
    e1_rows = []
    for ln in e1:
        _tag, key, spec = ln.split("\t", 2)
        intervals = _parse_e1_intervals(spec)
        body = ", ".join(f"({a}, {b})" for a, b in intervals)
        e1_rows.append(f'    ("{key}", &[{body}]),')
    e1_module = (
        "// @generated by metatheory/EmitWideRegistryProbe.lean via scripts/emit_descriptors.py"
        " — DO NOT EDIT BY HAND.\n"
        "//\n"
        "// THE E1 DELETION GEOMETRY (Epoch-1 SECOND flag-day): per wide-registry member, the\n"
        "// DERIVED per-member kill-set of DEAD v1-face columns — every column at index >= 90\n"
        "// referenced by NO surviving constraint / hash site / range (the retired aux band\n"
        "// 90..187 incl. the 60-col balance bit-decomposition, and the note/heap/refusal/cap-open\n"
        "// appendix scratch bands). Coordinates are POST-S2 (the columns as they sit in the\n"
        "// S2-compacted member), as ascending half-open `[start, end)` runs. The scan is capped at\n"
        "// the HOST width (`e1Ceiling`): the gentian floor-refuse aux block + the umem leg ride the\n"
        "// TOP of the member and are NOT producer-emitted (the gentian aux is filled at PROVE time by\n"
        "// `fill_refuse_aux`, AFTER the producer's `compact_e1`), so the kill-set must never reach\n"
        "// into them — else the deployed producer's pre-gentian `compact_e1` panics on a too-short row.\n"
        "// The Lean emit deleted these from the committed wide descriptors\n"
        "// (`RotWideCompactE1.compactE1`, gated per member by `compactE1Ok`);\n"
        "// the Rust trace producer must drop the SAME columns from its S2-compacted rows\n"
        "// (`trace_rotated::compact_e1_columns`, draining descending). One source: this table.\n"
        "\n"
        "/// `(registry key, &[(start, end), ...])` per wide member, in registry order — the\n"
        "/// ascending half-open POST-S2 kill-set runs. An empty slice means no E1-dead columns.\n"
        "pub const E1_COMPACT_TABLE: &[(&str, &[(usize, usize)])] = &[\n"
        + "\n".join(e1_rows)
        + "\n];\n"
    )
    GENERATED_RS[E1_COMPACT_RS] = e1_module


def split_bilateral(stdout: str, written):
    # key\tname\tjson  ->  <name>.json
    for line in stdout.splitlines():
        p = line.split("\t")
        if len(p) < 3:
            continue
        write_file(p[1] + ".json", p[2], written)


# ADDITIVE: the turn-wide cross-cell Σδ=0 conservation descriptor (foolable gap #6,
# `EmitCrossCellConservation.lean`). The emitter prints the BARE descriptor JSON (no
# `key\tname\tjson` TSV — `IO.println (emitVmJson2 crossCellConservationDescriptor)`), so the
# split routes its stdout verbatim into the single checked-in file.
CROSS_CELL_CONSERVATION_FILE = "dregg-cross-cell-conservation-v2.json"


# ⚑ DELETED 2026-07-31: `UMEM_COHORT_TSV` / `UMEM_COHORT_MULTI_TSV` (`umem-cohort-v1-…` and
# `umem-cohort-multidomain-v1-staged-registry.tsv`) with their `EmitUMemCohort{,Multi}.lean`
# drivers. The umem flip SHIPPED through the WELD, not the cohort: the weld builds its `umemOp`
# structurally in `weld_umem_into_descriptor_with_suffix` and never read either TSV, both files were
# byte-frozen at their 2026-06-25 birth while the welded registry was re-emitted seven times, and
# both call chains terminated in `sdk/tests/`.
#
# ⚑ DELETED 2026-07-31: `rotation-wide-umem-welded-registry-staged.tsv` (10,049,999 bytes) and
# `WIDE_UMEM_WELD_REGISTRY_FP`. See `split_wide_umem_weld` below — the welded members are still
# EMITTED and still CHECKED here, but what is installed is the ~8 KB derivation contract
# (`circuit/src/effect_vm/umem_weld_generated.rs`), not the members.


UMEM_WELD_RS_HEADER = "// @generated by metatheory/EmitWideUMemWeldRegistryProbe.lean via scripts/emit_descriptors.py — DO NOT EDIT BY HAND.\n//\n// THE WIDE+UMEM WELD DERIVATION CONTRACT. `circuit/descriptors/rotation-wide-umem-welded-registry-staged.tsv`\n// used to be a checked-in 10,049,999-byte artifact. It was a member-for-member 57/57 cover of\n// `rotation-wide-registry-staged.tsv` under one purely-ADDITIVE transform (name suffix, +7 trace\n// columns, main-table arity bump, two appended tables, one `umemOp` spliced before the trailing\n// fields-canonicity block) — so, over and above the separately FP-pinned bare wide registry, it\n// carried exactly the rows below. Every consumer parsed it straight back into an\n// `EffectVmDescriptor2`, and the deployed PROVER never opened it at all: it composes the same\n// object at runtime via `weld_umem_into_wide_descriptor`. So the verifier now derives its member\n// the same way the prover does, and this table is what the derivation is pinned to.\n//\n// Each row is Lean-emitted and covers EVERY degree of freedom the weld adds on top of the host:\n//\n//   * `domain`      — `EffectVmEmitUMemWeldWide.wideKeyUMemDomain key` (heap 1 / caps 2), the plane\n//                     the member's effect reconciles. A wrong domain binds NO descriptor on the wire.\n//   * `splice`      — where the `umemOp` sits in the welded constraint list. ⚑ LOCATED IN THE EMIT,\n//                     never recomputed: `fieldsCanonical9Wire` is applied to the ALREADY-welded\n//                     member, so the canonicity block lands PAST the op, and four order-preserving\n//                     passes (S2 / E1 / hardenLastRow / dropUnforcedPins) run after it. Rust used to\n//                     reproduce this as `constraints.len() - 2 * 8 * (7 + 12)` behind a\n//                     `debug_assert!` — a fail-closed check compiled out of release. That class is\n//                     deleted, not upgraded: the index comes from here and the boundary check runs\n//                     in every profile.\n//   * `trace_width` / `pi_count` / `constraints` / `name`\n//                   — the welded member's committed shape. The derivation is checked against all\n//                     four on every construction, so a table that drifts from the emit goes RED\n//                     instead of quietly minting a different AIR.\n//\n// ⚠ The welded leg's `vk_hash` is NO LONGER `blake3` of a committed JSON string (there is no longer\n// one). It is `blake3` of the descriptor's CANONICAL bytes\n// (`descriptor_ir2_canonical::canonical_effect_vm_descriptor2_bytes`), which every holder of the\n// object can recompute — measured to encode + strict-decode + re-encode byte-exactly on all 174\n// registry members. That is a WIRE-VISIBLE change to welded legs and nothing else: no VK rotates,\n// no AIR changes, no PI moves.\n\nuse crate::effect_vm_descriptors::UMemWeldRow;\n\n/// The Lean-emitted derivation contract, one row per wide-registry member, in registry order.\npub const UMEM_WELD_TABLE: &[UMemWeldRow] = &[\n"


def _derive_welded_member(wide: dict, domain: int, splice: int) -> dict:
    """The pure-JSON twin of Lean `weldUMemIntoWide` composed with the canonicity-block ordering,
    and of Rust `weld_umem_into_wide_descriptor`. A THIRD independent implementation on purpose:
    this is the reality gate, so it must not share code with either side it is checking."""
    d = json.loads(json.dumps(wide))
    base = d["trace_width"]
    d["name"] = d["name"] + WIDE_UMEM_WELD_SUFFIX
    d["trace_width"] = base + 7
    for t in d["tables"]:
        if t.get("sem") == "main":
            t["arity"] = base + 7
    d["tables"].append({"id": 6, "name": "umemory", "arity": 8, "sem": "umemory"})
    d["tables"].append({"id": 7, "name": "umem_boundary", "arity": 7, "sem": "umem_boundary"})
    d["constraints"].insert(splice, {
        "t": "umem_op",
        "guard": {"t": "var", "v": base + 6},
        "domain": domain,
        "key": {"t": "var", "v": base},
        "present": {"t": "var", "v": base + 1},
        "value": {"t": "var", "v": base + 2},
        "prev_present": {"t": "var", "v": base + 3},
        "prev_value": {"t": "var", "v": base + 4},
        "prev_serial": {"t": "var", "v": base + 5},
        "kind": "write",
    })
    return d


WIDE_UMEM_WELD_SUFFIX = "-umem-wide-welded-staged"


def split_wide_umem_weld(stdout: str, written):
    """`EmitWideUMemWeldRegistryProbe.lean` prints, per welded member, a `key\tname\tjson` MEMBER
    line and a `umemweld\t<key>\t<domain>\t<splice>\t<width>\t<pi>\t<constraints>\t<name>`
    CONTRACT line — exactly as `EmitWideRegistryProbe.lean` prints its `s2compact` / `e1compact`
    companions.

    ⚑ NOTHING FROM THE MEMBER LINES LANDS ON DISK. They are the REALITY GATE: each welded member
    is re-derived here, independently, from the bare wide member `rotation-wide-registry-staged.tsv`
    already carries plus its contract row, and the emit REFUSES unless all 57 agree exactly. That is
    where the end-to-end byte comparison the deleted 10 MB TSV used to provide still happens — it
    just does not get committed.

    What IS installed is `circuit/src/effect_vm/umem_weld_generated.rs`: the contract rows, which
    are every degree of freedom the weld adds on top of the (separately FP-pinned) bare wide member.
    """
    lines = [ln for ln in stdout.splitlines() if ln.strip()]
    members = [ln for ln in lines if not ln.startswith("umemweld\t")]
    contract = [ln for ln in lines if ln.startswith("umemweld\t")]
    if len(members) != 57:
        sys.exit(
            f"emit_descriptors: wide+umem weld emitter produced {len(members)} member lines "
            "(expected 57)"
        )
    if len(contract) != 57:
        sys.exit(
            f"emit_descriptors: wide+umem weld emitter produced {len(contract)} umemweld lines "
            "(expected 57)"
        )

    # ⚑ THE BARE HALF COMES FROM *THIS RUN*, NEVER FROM DISK.
    #
    # This read was `(DESC / WIDE_REGISTRY_TSV).read_text()` — the CHECKED-IN wide registry, i.e.
    # the artifact this very emit is about to replace. On a steady-state tree the two are equal and
    # the gate looked fine; the moment the Lean geometry moves, it compares THIS run's welded
    # members against the PREVIOUS run's bare members, they differ at `trace_width` / `constraints`
    # / `tables`, and the emit refuses — reporting the derivation as broken when the derivation is
    # correct and the on-disk file is simply old. Measured 2026-08-01: after the key-nonet flag day
    # (`76c3f7b9b`, pre-limbs 184 -> 187) this made the FIRST re-emit across the flag day impossible,
    # which is the exact run the geometry change requires. A gate that can only pass when nothing
    # changed is not a gate on the emission.
    #
    # `EmitWideRegistryProbe.lean` is emitter #4 and this one is #7, both handed the same `written`
    # buffer, so the freshly-emitted bare registry is always in hand here. There is NO disk
    # fallback: if it is absent the EMITTERS order was changed underneath this gate, and reading a
    # stale file instead is how the gate would go quietly blind again.
    fresh_wide = written.get(WIDE_REGISTRY_TSV)
    if fresh_wide is None:
        sys.exit(
            f"emit_descriptors: {WIDE_REGISTRY_TSV} was not emitted before the wide+umem weld "
            "probe, so the reality gate has no BARE half to re-derive from. It must never fall "
            "back to the checked-in file — that compares this run against the artifact it is "
            "replacing. Restore the EMITTERS order (EmitWideRegistryProbe.lean before "
            "EmitWideUMemWeldRegistryProbe.lean)."
        )
    bare = {}
    for ln in fresh_wide.splitlines():
        if not ln.strip():
            continue
        k, _n, j = ln.split("\t", 2)
        bare[k] = j

    rows = []
    for m, c in zip(members, contract):
        if m.count("\t") != 2:
            sys.exit(f"emit_descriptors: wide+umem weld member line malformed: {m[:80]!r}")
        mkey, mname, mjson = m.split("\t", 2)
        parts = c.split("\t")
        if len(parts) != 8:
            sys.exit(f"emit_descriptors: umemweld line malformed: {c[:80]!r}")
        _tag, key, domain, splice, tw, pi, nc, name = parts
        if key != mkey or name != mname:
            sys.exit(
                f"emit_descriptors: umemweld row {key}/{name} is out of step with its member line "
                f"{mkey}/{mname} — the emitter must print the contract row directly after its member"
            )
        if key not in bare:
            sys.exit(f"emit_descriptors: welded key {key} is not a bare wide registry key")
        want = json.loads(mjson)
        got = _derive_welded_member(json.loads(bare[key]), int(domain), int(splice))
        if got != want:
            differing = sorted(k for k in set(got) | set(want) if got.get(k) != want.get(k))
            sys.exit(
                f"emit_descriptors: REALITY GATE FAILED for {key} — the welded member the Lean emit "
                f"printed is NOT `weld(bare_wide[{key}], domain={domain}, splice={splice})`; they "
                f"differ at {differing}. The derivation the deployed prover and BOTH verifiers run "
                "would mint a different AIR than the emit committed. Refusing the install."
            )
        if int(tw) != want["trace_width"] or int(pi) != want["public_input_count"] \
                or int(nc) != len(want["constraints"]):
            sys.exit(
                f"emit_descriptors: umemweld row {key} disagrees with its own member on shape "
                f"(row {tw}/{pi}/{nc} vs member {want['trace_width']}/"
                f"{want['public_input_count']}/{len(want['constraints'])})"
            )
        rows.append(
            f'    UMemWeldRow {{ key: "{key}", domain: {int(domain)}, splice: {int(splice)}, '
            f"trace_width: {int(tw)}, pi_count: {int(pi)}, constraints: {int(nc)}, "
            f'name: "{name}" }},'
        )

    payload = "".join(ln + "\n" for ln in contract)
    fp = hashlib.sha256(payload.encode()).hexdigest()
    module = (
        UMEM_WELD_RS_HEADER
        + "\n".join(rows)
        + "\n];\n\n"
        + "/// sha256 of the Lean `umemweld` companion lines this table was rendered from — the byte\n"
        + "/// identity of the welded descriptor set, and half of `dregg_epoch::local_manifest`'s\n"
        + "/// `registry_fp` (it replaces the deleted `WIDE_UMEM_WELD_REGISTRY_FP`, which was the\n"
        + "/// sha256 of the deleted TSV).\n"
        + f'pub const UMEM_WELD_TABLE_FP: &str = "{fp}";\n'
    )
    GENERATED_RS[UMEM_WELD_RS] = module


def split_by_name(stdout: str, written):
    """`EmitByName.lean` prints one `<filename>\tjson` line per checked-in by-name descriptor —
    the surface `circuit/src/descriptor_by_name.rs::descriptor_by_name()` serves to `bridge/` and
    `wire/` at verify time.

    Routes each to `circuit/descriptors/by-name/<filename>` (the `by-name/` prefix makes the key
    relative to DESC, so install/FP/provenance all treat these exactly like the main set). This is
    what deletes the old UNGATED hand-transcription hop between the Lean `#guard` golden and the
    deployed bytes — the hop `predicate-arith.json` drifted through."""
    lines = [ln for ln in stdout.splitlines() if ln.strip()]
    if not lines:
        sys.exit("emit_descriptors: by-name emitter produced no lines")
    for ln in lines:
        if ln.count("\t") != 1:
            sys.exit(f"emit_descriptors: by-name line malformed (want `file\\tjson`): {ln[:80]!r}")
        filename, blob = ln.split("\t", 1)
        if not filename.endswith(".json"):
            sys.exit(f"emit_descriptors: by-name key is not a .json file: {filename!r}")
        if not blob.startswith('{"name":"'):
            sys.exit(
                f"emit_descriptors: by-name {filename} payload is not a descriptor JSON: {blob[:60]!r}"
            )
        # Reproduce the file's checked-in trailing-newline convention (see the frozenset above).
        if filename in BY_NAME_NEWLINE_TERMINATED:
            blob += "\n"
        write_file(f"by-name/{filename}", blob, written)


def split_seam_specs(stdout: str, written):
    """`EmitSeamSpecs.lean` prints one `<filename>\tjson` line per checked-in SeamSpec or
    PiPort census, routed to `circuit/descriptors/seams/<filename>`.

    These artifacts were once deliberately outside the whole-surface regen while the emitter's
    imported seam family was untracked and did not elaborate. The family is now landed and proved;
    leaving its renderer outside `EMITTERS` makes every descriptor flag day either a manual second
    ceremony or a routing-gap refusal. Buffering the rows here also preserves the regen driver's
    important property: no descriptor or seam byte reaches disk until the complete emission has
    succeeded and the authorization gate has passed.

    The checked-in convention is bare JSON with no trailing newline. Parse every payload before
    preserving those exact bytes: `ports.json` is a non-empty array and every other row is a seam
    object with two named ends. Structural and fingerprint-level validation remains in
    `circuit-prove/tests/seam_specs.rs`; this is the routing/type wall, not its twin.
    """
    lines = [ln for ln in stdout.splitlines() if ln.strip()]
    if not lines:
        sys.exit("emit_descriptors: seam emitter produced no lines")
    for ln in lines:
        if ln.count("\t") != 1:
            sys.exit(f"emit_descriptors: seam line malformed (want `file\\tjson`): {ln[:80]!r}")
        filename, blob = ln.split("\t", 1)
        if Path(filename).name != filename or not filename.endswith(".json"):
            sys.exit(f"emit_descriptors: seam key is not a plain .json filename: {filename!r}")
        try:
            payload = json.loads(blob)
        except json.JSONDecodeError as e:
            sys.exit(
                f"emit_descriptors: seam {filename} payload is not JSON ({e}): {blob[:60]!r}"
            )
        if filename == "ports.json":
            if not isinstance(payload, list) or not payload:
                sys.exit("emit_descriptors: seams/ports.json must be a non-empty JSON array")
        elif not (
            isinstance(payload, dict)
            and isinstance(payload.get("name"), str)
            and isinstance(payload.get("left"), dict)
            and isinstance(payload.get("right"), dict)
        ):
            sys.exit(
                f"emit_descriptors: seam {filename} is not a SeamSpec object with named ends"
            )
        write_file(f"seams/{filename}", blob, written)


def split_table_airs(stdout: str, written):
    """`EmitTableAirs.lean` prints one `<filename>\tjson` line per checked-in SHARED table AIR —
    the same `<file>\tjson` shape as `EmitByName.lean` — routed to
    `circuit/descriptors/table-airs/<filename>`.

    ⚑ **The emitter existed and was never invoked.** `EmitTableAirs.lean` has been the byte source
    for `table-airs/*.json` since those artifacts landed (2026-08-01), and it was absent from
    `EMITTERS`, so the seven files were checked in with NO emitter reproducing them. Two things
    followed, and the second is the expensive one:

      * the drift gate could not see them — the checked-in bytes and the Lean emission were free to
        diverge exactly the way `by-name/predicate-arith.json` once did; and
      * the coverage check at the END of this driver counts any descriptor no emitter reproduced as
        a ROUTING GAP and refuses the whole install — so these seven blocked EVERY re-emit of every
        other descriptor, which is how a geometry flag day sat un-re-emitted.

    Unlike `by-name/`, every artifact carries a trailing newline, so there is no per-file convention
    set to keep in sync: the newline `IO.println` produces is the newline on disk.

    ⚑ **TWO PAYLOAD SHAPES, and the second is a FAMILY.** `EmitTableAirs.lean` has two routing
    tables and two renderers (`EmitTableAirs.lean:28`, `:49`): `tableAirs` renders a singleton with
    `emitTableAirJson`, and `tableAirFamilies` renders a JSON ARRAY with `emitTableAirFamilyJson`
    (`Dregg2/Circuit/TableAirIR.lean:782-793`) — the wire form of a table AIR that is a SCHEMA
    rather than one object, element `i` being arity `i + 1`. The Rust side has decoded the array
    since the same commit (`circuit/src/table_air.rs:1029` include_str!s it,
    `parse_table_air_family` walks it, `exact_public_table_air_for` selects a member).

    This guard used to be `blob.startswith('{"name":"')` — a prefix test that hard-coded the
    SINGLETON grammar. `17b138e1f` landed the family end to end (Lean renderer, artifact, Rust
    parser) and did not reach here, so the emit step exited 1 on
    `dregg-ir2-exact-public-v1.json` and took the whole drift gate down with it for every lane.
    The array is not a regression; the prefix test was the stale side.

    The replacement PARSES rather than sniffs, so it is strictly stronger than what it replaces (a
    truncated or half-flushed blob now fails too), and it still writes `blob` VERBATIM — nothing
    here reserializes, because these bytes are FP/VK-pinned."""
    def table_air_object(v) -> bool:
        return (
            isinstance(v, dict)
            and isinstance(v.get("name"), str)
            and v.get("kind") == "table_air"
        )

    lines = [ln for ln in stdout.splitlines() if ln.strip()]
    if not lines:
        sys.exit("emit_descriptors: table-airs emitter produced no lines")
    for ln in lines:
        if ln.count("\t") != 1:
            sys.exit(
                f"emit_descriptors: table-airs line malformed (want `file\\tjson`): {ln[:80]!r}"
            )
        filename, blob = ln.split("\t", 1)
        if not filename.endswith(".json"):
            sys.exit(f"emit_descriptors: table-airs key is not a .json file: {filename!r}")
        try:
            payload = json.loads(blob)
        except json.JSONDecodeError as e:
            sys.exit(
                f"emit_descriptors: table-airs {filename} payload is not JSON ({e}): {blob[:60]!r}"
            )
        if isinstance(payload, list):
            if not payload:
                sys.exit(
                    f"emit_descriptors: table-airs {filename} is an EMPTY family array — a family "
                    "with no members would install a file `exact_public_table_air_for` can only "
                    "refuse"
                )
            bad = [i for i, m in enumerate(payload) if not table_air_object(m)]
            if bad:
                sys.exit(
                    f"emit_descriptors: table-airs {filename} family member(s) {bad[:5]} are not "
                    'table-AIR objects (want `{"name": str, "kind": "table_air", ...}`)'
                )
        elif not table_air_object(payload):
            sys.exit(
                f"emit_descriptors: table-airs {filename} payload is neither a table-AIR object "
                "nor a family array of them (want `{\"name\": str, \"kind\": \"table_air\", ...}` "
                f"or a non-empty list of those): {blob[:60]!r}"
            )
        write_file(f"table-airs/{filename}", blob + "\n", written)


def split_cert_f(stdout: str, written):
    """`EmitCertF.lean` prints the bare descriptor JSON via `IO.println`. The checked-in artifact
    carries NO trailing newline, so strip the one `IO.println` adds."""
    blob = stdout.rstrip("\n")
    if not blob.startswith('{"name":"cert-f"'):
        sys.exit(f"emit_descriptors: cert-f emitter produced unexpected output: {blob[:80]!r}")
    write_file(CERT_F_FILE, blob, written)


def split_cert_f_market4(stdout: str, written):
    """`EmitCertFMarket4.lean` — same convention as `EmitCertF.lean` (bare JSON, no trailing
    newline in the checked-in artifact)."""
    blob = stdout.rstrip("\n")
    if not blob.startswith('{"name":"cert-f"'):
        sys.exit(
            f"emit_descriptors: cert-f-market4 emitter produced unexpected output: {blob[:80]!r}"
        )
    write_file(CERT_F_MARKET4_FILE, blob, written)


def split_cross_cell_conservation(stdout: str, written):
    """`EmitCrossCellConservation.lean` emits the bare descriptor JSON via `IO.println`
    (no TSV prefix), so its stdout is the descriptor JSON + one trailing newline — exactly
    the checked-in file's bytes. Route the stdout VERBATIM (the trailing `\\n` from
    `IO.println` is part of the checked-in artifact; do NOT strip it)."""
    if not stdout.startswith('{"name":"dregg-cross-cell-conservation-v2"'):
        sys.exit(
            f"emit_descriptors: cross-cell-conservation emitter produced unexpected output: {stdout[:80]!r}"
        )
    write_file(CROSS_CELL_CONSERVATION_FILE, stdout, written)


# ---- FP rewriting -----------------------------------------------------------

def compute_fp_rewrites(written: dict[str, str]) -> tuple[dict[Path, str], int]:
    """For every emitted descriptor file, recompute sha256 and rewrite the
    matching `*_FP` constant IN MEMORY. Returns ({rust_path: new_text} for the
    files whose text actually changes, count of FP constants matched)."""
    # file -> sha256
    file_hash = {
        f: hashlib.sha256(content.encode()).hexdigest()
        for f, content in written.items()
    }
    updated = 0
    changes: dict[Path, str] = {}
    for rust in RUST_FP_FILES:
        if not rust.exists():
            continue
        text = rust.read_text()
        c2f = const_to_file(text)
        # invert: file -> set of json-const names
        file2consts: dict[str, list[str]] = {}
        for const, f in c2f.items():
            file2consts.setdefault(f, []).append(const)
        new_text = text
        for f, consts in file2consts.items():
            if f not in file_hash:
                continue
            h = file_hash[f]
            for jsonconst in consts:
                # The FP const shares the json-const prefix: X_JSON -> X_FP, but
                # bespoke pairs (e.g. V3_STAGED_REGISTRY_TSV/_FP) need a lookup by
                # the include_str adjacency. We match the FP const whose body is a
                # sha256 and which is the textually-nearest const after this one
                # that ends in _FP. Simplest robust rule: derive candidates.
                candidates = []
                if jsonconst.endswith("_JSON"):
                    candidates.append(jsonconst[:-5] + "_FP")
                if jsonconst.endswith("_TSV"):
                    candidates.append(jsonconst[:-4] + "_FP")
                # generic: strip a known suffix token then add _FP
                for cand in candidates:
                    pat = re.compile(
                        r'(pub const ' + re.escape(cand) + r':\s*&str\s*=\s*\n?\s*")[0-9a-f]{64}(")'
                    )
                    if pat.search(new_text):
                        new_text, n = pat.subn(r'\g<1>' + h + r'\g<2>', new_text)
                        updated += n
                        break
        if new_text != text:
            changes[rust] = new_text
    return changes, updated


def install_and_stamp(written: dict[str, str]) -> None:
    """The INSTALL phase: diff the buffered emission against disk; a byte-changing
    descriptor install is ack-gated, provenance-stamped, and audit-logged. A generated-Rust-only
    change is byte-safe (it cannot re-key a descriptor) and installs without a VK-regeneration
    acknowledgement. A byte-identical emission whose bytes the stamp ALREADY attests is a silent
    no-op; one the stamp does not cover still has to be stamped (see provenance_stamp_gap)."""
    # Nothing installs a module the drift gate cannot see: every buffered generated module must
    # be declared in GENERATED_RS_PATHS, and every FP-bearing source in RUST_FP_FILES. Together
    # those two tuples ARE `guarded_paths()`, which is what `check-descriptor-drift.sh` snapshots.
    assert_generated_declared()
    assert_fp_files_declared()

    # Converge the generated modules onto rustfmt's shape BEFORE the diff, so what we compare
    # against disk is exactly what we would write — and equals what the pre-commit hook and
    # `cargo fmt --all -- --check` produce (see normalize_generated_rust).
    normalize_generated_rust()

    fp_changes, n_fp = compute_fp_rewrites(written)

    changed_desc = sorted(
        name for name, content in written.items()
        if not (DESC / name).exists() or (DESC / name).read_text() != content
    )
    changed_gen = {
        p: content for p, content in GENERATED_RS.items()
        if not p.exists() or p.read_text() != content
    }
    changed = (
        changed_desc
        + sorted(str(p.relative_to(ROOT)) for p in fp_changes)
        + sorted(str(p.relative_to(ROOT)) for p in changed_gen)
    )

    # The STAMP's obligation is COVERAGE, not a byte diff, and `changed` above cannot see it: a
    # descriptor already carrying exactly the Lean bytes but with no row in PROVENANCE.json is
    # invisible to every term of it. Ask the stamp directly.
    stamp_gap = provenance_stamp_gap(written)
    # `reasons` is what the operator is shown and what the audit row records — the byte change-set
    # AND the stamp's shortfall, so a stamp-only regen is never logged as "(stamp only)" with no
    # statement of what it was short of.
    reasons = changed + [f"{PROVENANCE_FILE}: {g}" for g in stamp_gap]

    if not changed and not stamp_gap:
        print(
            f"emit_descriptors: NO-OP — all {len(written)} descriptor files and "
            f"{n_fp} FP constants are byte-identical to the Lean emission, and "
            f"{PROVENANCE_FILE} already attests exactly that set."
        )
        return

    # A Lean-authored Rust projection is not a VK regeneration. Requiring the federation-rekey ACK
    # for a generated-module-only change made the safe half of a layout refactor impossible to run
    # through the canonical emitter. Geometry changes remain protected: because the Lean descriptor
    # emit reads the same RotatedLayout, moving a consumed group column also changes descriptor bytes
    # and therefore enters the ack-gated branch below.
    #
    # A stamp shortfall does NOT ride this branch: writing PROVENANCE.json is a provenance CLAIM
    # about which committed Lean tree minted these bytes, so it goes through the committed-source
    # gate like any other, even when not one descriptor byte moves.
    if not changed_desc and not fp_changes and not stamp_gap:
        for p, content in changed_gen.items():
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(content)
        print(
            f"emit_descriptors: GENERATED-RUST UPDATE — installed {len(changed_gen)} Lean-authored "
            "module(s); descriptor bytes and FP constants are unchanged (no VK regen)."
        )
        return

    # Re-checked at install: a sibling's edit landing mid-emit must not be stamped as committed.
    auth = require_committed_emit_source("this emission")

    for name in changed_desc:
        (DESC / name).write_text(written[name])
    for p, new_text in fp_changes.items():
        p.write_text(new_text)
    for p, content in changed_gen.items():
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content)

    desc_hashes = {name: sha256_hex(content.encode()) for name, content in written.items()}
    fp_hashes = {
        str(p.relative_to(ROOT)): sha256_hex(p.read_bytes())
        for p in RUST_FP_FILES if p.exists()
    }
    write_provenance(build_provenance("emit", auth, desc_hashes, fp_hashes))
    append_audit("emit", auth, reasons)
    if not changed:
        # The bytes were already the Lean emission — this run WITNESSED that (it re-derived every
        # descriptor and found no difference) and is recording it. `mode` stays "emit", which is the
        # true claim: these hashes come from the emitters, not from re-reading disk.
        print(
            f"emit_descriptors: STAMP-ONLY REGEN — all {len(written)} descriptor files were already "
            f"byte-identical to the Lean emission, but {PROVENANCE_FILE} did not attest "
            f"{len(stamp_gap)} of them; re-stamped from the emitted bytes (mode=emit, tree "
            f"{auth['tree'][:12]}…); audit row appended to {AUDIT_LOG_REL}."
        )
        return
    print(
        f"emit_descriptors: AUTHORIZED REGEN — installed {len(changed_desc)} changed "
        f"descriptor files + {len(fp_changes)} FP-bearing Rust files "
        f"(of {len(written)} emitted / {n_fp} FP constants); provenance stamped "
        f"(tree {auth['tree'][:12]}…); audit row appended to {AUDIT_LOG_REL}."
    )


# The accepted flags, in ONE place. The usage message below is RENDERED from this rather than
# transcribed beside it — the transcription had already lagged (`--strict` and, the moment it
# landed, `--list-guarded-paths` were missing from the message that claims to enumerate them).
ACCEPTED_FLAGS = (
    "--list-emitter-modules",
    "--list-guarded-paths",
    "--verify-by-name-routing",
    "--verify-provenance",
    "--self-test-workflow-scope",
    "--self-test-provenance",
    "--rev",  # takes a value: `--rev HEAD` or `--rev=HEAD`
)


# ── the workflow-scope red-proof ──────────────────────────────────────────────────────────────
# `_wf_parse`'s `working-directory` scope decides where EVERY path in `verify_workflow_refs`
# resolves, and when it leaked (see that function's docstring) it produced both failure modes at
# once: eight false `WORKFLOW-GHOST` findings that no fix could clear, and fifteen real
# invocations silently deferred as "not checkable". Neither could be seen from the output —
# the reds looked like eight broken steps and the deferrals looked like coverage.
#
# So the scope gets its own can-it-go-red run, on SYNTHETIC workflows in a temp dir. Nothing in
# the repo is read or written. ~0s, no git, no Lean, no cargo.
_WF_SCOPE_CASES: tuple[tuple[str, str, dict[int, str]], ...] = (
    (
        "the leak itself: a shallower `- ` (`- cron:`) must not disable the reset",
        """
on:
  schedule:
    - cron: '0 6 * * *'
jobs:
  a:
    steps:
      - name: in metatheory
        working-directory: metatheory
        run: bash scripts/x.sh
      - name: at the root
        run: bash scripts/y.sh
""",
        {9: "metatheory", 11: ""},
    ),
    (
        "the key AFTER `run:` in the same item (ci.yml:192's shape)",
        """
jobs:
  a:
    steps:
      - run: cargo test
        working-directory: solana-lock
      - run: cargo build
""",
        {4: "solana-lock", 6: ""},
    ),
    (
        "a job-level `defaults.run.working-directory` reaches every run step, and stops at the "
        "next job",
        """
jobs:
  a:
    defaults:
      run:
        working-directory: extension
    steps:
      - run: ./build.sh
      - run: npm ci
  b:
    steps:
      - run: ./other.sh
""",
        {7: "extension", 8: "extension", 11: ""},
    ),
    (
        "`uses:` never inherits a cwd (it resolves against the workspace root)",
        """
jobs:
  a:
    defaults:
      run:
        working-directory: extension
    steps:
      - uses: ./.github/actions/thing
      - run: ./build.sh
""",
        {7: "", 8: "extension"},
    ),
    (
        # ⓘ This one is a FORWARD guard, not a refutation: the pre-2026-08-01 parser passed it
        # (it never reset anything, so it could not clear a key early). It exists because the
        # replacement pops a stack of open list items, which is a new way to get this wrong.
        # The four cases above each FAIL against the old parser — verified, not assumed.
        "a nested sequence inside a step does not clear that step's key",
        """
jobs:
  a:
    steps:
      - name: nested
        working-directory: wasm
        with:
          args:
            - --headless
            - --chrome
        run: wasm-pack test
      - run: cargo test
""",
        {10: "wasm", 11: ""},
    ),
)


def self_test_workflow_scope() -> int:
    import tempfile

    bad = 0
    print("emit_descriptors --self-test-workflow-scope (synthetic workflows in a temp dir)")
    with tempfile.TemporaryDirectory() as td:
        for name, text, want in _WF_SCOPE_CASES:
            p = Path(td) / "wf.yml"
            p.write_text(text.lstrip("\n"))
            got = {ln: wd for ln, _k, wd, _b in _wf_parse(p, "wf.yml")}
            # FLOOR: a parser that harvests nothing must not read as clean.
            if len(got) < len(want):
                print(f"  [BAD] {name}: parsed {len(got)} step(s), expected at least {len(want)}")
                bad += 1
                continue
            wrong = {ln: (got.get(ln), w) for ln, w in want.items() if got.get(ln) != w}
            if wrong:
                print(f"  [BAD] {name}: {wrong} (got/want)")
                bad += 1
            else:
                print(f"  [ok ] {name}")
    print(f"emit_descriptors --self-test-workflow-scope: "
          f"{'OK' if bad == 0 else str(bad) + ' CASE(S) WRONG'}")
    return 1 if bad else 0


# ── the provenance red-proof ──────────────────────────────────────────────────────────────────
#
# ⚑ `--verify-provenance` IS A NEGATIVE ASSERTION ("nothing has drifted"), which passes just as
# happily on a broken reader as on a clean tree — and it spent its whole life passing on nothing,
# because it was invoked by NO `.sh`, NO `.yml` and NO `.py`: thirteen references, every one of
# them prose. So before it is wired into `scripts/local-gates.sh` it has to be shown to go RED on
# each defect it claims to catch and GREEN when that defect is removed. Both directions, on
# SCRATCH COPIES; the shared working tree is never touched.
#
# The four mutations are the four shapes the ten table-AIR stamps were actually in:
#   * a descriptor byte moved while the stamp did not      (STAMP MISMATCH — 8 of the 10)
#   * a descriptor on disk with no row in the stamp        (MISSING ROW    — 2 of the 10)
#   * a row in the stamp with no descriptor behind it      (the deleted/renamed direction)
#   * a stamp recording source_dirty=true                 (the "looks taken and isn't" stamp)
# ...plus the CONTROL (unmutated HEAD must be green — otherwise every red below is free) and the
# VACUITY FLOOR (a walk that finds nothing must refuse, not report PASS).
def _findings_of(doors: bool = False) -> tuple[set[str], str]:
    """The finding SET against the currently-bound roots, plus any FATAL text.

    A FATAL (the vacuity floor, a missing stamp) raises SystemExit rather than returning a
    finding, and that is the point: it is a refusal to report at all, not a report. Returned as
    the second element so a case can assert on it."""
    out, err = io.StringIO(), io.StringIO()
    try:
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            findings, _ = _verify_provenance_findings(doors=doors)
        return set(findings), ""
    except SystemExit as exc:
        return set(), str(exc.code) if exc.code and not isinstance(exc.code, int) else "FATAL"


def self_test_provenance() -> int:
    bad = 0
    results: list[tuple[bool, str, str]] = []

    def case(ok: bool, name: str, detail: str = "") -> None:
        nonlocal bad
        if not ok:
            bad += 1
        results.append((ok, name, detail))

    print("emit_descriptors --self-test-provenance (scratch copies only; the working tree is "
          "never touched)")

    # (0) THE VACUITY FLOOR, first and on a synthetic root: a stamp whose legs are all `{}` beside
    # an empty descriptor directory must REFUSE, not report PASS over zero artifacts. Every other
    # case below is worthless if the checker can report green having compared nothing.
    with tempfile.TemporaryDirectory() as td:
        fake = Path(td)
        (fake / "circuit" / "descriptors").mkdir(parents=True)
        (fake / "circuit" / "descriptors" / PROVENANCE_FILE).write_text(json.dumps(
            {"descriptor_sha256": {}, "by_name_sha256": {}, "fp_file_sha256": {}}))
        with rooted_at(fake):
            found, fatal = _findings_of()
        case(fatal != "" and "vacuous PASS" in fatal,
             "VACUITY FLOOR: an empty walk refuses instead of reporting PASS",
             f"fatal={fatal[:120]!r} findings={len(found)}")

    with detached_worktree("HEAD", "self-test-provenance") as (wt, sha):
        desc = wt / "circuit" / "descriptors"
        stamp_path = desc / PROVENANCE_FILE
        pristine_stamp = stamp_path.read_bytes()

        # Pick the victim from the stamp itself rather than naming a file: a hardcoded filename
        # is a transcription that rots the day the artifact is renamed, and a red-proof that
        # silently stops exercising its own subject is the failure mode this file keeps finding.
        stamp = json.loads(pristine_stamp)
        subdir_legs = sorted(k for k in stamp if k.endswith("_sha256")
                             and k not in ("descriptor_sha256", "by_name_sha256",
                                           "fp_file_sha256"))
        case(bool(subdir_legs),
             "the stamp carries a descriptor SUBDIRECTORY leg for this proof to bite on",
             "none found — the table-airs leg (the ten shared table AIRs) is gone from the stamp")
        for leg in subdir_legs[:1]:
            sub = desc / leg[: -len("_sha256")]
            victim_name = sorted(stamp[leg])[0]
            victim = sub / victim_name
            pristine_bytes = victim.read_bytes()
            kind = leg[: -len("_sha256")]

            with rooted_at(wt):
                # THE FULL-PATH RUN, once: every leg including the four "committed reference to an
                # uncommitted target" doors. The delta cases below run with `doors=False` for
                # budget (see `_verify_provenance_findings`); this run is what keeps that
                # justified — if the full path ever stops working, the skip stops being harmless
                # and this case says so before any delta is trusted.
                full, ffatal = _findings_of(doors=True)
                case(ffatal == "", "FULL PATH (all legs, incl. the four doors) executes",
                     f"fatal={ffatal[:200]!r}")

                # THE BASELINE — whatever HEAD's findings are today. Not asserted to be empty;
                # asserted to be what every mutation below is measured AGAINST.
                base, fatal = _findings_of()
                case(fatal == "", f"BASELINE at HEAD ({sha[:12]}) computes without refusing",
                     f"fatal={fatal[:200]!r}")
                case(base <= full,
                     "the baseline is a SUBSET of the full-path findings (the skipped doors "
                     "only ever ADD findings, never mask one)",
                     f"baseline-only={sorted(base - full)[:2]}")
                if base:
                    print(f"  [ i ] baseline at HEAD carries {len(base)} pre-existing finding(s) "
                          f"(NOT this gate's subject; each mutation is measured as a DELTA):")
                    for f in sorted(base):
                        print(f"        · {f[:150]}")

                def delta(label: str, want: str) -> None:
                    """One injected fault must add a finding NAMING IT, and remove none."""
                    got, ftl = _findings_of()
                    new, lost = got - base, base - got
                    case(ftl == "" and any(want in n and victim_name in n for n in new)
                         and not lost, label,
                         f"fatal={ftl[:80]!r} new={sorted(new)[:2]} lost={sorted(lost)[:2]}")

                # (1) STAMP MISMATCH — a descriptor byte moves, the stamp does not. This is 8 of
                # the 10 shapes measured at `ca0970378`.
                victim.write_bytes(pristine_bytes.replace(b"{", b"{ ", 1))
                delta(f"RED on a mutated byte in {kind}/{victim_name}",
                      "does NOT match its stamped sha256")

                # ...and back to EXACTLY the baseline the moment it is restored. The direction
                # that proves the red was the MUTATION and not the machinery — and equality with
                # the baseline (not merely "green") is what makes it a measurement.
                victim.write_bytes(pristine_bytes)
                got, ftl = _findings_of()
                case(ftl == "" and got == base,
                     "back to EXACTLY the baseline once the byte is restored",
                     f"delta={sorted(got ^ base)[:2]}")

                # (2) MISSING ROW — the artifact ships, the stamp does not cover it. This is the
                # other 2 of the 10 (`chip-v1`, `chip-state16-v1`).
                dropped = json.loads(pristine_stamp)
                del dropped[leg][victim_name]
                stamp_path.write_text(json.dumps(dropped, indent=2) + "\n")
                delta(f"RED on a dropped stamp row for {victim_name}",
                      "NOT covered by the stamp")

                # (3) the other direction — a row with no artifact behind it (deleted/renamed).
                stamp_path.write_bytes(pristine_stamp)
                victim.unlink()
                delta(f"RED on a stamp row whose artifact is gone ({victim_name})",
                      "MISSING on disk")
                victim.write_bytes(pristine_bytes)

                # (4) a source_dirty=true stamp (pre-2026-11-06, or hand-edited). The emit can no
                # longer write one; the verify must still refuse one.
                dirty = json.loads(pristine_stamp)
                dirty["source_dirty"] = True
                stamp_path.write_text(json.dumps(dirty, indent=2) + "\n")
                got, ftl = _findings_of()
                new = got - base
                case(ftl == "" and any("source_dirty=true" in n for n in new) and not (base - got),
                     "RED on a source_dirty=true stamp",
                     f"new={sorted(new)[:1]}")
                stamp_path.write_bytes(pristine_stamp)

                # and back to the baseline, so (4) is a property of the stamp and not a latch.
                got, ftl = _findings_of()
                case(ftl == "" and got == base,
                     "back to EXACTLY the baseline once the stamp is restored",
                     f"delta={sorted(got ^ base)[:2]}")

    for ok, name, detail in results:
        print(f"  [{'ok ' if ok else 'BAD'}] {name}" + (f"  ({detail})" if not ok and detail else ""))
    print(f"emit_descriptors --self-test-provenance: "
          f"{'OK — ' + str(len(results)) + ' cases' if bad == 0 else str(bad) + ' CASE(S) WRONG'}")
    return 1 if bad else 0


# ── SCOPE ─ these three pairs are the ONLY copy, one per GATE MODE, and each prints on every
# run of ITS mode, pass or fail. They are NOT printed by the emit path or by the `--list-*`
# modes: `scripts/check-descriptor-drift.sh` consumes `--list-emitter-modules` and
# `--list-guarded-paths` on stdout line-by-line, and a banner there would be parsed as a module
# name. Three modes, three different questions — hence three pairs and not one. ────────────────
SCOPE_ANSWERS_VERIFY = (
    "at the named revision, checked out into a fresh clean detached worktree: does every "
    "committed file under circuit/descriptors/ (top level, by-name/, and every further "
    "subdirectory found by DISCOVERY) hash to the sha256 that same revision's PROVENANCE.json "
    "records for it, in BOTH directions, does the by-name routing table parsed out of "
    "EmitByName.lean plus every literal include_str/include_bytes target, first-party Lean "
    "import and workflow-invoked path resolve to a file that exists and is tracked, and does "
    "the stamp record source_dirty=false?"
)
SCOPE_DOES_NOT_ANSWER_VERIFY = (
    "whether the descriptors are STALE with respect to Lean. This is committed BYTES against "
    "the committed STAMP — a sha256 comparison, never a re-derivation; re-running the Lean "
    "emitters and diffing is scripts/check-descriptor-drift.sh, a separate gate. A stamp "
    "attesting a DIFFERENT (committed) Lean source tree PASSES here, and a stale "
    "fp_file_sha256 snapshot is printed rather than failed."
)

SCOPE_ANSWERS_SELFTEST_PROV = (
    "can the provenance checker still FIRE — on scratch copies inside a detached HEAD worktree, "
    "does each of four injected faults (a mutated descriptor byte, a dropped stamp row, a stamp "
    "row whose artifact is gone, a source_dirty=true stamp) add a finding "
    "that names that artifact and remove none, does restoring it return to EXACTLY the "
    "baseline, does an all-empty walk REFUSE instead of reporting PASS, and does the full "
    "doors-on path execute?"
)
SCOPE_DOES_NOT_ANSWER_SELFTEST_PROV = (
    "whether the descriptor set or its stamp is clean. HEAD findings are taken as a BASELINE, "
    "printed, and never asserted empty — every case is measured as a DELTA against them — so "
    "this row stays GREEN while circuit/descriptors carries real drift. The `provenance` row is "
    "what decides that; this one decides only that the instrument is not asleep."
)

SCOPE_ANSWERS_SELFTEST_WF = (
    "does _wf_parse compute the expected working-directory for every step of five SYNTHETIC "
    "workflow YAML fixtures written into a temp dir (a shallower `- ` must not clear the scope, "
    "a key after `run:` in the same item, a job-level defaults.run reaching every run step and "
    "stopping at the next job, `uses:` inheriting no cwd, a nested sequence inside a step), and "
    "did it harvest at least as many steps as each fixture expects?"
)
SCOPE_DOES_NOT_ANSWER_SELFTEST_WF = (
    "anything about THIS repository. It opens no tracked file and not one of "
    ".github/workflows/*.yml, so it says nothing about whether any workflow-invoked path exists "
    "or is tracked — that is verify_workflow_refs, which runs inside --verify-provenance."
)


def _print_scope(answers: str, does_not: str) -> None:
    print(f"ANSWERS:         {answers}", flush=True)
    print(f"DOES NOT ANSWER: {does_not}", flush=True)


def main():
    argv = sys.argv[1:]
    # `--rev` is the one flag that TAKES A VALUE, so it is consumed before the membership check
    # below — which is an exact-match filter and would otherwise reject the revision itself as an
    # unknown argument. Both spellings, because the shell gates in this repo accept both.
    rev: str | None = None
    rest: list[str] = []
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--rev":
            if i + 1 >= len(argv):
                sys.exit("emit_descriptors: --rev needs a revision (e.g. `--rev HEAD`)")
            rev = argv[i + 1]
            i += 2
            continue
        if a.startswith("--rev="):
            rev = a[len("--rev="):]
            if not rev:
                sys.exit("emit_descriptors: --rev= needs a revision (e.g. `--rev=HEAD`)")
            i += 1
            continue
        rest.append(a)
        i += 1
    argv = rest
    # An unrecognized flag must REFUSE, not be ignored: every dispatch below is an `in argv`
    # membership test, so a bare-argv fall-through runs the REAL ack-gated emit. A typo'd or
    # imagined `--dry-run` would therefore have regenerated the descriptor set for real.
    unknown = [a for a in argv if a not in ACCEPTED_FLAGS]
    if unknown:
        sys.exit(
            f"emit_descriptors: unknown arguments {unknown!r} (expected none, or one of: "
            + ", ".join(ACCEPTED_FLAGS) + ")"
        )
    # ...and the same refusal for a value-taking flag attached to a mode that ignores it. A
    # `--rev` silently dropped by another mode would read as "I graded that revision".
    # `--rev` means: grade that revision (`--verify-provenance`), or stamp it (the bare emit,
    # which requires the checkout to BE that revision). Any other mode would silently drop it.
    if rev is not None and argv and not ({"--verify-provenance"} & set(argv)):
        sys.exit(f"emit_descriptors: --rev {rev!r} is only meaningful with --verify-provenance "
                 f"or the bare emit (got {argv!r}); refusing to ignore it.")
    if "--self-test-workflow-scope" in argv:
        _print_scope(SCOPE_ANSWERS_SELFTEST_WF, SCOPE_DOES_NOT_ANSWER_SELFTEST_WF)
        sys.exit(self_test_workflow_scope())
    if "--self-test-provenance" in argv:
        _print_scope(SCOPE_ANSWERS_SELFTEST_PROV, SCOPE_DOES_NOT_ANSWER_SELFTEST_PROV)
        sys.exit(self_test_provenance())
    if "--verify-provenance" in argv:
        _print_scope(SCOPE_ANSWERS_VERIFY, SCOPE_DOES_NOT_ANSWER_VERIFY)
        verify_provenance(rev=rev)
        return
    if "--verify-by-name-routing" in argv:
        # Static, seconds, no Lean and no cargo — usable while the emit is blocked.
        findings = verify_by_name_routing()
        if findings:
            sys.stderr.write("verify-by-name-routing: FAIL\n")
            for f in findings:
                sys.stderr.write(f"  - {f}\n")
            sys.exit(1)
        print("verify-by-name-routing: PASS — the routing table and the checked-in "
              "by-name set cover each other, every routed artifact is stamped, and every "
              "literal include_str!/include_bytes! target, first-party Lean import, and "
              "path invoked by a tracked workflow exists and is tracked.")
        return
    if "--list-guarded-paths" in argv:
        # The change-set `install_and_stamp` can rewrite (see guarded_paths). No Lean run, so
        # `scripts/check-descriptor-drift.sh` can SNAPSHOT exactly what this driver may touch
        # instead of keeping its own transcription of it.
        print("\n".join(guarded_paths()))
        return
    if "--list-emitter-modules" in argv:
        # The build set the emitters need (see emitter_modules). No Lean run; pure source
        # scan, so `scripts/check-descriptor-drift.sh` can build exactly what it runs.
        print("\n".join(emitter_modules()))
        return
    if argv:
        # Recognized, but no mode claimed it. Refuse rather than fall through to the emit.
        sys.exit(f"emit_descriptors: {argv!r} names no mode (expected none, or one of: "
                 + ", ".join(ACCEPTED_FLAGS) + ")")

    if not (META / "lakefile.lean").exists() and not (META / "lakefile.toml").exists():
        sys.exit(f"emit_descriptors: not a lake project at {META}")
    written: dict[str, str] = {}

    # Fail fast, before any `lake build`: an uncommitted closure can never be stamped, and a
    # named revision must be the one checked out.
    if rev is not None:
        require_checkout_at(rev)
    require_committed_emit_source("the emit")

    rs_evd = (ROOT / "circuit" / "src" / "effect_vm_descriptors.rs").read_text()
    c2f = const_to_file(rs_evd)
    dn2file = ir2_defname_to_file(rs_evd, c2f)

    build_emitter_modules()
    print("emit_descriptors: running Lean emitters (source of truth)...")
    for lean in EMITTERS:
        print(f"  -> {lean}")
        out = emit(lean)
        if lean.endswith("EmitAllJson.lean"):
            split_v1(out, written)
        elif lean.endswith("EmitAllJsonV2.lean"):
            split_ir2(out, dn2file, written)
        elif lean.endswith("EmitRotationV3.lean"):
            split_rotation(out, written)
        elif lean.endswith("EmitWideRegistryProbe.lean"):
            split_wide_registry(out, written)
        elif lean.endswith("EmitBilateralLegs.lean"):
            split_bilateral(out, written)
        elif lean.endswith("EmitLayoutManifest.lean"):
            split_layout(out, written)
        elif lean.endswith("EmitCrossCellConservation.lean"):
            split_cross_cell_conservation(out, written)
        elif lean.endswith("EmitWideUMemWeldRegistryProbe.lean"):
            split_wide_umem_weld(out, written)
        elif lean.endswith("EmitByName.lean"):
            split_by_name(out, written)
        elif lean.endswith("EmitSeamSpecs.lean"):
            split_seam_specs(out, written)
        elif lean.endswith("EmitTableAirs.lean"):
            split_table_airs(out, written)
        elif lean.endswith("EmitCertFMarket4.lean"):
            split_cert_f_market4(out, written)
        elif lean.endswith("EmitCertF.lean"):
            split_cert_f(out, written)
        else:
            sys.exit(f"emit_descriptors: no split routine for {lean}")

    # Coverage check: every checked-in descriptor file must have been (re)emitted.
    # (PROVENANCE.json is the regen-control stamp, not an emitted artifact.)
    #
    # RECURSES (rglob, relative-keyed). It used to be `DESC.iterdir()` filtered on `p.is_file()` —
    # and `by-name/` is a DIRECTORY, so the entire deployed dispatch surface was silently exempt
    # from this gate: no by-name file was ever in `written`, nothing was ever reported missing, and
    # the drift checker's snapshot->emit->diff therefore left by-name byte-identical on both sides
    # (an unconditional PASS for any content whatsoever). That exemption is how a 5-wide re-authoring
    # of the 24-wide `predicate-arith` descriptor reached production. A by-name file no emitter
    # reproduces is now a routing-gap FAILURE, like every other descriptor.
    on_disk = {
        str(p.relative_to(DESC)) for p in DESC.rglob("*") if p.is_file()
    }
    missed = on_disk - set(written) - {PROVENANCE_FILE} - COVERAGE_EXEMPT
    if missed:
        sys.exit(
            "emit_descriptors: these checked-in descriptors were NOT reproduced "
            "by any emitter (routing gap):\n  " + "\n  ".join(sorted(missed))
        )

    install_and_stamp(written)


if __name__ == "__main__":
    main()
