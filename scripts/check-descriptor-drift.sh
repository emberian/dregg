#!/usr/bin/env bash
# check-descriptor-drift.sh — THE Lean<->JSON cache-freshness GATE (CI / pre-commit).
#
# The checked-in descriptors are a CACHE of the Lean emission (Lean is the source
# of truth). This GENERATE-FRESH gate regenerates them from the verified Lean
# emission and fails if the result differs from what is checked in. This is the
# only honest Lean<->JSON guard: a `sha256(bytes) == committed-FP` rehash proves
# only that a file matches the hash committed beside it (self-consistency) — it
# CANNOT catch a committed JSON gone stale while the Lean emission moved underneath
# it. Re-deriving from Lean is the whole point; this script re-derives.
#
# Usage:  scripts/check-descriptor-drift.sh
#         scripts/check-descriptor-drift.sh --rev HEAD     # clean extract (churn-safe)
#         scripts/check-descriptor-drift.sh --rev <sha>
# Exit:   0 = no drift; nonzero = the Lean emission and the checked-in artifacts
#         disagree (run scripts/emit-descriptors.sh and commit).
#
# ── ⚑ WHY `--rev` EXISTS (added 2026-08-02) ────────────────────────────────────
# Without it this gate grades THE WORKING TREE, and in a shared tree that means ANY
# lane's uncommitted WIP can hold it down for everybody. Measured: a sibling's
# in-flight table-AIR emitter (`ExactPublicTableEmit.lean`, untracked) wrote
# `circuit/descriptors/table-airs/dregg-ir2-exact-public-v1.json` as a JSON ARRAY
# where the loader expects an OBJECT, and the gate died in the emit step —
#     emit_descriptors: ... payload is not a table-AIR JSON: '[{"name": ...
# — for a lane that needed it to confirm byte-identity and whose own change was in
# HEAD and fine. None of the failing material was in HEAD. The blocked lane
# correctly refused to "fix" someone else's mid-flight file to clear its own gate,
# and had no other move.
#
# `--rev` is that other move: materialise the revision in a DETACHED, `git status`-
# clean worktree and run the whole gate there, so another lane's churn is
# structurally irrelevant to the verdict rather than politely worked around.
# `scripts/check-guard-modules.py --rev HEAD` is the in-repo precedent and this
# mirrors its interface. It uses a WORKTREE where that one uses `git archive`,
# because this gate's tail (`check-drift-taxonomy.sh`) needs a working `git` to
# resolve its base ref — an archive extract has no `.git` and the taxonomy leg
# would "skip cleanly", i.e. silently stop being a gate.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
ORIG_ROOT="$ROOT"
REV=""
FAIL_FAST=0
while [ $# -gt 0 ]; do
  case "$1" in
    --rev) REV="${2:-}"; [ -n "$REV" ] || { echo "check-descriptor-drift: --rev needs a revision" >&2; exit 2; }; shift 2 ;;
    --rev=*) REV="${1#--rev=}"; shift ;;
    --fail-fast) FAIL_FAST=1; shift ;;
    -h|--help) sed -n '2,40p' "$0"; exit 0 ;;
    *) echo "check-descriptor-drift: unknown argument '$1' (see --help)" >&2; exit 2 ;;
  esac
done

# ── SCOPE ─ this printf is the ONLY copy; it prints on every run, pass or fail. ───────
printf 'ANSWERS:         %s\nDOES NOT ANSWER: %s\n' \
  'does re-running the Lean emitters at the graded revision (scripts/emit-descriptors.sh, deliberately with NO regen ack) reproduce every path in emit_descriptors.py --list-guarded-paths byte-for-byte; does the static preflight find a committed reference to an uncommitted artifact, Lean module or workflow-invoked script; and, only when both are clean, does check-drift-taxonomy.sh classify the descriptor delta as something other than a geometry widen?' \
  'whether the Lean emission is RIGHT. It settles that the checked-in bytes are the ones THIS revision of the Lean produces and nothing more: not that a descriptor is sound, satisfiable, or says what its author meant, and not that a COSMETIC verdict from the canonicalizing comparator means the polynomials agree (only the equal-canonical-form direction is proved). Any artifact the driver does not name in its guarded-path list is neither snapshotted nor diffed.'

CLEANUP=()
cleanup() {
  local rc=$?
  for c in "${CLEANUP[@]:-}"; do [ -n "$c" ] && eval "$c" || true; done
  return $rc
}
trap cleanup EXIT

# COW/reflink where the filesystem has it (APFS `cp -c`, btrfs/xfs `--reflink`), a real copy
# otherwise. NEVER a hardlink: lake writes oleans in place and a hardlinked seed would corrupt the
# warm `.lake` this run borrowed from — the shared-`.lake` hazard that manufactures phantom olean
# errors and invalidates every timing taken beside it.
clone_dir() {
  cp -c -R "$1" "$2" 2>/dev/null && return 0
  cp --reflink=auto -R "$1" "$2" 2>/dev/null && return 0
  cp -R "$1" "$2"
}

if [ -n "$REV" ]; then
  SHA="$(git -C "$ORIG_ROOT" rev-parse --verify "$REV^{commit}" 2>/dev/null)" || {
    echo "check-descriptor-drift: FATAL — '$REV' does not resolve to a commit." >&2; exit 2; }
  WT="$(mktemp -d -t descriptor-drift-rev.XXXXXX)/tree"
  CLEANUP+=("git -C '$ORIG_ROOT' worktree remove --force '$WT' >/dev/null 2>&1; rm -rf '$(dirname "$WT")'")
  echo "check-descriptor-drift: materialising $REV ($(echo "$SHA" | cut -c1-12)) in a detached worktree..."
  git -C "$ORIG_ROOT" worktree add --detach "$WT" "$SHA" >/dev/null 2>&1 || {
    echo "check-descriptor-drift: FATAL — could not create a detached worktree at $WT" >&2; exit 2; }
  # ⚠ VERIFY THE CLEAN GUARANTEE rather than assuming it. A worktree that is somehow dirty is a
  # `--rev` run grading churn again, which is the whole thing this mode exists to stop.
  if [ -n "$(git -C "$WT" status --porcelain)" ]; then
    echo "check-descriptor-drift: FATAL — the fresh worktree is NOT clean; refusing to grade it." >&2
    git -C "$WT" status --porcelain | head -10 >&2
    exit 2
  fi
  # Seed the Lean build cache so this costs a rebuild-of-the-delta rather than a cold multi-hour
  # build. REFUSED when the toolchain or the lake manifest differ from the revision's, because lake
  # would then rebuild everything anyway and a mixed cache is worse than a cold one.
  if [ -d "$ORIG_ROOT/metatheory/.lake" ]; then
    same=1
    for f in lean-toolchain lake-manifest.json; do
      if ! git -C "$ORIG_ROOT" show "$SHA:metatheory/$f" 2>/dev/null | cmp -s - "$ORIG_ROOT/metatheory/$f"; then same=0; fi
    done
    if [ "$same" -eq 1 ]; then
      echo "check-descriptor-drift: seeding .lake from the working tree (COW clone; toolchain + manifest match $REV)..."
      clone_dir "$ORIG_ROOT/metatheory/.lake" "$WT/metatheory/.lake"
    else
      echo "check-descriptor-drift: ⚠ NOT seeding .lake — lean-toolchain/lake-manifest.json differ from $REV; this run pays a cold build."
    fi
  fi
  ROOT="$WT"
  echo "check-descriptor-drift: grading $REV at $ROOT (the shared working tree is NOT read)"
fi

# Locate lake (CI puts it on PATH; dev machines may only have the elan path).
if ! command -v lake >/dev/null 2>&1 && [ -x "$HOME/.elan/bin/lake" ]; then
  export PATH="$HOME/.elan/bin:$PATH"
fi
if ! command -v lake >/dev/null 2>&1; then
  echo "check-descriptor-drift: FATAL — 'lake' not on PATH (Lean toolchain required)." >&2
  exit 2
fi

# The emit normalizes its generated Rust modules through rustfmt so the generator's bytes equal
# the bytes the pre-commit hook and `cargo fmt --all -- --check` produce. Without rustfmt the emit
# would refuse (emit_descriptors.py: normalize_generated_rust) — say so HERE, before a ~1h Lean
# build, rather than after it.
if ! command -v rustfmt >/dev/null 2>&1; then
  echo "check-descriptor-drift: FATAL — 'rustfmt' not on PATH. The generated Rust modules are" >&2
  echo "  rustfmt-normalized at the pinned toolchain (rust-toolchain.toml) so generator bytes ==" >&2
  echo "  committed bytes; without it this gate cannot produce an honest verdict." >&2
  exit 2
fi

# PREFLIGHT — the by-name ROUTING round trip. Static (parses `EmitByName.lean`'s table out
# of the source), so it runs in seconds HERE, before the multi-hour Lean build, rather than
# reporting after it. It is also the only leg of this gate that still works when the emit
# CANNOT run — and a blocked emit is exactly when a routing gap sits unnoticed: a name added
# to `byNameDescriptors` with no committed artifact behind it is invisible to the emit's
# coverage check (which walks files that EXIST, and needs the emit anyway), to
# `--verify-provenance` (same), and to the derived-coverage test in effect_vm_descriptors.rs
# (same). One such ghost lived a full day in HEAD before this preflight existed.
# The SECOND DOOR rides along in the same invocation (emit_descriptors.verify_include_targets):
# an artifact is also claimed by a Rust `include_str!`, which rustc resolves at COMPILE time, so
# an absent or untracked target is not drift — the crate does not build. The Lean door cannot see
# it, and an UNTRACKED target compiles for exactly one lane (the one that emitted it) and reds for
# every co-tenant and every fresh clone. Both shipped at once: `descriptor_by_name.rs`
# include_str'd `dfa-routing-table-exact-public-v1.json` while the artifact was uncommitted.
#
# A THIRD leg (verify_lean_imports) is the same door one language over: a committed .lean that
# imports an uncommitted module. `20b9d9a20f` is literally titled "repairs a committed tree that
# imported untracked files", and it had already recurred. Worth catching HERE rather than after the
# multi-hour build below, since that build is what the missing module breaks.
#
# A FOURTH leg (verify_workflow_refs) is the same door in the CI medium: a committed
# `.github/workflows/*.yml` step whose `run:` invokes a script nobody committed. `bash
# scripts/x.sh` with `scripts/x.sh` untracked is green on the author's box and `No such file or
# directory` on every runner and every fresh clone — and it was live the night that leg was
# written (`scripts/check-ratchet-darkness.sh` sat untracked under an uncommitted ci.yml hunk that
# ran it). It rides along here for the same reason as the other three: this is the ~1s answer, and
# without it the medium's only detector is the broken job itself, AFTER it lands.
#
# ── ⚑ AND IT DOES NOT ABORT (changed 2026-08-06) ──────────────────────────────
# This leg used to `exit 1` on a reference gap, which made it a MASK: the gate
# whose job is detecting descriptor drift would stop ~40s in, on a question that
# is not drift, and never reach the byte comparison at all. Measured: a 45-file
# descriptor drift went unreported because an unstamped-artifact preflight
# failure exited first — the reference gap was real, the drift was real, and only
# the reference gap was ever printed. One gate's cheap leg hid the other leg's
# verdict, and the cheap leg is not the one the gate is named after.
#
# So the verdict is RECORDED and the run CONTINUES. Both legs are reported at the
# end and either one fails the gate — nothing is weakened, the refusal is just no
# longer allowed to be the only thing you learn. `--fail-fast` restores the old
# abort for the case where you genuinely only want the ~40s answer.
echo "check-descriptor-drift: by-name routing + include_str! targets + Lean imports + workflow-invoked paths (static preflight)..."
PREFLIGHT_RC=0
python3 "$ROOT/scripts/emit_descriptors.py" --verify-by-name-routing || PREFLIGHT_RC=$?
if [ "$PREFLIGHT_RC" -ne 0 ]; then
  echo "" >&2
  echo "REFERENCE GAP: something committed points at something that is not. EmitByName.lean's" >&2
  echo "  table, the checked-in by-name/ set, the Rust include_str!/include_bytes! targets, the" >&2
  echo "  first-party Lean imports and the paths the workflows invoke do not cover each other" >&2
  echo "  (see the findings above)." >&2
  echo "  Fix the routing table, or commit/stamp the artifact, module or script ALONGSIDE the" >&2
  echo "  reference to it — not this gate, and never by #[cfg]-gating the include away." >&2
  if [ "$FAIL_FAST" -eq 1 ]; then
    echo "  (--fail-fast: stopping here; the DRIFT question was never asked)" >&2
    exit 1
  fi
  echo "  ⚑ CONTINUING to the byte comparison anyway — a reference gap must not hide a drift." >&2
  echo "" >&2
fi

# The emitters import the compiled `Dregg2.Circuit.Emit.*` oleans (NOT the source),
# so the corpus must be built first or `lake env lean --run` will emit from STALE
# oleans and the gate would be blind to an un-rebuilt Lean change.
#
# BUILD WHAT WE RUN. `lake build Dregg2` alone is NOT that set: 17 of `EmitByName.lean`'s
# 26 imports (the `Dregg2.Circuit.Emit.*Emit` authors behind the DEPLOYED by-name dispatch
# surface) are reachable from NO default lake target — nothing in the `Dregg2` root's
# import closure pulls them in. Their oleans existed only by accident of an earlier build,
# so on a COLD checkout `lake env lean --run EmitByName.lean` died with 'object file does
# not exist' and emit_descriptors.py exited 2. This gate was green only where something
# OUTSIDE its own build step had warmed the cache. The build set is DERIVED from the
# emitters' own import lines (`--list-emitter-modules`), never hand-listed, so a new
# emitter — or a new import to an existing one — cannot silently reopen the hole.
echo "check-descriptor-drift: building the Lean corpus (fresh oleans)..."
EMIT_MODULES=()
while IFS= read -r m; do
  [ -n "$m" ] && EMIT_MODULES+=("$m")
done < <(python3 "$ROOT/scripts/emit_descriptors.py" --list-emitter-modules)
if [ "${#EMIT_MODULES[@]}" -eq 0 ]; then
  echo "check-descriptor-drift: FATAL — derived an EMPTY emitter build set (the module" >&2
  echo "  scan broke; building nothing would make this gate depend on a warm cache)." >&2
  exit 2
fi
echo "check-descriptor-drift:   ${#EMIT_MODULES[@]} modules the emitters import"
( cd "$ROOT/metatheory" && lake build Dregg2 "${EMIT_MODULES[@]}" )

# The artifacts the emit OWNS (regenerates): the descriptor files, the five Rust
# sources that carry generated `*_FP` constants, and the three WHOLE Lean-authored
# `*_generated.rs` modules. We measure ONLY the effect of re-emitting — we snapshot
# these paths, run emit, and diff the snapshot vs the result. (Diffing against the
# git index would also flag unrelated unstaged edits to the hand-maintained
# prose/logic in those same Rust files, which the emit does NOT touch and which are
# not drift.)
#
# The `*_generated.rs` modules were MISSING from this list, which was a hole, not a
# saving: a generated-Rust-only change takes the non-ack `GENERATED-RUST UPDATE`
# path in `install_and_stamp` (it cannot re-key a descriptor), so the emit INSTALLS
# it and returns 0 — and with the module unguarded this gate diffed nothing and
# reported PASS while the tree had just been rewritten underneath it.
#
# The guarded set must EQUAL `install_and_stamp`'s change-set. It used to be a hand
# transcription of it — right the day it was written, and one new generated module
# away from reopening that exact hole with nothing red (a transcription cannot go
# red; it just covers less). So it is DERIVED, from the same driver, the same way
# the emitter build set 25 lines above is: `--list-guarded-paths` prints
# `DESC + RUST_FP_FILES + GENERATED_RS_PATHS`, and `assert_generated_declared()`
# fails the EMIT if an emitter buffers a module that tuple does not declare. One
# authority, and a new generated module cannot arrive unguarded.
GUARDED=()
while IFS= read -r p; do
  [ -n "$p" ] && GUARDED+=("$p")
done < <(python3 "$ROOT/scripts/emit_descriptors.py" --list-guarded-paths)
if [ "${#GUARDED[@]}" -eq 0 ]; then
  echo "check-descriptor-drift: FATAL — derived an EMPTY guarded set (the path scan" >&2
  echo "  broke; snapshotting nothing would make this gate report PASS for any drift" >&2
  echo "  whatsoever)." >&2
  exit 2
fi
for p in "${GUARDED[@]}"; do
  if [ ! -e "$ROOT/$p" ]; then
    echo "check-descriptor-drift: FATAL — guarded path '$p' does not exist. The driver" >&2
    echo "  names a change-set member this checkout lacks; the snapshot would silently" >&2
    echo "  skip it." >&2
    exit 2
  fi
done
echo "check-descriptor-drift:   ${#GUARDED[@]} guarded paths (the driver's change-set)"

SNAP="$(mktemp -d -t descriptor-drift.XXXXXX)"
CLEANUP+=("rm -rf '$SNAP'")
for p in "${GUARDED[@]}"; do
  mkdir -p "$SNAP/$(dirname "$p")"
  cp -R "$ROOT/$p" "$SNAP/$p"
done

echo "check-descriptor-drift: regenerating from Lean (source of truth)..."
# Since 2026-11-06 the emit has no ack (SUBSTRATE-DECISION §9 row 4): from a COMMITTED
# emitter source closure it installs and stamps automatically, and the DIFF below
# against the pre-emit snapshot is the drift verdict. Its only refusal (exit 3) is an
# UNCOMMITTED closure, which a `--rev` worktree cannot have; on the working tree it
# means the gate cannot attribute the emission to committed source.
emit_rc=0
"$ROOT/scripts/emit-descriptors.sh" || emit_rc=$?
if [ "$emit_rc" -eq 3 ]; then
  echo "" >&2
  echo "EMIT REFUSED: the emitters' Lean source closure has uncommitted edits (listed" >&2
  echo "  above), so no emission from it can be attributed to committed source. Commit" >&2
  echo "  the Lean, or run this gate with --rev HEAD. The tree is UNTOUCHED." >&2
  exit 1
elif [ "$emit_rc" -ne 0 ]; then
  exit "$emit_rc"
fi

echo "check-descriptor-drift: diffing the regenerated artifacts against the pre-emit snapshot..."
drift=0
for p in "${GUARDED[@]}"; do
  if ! diff -ru "$SNAP/$p" "$ROOT/$p"; then
    drift=1
  fi
done

# ── ⚑ THE COMPARATOR (added 2026-08-06) ───────────────────────────────────────
# `diff` says WHETHER bytes moved. It cannot say whether the MEANING moved, so a
# pure re-encoding (a normalizer landing, a coefficient rendered rather than
# elided) and a changed polynomial read identically here — and the second is the
# only one that is dangerous.
#
# `measure-descriptor-normal-form.py --compare` canonicalizes both sides before
# diffing and classifies every arithmetic body IDENTICAL / COSMETIC / SEMANTIC.
# It is SOUND BY A LANDED THEOREM: `AirNormalForm.canonicalize_eval` proves
# `(canonicalize e).eval a = e.eval a` for every assignment, so equal canonical
# forms denote equal polynomials. ⚠ Only that direction is proved — a SEMANTIC
# verdict means "these did not reduce to one head", never "the polynomials
# differ". It costs zero bytes, zero VK rotations and zero re-emissions.
#
# ⚠ The comparator is a MEASUREMENT TOOL, not graded content, so it is taken from the tree that
# INVOKED this gate (`$ORIG_ROOT`), never from `$ROOT`. Under `--rev <old-sha>` the graded worktree
# predates `--compare`, and calling its copy would make every moved descriptor come back SEMANTIC —
# a tool-version error wearing a verdict's clothes. The capability is CHECKED and the gate REFUSES
# on absence rather than classifying with something that cannot classify.
if [ "$drift" -ne 0 ]; then
  echo ""
  echo "check-descriptor-drift: classifying the moved descriptors (canonicalizing comparator)..."
  CMP="$ORIG_ROOT/scripts/measure-descriptor-normal-form.py"
  if ! python3 "$CMP" --help 2>/dev/null | grep -q -- "--compare"; then
    echo "check-descriptor-drift: FATAL — $CMP does not support --compare; refusing to" >&2
    echo "  report a COSMETIC/SEMANTIC verdict from a tool that cannot compute one." >&2
    exit 2
  fi
  semantic=0
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    rel="${f#"$SNAP"/}"
    [ -f "$ROOT/$rel" ] || { echo "  GONE        $rel"; semantic=1; continue; }
    if out="$(python3 "$ROOT/scripts/measure-descriptor-normal-form.py" --compare "$f" "$ROOT/$rel" 2>&1)"; then
      echo "  COSMETIC    $rel — every body proves equal under canonicalize_eval"
    else
      echo "  ⚠ SEMANTIC  $rel"
      echo "$out" | sed 's/^/      /'
      semantic=1
    fi
  done < <(find "$SNAP/circuit/descriptors" -name '*.json' ! -name 'PROVENANCE.json' 2>/dev/null \
             | while IFS= read -r s; do r="${s#"$SNAP"/}"; \
                 [ -f "$ROOT/$r" ] && cmp -s "$s" "$ROOT/$r" || echo "$s"; done)
  if [ "$semantic" -eq 0 ]; then
    echo "check-descriptor-drift: every moved descriptor is a COSMETIC re-encoding."
    echo "  (still DRIFT — the checked-in bytes are stale — but no gate's meaning moved.)"
  fi
fi

if [ "$drift" -eq 0 ] && [ "$PREFLIGHT_RC" -eq 0 ]; then
  echo "check-descriptor-drift: PASS — the Lean emission matches the checked-in descriptors."
  # ADDITIVE — the DRIFT-TAXONOMY gate. Freshness (Lean<->JSON) is settled above;
  # now classify the descriptor delta vs the base ref and REFUSE a GEOMETRY-WIDEN
  # (a re-genesis flag-day) unless DREGG_ALLOW_REGENESIS=1. This answers "does this
  # upgrade need a wipe?" — a tail-append passes, a geometry-widen is caught.
  # (Skips cleanly when no base ref is resolvable, e.g. a detached fresh checkout.)
  echo ""
  # Under `--rev` the tail is handed the SAME revision, not `$ROOT`'s checkout of it. Re-rooting
  # already made the CONTENT right (the detached worktree is what `$ROOT` names), but the tail
  # then printed `-> working tree` for a tree nobody was working in, which is the label lying
  # about the one thing this mode exists to establish. Passing `--rev` makes both sides of the
  # classification commits AND makes the line true.
  if [ -n "$REV" ]; then
    "$ROOT/scripts/check-drift-taxonomy.sh" --rev "$SHA"
  else
    "$ROOT/scripts/check-drift-taxonomy.sh"
  fi
  exit $?
elif [ "$drift" -ne 0 ]; then
  echo "" >&2
  echo "DESCRIPTOR DRIFT: the emit run changed guarded artifacts despite reporting" >&2
  echo "  a no-op (this should be unreachable now that a byte-changing install is" >&2
  echo "  ack-gated — investigate). Run scripts/emit-descriptors.sh with the ack" >&2
  echo "  (see docs/VK-REGEN-CONTROLS.md) and commit the result." >&2
  echo "  The COSMETIC/SEMANTIC classification above says which kind of drift it is." >&2
  [ "$PREFLIGHT_RC" -ne 0 ] && echo "  ⚑ AND the static preflight ALSO failed (see the top of this run)." >&2
  exit 1
else
  # drift == 0, so the bytes are fresh; we are here only because the preflight
  # failed. Reaching this line at all is the point of the 2026-08-06 change —
  # the drift question got asked and ANSWERED (no drift) rather than being
  # pre-empted by a reference gap that is a different defect.
  echo "" >&2
  echo "check-descriptor-drift: the Lean emission MATCHES the checked-in descriptors" >&2
  echo "  (no drift), but the static preflight FAILED — see the REFERENCE GAP above." >&2
  echo "  Fix the reference gap; the descriptor bytes are not the problem." >&2
  exit 1
fi
