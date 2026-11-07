#!/usr/bin/env bash
# check-p3-rev.sh -- enforce that every hardcoded emberian/plonky3-recursion
# fork rev in the repo matches the single source of truth, scripts/p3-rev.env.
#
# The fork rev resolves the whole workspace's recursion crates and thus the
# compiled verifier. It is pinned in the AUTHORITATIVE workspace deps (root
# Cargo.toml [workspace.dependencies] p3-recursion/p3-circuit/...) and mirrored
# into several CI workflows (sibling-clone REV) and wasm/Cargo.toml's comment.
# All of these MUST stay in lockstep or the built verifier forks silently.
#
# Scoping: root Cargo.toml ALSO pins base upstream Plonky3/Plonky3 at a different
# 40-hex rev, so its p3-recursion rev is isolated by matching only
# `plonky3-recursion` lines (never a blind grep of the whole file). For the CI
# workflows + wasm/Cargo.toml the only 40-hex tokens present are the fork rev.
#
# ALSO enforced (was WARN-only until 2026-07-24): the VK-hash constant
# RECURSION_P3_REV in circuit-prove/src/recursive_witness_bundle.rs. It is the
# proving-system id folded into compute_recursive_vk_hash() -- the value
# lookup_recursive_vk() accepts on, i.e. the light-client trust anchor.
#
# It was excluded as "a VK-epoch event on a human-gated track". That reasoning did
# not survive contact with the code: compute_recursive_vk_hash() is recomputed by
# BOTH producer and verifier from this same constant, and NO golden/frozen hash of
# it exists anywhere in the tree -- so reconciling the string re-keys a value
# nothing external pins. The apex governance anchor DREGG_APEX_RECURSION_VK is a
# blake3 fingerprint of VK MATERIAL (recursion_vk_fingerprint) and does not read
# this constant at all. VK-CEREMONY.md's own cutover lists the reconcile as step
# (3) of §6.1, independent of ceremony output -- it was bundled into a BLOCKED
# ceremony, which is how it stayed drifted while the gate could not fail.
#
# A gate that cannot fail is not a gate (cf. scripts/check-mirror-gates.sh: "a
# gate that cannot bark is worse than none"), and this is the one consumer whose
# drift is directly security-relevant. It FAILS here.
# ── ⚑ `--rev` (added 2026-08-02): grade a COMMIT, not whatever is lying around ──────────
# This gate's verdict is cited in six docs as evidence that the fork rev is in lockstep, and
# without `--rev` every one of those verdicts was taken over a shared working tree: a sibling
# mid-bump has one consumer edited and four not, and the gate reports THEIR intermediate state
# under this gate's name. The mirror is `check-guard-modules.py --rev` / `check-descriptor-
# drift.sh --rev`: materialise the revision with `git archive <rev> | tar -x` and run the whole
# gate against the extract. An archive OF A COMMIT cannot contain churn — that is the same
# guarantee `check-descriptor-drift.sh` buys with an explicit `git status --porcelain` check on
# its worktree, obtained structurally instead.
#
# ── ⚑ ABBREVIATED PINS (2026-08-02): THE AUTHORITATIVE PIN MAY BE SHORTER THAN 40 HEX ────
# This gate FAILED from the day it was written until 2026-08-02, and its message was wrong.
# `d7ba0c4d3` pinned `rev = "fc3c6df"` — seven hex — while this gate matched `[0-9a-f]{40}`
# only. It therefore read NO rev from the authoritative source and reported the pin as
# VANISHED, when in fact the pin was present and the fork had moved TWO commits ahead of
# every mirror (0a4a554e -> fc3c6df, a ConstAir preprocessed-value FLAG DAY). Five mirrors,
# including RECURSION_P3_REV — the recursive VK's proving-system id — advertised a rev that
# was not the one compiling. The abbreviation is now accepted and RESOLVED through
# Cargo.lock's recorded full sha, so a short pin compares correctly and a short-but-DIFFERENT
# pin reds as a MISMATCH. Regression-guarded by arm R9 of scripts/check-p3-rev-selftest.py.
#
# Usage:  scripts/check-p3-rev.sh
#         scripts/check-p3-rev.sh --rev HEAD    # clean extract (churn-safe)
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

REV=""
while [ $# -gt 0 ]; do
  case "$1" in
    --rev) REV="${2:-}"; [ -n "$REV" ] || { echo "check-p3-rev: --rev needs a revision" >&2; exit 2; }; shift 2 ;;
    --rev=*) REV="${1#--rev=}"; shift ;;
    -h|--help) sed -n '2,56p' "$0"; exit 0 ;;
    *) echo "check-p3-rev: unknown argument '$1' (see --help)" >&2; exit 2 ;;
  esac
done

# ── SCOPE ─ this printf is the ONLY copy; it prints on every run, pass or fail. ───────
printf 'ANSWERS:         %s\nDOES NOT ANSWER: %s\n' \
  'does every consumer on the hand-maintained list inside this script — three workflow files scanned for any 40-hex token, wasm/Cargo.toml, two more workflows scanned for REV=<hex>, the root Cargo.toml pin resolved through the full sha Cargo.lock recorded, and the RECURSION_P3_REV constant in circuit-prove — still carry a pin at all, and does each one equal P3_REV as declared in scripts/p3-rev.env?' \
  'whether the pinned rev is the RIGHT one, or whether anything was built from it. This is a text comparison over a hand-maintained consumer list: a NEW file that pins the fork rev is not on the list and is never read, Cargo.lock records what cargo resolved rather than what any deployed binary or VK was compiled from, and lockstep across the mirrors is no evidence about how the recursive verifier behaves. Under --rev the subject is a git-archive extract of that commit, not the working tree.'

REV_TMP=""
rev_cleanup() { [ -n "${REV_TMP:-}" ] && rm -rf "$REV_TMP"; return 0; }
trap rev_cleanup EXIT
if [ -n "$REV" ]; then
  SHA="$(git -C "$repo_root" rev-parse --verify "$REV^{commit}" 2>/dev/null)" || {
    echo "check-p3-rev: FATAL — '$REV' does not resolve to a commit." >&2; exit 2; }
  REV_TMP="$(mktemp -d -t p3-rev-rev.XXXXXX)"
  git -C "$repo_root" archive "$SHA" | tar -x -C "$REV_TMP" || {
    echo "check-p3-rev: FATAL — git archive $REV failed." >&2; exit 2; }
  repo_root="$REV_TMP"
  echo "check-p3-rev: grading $REV ($(echo "$SHA" | cut -c1-12)) from a clean extract; the working tree is NOT read."
fi

env_file="$repo_root/scripts/p3-rev.env"

if [[ ! -f "$env_file" ]]; then
  echo "FAIL: single-source env missing: $env_file" >&2
  exit 1
fi
# shellcheck source=/dev/null
. "$env_file"

if [[ ! "${P3_REV:-}" =~ ^[0-9a-f]{40}$ ]]; then
  echo "FAIL: P3_REV in $env_file is not a 40-hex rev: '${P3_REV:-<unset>}'" >&2
  exit 1
fi

status=0

# --- Consumers whose ONLY 40-hex tokens are the fork rev: grep the whole file.
blind_files=(
  ".github/workflows/extension.yml"
  ".github/workflows/publish-sdk-ts.yml"
  # Was pages.yml until 2026-07-26. The Pages deploy split in two: the three wasm-pack
  # jobs (the only things that clone the sibling fork) moved to pages-wasm.yml, and
  # pages.yml is now a cargo-free content path that pins nothing. This gate's own
  # vanished-mirror check would have caught the move as a FAIL — which is the gate
  # working — so the mirror is re-pointed rather than dropped.
  ".github/workflows/pages-wasm.yml"
  "wasm/Cargo.toml"
)
for rel in "${blind_files[@]}"; do
  f="$repo_root/$rel"
  if [[ ! -f "$f" ]]; then
    echo "FAIL: consumer file missing: $rel" >&2
    status=1
    continue
  fi
  # A lockstep gate whose grep matches NOTHING passes having checked nothing: if a
  # consumer silently loses its pinned rev (line deleted / comment dropped / dep
  # restructured), the loop body never runs and no mismatch is reported. Count the
  # matches and FAIL LOUD on zero — a vanished mirror is a lockstep break, not a pass.
  seen=0
  while IFS= read -r rev; do
    [[ -z "$rev" ]] && continue
    seen=$((seen + 1))
    if [[ "$rev" != "$P3_REV" ]]; then
      echo "FAIL: $rel pins plonky3 rev $rev, expected $P3_REV" >&2
      status=1
    fi
  done < <(grep -ioE '[0-9a-f]{40}' "$f" | sort -u)
  if [[ "$seen" -eq 0 ]]; then
    echo "FAIL: $rel no longer contains the pinned fork rev — the lockstep gate would" >&2
    echo "      otherwise PASS having checked nothing here. Restore the pin, or drop $rel" >&2
    echo "      from blind_files if it is intentionally no longer a mirror." >&2
    status=1
  fi
done

# --- ⚑ MIRRORS THIS GATE NEVER WATCHED AT ALL (added 2026-08-02).
#
# Three more workflow steps clone the fork as a `[patch]` sibling, and none was in any list
# above: `.github/workflows/ci.yml` (the wasm job AND the forge-ci-runner job) and
# `.github/workflows/feature-surface.yml` (every deos-zed-full shard). Their own comments say
# they "must stay in lockstep or the VK forks" — and they were two fork commits stale, unread
# by the gate whose entire job is that sentence. A gate that reports OK while naming four of
# seven mirrors is the same failure as one that greps nothing: it just fails later.
#
# They cannot join blind_files: `ci.yml` also carries MATHLIB_REV (`56a00585…`), an unrelated
# 40-hex pin a blind grep would report as fork drift. So match the ASSIGNMENT form these steps
# actually use — `REV=<hex>` — which is exactly the token the clone consumes, and nothing else.
# 7--40 hex here too: an abbreviated REV= is the same trap the authoritative pin just sprang.
rev_assign_files=(
  ".github/workflows/ci.yml"
  ".github/workflows/feature-surface.yml"
)
for rel in "${rev_assign_files[@]}"; do
  f="$repo_root/$rel"
  if [[ ! -f "$f" ]]; then
    echo "FAIL: consumer file missing: $rel" >&2
    status=1
    continue
  fi
  seen=0
  while IFS= read -r rev; do
    [[ -z "$rev" ]] && continue
    seen=$((seen + 1))
    if [[ "$P3_REV" != "$rev"* ]]; then
      echo "FAIL: $rel sets REV=$rev for the sibling clone, expected $P3_REV" >&2
      echo "      That step is a \`[patch]\` target, so this job builds a DIFFERENT verifier" >&2
      echo "      than the workspace resolves." >&2
      status=1
    fi
  done < <(grep -oE 'REV=[0-9a-f]{7,40}' "$f" | sed 's/^REV=//' | sort -u)
  if [[ "$seen" -eq 0 ]]; then
    echo "FAIL: $rel has no \`REV=<hex>\` sibling-clone pin — either the clone step was" >&2
    echo "      removed (drop $rel from rev_assign_files) or it was rewritten into a form" >&2
    echo "      this check cannot see, in which case it is unguarded again." >&2
    status=1
  fi
done

# --- Authoritative workspace pin: isolate the plonky3-recursion rev only
# (base Plonky3/Plonky3 is legitimately a different rev in the same file).
#
# ⚑ A PIN MAY BE ABBREVIATED, AND FOR THREE DAYS THAT BLINDED THIS GATE (fixed 2026-08-02).
# cargo accepts any unambiguous prefix in `rev = "..."`, and `d7ba0c4d3` used SEVEN hex
# chars (`rev = "fc3c6df"`). This block matched `[0-9a-f]{40}` only, so it extracted NO rev
# from the authoritative source and fell into the vanished-pin branch below — reporting
# "the authoritative pin has VANISHED (dep renamed/removed?)" while the pin was sitting
# right there, present and DRIFTED two fork commits ahead of every mirror. A real,
# security-relevant drift in the recursive VK's proving-system id was served as a
# nonsense diagnosis, and the red was unattributable.
#
# So: accept 7--40 hex, and resolve it. The resolver is Cargo.lock, which records the FULL
# 40-hex sha cargo actually checked out for every `plonky3-recursion` entry
# (`...?rev=fc3c6df#fc3c6dfac26e...`). That is a strictly better anchor than the Cargo.toml
# text: it is what COMPILES, it is in-tree (no network, and it comes along in the --rev
# archive), and it is generated by cargo rather than hand-maintained — so checking it
# against the hand-maintained P3_REV is two INDEPENDENT sources, not a constant against
# its own definition.
cargo="$repo_root/Cargo.toml"
lock="$repo_root/Cargo.lock"
if [[ ! -f "$cargo" ]]; then
  echo "FAIL: root Cargo.toml missing" >&2
  status=1
elif [[ ! -f "$lock" ]]; then
  echo "FAIL: root Cargo.lock missing — the gate resolves the authoritative (possibly" >&2
  echo "      abbreviated) Cargo.toml pin through Cargo.lock's recorded full sha. Without" >&2
  echo "      it there is no resolver and an abbreviated pin cannot be compared." >&2
  status=1
else
  # (1) What cargo ACTUALLY resolved. Must be unique: two different resolved shas for the
  # same fork would mean the workspace compiles two verifiers at once.
  mapfile -t lock_revs < <(grep -oE 'plonky3-recursion\?rev=[0-9a-f]{7,40}#[0-9a-f]{40}' "$lock" \
                           | sed 's/.*#//' | sort -u)
  if [[ "${#lock_revs[@]}" -eq 0 ]]; then
    echo "FAIL: Cargo.lock records NO plonky3-recursion source — the resolver the gate" >&2
    echo "      anchors on has vanished (dep renamed/removed, or the lock is stale)." >&2
    status=1
  elif [[ "${#lock_revs[@]}" -gt 1 ]]; then
    echo "FAIL: Cargo.lock resolves plonky3-recursion to ${#lock_revs[@]} DIFFERENT shas:" >&2
    printf '        %s\n' "${lock_revs[@]}" >&2
    echo "      The workspace would compile more than one verifier. There is no single" >&2
    echo "      authoritative rev to hold the mirrors in lockstep against." >&2
    status=1
  else
    resolved="${lock_revs[0]}"
    if [[ "$resolved" != "$P3_REV" ]]; then
      echo "FAIL: Cargo.lock resolves plonky3-recursion to $resolved," >&2
      echo "      but $env_file declares P3_REV=$P3_REV." >&2
      echo "      The COMPILED verifier is $resolved; every mirror above was checked" >&2
      echo "      against P3_REV, so they are all in lockstep with a rev that is NOT built." >&2
      echo "      FIX: set P3_REV to the rev Cargo.lock establishes, then re-run to see" >&2
      echo "      which mirrors drift." >&2
      status=1
    fi

    # (2) The Cargo.toml pin must be a PREFIX of what the lock resolved. An abbreviation is
    # legitimate; a DIFFERENT rev is a lock/manifest split (someone edited the manifest and
    # did not re-lock, so the built verifier is not the pinned one).
    seen=0
    while IFS= read -r rev; do
      [[ -z "$rev" ]] && continue
      seen=$((seen + 1))
      if [[ "$resolved" != "$rev"* ]]; then
        echo "FAIL: root Cargo.toml pins plonky3-recursion rev '$rev', which is NOT a prefix" >&2
        echo "      of the sha Cargo.lock resolved ($resolved). The manifest and the lock" >&2
        echo "      disagree: the verifier that COMPILES is not the one the manifest pins." >&2
        echo "      FIX: re-run cargo so the lock re-resolves, or correct the manifest pin." >&2
        status=1
      fi
    done < <(grep 'plonky3-recursion' "$cargo" \
             | grep -oE 'rev[[:space:]]*=[[:space:]]*"[0-9a-f]{7,40}"' \
             | grep -oE '[0-9a-f]{7,40}' | sort -u)
    # The AUTHORITATIVE pin. If this yields zero (the `plonky3-recursion` dep line was
    # renamed or removed), the gate anchors on nothing and every consumer check above is
    # meaningless — the whole gate silently greens. That is the exact failure this gate
    # exists to prevent, turned on itself. FAIL LOUD.
    if [[ "$seen" -eq 0 ]]; then
      echo "FAIL: root Cargo.toml yielded NO plonky3-recursion rev — the authoritative pin" >&2
      echo "      the entire lockstep gate anchors on has vanished (dep renamed/removed?)." >&2
      echo "      The gate cannot verify lockstep against a missing source of truth." >&2
      echo "      NOTE: a 7--40 hex abbreviation is ACCEPTED and resolved through Cargo.lock," >&2
      echo "      so reaching this branch means there is genuinely no \`rev = \"<hex>\"\` on a" >&2
      echo "      plonky3-recursion line — not merely a short one." >&2
      status=1
    fi
  fi
fi

# --- ENFORCED: the VK-hash constant. This is the MOST load-bearing consumer, not
# the least: RECURSION_P3_REV is folded into compute_recursive_vk_hash(), the value
# lookup_recursive_vk() accepts on -- the light-client trust anchor's proving-system id.
vk="$repo_root/circuit-prove/src/recursive_witness_bundle.rs"
if [[ ! -f "$vk" ]]; then
  echo "FAIL: VK-hash consumer missing: circuit-prove/src/recursive_witness_bundle.rs" >&2
  status=1
else
  vk_rev="$(grep 'RECURSION_P3_REV' "$vk" | grep -ioE '[0-9a-f]{40}' | head -1 || true)"
  if [[ -z "$vk_rev" ]]; then
    echo "FAIL: RECURSION_P3_REV in recursive_witness_bundle.rs carries no 40-hex rev --" >&2
    echo "      the VK-hash proving-system id has vanished and this check would otherwise" >&2
    echo "      PASS having checked nothing (same vanished-pin class as above)." >&2
    status=1
  elif [[ "$vk_rev" != "$P3_REV" ]]; then
    echo "FAIL: RECURSION_P3_REV in recursive_witness_bundle.rs is $vk_rev, not $P3_REV" >&2
    echo "      The deployed recursive VK hash therefore advertises a proving system that" >&2
    echo "      is NOT the one compiled in (Cargo.lock resolves $P3_REV). Old recursive" >&2
    echo "      proofs built against $vk_rev stay indistinguishable-by-VK-hash from" >&2
    echo "      current ones -- the exact failure this constant exists to prevent." >&2
    echo "      FIX: reconcile the constant with the rev Cargo.lock establishes." >&2
    echo "      This re-keys compute_recursive_vk_hash(), which NOTHING external pins" >&2
    echo "      (lookup_recursive_vk recomputes it; the apex anchor DREGG_APEX_RECURSION_VK" >&2
    echo "      is a fingerprint of VK MATERIAL and is unaffected). It is not a ceremony." >&2
    status=1
  fi
fi

if [[ "$status" -eq 0 ]]; then
  echo "OK: all lockstep plonky3-recursion revs match P3_REV=$P3_REV"
fi
exit "$status"
