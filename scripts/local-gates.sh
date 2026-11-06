#!/usr/bin/env bash
# local-gates.sh — run the gates CI invokes, HERE, and print one table.
#
# ── WHY THIS EXISTS ────────────────────────────────────────────────────────────
# The bar is not "GitHub is green". It is: **these gates would succeed if run on a
# real box.** Those are different questions, and on this repo they are VERY
# different — measured 2026-07-26, of the last 60 `ci.yml` runs, 37 were CANCELLED
# and 21 failed and 0 succeeded. Not because the tree was that broken: the median
# gap between commits on `main` is 92 SECONDS and the median run needs ~87 MINUTES
# to reach a conclusion, so ~56 of every 57 pushes cancel their predecessor and
# never get measured at all. A GitHub verdict is a lottery ticket; a local run is
# an answer.
#
# Local is also, in at least two measured ways, the STRICTER test:
#   * `check-doc-refs` — macOS's case-insensitive APFS makes a doc's
#     `Circuit/Foo.lean` match the real `circuit/` dir, so ~60 dead references
#     RESOLVE on a Linux runner and die here.
#   * the `dregg-pq` fail-closed abort was CPU-count dependent: hosted runners are
#     4-vCPU (under the threshold), every dev box with 8+ cores aborted.
# So "it passed in CI" was never evidence that it passes for a person.
#
# ── USAGE ──────────────────────────────────────────────────────────────────────
#   ./scripts/local-gates.sh              # the cheap set (minutes)
#   ./scripts/local-gates.sh --all        # + the expensive ones (see below)
#   ./scripts/local-gates.sh doc-refs …   # only the named gates
#
# Exit 0 iff every gate it RAN passed. Skipped gates are printed, never silently
# dropped — a runner that quietly narrows its own coverage is the thing this repo
# keeps getting bitten by.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 2

RUN_ALL=0; WANT=()
for a in "$@"; do case "$a" in --all) RUN_ALL=1 ;; -h|--help) sed -n '2,30p' "$0"; exit 0 ;; *) WANT+=("$a") ;; esac; done

# name | timeout_s | command
GATES=(
  # ⚑ A WIPED DEPENDENCY THAT PRESENTS AS A PROOF FAILURE (2026-08-09, twice in one
  # evening). `~/src/mathlib4` was destroyed twice; `metatheory/.lake/packages/mathlib`
  # is a SYMLINK into it, so the damage does not read as "a dependency is missing" —
  # every mathlib-importing build dies on `object file '.../Ring/Defs.olean' does not
  # exist`, which looks exactly like a broken proof. A lane spent real time believing
  # its own module was at fault. Restore is ~10 min (clone at the pinned rev + `lake
  # exe cache get`, 8105 oleans), so the cost was never the repair — it was the
  # misdiagnosis. This row is first so the answer arrives before anything else runs.
  # ⚠ NOT the tree's own scripts: `pbuild` is the only real `rsync --delete` and was
  # hardened after it ate this same path on 07-28 (`pbuild:636-648`); `reclaim-space.sh`
  # does not follow the symlink (`find` without `-L`; `rm -rf` takes the LINK). The
  # destroyer is outside this repo. This gate does not name it — it makes the damage
  # legible, which is the part that kept costing hours.
  # ⚠ AND NOT "make it read-only": lake WRITES there by design (`cache get` populates
  # it, an uncached import is built there, a rev bump adds oleans). The invariant is
  # that lake writes and nothing DELETES THROUGH the link.
  "mathlib-intact|60|python3 scripts/check-mathlib-intact.py"
  "doc-refs|300|bash scripts/check-doc-refs.sh"
  # ⚑ THE DOCUMENTATION FORM OF A DANGLING IMPORT (2026-08-08). `doc-refs` checks cited FILES;
  # this checks cited LEAN NAMES: a comment citing a theorem/def that was deleted or renamed
  # (`FinalizedRegionStable` — six citing files incl. production Rust doc comments;
  # `stableCheck`; `isCordialBlock`; `propose_join_if_needed` in `join --help`) is a reader
  # being told something false at exactly the moment they check. History is legal when NAMED
  # ("deleted"/"former"/"renamed" near the mention); narrating a dead name as live fires.
  # The -red row is the constructive plant: three dead citation forms MUST fire, a real one
  # must not. Slow half is the one-time Mathlib universe scan (~2-4 min cold).
  "lean-citations|600|python3 scripts/check-lean-citations.py"
  "lean-citations-red|600|python3 scripts/check-lean-citations.py --self-test"
  "dark-modules|300|python3 scripts/check-dark-modules.py"
  "never-run-targets|300|python3 scripts/check-never-run-targets.py"
  # ⚑ THE COMPILE-FAIL RATCHET'S RED PROOF (2026-08-03). The two rows above are sweeps
  # 2 and 3 over `.github/dark-targets.txt`; sweep 1 — the one that catches a target
  # that DOES NOT COMPILE — had no script at all. It was inline shell in one step of
  # `ci.yml`'s `clippy-correctness`, which means the only machine that could ever run it
  # was a GitHub runner reaching step 7. MEASURED across every ci.yml run 08-01..08-03:
  # it executed 3 times and was SKIPPED 31, because step 6 (the correctness sweep) fails
  # first and Actions stops a job at the first failed step. `commons-arbiter` and
  # `confined-swarm` both went dark inside that window and nothing said so.
  # This row is the SELF-TEST (~3s, real cargo over a 3-crate temp workspace, 11 legs).
  # The full sweep is under --all below — it is a whole-workspace clippy.
  "dark-targets-red|300|python3 scripts/check-dark-targets.py --self-test"
  # ⚑ A VERIFIED LEAN DECISION THAT SHIPS AND THAT NO RUST FILE NAMES (2026-08-04). The sibling of
  # `dark-modules`: that one catches a `.rs` rustc never OPENS, this one catches a Lean gate rustc
  # never ASKS. There is no diagnostic for it — the symbol is in the archive, the module's theorems
  # are green, nothing fails. `dregg_mina_deferral_ok` shipped for five days deciding nothing while
  # its own file proved that an undischarged accumulator makes the terminal opening VACUOUS.
  # Ratchet: `.github/uncalled-exports.txt` (9 rows at landing, and it only shrinks).
  "export-callers|180|python3 scripts/check-export-callers.py"
  "export-callers-red|60|python3 scripts/check-export-callers.py --self-test"
  "emit-gate-weld|120|python3 scripts/check-emit-gate-weld.py"
  "independence-controls|300|bash scripts/check-independence-controls.sh"
  "ratchet-darkness|120|bash scripts/check-ratchet-darkness.sh"
  "lean-orphans|120|bash scripts/check-lean-orphans.sh"
  # A metatheory/Dregg2 module that CARRIES a differential guard (#guard / #assert_axioms /
  # #assert_namespace_axioms) but is UNROOTED (built by no default lake target, so its guard
  # never runs) or SORRY-carrying (its guard runs vacuously below a hole). Strictly stronger
  # than `lean-orphans`: that gate WAVES THROUGH an orphan if it is in lean-orphans-allow.txt
  # ("the exclusion is deliberate"); this one does NOT — a module that CLAIMS something
  # checkable and is deliberately never built is a deliberate SILENT CLAIM. Born 2026-08-01 from
  # `Dregg2.Bridge.MinaWrapFtEval0Weld`: a `#guard`-backed headline ("six gate bodies reproduce
  # the linearization constant term") with a GAMMA_CHAL `sorry` FROM ITS BIRTH COMMIT, in NO
  # lake target, so the guard NEVER RAN and the headline was never machine-checked — and the
  # guard also sat below a real gateLinConst defect. Two silences stacked.
  # ⚑ Census at HEAD: 77 unrooted + 1 sorry (Dregg2.Bignum.LedgerBalance's named completeness
  # pole) = 78, recorded in scripts/guard-modules-baseline.txt as a BURNDOWN LEDGER (not an
  # acceptance list). The gate reds on any (kind, module) NOT in the baseline (the next silent
  # claim stands out against green) and on a STALE row (a rooted/discharged module must retire
  # its own row — the census only ratchets DOWN). It PRINTS the full census every run. Pure text,
  # no Lean toolchain, ~2s (a git-archive HEAD extract keeps it churn-safe on a shared tree).
  # ⚠ It does NOT catch a TAUTOLOGICAL guard (#guard 1==1) — that is SEMANTIC vacuity, a harder
  # residual than the SYNTACTIC (never-built / built-below-a-hole) class this closes.
  # The `-red` row is not optional: the headline is a NEGATIVE assertion, which passes just as
  # happily on a broken reader. Its synthetic-tree red-proof checks the unrooted arm, the sorry
  # arm, the control (a clean rooted guard is NOT flagged), the admit-identifier/sorryAx-name-
  # literal false-positive guards, both ratchet directions (new -> red, stale -> red), and that
  # an empty (blinded) scan trips every non-vacuity floor. The working tree is never touched.
  "check-guard-modules|180|python3 scripts/check-guard-modules.py --rev HEAD"
  "check-guard-modules-red|60|python3 scripts/check-guard-modules.py --self-test"
  # THE `#guard` POPULATION MAY ONLY RATCHET DOWN, per module. `check-guard-modules` above asks
  # whether a guard RUNS; this one asks whether the fact should have been a `#guard` at all.
  # ⚑ THE MEASUREMENT: `#guard e` is implemented (Lean 4.30, Lean/Elab/Tactic/Guard.lean:154-167) as
  # `unsafe evalExpr Bool` — the SAME compiled evaluator `native_decide` runs on. So a `#guard` is
  # not a cheaper check than a `native_decide` theorem; it is the same check with the NAME, the TERM
  # and the AXIOM RECORD deleted. It does not avoid trusting the compiler — it trusts the compiler
  # SILENTLY, which is why `#assert_axioms` is structurally blind to all 15,850 of them (measured
  # 2026-08-02 across 1,159 files; KimchiStepMain.lean alone holds 838). This is the sin CLAUDE.md
  # already forbids in Rust — "case-tests prove NOTHING about all inputs" — and moving the case-tests
  # into Lean did not make them verification.
  # Policy: metatheory/docs/GUARD-DISCIPLINE.md. A fact worth asserting is worth naming.
  # 15,850 cannot go to zero in one pass and a flat ban would be a gate nobody keeps green, so:
  # a PER-MODULE baseline (scripts/guard-discipline-baseline.txt) that may only SHRINK. Three reds —
  # a module ABOVE its row (the habit regrew), BELOW it (a STALE row: you converted, retire the
  # number — this is what makes the census monotone, not merely non-increasing), or carrying guards
  # with NO row (the population grew sideways). Pure text, no Lean toolchain, ~2s, git-archive HEAD
  # extract for churn-safety on a shared tree.
  # ⚠ It bounds the COUNT; it does not read what any guard CLAIMS. A module at its baseline may hold
  # its most load-bearing pin as a `#guard` forever, and a guard DELETED rather than converted moves
  # the number the same way a converted one does. Only the diff says which.
  # The `-red` row is not optional: the headline is a NEGATIVE assertion, which passes just as
  # happily on a broken reader. The synthetic-tree red-proof exercises all three arms, the control
  # (a tree at its own baseline is green), the one-way ratchet (regrowth past a RETIRED row still
  # fails), the comment/string/#assert_axioms/#guard_msgs false-positive guards, and that a blinded
  # scan trips the non-vacuity floors. The working tree is never touched.
  "check-guard-discipline|180|python3 scripts/check-guard-discipline.py --rev HEAD"
  "check-guard-discipline-red|60|python3 scripts/check-guard-discipline.py --self-test"
  # ⚑ THE ANTI-VACUITY TOOTH MAY NOT ITSELF BE VACUOUS. Added 2026-08-16 after
  # `RecursiveAggregation.real_engine_sound` was found discharging "So `EngineSound` is
  # INHABITED — the headline is not vacuous" at `RealProof := Unit` + `acceptAll := fun _ =>
  # true`: one proof inhabitant, a verifier with no `false` in its range, so no forgery was
  # even EXPRESSIBLE and the structure could not be refuted from the verify side at any
  # aggregate. `#assert_axioms`, `#keystone_audit` and the guard ratchet were all green on it,
  # because each asks "is this proved?" and it was. Two siblings had the same shape.
  # Gates on the FINDING against a ledger (unlisted = red, stale row = red), not on its own
  # self-test; `-red` proves the detector can fire.
  "anti-vacuity-witness|120|python3 scripts/check-anti-vacuity-witness.py"
  "anti-vacuity-witness-red|60|python3 scripts/check-anti-vacuity-witness.py --self-test"
  # ⚑ ELABORATION COST, ratcheted on DECLARATIONS and SHAPE — never on a stopwatch. The same
  # modules measured 5-11x apart in-build vs standalone on hbox in one hour (PolishchukSpielman
  # 565 s vs 51.3 s), because ~50 concurrent `lean` processes each carry a ~2.4 GB working set
  # from `import Mathlib.Tactic` and the box thrashes. A wall-clock gate there is a coin flip.
  # So: `maxHeartbeats`/`maxRecDepth` may only fall, whole-`Mathlib` imports may only shrink,
  # and arm (d) refuses the data-from-gates SHAPE — a module with expensive theorems AND cheap
  # defs whose importers cite only the defs, which is how `MinaWrapGroupGate` (278.5 s / 4.23 GB)
  # got built by every consumer that wanted its TYPE. Backlog ledger, shrink-only, 36 rows.
  # The `-red` row is not optional: the headline is a NEGATIVE assertion and passes just as
  # happily on a broken reader. The self-test drives all four arms plus the controls that must
  # STAY green (a theorem-citing importer, a module with no declared raise, a raise mentioned
  # only in a docstring) on a synthetic tree; the working tree is never touched.
  "check-elab-cost|300|python3 scripts/check-elab-cost.py"
  "check-elab-cost-red|60|python3 scripts/check-elab-cost.py --self-test"
  "forcing-gadget-tie|120|python3 scripts/check-forcing-gadget-tie.py"
  "forcing-gadget-tie-red|60|python3 scripts/check-forcing-gadget-tie.py --self-test"
  # ⚑ `@[implemented_by]` ON THE PURE DEF MAKES ITS OWN DIFFERENTIAL A TAUTOLOGY.
  # The attribute is honoured by the COMPILED evaluator, which is the same evaluator `#guard` and
  # `native_decide` run on — so `#guard twin x == pure x` prints `true` for ANY twin when the
  # attribute sits on `pure`. Five ML-DSA ring seams were in that shape on the live FIPS 204
  # sign/verify path until 2026-08-09, and the obvious fix would have been a permanently green
  # check that READ as closure. This gate demands the structural fix: the attribute goes on an
  # alias carrying a `<target>_eq` witness, leaving an unrouted pure side to compare against.
  # The `-red` row is not optional — the headline is a negative assertion, so it passes just as
  # happily on a broken reader; the self-test plants the attribute on a pure def (both the
  # `attribute` and the inline `@[...]` form), plants a witness whose RHS is itself routed, and
  # checks a prose-only mention stays green. The working tree is never touched.
  "implemented-by-alias|120|python3 scripts/check-implemented-by-alias.py"
  "implemented-by-alias-red|60|python3 scripts/check-implemented-by-alias.py --self-test"
  # ⚑ THE WRAP VK's 56 COORDINATES ARE GENERATED, AND THIS IS THE DRIFT GUARD.
  # `Dregg2/Circuit/Emit/MinaWrapVkDigestChain.lean` derives the verifier-index digest — the one
  # element of the phase-1 tape that used to be a bare constant — from the sha256-pinned devnet Wrap
  # verifier indices. Its 112 decimals are WRITTEN by the generator, never typed, and `--check`
  # re-decodes both pinned fixtures and refuses if a committed literal has drifted from them.
  # ⚠ The `-red` row is not optional and it is not decoration: the thing this gate exists to catch
  # is a DECODE-CONVENTION swap, and the wrong convention yields 28 points that are ALL ON THE
  # CURVE. `--self-test` proves the check separates the parity reading from arkworks' `PositiveY`
  # (11 of 56 coordinates move, digest wrong), separates a one-digit literal drift, and separates a
  # one-byte fixture change. Pure python, no Lean toolchain, ~2s, nothing on disk moves.
  "wrap-vk-comm-drift|60|python3 metatheory/fixtures/gen_wrap_vk_comm_xy.py --check"
  "wrap-vk-comm-drift-red|60|python3 metatheory/fixtures/gen_wrap_vk_comm_xy.py --self-test"
  # A BYTE-FIDELITY MODEL THAT CERTIFIED ITSELF. `Dregg2/Exec/SigningMessage.lean` exists so the
  # §8 AuthPortal's opaque `stmt` is the preimage dregg1 ACTUALLY signs — "one byte differently
  # and the portal verifies the wrong message", in its own words. Its fidelity check was
  # `sepFull = ascii "dregg-action-sig-v2:"`: a Lean constant against a Lean restatement of it.
  # ONE SOURCE, so it could not go red when Rust moved — and Rust moved, to v3, inserting
  # `turn_nonce` (the Full-commitment replay closure, `authorize.rs:2293`). The model sat on v2
  # WITHOUT the nonce and every guard in the file stayed green. Measured 2026-08-02: five of six
  # builders faithful, the sixth stale by exactly the security fix. This gate reads the RUST
  # literals and the Rust field order as the second source; `--self-test` mutates a COPY (v3→v2,
  # nonce deleted, fields transposed) and refuses if any mutation stays green.
  "signing-message-fidelity|60|python3 scripts/check-signing-message-fidelity.py"
  "signing-message-fidelity-red|60|python3 scripts/check-signing-message-fidelity.py --self-test"
  # A SCHEMA EPOCH THAT MOVED AND SAID SO NOWHERE. `docs/VK-REGEN-LOG.md` is how a reader
  # reconstructs what each `CANONICAL_STATE_SCHEMA_EPOCH` re-genesised. On 2026-08-01 its last
  # row read "Schema epoch UNCHANGED at 20" while `persist/src/lib.rs` read 21 — `6441705e8`
  # bumped it and ran no emit — and the constant moved TWICE MORE the same day (`a62c48c7b`
  # 19 → 20 with no row at all, `6342defa2` 21 → 22).
  # ⚑ THE PLACEMENT IS THE FINDING, not the comparison. In the words of the lane that found it:
  # "an epoch is a Rust constant ANY COMMIT CAN BUMP, while ONLY the emit script appends to that
  # log — a gate that runs inside the emit path REPRODUCES THE BLIND SPOT EXACTLY." So this is
  # keyed on the CONSTANT and lives outside `emit_descriptors.py` entirely, with a second body one
  # altitude closer still (`dregg_persist::schema_epoch_log_row`, which reds for a lane that edits
  # the constant and runs `cargo test -p dregg-persist` without ever thinking about a descriptor;
  # leg 6 welds it, so deleting it reds here).
  # It also reads the SCHEMA EPOCH LEDGER against an INDEPENDENT source — `git log -p --
  # persist/src/lib.rs` — so a bump is caught by two legs that share no input, rather than by one
  # constant compared against its own definition.
  # ⚠ FAIL-CLOSED. An unparseable epoch cell, a missing column, a missing ledger, a missing
  # constant and a blind reader are each RED. A log with no `epoch:N` row is the shape this exists
  # to refuse: otherwise one malformed row silently disables the whole gate.
  # ⚠ NEVER fix a red here by widening what is compared. The constant moving IS a re-genesis;
  # the fix is an event row + a ledger row saying what re-genesised, what re-emits, and what now
  # refuses to load. ~0.4s, no cargo, no Lean, no node.
  # The `-red` row is not optional — the headline is a NEGATIVE assertion. It drives all three
  # directions on SCRATCH COPIES (bump with no row → red, add the row → green, truncate/garble/
  # delete the column → red), the ledger and monotonicity legs, a blinded reader against its own
  # floors, and — the leg that makes it a measurement rather than an injection — a RECONSTRUCTION
  # OF THE TREE AT `6441705e8`, where it must catch the bump that motivated it. A gate that cannot
  # catch its own origin story is decoration. It mutates nothing in the shared tree.
  "schema-epoch-log|120|python3 scripts/check-schema-epoch-log.py"
  "schema-epoch-log-red|120|python3 scripts/check-schema-epoch-log.py --self-test"
  # `emit_descriptors.py --verify-provenance`'s workflow leg resolves every path a `.github/
  # workflows/*.yml` step invokes, and `working-directory:` decides WHERE it resolves. That
  # scope LEAKED until 2026-08-01 — the reset baseline was taken from the first `- ` anywhere in
  # the file, which in `ci.yml` is `- cron:` under `on: schedule:` at a shallower indent than any
  # step, so the key was never reset again in that file. Both failure modes at once, and the
  # quiet one was worse: EIGHT false `WORKFLOW-GHOST` reds against `metatheory/scripts/*` that no
  # fix could clear (permanent noise trains readers to skip the check), and FIFTEEN static,
  # checkable invocations deferred as "not static" and never checked at all. Neither was visible
  # in the output. Repaired: 36 → 50 sites checked, 30 → 16 not-checkable, 0 ghosts.
  # This row is the scope's own can-it-go-red run, on SYNTHETIC workflows in a temp dir — four of
  # its five cases were verified to FAIL against the pre-repair parser (the fifth is a forward
  # guard on the new stack-popping and says so). ~0s, no git, no Lean, no cargo.
  "workflow-wd-scope-red|60|python3 scripts/emit_descriptors.py --self-test-workflow-scope"
  # ⚑ THE PICKLES SCOREBOARD, WHICH LIVED IN A SCRATCHPAD. "What percentage of Mina's wrap circuit do
  # we emit?" is the number this whole epoch is measured by, and until 2026-08-04 it was a `census.py`
  # in `/private/tmp/.../scratchpad/` re-typed by hand each session. Two figures got quoted all day
  # that the numbers do not support, and both are the shape a hand-read table produces:
  #   * "EndoMul 32x77 exactly Mina's" — Mina's wrap-transaction has SEVENTY-NINE runs of 32 EndoMul
  #     rows, not 77, and at the time it was quoted the Lean assembly emitted ZERO. It was a fact
  #     about MINA'S blob read off one column and repeated as a conformance result about US.
  #   * "Poseidon 89/89, 100%" — quoted as COVERAGE when it was per-instance internal-row identity of
  #     the blocks we do emit. Mina's wrap has 261 permutations; coverage was 34%.
  # So the gate prints both sides of every ratio and prints those two corrections in its own output.
  # ⚑ AND IT ASSEMBLES SOMETHING NO SINGLE ARTIFACT HOLDS. `rungsUpto` is a TREE: three branches hang
  # off `w9_prev`, so `w11_bullet.json` is `prev+combine+bullet` and contains no finalize/wraphack/
  # close. Censusing one file UNDERSTATES the assembly and summing the files DOUBLE-COUNTS `w9_prev`
  # five times. The union is built by prefix-stripping, VERIFIED on the emitted bytes (typ+coeffs),
  # and a branch that is not its base plus a suffix BLOCKS rather than grading.
  # This row is the `--self-test` half: it needs NEITHER Lean NOR an emission (Mina's own gate list is
  # the honest candidate), ~2s. The full grade needs a `DREGG_WM=wrap` emission and is under --all.
  "wrapmain-shape-diff-red|120|node bridge/mina-zkapp/scripts/wrapmain-shape-diff.mjs --self-test"
  "no-degraded-felt|180|bash scripts/check-no-degraded-felt.sh --rev HEAD"
  # ⚑ ADDED 2026-08-07, and the reason is a mispriced VK rotation. `pi_disposition_census.py`
  # answers "does any constraint IN THESE TWO REGISTRIES read PI index i". A prior lane read a zero
  # there as "nothing reads this slot" and declared eleven felts dead; four of them
  # (`EFFECTS_HASH_GLOBAL`, v1 37..40) are `sched::EFFECTS_HASH_GLOBAL` inside the 49-felt
  # bilateral-schedule window, projected into `dregg-bilateral-aggregation-v3` where the EMITTED
  # bytes force them (4 `window_gate`s) and pin them to its outer PI. The script now carries a
  # `PROJECTIONS` table CHECKED against those bytes and refuses (exit 1) when a declared projection
  # stops holding — so deleting the consumer goes RED here instead of quietly handing the slot back
  # to the "nothing reads it" column. It was a doc-reproduction script wired into no gate at all,
  # which is why the refusal needed a row before it could ever fire.
  "pi-projections|120|python3 scripts/pi_disposition_census.py"
  "pi-projections-red|120|python3 scripts/pi_disposition_census.py --self-test-projections"
  "emitter-routing|120|bash scripts/check-emitter-routing.sh"
  "anchored-lc-committee|60|bash scripts/check-anchored-lc-committee.sh"
  "anchored-lc-committee-red|60|bash scripts/check-anchored-lc-committee.sh --self-test"
  # ADDED 2026-09-29 with the `valid_until`-is-a-height cutover (issue #46): a production `Turn`
  # literal with `valid_until: None` in sdk/node/intent/starbridge-v2/coord never expires and
  # falls off the verified producer. Replaces the `include_str!` text ratchets of PRs #78-#84.
  "turn-valid-until|60|bash scripts/check-turn-valid-until.sh"
  "turn-valid-until-red|60|bash scripts/check-turn-valid-until.sh --self-test"
  "byte-to-felt|120|bash scripts/check-byte-to-felt.sh"
  "p3-rev|120|bash scripts/check-p3-rev.sh --rev HEAD"
  "drift-taxonomy|120|bash scripts/check-drift-taxonomy.sh --rev HEAD"
  "no-unchecked-auth|300|bash scripts/no-unchecked-auth.sh"
  "mirror-gates|900|bash scripts/check-mirror-gates.sh"
  "mirror-gates-canary|900|bash scripts/mirror-gates/canary.sh"
  # SPLIT 2026-07-27. The execution phase is one `cargo test --test <stem>` per gate across
  # 24 binaries; it grew past 600s and TIMED OUT, which is not a verdict — and a timeout ran
  # NEITHER phase, so this row reported nothing for a whole session while looking like
  # coverage. That is precisely the disease this gate was written to catch. S1..S4 need no
  # cargo, take ~0s, and catch the delete/rename/manifest-edit class; they run here. The
  # execution half keeps its real budget under --all, where it can finish.
  "gates-executed-static|120|python3 scripts/check-gates-executed.py --static-only"
  # feature-tiers is the STATIC half only (seconds, no cargo): every (crate, feature) pair in the
  # tree has a tier, and no tier row is stale. The T3 COMPILE sweep it plans is nightly and lives
  # in .github/workflows/feature-surface.yml — `scripts/feature-t3-sweep.sh` runs it by hand.
  "feature-tiers|180|python3 scripts/check-feature-tiers.py"
  "feature-t3-ratchet|60|bash scripts/feature-t3-sweep.sh --self-test"
  "ci-invariants-structural|900|bash scripts/ci-invariants.sh structural"
  "descriptor-drift|1800|bash scripts/check-descriptor-drift.sh --rev HEAD"
  # ⚑ DECORATIVE PUBLIC INPUTS — the class found BY HAND THREE TIMES before it was a gate.
  # A `pi_binding` ties a column to a public input and to NOTHING ELSE, so a descriptor can publish
  # a bank hash, an app hash, a target root, and never name that column in a gate body or a lookup
  # tuple. `solLcVerifyDesc` did exactly that with eleven anchors; `LightClientSolanaAir` §6b said
  # in PROSE that "the identical decomposition holds for the Midnight and Tendermint descriptors"
  # and prose is not a gate. Measured 2026-08-04 over all 84 served IR-v2 descriptors: 235
  # decorative anchors in 21 of them, 63 across the five light-client VERIFY descriptors.
  # ⚑ THAT LAST NUMBER IS 62 NOW, AND SOLANA IS 10 (it went 11 → 19 → 10 in one day). The verify
  # rung absorbed `dregg-solana-stake-table-fold::v1`, so its trust anchor is the fold's eight
  # `.last` output lanes instead of nine `.first` limbs no constraint read. Read the baseline
  # header before treating either move as a regression: COLUMN COUNT IS THE WRONG DENOMINATOR.
  # The check builds the column-connectivity graph (two columns adjacent iff ONE constraint names
  # both) and reds when a PI-bound column's component is a singleton it was not baselined as.
  # ⚠ An ARITY-1 RANGE LOOKUP READS A COLUMN AND JOINS IT TO NOTHING — Mina's eighteen 29/22-bit
  # lane bounds do not make its published state hashes bound, and the gate says so.
  # Ratchet, not ban: `scripts/descriptor-anchor-inertness-baseline.txt` may only shrink, and a NEW
  # descriptor carrying decorative anchors with no row is red. Lean twin (the six light clients as
  # named theorems, each a tripwire meant to fail when a binding lands):
  # `metatheory/Dregg2/Circuit/Emit/LightClientAnchorConnectivity.lean`.
  "descriptor-anchor-inertness|60|python3 scripts/check-descriptor-anchor-inertness.py"
  "descriptor-anchor-inertness-red|60|python3 scripts/check-descriptor-anchor-inertness.py --self-test"
  # ⚑ A FULLY-IMPLEMENTED GATE THAT NOTHING RAN. `emit_descriptors.py --verify-provenance` has
  # existed for months, checks every descriptor byte against `circuit/descriptors/PROVENANCE.json`,
  # and was invoked by NO `.sh`, NO `.yml` and NO `.py` — 13 references in the tree, every one of
  # them prose. `check-descriptor-drift.sh:130` names it IN A COMMENT and invokes only
  # `--verify-by-name-routing`, whose UNSTAMPED leg reads `by_name_sha256` alone and therefore
  # cannot see the subdirectory legs at all.
  # ⚑ MEASURED at `ca0970378` by this row's own `--rev`: EIGHT of the shared table AIRs did not
  # match their stamped sha256 and TWO (`chip-v1`, `chip-state16-v1` — the Poseidon2 chip every
  # descriptor's hash sites lower into) had NO stamp row whatsoever. Ten of ten tracked artifacts
  # wrong, in HEAD, with nothing red. Repaired in the stamp by `f0a34748f`.
  # ⚑ WHY IT WENT UNRUN IS THE REAL DEFECT, and `--rev HEAD` is the fix. The gate used to grade
  # THE WORKING TREE, which in a ~10-lane shared tree means any sibling's in-flight emission reds
  # it — right now a co-tenant's uncommitted `EmitByName.lean` edit makes the working-tree form
  # report a GHOST — and `--stamp-existing`, its only repair path, REFUSES while `metatheory/` is
  # dirty, which it never is. `DREGG_VK_REGEN_ALLOW_DIRTY=1` then records `source_dirty=true`,
  # which `--strict` refuses: a stamp that looks taken and isn't. Three lanes hit that wall in one
  # day and all three correctly declined, so the artifacts stayed unstamped. A gate whose only
  # correct invocation is impossible under the conditions the repo actually operates in does not
  # get fixed; it gets routed around.
  # So this row asks the question that is ALWAYS ANSWERABLE: are the COMMITTED bytes what the
  # COMMITTED stamp pins? Detached clean worktree, HEAD-vs-HEAD, no Lean, no cargo, ~5s.
  # (2026-11-06, SUBSTRATE-DECISION §9 row 4: `--stamp-existing`, the ack, ALLOW_DIRTY and
  # `--strict` are DELETED; the emit stamps automatically from a committed closure, and this
  # row additionally refuses a stamp whose `mode` is not `emit`. The history above is kept as
  # the record of why.)
  # ⚠ `--strict` is deliberately NOT here. Its extra clause compares the stamp's tree hash against
  # `HEAD:metatheory/Dregg2`, which moves on any commit to any of 2300 Lean modules — red within
  # minutes of any stamp and permanently after, i.e. furniture. Its honest question ("are the
  # descriptors stale w.r.t. Lean?") is answered by RE-DERIVING, which is the `descriptor-drift`
  # row above. `source_dirty` was moved OUT of `--strict` into the always-checked set for the
  # mirror-image reason: it is a property of the committed stamp, always answerable, and it was
  # the one clause that would have caught the force-stamp.
  # ⚠ BUDGET IS MEASURED, NOT GUESSED, and it is generous on purpose: a TIMEOUT is not a verdict,
  # and this table has already lost a whole session's coverage to one (`gates-executed`, split
  # 2026-07-27). The cost is a 454 MB detached-worktree checkout plus the four door scans (4344
  # tracked .rs, 2300 .lean, 26 workflows). MEASURED 2026-08-02: ~18s idle, 109s while sibling
  # cargo builds saturate the disk — 15% CPU, i.e. I/O-bound, so the tail is contention, not work.
  "provenance|600|python3 scripts/emit_descriptors.py --verify-provenance --rev HEAD"
  # The `-red` row is not optional: "nothing has drifted" is a NEGATIVE assertion and passes just
  # as happily on a broken reader — which is what this gate was, for months, at zero invocations.
  # Drives all four defect shapes the ten table AIRs were actually in (a moved byte, a dropped
  # stamp row, a row whose artifact is gone, a `source_dirty=true` stamp) plus BOTH directions on
  # the byte and the stamp (restore -> green, so the red was the mutation and not the machinery),
  # the clean control, and the VACUITY FLOOR — an empty walk must refuse, not report PASS over
  # zero artifacts. Scratch copies in a temp worktree; the shared tree is never touched.
  # MEASURED 2026-08-02: 228s under load, which TIMED OUT at 300s on its first wired run — eight
  # injected faults each re-running the four door scans over inputs the proof never mutates, i.e.
  # eight identical scans measuring nothing. The delta cases now skip those (the argument for why
  # that is sound is in `_verify_provenance_findings`, and ONE full-path run keeps it honest):
  # 95s under the same load, and 9 cases became 11.
  "provenance-red|600|python3 scripts/emit_descriptors.py --self-test-provenance"
  # ⚑ TWO OF THE TEN UNCALLED `--check` REGENERATORS, WIRED (2026-08-10). A census of the regen
  # family found ten scripts owning ~50 committed artifacts whose freshness-vs-source question is
  # asked by a `--check` mode that NO workflow, gate script or test invoked.
  # `check-emitter-routing.sh`'s `regen:` class names eight of them and verifies only that the
  # script EXISTS and mentions the file — never that the file is current — so the whole family read
  # as routed while being ungraded.
  # These two are the ones that cost nothing: no Lean, no cargo, no prover, no hbox lane. MEASURED
  # on this laptop: 0.17s and 0.66s. The other eight need `lake build` + `lake env lean --run`
  # (`regen-mina-commit-stages`, `regen-wrapmain-fixtures`, `regen-cert-qp`) or a real prover run on
  # a named hbox lane (the five `regen-pasta-*`), which is a build-box row and not this table's.
  #
  # `gen-mina-step-srs --check` re-decodes `metatheory/emitted/mina-accumulator/vesta_srs_g.bin`
  # into memory and diffs against `Dregg2/Circuit/Emit/MinaStepSrsG.lean` — 65,536 Vesta generators
  # that `mina_accumulator_discharge` trusts. It reds on EITHER side moving: a drifted blob or a
  # hand-edited Lean file. This is the transcription hop the repo keeps deleting, and until now the
  # only thing standing between the two copies was the sha256 pin on the blob, which says nothing
  # about the Lean.
  "mina-step-srs|60|python3 scripts/gen-mina-step-srs.py --check"
  # `test-drift-taxonomy.sh` is the -red row for `classify_descriptor_drift.py`, the classifier that
  # decides whether a descriptor change is a cheap tail-append or a re-genesis-forcing geometry
  # widen. Six cases including both non-vacuity poles (tail-append is NOT refused; geometry-widen IS
  # refused without `--allow-regenesis`). A classifier that quietly stopped refusing would have
  # waved a wipe-requiring change through, and nothing was running its driver.
  "drift-taxonomy-red|120|bash scripts/test-drift-taxonomy.sh"
  # A Lean emitter asking the poseidon2 chip for an arity the chip AIR does not admit. The
  # descriptor it produces CAN NEVER BE SATISFIED, and nothing said so: `57105f387` found the wide
  # blinded membership tooth had been asking for arity 9 SINCE THE DAY IT WAS WRITTEN, and it
  # surfaced only because somebody finally tried to prove against it — which for a staged
  # descriptor may be never. There is a second mode and it is worse: at an arity outside
  # {7,11,16} the deployed witness generator puts the ARITY TAG in lane 4 and zero in 5/6, so
  # inputs the emitter handed the chip never enter the preimage. Refused is loud; discarded looks
  # like it worked.
  # ⚑ THE ADMITTED SET IS NOT WRITTEN DOWN ANYWHERE IN THE GATE, and must not be: the AIR carries
  # it as a degree-7 product over the arity column, and a constant re-typed beside its own
  # definition is decoration. The gate hands the DEPLOYED `Ir2Air::Chip` evaluator the honest chip
  # row the DEPLOYED witness generator builds, at each candidate arity, and reads the verdict; it
  # derives the per-lane pin map the same way and the lane-DROP map from a second, independent
  # source (the deployed absorb). 368 descriptors / 35 121 chip lookups across every registry,
  # `by-name/`, the Lean-emitted trees and the staged registry TSVs. Rust, not python, for exactly
  # the reason above — it must RUN the chip.
  # ⚠ NEVER fix a red here by widening the admitted set. It is the chip's S-box budget; a bad
  # arity changes in `metatheory/` and re-emits.
  # ⓘ GREEN since 2026-08-01. It landed RED on one real finding —
  # `guarded-hiding-span-m0-wide-blinded-commit-blind5-v1` asked for arity 8 and arity 14, neither
  # admitted; the SOLE emitted hidden-span descriptor, and unprovable. That is repaired: `spanIns`
  # padded 8 → 11 and `commitStage2WideIns` 14 → 16 in Lean, golden re-guarded, re-emitted (two
  # bytes: the arity tags), and the descriptor now PROVES at the deployed prover for the first time
  # (`circuit/tests/guarded_hiding_span_prove.rs`).
  # ⚠ It also landed with a defect of its OWN which meant it reported nothing in either direction:
  # all six of its tests aborted at arity 17 on `chip_absorb_all_lanes`'s `arity <= CHIP_RATE`
  # assertion, because the lane-drop sweep reused `SWEEP_CEILING = 4·CHIP_RATE`. The generator legs
  # now stop at `DROP_SWEEP_CEILING = CHIP_RATE`, which is the absorb's actual domain; the admission
  # leg still sweeps past it, since `chip_air_row_accepts` is total there.
  # ⚑ The root cause was one level up and is also closed: `chipLookupTupleN`/`ChipTableSoundN` now
  # carry `ChipArityAdmitted` as a CHECKED side condition, so an emitter at a non-admitted arity
  # FAILS TO ELABORATE instead of proving vacuously against `ins.length ≤ CHIP_RATE`.
  # The `-red` row is not optional: the headline is a NEGATIVE assertion. It drives the gate
  # against a checked-in reconstruction of the PRE-`57105f387` descriptor (extracted from that
  # commit's parent, out of the Lean emitter's own byte-pinned golden — not a fixture anybody
  # invented) and requires BOTH modes to fire; requires the same descriptor GREEN after its
  # arity-11 repair; and points the corpus walk at an empty directory so a dead reader cannot read
  # as clean. It mutates nothing in the shared tree.
  "chip-absorb-arity|1200|bash scripts/check-chip-absorb-arity.sh"
  "chip-absorb-arity-red|1200|bash scripts/check-chip-absorb-arity.sh --self-test"
  "wasm-freshness|120|bash scripts/check-wasm-freshness.sh"
  # ⚑ THE REPO SHIPS TWO BROWSER BUNDLES AND THE GATE WAS AIMED AT ONE OF THEM.
  # `wasm-freshness` grades `wasm/pkg` — the site runtime. The extension's engine
  # (`extension/dregg_wasm.js` + `dregg_wasm_bg.wasm`, `--target no-modules`, loaded by the
  # MV3 service worker with `importScripts`) is a SEPARATE artifact, and until 2026-08-07 no
  # build step refreshed it and no gate looked at it. It rotted for a week: `wasm/src/lib.rs`
  # exported `build_poa_signal_claim_turn`, the shipped glue had ZERO occurrences of it, and
  # `background.ts:3499` refused EVERY judged PoA Signal claim on live beta. The instrument
  # was one artifact away from the drift.
  #
  # The second row grades THE PACKAGE — the .zip a store receives and a user installs —
  # because the directory and the archive are two things and only one of them ships.
  #
  # ⚑ BOTH ROWS ARE EXPECTED RED IN A LIVE MULTI-LANE TREE, for the same reason
  # `wasm-freshness` is: the wasm32 source closure moves every few minutes, so any bundle
  # older than the last lane's commit is genuinely stale. That is the gate working.
  # OWNER: whoever ships. CLEAR IT: `bash scripts/build-web-artifacts.sh` (both bundles), or
  # `cd extension && ./build.sh wasm && ./build.sh package` (the extension's alone).
  # Do NOT silence either row — an unshippable artifact reading green is the whole wound.
  "extension-wasm-freshness|180|bash scripts/check-wasm-freshness.sh extension --kind no-modules"
  "extension-package-freshness|180|bash scripts/check-wasm-freshness.sh extension/dist/dregg-cipherclerk-chrome.zip --kind no-modules"
  # The three rows above are NEGATIVE assertions — they pass just as happily when the
  # refuser is broken, which is precisely how this class survives. This row drives the gate
  # RED constructively on nine planted defects (missing record, superseded schema, edited
  # blob, edited glue, a glue a week behind whose export is GONE, a moved source
  # fingerprint, a glue that is not the kind claimed, and a package with no record) and
  # asserts each plant LANDED before reading the verdict — plus two CONTROLS asserting the
  # unmutated bundle is GREEN, without which nine reds are consistent with a gate that
  # refuses everything. It builds its subjects in a temp dir and mutates nothing in the
  # shared tree. ~5s, no cargo.
  "wasm-freshness-red|180|bash scripts/check-wasm-freshness.sh --self-test"
  "effect-payload-shape|900|bash scripts/check-effect-payload-shape.sh"
  # An em-dash in a string a PLAYER reads. Paired with its own can-it-go-red run, the way
  # `feature-t3-ratchet` is: the gate is a NEGATIVE assertion, which is the shape that passes
  # just as happily when the reader is broken. ~1s, no cargo.
  "player-copy-punctuation|180|python3 scripts/check-player-copy-punctuation.py"
  "player-copy-punct-red|60|python3 scripts/check-player-copy-punctuation.py --self-test"
  # A word from the project's PRIVATE VOCABULARY (`executor`, `receipt`, `merkle`, `no-cheat`, `fog`
  # …) in copy a player reads. Same shape and the same pairing as the two rows above, and for the
  # same reason: `dreggnet-web/src/guide.rs` had this gate and it WORKED, on ONE function — so
  # `/guide` scored 0 violations while the same list was broken on 6 of 13 live surfaces. The list
  # is now `scripts/player-vocabulary.tsv`, read by this sweep AND by `guide.rs` via `include_str!`,
  # because a second reader must not mean a second list. The `-red` row is not optional: the
  # headline is a NEGATIVE assertion, so it passes just as happily when the reader is broken, and
  # the self-test also drives the sweep's own MIN_SURFACES / MIN_UNITS floor red to show it bites.
  # ~1s, no cargo, and no wrapper needed — token 2 of the command is the script itself.
  "player-vocabulary|180|python3 scripts/check-player-vocabulary.py"
  "player-vocabulary-red|60|python3 scripts/check-player-vocabulary.py --self-test"
  # A ROUTING IDENTITY where a player expects a PERSON — `71b278f3dc43444…` in a column headed
  # Holder. The third widening of the same shape, and the clearest one yet that scope is the whole
  # game: `refusal::audit_player_text` has a raw-hex-run rule and has had one for a while — but say
  # WHERE it bans, because this file's whole thesis is that a gate not in this list is not a gate.
  # It is not in this list and it is not on any production path: measured 2026-07-27 it has TWENTY-
  # FOUR call sites and every one of them is test code (`baseline/production-callers.tsv` classes it
  # THEATRE), in `dreggnet-offerings/src/refusal.rs`'s own module tests, `dreggnet-web/tests/
  # refusal_copy_gate.rs`, and three `dreggnet-web` src test modules — each pointed by hand at an
  # ENUMERATED list of surfaces. That is the right runtime for a linter over STATIC copy (a check at
  # render time would be inspecting a message already on its way to a player), so this is not a
  # function to wire; it is a claim to state precisely. Its rule scored zero on this wound because it
  # is pointed at REFUSALS and a roster is not a refusal. It would not have
  # caught it pointed there either — the sites truncate to 15–18 chars and that rule starts at 32,
  # the shortest run in this product that IS a key. Seven sites across four crates on 2026-07-27,
  # each crate having minted its OWN `fn short_identity`, so the wound propagated by copy-paste
  # rather than by call — which is why rule R2 bans re-minting one (`short_root` / `short_digest`
  # stay legal: a root IS a machine value). The `-red` row is not optional: the headline is a
  # NEGATIVE assertion, so it passes just as happily on a broken reader, and the self-test also
  # narrows the scope to drive the MIN_FILES / MIN_POSITIONS floor red. ~1s, no cargo, and token 2
  # of the command is the script itself, so it needs no wrapper.
  "identity-as-a-name|180|python3 scripts/check-identity-as-a-name.py"
  "identity-as-a-name-red|60|python3 scripts/check-identity-as-a-name.py --self-test"
  # The JavaScript inside a Rust `r##"…"##` is a `&str` to rustc and to every reader
  # downstream of it. `dreggnet-web/src/telegram_miniapp.rs` shipped a SyntaxError in
  # `TG_SHELL_SCRIPT` for FOUR DAYS: a dead Mini App serving 200, `cargo test` green,
  # this table green, because nothing here had ever parsed a line of it. `node --check`
  # over every embedded bundle, ~4s, no cargo. Paired with its own can-it-go-red run —
  # like `player-copy-punct-red` and `feature-t3-ratchet`, it is a NEGATIVE assertion,
  # and it also asserts a MINIMUM unit count so a dead extractor cannot read as clean.
  # ⚠ It needs `node`, and it FAILS rather than skips without one. That is the point.
  "embedded-js|180|python3 scripts/check-embedded-js.py"
  "embedded-js-red|120|python3 scripts/check-embedded-js.py --self-test"
  "test-stubs-firewall|300|bash scripts/check-test-stubs-firewall.sh"
  "no-disarmed-guard|240|bash scripts/check-no-disarmed-guard.sh --rev HEAD"
  "no-disarmed-guard-red|120|bash scripts/check-no-disarmed-guard.sh --self-test"
  "lean-seed-freshness|120|bash scripts/check-lean-seed-freshness.sh"
  # ⚑ EXPECTED RED until a seed is cut under the closure key (2026-08-07 cutover).
  # `lean-seed-freshness` now compares the pin's `DREGG_CLOSURE_HASH` — the `Dregg2.FFI`
  # boundary closure, the set the archive actually holds — against this checkout's, both from
  # `scripts/lean-seed-key.sh`. The pin's field is EMPTY right now, which means no published
  # asset is reachable by name for any checkout, so this row fails with that message.
  # OWNER: `.github/workflows/lean-seed.yml` (workflow_dispatch-only, deliberately).
  # CLEAR IT: `gh workflow run lean-seed.yml -f platforms=linux-x86_64`, then write the printed
  # `DREGG_CLOSURE_HASH` into `dregg-lean-ffi/lean-seed.pin`. Do NOT silence the row instead —
  # an empty pin is MAXIMAL drift, and reading it as "no drift" is the eleven-day stale seed
  # this gate exists to have caught.
  # It still says nothing about what is IN the archive, and a seed can match the pin and still be missing every verified
  # decision export. Measured 2026-07-30 (issue #41): the seed installed in this checkout
  # carried 188 `Dregg2_*.o` against a 243-module boundary closure — 55 in-tree modules
  # absent, and no `Dregg2_FFI.o` — while reporting ZERO undefined initializers, because the
  # boundary object that would reference the missing 55 was itself missing. "It self-links"
  # is not the bar; the closure is. This row reads the members.
  "lean-seed-closure|180|bash scripts/check-lean-seed-closure.sh"
  # ⚑ THE THIRD QUESTION ABOUT THIS ARCHIVE, AND IT IS NOT A ROW HERE — read this before assuming
  # the two rows above cover it (2026-08-07). `lean-seed-freshness` asks whether a PUBLISHED ASSET
  # matches this checkout's closure key. `lean-seed-closure` asks whether a module has a MEMBER.
  # NEITHER asks whether a member is OLDER THAN THE `.lean` IT WAS COMPILED FROM, and that gap cost
  # a week: `dregg-lean-ffi::deployed_constraint_probe` printed `8 passed` from 07-30 to 08-06 with
  # SIX of its eight assertions false, because the archive linked on the box carried a 2026-07-25
  # `Dregg2_Exec_DeployedConstraint.o` — the pre-cutover admission-wire evaluator — that agreed
  # with the test's equally pre-cutover wire builder. Two stale things agreeing reads exactly like
  # correctness, and build.rs's PROVENANCE DOWNGRADE could not see it: that gate is whole-archive
  # and fires when the Lean build did not run. The Lean build ran. The `.c` was current. The splice
  # ran. ONE object was old.
  # For the archive a BUILD LINKED, the check is `dregg-lean-ffi/tests/linked_archive_freshness.rs`,
  # NOT a script and deliberately so: the only process that knows WHICH archive was linked is the
  # one that linked it, so build.rs hands the path over (`DREGG_LEAN_LINKED_ARCHIVE`) and the test
  # walks its `Dregg2_*.o` members against `metatheory/`. A script here would have to guess among
  # the per-OUT_DIR working copies, and `rerun-if-changed` refreshes those before a link anyway —
  # so a stale one merely resident in `target/` is not evidence of anything.
  # RUN IT WITH: `cargo nextest run -p dregg-lean-ffi --features lean-lib`.
  #
  # ⚑ AND FOR THE SEED, WHICH NO PROCESS LINKS — THIS ROW (added 2026-08-07). The paragraph above
  # is exactly why the SEED went unwatched: `libdregg_lean.a` is copied into every new `OUT_DIR`,
  # arrives by fetch/rsync/bootstrap, is inherited across checkouts, and is linked by NOTHING, so
  # the test above never has it as its subject. Measured the day this row landed: the working
  # archive was CLEAN (0 of 323) and the seed carried **56 stale members of 188** against the
  # `.lean` comparison — and **174 of 197** once the emitted `.c` is counted too, which is the
  # comparison this row makes. It is the same question, one subject wider, and it is a script
  # because the seed's path is FIXED (`dregg-lean-ffi/libdregg_lean.a`), needs no cargo, and takes
  # about a second.
  # STRICTLY STRONGER, NOT WIDER: a member must be at least as new as `max(.lean, .lake/build/ir/
  # *.c)`. The `.lean` half is the Rust test's comparison unchanged; the `.c` half only ever makes
  # it fire MORE (lake regenerates a module's C when its compiled image changes for reasons its own
  # source cannot show — an import moved). ⚠ Never raise SLACK_SECS to clear a finding; a member
  # that may legitimately lag is an ALLOWLIST entry with a written reason, and there are none.
  "lean-seed-member-freshness|120|python3 scripts/check-lean-seed-member-freshness.py"
  # The `-red` row is not optional: the headline is a NEGATIVE assertion and passes just as happily
  # on a broken reader. It plants a member stamped 2026-07-25 in a synthesized archive, ASSERTS THE
  # PLANT IS PRESENT, then reads the verdict; it also proves both `ar` long-name dialects parse, that
  # a `_` inside a module name still maps, that the `.c` leg fires where the `.lean` leg cannot, that
  # an hour is not inside the slack, and that every absent/unreadable/timestamp-stripped input FAULTS
  # rather than reading clean. ~1s, no cargo.
  "lean-seed-member-freshness-red|60|python3 scripts/check-lean-seed-member-freshness.py --self-test"
  "nightly-verdict|120|bash scripts/check-nightly-verdict.sh"
  # A function that DECIDES something — `verify_*`, `check_*`, `*_admits` — with no
  # production caller. `dregg_circuit::effect_vm::verify_balance_limb_pis` was the
  # Group 6 range precondition, was re-exported twice, said "verifiers MUST call this",
  # and was invoked by no production path and no test: nothing in the tree could report
  # that, because it compiles (it is `pub`, so not dead code) and has no failing test
  # (it has no test). A ratchet over the 235 known rows, not a threshold over the ~4 800
  # uncalled `pub fn`s — a library's surface is SUPPOSED to have callers it cannot see,
  # and a gate over that number is a wall nobody reads. Paired with its own red run: its
  # first scanner LOST both freshly-added call sites to a `/*` inside a line comment and
  # reported the symbol UNCALLED minutes after it was wired, which is exactly the
  # direction a negative assertion fails in. ~40s, no cargo.
  "production-callers|300|python3 scripts/check-production-callers.py"
  "production-callers-red|60|python3 scripts/check-production-callers.py --self-test"
  # An `#[ignore]` with no reason: a test switched off by someone no longer here to be
  # asked. The tree is at ZERO of them (270 attributes, 270 reasons) and this keeps it
  # there — at 270 across 224 crates, one un-annotated addition merges unnoticed.
  # ⚠ It is NOT `grep -F '#[ignore]'`, which reports 177 violations on a tree that has
  # none: this repo writes ABOUT its ignores constantly, in doc comments, in
  # `producer_descriptor_coverage_gate.rs`'s 24-row table, and inside the reason
  # strings themselves (`devnet_adversarial.rs` explains that "an #[ignore] reports
  # `ignored` (honest), not `ok` (a lie)"). So it scans source with comments and string
  # literals BLANKED, reusing check-production-callers.py::strip_noise rather than
  # growing a second Rust reader. ~27s, no cargo. Paired with its own red run — the
  # headline is a NEGATIVE assertion, and the -red row drives all four disease shapes
  # plus the nine prose shapes that fooled the naive scan. It also asserts a MINIMUM
  # population so a broken reader cannot read as clean.
  "bare-ignore|180|python3 scripts/check-bare-ignore.py"
  "bare-ignore-red|60|python3 scripts/check-bare-ignore.py --self-test"
  # The SAME disease one altitude up: a documentation example switched off. A ```ignore
  # doctest fence is an example the compiler was told not to read, and on 2026-07-27 the
  # tree had 71 of them with ZERO reasons — structurally none COULD have one, because a
  # fence info-string rejects unknown attributes. ~38 of the 71 turned out not to be
  # structural at all: real in-scope API that had DRIFTED (a missing `use`, a renamed
  # function) and was silenced rather than repaired. So the reason goes as the first
  # line INSIDE the block, where the reader gets it too, and ```ignore is reserved for
  # structural impossibility — a dependency cycle, a deliberately broken exhibit, source
  # quoted from a non-dependency. It also catches the INERT-ATTRIBUTE shape
  # (```ascii,no_run): rustdoc reads any unknown token as "not Rust", so the attribute
  # beside it silently does nothing — `gating defaults to silence`, in a code fence.
  # ⚠ NOT a grep, and NOT strip_noise either — strip_noise BLANKS comments and a fence
  # lives inside one, so it is the same lexer run inside-out. The -red row drives seven
  # disease shapes and twelve shapes a naive grep gets wrong on this tree (a ```ignore
  # nested inside an open ```text block; the marker named in prose; a fence inside a raw
  # string literal). Exemptions live in `scripts/doctest-ignore-baseline.tsv` and
  # RATCHET: a stale row is a FAILURE, so a repaired fence retires its own exemption.
  # Rides the default `bare-ignore` invocation too, so it cannot be the leg left unwired.
  "doctest-fences|180|python3 scripts/check-bare-ignore.py --fences"
  "doctest-fences-red|60|python3 scripts/check-bare-ignore.py --fences --self-test"
  # Every binary()/package()/test() name in `.config/nextest.toml` still resolves. That file
  # selects tests BY NAME, and a name that outlives its referent does not mislead a reader —
  # it changes what the suite RUNS. It has cost this repo twice. 2026-07-15, LOUD: a deleted
  # test binary made nextest hard-error while validating EVERY profile, so
  # `scripts/test-gauntlet.sh` exited nonzero in all four modes HAVING RUN ZERO TESTS, for an
  # unknown number of commits. 2026-07-27, SILENT: measured against nextest 0.9.136/137/140,
  # `binary()` and `package()` hard-error on an unresolvable name (exit 96) but `test(~…)`
  # returns exit 0 and prints NOTHING — and 21 of the 41 `test(~…)` names in that file named
  # tests deleted weeks earlier in `d260028f1`. Polarity decides the damage: in a `not (…)`
  # exclusion a dead name is only a lie, but in `heavy`/`gpu`'s POSITIVE selectors it silently
  # stops the profile running the test it exists to run, and drops GPU teeth into the
  # GPU-less `armed` lane. ~35s, NO cargo build — resolution is `cargo metadata --no-deps`
  # for binary/package (which beats nextest's own check, that can only fire after a full
  # workspace compile) and an `rg` over `fn` declarations for test(). Paired with its own red
  # run like the rows above, same reason: a NEGATIVE assertion passes just as happily when
  # its own extractor is broken. That row is not decoration — it caught this gate injecting
  # its fault into a COMMENT line and then pronouncing itself blind, and it drives the
  # MIN_NAMES / MIN_PACKAGES / MIN_FNS floors red so a dead reader cannot read as clean.
  "nextest-names|300|python3 scripts/check-nextest-names.py"
  "nextest-names-red|120|python3 scripts/check-nextest-names.py --self-test"
  # A test that `return`s on a missing fixture and reports `ok`. STRICTLY WORSE than the
  # row above: an `#[ignore]` prints `ignored`, which is a true statement, and this prints
  # the same word cargo prints for a test that ran every assertion. `libtest` has exactly
  # two runtime outcomes and no runtime skip, so `return` is never the honest third option.
  # Measured 2026-07-27 before the repair: 168 tests, 112 of them the Lean-archive class in
  # `exec-lean`/`node`/`dregg-lean-ffi`/`sdk` — i.e. concentrated in the suites that guard
  # the machine-checked cores, where a green is a claim nobody checked. The mechanism
  # (`dregg_lean_ffi::demand_lean`) already existed and was correct; it was DISARMED
  # everywhere a human looks — `ci.yml` armed it only on a successful seed fetch, and of
  # the last 60 ci.yml runs 0 succeeded, and THIS FILE never set it at all. It is now armed
  # by default (`DREGG_TEST_ALLOW_MISSING_LEAN=1` to opt out, visibly).
  # ⚠ NOT a grep: this tree writes ABOUT its own skips in doc comments and panic strings,
  # so it reads BLANKED source via check-production-callers.py::strip_noise, walks the brace
  # stack to drop `return`s belonging to closures/nested fns/async blocks, and resolves the
  # per-crate bool helpers (`skip_no_lean`, `ensure_oracle`, `skip_if_core_unlinked`) that
  # hide the probe one call away — keying on direct probes alone found 15 of exec-lean's 41.
  # SILENT is ZERO-TOLERANCE (the tree is at zero); INVERSE and REENTRANT are baselined
  # residuals with different fixes. ~50s, no cargo. Paired with its own red run — the
  # headline is a NEGATIVE assertion and its first cut reported ZERO findings tree-wide
  # because one offset was off by one. The -red row drives 7 disease shapes and 9 shapes
  # that must stay quiet (prose, closures, nested fns, an already-`#[ignore]`d test, a
  # two-armed if/else), and the MIN_TESTS/MIN_GUARDED floors so a dead reader cannot read
  # as clean.
  "silent-skip|300|python3 scripts/check-silent-skip.py"
  "silent-skip-red|120|python3 scripts/check-silent-skip.py --self-test"
  # A Cargo package that NO workspace claims, and a commit that does not resolve from a
  # clean checkout of ITSELF. Two shapes of the same silence. The first cost the most:
  # the ten `orb/crates/*` packages — ~40,000 lines of a TLS/HTTP dataplane — were in
  # neither the root `members` nor its `exclude` from `4bcb934a3` (an untitled sweep-up
  # with an empty body) until 2026-07-27. `cargo metadata` from inside any of them exited
  # 101; `cargo build --workspace` compiled NONE of them; so no `#[allow(dead_code)]` in
  # the subtree was checked by anything, which is how `dataplane/src/proxy_grpc.rs` — zero
  # callers repo-wide — kept a module doc saying it was "wired into the running dataplane".
  # The state emits no line: cargo complains only when you stand inside the directory.
  # This gate found SEVEN MORE the same day (`sel4/verifier-pd`, whose own manifest SAID it
  # was standalone and had never been made so; four `[patch]` sources; a nested vendored
  # crate under deos-homeserver's own workspace), so it is a class, not an instance.
  # The second shape is what a shared tree manufactures: AGENTS.md correctly tells each
  # lane to commit only its own named paths, and the result is a commit whose manifests
  # reference a sibling's still-uncommitted work — green for the author, a broken bisect
  # point for everyone. ⚠ IT IS A MANIFEST CHECK, NOT A BUILD: it catches a missing member
  # dir, a path dep on an uncommitted sibling, an unparseable manifest and a declared
  # `[[bin]]` whose source is not in the commit; it does NOT catch a missing `mod foo;`
  # file, a type error, or a missing build-script artifact. `cargo metadata --no-deps` is
  # ~0.3s, a `cargo check` per commit is hours; the manifest half is the half that broke.
  # ~12s / ~12s / ~70s, no compile. The -red row is not optional — the headline is a NEGATIVE
  # assertion — and it injects every fault into a FRESH `git archive` EXTRACT in a temp
  # dir, so unlike most red-proofs it cannot leave the shared tree disarmed. It also
  # blinds its own reader to drive the MIN_PACKAGES floor red.
  "workspace-closure|180|python3 scripts/check-workspace-closure.py"
  "commit-self-contained|180|python3 scripts/check-workspace-closure.py --rev HEAD"
  "workspace-closure-red|600|python3 scripts/check-workspace-closure.py --self-test"
  # ⚑ THE RECURSION FIREWALL, WHICH WAS PROSE UNTIL 2026-08-05. `turn/Cargo.toml:17-25` has
  # forbidden the `dregg-circuit-prove` edge since the prover extraction and justified it with
  # "the seL4 verifier-PD floor and the wasm/zkvm card" — a claim about the DEPENDENCY GRAPH,
  # written in a comment, checked by nothing. No `deny.toml`, no `[bans]`, no `cargo tree` gate,
  # no row in this file. The extraction design named the gate as its own acceptance criterion
  # (§5 PR1) and it was never written.
  # An unenforced firewall gets BELIEVED, and this one shaped code: `mina_head_verifier.rs`
  # could not verify a recursion root at all — while a 46-leaf fold of Mina block 539508's whole
  # phase-2 transcript sat proved and unreachable — because the comment said the edge was
  # forbidden, and nobody could see that BOTH its justifications had expired (the seL4 verifier
  # PDs build no dregg crate; `wasm/Cargo.toml` declares circuit-prove on purpose).
  # The rule is now DATA (`scripts/recursion-closure-policy.tsv`) checked against `cargo
  # metadata`'s resolve — this repo's own oracle for the class, ~15 gating defects deep, none of
  # them broken code. It reads the LIBRARY graph (normal + build edges); `dev` is excluded, and
  # the green control is the live proof of that filter, because `dregg-recursion-verify`
  # dev-deps `dregg-circuit-prove` while being FORBIDden it in the library graph.
  # ⚠ NOT AN ALLOWLIST OF WHO MAY: 123 of 227 members legitimately take the edge. The rows are
  # the set that must NOT, plus REQUIRE/REQUIRE_DIRECT rows so the gate cannot be satisfied by
  # DELETING the capability — "nothing reaches the recursion fork" is trivially true of a tree
  # that can no longer verify anything.
  # ~3s. Exit 3 (BLOCKED) when cargo emits no resolve: the gate DID NOT RUN, which is a failure
  # but not a divergence. The -red row is not optional — the headline is a negative assertion —
  # and it injects faults into the in-memory RESOLVE GRAPH, never the tree, so it cannot leave
  # a shared tree disarmed. It caught a hole in its own first draft: `REQUIRE dregg-node
  # dregg-recursion-verify` would not go red when that edge was deleted, because the node still
  # REACHED the crate via `dregg-circuit-prove`. Hence REQUIRE_DIRECT.
  "recursion-closure|180|python3 scripts/check-recursion-closure.py"
  "recursion-closure-red|300|python3 scripts/check-recursion-closure.py --self-test"
  # The OpenTheory→Lean importer, RUN. `docs/opentheory-importer-poc/OTPoC.lean` replays a
  # real OpenTheory v6 article into Lean `Expr`s and hands each export to the KERNEL — and
  # until 2026-07-27 it was wired into NOTHING: `grep -rn 'opentheory|OTPoC' .github/ scripts/
  # metatheory/lakefile*` returned zero hits, so it ran only when a human typed a command out
  # of a plan doc. Worse, its three real-article imports each sat behind `if ← p.pathExists
  # … else logInfo`, so with the articles absent the file elaborated EXIT=0 having imported
  # exactly one theorem (`True`). Both halves are closed: the Lean file HARD-ERRORS on a
  # missing article, and this row is the thing that runs it. The gate asserts FLOORS (≥3
  # kernel-checked exports, ≥14 axiom-gate discharges, ≥4 reject-tests refused for their
  # STATED reason), because "exit 0" was exactly the signal that lied. ~8s, no cargo; needs a
  # Lean toolchain and FAILS rather than skips without one, like `embedded-js` and `node`.
  # The -red row is not optional: two of the three checks it protects are NEGATIVE assertions
  # (a gate that refuses, a test that expects refusal), which pass just as happily when the
  # probe is broken. It removes each guard from a scratch copy — the axiom gate's exactness
  # check, the `thm` Γ-content check, the articles themselves, the reject-tests' reason
  # assertion — and requires the matching test to go red for its stated reason. A fault
  # injection that matches NOTHING is a failure, so renaming these lines breaks the self-test
  # loudly instead of disarming it. ~42s.
  "opentheory-importer|600|bash scripts/check-opentheory-importer.sh"
  "opentheory-importer-red|900|bash scripts/check-opentheory-importer.sh --self-test"
  # The Mina<->dregg attestation zkApp, RUN. Same shape as the row above and found the
  # same way: `bridge/mina-zkapp/` was in ZERO targets — no workflow, no gate script, no
  # npm workspace (docs/AUDIT-IMPORTER-AND-DOCS.md §3.6, F-B10) — and what was committed
  # did not run: `tsc` failed on `src/DreggPoseidonAttestation.ts` and the PoC that was
  # reported working had run in a SCRATCH DIR at an o1js the tree did not pin. So the one
  # cryptographic result in that directory (Mina's Poseidon and dregg's agree bit-for-bit,
  # and a Kimchi circuit can verify a Merkle path into a root the Rust side produced)
  # could not go red. This row runs it from the committed TypeScript, compiled by `tsc`
  # and executed out of `dist/`: 9 gold digests + the depth-2 root + the field modulus
  # against the Rust probe's pinned table, a real Pickles compile/prove/verify of the
  # in-circuit path, two tamper rejections, and the `DreggAttestedGate` zkApp deploying on
  # a local chain and CONSUMING the proof recursively (that last one is what makes "a Mina
  # zkApp verified…" name something that ran — before this, only a bare ZkProgram had).
  # It also checks the two things the devnet deployment listed AGAINST ITSELF: the ANCHOR
  # (its comment once said "relay-authorized" over a body that checked nothing, and then a
  # lane "fixed" that with a trusted relay key — so this gate now checks the PROOF
  # OBLIGATION `setDreggRoot` carries, that the obligation REFUSES a root with no
  # BabyBear vouch in it, and the placeholder key's polarities as a PLACEHOLDER), and that
  # a WELL-FORMED proof of another statement is refused by VERIFICATION rather than by the
  # parser — with the identical proof bytes accepted on their own account update as the
  # control, which is what makes the refusal attributable.
  # ⚑ Two more legs since 2026-07-28, both MEASUREMENTS that are ratcheted at 2%: RUNG 1
  # is a Poseidon2-BabyBear MERKLE OPENING (2,677 rows/level, 58,971 for the deployed
  # depth-22 — more than one Pickles step's usable rows) and RUNG 2 is ONE FRI QUERY at
  # the deployed geometry (684,726 rows, 13-15 steps). Both are KAT'd elementwise against
  # the DEPLOYED p3 objects via the probe's `p2merkle`/`p2fold` subcommands, and Rung 2
  # needs a 16 GB node heap. That is the size of the thing the placeholder key stands in
  # for, and having it measured is why the docs can say so.
  # ⚠ It needs `node` >= 20, o1js pinned at 2.15.0, and now `cargo`, and it FAILS rather
  # than skips without any of them — like `embedded-js`. The 1.9.1 the tree used to pin is
  # not a choice: its prover bindings abort inside Poseidon absorb during `compile()` on
  # node >= 26. Cargo is required because the third leg is the DREGG SIDE:
  # `circuit-prove/sketches/mina-pasta-hash-probe` is the crate that EMITS the attested
  # root, it is its own workspace so no other row reaches it, and this gate used to be
  # Node-only — so the emitting half of the bridge ran in no gate at all. That leg runs
  # `cargo test --locked` and then the `merkle` subcommand end to end on unprecomputable
  # leaves, cross-checked elementwise against o1js. No Lean. The -red row is not optional
  # — most of these legs are NEGATIVE assertions, which pass just as happily on a broken
  # driver. It injects FIFTY-SIX faults into SCRATCH COPIES of both the TypeScript and
  # the Rust crate (never the shared tree) — and a fault that matches NOTHING is itself a
  # failure. One of them bends only the `merkle` subcommand's printed root: every
  # `cargo test` still passes and only the cross-check catches it, which is the gap the
  # third leg exists to close. Another puts back the coset-descent bug the 16-layer chain
  # leg found — right on ~half of all query indices and on 100% of the all-zero one every
  # row measurement uses, which is why no single-round check saw it.
  # ⚑ Two more legs since 2026-07-28 EVENING, and the eighth is a SOUNDNESS rung, not a
  # measurement. RUNG 6 is the DEEP QUOTIENT: every rung before it starts its fold chain
  # from a WITNESSED reduced opening, so the walk authenticates a number the prover chose
  # and says nothing about the committed trace. It is now COMPUTED from the MMCS-opened
  # rows, the absorbed claimed evaluations and the transcript's alpha, KAT'd against
  # `p2deep` (p3's own `open_input`), and the leg PROVES a witness the pre-rung-6
  # statement admits and requires the new one to REFUSE it — the gap exhibited rather than
  # asserted. RUNG 7 starts the AIR constraint evaluation at zeta (selectors, alpha-fold,
  # quotient-chunk recomposition, closing equality, all KAT'd against p3's own domain
  # algebra) and prices it as `A + N*h` with `A` and `h` MEASURED and `N` — the constraint
  # count across the root's 7 AIRs — named as uncounted rather than invented.
  # ⚑ `SELFTEST_LEGS="deep air"` scopes PASS 2 of the -red row to named legs. The
  # PRE-FLIGHT is never scoped: what you re-run is a budget question, what you notice has
  # rotted is not. A scoped run says so in its PASS line.
  # ⚑ TIERED 2026-07-30, and the cheap tier is the DEFAULT. This row was 3000s and its
  # `-red` partner was 14400s — 56% of this whole table's budget for ONE directory — and
  # in the window that grew it to nineteen legs the self-test found NOTHING. Everything
  # that arc found was found by a cheap exhaustive out-of-circuit differential: the braid
  # twin walks 11,303 segments and found four defects that "would each have compiled and
  # proved cleanly for as far as any affordable run reaches"; the uniform checker walks
  # 820 boundaries and found ALL NINETEEN block-to-block joins broken, first observable at
  # instance 46. An injection proves the gate CAN fire; it does not find defects.
  # So the row here is TIER 0: MEASURED 25s. It runs those twins, the recorded-figure
  # census, the npm coverage check, and PASS 1 of the self-test — which on the day it
  # landed found SIX unusable injections in 3.2 seconds, four pointing at nothing and two
  # matching two sites each. NOTHING IN IT COMPILES A CIRCUIT, and it says so.
  # ⚠ WHAT MOVED OUT OF THE EVERYDAY RUN: every Pickles compile/prove/verify — the zkApp
  # consumption, the tamper refusals proved by a real prover, the row ratchets, the
  # splices, the chains, the ceiling. `--tier 1` (below, under --all) proves one instance
  # per family; `--tier 2` is the old headline. docs/MINA-GATE-TIERS.md has the table and
  # the honest trade.
  "mina-attestation|300|bash scripts/check-mina-attestation.sh"
  # The npm-script coverage mechanism, on its own row and with its own can-it-go-red run.
  # It is the thing that stops tiering becoming a way to quietly stop testing: measured
  # 2026-07-30, NINE npm scripts in `bridge/mina-zkapp/` were in no gate at all and
  # nothing went red when a tenth appeared. Lean has `lean-orphans-allow.txt`; TypeScript
  # had nothing. THREE more scripts appeared while the mechanism was being written, and it
  # caught all three. ~1s, needs node. The `-red` row is not optional — it is a NEGATIVE
  # assertion, which passes just as happily when the reader is broken.
  "mina-npm-coverage|120|bash scripts/check-mina-npm-coverage.sh"
  "mina-npm-coverage-red|120|bash scripts/check-mina-npm-coverage.sh --self-test"
  # ⚑ WHICH KEY IS THIS. `DreggHeadGate.advanceHead` pins a `TERMINAL_VK_HASH` that comes
  # out of an o1js `.compile()`; dregg's key REGISTERED on Mina devnet is DERIVED from
  # Lean-emitted `KimchiWrapMain` gates. The two differ and the gate refuses the registered
  # one — CORRECTLY, they key different circuits at opposite ends of the bridge — but until
  # this row the refusal was one number against another, and in that shape a CATEGORY ERROR
  # and a REAL DRIFT are indistinguishable. This tree has had both: the head's nine `vk_pin`
  # literals once named a program no descriptor in this tree had, and one test caught it.
  # The leg names every notion to the circuit it keys, RECOMPUTES each pin from its producer
  # key ring rather than trusting the emitted literal, and exercises both polarities. It
  # reads JSON and compiles nothing (~2s, needs node + `npm ci` in bridge/mina-zkapp).
  # The `-red` row is not optional: [2]'s drift check is never exercised on a healthy tree,
  # which is exactly the state in which nobody has shown it can fail.
  "mina-vk-identity|180|bash -c 'cd bridge/mina-zkapp && npm run --silent vk-identity'"
  "mina-vk-identity-red|180|bash -c 'cd bridge/mina-zkapp && npm run --silent vk-identity -- --self-test'"
  # ⚑ A CONTROL THAT CALLED ITSELF PERMANENT AND WAS IN NO GATE. `fri-mutation-gate.sh`'s own header
  # reads "THE PERMANENT MUTATION-DIFFERENTIAL CONTROL" and it is the answer to a proof-systems
  # review that ranked in-circuit verifier fidelity the #1 live risk — there is no other systematic
  # differential that the o1js FRI verifier accepts iff dregg's native one does. Grep-exhaustive over
  # `scripts/*.sh` and every workflow, 2026-08-05: invoked by NOTHING. A permanent control that
  # nothing runs is a control in name, and it had been one for weeks.
  # ⚠ THE ADVERSARY WAS CHECKED BEFORE THE WIRING, WHICH IS THE WHOLE ORDER OF OPERATIONS. This tree
  # has a recorded case of a mutation gate whose MUTATION decayed into a no-op — the hostile input
  # equalled the honest one, the gate could still go red, and the ADVERSARY had died with nothing
  # measuring it. Verified at HEAD before this row existed: the baseline decode is still BYTE-EQUAL
  # to the committed `real-root-fri.json`, 74 686 single-felt sites enumerate across 8 regions, and
  # 36 of 40 trials were rejected by BOTH verifiers with real old->new deltas. The remaining four
  # were the allow-listed `commit_pow_witness` (commitPowBits=0 ⇒ unabsorbed by `check_witness`).
  # ⚑ AND THE FLOORS ARE NOW IN THE INSTRUMENT, not only in this note. The twin previously scored an
  # empty population as `agreement 100.000%` (`trials === 0 ? 1 : …`), so an oracle that emitted its
  # baseline and died exited GREEN. It now reds on: a stream shorter than requested, ANY trial whose
  # reported `old->new` are equal (the direct no-op detector), a report shape that would make that
  # detector blind, zero both-rejects, and fewer than two bound regions sampled.
  # This row is the `--self-test`: control green, all four teeth removed ⇒ the forgery arm fires,
  # each tooth alone measured for independent bite (reported, not asserted — `final_poly` is 4 of
  # 74 686 sites and may go unsampled at a smoke count), the free-lane allow-list proved load-bearing,
  # both vacuity floors proved to refuse, and BLOCKED (3) proved distinct from every FAIL code.
  # MEASURED 2026-08-06: ~4 min at 12 trials/leg over nine differential runs, warm.
  # ⚠ It needs `target/release/root_fri_mutation`. The script BUILDS it when absent — a cold
  # `cargo build -p dregg-circuit-prove --release` is the whole budget below — and exits 3 (BLOCKED,
  # not FAIL) if that build cannot run. Produce the binary; do not narrow this row.
  "fri-mutation-red|2700|bash bridge/mina-zkapp/scripts/fri-mutation-gate.sh --self-test"
  # ⚑ THE CHAIN, NOT THE TIP. Until 2026-08-02 this repo's Mina light client read
  # `tip.data.header.protocol_state` off `get_best_tip` v2 and DROPPED `tip.proof` —
  # the merkle-list proof anchoring that tip to the serving peer's frontier root.
  # MEASURED: the reply is 61,193 bytes and the protocol state is 1,544 of them. What
  # was left is `blockchain_length`, which Samasika's short-range branch prefers and
  # which a peer can set to anything. The scope note this tree had been reciting since
  # 07-30 ("not 'and it is the chain the network selected'") named the consequence; the
  # cause was one discarded field.
  # This row asks EACH seed separately (a single `Client` latches onto the first peer to
  # connect, so one call is one peer's opinion), folds each transition-chain proof on
  # openmina's own Poseidon, and refuses any tip that does not descend from the root its
  # peer served. ~2s, offline, no cargo, no Lean, no network.
  # The red path is NOT optional and it is not a separate row, because the headline is a
  # NEGATIVE assertion ("no candidate is unanchored") that passes just as happily when
  # the checker is broken: SEVEN forgeries must be refused, with a control, and with a
  # CATCHER DISCIPLINE — at least two must die on the POSEIDON FOLD with every cheap
  # shape check passing. A suite whose every leg dies on an integer comparison would stay
  # green with the fold deleted, and the first version of this one nearly did (3 of 5).
  # It also prints the COVERAGE MAP: which byte ranges of the reply a flipped bit is
  # refused in (measured 20.2% — the two protocol states and the 290 body hashes), with
  # offsets DERIVED from the binprot layout rather than hardcoded. The hardcoded version
  # broke silently the first time a smaller block arrived.
  "mina-bestchain|300|bash scripts/check-mina-bestchain.sh"
  # THE SIX PICKLES PROVE+BIND HARNESSES, which ran in NO CI SCRIPT AT ALL until 2026-08-01.
  # `grep -rn pickles scripts/ .github/` returned the oracle runner, two workspace-closure
  # allowlist rows and one unrelated path — and not one of `metatheory/fixtures/pickles-*-harness/`.
  # Those crates ARE the accept/tamper-reject evidence for every Lean-synthesized circuit result in
  # the Pickles-in-Lean epoch (R4a's first provable Lean-placed circuit, the Poseidon permutation vs
  # the o1js gold, four curve gates, the first cross-gate copy wire, the 132-row step_main fragment,
  # and now the public-input path), and every one of them went red only when a person typed a
  # command. Same class as `check-guard-modules.py` one layer over: Rust harnesses instead of Lean
  # guards, and the same fix — an enumerator that RATCHETS so the next one cannot be added unwired.
  # ⚑ THE CHEAP ROW IS THE COVERAGE RATCHET, and it is not decoration: it globs
  # `pickles-*-harness/` off disk and reds on a directory nobody declared (the unwired-harness class
  # itself), on a declared directory that vanished, on a harness that DROPS BELOW its recorded
  # `#[test]` floor (a lost property), on zero committed fixtures, and on a fixture that exists but
  # is UNTRACKED (a green on a file HEAD does not carry proves nothing about the commit). ~1s, no
  # cargo. It is NOT a substitute for running them — that is the `--all` row below, and neither is a
  # substitute for the other.
  # ⚠ The full run is under --all because each harness is DELIBERATELY its own workspace (it pins
  # `o1-labs/proof-systems` at a tag the breadstuffs workspace patches away), so each carries its own
  # cold build of kimchi + arkworks: MEASURED 4m49s for the first, then seconds. Warm it is minutes;
  # cold on a fresh box it is ~30, which is a budget question, not an everyday one.
  # The `-red` row is not optional: the headline is a NEGATIVE assertion ("no pickles harness is
  # failing"), which passes just as happily when the runner is broken. It drives all five ratchet
  # legs on SCRATCH GIT TREES in a temp dir plus a CONTROL (an untouched copy must be green, or every
  # red is free) — and its last leg is the one that matters: it corrupts ONE public-input word in a
  # scratch copy of a committed fixture and requires `cargo test --release` to exit NON-ZERO, so what
  # is proved is that a broken Lean emit reaches a failing exit code THROUGH THE PROVER, not merely
  # that the script can print the word RED. The shared tree is never mutated.
  "pickles-harness-ratchet|120|bash scripts/pickles-harnesses.sh --static"
  "pickles-harness-ratchet-red|1800|bash scripts/pickles-harnesses.sh --self-test"
  # ⚑ THE ONE GATE THAT CAN SEE A FREE CELL. Every Pickles row above this one — the harnesses, the
  # region-conformance diffs, the byte oracles — is a SHAPE instrument. MEASURED 2026-08-03: not one
  # prover-chosen cell was visible to any of them AS SUCH, because a statement word with no in-circuit
  # source has the same ladder shape as one with a source and a free booleanity row is BYTE-IDENTICAL
  # to a derived one. Words 11/39, `vCipBit`, `branch_data`'s mask bits, `G`/`z₁`/`z₂`, the pad lane
  # and the wrap transcript's 119 supplied words were all invisible to the gate surface.
  # `KimchiStepProverChoice.lean` / `KimchiWrapProverChoice.lean` COMPUTE those counts in Lean, over
  # the actual emitted program, by `native_decide` — but `native_decide` reds when `= 19` stops
  # holding, and the next commit edits it to `= 20` and the build is green again with nineteen
  # environment cells having quietly become twenty. This row is the other source: 21 counts against
  # CEILINGS committed in the script, each with a DIRECTION (a free-cell count may fall, never rise;
  # a derived-word count may rise, never fall; a structural identity may not move). ~0.4s, node only,
  # no Lean build and no emitted artifact — it reads the census's own theorem statements, and a pin it
  # cannot READ is RED, never skipped, because a deleted census pin is how an instrument gets retired
  # without anyone deciding to.
  # The `-red` row is not optional: it raises every `max`/`eq` pin by one and lowers every `min` pin
  # by one and requires each to bite (19 + 2), renames a census theorem, and reshapes a statement —
  # against a CONTROL that the committed census must still pass, because a ratchet that reds on
  # everything proves nothing.
  "prover-freedom-ratchet|120|node bridge/mina-zkapp/scripts/prover-freedom-ratchet.mjs"
  "prover-freedom-ratchet-red|120|node bridge/mina-zkapp/scripts/prover-freedom-ratchet.mjs --self-test"
  # And the wrap conformance diff's OWN red path, which needs neither Lean nor an emission: it proves
  # the blob-fact legs bite (the Fp step circuit loaded where `wrap_main` belongs, and every `q-1`
  # coefficient shaved to `q-2`) and that `--report` EXITS NON-ZERO on divergence. Until 2026-08-03
  # `--report` exited 0 before the vector diff in both region-conformance scripts, so every GREEN from
  # that path was a formatting success. The full gate needs a fresh wrap emission and is in
  # `pickles-synthesis-oracles.sh` — which is now REACHED, by the `pickles-synthesis-oracles` row in
  # `GATES_ALL`. ⚠ Until 2026-08-03 it was reached by NOTHING: not a row here, not a job in
  # `.github/workflows/ci.yml`, and these two comments were the only mentions of it in the tree. A
  # delegation to a script nobody runs is the same fail-open as running only the `-red` path.
  "wrapmain-conformance-red|180|node bridge/mina-zkapp/scripts/wrapmain-region-conformance.mjs --self-test"
  # ⚑ TWO INSTRUMENTS THAT WERE IN NO SCRIPT AT ALL until 2026-08-03, and both were self-certifying.
  # `stepmain-shape-diff.mjs` printed two tables and exited 0 — no comparison, no failure counter —
  # and it is where HORIZONLOG:350's "all five run-length families INTACT: EndoMul 32×77 exactly
  # Mina's" came from: a human reading a printed table. `curve-gate-oracle.mjs` printed "MATCH Lean"
  # while reading o1js alone, so it was green for any Lean emitter whatsoever. Both now carry
  # verdicts, and these rows are their RED PATHS — answerable on any tree, no Lean and no emission:
  # the shape-diff grades Mina's own gate list against itself as the honest anchor and then bends it
  # four ways; the curve oracle bends a synthetic coeff-free gate list four ways plus an EMPTY-SET
  # anchor (an oracle that is green over no rows is the shape the old file had). The full gates need
  # an emission and live in `pickles-synthesis-oracles.sh` — see the `pickles-synthesis-oracles` row
  # in `GATES_ALL`, which is what makes that sentence a pointer rather than a dead end.
  "stepmain-shape-diff-red|120|node bridge/mina-zkapp/scripts/stepmain-shape-diff.mjs --self-test"
  "curve-gate-oracle-red|180|node bridge/mina-zkapp/scripts/curve-gate-oracle.mjs --self-test"
  # ⚑ AND THE FLOOR THOSE GATES DELEGATE FRESHNESS TO, with its own red path. Its THIRD leg — "the
  # emit cone was COMMITTED at the stamped HEAD" — was recorded as `cone_dirty_at_head` from the day
  # the module existed and GATED ON NOWHERE: its only consumers interpolated it into a status line.
  # MEASURED 2026-08-03: the committed stepmain fixture's sidecar carried
  # `cone_dirty_at_head: [KimchiStepMainCore.lean]` — the module that decides the emitted gates — so
  # that session's "conformance GREEN, 31/31 byte-exact" was a grade of a working tree no commit
  # contains, and legs 1 and 2 were green because they hash THAT SAME TREE. This row proves all three
  # legs refuse (plus a stamp from outside git, plus two anchors that must still be ACCEPTED), and it
  # re-measures the one-character display bug that hid the field in plain sight: `gitContext` used to
  # `.trim()` the porcelain output and then `slice(3)`, so the first path lost its first character
  # (`etatheory/…`). No Lean, no emission, ~0.2s.
  "emit-provenance-floor-red|60|node bridge/mina-zkapp/scripts/emit-provenance.mjs --self-test"
  # A CLAIM THE CODE DOES NOT CARRY. Every row above this one checks an ARTIFACT — a
  # target, a manifest, a fence, a caller, a row. None of them reads PROSE, and prose was
  # the carrier of six separate wounds on 2026-07-30 alone, every one found by a person
  # and none by a check. The worst was `DreggFederation.advanceState`, documented "the
  # state transition was cryptographically verified" on a file with ZERO occurrences of
  # `.verify(`, `Proof<`, `ZkProgram`, `SelfProof` and `DynamicProof` — a monotonic
  # counter with a signature-free setter — beside a class doc saying `nullifierRoot`
  # "prevents double-withdrawal" over a field set to `Field(0)` at init and never read
  # again. ⚑ That doc was hiding a LIVE HOLE, not overstating a weak one.
  # ⚠ IT CATCHES TWO OF THE SIX AND SAYS SO IN ITS OWN HEADER. The other four need a
  # reader, and the `-historical` row below is what keeps that number a MEASUREMENT: it
  # replays all six from git as they were BEFORE repair and FAILS if the score and the
  # design disagree — so narrowing a rule to go green somewhere else reds here.
  # ⚠ AND IT IS TUNED AGAINST CRYING WOLF, which is the failure mode that kills an
  # instrument like this. Scoped to a declaration's body R1 reported 34 honest sites;
  # file-scoped it reports zero. "blocks"/"stops" are not protective verbs here because
  # "block" is a noun on nearly every line of this tree that contains it. A NEGATED claim
  # is a disclaimer and a QUOTED one is a report, and both were caught firing by the
  # self-test. The contradicting-comments rule (specimen 3) was prototyped, MEASURED at
  # 1,589,852 pairs, and REJECTED — `--contradiction-probe` keeps it runnable so the
  # verdict stays checkable.
  # ~25s, no cargo, no node, no Lean toolchain. The `-red` row is not optional: the
  # headline is a NEGATIVE assertion and it drives four disease shapes, four honest
  # shapes that must stay quiet, R3 against synthetic import graphs, the allowlist's own
  # discipline, and six blindness FLOORS — including `Lean import edges`, which exists
  # because a 64 KB header slice silently zeroed R3's whole harvest during development
  # and the run still printed OK.
  # ⚑ EXECUTED, NOT GREPPED. Loads the real published verify-badge.js into a DOM +
  # fetch harness and plays the hostile host (forged bytes + a page-named node that
  # commits them). The `-red` row reinstates the defect in an in-memory copy and FAILS
  # if the gate stays green — the tree is never mutated.
  "verdict-provenance|120|node scripts/check-verdict-provenance.mjs"
  "verdict-provenance-red|120|node scripts/check-verdict-provenance.mjs --self-test"
  "prose-claims|300|python3 scripts/check-prose-claims.py"
  "prose-claims-red|180|python3 scripts/check-prose-claims.py --self-test"
  "prose-claims-historical|180|python3 scripts/check-prose-claims.py --historical"
  # ⚑⚑ THIS ROW IS RED AT LANDING, AND THE RED IS THE POINT. Measured 2026-08-10 against HEAD
  # materialised out of the object store: **7 of 7 `vk_pin`s served by this tree name a program NO
  # descriptor in this tree has.** Not one resolves. Every recursion bind in the Mina light-client
  # chain — link's absorb and body-chain seams, verify's chainlink/link/conjunction binds, and both
  # accumulator heads — attests a fingerprint nothing here produces. Fixing the seven VALUES is a
  # re-emit + VK rotation owned by the lanes currently holding `circuit/descriptors/` open; this row
  # is not waiting for them, because a documented wound is not a detected one and a gate held back
  # until its finding is repaired is the failure mode, not the courtesy.
  # ⚑ WHY IT CATCHES WHAT THE PER-PIN GATES CANNOT. A `vk_pin` is nine `Faithful9` lanes of the
  # bound program's semantic fingerprint — `blake3::derive_key` over the canonical descriptor
  # encoding — so an AIR author reads it off a Rust tool and TYPES IT INTO LEAN. Every existing gate
  # for that is hand-written for ONE pin and carries its own target name and its own copy of
  # `key_lanes9` (six such copies in the tree). A pin added after its gate was written is ungated by
  # construction, and nothing had ever asked the question of the whole tree. This asks it with NO
  # pin-to-target map: fingerprint every served descriptor, then resolve every served pin BY SEARCH
  # through that table. There is nothing in it to keep in sync and no pin it can miss.
  # ⚠ IT SAYS "SOME descriptor", NOT "the INTENDED one" — a pin resolving to the wrong descriptor is
  # a semantic error this cannot see, so the per-pin gates above stay load-bearing. Its companion
  # `distinct_descriptors_do_not_share_pin_lanes` is what makes "resolves" mean *identifies*;
  # without injectivity the headline would not be the claim it reads as.
  # ⚑ AND IT CARRIES THE REFUTATION OF A FALSE COST ESTIMATE.
  # `a_trailing_newline_does_not_move_a_descriptors_fingerprint` proves over all 158 served
  # descriptors, both directions, that the fingerprint is invariant under trailing whitespace —
  # because it is taken over the PARSED descriptor and never sees file bytes. That refutes
  # `emit_descriptors.py`'s `BY_NAME_NEWLINE_TERMINATED` frozenset, whose stated reason for existing
  # is that normalising "would re-key those 5 descriptors". It cannot: normalising is a PROVENANCE
  # re-stamp, no VK rotation, no consumer re-emit. That frozenset is the only thing reconciling
  # `MinaChainEmit.lean:48` (appends "\n") with `EmitByName.lean:788` (does not) — two emitters, two
  # byte streams, one object — and determinism restored by a hand-maintained lookup of 30 filenames
  # is not determinism.
  # ~3s, no Lean, no node; reads `circuit/descriptors/` and compiles no circuit. Point it at a rev
  # with `DREGG_DESCRIPTOR_ROOT=$(scripts/materialise-descriptors-at.sh HEAD)` — in a shared working
  # tree an uncommitted sibling re-emit otherwise flatters the verdict, and this tree has a recorded
  # case of exactly that reading outliving the tree it was measured on.
  "vk-pin-closure|300|cargo test -p dregg-circuit --test vk_pin_closure_over_the_served_tree"
  # ⚑⚑ THE OTHER HALF OF THE ROW ABOVE — the LITERAL side, which until 2026-08-11 was gated by
  # NOTHING while reading as gated. `vk_pin_closure_over_the_served_tree`'s header cited
  # `descriptor_pin_literals_are_not_transcriptions.rs` as covering the Lean literals, and that
  # citation was the file's ONLY occurrence in the tree. The two ask genuinely different questions
  # and this one is GREEN while that one is red, which is the argument for both existing:
  #   this row : the Lean `vkPin`/`descLanes` literal EQUALS some emitted pin (+ a seam end's
  #              literal is served under the descriptor name Lean pairs it with — INTENT, which the
  #              closure gate says outright it cannot see), and the three `FORGED_*` falsifier
  #              literals match NOTHING served (the red arm; a forged constant that drifts onto a
  #              real pin has stopped falsifying).
  #   above    : that emitted pin is the FINGERPRINT of a descriptor this tree serves.
  # A stale Lean literal is invisible above unless the descriptor was ALSO re-emitted — that proviso
  # is in the closure gate's own header and is the hole this closes.
  # ~3s, no Lean toolchain, no circuit compiled: it reads `metatheory/**.lean` as text and
  # `circuit/descriptors/`. `DREGG_METATHEORY_DIR` / `DREGG_DESCRIPTOR_ROOT` retarget either side.
  "vk-pin-literals|300|cargo test -p dregg-circuit --test descriptor_pin_literals_are_not_transcriptions"
  # ⚑⚑ THE TRANSCRIPTION ARMS OF THE BLAKE3 DIFFERENTIAL — the answer to the row above.
  # `vk-pin-closure` is red because a `vk_pin` is a derived value a human TYPES IN: nine `Faithful9`
  # lanes of `blake3::derive_key` over a descriptor's canonical encoding, obtained from a Rust tool
  # and written into a Lean file. `Dregg2.Crypto.Blake3Compute.blake3Derive` is that hash in pure
  # Lean, so the value can be COMPUTED where it is used instead of copied to where it is needed.
  # ⚠ THE DANGER OF THAT MOVE IS THAT A WRONG `blake3Derive` FAILS SILENTLY — every pin it computes
  # would be self-consistent and wrong, which is "two agreeing transcriptions are not two witnesses;
  # they are one witness copied", generated at scale. So the differential is a STANDING gate, four
  # arms, and this row is the two that cost nothing: the two derive-key CONTEXT STRINGS read out of
  # `circuit/src/{descriptor_ir2_canonical,air_descriptor}.rs` and compared against the Lean
  # constants (derive-key folds the context into the KEY, so one character moves every fingerprint
  # and nothing else would notice), and the 35 official BLAKE3 vectors transcribed into
  # `Blake3Kat.lean` re-derived from the BLAKE3 team's own committed `test_vectors.json`. Both are
  # things a human typed; both are therefore what rots. ~0.1s, no Lean, no cargo.
  # ⚑ ARM 3 NEEDS NO ROW: `Dregg2.Crypto.Blake3Kat` is rooted in `Dregg2.lean`, so its 35-vector ×
  # 3-mode theorems (`native_decide` + `#assert_compiled`) and its falsifiers run in every
  # `lake build`. ARM 4 — 158 served descriptors, both sides recomputed — is under --all below.
  "blake3-transcription|120|bash scripts/check-blake3-differential.sh --fast"
  # ⚑⚑ THE CHEAP ARM OF THE CANONICAL-ENCODER DIFFERENTIAL — the hop the row above could not reach.
  # `blake3-differential` gates `canonical bytes -> fingerprint -> lanes`; it is HANDED the canonical
  # bytes, because `canonical_effect_vm_descriptor2_bytes` was Rust-only, so a Lean
  # `EffectVmDescriptor2` term could not be fingerprinted at all and fourteen `*_VK_LANES` literals
  # stayed transcribed digits. `Dregg2.Circuit.DescriptorCanonical.canonicalBytes` is that encoder in
  # Lean. ⚠ IT IS NOT `emitVmJson2`: that renders the JSON build artifact (10 229 bytes for
  # `accumulator-nonrev`), this renders the fixed binary record the fingerprint is taken over (2 646
  # bytes, opening "DREGGIR2"). This row is the constants a human typed and that therefore rot — the
  # magic, the SCHEMA VERSION, the allocation bound, the BabyBear prime and the vacuous-range width,
  # each read out of the Rust source and compared with the Lean. A version bump on one side alone
  # rotates EVERY fingerprint and refuses every old record, and nothing else would notice. ~0.2s, no
  # Lean, no cargo. The named theorems ride `lake build` (both modules are rooted in `Dregg2.lean`);
  # the 159-descriptor arm is under --all below.
  "canonical-encoder-constants|120|bash scripts/check-descriptor-canonical-differential.sh --fast"
  # ⚑ FROZEN ARTIFACTS THAT STOPPED MATCHING THE LEAN THAT JUDGES THEM (2026-10-01). Eight weeks of
  # red that no row here could see: `finality_gate`'s verified-gate tests (and the attacker tooth,
  # VACUOUS) from `d182d10fc` 08-08; `poa_signal_genesis` under a genesis tuple frozen at counter 2
  # while the signed bundle moved to 12; `poa_galley_genesis` red from its birth commit; and
  # `linked_archive_freshness` red on every Linux box (deterministic `ar`, no stamps). Each was a
  # test that only ever ran on a lane someone happened to arm. These rows arm them.
  # `lean-hard-mode` is CARGO: two FILTERED nextest invocations (never a `-p` suite) under
  # DREGG_REQUIRE_LEAN=1 DREGG_TEST_REQUIRE_LEAN=1, wrapped in `swarm-build` when present, with
  # per-module floors + named anchors so a filter that matches nothing is red. Warm target: the
  # test-binary link + the Lean init per test process; a cold build or a Lean archive rebuild can
  # exceed the budget, which reports TIMEOUT (not a verdict) — that is the honest answer.
  "lean-hard-mode|3600|python3 scripts/check-lean-hard-mode.py"
  "lean-hard-mode-red|60|python3 scripts/check-lean-hard-mode.py --self-test"
  # The frozen network-genesis fixtures ARE Lean's render of `NetworkGenesis.fixtureInput`
  # (`NetworkGenesisFixtureEmitMain.lean`, `lake env lean --run`; needs the NetworkGenesisFixtures
  # olean, BLOCKED otherwise). `-red` plants a one-byte edit in each of the four files in a scratch
  # copy: all four must refuse by name, the untouched copy must pass.
  "poa-genesis-fixture|900|bash scripts/check-poa-genesis-fixture.sh"
  "poa-genesis-fixture-red|1800|bash scripts/check-poa-genesis-fixture.sh --self-test"
  # The Galley activated-content artifacts (`poa/artifacts/galley/epoch-1/`) re-derive from the
  # deployment manifest and the runtime source. Its only caller was `test-poa.sh` via a disabled
  # workflow, and they sat drifted (rules_digest) from 08-09. ~0.1s, no Lean, no cargo.
  "poa-galley-content|60|python3 scripts/poa-galley-content.py check"
  "poa-galley-content-red|60|python3 scripts/poa-galley-content.py self-test"
)
# Expensive — only under --all, each with the reason it is not in the cheap set.
GATES_ALL=(
  # ⚑⚑ THE DEPLOYED-INPUT ARM OF THE BLAKE3 DIFFERENTIAL, and it covers the WHOLE `vk_pin`
  # computation — `canonical bytes → BLAKE3 derive-key fingerprint → nine base-2^29 lanes` — over
  # EVERY DescriptorIR-v2 record this tree serves: 158 at landing, 17,990,701 canonical bytes, ALL
  # of them and not a sample. HOP 1 is pure-Lean `blake3Derive` against the `blake3` crate's
  # `new_derive_key`. HOP 2 is `Dregg2.Circuit.KeyLanes9.keyToLanes9` — the LEAN-AUTHORED encoder
  # the AIRs are proved against — versus Rust `key_limbs9`, on those same 158 fingerprints. Hop 2 is
  # NOT implied by hop 1: equal digests say nothing about two lane encoders agreeing, and six files
  # in this tree each carried their own copy of that packing on the assumption that they did.
  # Both sides are recomputed on every run (`cargo run -p dregg-circuit --example
  # descriptor_canonical_dump` re-encodes and re-hashes what is on disk; the Lean driver re-derives
  # from the same bytes). NOTHING here is a committed fixture, deliberately: a stored expectation is
  # the exact defect the pass exists to kill. Measured 2026-08-10 at landing: PASS on all 158, both
  # hops.
  # ⚠ WHY NOT THE CHEAP SET — ~1 min of interpreted Lean plus a cargo example build, and it needs
  # `lake build`, which no cheap row does. The cheap half is `blake3-transcription` above and the
  # 35 official vectors ride the ordinary Lean build; what is deferred here is the DEPLOYED-INPUT
  # question, not the correctness question.
  "blake3-differential|1500|bash scripts/check-blake3-differential.sh"
  # The -red row, ONE MUTATION PER HOP: row 0's fingerprint and row 1's first lane, in an in-memory
  # copy of the fresh dump. It FAILS if the differential stays green, it asserts each mutation
  # LANDED before reading any verdict (a mutation that quietly became a no-op is how an adversary
  # dies while its gate stays green), and it requires BOTH hop failures to be NAMED in the log — a
  # red that only reported hop 1 would leave the lane encoder unfalsified, and a refusal rendering
  # as the expected verdict is its own defect class. The tree is never mutated.
  "blake3-differential-red|1500|bash scripts/check-blake3-differential.sh --self-test"
  # ⚑⚑ THE DEPLOYED-INPUT ARM OF THE CANONICAL-ENCODER DIFFERENTIAL, over EVERY DescriptorIR-v2
  # record this tree serves: 159 at landing, 18,010,889 canonical bytes, byte for byte. ⚑ BOTH SIDES
  # COMPUTE FROM THE SAME INPUT — the descriptor JSON on disk. Rust parses and encodes it; Lean
  # parses it (`DescriptorCanonicalJson.parseDescriptor`) and encodes it
  # (`DescriptorCanonical.canonicalBytes`). Nothing is stored, so a sibling lane's uncommitted
  # re-emit moves both sides identically and cannot flatter the result. The fingerprint and the nine
  # lanes are then recomputed FROM THE LEAN BYTES, so the composite claim — a Lean descriptor TERM
  # produces the nine `vk_pin` digits the deployed tool prints — is checked end to end rather than
  # inferred from two half-results. A fourth arm censuses two deliberately WRONG encoders
  # (`EncoderVariant`): each must AGREE with the truth on most of the corpus and DIVERGE on at least
  # one descriptor, because a falsifier that diverges nowhere has become a no-op and one that agrees
  # nowhere is a different encoder rather than a probe. Measured at landing: 155/4 and 156/3.
  # ⚠ WHY NOT THE CHEAP SET — ~2.5 min of interpreted Lean over 57.8 MB of JSON, plus a cargo
  # example build and a `lake build`.
  "canonical-encoder-differential|1800|bash scripts/check-descriptor-canonical-differential.sh"
  # The -red row, THREE mutations because the gate has three ways to be hollow: a corrupted
  # canonical record must turn the ENCODER comparison red, a corrupted fingerprint must turn the
  # HASH comparison red, and a corpus with the chal_gate / ported-proof_bind carriers REMOVED must
  # turn the FALSIFIER CENSUS red. Each is built constructively and asserted to have landed before
  # any verdict is read, and each required failure must be NAMED in the log. The tree is never
  # mutated.
  "canonical-encoder-differential-red|1800|bash scripts/check-descriptor-canonical-differential.sh --self-test"
  # ⚑ THE PAYOFF ROW, and it is the row `vk-pin-closure` could not be: every `*_VK_LANES` literal in
  # the tree, resolved against the served corpus with the WHOLE chain recomputed IN LEAN
  # (`descriptor JSON -> canonical bytes -> derive-key -> nine lanes`), no Rust in the path. It
  # resolves BY VALUE — there is no literal-to-file map anywhere, because a stale map is invisible in
  # exactly the way the literals are. HARD failures: a literal that is not nine non-negative lanes,
  # and a deliberate FORGED_* falsifier that MATCHES a served descriptor (a forged pin naming a real
  # program is a falsifier that stopped falsifying). Measured at landing: 14 literals, 3 forged and
  # all three correctly matching nothing, 8 live literals naming no served program.
  # ⚠ It does NOT adjudicate those 8: which literal is wrong versus which descriptor moved is a
  # question about THIS tree and not a fact, and `vk_pin_closure_over_the_served_tree` already
  # carries that verdict — a second copy would be a twin, not a second witness. `--strict` exits 1.
  "vk-pin-literal-resolution|1800|bash scripts/check-vk-pin-literals.sh"
  # ⚑ THE ONLY GO MODULE IN THE REPOSITORY, AND UNTIL 2026-08-08 IT WAS IN NO WORKFLOW AND NO
  # RUNNER. `chain/gnark` holds the BN254 settlement wrap: the Lean-emitted R1CS templates under
  # `chain/gnark/emitted/`, the apex-VK governance pin the `SettlementCircuit` bakes, and the
  # replay drivers that run those emissions against the real apex-shrink proof fixture. Measured by
  # grep across `.github/workflows/`: no `go`, no `gnark`, no `chain/`. When the fixture was
  # re-minted at `94fc8e161` the emitted twin went stale and EIGHT tests went red — a red nothing
  # in the tree could report. `ci.yml`'s `gnark` job is the CI half; this is the local one, and
  # LOCAL is the stricter bar here.
  # ⚠ It is a differential over committed artifacts and CANNOT see staleness on its own. The
  # freshness instrument is `derive_deployed_apex_vk_identity_and_check_fixture` (route
  # `armed-dark`), which folds a fresh apex at HEAD; see the header of ci.yml's `gnark` job.
  # ⚠ `-timeout 70m` IS LOAD-BEARING. Go's default is 10m for the WHOLE binary and it PANICS rather
  # than failing, so a slow test kills the run with a goroutine dump and no verdict for anything
  # unfinished. MEASURED 2026-08-08 after the apex-shrink shape moved (FRI rounds 15 → 16, log-height
  # 18 → 19): `TestEmittedVerifierFullTranscriptLinkIsLoadBearing` took 9m21s and tripped it, and
  # everything that had already run had PASSED. Do not read that shape of red as the code.
  "gnark|5400|bash -c 'cd chain/gnark && go vet ./... && go test -timeout 70m ./...'"
  # THE COMPILE-FAIL RATCHET ITSELF, over the real tree. Expensive for one reason: it is a
  # whole-workspace `cargo clippy --all-targets --keep-going` (226 members). Its cheap half
  # — the self-test — is in the default set above and is the part that proves the gate can
  # go red. This is the part that says whether the tree IS dark right now.
  "dark-targets|5400|python3 scripts/check-dark-targets.py --sweep"
  "gates-executed|2400|python3 scripts/check-gates-executed.py"
  "lean-marshal|1200|bash scripts/check-lean-marshal.sh"
  "ci-invariants-falsifiers|14400|bash scripts/ci-invariants.sh falsifiers"
  # TIER 1 — one representative instance per family, COMPILED AND PROVED. This is the
  # pre-merge run and the one to reach for after touching a circuit: it restores what a
  # tier-0 green cannot imply, at one family member each rather than all of them.
  "mina-attestation-t1|3600|bash scripts/check-mina-attestation.sh --tier 1"
  # TIER 2 — the old headline. Every family member, the full chains, the ceiling.
  "mina-attestation-t2|7200|bash scripts/check-mina-attestation.sh --tier 2"
  # The injection suite. It holds 14 faults a permanent control now covers (their
  # patterns are still checked, every pass, by tier 0's pre-flight); `SELFTEST_ALL=1`
  # re-runs those too. ⚑ This is the row that was 4 HOURS of budget in the cheap set.
  "mina-attestation-red|14400|bash scripts/check-mina-attestation.sh --self-test"
  # THE PICKLES HARNESSES, RUN. `cargo test --release` per crate: every accept, every tamper-reject
  # and every non-vacuity control actually proved by `proof-systems` 0.3.0 against the committed
  # Lean-emitted fixtures. It also floors the reported pass COUNT per harness, because a `cargo test`
  # that exits 0 having compiled nothing is exactly the green this whole file refuses.
  # ⚠ Each crate cold-builds kimchi + arkworks into its OWN target/ (they are separate workspaces by
  # design — they pin a proof-systems tag the breadstuffs workspace patches away). MEASURED 4m49s
  # cold for the first; warm, the whole set is minutes. The cheap coverage ratchet is in the everyday
  # table above and reds if a harness is added, deleted or loses a property; THIS row is what makes
  # the properties themselves checkable.
  "pickles-harnesses|5400|bash scripts/pickles-harnesses.sh"
  # A verification key DERIVED from Lean-emitted wrap gates, REGISTERED on an account by Mina's own
  # OCaml transaction logic (js_of_ocaml, in-process — nothing is submitted to any network). Expensive
  # because it re-derives the keys from the Lean emission every run rather than trusting a fixture:
  # `cargo run --release` on pickles-vk-derive, then o1js LocalBlockchain.
  # ⚑ ONE row, and it is the `--self-test` one on purpose: that flag runs the whole green path AND
  # then proves the gate goes RED on a bent key and on absent input. The green-only invocation is a
  # strict subset, so a second row would add budget and no coverage.
  "foreign-vk-registration|2400|bash scripts/foreign-vk-registration-gate.sh --self-test"
  # ⚑ THE REAL CONFORMANCE GRADES, and until 2026-08-03 NOTHING RAN THEM. The everyday table above
  # carries `wrapmain-conformance-red`, `stepmain-shape-diff-red` and `curve-gate-oracle-red` — the
  # `--self-test` halves — and its own comments delegate "the full gate" to
  # `scripts/pickles-synthesis-oracles.sh`. MEASURED: `grep -rn pickles-synthesis-oracles scripts/
  # .github/` returned that script and those two COMMENTS, and nothing else. The script exists, is
  # green-or-bust, runs eleven real diffs (`wrapmain-region-conformance` bare,
  # `stepmain-region-conformance --falsify --stale-self-test`, `stepmain-shape-diff` bare,
  # `curve-gate-oracle` bare, `prover-freedom-ratchet` bare, the three .ts statement oracles and the
  # cross-implementation differential) — and was reachable from no runner and no CI job. A `-red`
  # row proves an instrument CAN go red; it says nothing about the tree. This row is the other half.
  # ⚠ WHY `--all` AND NOT THE CHEAP SET, and neither reason is budget alone:
  #   * it needs o1-labs' circuit blobs, resolved from `$MINA_CIRCUIT_BLOBS_BASE_DIR`,
  #     `~/.mina/circuit-blobs` or `/usr/local/lib/mina/circuit-blobs` and otherwise FETCHED — a
  #     network dependency the everyday table does not have;
  #   * the wrap half needs a `DREGG_WM=wrap` emission at the top rung and REFUSES (exit 3) without
  #     one rather than skipping — which is exactly why it is worth running, and also why it cannot
  #     be a row people hit on every commit;
  #   * the .ts oracles need `bridge/mina-zkapp` `npm ci`, and the cross-impl differential cold-builds
  #     kimchi + arkworks unless `PICKLES_XI_RUST_VECTORS` points at pre-made vectors.
  # It is invoked WITHOUT `--no-ts`/`--no-xi` on purpose: a missing ts-node prints `RED` and exits
  # non-zero, and narrowing the invocation here would re-create the delegation this row closes.
  "pickles-synthesis-oracles|14400|bash scripts/pickles-synthesis-oracles.sh"
  # ⚑ THE WRAP CENSUS ITSELF — the ratchet, not its red-path proof (that row is in the everyday table
  # above and needs nothing). MEASURED 2026-08-04 over all fourteen rungs at the committed wrap shape:
  # 12 550 of Mina's 15 122 gates = 83.0%, with EndoMul 2528/2528, VarBaseMul 2417/2417 and
  # CompleteAdd 492/492 at parity, and PI 24 of the 24 statement words `wrap_main` actually pins.
  # RATCHET: per gate type and per `typ x length` family, |ours - mina| may SHRINK, never GROW; a new
  # divergent family reds; and a shrink that the baseline does not record reds too, which is what makes
  # the census MONOTONE rather than merely non-increasing. `--update-baseline` REFUSES on growth or on
  # a new family unless `--accept-growth` is passed, so the reflex after a red is the safe path.
  # ⚠ HERE AND NOT ABOVE for one reason: it needs a `DREGG_WM=wrap` emission of all fourteen rungs
  # (hours of Lean; `w11_bullet`'s placement alone measured 2109 s) and REFUSES — exit 3, BLOCKED —
  # without one, rather than skipping or grading a nine-rung assembly as though it were the circuit.
  # It also refuses an emission whose provenance stamp does not match the source cone as the tree
  # stands right now, so it cannot grade a file nobody emitted. ~3s when the emission is present.
  "wrapmain-shape-diff|300|node bridge/mina-zkapp/scripts/wrapmain-shape-diff.mjs"
  # THE MUTATION DIFFERENTIAL ITSELF, at its RECORDED constants — the everyday table above carries
  # only the `--self-test`, which proves the instrument can go red and says nothing about the tree.
  # This is the other half: seed 20260731, 3000 trials, floor 1.0, EXPECTED_FREE=commit_pow_witness,
  # the exact parameters the 2026-07-31 observation was taken at (agreement 100.000%, 0 forgeries,
  # 0 completeness gaps, free lanes only in `commit_pow_witness`). Changing any of them is a
  # deliberate act and the script says so in its own header.
  # ⚠ HERE AND NOT ABOVE for two reasons, and budget is the smaller one: it cargo-builds
  # `root_fri_mutation` in RELEASE when the binary is absent, and 3000 trials each run the DEPLOYED
  # `TwoAdicFriPcs::verify` over a re-decoded proof (~2 s/trial measured at 12 and 40 trials, warm).
  # It exits 3 — BLOCKED, not FAIL — when the oracle cannot be built or `.fullchain/real-root-*.json`
  # is not on the box, rather than skipping or grading a shorter run as though it were the control.
  "fri-mutation|14400|bash bridge/mina-zkapp/scripts/fri-mutation-gate.sh"
  # ⚑ DOES **HEAD** BUILD FOR SOMEBODY WHO JUST CLONED — and the instrument that answers it was, as
  # of 2026-08-06, referenced by NOTHING: not this table, not a workflow, not a doc. Its own header
  # records `main` breaking at HEAD three times in one morning with a working-tree `cargo check`
  # reporting exit 0 each time, because in a shared-tree swarm the working tree is the UNION of every
  # lane's in-flight work and is therefore systematically GREENER than HEAD.
  # ⚑ IT WENT RED THE FIRST TIME IT WAS RUN HERE, which is its red-proof and a measured one: six
  # targets across four crates, all downstream of the 2026-08-05 `dregg-verifier` carve that deleted
  # `verify_effect_vm_proof`/`replay_chain`/`ReplayVerdict` while their consumers stayed. Four were
  # landed by a sibling mid-flight; the other two (`proof_bind_seam_bites`, `wide_completeness_ledger`)
  # had not compiled in HEAD OR in any working tree and are repaired in `c3b18ac42`.
  # ⚠ AND IT NOW HAS A NON-VACUITY FLOOR. `cargo check` exits 0 printing `Finished` when everything is
  # already fresh, so an inherited `CARGO_TARGET_DIR` would have turned the whole gate into a no-op
  # that reads exactly like a pass. It refuses a run that compiled fewer units than half the workspace
  # member count — derived from `cargo metadata`, not typed in.
  # ⚠ HERE AND NOT ABOVE only for cost: a fresh `--shared` clone plus a cold whole-workspace
  # `cargo check --all-targets --keep-going` over 226 members. ~20 min measured, longer under load.
  # `HEADBUILD_KEEP_LOG=/path` preserves the full rustc output, which a red always wants.
  "head-builds|7200|bash scripts/check-head-builds.sh HEAD"
)

want() { [ ${#WANT[@]} -eq 0 ] && return 0; printf '%s\n' "${WANT[@]}" | grep -qx "$1"; }

# ── SCOPE ─ THE RUNNER'S OWN. Every gate below now prints its own ANSWERS / DOES NOT ANSWER
# pair as its first two lines of output, because the nine instrument-defects of 2026-08-01..07
# were every one of them a check that was CORRECT and MISREAD — and the misreads happened to
# people reading RESULTS, not source. This block is the same statement for the TABLE.
# ⚠ It is printed twice on purpose (here and in the summary): a reader who scrolls to the
# bottom for `passed N · failed M` is exactly the reader who was misled.
SCOPE_ANSWERS='would each named gate, RUN HERE, on THIS checkout, right now, reach exit 0?'
SCOPE_DENIES='whether the repo is correct, whether CI is green, or whether the gates COVER anything. Each row is as narrow as its own scope line says; a full-green table is the conjunction of ~110 narrow questions and nothing wider. Rows under --all are NOT run by default and are printed SKIP, never counted as passing.'
printf 'ANSWERS:         %s\nDOES NOT ANSWER: %s\n\n' "$SCOPE_ANSWERS" "$SCOPE_DENIES"

printf '%-28s %-6s %-8s %s\n' GATE RESULT TIME NOTE
printf '%.0s─' {1..96}; echo

pass=0; fail=0; skip=0; timedout=0; blocked=0; unprobed=0; failed=()
run_one() {
  IFS='|' read -r name to cmd <<< "$1"
  want "$name" || return 0
  # ── A gate whose script is missing is a FINDING, not a skip: something references it. ──────────
  #
  # ⚠ IT USED TO TAKE "THE SECOND WORD" AS THE SCRIPT, AND TWO ROWS COULD THEREFORE NEVER RUN.
  # `bash -c 'cd bridge/mina-zkapp && npm run --silent vk-identity'` has `-c` in that position, so
  # `[ ! -f "-c" ]` was true and BOTH `mina-vk-identity` rows printed MISSING and returned WITHOUT
  # INVOKING ANYTHING — a gate reporting a permanent red for a file that was never its script, while
  # the check it names (the VK-notion identity gate, and its own red-proof) had not executed once.
  # The inverse of this table's usual disease: not a gate that cannot fail, a gate that cannot PASS,
  # and a red nobody can act on gets skipped by readers exactly as fast as a green nobody checks.
  # Measured 2026-08-06: 2 of 109 rows.
  #
  # So the probe now IDENTIFIES the script — every token that looks like a repo-relative script path
  # — instead of guessing by position. And where a row invokes NO identifiable script (an npm run, an
  # inline shell), it says so in the summary rather than inventing a verdict: a pre-flight that
  # cannot speak for a row must not be counted as having cleared it.
  local tok scripts=() missing=()
  for tok in $cmd; do
    tok="${tok#\'}"; tok="${tok%\'}"
    case "$tok" in
      */*.sh|*/*.py|*/*.mjs|*/*.js|*/*.ts)
        scripts+=("$tok"); [ -f "$tok" ] || missing+=("$tok") ;;
    esac
  done
  if [ "${#missing[@]}" -gt 0 ]; then
    printf '%-28s \033[31m%-6s\033[0m %-8s %s\n' "$name" MISSING "-" "${missing[*]} does not exist"
    fail=$((fail+1)); failed+=("$name"); return 0
  fi
  [ "${#scripts[@]}" -eq 0 ] && unprobed=$((unprobed+1))
  local s e rc out
  s=$(date +%s); out="$(timeout "$to" bash -c "$cmd" 2>&1)"; rc=$?; e=$(date +%s)
  local note; note="$(printf '%s' "$out" | tail -1 | cut -c1-46)"
  if [ "$rc" -eq 0 ]; then
    printf '%-28s \033[32m%-6s\033[0m %-8s %s\n' "$name" PASS "$((e-s))s" "$note"; pass=$((pass+1))
  elif [ "$rc" -eq 124 ]; then
    # ⚑ A TIMEOUT IS A FAILURE, AND ITS OWN MESSAGE SAYS WHY: "not a verdict".
    #
    # This used to increment `skip`, so a gate that could NEVER finish contributed nothing and
    # the table still ended clean. Measured: `gates-executed` timed out for an entire session
    # (528s in the morning, past its 600s budget by evening) while sitting in the cheap set
    # looking like coverage — and the summary read "1 failing" with it invisible.
    #
    # That is this repo's signature disease pointed at its own instrument: a gate that cannot go
    # red is not a gate, and a gate that cannot FINISH cannot go red. Counted as a failure now,
    # and named separately in the summary so a reader can tell "produced no verdict" from "found
    # a defect" — those want different fixes (a budget or a phase split, vs an actual repair).
    printf '%-28s \033[31m%-6s\033[0m %-8s %s\n' "$name" TIMEOUT "$((e-s))s" "exceeded ${to}s — NOT A VERDICT, counted as a failure"
    fail=$((fail+1)); failed+=("$name (timeout)"); timedout=$((timedout+1))
  elif [ "$rc" -eq 3 ]; then
    # ⚑ 3 IS NOT 1, AND IT IS NOT 0 EITHER.
    #
    # Several gates in this table already SPEAK the distinction — the pickles conformance gates and
    # the wrap census exit 3 when a PREREQUISITE is absent or stale (no emission on this box, an
    # artifact whose provenance stamp does not match the source cone) and 1 when they found a real
    # divergence. `pickles-synthesis-oracles.sh` names them apart internally; THIS runner collapsed
    # both into `FAIL`, so "there is no wrap emission on this machine" and "the Lean assembly
    # diverged from Mina's compiled circuit" arrived as the same red line. A reader cannot act on
    # that, and the predictable response to an unactionable red is to stop reading the gate.
    #
    # ⚠ AND BLOCKED IS STILL A FAILURE. A prerequisite that is absent means the gate DID NOT RUN,
    # which is not a pass — this is about making the failure ACTIONABLE, never about letting one
    # through. It counts in `fail` and the run exits non-zero exactly as before.
    printf '%-28s \033[33m%-6s\033[0m %-8s %s\n' "$name" BLOCKED "$((e-s))s" "prerequisite absent/stale — DID NOT RUN, counted as a failure"
    fail=$((fail+1)); failed+=("$name (blocked)"); blocked=$((blocked+1))
  else
    printf '%-28s \033[31m%-6s\033[0m %-8s %s\n' "$name" "FAIL" "$((e-s))s" "$note"
    fail=$((fail+1)); failed+=("$name")
  fi
}

for g in "${GATES[@]}"; do run_one "$g"; done
if [ "$RUN_ALL" -eq 1 ]; then
  for g in "${GATES_ALL[@]}"; do run_one "$g"; done
else
  for g in "${GATES_ALL[@]}"; do
    IFS='|' read -r name _ _ <<< "$g"; want "$name" || continue
    printf '%-28s \033[90m%-6s\033[0m %-8s %s\n' "$name" SKIP "-" "needs --all"; skip=$((skip+1))
  done
fi

echo
printf 'ANSWERS:         %s\nDOES NOT ANSWER: %s\n' "$SCOPE_ANSWERS" "$SCOPE_DENIES"
echo "passed $pass · failed $fail · skipped $skip"
[ "$timedout" -gt 0 ] && echo "  ⚠ $timedout failure(s) produced NO VERDICT (timeout) — that wants a budget or a phase split, not a repair"
[ "$blocked" -gt 0 ] && echo "  ⚠ $blocked failure(s) are BLOCKED (exit 3) — an INPUT is absent or stale, not a divergence. Produce the input; do not 'fix' the gate"
[ "$unprobed" -gt 0 ] && echo "  · $unprobed row(s) invoke no identifiable script path (npm run / inline shell), so the missing-script pre-flight could not speak for them — they RAN and their verdict above is their own"
[ ${#failed[@]} -gt 0 ] && printf 'failing: %s\n' "${failed[*]}"

# ── WHAT THIS DELIBERATELY DOES NOT RUN, and why ───────────────────────────────
cat <<'EOF'

NOT run here, deliberately — each is a real gate, none of them is covered by the above:
  * scripts/axiom-hygiene-guard.sh   whole Dregg2 Lean corpus. A hosted runner was KILLED at
                                     ~56 min (exit 143); it plausibly only ever failed for being
                                     on the wrong machine. Run it locally where .lake is warm.
  * scripts/bare-clone-repro-gate.sh clones + builds from scratch; minutes-to-an-hour of its own.
  * cargo test --workspace           the broadest signal there is. Run it separately, and note
                                     `--no-fail-fast` or the first failure abandons the remaining
                                     test targets and you measure less than you think.
                                     ON LINUX IT IS TWO INVOCATIONS, and the second is not
                                     optional — it is what keeps the first from costing 9 tests:
                                       CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0 \
                                       cargo test --workspace --exclude deos-zed \
                                         --exclude grain-verify-wasm --exclude starbridge-web \
                                         --no-fail-fast -- --test-threads=4
                                       cargo test -p grain-verify-wasm -p starbridge-web --lib
                                     THE debuginfo-OFF PAIR IS NOT COSMETIC. Measured on
                                     persvati 2026-07-26 with the repo default
                                     (`[profile.dev] debug = "line-tables-only"`): this run
                                     grew one lane's target/ to 311 GB and died at
                                     `rustc-LLVM ERROR: IO failure on output stream: No space
                                     left on device` with ~250 GB free when it started. ci.yml
                                     sets both vars for exactly this reason; a local run that
                                     omits them measures an ENOSPC, not the tree.
                                     Those two crates declare `crate-type = ["cdylib","rlib"]`
                                     and reach the Lean archive, and a `-shared` ELF link of
                                     libleanrt's local-exec-TLS mimalloc is rejected outright
                                     (R_X86_64_TPOFF32). `--lib` builds the lib with `--test`,
                                     i.e. an executable, so their tests still run. See the block
                                     above `members` in Cargo.toml.
  * ci-invariants falsifiers         38 rows x ~7 min, each a separate `cargo test -p <crate>`
                                     link. It holds the ONE cargo target lock for ~4 h and blinds
                                     every other lane on the box. Offload it:
                                       scripts/pbuild <warm-lane> bash scripts/ci-invariants.sh falsifiers
EOF
[ "$fail" -eq 0 ]
