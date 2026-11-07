//! **LAW #1 RATCHET** — the systematic enforcement of "zero Rust-authored constraints or AIRs, ever".
//!
//! `metatheory/README.md:15` states architectural law #1: *"Circuits are **emitted from Lean**... Rust only
//! INTERPRETS those artifacts. A coverage gap is closed by emitting from a new proved module, **never** by
//! hand-authoring a constraint."* Until this gate existed the law lived only in PROSE — and prose does not
//! fail a build.
//!
//! ## What this gate looks at (2026-07-25 rewrite — read this before trusting a number)
//!
//! The previous revision of this file was **blind in two directions at once**, and the two blindnesses
//! compounded: it scanned only `circuit/src` + `circuit-prove/src`, and within that scope it counted
//! `ConstraintExpr::` *textually*, which counts `match` PATTERNS as if they were authored algebra.
//!
//! * **Scope.** The single largest hand-written Rust AIR in the tree — `param-compose/src/air.rs` +
//!   `param-compose/src/builder.rs`, ~1000 lines, its own `Head` polynomial type, its own
//!   `assert_zero`, its own `air_accepts`, and a `tamper()` forgery harness — sat entirely OUTSIDE the
//!   scanned directories and was therefore invisible to a gate whose entire purpose is to see it. At
//!   the time of that rewrite it was live on a production path (`entity-compose/src/lib.rs` imported
//!   `dregg_param_compose::air::{ComposeAir, build}` in non-test code), both crates are workspace
//!   `default-members`, and `metatheory/` contained **no** `paramCompose` emitter. This gate now scans
//!   **every `.rs` file under any `src/` tree in the repository**, so a violation cannot hide by being
//!   in a different crate. **OUTCOME (2026-07-25): both files are DELETED.** Lean grew the route
//!   (`Dregg2/Circuit/Emit/ParamComposeEmit.lean` + `ParamComposeRefine`, all 18 corpus shapes
//!   `#guard`-pinned), the consumers and the whole test corpus moved onto the emitted descriptor, and
//!   the two `BASELINE` rows went with the files.
//! * **Counting.** `circuit/src/custom_leaf_lowering.rs` "violated" the old gate 46 times. Every one of
//!   those 46 is `ConstraintExpr::Variant { .. } =>` — a match arm in a LOWERING. Destructuring a
//!   constraint authors nothing. A gate that cries wolf 46 times gets ignored, and this one was: the
//!   previous revision, compiled and run against the tree it shipped with, **exited 101 — RED at HEAD**,
//!   its largest single "violation" being those 46 non-violations. Nobody noticed because the CI job
//!   that runs it (`cargo test --workspace`, `.github/workflows/ci.yml` Test (macos/ubuntu)) has been
//!   dying while compiling `dregg-lean-ffi`'s BUILD SCRIPT — ten `E0433`/`E0425`s against
//!   `build_parallel` — so the test binary is never linked and the gate never executes. A red gate
//!   nobody sees and a gate that does not run are the same object. So the gate now **classifies
//!   construction against destructuring** rather than grepping.
//!
//! ## The FIVE constraint dialects
//! A grep for one dialect sees a fifth of the truth. Miss one and you will miscount — that is the whole
//! point of this gate. In dependency order of how easy they are to overlook:
//!
//!   1. **plonky3 symbolic** — `x.assert_zero(..)` on ANY receiver. The previous revision hard-coded the
//!      receiver name `builder`, so `b.assert_zero(&Head::lin(..))` (param-compose's whole AIR, 19 sites)
//!      and `tb`/`lb`/`fb`/`self` receivers were unmatched. Receiver-agnostic now.
//!      `.assert_eq(..)` and `.when*(..)` join it ONLY in a file that mentions `AirBuilder` — `when` is a
//!      constraint dialect only in an AirBuilder context, and without that guard every gpui
//!      `.when(cond, ..)` in `starbridge-v2/src/cockpit/*` becomes a fake AIR violation.
//!   2. **closures** — `eval: Box::new(|row, _, pi| ..)`. Invisible to (1).
//!   3. **`ConstraintExpr` literals** — the DSL descriptor algebra. Invisible to (1) and (2).
//!   4. **descriptor gate trees** — `LeanExpr` / `VmConstraint` / `VmConstraint2` values built directly in
//!      Rust. This is the dialect that let a file truthfully say it "authors NO constraints" while
//!      authoring the entire descriptor. The worked example was `shielded_ring_clearing_air.rs`, which
//!      built 75 of them with no `include_str!` and no `parse_vm_descriptor2` anywhere in the file while
//!      its own module docblock said "NOT an AIR ... it authors NO constraints in any of the three
//!      dialects" — true of dialects (1)-(3) and false of the whole. That file is DELETED (2026-08-07,
//!      see its ledger note below); the dialect it exposed is why (4) exists. `perf/src/lib.rs`
//!      hand-builds a `VmConstraint2::MapOp` / `UMemOp` descriptor in a crate the old scope never reached.
//!   5. **`air_accepts` predicates** — a Rust-authored answer to "does the AIR accept this row". The law
//!      names these explicitly; they get their own ledger below (`AIR_ACCEPTS_LEDGER`) and their own test.
//!
//! ## AUTHORING vs LOWERING — the distinction, in code, not in an exclusion list
//! For dialects (3) and (4) the same text `ConstraintExpr::Binary { col }` is either **construction**
//! (algebra originates here — authoring) or **destructuring** (algebra arrived from somewhere else and is
//! being read — lowering / interpreting). `classify_site` decides it syntactically:
//!
//! * balanced match-arm headers up to `=>` (stopping before any `if` guard) are patterns,
//!   including nested tuple/or-patterns and trailing commas,
//! * only the SECOND `matches!` argument is a pattern; its scrutinee and guard construct,
//! * `if let`, `while let`, `let .. =` before the binding `=` are patterns,
//! * inline `const` blocks are expressions even inside patterns; anything else constructs.
//!
//! Pattern contexts are computed once per file. The innermost explicit context wins; no
//! filename is exempted and `#[cfg(test)]` attribution never changes the count.
//!
//! This is the *only* exclusion in the gate and it is a property of the source text, not a list of
//! forgiven filenames. It takes `custom_leaf_lowering.rs` from 46 phantom violations to 0 — while still
//! counting the 64 `LeanExpr` nodes that file really does construct, because a lowering that authors
//! `x·(x−1)` for `Binary` **is** authoring that algebra in Rust; that is exactly the debt
//! `CustomLeafEncoding.lean::cell_to_descriptor_faithful` exists to discharge. Destructuring is free;
//! construction is counted wherever it happens.
//!
//! ## `#[cfg(test)]` INSIDE a `src/` file is COUNTED — and that is not an accident (2026-07-30)
//! The scope test is `rel.contains("/src/")`, so the gate's "test code is not ratcheted" decision is
//! implemented as a **directory** property. That proxy is wrong in exactly one direction: a
//! `#[cfg(test)] mod tests` inside a `src/` file is test code that the directory test calls
//! production, and identical source text therefore scores 8 in `circuit-prove/src/foo.rs` and 0 in
//! `circuit-prove/tests/foo.rs`.
//!
//! **The strictness EARNED ITS KEEP, so it stays.** On 2026-07-30 the gate went red on
//! `circuit-prove/src/dregg_mina_config.rs` — 8 sites, 8 symbolic, all inside `#[cfg(test)]`, and all
//! of them a byte-identical THIRD copy of the toy Fibonacci AIR that `dregg_outer_config::tests` and
//! `gpu_backend::tests` already each carried. None of it was dregg constraint content; the file's own
//! module doc opened with "no AIR, no constraint, no gadget" and was, on the plumbing question,
//! correct. It was still a hand-written Rust AIR, and law #1's own words are that an existing Rust AIR
//! is debt rather than a foundation, so copying one **is** the drift. Had `#[cfg(test)]` been free,
//! that third copy would have landed silently and a fourth would have followed. The fix was
//! subtraction — three copies became one shared `dregg_outer_config::toy_fib_air` — and this gate was
//! not touched to make it green.
//!
//! What DID change is that `cfg_test_regions` now ATTRIBUTES sites, so a failure message can say
//! "ALL 8 inside `#[cfg(test)]`" instead of leaving the reader to open the file and guess whether the
//! gate mis-fired. Attribution only: `authored()` is unchanged, and `#[cfg(any(test, feature = ..))]`
//! deliberately does not count as test-only because that item ships whenever the feature is on.
//!
//! **The asymmetry's correct resolution is to close the `tests/` hole, not to widen the `src/`
//! exemption** — the direction of the law is fewer Rust-authored constraints, and the hole is the
//! looser side. That is a campaign, not a line: 847 sites across 41 files, most of them legitimate
//! emit-gate differentials that must be separated from the rest before any of it can be ratcheted.
//! **First rung, named so it is findable:** classify `tests/` sites into (a) differentials that build
//! a Rust expectation *and compare it against a Lean emission in the same file* — the law working —
//! and (b) everything else, then ratchet (b) alone. Until that exists, the bullet below stands.
//!
//! ## What this gate CANNOT see (say it out loud rather than imply coverage)
//! * **`tests/` trees.** 41 test files author 847 sites — overwhelmingly emit-gate differentials,
//!   which must build a Rust-side expectation in order to compare it against the Lean emission (that is
//!   the law working). They are not ratcheted here, so a hand-written AIR parked in a `tests/` directory
//!   is invisible to this gate. Scoped out deliberately, named as a hole. ⚑ And it is the LOOSER side
//!   of the `#[cfg(test)]` asymmetry above: moving a counted `src/` AIR into `tests/` would zero its
//!   score without deleting a line, which is laundering, not a fix.
//! * **Semantics.** The count is IR *nodes constructed*, not constraint *degree* or *soundness*. It is a
//!   monotone proxy: more Rust-authored algebra ⇒ a bigger number. It says nothing about whether a
//!   constraint is right, and a file can restructure to lower its number without emitting from Lean.
//! * **Indirection.** Algebra built through a helper that takes the variant as data (a `Vec<PolyTerm>`
//!   assembled far from any `ConstraintExpr::`) is undercounted; only the final constructor is seen.
//! * **Non-Rust hosts.** Solidity, Lean-adjacent scripts, and generated code under `target/` are out of
//!   scope, as are `docs/` snapshots of Rust (there is a byte-identical copy of `descriptor_ir2.rs` under
//!   `docs/deos/artifacts/` that is documentation, not a compiled unit).
//! * ⚑ **THE VENDORED FORKS — the largest blind spot, and it is Rust (named 2026-07-30).**
//!   `scan_repo` walks `repo_root()`, which is THIS repository. Every p3 crate enters as a **git
//!   dependency** on `emberian/plonky3-recursion` (pinned by rev in the root `Cargo.toml`), so
//!   `circuit-prover/src/air/{const,alu,public,recompose,expose_claim}_air.rs` — the ENTIRE primitive
//!   AIR layer the whole prover stands on — scores exactly **zero** here, no matter what is written in
//!   it. So do `vendor/plonky3-fri-82cfad73` and the other `[patch]`ed trees.
//!   MEASURED: `fc3c6df` added `builder.assert_eq(main.value[i], prep.value[i])` to `ConstAir::eval`,
//!   binding a constant's value into the preprocessed commitment. Run the gate's own classifier over
//!   that file and it scores **1 authored symbolic site**
//!   (`LAW1_EXPLAIN=../plonky3-recursion/circuit-prover/src/air/const_air.rs`); run the RATCHET and the
//!   delta is **0**, because the walker never reaches it. A zero delta from this gate is therefore NOT
//!   evidence that no Rust constraint was authored — only that none was authored *in this repo*.
//!   That change was a deliberate, recorded decision (it is a p3 primitive with no Lean authoring path
//!   short of replacing p3, and dregg's own circuit logic stayed Lean-authored), which is exactly why it
//!   is written down here rather than left to a silent zero.
//!   ⚑ The remedy is NOT to scan a sibling checkout: the fork resolves from git, so a fresh clone and CI
//!   have no sibling path to walk, and a gate that only fires on one developer's machine is worse than
//!   one that admits its scope. It needs a ratchet keyed to the **pinned rev** — a recorded per-rev site
//!   count for the fork's `src/` trees, checked against the resolved source in `~/.cargo/git/checkouts`.
//!   That is a campaign, not a line; until it exists, this bullet is the honest statement of coverage.
//! * **`metatheory/`** is skipped entirely — that is where the algebra is SUPPOSED to live.
//!
//! ## ⚑ RED AND UNOWNED FOR 25 HOURS — what a COUNT cannot tell you (2026-07-31)
//!
//! This gate went red at `81ee5492d` (2026-07-30 20:04:39) and was still red a day later. Two
//! commits that edit THIS FILE landed inside that window — `300591cfc` (21:30, the Mina toy-AIR
//! de-duplication) and `fd507d99b` (23:14) — and neither noticed, because neither ran it. Two
//! other lanes DID hit the red, each investigated it, and each correctly concluded "not mine"
//! and moved on. Meanwhile every brief written that day asserted the gate was green.
//!
//! **The count was RIGHT in all three rows.** What failed was the DIAGNOSTIC. A row that says
//! `283 -> 287` names a file and a delta, and there was no supported way to ask WHICH four sites
//! moved: reconstructing it took a standalone re-compile of this file's classifier plus a
//! 40-revision walk of each file's history. A lane that owns an unrelated change will always,
//! and correctly, decide that is not its job. **A red that cannot be attributed is a red that
//! will not be owned** — so the repair belongs in the MESSAGE, not in the ledger:
//!
//! * a `GREW` row now prints the grown file's authored sites: a by-kind histogram (a growth of
//!   four is usually a SINGLETON variant, findable at a glance) and, at or under 40 sites, every
//!   line, with `#[cfg(test)]` membership marked;
//! * `LAW1_EXPLAIN` now lists the SYMBOLIC and CLOSURE dialects too. It listed only dialects
//!   (3)+(4), so a maintainer auditing `descriptor_ir2.rs`'s 287 saw 169 lines and could not
//!   reconcile the listing with the number — the 118 `assert_zero`-family sites were invisible;
//! * the failure message carries the recipe that finds the origin COMMIT without a bisect.
//!   `LAW1_EXPLAIN` resolves through `Path::join`, so an ABSOLUTE path wins and
//!   `git show <rev>:<file> > /tmp/at-rev.rs` feeds it directly.
//!
//! ⚑ **THE STRICTNESS DID NOT MOVE.** No exemption was added, no dialect dropped, no classifier
//! loosened; `authored()` is byte-for-byte the same predicate. The three rows were re-pinned to
//! their MEASURED values with the origin commit and the nature of every site written into the
//! row — see the three `RE-PINNED 2026-07-31` blocks in `BASELINE`, which is where a reader six
//! weeks out has to be able to find them.
//!
//! ## The TRANSPORT class — a real over-count, NAMED rather than silently forgiven
//!
//! Five of those eleven sites are one shape, and it is worth a name because it will recur:
//!
//! ```text
//! WindowExpr::Add(a, b) => LeanExpr::Add(Box::new(f(a)?), Box::new(f(b)?))
//! ```
//!
//! Every argument was DESTRUCTURED from the same algebra one line earlier; the operator, the
//! arity and the columns are all fixed by the node being read. Nothing ORIGINATES — which is
//! precisely this gate's own authoring-vs-lowering test — yet `classify_site` scores it
//! `Construct`, because it looks only at the syntactic position of the CONSTRUCTED node and the
//! source type (`WindowExpr`) is not in `IR_TYPES`. So the arm counts +1 authored and +0
//! lowering. This is a genuine over-count and it is not the same thing as
//! `custom_leaf_lowering.rs`, which maps `Binary` to `x·(x−1)` and therefore really does choose
//! algebra in Rust.
//!
//! **It is named here and NOT auto-detected, deliberately.** Every syntactic rule tried against
//! the real specimens either under-fires (variant-name equality frees `Add`/`Mul`/`Const` but
//! not `Loc -> Var`, leaving the row red at 284 and the rule looking principled while doing
//! nothing) or needs an argument-provenance analysis — "every argument is a binding of this
//! arm's pattern or a recursive call" — which is a real mini-parser inside the one gate whose
//! wrongness is most expensive. A classifier that stops over-matching by also under-matching is
//! worse than the false positive it fixes, and a buggy classifier in the LAW gate is worse than
//! a number that is right for a boring reason. If a third transport shows up, THAT is the
//! moment to build the provenance analysis — with these five as its fixtures.
//!
//! ## Two MORE over-counts, named on the same terms (2026-08-06)
//!
//! The 179 -> 198 repair on `descriptor_ir2.rs` turned up two shapes this gate had never scored
//! before. Both are named here and NEITHER is auto-detected, for the reason above.
//!
//!   * ⚑ **THE CONSTANT-FALSE REFUSAL.** `builder.assert_zero(AB::Expr::ONE)` asserts `1 = 0`: it
//!     names no column and no coefficient, and it makes the AIR unsatisfiable on a shape an
//!     admission door already refused. It is `return Err` spelled in the AIR — the OPPOSITE of
//!     authoring a constraint — and dialect (1) scores it 1 because dialect (1) counts syntactic
//!     `assert_zero` call sites and looks at nothing else. There are five at HEAD.
//!     ⚠ **Do not exempt it.** A syntactic "argument is a bare constant path" rule is easy to
//!     write and impossible to smuggle algebra through, and it is STILL the wrong trade: an
//!     exemption list in the LAW gate costs more than five over-counted sites, and the pressure a
//!     count creates on a fail-closed backstop — *delete the refusal and the gate goes green* —
//!     is a pressure this repo can least afford to point that way. The row carries the reason
//!     instead, which is what a reader needs.
//!   * ⚑ **THE VECTOR-VALUED INTERPRETER ARM.** `Ir2Air`'s row-local walk ends in ONE shared
//!     `builder.assert_zero(match sel { .. })`, so `Gate`/`Boundary`/`Transition`/`PiBinding`/
//!     `WindowGate` — five node kinds, every descriptor, thousands of constraints — cost this file
//!     exactly ONE site between them. A node kind whose Lean denotation is a VECTOR of congruences
//!     (`ProofBind.holdsAt` is `1 + n + n` of them) cannot fold into that tail and pays per call
//!     site. So the number moves with a node kind's ARITY, not with how much algebra originates in
//!     Rust — and `PiBinding`, whose polynomial `local[col] − pv[pi]` is just as Rust-chosen, has
//!     always been free. This is the sharpest known limit of dialect (1) as a proxy; a real fix is
//!     the same provenance analysis the TRANSPORT class needs, on the same terms.
//!
//! ## If this test fails
//! You (or an agent) hand-authored a constraint in Rust. That is the violation itself — do NOT add your
//! file to the baseline to make it green. Emit it from Lean instead (`metatheory/Dregg2/Circuit/Emit/*.lean`
//! -> `emitVmJson2` -> `descriptors/by-name/*.json` -> `descriptor_by_name` -> `prove_vm_descriptor2`; see
//! `EffectVmEmitTurnChainBinding.lean` + `metatheory/EmitTurnChain.lean` for the worked end-to-end example).
//! Lower the baseline when you retire algebra. RAISING a row needs a reason written INTO THE ROW —
//! the origin commit, and what each new site is if it is not AIR. In the row, not in a companion
//! document: the 2026-07-31 red was investigated three times because the reasons for the numbers
//! were nowhere near the numbers, and a reason a reader has to go find is a reason nobody reads.
//! A silent re-print to green is the move CLAUDE.md was written against; it turns a law into a habit.
//! `LAW1_PRINT_BASELINE=1 cargo test -p dregg-circuit-prove --test law1_enforcement_gate -- --nocapture`
//! prints the current ledger in source form, so a legitimate SHRINK is a copy-paste.
//!
//! ## Why entries remain (the honest ledger, not an amnesty)
//! * INTERPRETERS (the law WORKING — they evaluate Lean-authored constraints): `descriptor_ir2.rs`,
//!   `descriptor_ir2_canonical.rs`, `dsl/dsl_p3_air.rs`, `lean_lookup_air.rs` (the proven range gadget).
//!   Their *pattern* halves are now free; the residual is the IR they construct while translating.
//! * LOWERING DEBT: `custom_leaf_adapter.rs` / `custom_leaf_lowering.rs` —
//!   `CustomLeafEncoding.lean::cell_to_descriptor_faithful` explicitly covers the Lean mirror,
//!   not the deployed Rust lowerer. That citation does not discharge compiler refinement.
//! * LEGACY SOURCE DESCRIPTORS: `dsl/derivation.rs`, `dsl/note_spending.rs` remain Rust-authored
//!   DSL constraints. Note-spend consumers now parse the repaired Lean artifact directly;
//!   the DSL remains the witness recipe's source, not a proof of descriptor equivalence.
//!   The removed lowerers checked supported kinds/layout, not arbitrary semantic drift.
//! * THE USER-PROGRAM GRAMMAR: `dsl/predicates/*`, `dsl/descriptors.rs` — the host-trusted smart-contract
//!   surface users deploy programs against; interpreted, fails closed on an unknown vk_hash.
//! * THE ONE TEST-ONLY TOY AIR: `dregg_outer_config.rs` (8) — `toy_fib_air::ToyFibAir`, the p3
//!   uni-stark 2-column Fibonacci, `#[cfg(test)]`-gated and shared by all three configs in the crate
//!   (CPU outer, GPU outer, Mina terminal). A `StarkConfig` round-trip needs *an* AIR to prove and it
//!   must deliberately not be a dregg one. Was THREE copies until 2026-07-30; `gpu_backend.rs` (8) and
//!   a fresh `dregg_mina_config.rs` (8) are both retired into this row.
//! * NAMED RESIDUALS — real debt, now VISIBLE for the first time:
//!   - ~~**`param-compose/src/{air,builder}.rs` (28) + the `entity-compose` consumer.**~~ **CLOSED
//!     2026-07-25 — DELETED, 1028 lines.** It was a complete hand-written Rust AIR: 24 `assert_zero`
//!     sites, its own `ConstraintExpr` emission, `air_accepts`, and `tamper()`, and `builder.rs`
//!     documented itself as "a sibling of `dregg-automatafl`'s builder … duplicated rather than
//!     shared" — the automatafl Rust-AIR deletion was recorded as complete, but the clone had already
//!     been copied out into `param-compose/`, where it survived precisely because it was outside this
//!     gate's old scope. The "There is NO Lean route" line this entry carried is what changed:
//!     `Dregg2/Circuit/Emit/ParamComposeEmit.lean` now authors the whole AIR and byte-pins the wire,
//!     `ParamComposeRefine.paramCompose_refines_law` refines it, and all 18 shapes the test corpus
//!     exercises are `#guard`-pinned, so consumers and tests alike ride the emitted descriptor.
//!     Deleting it was the fix; this line is the receipt that it happened. (The honest price — four
//!     coverage items that lost their only checker — is recorded in `param-compose/src/lib.rs`.)
//!   - **`perf/src/lib.rs` (28)** — a hand-built `VmConstraint2::{MapOp,UMemOp}` descriptor, dialect (4),
//!     in a crate no previous audit scanned.
//!   - `ivc.rs` + `dsl/fold.rs` (`FoldAir`) — test-only; `ivc`'s emitter is one Lean PROVES insufficient
//!     (`ivc_anchor_insufficient`).
//!   - `dregg-dsl-differential/*`, `dregg-dsl-runtime/src/composition.rs`, `constraint-lowering/src/lib.rs`,
//!     `game-turn-slice/src/compiler.rs`, `sdk/src/full_turn_proof.rs`, `turn/src/umem.rs`,
//!     `tests/src/dsl_pipeline.rs` — the rest of the surface the two-directory scope hid.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

// ─────────────────────────────────────────────────────────────────────────────
// Lexical normalisation. Comments and string bodies are blanked (newlines kept, so
// byte offsets and line numbers survive) — otherwise this gate's OWN module docs,
// and every `"ConstraintExpr::Foo"` in an error message, would count as algebra.
// ─────────────────────────────────────────────────────────────────────────────
fn blank_noncode(src: &str) -> String {
    let b = src.as_bytes();
    let n = b.len();
    let mut out = Vec::with_capacity(n);
    let mut i = 0usize;
    // Copy `k` bytes as blanks, preserving newlines so offsets->lines stay honest.
    macro_rules! blank_to {
        ($j:expr) => {{
            let j = $j;
            for &c in &b[i..j] {
                out.push(if c == b'\n' { b'\n' } else { b' ' });
            }
            i = j;
        }};
    }
    while i < n {
        let c = b[i];
        if c == b'/' && i + 1 < n && b[i + 1] == b'/' {
            let j = b[i..].iter().position(|&c| c == b'\n').map_or(n, |p| i + p);
            blank_to!(j);
        } else if c == b'/' && i + 1 < n && b[i + 1] == b'*' {
            // Rust block comments nest.
            let mut depth = 0usize;
            let mut j = i;
            while j < n {
                if b[j] == b'/' && j + 1 < n && b[j + 1] == b'*' {
                    depth += 1;
                    j += 2;
                } else if b[j] == b'*' && j + 1 < n && b[j + 1] == b'/' {
                    depth -= 1;
                    j += 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    j += 1;
                }
            }
            blank_to!(j.min(n));
        } else if c == b'r' && !prev_is_ident(b, i) && raw_string_hashes(b, i).is_some() {
            let h = raw_string_hashes(b, i).unwrap();
            // r{#*}" .. "{#*}
            let open_end = i + 1 + h + 1;
            let mut close = String::from("\"");
            close.push_str(&"#".repeat(h));
            let j = find(b, open_end, close.as_bytes()).map_or(n, |p| p + close.len());
            blank_to!(j);
        } else if c == b'"' {
            let mut j = i + 1;
            while j < n {
                if b[j] == b'\\' {
                    j += 2;
                    continue;
                }
                if b[j] == b'"' {
                    j += 1;
                    break;
                }
                j += 1;
            }
            blank_to!(j.min(n));
        } else if c == b'\'' {
            // A char literal, or a lifetime. `'"'` would otherwise flip string state.
            let lit_end = if i + 1 < n && b[i + 1] == b'\\' {
                // '\n' '\'' '\u{1F}'
                let mut j = i + 2;
                while j < n && b[j] != b'\'' {
                    j += 1;
                }
                if j < n { Some(j + 1) } else { None }
            } else if i + 2 < n && b[i + 2] == b'\'' {
                Some(i + 3)
            } else {
                None // lifetime
            };
            match lit_end {
                Some(j) => blank_to!(j.min(n)),
                None => {
                    out.push(c);
                    i += 1;
                }
            }
        } else {
            out.push(c);
            i += 1;
        }
    }
    String::from_utf8(out).unwrap_or_else(|_| src.to_string())
}

fn prev_is_ident(b: &[u8], i: usize) -> bool {
    i > 0 && (b[i - 1].is_ascii_alphanumeric() || b[i - 1] == b'_')
}

/// `Some(hashes)` when `b[i..]` opens a raw string (`r"`, `r#"`, `r##"`, ...).
fn raw_string_hashes(b: &[u8], i: usize) -> Option<usize> {
    let mut j = i + 1;
    while j < b.len() && b[j] == b'#' {
        j += 1;
    }
    if j < b.len() && b[j] == b'"' {
        Some(j - i - 1)
    } else {
        None
    }
}

fn find(b: &[u8], from: usize, needle: &[u8]) -> Option<usize> {
    if from >= b.len() {
        return None;
    }
    b[from..]
        .windows(needle.len())
        .position(|w| w == needle)
        .map(|p| p + from)
}

// ─────────────────────────────────────────────────────────────────────────────
// AUTHORING vs LOWERING
// ─────────────────────────────────────────────────────────────────────────────
#[derive(PartialEq, Eq, Debug, Clone, Copy)]
enum Site {
    /// The algebra ORIGINATES here — an authored constraint. Counted.
    Construct,
    /// The algebra ARRIVED here and is being read — a lowering / interpreter. Free.
    Pattern,
}

/// Index just past the delimiter group opened at `i`.
fn matching(b: &[u8], i: usize) -> usize {
    let mut depth = 0i32;
    let mut j = i;
    while j < b.len() {
        match b[j] {
            b'{' | b'(' | b'[' => depth += 1,
            b'}' | b')' | b']' => {
                depth -= 1;
                if depth == 0 {
                    return j + 1;
                }
            }
            _ => {}
        }
        j += 1;
    }
    b.len()
}

fn skip_ws(b: &[u8], mut i: usize) -> usize {
    while i < b.len() && (b[i] as char).is_whitespace() {
        i += 1;
    }
    i
}

/// An explicitly delimited syntactic context. The innermost context wins: a `matches!`
/// pattern inside a guard is a pattern, but the guard and the macro's scrutinee are expressions.
#[derive(Debug)]
struct SiteContext {
    start: usize,
    end: usize,
    site: Site,
}

/// Walk balanced groups, recording the PATTERN portion of match arms / bindings / `matches!`.
/// Unlike looking at the byte after a constructor, this handles a tuple's first component,
/// nested or-patterns and trailing commas without mistaking siblings for new constraints.
/// No filename/type-variant exemption: every RHS, guard and scrutinee remains construction.
fn site_contexts(b: &[u8]) -> Vec<SiteContext> {
    fn walk(b: &[u8], lo: usize, hi: usize, out: &mut Vec<SiteContext>) {
        let mut i = lo;
        let mut arm_start = lo;
        let mut guard = None;
        let mut in_rhs = false;
        let mut binder = None;
        while i < hi {
            if matches!(b[i], b'(' | b'[' | b'{') {
                let after = matching(b, i).min(hi);
                if after <= i + 1 {
                    break;
                }
                walk(b, i + 1, after - 1, out);
                // A block-valued arm need not have a comma before the next arm. Never do
                // this before `=>`: the group may be a STRUCT PATTERN or a guard block.
                if in_rhs && b[i] == b'{' {
                    arm_start = after;
                    guard = None;
                    in_rhs = false;
                }
                i = after;
                continue;
            }
            if b[i..].starts_with(b"=>") {
                let pattern_end = guard.unwrap_or(i);
                out.push(SiteContext {
                    start: arm_start,
                    end: pattern_end,
                    site: Site::Pattern,
                });
                if let Some(g) = guard {
                    out.push(SiteContext {
                        start: g,
                        end: i,
                        site: Site::Construct,
                    });
                }
                in_rhs = true;
                binder = None;
                i += 2;
                continue;
            }
            if b[i] == b',' || b[i] == b';' {
                arm_start = i + 1;
                guard = None;
                in_rhs = false;
                binder = None;
            }
            if b[i] == b'='
                && b.get(i + 1) != Some(&b'=')
                && b.get(i.wrapping_sub(1)) != Some(&b'=')
            {
                if let Some(start) = binder.take() {
                    out.push(SiteContext {
                        start,
                        end: i,
                        site: Site::Pattern,
                    });
                }
            }
            if b[i].is_ascii_alphabetic() || b[i] == b'_' {
                let end = ident_at(b, i);
                let word = &b[i..end];
                if word == b"let" {
                    binder = Some(end);
                }
                if word == b"if" && !in_rhs && guard.is_none() {
                    guard = Some(i);
                }
                if word == b"matches" {
                    let bang = skip_ws(b, end);
                    let open = skip_ws(b, bang + 1);
                    if b.get(bang) == Some(&b'!') && b.get(open) == Some(&b'(') {
                        let close = matching(b, open).saturating_sub(1).min(hi);
                        let mut k = open + 1;
                        let mut pattern_start = None;
                        let mut pattern_end = close;
                        while k < close {
                            if matches!(b[k], b'(' | b'[' | b'{') {
                                k = matching(b, k);
                                continue;
                            }
                            if b[k] == b',' && pattern_start.is_none() {
                                pattern_start = Some(k + 1);
                            }
                            if b[k].is_ascii_alphabetic() || b[k] == b'_' {
                                let e = ident_at(b, k);
                                if pattern_start.is_some() && &b[k..e] == b"if" {
                                    pattern_end = k;
                                    break;
                                }
                                k = e;
                            } else {
                                k += 1;
                            }
                        }
                        // The first argument is an expression, NEVER a pattern. No blanket
                        // "inside matches!" exception (which hid real constructors there).
                        if let Some(start) = pattern_start {
                            out.push(SiteContext {
                                start: open + 1,
                                end: start,
                                site: Site::Construct,
                            });
                            out.push(SiteContext {
                                start,
                                end: pattern_end,
                                site: Site::Pattern,
                            });
                            out.push(SiteContext {
                                start: pattern_end,
                                end: close,
                                site: Site::Construct,
                            });
                        }
                    }
                }
                // Inline const expressions in patterns can themselves BUILD an IR node.
                if word == b"const" {
                    let open = skip_ws(b, end);
                    if b.get(open) == Some(&b'{') {
                        out.push(SiteContext {
                            start: open + 1,
                            end: matching(b, open) - 1,
                            site: Site::Construct,
                        });
                    }
                }
                i = end;
            } else {
                i += 1;
            }
        }
    }
    let mut out = Vec::new();
    walk(b, 0, b.len(), &mut out);
    out
}

fn classify_site(contexts: &[SiteContext], path_start: usize) -> Site {
    contexts
        .iter()
        .filter(|c| c.start <= path_start && path_start < c.end)
        .min_by_key(|c| c.end - c.start)
        .map_or(Site::Construct, |c| c.site)
}

// ─────────────────────────────────────────────────────────────────────────────
// The five dialects
// ─────────────────────────────────────────────────────────────────────────────

/// Dialects (3) and (4): the constraint IR types whose CONSTRUCTION is authored algebra.
const IR_TYPES: &[&str] = &[
    "ConstraintExpr",
    "LeanExpr",
    "VmConstraint2",
    "VmConstraint",
];

/// Cheap prefilter. A file with none of these cannot hold any dialect, so the ~2500-file
/// walk does not pay for a full lex. Exact given that `assert_eq`/`when` are only counted
/// inside an `AirBuilder` file.
const MARKERS: &[&str] = &[
    "assert_zero",
    "AirBuilder",
    "ConstraintExpr",
    "LeanExpr",
    "VmConstraint",
    "eval: Box::new",
];

/// One site, as reported by `count_sites_explained` — the unit a `GREW` row prints so the
/// reader is not left with a delta and a bisect. Covers ALL FIVE dialects: the explain path
/// used to record only (3)+(4), which made `descriptor_ir2.rs`'s 118 `assert_zero`-family
/// sites invisible in a listing that claimed to explain its 287.
#[derive(Debug, Clone)]
struct SiteRecord {
    line: usize,
    /// `ConstraintExpr::Binary`, `.assert_zero(..)`, `eval: Box::new(..)`.
    what: String,
    site: Site,
    /// Attribution only — a test-only site is authored exactly like any other.
    cfg_test: bool,
}

#[derive(Default, Debug, Clone, Copy)]
struct Counts {
    /// (1) plonky3 symbolic builder calls.
    symbolic: usize,
    /// (2) closure constraints.
    closures: usize,
    /// (3)+(4) constraint-IR values CONSTRUCTED.
    ir_constructed: usize,
    /// (3)+(4) constraint-IR values DESTRUCTURED. Reported, never counted as a violation.
    ir_lowered: usize,
    /// How many of the AUTHORED sites sit inside a `#[cfg(test)]` item — a SUBSET of
    /// `authored()`, not a deduction from it. Reported so a failure message can say
    /// "8 of 8 are test-only" instead of leaving the reader to open the file.
    cfg_test: usize,
}

impl Counts {
    fn authored(&self) -> usize {
        self.symbolic + self.closures + self.ir_constructed
    }

    /// The `, N of them #[cfg(test)]-only` clause, or nothing when N is 0.
    fn cfg_test_note(&self) -> String {
        if self.cfg_test == 0 {
            String::new()
        } else if self.cfg_test == self.authored() {
            format!(", ALL {} inside `#[cfg(test)]`", self.cfg_test)
        } else {
            format!(", {} of them inside `#[cfg(test)]`", self.cfg_test)
        }
    }
}

fn ident_at(b: &[u8], i: usize) -> usize {
    let mut j = i;
    while j < b.len() && (b[j].is_ascii_alphanumeric() || b[j] == b'_') {
        j += 1;
    }
    j
}

/// `.name(` with arbitrary whitespace around the dot (chained builders wrap lines), and
/// NOT `..name(`. A leading dot is what separates the `assert_eq` METHOD from the
/// `assert_eq!` macro. Returns the OFFSET of each hit so it can be attributed to a
/// `#[cfg(test)]` region (see `cfg_test_regions`) — the count alone cannot be.
fn method_call_sites(b: &[u8], names: &[&str], prefix_match: bool) -> Vec<usize> {
    let n = b.len();
    let mut hits = Vec::new();
    let mut i = 0usize;
    while i < n {
        if !(b[i].is_ascii_alphabetic() || b[i] == b'_') || prev_is_ident(b, i) {
            i += 1;
            continue;
        }
        let end = ident_at(b, i);
        let word = &b[i..end];
        let matched = names.iter().any(|nm| {
            let nb = nm.as_bytes();
            if prefix_match {
                word.starts_with(nb)
            } else {
                word == nb
            }
        });
        if matched {
            // preceding non-ws must be a single `.`
            let mut p = i;
            while p > 0 && (b[p - 1] as char).is_whitespace() {
                p -= 1;
            }
            let dotted = p > 0 && b[p - 1] == b'.' && !(p > 1 && b[p - 2] == b'.');
            let q = skip_ws(b, end);
            if dotted && q < n && b[q] == b'(' {
                hits.push(i);
            }
        }
        i = end.max(i + 1);
    }
    hits
}

/// Byte ranges of `#[cfg(test)]`-gated items. Computed on the BLANKED code, so a
/// commented-out attribute never opens a region.
///
/// ⚑ **This is ATTRIBUTION, not an exemption.** A site inside one of these ranges is
/// counted by `authored()` exactly like any other; the range only lets the failure
/// message say *which* sites are test-only, so the reader is not left guessing. See the
/// module docs' `#[cfg(test)]`-inside-`src/` note for why the counting stays strict.
///
/// Only the LITERAL `#[cfg(test)]` opens a range. `#[cfg(any(test, feature = "x"))]`
/// deliberately does not — that item compiles in a production build whenever the feature
/// is on, so calling it test-only would be false.
fn cfg_test_regions(b: &[u8]) -> Vec<(usize, usize)> {
    let n = b.len();
    // `#![cfg(test)]` is an INNER attribute: it gates the whole file.
    if find(b, 0, b"#![cfg(test)]").is_some() {
        return vec![(0, n)];
    }
    let attr = b"#[cfg(test)]";
    let mut out = Vec::new();
    let mut i = 0usize;
    while let Some(p) = find(b, i, attr) {
        i = p + 1;
        let mut j = skip_ws(b, p + attr.len());
        // Any further outer attributes on the same item.
        while j < n && b[j] == b'#' {
            let Some(open) = find(b, j, b"[") else { break };
            j = skip_ws(b, matching(b, open));
        }
        // Visibility / qualifier words, then the item keyword.
        let mut item_has_body = true;
        loop {
            let e = ident_at(b, j);
            if e == j {
                break;
            }
            match std::str::from_utf8(&b[j..e]).unwrap_or("") {
                "pub" | "unsafe" | "async" | "default" => {
                    let k = skip_ws(b, e);
                    // `pub(crate)` / `pub(super)`
                    j = if b.get(k) == Some(&b'(') {
                        skip_ws(b, matching(b, k))
                    } else {
                        k
                    };
                }
                // Bodyless items: `use a::{b, c};` opens a brace that is NOT a region.
                "use" | "type" | "const" | "static" | "let" | "extern" => {
                    item_has_body = false;
                    break;
                }
                _ => break, // mod / fn / impl / struct / enum / trait / macro_rules
            }
        }
        if !item_has_body {
            continue;
        }
        // The body is the first brace group — but only if a `{` precedes the item's `;`.
        let mut k = j;
        while k < n && b[k] != b'{' && b[k] != b';' {
            k += 1;
        }
        if k < n && b[k] == b'{' {
            out.push((j, matching(b, k)));
        }
    }
    out
}

fn count_sites(raw: &str) -> Counts {
    count_sites_explained(raw, None)
}

/// `explain` collects a `SiteRecord` per site — ALL FIVE dialects — so a maintainer can audit
/// WHY a file scores what it scores:
/// `LAW1_EXPLAIN=circuit/src/foo.rs cargo test -p dregg-circuit-prove --test law1_enforcement_gate -- --nocapture`
///
/// The path resolves through `Path::join`, so an ABSOLUTE path wins over the repo root — which
/// is what lets `git show <rev>:<file> > /tmp/at-rev.rs` be scored directly, and is the whole
/// difference between finding a growth's origin commit in one loop and bisecting for it.
fn count_sites_explained(raw: &str, mut explain: Option<&mut Vec<SiteRecord>>) -> Counts {
    let code = blank_noncode(raw);
    let b = code.as_bytes();
    let mut c = Counts::default();
    let regions = cfg_test_regions(b);
    let contexts = site_contexts(b);
    let in_cfg_test = |p: usize| regions.iter().any(|&(s, e)| p >= s && p < e);
    let line_of = |p: usize| b[..p].iter().filter(|&&x| x == b'\n').count() + 1;

    // (1) `x.assert_zero(..)` on any receiver — this is the form the previous revision
    // missed on `b.assert_zero(&Head::..)`, which is param-compose's ENTIRE AIR.
    let mut sym = method_call_sites(b, &["assert_zero"], false);
    // `.assert_eq(..)` / `.when*(..)` are a constraint dialect only on an AirBuilder.
    if code.contains("AirBuilder") {
        sym.extend(method_call_sites(b, &["assert_eq"], false));
        sym.extend(method_call_sites(b, &["when"], true));
    }
    c.symbolic += sym.len();
    c.cfg_test += sym.iter().filter(|&&p| in_cfg_test(p)).count();
    if let Some(ex) = explain.as_deref_mut() {
        for &p in &sym {
            ex.push(SiteRecord {
                line: line_of(p),
                what: format!(".{}(..)", String::from_utf8_lossy(&b[p..ident_at(b, p)])),
                site: Site::Construct,
                cfg_test: in_cfg_test(p),
            });
        }
    }

    // (2) closures.
    {
        let mut i = 0usize;
        while let Some(p) = find(b, i, b"eval") {
            let q = skip_ws(b, p + 4);
            if q < b.len() && b[q] == b':' && !prev_is_ident(b, p) {
                let r = skip_ws(b, q + 1);
                if b[r..].starts_with(b"Box::new") {
                    c.closures += 1;
                    if in_cfg_test(p) {
                        c.cfg_test += 1;
                    }
                    if let Some(ex) = explain.as_deref_mut() {
                        ex.push(SiteRecord {
                            line: line_of(p),
                            what: "eval: Box::new(..)".to_string(),
                            site: Site::Construct,
                            cfg_test: in_cfg_test(p),
                        });
                    }
                }
            }
            i = p + 4;
        }
    }

    // (3)+(4) constraint IR: construction is authored, destructuring is not.
    let mut i = 0usize;
    while i < b.len() {
        if !(b[i].is_ascii_alphabetic() || b[i] == b'_') || prev_is_ident(b, i) {
            i += 1;
            continue;
        }
        let end = ident_at(b, i);
        let word = std::str::from_utf8(&b[i..end]).unwrap_or("");
        if IR_TYPES.contains(&word) && b[end..].starts_with(b"::") {
            let vstart = end + 2;
            let vend = ident_at(b, vstart);
            if vend > vstart && b[vstart].is_ascii_uppercase() {
                let site = classify_site(&contexts, i);
                match site {
                    Site::Construct => {
                        c.ir_constructed += 1;
                        if in_cfg_test(i) {
                            c.cfg_test += 1;
                        }
                    }
                    Site::Pattern => c.ir_lowered += 1,
                }
                if let Some(ex) = explain.as_deref_mut() {
                    ex.push(SiteRecord {
                        line: line_of(i),
                        what: String::from_utf8_lossy(&b[i..vend]).into_owned(),
                        site,
                        cfg_test: in_cfg_test(i),
                    });
                }
                i = vend;
                continue;
            }
        }
        i = end.max(i + 1);
    }
    if let Some(ex) = explain.as_deref_mut() {
        ex.sort_by_key(|r| r.line);
    }
    c
}

// ─────────────────────────────────────────────────────────────────────────────
// Scope: every `src/` tree in the repository.
// ─────────────────────────────────────────────────────────────────────────────
/// Directories that hold no compiled first-party Rust, or hold the place the algebra is
/// SUPPOSED to live. Keep this list boring and justifiable — it is the one place a
/// violation could be parked deliberately.
const SKIP_DIRS: &[&str] = &[
    "target", // build output
    ".git",
    "node_modules",
    "vendor", // third-party forks (bulletproofs-r1cs-wgpu, curve25519-dalek-dregg)
    "docs",   // prose + byte-copies of Rust kept as documentation artifacts
    ".cache",
    ".lake",
    "metatheory", // Lean. This is WHERE ALGEBRA BELONGS.
];

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("circuit-prove has a parent")
        .to_path_buf()
}

/// ⚑ **THE REPOSITORY IS WHAT `git` TRACKS, NOT WHAT IS ON DISK** (added 2026-08-07).
///
/// The walker below is a filesystem walk, and a filesystem walk sees whatever a lane happened to
/// leave lying around. `SKIP_DIRS` was the only defence and it is a DENY-LIST, so it can only ever
/// name the scratch directories that already exist. It did not name `headver/` — a 679 MB
/// **untracked, `.gitignore`d, separately-`git init`ed** checkout of HEAD that a lane creates to
/// verify a build against the committed tree — and so the gate walked `headver/**/src/*.rs` as if
/// it were source. MEASURED 2026-08-07: **2 890 `.rs` files under a `src/` inside `headver/`**, two
/// of which define `air_accepts`. Every ledgered file was re-reported a second time under the
/// `headver/` prefix, where no `BASELINE` row matches it, which is the gate's definition of a NEW
/// violation — and the two `air_accepts` copies were unledgered by the same mechanism. **Two
/// failing cases, both pure artefact**, and the ledger they printed was the ledger DUPLICATED.
///
/// That is a gate aimed at a directory that is not in the repository. A deny-list cannot fix it —
/// the next scratch checkout has a different name. So scope is now an ALLOW-list taken from
/// `git ls-files`: a file is in scope iff git tracks it. `SKIP_DIRS` stays because it is also the
/// place a *tracked* directory is deliberately excluded (`docs/`'s byte-copies, `metatheory/`),
/// and because the synthetic-tree red path has no git to ask.
///
/// **No fallback.** If `git ls-files` cannot be run or comes back empty, this PANICS rather than
/// silently reverting to the untracked walk — a scope oracle that fails open is how the gate got
/// here.
///
/// ⚠ **AND SAY WHAT IT NOW CANNOT SEE.** This narrows the gate in one real direction: a hand-written
/// AIR in a brand-new `src/*.rs` that its author has written but not yet `git add`ed scores ZERO
/// here, where the old walk would have caught it. That is the correct trade — an un-added file is
/// not in the repository and cannot be reviewed, merged or built by anyone else, and the gate is a
/// property of what the repository holds — but it is a hole, and the moment the file is added it
/// closes. `git add -N` (intent-to-add, no content staged) is enough to bring it into scope, which
/// is exactly how `the_scope_is_git_tracked_files_not_the_filesystem` proves both poles below.
fn tracked_rs_under_src() -> BTreeSet<String> {
    tracked_rs_in(&repo_root())
}

/// Parameterised on the root for the same reason `scan_tree` is: the tooth
/// (`teeth::the_scope_is_git_tracked_files_not_the_filesystem`) drives THIS oracle over a real
/// throwaway git repo rather than a reimplementation of it.
fn tracked_rs_in(root: &Path) -> BTreeSet<String> {
    let out = std::process::Command::new("git")
        .arg("-C")
        .arg(root)
        .args(["ls-files", "-z", "--", "*.rs"])
        .output()
        .expect("LAW1 SCOPE ORACLE: `git ls-files` could not be run; refusing to scan an unbounded filesystem tree");
    assert!(
        out.status.success(),
        "LAW1 SCOPE ORACLE: `git ls-files` exited {}: {}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    let set: BTreeSet<String> = String::from_utf8_lossy(&out.stdout)
        .split('\0')
        .filter(|s| !s.is_empty())
        .map(|s| s.replace('\\', "/"))
        .collect();
    assert!(
        !set.is_empty(),
        "LAW1 SCOPE ORACLE: `git ls-files -- *.rs` returned NOTHING. This repository has \
         thousands of tracked .rs files, so an empty answer means the oracle is broken, not \
         that the tree is empty. Refusing to report a green ledger from a scope of zero."
    );
    set
}

fn scan_repo() -> BTreeMap<String, Counts> {
    scan_tree(&repo_root(), Some(&tracked_rs_under_src()))
}

/// Parameterised on the root so the RED path (`teeth::the_gate_goes_red_on_a_hand_written_air`)
/// exercises this exact walker over a synthetic tree instead of a reimplementation of it.
///
/// `tracked` is the allow-list described on [`tracked_rs_under_src`]. `None` means "there is no
/// git here" and is used ONLY by the synthetic-tree teeth, which build their own root in a
/// tempdir; the real scan always passes `Some`.
fn scan_tree(root: &Path, tracked: Option<&BTreeSet<String>>) -> BTreeMap<String, Counts> {
    let mut found = BTreeMap::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for e in entries.flatten() {
            let p = e.path();
            let name = e.file_name().to_string_lossy().to_string();
            if p.is_dir() {
                if SKIP_DIRS.contains(&name.as_str()) || name.starts_with('.') {
                    continue;
                }
                stack.push(p);
                continue;
            }
            if p.extension().and_then(|s| s.to_str()) != Some("rs") {
                continue;
            }
            let rel = p
                .strip_prefix(root)
                .unwrap_or(&p)
                .to_string_lossy()
                .replace('\\', "/");
            // Only compiled crate sources. `tests/` trees are a NAMED blind spot (module docs).
            if !rel.contains("/src/") {
                continue;
            }
            // …and only files the repository actually holds. See `tracked_rs_under_src`.
            if tracked.is_some_and(|t| !t.contains(&rel)) {
                continue;
            }
            let Ok(raw) = std::fs::read_to_string(&p) else {
                continue;
            };
            if !MARKERS.iter().any(|m| raw.contains(m)) {
                continue;
            }
            let c = count_sites(&raw);
            if c.authored() > 0 {
                found.insert(rel, c);
            }
        }
    }
    found
}

// ─────────────────────────────────────────────────────────────────────────────
// The ratchet. Frozen ground truth as re-measured 2026-07-25 with the widened scope,
// the fifth `assert_zero` form, the descriptor-tree dialect, and patterns no longer
// miscounted. 88 files, 1560 authored sites (494 further sites are lowering/destructuring
// and are FREE). Every entry is debt that is ALLOWED to shrink and MUST NOT grow.
//
// This was measured on a tree with several sibling lanes committing into `circuit/src` during
// the same hour, so a GREW line the day after this lands is as likely to be honest churn from
// that work as a fresh violation — read the file, then either fix it or re-print the ledger.
// ─────────────────────────────────────────────────────────────────────────────
#[rustfmt::skip]
const BASELINE: &[(&str, usize)] = &[
    // 2026-11-06: native scanner confirms zero authored sites after generated
    // solvency, caveat, DECO, membership and sovereign leaf cutovers; no slack rows.
    ("circuit-prove/src/carrier_pin_twin.rs", 6),
    ("circuit-prove/src/custom_leaf_adapter.rs", 3),
    // ⚑ THE CRATE'S ONE TEST-ONLY TOY AIR lives here, and all 8 sites are it:
    // `toy_fib_air::ToyFibAir`, the p3 uni-stark 2-column Fibonacci, `#[cfg(test)]`-gated,
    // shared by `dregg_outer_config`, `gpu_backend` and `dregg_mina_config`. It constrains
    // nothing about dregg state — a StarkConfig round-trip needs *an* AIR and it must
    // deliberately not be a real one. This row is the price of that, paid ONCE.
    ("circuit-prove/src/dregg_outer_config.rs", 8),
    ("circuit-prove/src/dsl_leaf_adapter.rs", 3),
    ("circuit-prove/src/effect_vm_p3_air.rs", 11),
    ("circuit-prove/src/factory_leaf_adapter.rs", 2), // generated tuple; only test comparisons remain
    // ── `circuit-prove/src/gpu_backend.rs` (was 8) is GONE from this ledger, 2026-07-30.
    //    Its 8 sites were a second private copy of the toy Fibonacci AIR above; the copy is
    //    deleted and `gpu_backend::tests` imports `toy_fib_air` instead, so the file now
    //    authors ZERO. The row is REMOVED rather than left at 8, because 8 sites of unused
    //    slack in a ratchet is 8 hand-authored constraints a later lane can add without the
    //    gate noticing (the same reason `descriptor_ir2.rs` was re-pinned 298 -> 283).
    //    A byproduct worth naming: the GPU/CPU byte-identity test now proves literally the
    //    same `Air` impl under both configs, so a byte difference cannot be the AIR's.
    ("circuit-prove/src/hatchery_leaf_adapter.rs", 2), // generated tuple; only test comparisons remain
    ("circuit-prove/src/joint_turn_recursive.rs", 28),
    ("circuit-prove/src/lean_lookup_air.rs", 3),
    ("circuit-prove/src/mpt_holding_leaf.rs", 8),
    // Note-spend adapter: 41 -> 0 (2026-11-06), shared Lean artifact consumer.
    // No slack row: its remaining VmConstraint matches only inspect generated IR.
    ("circuit-prove/src/private_book_bfv_terminal/fused.rs", 24),
    ("circuit-prove/src/private_graph_rewrite_cell.rs", 2),
    ("circuit-prove/src/private_preference_cell.rs", 2),
    ("circuit-prove/src/shielded/attest.rs", 11),
    // ── `circuit-prove/src/shielded/spend_circuit.rs` (was 11) is GONE from this ledger,
    //    2026-08-07 — the file is DELETED. It was the Rust-authored shielded-spend AIR
    //    (`shielded_spend_descriptor` / `shielded_spend_circuit`, width 20, PIs
    //    `[nullifier, merkle_root, value_binding]`). The deployed path stopped using it at
    //    `8c90ba1a0`, which routed `apply_shielded_transfer` through the LEAN-emitted
    //    `dregg-shielded-spend-complete-fsi2::v1`
    //    (`metatheory/Dregg2/Circuit/Emit/ShieldedSpendCompleteEmit.lean`, 557 cols, 25 PIs)
    //    and judged spends against the executor's own `note_shielded.root8()` instead of a
    //    wire-supplied `merkle_root`. What remained was a Rust AIR nothing live called.
    //    The row is REMOVED rather than zeroed: see the `gpu_backend.rs` note above for why
    //    a ledger must not carry slack for a file.
    // circuit-prove/src/shielded/wide_value_binding.rs is GONE from this ledger (was 7).
    // Dregg2/Circuit/Emit/WideValueBindingEmit.lean authors the whole AIR (byte-pinned, 29874 B)
    // and WideValueBindingRefine proves EVERY emitted constraint — including
    // legacy_join_cannot_separate_aliases, which needs no crypto: the one-felt legacy join is
    // provably blind to a v / v+p alias pair, for ANY hash. The sidecar now reads that golden
    // and proves through Plonky3HidingFriReference (the SAME create_zk_config the retired
    // prove_dsl_zk route used, so hiding is preserved); the descriptor-authoring half of the
    // file — mod col's AIR use, constant_gate, limb_recompose, u64_recompose,
    // wide_input_columns, wide_value_binding_descriptor, wide_value_binding_circuit — is deleted.
    // ── THREE MORE ROWS GONE 2026-08-07, with the spend AIR above: the whole Rust-authored
    //    shielded-spend tower is DELETED, 157 authored sites off this ledger in one cut.
    //
    //    `circuit-prove/src/shielded_spend_leaf_adapter.rs` (was 39) — existed for one purpose:
    //    splice the deleted `shielded_spend_descriptor` into a foldable leaf exposing
    //    `[nullifier, merkle_root, value_binding]`. With the descriptor gone it proves nothing.
    //
    //    `circuit-prove/src/shielded_ring_clearing_air.rs` (was 75) and
    //    `circuit-prove/src/shielded_ring_clearing_nleg_air.rs` (was 32) — the 2-leg and N-leg
    //    ring-clearing apex. Their clause (a), "each leg is a valid shielded spend", WAS the leaf
    //    adapter: `bind_leg_node` `connect`ed each leg's 3-lane claim to a leaf minted by
    //    `prove_shielded_spend_leaf_with_claim`. Delete the adapter and that clause has nothing
    //    behind it — the apex would fold whatever `RecursionOutput` a caller handed it, which is
    //    the empty-premise vacuity this repo keeps re-discovering. Keeping them was not an option
    //    that preserved a check; it only preserved the appearance of one.
    //
    //    ⚠ WHAT THIS COST, said out loud: the ring-clearing family was the DrEX rung-3 private
    //    matching silicon (`Market/ShieldedClearing.lean::shielded_ring_clears`), and its 8/8 and
    //    12/12 circuit-UNSAT teeth go with it. It was never on the deployed path (never emitted to
    //    `circuit/descriptors/`, absent from `PROVENANCE.json`, reachable only from its own
    //    `#[cfg(test)]` modules), its conservation ran over `pedTwoGen` — a coordinate ABSTRACTION
    //    of Ristretto, not the curve — and the redesign that once planned to route the deployed
    //    transfer through it (`docs/PLAN-shielded-apex-redesign-2026-07-20.md`) was superseded
    //    twice: by the Lean-emitted FWS1 substrate (`docs/DESIGN-bazaar-apex-v4.md`) and then by
    //    the FSI2 transfer cutover. RE-AUTHORING RING CLEARING IS LEAN-SIDE WORK: there is no
    //    `Emit/ShieldedRingClear*.lean` in the tree, and that absence — not these Rust files — is
    //    the open item.
    ("circuit-prove/src/zkoracle_leaf_adapter.rs", 16),
    ("circuit/src/bilateral_aggregation_air.rs", 16),
    // 5 -> 7, 2026-08-01, membership `node8` cutover. The reason, as this gate demands: NONE of
    // the 7 is authored constraint algebra. All 7 are `LeanExpr::Const` inside `#[cfg(test)]`,
    // asserting the ARITY TAG of a chip lookup read off the LEAN-EMITTED descriptor
    // (`assert_eq!(chips[i].tuple[0], LeanExpr::Const(16))`) — i.e. they READ emitted bytes to pin
    // the shape, they do not construct it. The count rose because the wide descriptor carries FOUR
    // chip lookups (three arity-16 node8 fold stages + the arity-11 blinding absorb) where the
    // retired one-felt descriptor carried two. The constraints themselves moved the other way:
    // they are authored in `metatheory/Dregg2/Circuit/Emit/BlindedMembershipWideEmit.lean` and
    // Rust only parses `blinded-membership-4ary-wide.json`.
    ("circuit/src/blinded_membership_witness.rs", 7),
    ("circuit/src/bound_presentation_witness.rs", 1),
    ("circuit/src/committed_threshold.rs", 7),
    ("circuit/src/constraint_prover.rs", 1),
    ("circuit/src/custom_leaf_lowering.rs", 64),
    ("circuit/src/delegate_descriptor.rs", 2),
    ("circuit/src/derivation_air.rs", 1),
    ("circuit/src/descriptor_by_name.rs", 1),
    // TIGHTENED 2026-07-30, 298 -> 283. `Ir2Air::Main`'s four grouped constraint blocks
    // (when_first_row / when_last_row / when_transition / every-row) collapsed into ONE shared
    // `eval_row_local_constraints` walk with a single `assert_zero`, which `Ir2UniAir` also calls
    // — so the row-local algebra now has exactly one interpreter instead of two. The row is
    // re-pinned to the measurement rather than left at its old allowance: 15 sites of unused slack
    // in a ratchet is 15 hand-authored constraints a later lane can add without the gate noticing.
    //
    // ⚑ RE-PINNED 2026-07-31, 283 -> 287. ORIGIN: `81ee5492d` (2026-07-30 20:04, the last-row
    // anchor-forge flag day), which is where this gate went RED and stayed red for a day. The
    // four sites are the four arms of the `window_body_as_local` that commit added:
    //     WindowExpr::Loc(c)      => LeanExpr::Var(*c)
    //     WindowExpr::Const(k)    => LeanExpr::Const(*k)
    //     WindowExpr::Add(a, b)   => LeanExpr::Add(..)
    //     WindowExpr::Mul(a, b)   => LeanExpr::Mul(..)
    // WHY THIS IS NOT AIR: it is the TRANSPORT class (module docs). The Lean emitters lower a
    // row-local body TWO ways that denote the same polynomial over the same columns —
    // `Base(Gate(b))` on the transition domain, `WindowGate { b, on_transition: false }` on the
    // whole domain — and that flag day moved 6923 gates to the second spelling. This function
    // reads the second back as the first so `row_local_body` can hand every witness-side decoder
    // one shape. Operator, arity and columns are all fixed by the node destructured a character
    // earlier; no algebra ORIGINATES here, which is this gate's own authoring-vs-lowering test.
    // The classifier scores it `Construct` only because `WindowExpr` is not in `IR_TYPES`, so the
    // arm counts +1 authored and +0 lowering. Pinned to the measurement, not to slack.
    // LOWERED 287 -> 285 on 2026-08-01: the `Ir2Air::MapAbsent` arm — the live in-circuit
    // double-spend gate, reached through `noteSpendVmDescriptor2R24`'s `nullifierFreshOp` — was
    // DELETED and replaced by `Ir2Air::LeanTable`, which interprets a Lean emission
    // (`Dregg2/Circuit/Emit/MapAbsentTableEmit.lean` -> `circuit/descriptors/table-airs/
    // dregg-ir2-map-absent-v1.json`) instead of authoring the algebra. This is the direction of
    // the law; the row moves DOWN with it so the retired algebra cannot quietly come back.
    // `circuit/src/table_air.rs`, the new decoder, scores ZERO and therefore has no row at all.
    // LOWERED 285 -> 281 on 2026-08-01 (same day, second pass): the `Ir2Air::ByteTable` arm — the
    // shared `[0,16)` limb table every range check in IR-v2 bottoms out in — was DELETED and
    // replaced by a second `Ir2Air::LeanTable` instance (`Dregg2/Circuit/Emit/ByteTableEmit.lean`
    // -> `circuit/descriptors/table-airs/dregg-ir2-byte-v1.json`). The arm's two filtered
    // `assert_zero`s and its `table_entry` leg are gone; the interpreter gained a `RowSel` factor
    // and a `BusOp::Provide` case, which are lowering, not authoring.
    // LOWERED 281 -> 265 on 2026-08-01 (third pass): the `Ir2Air::Memory` arm — the flat memory OP
    // LOG, i.e. the positional serial chain, the read discipline, the serial-gap range check, both
    // `ir2_mem_check` Blum legs and the `ir2_mem_addrs` closure query — was DELETED and replaced by
    // a fourth `Ir2Air::LeanTable` instance (`Dregg2/Circuit/Emit/MemoryTableEmit.lean` ->
    // `circuit/descriptors/table-airs/dregg-ir2-memory-v1.json`). The `Memory` VARIANT is gone from
    // the enum entirely, not just its body. ⓘ Two bus-name constants (`BUS_MEM_CHECK`,
    // `BUS_MEM_ADDRS`) went with it: their only readers were the `Memory` and `MemBoundary` arms
    // and both are Lean-authored now. The `MEM_*` COLUMN offsets did NOT go — the witness producer
    // is the last thing in Rust that knows what column 3 means, so it writes its row BY NAME.
    // LOWERED 265 -> 260 on 2026-08-01 (fourth pass): the `Ir2Air::UMemBoundaryCohort` arm — the
    // width-9 single-row universal boundary — was DELETED and replaced by a fifth
    // `Ir2Air::LeanTable` instance (`Emit/UMemBoundaryCohortTableEmit.lean` ->
    // `dregg-ir2-umem-boundary-cohort-v1.json`). The VARIANT is gone from the enum. The `UBC_*`
    // column offsets did NOT go dead and are not deleted: they now back a compile-time assertion
    // (`THE_COHORT_IS_THE_GENERAL_PREFIX`) that the cohort layout IS the general boundary's
    // 9-column prefix, which is what licenses `build_traces` writing one by-name prefix for both.
    // LOWERED 260 -> 251 on 2026-08-01 (fifth pass): the `Ir2Air::UMemBoundary` arm — the width-38
    // GENERAL universal boundary, i.e. the domain-major lexicographic strict-increase comparator
    // over full-felt keys that establishes `Nodup` — was DELETED and replaced by a sixth
    // `Ir2Air::LeanTable` instance (`Emit/UMemBoundaryTableEmit.lean` ->
    // `dregg-ir2-umem-boundary-v1.json`). Its VARIANT is gone from the enum too, so both universal
    // boundary forms are now Lean-authored. ⓘ The `UB_*` column offsets did NOT go dead: the
    // witness producer writes the shared nine-column prefix BY NAME, and `UBC_*` back the
    // compile-time `THE_COHORT_IS_THE_GENERAL_PREFIX` assertion that the cohort layout IS that
    // prefix (`UBC_WIDTH == UB_KEY_HI4`).
    // LOWERED 251 -> 236 on 2026-08-01 (sixth pass): the `Ir2Air::UMemory` arm — the OP LOG of the
    // ONE Blum multiset over `Domain × κ`, i.e. five booleans, the real prefix, the positional
    // serial chain, a read discipline over BOTH components of the `Option` cell, canonical-`none`
    // on both images, the serial-gap range check, the NULLIFIER insert-only tooth and the four
    // `ir2_umem_log`/`ir2_umem_check`/`ir2_umem_addrs` legs — was DELETED and replaced by a seventh
    // `Ir2Air::LeanTable` instance (`Emit/UMemoryTableEmit.lean` -> `dregg-ir2-umemory-v1.json`).
    // The VARIANT is gone from the enum. ⓘ Two bus-name constants (`BUS_UMEM_CHECK`,
    // `BUS_UMEM_ADDRS`) went with it — their only readers were this arm and the two universal
    // boundary arms, all three Lean-authored now — exactly as `BUS_MEM_CHECK`/`BUS_MEM_ADDRS` did
    // in the third pass. The `UM_*` COLUMN offsets did NOT go: the witness producer now writes its
    // row BY NAME through them, because it is the last thing in Rust that knows what a column means.
    // LOWERED 236 -> 204 on 2026-08-02 (seventh pass): the `Ir2Air::MapOps` arm — the map
    // RECONCILIATION table, i.e. the row guard and op membership, the AAFI selector's three pins,
    // the read discipline, 32 direction booleans across TWO independent paths, the pointer-bracket
    // range block (three canonical splits + two lexicographic comparators) and FIVE node8 Merkle
    // folds totalling 84 chip legs — was DELETED and replaced by an eighth `Ir2Air::LeanTable`
    // instance (`Emit/MapOpsTableEmit.lean` -> `dregg-ir2-map-ops-v1.json`, 331 KB, the largest of
    // the eight). The VARIANT is gone from the enum, so `Ir2Air` is now Main / Chip / ChipState16 /
    // LeanTable / ExactPublicTable.
    // ⓘ SEVEN helpers went with it, and TWO of them were ALREADY DEAD AT HEAD: `eval_canon_decomp`
    // and `eval_lex_lt` (the UNCOUNTED canonical-split and comparator emitters) lost their last
    // caller in the `Ir2Air::MapAbsent` cutover on 2026-08-01 and were left standing — 20 of the 32
    // sites this pass retires are theirs and the three GATE-COUNTED twins'. The rest are
    // `map_group8`, `node8_lookup_tuple`, `map_log_tuple`, `map_leaf_input_cols` and `KEY_HI_BASE`.
    // A ratchet counts what is THERE, not what runs, so dead Rust-authored algebra scores exactly
    // like live Rust-authored algebra — which is the correct behaviour and is why they are deleted
    // rather than left as harmless.
    // The `MAP_*` COLUMN offsets did NOT go: the witness producer writes its row BY NAME through
    // them, because it is the last thing in Rust that knows what a column means.
    // ⚑ RE-PINNED 2026-08-02, 204 -> 180: the `Ir2Air::Chip | Ir2Air::ChipState16` arm — the
    // LARGEST hand-written arm in the file, ~280 lines of arity/selector/seeding/output algebra
    // plus the inline call to `poseidon2_permute_expr_lanes`'s 352 constraints — was DELETED and
    // replaced by two more `Ir2Air::LeanTable` instances (`Emit/ChipTableEmit.lean` +
    // `Emit/Poseidon2RoundGates.lean` -> `dregg-ir2-chip{,-state16}-v1.json`, 159 KB each). BOTH
    // VARIANTS are gone from the enum, so `Ir2Air` is now Main / LeanTable / ExactPublicTable —
    // three arms, one of which is the interpreter and one of which is the last hand-written one.
    // ⓘ `BUS_FACT` and `WindowExpr::degree` went with it (their only readers were in that arm), and
    // `max_constraint_degree` lost its hardcoded `Some(7)`: the chip's degree now comes out of the
    // emitted definition list through `LeanTableAir::def_degrees`, and `ir2_degree_budget` is
    // UNCHANGED because sharing is a change of representation, not of degree.
    // ⚑ RE-PINNED 2026-08-02, 180 -> 179: the `Ir2Air::ExactPublicTable` arm — the ELEVENTH AND
    // LAST hand-written table AIR in this file, and the smallest (one `assert_zero` pinning a
    // committed capacity column to a preprocessed one, plus one `table_entry` leg) — was DELETED
    // and replaced by an `Ir2Air::LeanTable` walking a Lean-emitted FAMILY
    // (`Emit/ExactPublicTableEmit.lean` -> `dregg-ir2-exact-public-v1.json`, 64 members, one per
    // declared tuple arity). The VARIANT is gone from the enum.
    // ⚑ **SO `Ir2Air` IS NOW `Main | LeanTable`, and that is the point of the number rather than
    // the number itself.** One arm interprets the MAIN descriptor and one interprets a
    // Lean-authored TABLE; there is no arm of that enum where a constraint can be written, so law
    // #1's failure mode — "the Rust AIR crate is right there, every step compiles" — has no entry
    // point on the IR-v2 path at all, and a new shared table is an EMISSION rather than a variant.
    // ⓘ The delta is ONE because the arm was one `assert_zero`; the eleven ports together moved
    // this row 287 -> 179. What the last one cost was in the IR, not in the constraint: a `prep`
    // expression leaf reading a SECOND (verifier-recomputed) column space, its own declared
    // `prep_width` bound, and a schema rather than a table — `TableAirIR` §7, all four items.
    // ⓘ `exact_public_bus_name` did NOT go dead and did not shrink this row: it keys on the ARITY
    // now (`ir2_exact_public_a{n}`) with the table id moved into the served tuple, because an
    // artifact cannot know a table id — which is what made a per-arity Lean-emitted family
    // possible. `Ir2Air::Main`'s QUERY side still calls it, so the name is a genuine coupling
    // between this file and the Lean author, exactly like `ir2_p2` / `ir2_p2_narrow`.
    //
    // ⚑ RE-PINNED 2026-08-06, 179 -> 198. NOT ONE FLAG DAY — FOUR COMMITS OVER THREE DAYS, and the
    // attribution this repair inherited (`c08967ca2`, "the challenges/ChalGate flag day") is wrong
    // twice: that commit touches ONLY `perf/src/lib.rs` (three `challenges: 0` initializers) and
    // grew this file by ZERO. Measured by scoring `git show <rev>:<file>` with this file's own
    // classifier, which is what the `GREW` row's recipe is for:
    //
    //   17b138e1f 179 -> f2fc52c39 185 -> 46493491d 188 -> dc5abe4ab 191 -> 72e86fc8d 198
    //
    // The nineteen are FOUR objects, and only ONE of them is polynomial algebra:
    //
    //  * **10 `#[cfg(test)]` sites**, in two tests. `f2fc52c39` (+6) added
    //    `ir2_three_range_widths_coexist_and_prove` — a SYNTHETIC three-table descriptor
    //    (3 `VmConstraint2::Lookup` + 3 `LeanExpr::Var`) built to show a 29/16/8-bit range trio
    //    coexists; nothing emits it and nothing should. `72e86fc8d` (+4) added
    //    `parses_lean_proof_bind_golden` — 4 `LeanExpr::{Var,Const}` built as the EXPECTED half of
    //    `assert_eq!` against a `proof_bind` DECODED FROM the Lean golden, i.e. a differential,
    //    which is the law working. Counted because `#[cfg(test)]`-inside-`src/` is counted on
    //    purpose (module docs); the row moves, the rule does not.
    //  * **5 `assert_zero(AB::Expr::ONE)` — a constant-FALSE REFUSAL, not a constraint.** Three in
    //    the `ProofBind` arm (`commit.len() != vk.len()`, and either declared pin shorter than the
    //    vector it pins — `72e86fc8d`), two for the challenge leaf (`dc5abe4ab`: the short
    //    `permutation_randomness()` backstop in `Ir2Air::Main`, and `Ir2UniAir`'s unreachable
    //    `ChalGate` arm). `1 = 0` names no column and no coefficient; it is `return Err` spelled in
    //    the AIR, under an admission door that already refused the same shape. ⚑ NOT auto-detected,
    //    for the reason the TRANSPORT class is not: a syntactic exemption in the LAW gate is worth
    //    less than a number that is right for a boring reason — and the incentive it would create,
    //    "delete the backstop to make the gate green", is the one this repo can least afford.
    //  * **1 `VmConstraint2::ChalGate(..)` in `parse_constraint2`** — the JSON DECODER's `chal_gate`
    //    arm (`dc5abe4ab`). Pure TRANSPORT: the node is being rebuilt from bytes Lean emitted. Its
    //    three siblings in the same `match` (`WindowGate`, `ProofBind`, the `v1tag` `Base`) are
    //    already inside the 179, so this is growth of an ALREADY-COUNTED class, not a new one.
    //  * **3 genuine congruence bodies** — the `VmConstraint2::ProofBind` arm of
    //    `eval_row_local_constraints` (`46493491d`): `guard·(guard − 1)`, `guard·(vk − vk_pin)`,
    //    `guard·(commit − bound)`. This is the ONE that is polynomial algebra, and it is the
    //    interpreter of an IR NODE whose meaning is `DescriptorIR2.ProofBind.holdsAt` in Lean —
    //    the same act as rendering `VmConstraint::PiBinding{row,col,pi}` as `local[col] − pv[pi]`,
    //    which has ridden the shared `assert_zero` tail inside this row since the beginning.
    //    ⚑ It scores 3 rather than 0 only because the arm emits a VECTOR of bodies and therefore
    //    cannot use that shared tail: dialect (1) counts syntactic call SITES and has no
    //    authoring-vs-lowering classifier at all, so a node kind whose denotation is `1 + n + n`
    //    congruences scores per-site while one whose denotation is a bus send scores zero.
    //    ⚠ And what it BOUGHT is why it is not being undone: before `3f4d703ae` this kind denoted
    //    NOTHING in either language — `.proofBind` sat in the `continue` list and emitted no bus
    //    interaction either — so a row's claim about its sub-proof was unconstrained. Deleting
    //    these three to lower a count would re-open that.
    ("circuit/src/descriptor_ir2.rs", 198), // 165 of 198 #[cfg(test)]
    // ⚑ RE-PINNED 2026-08-06, 48 -> 49. ORIGIN: `dc5abe4ab` (the challenge leaf). ONE site, and it
    // is the canonical (binary) DECODER's tag-7 arm — `7 => Ok(VmConstraint2::ChalGate(..))` at
    // `descriptor_ir2_canonical.rs:1018`. The TRANSPORT class again, and the exact twin of the JSON
    // parser's arm above: the ENCODER's `ChalGate` at :593 is a match pattern and stays free. No
    // polynomial, no column, no coefficient originates here — the node is rebuilt from bytes.
    ("circuit/src/descriptor_ir2_canonical.rs", 49),
    ("circuit/src/direct_logic_frontend.rs", 3),
    ("circuit/src/dsl/accumulator.rs", 10),
    ("circuit/src/dsl/cap_membership.rs", 4),
    ("circuit/src/dsl/committed_threshold.rs", 7),
    ("circuit/src/dsl/derivation.rs", 58),
    ("circuit/src/dsl/descriptors.rs", 7),
    ("circuit/src/dsl/dfa_routing.rs", 9),
    ("circuit/src/dsl/dsl_p3_air.rs", 25),
    ("circuit/src/dsl/fold.rs", 15),
    ("circuit/src/dsl/garbled.rs", 14),
    ("circuit/src/dsl/note_spending.rs", 23),
    ("circuit/src/dsl/openable_fields_insertion.rs", 6),
    ("circuit/src/dsl/predicates/arithmetic.rs", 42),
    ("circuit/src/dsl/predicates/base.rs", 34),
    ("circuit/src/dsl/predicates/compound.rs", 20),
    ("circuit/src/dsl/predicates/relational.rs", 31),
    ("circuit/src/dsl/temporal_absence.rs", 4),
    ("circuit/src/effect_action_air.rs", 3),
    ("circuit/src/effect_vm/authority_digest_weld.rs", 11),
    ("circuit/src/effect_vm/bare_floor_refuse_weld.rs", 11),
    ("circuit/src/effect_vm/burn_avail_weld.rs", 1),
    ("circuit/src/effect_vm/carrier_floor_weld.rs", 11),
    ("circuit/src/effect_vm/discharge_weld.rs", 5),
    // 2 -> 3, 2026-11-07, classifier repair (match guards are expressions). No new algebra: the
    // third site is `LeanExpr::Var(ESCROW_SEL_COL)` on the right of `==` in a match-arm GUARD
    // inside `#[cfg(test)]` (:247), which READS the Lean-emitted escrow gates to compare them
    // byte for byte. The old classifier skipped it as part of the arm header; guards construct.
    ("circuit/src/effect_vm/satisfaction_weld.rs", 3),
    ("circuit/src/effect_vm/transfer_avail_weld.rs", 1),
    ("circuit/src/effect_vm/transfer_fee_avail_weld.rs", 1),
    ("circuit/src/effect_vm/vault_weld.rs", 5),
    // ⚑ RE-PINNED 2026-07-31, 18 -> 24. ORIGIN: `7da5ac1ea` ("fields nonet + cap-open TB").
    // ALL SIX new sites are inside `#[cfg(test)]` — the file's cfg-test subset went 2 -> 8 while
    // its production half did not move — and they are two objects:
    //   * 2 x `LeanExpr::Var(col)` built as the EXPECTED half of an `assert_eq!` against the
    //     `proof_bind` READ OUT OF the emitted descriptor (`d.constraints.iter().find_map(..)`).
    //     That is a differential: a Rust expectation compared against a Lean emission in the same
    //     file, which is the law working, not a constraint.
    //   * `VmConstraint2::ProofBind(ProofBindSpec { guard: Const(1), commit: Var, vk: Var })`
    //     plus its 3 leaves — a SYNTHETIC descriptor fixture handed to `custom_commit_version` to
    //     prove that classifier fails CLOSED on a 12-slot exposure window and on a bare anchor
    //     pair with no declaration. It is an input to a Rust decider, never seen by a prover, and
    //     it decides no acceptance.
    // Neither belongs in Lean and neither is AIR. They are COUNTED because `#[cfg(test)]`-inside-
    // `src/` is counted on purpose (module docs), and that strictness is not being relaxed to
    // absorb them — the row moves, the rule does not.
    // ⚑ RE-PINNED 2026-08-06, 24 -> 26. ORIGIN: `72e86fc8d` ("the recursion seam ties the whole
    // digest, not a limb"). BOTH new sites are inside `#[cfg(test)]` — the file's cfg-test subset
    // went 8 -> 10 while its production half did not move — and both are ONE object:
    // `rotation_caveat_layout_matches_lean` asserts the DEPLOYED member's `proof_bind` lane 0 is
    // the anchor column the rotated layout names, as
    // `assert_eq!((commit.first(), vk.first()), (Some(&LeanExpr::Var(PARAM_BASE + …)), …))`. The
    // two `LeanExpr::Var`s are the EXPECTED half of a differential against a descriptor READ OUT
    // OF the deployed bytes; the widening from one felt to eight lanes is what turned a scalar
    // field into a vector and therefore a `.first()` comparison into two. Same class, same reason,
    // and the same answer as this row's 2026-07-31 block: neither is AIR, and the strictness is
    // not relaxed to absorb them.
    ("circuit/src/effect_vm_descriptors.rs", 26),
    ("circuit/src/lean_descriptor_air.rs", 47),
    ("circuit/src/membership_descriptor_4ary.rs", 1),
    // 2026-11-06: 247ebb4b9 moves binary membership to the Lean-generated artifact.
    // Native integration scan at f2b9e86f: 0 authored / 2 pattern sites; no slack row.
    ("circuit/src/merkle_types.rs", 4),
    // Note-spend core: 41 -> 0 (2026-11-06), noteSpendLeafDescFixed authors the AIR.
    // Witness generation and production-evaluator mutants construct no constraints.
    ("circuit/src/plonky3_prover.rs", 7),
    ("circuit/src/plonky3_recursion.rs", 6),
    // ⚑ THE LAW WON HERE (2026-08-06). `circuit/src/presentation.rs`'s row was 1 — the closure
    // `eval: Box::new(move |row, _, public_inputs| row[i] - public_inputs[i])` in
    // `impl Air for PresentationAir::constraints`, dialect (2). That impl authored NINETEEN
    // constraints from that one site and every one of them was IDENTICALLY ZERO: its own
    // `generate_trace` returned `public_inputs = row.clone()`, so each evaluated `0 - 0`. It also
    // had no caller of any kind (nothing in the workspace ever handed a `PresentationAir` to
    // `ConstraintValidator` or `TraceSummary`). It is DELETED, not baselined, and the family's real
    // AIR is the Lean emission it was transcribed into —
    // `Dregg2/Circuit/Emit/PresentationEmit.lean` -> `dregg-presentation-freshness::summary-v1`,
    // live in `wire::server::StarkVerifier`. The row is GONE, which the scan requires: a file with
    // zero authored sites never enters `found`, so no baseline line may claim it has one.
    // ⚑ RE-PINNED 2026-08-06, 38 -> 24. `circuit/src/whole_image_fold.rs` lost its two BOUND
    // variants (`whole_image_fold_bound_descriptor` + `..._bound_mem_descriptor`, their witness
    // builders and prove/verify pairs) — 14 dialect-(4) sites, the `VmConstraint2::{UMemOp, MemOp}`
    // specs and their `LeanExpr` leaves. They are deleted rather than emitted from Lean because
    // they were not doing anything to emit: the boundary table they bound against is
    // prover-supplied and is verified against an EMPTY public-value vector (`verify_vm_descriptor2`
    // gives `pvs` to the MAIN instance only), so their public inputs were byte-identical to the
    // unbound chip's and every boundary tooth refused at PROVE time. The surviving 24 are the
    // unbound fold chip, whose teeth ARE verifier-visible and whose Lean correspondent
    // (`Dregg2.Circuit.WholeImageFoldRealization.wholeBoundaryFold8`) exists — it remains DEBT,
    // just 14 sites less of it.
    ("circuit/src/whole_image_fold.rs", 24),
    // ── OUTSIDE the old two-directory scope: the surface this gate could not see ──
    ("constraint-lowering/src/lib.rs", 8),
    ("dregg-doc/src/ci_assurance.rs", 1),
    ("dregg-dsl-differential/src/plonky3_runner.rs", 10),
    ("dregg-dsl-runtime/src/composition.rs", 13),
    ("game-turn-slice/src/compiler.rs", 6),
    // ── THE LAW WON HERE (2026-07-25). `param-compose/src/air.rs` (19 sites) and
    //    `param-compose/src/builder.rs` (9) — the largest hand-written Rust AIR in the tree,
    //    1028 lines — are DELETED. Dregg2/Circuit/Emit/ParamComposeEmit.lean authors the whole
    //    AIR and byte-pins the wire, all 18 shapes the corpus exercises are #guard-pinned, and
    //    param-compose's own test corpus now rides the emitted descriptor. Their rows are gone
    //    from this BASELINE in that same change (the stale-entry check below requires it).
    ("perf/src/lib.rs", 28),  // ⚑ a hand-built VmConstraint2::{MapOp,UMemOp} descriptor.
    // ⚑ RE-PINNED 2026-07-31, 2 -> 3. ORIGIN: `912b13375` ("cap-remove: the AIR binding is
    // intact — four teeth had gone blind to it six hours earlier"). One `#[cfg(test)]` site:
    // `VmConstraint2::Base(VmConstraint::Gate(row_local_body(k)?.into_owned()))`, which re-
    // expresses the DEPLOYED descriptor into the other row domain and requires the cap-root weld
    // decoder to give the same 16 answers either way — the tooth for the blindness `81ee5492d`
    // caused. The body is TRANSPORTED verbatim out of the Lean-emitted constraint (same class as
    // `descriptor_ir2::window_body_as_local` above); the only thing Rust picks is the wrapper.
    // Net +1 and not +2 because that same commit turned an authored `LeanExpr::Var` into a
    // `matches!` pattern, which the classifier correctly stopped counting.
    ("sdk/src/full_turn_proof.rs", 3),
    ("tests/src/dsl_pipeline.rs", 8),
    ("turn/src/executor/membership_verifier.rs", 2),
    ("turn/src/umem.rs", 8),
];

/// Dialect (5). The law names `air_accepts` predicates explicitly, so they are ledgered by
/// name with a reason rather than folded into a count. A NEW one fails.
#[rustfmt::skip]
const AIR_ACCEPTS_LEDGER: &[(&str, &str)] = &[
    ("circuit/src/lean_descriptor_air.rs",
     "test-module ORACLE: it does not decide acceptance itself, it calls prove_vm_descriptor + \
      verify_vm_descriptor and treats a prover panic as reject. Delegation, not authorship."),
    // `param-compose/src/builder.rs`'s `air_accepts` — a real hand-authored acceptance predicate
    // over a hand-authored Rust AIR, paired with tamper() for forgery tests — is DELETED with the
    // AIR (2026-07-25), so it needs no ledger line. It was retired exactly as this ledger demanded:
    // with the AIR, not separately.
    // `entity-compose/src/lib.rs` — RETIRED 2026-07-25. Its line claimed the crate "rebuilds the
    // param-compose AIR and calls ITS air_accepts". Both halves are now false: entity-compose defines
    // no `air_accepts` at all, and it references neither `param_compose::air` nor `::builder` — it
    // proves the Lean-emitted descriptor directly. The line survived a lane's deletion because THIS
    // LEDGER HAD NO STALE-CHECK: the test below only hunted NEW entries, so a row describing an
    // object that no longer exists passed green while lying. That check now exists (see
    // `stale` in `law1_no_new_rust_authored_air_accepts`), which is why this row could be removed
    // instead of quietly rotting.
];

fn print_baseline(found: &BTreeMap<String, Counts>) {
    println!("// LAW1 baseline, machine-printed:");
    for (f, c) in found {
        let note = if c.cfg_test > 0 {
            format!("  // {} of {} #[cfg(test)]", c.cfg_test, c.authored())
        } else {
            String::new()
        };
        println!("    (\"{f}\", {}),{note}", c.authored());
    }
    println!(
        "// {} files, {} authored sites ({} of them inside #[cfg(test)], counted all the same), \
         {} lowering sites (free)",
        found.len(),
        found.values().map(|c| c.authored()).sum::<usize>(),
        found.values().map(|c| c.cfg_test).sum::<usize>(),
        found.values().map(|c| c.ir_lowered).sum::<usize>(),
    );
}

/// The site listing a `GREW` row carries, so the reader can find WHICH sites moved instead of
/// re-deriving them.
///
/// ⚑ WHY THIS EXISTS. This gate was red from `81ee5492d` (2026-07-30 20:04) for a full day with
/// nobody owning it, and the reason is in the old message: `283 -> 287` is a file and a delta and
/// nothing else. Two lanes hit it, investigated, and each correctly concluded "not mine" —
/// because attributing four sites inside 287 meant re-compiling this file's classifier standalone
/// and walking 40 revisions. That is not a thing a lane doing unrelated work will do, so the red
/// went unowned. A ratchet that cannot say what moved does not get repaired; it gets stepped over.
fn grew_site_report(root: &Path, rel: &str) -> String {
    let Ok(raw) = std::fs::read_to_string(root.join(rel)) else {
        return String::new();
    };
    let mut ex = Vec::new();
    count_sites_explained(&raw, Some(&mut ex));
    ex.retain(|r| r.site == Site::Construct);

    // By-kind, commonest first. A growth of a handful is almost always a SINGLETON variant, so
    // the tail of this histogram is usually the answer on its own.
    let mut hist: BTreeMap<&str, usize> = BTreeMap::new();
    for r in &ex {
        *hist.entry(r.what.as_str()).or_default() += 1;
    }
    let mut kinds: Vec<(&str, usize)> = hist.into_iter().collect();
    kinds.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));

    let mut s = String::new();
    s.push_str(
        "\n       -> AUTHORED sites by kind. Diff this against the SAME listing at the baseline's\n          \
         revision (recipe below) and the moved sites fall out; a lone singleton usually IS them:\n          ",
    );
    s.push_str(
        &kinds
            .iter()
            .map(|(k, n)| format!("{k} x{n}"))
            .collect::<Vec<_>>()
            .join(", "),
    );
    s.push('\n');
    if ex.len() <= 40 {
        s.push_str("       -> and where every one of them is:\n");
        for r in &ex {
            s.push_str(&format!(
                "          {:>6}  {}{}\n",
                r.line,
                r.what,
                if r.cfg_test { "   [#[cfg(test)]]" } else { "" }
            ));
        }
    }
    s.push_str(&format!(
        "       -> full listing, authored AND lowering:\n          \
         LAW1_EXPLAIN={rel} cargo test -p dregg-circuit-prove --test law1_enforcement_gate -- --nocapture\n       \
         -> which COMMIT grew it, WITHOUT a bisect (LAW1_EXPLAIN takes an absolute path):\n          \
         for r in $(git log --format=%h -40 -- {rel}); do git show $r:{rel} > /tmp/at-rev.rs; \\\n            \
         echo -n \"$r \"; LAW1_EXPLAIN=/tmp/at-rev.rs cargo test -p dregg-circuit-prove \\\n            \
         --test law1_enforcement_gate -- --nocapture 2>/dev/null | grep -m1 'authored='; done\n"
    ));
    s
}

/// The ratchet itself: a NEW file fails, a listed file that GREW fails, shrinking is always
/// allowed (that is the direction of the law), and a ledger line for a file that no longer
/// exists fails so the debt cannot be inflated by rot. Parameterised so the teeth below run
/// THIS code against a synthetic tree.
fn ratchet(
    root: &Path,
    found: &BTreeMap<String, Counts>,
    baseline: &[(&str, usize)],
) -> Vec<String> {
    let base: BTreeMap<&str, usize> = baseline.iter().map(|(f, n)| (*f, *n)).collect();
    let mut violations = Vec::new();
    for (rel, c) in found {
        let n = c.authored();
        match base.get(rel.as_str()) {
            None => violations.push(format!(
                "  NEW Rust-authored constraints: {rel} ({n} sites: {} symbolic, {} closure, {} IR{})\n\
                      -> EMIT IT FROM LEAN. Do not add it to the baseline.\n\
                      -> If the sites are `#[cfg(test)]`-only they are STILL a hand-written Rust AIR, and the\n\
                         remedy is still not a baseline row: reuse the crate's one shared test AIR\n\
                         (`circuit-prove/src/dregg_outer_config.rs::toy_fib_air`) or delete the copy.",
                c.symbolic, c.closures, c.ir_constructed, c.cfg_test_note()
            )),
            Some(allowed) if n > *allowed => violations.push(format!(
                "  GREW: {rel} ({allowed} -> {n} sites)\n       \
                 -> new hand-authored constraints. Emit them from Lean.\n       \
                 -> if they are NOT constraint algebra, the row moves only WITH a written reason\n          \
                 naming the origin commit and why each site is not AIR. Never a silent re-print.{}",
                grew_site_report(root, rel)
            )),
            _ => {}
        }
    }
    for (f, n) in baseline {
        if !root.join(f).exists() {
            violations.push(format!(
                "  STALE BASELINE ENTRY: {f} ({n} sites) no longer exists.\n\
                      -> the law WON here. Delete this line from BASELINE."
            ));
        }
    }
    violations
}

#[test]
fn law1_no_new_rust_authored_constraints() {
    if let Ok(f) = std::env::var("LAW1_EXPLAIN") {
        // `join` lets an ABSOLUTE path win, which is what makes `git show <rev>:<file>` scorable.
        let raw = std::fs::read_to_string(repo_root().join(&f)).expect("LAW1_EXPLAIN path");
        let mut ex = Vec::new();
        let c = count_sites_explained(&raw, Some(&mut ex));
        // `authored=` is the greppable field: the origin-hunting loop in a GREW row reads it.
        println!(
            "{f}: authored={} (symbolic {}, closure {}, IR {}), lowering {}, cfg_test {}",
            c.authored(),
            c.symbolic,
            c.closures,
            c.ir_constructed,
            c.ir_lowered,
            c.cfg_test
        );
        for r in ex {
            println!(
                "  {:>6}  {}  {}{}",
                r.line,
                if r.site == Site::Construct {
                    "AUTHORED "
                } else {
                    "lowering "
                },
                r.what,
                if r.cfg_test { "   [#[cfg(test)]]" } else { "" }
            );
        }
    }
    let found = scan_repo();
    if std::env::var("LAW1_PRINT_BASELINE").is_ok() {
        print_baseline(&found);
    }
    let violations = ratchet(&repo_root(), &found, BASELINE);
    assert!(
        violations.is_empty(),
        "\n\nARCHITECTURAL LAW #1 VIOLATED — Rust must author NO constraints.\n\n{}\n\n\
         See this file's module docs for how to emit from Lean instead. Re-print the ledger with\n\
         LAW1_PRINT_BASELINE=1 cargo test -p dregg-circuit-prove --test law1_enforcement_gate -- --nocapture\n",
        violations.join("\n")
    );
}

/// `fn air_accepts` / `fn <something>_air_accepts` — a DEFINITION, not a call site and not
/// a test named after one (`fn air_accepts_valid_ring3` is a test, and does not count).
fn defines_air_accepts(code: &str) -> bool {
    let b = code.as_bytes();
    let mut i = 0usize;
    while let Some(p) = find(b, i, b"fn ") {
        if !prev_is_ident(b, p) {
            let s = skip_ws(b, p + 3);
            let e = ident_at(b, s);
            let name = std::str::from_utf8(&b[s..e]).unwrap_or("");
            if name == "air_accepts" || name.ends_with("_air_accepts") {
                return true;
            }
        }
        i = p + 3;
    }
    false
}

#[test]
fn law1_no_new_rust_authored_air_accepts() {
    let root = repo_root();
    let ledgered: Vec<&str> = AIR_ACCEPTS_LEDGER.iter().map(|(f, _)| *f).collect();
    let mut new_ones = Vec::new();
    for rel in scan_repo_all_src() {
        let Ok(raw) = std::fs::read_to_string(root.join(&rel)) else {
            continue;
        };
        if !raw.contains("air_accepts") || !defines_air_accepts(&blank_noncode(&raw)) {
            continue;
        }
        if !ledgered.contains(&rel.as_str()) {
            new_ones.push(rel);
        }
    }
    assert!(
        new_ones.is_empty(),
        "\n\nARCHITECTURAL LAW #1 VIOLATED — a Rust-authored `air_accepts` predicate.\n{}\n\n\
         The law names these explicitly: acceptance is decided by the EMITTED artifact and the prover,\n\
         never by a Rust function that re-implements the AIR. If a new one is genuinely a delegating\n\
         oracle, add it to AIR_ACCEPTS_LEDGER *with the reason*.\n",
        new_ones.join("\n")
    );

    // STALE-ENTRY CHECK. Without this the ledger passes green while LYING: a row survives the file
    // it describes, and the debt it records reads as live when the object is gone. That happened —
    // `entity-compose/src/lib.rs` sat here after the crate stopped defining `air_accepts` at all.
    // A ledger that cannot go red about its own rot is not a ledger.
    let stale: Vec<&str> = AIR_ACCEPTS_LEDGER
        .iter()
        .map(|(f, _)| *f)
        .filter(|rel| {
            match std::fs::read_to_string(root.join(rel)) {
                Ok(raw) => !defines_air_accepts(&blank_noncode(&raw)),
                Err(_) => true, // the file itself is gone
            }
        })
        .collect();
    assert!(
        stale.is_empty(),
        "\n\nSTALE AIR_ACCEPTS_LEDGER ENTRY — the law WON here, the ledger just did not notice.\n{}\n\n\
         Each listed file no longer defines `air_accepts` (or no longer exists), so its ledger line\n\
         describes an object that is not there and overstates the remaining debt. Delete the line.\n",
        stale.join("\n")
    );
}

/// Every `.rs` under a `src/` tree in scope, without the marker prefilter (the `air_accepts`
/// check has a different trigger word).
fn scan_repo_all_src() -> Vec<String> {
    let root = repo_root();
    let tracked = tracked_rs_under_src();
    let mut out = Vec::new();
    let mut stack = vec![root.clone()];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for e in entries.flatten() {
            let p = e.path();
            let name = e.file_name().to_string_lossy().to_string();
            if p.is_dir() {
                if SKIP_DIRS.contains(&name.as_str()) || name.starts_with('.') {
                    continue;
                }
                stack.push(p);
                continue;
            }
            if p.extension().and_then(|s| s.to_str()) != Some("rs") {
                continue;
            }
            let rel = p
                .strip_prefix(&root)
                .unwrap_or(&p)
                .to_string_lossy()
                .replace('\\', "/");
            // Same scope oracle as `scan_tree`: tracked-and-under-`src/`, never "on disk".
            if rel.contains("/src/") && tracked.contains(&rel) {
                out.push(rel);
            }
        }
    }
    out
}

// ─────────────────────────────────────────────────────────────────────────────
// The gate's own teeth. A gate that cannot go red is not a gate — and a gate whose
// CLASSIFIER is wrong goes red on the wrong things, which is how the previous revision
// accumulated 46 phantom violations in one lowering. These fixtures pin both directions.
// ─────────────────────────────────────────────────────────────────────────────
mod teeth {
    use super::*;

    #[test]
    fn destructuring_is_not_authoring() {
        // Every shape the LOWERINGS actually use. None of these author algebra.
        let lowering = r#"
            fn gate_body(e: &ConstraintExpr) -> LeanExpr {
                match e {
                    ConstraintExpr::Equality { col_a, col_b } => zero(),
                    ConstraintExpr::Binary { .. } => zero(),
                    ConstraintExpr::Gated { .. } if flag => zero(),
                    ConstraintExpr::Hash { .. } | ConstraintExpr::Hash2to1 { .. } => zero(),
                    _ => zero(),
                }
            }
            fn n(c: &ConstraintExpr) -> bool { matches!(c, ConstraintExpr::MerkleHash8 { .. }) }
            fn m(c: &ConstraintExpr) { if let ConstraintExpr::Squared { inner } = c { drop(inner) } }
        "#;
        let c = count_sites(lowering);
        assert_eq!(c.ir_constructed, 0, "a lowering authored nothing: {c:?}");
        assert_eq!(c.ir_lowered, 7, "all seven sites are destructuring: {c:?}");
    }

    /// The real flat-interpreter and Mina sites: tuple siblings and trailing commas are
    /// syntax inside a pattern, not constructors. These are synthetic; production stays intact.
    #[test]
    fn nested_tuple_or_and_trailing_comma_patterns_are_lowering() {
        let fixtures = [
            (
                r#"match (k, ck) {
                (VmConstraint2::Base(VmConstraint::Gate(_)), CompiledK::Body(f)) => read(f),
                (VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index }), _) => read(col),
                (VmConstraint2::Lookup(_) | VmConstraint2::MemOp(_), _,) => skip(),
            }"#,
                6,
            ),
            (
                r#"match body {
                LeanExpr::Add(l, r) => match (&**l, &**r) {
                    (LeanExpr::Var(c), LeanExpr::Const(k)) if *c == col => Some(-*k),
                    (LeanExpr::Const(k), LeanExpr::Var(c)) if *c == col => Some(-*k),
                    _ => None,
                },
                LeanExpr::Var(c) if *c == col => Some(0),
                _ => None,
            }"#,
                6,
            ),
            (
                r#"match c {
                VmConstraint2::Base(
                    VmConstraint::PiBinding { row, col, pi_index },
                ) if *pi_index == pi => Some((*row, *col)),
                _ => None,
            }"#,
                2,
            ),
            (
                r#"match (k, ck) {
                (VmConstraint2::Base(VmConstraint::Gate(_) | VmConstraint::Boundary { .. })
                    | VmConstraint2::WindowGate(_) | VmConstraint2::ChalGate(_), _,) => refuse(),
            }"#,
                5,
            ),
        ];
        for (src, expected) in fixtures {
            let c = count_sites(src);
            assert_eq!(
                c.ir_constructed, 0,
                "a pattern builds no algebra: {src} {c:?}"
            );
            assert_eq!(
                c.ir_lowered, expected,
                "every nested node is classified: {src} {c:?}"
            );
        }
    }

    /// Patterns must not swallow neighboring expressions. In particular the old blanket
    /// `matches!` / following `|` / bare `..` heuristics silently hid these constructors.
    #[test]
    fn pattern_contexts_keep_guards_scrutinees_and_rhs_constructed() {
        let fixtures = [
            (
                r#"match value {
                LeanExpr::Var(c) if predicate(LeanExpr::Const(7), *c) => LeanExpr::Var(*c),
                _ => LeanExpr::Const(0),
            }"#,
                3,
                1,
            ),
            (
                r#"matches!(LeanExpr::Const(7), LeanExpr::Const(x) if check(LeanExpr::Var(x)))"#,
                2,
                1,
            ),
            (
                r#"let result = LeanExpr::Const(1) | LeanExpr::Var(2);"#,
                2,
                0,
            ),
            (
                r#"let result = VmConstraint::Custom { values: (0..), ..base };"#,
                1,
                0,
            ),
            (
                r#"match value { const { LeanExpr::Const(1) } => accept(), _ => refuse() }"#,
                1,
                0,
            ),
            (
                r#"match value {
                LeanExpr::Var(c) => { consume(LeanExpr::Const(3)); }
                LeanExpr::Const(c) => consume(LeanExpr::Var(c)),
            }"#,
                2,
                2,
            ),
            (
                r#"let (LeanExpr::Var(a), LeanExpr::Const(b)) =
                (LeanExpr::Var(3), LeanExpr::Const(5)) else { return; };"#,
                2,
                2,
            ),
        ];
        for (src, constructed, patterns) in fixtures {
            let c = count_sites(src);
            assert_eq!(
                c.ir_constructed, constructed,
                "real construction must remain visible: {src} {c:?}"
            );
            assert_eq!(
                c.ir_lowered, patterns,
                "only pattern positions are free: {src} {c:?}"
            );
        }
    }

    #[test]
    fn nested_pattern_contexts_use_the_innermost_role() {
        let src = r#"
            matches!(match value {
                LeanExpr::Var(c) => LeanExpr::Const(c),
                _ => LeanExpr::Const(0),
            }, LeanExpr::Const(k));
            match value {
                LeanExpr::Var(c) if matches!(value, LeanExpr::Const(v)) => accept(),
                _ => refuse(),
            }
        "#;
        let c = count_sites(src);
        assert_eq!(
            c.ir_constructed, 2,
            "only the inner match RHSs construct: {c:?}"
        );
        assert_eq!(
            c.ir_lowered, 4,
            "nested match/macro patterns remain patterns: {c:?}"
        );
    }

    #[test]
    fn construction_is_authoring() {
        let authored = r#"
            fn build() -> Vec<ConstraintExpr> {
                vec![
                    ConstraintExpr::Binary { col: 3 },
                    ConstraintExpr::Polynomial { terms: t },
                    ConstraintExpr::Gated { gate: g, ..base },
                ]
            }
            fn tree() -> VmConstraint2 {
                VmConstraint2::Base(VmConstraint::PiBinding { row: VmRow::First, col: 0, pi: 1 })
            }
            fn leaf() -> LeanExpr { LeanExpr::mul(LeanExpr::Var(2), LeanExpr::Const(1)) }
        "#;
        let c = count_sites(authored);
        assert_eq!(c.ir_constructed, 7, "seven constructed IR values: {c:?}");
        assert_eq!(c.ir_lowered, 0, "nothing destructured: {c:?}");
    }

    #[test]
    fn the_fifth_assert_zero_dialect_is_visible() {
        // param-compose's actual form. The previous revision hard-coded `builder.` and saw ZERO.
        let param_compose_shaped = r#"
            fn build(b: &mut Builder) {
                b.assert_zero(&Head::lin(1, col).add_const(-1));
                b
                    .assert_zero(&Head::lin(-1, out).add_prod(1, vec![a, b]));
                self.assert_zero(&recomp);
            }
        "#;
        let c = count_sites(param_compose_shaped);
        assert_eq!(
            c.symbolic, 3,
            "three assert_zero sites on non-`builder` receivers: {c:?}"
        );
    }

    #[test]
    fn gpui_when_is_not_a_constraint() {
        // starbridge-v2's cockpit is full of `.when(cond, |el| ..)`. Without the AirBuilder
        // guard, widening the scope to the workspace would have invented hundreds of violations.
        let gpui =
            r#"fn ui(el: Div) -> Div { el.when(flag, |e| e.child(x)).when_some(o, |e, v| e) }"#;
        assert_eq!(count_sites(gpui).symbolic, 0);
        let air = r#"fn eval<AB: AirBuilder>(b: &mut AB) { b.when_transition().assert_eq(a, c); }"#;
        assert_eq!(
            count_sites(air).symbolic,
            2,
            "when_transition + assert_eq inside an AirBuilder"
        );
    }

    /// `#[cfg(test)]` ATTRIBUTES a site; it never forgives one. Both halves are pinned,
    /// because the tempting "fix" for the 2026-07-30 red was to subtract these from
    /// `authored()` — which would have made a copied Rust AIR in a `src/` file invisible
    /// exactly when the gate needed to see it.
    #[test]
    fn cfg_test_sites_are_counted_and_merely_attributed() {
        let mixed = r#"
            fn prod<AB: AirBuilder>(b: &mut AB) { b.assert_zero(x); }
            #[cfg(test)]
            mod tests {
                use p3_air::{Air, AirBuilder};
                fn toy<AB: AirBuilder>(b: &mut AB) {
                    b.assert_zero(y);
                    b.assert_eq(y, z);
                    b.push(ConstraintExpr::Binary { col: 3 });
                }
            }
        "#;
        let c = count_sites(mixed);
        assert_eq!(
            c.authored(),
            4,
            "cfg(test) sites are STILL counted as authored: {c:?}"
        );
        assert_eq!(c.cfg_test, 3, "three of the four are test-only: {c:?}");
        assert!(
            c.cfg_test_note().contains('3'),
            "the message names the split: {}",
            c.cfg_test_note()
        );

        // A `use a::{b, c};` under the attribute opens a brace that is NOT a body — if the
        // region walker took it, everything after the import would read as test-only.
        let prod_only = r#"fn f<AB: AirBuilder>(b: &mut AB) { b.assert_zero(x); }"#;
        assert_eq!(count_sites(prod_only).cfg_test, 0);
    }

    /// `#[cfg(any(test, feature = "x"))]` is NOT test-only: that item compiles into a
    /// production build whenever the feature is on. Only the literal `#[cfg(test)]` counts.
    #[test]
    fn cfg_any_test_feature_is_not_test_only() {
        let src = r#"
            #[cfg(any(test, feature = "probe"))]
            mod maybe {
                fn f<AB: AirBuilder>(b: &mut AB) { b.assert_zero(x); }
            }
        "#;
        let c = count_sites(src);
        assert_eq!(c.authored(), 1, "still authored: {c:?}");
        assert_eq!(
            c.cfg_test, 0,
            "a feature can turn this on in a shipped build: {c:?}"
        );
    }

    #[test]
    fn comments_and_strings_are_not_algebra() {
        let doc = r#"
            /// Lowers ConstraintExpr::Binary into LeanExpr::mul.
            // b.assert_zero(&Head::zero());
            fn f() -> &'static str { "ConstraintExpr::Polynomial" }
        "#;
        let c = count_sites(doc);
        assert_eq!(c.authored(), 0, "prose is not a constraint: {c:?}");
        assert_eq!(c.ir_lowered, 0);
    }

    /// END-TO-END RED PATH. A gate that cannot go red is not a gate — so this runs the REAL
    /// walker (`scan_tree`) and the REAL ratchet (`ratchet`) over a synthetic repo containing
    /// a hand-written Rust AIR, and asserts each failure mode fires. If someone neuters the
    /// scanner or the comparison, this goes red before the (green) production ledger can lie.
    /// ⚑ **SCOPE IS `git ls-files`, NOT THE FILESYSTEM** — both poles, over a REAL throwaway git
    /// repo, driving the REAL oracle (`tracked_rs_in`) and the REAL walker (`scan_tree`).
    ///
    /// The wound this pins: until 2026-08-07 the walker was a bare filesystem walk defended only by
    /// a deny-list, so an untracked, `.gitignore`d 679 MB `headver/` scratch checkout of HEAD was
    /// scanned as source and every ledgered file was re-reported under a `headver/` prefix that no
    /// `BASELINE` row matches — two failing cases, both pure artefact, and a printed ledger that was
    /// the real ledger duplicated.
    ///
    /// One pole alone would be worthless in either direction: "the untracked copy is ignored" is
    /// satisfied by a gate that sees NOTHING, and "the tracked file is caught" is satisfied by the
    /// old unbounded walk. Both, on byte-identical content differing only in whether git holds the
    /// path, is the whole claim.
    #[test]
    fn the_scope_is_git_tracked_files_not_the_filesystem() {
        let evil = "pub fn build(b: &mut Builder) {\n\
                    \x20   b.assert_zero(&Head::lin(1, 0).add_const(-1));\n\
                    \x20   b.push(ConstraintExpr::Binary { col: 4 });\n\
                    }\n";
        let tmp = std::env::temp_dir().join(format!("law1-scope-{}", std::process::id()));
        std::fs::remove_dir_all(&tmp).ok();
        let src = tmp.join("evilcrate/src");
        std::fs::create_dir_all(&src).expect("tmp tree");

        let git = |args: &[&str]| {
            let st = std::process::Command::new("git")
                .arg("-C")
                .arg(&tmp)
                .args(args)
                .output()
                .expect("git runs");
            assert!(st.status.success(), "git {args:?}: {st:?}");
        };
        git(&["init", "-q"]);

        // Byte-identical content. The ONLY difference is whether git holds the path.
        std::fs::write(src.join("tracked_air.rs"), evil).expect("write tracked");
        std::fs::write(src.join("scratch_air.rs"), evil).expect("write scratch");
        // `-N` (intent-to-add) stages the PATH without the content — the lightest thing that makes
        // a file part of the repository, and enough for `git ls-files` to report it.
        git(&["add", "-N", "evilcrate/src/tracked_air.rs"]);

        let tracked = tracked_rs_in(&tmp);
        assert!(
            tracked.contains("evilcrate/src/tracked_air.rs"),
            "the oracle must see the added path; got {tracked:?}"
        );
        assert!(
            !tracked.contains("evilcrate/src/scratch_air.rs"),
            "the oracle must NOT see the un-added path; got {tracked:?}"
        );

        // POLE 1 — the tracked violation is CAUGHT. Without this the fix is indistinguishable
        // from blinding the gate.
        let found = scan_tree(&tmp, Some(&tracked));
        assert!(
            found.contains_key("evilcrate/src/tracked_air.rs"),
            "a TRACKED hand-written AIR must still be seen: {found:?}"
        );
        let v = ratchet(&tmp, &found, &[]);
        assert!(
            v.iter().any(|s| s.contains("NEW Rust-authored constraints")
                && s.contains("evilcrate/src/tracked_air.rs")),
            "…and must still fail the ratchet; got {v:?}"
        );

        // POLE 2 — the untracked twin is INVISIBLE. This is the `headver/` artefact, gone.
        assert!(
            !found.contains_key("evilcrate/src/scratch_air.rs"),
            "an UNTRACKED scratch copy is not source and must not be reported: {found:?}"
        );
        assert_eq!(found.len(), 1, "exactly one file is in scope: {found:?}");

        // CONTROL — with no oracle (`None`, the synthetic-tree path) the walker sees BOTH, so
        // pole 2 is the tracking filter doing work and not the walker failing to reach the file.
        let unfiltered = scan_tree(&tmp, None);
        assert_eq!(
            unfiltered.len(),
            2,
            "the walker itself reaches both files; only the oracle separates them: {unfiltered:?}"
        );

        std::fs::remove_dir_all(&tmp).ok();
    }

    #[test]
    fn the_gate_goes_red_on_a_hand_written_air() {
        let tmp = std::env::temp_dir().join(format!("law1-red-{}", std::process::id()));
        let src = tmp.join("evilcrate/src");
        std::fs::create_dir_all(&src).expect("tmp tree");
        std::fs::write(
            src.join("hand_written_air.rs"),
            "pub fn build(b: &mut Builder) {\n\
             \x20   b.assert_zero(&Head::lin(1, 0).add_const(-1));\n\
             \x20   b.push(ConstraintExpr::Binary { col: 4 });\n\
             \x20   b.push(VmConstraint2::Base(VmConstraint::Gate(LeanExpr::Var(2))));\n\
             }\n",
        )
        .expect("write evil");

        let found = scan_tree(&tmp, None);
        let key = "evilcrate/src/hand_written_air.rs";
        let counts = found.get(key).copied().unwrap_or_else(|| {
            panic!("the walker did not even SEE the hand-written AIR; found: {found:?}")
        });
        assert_eq!(counts.symbolic, 1, "the assert_zero dialect: {counts:?}");
        assert_eq!(
            counts.ir_constructed, 4,
            "ConstraintExpr + 3 gate-tree nodes: {counts:?}"
        );

        // 1. an UNLISTED file is a violation.
        let v = ratchet(&tmp, &found, &[]);
        assert!(
            v.iter()
                .any(|s| s.contains("NEW Rust-authored constraints") && s.contains(key)),
            "a new hand-written AIR must fail the gate; got {v:?}"
        );
        // 2. a listed file that GREW is a violation.
        let v = ratchet(&tmp, &found, &[(key, 4)]);
        assert!(
            v.iter().any(|s| s.contains("GREW") && s.contains(key)),
            "growth past the baseline must fail; got {v:?}"
        );
        // 3. at or below baseline is clean — shrinking is the direction of the law.
        assert!(
            ratchet(&tmp, &found, &[(key, 5)]).is_empty(),
            "at baseline: green"
        );
        assert!(
            ratchet(&tmp, &found, &[(key, 99)]).is_empty(),
            "shrunk: green"
        );
        // 4. a ledger line for a vanished file is a violation (debt must not rot upward).
        let v = ratchet(&tmp, &found, &[(key, 5), ("evilcrate/src/deleted.rs", 12)]);
        assert!(
            v.iter().any(|s| s.contains("STALE BASELINE ENTRY")),
            "a stale ledger line must fail; got {v:?}"
        );

        std::fs::remove_dir_all(&tmp).ok();
    }

    /// A `GREW` row must NAME THE SITES, not just the delta — the repair for the 2026-07-31
    /// red-and-unowned day. Pinned as a tooth because a diagnostic is exactly the kind of thing
    /// that rots into decoration: nothing else in this file fails if the listing goes empty, and
    /// the next reader would silently be back to a number and a bisect.
    #[test]
    fn a_grew_row_names_the_sites_not_just_the_delta() {
        let tmp = std::env::temp_dir().join(format!("law1-grew-{}", std::process::id()));
        let src = tmp.join("evilcrate/src");
        std::fs::create_dir_all(&src).expect("tmp tree");
        // Three dialects at once, so the listing is checked to cover the SYMBOLIC one too —
        // the explain path used to record only the IR dialects, which is how a maintainer
        // auditing descriptor_ir2.rs's 287 got a 169-line listing that could not be reconciled.
        std::fs::write(
            src.join("grown.rs"),
            "use p3_air::AirBuilder;\n\
             pub fn build(b: &mut B) {\n\
             \x20   b.assert_zero(&Head::lin(1, 0));\n\
             \x20   b.push(ConstraintExpr::Binary { col: 4 });\n\
             }\n\
             #[cfg(test)]\n\
             mod tests {\n\
             \x20   fn t(b: &mut B) { b.push(LeanExpr::Var(9)); }\n\
             }\n",
        )
        .expect("write grown");

        let found = scan_tree(&tmp, None);
        let key = "evilcrate/src/grown.rs";
        let v = ratchet(&tmp, &found, &[(key, 1)]);
        let msg = v.join("\n");
        assert!(
            msg.contains("GREW") && msg.contains(key),
            "the row fires: {msg}"
        );
        // The by-kind histogram reaches all three dialects present.
        for kind in [
            ".assert_zero(..)",
            "ConstraintExpr::Binary",
            "LeanExpr::Var",
        ] {
            assert!(
                msg.contains(kind),
                "a GREW row must name the site KINDS; `{kind}` missing from:\n{msg}"
            );
        }
        // ...and the per-site listing carries LINE NUMBERS, which is what turns "which four
        // moved?" into a read instead of a 40-revision walk.
        for line in ["     3", "     4", "     8"] {
            assert!(
                msg.contains(line),
                "a GREW row must name the site LINES; `{line}` missing from:\n{msg}"
            );
        }
        // A test-only site is MARKED, never subtracted.
        assert!(
            msg.contains("#[cfg(test)]"),
            "test-only sites are attributed in the listing:\n{msg}"
        );
        // And the reader is told how to find the origin commit without bisecting.
        assert!(
            msg.contains("LAW1_EXPLAIN") && msg.contains("git log"),
            "a GREW row must carry the origin-hunting recipe:\n{msg}"
        );

        // A NEW-file row and a STALE row are unaffected — the listing is attached to GREW only.
        assert!(
            !ratchet(&tmp, &found, &[])
                .iter()
                .any(|s| s.contains("assert_zero(..) x")),
            "the histogram belongs to GREW, not to the NEW row"
        );
        std::fs::remove_dir_all(&tmp).ok();
    }

    /// The explain path must see ALL FIVE dialects, not just the IR ones. It saw only (3)+(4)
    /// until 2026-07-31, so `LAW1_EXPLAIN` on any `AirBuilder` file printed a listing that
    /// silently omitted every `assert_zero`-family and closure site it was counting.
    #[test]
    fn the_explain_listing_reconciles_with_the_count() {
        let src = r#"
            fn prod<AB: AirBuilder>(b: &mut AB) {
                b.assert_zero(x);
                b.when_transition().assert_eq(a, c);
                b.push(ConstraintExpr::Binary { col: 3 });
                let g = Gadget { eval: Box::new(|row, _, pi| row[0]) };
                match k { ConstraintExpr::Gated { .. } => (), _ => () }
            }
        "#;
        let mut ex = Vec::new();
        let c = count_sites_explained(src, Some(&mut ex));
        let authored = ex.iter().filter(|r| r.site == Site::Construct).count();
        let lowered = ex.iter().filter(|r| r.site == Site::Pattern).count();
        assert_eq!(
            authored,
            c.authored(),
            "every AUTHORED site must appear in the listing: {c:?} vs {ex:?}"
        );
        assert_eq!(lowered, c.ir_lowered, "and every lowering site too: {c:?}");
        assert!(
            ex.iter().any(|r| r.what == ".assert_zero(..)")
                && ex.iter().any(|r| r.what == ".when_transition(..)")
                && ex.iter().any(|r| r.what == "eval: Box::new(..)"),
            "the symbolic and closure dialects are listed by name: {ex:?}"
        );
        // Sorted by line, so the listing reads like the file.
        assert!(
            ex.windows(2).all(|w| w[0].line <= w[1].line),
            "the listing is in source order: {ex:?}"
        );
    }

    #[test]
    fn the_scope_reaches_outside_the_two_old_directories() {
        // The regression that made this rewrite necessary: the biggest Rust AIR in the tree
        // (`param-compose/src/{air,builder}.rs`) sat outside the scanned `circuit/src` +
        // `circuit-prove/src` and was invisible to a gate whose whole purpose was to see it.
        //
        // That AIR is now DELETED (2026-07-25) — so it can no longer serve as the scope probe,
        // and the probe moves to the OTHER files the two-directory scope hid. If this stops
        // finding them, the scope broke again.
        let found = scan_repo();
        for f in [
            "perf/src/lib.rs",
            "constraint-lowering/src/lib.rs",
            "dregg-dsl-runtime/src/composition.rs",
            "game-turn-slice/src/compiler.rs",
        ] {
            assert!(
                found.contains_key(f),
                "{f} authors constraints outside circuit/ + circuit-prove/ and the gate must \
                 see it; scope regressed"
            );
        }
        // ...and the file the probe used to be is GONE, which is the direction of the law. A
        // reappearance is a NEW hand-written Rust AIR and must not pass silently.
        for gone in ["param-compose/src/air.rs", "param-compose/src/builder.rs"] {
            assert!(
                !repo_root().join(gone).exists(),
                "{gone} was DELETED — a hand-written Rust AIR must not come back"
            );
        }
        assert!(
            found.len() > 60,
            "the widened scope should reach ~86 files across the workspace, found {}",
            found.len()
        );
    }
}
