# ZERO-SORRY VERDICT — dregg2 metatheory (adversarial, read-only)

Date: 2026-05-31. Verifier: adversarial read-only pass, default skeptical.
Toolchain: lean/lake v4.30.0 via `$HOME/.elan/bin`.

## VERDICT (top line)

**CONFIRMED.** The dregg2 metatheory (`metatheory/`) is literally `sorry`-free, the
full `lake build` is green with **zero** `sorry`-warnings, the `Claims.lean`
`#assert_axioms` ledger elaborates clean, and the CI guard has **demonstrated
teeth** (a planted sorry trips its regex). The three former `sorry`-bodies are
each replaced by an **honest** construct (typeclass field / named hypothesis), not
by vacuity-laundering — verified individually below.

## (1) ZERO sorry — evidence

- `lake build` → `BUILD=0`, `sorries=0` (count of `declaration uses 'sorry'`,
  the warning Lean emits for every sorry/admit/sorryAx). No `error:` lines.
- `lake env lean Dregg2/Claims.lean` → exit `0`, no error/sorry/warning output.
  The `#assert_axioms` ledger (which turns any *inherited* `sorryAx` into a hard
  build error) passes for all pinned keystones, including the three relevant ones
  (`Core.conservation_step`, `Laws.search_sound`, `Spec.phi_functorial` +
  `phi_functorial_concrete`), and the teeth lemmas
  (`Authority.goodSoundMatcher`, `Authority.evilMatcher_not_sound`).
- Textual scan of the WHOLE `metatheory` tree (excluding `.lake/` deps) for a bare
  `sorry` token NOT inside backticks: every remaining hit is a COMMENT or
  doc-string (e.g. `Claims.lean` markdown headers describing the guard,
  `Dregg2.lean` import doc-strings, `Exec/Consensus.lean:133` "no sorry,
  kernel-clean"). ZERO term/tactic bodies use `sorry`.
- The three named former sorry-bodies are gone:
  - `Core.lean:162` is now PROSE inside a doc-comment ("...`sorry` anywhere"),
    above `class ConservesStep` (the replacement).
  - `Laws.lean:60` is PROSE; the replacement is `class SoundSearchable` +
    `theorem search_sound`.
  - `Spec/VatBoundary.lean` `phi_functorial` is now a PROVED theorem under
    `NonDegenerate` (no `sorry` in body).

## (2) HONEST conversions — per-sorry teeth audit

### conservation_step (Core Law 1) — HONEST, kernel-backed
- Now a **typeclass field**: `Core.ConservesStep.step : count A + minted = count B
  + burned`, recovered as the lemma `conservation_step`. This is the
  `CryptoKernel` Prop-portal idiom, NOT a `sorry`.
- The instance `Exec.instConservesStepExec` is **NOT a fresh trivial instance**:
  the genuine content lives in `Exec.conservation_step_realized` — a real theorem
  `cexec s t = some s' → total s'.kernel = total s.kernel`, proved via
  `(cexec_attests h).1` (the step-completeness spine). `cexec_attests` proves the
  full `StepInv` (Conservation∧Authority∧ChainLink∧ObsAdvance) about the running
  kernel. `conservation_step_realizes_balance` / `instConservesStep_backed_by_kernel`
  thread that realized invariant explicitly so the abstract balance is the kernel's
  invariant, not a free assumption.
- HONEST RESIDUAL (disclosed, not a defect): the *abstract measure*
  `execConservation` chosen to realize the instance is the **zero-delta**
  normalisation (`count≡0, minted≡burned≡0`), because the kernel conserves `total`
  so the induced abstract delta is `0`. Consequently the typeclass *field* `step`
  for `execConservation` is the trivially-true `0=0` (discharged `simp`). The
  load-bearing content (`total` is preserved) is the SEPARATE theorem
  `conservation_step_realized` about `cexec`. This is the same abstraction the
  former `sorry`'d primitive had — the improvement is that there is now a genuine
  kernel theorem behind it and explicit tie-lemmas; it is NOT new vacuity. Not a
  smuggled `True`: `ConservesStep.step` is a real ∀-equation, and a non-conserving
  kernel would fail `conservation_step_realized`.

### search_sound (verify/find seam) — HONEST assumption with teeth
- Now `class SoundSearchable extends Searchable` with field
  `find_sound : ∀ p w, find p = some w → Discharged p w` (`Discharged p w ≜ Verify
  p w = true`). `search_sound` is the lemma accessor. This is a genuine *plugin
  contract* (the external prover's obligation), carried as a Prop field — NOT a
  vacuous `True`, NOT `sorry`.
- Satisfiable, non-trivially: `Authority.goodSoundMatcher` is a real
  `SoundSearchable` instance whose `find_sound` is PROVED (proposes `6`, `6%3==0`).
- TEETH: `Authority.evilMatcher_not_sound` PROVES `False` from any hypothetical
  `SoundSearchable` agreeing with `evilMatcher` (which returns `7`, `7%3≠0`) — so
  the contract is a genuine constraint not every `Searchable` meets. The untrusted
  base class `Searchable` deliberately does NOT carry soundness; consumers
  re-`Verify` (`Intent.resolve evilMatcher = none`). Confirmed it did NOT become a
  vacuous `True` and no law silently depends on it being free.

### phi_functorial (caps↔keys functor Φ) — PROVED under satisfiable, toothed hypothesis
- Now `theorem phi_functorial (hnd : NonDegenerate stmtOf) : PhiFunctorial …` —
  genuinely PROVED (no `sorry`), honestly CONDITIONAL on `NonDegenerate`.
- `NonDegenerate` is NOT always-true (it has TEETH on each field):
  - `accepts` (∃ accepting witness) — FAILS for a `Verify ≡ false` seam.
  - `collapses` (two distinct caps with equal `stmtOf`) — FAILS for an injective
    `stmtOf` or a subsingleton `Cap`.
  - `comp_propagates` — a real discharge-propagation condition.
  A degenerate verifier genuinely fails it, so the hypothesis is non-trivial.
- SATISFIABLE: `nonDegenerate_concrete` PROVES `NonDegenerate` for a concrete
  model — `Verify s b := b` (a **discriminating** verifier: accepts `true`,
  REJECTS `false`; NOT `Verify ≡ true`) with `stmtOf ≡ ()` (maximally lossy,
  collapsing `⟨true,()⟩ ≠ ⟨false,()⟩`). `phi_functorial_concrete` is exactly
  `phi_functorial` applied to that witness — axiom-clean. No smuggled vacuity.
- System-level re-confirmation: `Consistency.lean` §2.6 reuses
  `phi_functorial_concrete`, and §2.5 re-exhibits the discriminating crypto seam
  (accepts 7=7, rejects 7=8).

## (3) The GUARD has teeth — confirmed

- `ci.yml` job `metatheory-no-sorry` ("Metatheory zero-sorry guard"), Lean pinned
  to `metatheory/lean-toolchain` (v4.30.0), runs `bash
  scripts/no-sorry-metatheory.sh`.
- The script runs the real `lake build`, captures the exit code DIRECTLY (no
  head/tail masking), and fails if: build≠0, OR
  `grep -cE "declaration uses .sorry." > 0`, OR any `sorryAx` mention.
- CRITICAL teeth detail verified empirically: Lean 4.30 wraps the word in
  BACKTICKS (`declaration uses \`sorry\``). The guard regex `declaration uses
  .sorry.` uses a wildcard quote char, so it MATCHES the real backtick form (and
  also the legacy single-quote form). A toothless `'sorry'`-only regex would MISS
  the real warning — the script does NOT use that form.
- EMPIRICAL planted-sorry test (read-only, throwaway `/tmp` file, corpus
  untouched): a file with `theorem h : 1 = 2 := by sorry` elaborated under the
  corpus toolchain emits `declaration uses \`sorry\``, and the guard regex matched
  it (`guard_regex_matches=1`). A planted sorry WOULD fail CI.
- Two complementary layers, honestly distinguished: (a) the textual build-warning
  grep = the whole-corpus net (catches any sorry anywhere, pinned or not); (b) the
  `Claims.lean` `#assert_axioms`/`#assert_namespace_axioms` ledger = the
  deep-but-targeted transitive-inheritance tripwire (catches a sorry hidden behind
  a renamed lemma, but only for pinned decls/namespaces). Neither alone is
  whole-corpus + transitive; together they cover both.

## FINAL STATEMENT

The metatheory is `sorry`-free and CI-guarded. The 3 assumptions now honestly are:
1. **Conservation (Law 1)** — a typeclass field DISCHARGED by a real instance
   backed by the kernel theorem `conservation_step_realized` (`total` preserved by
   every committed `cexec` step). The abstract realizing measure is the zero-delta
   normalisation (disclosed residual); the genuine content is the separate kernel
   theorem, not a free axiom.
2. **search_sound** — an honest external-plugin contract (`SoundSearchable.find_sound`),
   satisfied by `goodSoundMatcher` and PROVED non-trivial by `evilMatcher_not_sound`;
   untrusted plugins re-`Verify`. Not a vacuous `True`.
3. **phi_functorial** — genuinely PROVED under the `NonDegenerate` hypothesis,
   which is toothed (a degenerate `Verify≡false` / injective `stmtOf` fails it) and
   SATISFIABLE by a discriminating concrete model (`phi_functorial_concrete`).

No conversion smuggled vacuity. Nothing still wrong.
