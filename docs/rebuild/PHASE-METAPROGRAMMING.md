> **Provenance.** Recovered 2026-05-30 from the prior session's read-only study agent
> (`~/.claude/.../subagents/`), which designed this as the body for this path but could not
> write it (read-only `Plan` mode). Verbatim except for stripped read-only-mode preamble.
> Consolidated alongside `PHASE-SHIFT.md`.

# Report: Phase-Metaprogramming Study

The doc below is the proposed content for `/Users/ember/dev/breadstuffs/docs/rebuild/PHASE-METAPROGRAMMING.md`. I am in read-only mode and cannot write it; the parent agent should create the file with this content.

## Grounding (what exists, what repeats)

Confirmed by reading the source:

- **`Dregg2/Tactics.lean`** — `#assert_axioms id` (an `elab … : command` that runs `Lean.collectAxioms` and rejects anything outside `{propext, Classical.choice, Quot.sound}`, notably `sorryAx`), `dregg_auto` (a `first | rfl | trivial | … | omega | tauto` closer), `option_inj at h` (a `simp only [Option.some.injEq, Prod.mk.injEq]` macro).
- **`Dregg2/Conserve.lean`** — the general conservation library (`sum_indicator`, `sum_pointUpdate`, `sum_conserve_of_deltas_zero`, `sum_transfer_conserve`) plus two honest tactics: `conserve` (pointwise delta cancellation, wrapped in `first | <real>; done | fail "…"`) and `commit_cases h with pat` (`split at h`; kill the `none` branch via `case isFalse => exact absurd h (by simp)`; read back `Option`/`Prod` injection + `subst` + `obtain pat := ‹_ ∧ _›`, leaving the content goal OPEN). The honesty rail — `done` is load-bearing, negative tests use `fail_if_success` — is the template for every new tactic.
- **`Dregg2/Claims.lean`** — 153-line ledger: `import Dregg2` + ~110 `#assert_axioms FullyQualified.name` lines, grouped §0–§17, with PARKED (commented) pins for not-yet-in-olean-closure constants (§12 Coherence, §16 Upgrade spine). This is the hand-maintained CI artifact.
- **`Dregg2/Spec/Guard.lean`** — the unification keystone: the 5-constructor `Guard` inductive (`firstParty`/`witnessed`/`all`/`any`/`gnot`), `admits` via a `mutual` block, and §7 "DERIVED legacy reconstructions" — `monotonic`, `sumEquals`, `senderAuthorized`, `oneOf`, `nonMembership`, each a one-liner over a primitive PLUS an `@[simp] admits_X … ↔ …` characterization lemma PLUS an `#assert_axioms` pin at §8. **This §7+§8 triple is exactly the shape a codegen must emit, ~90 times.**
- **`Dregg2/Spec/Authority.lean`** — `confers`/`confers_trans`, the Gen/Restrict op structures, `attenuate_is_restrictive_narrowing` (proof body is `step.narrows.2`).
- **`Dregg2/Proof/Refine.lean`** — refinement squares: each is `theorem refine_X (k k' turn) (h : exec k turn = some k') : <abstract law> := <relay of an exec lemma>`, plus `exec_refines` (forward simulation, conservation half proved via `refine ⟨cc, ?_, rfl⟩; unfold R …; rw [hR, (exec_conserves …).symm]`).

The **Rust catalog** (the GENERATE target), measured:
- `cell/src/program.rs`: `StateConstraint` = **29 variants**, plus `SimpleStateConstraint` (~14), `TransitionGuard`, `AuthorizedSet`, etc.
- `turn/src/action.rs`: `Effect` = **52 variants**, `Authorization` = **10 variants**, `LinearityClass`, `WitnessKind`.
- Total ~90 variants that become Spec smart-constructors.

**aesop is available** (`.lake/packages/aesop` — it ships as a mathlib transitive dep) but is **not currently imported or used anywhere in `Dregg2/`**. This is a key finding: a rule-set is a low-cost add.

---

# PHASE-METAPROGRAMMING.md

# Phase-Metaprogramming — the tooling phase-shift for dregg2's Lean metatheory

**Question.** What Lean 4 metaprogramming + proof-tactic infrastructure does dregg2 need
to (a) generate the catalog smart-constructors from the coproducts, (b) discharge the
recurring proof obligations, and (c) elaborate the eDSL?

**Stance.** dregg2 already has the *seeds* — `#assert_axioms`, `conserve`, `commit_cases`,
the §7 "DERIVED legacy reconstructions" pattern in `Spec/Guard.lean`. This phase is not
inventing new theory; it is *industrializing the repetition* those seeds revealed, with the
same honesty discipline (fail-loud, never fake-close). aesop is present in the toolchain
slice but unused; we adopt it as a rule-set backbone where it earns its keep.

---

## 0. The repetition inventory (what we are automating)

Measured against the corpus:

| Pattern | Where it repeats | Count | Current cost |
|---|---|---|---|
| smart-constructor + `admits`-characterization + `#assert_axioms` triple | `Spec/Guard.lean §7`, will recur for every `StateConstraint`/`Effect`/`Authorization` variant | ~90 | 3 hand-written decls each |
| `unfold f at h; commit_cases h with ⟨…⟩` fail-closed read-back | every `Exec/*` executor | ~30 files | partially factored (`commit_cases`) |
| `Σ delta = 0` conservation | `Exec/Kernel`, `Generators`, `MultiAsset`, `RecordCell` | ~8 sites | factored (`conserve` / `sum_transfer_conserve`) |
| refinement square `exec k turn = some k' → <abstract law>` | `Proof/Refine.lean`, will recur per Exec module | ~12 | hand-written relays |
| `confers`/attenuation meet-narrowing | `Spec/Authority`, `Spec/Guard` | ~10 | hand-written |
| `#assert_axioms FullyQualified.name` pin | `Claims.lean` | ~110 | hand-maintained ledger |

Three of these (`commit_cases`, `conserve`, the Guard §7 pattern) are already PROVEN to
factor. This phase finishes the job.

---

## 1. Code-gen for the catalog

### 1.1 The target shape (from `Spec/Guard.lean §7`)

Every catalog variant wants, verbatim, the Guard §7 triple. For `monotonic`:

    def monotonic (f : Request → Nat) (t : Nat) : Guard Request Statement :=
      firstParty (fun req => decide (t ≤ f req))

    @[simp] theorem admits_monotonic (f t req w) :
        admits (monotonic f t) req w = true ↔ t ≤ f req := by simp [monotonic]

    #assert_axioms Guard.admits_monotonic   -- (pinned at §8)

The ~90 catalog variants are all of this form: **a smart-constructor that builds a `Guard`
term from the variant's fields, an iff-characterization stating what `admits` reduces to,
and an axiom pin.** That is mechanical given (constructor-body, characterization-RHS).

### 1.2 The codegen API — a catalog DSL elaborator

We do **not** use a `deriving` handler against a Lean `inductive` — the catalog source of
truth is *Rust*, and the abstraction we want (`Guard` over orthogonal primitives) is
deliberately NOT a flat 90-constructor Lean inductive (that flat port "is exactly the
legacy mistake this layer exists to delete" — `Guard.lean §1`). Instead we introduce a
**declarative catalog block** that elaborates each entry to the triple:

    syntax (name := catalogBlock) "catalog " ident " where" (ppLine catalogEntry)+ : command

    syntax (name := catalogEntry)
      "| " ident binders " := " term            -- name, fields, Guard body
        " admits " term                          -- the characterization RHS
        (" by " tacticSeq)?                      -- optional proof (default: `simp [name]`)
      : catalogEntry

Usage (regenerating Guard §7 from a spec):

    catalog StateConstraintGuard where
      | monotonic (f : Request → Nat) (t : Nat) := firstParty (fun req => decide (t ≤ f req))
          admits (t ≤ f req)
      | sumEquals (fs : List (Request → Nat)) (v : Nat) :=
            firstParty (fun req => decide ((fs.map (· req)).sum = v))
          admits ((fs.map (· req)).sum = v)
      | senderAuthorized (s : Statement) := witnessed s
          admits (Discharged s (w s))
      | nonMembership (s : Statement) := gnot (witnessed s)
          admits (¬ Discharged s (w s))

Elaborator sketch (`Lean.Elab.Command`):

    elab_rules : command
      | `(catalog $cat:ident where $[| $names:ident $bs:binders := $bodies:term
                                       admits $rhs:term $[by $prfs:tacticSeq]?]*) => do
        for (name, bs, body, rhs, prf?) in entries do
          -- 1. emit  def $name $bs : Guard _ _ := $body
          elabCommand (← `(command| def $name $bs : Guard _ _ := $body))
          -- 2. emit  @[simp] theorem admits_$name … : admits ($name …) req w = true ↔ $rhs
          let thmName := mkIdent (`admits ++ name.getId)
          let proof := prf?.getD (← `(tacticSeq| simp [$name:ident]))
          elabCommand (← `(command|
            @[simp] theorem $thmName $bs (req w) :
                admits ($name $args) req w = true ↔ $rhs := by $proof))
          -- 3. emit  #assert_axioms $thmName   (the honesty pin, automatic)
          elabCommand (← `(command| #assert_axioms $thmName))

**Honesty rail (inherited automatically):** because step 3 emits `#assert_axioms` for every
generated characterization, a variant whose default `simp [name]` proof secretly needs a
`sorry` fails the pin AT GENERATION TIME. The codegen cannot manufacture a fake lemma — the
tripwire is wired into its output. A variant whose characterization is non-trivial supplies
an explicit `by …`; if that proof is incomplete the build breaks at the pin, not downstream.

### 1.3 Rust→catalog-block extraction (the source-of-truth bridge)

The catalog block is hand-written-once but should be *checked against* Rust, not drift from
it. A small build script (NOT Lean) parses the `#[derive]`d enums in `program.rs`/`action.rs`
(syn-based, ~150 LoC) and emits the **variant-name + field-type skeleton** of the catalog
block; the human fills the `Guard` body + characterization RHS (the semantics — which a
parser cannot infer). A `verify-catalog.sh` (mirroring svenvs' `verify-claims.sh`) diffs the
extracted skeleton against the committed catalog block and FAILS CI if a Rust variant has no
Lean entry — closing the "Rust grew a variant, Lean silently lags" gap.

### 1.4 Coverage estimate

- **Fully mechanical (body is one primitive + `simp` proof):** ~60 of 90 variants —
  `FieldEquals`, `FieldGte`, `FieldLte`, `WriteOnce`, `Immutable`, `Monotonic`,
  `SumEquals`, `SenderAuthorized`, the `Effect` `SetField`/`Transfer`/`IncrementNonce`
  family, the `Authorization` `Signature`/`Bearer`/`OneOf`/`Stealth` family. The codegen
  emits all three decls, default `simp` proof closes, pin passes — zero hand-proof.
- **Body-mechanical, proof-manual (~25):** `TemporalGate`, `RateLimit`, `BoundDelta`,
  `AllowedTransitions`, `Witnessed`, the bridge/escrow effects — the constructor is generated
  but the characterization needs a real proof (supplied via `by …`). Still saves the boilerplate
  def + statement + pin.
- **Genuinely bespoke (~5):** `Custom`, `Renounced`, `AnyOf` (recursive), the
  `LinearityClass` discriminator — these stay hand-written; the catalog block skips them.

**Net: the codegen eliminates ~85% of the ~270 hand-decls (90 × 3) the flat instantiation
would require, and wires the honesty pin into 100% of generated output.**

---

## 2. Domain tactics (beyond `conserve`/`commit_cases`)

All follow the `Conserve.lean` honesty template: real work wrapped in
`first | <real>; done | fail "<diagnostic>"`, negative-tested with `fail_if_success`.

### 2.1 `guard` / `discharge` — unfold `admits`, split the seam *(HIGH leverage)*

The single most-repeated opening move across `Spec/Guard` consumers and every `Exec/*`
executor that gates on a `CellProgram.admits`: unfold the guard, push `admits` through the
`all`/`any`/`gnot` structure via the §3 `@[simp]` lemmas, and split the verify seam into its
`firstParty` (decidable-now) and `witnessed` (oracle) obligations.

    /-- `discharge` — reduce a goal/hyp mentioning `Guard.admits` to its leaf obligations:
        rewrite via `admits_all`/`admits_any`/`admits_gnot`/`admits_firstParty`/
        `admits_witnessed`, then `Bool.and_eq_true`/`or_eq_true` split. Leaves one goal per
        leaf (a `firstParty` decidable prop or a `Discharged s (w s)`). FAILS LOUDLY if the
        goal mentions no `admits`. -/
    macro "discharge" : tactic =>
      `(tactic| first
        | (simp only [Guard.admits_all_eq, Guard.admits_any_eq, Guard.admits_gnot,
                      Guard.admits_firstParty, Guard.admits_witnessed,
                      Guard.admitsAll_cons, Guard.admitsAll_nil,
                      Guard.admitsAny_cons, Guard.admitsAny_nil,
                      Bool.and_eq_true, Bool.or_eq_true] at *
           done)  -- load-bearing: never leave a half-unfolded admits masquerading as progress
        | fail "discharge: no `Guard.admits` to unfold — is this a guard goal?")

This is the natural sibling of `commit_cases`: `commit_cases` opens the *executor* seam,
`discharge` opens the *guard* seam. Highest leverage because EVERY catalog characterization
proof and every Exec admissibility proof starts here.

### 2.2 `refine_square` — the Exec⊑Spec relay *(HIGH leverage)*

`Proof/Refine.lean` shows every clean refinement is a relay: `theorem refine_X (h : exec k
turn = some k') : <law> := <exec_lemma> k k' turn h`. Automate the relay-or-fail:

    /-- `refine_square via lemma` — close an Exec⊑Spec obligation
        `<abstract law about k'>` given `h : exec k turn = some k'`, by relaying the named
        kernel lemma (`exec_conserves`, `exec_authorized`, …) and rewriting the abstract
        measure through the refinement relation `R`. FAILS LOUDLY if the relay's conclusion
        does not match the abstract goal (never closes a square the kernel does not justify). -/
    syntax "refine_square" " via " ident : tactic
    macro_rules
      | `(tactic| refine_square via $lem:ident) =>
        `(tactic| first
          | (first
             | exact $lem ‹_› ‹_› ‹_› ‹_›          -- direct relay (refine_conservation shape)
             | (refine ⟨_, ?_, rfl⟩; unfold R at *; -- forward-sim conservation half
                rw [‹_ = _›, ($lem ‹_› ‹_› ‹_› ‹_›).symm]))
            done
          | fail "refine_square: relay `{lem}` does not discharge this abstract law — \
              the concrete step does not justify it; this square is OPEN, not closeable")

The fail branch is the honest one: a refinement square that the kernel lemma does NOT
justify is a genuine `-- OPEN:` (like `exec_refines`'s operational half) — the tactic must
refuse it, not fall through to `simp`.

### 2.3 `conserve_multi` — multi-domain conservation *(MEDIUM leverage)*

`Spec/Conservation.lean` has `conservation_over_monoid` and `multi_domain_independent`:
conservation now holds per value-domain (asset type), value-monoid-parametric. The existing
`conserve` is single-domain (`ℤ`). `conserve_multi` lifts it: split the goal per domain
(`Finset.sum` over the domain index), then run `conserve` / `sum_transfer_conserve` on each.

    macro "conserve_multi" : tactic =>
      `(tactic| first
        | (rw [Finset.sum_comm]            -- swap to per-domain inner sums (when applicable)
           refine Finset.sum_congr rfl ?_
           intro _dom _
           first | conserve | (apply sum_transfer_conserve <;> assumption)
           done)
        | fail "conserve_multi: per-domain deltas do not each cancel — bring the per-domain \
            `src ≠ dst` / membership facts, or a domain does not conserve")

Medium (not high) because multi-asset conservation appears at ~3 sites today; valuable but
narrower than `discharge`.

### 2.4 `attenuate` — meet-narrowing *(MEDIUM leverage)*

`Spec/Guard.attenuate_narrows` and `Spec/Authority.attenuate_is_restrictive_narrowing` are
both the meet law `a ⊓ b ≤ a`. The tactic discharges any "attenuating preserves/narrows"
goal by reducing to `.narrows.2` / `Bool.and_eq_true …|>.1` and applying the meet lemma —
**refusing the residual.** The honesty point is specific to this domain: it must NOT close a
goal that secretly needs the Heyting residual `a ≤ b ⇨ c` (a *weakening*), only the genuine
meet narrowing (`Guard.lean §5` is emphatic on this).

    macro "attenuate" : tactic =>
      `(tactic| first
        | (first
           | exact (Guard.attenuate_narrows _ _ _ _ ‹_›)
           | (rw [Guard.admits_attenuate, Bool.and_eq_true] at *; tauto)
           | exact ‹Dregg2.Spec.Attenuate _ _ _ _ _›.narrows.2)
          done
        | fail "attenuate: goal is not a MEET-narrowing (a ⊓ b ≤ a) — if it needs the \
            Heyting residual (a weakening) that is NOT attenuation; prove it explicitly")

### 2.5 Tactic-suite priority within §2

1. `discharge` (every guard/admissibility proof opens with it),
2. `refine_square` (every new Exec module needs ~3),
3. `conserve_multi`, `attenuate` (domain-specific, fewer sites).

### 2.6 aesop rule-set (the backbone)

aesop is in the toolchain but unused. Rather than grow `discharge`/`conserve` into mega-macros,
register their lemma sets as a **named aesop rule-set** so the leaf goals after `discharge`
close automatically:

    declare_aesop_rule_sets [Dregg2]
    attribute [aesop safe simp (rule_sets := [Dregg2])]
      Guard.admits_all_eq Guard.admits_any_eq Guard.admits_firstParty Guard.admits_witnessed
      Conserve.sum_indicator Conserve.sum_pointUpdate
    -- usage: `aesop (rule_sets := [Dregg2])` as the leaf closer, behind a `first | … | fail`.

Keep aesop *behind* the honesty rail (wrap `aesop (rule_sets := [Dregg2])` in
`first | … | fail`), so it never silently weakens an obligation. aesop is a closer, not a
license to skip the fail-loud wrapper.

---

## 3. eDSL elaboration support — the proof-carrying seam

The eDSL study (`docs/rebuild/03-spine-proof.md §"proof-carrying receipt"`) wants a DSL term
to elaborate to a Spec construction AND emit its obligations as goals. The metaprogramming
seam:

### 3.1 The shape: elaborate-to-Spec-term + emit-obligations

A DSL `program`/`turn` literal elaborates to a `Guard`/`Effect` Spec term, and its
side-conditions (conservation, authority, well-formedness) are emitted as **synthetic goals**
the surrounding proof must discharge — proof-carrying elaboration.

    syntax (name := dreggProgram) "program% " dslBody : term
    elab_rules : term
      | `(program% $body) => do
        -- 1. elaborate the DSL body to a Spec `CellProgram`/`Guard` term
        let specTerm ← elabDslToSpec body
        -- 2. for each declared invariant, synthesize an obligation metavariable of type
        --    `∀ k turn, specTerm.admits k turn = true → <invariant>` and register it as a
        --    new goal (via `Lean.Elab.Term.addAutoBoundImplicits` / `mkFreshExprMVar` +
        --    `pushGoal`), so it surfaces in the ambient tactic block.
        let obligations ← collectObligations body specTerm
        for o in obligations do
          let mv ← mkFreshExprMVar o
          appendGoals [mv.mvarId!]
        return specTerm

The seam is: **`elabDslToSpec` produces the term (the *demand*), `collectObligations`
produces the goals (the *supply contract*)** — mirroring the demand⊣supply split that
`Guard.lean §6` already formalizes (`admits` on a `witnessed` guard IS `Laws.Discharged` at
the verify seam). The eDSL elaborator is the *syntactic* face of that adjunction.

### 3.2 Why an elaborator, not a macro

A macro expands syntactically and cannot inspect *types* to know which obligations a DSL
term incurs. The eDSL needs the elaborator's access to the local context (the cell's slot
types, the value-monoid instance) to generate the *right* obligation goals — e.g. a
`Transfer` effect emits a conservation goal only when its `LinearityClass` is `Linear`.
This is `Lean.Elab.Term` territory, not `macro`.

### 3.3 Honesty at the eDSL seam

The emitted obligations are REAL goals in the ambient block — they cannot be silently
discharged by the elaborator. If the DSL author does not prove them, the surrounding
definition has open goals and the build fails. The elaborator is incapable of fake-closing
(it only *emits* goals; it never *solves* them). Each top-level eDSL definition is then
pinned with `#assert_axioms`, closing the loop: a DSL program whose obligations were
discharged by `sorry` trips the tripwire.

### 3.4 Phasing

The eDSL elaborator is the *most* speculative deliverable — it depends on the eDSL study
fixing the surface syntax. Build it LAST (after the catalog codegen, which gives it the Spec
constructors to elaborate *into*). Until then, the catalog smart-constructors ARE the eDSL's
target vocabulary.

---

## 4. The `#assert_axioms` discipline as infra

### 4.1 `#assert_axioms_all` — module-wide pinning

`Claims.lean` hand-lists ~110 fully-qualified names. Replace the per-module sections with a
command that iterates the environment and pins every theorem in a namespace:

    open Lean Elab Command in
    elab "#assert_axioms_all" ns:ident : command => do
      let env ← getEnv
      let prefixName := ns.getId
      let mut checked := 0
      for (name, info) in env.constants.toList do
        unless name.getPrefix == prefixName do continue   -- direct members of the namespace
        unless info.isThm do continue                      -- theorems only, skip defs/inductives
        if name.isInternal then continue
        let axs ← collectAxioms name
        let bad := axs.filter (· ∉ [``propext, ``Classical.choice, ``Quot.sound])
        unless bad.isEmpty do
          throwError "axiom-hygiene FAIL: {name} depends on {bad.toList}"
        checked := checked + 1
      logInfo m!"#assert_axioms_all {prefixName}: {checked} theorems pinned, all kernel-clean"

Usage in `Claims.lean`:

    #assert_axioms_all Dregg2.Spec.Guard      -- replaces 11 hand-written §4 lines
    #assert_axioms_all Dregg2.Conserve        -- replaces 4 §0 lines

**Critical honesty caveat:** module-wide pinning can hide a *legitimately-resting* keystone
(one that rests on a §8 oracle / Law-1 `sorry`'d primitive, which `Claims.lean` deliberately
does NOT pin). So `#assert_axioms_all` needs an **allow-out list**:

    elab "#assert_axioms_all" ns:ident ("except" ids:ident*)? : command => …
        -- names in `except` are SKIPPED (they legitimately rest on an oracle) — but each
        -- skip must be justified by a comment, exactly as Claims.lean §12/§16 PARKED pins are.

This preserves the "a keystone resting on a primitive is NOT pinned" discipline while
deleting the 110-line manual ledger for the clean majority.

### 4.2 Framing/retired-label guard (the `verify-claims.sh` citation-integrity analog)

svenvs' `verify-claims.sh` checks citation integrity. The Lean analog: a command that
ensures every keystone the prose `CLAIMS.md` advertises as PROVED has a live pin, and that
no pin references a *retired* (renamed/deleted) constant:

    elab "#assert_claims_cover" : command => do
      -- read the claimed-PROVED names from a side table (a `def claimedKeystones : List Name`)
      -- and verify (a) each is a known constant (`env.contains` — a retired name is an error),
      --            (b) each is reachable from the import closure (not PARKED-and-forgotten).
      -- Inverse of `unknownConstant`: catches CLAIMS.md drift in BOTH directions.

This makes `CLAIMS.md` ↔ `Claims.lean` ↔ environment a closed, build-checked triangle: a
claim with no pin, or a pin with no constant, breaks the build — the framing/retired-label
guard in Lean form.

### 4.3 CI hook

`lake env lean Dregg2/Claims.lean` (already a credibility artifact) plus the new
`verify-catalog.sh` (Rust↔catalog-block diff, §1.3) become two CI gates. Neither builds new
proofs; both are pure auditors that can only *reject*.

---

## 5. Tooling priorities (build order for max leverage)

Ordered by (leverage × independence-from-unbuilt-things):

1. **`#assert_axioms_all` (+ `except`)** — *smallest, safest, immediate.* Pure rejector,
   no new proofs, collapses the 110-line `Claims.lean` ledger, and is a prerequisite for the
   codegen's auto-pinning step. ~40 LoC of `Lean.Elab.Command`. Build FIRST.

2. **The catalog codegen (`catalog … where` elaborator)** — *highest total leverage.*
   Eliminates ~85% of the ~270 hand-decls the flat ~90-variant port would need, and wires
   the honesty pin into 100% of its output. Depends on #1 for the auto-pin. Build SECOND.

3. **`discharge` tactic (+ aesop `Dregg2` rule-set)** — *highest per-proof leverage.* Every
   catalog characterization and every Exec admissibility proof opens with it; it makes the
   codegen's default `simp`-proofs actually close for the ~60 mechanical variants. Build
   THIRD, co-developed with #2.

Then, in rough order: `refine_square`, `verify-catalog.sh` (Rust↔Lean diff),
`conserve_multi`/`attenuate`, and LAST the eDSL elaborator (gated on the eDSL surface-syntax
study).

---

## Recommended first 2–3 tools to build

1. **`#assert_axioms_all <ns> [except …]`** — module-wide axiom-hygiene pinning with a
   justified allow-out list. Tiny, pure-rejector, prerequisite for codegen auto-pinning.
2. **The `catalog … where` codegen elaborator** — generates the smart-constructor +
   `admits`-characterization + auto-`#assert_axioms` triple per variant, eliminating ~85% of
   the ~270 hand-decls and wiring the honesty tripwire into every generated lemma.
3. **`discharge` tactic + the aesop `Dregg2` rule-set** — the guard-seam opener that makes
   the codegen's default proofs close and that every admissibility/characterization proof
   starts with.

All three are pure-additive, fail-loud, and incapable of fake-closing a goal — the
`Conserve.lean` honesty discipline carried into the tooling phase.

---

## Critical Files for Implementation

- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Tactics.lean` — home of `#assert_axioms`; where `#assert_axioms_all` and the catalog `elab_rules` go.
- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Spec/Guard.lean` — the §7+§8 triple the codegen mechanizes; the `admits` simp-lemma set `discharge` rewrites with.
- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Conserve.lean` — the honesty-rail template (`first | <real>; done | fail`, `fail_if_success` negative tests) every new tactic copies; `conserve_multi`'s base.
- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Claims.lean` — the 110-line ledger `#assert_axioms_all` collapses; the citation-integrity triangle.
- `/Users/ember/dev/breadstuffs/cell/src/program.rs` and `/Users/ember/dev/breadstuffs/turn/src/action.rs` — the Rust catalog (29 `StateConstraint` + 52 `Effect` + 10 `Authorization` variants) that the codegen and `verify-catalog.sh` extractor read as source-of-truth.

Also load-bearing: `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Proof/Refine.lean` (the `refine_square` template).
