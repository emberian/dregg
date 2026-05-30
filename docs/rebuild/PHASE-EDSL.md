> **Provenance.** Recovered 2026-05-30 from the prior session's read-only study agent
> (`~/.claude/.../subagents/`), which designed this as the body for this path but could not
> write it (read-only `Plan` mode). Verbatim except for stripped read-only-mode preamble.
> Consolidated alongside `PHASE-SHIFT.md`.

# PHASE-EDSL — Embedded DSLs for dregg2 in Lean 4

**Intended doc path:** `/Users/ember/dev/breadstuffs/docs/rebuild/PHASE-EDSL.md`
*(I operate in read-only planning mode and cannot create the file; the complete content below is ready to be written verbatim by a write-capable step.)*

**Question.** What embedded DSL(s) does dregg2 need, and how do we build them in Lean 4, so that writing a dregg cell/program/choreography is ergonomic AND elaborates directly to the verified `Spec` constructions?

---

## 0. Grounding — what the DSLs must target (the Spec seam)

Four constructions in `metatheory/Dregg2/` are the elaboration *targets*. They are deliberately small and already carry their characterization lemmas:

1. **`Guard Request Statement`** (`Dregg2/Spec/Guard.lean:90`) — the ONE verify/find seam. Five primitives: `firstParty (p : Request → Bool)`, `witnessed (s : Statement)`, `all`, `any`, `gnot`. Evaluated by `admits g req w : Bool` (`:107`). Smart constructors already exist: `monotonic`, `sumEquals`, `senderAuthorized`, `oneOf`, `nonMembership`, `attenuate` (`:248-285`), each with a `@[simp] admits_*` lemma. `attenuate g c := all [g, c]` is the meet (`:195`).

2. **`RecordProgram` / `StateConstraint` / `SimpleConstraint`** (`Dregg2/Exec/Program.lean:58-210`) — the executable, `#eval`-able cell-program catalog (the structural subset of dregg1's 21 `StateConstraint`s in `cell/src/program.rs:597`), name-keyed over `Value` records. `RecordProgram.admits : RecordProgram → Nat → Value → Value → Bool` (`:216`) is the decidable golden oracle. `recExec` (`RecordCell.lean:99`) gates the live arrow; `recExec_admitted` is the keystone; `recReplay_preserves_sumEquals` (`RecordCellLive.lean:169`) is conservation over records.

3. **`LinearityClass`** (`Dregg2/Spec/Conservation.lean:79`) — the six-color effect coloring (`Conservative`/`Monotonic`/`Terminal`/`Generative`/`Annihilative`/`Neutral`) with `linearity : Effect → LinearityClass` (`:165`), `conservedInDomain` (`:211`), `Receipt.WellFormed` disclosure (`:265`), and the four key conservation theorems.

4. **`GlobalType`** (`Dregg2/Coordination.lean:98`) — the choreography: `comm src dst s cont`, `choice src dst branches`, `mu`/`var`, `done`; with `project : GlobalType → Role → LocalType` (`:241`), `Projectable` (`:325`), and the fidelity/deadlock theorems (some `sorry`-OPEN).

Plus the **authority graph ops** (`Dregg2/Spec/Authority.lean`): `Introduce`/`Amplify`/`Mint`/`Endow`/`Attenuate`/`Revoke` as `Prop`-structures, folded under `GenAct`/`RestrictAct`. And `Spec/Coherence.lean` proves all four targets are **one web** (conferral IS a `firstParty` Guard `:94`; CG-5 IS cross-cell `Σ=0` `:160`; attenuation is one meet-order `:376`).

**dregg1's existing DSL** (`dregg-dsl/`): proc-macro attributes `#[dregg_caveat]`/`#[dregg_effect]`/`#[dregg_circuit]` (`lib.rs:54,114,185`) over Rust fn bodies of `require!(a <= b)`, `.contains()`, `in_range!`, `merkle_member!`, `poseidon2_assert!`, and `*x op= y` mutations. Parsed to a flat `ConstraintIr` (`ir.rs:9`: `params : Vec<Param>`, `statements`, `RequirementKind`) and fanned out to **eight backends** (Rust eval, AIR, Datalog, Kimchi, STARK, Midnight, Plonky3, SP1). 

**What works:** the surface (`require!(balance >= amount)`) is genuinely readable; the multi-backend fan-out from one IR is the right factoring. **What's clunky:** (a) it is *external* — the constraint is a Rust function whose semantics live only in generated code, with **no proof** that the eight backends agree (the `gen_diff_test.rs` differential test is the only link, and it is testing, not proof); (b) `RequirementKind` is a flat ~8-variant union that grew the same way `StateConstraint` grew to 21 — the exact "flat catalog" mistake `Spec/Guard.lean:38` exists to delete; (c) parameters are bit-positioned / typed ad hoc (`ParamType::ByteArray32`, slot indices `u8`), not name-keyed; (d) there is no single semantic object the surface *denotes* — `require!` lowers straight to codegen, so "what does this caveat mean" has no answer except "run the Rust."

---

## 1. Which DSLs

Recommendation: **three eDSLs, layered, sharing one elaboration core.** All embedded in Lean.

### DSL-A — the **cell-program DSL** (`dregg_program`) — *build this first*

The migration target for `#[dregg_caveat]`/`#[dregg_effect]`. Surface = named-field constraints/guards; elaborates to `RecordProgram` (and, where the program is a pure gate over a request, to `Spec.Guard`).

Proposed surface (a `term`-level elaborator producing a `RecordProgram`):

```lean
def counter : RecordProgram := dregg_program {
  invariant { monotonic count }          -- .predicate [.simple (.monotonic "count")]
}

def escrow : RecordProgram := dregg_program {
  on deposit  { strictMono balance }     -- a Cases arm, guard = .methodIs ⟨"deposit"⟩
  on release  { status : 1 => 2          -- allowedTransitions "status" [(1,2)]
              ; immutable amount }
  invariant   { sum [locked, free] = 100 }   -- .sumEquals ["locked","free"] 100
}

Atom keywords map 1:1 onto the catalog and reuse the existing `@[simp]` lemmas:

| surface | elaborates to | dregg1 origin |
|---|---|---|
| `field >= v` / `<= v` / `= v` | `.simple (.fieldGe/.fieldLe/.fieldEquals f v)` | `RequirementKind::GreaterEqual…` |
| `monotonic f` / `strictMono f` | `.simple (.monotonic/.strictMono f)` | `StateConstraint::Monotonic` |
| `immutable f` / `writeOnce f` | `.simple (.immutable/.writeOnce f)` | `Immutable`/`WriteOnce` |
| `f := old + d` | `.simple (.fieldDelta f d)` | `FieldDelta` |
| `f in old+[lo,hi]` | `.fieldDeltaInRange f lo hi` | `FieldDeltaInRange` |
| `f : a => b` (state machine) | `.allowedTransitions f [(a,b)]` | `AllowedTransitions` |
| `sum [fs] = v` | `.sumEquals fs v` | `SumEquals` |
| `conserve [ins] => [outs]` | `.sumEqualsAcross ins outs` | `SumEqualsAcross` |
| `any { c1 ; c2 }` | `.anyOf [c1,c2]` | `AnyOf` (Heyting ⊔) |
| `not c` | `.simple (.not c)` | `SimpleStateConstraint::Not` |
| `on m { … }` | a `TransitionCase ⟨.methodIs m, …⟩` | `Cases` / `MethodIs` |
| `witnessed s` | `Guard.witnessed s` (Guard form) | `Witnessed`/`SenderAuthorized` |

### DSL-B — the **choreography DSL** (`dregg_choreo`) — *build second*

Surface for `GlobalType` with the textbook MPST notation, elaborating to `Coordination.GlobalType` and (optionally) auto-running `project`/`Projectable` at elaboration time:

```lean
def auction : GlobalType := dregg_choreo {
  bidder →(bid) seller;                      -- comm bidder seller "bid" …
  seller →(result) bidder { accept . done    -- choice with two labels
                          | reject . done }
}
-- elaborates to: .comm 0 1 0 (.choice 1 0 [(accept,.done),(reject,.done)])

### DSL-C — the **effect/turn DSL** (`dregg_effect`) — *build third (smallest)*

Surface for declaring an effect and its `LinearityClass`, so the coloring map and disclosure obligation are generated, not hand-written:

```lean
dregg_effect transfer (amount : Nat) : Conservative   -- adds a `linearity` arm + paired-sibling VC
dregg_effect mint     (amount : Nat) : Generative      -- adds disclosure obligation to the receipt

This is mostly a `command` macro that extends the `linearity` match and emits the `requires_paired_sibling` / `is_disclosed_non_conservation` obligations.

**Why these three and not more.** The authority graph ops (`Introduce`/`Mint`/…) do *not* need their own surface DSL: `Coherence.lean:94` already proves conferral is a `firstParty` Guard, so authority caveats are expressed in DSL-A's `witnessed`/`firstParty` vocabulary. The four sites collapse onto Guard (`Guard.lean:8-26`); the DSL should mirror that collapse, not re-fork it.

---

## 2. Embedded vs external — recommend **embedded-in-Lean**

**Recommend embedded.** The decisive reason is the dregg1 gap: its DSL is external (Rust proc-macros → 8 codegen targets), so a program's *meaning* is the generated code, and nothing proves the backends agree. In Lean-embedded form, a `dregg_program {...}` term **is** a `RecordProgram` — a value in the verified theory — so:

- the program is verified *in situ*: `#eval program.admits …` is the golden oracle, and `recReplay_preserves_sumEquals` etc. apply to *this exact term* with no transcription gap;
- proof obligations are real Lean goals attached to the elaborated term (§3), not differential tests;
- error messages, hover, and go-to-definition come free from the Lean elaborator;
- the "multi-backend fan-out" survives as a *post-elaboration* pass: a `RecordProgram → AIR` compiler (`RecordCircuit`, Build 3) runs on the verified term, and the `admits ↔ circuit` correspondence (`Exec/Program.lean:16`) is provable rather than tested.

**Tradeoff:** authors must write inside a `.lean` file and accept Lean's parser. Mitigation: the `dregg_program {…}` block uses its own `declare_syntax_cat`, so inside the braces the grammar is the DSL's, not Lean's — authors never see `RecordProgram` constructors. For non-Lean authors, a thin **external front-end that emits the `dregg_program {…}` block** (a pretty-printer, not a compiler) recovers a standalone surface while keeping Lean as the single source of semantic truth — the inverse of dregg1 (there the verified artifact was downstream of codegen; here it is the artifact).

**How dregg1's proc-macro maps to the Lean eDSL.** Direct correspondence:

| dregg1 (Rust proc-macro) | dregg2 (Lean eDSL) |
|---|---|
| `#[dregg_caveat] fn` + `parse_macro_input!` | `syntax`/`declare_syntax_cat` + `elab` |
| `ConstraintIr` (`ir.rs:9`) | the **elaborated `RecordProgram`/`Guard` term itself** (no separate IR) |
| `RequirementKind` flat enum | the small catalog `SimpleConstraint`/`StateConstraint` |
| `gen_rust`/`gen_air`/… (8 backends) | post-elaboration passes over the verified term |
| `gen_diff_test.rs` differential test | a *theorem* `admits ↔ circuit` |
| `requires = "Send"` permission attr | a `witnessed`/`firstParty` conjunct (Guard) |
| typed `params : Vec<Param>` | the field-name set the constraints read (name-keyed `Value`) |

The IR *disappears*: in dregg1 the IR exists because the surface and every backend are distinct artifacts. In dregg2 the surface elaborates straight to the semantic object that all later passes consume, so the "IR" is `RecordProgram` and it is already a verified type.

---

## 3. The elaboration story (the metaprogramming seam)

Use the **standard four-stage Lean eDSL pattern** (the same idiom as `Dregg2/Conserve.lean:182` `syntax`+`macro_rules`, generalized to `elab`):

1. **`declare_syntax_cat dregg_constraint`** — a fresh syntactic category so the DSL grammar is isolated from Lean's term grammar inside the braces.
2. **`syntax` rules** — one per atom (`field ">=" term`, `"monotonic" ident`, `"any" "{" … "}"`, `"on" ident "{" … "}"`, …). These are pure parser productions, no semantics yet.
3. **`elab`/`macro_rules`** — translate each syntax node to a `RecordProgram`/`StateConstraint`/`Guard` term, calling the **existing smart constructors** (`Guard.monotonic`, `.simple (.fieldGe …)`, `.allowedTransitions`, `Guard.attenuate`). Field names (`count`, `balance`) become `String` literals into `Value.scalar` — the name-keyed discipline of `Exec/Program.lean:14`. This stage is a `macro` when the translation is purely syntactic (the common case) and an `elab` only when it must consult the elaboration context (e.g. resolving a method symbol or an effect's declared color).
4. **(optional) obligation emission** — the elaborator additionally produces the **verification conditions** as Lean goals, so writing a program *generates the VCs the WP/VCG study will discharge*.

**Carrying proof obligations (proof-carrying elaboration).** Two complementary mechanisms, pick per-atom:

- **Decidable-by-construction (the default).** Every catalog atom's `admits` is already decidable and `#eval`-able (`Exec/Program.lean` is "pure, computable, `#eval`-able"). So a *closed* program needs no proof obligation — `admits` just computes. The obligation only appears when the author asserts a *property* of the program. For that, the `dregg_program` elaborator can be wrapped by an `assert`-style form:

  ```lean
  def escrow : RecordProgram := dregg_program { … }
  theorem escrow_conserves :
      ... := by dregg_vcg escrow   -- the VCG study discharges this

- **Sigma-type elaboration (proof-carrying terms).** For atoms whose admissibility is *not* first-party (the `witnessed`/`circuit`/`boundDelta` family — `Program.lean:99-102` defers these), the elaborator emits a `RecordProgram × (proof obligation)` pair, i.e. it elaborates to a term of type `{ p : RecordProgram // VC p }` where `VC p` is an `?obligation` metavariable. The author discharges it with the WP tactic, or `sorry`-stubs it (visible as an OPEN, matching the lib's `-- OPEN:` discipline). This is the seam to the VCG/WP study: **the eDSL produces the goals; the WP study produces the tactic that closes them.** Concretely the obligation shapes are: for `boundDelta` → the JointTurn aggregate's `Σδ=0` (CG-5, `Conservation.lean:367`); for `witnessed s` → `Discharged s (w s)` (`Guard.lean:225`); for a `Cases` program → default-deny well-formedness (`admits_cases_nil`, `Program.lean:235`).

**The seam, stated precisely.** A DSL term `dregg_program {C}` elaborates to `mkProgram C : RecordProgram` by structural recursion over the syntax, where each leaf calls a catalog smart constructor. The elaboration is *sound by reuse*: because it bottoms out in `Guard.monotonic`, `.simple (.fieldGe …)`, etc., the `@[simp] admits_*` lemmas (`Guard.lean:251-289`, `Program.lean:228-253`) immediately characterize what the elaborated term admits. There is **no new metatheory to prove for the DSL** — the DSL is a *parser onto already-proved constructors*. That is the whole ergonomic win and the whole safety argument at once.

---

## 4. Worked example — a monotonic-counter and an escrow

Take the real dregg1 monotonic counter (`#[dregg_caveat] fn` with `require!(new_count >= old_count)`) and the escrow workflow.

### Counter

**DSL syntax:**
```lean
def counter : RecordProgram := dregg_program {
  invariant { monotonic count }
}

**Elaborates to** (verbatim the existing `counterProgram`, `Exec/Program.lean:258`):
```lean
RecordProgram.predicate [StateConstraint.simple (SimpleConstraint.monotonic "count")]

**Obligations:** none at definition (closed, decidable). The *property* an author asserts:
```lean
example : counter.admits 0 (.record [("count", .int 5)]) (.record [("count", .int 7)]) = true := by
  decide   -- or `dregg_vcg`; reduces via `admits_predicate` + `evalSimple` (Program.lean:124)
And the live-cell invariant comes free from `RecordCellLive.lean`: `recReplay_preserves_sumEquals` / `recCexec_attests` apply to this exact term.

### Escrow (the RDII-style workflow: deposit → release, status machine + conservation)

**DSL syntax:**
```lean
def escrow : RecordProgram := dregg_program {
  on deposit  { strictMono balance }
  on release  { status : 1 => 2 ; immutable amount }
  invariant   { conserve [locked] => [paid] }
}

**Elaborates to:**
```lean
RecordProgram.cases [
  ⟨TransitionGuard.methodIs depositSym,  [.simple (.strictMono "balance")]⟩,
  ⟨TransitionGuard.methodIs releaseSym,
     [.allowedTransitions "status" [(1, 2)], .simple (.immutable "amount")]⟩,
  ⟨TransitionGuard.always, [.sumEqualsAcross ["locked"] ["paid"]]⟩ ]
(`depositSym`/`releaseSym` are the method `Nat`s; the `elab` resolves the identifiers `deposit`/`release` to these — the one place an `elab` over a `macro` is needed.)

**Obligations generated** (the VCs the WP/VCG study discharges), read straight off the catalog semantics:
1. **default-deny soundness** — because `release`/`deposit` are method-dispatching arms, an unknown method is denied: VC `escrow.admits m old new = false` for `m ∉ {deposit, release}` follows from `admits_cases_nil`-style reasoning (`Program.lean:222,235`). *Mechanical.*
2. **state-machine totality** — `status` transitions only `1→2`; the author may want `0→1` (Open→Claimed) too, surfacing a VC that the allowed-set covers the reachable states. *Mechanical (decidable).* 
3. **conservation** — `conserve [locked] => [paid]` generates the VC discharged by `recReplay_preserves_sumEquals` (`RecordCellLive.lean:169`): `Σ locked` is preserved across every run. *Mechanical via the existing theorem.*
4. If `release` were gated on a witness (e.g. a signature/credential), the `witnessed s` atom would emit the **proof-carrying** obligation `Discharged s (w s)` (`Guard.lean:225`) — the genuinely *hard* VC, routed to the verify seam. *This is the only non-mechanical one.*

The payoff: the author wrote ~5 lines of readable surface; the elaborator produced a verified `RecordProgram` term plus four named goals, three of which close by `decide`/existing lemmas and one of which is the honest crypto-seam OPEN.

---

## 5. Open questions / risks

**Hard:**
- **Proof-carrying elaboration ergonomics.** The sigma-type approach (`{p // VC p}`) is clean but composes awkwardly when nesting `any`/`on` arms whose obligations interact. Risk: obligation explosion. Mitigation: emit obligations *only* for the witnessed/circuit/boundDelta family (everything first-party is decidable and needs none).
- **Error messages.** A `field >= v` where `field` is misspelled silently becomes a fail-closed `none` (absent field ⇒ `false`, `Program.lean:39`), not an elaboration error. The eDSL should optionally take a `Schema` (`Exec/Value.lean:56`) and `elab`-check field names against it, turning fail-closed-at-runtime into error-at-elaboration. This is the single biggest ergonomics lever and is *mechanical* but not free.
- **Choreography projection in-DSL.** DSL-B can run `project`/`Projectable` at elaboration time, but `Projectable` is a real (non-vacuous) predicate (`Coordination.lean:328`) and `deadlock_freedom_by_design`/`privacy_by_projection` are `sorry`-OPEN (`:443,534`). So `dregg_choreo` can *check projectability* (decidable via `MergesAt`) and *fail at elaboration* on a non-projectable choreography — a genuine win — but cannot yet certify deadlock-freedom. Risk: authors read "elaborated" as "deadlock-free." Mitigation: surface the OPEN explicitly.
- **Method-symbol resolution.** `on deposit` needs `deposit` → `Nat`/`[u8;32]`. Whether to hash the name (dregg1's BLAKE3 method symbol, `program.rs:137`) or assign indices is a real design choice with cross-system-compat implications.

**Mechanical:**
- All first-party atoms (the bulk of dregg1's `RequirementKind` and `SimpleStateConstraint`): pure `macro_rules` onto smart constructors, each backed by an existing `@[simp]` lemma.
- The `any`/`not` Heyting fragment: `Program.lean:251` (`evalConstraint_anyOf`), `:244` (`evalSimple_not`) already prove the algebra.
- The `RecordProgram → AIR` / multi-backend fan-out: a downstream pass over the verified term (Build 3, `RecordCircuit`), inheriting dregg1's `gen_*` structure but now provable.

---

## Recommended minimal first DSL

**Build DSL-A (the cell-program DSL), restricted to the first-party / decidable fragment of the catalog**: the `SimpleConstraint` atoms + `predicate`/`cases`/`anyOf`/`not` + `sumEquals`/`sumEqualsAcross`/`allowedTransitions`. 

Why this first:
- It is the **direct migration of dregg1's `#[dregg_caveat]`/`#[dregg_effect]`** (the highest-traffic, highest-clunk surface) onto the part of the theory that is *fully proved and `#eval`-able* (`Exec/Program.lean` + `RecordCellLive.lean` have zero `sorry`, all `#assert_axioms`-clean).
- It needs **no proof-carrying elaboration** — every atom is decidable, so the eDSL is a pure `declare_syntax_cat` + `macro_rules` parser onto existing smart constructors, the lowest-risk metaprogramming.
- It immediately yields verified, runnable programs (the counter/escrow examples above) whose invariants are the *already-proved* `recReplay_preserves_sumEquals` / `recCexec_attests`.
- It establishes the elaboration core (syntax category, field-name discipline, optional `Schema` checking) that DSL-B (choreography) and DSL-C (effects/linearity) and the witnessed/proof-carrying extension all reuse.

Defer the `witnessed`/`circuit`/`boundDelta` atoms (they need the verify seam and proof-carrying elaboration — the WP/VCG study's job) and DSL-B/DSL-C until the core is proven out.

---

### Critical files for implementation
- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Exec/Program.lean` — the `RecordProgram`/`StateConstraint` catalog + `admits` evaluator; DSL-A's elaboration target and smart constructors.
- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Spec/Guard.lean` — the `Guard` primitives + derived smart constructors (`monotonic`, `sumEquals`, `senderAuthorized`, `attenuate`); the Guard-form elaboration target and the witnessed seam.
- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Exec/RecordCellLive.lean` — the live-cell invariants (`recCexec_attests`, `recReplay_preserves_sumEquals`) that elaborated programs inherit as VCs.
- `/Users/ember/dev/breadstuffs/metatheory/Dregg2/Conserve.lean` — the existing `syntax`/`macro_rules` idiom (`:182`) to follow for the eDSL grammar, plus `Dregg2/Tactics.lean` for `#assert_axioms`/`elab` patterns.
- `/Users/ember/dev/breadstuffs/dregg-dsl/src/ir.rs` and `/Users/ember/dev/breadstuffs/dregg-dsl/src/lib.rs` — the dregg1 surface + IR + multi-backend structure being migrated (the `RequirementKind`→catalog map and the codegen fan-out to preserve as post-elaboration passes).
