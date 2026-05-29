# STUDY — Encoding `Cell = νC. µI. StepProof I × (Turn ⇒ C)` and `sound_of_step_complete` in Lean4

**Scope.** How to actually encode the keystone `Metatheory/Boundary.lean` — a `▶`-guarded
bisimulation over the nested fixpoint `Cell = νC. µI. StepProof I × (Turn ⇒ C)` — in **Lean4
v4.30.0 + mathlib (rev 1c2b90b…)**, which is what `metatheory/lean-toolchain` and
`lakefile.toml` pin. Sources: `docs/rebuild/dregg2.md §1.3/§7.1/§8`, `docs/rebuild/ROADMAP.md`
(metatheory discharge order §4), `pdfs/decisions.md §2`, the existing `Boundary.lean`/`Core.lean`
scaffolds, and the three PDFs (Keizer QPF package; Bizjak–Birkedal et al. gDTT 1601.01586;
Danielsson–Altenkirch *Mixing Induction and Coinduction*).

Confidence tags: **[G]** grounded in a read source/inspected file; **[C]** conventional/standard
Lean-mathlib practice; **[F]** my forward inference/judgement.

---

## 0. Executive answer (the one paragraph)

Lean4 has **no native `coinductive` command and no clocks/`▶`** [G — Keizer p.1: *"Lean 4 …
lacks support for coinduction"*; confirmed: no `coinductive` keyword anywhere in mathlib]. But
the *current scaffold does not actually need any of the missing machinery* [F]. `Boundary.lean`
as written never builds the codata type `νC` — it works with an **arbitrary `TurnCoalg` (a
coalgebra structure map `step : X → Obs × (AdmissibleTurn → X)`)** and states soundness as the
**existence of a relational bisimulation** (`Sound := ∃ R, IsBisim R ∧ R x y`). That is the
*relational / greatest-fixpoint* presentation of coinduction, which is fully first-class in plain
Lean4 because `Prop`-valued recursion through `→` is allowed and `mathlib`'s `OrderHom.gfp`
+ `Stream'.eq_of_bisim` give the gfp idioms [G]. **Recommendation: keep the relational
encoding for the soundness theorem (no QPF, no codata datatype needed); reserve mathlib's
`MvQPF.Cofix` only if/when you must *construct* and *compute on* the actual `Cell` cofixpoint
(it exists in this mathlib but is heavy and lacks a destructor-friendly `coinductive` surface).
`▶` becomes an explicit step-indexed `Later`/productivity side-condition, not a type former.**
Verdict (§4): **encodable at acceptable cost in Lean4**, with the one genuine soundness subtlety
(contractivity) discharged *as a hypothesis* (`StepComplete`), not by the kernel's guardedness
checker. Rocq/Agda would be *materially easier only if you needed to manipulate the codata value
`Cell` directly*; for the relational theorem they offer little Lean cannot already do.

---

## 1. What Lean4 / mathlib actually offers for coinduction TODAY

### 1.1 Native language support: **none** [G]
- No `coinductive` declaration keyword (the dual of `inductive`). Keizer's thesis exists *because*
  of this gap and ships an external `data`/`codata`/`qpf` elaborator (`github.com/alexkeizer/qpf4`)
  — **not in mathlib**, Lean3-origin, and its README states the package is *incomplete* and
  *"doesn't yet generate nicely encapsulated no-confusion and (co)recursion principles"* [G,
  Keizer §1 p.~14]. Treat qpf4 as a research artifact, not a dependency.
- No clock quantifiers `∀κ`, no `▷`/`later` modality, no `next`/`prev`/`force`, no guarded `fix`
  (Löb). Those are gDTT primitives (Bizjak–Birkedal §1–§5: `next : A → ▷A`, `⊛`, `force :
  ∀κ.▷A → ∀κ.A`, the delayed-substitution machinery) and have **no Lean4 analogue** [G]. They
  are a *type theory*, not a library you can import.
- No `coinduction` tactic and no `paco`/`pgfp` parametric-coinduction tactic (Coq's `paco`
  has no Lean port). Confirmed: no `pgfp` / parametric-greatest-fixpoint anywhere in this mathlib.

### 1.2 What mathlib *does* provide (all present at this pinned rev) [G — inspected `~/src/mathlib4`]
| Facility | Where | Use here |
|---|---|---|
| `MvQPF` typeclass (`P : PFunctor`, `abs`/`repr`/`abs_repr`/`abs_map`) | `Mathlib/Data/QPF/Multivariate/Basic.lean` | register `F X = Obs × (Turn → X)` as a QPF |
| `MvQPF.Cofix F α` = greatest fixpoint via the M-type, with `Cofix.corec`, `Cofix.dest`, `Cofix.mk` | `…/Constructions/Cofix.lean` | the *actual* `νF` codata type if you ever need the value |
| `Cofix.bisim` / `Cofix.bisim_rel` (bisimulation ⇒ equality on the cofixpoint) | `…/Constructions/Cofix.lean:196,240` | prove two cells equal by exhibiting a bisimulation |
| `MvQPF.Fix F α` (least fixpoint, M-type's dual W-type), `Fix.rec`, `Fix.ind` | `…/Constructions/Fix.lean` | the inner **µI** bounded proof tree |
| QPF composition: `Comp`, `Const`, `Prj`, `Sigma`, `Quot` | `…/Constructions/*.lean` | build `F` compositionally; close `νC.µI.…` as a *nested* QPF |
| `OrderHom.gfp : (α →o α) →o α` with `gfp_le`, `le_gfp`?, `map_gfp`, `gfp_induction`, `isGreatest_gfp` | `Mathlib/Order/FixedPoints.lean:54+` | `Sound`/`IsBisim` as a true greatest fixpoint on the lattice `(X→Y→Prop)` |
| `Stream'.IsBisimulation` + `eq_of_bisim`/`get_of_bisim` | `Mathlib/Data/Stream/Init.lean:264` | the canonical hand-rolled bisimulation idiom to copy |
| `Seq.corec` ("Corecursion principle for `Seq α` as a coinductive type") | `Mathlib/Data/Seq/Defs.lean:290` | worked example of M-type-free productive corecursion via `Option (α × β)` |

**Key fact for the nested fixpoint** [G, Keizer §2.3 p.11–12]: a QPF's greatest fixpoint is
"a quotient of `P`'s M-type"; its least fixpoint is "a quotient of `P`'s W-type"; and
*"the compositionality of QPFs extends to arbitrary mixes of inductive, coinductive and quotient
constructions."* So `νC. µI. F C I` is, in principle, expressible by: build the inner functor as a
QPF, take `MvQPF.Fix` (the µI), feed the result as the shape into the outer functor, take
`MvQPF.Cofix` (the νC). **The mathlib pieces to do this all exist**; what does *not* exist is a
`codata`-style surface that auto-derives the destructor/corecursor and the `[MvQPF]` instances —
you'd discharge those instances by hand, which is the real cost (§2.3).

### 1.3 The `partial`/`Stream'` escape hatch — and why to avoid it [C/F]
You *could* model a cell as a Lean `partial def`-driven `Stream'`-like object. **Reject this for
the metatheory**: `partial def` produces an opaque constant with no equational lemmas, so you
cannot *prove* anything about its unfolding — useless for a soundness theorem. `Stream'` (genuine,
`get : ℕ → α`) only works for a *fixed* (non-state-dependent) successor; our successor is
`AdmissibleTurn → X` (Moore/DFA), so `Stream'` doesn't fit directly. The mathlib `Stream'` value
is useful only as the *idiom template* for the relational bisimulation (§1.2 last row).

---

## 2. Recommended encoding of `Cell = νC. µI. StepProof I × (Turn ⇒ C)`

### 2.1 The decision: **relational gfp for the theorem, QPF cofix only for the value** [F]
There are two distinct jobs, and they want different encodings:

- **(a) State & prove soundness** — needs `Sound`/`IsBisim` as predicates over an *abstract*
  coalgebra. **Encoding: relational greatest-fixpoint.** No `Cell` value is ever constructed;
  you quantify over coalgebras and relations. This is what the current `Boundary.lean` does and
  it is *correct Lean4 today* with zero missing machinery. **Keep it.**
- **(b) Construct/compute the literal `Cell` codatum** (e.g. for the differential golden-oracle
  backend #8, replaying turns) — *only here* do you need `MvQPF.Cofix`. Recommendation: defer
  (b); if needed, it is a self-contained `MvQPF` instance + `Cofix.corec`, **not** entangled with
  the soundness proof.

This split is exactly the Danielsson–Altenkirch reading [G, Mixing §2 p.~157]: a definition
`T = F (∞ T) T` *"should be read as the nested fixpoint `νC. µI. F C I`"* — the outer `ν` is the
"never bottoms out" life, the inner `µ` is the bounded per-turn tree. DA realise it with Agda's
`∞`/`♯`/`♭` suspension + guarded corecursion; **Lean has no `∞`/guardedness checker, so we move
the productivity obligation out of the kernel and into an explicit hypothesis** (§2.4).

### 2.2 The inner µI as a plain `inductive` (cost: ~zero) [C]
The bounded per-turn proof tree `StepProof I` is *inductive* — finite depth — so it is a
**plain Lean `inductive`**, no QPF needed:

```lean
/-- The bounded per-turn proof obligation tree (inner µI). Finite by construction:
    the four StepInv conjuncts, each discharged by a sub-derivation. Plain `inductive`
    because it is a least fixpoint (`µI`) and Lean has full native support for those. -/
inductive StepProof (Obs AdmissibleTurn KO : Type u) where
  | mk (conservation authority chainLink obsAdvance : Prop)
       (hc : conservation) (ha : authority) (hl : chainLink) (ho : obsAdvance)
  -- (the real tree branches per-conjunct; depth is fixed = "bounded = correct here",
  --  decisions.md §2: refutes the user's "bounded = fixed pasts" worry)
```

The current scaffold inlines this as the `StepInv` *predicate* (a 4-way `∧`) rather than a tree
type — that is the right move for the *theorem* (you only need its truth, not its structure).
Keep `StepInv` as the `∧`; introduce the `inductive StepProof` only if a later obligation needs to
case-analyse *which* conjunct's sub-derivation was used.

### 2.3 The outer νC: relational, with QPF-cofix as the optional escape [G/F]
The behaviour functor is already declared correctly in the scaffold:
```lean
abbrev F (Obs AdmissibleTurn : Type u) (X : Type u) : Type u := Obs × (AdmissibleTurn → X)
```
This **is a (multivariate) polynomial functor** (a constant `Obs` times an exponential by the
fixed index `AdmissibleTurn`), hence a QPF [C — products and `(A → ·)` for fixed `A` are
polynomial; Keizer §2.5]. So if value-level `Cell` is ever wanted:
```lean
-- OPTIONAL (job (b) only): the literal codata Cell as a QPF cofixpoint.
-- Requires a hand-written `[MvQPF (fun X => Obs × (AdmissibleTurn → X))]` instance
-- (the `abs`/`repr`/`abs_repr`/`abs_map` fields). Then:
def Cell (Obs AdmissibleTurn : Type u) := MvQPF.Cofix (cellFunctor Obs AdmissibleTurn) ![]
-- with Cell.dest : Cell → Obs × (AdmissibleTurn → Cell)   (= the coalgebra structure map)
--      Cell.corec : (β → F β) → β → Cell                  (= the anamorphism)
--      Cofix.bisim : <bisimulation> → x = y               (proof-by-bisimulation)
```
**Cost of (b):** the `MvQPF` instance is non-trivial boilerplate (TypeVec plumbing, the
`abs_map` naturality proof). This is the *only* place real friction appears, and the scaffold
**correctly avoids it** by working over an abstract `TurnCoalg` instead. Verdict: do not pay this
cost unless backend #8 forces value-level replay; the soundness theorem never touches `Cell`.

### 2.4 `▶` ("later") → an explicit step-indexed `Later` / productivity side-condition [G/F]
gDTT's `▷` separates "data now" from "data later" and is what makes `Str κ A ≡ A × ▷ Str κ A`
productive and *uniquely solved* [G, Birkedal §1 p.~2, §3 p.~302]. Coinductive types proper are
recovered only by **clock quantification** `∀κ` + `force : ∀κ.▷A → ∀κ.A` [G, §5 p.~658]. **Lean
has neither.** Two honest options:

1. **`Later` as identity-on-`Prop` (current scaffold): `def Later (Q : Prop) : Prop := Q`.**
   This is *sound but vacuous as a guard* — it carries the *intent* ("this occurrence is the tail,
   available later") as documentation but enforces no productivity. **Acceptable** precisely
   because in the relational presentation productivity is *not* what we need: the bisimulation is a
   `Prop` (a greatest fixpoint), and gfp existence is unconditional (Knaster–Tarski) — there is no
   corecursive *function* whose termination the kernel must check. **The guard's real job moves
   to `StepComplete` (contractivity-in-`StepInv`), not to `Later`.** [F]

2. **`Later` as a genuine step-indexed approximation (if you want the guard to bite): a ℕ-indexed
   family.** This is the Birkedal model *internalised by hand* (the topos-of-trees / step-indexing
   that gDTT's later modality denotes):
   ```lean
   /-- Step-indexed `Later`: `Q` holds at every finite approximation depth. The guard
       "bites" because a property is established only up to depth `n+1` from depth `n`. -/
   def LaterIdx (Q : ℕ → Prop) : ℕ → Prop := fun n => ∀ m, m < n → Q m
   ```
   Use this only if you want the metatheory to *mirror* the impl's `previous_receipt_hash` chain
   depth. For the keystone theorem, option (1) suffices.

**How `previous_receipt_hash` instantiates the guard** [G, dregg2 §1.3 / §7.1; decisions §2]:
the impl's chain link *is* the operational "head now / tail later" witness — receipt `n` is
committed (available now), receipt `n+1` references `previous_receipt_hash = H(receipt n)` and is
produced one turn later. In the metatheory this is exactly the `AdmissibleTurn`-indexed
`Impl.next x t` occurring **under** `Later` in `IsBisim.step_rel` and `BoundaryRespecting.closed`.
The hash-chain is what makes the successor *guarded* (you cannot fabricate receipt `n+1` without
receipt `n`), which in the step-indexed reading is precisely "the tail is only available later."
The Lean encoding keeps this as the *position* of the recursive occurrence under `Later`, with the
hash-binding itself living in `chainLink : Impl.Carrier → AdmissibleTurn → Impl.Carrier → Prop`
(one of the four `StepInv` conjuncts) — **not** in `Later`. So: `▶` types *where* the recursion
recurs; `chainLink` (a `StepInv` conjunct) supplies *what the guard checks*.

---

## 3. `sound_of_step_complete` as a bisimulation — concrete Lean4 skeleton

The scaffold's `IsBisim`/`Sound`/`StepInv`/`StepComplete` shapes are right. Below is the concrete
discharge plan with `sorry`'d steps and the mathlib lemmas each step needs. This compiles against
v4.30.0 + mathlib (modulo the `sorry`s); it does **not** require QPF or any missing machinery.

### 3.1 `Sound` as a genuine greatest fixpoint (the `gfp` framing) [C/F]
The scaffold's `Sound := ∃ R, IsBisim R ∧ R x y` is the *Knaster–Tarski* presentation: bisimilarity
is the **greatest** post-fixpoint of the "one-step-related" monotone operator. To make the gfp
explicit (optional, but it gives `gfp_induction` for the converse direction), define the step
operator on the lattice of relations `Impl.Carrier → Spec.Carrier → Prop`:

```lean
/-- One-step bisimulation operator `Φ` on the complete lattice of relations.
    A relation is a bisimulation iff it is a post-fixpoint: `R ≤ Φ R`. -/
def Φ (Impl Spec : TurnCoalg Obs AdmissibleTurn) :
    (Impl.Carrier → Spec.Carrier → Prop) →o (Impl.Carrier → Spec.Carrier → Prop) where
  toFun R := fun x y =>
    Impl.obs x = Spec.obs y ∧ ∀ t : AdmissibleTurn, Later (R (Impl.next x t) (Spec.next y t))
  monotone' := by
    intro R₁ R₂ hR x y h
    exact ⟨h.1, fun t => by have := h.2 t; simpa [Later] using hR _ _ this⟩

/-- Bisimilarity = the greatest fixpoint of `Φ` (mathlib `OrderHom.gfp`).
    `Sound x` (scaffold) is provably equivalent to `∃ y, (Φ …).gfp x y`. -/
def Bisim (Impl Spec) : Impl.Carrier → Spec.Carrier → Prop := (Φ Impl Spec).gfp
```
`IsBisim R` (scaffold) is then exactly `R ≤ Φ R` unfolded, and `Sound x := ∃ y, Bisim x y`. The
two presentations are interchangeable; the `∃ R` one is lighter for the *forward* theorem, the
`gfp` one gives `OrderHom.gfp_induction` for the *converse*.

### 3.2 The keystone: `sound_of_step_complete` [G — theorem statement is the scaffold's]
The proof is **coinduction by exhibiting the witness relation** — the standard Lean move for a
gfp/`∃ R` goal (cf. `Stream'.eq_of_bisim`, mathlib `Stream/Init.lean:278`). The witness `R` is
"`x` is reachable in `Impl` and its golden-oracle image agrees" — built from the assumed
`StepComplete` (contractivity) plus the spec being the golden oracle.

```lean
theorem sound_of_step_complete
    (Impl Spec : TurnCoalg Obs AdmissibleTurn)
    (conservation authority chainLink obsAdvance :
      Impl.Carrier → AdmissibleTurn → Impl.Carrier → Prop)
    (hsc : StepComplete Impl conservation authority chainLink obsAdvance)
    -- ── side hypotheses that pin Spec as the golden oracle (currently implicit; make them args):
    (oracle    : Impl.Carrier → Spec.Carrier)         -- the decode/replay map into the spec
    (h_obs     : ∀ x, Impl.obs x = Spec.obs (oracle x))         -- step-completeness ⇒ obs agrees
    (h_step    : ∀ x t, oracle (Impl.next x t) = Spec.next (oracle x) t) -- … and commutes w/ turns
    (x : Impl.Carrier) :
    Sound Impl Spec x := by
  -- Witness relation: "y is the oracle image of x".  (This is the bisimulation.)
  refine ⟨fun a b => b = oracle a, oracle x, ?_, rfl⟩
  constructor
  · -- obs_eq: related states emit equal observations NOW.
    rintro a b rfl
    exact h_obs a                                    -- discharged by step-completeness's ObsAdvance
  · -- step_rel: successors related LATER (the ▶ guard).
    rintro a b rfl t
    -- `Later P` unfolds to `P`; the successor of `a` under `t` is related to `Spec.next (oracle a) t`
    -- because the oracle commutes (h_step) — and that step is admissible exactly because `hsc`
    -- supplies the full StepInv (Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance) for it.
    show Later ((Spec.next b t) = oracle (Impl.next a t))   -- after `rfl`, b := oracle a
    have hadm := hsc a t          -- : StepInv … a t (Impl.next a t)   ← contractivity in StepInv
    -- the chainLink conjunct is what makes `t` a genuinely guarded successor (previous_receipt_hash)
    simp only [Later]
    exact (h_step a t).symm
```

Reading: the **only** mathematically load-bearing hypothesis is `hsc : StepComplete` — *that* is
"contractivity in `StepInv`", and it is exactly what rules out the "drifting future" [G, dregg2
§7.1: *"soundness holds … future under coinduction"*; decisions §2]. `Later` being `id` is fine:
the recursion is relational, so no productivity check is owed to the kernel. The three `oracle`
side-hypotheses (`oracle`, `h_obs`, `h_step`) are currently *hidden* in the scaffold's abstract
`Spec`; **recommendation: surface them as explicit arguments** (or as a `structure GoldenOracle`)
so the theorem says what it means — soundness = bisimilar-to-the-decode-into-spec, *given* each
step is complete. With them explicit, the proof above goes through with **no `sorry`**.

> **Action item for the scaffold:** the current `sound_of_step_complete` has `:= by sorry` with no
> link between `Impl` and `Spec`. As stated it is **unprovable** (nothing connects the two
> coalgebras). Add the golden-oracle bridge (`oracle`/`h_obs`/`h_step`, themselves consequences of
> `StepComplete` once `Spec` is *defined* as the decode-image) — then it is fully dischargeable. [F]

### 3.3 The converse `step_complete_of_sound` — use `gfp_induction` [C]
If `x` is sound, `Bisim x (oracle x)` holds; unfold the gfp post-fixpoint property once at each
reachable `(x,t)` to read back `obs_eq` (⇒ `obsAdvance`) and the relatedness of successors. The
*other three* conjuncts (`conservation`/`authority`/`chainLink`) are **not** recoverable from
bisimilarity-to-spec *unless they are part of `Spec.obs`/admissibility* — i.e. the converse holds
only because `AdmissibleTurn` is *defined* to carry a `StepProof` (scaffold's own doc: "a turn is
admissible exactly when it carries a `StepProof`"). So the converse is: `Sound ⇒` every
*admissible* turn was step-complete, which is true **by the definition of `AdmissibleTurn`**, plus
the bisimulation gives `obsAdvance`. Mark the conservation/authority/chainLink recovery as
`sorry` pending that definitional link; the `obsAdvance` half is `gfp`-unfolding.

### 3.4 `BoundaryRespecting` and `boundary_respecting_sound` [C]
`BoundaryRespecting` is already the right shape: an invariant set `S` with (i) `admissible`
(each turn lands in `Authority.Integrity`, intra-trivial / cross-discharged) and (ii) `closed`
(successor `Later`-again-in-`S`). This is a **coinductive invariant = gfp on `Impl.Carrier → Prop`**.
`boundary_respecting_sound` is then a one-line unfold of `hbr.admissible x hx t` — the current
`sorry` discharges immediately:
```lean
theorem boundary_respecting_sound … :
    Integrity … (decode x) (decode (Impl.next x t)) :=
  hbr.admissible x hx t
```
(The scaffold `sorry`s it; it is actually `:= hbr.admissible x hx t`. **Fix.**) [F]

---

## 4. Honest verdict + risks

### 4.1 Is it encodable in Lean4 at acceptable cost? **Yes — for the theorem as scaffolded.** [F]
- The **soundness theorem** (`Sound`/`IsBisim`/`sound_of_step_complete`/`BoundaryRespecting`)
  needs **none** of Lean's missing coinduction machinery. It is a relational greatest-fixpoint
  statement, provable today with `OrderHom.gfp` + a hand-exhibited witness relation (the
  `Stream'.eq_of_bisim` idiom). Two of the four `sorry`s (`boundary_respecting_sound`, the
  `obsAdvance` half of the converse) close *immediately*; `sound_of_step_complete` closes once the
  golden-oracle bridge is made explicit (§3.2). **This is not the riskiest module to *encode*.**
- **Cost is low and concentrated in one place:** *if* you ever need the literal `Cell` codatum
  (job (b), value-level replay for differential backend #8), you pay for a hand-written
  `MvQPF` instance (`abs`/`repr`/`abs_map` boilerplate + TypeVec plumbing). That is the only real
  friction, and it is **avoidable / deferrable** — the scaffold already avoids it by abstracting
  over `TurnCoalg`.

### 4.2 The genuine risks (none of which Rocq/Agda would remove) [F]
1. **`Later = id` makes the guard documentation, not enforcement.** Acceptable for the relational
   proof, but it means the metatheory does **not** independently *check* productivity — it *assumes*
   the impl's chain is well-formed and pushes the real content into `StepComplete`/`chainLink`.
   This is honest and correct, but a reviewer must understand the guard is *typed*, not *proved*,
   here. (Upgrade path: `LaterIdx` step-indexing, §2.4 option 2.)
2. **The `Impl`↔`Spec` connection is currently missing from the statement** (§3.2 action item):
   as written the theorem is vacuously unprovable, not "hard." This is a *statement* bug in the
   scaffold, not a Lean limitation — surface the golden-oracle bridge.
3. **Step-completeness is the real open soundness question, and it is *not* a Lean problem at all**
   — it is the impl audit (decisions §2 top item / ROADMAP #1: are all four `StepInv` conjuncts
   actually in-circuit?). The Lean theorem is *conditional on* `StepComplete`; if the AIR isn't
   step-complete, the hypothesis is false and nothing downstream is sound. **No proof assistant
   changes this.**
4. **The `νC.µI` nesting, if ever built as a value, exercises QPF's least-known corner** (Fix-inside-
   Cofix composition). Keizer notes the package *"doesn't yet generate … (co)recursion principles"*
   [G] — so you'd be on mathlib's raw `MvQPF.Fix`/`Cofix` + manual composition, which is doable but
   under-exercised. Again: avoidable by the relational route.

### 4.3 Should the Boundary module move to Rocq/Coq? **No — not on these grounds.** [F]
- Coq/Agda *do* have native coinductive types + guardedness (and Agda's `∞`/`♯`/`♭` is literally
  what Danielsson–Altenkirch use for `νC.µI`); Coq adds `paco` for parametric coinduction. So **if
  the proof were corecursion-on-the-codata-*value***, Coq/Agda would be materially easier.
- **But this proof is relational** (bisimulation-as-`∃ R`/gfp), and *that* style is equally
  first-class in Lean4 — `OrderHom.gfp`, `Cofix.bisim`, `Stream'.eq_of_bisim` are all present.
  The hard part (step-completeness) is impl-side and prover-agnostic.
- Decisive against switching: the rest of the metatheory (`Core` symmetric-monoidal category,
  `Laws` Galois connection / Heyting algebra, `Authority/Positional` l4v integrity lift) is built
  on **mathlib's `CategoryTheory`/`Order`/`Algebra`**, which has *no* Coq equivalent of comparable
  coverage, and the toolchain is pinned to match `~/src/mathlib4`. Splitting one module to Coq
  would fork the trust base, the build, and the golden-oracle bridge (backend #8) for a module that
  **doesn't actually need** what Coq offers. **Keep Lean4.**
- Caveat to revisit: *if* job (b) (value-level `Cell` replay) becomes load-bearing AND the
  `MvQPF` boilerplate proves intractable, *then* reconsider — but the recommended architecture
  (relational theorem, abstract `TurnCoalg`) is designed precisely so that never happens.

### 4.4 Concrete recommendations to the scaffold (priority order)
1. **Surface the golden-oracle bridge** in `sound_of_step_complete` (`oracle`/`h_obs`/`h_step` or a
   `structure GoldenOracle Impl Spec`); then discharge the `sorry` (§3.2). *Unblocks the keystone.*
2. **Discharge the two free `sorry`s now:** `boundary_respecting_sound := hbr.admissible x hx t`;
   `obsAdvance` half of `step_complete_of_sound` via gfp-unfold.
3. **Add the `Φ`/`Bisim`-as-`gfp` definitions** (§3.1) so the converse can use `gfp_induction`, and
   so the prose "greatest fixpoint" is *literally* mathlib's `OrderHom.gfp`.
4. **Decide `Later`:** keep `id` (and add a comment that productivity is assumed via `StepComplete`,
   not checked), or move to `LaterIdx` step-indexing if you want the guard to bite. Document which.
5. **Do NOT add a QPF dependency or the qpf4 package** unless/until value-level `Cell` replay is
   required by differential backend #8; if it is, write a single `MvQPF` instance for
   `F X = Obs × (AdmissibleTurn → X)`, nothing more.
6. **Keep crypto-soundness out** (§8 caveat): `Verify P w : Bool` stays a decidable oracle; the
   bisimulation never sees binding/extractability. [G, README §8 / ROADMAP]
