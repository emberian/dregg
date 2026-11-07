/-
# Dregg2.Intent.Match — the solver as a coend `∫^B`, and the bilateral lens fill.

Phase 2, layer 3 (`.docs-history-noclaude/rebuild/metatheory/PHASE-2-INTENT-SPEC.md`; spine `INTENT-AS-CO-RECEIPT.md` §3,
`INTENT-REFS-optics.md`). Bilateral matching ("I want C, you offer C") is the easy case. A real
**exchange** routes demand to supply *through intermediate resources*: an intent `A ⊢ C` is filled by a
chain `A → B → C` assembled from available offers, existentially over the intermediate `B`. That
existential-over-the-middle is a **coend**:

```
  Match(A, C)  =  ∫^B  Offer(A → B) × Offer(B → C)          (solver = coend assembly)
```

This is the profunctor-optic / Tambara composition law, and the categorical content of an AMM router /
a multi-hop swap. We **reuse mathlib's coend** (`CategoryTheory.Limits.Types.coend`, brand-new in v4.30:
`coend F = Quot (coendRel F)` over the offer profunctor). For the offer profunctor, `Offer(A → B)` = the
free conversions `A ⟶ B` of the resource theory (a conversion IS an offer) — so the coend is the
density/co-Yoneda `∫^B (A ⟶ B) × (B ⟶ C)`, whose elements are the *routes* from `A` to `C`.

Per the spec: the FIRST app (the auction) models the bilateral fill as a simple **lens** (get/put) and
keeps the heavy coend for the multi-hop exchange — so the auction proof does NOT depend on the coend
machinery. We build the coend `Match` (non-vacuous; multi-hop typechecks) AND the lens fill; the auction
uses the lens. The coend's co-Yoneda **collapse** `Match A C ≅ (A ⟶ C)` (§5) is the density theorem
`∫^B (A⟶B)×(B⟶C) ≅ (A⟶C)`: a route's content IS its composite. It is **now proved** — the obstruction
was mathlib v4.30's brand-new coend API threading every functorial action through the bundled `TypeCat`
hom-coercion (`TypeCat.Hom.hom`), which does not reduce under `simp`/`dsimp`/`aesop_cat`. We crack it at
the term level: two reduction lemmas (`offer_leftLeg`, `offer_rightLeg`) compute the two coend legs
through the coercion explicitly (`hom_ofHom` + the category identities), and then the collapse descends
through `Quot.lift`/`Quot.sound` against `Types.coendRel_iff`. Both round-trips hold, giving the full
categorical `Iso` in `Type u` (`collapseIso`) and the underlying `Equiv` (`collapseEquiv`).

Restricted to `[SmallCategory R]` (the auction's `DemoRes` is small) so the coend universes pin cleanly.
Pure.
-/
import Mathlib.CategoryTheory.Limits.Types.End
import Mathlib.CategoryTheory.Functor.Currying
import Dregg2.Intent.Core
import Dregg2.Tactics

universe u

namespace Dregg2.Intent

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [SmallCategory R]

/-! ## 1. The offer profunctor `Offer(A → ·) × (· → C)`. -/

/-- **The offer pairing** `(X, Y) ↦ (A ⟶ Y) × (X ⟶ C)`: covariant in the covariant slot `Y` (an offer
into `Y` postcomposes), contravariant in `X` (an offer out of `X` precomposes). This is the bifunctor
whose coend over the diagonal is the solver. -/
def offerPairing (A C : R) : Rᵒᵖ × R ⥤ Type u where
  obj p := (A ⟶ p.2) × ((Opposite.unop p.1) ⟶ C)
  map {p q} f := ↾fun x => (x.1 ≫ f.2, f.1.unop ≫ x.2)

/-- The offer **profunctor** `Rᵒᵖ ⥤ R ⥤ Type`, curried for mathlib's coend. -/
def offerProf (A C : R) : Rᵒᵖ ⥤ R ⥤ Type u := Functor.curryObj (offerPairing A C)

/-! ## 2. `Match` = the coend (the multi-hop solver). -/

/-- **`Match A C = ∫^B (A ⟶ B) × (B ⟶ C)`** — the set of routes from `A` to `C` through some
intermediate resource `B`, as mathlib's coend `Quot (coendRel (offerProf A C))`. The coend quotients by
dinaturality (reparametrizing the intermediate `B`), so a route is identified with its composite. The
solver, first-class. -/
def Match (A C : R) : Type u := Types.coend.{u, u, u} (offerProf A C)

/-- **`oneHop k`** — a DIRECT conversion `k : A ⟶ C` as a one-hop route (intermediate `B := A`, with the
trivial first leg `𝟙 A`). Non-vacuity: every conversion is a match. -/
def oneHop {A C : R} (k : A ⟶ C) : Match A C := Quot.mk _ ⟨A, (𝟙 A, k)⟩

/-- **`twoHop B f g`** — a genuine MULTI-HOP route `A →[f] B →[g] C` through the intermediate `B`. This
typechecks as an element of `Match A C` — the `∫^B` is real (the auction's offer-generated resource
theory, Phase 4, populates it with non-identity offers; in the discrete demo `R`, routing forces the
hops through equal objects). -/
def twoHop {A C : R} (B : R) (f : A ⟶ B) (g : B ⟶ C) : Match A C := Quot.mk _ ⟨B, (f, g)⟩

/-- **`Converts A C → Nonempty (Match A C)`** — the match relation `⪰` (`Intent/Resource.lean`) lifts to
the solver: any convertibility witness is a (one-hop) route. The converse — collapsing a route back to a
single conversion (the co-Yoneda reduction `Match A C ≅ (A ⟶ C)`) — is now proved as `collapseIso` (§5);
so in fact `Nonempty (Match A C) ↔ Converts A C` (`match_iff_converts`). -/
theorem match_of_converts {A C : R} (h : Converts A C) : Nonempty (Match A C) :=
  h.elim fun k => ⟨oneHop k⟩

/-! ## 3. The bilateral lens fill (the auction's path — get/put optics).

`INTENT-REFS-optics.md`: an optic is a `get`/`put` pair. For a bilateral fill, the lens IS a direct
conversion: `get` extracts the offered `A`, `put` installs the produced `C`. No coend needed (the
intermediate is trivial). This is what the auction proof uses; `Match` (§2) is the multi-hop
generalization the lens embeds into (`toMatch`). -/

/-- **A bilateral lens fill** `A ⊸ C` — the get/put optic for a direct fill: it carries the conversion
`convert : A ⟶ C`. (`get` = the offered `A` consumed by `convert`; `put` = the produced `C`.) -/
structure LensFill (A C : R) where
  /-- The direct conversion filling the hole. -/
  convert : A ⟶ C

/-- A lens fill IS a convertibility witness (the thin match relation). -/
theorem LensFill.converts {A C : R} (l : LensFill A C) : Converts A C := ⟨l.convert⟩

/-- A bilateral lens fill embeds into the coend solver as a one-hop route — the lens is the trivial
case of the `∫^B`. -/
def LensFill.toMatch {A C : R} (l : LensFill A C) : Match A C := oneHop l.convert

/-! ## 4. Bridge to `Intent.fulfill` + non-vacuity on the demo resource theory. -/

/-- A fulfilled intent's receipt yields a bilateral lens fill `offered ⊸ outcome` (the conversion it
carries) — connecting the discharge keystone (`Intent/Core.lean`) to the solver layer. -/
def FillReceipt.lensFill {Stmt Wit : Type}
    {B : Dregg2.Authority.Blocklace.Lace} {reg : Dregg2.Authority.Predicate.Registry Stmt Wit}
    {stmtOf : Dregg2.Time.Frame.FrameStatement → Stmt} {i : Intent R B reg stmtOf}
    (r : FillReceipt i) : LensFill i.offered r.outcome :=
  { convert := r.conversion }

/-- **Non-vacuity: a concrete match exists** — the demo intent's fulfillment (`demoReceipt`, 1 art ⟶ 1
art) yields a lens fill, hence a one-hop route in `Match (res 0 1) (res 0 1)`. -/
def demoMatch : Match (res 0 1) (res 0 1) := demoReceipt.lensFill.toMatch

/-- **Non-vacuity: the multi-hop `∫^B` typechecks** — a two-hop route through the intermediate `res 0 1`
(in the discrete demo the hops are identities; Phase 4's offer-generated theory makes them real). -/
def demoMultiHop : Match (res 0 1) (res 0 1) :=
  twoHop (res 0 1) (𝟙 (res 0 1)) (𝟙 (res 0 1))

/-- The demo convertibility witness lifts to the solver. -/
theorem demo_match_nonempty : Nonempty (Match (res 0 1) (res 0 1)) :=
  match_of_converts (Converts.refl' _)

/-! ## 5. The co-Yoneda collapse `Match A C ≅ (A ⟶ C)` — the density theorem.

The coend `∫^B (A⟶B)×(B⟶C)` reduces to the homset `A ⟶ C`: a route's categorical content is exactly its
composite, and the coend's dinaturality quotient says reparametrizing the intermediate `B` along any
`f : B ⟶ B'` does not change that composite (`(a, f≫b)` and `(a≫f, b)` both compose to `a≫f≫b`). This is
the standard co-Yoneda / density isomorphism; mechanizing it against mathlib v4.30's coend API requires
descending through the bundled `TypeCat.Hom.hom` coercion at the term level (it does not reduce under
tactics), which the two leg lemmas below do explicitly.

The two coend legs (the maps whose images `coendRel.mk` identifies) computed through the `TypeCat`
coercion. For `f : j ⟶ j'` and `x : (A ⟶ j) × (j' ⟶ C)`:

* **`offer_leftLeg`** `(F.map f.op).app j` (reparametrize the SOURCE of the second leg) sends
  `(a, b) ↦ (a, f ≫ b)` — the intermediate becomes `j`, the route is `A →[a] j →[f≫b] C`.
* **`offer_rightLeg`** `(F.obj (op j')).map f` (reparametrize the TARGET of the first leg) sends
  `(a, b) ↦ (a ≫ f, b)` — the intermediate becomes `j'`, the route is `A →[a≫f] j' →[b] C`.

These two `rfl`-after-`simp` reductions are the entire fight with the coercion; everything else is
`Quot.lift` / `Quot.sound` term-surgery. -/
theorem offer_leftLeg (A C : R) {j j' : R} (f : j ⟶ j')
    (x : ((offerProf A C).obj (Opposite.op j')).obj j) :
    TypeCat.Hom.hom (((offerProf A C).map f.op).app j) x = (x.1, f ≫ x.2) := by
  simp only [offerProf, offerPairing, Functor.curryObj, TypeCat.hom_ofHom,
    Category.comp_id, Quiver.Hom.unop_op]
  rfl

theorem offer_rightLeg (A C : R) {j j' : R} (f : j ⟶ j')
    (x : ((offerProf A C).obj (Opposite.op j')).obj j) :
    TypeCat.Hom.hom (((offerProf A C).obj (Opposite.op j')).map f) x = (x.1 ≫ f, x.2) := by
  simp only [offerProf, offerPairing, Functor.curryObj, TypeCat.hom_ofHom,
    CategoryTheory.unop_id_op, Category.id_comp]
  rfl

/-- **`collapse`** — the forward map `Match A C → (A ⟶ C)`: a route `A →[a] B →[b] C` collapses to its
composite `a ≫ b`. Well-defined on the coend quotient because the two legs (`offer_leftLeg`,
`offer_rightLeg`) compose to the same thing by associativity — that IS dinaturality for this profunctor.
This is the co-Yoneda counit (the density of representables). -/
def collapse {A C : R} : Match A C → (A ⟶ C) :=
  Quot.lift (fun p => p.2.1 ≫ p.2.2) (by
    rintro p q h
    cases h with
    | mk f x =>
      rw [offer_leftLeg, offer_rightLeg]
      dsimp only
      rw [Category.assoc])

@[simp]
theorem collapse_oneHop {A C : R} (k : A ⟶ C) : collapse (oneHop k) = k := by
  show 𝟙 A ≫ k = k
  rw [Category.id_comp]

/-- The collapse of a genuine two-hop route is the composite of its hops. -/
@[simp]
theorem collapse_twoHop {A C : R} (B : R) (f : A ⟶ B) (g : B ⟶ C) :
    collapse (twoHop B f g) = f ≫ g := rfl

/-- **`oneHop_collapse`** — the round-trip `oneHop ∘ collapse = id`. EVERY route equals its composite
seen as a one-hop route: this is the nontrivial direction, the actual *density*. It descends through
`Quot.ind` and discharges the resulting coend equality by `Quot.sound` against `coendRel_iff` with the
explicit reparametrizing witness `(f := a, y := (𝟙 A, b))`. -/
theorem oneHop_collapse {A C : R} (q : Match A C) : oneHop (collapse q) = q := by
  induction q using Quot.ind with
  | mk p =>
    obtain ⟨B, a, b⟩ := p
    show oneHop (a ≫ b) = Quot.mk _ ⟨B, (a, b)⟩
    apply Quot.sound
    refine (Types.coendRel_iff (F := offerProf A C) _ _ _ _).mpr ?_
    refine ⟨a, (𝟙 A, b), ?_, ?_⟩
    · exact offer_leftLeg A C a (𝟙 A, b)
    · exact (offer_rightLeg A C a (𝟙 A, b)).trans (Prod.ext (Category.id_comp a) rfl)

/-- **The co-Yoneda density `Equiv`** `Match A C ≃ (A ⟶ C)` — the underlying type-level bijection of the
collapse: routes through an arbitrary intermediate are in canonical bijection with direct conversions. -/
def collapseEquiv (A C : R) : Match A C ≃ (A ⟶ C) where
  toFun := collapse
  invFun := oneHop
  left_inv := oneHop_collapse
  right_inv := collapse_oneHop

/-- **The co-Yoneda density `Iso`** `Match A C ≅ (A ⟶ C)` in `Type u` — the full categorical
isomorphism: `∫^B (A⟶B)×(B⟶C) ≅ (A⟶C)`. This is the solver's *soundness-and-completeness* as a single
iso: every route collapses to a conversion (`hom = collapse`) and every conversion is a route
(`inv = oneHop`), with both round-trips (`hom_inv_id`, `inv_hom_id`). The multi-hop router and the
bilateral lens fill (§3) compute the *same* answer up to this iso — `LensFill.toMatch` is `inv`. -/
def collapseIso (A C : R) : Match A C ≅ (A ⟶ C) where
  hom := ↾collapse
  inv := ↾oneHop
  hom_inv_id := by
    ext q
    exact oneHop_collapse q
  inv_hom_id := by
    ext k
    exact collapse_oneHop k

/-- With the collapse proved, membership in the solver is EXACTLY convertibility — the honest direction
(`match_of_converts`) now has its converse: a route yields its collapsed conversion. -/
theorem match_iff_converts {A C : R} : Nonempty (Match A C) ↔ Converts A C :=
  ⟨fun ⟨q⟩ => ⟨collapse q⟩, match_of_converts⟩

end Dregg2.Intent

/-! ## Axiom-hygiene pins — the kernel triple only (`propext`, `Classical.choice`, `Quot.sound`).
`Quot.sound` is load-bearing here: the coend IS a quotient, and the density round-trip
(`oneHop_collapse`) closes a coend equality by `Quot.sound`. -/
#assert_axioms Dregg2.Intent.offer_leftLeg
#assert_axioms Dregg2.Intent.offer_rightLeg
#assert_axioms Dregg2.Intent.collapse
#assert_axioms Dregg2.Intent.oneHop_collapse
#assert_axioms Dregg2.Intent.collapse_oneHop
#assert_axioms Dregg2.Intent.collapseEquiv
#assert_axioms Dregg2.Intent.collapseIso
#assert_axioms Dregg2.Intent.match_iff_converts
