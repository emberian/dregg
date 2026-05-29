# study-category — stress-testing the dregg2 categorical model

> **Brief:** does the dregg2 category (`dregg2.md §1` coalgebra + `§1.6` ⊗ + `§2` the
> two laws; `discoveries §3` corrections) actually hold together, or does the
> categorical framing hide lurking impossibilities? Tags: `[HOLD]` survives stress ·
> `[STRAIN]` holds but only under a stated restriction · `[BREAK]` the categorical claim
> as written is false / ill-typed. The fulcrum question throughout: **where is the
> category load-bearing (catches a real bug) vs decorative (cosplay)?**
>
> Sources read: `metatheory/Metatheory/{Core,Laws,Boundary}.lean` (the actual
> encodings), `pdfs/{mathematical-theory-of-resources,selinger-graphical-languages,
> coalgebraic-semantics-silva,guarded-recursion-coinductive}`, `pdfs/discoveries.md §3`,
> `circuit/src/bilateral_aggregation_air.rs`, `cell/src/program.rs`.

---

## 0. TL;DR verdict

| Claim | Status | One-line |
|---|---|---|
| Cell = final coalgebra `νF`, `F X = Obs × (AdmTurn ⇒ X)` | **[HOLD]** | Moore coalgebra; final coalgebra exists; bisimulation = soundness is clean. |
| **Cross-cell turn = morphism on `νF₁ ⊗ νF₂`** | **[BREAK→reframe]** | `νF₁ ⊗ νF₂` is **not** the final coalgebra of a product behaviour, and the doc never claimed the *coalgebra* tensors — it tensors the *category objects*. The honest reframe (the binding is an equalizer/pullback *outside* the coalgebra map) is correct; the slogan "`⊗` of coalgebras" is the load-bearing lie to retire. |
| `Σ_k` strong-monoidal functor, constant on non-mint/burn homs | **[STRAIN]** | It is a **monoid homomorphism on objects** (an additive monotone forced to `=`), not a functor *on the morphism category* in the encoded sense; "constant on a hom-set" is a property of the object-map, and it is **only** functorial if the category is set up so endpoints determine the count. Coherent, but the word "functor" is doing less work than it sounds. |
| `Predicate ⊣ Witness` Galois + VERIFY/FIND seam | **[HOLD]** | Genuinely structural, not bolted on — it *is* the admissibility-arrow's domain selector (§1.5), and the Heyting residual *is* attenuation. The single most coherent part. |
| GC = reachability side-condition on `ν` | **[HOLD]** | Absorbs cleanly; no new categorical machinery. |

**The single most important coherence-finding is in §1: the tensor.** It is the one
place the category is *load-bearing* — it catches a real architectural fact (cross-cell
joint soundness is irreducible to per-cell soundness) — *precisely by failing* to be
what the slogan says. The metatheory's Boundary module must encode the binding as an
**external joint obligation**, never as a derived clause of a tensored `step`.

---

## 1. The tensor of coalgebras — the load-bearing finding `[BREAK→reframe]`

### 1.1 The subtlety, stated precisely

A cell is the final `F`-coalgebra `νF`, `F X = Obs × (AdmTurn ⇒ X)`. The dregg2 claim
(`§1.6`) is that a turn over N cells is a *morphism* on the tensor `νF₁ ⊗ … ⊗ νFₙ`, with
the cross-cell binding an equalizer/pullback. The question the user wants stressed: **is
`νF₁ ⊗ νF₂` itself a coalgebra of the right shape — does codata tensor cleanly?**

**Answer: No, and the model is right not to need it to.** Two facts:

1. **The carrier tensors; the *finality* does not.** `νF₁ ⊗ νF₂` (a product of two
   carriers in the cartesian base, or a `⊗` in a symmetric-monoidal base) is a perfectly
   good *object*. But it is **not** the carrier of the final coalgebra of any single
   behaviour functor `G` whose successors range over the joint state. The final coalgebra
   of the *product* behaviour `G X = (Obs₁×Obs₂) × ((AdmTurn₁×AdmTurn₂) ⇒ X)` is
   `ν(F₁×F₂)`, and there is a canonical **comparison map** `ν(F₁×F₂) → νF₁ × νF₂` (pair the
   two anamorphisms) but **no inverse in general** — a joint behaviour carries
   *correlation* between the two streams that the product of the two final coalgebras
   forgets. Final coalgebras do **not** preserve products in this direction; only the
   *forgetful* direction is canonical. (This is the dual of the well-known fact that
   initial algebras don't tensor; cf. the resource-theory SMC never being cartesian,
   `mathematical-theory-of-resources §2`, and Selinger's no-`Δ`/`◇`, `§6`.)

2. **What *does* tensor cleanly is the guard, not the coalgebra.** Guarded recursion's
   `▶` modality preserves products via a canonical iso `can : ▶X × ▶Y ≅ ▶(X×Y)`
   (`guarded-recursion-coinductive`, denotation of `g(t₁,…,tₙ)`). This is exactly the
   productivity-level fact dregg2 leans on — and it is *strictly weaker* than the final
   coalgebra tensoring. It buys "the joint unfold is productive," **not** "the joint
   unfold is the final object." So even at the guard level, the support for "⊗ of codata"
   is a productivity iso, not a finality iso.

### 1.2 Consequence — exactly the doc's own §10 honesty note, sharpened

`dregg2 §10` already says: *"the type composes via `⊗` cleanly, but soundness of a
cross-cell turn is not reducible to per-cell soundness alone — it needs the joint
agreement binding as an irreducible extra."* **This study confirms that note and
upgrades it from a caveat to a theorem-shaped constraint:**

> **Cross-cell joint-soundness sits OUTSIDE the single-cell coalgebraic frame.** The
> binding is a morphism into an equalizer in the *base* category, not a clause of any
> coalgebra structure-map `c : X → F X`. There is no functor `F⊗` whose final coalgebra
> is `νF₁ ⊗ νF₂` and whose `step` *contains* CG-2/CG-5.

This is **grounded in code**: `bilateral_aggregation_air.rs` enforces CG-2 (turn-identity
agreement: every cell's row agrees on `TURN_HASH`/`EFFECTS_HASH_GLOBAL`/`ACTOR_NONCE`/
`PREVIOUS_RECEIPT_HASH`) and CG-5 (cross-side existence: every half-edge has its peer) as
**per-row constraints over a single shared trace holding all N cells' rows** — i.e. a
joint predicate over the tuple, declared per-cell by `StateConstraint::BoundDelta {
peer_cell, peer_slot, delta_relation: EqualAndOpposite }` (`program.rs:747`). A single
cell's `program.evaluate(old,new,ctx)` (§1.5, the `AdmTurn ⇒ Cell` arrow) **cannot**
discharge CG-2: it has no access to the peer's row. The agreement is structurally a
pullback over the shared `TURN_HASH`; the balance is structurally the equalizer.

### 1.3 Where the category is LOAD-BEARING here

This *is* the category catching a real bug, not cosplay. If you believed the slogan
("a cross-cell turn is just a morphism on the tensored coalgebra"), you would expect
cross-cell soundness to **fall out of** per-cell step-completeness — and you would build
a Boundary module that proves joint soundness by conjoining two single-cell
`sound_of_step_complete` instances. **That would be unsound:** two cells can each be
locally step-complete (each conserves *its own* slot, each has a valid auth path) while
the cross-cell turn they purport to share **does not exist as one turn** (mismatched
`TURN_HASH`) or **does not balance** (`Σ half-edges ≠ 0`). The tensor's failure to be
final is *precisely* the formal reason CG-2 ⊗ CG-5 must be an irreducible extra
obligation. The category earns its keep by forbidding the tempting wrong factoring.

### 1.4 Mandate for the metatheory Boundary module

`Boundary.lean` today defines `TurnCoalg` for a **single** cell (carrier `X`, `step : X →
F X`) and `sound_of_step_complete` over that single carrier. **This is correct and should
not be "fixed" by adding a tensored coalgebra.** Instead, Boundary must add a *separate*,
explicitly-joint object:

```
-- a cross-cell turn is a span/tuple, NOT a coalgebra step
structure JointTurn (T₁ T₂ : TurnCoalg Obs AdmTurn) where
  t      : AdmTurn                          -- the ONE shared turn
  agree  : turnId (T₁.next x₁ t) = turnId (T₂.next x₂ t)   -- CG-2 (pullback)
  balance: halfEdges x₁ t + halfEdges x₂ t = 0            -- CG-5 (equalizer)

theorem joint_sound :
    StepComplete T₁ … → StepComplete T₂ … → JointTurn T₁ T₂ → JointSound …
```

i.e. **joint soundness = (per-cell step-completeness) ∧ (the equalizer/pullback binding)**,
with the binding as a *hypothesis you must supply*, never a lemma you derive from the two
coalgebras. This matches `§1.6`'s "CG-2 ⊗ CG-5" and `§10`'s honesty note exactly.

---

## 2. The conservation functor `Σ_k` `[STRAIN — coherent, but "functor" overstated]`

### 2.1 What is actually encoded

`Core.lean` encodes `Σ_k` as `ConservationFunctor.count : Cell → Nat` — a map on
**objects only** — plus laxator placeholders `unit_zero` (`count I = 0`) and `tensor_add`
(`count (A⊗B) = count A + count B`). The conservation law `conservation_ordinary` is then
`f.tag = ordinary → count A = count B`: the *object-map agrees on the two endpoints of an
ordinary morphism*. Mint/burn shift it by their declared amount (`mint_delta`,
`burn_delta`).

### 2.2 Is "constant on a hom-set" actually functorial?

**Two readings, and the doc conflates them:**

- **Reading A (what's encoded — coherent):** `Σ_k` is a **strong monoidal functor to the
  one-object category `(ℕ,+,0)` viewed discretely** — i.e. it sends every morphism to the
  identity of `(ℕ,+)` *as a monoid element*, and the real content is the **object-map**
  `count`, which is a monoid homomorphism `(|TurnCat|, ⊗, I) → (ℕ,+,0)`. "Constant on
  every non-mint/burn hom-set" then means: an ordinary `f : A⟶B` forces `count A =
  count B`. This is well-typed and respects ⊗ via `tensor_add`. **It does NOT break
  functoriality** — because to a discrete/one-object target *every* hom maps to the same
  identity, so composition is preserved trivially (`id ∘ id = id`). This is precisely an
  **additive monotone forced from `≥` to `=`** (`resources §5.3`: an additive monotone
  with `M(0)=0` *is* a monoid hom; dregg strengthens `≥` to `=` because mint/burn are the
  only count-movers). `discoveries §3.2`'s "invariance, not monotone" is right and
  defensible.

- **Reading B (the tempting over-claim — would break):** if one read `Σ_k` as a functor
  *into the poset `(ℕ,≤)` as a thin category* whose morphisms are `≤`-steps, then "constant
  on a hom-set" is fine (it's the object-map again), **but** then mint/burn morphisms must
  map to genuine `<` arrows and you have re-imported the monotone `≥` framing the model
  explicitly rejects — and worse, a thin `(ℕ,≤)` target **cannot carry the symmetry iso**
  Law 1 needs (`discoveries §3.2`'s own warning against "thin posetal"). So Reading B is
  self-contradictory; the model must mean Reading A.

### 2.3 The strain, named

The strain is purely *nomenclature*: calling `count` a "functor" invites Reading B and the
swarm's own thin-category trap. The **load-bearing object is the monoid homomorphism on
the object-monoid** `(|TurnCat|, ⊗) → (ℕ,+)`, with conservation = "ordinary morphisms are
hom-set-constant for it." It is coherent (Reading A), but the metatheory should state it as
`count` is a `MonoidHom` and conservation is an *invariance property of the morphism class*,
rather than leaning on "strong monoidal functor" — which, with a discrete target, is
true-but-vacuous on morphisms and therefore decorative. **Verdict: HOLD as a monoid-hom +
invariance; the "functor" dressing is DECORATIVE and slightly misleading.** Per-asset
folding (`§6.1`, the value rib) is the real soundness content and is independent of the
functor framing.

---

## 3. `Predicate ⊣ Witness` Galois + the VERIFY/FIND seam `[HOLD — most coherent]`

This is the part that is **most** load-bearing and **least** decorative.

- `Laws.lean` encodes `Verifiable.Verify : P → W → Bool` (decidable, the TCB), `Searchable.
  find : P → Option W` (opaque, no completeness/termination), and `search_sound` (the sole
  contract: returned witnesses verify). This *is* the VERIFY/FIND seam, and it is honest:
  the asymmetry (verify decidable, find undecidable — `§4`'s `HOU ⪯ GeneralMatch`) is
  baked into the *types* (`Bool` vs `Option`), not asserted in prose.
- The Galois connection (`predicate_witness_galois`) + Heyting residual (`predicate_heyting`:
  `a⊓b ≤ c ↔ a ≤ b⇨c`) is **coherent with the monoidal/coalgebraic structure, not bolted
  on**, because it *is* the structure-map's domain selector: `§1.5` says the `CellProgram`
  *is* the `AdmTurn ⇒ Cell` arrow, and its domain is `{t | ⋀cᵢ}` — a meet in the predicate
  Heyting algebra. **Attenuation = the residual `⇨`** (a stricter predicate entails a laxer
  one); this is the *same* `⇨` that `Authority/Positional.lean`'s `LossyMorphism` uses for
  "a key may only narrow." So the Galois/Heyting fragment threads through three modules
  (Laws → Core's admissibility → Authority's attenuation) coherently.
- `discoveries §3.4`'s downgrade from heavy `Adjunction` to `GaloisConnection` +
  `HeytingAlgebra` (both posetal) is the right call: it is the *thin* fragment, and lives
  comfortably *beside* the non-thin symmetric-monoidal Core (`§2.1`'s "thin only in its
  ordering fragment"). No incoherence.

**One seam to watch (not a break):** the predicate order `≤` (entailment) and the witness
order `≤` (specificity) must be pinned for the Galois connection to typecheck —
`predicate_witness_galois` takes `l`/`u` as free placeholders. Until those two preorders
are concretely the slot-caveat entailment and the witness-refinement orders, the connection
is *stated* but not *grounded*. This is a `sorry`-discharge task, not a coherence defect.

---

## 4. GC, the runtime character, and the rest `[HOLD]`

- **GC (`§1.7`):** absorbs as a reachability side-condition on `ν` ("while reachable, the
  unfold never bottoms out"). No new machinery; the drop-protocol is the backward face of
  the await engine. Coherent. The coinductive frame genuinely does *not* strain here
  (confirmed against `§10`'s honesty note).
- **Runtime as theorems (checkpoint/restore/replay/time-travel):** these are anamorphism
  re-seeding facts about `νF`; standard codata, coherent.
- **Ordering / Law 2 (`§2.2`):** correctly held *out* of the proof and off the SMC — it is
  the thin join-semilattice fragment with the I-confluence side-condition. The decision to
  make tier-1 eligibility a *static type error* unless the cell-state is an
  invariant-preserving bounded join-semilattice (`discoveries §3.7`, BEC) is the category
  doing real work: it's a well-formedness condition the type system can check. **HOLD,
  load-bearing.**

---

## 5. Verdict — is more categorical detail needed, or is the level right?

**More detail is warranted in exactly one place: the cross-cell tensor (§1).** Everywhere
else the current level is right or *over*-specified (the "strong monoidal functor" framing
of conservation is more decoration than the monoid-hom needs). Specifically:

1. **Add the joint-turn object to the metatheory** (`§1.4`): an explicit `JointTurn`/
   equalizer structure with `joint_sound` taking the binding as a hypothesis. This is the
   one categorical refinement that prevents a real unsoundness (the wrong factoring of
   §1.3). **This is the load-bearing addition.**
2. **Retire the "⊗ of coalgebras" slogan**; replace with "the carriers tensor in the base;
   the binding is an equalizer; finality does not transport." The doc's `§10` note is
   already 90% there — promote it into `§1.6` body, don't leave it as a closing caveat.
3. **Demote "conservation functor" to "conservation monoid-hom + invariance."** Keep the
   SMC (it carries the symmetry Law 1 needs); drop the functorial-on-morphisms framing as
   vacuous-on-a-discrete-target.

**Where category = load-bearing (catches real bugs):** (a) the **tensor non-finality**
forcing CG-2⊗CG-5 to be irreducible — the single most important finding; (b) the
**no-`Δ`/`◇` (no copy/discard)** structural statement of conservation; (c) the **Heyting
residual = attenuation** thread; (d) the **I-confluence join-semilattice** tier-1
eligibility type-error.

**Where category = decorative (cosplay risk):** (a) "strong monoidal *functor*" for
conservation (the content is a monoid-hom; functoriality is vacuous on a discrete target);
(b) any reading of the cross-cell story as "tensoring coalgebras," which actively misleads.

**Bottom line:** the model **holds together** — but only because its own `§10` honesty
note quietly does the work the `§1.6` headline slogan overclaims. The category is genuinely
load-bearing, and it earns that status *by exposing*, not hiding, that **cross-cell
joint-soundness is an irreducible extra outside the coalgebraic frame.** Encode that
honestly in `Boundary.lean` and the model is coherent at the right level of detail.
