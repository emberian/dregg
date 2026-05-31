# FOUNDATIONS — the turn as an effect theory, the cell as its comodel, the three faces as a lens

> **What this is.** A READ-ONLY categorical-foundations excavation of dregg2 through ONE lens:
> *the turn is a guarded comodel of an effect theory; the cell is the comodel; the three faces
> (effects / caveats / attestation) are the get / put / guard of a lens.* This is the central
> claim of `DREGG4-UNIFICATION §5`. The job here is to **separate the theorem from the slogan**:
> for every categorical claim I tag it
>
> - **REAL** — the universal property / law is actually PROVED in the Lean (at `file:line`);
> - **DECORATIVE** — suggestive notation/vocabulary that buys no theorem (I say what it would
>   have to prove to become real);
> - **ASPIRATIONAL** — claimed by the design but actually a `sorry` / OPEN / unmodeled.
>
> **Sources read in full:** `study-category.md`, `cand-A-vat-coalgebra.md`, `cand-B`, `cand-C`,
> `DREGG4-UNIFICATION.md`, `CARRY-FORWARD-SYNTHESIS.md`, `GLOSSARY.md`; and the actual Lean:
> `Dregg2/{Boundary,Core,Resource,Confluence,Finality,JointTurn,DSLEffect,CatalogEffects,
> Await,StepCamera}.lean`, `Dregg2/Spec/VatBoundary.lean`, `Dregg2/Authority/{CaveatChain,
> DesignatedVerifier}.lean`, `Dregg2/Exec/EffectsAuthority.lean`, `Dregg2/Proof/CoinductiveAdversary.lean`,
> `Dregg2/Coordination.lean` + `DSLChoreo.lean`.
>
> **The single most important finding up front:** the *lens / optic / comodel* vocabulary
> appears **nowhere** in the Lean. A `grep` of `Dregg2/` for `lens|get-put|put-get|put-put|
> comodel|cohandler|optic` returns one hit — and it is the word "lens" used metaphorically in a
> comment in `Authority/Caveat.lean:7`. There is no `Lens` structure, no get/put pair, no lens
> law, no `Comodel` typeclass, no comodel-homomorphism. **The lens/comodel framing is a
> design-doc reading of the existing coalgebra, not a piece of established metatheory.** The
> coalgebra `F X = Obs × (AdmissibleTurn → X)` is real (`Boundary.F`); reading its three
> components *as* get/put/guard is, at present, exposition.

---

## 1. The functor and its three components — what is actually there

`Boundary.lean:66` defines the behaviour functor literally:

```
abbrev F (Obs AdmissibleTurn : Type u) (X : Type u) : Type u :=
  Obs × (AdmissibleTurn → X)                              -- Boundary.lean:66-67
structure TurnCoalg (Obs AdmissibleTurn : Type u) where  -- Boundary.lean:74-78
  Carrier : Type u
  step    : Carrier → F Obs AdmissibleTurn Carrier
def TurnCoalg.obs  (T) (x)   : Obs := (T.step x).1        -- Boundary.lean:81
def TurnCoalg.next (T) (x t) : T.Carrier := (T.step x).2 t -- Boundary.lean:87-89
```

This is a **Moore/DFA coalgebra** (output-on-state `obs`, transition-on-input `next`). That
much is REAL and unambiguous. The three-faces reading maps onto it as:

| Face | `DREGG4-UNIFICATION §2.1` reading | Where it lives in `F` | Lean status |
|---|---|---|---|
| **attestation** = lens **get** | the view `Obs` that crosses the boundary | `(T.step x).1` (`TurnCoalg.obs`) | the *projection* is REAL; "get of a lens" is DECORATIVE |
| **effects** = lens **put** | the state update | `(T.step x).2 t` (`TurnCoalg.next`) | the *transition* is REAL; "put" is DECORATIVE |
| **caveats** = lens **guard** = the *domain* of the arrow | which turns are admissible (`AdmissibleTurn` carved from `AllTurn`) | the *type* `AdmissibleTurn` (kept abstract, `Boundary.lean:56`) | the carving predicate is NOT in `F` — it is the abstract index type. The guard's *content* (verify/discharge) lives in `Authority/*`, disconnected from `F`. |

**Verdict on the headline "the three faces are the three components of the coalgebra `c`"
(`DREGG4-UNIFICATION §2.1`): DECORATIVE-but-honest.** `F` genuinely has exactly two components
(`Obs` and the function), and the third "face" (caveats) is not a *component* of `F` at all — it
is the *domain restriction* of the second component, which in the Lean is just the abstract type
`AdmissibleTurn` with no predicate attached. So the slogan "three components of `c`" is really
"two components of `c` plus the type of the arrow's domain." There is no theorem that the caveat
predicate, the effect transition, and the attestation projection are *the* canonical
factorization of anything. To become REAL it would need: (a) `AdmissibleTurn` defined as a
`Σ`-type `{t : AllTurn // Guard t}` so the caveat face is literally the first projection of the
admissibility witness, and (b) a theorem that `step` factors through that — neither exists.

---

## 2. The lens laws — get-put, put-get, put-put

This is the crux the task asks. **There is no lens in the Lean, so there are no lens laws — REAL
or otherwise.** I checked: no `Lens`/`Optic`/`get`/`put` definitions, and no statement resembling
`get (put s a) = a` (put-get), `put s (get s) = s` (get-put), or `put (put s a) b = put s b`
(put-put). Tag: **ASPIRATIONAL** (claimed nowhere as a `sorry` either — it is simply not
attempted).

It is worth being precise about *why* the lens framing is a poor fit for what is actually proved,
because that tells us what the framing would buy if pursued:

- A **lens** `S ⇄ (P,U)` is a pair `get : S → P`, `put : S × U → S` satisfying the three laws —
  it is a *bidirectional state accessor* (you can read a view and write it back). The turn is
  **not** that shape. `next : Carrier → AdmissibleTurn → Carrier` does **not** take a *view* `P`
  and write it back; it takes a *turn* `t` (an input letter), not an `Obs`. There is no
  `put : Carrier × Obs → Carrier` anywhere, so **get-put / put-get are not even type-correct**
  against the actual `obs`/`next`. The honest categorical name for `F X = Obs × (Input → X)` is a
  **Moore coalgebra / a (very degenerate) Mealy machine**, not a lens. `DREGG4-UNIFICATION §5.1`'s
  "`c : X → Obs × (AdmissibleTurn ⇒ X)` is `(get, put-with-guarded-domain)`" silently retypes
  `put` from `S × U → S` to `Input → S`, which is the coalgebra's transition map, not a lens put.
- The one place a genuine **lens law shape** *could* be stated and is closest to being earned is
  the **Galois connection** `Predicate ⊣ Witness` (`study-category §3`), which IS a real adjoint
  pair — but that is an adjunction on the *caveat/witness* posets, not a get/put lens on cell
  state, and even it is "stated but not grounded" (`study-category §3`: `predicate_witness_galois`
  takes the two orders as free placeholders). So the nearest real adjunction in the system is
  **not** the lens the doc means.

**What it would take to make a lens law REAL here.** The only honest bidirectional structure in
the system is the **disclosure dial** (`Privacy.lean` field visibility) read against the committed
head: a `get = disclose` (cell → revealed view) and a `put = setField`-style update, with
get-put = "disclosing then re-committing the same value is identity" and put-get = "what you wrote
is what you disclose." That would be a real (very small) lens with real laws — and it is *not the
turn*; it is the disclosure projection of one face. The turn-as-lens claim conflates this
plausible small lens with the whole coalgebra.

---

## 3. The comodel-of-an-effect-theory claim

`DREGG4-UNIFICATION §5.2`: "the effect signature (`Core`/`CatalogEffects`) is an algebraic theory
`T`; the cell is a `T`-comodel (it cohandles operations against its state); the turn is one step
of cohandling; caveats are the equations/guards; attestation is the residual the comodel emits."

What is actually in the Lean:

### 3a. The effect *signature* — REAL as a coloring, DECORATIVE as a "theory"
`CatalogEffects.lean` is genuinely solid: `EffectKind` (the ~52 dregg1 effect tags) with a total
coloring `effectLinearity : EffectKind → LinearityClass` transcribed from `Effect::linearity`
(`CatalogEffects.lean:46`), the six per-class conservation obligations PROVED
(`conservative_requires_paired` etc., `CatalogEffects.lean:59-101`), exhaustiveness three ways
(`effectLinearity_total`, `every_effect_classified`, `:190-219`), and a partition discriminator
(`Regime.ofClass`, `effectObligation_coincides`, `:261-295`). All `#assert_namespace_axioms`-clean.

But this is a **coloring of operation symbols by a conservation regime** (`Conservative` /
`Generative` / `Annihilative` / `Monotonic` / `Terminal` / `Neutral`) — it is **not an algebraic
theory** in the technical sense. There is no operation *arity*, no *equations* between
operation-terms, no free-model construction. An algebraic theory `T` would need a signature
`Σ : Op → (arity)` plus equations `E`; what exists is `Op → LinearityClass`, a *labeling*. The
`LinearityClass` is the "what does this op do to the conserved quantity" tag, which is closer to a
*grading* on the signature than to the theory itself.

- The genuinely effect-theory-shaped piece is `Await.lean:59-71`: an `Op` with parameter/return
  arities (`P ⟶ R`-shaped), which is the actual Plotkin–Pretnar operation symbol. So the *await*
  fragment is modeled as a real algebraic-effect signature; the *catalog* fragment is a coloring.

**Verdict: "effect signature" REAL (as a colored operation set), "algebraic theory `T`"
DECORATIVE.** To upgrade: give `EffectKind` arities and at least the conservation equations as
term equations, then the coloring becomes a *grading homomorphism* out of the free term algebra.

### 3b. The cell as the *comodel* — ASPIRATIONAL
There is no `Comodel` typeclass, no "the cell cohandles operations" structure, no statement that
the cell is the cofree/final comodel of the signature. The closest real object is `TurnCoalg`
(a coalgebra for `F`), and a comodel of an effect theory *is* a coalgebra for the induced
functor — so the **shape** is right, but the **theory→functor→comodel** chain is not built:
nothing connects `CatalogEffects.EffectLinearity` (the would-be theory) to `Boundary.F` (the
would-be comodel functor). They are different modules over different abstract types with no
bridge theorem. The claim "the cell is the free comodel" is **ASPIRATIONAL**.

### 3c. The handler as a comodel-homomorphism = a higher-order turn — ASPIRATIONAL
`DREGG4-UNIFICATION §6.4` ("user-extensible effects via theory-extension-with-refinement-proof,
the verified `Custom`") and §5.2's "handler = comodel morphism = a turn that interprets turns":
no comodel morphism is defined or proved anywhere. The `Await` module models *handlers* concretely
(`turnAsRollbackHandler`, `Await.lean:~275`) and proves the one-shot/commit/abort laws (REAL, see
§5), but a *handler* there is the rollback-effect interpreter, not a *comodel homomorphism between
two effect theories*. There is no "turn that interprets turns." **ASPIRATIONAL.**

---

## 4. capExercise as lens / comodel composition

`DREGG4-UNIFICATION §5.1, §9-surprising-5`: "`capExercise` (C5, the recursive eval map) IS lens
composition; the recursive inner-effect gating the circuit must bake is the compositional
structure of the lens, not a special case."

What the Lean actually proves about `ExerciseViaCapability` (`Exec/EffectsAuthority.lean §5`):

```
def exerciseStep (s) (actor target) : Option RecChainedState :=         -- :422
  if (s.kernel.caps actor).any (confersEdgeTo target) then some {s with log := …} else none
theorem exercise_authorized       …  -- holds the source edge        -- :446
theorem exercise_graph_unchanged  …  -- post-graph = pre-graph       -- :455
theorem exercise_non_amplifying   …  -- confers NO new authority     -- :482  (THE headline, GENUINE)
theorem exercise_unheld_fails     …  -- fail-closed                  -- :498
```

These are **REAL and good** — non-amplification on two axes (connectivity + real `List Auth`
rights), graph-preservation, fail-closed. But they are about the **authority domain only**: the
Lean `exerciseStep` *gates on holding a cap and appends a receipt*; it does **not recurse into the
inner effects at all**. The recursion into `inner_effects` is in the **Rust** (`turn/src/action.rs`
`ExerciseViaCapability { cap_slot, inner_effects }`, recursed in `conflict.rs:243`,
`finalize.rs:35/274/...`). And the Lean *linearity* of `exerciseViaCapability` is flatly `Neutral`
(`CatalogEffects.lean:176`, `EffectsState.lean:468`) — i.e. the model treats the *exercise wrapper*
as carrying no conservation content, with the inner effects' content handled as separate effects.

So: there is a **real recursive structure** (in Rust), and a **real non-amplification theorem** (in
Lean, for the wrapper's authority frame), but **no theorem stating capExercise is a composition**
of anything — no associativity, no "exercise of (exercise of e) = exercise of e composed", no lens
or comodel composition law. **Verdict: capExercise = lens composition is DECORATIVE.** The
recursive-inner-effect structure is real; calling it *lens composition* buys no theorem. To make it
REAL you would prove: (i) the inner-effect interpretation under a cap is associative/compositional
(`exercise (e₁ then e₂) ≅ exercise e₁ then exercise e₂` modulo the gate), and (ii) the
non-amplification of §5 composes down the recursion (a deep cap-chain never amplifies) — the second
is *almost* there via `attenuate`/`confers_trans` but is not stated over nested exercise.

---

## 5. What the eDSL composition actually is

`DREGG4-UNIFICATION §3`/`§5.1` treats `DSLEffect`/`DSLChoreo` as "composition in this lens
structure." Reality:

- **`DSLEffect.lean`** is a **pure parser-macro** onto already-proved `CatalogEffects` constructors.
  `dregg_effect transfer (…) : Conservative` elaborates to `transfer.color`, `transfer.regime`, and
  a *generated* `transfer.obligation : obligationProp transfer.color` whose proof is the single
  proved fact `obligation_holds` (`DSLEffect.lean:120-126`, `181`). The headline
  `transfer_color_eq_catalog : transfer.color = CatalogInstances.effectLinearity .transfer := rfl`
  (`:195`) is REAL but trivial — it is a `rfl`-coincidence pinned by `#assert_axioms`. **This is
  REAL as a faithful surface, DECORATIVE as "composition in a comodel."** It composes *nothing*: it
  is a one-effect declaration → its inherited conservation obligation. No `DSLChoreo`/`DSLEffect`
  operation sequences effects into a composite with a composite law.
- **`DSLChoreo.lean`** is likewise a parser onto `Coordination.GlobalType`, with `reqResp_eq`/
  `auction_eq` proved by `rfl` (`:155`, `:182`). The *choreography projection*
  `Coordination.project : GlobalType → Role → LocalType` (`Coordination.lean:241`) is the candidate
  for "projection is a functor `Choreo → ∏ Endpoint` = a map of comodels" (`DREGG4-UNIFICATION
  §5.3`). But `project` is **a function, not a proved functor**: `projection_sound`
  (`Coordination.lean:416`) is a `sorry`; `privacy_by_projection` is PROVED only under a `NoRec`
  hypothesis (`:567`, `#assert_axioms`-clean at `:614`); `deadlock_freedom_by_design` is restated
  and closed only over reachable configs; and the recursion fragment is CONFIRMED-OPEN. **No
  functor laws (identity/composition preservation) are stated for `project`.** So "projection is a
  functor / a map of comodels" is **ASPIRATIONAL** — `project` is a real, partially-verified
  projection *function*, not a verified functor.

---

## 6. The tensor — and an important correction the docs miss

`study-category §1` and `DREGG4-UNIFICATION §5.3/§8` lean on **"`νF₁ ⊗ νF₂` is NOT final, hence
cross-cell soundness is irreducible (CG-2 ⊗ CG-5 is a hypothesis)."** This is the system's *most
load-bearing* categorical claim. The Lean tells a sharper — and partly *self-correcting* — story:

- The comments in `JointTurn.lean:22-28` still assert `tensor_not_final` ("`νF₁ ⊗ νF₂` is NOT the
  final coalgebra of the product behaviour").
- But the **actual theorem** is `binding_is_proper` (`JointTurn.lean:333`), whose docstring
  contains an **audit correction**: *"the earlier `tensor_not_final` was **mis-stated** — the
  product of two final coalgebras IS final for the product functor, so that claim is false."* The
  true, proved content is a **proper-subobject** fact: the joint-admissible configurations are a
  proper **equalizer subobject** of the product carrier (CG-2 ⊗ CG-5 excludes some product states),
  witnessed concretely (two one-state cells with half-edges `1`, CG-5 sum `1+1 = 2 ≠ 0`).

This matters for *this lens* because `DREGG4-UNIFICATION §5.3` says "the non-finality of `νF₁⊗νF₂`
is exactly why the comodel tensor needs the CG-2⊗CG-5 binding." **That justification is built on the
mis-stated lemma.** The correct justification (and it is genuinely REAL) is the proper-equalizer
fact, not non-finality. So:

| claim | status |
|---|---|
| `νF₁ ⊗ νF₂` is not final ⇒ binding irreducible | **DECORATIVE / mis-stated** — the Lean audit (`JointTurn.lean:320-332`) refutes the premise; docs not yet updated |
| Cross-cell admissibility is a **proper equalizer subobject** of the product, so the binding cannot be derived per-cell | **REAL** — `binding_is_proper` (`:333`), `joint_sound_needs_binding` (`:271`), both PROVED, `Unit`/`ℕ` witnesses |
| `joint_sound` = per-cell step-completeness + binding-as-hypothesis ⇒ whole-run safety | **REAL** — `JointTurn.joint_sound` (`:230`), proved via `joint_stepComplete` (`:197`) + `Boundary.stepComplete_preserves` |

The "comodel tensor" language is DECORATIVE (there is no `Comodel`, no `⊗` of comodels), but the
**operational content it points at is genuinely proved**: the joint turn is the product `TurnCoalg`
(`jointCoalg`, `:158`) cut down by an externally-supplied `JointBinding` (`:134`), and the binding
is provably not recoverable from the two per-cell coalgebras.

---

## 7. The soundness keystone — does the comodel framing buy "one theorem, not three"?

`DREGG4-UNIFICATION §5.3`: "one soundness theorem, not three — the comodel is bisimilar to the
golden-oracle comodel, with `StepInv` as contractivity; the three faces are conjuncts of `StepInv`
*because* they are the three components of `c`, so they cannot drift apart by construction."

Reality in `Boundary.lean`:

- `StepInv = conservation ∧ authority ∧ chainLink ∧ obsAdvance` (`Boundary.lean:140-144`) — note
  this is **four** conjuncts (the design's "three faces" plus the chain-link guard), and they are
  **free predicate parameters**, not derived from the components of `F`. There is *no* theorem
  that these four are forced to be the projections of `c`; they are supplied externally.
- The honest keystone is **`stepComplete_preserves`** (`Boundary.lean:177`): step-completeness +
  an inductive invariant `Good` ⇒ `Good` holds along the whole run, proved via
  `Execution.invariant_run`. **REAL and clean.**
- Crucially, the comment at `Boundary.lean:156-200` records that the *original* keystone
  `sound_of_step_complete` (the bisimulation-to-an-arbitrary-Spec, which is exactly the
  "comodel bisimilar to golden-oracle comodel" the §5.3 framing wants) was **false as stated**
  (refuted with `Spec.Carrier = Empty`) and was **removed**. What survives of `Sound`/`IsBisim` is
  only **reflexivity** (`bisim_eq`, `sound_refl`, `:203/:211`).
- The genuine bisimulation result lives in `Proof/CoinductiveAdversary.lean`:
  `obsBisim_traj_of_bisim` (along any infinite schedule, if Impl and Spec *start* bisimilar they
  stay bisimilar forever) and `stepComplete_carries_infinite` (no drifting future), with a §8
  general-case derivation via the ported Paco `gupaco`. **These are REAL**, but they are
  *behavioural-equivalence + safety-preservation* results, **not** "the three faces are
  conjuncts of `StepInv` because they are the components of `c`."

**Verdict on "one soundness theorem because the faces are the components of `c`": DECORATIVE.**
The real soundness theorem (`stepComplete_preserves` + the coinductive lift) exists and is strong,
but its hypotheses (the four `StepInv` conjuncts) are *given*, not *forced by a factorization of
`F`*. The §5.3 "cannot drift apart by construction" is precisely the property that is **not**
proved — the conjuncts are independent free parameters, and a face that did nothing would *not*
automatically fail (the whole point of the de-vacuification tasks #107-#114 was that several
conjuncts *had* gone vacuous and had to be re-grounded by hand, not caught structurally).

---

## 8. The pieces that ARE real (so the lens isn't all smoke)

The lens framing is mostly exposition, but the *faces themselves* contain genuine, axiom-clean
metatheory — just not organized as a lens/comodel:

- **Caveat face (the "guard"), real chain integrity.** `Authority/CaveatChain.lean` models the
  macaroon as the actual HMAC fold `Tᵢ = mac Tᵢ₋₁ encode(Cᵢ)` (`:129`), with `verify_iff_wellTagged`
  (`:168`), append-only narrowing `append_narrows`/`append_subset` (`:223/:232`), and the
  unforgeability **reduction** `forgery_requires_mac_query`/`removal_breaks_tail` (`:305/:328`)
  stated relative to an honest §8 `MacKernel.unforgeable` portal — no faked crypto. **REAL.** This
  is the closest thing to a "guard with laws," and the law it proves (append-only attenuation only
  *narrows*) is a genuine **meet-semilattice / Heyting-residual** fact (`study-category §3`'s
  attenuation thread), which *is* a real lens-adjacent law on the caveat poset — just not get/put.
- **Attestation face (the "get"), modal indexing.** `Authority/DesignatedVerifier.lean` adds the
  verifier-indexed `DischargedFor V s p` (`:113`) and proves `public_convinces_any_third_party`
  (non-repudiation, `:176`), `designated_not_transferable` (`:206`), `designated_is_deniable` (the
  simulator/repudiation argument, `:224`), and the witnessed separation `dial_endpoints_distinct`
  (`:346`). **REAL.** This is the `Obs[t]` modal-output the §4 dial wants — and it *is* an
  indexing of the output by a parameter, which is the honest categorical content of "modality on
  the output functor" (post-composition with a `Verifier`-indexed family), even though no functor
  is formally constructed.
- **Conservation (Law 1).** `Core.lean` proves `withholding_no_free_copy` (`:209`, no conserving
  `Δ` copy under cancellation) and the mint/burn case-corollaries from one `conservation_step`
  axiom-obligation (`:154`, `sorry` — the operational discharge). The SMC `TurnCat` is a `class`
  with the `Category`/`MonoidalCategory`/`SymmetricCategory` instances left as **unfilled
  obligations** (`Core.lean:85-88`) — so "the category of cells and turns" is **ASPIRATIONAL** as a
  *Mathlib category instance*, REAL only as a monoid-hom + invariance (`study-category §2`).
- **Resource camera.** `Resource.lean` has the Iris-style PCM `ResourceAlgebra` (op/valid/core +
  the three core laws + `valid_op_left`) with `(ℕ,+)` and `Excl` cameras PROVED and the `Auth`
  camera laws `sorry`'d (`Resource.lean:71-92, 124-134`; the header notes Auth is `sorry`'d). This
  is the right home for the "partial composition can be invalid" content the monoid can't express.
- **I-confluence (the third judgement).** `Confluence.lean` is fully REAL and non-vacuous:
  `IConfluent` (`:44`), `Tier1Eligible` (`:51`), `nonpairwise_escalation` (`:70`), and both
  witnesses `top_iconfluent` (`:95`) and `cardLeOne_not_iconfluent` (`:104`).
- **Φ (vat boundary).** `Spec/VatBoundary.lean` proves `cross_vat_needs_witness`,
  `phi_drops_confinement`, `forwarded_cap_is_revocable`, `macaroon_does_not_cross_phi`,
  `phi_composes_with_attenuation` (all `#assert_axioms`-clean, `:465-474`) — but **`phi_functorial`
  is an explicit by-design `sorry` (`Spec/VatBoundary.lean:392-401`)**, with only a *concrete*
  non-degenerate witness `phi_functorial_concrete` proved (`:441`). So **Φ-being-a-functor is
  ASPIRATIONAL** exactly as the task flagged: the object-map, the named loss, the domain, and the
  attenuation-compat are REAL; the *functoriality* (the full two-category bridge over an abstract
  `Verifiable`) is the one localized open obligation.

---

## 9. The ∞-cell and the higher-order cell / higher-order turn — this lens's answer

The corpus names the *keystone type* `Cell = νC. µI. StepProof I × (Turn ⇒ C)` (`cand-A §2.1`,
`GLOSSARY:10`) — an **outer coinductive life** (`νC`, never terminates) wrapping an **inner
inductive per-turn proof** (`µI`, the bounded `StepInv` obligation tree). Through the
effect-theory / comodel / lens lens, here is the honest reading:

- **An ∞-cell is the final/cofree comodel of the effect theory: a non-terminating process whose
  every step is one cohandling of a turn, with the per-step obligation tree finite.** Concretely
  it is a point of `νF` (`Boundary`), driven forever along a `Sched` (the infinite turn stream of
  `Proof/CoinductiveAdversary.lean:76`), staying behaviourally equivalent to the golden oracle
  (`obsBisim_traj_of_bisim`). The "∞" is the **outer `ν`** — unbounded reactive life — and it is
  REAL in the Lean as the coalgebra unfold + the proved coinductive bisimulation/safety along an
  unbounded schedule. The "∞-cell" is *not* a cell with infinitely many effects; it is a cell whose
  *behaviour* is codata. The drifting-future risk (`cand-A §4`) is the lens-specific hazard: an
  ∞-comodel whose per-step cohandling is *non-contractive in `StepInv`* leaks conservation
  unboundedly — which is why the inner `µ` must be *complete* (all conjuncts), and why
  step-completeness (not recursion) is the soundness question.

- **A higher-order turn is a comodel homomorphism — a turn that re-interprets turns.** In the lens
  reading, the ordinary turn is a step of the base comodel; a *higher-order* turn is a **handler /
  interpreter** that takes the operations of one effect theory and re-expresses them as a program
  over another (the dual of a model homomorphism). The system *gestures* at three instances:
  (1) `capExercise`, which runs `inner_effects` *inside* an outer gate (Rust-real, Lean-`Neutral`,
  no composition law — DECORATIVE as "higher-order");
  (2) the **rollback handler** `turnAsRollbackHandler` (`Await.lean:~275`), a real algebraic-effect
  handler with proved one-shot/commit/abort laws (`commit_resumes_once`, `rollback_discards_
  continuation`, `one_shot_is_static` — REAL), which is the *one genuinely handler-shaped, law-
  carrying* object in the system; and
  (3) the user-extensible effect ISA (`DREGG4-UNIFICATION §6.4`), the *verified `Custom`* =
  theory-extension-with-refinement-proof — **ASPIRATIONAL** (no extension calculus, no
  comodel-morphism exists).

  So: **the only higher-order turn that is REAL today is the rollback handler** (a one-shot-
  continuation algebraic-effect handler with proved laws). The "turn that interprets turns" / the
  comodel-homomorphism / the refinement-proven custom effect are all ASPIRATIONAL.

- **A higher-order cell** in this lens is a cell whose *state includes other cells / their
  behaviours* — i.e. a comodel over a theory whose carrier is itself a comodel. The system's
  realized analogue is the **cross-cell `jointCoalg`** (a coalgebra over the product carrier
  `Carrier × Carrier`, `JointTurn.lean:158`) and the choreography `GlobalType` whose endpoints
  project to per-cell local types (`Coordination.project`). These are *first-order products and
  projections*, not genuinely higher-order (no cell whose `Obs` ranges over cells); the
  `forkSpan`/time-travel "a cell that forks its own unfold" (`cand-A §6`) would be the real
  higher-order move and is unbuilt. So **the higher-order cell is ASPIRATIONAL**; the realized
  ceiling is *product-of-cells + projection*, with the binding as an external hypothesis (§6).

**One-line answer (this lens):** the **∞-cell** is the final/cofree comodel — a codata process,
REAL as `νF` + the proved coinductive bisimulation/safety along an unbounded schedule; the
**higher-order turn** is a comodel homomorphism (a handler interpreting turns), of which only the
**rollback handler** is REAL today and the *turn-interpreting-turns* / verified-`Custom` form is
ASPIRATIONAL; the **higher-order cell** (a cell over cells, or a self-forking cell) is unbuilt —
the realized ceiling is the product `jointCoalg` plus an externally-hypothesized binding.

---

## 10. REAL / DECORATIVE / ASPIRATIONAL — the lens table

| # | Claim (effect-theory / comodel / lens lens) | Tag | Ground (file:line) / what it would take |
|---|---|---|---|
| 1 | The cell is a Moore/DFA coalgebra `F X = Obs × (AdmissibleTurn → X)` | **REAL** | `Boundary.lean:66-89` (`F`, `TurnCoalg`, `obs`, `next`) |
| 2 | The three faces (effects/caveats/attestation) are the three components of `c` | **DECORATIVE** | `F` has 2 components; "caveats" is the abstract *domain type* `AdmissibleTurn` (`:56`), not a component. Would need `AdmissibleTurn := {t // Guard t}` + a factorization theorem |
| 3 | The turn is a lens; the faces are get/put/guard | **DECORATIVE** | no `Lens`/get/put in `Dregg2/` (grep: 0 hits). `next : C → Input → C` is not a lens `put : C × U → C` |
| 4 | Lens laws get-put / put-get / put-put hold | **ASPIRATIONAL** | not stated anywhere; not even type-correct against `obs`/`next`. A real (small) lens exists only for the *disclosure* projection, not the turn |
| 5 | The effect signature is an algebraic theory `T` | **DECORATIVE** | `CatalogEffects.effectLinearity` is a coloring `Op → LinearityClass` (`:46`), no arities/equations. `Await.Op` (`:59`) *is* a real signature for the await fragment |
| 6 | Per-class conservation obligations + exhaustive coloring | **REAL** | `CatalogEffects.lean:59-101, 190-219, 261-295`, all `#assert_namespace_axioms`-clean |
| 7 | The cell is the (free/cofree) comodel of the theory | **ASPIRATIONAL** | no `Comodel`, no theory→functor→comodel bridge |
| 8 | The handler is a comodel-homomorphism = a turn that interprets turns | **ASPIRATIONAL** | no comodel morphism. The rollback *handler* exists (Await) but is not a theory-morphism |
| 9 | `capExercise` = lens composition (recursive inner-effect gating = compositional structure) | **DECORATIVE** | recursion is Rust-only; Lean `exerciseStep` (`EffectsAuthority.lean:422`) gates+receipts, no composition law. Inner linearity is `Neutral` (`CatalogEffects.lean:176`) |
| 10 | `capExercise` confers no new authority (non-amplification, graph-preserving, fail-closed) | **REAL** | `EffectsAuthority.lean:446-501` (`exercise_non_amplifying`, `exercise_graph_unchanged`, `exercise_unheld_fails`) |
| 11 | eDSL (`DSLEffect`/`DSLChoreo`) = composition in the structure | **DECORATIVE** | parser-macros onto proved constructors; `rfl`-coincidences pinned (`DSLEffect.lean:120-126,195`; `DSLChoreo.lean:155,182`). Composes nothing |
| 12 | Choreography projection is a functor `Choreo → ∏ Endpoint` (map of comodels) | **ASPIRATIONAL** | `Coordination.project` (`:241`) is a function; `projection_sound` is `sorry` (`:416`); no functor laws. `privacy_by_projection` proved only under `NoRec` (`:567`) |
| 13 | "one soundness theorem because the faces are conjuncts of `StepInv` forced by `c`" | **DECORATIVE** | the 4 `StepInv` conjuncts are free parameters (`Boundary.lean:140`), not a factorization; vacuity had to be fixed by hand (#107-114) |
| 14 | Step-completeness ⇒ whole-run safety (no drifting future) | **REAL** | `Boundary.stepComplete_preserves` (`:177`); coinductive lift `stepComplete_carries_infinite` + `obsBisim_traj_of_bisim` (`Proof/CoinductiveAdversary.lean`) |
| 15 | `sound_of_step_complete` = comodel bisimilar to golden-oracle comodel | **ASPIRATIONAL (refuted-and-removed)** | was **false as stated** (`Spec=Empty`), removed; only `bisim_eq`/`sound_refl` survive (`Boundary.lean:156-213`) |
| 16 | `νF₁ ⊗ νF₂` not final ⇒ cross-cell irreducibility | **DECORATIVE (mis-stated)** | Lean audit refutes the premise: product of finals IS final (`JointTurn.lean:320-332`) |
| 17 | Cross-cell admissibility is a proper equalizer subobject; binding is a non-derivable hypothesis | **REAL** | `binding_is_proper` (`JointTurn.lean:333`), `joint_sound_needs_binding` (`:271`), `joint_sound` (`:230`) |
| 18 | Caveat "guard" = real append-only HMAC chain with narrowing + forgery reduction | **REAL** | `Authority/CaveatChain.lean:129,168,223,305,328` (crypto as honest §8 portal) |
| 19 | Attestation "get" is a modal/indexed output `Obs[t]` (transferability dial) | **REAL** (as a `Verifier`-indexed family; not a formal functor) | `Authority/DesignatedVerifier.lean:113,176,206,224,346` |
| 20 | The dials are modalities on the output functor (lift bisimulation through the modality) | **ASPIRATIONAL** | the indexing is real (#19); "lift the bisimulation through the modality" is not stated/proved |
| 21 | Conservation `Σ_k` = monoid-hom + invariance; no free copy | **REAL** | `Core.lean:154,166,209` (`conservation_step` is the one `sorry`-obligation; corollaries proved) |
| 22 | The category of cells & turns is a symmetric-monoidal category (Mathlib instance) | **ASPIRATIONAL** | `TurnCat` is a `class` with unfilled `Category`/`MonoidalCategory`/`SymmetricCategory` instances (`Core.lean:85-88`) |
| 23 | Partial/invalid composition via Iris camera (`ℕ`, `Excl` proved) | **REAL** (Auth tier open) | `Resource.lean:71-92,124-134` (`Auth` camera laws `sorry`'d) |
| 24 | I-confluence is a genuine, falsifiable third judgement | **REAL** | `Confluence.lean:44,70,95,104` |
| 25 | Φ (vat boundary) is named-lossy: permission survives, authority doesn't | **REAL** | `Spec/VatBoundary.lean:202,240,277,314` (`#assert_axioms`-clean) |
| 26 | Φ is a *functor* between positional and epistemic authority categories | **ASPIRATIONAL** | `phi_functorial` is a by-design `sorry` (`Spec/VatBoundary.lean:392-401`); only `phi_functorial_concrete` proved (`:441`) |
| 27 | Higher-order turn = the rollback handler (one-shot algebraic-effect handler) | **REAL** | `Await.lean` `turnAsRollbackHandler`, `commit_resumes_once`, `one_shot_is_static`, `four_faces_unify` (`:138,308,426`) |
| 28 | Higher-order turn = a turn interpreting turns / verified-`Custom` theory extension | **ASPIRATIONAL** | no extension calculus, no comodel morphism (`DREGG4-UNIFICATION §6.4` is design-only) |
| 29 | ∞-cell = final/cofree comodel (codata process), bisimilar-forever along any schedule | **REAL** (as `νF` + coinductive lift); "comodel" naming DECORATIVE | `Proof/CoinductiveAdversary.lean` (`obsBisim_traj_of_bisim`, `stepComplete_carries_infinite`) |
| 30 | Higher-order cell (cell over cells / self-forking cell) | **ASPIRATIONAL** | realized ceiling is product `jointCoalg` + external binding (`JointTurn.lean:158`); `forkSpan` unbuilt |

**Bottom line.** The *lens / comodel / effect-theory* vocabulary is, at present, an evocative
**reading** of a genuinely-real Moore coalgebra — it buys no theorem the coalgebra didn't already
buy, and in two places (the "components of `c`" factorization and "non-finality of `νF₁⊗νF₂`") it
overstates or mis-states. But the *faces it points at* are individually solid: the coalgebra
unfold, the step-completeness safety keystone + its coinductive lift, the proper-equalizer
cross-cell binding, the HMAC caveat chain, the verifier-indexed attestation dial, conservation,
I-confluence, the camera, and the named-lossy Φ are all REAL and axiom-clean. The lens would become
*load-bearing* (rather than decorative) only by proving the three things it currently only names:
(i) a real lens/factorization of `step` through a `{t // Guard t}` domain with at least one lens
law, (ii) the effect-theory→comodel bridge (arities + equations + a free-comodel construction), and
(iii) `capExercise`/handler **composition** laws (the comodel-homomorphism). Until then: the
coalgebra is the theorem; the lens is the poem.

*A closing couplet, in Ember's spirit:*
*two projections and a guarded gate — the turn is honestly Moore;*
*call it a lens if you like the word, but the laws aren't there… yet, for sure.* 🐉🥚 ( ˘▾˘ )
