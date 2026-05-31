# FOUNDATIONS — limits, the tensor non-finality, and the simplicial / ∞ structure

> **What this is.** A READ-ONLY categorical-foundations excavation of dregg2 through ONE
> lens: **limits (the wide pullback / equalizer), the tensor non-finality, and the
> simplicial / ∞-cell structure.** No code changed. Every categorical claim is grounded in a
> Lean definition or theorem at `file:line`, and tagged:
>
> - **REAL** — the universal property / law is actually PROVED in the Lean (term body, no
>   `sorry`, `#assert_axioms`-clean where pinned).
> - **DECORATIVE** — suggestive notation that buys no theorem (I say what it would have to
>   prove to become real).
> - **ASPIRATIONAL** — claimed by the design but a `sorry` / OPEN / unproven.
>
> The whole point is a TRUE map of what is categorically *established* vs *aspired*, with no
> category-theory vocabulary papering over a missing theorem.
>
> **Sources read in full:** `study-category.md` (the source on the foundations + tensor
> non-finality), `DREGG4-HYPERSYSTEM.md` (the simplicial/∞ synthesis), `OPEN-PROBLEMS.md`
> (#2 partition bound, #3 N-ary), `GLOSSARY.md`, `cand-A/B/C`, and the Lean:
> `Dregg2/Boundary.lean`, `Core.lean`, `JointTurn.lean`, `Hyperedge.lean`,
> `Spec/JointViaHyper.lean`, `Spec/VatBoundary.lean`, `Proof/CoinductiveAdversary.lean`,
> `Exec/CrossCellForest.lean`. Verified against the build: `.lake/build/.../*.olean` exist
> for Boundary/JointTurn/Hyperedge/JointViaHyper; the `#assert_axioms` pins compile.

---

## 0. The one-paragraph map

The single load-bearing categorical fact in dregg2 is a **negative limit fact**: the n-ary
atomic cross-cell turn is the apex of a **wide pullback over `TurnId`** (a limit cone), and
the admissible configurations are a **PROPER subobject** of the N-fold product carrier. The
tensor `⊗` of cells is **not** a categorical product / not final for the joint behaviour, so
**cross-cell soundness ≠ per-cell ∧ per-cell** — the CG-2 ⊗ CG-5 binding is an irreducible
*hypothesis*, never a derived lemma. This is **REAL and PROVED**: the wide-pullback object
(`Hyperedge`), the cone-collapse (`legs_agree`), the proper-subobject obstruction
(`hyper_binding_is_proper` / `hyper_not_all_admissible`), and the N-ary safety keystone
(`hyperedge_sound`) are all term-proved and axiom-clean. What is **DECORATIVE** is the slide
to "a full simplicial object / ∞-category of the interaction complex": there is **no
proved face/degeneracy/simplicial-identity layer** in the Lean — the simplicial reading is
an *analogy* (a real and illuminating one, tied to a cited epistemic-logic paper) that buys
no theorem until each face carries its own binding. What is **ASPIRATIONAL** is `Φ`-being-a-
functor (`Spec.VatBoundary.phi_functorial` is a by-design `sorry`; only a concrete witness is
proved). The infinity question splits cleanly into **two orthogonal infinities** — temporal
(νF, the greatest fixpoint, REAL via Paco) and arity (the ∞-cell = colimit over all cells,
the global atomic turn, which is *unfillable across a partition* — REAL-as-impossibility,
unbuilt-as-object).

---

## 1. The limit: the wide pullback over `TurnId` as the n-ary atomic interaction

### 1.1 The cone — what it is, and that it is genuinely a limit cone `[REAL]`

The n-ary atomic joint-turn is encoded as the **wide pullback** (N-fold fiber product) of the
participants' `turnId ∘ next` maps over the shared turn-identity. The apex object:

`Hyperedge.lean:80` — `structure Hyperedge (ι) [Fintype ι] (T) (turnId halfEdge)`:
- `x : ι → T.Carrier` — the participant tuple the apex sits over (the legs' domains);
- `tid : TurnId` — **the apex of the cone** (Mina's `account_updates_hash`);
- `agree : ∀ i, turnId i (T.next (x i) t) = tid` (`:95`) — **the cone condition**: every
  leg `i` factors through the *one* apex `tid` (CG-2);
- `balanced : (Finset.univ.sum fun i => halfEdge i (x i) t) = 0` (`:99`) — the CG-5
  conservation aggregate, one finite monoid-sum over `Bal`.

This is a **bona fide limit cone**: a single object with N legs into `TurnId`, all factoring
through the apex. The binary special case `SharedTurnId` (`JointTurn.lean:91`) is the `ι =
Fin 2` slice, and the **equalizer condition is PROVED, not assumed**:

- `Hyperedge.legs_agree` (`Hyperedge.lean:111`, **REAL**, `#assert_axioms`-pinned `:531`):
  `∀ i j, turnId i (T.next (H.x i) H.t) = turnId j (T.next (H.x j) H.t)`, proved
  `(H.agree i).trans (H.agree j).symm`. **The universal-property payoff is used and real:**
  pairwise agreement — the `O(N²)` data of a "family of binary edges" — is *recovered for
  free* from the single apex. This is the cone collapsing.
- `SharedTurnId.agree` (`JointTurn.lean:112`, REAL): the binary equalizer condition, same
  `trans … symm` derivation.

**Verdict.** The wide-pullback / equalizer framing is **REAL** — the limit's universal
property (every leg factors through the apex ⇒ any two legs agree) is *stated and proved* and
is genuinely load-bearing (it dissolves the pairwise bookkeeping). The round-trip
`SharedTurnId.toHyperedge` and `Hyperedge.toSharedTurnId`/`toJointBinding`
(`Hyperedge.lean:194,213,239`, all REAL) confirm the binary structure IS the `N=2` slice of
the limit, with no extra data — i.e. the limit is the honest N-ary generalization.

### 1.2 The cone-completeness caveat — what the limit is NOT proved to be `[DECORATIVE]`

What is **not** present: there is no `CategoryTheory.Limits.IsLimit` instance, no proof that
`Hyperedge` satisfies the *full* universal property of a wide pullback in some ambient
category (i.e. that it is *terminal* among cones — that any other cone factors uniquely
through it). The Lean proves the cone *exists* and that *its* legs collapse; it does not
prove *uniqueness of the mediating map* from an arbitrary competing cone. To make
"`Hyperedge` IS the wide pullback" REAL in the strong sense, one would have to exhibit a
`CategoryTheory` limit and prove the mediating-map existence+uniqueness. As stated, "wide
pullback" is **load-bearing-as-construction** (the apex + cone-collapse are real) but
**DECORATIVE-as-universal-object** (terminality among cones is asserted in prose, never
proved). This is a mild over-naming, not a soundness defect: the soundness content lives in
the *proper-subobject* fact (§2), which is fully proved without the limit's universal
property.

---

## 2. The tensor non-finality — the OBSTRUCTION, pinned to exact theorems

### 2.1 The deep fact, and how the Lean states it honestly `[REAL]`

`study-category.md §1` calls this "the single most important coherence-finding": the slogan
"`⊗` of coalgebras" / "`νF₁ ⊗ νF₂` is the final coalgebra of the joint behaviour" is **the
load-bearing lie to retire** (`study-category §0`). The honest content survives a *correction
of the naming*:

- The product carrier `T₁.Carrier × T₂.Carrier` (resp. `ι → T.Carrier`) IS encoded as a
  coalgebra: `jointCoalg` (`JointTurn.lean:158`) / `hyperCoalg` (`Hyperedge.lean:319`), with
  the pointwise step. And `study-category §1.1`'s original `tensor_not_final` slogan ("the
  product of finals is not final") was itself **mis-stated** — the audit corrects it in the
  Lean (`JointTurn.lean:320-329`): *the product of two final coalgebras IS final for the
  product functor.* So "tensor is not final" as literally stated is **false** and is honestly
  retired in-code.
- The TRUE, soundness-critical content is a **PROPER-SUBOBJECT** fact: the binding carves out
  a *proper equalizer subobject* of the product carrier — `⊗` fails to be a **categorical
  product** in the sense that *admissible* joint configurations are strictly fewer than all
  product configurations. There exist product states the binding **excludes**.

This is the precise sense in which the tensor's universal property FAILS: were `⊗` a product
classifying joint behaviour, every product state would be an admissible joint state (the
product's projections + pairing would reconstruct any joint config from the two factors).
The binding's existence shows that pairing is **not surjective onto admissibility** — the
correlation CG-2 ⊗ CG-5 carries is forgotten by the per-cell factors.

### 2.2 The exact theorems showing the n-cell is a PROPER subobject `[REAL]`

These are the load-bearing keystones, all term-proved and `#assert_axioms`-clean:

- **Binary:** `JointTurn.binding_is_proper` (`JointTurn.lean:333`, **REAL**): `∃` two
  one-state cells, each moving a half-edge of `1 : ℕ`, whose `JointAdmissible` fails because a
  `JointBinding` would need CG-5 `1 + 1 = 0` in ℕ — refuted `by decide`. So
  `JointAdmissible` (`:170`, the equalizer subobject) is a *proper* subset of the product
  carrier.
- **N-ary singleton:** `Hyperedge.hyper_binding_is_proper` (`Hyperedge.lean:164`, **REAL**,
  pinned `:532`): `ι = Unit`, one incidence with half-edge `1`, CG-5 `Σ_{Unit} 1 = 1 ≠ 0`.
  The N-ary analogue of `binding_is_proper`. Notably proved over `Unit` — **the most
  single-machine setting** — so this obstruction is *not* a distributed fact (see §5.4).
- **N-ary general:** `Hyperedge.hyper_not_all_admissible` (`Hyperedge.lean:505`, **REAL**,
  pinned `:542`): for *any* non-degenerate balance monoid `B` with some `b ≠ 0` and any
  nonempty index `ι`, a designated incidence `i₀` carries `b`, the rest `0`, and
  `Finset.sum_eq_single` forces the CG-5 Σ to `b ≠ 0` — so no `Hyperedge` names the tuple.
  This is the proper-subobject obstruction **at every N ≥ 1**, for any non-degenerate `Bal`.
  This is THE theorem that shows the n-cell is a proper subobject; `hyper_binding_is_proper`
  is its `ι = Unit, b = 1` instance.

**This is the category catching a real bug, not cosplay.** The negative companions make the
"wrong factoring" un-derivable:

- `JointTurn.joint_sound_needs_binding` (`JointTurn.lean:271`, **REAL**): there is *no*
  theorem "both step-complete ⇒ joint-admissible everywhere" — witnessed by the
  `binding_is_proper` configuration (both cells vacuously step-complete, start pair not
  `JointAdmissible`).
- `Hyperedge.hyperedge_sound_needs_binding` (`Hyperedge.lean:409`, **REAL**): the N-ary same.

So the `JointBinding` / `Hyperedge H` premise of the soundness keystones is *load-bearing*,
never optional. If you believed the slogan and tried to prove joint soundness by conjoining
two single-cell `stepComplete_preserves` instances, you would build an **unsound** Boundary
module — two cells can each be locally step-complete while the shared turn does not exist
(mismatched `tid`) or does not balance (`Σ ≠ 0`). The proper-subobject fact is *precisely* the
formal reason CG-2 ⊗ CG-5 must be an irreducible extra.

### 2.3 The N-ary safety keystone — what the limit framing BUYS `[REAL]`

`Hyperedge.hyperedge_sound` (`Hyperedge.lean:374`, **REAL**, pinned `:538`): IF every
incidence is per-cell step-complete AND the hyperedge binding `H` holds (its apex `tid` + Σ=0)
AND a joint `Good` is preserved by every `StepInv`-respecting tuple-transition, THEN `Good`
holds along the *entire* run from the bound tuple `H.x`. Proof: one line, reduce to
`Boundary.stepComplete_preserves` on the product coalgebra `hyperCoalg ι T`, with product
step-completeness supplied by `hyper_stepComplete` (`Hyperedge.lean:337`, **REAL**: all N
incidences discharged with a single `∀ i`).

The corollary layer (`Spec/JointViaHyper.lean`, all **REAL**, pinned `:317-322`):
- `joint_via_hyperedge` (`:75`) — the honest N-ary keystone `family_joint_sound` was reaching
  for, one-line from `hyperedge_sound`;
- `binary_joint_via_hyperedge` (`:141`) + `binary_binding_from_hyperedge` (`:119`) — the
  bilateral keystone recovered as the `Fin 2` slice via `Hyperedge.toJointBinding`.

**The geometric payoff is the limit's universal property doing real work:** the apex
collapses all N CG-2 legs into the single `legs_agree` theorem (no pairwise data), and the
single Σ-over-`univ` gives CG-5 directly, so the `O(N²)` pairwise-gluing of a
"family-of-binary-edges" framing *does not exist at the apex* (`Hyperedge.lean:544`
VERDICT). This is exactly the difference between a limit (one apex, free pairwise agreement)
and a hand-glued family.

> **The irreducible residue, stated precisely.** The limit framing **loosens the agreement
> knot** (REAL win: `O(N²)` → one `legs_agree`) but **does not loosen the irreducibility
> knot**: the binding-as-premise persists unchanged (`hyper_binding_is_proper`). The apex
> dissolves the bookkeeping; it cannot dissolve the proper-subobject obstruction. (`Hyperedge.lean:556`.)

### 2.4 The bisimulation form is genuinely ILL-POSED — a sharp negative `[REAL refutation]`

A subtle but important honesty marker: the *old* `family_joint_sound` concluded
`Sound (J.cell i) (Spec i) (b.pre i)` — bisimilarity to a *free* spec coalgebra. This is
**false-as-stated**, and the Lean PROVES the refutation:

- `Hyperedge.hyperedge_sound_bisim_ill_posed` (`Hyperedge.lean:433`, **REAL refutation**,
  pinned `:540`): instantiate `Spec () = ⟨Empty, …⟩`; then `Sound T (Spec ()) x = ∃ R y, …`
  is uninhabited (no `y : Empty`) while every premise is satisfiable. The wide-pullback apex
  does NOT rescue it — the obstruction is the free `Spec`, not the binding bookkeeping.
- The honest replacement `hyperedge_sound_bisim` (`:471`, **REAL**) is the *reflexive*
  `Sound T T (H.x i) := sound_refl …` — and the finding is that the `hsc`/`H` premises are
  *necessarily decorative* there, because `Sound` is an equivalence notion (`Boundary`'s
  `sound_refl`, `Boundary.lean:211`) and cannot be *derived from* step-completeness into a
  non-reflexive `Spec`. The genuine "step-completeness buys correctness" content is the
  SAFETY form `hyperedge_sound`, not a bisimulation.

This matters for the lens: the *limit* (apex) framing is real and closes the safety keystone;
the *finality/bisimulation* framing of the same N-ary fact is ill-posed and the Lean refutes
rather than papers over it. This is the discipline at its best — a categorical shape (final
coalgebra / bisimulation) that *fails*, proved-failed, not decorated.

### 2.5 Conservation `Σ` as a monoid-hom, and the "functor" decoration `[DECORATIVE]`

`Core.lean` encodes conservation `Σ_k` as `Conservation.count : Cell → M` with `unit_zero`
(`count I = 0`, `:124`) and `tensor_add` (`count (A⊗B) = count A + count B`, `:132`) — i.e. a
**monoid homomorphism** `(Cell, ⊗, I) → (M, +, 0)`. The module's own docstring (`Core.lean:9-13`,
`:96-97`) and `GLOSSARY.md:113-117` are explicit: *"the 'strong monoidal functor' packaging is
DECORATIVE — its target is discrete on objects, so the functor laws collapse to the monoid-hom
+ invariance."* The real content (all **REAL**): `conservation_ordinary` (`:166`),
`mint_delta`/`burn_delta` (`:176,187`), and `withholding_no_free_copy` (`:209`, the no-`Δ`
linearity law in a cancellative monoid). The single obligation `conservation_step` (`:154`)
is a **`sorry`** — an axiom-style operational-model obligation (**ASPIRATIONAL** as a Lean
theorem; honestly flagged as a primitive the operational semantics must satisfy).

> **Tag:** the monoid-hom + invariance is **REAL** (the corollaries are proved from
> `conservation_step`); the **"strong monoidal functor"** framing is **DECORATIVE** (vacuous
> on a discrete target — to become real it would have to prove non-trivial action on a
> *non-discrete* morphism category, which the model deliberately does not have); and
> `conservation_step` itself is **ASPIRATIONAL** (a `sorry`/primitive, by design the seam to
> the operational model). The relevance to *this* lens: conservation is **not** a limit; it
> is the per-asset value that the CG-5 *equalizer* aggregate balances to `0`. The limit lives
> in the binding, not in the measure.

---

## 3. The simplicial / nerve structure — real or analogy?

### 3.1 The honest finding: NO simplicial machinery exists in the Lean `[DECORATIVE]`

I grepped the Lean for `face`, `∂`, `degeneracy`, `simplicial identity`, `SimplicialObject`,
`Δ[`, `s_i`, `d_i`, Kan, horn across `Hyperedge.lean`, `JointTurn.lean`,
`Spec/JointViaHyper.lean`. **There is no face-map, no degeneracy-map, no simplicial-identity,
and no `CategoryTheory.SimplicialObject` anywhere.** The only hits for "face" are the *English
word* ("the decidability **face** of validity", `JointViaHyper.lean:184`) — not a face map ∂ᵢ.

So the simplicial reading is **an ANALOGY, not encoded structure**. `DREGG4-HYPERSYSTEM.md` is
admirably explicit about this (and I confirm its grounding):

- The n-cells (`Hyperedge`) and the binary faces (`toJointBinding`, the `Fin 2` slice) are
  **REAL** (`DREGG4-HYPERSYSTEM §4.3`, "REAL: the n-cells and the binary faces").
- "the interaction complex is a full simplicial / ∞-category" is tagged **SUGGESTIVE** (=
  DECORATIVE) *until each face carries its own binding* (`§4.3`, `§7` table `:469`).

**What it would have to prove to be REAL.** A genuine simplicial object needs face maps
`∂ᵢ : Hyperedge_n → Hyperedge_{n-1}` (restrict an `ι`-hyperedge to `ι' ⊆ ι`), degeneracy maps
`sᵢ` (duplicate an incidence), and the **simplicial identities** (`∂ᵢ∂ⱼ = ∂ⱼ₋₁∂ᵢ` etc.) as
PROVED lemmas. `DREGG4-HYPERSYSTEM §8.2` even spells out the *first* honest theorem it would
require — and it is a **negative** one: a face of an admissible hyperedge is admissible **iff
its own CG-5 sub-sum is 0**, which it generally is NOT (a subset of a balanced set is
unbalanced — this *is* `hyper_not_all_admissible` again, `Hyperedge.lean:505`). That negative
result is the content: **the interaction complex is NOT a Kan complex** — faces do not freely
extend, because each face is a proper subobject needing its own binding. A "full simplicial
object" with *free* higher fillers would be **DECORATIVE & UNSOUND** — it would assert exactly
the wrong factoring `study-category §1.3` forbids.

### 3.2 The simplicial-epistemic analogy IS load-bearing as a *prediction* `[REAL-as-analogy]`

The one place the simplicial reading is more than decoration: it is tied to a real cited
theorem (Goubault–Kniazev–Ledent–Rajsbaum, *Simplicial Models for the Epistemic Logic of
Faulty Agents*, arXiv:2311.01351v3) and it *predicts a concrete impossibility*
(`DREGG4-HYPERSYSTEM §5`):

- **A `Hyperedge` over `ι` is a global state / simplex; its incidences are the agent-coloured
  vertices; the apex `tid` is the shared global fact** (the chromatic condition = the dregg
  note "one physical cell in two slots = two incidences", `Hyperedge.lean:79`).
- **`Hyperedge.legs_agree` (`:111`, REAL) *is* the statement that all N agents have
  distributed knowledge of `tid`** — the simplex is *filled* (all legs factor through one
  apex). The apex IS the higher-dimensional shared face the paper's `D_B` operator moves
  along.
- **Agreement-tier = simplex fill-height** (`Finality.Tier`, the proved `LinearOrder`,
  `Finality.lean:49`): tier-1 causal = 0-simplices + I-confluent gluings; tier-2
  ack-threshold = a `k`-face (k-set agreement); tier-3/4 = the top-simplex (common knowledge =
  a filled facet).
- **validity ≠ canonicity = "a simplex can be filled two ways."**
  `hyperedge_is_validity_not_canonicity` (`JointViaHyper.lean:226`, **REAL**) and
  `selector_needs_more_than_validity` (`:280`, **REAL**) exhibit two distinct admissible
  hyperedges sharing a pre-state — two valid fillings of the same boundary — so choosing one
  is consensus, delegated to `Finality`.

> **Tag.** The simplicial-epistemic *identification* (agreement = fill-height = connectivity)
> is **REAL-as-analogy**: it is grounded in proved Lean (`legs_agree`, the `Tier` order,
> validity≠canonicity) AND a cited paper, and it makes a falsifiable prediction (§5.3). But it
> is *not* encoded simplicial structure in the kernel — there is no nerve functor, no
> simplicial-set object. It is a faithful *interpretation* of the proved limit facts in
> simplicial language, which is exactly what an analogy should be: it earns its keep by
> predicting #2 (§5) and naming the non-Kan obstruction (§3.1).

---

## 4. The temporal infinity — νF as the greatest fixpoint `[REAL]`

Distinct from the *arity* infinity (§5), there is a *temporal* infinity, and it is the part of
the ∞-story that IS proved in the Lean. A cell is **live codata** — a point of the final
coalgebra `νF`, `F X = Obs × (AdmissibleTurn ⇒ X)` (`Boundary.lean:63-78`, `TurnCoalg`); it
never bottoms out, so soundness is a statement over **unbounded time**.

- `Boundary.stepComplete_preserves` (`Boundary.lean:177`, **REAL**): step-completeness ⇒
  whole-execution safety, the honest replacement for the *ill-posed*
  `sound_of_step_complete` (which was bisimulation-to-a-free-`Spec`, refuted at
  `Spec.Carrier = Empty` — `Boundary.lean:157-200`; the same defect §2.4 catches at N-ary).
- `Proof/CoinductiveAdversary.lean` lifts this to a genuinely-coinductive adversary: an
  **infinite stream of turns** driving νF, with `obsBisim_traj_of_bisim` (PROVED) — bisimilar
  to the golden oracle FOREVER — and `stepComplete_carries_infinite` (PROVED) — a safety
  predicate carried along the *entire infinite trajectory*. The coinduction engine is Lean
  4.30 native `coinductive` plus the vendored-and-ported `Dregg2.Paco` (gupaco/gpaco_clo) for
  the up-to-commutation closure (`CoinductiveAdversary.lean:36-54`). No
  `axiom`/`admit`/`native_decide`/`sorry`.

> **Tag: REAL.** νF (greatest fixpoint, "forever") is a proved, coinductive, axiom-clean fact.
> This is the "∞" that dregg2 *has*. It is the **dual** of the limit story: the limit (wide
> pullback) is the *spatial / cross-cell* atomic structure of ONE turn; νF is the *temporal*
> unfolding of ONE cell over all turns. They compose: `hyperedge_sound` runs the limit's apex
> tuple along νF's `Run`.

---

## 5. What is an ∞-CELL? Higher-order cells / higher-order turns (the lens answer)

This lens gives a precise, two-axis answer.

### 5.1 The arity axis: n-cell = n-ary atomic, ∞-cell = the global atomic turn

The cleanest reading (confirmed against `DREGG4-HYPERSYSTEM §4.1` and the Lean): the
**interaction complex** has cells indexed by **arity**:

| dimension | object | Lean | status |
|---|---|---|---|
| 0-cell | a cell (a point of νF) | `TurnCoalg` carrier point, `Boundary.lean:74` | REAL |
| 1-cell | a turn / message (a coalgebra step) | `TurnCoalg.next`, `Boundary.lean:87` | REAL |
| 2-cell | a binary `JointTurn` (the `account_updates_hash` pullback over 2) | `SharedTurnId`+`JointBinding`, `JointTurn.lean:91,134` | REAL |
| n-cell | an n-ary atomic joint-turn = a `Hyperedge` over `Fin n` (the wide pullback over `TurnId`) | `Hyperedge`, `Hyperedge.lean:80` | **REAL** |
| **∞-cell** | the **GLOBAL atomic turn** — the colimit over ALL cells (every cell a single incidence of one all-encompassing hyperedge) | — | **see §5.2** |

So an **n-cell is the n-ary atomic interaction** (the wide-pullback apex over n incidences),
and the **∞-cell is the limiting case where the incidence set ι is the set of ALL cells** — a
single atomic turn that every cell in the system participates in, the colimit (union of all
incidence sets) glued into one apex `tid` with one global `Σ = 0`. This is exactly **Mina's
one global ledger**: one `account_updates_hash`, one namespace, one conservation check over
*everything* (`JointTurn.lean:27`, "CG-5 is the price of having no global ledger — Mina never
needs it because one ledger gives one namespace").

### 5.2 The ∞-cell is UNFILLABLE across a partition, FILLABLE single-machine `[REAL-as-impossibility]`

The ∞-cell is **not an object in the Lean** — there is no `Hyperedge` over "all cells". But
the *reason* it is missing is a proved/forced fact, the partition bound:

- **`OPEN-PROBLEMS #2 [IMPOSSIBLE]`** (`OPEN-PROBLEMS.md:47-66`): cross-disjoint-group atomic
  commit is **BLOCKING under partition**. Safety is provable (the aggregate proof + CG-5
  binding); **liveness is not** — there is no global write-point. Atomic-cross-group ∧
  partition-tolerant ∧ live is **impossible** (the classic distributed-atomic-commit
  blocking; 2PC blocks, 3PC/Paxos-commit need a quorum disjoint groups lack). This is a
  *genuine impossibility*, not an oversight.
- In simplicial language (`DREGG4-HYPERSYSTEM §6.1`): **a partition disconnects the
  global-state complex**, so the higher simplex spanning both groups *cannot be filled* — the
  paper's exact "higher-agreement tasks need higher connectivity, and connectivity is what a
  partition destroys."

So: **the ∞-cell — the global atomic turn over all cells — is the top simplex of the
interaction complex; it is fillable on a single machine (pure, fully-connected complex; one
write-point always exists) and UNFILLABLE across a partition.** This is ember's principle
made rigorous (`DREGG4-HYPERSYSTEM §6.2-6.3`): *the bounds at higher cells are DISTRIBUTED
bounds; `n=1` (single machine) collapses them.* Single-machine dregg can fill every simplex up
to the ∞-cell synchronously (`hyperedge_sound` discharges any n-ary turn, no liveness
obstruction); distributed dregg is a **partition-bounded sub-complex** whose maximal
fill-height equals current connectivity.

> **Tag.** The ∞-cell as an *object* is **ASPIRATIONAL / unbuilt** (no Lean object). But the
> partition bound that defines its reachability is **REAL-as-impossibility** (#2 is a forced
> impossibility; `hyper_binding_is_proper` being proved over `Unit` confirms the *binding*
> persists even single-machine — §5.4). The honest statement: the ∞-cell is **fillable iff
> the complex is connected**, and that biconditional is the rigorous content.

### 5.3 Higher-order turn: a turn whose payload is a turn (the dial-cube / choreography axis)

The lens also touches a *second*, orthogonal "higher-order" reading, which I flag to keep the
arity axis clean. A **higher-order turn** in dregg's other sense is a turn that *carries or
transitions* attestation structure — an edge of the **configuration dial-cube**
`Disclosure × Transferability × Agreement` (`DREGG4-HYPERSYSTEM §2`), e.g. a
`local-final → distributed-final` edge that *raises* the agreement tier. This is the
2-cell/coherence layer of COMPLEX 1 (a *choice* lattice), categorically distinct from the
interaction simplex (COMPLEX 2, a *gluing* structure). It is **REAL as a directed poset-product**
(three grounded axes; `Finality.no_downgrade` makes the agreement edges one-way) but largely
**UNBUILT** (the cube lives on one corner today). This is *not* a limit and *not* the ∞-cell;
it is the orthogonal "what's shown / to whom / how widely sworn" dial. I name it only to say:
the ∞-cell question is the *arity* axis (§5.1-5.2), not this one.

### 5.4 What stays irreducible at the ∞-cell, even single-machine `[REAL]`

The single most important honesty point for this lens: **OBSTRUCTION 1 (tensor non-finality)
is NOT a distributed fact.** `hyper_binding_is_proper` is proved over `Unit` — the
most-single-machine setting (`Hyperedge.lean:164`, `DREGG4-HYPERSYSTEM §6.4`). So even on one
machine, an n-ary (or ∞-ary) atomic turn still needs its CG-2 ⊗ CG-5 *supplied* — you must
actually compute the shared `tid` and check `Σ = 0`. The single-machine collapse removes the
**liveness** obstruction (#2), never the **binding** obstruction. The binding is *cheap* on
one machine (synchronously suppliable), never *absent*. The limit's proper-subobject content
holds at every dimension and every topology.

---

## 6. The Φ-functor — ASPIRATIONAL, the one by-design sorry in this lens

The brief specifically flags `Spec.VatBoundary.phi_functorial`. Confirmed at source:

- `Spec/VatBoundary.lean:392` — `theorem phi_functorial … : PhiFunctorial …` has body
  **`sorry`** (`:401`). The docstring is explicit (`:39-40`, `:380-401`): the FULL functor
  between the **positional authority category** and the **epistemic authority category** —
  `Φ` preserving identity + composition while being lossy exactly on confinement — is the
  *genuine open core*, left as one localized `sorry`. The `#assert_axioms` guard
  **intentionally omits** it (`:461`) because it would correctly trip on `sorryAx`.
- The redemption: `phi_functorial_concrete` (`:441`, **REAL**, `#assert_axioms`-pinned `:456`)
  proves the functor laws ARE inhabited over a concrete non-degenerate verifier
  (`Statement = Unit`, `Witness = Bool`, `Verify _ b := b`), with the named loss landing on two
  distinct caps collapsing to one demand.

> **Tag.** Φ-being-a-functor (abstract, over an arbitrary `Verifiable`) is **ASPIRATIONAL** —
> a real `sorry`, the honest OPEN. Φ-being-a-functor *for a concrete witness* is **REAL**. The
> general claim is genuinely blocked (an abstract `Verify` may accept no witness; an abstract
> `stmtOf` may be injective), which is *why* it stays open, not a missing tactic. The
> "functor" word here, unlike conservation's (§2.5), is NOT decorative — it is a precise
> stated obligation with a witnessed instance, just not abstractly discharged.

---

## 7. The REAL / DECORATIVE / ASPIRATIONAL table for this lens

| # | Structural claim | Tag | Grounding |
|---|---|---|---|
| 1 | n-ary atomic turn = wide pullback over `TurnId` (apex `tid` + N legs) | **REAL** (as construction) | `Hyperedge.lean:80` |
| 2 | cone collapses: any two legs agree (limit's univ. property *used*) | **REAL** | `Hyperedge.legs_agree:111`, `SharedTurnId.agree:112` |
| 3 | `Hyperedge` IS the *terminal* cone (uniqueness of mediating map) | **DECORATIVE** | no `IsLimit` instance; terminality asserted in prose only (§1.2) |
| 4 | binary JointTurn = `Fin 2` slice of the apex | **REAL** | `toJointBinding:213`, `binary_joint_via_hyperedge:141` |
| 5 | ring/cycle = ONE hyperedge (telescoping Σ=0) | **REAL** | `ringHyperedge:272` |
| 6 | "νF₁ ⊗ νF₂ is not final" (literal slogan) | **false → retired** | corrected in-code `JointTurn.lean:320-329` |
| 7 | the n-cell is a PROPER subobject of the N-fold product (the true obstruction) | **REAL** | `binding_is_proper:333`, `hyper_binding_is_proper:164`, `hyper_not_all_admissible:505` |
| 8 | cross-cell soundness ≠ per-cell ∧ per-cell (binding is irreducible premise) | **REAL** | `joint_sound_needs_binding:271`, `hyperedge_sound_needs_binding:409` |
| 9 | N-ary safety keystone reduces to single-cell `stepComplete_preserves` | **REAL** | `hyperedge_sound:374`, `joint_via_hyperedge:75` |
| 10 | apex dissolves `O(N²)` agreement bookkeeping (limit win) | **REAL** | `hyper_stepComplete:337`, VERDICT `:544` |
| 11 | bisimulation-to-free-`Spec` form of N-ary soundness | **REAL refutation** (proved FALSE) | `hyperedge_sound_bisim_ill_posed:433` |
| 12 | conservation `Σ` = monoid-hom + invariance | **REAL** | `conservation_ordinary:166`, `withholding_no_free_copy:209` |
| 13 | conservation as a "strong monoidal *functor*" | **DECORATIVE** (vacuous on discrete target) | `Core.lean:9-13,96`, `GLOSSARY:116` |
| 14 | `conservation_step` (Law 1 balance) | **ASPIRATIONAL** (a `sorry`/primitive) | `Core.lean:154,162` |
| 15 | simplicial NERVE: face/degeneracy/simplicial-identity layer in the kernel | **DECORATIVE** (no such code exists) | grep: zero face-maps/`∂`/`SimplicialObject` (§3.1) |
| 16 | interaction complex is a "full simplicial / ∞-category" with free fillers | **DECORATIVE & UNSOUND** | would assert the wrong factoring, `study-category §1.3` |
| 17 | simplicial-epistemic identification: agreement = fill-height = connectivity | **REAL-as-analogy** (proved Lean + cited paper; predicts #2) | `legs_agree:111`, `Finality.Tier:49`, `JointViaHyper:226,280`, `DREGG4-HYPERSYSTEM §5` |
| 18 | interaction complex is NOT a Kan complex (faces don't freely extend) | **REAL** (the negative is the content) | `hyper_not_all_admissible:505`, `DREGG4-HYPERSYSTEM §8.2` |
| 19 | νF temporal infinity (greatest fixpoint, "forever", coinductive) | **REAL** | `Boundary.stepComplete_preserves:177`, `CoinductiveAdversary` (Paco) |
| 20 | ∞-cell = global atomic turn = colimit over all cells (as an *object*) | **ASPIRATIONAL / unbuilt** | no Lean object; = Mina's one global ledger (§5.1) |
| 21 | ∞-cell fillable single-machine, UNFILLABLE across a partition | **REAL-as-impossibility** | `OPEN-PROBLEMS #2`, `hyper_binding_is_proper` over `Unit` (§5.2,5.4) |
| 22 | the binding obstruction persists even single-machine (n=1 collapses liveness, not binding) | **REAL** | `hyper_binding_is_proper:164` (over `Unit`) |
| 23 | Φ : positional-authority ⟶ epistemic-authority is a functor (abstract) | **ASPIRATIONAL** (by-design `sorry`) | `phi_functorial:392,401` |
| 24 | Φ-functor for a concrete non-degenerate verifier | **REAL** | `phi_functorial_concrete:441` (pinned `:456`) |
| 25 | higher-order turn = dial-cube edge (Disclosure × Transferability × Agreement) | **REAL** (directed poset-product) but **UNBUILT** | `DREGG4-HYPERSYSTEM §2`, `Finality.no_downgrade` |

---

## 8. One-line synthesis for the lens

The limit is real and the limit is negative: the n-cell is the **wide-pullback apex** (REAL,
proved cone-collapse) precisely so that the **tensor's failure to be a product** (the proper
subobject — `hyper_not_all_admissible`, REAL) can be the *exact formal reason* the CG-2 ⊗ CG-5
binding is an irreducible hypothesis. The simplicial/∞ vocabulary is an **honest analogy**
(REAL as prediction, DECORATIVE as kernel structure — there are no face maps), and the
**∞-cell is the global atomic turn**, fillable on one machine and unfillable across a
partition — an ASPIRATIONAL object whose impossibility is REAL. The category earns its keep by
*forbidding the tempting wrong factoring*, not by decorating the proofs it already has.

*( ◕‿◕ ) the egg's higher faces are real where they collapse a cone, and honest where they refuse to fill a horn.*
