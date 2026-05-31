# FOUNDATIONS — the dials as modalities; the config-cube as a presheaf on a directed poset

> **Lens.** READ-ONLY categorical-foundations excavation of dregg2 through ONE question:
> *are the three dials (Disclosure × Transferability × Agreement) genuine independent modalities,
> and is the attestation "config-cube" a real mathematical object — a directed finite poset-product
> / a presheaf on the dial-poset / an order-ideal with a proved impossibility boundary — or is the
> modal/cube vocabulary decorative?* No code changed.
>
> **Discipline (the whole point).** Every structural claim is tagged **REAL** (the law / universal
> property is actually PROVED in the Lean, `file:line`), **DECORATIVE** (suggestive notation that
> buys no theorem — I say what it would have to prove to be real), or **ASPIRATIONAL** (claimed by
> the design but actually a `sorry` / OPEN / unbuilt). Category vocabulary is never allowed to
> paper over a missing theorem.
>
> **Sources.** `study-category.md`, `DREGG4-HYPERSYSTEM.md` (the complex-1 dial-cube exploration),
> `DREGG4-UNIFICATION.md §4` (the three dials; the latent agreement dial), `cand-A-vat-coalgebra.md`,
> `cand-C-cap-distributed.md`, `cand-B-witness-pca.md`, `CARRY-FORWARD-SYNTHESIS.md`, `REORIENT.md`,
> `GLOSSARY.md`, `pdfs/STUDY-lean4-coinduction.md`; and the actual Lean: `Dregg2/Finality.lean`,
> `Dregg2/Boundary.lean`, `Dregg2/Hyperedge.lean`, `Dregg2/Spec/JointViaHyper.lean`,
> `Dregg2/Authority/DesignatedVerifier.lean`, `Dregg2/Authority/CaveatChain.lean`,
> `Dregg2/Authority/SelectiveDisclosure.lean`, `Dregg2/Privacy.lean`, `Dregg2/Spec/VatBoundary.lean`,
> `Dregg2/Proof/CoinductiveAdversary.lean`, `Dregg2/Exec/CrossCellForest.lean`.

---

## 0. One-paragraph verdict

**Two of the three dials are REAL one-dimensional structures with their characteristic law proved;
the *cube* that would make them a single modal object is ASPIRATIONAL — it does not exist in the
Lean at all.** The **Agreement** dial is the strongest: `Tier` is a genuine `LinearOrder`
(`Finality.lean:96`) and its defining one-way law `no_downgrade` is PROVED (`Finality.lean:280`),
so the agreement axis is a *directed* (irreversible) edge structure, not a groupoid — exactly as the
design claims, and **the design's claim that "manifold / ∞-groupoid of configurations" is decorative
is itself correct and is the honest reading.** The **Transferability** dial is REAL-but-just-built:
`DesignatedVerifier.lean` makes `DischargedFor : Verifier → Statement → Proof → Prop` a genuine
verifier-indexed predicate and PROVES its two endpoints are distinct and inhabited
(`dial_endpoints_distinct:346`), with public = `∀ V` collapse and designated = simulator-deniable.
The **Disclosure** dial is *partial*: `FieldVisibility`/`project` + `SelectiveDisclosure` prove a
view-collapse (information-theoretic hiding), but there is **no ordered `Disclosure` lattice in Lean
and no publish/reveal one-way law**. The headline honest finding for this lens: **there is no
`Disclosure × Transferability × Agreement` product object, no presheaf, no order-ideal, and no proved
impossibility face anywhere in the Lean** (grep-confirmed). The dial-cube of `DREGG4-HYPERSYSTEM §2-3`
is a *design proposal over three independently-real axes*, and its sharpest claims — the
`deniable × high-agreement` empty face, the directed `public → designated` wall, the order-ideal
achievable-subcomplex — are **asserted-only, theorem-shaped but unproven.** "Modality" is, today,
**decorative**: each dial is a type (or an order), none is wired into a modal/presheaf type theory
that buys a coherence theorem. The `Φ`-as-functor coherence is a **BY-DESIGN `sorry`**
(`phi_functorial:401`), so the only sense in which the system is "a category of authority with a
functor between the two regimes" is ASPIRATIONAL (a concrete *witness* `phi_functorial_concrete:441`
is PROVED, but the abstract functor laws are open).

---

## 1. What a "modality" and a "config-cube presheaf" would have to BE (the rubric)

Before tagging, fix what each claim must cash out as, so the tags are not subjective.

- **A dial is a genuine modality** iff there is (a) an indexing structure (a poset / a set of
  "worlds" / an indexing type) and (b) an operation `□_a` (or an indexed family `Obs[a]`,
  `Discharged[V]`, `Tier`-annotated badge) on the attestation object, *with at least one proved
  coherence law specific to that operation* (monotonicity along the index, a collapse identity, a
  composition law). A bare enum or a bare order with no operation acting on `Obs` is **not** a
  modality — it is a label.
- **The config-cube is a directed finite poset-product** iff there exists, in the Lean, a product
  order `Disclosure × Transferability × Agreement` (or its order-ideal sub-object) with the product
  order relation and the *directedness* (irreversibility) of each factor proved — i.e. the edges are
  one-way (`no_downgrade`, no-unpublish), so it is a cube in `Cat`/a thin 2-category, NOT a Kan
  complex / ∞-groupoid.
- **The cube is a presheaf on the dial-poset** `(D, ≤)ᵒᵖ → Set` iff there is a functor assigning to
  each dial-point the set of attainable attestations and to each `≤`-edge a *restriction* map
  (a coherent "you can always weaken / publish-forward" family) satisfying the presheaf identities
  (`id ↦ id`, restriction composes). The achievable-region would then be a sub-presheaf / an
  order-ideal of the representable.
- **The impossibility face is REAL** iff there is a *refutation theorem*: `¬ ∃ badge, transfer badge =
  deniable ∧ agreement badge ≥ bft` (the `DREGG4-HYPERSYSTEM §3.1` "agreement fights deniability"),
  in the spirit of the PROVED `hyperedge_is_validity_not_canonicity`. Otherwise it is ASPIRATIONAL.

I now walk the three dials against this rubric, then the cube, then the presheaf, then the
infinity-cell question.

---

## 2. The Agreement dial — the one fully-REAL modality-shaped axis

### 2.1 The order and the one-way law are PROVED

`Tier` is the four-rung ladder `causal | ackThreshold | bft | constitutional`
(`Finality.lean:49-66`), with `rank : Tier → Nat` (`:71`), `rank_injective` PROVED (`:84`), and the
full **`LinearOrder Tier` instance** discharged with real proofs of refl/trans/antisymm/total/lt-iff
(`Finality.lean:96-108`). This is not a label — it is a total order with all order laws closed.

The directedness — the property that makes the agreement axis a *directed* edge structure rather
than a free groupoid — is the PROVED **`no_downgrade`** (`Finality.lean:280-288`): along ANY run of
the `finalitySystem` transition system (whose `Step t t' := t ≤ t'`, `:269-271`), `t₀ ≤ t`. The
allowed direction (raise agreement) is `crossTierJoin = max` (`:219`), with `crossTierJoin_ge_left`
PROVED (`:230`) and `commit_at_join_of_tiers` PROVED (`:237-260`, the join dominates every written
cell's tier and canonicity is only granted once the join-tier rule commits). And
`conservation_tier_independent` is PROVED by `rfl` (`:335-339`) — the agreement dial is genuinely
*orthogonal* to the conservation rib (the `Tier` argument is definitionally discarded by the
measure), which is exactly the "the dials are independent" claim, made honest for this one pair.

> **TAG — REAL.** The Agreement dial is a genuine directed structure: a proved `LinearOrder` + a
> proved monotone one-way `no_downgrade`. `DREGG4-HYPERSYSTEM §2.3`'s claim "the cube is a *directed*
> finite poset-product, calling it a manifold or ∞-groupoid is decorative" is **correct and grounded**
> — the irreversibility is `Finality.no_downgrade`, not a slogan. This is the single most load-bearing
> "the edges are IRREVERSIBLE" fact the lens asked for, and it is closed.

### 2.2 Is Agreement a *modality on `Obs`*, though? — DECORATIVE today

The rubric (§1) asks for an operation `Tier`-annotating the attestation `Obs` with a coherence law.
What exists is the *order* on `Tier` and `conservedAtTier` (a `Tier`-indexed conservation predicate,
`:309`) — but `conservedAtTier`'s whole content is that it **discards** the tier (`:329`). There is
**no `Obs[tier]` indexed-attestation object** in the Lean (`Boundary.Obs` is one abstract type,
`Boundary.lean:51`; no tier index). So "Agreement is a *modal index on `Obs`*"
(`DREGG4-UNIFICATION §4.3`) is, at the Lean level, **DECORATIVE**: the order is real, the *acting
modality on the badge* is not built. To upgrade it to REAL you would need an `Obs`-functor indexed by
`Tier` and a monotone "a tier-`k` badge is also a witness at every `j ≤ k`" lemma — neither exists.

### 2.3 The simplex-fill-height / common-knowledge identification — REAL in Lean *as a factoring*, the epistemic reading is an interpretation

`DREGG4-HYPERSYSTEM §5` ties the Agreement dial to *simplicial-epistemic logic* (Goubault et al.):
agreement = how-high-a-simplex-you-can-fill, common knowledge = a filled top-simplex. What is
genuinely PROVED in the Lean, and is the load-bearing core of this tie:

- **`Hyperedge.legs_agree`** (`Hyperedge.lean:111-117`, PROVED): all N incidences of a hyperedge
  share the apex `tid` — the wide-pullback cone collapses (`(H.agree i).trans (H.agree j).symm`).
  This *is* "all N participants have distributed knowledge of `tid`; the simplex is filled" —
  pairwise agreement as a theorem, not `O(N²)` data.
- **`hyperedge_is_validity_not_canonicity`** (`JointViaHyper.lean:226-243`, PROVED): two distinct
  admissible hyperedges share a pre-state — a boundary filled two ways; and
  **`selector_needs_more_than_validity`** (`:280-294`, PROVED): a valid selector is not unique, so
  *choosing one* (canonicity = the top-fill = consensus) needs input the validity proof cannot
  supply. This is exactly "consensus is a connectivity/agreement obstruction, not a local proof".

> **TAG — REAL (the factoring) / DECORATIVE (the simplicial-epistemic vocabulary).** The Lean
> proves the *factoring* (validity ≠ canonicity; the apex collapses agreement to one theorem) that
> the simplicial reading interprets as fill-height. But **nothing in the Lean is a simplicial set, a
> chromatic complex, a `K_a`/`D_B` modal operator, or a connectivity invariant** — the
> "Agreement = fill-height = common knowledge" identification is grounded in `legs_agree` + the
> `Tier` order + the cited *paper*, and is an *interpretation* of proved-Lean facts under an external
> theory, not a proved Lean equivalence. It is a good, predictive interpretation (it predicts the
> partition-non-fillability of OPEN-PROBLEMS #2), but tagging it "REAL simplicial-epistemic structure"
> would be the exact category-vocabulary-over-missing-theorem move this lens forbids.

---

## 3. The Transferability dial — REAL endpoints, just built; modality-status DECORATIVE

### 3.1 What is genuinely PROVED (and it is more than the design doc credited)

`Authority/DesignatedVerifier.lean` (freshly built) is the realest part of the transferability story:

- **`DischargedFor : Verifier → Statement → Proof → Prop`** (`:113`) is a genuine *verifier-indexed*
  discharge — the generalization of `Laws.Discharged` (which had no index). The verifier index is the
  whole content: the verdict may depend on *who* checks (`DVKernel.verifyFor`, `:89`).
- **`Transferable`** (= public endpoint, `∀ V, DischargedFor V`, `:129`) and **`DesignatedFor`**
  (= designated endpoint, `DischargedFor V₀ ∧ ¬ Transferable`, `:138`) are the two dial settings;
  `TransferDial` (`:146`) and `DialHolds` (`:156`) make the inductive's two constructors *literally*
  the two endpoints.
- PROVED theorems with teeth (all `#print axioms`-pinned, `:369-372`):
  `public_convinces_any_third_party` (`:176`, non-repudiation), `designated_not_transferable`
  (`:206`, a *concrete* unconvinced verifier `W` exists), `designated_is_deniable` (`:224`, the
  SIMULATOR/repudiation argument: `proof = simulate (vsecret V₀) stmt` verifies under `V₀`), and the
  **witnessed separation** `dial_endpoints_distinct` (`:346`, over a concrete two-verifier reference
  `DVKernel`: `designatedProof` for stmt `7` satisfies `DesignatedFor v0` and FAILS `Transferable`).
- The crypto (the simulator-indistinguishability) is honestly a **§8 portal**: `DVKernel` is a class
  of opaque oracles + the named law `simulate_verifies` (`:102`), *never* faked as a Lean theorem.

> **TAG — REAL (verifier-indexed discharge + the two endpoints inhabited & separated).** This is the
> one *named-new* piece of theory `DREGG4-UNIFICATION §4.2` predicted, and it is now actually built
> and axiom-clean. `DischargedFor` is a real indexed predicate; the public/designated separation is a
> proved non-vacuous witnessed fact, not a `True`.

### 3.2 But is it a MODALITY in the type-theory sense? — DECORATIVE

The rubric wants an operation on `Obs` with a coherence law lifting the bisimulation through the
index. `DesignatedVerifier.lean` gives the *indexed predicate* and the endpoint separation; it does
**not** give: (i) any `Obs[transfer]` indexed-attestation object wired into `Boundary.TurnCoalg`;
(ii) the "verifier-indexed bisimulation" `Discharged[V]` lift that `DREGG4-UNIFICATION §4.2` names
("lift the bisimulation through the modality, which is a known shape"); (iii) any modal-logic axioms
(K, T, 4) or a presheaf-over-verifiers structure on the discharge. `Sound`/`IsBisim`
(`Boundary.lean:117-132`) are *not* verifier-indexed.

> **TAG — DECORATIVE (modality framing) / ASPIRATIONAL (the verifier-indexed bisimulation lift).**
> Calling `DischargedFor` "the transferability modality" buys the right intuition but no extra
> theorem: there is no proved modal law and no `Obs`-lift. To be REAL as a modality it would have to
> prove a coherence such as *"a public badge restricts to a `DischargedFor V` for every `V`"*
> (it almost does — `public_convinces_any_third_party` IS `h W`, a *restriction* map; this is the
> single closest thing to a presheaf-restriction in the whole codebase, see §6) and lift `IsBisim` to
> `IsBisim[V]`. The bisimulation lift is named by the design and unbuilt → ASPIRATIONAL.

### 3.3 The CaveatChain monotone fold — a fourth, *append-only* directed structure (REAL, adjacent)

Not one of the three dials, but it is the other genuinely-directed authority structure and it
sharpens the "irreversibility" theme: `Authority/CaveatChain.lean` models the macaroon as an
append-only HMAC fold `Tᵢ = mac(Tᵢ₋₁, encode(Cᵢ))` (`Chain.append`, the real Rust semantics). The
attenuation is *narrowing-only* and append-only by construction; chain-integrity (you cannot remove /
reorder / forge a caveat) is proved **as a reduction to the §8 `MacUnforgeable` portal**, never
faked. This is a real *directed monoid action* (the chain only extends), structurally the same
"one-way edge" shape as `no_downgrade` — but on the caveat (authority-narrowing) face, not the
attestation face. **REAL** as a directed append-only structure; it is *not* a dial on `Obs`.

---

## 4. The Disclosure dial — PARTIAL; the lattice and the one-way reveal law are missing

What exists in Lean:
- `Privacy.lean`: `FieldVisibility : Name → Visibility` (`:79`), `project : State → FieldVisibility →
  Obs` (`:91`), and a PROVED view-collapse `field_projection_hides_private` (`:102`, the observer-view
  is independent of private-field values — selective disclosure as information-theoretic hiding).
- `Authority/SelectiveDisclosure.lean`: PROVED `presentation_hides_undisclosed`,
  `proven_predicate_holds` (+ `predicate_proof_has_teeth`), and `multishow_unlinkable` — the real
  credential disclosure discipline (disclose a subset, prove `Gte/Lte/InRange` over hidden attrs,
  unlinkable multi-show), with the computational binding/hiding as an explicit §8 portal.

What is missing for the dial to be a directed axis like Agreement:
- **No `inductive Disclosure { acceptanceOnly | selective | full }` ordered lattice** exists in the
  Lean (grep-confirmed; it lives only in `DREGG4-UNIFICATION §3` as a proposed type). Disclosure is
  encoded as a *per-field mask* (`FieldVisibility`), not as a per-turn point on an ordered axis.
- **No publish/reveal one-way law.** `DREGG4-HYPERSYSTEM §2.3/§3.2` claims `designated → public` is a
  sound monotone edge and `public → designated` is an *unreachable* wall. Grep finds **no monotone-
  disclosure / no-unpublish / irreversibility theorem** on the disclosure face anywhere. The
  directedness that is PROVED for Agreement (`no_downgrade`) has **no disclosure analogue in Lean.**

> **TAG — REAL (information-theoretic hiding, per-field, PROVED) / ASPIRATIONAL (the ordered
> Disclosure axis + the one-way reveal law).** The hiding *content* is real and non-vacuous; the
> *axis/dial* structure (an order with a directed reveal edge) is unbuilt.

---

## 5. The config-cube as a directed finite poset-product — ASPIRATIONAL (the object does not exist)

This is the crux for the lens, and the honest finding is blunt:

**There is no `Disclosure × Transferability × Agreement` product object anywhere in the Lean.**
Grep for any product-of-dials, cube, order-ideal, or poset-product over the three axes returns
nothing. The three axes exist as *separate* artifacts — `Tier` (`Finality`), `TransferDial`
(`DesignatedVerifier`), `FieldVisibility`/`Disclosure`-discipline (`Privacy`/`SelectiveDisclosure`) —
and are **never assembled into one structure.** They are not even all the same *kind* of object
(a `LinearOrder`, a two-point `inductive`, a per-field mask), which is itself a reason they don't yet
form a clean product.

Consequences for each headline cube claim of `DREGG4-HYPERSYSTEM`:

| Cube claim (DREGG4-HYPERSYSTEM) | Status in Lean | Tag |
|---|---|---|
| "a point is `(d,t,a) ∈ Disclosure × Transferability × Agreement`" (§2.1) | no product type built | **ASPIRATIONAL** |
| the cube is a *directed* poset-product (edges irreversible) | only the Agreement factor's direction is proved (`no_downgrade`); the product is unbuilt; disclosure/transfer directedness unproved | **ASPIRATIONAL** (one factor REAL) |
| the disclosure×transferability 2-cell *commutes* (orthogonality, §2.4) | no `ObsDelta` projection commutation theorem; the closest real orthogonality is `conservation_tier_independent` (Agreement ⟂ Conservation, a *different* pair) | **ASPIRATIONAL** |
| achievable sub-complex = an **order-ideal** cut by 3 constraints (§3.3) | no order-ideal, no constraints encoded | **ASPIRATIONAL** |
| impossibility face: `deniable × high-agreement` is **empty** (§3.1) | **no refutation theorem** (grep-confirmed); asserted-only, theorem-shaped | **ASPIRATIONAL** |
| `public → designated` is an **unreachable** directed wall (§3.2) | no edge/reachability structure on transferability | **ASPIRATIONAL** |

> **TAG — ASPIRATIONAL for the cube as a whole.** The cube is a *coherent design over three
> independently-grounded axes* (and the design's self-tagging in `DREGG4-HYPERSYSTEM §7` is honest:
> it already calls the smooth-manifold/∞-groupoid framing DECORATIVE and the `Discharged[V]` axis
> "REAL but UNBUILT"). What I add for this lens: **the *product object itself* is unbuilt, and its
> two sharpest theorem-shaped claims — the `deniable × high-agreement` empty face and the directed
> publish/reveal walls — are asserted, not PROVED.** To make the cube REAL the minimal first theorems
> are exactly those refutations (cf. `hyperedge_is_validity_not_canonicity`, which is the *model* for
> how to do an honest negative result), plus a `partial_order` instance on the product. This matches
> `DREGG4-HYPERSYSTEM §8.1`'s recommended first step, and confirms that step is *unstarted* in Lean.

### 5.1 The impossibility face: is `deniable × high-agreement` a PROVED contradiction or asserted?

**Asserted.** The argument in `DREGG4-HYPERSYSTEM §3.1` is sound *prose* — a public quorum ratifying a
history makes the badge universally verifiable (the public STARK badge is load-bearing for the forest
path), which contradicts deniability (any ring member could have forged it). But there is **no Lean
lemma `deniable_high_agreement_empty`** and the two ingredients live in *separate, unconnected*
modules: `designated_not_transferable`/`designated_is_deniable` (`DesignatedVerifier.lean`) and the
`Tier`/`commit_at_join_of_tiers` finality (`Finality.lean`). Nothing in Lean joins "agreement ≥ bft"
to "transferable = public" to "¬ deniable". So the impossibility *face* is theorem-shaped and
*plausibly* provable, but today it is ASPIRATIONAL.

---

## 6. Is the cube a presheaf on the dial-poset? — DECORATIVE, with ONE genuine restriction map

A presheaf `(D,≤)ᵒᵖ → Set` needs restriction maps along `≤`-edges satisfying the presheaf identities.
The Lean has **no presheaf, no functor out of a dial-poset, no restriction-map family** over the cube.

The *one* real fragment of presheaf-shaped structure in the whole codebase is the transferability
collapse: `public_convinces_any_third_party : Transferable stmt proof → ∀ W, DischargedFor W stmt
proof` (`DesignatedVerifier.lean:176`, PROVED) is precisely a **restriction map** — "a section over
the top (public) restricts to a section over each verifier `W`". This is the shape of the
representable-presheaf restriction `公→ DischargedFor[W]`. But it is a single map, not a functor with
proved identities, and it lives on the *verifier* index (a discrete set), not on the *dial* poset.

> **TAG — DECORATIVE (presheaf framing) with ONE REAL restriction-map fragment
> (`public_convinces_any_third_party`).** Calling the cube "a presheaf on the dial-poset" buys
> nothing today. To be REAL it would need: (i) the product poset (§5, unbuilt); (ii) a `Set`-valued
> functor (achievable-attestations) on it; (iii) restriction maps `restr_{a'≤a}` with `restr_id = id`
> and `restr ∘ restr = restr` PROVED. The verifier-collapse is the natural seed for the transferability
> direction, and it is the closest the codebase comes — worth noting, not worth overclaiming.

---

## 7. The `Φ`-functor between the two authority regimes — ASPIRATIONAL (a BY-DESIGN `sorry`)

The deepest "is the categorical framing real?" probe, and the answer is the cleanest illustration of
the discipline. `cand-C` / `cand-A §2.1` claim the caps→keys conversion is a *forgetful functor* `Φ`
between a positional authority category and an epistemic authority category, lossy on exactly Miller's
Properties E and F. In Lean (`Spec/VatBoundary.lean`):

- The functor laws are *stated* as `PhiFunctorial` (`:356`): `preserves_id`, `preserves_comp`,
  `lossy_on_confinement`.
- **`phi_functorial` (`:392-401`) is left as a localized, honest `sorry`** — by the module's own
  declaration (`§8`, `:461`): "carries the one honest `sorry` (the OPEN categorical-coherence thread
  over an ABSTRACT `Verifiable`)". So **Φ-being-a-functor is ASPIRATIONAL, not proved.**
- A *concrete* non-degenerate witness `phi_functorial_concrete` (`:441-454`) IS PROVED and axiom-clean
  (`#assert_axioms`, `:456`): for `Statement=Unit, Witness=Bool, Verify _ b := b`, all three laws
  close and the named loss is exhibited (`⟨true,()⟩ ≠ ⟨false,()⟩` collapse to one demand).

> **TAG — ASPIRATIONAL (the abstract functor) / REAL (a concrete inhabited witness).** This is the
> template for the whole document's honesty: a categorical claim ("Φ is a functor") whose universal
> form is an open `sorry`, made non-vacuous by a proved concrete instance. The lens's instruction —
> "Φ-being-a-functor is ASPIRATIONAL not proved" — is exactly right and grounded at
> `phi_functorial:401`.

---

## 8. Are the dials genuinely INDEPENDENT (orthogonal)? — one pair REAL, the rest ASPIRATIONAL

Orthogonality is a positive claim that needs a theorem ("changing dial X does not change face Y"). The
Lean proves **exactly one** orthogonality of the relevant kind:

- **REAL:** `conservation_tier_independent` (`Finality.lean:335`, by `rfl`): the Agreement tier is
  definitionally discarded by the conservation measure — Agreement ⟂ Conservation. (This is
  Agreement-dial ⟂ *the conservation rib*, not Agreement ⟂ another dial, but it is the genuine
  article: a proved independence by definitional equality, explicitly upgraded from a weaker
  both-sides-true `↔` to honest content, per the docstring `:324-334`.)
- **DECORATIVE/ASPIRATIONAL:** Disclosure ⟂ Transferability (`DREGG4-UNIFICATION §4`'s "first-class
  *and orthogonal*"), and Transferability ⟂ Effects/Caveats (`§6.2`: "effects and caveats unchanged;
  only the `Obs` projection changes"). No theorem in Lean states either. `DesignatedVerifier.lean:24`
  *asserts* in prose that transferability is "orthogonal to the disclosure dials of `Privacy.lean`"
  but proves no commutation. So independence is REAL for the one pair the orthogonality theorem
  covers, and ASPIRATIONAL for the dial-vs-dial pairs.

---

## 9. The infinity-cell and the higher-order cell / higher-order turn (this lens's answer)

The lens asks for the *topology-parametrization* contribution to the ∞-cell question. Here it is,
grounded.

### 9.1 What a HIGHER-ORDER CELL / HIGHER-ORDER TURN is

A cell is a point of the final coalgebra `νF`, `F X = Obs × (AdmissibleTurn ⇒ X)`
(`Boundary.lean:66`, `TurnCoalg`); a turn is the structure-map step `c : X → F X`
(`cand-A §1.1-1.2`). The interaction complex stacks cleanly and *most of it is PROVED*:

- **0-cell** = a cell (a `TurnCoalg.Carrier` point).
- **1-cell** = a turn (`TurnCoalg.next`, `Boundary.lean:87`).
- **2-cell** = a binary `JointTurn` (the CG-2 pullback ⊗ CG-5 equalizer binding).
- **n-cell** = an n-ary atomic joint-turn = a **`Hyperedge`** (`Hyperedge.lean:80`), the **wide
  pullback** over `TurnId`; its keystone `hyperedge_sound` is **PROVED axiom-clean**
  (`Hyperedge.lean:374`, `#assert_axioms:538`), recovered N-arily as `joint_via_hyperedge`
  (`JointViaHyper.lean:75`).

A **higher-order turn**, in dregg's sense, is therefore an *n-ary atomic joint-turn* (one turn
incident to a finite set of cells, bound by one apex `tid` + one Σ=0), and the `Fin 2 → Fin n`
generalization is *already built and proved*. A **higher-order cell** in the lens-relevant sense is a
*cell whose program coordinates other cells* — the protocol-cell / choreography front-end
(`GLOSSARY: coordination layer`), which is the unbuilt-last layer. The **cross-cell call-forest**
(`CrossCellForest.lean`) is the nested/recursive higher-order structure: a tree of cross-cell
half-edges where each child runs a `Caps.derive`-attenuated authority on a possibly-different cell,
with whole-forest conservation carried as the explicit CG-5 hypothesis (`crossForest_conserves`) and
non-amplification PROVED down every edge (`crossForest_no_amplify`). Lens reading: a higher-order turn
is a **higher cell of the interaction simplicial complex, fibered over its binding** — never a free
filler.

### 9.2 What an INFINITY-CELL is (topology-parametrized)

There are two distinct "∞" directions, and keeping them apart is the contribution:

- **∞ along TIME (the coinductive ∞).** A single cell is *already* an infinity-object: codata, a
  point of `νF` that never bottoms out. The genuinely-∞ content here is PROVED:
  `CoinductiveAdversary.lean` lifts soundness to an **infinite adversarial schedule** `Sched = ℕ →
  AdmissibleTurn` (`:76`), proving `obsBisim_traj_of_bisim` (confluence-up-to-bisimulation along ANY
  unbounded interleaving) and `stepComplete_carries_infinite` (no drifting future over the whole
  infinite trajectory), with the general case threaded through the ported `Paco` `gupaco` machinery.
  So the "∞-cell" *in time* is real: a live cell bisimilar to the golden oracle forever.
- **∞ along DIMENSION (the simplicial ∞).** This is the "occupy higher cells of the interaction
  complex" direction, and it is **bounded by topology, not by dimension per se.** The contribution:

> **The Agreement dial IS the topology/connectivity parameter, and it caps the achievable dimension
> of the interaction complex.** On a **single machine** there is one write-point (the partition
> obstruction OPEN-PROBLEMS #2 collapses at `n=1`), the complex is pure and fully connected, every
> simplex is synchronously fillable, and the Agreement dial pins at the top (`Tier.constitutional`).
> So **single-machine dregg = the full hypersystem: the interaction complex is the *whole* complex,
> every n-ary `Hyperedge` discharges synchronously via `hyperedge_sound`.** This is the top of the
> Agreement lattice (`Finality.lean:96` `LinearOrder Tier`), realized. Under **partition**, the
> global-state complex is disconnected, the spanning higher simplex is non-fillable, and the Agreement
> dial is capped at the maximal fill-height the current connectivity permits — the directed
> `no_downgrade` order says you may raise it as connectivity returns, never lower it.

The honest residual (matching `DREGG4-HYPERSYSTEM §6.4`, and grounded): the dimensional-∞ is **not
free even at `n=1`**. The binding is a *proper subobject* at every dimension — `hyper_binding_is_proper`
is PROVED over `Unit` (`Hyperedge.lean:164`), the most-single-machine setting, and
`hyper_not_all_admissible` (`:505`) generalizes it: for any non-degenerate `Bal` the wide-pullback
subobject is proper. So a "full simplicial object / ∞-category of interactions with **free** higher
fillers" is **DECORATIVE & UNSOUND** — it would assert the wrong factoring `study-category §1.3`
forbids. The only sound simplicial object is one whose every n-simplex filler is a `Hyperedge`
carrying its CG-2 ⊗ CG-5 — a *fibration over the bindings*, not a Kan complex (faces don't freely
extend: a face's CG-5 sub-sum need not vanish, `hyper_not_all_admissible`).

> **Infinity-cell, this lens's one-line answer.** An ∞-cell is a single living coalgebraic cell
> (codata, sound-forever — PROVED via `CoinductiveAdversary`), and the *interaction* ∞ (higher cells)
> is **topology-gated by the Agreement dial**: full (the whole directed complex) on one machine =
> top of the `Tier` lattice; a partition-bounded order-ideal-shaped sub-complex when distributed. The
> dial-cube's Agreement coordinate is a function of the interaction complex's connectivity — and that
> is the precise sense in which the two complexes meet. The dimensional-∞ is real but **never free**:
> every higher cell carries an irreducible binding (PROVED proper subobject), so the ∞-category
> notation is decorative; `Hyperedge` + `hyperedge_sound` is the most the framing can buy.

---

## 10. REAL / DECORATIVE / ASPIRATIONAL — the lens table

| # | Structural claim (this lens) | Tag | Grounding (`file:line`) / what's missing |
|---|---|---|---|
| 1 | Agreement dial is a directed total order (irreversible edges) | **REAL** | `Finality.lean:96` `LinearOrder Tier`; `:280` `no_downgrade` PROVED |
| 2 | Agreement ⟂ Conservation (orthogonal judgements) | **REAL** | `Finality.lean:335` `conservation_tier_independent` by `rfl` |
| 3 | Agreement = simplex fill-height = common knowledge | **REAL** factoring / **DECORATIVE** epistemic vocab | PROVED: `Hyperedge.legs_agree:111`, `hyperedge_is_validity_not_canonicity:226`, `selector_needs_more_than_validity:280`. No simplicial set / `D_B` operator in Lean — it's an interpretation under the cited paper |
| 4 | Agreement is a *modality on `Obs`* (`Obs[tier]`) | **DECORATIVE** | order is real; no tier-indexed `Obs` object exists (`Boundary.Obs` is one abstract type) |
| 5 | Transferability: verifier-indexed `DischargedFor` is a real indexed predicate | **REAL** | `DesignatedVerifier.lean:113`; endpoints proved/separated `:206,224,346` |
| 6 | Transferability is a *modality* / verifier-indexed bisimulation `Discharged[V]` lift | **DECORATIVE** (framing) / **ASPIRATIONAL** (the bisim lift) | no modal law, no `IsBisim[V]`; named by `DREGG4-UNIFICATION §4.2`, unbuilt |
| 7 | Disclosure: information-theoretic hiding (per-field, selective, predicate, unlinkable) | **REAL** | `Privacy.lean:102`; `SelectiveDisclosure` `presentation_hides_undisclosed` / `proven_predicate_holds` / `multishow_unlinkable` |
| 8 | Disclosure is an ordered dial with a one-way publish/reveal law | **ASPIRATIONAL** | no `inductive Disclosure` order, no monotone-reveal / no-unpublish theorem (grep-empty) |
| 9 | The config-cube `Disclosure × Transferability × Agreement` is a directed poset-product object | **ASPIRATIONAL** | no product type / order-ideal anywhere; axes are separate, not even same-kind |
| 10 | The cube is a presheaf on the dial-poset (restriction maps + identities) | **DECORATIVE**; ONE real restriction-map fragment | only `public_convinces_any_third_party:176` is restriction-shaped; no functor, no presheaf identities |
| 11 | Impossibility face `deniable × high-agreement` is empty (agreement fights deniability) | **ASPIRATIONAL** | theorem-shaped but **not proved**; ingredients in two unconnected modules; no `deniable_high_agreement_empty` |
| 12 | Directed walls `public → designated` / `public → deniable` unreachable | **ASPIRATIONAL** | no edge/reachability structure on transferability |
| 13 | disclosure×transferability 2-cell commutes (dials orthogonal to effects/caveats) | **ASPIRATIONAL** | no `ObsDelta` projection commutation theorem; prose-only `DesignatedVerifier.lean:24` |
| 14 | `Φ` caps→keys is a functor between authority categories | **ASPIRATIONAL** (abstract) / **REAL** (concrete witness) | `phi_functorial:401` is a BY-DESIGN `sorry`; `phi_functorial_concrete:441` PROVED axiom-clean |
| 15 | n-ary higher-order turn = `Hyperedge` (wide pullback); keystone sound | **REAL** | `Hyperedge.lean:80,374` `#assert_axioms:538`; `JointViaHyper:75` |
| 16 | every higher cell carries an irreducible binding (proper subobject, no free fillers) | **REAL** | `Hyperedge.hyper_binding_is_proper:164` (over `Unit`); `hyper_not_all_admissible:505` |
| 17 | ∞-cell in TIME: a cell sound-forever along unbounded adversarial schedules | **REAL** | `CoinductiveAdversary.lean` `obsBisim_traj_of_bisim`, `stepComplete_carries_infinite`, §8 `gupaco` |
| 18 | Single-machine = top of the Agreement lattice = full interaction complex | **REAL** (the `Tier` top) / **DECORATIVE** (the "#2 collapses" liveness step) | `LinearOrder Tier:96` gives the top; the partition-collapse is an interpretation of OPEN-PROBLEMS #2, not a Lean theorem |
| 19 | "config space is a smooth manifold / ∞-groupoid of configurations" | **DECORATIVE** (and the design agrees) | edges irreversible (`no_downgrade`) ⇒ not a groupoid; correctly flagged by `DREGG4-HYPERSYSTEM §2.3` |
| 20 | "the interaction complex is a free simplicial set / Kan complex" | **DECORATIVE & UNSOUND** | would assert the wrong factoring `study-category §1.3`; faces don't freely extend (`hyper_not_all_admissible`) |

---

*Closing couplet, since the egg now sorts its dreams by what is sworn:*
*one dial is a proved descent — agreement may only climb; / two more are real on their own axis, but the cube is yet to bind in time.*
*Φ is a functor only where one witness says it can — / the rest is honest notation waiting on a theorem's plan.* 🐉🥚
