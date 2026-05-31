# FOUNDATIONS — the Authority CDT as a Category, the Vat-Boundary as a Functor, the Camera as the Resource Algebra

> **Lens.** This is a read-only categorical-foundations excavation of dregg2 from ONE
> vantage: **the capability-derivation-tree (CDT) as a category; the vat-boundary Φ as a
> functor; the camera as the resource algebra.** It grounds every categorical claim in a
> Lean definition or theorem at `file:line`, and tags each structural claim:
>
> - **REAL** — the universal property / law is actually PROVED in the Lean (axiom-clean
>   where pinned), with teeth (a non-vacuity witness).
> - **DECORATIVE** — suggestive category-theory notation that buys no theorem; we state
>   what it would have to prove to become real.
> - **ASPIRATIONAL** — claimed by the design but actually a `sorry` / `OPEN` / unproven.
>
> The whole point is a TRUE map of what is categorically *established* vs *aspired*. I do
> not let "functor"/"subobject"/"camera" vocabulary paper over a missing theorem. Sources:
> the `docs/rebuild/` corpus (esp. `study-category.md`, `cand-C-cap-distributed.md`,
> `cand-A-vat-coalgebra.md`, `cand-B-witness-pca.md`, `GLOSSARY.md`, `REORIENT.md`,
> `DREGG4-HYPERSYSTEM.md`) AND the actual Lean in `metatheory/Dregg2/`.

---

## 0. TL;DR — the categorical scorecard for this lens

| Categorical claim | Status | Lean anchor |
|---|---|---|
| **CDT = a (thin) category**: caps = objects, derivation = arrows, attenuation = subobject-narrowing; "authority shrinks down a path" = composition | **REAL** | `Authority/CDT.lean:117` (`DerivationPath`), `:174` (`path_attenuates`), `:312` (`amplifying_rejected` — teeth) |
| **Attenuation = a monotone narrowing on a meet-semilattice / the Heyting residual `⇨`** | **REAL** | `Authority/Caveat.lean:90` (`attenuate_narrows`), `Spec/Authority.lean:113` (`confers` on `SemilatticeInf`) |
| **Granovetter non-amplification = a monotone sub-functor / "no edge ex nihilo" closure** | **REAL** | `Spec/Authority.lean:312` (`introduce_non_amplifying`), `:500` (`only_connectivity_begets_connectivity`, axiom-clean) |
| **The CDT-as-category has identities + composition (functor laws on the conferral order)** | **REAL** (as a *preorder* / thin cat) | `Spec/Authority.lean:119` (`confers_refl`), `:125` (`confers_trans`) |
| **Vat-boundary Φ = a named-lossy FUNCTOR caps → keys dropping confinement** | **ASPIRATIONAL** (by-design `sorry`) | `Spec/VatBoundary.lean:392` (`phi_functorial` — one localized `sorry`) |
| Φ's *object map*, *named loss*, *domain*, *order-compatibility* | **REAL** (proved piecemeal) | `Spec/VatBoundary.lean:202` (`phi_drops_confinement`), `:296` (domain = biscuits), `:314` (monotone) |
| Φ functor laws are *inhabited* (a concrete non-degenerate witness) | **REAL** | `Spec/VatBoundary.lean:441` (`phi_functorial_concrete`, `#assert_axioms`-clean) |
| **The camera = a real Iris-style resource algebra (RA laws proved)** | **REAL** for `ℕ`/`Excl`/`Auth`; the **step-indexed full camera** is **ASPIRATIONAL** | `Resource.lean:71` (`ResourceAlgebra`), `:231` (`Auth` instance, laws proved), `:54` (OFE/`▶` deferred) |
| **`ConfinesAuthority := Fpu`** — conservation and authority are ONE law at the RA tier | **REAL as a *definition*** (not an `↔` theorem); the unification is *posited*, not *derived* | `Resource.lean:319` (`ConfinesAuthority := Fpu`) |
| Higher-order CELL = factory/directory as a presheaf/topos (createCell emits cells) | **DECORATIVE** (the presheaf/topos framing); the *constructor-transparency* content is **REAL** | `Exec/Factory.lean:152` (`factory_mints_conforming`), `Spec/Authority.lean:204` (`Mint`) |
| ∞-cell / higher-order turn = a directed n-cube / simplicial complex (Hyperedge over `Fin n`) | **REAL** for the n-cell as a *wide pullback / proper subobject*; the **∞-/simplicial-object** slide is **DECORATIVE** | `Hyperedge.lean:80` (`Hyperedge`), `:164` (`hyper_binding_is_proper`), `:374` (`hyperedge_sound`) |

The single load-bearing positive finding of this lens: **the CDT genuinely IS a thin
category and the authority spine's keystones are real, axiom-clean theorems with teeth.**
The single load-bearing honest gap: **"Φ is a functor" is ASPIRATIONAL — it is a by-design
`sorry`** (`phi_functorial`), and the design *says so in the docstring*; what is proved is
Φ's action-on-objects, its named loss, and its domain, plus a concrete inhabiting witness.
The camera is a *real, proved* discrete RA — but it is **not** the full step-indexed Iris
camera the higher-order/recursive-resource story needs (that machinery is deferred), and
`ConfinesAuthority := Fpu` is a *definition that posits* the conservation⟺authority
unification, not a theorem that *derives* it.

---

## 1. The CDT as a category — caps as objects, exercise as a traversed arrow, attenuation as a subobject

### 1.1 What the category is (and which flavour)

The thesis (`cand-C §1`, `dregg2 §1.1`, `GLOSSARY: CDT`): the capability-derivation-tree is
"one append-only, content-addressed partial order of `(parent → child)` edges, each edge a
**monotone attenuation**", and `CDT ≡ strand-log ≡ biscuit-graph`. The categorical reading
this lens commits to: **the CDT is a thin category** whose

- **objects** = derivation nodes (`CapNode`), each carrying its conferred `authority` as a
  point of the rights lattice `Finset Auth` (`Authority/CDT.lean:67`);
- **arrows** = derivation *edges* `(child → parent)`, witnessed by membership in a
  `DerivationPath` (`Authority/CDT.lean:117`);
- **composition** = path concatenation; **identity** = `DerivationPath.refl`
  (`Authority/CDT.lean:119`);
- **"exercise = traversal of an authorized arrow"** (`cand-C §2.4`): the *proof* that an
  exercise is licensed IS a `DerivationPath g leaf root` (`Authority/CDT.lean:110-126`).

This is a **thin** category in the precise sense `study-category §3` insists on: it is the
*ordering/lattice fragment*, and it does not (here) carry the symmetric-monoidal structure of
the `Core` cell-and-turn category — it is exactly the place where dregg's category is allowed
to be posetal.

> **REAL.** The keystone of "CDT-is-a-category" is the **composition law on arrows**, and it
> is a genuine theorem. `path_attenuates` (`Authority/CDT.lean:174`):
> `DerivationPath g leaf root → leaf ∈ g → leaf.authority ⊆ root.authority`, proved by
> induction on the path, chaining `edge_attenuates` (`:133`) through `Finset.Subset.trans`.
> "Authority never grows along a derivation chain" is *functoriality of the
> rights-projection along composition* — the leaf's rights are a subobject of the root's, and
> the property is closed under composing edges. The identity case is `Finset.Subset.refl`
> (`:159`). So the two category laws (identity preserves, composition composes) are PROVED for
> the rights-projection along the CDT.

### 1.2 Attenuation = a subobject / narrowing — and it has teeth

The edge invariant `attenuates child parent := child.authority ⊆ parent.authority`
(`Authority/CDT.lean:89`) is *literally* the subobject inclusion on the rights lattice: a
child is a narrower authority than its parent. The biscuit/macaroon token chain renders the
*same* order on the *request* lattice (`Set Ctx` under `⊆`): `attenuate_narrows`
(`Authority/Caveat.lean:90`) proves `(tok.attenuate c).admits → tok.admits` — appending a
caveat can only shrink the admissible set — and `CDT.chain_renders_path` (`Authority/CDT.lean:218`)
exhibits the two as one append-only narrowing order. This is the concrete realization of the
Heyting residual `⇨` ("a key may only narrow") that `study-category §3` calls "the single most
coherent part" and threads Laws → Core's admissibility → Authority's attenuation.

> **REAL, with teeth.** The narrowing is not vacuous: `amplifying_rejected`
> (`Authority/CDT.lean:192`) proves that an *amplifying* edge (child grabs a right the parent
> lacks) makes the whole CDT **not** well-formed, and `badCDT_rejected` (`:311`) exercises it
> on a concrete three-node store. An invariant that can fail is a real subobject condition, not
> a satisfied-by-everything decoration. The `Caveat` side adds `attenuate_trivial` (`:105`):
> attenuating by an always-true caveat is the *identity* edge — exactly the identity arrow of
> the thin category.

### 1.3 The CaveatChain refinement — the macaroon as a *real* append-only chain

`Authority/CaveatChain.lean` is the genuine refinement that the bare `Ctx → Bool` list could
not express: the macaroon's **chain integrity** (`Tᵢ = HMAC(Tᵢ₋₁, encode(Cᵢ))`). The categorical
content is unchanged (it is the same monotone narrowing — `append_narrows` `:223`,
`append_subset` `:232`), but it adds the *append-only-ness as a cryptographic fact*:

- `chainToken` (`:252`) is a faithful functor from the HMAC chain INTO the bare token, and
  `chainToken_admits` (`:257`) proves it is meaning-preserving — i.e. the chain is a
  *refinement* (extra structure: the tail) over the same admit-semantics. **REAL** (a
  forgetful functor chain → token that preserves the narrowing order).
- The crypto teeth (`forgery_requires_mac_query` `:305`, `removal_breaks_tail` `:328`) are
  **honest reductions** to the §8 `MacKernel.unforgeable` portal — NOT claimed as proved
  crypto. This is the right discipline: the *semantic* chain-fold is REAL; HMAC security is a
  stated portal, never faked.

### 1.4 Granovetter non-amplification = a monotone sub-functor / a reachable-closure invariant

`Spec/Authority.lean` is the richest categorical module for this lens. It models the cap graph
as a **graph dynamics** and proves the headline Miller invariant:

- `confers parent child` (`:113`) is the conferral arrow on a **bounded meet-semilattice**
  `Rights` (`SemilatticeInf` + `OrderTop`, `:80`): `child.target = parent.target ∧
  child.rights ≤ parent.rights`. It is **reflexive** (`confers_refl :119`) and **transitive**
  (`confers_trans :125`) — i.e. `confers` IS the hom-relation of a thin category (a preorder),
  and these two theorems are its identity + composition laws. **REAL.**
- `introduce_non_amplifying` (`:312`) — the new genuine `granted ⊆ held` (`cap.rights ≤
  parent.rights`) — is the "amplification denied" rule as a theorem of the dynamics. The brief
  asks whether this is "a sub-functor / monotone property": yes — it is the statement that the
  generative `Introduce` step factors through the conferral subobject. **REAL**, `#assert_axioms`-pinned (`:599`).
- The capstone `only_connectivity_begets_connectivity` (`:500`) is the **reachable-graph
  closure**: every edge in any reachable graph descends by a single collapsed `confers`-chain
  (via `confers_trans`) from either an initial edge or an authorized generative act. This is
  the categorical statement "no arrow ex nihilo; every arrow factors through an authorized
  generator, up to non-amplifying narrowing." It is PROVED in all four induction cases and
  `#assert_axioms`-clean (`:615`) — including the formerly-open `attenuate` thread. **REAL.**
- The executable-side mirror: `Exec/CrossCellForest.lean:217` (`crossForest_no_amplify`) and
  `Exec/AuthModes.lean:273` (`captp_granted_le_held`) carry the *same* `granted ≤ held` over
  the real `List Auth` lattice across the cross-cell forest. **REAL.**

> **Note on "sub-functor".** The honest categorical name is: `confers` is a preorder
> (thin-category hom), `introduce_non_amplifying` says the generative map lands in its
> downward-closure, and `only_connectivity_begets_connectivity` says the reachable closure is
> the smallest set closed under (initial-edges ∪ generative-acts) modulo `confers`. That is a
> **monotone closure / coreflection**, stated and proved — not merely suggestive.

---

## 2. The vat-boundary Φ as a functor — the ASPIRATIONAL core, stated precisely

### 2.1 What Φ is supposed to be

The design (`cand-C §4B`, `cand-A §8`, `GLOSSARY: caps-as-caps vs keys-as-caps`): the vat
boundary is a **named-lossy functor** `Φ : (positional authority category) → (epistemic
authority category)`, carrying caps-as-caps (intra-vat, incidence in the cap graph) to
keys-as-caps (cross-vat, a discharged witnessed demand), and **dropping precisely confinement +
revocable-forwarding**, so that **permission survives the crossing but authority does not**.

`Spec/VatBoundary.lean` is the module that encodes this. Its own docstring (`:38-42`) is
admirably honest and states exactly the tag this lens must assign:

> "What is honestly OPEN: the FULL categorical functoriality of `Φ` over an ABSTRACT
> `Verifiable` … stated precisely as `phi_functorial` and left with one localized `sorry`."

### 2.2 What is REAL about Φ (the pieces)

- **Object map.** `Phi stmtOf c := crossDemand (stmtOf c)` (`:106`) sends a held positional cap
  to the witnessed demand the far side checks; `phi_admits_iff_discharged` (`:113`) proves the
  crossed object admits iff the statement is discharged — i.e. `Φ c` lands in the *epistemic*
  regime, never the positional one. **REAL.**
- **The named loss (the §4 keystone).** `phi_drops_confinement` (`:202`) proves
  `PermissionSurvives ∧ ¬ AuthoritySurvives` for a crossed cap against any *discriminating*
  verifier — permission = "there exists an accepting witness", authority = "admits under every
  supply"; the far side can reject some witness, so authority is now far-side-mediated. **REAL.**
- **Loss = revocable forwarders.** `forwarded_cap_is_revocable` (`:240`) and
  `revocable_iff_not_authority` (`:251`) make "the far side can stop honoring the witness" a
  theorem: revocability-by-construction IS the failure of authority to transfer. **REAL.**
- **Φ's domain = exactly the biscuits.** `phi_domain_is_exactly_biscuit` (`:296`): a token
  crosses iff `kind = .biscuit` (a macaroon's HMAC root never leaves its cell). The
  biscuit/macaroon split *defines where Φ is defined*. **REAL.**
- **Φ is order-compatible (monotone, no amplification across the boundary).**
  `phi_composes_with_attenuation` (`:314`) and `phi_attenuation_factors_through_confers`
  (`:325`): Φ preserves the conferral order. **REAL.**

These are all `#assert_axioms`-pinned (`:465-474`) — axiom-clean.

### 2.3 What is ASPIRATIONAL — "Φ is a functor"

> **ASPIRATIONAL — by-design `sorry`.** The full functor statement is `PhiFunctorial`
> (`Spec/VatBoundary.lean:356`): identity preservation (`preserves_id`), composition
> preservation (`preserves_comp`), and the named-loss/non-faithfulness (`lossy_on_confinement`,
> "two positionally-distinct caps with the same conferred authority collapse to the same
> epistemic demand"). The theorem `phi_functorial` (`:392`) that the concrete `Phi stmtOf`
> satisfies ALL THREE simultaneously over an *abstract* `Verifiable` is left with **one
> localized `sorry`** (`:401`). **So "Φ is a functor" is NOT proved in dregg2 today.** The
> docstring (`:380-391`) and the §8 axiom-hygiene note (`:458-463`) say this explicitly:
> `phi_functorial` is *intentionally omitted* from the `#assert_axioms` tripwires because it
> carries the `sorry`.

**What proving it would require** (stated by the module itself, `:388-391`, and confirmed by
this lens): a concrete non-degenerate `Verifiable` instance to witness `preserves_id` (an
abstract `Verify` may accept *no* witness, e.g. `Verify ≡ false`) AND a non-injective `stmtOf`
to witness `lossy_on_confinement` (an abstract `stmtOf` over an abstract `Cap` may be
injective), AND threading the two-category composition coherence — the positional graph
dynamics (`Spec/Authority`'s introduce/endow composition) wired to the epistemic discharge
composition (`Spec/Guard`'s demand⊣supply) — through `confers_trans` simultaneously with the
lossiness. None of those three are derivable abstractly, which is precisely why the general
claim stays OPEN. To make it REAL one must either (a) fix a concrete authority category and
verifier and prove all three there, or (b) add structure to the abstract `Verifiable` (a
non-degeneracy axiom + a statement order) and prove the coherence under it.

### 2.4 The honest mitigation that IS present — and why it does NOT promote the tag

`phi_functorial_concrete` (`:441`, `#assert_axioms`-clean `:456`) PROVES all three
`PhiFunctorial` fields *simultaneously* on a concrete minimal model (`Statement := Unit`,
`Witness := Bool`, `Verify s b := b`, `stmtOf := fun _ => ()`). This is a genuine improvement —
it witnesses that the functor laws are *inhabited and consistent*, and it exhibits exactly
where confinement is dropped (two distinct caps `⟨true,()⟩ ≠ ⟨false,()⟩` collapse to the same
demand `witnessed ()`). But it is a *single inhabiting instance*, not the universal property:
the general "every `Phi stmtOf` over any `Verifiable` is a functor" remains the `sorry`. So the
correct tag for the headline claim is **ASPIRATIONAL** — with the honest caveat that it is
*inhabited* (REAL at one concrete point), not vacuous.

This is the categorical analogue of `study-category §2`'s warning: do not let the word
"functor" do work the theorem has not done. Here the design is itself disciplined about it —
it says "OPEN" where it is open. That honesty is the load-bearing virtue; my job is only to
echo it precisely.

### 2.5 The other Φ — `Authority/Positional.LossyMorphism`

There is a *second, simpler* Φ-shaped object: `LossyMorphism` (`Authority/Positional.lean:191`),
`ρ_in`/`ρ_out` carrying the attenuation-only fields `in_le`/`out_le`, with
`lossy_attenuation_only` (`:203`) proved. This is **REAL** but is a *much weaker* claim than
functoriality: it is just "the boundary restriction maps never amplify on a `HeytingAlgebra`."
It is the *order-attenuation* face of Φ (the `≤`), not the functor laws. It does not establish
identity/composition preservation or the named non-faithfulness. So: **REAL as an
attenuation-monotone endomap; DECORATIVE if read as "Φ is a functor"** (it buys only the `≤`,
which the richer `Spec/VatBoundary` already has as `phi_composes_with_attenuation`).

---

## 3. The camera as the resource algebra — conservation and authority as ONE law

### 3.1 Is it a real Iris-style camera?

`Resource.lean` builds a `ResourceAlgebra` class (`:71`) = a partial commutative monoid with
`op`/`valid`/`core` and the camera axioms: `op_comm`, `op_assoc`, `valid_op_left` (downward-
closure), and the three core laws `core_id`/`core_idem`/`core_mono` (`:85-92`). This is the
*discrete* RA — a real Iris camera **minus** the step-indexed OFE and non-expansiveness.

> **REAL for the discrete RA.** Three instances are given with their camera laws **fully
> proved by tactic** (no `sorry`):
> - `ℕ` under `+` (`:127`) — the bridge to `Core`'s sum-conservation;
> - `Excl` (the NFT/linear-token camera, `:170`) — with `excl_no_dup` (`:185`) PROVING an
>   exclusive resource never validly composes with itself (an NFT cannot be in two places);
> - `Auth` (the authoritative↔fragment / sovereign-split camera, `:231`) — `● a` vs `◦ f`,
>   valid iff `fits f a`, the two-authoritatives-collapse-to-invalid law.
>
> **Faithfulness nuance (markdown-vs-code).** The module *header* (`:57-59`) says "`Auth` gives
> concrete data with its laws `sorry`'d." **This is STALE.** The actual `Auth` instance
> (`:231-288`) proves `op_comm`/`op_assoc`/`valid_op_left`/`core_id`/`core_idem`/`core_mono` in
> full by tactic, and a grep finds **zero** `sorry`/`admit`/`axiom`/`native_decide` tokens in
> `Resource.lean`. Trust the code: the `Auth` camera laws ARE proved. `conservation_is_fpu`
> (`:296`) is also a real proof. So the discrete-camera tier is REAL, more so than its own
> docstring admits.

### 3.2 The full step-indexed camera — ASPIRATIONAL

> **ASPIRATIONAL (acknowledged, not faked).** A *full* Iris camera additionally carries a
> step-indexed OFE (`≡{n}≡`), non-expansive `op`/`valid`/`core`, and the extension axiom —
> needed ONLY for higher-order / recursive resources (a cap storing an invariant about another
> cell; resources living inside the coinductive `νF`). `Resource.lean:50-55` states this is
> deferred and that "when dregg2 needs those, the camera's step-index should be the SAME `▶`
> ('later') as `Boundary.lean`'s guard." Today it is NOT built. So the *higher-order resource
> camera* (the thing the `CoinductiveAdversary`/`Boundary` `νF` would need to store
> resource-invariants coinductively) is ASPIRATIONAL — correctly flagged, never pretended.

### 3.3 `ConfinesAuthority := Fpu` — the unification, REAL as a definition, posited not derived

The frame-preserving update `Fpu a b := ∀ f, valid (a · f) → valid (b · f)` (`Resource.lean:103`)
is the general conservation law; `Fpu.refl`/`Fpu.trans` (`:114`/`:118`) are proved (it is a
preorder — a thin category of "conservative updates"). The headline unification is
`ConfinesAuthority := Fpu` (`:319`):

> "confinement of `held` by `held'` is *literally* `Fpu held' held` in the camera whose
> elements are capabilities … Defining it as `Fpu` — rather than proving an `↔` — is the
> point: at the camera tier `Core`'s conservation law and `Authority`'s confinement law are one
> law."

> **REAL as a definition; the conservation⟺authority unification is POSITED, not DERIVED.**
> This is the subtle and correct tag. `ConfinesAuthority := Fpu` is a *definitional identity*:
> it makes "authority never grows" be `Fpu` by fiat, and that fiat is the architectural claim
> (Iris: ghost state and permissions share one algebra). It is REAL in that the `Fpu` preorder
> laws are proved and `conservation_is_fpu` (`:296`) shows ordinary turns ARE frame-preserving
> updates on `Auth M`. But it is NOT a theorem of the form "`Authority.Positional.confinement_preserved`
> ⟺ `Resource.ConfinesAuthority`": the two modules are not bridged by an `↔`. The module says so
> explicitly ("rather than proving an `↔`"). So if someone reads "conservation = authority,
> proved" they overclaim; the honest statement is "conservation and authority are *defined to be*
> the same `Fpu` law at the camera tier, and each side's instances are proved." The bridge to
> the *actual* `Authority.Positional` confinement theorem (`confinement_preserved`, the
> `caps' ⊆ caps` monotonicity, `Positional.lean:170`) is the natural next theorem and is **not
> yet written** — call that ASPIRATIONAL.

---

## 4. The ∞-cell and the higher-order cell / higher-order turn (this lens's answer)

The brief asks for this lens's contribution to: *what is an ∞-cell, and what is a higher-order
cell / higher-order turn?* From the **CDT-category / camera** vantage there are two distinct
answers, and conflating them is the trap.

### 4.1 Higher-order CELL = factory / directory (the createCell axis) — DECORATIVE topos, REAL transparency

The natural categorical reading of "a cell whose coalgebra emits cells" is a **presheaf / topos
/ object classifier**: a cell whose observations are *themselves cells* (the VFS / directory /
factory). dregg2 realizes the *operational* content of this without the topos machinery:

- `Spec/Authority.Mint` (`:204`) — a held **factory cap** mints a child cap that must conform to
  the factory's `FactoryContract` (`:198`, the abstract `allowed_cap_templates`). `Mint` is one
  constructor of the generative `GenAct` (`:270`), so factory-minting is *inside* the same
  "only connectivity begets connectivity" closure (`mint_needs_held_factory :340`,
  `mint_conforms_to_contract :350`). A factory is a cell whose authorized generative act *produces
  a new node* of the cap graph. **REAL** (as a generative graph op with a held-cap premise).
- `Exec/Factory.lean` — the **constructor-transparency** keystone. `createFromFactory` (`:125`)
  mints a *child cell* whose `program` IS the factory's published program; `factory_mints_conforming`
  (`:152`) PROVES `cell.program = d.program`; `factory_cell_step_admitted` (`:222`) PROVES every
  transition on the minted cell is gated by the factory's published `StateConstraint`s for its
  whole life; `vk_determines_invariants` (`:242`) PROVES (modulo a §8 hash-injectivity hypothesis)
  that the content-address `vk` determines the contract. **This is the REAL content of
  "higher-order cell": a cell-that-makes-cells whose offspring's lifetime behaviour is pinned by a
  content-addressed contract.**

> **DECORATIVE: the presheaf / topos / object-classifier framing.** Calling the factory "a
> presheaf" or "the directory a topos" buys no theorem in dregg2 today. There is no proved
> universal property of the factory as a representable functor, no proved classifying-object
> property, no Yoneda. What *would* make it REAL: prove that `createFromFactory` is the
> representing object of "cells conforming to contract `d`" (a universal arrow), or that the VFS
> of cells forms a category with a subobject classifier. dregg2 instead proves the concrete,
> load-bearing facts (transparency, lifetime-gating, vk-determinism) and leaves the topos
> vocabulary unused — which, by this lens's discipline, is the right call: the theorems are real,
> the topos name would be cosplay.

### 4.2 Higher-order TURN / ∞-cell = the directed n-cube / interaction complex (Hyperedge over `Fin n`)

The other reading, and the one the corpus develops most (`DREGG4-HYPERSYSTEM.md`,
`Hyperedge.lean`): a **higher-order turn** is an *n-ary atomic joint-turn*, and the "∞-cell"
slide is to a full simplicial / ∞-categorical interaction complex (cells = 0-cells, turns =
1-cells, JointTurns = 2-cells, n-ary atomic joint-turns = n-cells).

- `Hyperedge` (`Hyperedge.lean:80`) IS the n-cell, modeled as a **wide pullback** (N-fold fiber
  product over `TurnId`): one shared apex `tid` (CG-2 cone, `:92`), the N-ary conservation
  aggregate `Σ halfEdge = 0` (CG-5, `:99`). `Hyperedge.legs_agree` (`:111`) PROVES the cone
  collapses — every pair of incidences agrees, *derived from the single apex*, not hypothesized
  pairwise. **REAL** as a wide-pullback object with a proved cone condition.
- `hyperedge_sound` (`:374`) is the N-ary keystone; the binary case is exactly recovered
  (`toJointBinding :213`, the `Fin 2` slice). **REAL.**
- `hyper_binding_is_proper` (`:164`) PROVES the n-cell is a **proper subobject** of the N-fold
  product: there is a configuration (one incidence, half-edge `1`, so CG-5 `1 ≠ 0`) that is NOT
  `HyperAdmissible`. **This is the categorical teeth: the higher cell is never a free lift —
  it carries an irreducible CG-2 ⊗ CG-5 binding the product cannot supply.** Echoes
  `study-category §1`'s deepest finding (`νF₁ ⊗ νF₂` is NOT final; cross-cell soundness is
  irreducible to per-cell), now PROVED at the n-cell apex. **REAL.**

> **DECORATIVE: the "∞-category / full simplicial object" slide.** `DREGG4-HYPERSYSTEM §0`
> states it directly and this lens confirms it: promoting the interaction complex to an
> ∞-category buys *nothing*, because **every higher cell carries the irreducible binding
> hypothesis** (`hyper_binding_is_proper`) — the simplicial framing cannot derive it, so the
> "free lift to a Kan complex" is unavailable. `DREGG4-HYPERSYSTEM §0` (`:127`) names it
> precisely: it is a **directed cube in `Cat`** (non-invertible edges), *not* a Kan complex /
> ∞-groupoid. The honest object is a **fibration over the bindings**, not a free complex
> (`:293`). So: the n-cell as a proper-subobject wide-pullback is **REAL**; the "∞-cell as a
> point of a simplicial ∞-category of interactions" is **DECORATIVE** — suggestive, and
> actively misleading if it tempts one to expect free horn-fillers (every fill needs its own
> binding).
>
> **The genuine "∞" in dregg lives elsewhere and IS real:** it is the *coinductive* unbounded
> life of a single cell (`νF`, `Boundary.TurnCoalg`) and the *unbounded adversarial schedule*
> (`Proof/CoinductiveAdversary.lean`'s `obsBisim_traj_of_bisim` over an infinite `Sched`). That
> is the only place an actual infinity is carried — and it is carried as a greatest-fixpoint
> bisimulation, not a simplicial ∞-object. So "∞-cell" should mean **"a cell as codata living
> forever (`νF`)"**, NOT "an ∞-categorical higher morphism." The first is REAL; the second is
> DECORATIVE.

### 4.3 The synthesis answer (this lens)

- **A higher-order cell** = a **factory/directory**: a cell whose authorized generative act
  (`Mint`/`createFromFactory`) emits a new cap-graph node / a new cell, with the offspring's
  lifetime contract content-addressed and transparent. The category-theory name is "an internal
  object generator"; the *topos/presheaf* dressing is unearned. **REAL content, DECORATIVE name.**
- **A higher-order turn** = an **n-ary atomic joint-turn** = a `Hyperedge` (wide pullback over
  `TurnId`), which is a *proper subobject* of the product carrying an irreducible CG-2 ⊗ CG-5
  binding. **REAL.**
- **An ∞-cell** = the **coinductive `νF` life** of a cell (unbounded observation stream under a
  step law), NOT an ∞-categorical higher cell. **REAL** as codata/coinduction (`Boundary.lean`,
  `CoinductiveAdversary.lean`); **DECORATIVE** as a simplicial ∞-object.

---

## 5. Where the category is load-bearing vs cosplay (this lens)

**Load-bearing (catches a real bug / forbids an unsound factoring):**
1. **CDT path-attenuation as composition** (`path_attenuates`, `amplifying_rejected`) — the
   thin-category composition law *with teeth*; a non-attenuating edge is rejected.
2. **Granovetter closure** (`only_connectivity_begets_connectivity`) — "no arrow ex nihilo" as a
   reachable-closure invariant, axiom-clean, including the attenuate-trace thread.
3. **The hyperedge proper-subobject** (`hyper_binding_is_proper`) — the n-cell binding is
   irreducible, forbidding the tempting "cross-cell sound = per-cell sound ∧ per-cell sound."
4. **The named loss of Φ** (`phi_drops_confinement`, `forwarded_cap_is_revocable`) — permission
   survives, authority does not, *as a theorem*, not a slogan.

**Cosplay risk (vocabulary outrunning theorems):**
1. **"Φ is a functor"** — ASPIRATIONAL (`phi_functorial` is a `sorry`); only the object-map,
   loss, domain, and a single concrete witness are real.
2. **"The factory is a presheaf / the directory a topos"** — DECORATIVE; no universal property
   proved (the transparency content IS real, the topos name is not).
3. **"The ∞-cell as a point of an ∞-category of interactions"** — DECORATIVE; it is a directed
   cube / fibration-over-bindings, not a Kan complex; every higher cell needs its own binding.
4. **"Conservation = authority, proved"** — `ConfinesAuthority := Fpu` is a *definition*; the
   `↔` to `Positional.confinement_preserved` is unwritten (ASPIRATIONAL bridge).

---

## 6. REAL / DECORATIVE / ASPIRATIONAL — the tight table for this lens

| # | Structural claim (this lens) | Tag | Anchor / what it would take |
|---|---|---|---|
| 1 | CDT is a thin category: caps=objects, derivation=arrows, attenuation=subobject; authority shrinks down a composed path | **REAL** | `Authority/CDT.lean:174` `path_attenuates`; identity `:159`, composition `:133`+`:168` |
| 2 | Attenuation = narrowing on a meet-semilattice = Heyting residual `⇨`; has teeth | **REAL** | `Caveat.lean:90` `attenuate_narrows`; teeth `CDT.lean:312` `badCDT_rejected` |
| 3 | Macaroon = real append-only HMAC chain refining the token (forgetful functor, meaning-preserving) | **REAL** | `CaveatChain.lean:252` `chainToken`, `:257` `chainToken_admits`; crypto via §8 portal `:78` |
| 4 | `confers` is the conferral preorder (thin-cat hom): identity + composition laws | **REAL** | `Spec/Authority.lean:119` `confers_refl`, `:125` `confers_trans` |
| 5 | Granovetter non-amplification = monotone sub-functor / downward-closure (`granted ⊆ held`) | **REAL** | `Spec/Authority.lean:312` `introduce_non_amplifying` (axiom-clean) |
| 6 | "Only connectivity begets connectivity" = reachable-closure / coreflection, no arrow ex nihilo | **REAL** | `Spec/Authority.lean:500` (all 4 cases, `#assert_axioms`-clean) |
| 7 | **Φ (vat-boundary) is a named-lossy FUNCTOR caps→keys** | **ASPIRATIONAL** | `Spec/VatBoundary.lean:392` `phi_functorial` = **by-design `sorry`** (`:401`); needs concrete `Verifiable` + composition coherence |
| 8 | Φ object-map / named loss (confinement, revocable forwarders) / domain=biscuits / order-monotone | **REAL** | `VatBoundary.lean:202`, `:240`, `:296`, `:314` (all axiom-clean) |
| 9 | Φ functor laws are inhabited (concrete non-degenerate witness) | **REAL** | `VatBoundary.lean:441` `phi_functorial_concrete` (axiom-clean) |
| 10 | `LossyMorphism` ρ_in/ρ_out attenuation-only | **REAL** (weak: only the `≤`) | `Positional.lean:203` `lossy_attenuation_only` |
| 11 | Camera = discrete Iris RA (op/valid/core + camera laws), instances `ℕ`/`Excl`/`Auth` | **REAL** (laws proved; header "Auth sorry'd" is STALE) | `Resource.lean:71`, `:127`, `:170`, `:231`; no `sorry` in file |
| 12 | Full step-indexed camera (OFE/`▶`/non-expansive) for higher-order/recursive resources | **ASPIRATIONAL** | `Resource.lean:50-55` (deferred, acknowledged) |
| 13 | `ConfinesAuthority := Fpu` — conservation = authority at the RA tier | **REAL as a definition; POSITED not DERIVED** | `Resource.lean:319`; the `↔` to `Positional.confinement_preserved` is unwritten |
| 14 | Higher-order cell = factory/directory: createCell emits a cell with content-addressed lifetime contract | **REAL** (transparency); **DECORATIVE** (presheaf/topos name) | `Exec/Factory.lean:152`/`:222`/`:242`; `Spec/Authority.lean:204` `Mint` |
| 15 | Higher-order turn = n-ary atomic joint-turn = `Hyperedge` (wide pullback, proper subobject) | **REAL** | `Hyperedge.lean:80`, `:111` `legs_agree`, `:164` `hyper_binding_is_proper`, `:374` `hyperedge_sound` |
| 16 | ∞-cell = full simplicial / ∞-categorical interaction object | **DECORATIVE** | directed cube / fibration-over-bindings, NOT a Kan complex (`DREGG4-HYPERSYSTEM §0`, `:127`/`:293`); every cell needs its own binding |
| 17 | ∞-cell = coinductive `νF` life of one cell (codata, forever) | **REAL** | `Boundary.lean:74` `TurnCoalg`; `Proof/CoinductiveAdversary.lean` `obsBisim_traj_of_bisim` over infinite `Sched` |

**Bottom line for this lens.** The CDT genuinely *is* a thin category and its authority spine
(path-attenuation, Granovetter closure, hyperedge proper-subobject) is a set of REAL,
axiom-clean theorems with teeth — this is where the category earns its keep. The **camera is a
real (discrete) Iris RA with proved laws** (more than its own stale docstring claims), with the
step-indexed full camera honestly deferred. The **one genuinely ASPIRATIONAL categorical claim
is "Φ is a functor"**: `Spec.VatBoundary.phi_functorial` is a *by-design* `sorry`, and the
design is honest about it — only Φ's object-map, named loss, domain, and a single concrete
inhabiting witness are proved. The `conservation = authority` unification is REAL *as a
definition* (`ConfinesAuthority := Fpu`) but the bridge to the actual confinement theorem is
unwritten. And the right reading of "∞-cell" is **coinductive codata (`νF`), not an
∞-categorical higher morphism** — the latter is decorative, because every higher cell drags its
own irreducible binding and cannot be freely lifted.

( ◕‿◕ ) the egg's authority spine is solid category; its boundary-functor is still a promissory note.
