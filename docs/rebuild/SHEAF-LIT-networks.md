# SHEAF-LIT-networks — sheaves on networks/graphs, sheaf consensus, and the verifier-sheaf for dregg

**Scope.** Read-only literature distillation for ember's idea: *a metatheory of distributed systems
should not assume a single global Verifier; instead each party carries its own verifier, and the
right organizing structure is a (cellular/network) sheaf of verifiers over the parties.* This file
covers the **networks-and-consensus half**: cellular sheaves on graphs, the sheaf Laplacian, the
cohomology H⁰ = global sections = consensus / H¹ = obstruction, and the structural twin
**contextuality = no global section** from Abramsky–Brandenburger. It then maps each load-bearing
construct onto the dregg artifacts (verifier-indexed `DischargedFor`, the proof-forest, Cordial
Miners, the hyperedge/joint-turn site) and ends with an **honest line** separating the
real-and-buildable core from cohomology poetry.

Companion (sister focus, not this file): simplicial-epistemic logic for faulty agents +
reconfigurable heterogeneous quorum systems (`pdfs/zotero-simplicial-epistemic-logic-faulty-agents.pdf`,
`pdfs/zotero-reconfigurable-heterogeneous-quorum-systems.pdf`).

## Papers pulled (into `pdfs/`)

- **Hansen & Ghrist, "Toward a Spectral Theory of Cellular Sheaves"** (arXiv:1808.01513).
  `pdfs/sheaf-spectral-cellular-ghrist-hansen-1808.01513.pdf`. *The core: cellular sheaves, sheaf
  Laplacian, Hodge theorem (ker Δ ≅ Hᵏ), §8 applications incl. distributed consensus.*
- **Hansen & Ghrist, "Opinion Dynamics on Discourse Sheaves"** (arXiv:2005.12798).
  `pdfs/sheaf-opinion-dynamics-discourse-hansen-ghrist-2005.12798.pdf`. *Consensus = Laplacian flow
  → projection onto H⁰; restriction maps encode policy / selective expression / lying; harmonic
  extension via cohomology. The most directly "agents-can-lie-on-some-edges" treatment.*
- **Abramsky & Brandenburger, "The Sheaf-Theoretic Structure of Non-Locality and Contextuality"**
  (arXiv:1102.0264). `pdfs/sheaf-nonlocality-contextuality-abramsky-brandenburger-1102.0264.pdf`.
  *The structural twin: presheaf-of-events + sheaf condition (gluing); contextuality / non-locality
  = NO global section = obstruction; no-signalling = compatibility-on-overlaps.*
- **Curry, "Sheaves, Cosheaves and Applications"** (PhD thesis, arXiv:1303.3255).
  `pdfs/sheaf-cosheaves-applications-curry-thesis-1303.3255.pdf`. *Foundations: cellular sheaf =
  functor on the face poset (Alexandrov); gluing axiom = "algorithmic compression" (cover →
  compute-locally → glue via a limit = kernel of a matrix); Mayer–Vietoris = cellular sheaf
  cohomology; the three issues — Foundations / Computations / Perturbations.*

---

## 1. What a network / cellular sheaf IS, precisely

All four papers agree on the same combinatorial object (Shepard/MacPherson's *cellular sheaf*; Curry
revives it; Hansen–Ghrist make it spectral). Specialize to a graph for distributed systems.

**Cell complex / poset (the site).** Fix a regular cell complex `X` (for us: a graph `G = (V, E)`,
or higher: a simplicial complex). Cells are partially ordered by the **face incidence relation**
`σ ⊴ τ` ("`σ` is a face of `τ`"). Curry (Ch. 4, preface p. xiv): a cellular sheaf is exactly a
**functor `𝓕 : P_X → Vect`** from the face-relation poset to vector spaces — i.e. it IS a genuine
sheaf for the Alexandrov topology on the poset. The poset *is* the site; "who shares context with
whom" is the incidence structure.

**Cellular sheaf** (Hansen–Ghrist 1808.01513, Def. 2.4; Opinion 2005.12798 §2.1):

- a **stalk** `𝓕(σ)` (a vector space) on each cell `σ` — *the local data / local state / local
  verdict-space of that party*;
- a **restriction map** `𝓕_{σ⊴τ} : 𝓕(σ) → 𝓕(τ)` (a linear map) for each incident pair `σ ⊴ τ`,
- satisfying **identity** `𝓕_{σ⊴σ} = id` and **composition/functoriality** `ρ⊴σ⊴τ ⟹ 𝓕_{ρ⊴τ} =
  𝓕_{σ⊴τ} ∘ 𝓕_{ρ⊴σ}`.

On a graph: a stalk `𝓕(v)` on each **vertex** (a party's private state), a stalk `𝓕(e)` on each
**edge** (a shared "discourse"/comparison space for the two endpoints), and for an edge `e = u ∼ v`
two restriction maps `𝓕_{u⊴e} : 𝓕(u) → 𝓕(e)` and `𝓕_{v⊴e} : 𝓕(v) → 𝓕(e)`. Two parties **locally
agree on `e`** iff `𝓕_{u⊴e}(x_u) = 𝓕_{v⊴e}(x_v)` — agreement is *agreement after restriction to the
shared space*, not equality of private states. (Opinion §3: "this does not imply `u` and `v` have the
same opinions; it means their *expressions* on the shared topics agree.")

**The constant sheaf** `𝕍` (all stalks = `𝕍`, all restriction maps = id) is the degenerate
everyone-shares-everything-perfectly case — i.e. the classical single-global-verifier / classical
consensus assumption. *The whole point of going to a non-constant sheaf is to drop that assumption.*

**Cochains, coboundary, cohomology** (1808.01513 §2.2.2; Opinion §2.2):

- `Cᵏ(X; 𝓕) = ⨁_{dim σ = k} 𝓕(σ)`. So `C⁰ = ⨁_v 𝓕(v)` (a global assignment of private states),
  `C¹ = ⨁_e 𝓕(e)` (a value on every shared comparison space).
- the **coboundary** `δ : C⁰ → C¹` on an oriented edge `e = u → v`:
  `(δx)_e = 𝓕_{v⊴e} x_v − 𝓕_{u⊴e} x_u`. **`δ` measures disagreement across each edge.**
- `δ ∘ δ = 0` (from functoriality + the signed-incidence relation), giving a cochain complex and
  **sheaf cohomology** `Hᵏ(X; 𝓕)`.

**The two invariants that carry the whole idea:**

- **`H⁰(X; 𝓕) = ker δ = Γ(X; 𝓕)` = the space of GLOBAL SECTIONS.** A global section is a choice
  `x_σ ∈ 𝓕(σ)` for every cell that is *consistent across every overlap* (`x_τ = 𝓕_{σ⊴τ} x_σ` for all
  `σ ⊴ τ`; Hansen–Ghrist Def. 2.5). On a graph: private states `(x_v)` whose expressions agree on
  every edge. **H⁰ = the globally-agreed verdicts = consensus / common knowledge.**
- **`H¹(X; 𝓕)` = the OBSTRUCTION.** When local sections that agree pairwise on overlaps *cannot* be
  glued into a global section, the failure lives in `H¹`. **H¹ = forks, bugs, version-skew,
  Byzantine disagreement — the obstruction-to-agreement.**

Curry (preface p. xv) states the gluing axiom operationally: *"if one wants to query the data lying
over a large space, it suffices to pass to a cover, compute each piece separately, and then glue
together the results via a limit (kernel of a matrix)."* For graphs the limit is exactly
`ker δ = H⁰`. He also notes **Mayer–Vietoris is a special case of cellular sheaf cohomology**, and
that higher-order stitching needs a spectral sequence (Leray differentials) **which can be ignored
over graphs** (thesis Ch. 14). This is load-bearing for dregg: *the graph case is the
no-spectral-sequence, "kernel of a matrix" case — finite, checkable, programmable.*

---

## 2. The sheaf Laplacian and consensus (the load-bearing theorems)

The sheaf Laplacian is the bridge from the static invariants (H⁰/H¹) to a **distributed algorithm**
that computes them — i.e. from "consensus is the set of global sections" to "a local message-passing
process converges to consensus."

**Sheaf Laplacian** (1808.01513 §3.2; Opinion §2.3). Give each stalk an inner product (weighted
cellular sheaf). Then `δ` has an adjoint `δ*` and the **degree-0 (graph) sheaf Laplacian** is

> `L_𝓕 = δ* δ : C⁰(X; 𝓕) → C⁰(X; 𝓕)`,

a symmetric positive-semidefinite block matrix: diagonal block `L_vv = Σ_{v⊴e} 𝓕_{v⊴e}* 𝓕_{v⊴e}`,
off-diagonal block `L_vu = − 𝓕_{v⊴e}* 𝓕_{u⊴e}` for the edge `e = u∼v`. It **specializes to the
ordinary graph Laplacian when `𝓕` is the constant sheaf** (Opinion Ex. 2.3 / Hansen–Ghrist §3.2).
`(L_𝓕 x)_v` measures *the disagreement of party `v` with an (restriction-weighted) average of its
neighbors* — the local-averaging interpretation (1808.01513 Def. 3.2: a 0-cochain is *harmonic* at
`v` iff `x_v = (1/d_v) Σ_{u∼v} x_u` in the constant case).

**Hodge theorem** (1808.01513 Thm. 3.1; Opinion Thm. 2.2 — the central fact):

> **`ker L_𝓕 ≅ H⁰(X; 𝓕)`.** The kernel of the sheaf Laplacian *is* the space of global sections
> (= harmonic 0-cochains `𝓗⁰`). More generally `ker Δᵏ ≅ Hᵏ`, with the orthogonal decomposition
> `Cᵏ = 𝓗ᵏ ⊕ im δᵏ⁻¹ ⊕ im (δᵏ)*`.

So **consensus = ker L_𝓕**, computable by linear algebra; disagreement = the orthogonal complement.

**The consensus theorem** (1808.01513 Prop. 8.1; Opinion Thm. 4.1 — the dynamical version):

> The sheaf heat/diffusion flow `ẋ = −L_𝓕 x` (or discrete `x[t+1] = (I − αL_𝓕)x[t]`) is **local
> with respect to the graph** (each `ẋ_v` depends only on `v`'s neighbors) and **converges
> exponentially to the orthogonal projection of `x(0)` onto `H⁰(X; 𝓕)`** — i.e. onto the nearest
> global section. Rate = the smallest nonzero eigenvalue `λ₁(L_𝓕)` (a *sheaf* Fiedler value /
> algebraic connectivity).

This is the precise statement of "a distributed system reaches consensus on the nearest global
section." Three things make it the right primitive for a verifier-sheaf:

1. **It is a *local* protocol.** Each party only talks to its incident neighbors over the shared
   stalk `𝓕(e)`; no global coordinator. This is exactly "no single global Verifier."
2. **Consensus is the global section, NOT the naive average.** Unlike the constant-sheaf graph
   Laplacian (which always agrees on the mean), a non-constant sheaf can have `H⁰ = 0` (no nontrivial
   global section): *the agents provably cannot agree.* This is the algebraic signature of a fork /
   irreconcilable heterogeneity.
3. **Stubborn / partial agents → harmonic extension** (Opinion §5, Thm. 5.1): pin a subset `U` of
   parties' states (they refuse to move — adversarial or authoritative nodes); the rest converge to
   the **harmonic extension** of `U`, which *exists and is unique iff the relative cohomology
   `H⁰(G, U; 𝓕) = 0`.* So "can the honest majority reconcile around fixed/Byzantine inputs?" is a
   *cohomology computation*. (`H⁰(G,U;𝓕)` = global sections vanishing on `U`.)

**Heterogeneity and lying are restriction-map data** (Opinion §3, the load-bearing paragraph for the
dregg mapping):

> "Because edge stalks are not identical to vertex stalks, the discourse sheaf does not require
> everyone to share all their opinions with every neighbor… The restriction maps allow for the
> formation of *policies* from *principles*… **Negative scalar multiplication in a restriction map
> permits falsehoods: one can model agents who dissemble or deceive selectively. What C says to B
> need not match what C says to A (even if they are discussing the same topic).**"

This is the crucial structural insight: **software heterogeneity, version skew, and even Byzantine
lying are not separate concepts bolted on — they are different *restriction maps* in the same sheaf.**
A buggy/upgraded/lying party is one whose restriction maps fail to make its local section glue on the
overlaps; the failure is detected as nonzero `δ` on the incident edges and obstructs `H⁰`.

Other Hansen–Ghrist applications confirming the consensus reading: **flocking** (§8.2 — agree on a
global heading from pairwise bearings; the global heading is a section), **synchronization** (§8.7 —
denoise pairwise group elements `g_ij` to a section = cycle-consistency), and **consistent clustering**
(§8.8 — partition the graph into subgraphs each supporting a global section = the maximal
agreeing-communities). All three are "find the global section, or the maximal regions that have one"
— exactly the consensus/fork dichotomy.

---

## 3. Contextuality = no global section (the structural twin of fork = obstruction)

Abramsky–Brandenburger (1102.0264) give the cleanest, most rigorous instance of "agreement = gluing,
disagreement = cohomological obstruction." It is set-theoretic (presheaf of events) rather than
linear-algebraic (cellular sheaf), but the structure is identical and the obstruction language is
explicit.

**The setting** (A–B §2):

- a set `X` of **measurements** (read: *the questions / claims a party can be asked to verify*);
- for `U ⊆ X`, the **event sheaf** `𝓔(U) = Oᵁ` = assignments of outcomes to the measurements in `U`
  (read: *a verdict-assignment over a context*). Restriction `res^{U'}_U : 𝓔(U') → 𝓔(U), s ↦ s|U`.
- `𝓔` **is a sheaf**: the **gluing/sheaf condition** holds — a family of local sections `{s_i}` that
  is **compatible** (`s_i|U_i∩U_j = s_j|U_i∩U_j` for all `i,j`) glues to a **unique** global section
  `s` with `s|U_i = s_i`. (For events this is trivial — partial functions agreeing on overlaps glue.)
- a **measurement cover** `𝓜` = the family of *maximal jointly-performable* sets of measurements
  (an anti-chain covering `X`). **This is the simplicial site:** which questions can be answered
  together / which parties share a context.
- an **empirical model** = a *no-signalling* family of distributions `{e_C}_{C∈𝓜}`, one per context,
  **compatible on overlaps** (`e_C|C∩C' = e_{C'}|C∩C'`). A–B (§2.5): *compatibility on overlaps IS
  no-signalling* — Bob's choice of measurement cannot change Alice's marginal.

**The theorem** (A–B §3, Prop. 3.1 + Thm. 8.1 — *factorizability ⇔ global section*):

> A **global section** of the empirical model is a single distribution `d ∈ 𝒟_R 𝓔(X)` on *all*
> measurements jointly that **marginalizes to the observed `e_C` on every context** (`d|C = e_C`).
> Such a global section exists **iff** the model has a (factorizable / non-contextual / local
> hidden-variable) realization. Therefore:
>
> **non-locality and contextuality = the NON-EXISTENCE of a global section = an obstruction to
> gluing the locally-consistent family `{e_C}` into a global one.**

The Bell model has no global section (A–B Prop. 4.2 — a linear-program infeasibility); that *is*
Bell's theorem in this language. A–B even build the **incidence matrix `M`** (§4.1) — a 0/1 matrix
whose rows are restriction maps — so that *global sections = solutions of `M·X = V` over the
semiring*; existence of a global section is a linear-feasibility question. (Curry's "kernel of a
matrix" and Hansen–Ghrist's `ker L_𝓕` and A–B's `MX=V` are the **same computational shape**: glue =
solve a linear system built from the restriction maps.)

**The structural dictionary** (this is the twin):

| Abramsky–Brandenburger | dregg / distributed systems |
|---|---|
| measurement context `C ∈ 𝓜` | a set of parties sharing context (a hyperedge / joint turn) |
| local section `s ∈ 𝓔(C)` | a party-coalition's local verdict/history |
| compatibility on overlap (`= no-signalling`) | local verdicts agree on the shared sub-context |
| **global section exists** (factorizable) | **consensus / a sound global history** |
| **NO global section** (contextual / non-local) | **fork / Byzantine disagreement / unreconcilable upgrade** |
| degree of contextuality (Bell < Hardy < GHZ) | *severity* of the obstruction (a quantitative `H¹`) |

A–B stop at "obstruction to a global section"; the explicit **cohomological** computation of that
obstruction (a Čech `H¹` whose non-vanishing certifies contextuality) is the follow-on Abramsky–
Mansfield–Barbosa "Cohomology of non-locality and contextuality" line — *not in this PDF*, flagged
below as the honest gap to either pull or build.

---

## 4. The dregg mapping — verifier-sheaf, with the REAL anchors

The idea: replace the single global `Verifier` with a **(pre)sheaf of verifiers over the site of
parties**. Stalk over a party = that party's verdict-space; restriction to a shared sub-context = how
a verdict restricts to what two parties can mutually check; gluing = local verdicts agreeing on
overlaps glue to a global verified history; H⁰ = consensus; H¹ = fork/bug/skew.

The encouraging fact is that **the pieces already exist as term-proved Lean artifacts** — the sheaf
language is a *unification and generalization* of what dregg already has, not a fantasy.

**(a) Verdict indexed by party — the stalk.** `metatheory/Dregg2/Authority/DesignatedVerifier.lean`
defines `DischargedFor : Verifier → Statement → Proof → Prop` (line 109–113): the verdict is *indexed
by the verifying party `V`*. This is exactly "each party has its own verifier." Then:

- `Transferable stmt proof := ∀ V, DischargedFor V stmt proof` (line 129) — *a global section over the
  discrete verifier-set: every party is convinced.* This is the **H⁰ / public-knowledge** end.
- `DesignatedFor V₀ stmt proof := DischargedFor V₀ stmt proof` (line 138) — a single **local section**
  (one stalk).
- The theorems `public_convinces_any_third_party`, `publicMode_collapses_to_universal`
  (`Transferable ↔ ∀ V, DischargedFor V`), and `designated_not_transferable`
  (`∃ W, ¬ DischargedFor W` — a party that genuinely fails to be persuaded) are *already the
  global-section-vs-local-section distinction*, proved. The "designated-verifier disagreement" theorem
  is a baby `H¹ ≠ 0` (a local section that does not extend to a global one).

  **The sheaf generalization the file is missing:** right now the verifier index `V` is a *bare type
  with no site structure* — `DischargedFor` is a presheaf over the **discrete** category of verifiers
  (no overlaps, no restriction maps). The real upgrade: index `DischargedFor` over the **face poset of
  shared contexts** (who-shares-context-with-whom), add restriction maps `DischargedFor V →
  DischargedFor (V∩W)`, and recover `Transferable` as `H⁰`. *That is the concrete, buildable next step.*

**(b) Local proofs glue along linking — the proof-forest IS a finite sheaf-gluing.**
`metatheory/Dregg2/Exec/ProofForest.lean` is, structurally, exactly a cellular-sheaf gluing on a graph:

- each `ProofNode` carries `StepProofValid : Prop` — *the local section / local verdict* (the §8
  cryptographic-soundness seam, a hypothesis, not proved here);
- `Linked` / `chainLinked` (lines 134–148): adjacent nodes agree on the shared commitment
  (`prev.newCommit = next.oldCommit`) — *this is precisely the restriction-maps-agree-on-the-overlap
  condition `𝓕_{u⊴e}(x_u) = 𝓕_{v⊴e}(x_v)`*, with `𝓕(e) = ` the commitment/effects-hash linking surface;
- `fullProofForestInv := (∀ n, n.StepProofValid) ∧ Linked` (line 161) ⟹ a composed, globally-valid
  history — *this is the gluing theorem: pairwise-agreeing local sections + per-node validity ⟹ a
  global section.*

So the existing proof-forest composition theorem (`PF-Lean`, task #101) **is** the H⁰ statement of a
verifier-sheaf, restricted to (i) a *path/chain* site and (ii) *equality* restriction maps along the
chain-link. The honest generalization is to allow (i) a genuine **DAG/hypergraph** site and (ii)
non-trivial restriction maps (different commitment schemes / verifier software per node = different
restriction maps = genuine heterogeneity). `Exec/CrossCellForest.lean` already pushes toward (i).

**(c) The simplicial site = hyperedge / joint turn.** dregg's `Hyperedge` / `JointTurn` (multi-party
turns) is the measurement-context / maximal-jointly-performable-set `C ∈ 𝓜` of A–B, and the
1-/2-cells of the cellular complex. A turn jointly witnessed by parties `{P₁,…,Pₖ}` is a `k`-cell;
its faces are the sub-coalitions that share that context. **The simplicial-epistemic-logic-for-
faulty-agents paper is the same site** (a simplicial complex of compatible local states); the sheaf
adds *data* (verdict-stalks) and *cohomology* (the obstruction) on top of that bare complex.

**(d) Consensus = agreement = H⁰; fork = obstruction = H¹.** `metatheory/Dregg2/Proof/CordialMiners.lean`
(the real Cordial-Miners DAG model, tasks #106/#113) computes *super-ratification* — agreement derived
from the lace structure. In sheaf terms, ratification is the statement "the local verdicts over the
DAG glue to a global section," i.e. the projection onto `ker L_𝓕`/H⁰. **Equivocation / a fork is a
nonzero class in H¹** (incomparable, non-gluing local sections) — and dregg's equivocation-by-
incomparability detector (`R-BLOCKLACE`, task #105) is the combinatorial shadow of "this family does
not glue." The blocklace's "Byzantine-repelling" property is, conjecturally, a *Cheeger-type* bound on
the sheaf Laplacian (Hansen–Ghrist §7): a spectral guarantee that a bounded fraction of bad restriction
maps cannot collapse `H⁰`.

**(e) The Galois connection (verify/find seam) and the diffusion.** The verify-vs-find seam noted in
the foundations review is the adjunction between *checking* a global section (apply `δ`, test `= 0`)
and *constructing* one (project onto `ker L_𝓕` via the diffusion flow `ẋ = −L_𝓕 x`). The Hodge
decomposition `Cᵏ = 𝓗ᵏ ⊕ im δ ⊕ im δ*` is the precise statement that *every local state splits into a
consensus part (𝓗⁰) and a disagreement part (im δ*)* — a clean target for a "distance-to-consensus"
metric on dregg histories.

---

## 5. The honest line (kernel-exposes-gaps discipline)

**REAL and buildable (the core that cashes out as theorems):**

1. **Proof-forest = finite sheaf-gluing on a graph.** Already term-proved (`ProofForest.lean`,
   `fullProofForestInv`). The chain-link IS restriction-map-agreement; composition IS H⁰. This is not
   poetry — it is the existing theorem, re-read in sheaf vocabulary. *Generalizing the site
   path→DAG/hyperedge and the restriction maps equality→arbitrary-linear is a concrete diff.*
2. **Verifier-indexed verdict = stalk.** `DischargedFor : Verifier → …` is already verdict-per-party;
   `Transferable = ∀V, DischargedFor V` is already "global section over the discrete verifier set."
   *Adding site structure (overlaps + restriction maps) to the verifier index is the buildable upgrade
   that turns this from a presheaf-over-a-discrete-set into a genuine sheaf.*
3. **The target theorem (the generalization worth proving).** *Proof-forest soundness generalized over
   a verifier-sheaf:* heterogeneous local verdicts (`DischargedFor` per party, possibly different
   verifier software = different stalks/restriction maps) that **agree on every overlap** ⟹ a **sound
   global verdict** (a global section / `H⁰` element). This is Hansen–Ghrist Prop. 8.1 + A–B Thm. 8.1
   instantiated to dregg's verifier-stalks. It is REAL because (a) the gluing is finite and
   linear-algebraic ("kernel of a matrix," Curry; no spectral sequence over graphs), and (b) dregg
   already has the path/equality special case proved. **This is the theorem that would make the
   sheaf-of-verifiers claim load-bearing rather than suggestive.**
4. **Fork/bug/skew/Byzantine = restriction-map data, detected as δ ≠ 0 / H¹ ≠ 0.** Opinion §3's
   "negative-scalar restriction map = lying" + "what C says to A ≠ what C says to B" is the rigorous
   model for software bugs, upgrades (v1 vs v2 = different sections; backward-compat = overlap-
   agreement), and heterogeneity. dregg's equivocation-by-incomparability is its combinatorial shadow.

**SUGGESTIVE until it cashes out (the cohomology poetry to either prove or quarantine):**

- **"H¹ = the invariant classifying all forks."** The *definition* of `H⁰`/`H¹` over a graph is solid
  and finite. But the claim that "H¹ is THE complete invariant of Byzantine disagreement" is, so far,
  vocabulary. To make it real: exhibit a fork in a concrete dregg run, build the verifier-sheaf, and
  *compute a nonzero H¹ class that certifies that specific fork* — and conversely prove `H¹ = 0 ⟹ no
  fork`. Until that round-trip is a Lean/Rust artifact, "cohomology of consensus" stays a slogan.
- **"Byzantine-repelling = a Cheeger inequality on `L_𝓕`."** Hansen–Ghrist's structural Cheeger
  inequality (§7) is *preliminary even in their paper* ("we have some preliminary results"). Mapping
  the blocklace's f-Byzantine tolerance to a spectral gap `λ₁(L_𝓕)` bound is an attractive conjecture,
  NOT a theorem — do not state it as one.
- **The explicit cohomological obstruction class for contextuality** (Čech `H¹` à la Abramsky–
  Mansfield–Barbosa) is *not in the A–B PDF we have*; A–B only prove "obstruction to a global section"
  qualitatively (a linear-feasibility (in)existence). The sheaf-cohomology-as-fork-certificate needs
  that follow-on paper (gap flagged in §6).
- **Higher cells / `H^{≥2}`.** Curry: over graphs there are no higher obstructions (no spectral
  sequence). The moment dregg's site is a genuine *simplicial complex* of multi-party joint turns
  (not just a graph), `H^{≥2}` and Leray differentials reappear — interesting, but explicitly
  *deferred*; the graph/DAG case is the buildable one and is sufficient for the consensus story.

**Discipline:** keep §5.1–5.4 (REAL) separate from §5's suggestive list in any downstream write-up.
The sheaf vocabulary must *generalize an existing theorem* (the proof-forest gluing), never *paper over
a missing one*. The single most valuable next artifact is theorem (3): proof-forest soundness over a
verifier-sheaf.

---

## 6. Gaps / further fetches (named, not silently skipped)

- **Abramsky, Mansfield & Barbosa, "The Cohomology of Non-Locality and Contextuality"** (QPL 2011,
  arXiv:1111.3620) — the explicit Čech-`H¹` obstruction class. *This is the paper that turns A–B's
  "no global section" into a computable cohomology class — the direct twin of "H¹ certifies a fork."*
  **Present in the library** (`pdfs/sheaf-cohomology-nonlocality-1111.3620.pdf`, fetched alongside
  this review). Distilling its Čech-`H¹` construction is the next step for cashing out §5's
  "H¹ as the complete fork invariant" from suggestive to a buildable certificate.
- **Robinson, sheaves-on-networks / topological signal processing** (`pdfs/sheaf-networks-robinson-1308.4621.pdf`)
  and **a distributed-tasks sheaf paper** (`pdfs/sheaf-tasks-distributed-2503.02556.pdf`) — also now
  in the library (sibling fetches); the Robinson line is the engineering "consistency radius"
  (distance-to-a-global-section), the practical analogue of a dregg "distance-to-consensus" metric.
- **Hansen & Ghrist, "Distributed Optimization with Sheaf Homological Constraints"** (Allerton 2019)
  and **Hansen's thesis "Laplacians of Cellular Sheaves"** (UPenn 2020) — the fuller spectral/Cheeger
  development behind 1808.01513 §7.
- **Riemann/Robinson, "Sheaves are the canonical data structure for sensor integration"** and
  Robinson's *Topological Signal Processing* — the engineering "consistency radius" (= a quantitative
  distance-to-a-global-section), the practical analogue of a "distance-to-consensus" metric.
- The companion sister-file should connect this to `zotero-simplicial-epistemic-logic-faulty-agents.pdf`
  (the bare site of faulty agents — the sheaf adds verdict-data + cohomology on top) and
  `zotero-reconfigurable-heterogeneous-quorum-systems.pdf` (heterogeneous quorums = a non-constant
  sheaf where stalks/restriction maps differ per node = genuine software heterogeneity).

## 7. One-paragraph summary

A network sheaf assigns a verdict-space (stalk) to each party and a restriction map to each shared
context, with the sheaf Laplacian `L_𝓕 = δ*δ` as the bridge to a *local* (no-global-coordinator)
algorithm: `ker L_𝓕 ≅ H⁰` = the global sections = **consensus**, and the diffusion `ẋ = −L_𝓕 x`
converges to the nearest global section (Hansen–Ghrist Prop. 8.1 / Opinion Thm. 4.1); software
heterogeneity, upgrades, and Byzantine lying are all just *restriction-map data* (Opinion §3), and a
**fork is the failure to glue = a nonzero `H¹`**, the exact structural twin of Abramsky–Brandenburger's
**contextuality = no global section = obstruction**. In dregg this is not aspirational: `DischargedFor`
is already a per-party verdict, `Transferable = ∀V, DischargedFor V` is already a global section over
the (discrete) verifier set, and the proof-forest's `Linked + StepProofValid ⟹ composed validity` is
already a finite sheaf-gluing on a graph. The honest, buildable theorem that would make the whole claim
load-bearing — and the recommended next artifact — is **proof-forest soundness generalized over a
verifier-sheaf: heterogeneous local verdicts agreeing on overlaps ⟹ a sound global verdict** —
everything else (H¹ as the complete fork invariant, a Cheeger/Byzantine-tolerance spectral gap, the
explicit cohomology class, higher cells) stays explicitly flagged as suggestive until it term-proves.
