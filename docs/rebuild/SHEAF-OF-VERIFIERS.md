# SHEAF-OF-VERIFIERS — a metatheory of distributed systems with no global oracle

> **The idea (ember).** A real metatheory of distributed/decentralized systems should **not**
> assume a single global `Verifier`. Each party has its OWN verifier; the structure that organizes
> a family of per-party verifiers is a **(pre)sheaf**: a sheaf 𝒱 of verifiers over the **site** of
> parties (the simplicial-epistemic complex of who-shares-context). Restriction maps say how a
> verdict restricts to a shared sub-context; the **gluing/sheaf condition** says local verdicts that
> agree on overlaps glue to a global section. This one structure captures **software bugs** (a
> party's section is wrong, disagrees on the overlap, fails to glue), **upgrades** (v1 vs v2 =
> different sections; backward-compat = overlap-agreement), and **genuine heterogeneity** (different
> software per node = different sections). The **cohomology** is the invariant: **H⁰ = the
> globally-agreed verdicts** = consensus / common knowledge; **H¹ = the obstructions** = forks,
> bugs, version-skew, Byzantine disagreement.

> **The honest line (kept front and center; the kernel-exposes-gaps discipline).** The
> **proof-forest-as-finite-sheaf-gluing is REAL** (term-proved in `Exec/ProofForest.lean`). The
> **verifier-indexed `DischargedFor` is the REAL first step** (a verdict genuinely indexed by the
> checking party). The **cohomology-of-consensus (H⁰ = consensus, H¹ = fork) is SUGGESTIVE** —
> backed by published theorems in adjacent fields, but **POETRY inside dregg until it cashes out as
> a Lean theorem.** The single line past which "sheaf of verifiers" stops being suggestive is the
> theorem in §5: **proof-forest soundness GENERALIZED over a per-node verifier-sheaf**. Sheaf
> vocabulary must *generalize an existing theorem*, never *paper over a missing one*.

**Source distillations this doc synthesizes** (read in full):
- `docs/rebuild/SHEAF-LIT-networks.md` — cellular sheaves on graphs, the sheaf Laplacian, H⁰=ker δ,
  contextuality = no global section (Hansen–Ghrist; Abramsky–Brandenburger; Curry).
- `docs/rebuild/SHEAF-LIT-epistemic.md` — the simplicial-epistemic ↔ Kripke equivalence, the
  Čech-H¹ obstruction, the 2025 task-sheaf bridge, heterogeneous quorums; ESTABLISHED/ANALOGY tags.
- `docs/rebuild/SHEAF-GROUND-dregg.md` — what dregg ALREADY term-proves, mapped row-by-row to sheaf
  structure, tagged REAL/PARTIAL/POETRY at `file:line`.

Each downstream claim is tagged **REAL** (a term-proved Lean theorem with teeth), **ESTABLISHED**
(a published theorem in the lit), **ANALOGY** (a motivated correspondence not yet a dregg theorem),
or **POETRY / OPEN** (vocabulary naming the theorem it would have to prove).

---

## 1. THE PRECISE STRUCTURE — the site, the (pre)sheaf 𝒱 of verifiers, restriction, gluing

A sheaf needs four data: a **site**, a **stalk** over each object, **restriction maps** along
incidences, and the **gluing/sheaf condition**. We give each, grounded in the network-sheaf
definitions from the lit (`SHEAF-LIT-networks.md §1`), and pin the dregg analogue at `file:line`.

### 1.1 The site — the simplicial-epistemic complex of who-shares-context

Fix the combinatorial object all four lit sources agree on (Shepard/MacPherson's cellular sheaf;
Curry's functor-on-the-face-poset; `SHEAF-LIT-networks.md §1`). For distributed systems the site is
a **chromatic simplicial complex** ⟨V, S, χ⟩ (`SHEAF-LIT-epistemic.md §1`, Goubault–Kniazev–Ledent–
Rajsbaum, Def. 1):

- **vertices V = local states**, each colored χ by the party that owns it;
- **simplices S = compatible tuples of local states** — a set of local states that can *coexist in
  one global state*;
- **facets (maximal simplices) = global states / possible worlds.**

The crux equivalence (`SHEAF-LIT-epistemic.md §1`, Theorem 4, **ESTABLISHED**): the category of
pure chromatic simplicial complexes is **equivalent** to the category of proper S5ₙ epistemic
frames; **`w ∼_a w′` (party `a` cannot distinguish the two worlds) ⟺ the two facets share the
vertex colored `a`.** *Indistinguishability is shared faces.* The site `is` the who-shares-context
structure.

**dregg's site (REAL as a poset/DAG; POETRY as a Grothendieck site):**

- The **proof-forest's happened-before chain/DAG** — `ProofForest.nodes` ordered by `Linked`
  (`Exec/ProofForest.lean:137,148`). A path-shaped site today.
- The **N-ary `Hyperedge`** — the simplicial joint-turn. `structure Hyperedge`
  (`Hyperedge.lean:80`) is a **wide pullback over `TurnId`**: the participant tuple `x : ι → T.Carrier`
  is a simplex's vertices, the apex `tid` is the shared sub-context all incidences restrict to, and
  the cone condition `agree` (CG-2) makes it a genuine compatible-tuple. `legs_agree`
  (`Hyperedge.lean:111`, PROVED) recovers the O(N²) pairwise agreements from the single apex — the
  cone collapse. **Tag: REAL as the simplicial site / wide-pullback** (construction + soundness
  proved); **POETRY as a Grothendieck topology / Kan complex.**

**A proved constraint on the site the verifier-sheaf must respect.** The hyperedge is a **proper
subobject**: `hyper_not_all_admissible` (`Hyperedge.lean:505`, PROVED) shows *not every product
tuple is a simplex* — a face of a balanced hyperedge is generally unbalanced. So the only sound
sheaf is a **fibration over the bindings, never a free complex** (`SHEAF-GROUND-dregg.md §5`); covers
are the bindings, and gluing across a partition can be *unfillable*. This matters: it is the dregg
shadow of "the protocol complex is a *proper* subcomplex of the full join" (`SHEAF-LIT-epistemic.md
§1`, `hyper_not_all_admissible` = "the simplicial complex is a proper subcomplex").

### 1.2 The stalk — 𝒱(party) = that party's VerifierKernel

The (pre)sheaf 𝒱 of verifiers assigns to each party `V` (each vertex / cell of the site) its
**verdict-space** — the set of verdicts `V`'s own verifier can issue. In the lit this is the stalk
`𝓕(σ)` of a cellular sheaf (`SHEAF-LIT-networks.md §1`, Hansen–Ghrist Def. 2.4): "the local data /
local state / local verdict-space of that party." Felber et al. (2025) make it literal — **one
sheaf `F_p` per process `p`**, "a set of functors with common codomain"
(`SHEAF-LIT-epistemic.md §4`, Def. 17 + §4.2) — which is **exactly** ember's "(pre)sheaf of
verifiers over the parties."

**dregg's stalk (REAL — the one place the verdict is genuinely indexed by who checks):**

```
def DischargedFor [DVKernel Verifier Statement Proof VSecret]      -- DesignatedVerifier.lean:113
    (V : Verifier) (stmt : Statement) (proof : Proof) : Prop :=
  DVKernel.verifyFor (VSecret := VSecret) V stmt proof = true
```

`verifyFor : Verifier → Statement → Proof → Bool` (`DesignatedVerifier.lean:89`) is the
verifier-**indexed** oracle: *unlike* the universal `presentation.rs::verify(&self)` and the Lean
`Laws.Discharged` (`Laws.lean:38`), the verdict may depend on **who** is checking. The module's
opening states the gap it closes: the running system has "a single UNIVERSAL verify relation, NOT
indexed by who is checking" and "cannot even EXPRESS 'convincing only to verifier V'"
(`SHEAF-GROUND-dregg.md §2`). `DischargedFor V s p` is **the germ of the section at the stalk over
party `V`.** **Tag: REAL.**

### 1.3 The restriction maps — how a verdict restricts to a shared overlap

For an incidence `σ ⊴ τ` the sheaf carries `𝓕_{σ⊴τ} : 𝓕(σ) → 𝓕(τ)`; two parties **locally agree on
the shared edge `e`** iff `𝓕_{u⊴e}(x_u) = 𝓕_{v⊴e}(x_v)` (`SHEAF-LIT-networks.md §1`, Opinion §3).
Agreement is *agreement after restriction to the shared space*, **not** equality of private states —
"their *expressions* on the shared topics agree." Heterogeneity, version-skew, and even Byzantine
lying are **restriction-map data**, not separate concepts (`SHEAF-LIT-networks.md §2`, Opinion §3:
"negative scalar multiplication in a restriction map permits falsehoods… what C says to B need not
match what C says to A").

**dregg's restriction-agreement (REAL as the agreement relation; PARTIAL as a functorial ρ):**

```
def chainLinked : List ProofNode → Prop                 -- ProofForest.lean:137
  | a :: b :: rest =>
      a.newCommit = b.oldCommit          -- state continuity across the overlap
      ∧ b.prevReceipt = a.newCommit      -- receipt-chain pointer agrees on the overlap
      ∧ b.seq = a.seq + 1                -- monotone (no replay/fork)
      ∧ chainLinked (b :: rest)
def Linked (pf : ProofForest) : Prop := chainLinked pf.nodes   -- :148
```

`a.newCommit = b.oldCommit` **IS** the restriction-agreement: section `a` restricted to the `a∩b`
overlap (its terminal commitment) equals section `b` restricted to the same overlap (its initial
commitment); `𝓕(e)` is the shared commitment/effects-hash linking surface. This is purely
combinatorial — no crypto — and is the verifier's PROVED-side check.

A **second** restriction law on the same site: the cross-cell overlap is not `new = old` continuity
but the **CG-5 N-ary balance** `Σδ = 0` (`crossForest_attests`, `CrossCellForest.lean:278`, PROVED;
`δ` is already a field `ProofForest.lean:93`). So the site has two kinds of cover — intra-cell
sequential (`new = old`) and cross-cell hyperedge (`Σδ = 0`, valued in a commutative monoid). This
is genuinely richer than continuity alone (`SHEAF-GROUND-dregg.md §1.5`).

**Tag: REAL as the agreement *equation* `ρ_a(a) = ρ_b(b)`; PARTIAL as a functorial restriction
map** — dregg has the equation, not yet ρ as a functor with `ρ_{σ⊴σ} = id` and `ρ∘ρ` coherence (no
`CategoryTheory.Presheaf` instance; the word "sheaf" does not appear in `Dregg2/`,
`SHEAF-GROUND-dregg.md §1` grep-confirmed).

### 1.4 The gluing / sheaf condition — local verdicts agreeing on overlaps glue

The sheaf condition: a **compatible** family of local sections (agreeing pairwise on overlaps) glues
to a **unique** global section (`SHEAF-LIT-networks.md §1,§3`; Abramsky–Brandenburger §2.4). For
graphs the glue is "kernel of a matrix" — finite, checkable, no spectral sequence (Curry;
`SHEAF-LIT-networks.md §1`). `H⁰(X;𝓕) = ker δ = Γ(X;𝓕)` = the global sections.

**dregg's gluing (REAL — term-proved, axiom-clean):**

```
theorem proofForest_sound (pf : ProofForest)                       -- ProofForest.lean:177
    (hvalid : ∀ n ∈ pf.nodes, n.StepProofValid)   -- (P) every local section verifies  [§8 seam]
    (_hlinked : Linked pf) :                        -- (L) sections agree on overlaps    [PROVED-side]
    fullProofForestInv pf := by
  unfold fullProofForestInv
  exact execForest_attests (pf.attested hvalid)
-- #assert_axioms proofForest_sound                                -- ProofForest.lean:223 (axiom-clean)
```

The split is **exactly the sheaf split**: (P) `∀ n, StepProofValid` is the per-open local data; (L)
`Linked` is the compatibility-on-overlaps condition; the conclusion `fullProofForestInv` (the
four-conjunct `StepInv` over the whole forest — Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance)
is the unique global section. `StepProofValid : Prop` (`ProofForest.lean:98`) is the §8
cryptographic-soundness seam — a named abstract `Prop`, never a concrete predicate, entered as DATA
exactly like the `CryptoKernel`/`World` portals. **Tag: REAL** (finite gluing); **POETRY** as a
colimit universal property (`SHEAF-GROUND-dregg.md §1.3`).

**The sheaf condition BITES** (the gluing is non-vacuous because non-gluing is witnessed):

```
def badNode : ProofNode := { oldCommit := 99, … StepProofValid := True }   -- ProofForest.lean:288
example : ¬ chainLinked [node0, badNode] := by …                          -- ProofForest.lean:293
```

Each node individually verifies (`StepProofValid := True`), yet they DO NOT glue: `node0.newCommit
(1) ≠ badNode.oldCommit (99)` — the verifier rejects at the overlap check. **Tag: REAL as a witnessed
non-gluing.** This is the structural twin of Abramsky–Brandenburger's "locally compatible family that
has no global section = contextuality" (`SHEAF-LIT-networks.md §3`).

### 1.5 The Laplacian bridge (lit-only, ANALOGY in dregg)

The lit supplies the *algorithm* that finds the gluing without a coordinator: the **sheaf Laplacian**
`L_𝓕 = δ*δ` (`SHEAF-LIT-networks.md §2`, Hansen–Ghrist §3.2), with the **Hodge theorem**
`ker L_𝓕 ≅ H⁰` (Thm. 3.1) and the **consensus theorem** — the *local* diffusion `ẋ = −L_𝓕 x`
converges exponentially to the projection onto the nearest global section (Prop. 8.1 / Opinion
Thm. 4.1). It specializes to the ordinary graph Laplacian for the **constant sheaf** (the classical
single-global-verifier case). dregg has no Laplacian object; this is the **ANALOGY** layer (and the
home of the suggestive Byzantine-tolerance = Cheeger-gap conjecture, §3 below).

---

## 2. THE CAPTURE — bugs / upgrades / heterogeneity as sections + overlap-(dis)agreement

The structural payoff: **bugs, upgrades, and heterogeneity are not three concepts bolted on — they
are different *sections* of the same verifier-sheaf, distinguished only by their restriction-map
data** (`SHEAF-LIT-networks.md §2`, Opinion §3; `SHEAF-LIT-epistemic.md §5`, Li–Lesani). The systems
anchor is the heterogeneous quorum system (`SHEAF-LIT-epistemic.md §5`, Li–Lesani DISC 2024,
**ESTABLISHED systems**): each party `p` declares its own trust set `Q(p)` (its own section of
who-it-believes), consistency = quorum intersection `q ∩ q′ ∩ P ≠ ∅` (the overlap-agreement /
sheaf-compatibility condition), and "reconfiguration can be the antecedent to a fork and
double-spending" (an incompatible upgrade = a self-inflicted loss of the global section).

| Phenomenon | Sheaf-of-verifiers reading | dregg witness |
|---|---|---|
| **Software bug** | a party's stalk carries a wrong verdict that **disagrees on the overlap** → the family fails to glue → no global section | `¬ chainLinked [node0, badNode]` (`ProofForest.lean:293`): each node valid, but `1 ≠ 99` at the overlap |
| **Upgrade (v1 vs v2)** | two different sheaves over a moving site; **backward-compat = restriction maps still agree on the shared sub-context** (the reconfigured sheaf still admits a global section); incompatible upgrade = self-inflicted H¹ fork | expressible the moment `Vᵢ` varies (§5); a *theorem* about backward-compat is modeled on `Upgrade.lean`'s `no_downgrade`/genealogy spine (`SHEAF-GROUND-dregg.md §7.3`) — OPEN |
| **Genuine heterogeneity** | the sheaf is honestly **non-constant**: different verifier software per node = different stalks/restriction maps; agreement is "agree *after a restriction map*," not "hold identical bits" | `designated_not_transferable` (`DesignatedVerifier.lean:206`): a *concrete* party `W` provably rejects a verdict another accepts |
| **Byzantine lying** | a restriction map that lies (Opinion §3's negative-scalar map) → `δ ≠ 0` on the incident edges → obstructs H⁰ | `Equivocator` (`CordialMiners.lean:144`): a party emitting two incomparable blocks — a local datum that cannot glue |

### 2.1 Worked micro-example (grounded in the term-proved non-gluing witness)

Take the smallest concrete case dregg already proves, and re-read it as the verifier-sheaf capture.

**Site:** a 2-node path — two adjacent cell-steps `node0 → node1`, sharing one overlap (the
boundary commitment). **Sections:** each node's `StepProofValid`. **Restriction:** `newCommit` of
`node0` vs `oldCommit` of the successor.

- **Honest, homogeneous run (glues → H⁰).** `goodProofForest`: `node0.newCommit = node1.oldCommit`,
  so `chainLinked [node0, node1]` holds (`ProofForest.lean:266`) and `fullProofForestInv
  goodProofForest` follows (`ProofForest.lean:274`). The two local verdicts **glue to one global
  verified history** — a global section. This is the H⁰ content.
- **Buggy / version-skewed node (fails to glue → the obstruction).** Replace `node1` by `badNode`
  with `oldCommit := 99` and `StepProofValid := True` (`ProofForest.lean:288`). Each node *still
  verifies locally* — `node0`'s verifier and `badNode`'s verifier each say "valid." But they
  **disagree on the overlap** (`1 ≠ 99`): `¬ chainLinked [node0, badNode]` (`ProofForest.lean:293`,
  PROVED). The compatible-family hypothesis fails; there is **no global section**. In ember's
  framing: `badNode` is a party running buggy/upgraded software whose restriction map no longer
  matches its neighbor's on the shared sub-context — the canonical software-bug / version-skew /
  fork, made into a *proved non-gluing*.

This is the whole capture in miniature: **local validity is per-stalk (each verifier accepts its own
section); gluing is the overlap-agreement; a bug/upgrade/heterogeneity is a section whose restriction
fails to match on the overlap, and the obstruction is exactly the failure to glue.** The heterogeneity
is genuine, not hypothetical: `designated_not_transferable` (`DesignatedVerifier.lean:206`, PROVED)
extracts a *concrete* party `W` whose verifier rejects a verdict `V₀` accepts, and
`dial_endpoints_distinct` (`DesignatedVerifier.lean:346`, PROVED, axiom-clean over a 2-verifier
reference kernel) witnesses the separation — dregg already has **heterogeneous, non-gluing local
verdicts as a proved phenomenon** (`SHEAF-GROUND-dregg.md §2.3`).

---

## 3. THE COHOMOLOGY — H⁰ = consensus, H¹ = obstruction (with the honest ledger of what's proved)

### 3.1 H⁰ = the global section = consensus / common knowledge

`H⁰(X;𝓕) = ker δ = Γ(X;𝓕)` is the space of global sections (`SHEAF-LIT-networks.md §1`,
Hansen–Ghrist Def. 2.5; `SHEAF-LIT-epistemic.md §2`, `H⁰ ≅ Γ`). Three independent literatures state
**"consensus = a global section (H⁰)"** as a theorem, NOT an analogy (`SHEAF-LIT-epistemic.md §7`,
**ESTABLISHED**): (i) epistemic-connectivity — common knowledge ⟺ `∼`-connectivity (Halpern–Moses
lineage, Goubault et al.); (ii) cellular-sheaf `H⁰ ≅ Γ` (Hansen–Ghrist, Curry); (iii) the 2025
task-sheaf Thm 20 — *task solvability ⟺ existence of a global section*, with the section space
computed as `H⁰ = ker D` (Felber–Hummes Flores–Rincon-Galeana).

**dregg HAS the H⁰ *content* (REAL); it does NOT have an H⁰ *object* (POETRY):**

- a unique global verified history: `proofForest_sound` (`ProofForest.lean:177`);
- one final leader per wave: `cordial_agreement` (`CordialMiners.lean:336`, PROVED, axiom-clean) —
  agreement proved by **quorum intersection at an honest party** (two `n−f` ratification quorums
  share an honest ratifier whose honesty law forces the two leaders equal), with the ratifying set
  **read off the real blocklace** (`superRatifiedFromLace`, `CordialMiners.lean:232`;
  `cordial_agreement_from_lace`, `CordialMiners.lean:484`), not assumed. The honest-party-in-the-
  intersection IS the overlap on which the local sections must agree.
- one verdict for all parties: `public_convinces_any_third_party` (`DesignatedVerifier.lean:176`),
  `publicMode_collapses_to_universal` (`DesignatedVerifier.lean:186`) — the current single-universal-
  verifier behaviour **is exactly** `∀ V, DischargedFor V`, a **constant global section** of the
  verifier presheaf (the *constant sheaf* = the homogeneous special case,
  `SHEAF-LIT-networks.md §1`). `public_convinces_any_third_party` is "a constant global section
  restricts to a section over each party `W`."

What is missing: a global-sections functor `Γ`, no `H⁰ = ker δ⁰`. **The content is REAL; the name
"H⁰" is POETRY** (`SHEAF-GROUND-dregg.md §6`).

### 3.2 H¹ = the obstruction = fork / bug / version-skew / Byzantine disagreement

The obstruction is genuinely cohomological in the lit: Abramsky–Mansfield–Barbosa build a Čech
class `γ(s) ∈ Ȟ¹` that **vanishes if `s` extends to a global section** (`SHEAF-LIT-epistemic.md §3.2`,
**ESTABLISHED**). On a graph `H¹ = ker δ₁ / im δ₀` = the local-consistencies that fail to glue
(`SHEAF-LIT-networks.md §1`).

**The honest caveat dregg MUST inherit** (`SHEAF-LIT-epistemic.md §3.2,§4`): the cohomological
detector is **sufficient but not always necessary** — a nonzero class *certifies* a fork, but a zero
class does not by itself certify agreement (there exist contextual models whose first Čech class
vanishes). The clean iff is **"global section exists ⟺ non-contextual"**; the **"⟺ H¹ = 0"** upgrade
holds only in *good cases* (possibilistic / ℤ₂ / All-vs-Nothing). Moreover the task-sheaf paper's
*headline* impossibility test is **triviality of H⁰**, not non-vanishing of H¹
(`SHEAF-LIT-epistemic.md §4`, degree caveat) — both framings are correct and dual, but the defensible
statement is: **consensus = H⁰ non-trivial and contains the desired section; a fork = that section
does not exist, certified by a nonzero relative-H¹ class (sound, not always complete).** Do NOT
assert "fork = nonzero H¹" as an iff without the good-case hypothesis.

**dregg HAS witnessed *non-gluing* (REAL); it does NOT have an H¹ *object* (POETRY):**

- `¬ chainLinked [node0, badNode]` (`ProofForest.lean:293`) — locally-valid, unglueable;
- `designated_not_transferable` (`DesignatedVerifier.lean:206`) — a party that provably rejects;
- `Equivocator` / `honest_no_equivocation` (`CordialMiners.lean:144`, the discharge near `:588`) —
  a Byzantine party's incomparable blocks cannot glue (the consensus-layer analogue of the `¬
  chainLinked` witness).

What is missing: a Čech complex over the cover, a coboundary `δ⁰ : sections → overlaps`, an
"obstruction class is nonzero iff no global section." **The witnesses are REAL; the name "H¹ class"
is POETRY** (`SHEAF-GROUND-dregg.md §6`).

### 3.3 The dials this ties to — fill-height (Agreement) and filled-simplex (common knowledge)

- **Agreement dial = fill-height.** Consensus is "the local family glues" = the projection onto
  `ker L_𝓕` / H⁰ (`SHEAF-LIT-networks.md §2`). The degree-of-agreement is how much of the local data
  lies in the consensus subspace vs the disagreement complement (the Hodge split `Cᵏ = 𝓗ᵏ ⊕ im δ ⊕
  im δ*`) — a "distance-to-consensus" metric (Robinson's consistency radius,
  `SHEAF-LIT-networks.md §6`). In dregg this is the fill-height of the gluing: a fully-`Linked`
  forest is fully filled (H⁰); a `¬ chainLinked` gap is unfilled (the obstruction). ANALOGY (no
  Laplacian/consistency-radius object in dregg).
- **Common knowledge = filled simplex.** Common knowledge ⟺ 0-connectivity of the protocol complex
  (`SHEAF-LIT-epistemic.md §1`, **ESTABLISHED**): "consensus is impossible exactly because the
  protocol complex stays (0-)connected"; disconnection (bought by extra rounds) creates the room for
  a non-trivial global decision. A *filled* simplex (every sub-coalition shares the context) is the
  site-level statement that the parties' contexts overlap enough to support a global section. dregg's
  filled simplex is the balanced `Hyperedge` whose `legs_agree` (`Hyperedge.lean:111`) holds for all
  pairs; its proper-subobject obstruction `hyper_not_all_admissible` (`Hyperedge.lean:505`) is "not
  every face is fillable" — the precise sense in which common-knowledge fillability is *constrained*,
  not free.

**Establishment summary (per the lit verdict, `SHEAF-LIT-epistemic.md §7`):** "consensus = H⁰" is
**ESTABLISHED** (three literatures + the 2025 task-sheaf theorem). "Fork = H¹" is **ESTABLISHED in
contextuality and in the cellular `ker δ₁/im δ₀` sense; ANALOGY-trending-ESTABLISHED in distributed
computing** — claim it as a *sound obstruction detector*, not an iff. **Inside dregg both H⁰ and H¹
are POETRY** (no cohomology object exists) — only the *content* (gluing, non-gluing) is REAL.

---

## 4. HOW IT DEEPENS THE METATHEORY

The sheaf-of-verifiers is a **unification and generalization** of structure dregg already has, not a
new layer. Five existing seams are subsumed:

1. **The verify-seam becomes a verifier-SHEAF.** Today the verify/find seam is a single Galois
   connection: `predicate_witness_galois` (`Laws.lean:101`, PROVED) is the Birkhoff polarity of the
   *universal* `Discharged` relation (`Laws.lean:38`); `find` is the opaque untrusted search side
   (`search_sound` is a by-design contract, `Laws.lean:53`). The seam pins **the verifier as the
   TCB** — the very object the sheaf is a sheaf *of*. The deepening: replace the one universal
   `Discharged` by the indexed `DischargedFor V`, so each stalk carries its own polarity adjunction.
   (Promoting the per-`V` Galois structure is OPEN; the seam itself is REAL,
   `SHEAF-GROUND-dregg.md §3`.)
2. **Consensus becomes sheaf-gluing.** `cordial_agreement` (`CordialMiners.lean:336`) — a unique
   global section per wave — is the H⁰ content; the honest-ratifier-in-the-intersection is the
   overlap. Re-read, consensus is "the per-party local verdicts glue" rather than "a global oracle
   decides." (REAL as agreement; the cohomology naming is POETRY.)
3. **Attestation becomes a section.** A `ProofNode` + `StepProofValid` (`ProofForest.lean:81,98`) is
   a section of the verifier presheaf over a single open; `crossForest_attests`
   (`CrossCellForest.lean:278`) is the cross-cell wide-pullback section whose overlap is `Σδ = 0`.
   "An attestation" stops being a free-floating receipt and becomes "a local section that must glue
   on its overlaps."
4. **It makes 'no global oracle' first-class.** This is the conceptual core. The current
   single-universal-verifier is recovered as the **constant sheaf** — the degenerate
   everyone-shares-everything-perfectly case (`SHEAF-LIT-networks.md §1`). `DischargedFor V`
   (`DesignatedVerifier.lean:113`) and `publicMode_collapses_to_universal`
   (`DesignatedVerifier.lean:186`) already exhibit the universal verifier as the `∀ V` collapse, so
   "no global oracle" is not a wish — it is the *general* case of which dregg's current behaviour is
   the constant special case.
5. **It subsumes heterogeneous trust + version-skew + Byzantine in one structure.** Per §2: bugs,
   upgrades, heterogeneity, and lying are all *restriction-map data* in one non-constant sheaf
   (`SHEAF-LIT-networks.md §2`; Li–Lesani heterogeneous quorums, `SHEAF-LIT-epistemic.md §5`). The
   metatheory stops needing separate machinery for each.

---

## 5. THE LEAN SHAPE + THE MINIMAL REAL FIRST THEOREM

### 5.1 The theorem (the smallest buildable generalization)

Everything above is assembled around a **single** verifier: `StepProofValid` is *one* abstract `Prop`
per node — the *same* notion of "valid" at every node — and the consensus/`World` verdicts are
universal. The genuine generalization ember's idea asks for, and the smallest one that is **REAL and
buildable**, is to **index the proof-forest's validity by a per-node verifier and re-prove the
gluing** (`SHEAF-GROUND-dregg.md §7`; `SHEAF-LIT-networks.md §5.3`; `SHEAF-LIT-epistemic.md §7`).

**`proofForest_sheaf_sound` (OPEN → REAL+buildable):**

> *Given a sheaf of verifiers `Vᵢ` over the proof-forest's happened-before site (each `ProofNode` `i`
> checked by **its own** verifier via `DischargedFor Vᵢ (stmtOf nᵢ) (proofOf nᵢ)` — heterogeneous
> software / upgrades / bugs all live in the choice of `Vᵢ`), IF the local verdicts agree on overlaps
> (`Linked`, unchanged — it is verifier-independent, about commitments not about who checks) AND the
> per-node verifiers are compatible on the shared overlap surface (`Vᵢ` and `Vⱼ`'s verdicts on the
> shared commitment agree), THEN there is a sound global verified history (`fullProofForestInv`) — a
> global section.*

Concretely: take `proofForest_sound` (`ProofForest.lean:177`) and replace the uniform hypothesis (P)
`∀ n ∈ pf.nodes, n.StepProofValid` by the **heterogeneous, verifier-indexed**
`∀ i, DischargedFor Vᵢ (stmtOf nᵢ) (proofOf nᵢ)`, adding an explicit **overlap-compatibility**
hypothesis on the `Vᵢ`. The conclusion is unchanged; the new content is the **sheaf condition for a
*sheaf of verifiers* rather than a sheaf with one verifier.** Per Felber et al. the right global
object is the **colimit `colim_p F_p`** and the sharpest target is *"a global section of `colim_p F_p`
exists iff each `F_p` admits one and they agree on overlaps"* (`SHEAF-LIT-epistemic.md §4,§7`).

### 5.2 Why it is REAL-buildable NOW (not poetry)

All inputs are term-proved (`SHEAF-GROUND-dregg.md §7.2`):

- the per-party verdict: `DischargedFor` (`DesignatedVerifier.lean:113`);
- the overlap relation: `Linked` (`ProofForest.lean:148`) — verifier-independent, reused unchanged;
- the gluing spine: `proofForest_sound` (`ProofForest.lean:177`), axiom-clean (`:223`);
- the **backward-compat / non-vacuity check**: `public_convinces_any_third_party`
  (`DesignatedVerifier.lean:176`) and `publicMode_collapses_to_universal` (`:186`) supply "uniform
  verifier = constant section," so the new theorem **specializes back** to `proofForest_sound` when
  all `Vᵢ` are equal;
- the **obstruction made into a real failed hypothesis**: a software bug / version-skew is a verifier
  `Vᵢ` whose verdict disagrees with `Vⱼ` on the overlap → the compatibility hypothesis FAILS → no
  global section — witnessed exactly as `designated_not_transferable` (`DesignatedVerifier.lean:206`)
  already witnesses a disagreeing verifier.

It respects the proven constraints: the **fibration-over-bindings** (covers are bindings, not free
fillers — `hyper_not_all_admissible`, `Hyperedge.lean:505`) and the **two overlap laws** (`new = old`
intra-cell, `Σδ = 0` cross-cell via `crossForest_attests`, `CrossCellForest.lean:278`). This is the
gluing of an **existing term-proved theorem**, re-proved over a verifier-indexed fibre — the line
past which "sheaf of verifiers" earns its keep.

### 5.3 What is REAL-buildable-now vs ASPIRATIONAL

| Item | Status | Receipt |
|---|---|---|
| Proof-forest = finite SHEAF-GLUING (valid + agree-on-overlap ⟹ global) | **REAL** | `proofForest_sound` `ProofForest.lean:177`, axiom-clean `:223` |
| The sheaf condition BITES (valid-but-unglueable witnessed) | **REAL** | `¬ chainLinked [node0, badNode]` `ProofForest.lean:293` |
| Cross-cell overlap = `Σδ = 0` (a second cover/restriction law) | **REAL** | `crossForest_attests` `CrossCellForest.lean:278` |
| Verifier-INDEXED verdict = the per-party stalk | **REAL** | `DischargedFor` `DesignatedVerifier.lean:113` |
| Heterogeneous, non-gluing local verdicts EXIST | **REAL** | `designated_not_transferable` `:206`, `dial_endpoints_distinct` `:346` |
| Uniform verifier = constant global section (the `∀V` collapse) | **REAL** | `public_convinces_any_third_party` `:176`, `publicMode_collapses_to_universal` `:186` |
| Consensus = unique global section per wave (the H⁰ content) | **REAL** | `cordial_agreement` `CordialMiners.lean:336`, `cordial_agreement_from_lace` `:484` |
| Hyperedge = the simplicial who-shares-context SITE | **REAL** | `Hyperedge` `:80`, `legs_agree` `:111`, `hyper_not_all_admissible` `:505` |
| Verify (not find) is the adjoint side = the verifier-as-TCB | **REAL** | `predicate_witness_galois` `Laws.lean:101` |
| `proofForest_sheaf_sound` (soundness over a verifier-SHEAF) | **OPEN → REAL+buildable (the first theorem)** | all inputs term-proved; §5.1–5.2 |
| Functorial restriction ρ with identities/composition; a `Presheaf` object | **PARTIAL / OPEN** | dregg has the agreement *equation*, not ρ as a functor (no `Presheaf` in `Dregg2/`) |
| H⁰ / H¹ as cohomology OBJECTS (Čech complex, δ⁰, classes) | **POETRY / ASPIRATIONAL** | no complex, no coboundary, no `H` object anywhere; §3 names the gap |
| Sheaf Laplacian `L_𝓕` / consensus diffusion / consistency-radius | **ANALOGY (lit-only)** | `SHEAF-LIT-networks.md §2`; no Laplacian object in dregg |
| Byzantine-tolerance = a Cheeger gap on `L_𝓕` | **CONJECTURE — do not state as theorem** | `SHEAF-LIT-networks.md §5` (preliminary even in Hansen–Ghrist) |
| Upgrade/version axis backward-compat as a theorem | **OPEN** | expressible once `Vᵢ` varies; theorem modeled on `Upgrade.lean` `no_downgrade`, `SHEAF-GROUND-dregg.md §7.3` |

### 5.4 The disciplined build order

1. **`proofForest_sheaf_sound`** (§5.1) — index the fibre by `Vᵢ`, add overlap-compatibility,
   re-prove. Specializes back to `proofForest_sound` via the constant-verifier collapse. *This is the
   one artifact that makes the claim load-bearing.*
2. **The Čech 2-term complex** (only after step 1): `C⁰ = ∏_opens (verified sections)`, `C¹ = ∏_overlaps
   (agreement residuals)`, `δ⁰ s = (ρ_a s_a − ρ_b s_b)_overlaps`. Then `ker δ⁰` = `Linked` families =
   §1.4's hypothesis, and "`δ⁰ s = 0 ⟹ ∃! global section`" is *exactly* `proofForest_sheaf_sound`
   re-read; `H¹ = coker δ⁰ ≠ 0` literally classifies the fork/bug/skew (`SHEAF-GROUND-dregg.md §6`).
   Only here does "cohomology of consensus" earn the word — and only as a *sound* detector (§3.2
   caveat).
3. **Functorial ρ / Grothendieck topology / colimit `colim_p F_p`** — the genuine `Presheaf` object
   with ρ-coherence; promote `Linked` and `public_convinces_any_third_party` to a functor. DECORATIVE
   until step 1, by the discipline.

**Discipline (the kernel-exposes-gaps rule).** Ship the gluing as a gluing (REAL); label the
cohomology as the next theorem (OPEN). The sheaf vocabulary must generalize the term-proved
proof-forest gluing, never paper over the missing Čech complex. Calling today's gluing "cohomology"
would let vocabulary substitute for the absent coboundary — exactly what this doc refuses.

---

## 6. ONE-PARAGRAPH SYNTHESIS

A metatheory of distributed systems with **no global oracle** organizes per-party verifiers as a
**(pre)sheaf 𝒱 over the simplicial-epistemic site** (vertices = local states, simplices = compatible
tuples, indistinguishability = shared faces — `SHEAF-LIT-epistemic.md §1`, ESTABLISHED): the **stalk**
at a party is its `VerifierKernel` (`DischargedFor`, `DesignatedVerifier.lean:113`, REAL), the
**restriction maps** are how a verdict restricts to a shared overlap (`a.newCommit = b.oldCommit`
intra-cell, `Σδ = 0` cross-cell — REAL as the agreement equation), and the **gluing condition** says
compatible local verdicts glue to a global section (`proofForest_sound`, `ProofForest.lean:177`,
REAL, axiom-clean — *and the sheaf condition bites*, `¬ chainLinked [node0, badNode]`, `:293`).
**Software bugs, upgrades, and heterogeneity are one phenomenon** — different sections distinguished
by their restriction-map data, with overlap-disagreement = failure to glue (the worked micro-example
is the term-proved `badNode`; heterogeneity is the term-proved `designated_not_transferable`). The
**cohomology is the invariant**: **H⁰ = consensus / common knowledge** (ESTABLISHED across three
literatures + the 2025 task-sheaf theorem; REAL as *content* in `cordial_agreement`,
`CordialMiners.lean:336`, but POETRY as an *object* in dregg), **H¹ = the obstruction** (forks /
bugs / skew / Byzantine — ESTABLISHED-as-a-sound-but-not-complete-detector in the lit; REAL as
*witnessed non-gluing* but POETRY as an *object* in dregg). The structure **deepens the metatheory**
by turning the verify-seam into a verifier-sheaf, consensus into gluing, attestation into a section,
and "no global oracle" into the *general* case of which today's single-universal-verifier is the
**constant-sheaf** special case (`publicMode_collapses_to_universal`, `:186`). The **one honest,
buildable next theorem** — the line past which the whole claim stops being suggestive — is
**`proofForest_sheaf_sound`: proof-forest soundness GENERALIZED over a per-node verifier-sheaf
(heterogeneous local verdicts agreeing on the linking overlaps ⟹ a sound glued global verdict)**,
buildable today from term-proved pieces; everything beyond (the Čech `H⁰`/`H¹` objects, the
functorial presheaf, the Laplacian/Cheeger spectral story) stays explicitly flagged ANALOGY/OPEN/
POETRY until it term-proves.

( ⌐■_■ ) the egg grows many eyes; the sheaf is how they learn to agree — and how it learns when they
can't.

---

## 7. VERDICT — adversarial READ-ONLY audit (2026-05-31)

Default-skeptical re-derivation against the actual Lean. Method: read `Exec/ProofForest.lean`,
`Authority/DesignatedVerifier.lean`, `Proof/CordialMiners.lean`, `Exec/CrossCellForest.lean`,
`Hyperedge.lean`, `Laws.lean`; grep `Dregg2/` for sheaf/cohomology vocabulary; probe the pinned
mathlib (`leanprover/lean4:v4.30.0`, local `mathlib4`) for the cohomology machinery; compile
`ProofForest.lean` standalone (clean, no axiom violation). **Every `file:line` in §§1–5 verified
exact.** Every REAL anchor is a term-proved theorem that I confirmed compiles and is non-vacuous
(`fullForestInv` = the four real conjuncts Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance, NOT
`True`; the `badNode` non-gluing genuinely fails `1 = 99`; the reference DV-kernel genuinely
separates `v0` from `vOther`). **No claim in §§1–5 was found overstated.** The doc's own
REAL/ESTABLISHED/ANALOGY/POETRY discipline is honest and holds. The verdict below re-tags in this
audit's vocabulary (**REAL / DECORATIVE / ASPIRATIONAL**) and answers the three hardest questions.

### 7.1 The table

| Structural claim | Tag | Adversarial note (what it proves / what it would have to prove) |
|---|---|---|
| Proof-forest = finite gluing: (per-node valid) ∧ (agree-on-overlap `Linked`) ⟹ global `StepInv` | **REAL** | `proofForest_sound` `ProofForest.lean:177`, compiles clean, `#assert_axioms` whitelisted `:223`. `fullForestInv` is the 4 real conjuncts (`TurnForest.lean:282-283`). |
| The gluing BITES (locally-valid-but-unglueable witnessed) | **REAL** | `¬ chainLinked [node0, badNode]` `:293`; `StepProofValid := True` on both nodes yet `1 ≠ 99` at the overlap. Genuine teeth. |
| Cross-cell overlap = a *second* restriction law `Σδ = 0` | **REAL** | `crossForest_attests` `CrossCellForest.lean:278`. The site genuinely has two cover-kinds. |
| Verifier-INDEXED verdict = the per-party stalk | **REAL** | `DischargedFor` `DesignatedVerifier.lean:113`; `verifyFor : Verifier → … → Bool` `:89`. The one place the verdict depends on *who checks*. |
| Heterogeneous, non-gluing local verdicts EXIST | **REAL** | `designated_not_transferable` `:206`, `dial_endpoints_distinct` `:346` over a concrete 2-verifier kernel (`v0` accepts, `vOther` provably rejects). Non-vacuous. |
| Uniform verifier = constant global section (the `∀V` collapse) | **REAL** | `public_convinces_any_third_party` `:176`, `publicMode_collapses_to_universal` `:186` (`Iff.rfl`). The current single-verifier IS the constant-sheaf special case. |
| Consensus = unique global section per wave (the H⁰ *content*) | **REAL** | `cordial_agreement` `:336`, `cordial_agreement_from_lace` `:484`; quorum read off the real lace (`superRatifiedFromLace` `:232`). |
| Hyperedge = the simplicial who-shares-context SITE | **REAL** (as wide-pullback) | `Hyperedge` `:80`, `legs_agree` `:111`, `hyper_not_all_admissible` `:505` (proper subobject — fibration-over-bindings, not free complex). |
| Verify (not find) is the adjoint side = verifier-as-TCB | **REAL** | `predicate_witness_galois` `Laws.lean:101`. `find`/`search_sound` is a by-design `sorry` contract (`:60`), correctly fenced. |
| **`proofForest_sheaf_sound`** (soundness over a per-node verifier-sheaf) | **REAL + buildable, NOT YET BUILT** | All inputs term-proved; the one artifact that makes the claim load-bearing. See §7.4 — it is genuinely non-vacuous. |
| "Restriction map" as a *functorial* ρ (with `ρ_id = id`, `ρ∘ρ`); a `Presheaf` object | **DECORATIVE** until built | dregg has the agreement *equation* `ρ_a(a)=ρ_b(b)`, NOT a functor. Grep-confirmed: `sheaf`/`presheaf` appear **0 times** in `Dregg2/`. Would have to prove the equalizer/iso onto compatible families. |
| H⁰ / H¹ as cohomology *objects* (Čech complex, δ⁰, classes) | **DECORATIVE → ASPIRATIONAL** | No complex, no coboundary, no `H` object in `Dregg2/` (grep-empty for `cohomolog`/`Čech`/`coboundary`). The doc is *correct* to call these POETRY. Becomes ASPIRATIONAL once you try to *build* them (§7.3). |
| Sheaf Laplacian `L_𝓕` / consensus diffusion / consistency-radius | **DECORATIVE (lit-only)** | No Laplacian object in dregg; pure ANALOGY. The doc flags this correctly (§1.5). |
| "Byzantine-tolerance = a Cheeger gap on `L_𝓕`" | **DECORATIVE / CONJECTURE** | Not stated as a theorem anywhere — correctly fenced (§5.3). Would need a spectral object dregg lacks. |
| "H¹ = fork" as an **iff** | **DECORATIVE (overclaim if asserted as iff)** | The lit itself (`SHEAF-LIT-epistemic.md §3.2`) proves the cohomological detector is **sound, not complete**. The doc *correctly* refuses the iff. Asserting it would be the one place sheaf-talk overclaims; the doc does not. |

### 7.2 (a) Is the proof-forest ACTUALLY a sheaf, or only a gluing/presheaf?

**Only a gluing — and the doc says so. It is neither a presheaf nor a sheaf as a constructed
object.** A presheaf needs a functor `𝓕 : Open^op → Set` with `ρ_id = id` and `ρ∘ρ` coherence; a
sheaf adds the gluing axiom (existence) **and the separation axiom** (uniqueness: agreeing
restrictions force equal sections). What dregg has:

- **Gluing (existence), REAL.** `proofForest_sound`: a compatible family (valid + `Linked`) yields a
  global section (`fullForestInv`). Term-proved.
- **Separation/uniqueness, PARTIAL-at-best.** There is *no* theorem "two global sections restricting
  equally on all overlaps are equal." It is plausibly recoverable (the witness `execForest s f` is a
  deterministic function, so the post-state is determined), but it is **not stated**. A genuine sheaf
  needs it; dregg has not proved it.
- **The functor itself, ABSENT.** `Linked` is a *relation* (`a.newCommit = b.oldCommit`), not a
  restriction *map*. There is no `𝓕`, no `Open` category, no `ρ`. Grep: zero `sheaf`/`presheaf` in
  `Dregg2/`.

**What is missing to make it a genuine sheaf of *different per-node* verifiers** (the harder half):
the current gluing uses **one** notion of valid (`StepProofValid`, the same abstract `Prop` at every
node). The per-node verifier index (`DischargedFor Vᵢ`) **exists** but is **not yet wired into the
proof-forest** — `ProofNode` carries `StepProofValid : Prop`, not `DischargedFor Vᵢ (stmtOf n)
(proofOf n)`. So today's gluing is the *constant sheaf* (homogeneous). To be a sheaf of *different*
verifiers you must (i) replace the fibre by the `V`-indexed verdict, (ii) add the overlap-compatibility
hypothesis on `Vᵢ, Vⱼ`, (iii) re-prove gluing — i.e. exactly `proofForest_sheaf_sound` (§5.1, still
**unbuilt**), and ideally (iv) the separation axiom. **Honest answer: a finite gluing of a constant
fibre, packaged with the *ingredients* of a verifier-sheaf, but not yet assembled into one.**

### 7.3 (b) Does "H¹ = fork" cash out as a theorem? Does mathlib even have the machinery?

**No, it does not cash out — it is analogy until someone builds the cohomology over the actual
party-complex; and mathlib's available machinery is the *wrong shape* for the doc's stated plan.**
Two distinct findings:

1. **Inside dregg: pure analogy.** There is no Čech complex, no `δ⁰`, no `H¹` object, no
   "obstruction-class ≠ 0 ⟺ no global section." There are *witnessed non-gluings* (`¬ chainLinked`,
   `designated_not_transferable`, `Equivocator`) — REAL as witnesses, but a *witness that a specific
   family fails to glue* is not *a cohomology class classifying all such failures*. The doc's "H¹ =
   POETRY inside dregg" is exactly right.

2. **Mathlib: it has cohomology, but NOT the cellular-sheaf kind the doc's §5.2 plan needs.** The
   pinned mathlib HAS `CategoryTheory/Sites/SheafCohomology/{Basic,Cech,MayerVietoris}.lean` and full
   `Algebra/Homology`. **But** `Sheaf.H F n` is **derived-functor (Ext-group) cohomology** of an
   *abelian* sheaf on a site `(C, J)` with a **Grothendieck topology**, valued in `AddCommGrpCat`,
   requiring `HasSheafify` and `HasExt` (enough injectives) — the heavy abstract topos machine. There
   is **no `cellular sheaf`** in mathlib (grep-empty), and the only `SimplicialComplex` is the
   geometric/`Analysis.Convex` one, not the Hansen–Ghrist cellular-sheaf-on-a-poset object. The doc's
   §5.2 plan is the *lightweight* finite linear-algebra `H⁰ = ker δ⁰`, `H¹ = coker δ⁰` over a 2-term
   complex — which is the **right** plan, but it would be **hand-built on `Algebra/Homology`**, NOT a
   reuse of `Sheaf.H`. Reusing mathlib's `Sheaf.H` would require equipping the proof-forest poset with
   a Grothendieck topology, an abelian-group-valued sheaf, and enough-injectives — disproportionate
   and arguably the wrong invariant for a finite party-complex. **So "H¹ = fork" is ASPIRATIONAL: it
   needs unbuilt machinery, and the cheapest path deliberately avoids mathlib's existing
   cohomology.** The doc's §5.4-step-2 plan (hand-built Čech 2-term complex) is the correct, honest
   route; it is simply not started.

### 7.4 (c) Is `proofForest_sheaf_sound` buildable NOW, and would it be NON-VACUOUS?

**Yes, buildable now; and yes, genuinely non-vacuous — provided the overlap-compatibility hypothesis
is stated with teeth and not as a tautology.** Audit of the build:

- **Inputs all present & compiling.** `DischargedFor` `:113`; `Linked` `:148` (verifier-independent,
  reused verbatim); the gluing spine `proofForest_sound` `:177` (axiom-clean); the constant-collapse
  `publicMode_collapses_to_universal` `:186` so it specializes back when all `Vᵢ` equal (backward-compat /
  non-vacuity check); the disagreeing-verifier witness `designated_not_transferable` `:206`.
- **Non-vacuity TEETH — the one trap.** The theorem is non-vacuous **iff the overlap-compatibility
  hypothesis can genuinely FAIL** for a buggy/version-skewed `Vᵢ`. The reference DV-kernel already
  proves this: `dial_endpoints_distinct` `:346` exhibits a concrete `(stmt, proof)` where `v0` accepts
  and `vOther` rejects — i.e. two verifiers that **disagree on the same surface**. Feed `vOther` as a
  node's verifier and the compatibility hypothesis is **false**, so the global section is **not**
  derivable — the buggy section is genuinely rejected. This is the discharge: a disagreeing
  verifier-section is rejected by a *real failed hypothesis*, witnessed by an *already-proved*
  separation, not assumed.
- **The discipline trap to avoid when building it.** The compatibility hypothesis must be the
  *substantive* "`Vᵢ` and `Vⱼ` return the same verdict on the shared commitment surface," NOT the
  vacuous "`Vᵢ = Vⱼ`" (which collapses straight back to the constant sheaf and proves nothing new) and
  NOT "the conclusion already holds" (circular). With the substantive hypothesis it is a genuine
  generalization; with either degenerate one it is DECORATIVE. The pieces to state the substantive
  version exist. **Buildable, non-vacuous, and the single artifact that earns the title.**

### 7.5 Bottom line — genuine deepening, or beautiful reframing?

**Both, honestly, and the doc itself draws the line correctly. It is a genuine foundational
deepening of *one* axis — "no global oracle" — and a beautiful-but-not-yet-cashed reframing of the
rest.**

- **Genuine deepening (REAL, today):** the verifier *index* is real (`DischargedFor`), heterogeneous
  non-gluing verdicts are a *proved phenomenon* (`designated_not_transferable`,
  `dial_endpoints_distinct`), the gluing is term-proved and *bites* (`proofForest_sound` +
  `¬ chainLinked`), and the current single-universal-verifier is *correctly* recovered as the
  constant-sheaf special case. That is more than vocabulary: it is the conceptual move "the global
  oracle is the degenerate case" backed by compiling theorems. This is real.
- **Beautiful reframing (not yet load-bearing):** the *sheaf* (functorial ρ, separation axiom,
  presheaf object) and the *cohomology* (H⁰/H¹ as objects, the Čech complex, "H¹ = fork") are, inside
  dregg, **vocabulary naming theorems that are not yet proved.** The doc is scrupulously honest about
  this — it tags them POETRY/ASPIRATIONAL and refuses the "H¹ = fork" iff. The reframing is
  *well-aimed* (three published literatures + the 2025 task-sheaf theorem make it citable in the
  lit), but it has not deepened *dregg's* metatheory until the Lean exists.
- **The hinge.** Everything turns on **one unbuilt theorem**: `proofForest_sheaf_sound`. Until it is
  in the Lean, "sheaf of verifiers" is REAL-as-ingredients + DECORATIVE-as-assembled-structure. Once
  it is in — and it is buildable now, non-vacuously (§7.4) — the reframing becomes a deepening on the
  proof-forest axis too. **The cohomology stays ASPIRATIONAL beyond that, and rightly labeled so.**

**The single most-buildable real first theorem (unchanged from §5.1, audit-confirmed buildable &
non-vacuous):**

> **`proofForest_sheaf_sound`** — generalize `proofForest_sound` (`ProofForest.lean:177`) by replacing
> the uniform `StepProofValid` fibre with the per-node verifier-indexed verdict
> `DischargedFor Vᵢ (stmtOf nᵢ) (proofOf nᵢ)`, keep `Linked` (verifier-independent), add a
> **substantive** overlap-compatibility hypothesis on the `Vᵢ` (same verdict on the shared
> commitment surface — *not* `Vᵢ = Vⱼ`), and re-prove `fullProofForestInv`. It specializes back to
> `proofForest_sound` via `publicMode_collapses_to_universal` (`:186`), and its non-vacuity teeth are
> already proved (`dial_endpoints_distinct` `:346` exhibits a disagreeing verifier whose section is
> genuinely rejected). All inputs term-proved; this is the line past which the claim stops being
> suggestive.

**Discipline upheld.** The doc never lets sheaf vocabulary paper over a missing theorem: it ships the
gluing as a gluing (REAL), names the cohomology as the next theorem (OPEN), and refuses the unsound
"H¹ = fork" iff. This audit found nothing to walk back and one thing to emphasize: mathlib's existing
`Sheaf.H` is the *wrong* tool for the cohomology step — the honest path is the hand-built finite
2-term complex the doc already proposes, not a reuse of the topos machine.

( ◕‿◕ ) the egg's many eyes are real; the sheaf that binds them is one theorem from real — and the
cohomology, two. honest count, honest egg.
