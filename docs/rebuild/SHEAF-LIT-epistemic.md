# SHEAF-LIT — the simplicial-epistemic ↔ sheaf bridge, cohomology as agreement-obstruction, and heterogeneous trust

> **What this is.** A READ-ONLY literature distillation answering one question for the
> "sheaf of verifiers over the parties" idea: **is "common knowledge = a global section (H⁰)
> / fork = an H¹ obstruction" an established mathematical correspondence, or a fresh
> analogy?** Scope: the simplicial-epistemic-logic line (Goubault–Kniazev–Ledent–Rajsbaum),
> sheaves *on* simplicial / cellular complexes (Curry, Hansen–Ghrist), the sheaf-theoretic
> contextuality canon (Abramsky–Brandenburger; Abramsky–Mansfield–Barbosa), the brand-new
> sheaf-of-tasks bridge (Felber–Hummes Flores–Rincon-Galeana 2025), and heterogeneous quorum
> systems (Li–Lesani). Every claim is tagged:
>
> - **ESTABLISHED** — a published theorem (cited at `pdfs/<file>` + arXiv/DOI) says exactly this.
> - **ANALOGY** — a real, well-motivated correspondence that is *suggestive* but is not (yet)
>   cashed out as a theorem in the form ember wants for dregg.
> - **dregg-ANCHOR** — what is already term-proved on the dregg side, cited at `file:line`.
>
> The discipline (per `FOUNDATIONS-*.md`): do **not** let sheaf vocabulary paper over a missing
> theorem. Separate the real-buildable core from cohomology poetry.

**Papers fetched to `pdfs/` for this review** (all validated `head -c 4 == %PDF`):
- `pdfs/sheaf-tasks-distributed-2503.02556.pdf` — **Felber, Hummes Flores, Rincon-Galeana**,
  *A Sheaf-Theoretic Characterization of Tasks in Distributed Systems*, arXiv:2503.02556v2
  (2025), DISC-2024 brief-announcement full version. **THE direct bridge.**
- `pdfs/sheaf-nonlocality-contextuality-abramsky-brandenburger-1102.0264.pdf` — **Abramsky & Brandenburger**,
  *The Sheaf-Theoretic Structure of Non-Locality and Contextuality*, New J. Phys. 13 (2011)
  113036, arXiv:1102.0264. **The established "compatibility = sheaf-condition / contextuality
  = no global section" theorem.**
- `pdfs/sheaf-cohomology-nonlocality-1111.3620.pdf` — **Abramsky, Mansfield & Barbosa**,
  *The Cohomology of Non-Locality and Contextuality*, arXiv:1111.3620 (QPL 2011). **The
  established "obstruction = a Čech cohomology class in Ȟ¹" theorem.**
- `pdfs/sheaf-spectral-cellular-ghrist-hansen-1808.01513.pdf` — **Hansen & Ghrist**, *Toward a Spectral
  Theory of Cellular Sheaves*, J. Appl. Comput. Topol. (2019), arXiv:1808.01513. **The
  algebraic spine: H⁰ ≅ Γ(X;F) = global sections = ker δ = sheaf-Laplacian kernel.**
- `pdfs/sheaf-networks-robinson-1308.4621.pdf` — **Robinson**, *Understanding networks and their
  behaviors using sheaf theory*, arXiv:1308.4621. (Consistency-radius / data-fusion framing.)

**Already in the library, re-read in full:**
- `pdfs/zotero-simplicial-epistemic-logic-faulty-agents.pdf` — **Goubault, Kniazev, Ledent,
  Rajsbaum**, *Simplicial Models for the Epistemic Logic of Faulty Agents*, arXiv:2311.01351v3.
- `pdfs/zotero-reconfigurable-heterogeneous-quorum-systems.pdf` — **Li & Lesani**,
  *Reconfigurable Heterogeneous Quorum Systems*, DISC 2024, arXiv:2304.02156v2.

---

## 0. The one-paragraph verdict

The chain ember wants has **two ESTABLISHED links and one ANALOGY link that is now mostly
closed**. (1) The simplicial-epistemic equivalence is ESTABLISHED: there is a *categorical
equivalence* between proper S5ₙ epistemic (Kripke) frames and pure chromatic simplicial
complexes — **vertices = local states / perspectives, simplices (facets) = compatible global
states / worlds** — and **common knowledge ⟺ 0-dimensional connectivity** of that complex
(Goubault et al., generalizing Halpern–Moses). (2) The sheaf-cohomology-of-agreement link is
ESTABLISHED *in the contextuality setting*: Abramsky–Brandenburger prove that **compatibility
on overlaps is exactly the sheaf condition**, that **non-contextuality ⟺ a global section
exists**, and Abramsky–Mansfield–Barbosa prove the **obstruction to gluing is a Čech
cohomology class in Ȟ¹ that vanishes when a global section exists** (non-vanishing is
*sufficient*, and in "good"/possibilistic cases necessary, for the obstruction). (3) The link
ember actually needs — *distributed-systems agreement* expressed as a sheaf whose **global
section = a consistent global decision and whose cohomology = the obstruction** — was, until
~early 2025, the ANALOGY. It is now **largely cashed out as a theorem** by Felber–Hummes
Flores–Rincon-Galeana (2025): they build a **task sheaf** over the indistinguishability
("who-shares-context") complex and prove **task solvability ⟺ existence of a global section**,
with the section space computed as **H⁰ = ker(coboundary)** and impossibility read off from a
trivial section space. So "consensus = a global section" is now **ESTABLISHED** (2025, single
paper, model-independent); "fork/disagreement = H¹ class" is **ESTABLISHED in contextuality and
ANALOGY-trending-ESTABLISHED in distributed computing** (the obstruction is real and
cohomological; whether the precise degree is H¹ depends on the encoding — see §4 caveat). The
honest line for dregg: the **proof-forest-as-sheaf-gluing is REAL** (dregg-ANCHOR, term-proved),
the **per-party verifier = a sheaf over the parties is REAL and matches the literature's
per-process sheaf construction exactly**, and the **cohomology-of-consensus is now a citable
theorem, not poetry** — provided dregg states the generalized theorem it implies (§7) rather
than gesturing at the vocabulary.

---

## 1. The simplicial-epistemic layer (Goubault–Kniazev–Ledent–Rajsbaum) `[ESTABLISHED]`

`pdfs/zotero-simplicial-epistemic-logic-faulty-agents.pdf` (arXiv:2311.01351v3).

**The objects.** Move from *worlds* (global states) to *perspectives* (local states). Per the
1993 Herlihy–Shavit insight, "what exists in a distributed system is only the local states of
the agents." A **chromatic simplicial complex** ⟨V, S, χ⟩ (Def. 1, paper p.6) has:
- **vertices V = local states**, each *colored* χ by the agent that owns it;
- **simplices S = compatible tuples of local states**, i.e. a set of local states that can
  *coexist in one global state*;
- **facets (maximal simplices) = global states / possible worlds.**

**The equivalence (the load-bearing theorem).** *Theorem 4 (p.7, citing the 2021
Goubault–Ledent–Rajsbaum original):*

> The category of pure chromatic simplicial complexes `SimCpxᴬ_pure` is **equivalent** to the
> category of proper epistemic (S5ₙ) frames `EFrameᴬ_proper`.

A world `w` of the Kripke frame ↔ a facet (top simplex) of the complex; **`w ∼_a w′`
(agent `a` cannot distinguish the two worlds) ↔ the two facets share the vertex colored `a`**
(p.7, Example 5). This is a genuine equivalence of categories, not a slogan: indistinguishability
*is* shared faces. The "impure" extension of this paper drops the all-agents-present assumption
so that worlds can have varying dimension — modeling **crash failures** (a dead agent = a missing
vertex) — and adds the **distributed-knowledge operator** `D_B φ` whose semantics is "move from
simplex to simplex along the shared face of the `k` vertices colored by `B`" (p.2, §3). This is
the **simplicial site = who-shares-context** structure ember names.

**Common knowledge ⟺ connectivity (the crux for cohomology).** The paper states the classical
fact precisely (p.2): *"The solvability of some tasks such as consensus depends only on the
one-dimensional (graph) connectivity of the Kripke structure of global states, and hence is
intimately related to common knowledge."* The impossibility argument (§7.3, pp.34–35) is exactly
this: in the one-round, one-crash synchronous-broadcast protocol complex, the facet labeled
`{input0_a, input0_b, input0_c}` is **connected** (through indistinguishability edges) to the
facet labeled `{input1_a, ...}`. Because they are connected, **no agent group can reach common
knowledge `C_A` of the input value**, and the consensus obstruction formula `φ₀ ∨ φ₁` cannot be
satisfied. **Consensus is impossible exactly because the protocol complex stays (0-)connected.**

> **Read this as cohomology-in-disguise.** "0-connected ⇒ no common knowledge ⇒ no consensus" is
> the **H⁰ statement** for the constant/locally-constant sheaf: on a connected complex the only
> globally-constant section is the constant one, so you cannot glue together a decision that
> separates the two input components. A **disconnection** of the protocol complex (which extra
> rounds buy you) is what creates the room for a non-trivial global decision. This is the
> precise sense in which the Goubault line is the **H⁰/connectivity half** of the
> consensus↔cohomology story (the *agreement = global section* half). The Felber et al. paper
> (§4) supplies the *sheaf* that makes this a literal H⁰.

**dregg-ANCHOR.** This is the cited epistemic-logic paper behind dregg's simplicial reading.
`FOUNDATIONS-limits-tensor-simplicial.md` is explicit that the dregg `Hyperedge`/`JointTurn`
**wide-pullback** is the *binary/N-ary compatible-tuple* (= a simplex's compatibility datum):
the apex `tid` + `legs_agree` is the cone-collapse (`Hyperedge.lean:111`), and the
proper-subobject obstruction `hyper_not_all_admissible` (`Hyperedge.lean:505`) is the statement
*"not every product-tuple is a simplex"* — i.e. the simplicial complex is a **proper** subcomplex
of the full join. **REAL as construction; DECORATIVE as a full simplicial object** (no proved
face/degeneracy layer; the simplicial reading is the analogy tied to *this* paper).

---

## 2. Sheaves ON simplicial / cellular complexes (Curry; Hansen–Ghrist) `[ESTABLISHED]`

`pdfs/sheaf-spectral-cellular-ghrist-hansen-1808.01513.pdf` (arXiv:1808.01513).

A **cellular sheaf** `F` on a cell complex `X` (Curry 2014; the computable combinatorial
counterpart of a sheaf on a space) assigns:
- a **stalk** `F(σ)` (a vector space / set / module — the *data per cell*) to each cell `σ`;
- a **restriction map** `F(σ ⊴ τ): F(σ) → F(τ)` for each incidence `σ ⊴ τ`.

This is **exactly "data-per-perspective with gluing"**: stalk over a vertex = a party's local
data; restriction along a shared face = how that data restricts to a shared sub-context.

**The algebraic spine (the part to quote when someone says "H⁰ = consensus").** Hansen–Ghrist,
Def. 2.5 and the cohomology construction (paper pp.7–10):
- A **global section** `x` of `F` is an assignment `x_σ ∈ F(σ)` per cell that is *consistent*:
  it agrees under every restriction map. `Γ(X;F)` is the space of global sections.
- The **coboundary** `δ` measures disagreement across incidences; sections are `ker δ`.
- **`H⁰(X;F) ≅ Γ(X;F)`** — *"the 0-th cohomology is naturally isomorphic to the space of global
  sections"* (paper p.10, around l.325). In the weighted/Hilbert setting,
  **`Γ(X;F) = ker δ = ker Δ₀` = the harmonic 0-cochains = kernel of the sheaf Laplacian**
  (pp.13–17, §3.2.1).
- **`H¹(X;F)`** is `ker δ₁ / im δ₀` — the space of **local-consistencies that fail to glue into
  global ones**: the obstructions. The long exact sequence of a pair
  `0 → H⁰(X,A;F) → H⁰(X;F) → H⁰(A;F) → H¹(X,A;F) → …` (paper l.342) is the standard machinery
  that turns "a local section over `A` that does not extend" into a **connecting-homomorphism
  image in H¹**.

**Why this is the right structure for ember's idea.** The sheaf Laplacian `Δ₀ = δᵀδ` is *the*
operator whose **heat flow drives the network to a global section (= to agreement)** and whose
**kernel is the consensus space**; Hansen–Ghrist's program (and Hansen's distributed-optimization
work) is literally "**sheaves generalize the graph Laplacian of consensus dynamics from
'everyone agrees on one value' to 'everyone agrees after a restriction map.'**" That generalization
**is** heterogeneous agreement: different parties can hold different local data and still glue,
provided the restriction maps reconcile on overlaps. **ESTABLISHED math; the distributed-systems
*interpretation* is exactly Felber et al. (§4).**

---

## 3. The contextuality canon — the ESTABLISHED "agreement = global section, obstruction = Ȟ¹"

This is the **mathematically rock-solid** instance of ember's correspondence, in a different
applied domain (quantum foundations), and it is what every later paper cites.

### 3.1 Abramsky–Brandenburger: compatibility = sheaf condition; (non-)contextuality = (no) global section `[ESTABLISHED]`
`pdfs/sheaf-nonlocality-contextuality-abramsky-brandenburger-1102.0264.pdf` (NJP 13:113036, 2011).

- Measurements/contexts form a cover; **the assignment of (distributions over) outcomes is a
  presheaf `E` — the "sheaf of events"** (paper §2, l.225–226).
- A family of local sections `{s_i ∈ E(U_i)}` is **compatible** iff they *agree on overlaps*:
  `s_i |_{U_i ∩ U_j} = s_j |_{U_i ∩ U_j}` (l.220). **This compatibility is precisely
  no-signalling** (l.118–123): *"the property of compatibility of a family of sections on a
  presheaf corresponds to a form of no-signalling."*
- **The sheaf condition** is: every compatible family glues to a **unique global section**
  (l.223–226). **Non-contextuality ⟺ a global section exists**; **contextuality ⟺ the locally
  compatible family does NOT glue** (abstract l.30; §2.4). *Strong contextuality* = there is no
  global section even in the support (possibilistic).

> **This is the exact shape of ember's idea, proved.** "Each party's local verdict" = a local
> section `s_i`; "agree on the shared sub-context" = compatibility on overlaps = the restriction
> maps coincide; "glue to a global verdict" = the sheaf condition; "a fork / disagreement that
> cannot be reconciled" = **the family is locally compatible but has no global section** =
> contextuality. The Two-Generals / FLP / fork phenomenon is the *distributed-systems instance*
> of "locally consistent, globally non-gluable."

### 3.2 Abramsky–Mansfield–Barbosa: the obstruction IS a cohomology class `[ESTABLISHED]`
`pdfs/sheaf-cohomology-nonlocality-1111.3620.pdf` (arXiv:1111.3620).

- Build an **abelian presheaf** `F` from the support of the model; take **Čech cohomology**
  `Ȟ*(U, F)` over the measurement cover (paper §3).
- For a chosen local section `s` over a context `C`, define a cochain `c`, take its coboundary
  `z = δ⁰(c)`; `z` is a cocycle in the *relative* cohomology w.r.t. the rest of the cover, and
  **`γ(s) := [z] ∈ Ȟ¹(U, F_{C̄₁})` is the obstruction class** (Prop. 4.1, Def. of `γ`, l.220–232).
- **Theorem (l.13–22, §4):** `γ(s)` **vanishes if `s` extends to a global section.** Hence
  **non-vanishing of the obstruction is a *sufficient* condition for contextuality** (no global
  gluing). *"There is a more conceptual way of defining this obstruction, using the connecting
  homomorphism from the long exact sequence of cohomology"* (l.237) — i.e. it is the standard
  `H⁰(local) → H¹(pair)` boundary map. In "good cases" (e.g. possibilistic/`ℤ₂`, the
  All-vs-Nothing and Kochen–Specker families) the condition is **also necessary**, giving a
  cohomological *characterization*.

> **The honest caveat that dregg must inherit.** The cohomological obstruction is **sufficient
> but not always necessary**: there exist contextual models (no global section) whose *first*
> Čech obstruction class nonetheless vanishes ("false negatives" of cohomology). The clean
> iff-statement is **"global section exists ⟺ the family is non-contextual"** (§3.1, ESTABLISHED);
> the **"⟺ H¹ = 0"** upgrade holds only in good cases. **So: "consensus = global section (H⁰)"
> is the iff; "fork = nonzero H¹" is the *sound-but-incomplete* detector** (a nonzero class
> certifies a fork; a zero class does not by itself certify agreement in general). This is the
> exact place where sloppy sheaf-talk overclaims, and where dregg's kernel-exposes-gaps
> discipline must bite.

---

## 4. The direct bridge — Felber–Hummes Flores–Rincon-Galeana (2025) `[ESTABLISHED, recent/single-source]`

`pdfs/sheaf-tasks-distributed-2503.02556.pdf` (arXiv:2503.02556v2, Aug 2025). This is the paper
that **moves "consensus = a global section" from ANALOGY to THEOREM** for general distributed
computing, and it explicitly builds on both Goubault et al. (chromatic semi-simplicial sets) and
Abramsky (cited as [1]).

**The construction (the per-party-verifier sheaf, made precise).**
- **Execution graph / system frame** (Def. 2–4): vertices = global configurations of a run;
  edges = **indistinguishability** `⟨g⟩ ∼_p ⟨h⟩` (process `p` cannot tell two configs apart).
  *This is literally the simplicial-epistemic indistinguishability graph of §1, used as the
  **site**.*
- **Task** `T = ⟨I, O, Δ⟩` (Def. 7); **execution cut** (Def. 9) = a frontier intersecting every
  run where processes "have enough information to decide" (= the epistemic horizon).
- **Task sheaf `F_{S,T}`** (Def. 17): a **cellular sheaf over the system slice**; stalk over a
  configuration = the **task-valid output vectors** there; restriction maps send a joint decision
  to its **process-wise (colored) faces** (the chromatic-semi-simplicial / Goubault encoding,
  §4.1). Crucially (§4.2): there is **one sheaf `F_p` per process `p`** — the localization of the
  slice to `p`'s view — *"a set of functors with common codomain,"* and the **global sheaf `F` is
  the colimit `colim_p F_p`**, with the property *"a global section exists iff there is a global
  section on the individual ones"* (paper l.562–567).

> **This is exactly ember's "(pre)sheaf of verifiers over the parties," in the literature.** One
> verifier/decision-sheaf per party `F_p`; the site = the indistinguishability (who-shares-context)
> complex; restriction maps = how a verdict restricts to a shared sub-context; the **colimit `F`
> with "global section iff each local one glues" = the gluing/sheaf condition.** Heterogeneity is
> free: the `F_p` need not be the same functor.

**The main theorems.**
- **Theorem 20 (Terminating Task Solvability):** *there exists a terminating decision map `δ`
  solving `T` **iff** some execution cut's system slice has a **section** over the task sheaf
  `F_{A,≃}`.* (Proof, pp.11–12.) **`agreement/solvability ⟺ existence of a global section`.**
- **Cohomology (Defs. 22–24, §5):** `C⁰ = ⊕_v F(v)` (assignments to configurations),
  `C¹ = ⊕_e F(e)` (per-process choices along indistinguishability edges); coboundary
  `d(x)_e = π_p(x_h) − π_p(x_g)` (the difference between indistinguishable configs); **a section is
  a 0-cochain killed by `d`**, and *"the set of all sections is the kernel `ker(D)`"* =
  **`H⁰` (Def. 24, l.728)**. The decision space and the **obstructions to solving the task are
  read off the cohomology** (abstract l.27–28; §5).
- **Theorem 26 (Computable Decision Maps):** a task solvable in a finite slice ⟺ that slice
  admits a **non-trivial zeroth cohomology**; the impossibility example (ε-agreement in 0 steps,
  Example 25) is proved by exhibiting **`ker D = {trivial}` — no global section ⇒ impossible**,
  with every step *deterministic and computable* (turning topological impossibility into linear
  algebra).

> **The degree caveat — be precise for dregg.** In *this* construction the **section space is
> H⁰ (= ker of the coboundary), and "impossible" = H⁰ trivial.** Their cohomology "encodes the
> obstructions" but the headline impossibility test is **triviality of H⁰**, not non-vanishing of
> H¹. The **H¹-as-obstruction** statement is the *contextuality* form (§3.2) and the *cellular*
> form (Hansen–Ghrist §2): when you phrase "a locally consistent family that fails to glue," the
> failure-to-extend lives in H¹ via the connecting homomorphism. **Both are correct; they are dual
> framings of one fact.** The clean, defensible dregg statement is therefore:
> **consensus/agreement = H⁰ is non-trivial and contains the desired section (a global section
> exists); a fork = that section does not exist = the local family is non-gluable, certified by a
> non-vanishing relative-H¹ obstruction class (sound, not always complete).** Do not assert "fork
> = nonzero H¹" as an iff without the good-case hypothesis.

**Maturity flag.** Felber et al. is **recent (2025), single-group, brief-announcement-grown**.
It is rigorous and model-independent, but it is *not* yet canon the way Abramsky-contextuality or
Goubault-simplicial are. For dregg: cite it as **the existence proof that the bridge is buildable
and the iff is real**, while treating the precise cohomological packaging as still-settling.

---

## 5. Heterogeneous / reconfigurable trust = the heterogeneous sheaf (Li–Lesani) `[ESTABLISHED systems; ANALOGY to sheaf]`

`pdfs/zotero-reconfigurable-heterogeneous-quorum-systems.pdf` (DISC 2024, arXiv:2304.02156v2).

This is the systems-side anchor for "**different software / different trust per node = different
sections.**" A **heterogeneous quorum system (HQS)** `Q` (Def. 1) *"maps each active process to a
non-empty set of individual minimal quorums"* — i.e. **each party declares its own trust set**
(its own "section" of who-it-believes). No global quorum assumption: *"open quorum systems
relinquish global information as processes specify their own quorums"* (p.2). The properties:
- **Consistency = quorum intersection** (Def. 3): `∀ p,p′ well-behaved, ∀ q∈Q(p), q′∈Q(p′),
  q ∩ q′ ∩ P ≠ ∅`. **This is the overlap-agreement / sheaf-compatibility condition**: any two
  parties' trust sets must agree on a shared sub-context. *"The safety of consensus naturally
  relies on the consistency (or quorum intersection)"* (p.2).
- **Availability** (Def. 6) and **inclusion** (p.3) round out the well-formedness.
- **Quorum graph + single sink component** (§4, pp.12–13): vertices = processes, edge `p→p′` iff
  `p′` is in a minimal quorum of `p`; SCCs condense to a **DAG with exactly one sink component**;
  *"preserving consistency reduces to preserving quorum intersections in the sink component"*
  (p.2, Lemmas 16–17). **Any reconfiguration outside the sink preserves consistency**, so a node
  can locally reconfigure without global synchronization (the decentralized sink-discovery
  protocol).

**Mapping to the sheaf-of-verifiers.**

| HQS notion | Sheaf-of-verifiers notion |
|---|---|
| process `p`'s declared quorums `Q(p)` | the **stalk** `F(p)` = `p`'s local verdict/trust data |
| heterogeneous trust (each `p` differs) | a **non-constant sheaf**: stalks/restrictions differ per party |
| consistency = quorum intersection `q∩q′∩P ≠ ∅` | the **restriction maps agree on overlaps** (compatibility) |
| consensus safety rests on consistency | **a global section exists ⟹ a sound global verdict** |
| **single sink component** of the quorum graph | the **support of the global section** = the locus where gluing is forced/decided (the H⁰-bearing core); changes outside it are H⁰-invariant |
| reconfiguration (join/leave/add/remove) | **change of site/sheaf over time** = upgrades & membership change |
| a reconfiguration that breaks consistency → fork/double-spend | a change that **destroys the global section** = an H¹ obstruction (a fork) |

> **This is the precise home for ember's three motivating cases.** **Software bugs**: a party's
> stalk `F(p)` carries a wrong verdict that disagrees on the overlap → no global section (the
> family fails to glue). **Upgrades (v1 vs v2)**: two different sheaves over a moving site;
> backward-compat = the restriction maps still agree on the shared sub-context = the reconfigured
> sheaf still admits a global section; an incompatible upgrade = a self-inflicted H¹ fork (Li–Lesani's
> *"reconfiguration can be the antecedent to a fork and double-spending,"* p.2). **Genuine
> heterogeneity**: the sheaf is honestly non-constant; agreement is "agree *after a restriction
> map*," not "hold the identical bits" — which is the whole point of the cellular-sheaf
> generalization of consensus (§2). The HQS theorems (consistency = intersection; single-sink
> condensation) are **ESTABLISHED**; the *sheaf re-description* is an apt **ANALOGY** that would
> become a theorem by exhibiting the quorum-consistency presheaf and proving its global sections
> are exactly the consistent global states (a clean, buildable target — §7).

---

## 6. Cross-paper synthesis — the bridge in one table

| Layer | Site (who-shares-context) | "Data per perspective" | Agreement / consensus | Disagreement / fork | Status |
|---|---|---|---|---|---|
| **Epistemic / Kripke (S5ₙ)** | worlds + `∼_a` | valuation per world | **common knowledge `C_A`** = a fact true throughout a `∼`-connected component | distinct components / non-shared knowledge | ESTABLISHED |
| **Simplicial-epistemic (Goubault)** | chromatic complex: vertices=local states, simplices=compatible globals | label `ℓ(v)` per vertex | **0-connectivity ⟹ common knowledge; consensus solvable** only after the protocol complex *disconnects* | protocol complex stays connected ⟹ consensus impossible | ESTABLISHED |
| **Cellular sheaf (Hansen–Ghrist)** | cell complex `X`, incidences | stalk `F(σ)` + restrictions | **`H⁰=Γ(X;F)=ker δ`** = global sections = consensus space (Laplacian kernel) | `H¹ = ker δ₁/im δ₀` = local-consistencies that don't glue | ESTABLISHED (math) |
| **Contextuality (Abramsky et al.)** | measurement cover | distribution per context | **global section exists ⟺ non-contextual / no-signalling glues** | contextual = compatible-but-non-gluable; obstruction `γ(s)∈Ȟ¹` (vanishes if section exists) | ESTABLISHED |
| **Task sheaf (Felber et al. 2025)** | execution/indistinguishability graph (cut) | task-valid outputs per config; **one `F_p` per process** | **Thm 20: solvable ⟺ global section; Thm 26: `H⁰`(=ker D) non-trivial**; `F = colim_p F_p` | trivial section space ⟹ impossible (FLP/ε-agreement) | ESTABLISHED (recent) |
| **Heterogeneous quorums (Li–Lesani)** | quorum graph (single sink) | each `p`'s own quorums `Q(p)` | consistency = quorum intersection on overlaps ⟹ safety | reconfiguration breaking intersection ⟹ fork/double-spend | ESTABLISHED systems; sheaf re-reading = ANALOGY |
| **dregg proof-forest** | happened-before edges (site) | `ProofNode` = per-step `StepInv` witness | `proofForest_sound`: per-node valid ∧ `Linked` ⟹ whole-run `StepInv` (**gluing axiom, term-proved**) | UNLINKED-but-locally-valid list does **not** glue (`¬chainLinked`, proved) — the sheaf condition *bites* | **dregg-ANCHOR (REAL gluing)** |

---

## 7. Honest verdict for dregg — what is real, what is the missing theorem

**What is ESTABLISHED (cite freely):**
1. **Simplicial-epistemic ↔ Kripke** is a categorical equivalence; **common knowledge ⟺
   connectivity** (Goubault et al.; Halpern–Moses lineage). The simplex = compatible global state =
   ember's "simplicial-epistemic complex." `[ESTABLISHED]`
2. **A sheaf over that complex = data-per-perspective with gluing**, and **`H⁰ = global sections =
   the agreement space`** is a definitional theorem of cellular-sheaf cohomology (Hansen–Ghrist,
   Curry). `[ESTABLISHED]`
3. **Agreement = a global section, obstruction = a cohomology class that vanishes when a section
   exists** is a *proved theorem* in the contextuality setting (Abramsky–Brandenburger;
   Abramsky–Mansfield–Barbosa), with the standard caveat that the cohomological detector is
   **sufficient, not always necessary** for non-gluing. `[ESTABLISHED, with caveat]`
4. **Distributed task solvability ⟺ existence of a global section of a task sheaf over the
   indistinguishability complex**, with **one sheaf per process and the global sheaf as their
   colimit**, and cohomology encoding the obstructions, is proved model-independently by
   **Felber–Hummes Flores–Rincon-Galeana (2025)**. This is the **direct cash-out** of ember's
   idea and it confirms it is buildable. `[ESTABLISHED, recent/single-source]`
5. **Heterogeneous trust = each party its own (non-constant) section; consistency = overlap
   intersection; fork = loss of the global section** matches reconfigurable HQS exactly
   (Li–Lesani). `[ESTABLISHED systems]`

**So: is "common knowledge = H⁰ / fork = H¹" established or fresh analogy?**
- **"Common knowledge / consensus = a global section (H⁰)"** — **ESTABLISHED.** Three independent
  literatures (epistemic-connectivity, cellular-sheaf `H⁰≅Γ`, and the 2025 task-sheaf Thm 20)
  state precisely this. Not a fresh analogy.
- **"Fork / Byzantine disagreement = an H¹ obstruction"** — **ESTABLISHED in contextuality and
  in the cellular-sheaf `ker δ₁/im δ₀` sense; ANALOGY-trending-ESTABLISHED in distributed
  computing.** The obstruction is genuinely cohomological (a connecting-homomorphism class), and
  non-vanishing certifies non-gluing; but it is the **sound-not-complete** direction, and the
  task-sheaf paper's headline test is *triviality of H⁰*, not nonzero H¹. **Claim it as a sound
  obstruction detector, not an iff, unless you prove the good-case hypothesis for dregg's sheaf.**

**The dregg-ANCHOR (REAL, already term-proved):**
- The **proof-forest IS a finite sheaf-gluing**: `ProofForest.proofForest_sound`
  (`metatheory/Dregg2/Exec/ProofForest.lean:177`, axiom-clean) = per-node validity (local
  sections) + `Linked` (agreement on overlaps: `newCommit = oldCommit` = restriction maps
  coincide) ⟹ whole-run `StepInv` (the global section). The **sheaf condition bites**: the
  unlinked-but-locally-valid list is provably **not** `chainLinked`
  (`ProofForest.lean:293`) — local validity alone does **not** glue. The cross-cell case
  (`Exec/CrossCellForest.lean:278`, `crossForest_attests`) is the **wide-pullback gluing** whose
  overlap condition is the CG-5 N-ary balance `Σδ=0`. `[REAL as a 1-categorical gluing;
  universal-property/colimit naming is DECORATIVE — see FOUNDATIONS-verify-find-logic.md §3.2.]`
- **Verifier-indexed verdict** = the first step of "one sheaf per party": `DischargedFor`
  (`metatheory/Dregg2/Authority/DesignatedVerifier.lean:113`), with public mode recovered as the
  `∀ V` collapse (the *constant* sheaf = the homogeneous special case). This is the `F_p` index.

**The MISSING THEOREM (the buildable, REAL next step — do NOT let vocabulary substitute for it):**
> **Proof-forest soundness, generalized over a verifier-sheaf.** State and prove: *given a sheaf
> of verifiers `F_p` over the happened-before/indistinguishability site (each party with its own,
> possibly heterogeneous, `DischargedFor`-verdict), if the local verdicts are pairwise compatible
> on overlaps (the restriction maps agree = `Linked` lifted to `∀ p`), then they glue to a sound
> global verdict (a global section), and the gluing is non-trivial exactly when the overlap
> family is consistent.* This is `proofForest_sound` with the constant fibre replaced by a
> `V`-indexed (verifier-indexed) fibre — i.e. **dregg's already-proved finite sheaf-gluing, made
> into an honest presheaf of verifiers.** Per Felber et al., the right global object is the
> **colimit `colim_p F_p`** and the theorem to target is **"a global section of `colim_p F_p`
> exists iff each `F_p` admits one and they agree on overlaps."** That is REAL + buildable today,
> directly extends a term-proved theorem, and is the line past which the cohomology-of-consensus
> stops being suggestive. **Everything beyond — naming the obstruction space `H¹`, computing it,
> calling the directory a topos — stays DECORATIVE until that generalized gluing theorem is in
> the Lean.** (Discipline per the kernel-exposes-gaps rule and FOUNDATIONS-verify-find-logic.md.)

**Bottom line.** The sheaf framing is **not poetry**: the per-party-verifier-as-sheaf and
consensus-as-global-section have *published theorems* (Goubault; Hansen–Ghrist; Abramsky;
Felber 2025), and dregg's proof-forest is *already* a term-proved finite sheaf-gluing with the
verifier index in hand. The single honest gap between dregg-today and the full picture is the
**verifier-sheaf-generalized gluing theorem** above — small, buildable, and the exact thing that
turns "the proof-forest is a sheaf" into "the sheaf-of-verifiers soundness theorem." H⁰-as-consensus
is solid; treat H¹-as-fork as a sound obstruction detector (sufficient, not iff) until dregg's own
sheaf earns the good-case characterization.
