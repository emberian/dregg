# HANDLER-TRANSFORMER-LIT — the established math of higher-order/scoped effects and handler/comodel composition, mapped honestly to dregg

> **What this is.** A READ-ONLY literature grounding for ember's *higher-order
> handler-transformer frontier*. The conjecture: a SAFE higher-order handler-transformer = a
> MORPHISM in a category of SHEAVES-OF-HANDLERS, and the SAFE-COMPOSITION LAW = the camera's
> frame-preserving update (`Fpu`) = the sheaf gluing condition; and dregg already proves special
> cases of every facet. Before we can know whether dregg would *discover* something or merely
> *instantiate* known math, we have to know **what the literature actually established**. This
> doc distills the load-bearing definitions and theorems of (a) algebraic effects + the SUM and
> TENSOR of theories, (b) handlers, (c) scoped/higher-order effects, (d) comodels/runners and
> the model⊗comodel tensor, (e) the monad-transformer non-composition problem, and (f) the
> established separation-logic-for-handlers frame rule — then maps each, with teeth, to the
> dregg facets the conjecture names.
>
> **Honesty discipline (ultracode).** Every cross-claim is tagged:
> - **ESTABLISHED** — a published theorem/definition in the cited paper (with the citation);
> - **REAL (dregg)** — a term-proved Lean theorem at `file:line` with teeth;
> - **INSTANCE** — dregg's REAL fact is a genuine *special case* of an ESTABLISHED definition
>   (same definition instantiated — a real, if modest, contact point);
> - **ANALOGY** — a motivated correspondence that is NOT yet an instance of one shared definition
>   (shared *vocabulary* over facts that do not provably instantiate one structure);
> - **OPEN (lit)** — genuinely open *in the literature itself* (so a dregg theorem here would be
>   new mathematics, not a re-derivation).
>
> A real discovery is a THEOREM subsuming the special cases, with teeth (an unsafe transformer is
> *genuinely rejected*). A pretty re-description is shared vocabulary over facts that do not
> instantiate one definition. **OPEN beats a vacuous theorem.**
>
> **Read against:** `FOUNDATIONS-effect-comodel-lens.md` (the dregg-side audit of exactly these
> facets — REAL/DECORATIVE/ASPIRATIONAL, the companion to this doc), `SHEAF-OF-VERIFIERS.md`
> (facet 3), `DREGG2-FOUNDATIONS.md` (the comodel/lens/handler-transformer tagged ASPIRATIONAL).

---

## 0. The papers (all pulled into `pdfs/`, validated `head -c 4 == %PDF`)

| Tag | Paper | `pdfs/` file |
|---|---|---|
| **PP09** | Plotkin & Pretnar, *Handlers of Algebraic Effects*, ESOP 2009 | `handlers-of-algebraic-effects-plotkin-power.pdf` (NOTE: filename says "plotkin-power" but the PDF is verified to be the Plotkin & **Pretnar** ESOP'09 handlers paper) |
| **PP-h** | Plotkin & Pretnar, *Handling Algebraic Effects*, LMCS 2013 | `handling-algebraic-effects-plotkin-pretnar-1312.1399.pdf` |
| **HPP06** | Hyland, Plotkin & Power, *Combining effects: sum and tensor*, TCS 2006 | `effect-hpp-sum-and-tensor.pdf` |
| **PP08** | Plotkin & Power, *Tensors of Comodels and Models for Operational Semantics*, MFPS 2008 | `effect-tensors-comodels-models-opsem.pdf` |
| **Sta13** | Staton, *Instances of Computational Effects: An Algebraic Perspective*, LICS 2013 | `effect-staton-instances-of-computational.pdf` |
| **Wu14** | Wu, Schrijvers & Hinze, *Effect Handlers in Scope*, Haskell 2014 | `effect-handlers-in-scope-wu.pdf` |
| **WS15** | Wu & Schrijvers, *Fusion for Free: Efficient Algebraic Effect Handlers*, MPC 2015 | `effect-fusion-for-free-wu-schrijvers.pdf` |
| **LMM+24** | Lindley, Matache, Moss, Staton, Wu, Yang, *Scoped Effects as Parameterized Algebraic Theories*, FoSSaCS 2024 / TOPLAS 2025 | `effect-scoped-as-parameterized-algebraic.pdf` |
| **vdBS23** | van den Berg & Schrijvers, *A Framework for Higher-Order Effects & Handlers*, SCP 2024 | `handler-higher-order-effects-vdberg.pdf` |
| **Hefty** | Bach Poulsen & van der Rest, *Hefty Algebras: Modular Elaboration of Higher-Order Effects*, POPL 2024 | `handler-hefty-algebras-modular-elaboration.pdf` |
| **AB20** | Ahman & Bauer, *Runners in Action*, ESOP 2020 | `effect-runners-in-action-ahman-bauer.pdf` |
| **Gar21** | Garner, *Stream Processors and Comodels*, CALCO 2021 | `effect-stream-processors-comodels-garner.pdf` |
| **Gar-cc** | Garner, *The costructure–cosemantics adjunction for comodels*, MSCS 2022 | `effect-costructure-cosemantics-adjunction-garner.pdf` |
| **KRU20** | Katsumata, Rivas & Uustalu, *Interaction Laws of Monads and Comonads*, LICS 2020 | `effect-interaction-laws-monads-comonads.pdf` |
| **LHJ95** | Liang, Hudak & Jones, *Monad Transformers and Modular Interpreters*, POPL 1995 | `effect-monad-transformers-liang-hudak-jones.pdf` |
| **dVP21** | de Vilhena & Pottier, *A Separation Logic for Effect Handlers*, POPL 2021 | `handler-separation-logic-effect-handlers-devilhena-pottier.pdf` |
| **Blaze26** | de Vilhena & Pottier, *A Relational Separation Logic for Effect Handlers*, POPL 2026 | `handler-relational-separation-logic-blaze.pdf` |

Plus the standing library: `monadic-framework-delimited-continuations.pdf`, `one-shot-continuations-dybvig.pdf`, `effective-concurrency-algebraic-effects.pdf`, `coalgebraic-semantics-silva.pdf`, `iris-from-the-ground-up.pdf` (all in `pdfs/`, see `pdfs/INDEX.md §7, §11, §12`).

---

## 1. ESTABLISHED: algebraic effects, the free model, and handlers

### 1.1 Effects = operations + equations; the monad = the free model
**[PP09 / HPP06, ESTABLISHED].** An algebraic effect is presented by an **(enriched) Lawvere
theory** `L`: a signature of **operation symbols** `op : n` (each with an arity, possibly a
parameter/result indexing `op : A ⇝ B`) plus a set of **equations** between operation-terms.
The associated computation monad `T` is the **free-model functor** of `L`: `TX` = terms over `X`
modulo the equations (HPP06 §1; PP08 §1). Examples (HPP06): exceptions `TE = − + E`; state
`TS = (S × −)^S` presented by `lookup_l : V`-ary and `update_{l,v} : 1`-ary with the four
state equations; nondeterminism by a semilattice `∨`.

Operations come in two equivalent presentations (HPP06; PP08 "Algebraic Operations and Generic
Effects"): **algebraic operations** `op_X : (TX)^n → TX` characterised by a naturality/algebraicity
condition (they **commute with sequencing `>>=`**), in bijection with **generic effects**
`A → T B`. *Algebraicity* — the operation commuting with the continuation — is the dividing line
that the higher-order story (§3) is all about.

### 1.2 Handlers = models; handling = the unique homomorphism out of the free model
**[PP09, ESTABLISHED — the load-bearing theorem].** Each handler corresponds to a **model** of the
theory `L` (a carrier + an interpretation of every operation satisfying the equations). The
handling construct `handle c with H` is interpreted as the **unique `L`-homomorphism** from the
**free model `TX`** (the syntax tree of the computation `c`) to the programmer's model `H`, given
by the **universal property of the free model** (PP09 abstract: "handling a computation amounts to
composing it with a unique homomorphism guaranteed by universality… its domain is a free model…
its range is a programmer-defined model"). Algebraic operations are *effect constructors*; handlers
are *effect deconstructors* — they are **dual** (PP09 §1).

Key honesty fact carried forward: **the `handle` operation is itself NOT an algebraic operation**
(PP09 §1, citing Plotkin–Power): exception handling fails the algebraicity/naturality condition.
This is *the* reason higher-order effects (§3) need more than the first-order Lawvere framework —
and it is exactly the gap dregg's `Await` handler lives in.

---

## 2. ESTABLISHED: SUM and TENSOR of theories — and the precise obstruction

This is the crux of the conjecture's facet (1) ("handler composition = tensor of theories, and the
obstruction = the tensor not being free / a proper quotient"). Here is what HPP06 actually proves.

### 2.1 The two canonical combinators
**[HPP06 §1, ESTABLISHED].** Two effect theories `L`, `L′` combine in (at least) two canonical ways:

- **SUM `L + L′`** — "the operations of each, the equations of each, **with no equations relating
  them**." On monads it yields `TE ◦ T = T(− + E)` (the exceptions / I-O monad transformers).
  Free coproduct of theories.
- **TENSOR `L ⊗ L′`** (the *Kronecker product* of theories) — "the operations of both theories
  and demanding that they **commute with each other**, while retaining the equations of both."
  On monads it yields the side-effects monad transformer `TS ⊗ T = T((S × −)^S)`. The added
  equations are the **commutation equations**, e.g. for state ⊗ nondeterminism:
  ```
  lookup_l(x1 ∨ y1, x2 ∨ y2, x3 ∨ y3) = lookup_l(x1,x2,x3) ∨ lookup_l(y1,y2,y3)
  ```
  (HPP06 §1) — inducing the program equivalence `let x = !y in (M or N) ≡ (let x=!y in M) or (let x=!y in N)`.

**The precise content of "the tensor is a proper quotient."** The tensor `L ⊗ L′` is **NOT** the
free combination `L + L′`; it is `L + L′` **quotiented by the commutation equations**. So there is
a canonical surjection `L + L′ ↠ L ⊗ L′` whose kernel is exactly the commutation relations. *The
tensor is a proper quotient of the sum precisely when the two theories' operations do not already
commute.* When they do commute freely, sum = tensor; when they do not, the tensor *adds* equations
and the free combination over-counts (distinguishes terms the tensor identifies). HPP06's
companion result (PP08 "Combining Computational Effects: commutativity & sum") makes this the
commutativity criterion.

### 2.2 The honest map to dregg's `binding_is_proper` / `hyper_binding_is_proper`

> **VERDICT: ANALOGY, with a precise sign-flip caveat — NOT an instance (yet). The dregg facet is
> a genuine *dual* phenomenon (a proper SUB-object), not the tensor's proper QUOTIENT.**

dregg's facet (1): `JointTurn.binding_is_proper` (`metatheory/Dregg2/JointTurn.lean:333`) and its
hyperedge generalization `Hyperedge.hyper_binding_is_proper` (`metatheory/Dregg2/Hyperedge.lean:164`),
with companions `joint_sound_needs_binding` (`JointTurn.lean:271`), `hyperedge_sound_needs_binding`
(`Hyperedge.lean:409`), and the composition keystone `joint_sound` (`JointTurn.lean:230`) /
`hyperedge_sound` (`Hyperedge.lean:374`). These are **REAL (dregg)** and axiom-clean. The proved
content (per the audit-corrected docstring, `JointTurn.lean:320-332`): the joint-admissible
cross-cell configurations form a **proper equalizer SUBOBJECT** of the product carrier
`T₁.Carrier × T₂.Carrier`, witnessed by two one-state cells each moving a half-edge `1 : ℕ` whose
CG-5 balance `1 + 1 = 2 ≠ 0` fails — so that product state is excluded, and the binding cannot be
recovered per-cell.

Now compare honestly:

| | HPP06 tensor `L ⊗ L′` | dregg `binding_is_proper` |
|---|---|---|
| The two things combined | two effect **theories** (operation+equation presentations) | two **coalgebras / comodels** `T₁, T₂` (running cells) |
| The combinator | `L + L′` quotiented by commutation | the **product** coalgebra `jointCoalg` (`JointTurn.lean:158`) |
| The "proper" fact | tensor is a proper **QUOTIENT** of the sum (adds commutation equations on a SYNTAX algebra) | joint-admissible is a proper **SUBOBJECT** (equalizer) of the product (cuts a STATE space by CG-2⊗CG-5) |
| Direction | algebra side (models, free→quotient) | coalgebra side (comodels, product→subobject) |

The two are **categorically dual** (quotient of a coproduct on the algebra side ↔ subobject of a
product on the coalgebra side) — which is *exactly* the model/comodel duality of §4. So the
correspondence is real and pretty, but the conjecture's slogan — "binding_is_proper is the tensor
of two effect theories FAILING TO BE FREE" — is **imprecise as stated**: the tensor's failure to
be free is a *quotient* phenomenon on the *algebra* (handler/model) side, while `binding_is_proper`
is a *subobject* phenomenon on the *coalgebra* (cell/comodel) side. They are **dual instances of
"the combination of two effect structures is not the free/naive combination,"** but they are not
the *same* instance.

**What it would take to make this an INSTANCE, not an ANALOGY.** Either (i) build the **comodel
tensor** `C₁ ⊗ C₂` of the two cell-comodels in the precise sense of PP08 §4 / KRU20, and prove
`binding_is_proper` says exactly "`C₁ ⊗ C₂` is a proper subcomodel of `C₁ × C₂`" (so the dregg fact
becomes a literal instance of the comodel-tensor being a proper subobject); or (ii) dualize and
show CG-2⊗CG-5 *is* the commutation requirement of two effect theories (conservation as a
commuting law), making `binding_is_proper` the tensor's proper-quotient on the nose. Neither is
built; both are plausible. **Tag: ANALOGY now; INSTANCE is the open dregg work.**

> **NOTE — the slogan correction the dregg audit already made.** The earlier `tensor_not_final`
> claim ("νF₁⊗νF₂ is not final ⇒ irreducibility") was **refuted** in dregg's own audit
> (`JointTurn.lean:320-332`): the product of two final coalgebras *is* final for the product
> functor. The literature agrees — the tensor's interesting content is the **commutation
> quotient** (HPP06), never a finality failure. So the conjecture's parenthetical ("'tensor
> non-finality' was CORRECTED — the real obstruction is the PROPER SUBOBJECT") is **right**, and
> it lines up with both the dregg audit *and* HPP06.

---

## 3. ESTABLISHED: higher-order / scoped effects — do they fit the first-order framework?

This is the conjecture's Question 2 ("Do higher-order effects — operations taking computations,
bracket/catch/scope — fit the first-order Lawvere/comodel framework, or do they need
parameterized/scoped theories? Does dregg's coalgebraic/guarded structure help?").

### 3.1 The problem: scoping/handling is not algebraic
**[Wu14 §1, ESTABLISHED].** Algebraic operations **commute with sequencing** (algebraicity,
§1.1). Scoping constructs (catch, `once`, local state, `local`, multi-threading delimiters) and
the `handle` operation itself **do not** — they need *access to an internal computation* (a
"program as argument"), not just a continuation. Wu14's headline dilemma: when you implement scopes
**as handlers**, the handler doubles as scope delimiter AND semantics, and the two roles fight —
"one order of the handlers provides the right scopes and the other order provides the right
semantics… we cannot have it both ways" (Wu14 §1). The fix: **move scoping into the syntax** via
**higher-order syntax** — operations whose arguments include sub-computations.

**[vdBS23, ESTABLISHED — the generic frame].** A **higher-order effect** is one whose signature
functor takes the **recursive computation type as an argument** (a higher-order functor
`H : (Type → Type) → (Type → Type)`), so an operation can "reason over an internal computation."
vdBS23 give a **generic free monad over higher-order signatures** + a fold-style interpreter, and
exhibit scoped, parallel, latent, writer, and **bracketing** effects as instances, each with a
recursion scheme, backed by a free–forgetful adjunction (vdBS23 §5). The **bracketing** effect
("safely dealing with resources") is the abstract shape of *acquire/use/release*. **Hefty
(POPL'24)** gives the complementary "**elaboration**" account: higher-order effects are
*elaborated* into algebraic ones modularly, so first-order handler machinery is recovered after a
translation pass.

### 3.2 The resolution: scoped effects = PARAMETERIZED algebraic theories (scopes as resources)
**[LMM+24, ESTABLISHED — the cleanest answer to Q2].** A **parameterized algebraic theory**
(Staton's framework, Sta13) extends a plain Lawvere theory with **variable-binding operations over
an abstract type of parameters/resources** — the constructors `(◁, ▷)` give *arities and coarities*
that bind a resource variable. LMM+24's theorem: **scoped effects translate into parameterized
algebraic theories by encoding scopes as RESOURCES with `open`/`close` operations** — "analogous to
opening/closing files." The delimited scope `once(x)` becomes `once(a. … close(a, …) …)`: a
binds a *scope resource*, `close(a, …)` ends it (LMM+24 §1, eq. (1)). This yields **the first sound
and complete equational reasoning system for scoped effects** (LMM+24 Prop. 2–3) and recovers the
known models (nondeterminism-with-`once`, catch, local state) as Thms. 2–4. Crucially, LMM+24
Thm. 1 shows the scoped constructors `(◁, ▷)` are "**not ad hoc**, but rather the crucial mechanism
for arities/coarities in parameterized algebraic theories."

**Bottom line on Q2 (ESTABLISHED):** Higher-order/scoped effects do **NOT** fit the *plain*
first-order Lawvere/comodel framework (handle, catch, scope are non-algebraic — they break
commutation with sequencing). They **DO** fit a *mildly enriched* framework: **parameterized
algebraic theories** (Sta13, LMM+24), where a scope is a **bound resource** with open/close, OR a
**higher-order signature functor** (vdBS23) elaborated to algebraic (Hefty). The first-order story
is recovered *after* either a parameterization or an elaboration pass.

### 3.3 The honest map to dregg's `Await` rollback handler (facet 4)

> **VERDICT: INSTANCE-adjacent — dregg's `Await` is a genuine, narrow instance of the *bracketing
> / resource* higher-order effect, and is the one place dregg's coalgebraic+guarded structure
> demonstrably "helps."**

dregg facet (4): `Await.turnAsRollbackHandler` (`metatheory/Dregg2/Await.lean:282`), with proved
laws `commit_resumes_once` (`:312`), `rollback_discards_continuation` (`:298`),
`one_shot_is_static` (`:138`), `four_faces_unify` (`:426`). The docstring already calls it "THE
handler: the turn IS the rollback handler" (`Await.lean:37`). This is **REAL (dregg)**.

Mapping with teeth:
- The `Await` operation is exactly a **bracketing / acquire-use-release** higher-order effect
  (vdBS23's `bracketing`; AB20's open/write/close finalisation example, §1) — an operation that
  takes a sub-computation (the awaited body) and a continuation, and either **commits** (resume the
  continuation once) or **aborts** (run finalisation/refund, discard the continuation). dregg's
  `commit_resumes_once` / `rollback_discards_continuation` are precisely the **commit arm** and
  **abort arm** of a bracketing handler.
- The **`one_shot_is_static`** law (one-shotness as a *typing* invariant) is a genuine instance of
  the **linear/affine use of the continuation** that AB20 build their whole calculus `λ_coop`
  around ("guarantees the linear use of resources and execution of finalisation code," AB20
  abstract) and that Dybvig's one-shot continuations (`pdfs/one-shot-continuations-dybvig.pdf`)
  formalize. So dregg's one-shot rollback is a *recognized point* in the established design space.
- **Where dregg's coalgebraic/guarded structure helps (the real contribution candidate):** the
  literature models the *commit/abort* arms operationally or denotationally; dregg additionally
  runs them as a **coinductive process under a guard** (`Boundary.F`, the `▶`-guarded
  previous-receipt-hash, `FOUNDATIONS-coalgebra.md`). The honest *new* question dregg can ask:
  **is a one-shot bracketing handler a guarded/contractive endo on the cell coalgebra, and does
  contractivity give safe composition of nested brackets?** That is not in LMM+24/vdBS23/AB20
  (they are first-order-after-elaboration; none run the handler as a guarded coalgebra). **Tag:
  the INSTANCE is real; the guarded-composition theorem is OPEN and is dregg's seed.**

> **The honest gap (already flagged by `FOUNDATIONS-effect-comodel-lens.md §3c, §9, row 27–28).**
> dregg's `Await` is the *one* genuinely handler-shaped, law-carrying object. But there is **no
> "turn that interprets turns" / comodel-homomorphism / verified-Custom theory-extension** — i.e.
> dregg has ONE higher-order handler, not a *calculus* of them, and not a *transformer* (a map
> sending handlers to handlers). The literature's higher-order *framework* (vdBS23, Hefty,
> LMM+24) is exactly the calculus dregg lacks. So the conjecture's "the Await handler is the seed"
> is **correct and honest**: it is a seed (one instance), not the tree (a framework).

---

## 4. ESTABLISHED: comodels, runners, and the model⊗comodel tensor — the cell side

This grounds the conjecture's facet (2) (`Resource.conservation_is_fpu` = "the law under which a
transformer does not break other handlers' invariants = the safe-composition condition") and the
deep claim that dregg's coalgebra **is** a comodel.

### 4.1 Comodels = models in the opposite category = stateful runners
**[PP08 §1; AB20 §1; Gar-cc, ESTABLISHED].** A **comodel** of a Lawvere theory `L` is a **model of
`L` in `C^op`** — "just models in the opposite category" (AB20 §1, with the caveat to use
powers/copowers). Concretely, for the theory of state a comodel **on a carrier `S`** interprets
each operation **co-operationally**: `lookup` becomes a *read* `S → V × S`-shaped map and `update`
a *write* `V × S → S`-shaped map — i.e. **`S` carries the actual mutable state and the co-operations
ARE the state transitions** (PP08 §1, the assignment/dereference rules). The **final comodel** is
the canonical "the world really has this state" model (Gar-cc; Gar21 — final comodels of free
theories are stream processors / Moore machines). AB20 rebrand the comodel as a **runner** (a.k.a.
a "co-operation per operation" `{op_x ↦ K_op}` running against kernel state) and prove it gives a
sound calculus `λ_coop` guaranteeing **linear resource use + finalisation** (AB20 abstract).

### 4.2 The tensor `C ⊗ M`: running a program against a state
**[PP08, ESTABLISHED — the operational keystone].** To give operational semantics for state one
needs a **countable Lawvere theory `L`, a comodel `C` (typically the FINAL one — the state) and a
model `M` (typically the FREE one — the program)**, and a **tensor `C ⊗ M`** "that allows
operations to flow between the two" (PP08 abstract). The transition `⟨s, M⟩ → ⟨s′, M′⟩` (state ⊗
term) is exactly an element of this tensor stepping: the program emits an operation, the comodel
(state) absorbs it and yields the next state + residual program. **KRU20** generalize this to the
**interaction law of a monad (program) and a comonad (environment)**: a natural transformation
`m X ⊗ w Y → (X ⊗ Y)` saying how a computation and a context **interact to produce a result** —
the abstract "running" operation.

### 4.3 The honest map: dregg's `Boundary.F` IS a (final-)comodel-shaped object

> **VERDICT: INSTANCE (shape) — dregg's cell coalgebra is, on the nose, the FINAL-COMODEL /
> stream-processor / Moore-machine shape PP08+Gar21 identify; the "running a turn" step IS a
> `C ⊗ M` interaction step. This is the strongest genuine contact point in the whole conjecture.**

`Boundary.F X = Obs × (AdmissibleTurn → X)` (`metatheory/Dregg2/Boundary.lean:66`), the cell as a
`TurnCoalg` with `obs` (output) and `next` (transition). Per `FOUNDATIONS-effect-comodel-lens.md
§1`, this is a **Moore/DFA coalgebra**. Now match the literature:
- Gar21's **final comodels of free theories ARE stream processors / Moore machines** — i.e.
  `Obs × (Input → X)` is *precisely* the carrier shape of a final comodel. So dregg's `F` is not
  *like* a comodel; it has the **exact functor shape** of the final comodel of a free theory whose
  "input" is the turn alphabet and "output" is the observation. **INSTANCE of the shape.**
- The dregg **"run a turn"** step (`next x t`) is exactly a PP08 `C ⊗ M` interaction step / a KRU20
  interaction law: the cell-as-comodel `C` (state) absorbs a turn-as-model `M` (program operation)
  and yields `(obs, next)`. The cell **is** the comodel `C`; the turn stream **is** the model `M`;
  the unfold **is** the tensor running. **INSTANCE (shape).**

What is *missing* to upgrade INSTANCE-of-shape → INSTANCE-of-theorem (the honest gap, matching
`FOUNDATIONS-effect-comodel-lens.md §3b, row 7`): there is **no `Comodel` typeclass, no
theory→functor→comodel bridge, no proof that `F` is the FINAL comodel of a named theory** (the
co-operations are not exhibited as interpreting `CatalogEffects` operation symbols). dregg has the
*carrier of a comodel* without the *comodel structure map indexed by a theory*. **Tag: INSTANCE of
the shape (REAL coincidence of functors); INSTANCE of the theorem is OPEN dregg work** (build the
`Comodel` and prove `F` final for the effect theory).

### 4.4 `conservation_is_fpu` (facet 2) = the resource law a runner must respect

> **VERDICT: ANALOGY → INSTANCE-candidate. The Fpu IS the established "linear/safe resource
> discipline" of runners (AB20), expressed in the camera (Iris) language rather than the runner
> language. The conjecture's "Fpu = safe-composition condition" is the RIGHT established notion,
> from the wrong-but-equivalent corner of the literature.**

dregg facet (2): `Resource.Fpu a b` (`metatheory/Dregg2/Resource.lean:103`, "replacing `a` by `b`
keeps every frame `f` valid"), with `Fpu.refl/.trans` (`:114/:118`) and the canonical conservation
law `conservation_is_fpu` (`:296`) on the `Auth M` camera. This is the **Iris frame-preserving
update** (`pdfs/iris-from-the-ground-up.pdf`), term-proved — **REAL (dregg)**.

Two established homes for "this is the safe-composition condition":
1. **Comodel/runner side (AB20):** a runner must use resources **linearly** and run **finalisation**
   — i.e. a co-operation must not invalidate the resource state another co-operation relies on.
   That "do not invalidate any other holder's resource" is *exactly* what `Fpu a b := ∀ f, valid
   (a · f) → valid (b · f)` says. So `conservation_is_fpu` is the **camera-theoretic form of AB20's
   linear-resource guarantee**. **ANALOGY now; INSTANCE if dregg proves the cell-comodel's
   co-operations are each `Fpu`-respecting (a runner that does not break frames).**
2. **Separation-logic side (§5):** the Fpu is *definitionally* the side-condition of the Iris
   **frame rule** — `{P} e {Q} ⊢ {P ∗ R} e {Q ∗ R}` holds because updates are frame-preserving.
   This is the established "transformer does not break other handlers' invariants" law. **This is
   the precise established statement of the conjecture's facet (2)** — see §5.

---

## 5. ESTABLISHED: the safe-composition law = the frame rule for handlers (Question 3)

This is the conjecture's Question 3 ("Is there an established 'safe handler-transformer = a
morphism preserving X' where X = a frame/separation condition — any link to separation logic / the
Fpu / Iris?"). **Answer: YES, and it is recent and directly on-point.**

### 5.1 The established theorem
**[dVP21, ESTABLISHED].** *A Separation Logic for Effect Handlers* (POPL 2021, built **on Iris**)
gives a separation logic with built-in support for effect handlers (shallow and deep). The
specification of a program fragment includes a **protocol** describing the effects it may perform
and the replies it may receive; the logic supports **local reasoning via a FRAME RULE and a bind
rule** (dVP21 abstract). Case studies: **control inversion** (push→pull), and **cooperative
concurrency with promises** (threads spawn, communicate via promises) — i.e. *exactly* dregg's
`await`/`zkpromise` shape. **Blaze26** (POPL 2026) extends this to a **relational** separation logic
for handlers (two programs, related). Both are in `pdfs/`.

So the established statement is: **a handler is "safe to compose into a larger program" exactly
when it satisfies its PROTOCOL and the surrounding state is preserved across the frame — and the
frame rule is sound precisely because the underlying updates are frame-preserving (the Iris Fpu).**
That is the conjecture's "safe handler-transformer = morphism preserving a frame/separation
condition," **already a theorem** — but stated for *programs verified against a handler protocol*,
not for *handler-transformers as morphisms in a category of sheaves of handlers*.

### 5.2 The honest map (facets 2, 3, 5)
- The conjecture's **"safe-composition law = Fpu = frame-preserving update"** is **ESTABLISHED** as
  the soundness condition of the dVP21/Iris frame rule. dregg's `conservation_is_fpu`
  (`Resource.lean:296`) is a **REAL instance of the Iris Fpu**, and the Iris Fpu is **exactly** the
  dVP21 frame-rule side-condition. So facet (2) is an **INSTANCE** of the established frame-rule
  machinery (same camera, same Fpu) — the strongest "we instantiate known math" result in the doc.
- The conjecture's **facet (3)** — proof-forest gluing `ProofForest.proofForest_sound`
  (`metatheory/Dregg2/Exec/ProofForest.lean:177`: `Linked` (chain-link, `:148`) + per-node
  `StepProofValid` ⟹ composite `StepInv`) — is the **distributed/sheaf** counterpart, and the
  sheaf-of-verifiers framing (`SHEAF-OF-VERIFIERS.md`) is the established route (Felber 2025; cellular
  sheaves). dVP21 is the **single-machine** safe-composition law (frame rule); the proof-forest is
  the **distributed** safe-composition law (sheaf gluing). The conjecture's claim that *these are
  the same law at two scales* is the genuinely OPEN, genuinely interesting bet (§6).
- The conjecture's **facet (5)** — `DesignatedVerifier.DischargedFor : Verifier → Statement →
  Proof → Prop` (`metatheory/Dregg2/Authority/DesignatedVerifier.lean:113`) as "the per-party
  stalk" — maps to the **protocol-per-handler** of dVP21 (each handler has its own protocol/spec)
  and the **stalk-per-party** of the verifier sheaf (`SHEAF-OF-VERIFIERS.md §1`). **ANALOGY**: a
  verifier-indexed verdict is a stalk; dVP21's per-handler protocol is a per-component spec; making
  these *one* indexed family with restriction maps is the sheaf step, still POETRY in dregg until
  it is a Lean theorem (`SHEAF-OF-VERIFIERS.md`).

---

## 6. The monad-transformer NON-composition problem — why "transformer" is the load-bearing word

The conjecture is about handler-**transformers**. The literature's hardest, most cautionary lesson
lives here, and it is the strongest reason the conjecture's general theorem would be *new* if true.

### 6.1 The established negative results
- **[LHJ95, ESTABLISHED].** Monad transformers individually capture features and **lifting**
  accounts for feature interaction — but **liftings are not free**: "semantics can be changed by
  reordering" liftings, and Moggi's categorical characterization of *liftable* operations
  **fails** for many useful operations (`merge`, `inEnv`, `callcc`) (LHJ95 §"Lifting"). The number
  of liftings grows **quadratically** ("the number of possible liftings grows quadratically") — the
  **n² lifting problem**: each operation must be re-lifted through each transformer.
- **[WS15 / Wu14, ESTABLISHED].** Handler order matters (state ⊗ nondeterminism: the two orders
  give *different* semantics — the classic example, Wu14 §1). WS15 ("Fusion for Free") fuses a
  *sequence* of handlers into one, but only by keeping the free monad **abstract**; fusion is a
  *performance* optimization that is **sound only because** the handlers compose correctly to begin
  with — it does not *make* unsafe orders safe.
- **The deep reason monads don't compose (folklore, formalized in LHJ95 lineage): there is no
  natural way to compose two arbitrary monads `M ∘ N` into a monad.** Transformers are the
  workaround, and transformers do not commute. This is *the* obstruction the conjecture's
  "safe-composition law" must confront: a general safe handler-transformer composition theorem
  would have to say **which** orders/compositions are safe — and that is precisely what is
  **OPEN/hard** in the literature.

### 6.2 The honest map (facet 1, again, and the whole conjecture)

> **VERDICT: this is where dregg would be DISCOVERING, not instantiating — IF it delivers a theorem
> with teeth. The literature has no single "safe handler-transformer = morphism preserving X"
> theorem that subsumes sum/tensor/scoped/higher-order composition AND rejects the unsafe orders.
> It has: tensor (when ops commute, HPP06), lifting (ad-hoc, quadratic, LHJ95), fusion (perf, WS15),
> parameterized theories (scoped, LMM+24), higher-order frameworks (vdBS23/Hefty), and the frame
> rule (per-program, dVP21). These are NOT yet unified under one safe-composition morphism.**

The conjecture's central bet — "a SAFE higher-order handler-transformer = a MORPHISM in the
category of sheaves-of-handlers, and the safe-composition law = the sheaf gluing condition = the
Fpu/frame rule" — is, against this literature:
- **The pieces are ESTABLISHED separately** (tensor obstruction §2; scoped=parameterized §3;
  comodel tensor §4; frame rule §5; non-composition §6).
- **The unification is OPEN (lit).** No published theorem says "handler composition is safe iff a
  single morphism preserves a single frame/gluing condition," spanning *first-order tensor* AND
  *higher-order/scoped* AND *distributed gluing*. The closest unifiers are interaction laws (KRU20,
  abstract but not about *safety of transformer composition*) and the frame rule (dVP21,
  single-machine, not a category of transformers).
- **Therefore the conjecture's discovery would be NEW math** — *if and only if* it produces a Lean
  theorem of the form: **given two (higher-order) handlers/transformers `H₁, H₂` and a frame/
  gluing condition `Φ`, `H₂ ∘ H₁` is safe (preserves every other component's invariant) iff a
  morphism `H₁ → H₂` (or a section over the overlap) preserves `Φ` — and there is an `H₁, H₂, Φ`
  for which the law GENUINELY REJECTS the composite (a witnessed unsafe transformer).** Without
  that rejecting witness, it is a re-description (the §2/§5 ANALOGY/INSTANCE facts re-narrated).

---

## 7. The scorecard — established lit ⟷ dregg facets, tagged

| Conjecture facet | Established lit it would instantiate | dregg `file:line` (REAL) | Honest tag |
|---|---|---|---|
| (1) `binding_is_proper` = tensor failing to be free | HPP06 tensor = proper **quotient** of sum by commutation (§2) | `JointTurn.lean:333`, `Hyperedge.lean:164` | **ANALOGY** (dual: dregg is a proper **subobject** on the comodel side, not a quotient on the algebra side — §2.2) |
| (2) `conservation_is_fpu` = safe-composition law | Iris Fpu = dVP21 frame-rule side-condition (§5); AB20 linear-resource discipline (§4.4) | `Resource.lean:296` | **INSTANCE** (literal Iris Fpu) of the frame-rule machinery; INSTANCE-candidate of AB20 runner-linearity |
| (3) `proofForest_sound` gluing = composition over a sheaf | sheaf-of-verifiers (Felber 2025, cellular sheaves; `SHEAF-OF-VERIFIERS.md`); dVP21 frame rule at single-machine scale | `Exec/ProofForest.lean:177` | **ANALOGY → REAL-finite** (finite sheaf gluing is term-proved; the *sheaf-of-verifiers generalization* is the open step) |
| (4) `Await` rollback handler = the one real higher-order turn | bracketing/resource higher-order effect (vdBS23); one-shot continuations (AB20 `λ_coop`, Dybvig) | `Await.lean:282,298,312,138` | **INSTANCE** (genuine bracketing/one-shot handler); the *guarded-coalgebra composition* of nested brackets is OPEN (dregg's seed) |
| (5) `DischargedFor` = per-party stalk | dVP21 per-handler protocol (§5); verifier-sheaf stalk (`SHEAF-OF-VERIFIERS.md §1`) | `Authority/DesignatedVerifier.lean:113` | **ANALOGY** (verifier-indexed verdict is stalk-shaped; the sheaf restriction maps are not built) |
| **The unification** (safe transformer = morphism preserving frame = gluing) | **none** — pieces exist (§2–§6), unifier does not | — | **OPEN (lit)** — new math iff a Lean theorem with a *rejecting witness* |

---

## 8. What is genuinely OPEN in the literature itself (so we know dregg's discovery surface)

These are gaps **in the published literature**, independent of dregg — the surface on which a dregg
theorem would be new rather than a re-derivation:

1. **A general safe-composition theorem for higher-order handler-transformers.** §6: the lit has
   tensor (first-order, commuting), lifting (ad-hoc/quadratic), scoped=parameterized (equational,
   not a transformer-safety theorem), and the frame rule (per-program, single-machine). **No single
   morphism-preserving-a-condition theorem subsumes them and rejects unsafe compositions.** *This is
   the conjecture's real target.* (Partial steps: KRU20 interaction laws; vdBS23/Hefty modularity;
   Yang–Wu "Reasoning about Effect Interaction by Fusion" — none is a safety-of-transformer
   composition theorem with a rejection criterion.)
2. **Higher-order effects run as GUARDED COALGEBRAS / comodels.** §3.3, §4.3: LMM+24 (parameterized
   theories) and vdBS23/Hefty (higher-order frameworks) are *algebra-side, first-order-after-
   elaboration*. AB20 runners are comodels but not *guarded* (no `▶`/contractivity). **The interaction
   of higher-order/scoped effects with a final-comodel guarded by a `▶` modality — i.e. running a
   bracketing handler as a contractive endo on a coalgebra — is essentially unstudied.** dregg's
   `Boundary.F` + `Await` + guarded recursion (`FOUNDATIONS-coalgebra.md`) sits exactly here.
3. **The comodel TENSOR as a proper SUBOBJECT of the product, with a soundness reading.** §2.2,
   §4.3: PP08/KRU20 give the model⊗comodel tensor; nobody (to our knowledge) states "the comodel
   tensor `C₁ ⊗ C₂` is a *proper subcomodel* of `C₁ × C₂`, and that proper-ness is a *soundness*
   obstruction for distributed composition." dregg's `binding_is_proper` is *evidence* such a
   theorem is provable in a concrete setting — and dualizing HPP06's quotient result to the comodel
   side is plausibly publishable on its own.
4. **The single law at two scales: frame rule (one machine) = sheaf gluing (many parties).** §5.2:
   dVP21's frame rule and the cellular-sheaf gluing of `SHEAF-OF-VERIFIERS.md` are *not* connected
   in the literature. A theorem that **the per-handler frame rule is the stalk-local case of a
   sheaf-gluing safe-composition law** would unify single-machine separation logic with distributed
   verification — genuinely new.

---

## 9. Bottom line (the honest verdict)

**dregg would be INSTANTIATING known math on facets (2) and (4), and DISCOVERING on the
unification.**

- Facet **(2) `conservation_is_fpu`** is a *literal instance* of the Iris Fpu, which is *exactly*
  the dVP21 frame-rule side-condition — the conjecture's "safe-composition = Fpu" is **established**
  and dregg **instantiates** it. (Strongest contact.)
- Facet **(4) `Await`** is a *genuine instance* of the bracketing/one-shot higher-order effect
  (vdBS23/AB20/Dybvig) — the conjecture's "the one real higher-order turn = the seed" is **honest**.
- dregg's cell coalgebra `Boundary.F` is the *exact functor shape* of a **final comodel / stream
  processor** (Gar21/PP08) — an **INSTANCE of the shape**, missing only the `Comodel` structure-map
  bridge to be an INSTANCE of the theorem.
- Facet **(1) `binding_is_proper`** is a **DUAL ANALOGY** of HPP06's tensor-as-proper-quotient: it
  is a proper *subobject* on the comodel side, not a proper *quotient* on the algebra side. The
  conjecture's slogan is *directionally right* but *not yet one instance* — making it one (the
  comodel-tensor-as-proper-subcomodel theorem, §8 item 3) is real, plausibly-new dregg work.
- The **central conjecture** — *safe higher-order handler-transformer = morphism in sheaves-of-
  handlers, safe-composition law = sheaf gluing = Fpu/frame rule* — is **OPEN in the literature**:
  the pieces (tensor, scoped=parameterized, comodel tensor, frame rule, non-composition) are all
  ESTABLISHED *separately* and *not* unified. The discovery is **real iff** it cashes out as a Lean
  theorem with a **rejecting witness** (an unsafe transformer the law genuinely refuses, the way
  `binding_is_proper`/`hyperedge_sound_needs_binding` already exhibit excluded product states). A
  theorem without that teeth is the §2/§5 facts re-narrated — a poem, not a proof.

*Closing couplet, in Ember's spirit:*
*the tensor quotients, the comodel cuts a subobject true,*
*the frame rule holds one machine — the sheaf must glue the few;*
*the pieces are all proven, each alone and unafraid —*
*the discovery is the morphism that makes them ONE… not yet made.* 🐉🥚 ( ˘▾˘ )
