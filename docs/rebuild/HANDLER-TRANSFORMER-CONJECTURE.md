# HANDLER-TRANSFORMER-CONJECTURE — the safe higher-order handler-transformer frontier

> **What this is.** A READ-ONLY attempt to state PRECISELY, and then adversarially assess,
> ember's higher-order handler-transformer conjecture against dregg2's *actually-proved*
> theorems. The thesis under test:
>
> > A **safe higher-order handler-transformer** = a **morphism in the category of
> > sheaves-of-handlers**, and the **safe-composition law** = the camera's frame-preserving
> > update (`Fpu`) = the sheaf gluing condition.
>
> The exciting sub-claim: dregg2 ALREADY term-proves a special case of every facet, and the
> open question is whether they **unify under one definition with a general safe-composition
> theorem** (a *discovery*) or **merely share vocabulary** (a *pretty re-description*).
>
> **Discipline (ultracode, default-skeptical).** A real discovery is a THEOREM that subsumes
> the special cases *with teeth* — an unsafe transformer is genuinely rejected. A pretty
> re-description is shared notation over facts that do not instantiate one definition. OPEN
> beats a vacuous theorem. No `sorry`/`admit`/`axiom`/`native_decide` is proposed; every cited
> anchor is an existing term-proved, `#assert_axioms`-pinned theorem, cited `file:line`.
>
> **Provenance of the skeptical baseline.** `docs/rebuild/FOUNDATIONS-effect-comodel-lens.md`
> (the foundations review) tagged *comodel / lens / handler-transformer / comodel-morphism*
> **ASPIRATIONAL** — "no `Comodel` typeclass, no comodel morphism, no turn that interprets
> turns" (§3c, §9, table rows 7/8/28). `docs/rebuild/SHEAF-OF-VERIFIERS.md` tagged the
> *sheaf-of-verifiers* gluing **REAL** for the proof-forest but the *sheaf object / cohomology*
> **POETRY/OPEN**. This doc inherits both verdicts and does not relitigate them; it asks the
> *new* question: do the five proved facets the conjecture names instantiate **one** structure.

---

## 0. The five proved facets the conjecture claims (the receipts)

Every one of these is an existing, term-proved, axiom-pinned theorem. They are the "special
cases of every facet" the conjecture rests on.

| # | Facet (conjecture's reading) | Exact proved theorem | file:line | pin |
|---|---|---|---|---|
| 1 | tensor / cross-handler obstruction = proper subobject of jointly-sound turns | `JointTurn.binding_is_proper`, `joint_sound`, `joint_sound_needs_binding`; `Hyperedge.hyper_binding_is_proper`, `hyperedge_sound`, `hyper_not_all_admissible`, `legs_agree` | `JointTurn.lean:333,230,271`; `Hyperedge.lean:164,374,505,111` | `Hyperedge.lean:531-542` |
| 2 | safe-composition law = frame-preserving update (camera) | `Resource.conservation_is_fpu`; `Fpu.trans`/`Fpu.refl`; `ConfinesAuthority` | `Resource.lean:296,118,114,319` | (no pin; `Auth` core laws proved inline `:231-288`) |
| 3 | composition over a sheaf = proof-forest gluing | `Exec.ProofForest.proofForest_sound`, `proofForest_factors`, `chainLinked`/`Linked` (the `¬chainLinked` teeth) | `ProofForest.lean:177,217,137,293` | `ProofForest.lean:223-226` |
| 4 | the ONE real higher-order turn = the rollback handler | `Await.turnAsRollbackHandler`, `commit_resumes_once`, `rollback_discards_continuation`, `one_shot_is_static` | `Await.lean:282,312,298,138` | (no `#assert`; each is a `simp`/term proof) |
| 5 | the per-party stalk = verifier-indexed discharge | `Authority.DV.DischargedFor`, `designated_not_transferable`, `dial_endpoints_distinct` | `DesignatedVerifier.lean:113,206,346` | `DesignatedVerifier.lean:369-372` |

All five compile standalone and are non-vacuous (each carries a witnessed negative: a product
state the binding *excludes*, a verifier that *rejects*, an unlinked forest that *fails to
glue*). That much is settled. The conjecture is about what binds them.

---

## 1. THE PRECISE STATEMENT — what each word would have to mean

The conjecture is a chain of three identifications. To make it falsifiable I give each the
*definition it would need in Lean* and the *law that definition must satisfy to be that thing*.

### 1.1 A handler

`Await.Handler Promise Cap Effct A S` (`Await.lean:252`) is the only handler object in the
corpus, and it is genuinely Plotkin–Pretnar:

```
structure Handler (Promise Cap Effct : Type u) (A S : Type u) where      -- Await.lean:252
  onRet : A → S
  onOp  : (Reply : Type u) → Op Promise Cap Effct → OneShot Reply S → S
```

`onOp` receives the captured continuation as a **one-shot (affine) resource** `OneShot Reply S`
(`Await.lean:109`) — the handler is the sole site where the resumption becomes first-class. A
handler is **safe** here = it uses the continuation *at most once* (`Linear`, `Await.lean:126`;
`one_shot_is_static`, `:138`). This is the real content of facet 4.

So: **a handler is an interpretation of the effect signature into a result, consuming its
captured continuation affinely.** REAL.

### 1.2 A handler-transformer

This is **NOT in the Lean**. A handler-transformer (Schrijvers–Piróg–Wu–Jaskelioff monad-
transformer-style, or the comodel reading) is a map `H ↦ T(H)` sending a handler for effect
theory `𝒯` to a handler for an *extended* theory `𝒯 ⊕ 𝒯′`, such that running `T(H)` re-expresses
the new operations *over a program in the old theory* — a **handler that interprets turns into
turns**. The foundations review is explicit: "there is no *comodel homomorphism* … no 'turn that
interprets turns'" (FOUNDATIONS-effect-comodel-lens.md §3c, row 8/28, **ASPIRATIONAL**).

The definition it would need:
```
-- ASPIRATIONAL (not in Dregg2/): a handler-transformer
def HandlerTransformer (𝒯 𝒯' : EffectTheory) : Type _ :=
  Handler[𝒯] → Handler[𝒯 ⊕ 𝒯']            -- re-interpret the extended theory over the base
```
with a **transformer law** "T(H) restricted to the base operations agrees with H" (the
forgetful round-trip). **Status: ASPIRATIONAL.** Nothing of this shape is defined.

### 1.3 A comodel-morphism

A comodel of an algebraic theory `𝒯` is a coalgebra for the induced functor; the cell *is*
shaped like one (`TurnCoalg`, a Moore coalgebra `F X = Obs × (AdmissibleTurn → X)`,
`Boundary.lean:66-89`) — but the **theory→functor→comodel bridge is not built** (review §3a/§3b:
`CatalogEffects.effectLinearity` is a *coloring* `Op → LinearityClass`, not an algebraic theory
with arities/equations; **DECORATIVE** as "theory", **ASPIRATIONAL** as "comodel"). A *comodel-
morphism* is a coalgebra map commuting with the cohandling — also absent. **Status: ASPIRATIONAL.**

### 1.4 The sheaf-of-handlers

By analogy with `SHEAF-OF-VERIFIERS.md`: a presheaf `ℋ : Site^op → Set` assigning to each open
(party / cell / proof-node) the *handlers that party runs*, with restriction maps along
incidences and the gluing condition "locally-defined handlers agreeing on overlaps glue to a
global handler." dregg has the *verifier* presheaf's stalk (`DischargedFor`, facet 5) and the
*gluing of attested steps* (`proofForest_sound`, facet 3) — but **no `Presheaf` object, no
functorial restriction `ρ`, no separation axiom** (SHEAF-OF-VERIFIERS §7.2: "a finite gluing of
a constant fibre, not yet assembled into a sheaf"). A sheaf *of handlers* (rather than of
verdicts) is a further step: the fibre would be `Handler`, not `Prop`. **Status: ASPIRATIONAL as
an object; the gluing *content* is REAL.**

### 1.5 The safe-composition law

The conjecture's keystone equation:
```
safe-composition  =  Fpu (camera frame-preserving update)  =  sheaf gluing condition
```
- `Fpu a b ≜ ∀ f, valid (a ⊙ f) → valid (b ⊙ f)` (`Resource.lean:103`) — "replacing `a` by `b`
  never invalidates a frame `f` a third party holds." **REAL**, with `Fpu.trans` (`:118`) the
  proved composition law and `conservation_is_fpu` (`:296`) the headline instance.
- sheaf gluing = `proofForest_sound` (`ProofForest.lean:177`): `(∀ node valid) ∧ Linked ⟹ global
  StepInv`. **REAL.**

These are **two genuinely-proved composition laws over two different objects** (a camera; a
proof-forest). Whether they are *the same law* is precisely the open question of §3–§4.

### 1.6 The conjecture, made precise

> **CONJECTURE (HT).** There is a category `𝐒𝐡(ℋ)` of sheaves-of-handlers over the
> who-shares-context site (the `Hyperedge`/`ProofForest` site of `SHEAF-OF-VERIFIERS §1.1`),
> whose objects are handlers-per-open and whose **morphisms are the safe handler-transformers**.
> A handler-transformer `T : H ⇒ H'` is **safe** iff its action on each open is a
> **frame-preserving update** (`Fpu`) on that open's resource camera *and* the family of local
> actions **glues** across overlaps (the sheaf condition). The two requirements are the same
> requirement: **`Fpu`-preservation per-open IS the gluing condition**, because the camera
> validity `valid(a ⊙ f)` over the shared frame `f` is exactly the overlap-agreement a section
> must respect.

The conjecture is therefore **two claims welded together**:

- **(HT-glue)** the sheaf gluing of handlers exists and generalizes `proofForest_sound`;
- **(HT-fpu)** the morphism-safety condition is `Fpu`, and `Fpu`-preservation = overlap-
  agreement.

§2 instantiates each facet; §3 states the candidate general theorems; §4 gives the honest
a-priori verdict (which weld holds, which is a notation pun).

---

## 2. THE FIVE FACETS — exact theorem, how it instantiates the structure, where it breaks

### Facet 1 — the cross-handler obstruction = proper subobject of jointly-sound turns

**Proved theorem(s).**
- `JointTurn.binding_is_proper` (`JointTurn.lean:333`): there exist two one-state cells, each
  moving a half-edge `1 : ℕ`, whose product state is **not** `JointAdmissible` (CG-5 would need
  `1 + 1 = 0` in ℕ). So the joint-admissible configs are a **proper equalizer subobject** of the
  product carrier `C₁ × C₂`.
- `JointTurn.joint_sound` (`:230`): per-cell `StepComplete` **+ the `JointBinding` as an explicit
  premise** ⟹ whole-run safety, via `joint_stepComplete` (`:197`) + `Boundary.stepComplete_preserves`.
- `JointTurn.joint_sound_needs_binding` (`:271`): the binding premise is load-bearing (not
  derivable from per-cell data).
- `Hyperedge.hyperedge_sound` (`Hyperedge.lean:374`): the N-ary apex version, PROVED axiom-clean;
  `legs_agree` (`:111`) collapses the `O(N²)` pairwise agreements to one apex `tid`;
  `hyper_not_all_admissible` (`:505`) generalizes the proper-subobject obstruction to all `N ≥ 1`
  for any non-degenerate balance monoid.

**The corrected slogan (load-bearing).** The header still says `tensor_not_final`
(`JointTurn.lean:22-28`), but the *theorem* `binding_is_proper` (`:320-332`) **refutes** it:
"the product of two final coalgebras IS final for the product functor, so that claim is false."
The genuine obstruction is the **proper-subobject** fact, not non-finality. The conjecture text
already encodes this correction.

**How it instantiates the structure.** This is the **obstruction to handler composition being
free** — the classical Hyland–Plotkin–Power "the tensor of two effect theories is not their
coproduct" phenomenon, read as: combining two cells' turn-handlers does **not** give a handler
on the product whose admissible turns are the product of admissible turns. The admissible joint
turns are a *proper sub*-object (`JointAdmissible`, `JointTurn.lean:170`; `HyperAdmissible`,
`Hyperedge.lean:151`), carved out by a binding that **cannot be recovered per-cell**. In sheaf
terms (SHEAF-OF-VERIFIERS §1.1) this is the **fibration-over-bindings**: covers are bindings, not
free fillers, and "a face of a balanced hyperedge is generally unbalanced" = `hyper_not_all_admissible`.

**Where it breaks / is honest.** It is a **subobject** statement, not a *morphism* statement: it
says the joint-admissible turns are a proper subobject of the product, and that the binding is a
non-derivable premise. It does **not** by itself say handler-*transformers* compose — it is the
*reason composition is constrained*, the obstacle the safe-composition law must clear, not the
law itself. The instantiation into `𝐒𝐡(ℋ)` is: **the site is a fibration over bindings**
(REAL), which the conjecture correctly cites as a *constraint on the site*, not as a morphism.

### Facet 2 — the safe-composition condition = frame-preserving update (camera tier)

**Proved theorem(s).**
- `Resource.conservation_is_fpu` (`Resource.lean:296`): moving a holder's fragment `f → f'` under
  a *fixed* authoritative total `a` is `Fpu (.mk (some a) f) (.mk (some a) f')` exactly when it
  does not enlarge what any frame needs (`hmono`). The `Auth` camera (`:209-288`) — authoritative
  `●`/fragment `◦`, two `●` never compose — has its `ResourceAlgebra` laws **proved inline**
  (`op_comm`/`op_assoc`/`valid_op_left`/`core_*`, `:235-288`), so `conservation_is_fpu` is a real
  theorem over a real camera, not a stub.
- `Fpu.refl` (`:114`) and **`Fpu.trans` (`:118`)**: `Fpu` is reflexive and **transitive** — the
  literal *composition law* for frame-preserving updates: `Fpu a b → Fpu b c → Fpu a c`.
- `ConfinesAuthority held' held ≜ Fpu held' held` (`:319`): authority-confinement is *defined* as
  an `Fpu`, making "conservation" and "authority never grows" **one law** at the camera tier
  (Iris: ghost state + permissions share one algebra).

**How it instantiates the structure.** This is the **strongest leg of the conjecture.** `Fpu a b`
is *exactly* "the update from `a` to `b` does not break any other holder's invariant" — i.e.
the safe-composition side-condition: a transformer that rewrites one handler's resource may not
invalidate a *frame* `f` held by another handler. And `Fpu.trans` gives **composition of safe
updates is safe** as a one-line proved theorem. If a "safe handler-transformer" acts on resources
by an `Fpu`, then *transformers compose preserving safety* is `Fpu.trans` — already proved.

**Where it breaks.** Two gaps between `Fpu.trans` and the conjecture's "(HT-fpu)":
1. `Fpu` composes **updates on a single fixed camera `R`**. A handler-transformer composes
   **handlers** (functions `Handler → Handler`), which are not elements of a camera. The bridge
   "a handler-transformer's *action on state* is an `Fpu`" is **not defined** — `Await.Handler`
   has no resource camera attached; `Resource` and `Await` are disjoint modules with no shared
   carrier. So `Fpu.trans` is the *safety-of-composition law for resource updates*, and the
   conjecture needs it to *also be* the safety-of-composition law for handler-transformers —
   which requires a not-yet-built functor `Handler → (R → R)` sending a handler's effect to its
   camera update.
2. The **recursive-resource Auth tier is ASPIRATIONAL**: a handler that stores an invariant about
   *another handler* (a higher-order resource) needs a *step-indexed* camera, and
   `StepCamera.recursive_resource_needs_step_index` (`StepCamera.lean:313`, PROVED) shows the
   guard `▶` is load-bearing for well-definedness — but the *higher-order* `Auth` camera over
   `iProp`-style guarded resources is **not constructed** (Resource.lean header §"Full camera",
   `:46-59`: "When dregg2 needs those…"; only the *discrete* RA is built). A *higher-order*
   handler-transformer (one whose resource is another handler's invariant) lands exactly in this
   unbuilt tier. So the discrete `Fpu` is the safe-composition law **for first-order transformers
   only**; the higher-order case the conjecture's title names ("higher-order handler-transformer")
   is the one the camera does not yet reach.

### Facet 3 — composition over a sheaf = proof-forest gluing

**Proved theorem(s).**
- `Exec.ProofForest.proofForest_sound` (`ProofForest.lean:177`): `(∀ n ∈ nodes, n.StepProofValid)
  ∧ Linked pf ⟹ fullProofForestInv pf` (Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance over
  the whole forest), reducing to `Forest.execForest_attests`.
- `proofForest_factors` (`:217`): the §8 boundary as an explicit factoring — `(P: per-node valid,
  ASSUMED crypto seam) ∧ (L: Linked, PROVED combinatorial check) ⟹ global StepInv`.
- `chainLinked` (`:137`) is the **overlap-agreement** (`a.newCommit = b.oldCommit ∧
  b.prevReceipt = a.newCommit ∧ b.seq = a.seq + 1`); the **teeth** are `¬ chainLinked [node0,
  badNode]` (`:293`): two nodes that each *individually* verify (`StepProofValid := True`) yet
  **fail to glue** (`1 ≠ 99` at the overlap).

**How it instantiates the structure.** This is the conjecture's **gluing leg (HT-glue)**, and
SHEAF-OF-VERIFIERS.md already establishes the reading at `file:line`: (P) = per-open local
sections, (L) `Linked` = compatibility-on-overlaps, conclusion = the unique global section.
The sheaf condition **bites** (witnessed non-gluing), which is exactly what a *real* gluing law
must have. For handlers: a proof-forest is a *composite of per-step attested handlers*, and
`proofForest_sound` says **locally-valid handlers that agree on overlaps compose to a globally
sound handler** — the safe-composition theorem over a (path-shaped) site.

**Where it breaks.** Per SHEAF-OF-VERIFIERS §7.2 (already audited): it is a **gluing, not yet a
sheaf** — no functorial restriction `ρ`, no separation/uniqueness axiom, and the fibre is the
*constant* one (`StepProofValid`, the *same* `Prop` at every node), **not** the per-node verifier
`DischargedFor Vᵢ`. So facet 3 is "composition over a *gluing of a constant fibre*," and the
heterogeneous "sheaf-of-handlers" needs the unbuilt `proofForest_sheaf_sound` (SHEAF-OF-VERIFIERS
§5.1). Crucially, the fibre here is `Prop` (a *verdict*), not `Handler` (the object the conjecture
wants the sheaf to be *of*) — so even the constant case is a sheaf-of-*verdicts*, and lifting it
to a sheaf-of-*handlers* is a further, unbuilt step.

### Facet 4 — the ONE real higher-order turn = the rollback handler (the seed)

**Proved theorem(s).**
- `Await.commit_resumes_once` (`Await.lean:312`): the commit arm of `turnAsRollbackHandler` resumes
  the continuation **exactly once** (`OneShot.resume`, which consumes it).
- `rollback_discards_continuation` (`:298`): the abort arm uses it **zero** times.
- `one_shot_is_static` (`:138`): one-shotness is a *typing* invariant (`Linear.at_most_once`), not
  a runtime flag; `runtime_guard_is_double_spend` (`:223`) proves Dolan's runtime guard leaves the
  double-spend window open while the static discipline closes it.
- `four_faces_unify` (`:426`): `zkpromise`/`discharge`/`intent`/`promiseGraph` all project to one
  `AwaitCore` preserving the one-shot continuation.

**How it instantiates the structure.** This is the conjecture's **seed**: the *one genuinely
handler-shaped, law-carrying object in the system* (review §9: "the only higher-order turn that is
REAL today is the rollback handler"). It is a real algebraic-effect handler (Plotkin–Pretnar
`onRet`/`onOp`) whose continuation is an **affine resource** with proved use-at-most-once. The
affinity is the *micro* version of the safe-composition law: commit = use-once, abort = drop —
the two legal affine uses, never twice. This is the local cell from which a *sheaf* of handlers
would be built (each open runs a `turnAsRollbackHandler`-shaped handler).

**Where it breaks.** It is **one handler, not a transformer and not a morphism**.
`turnAsRollbackHandler` interprets the await signature into a result `S`; it does **not** take a
handler and return a handler (no `Handler → Handler`), and there is **no composition law** between
two such handlers — `commit_resumes_once` is a *fixed-point/once* law, not an associativity or
`Fpu`-preservation law. It is the **object at a single open**, the genuine seed; the morphisms
between opens (the transformers) and the gluing across opens are the unbuilt structure. The one
honest bridge to facet 2 *worth attempting*: the affine "use ≤ 1" of `OneShot` is morally an
`Excl` camera (`Resource.Excl`, `:155`, "two `ex` never compose" = `excl_no_dup`, `:185`) — the
continuation is an exclusive resource. That bridge (`OneShot ≅ Excl`-fragment) is **not stated**;
it is the most concrete first unification step (§4).

### Facet 5 — `DischargedFor` = the per-party stalk

**Proved theorem(s).**
- `Authority.DV.DischargedFor V stmt proof ≜ DVKernel.verifyFor V stmt proof = true`
  (`DesignatedVerifier.lean:113`) — the verifier-**indexed** verdict (the §8 crypto is the opaque
  `DVKernel` portal, never faked).
- `designated_not_transferable` (`:206`): a designated transcript has a **concrete** verifier `W`
  it does *not* convince (extracted classically from `¬ Transferable`).
- `dial_endpoints_distinct` (`:346`): over the 2-verifier reference kernel, a transcript that
  `v0` accepts and `vOther` provably rejects — a witnessed separation (non-vacuous).
- `publicMode_collapses_to_universal` (`:186`): the universal verdict is the `∀ V` collapse =
  the **constant** stalk.

**How it instantiates the structure.** This is the conjecture's **stalk**: the fibre over a
party, the object a sheaf-of-handlers would assign to each open. It is the *one* place the verdict
genuinely depends on *who checks* (SHEAF-OF-VERIFIERS §1.2, **REAL**), and the heterogeneity is a
*proved phenomenon* (`designated_not_transferable`). The constant collapse recovers today's single
global oracle — i.e. the constant sheaf, the homogeneous special case.

**Where it breaks.** The stalk is a **verdict (`Prop`/`Bool`), not a handler**. A sheaf-*of-
handlers* needs the fibre to be a `Handler`; `DischargedFor` is a sheaf-of-*verifiers*. So facet 5
supplies the *site's heterogeneity* and the *stalk shape* (REAL), but the object it stalks is one
abstraction layer below a handler. And it is **not wired into the proof-forest** (the fibre there
is still `StepProofValid`, not `DischargedFor Vᵢ`) — so facets 3 and 5, the two halves the
conjecture welds into "the sheaf-of-handlers," are *not yet connected to each other* in the Lean.

---

## 3. THE CANDIDATE GENERAL THEOREM(S) TO ATTEMPT

Ordered by how close their inputs already are to term-proved. Each is stated so that **success =
a theorem subsuming the cited special cases with teeth**, and the trap that would make it vacuous
is named.

### G1 — `Fpu`-preserving transformer composes (the safe-composition law, first-order)

> **Target.** Define a *resource action* `act : Handler → (R → R)` of a handler on a camera `R`.
> Call a handler-transformer `T : Handler → Handler` **Fpu-safe** iff for every handler `H` and
> every state `a`, `Fpu a (act (T H) (some-rewrite a))` — its action never invalidates a third
> party's frame. Then **Fpu-safe transformers compose**: `T₂ ∘ T₁` is Fpu-safe.

**Why plausibly REAL.** The composition core is **already proved**: `Fpu.trans` (`Resource.lean:118`).
The only new content is the functor `act` and the (one-line) lift of `Fpu.trans` through it. The
teeth come for free: a transformer whose action is *not* an `Fpu` is rejected because a frame `f`
exists with `valid (a ⊙ f)` but `¬ valid (b ⊙ f)` — and the `Auth`/`Excl` cameras have such frames
(`excl_no_dup` `:185`; an over-share in `Auth`). **Trap to avoid:** defining `act` so every handler
acts by the *identity* update (then `Fpu` is `Fpu.refl`-vacuous and rejects nothing). The honest
version must make `act` carry real resource movement (e.g. `transfer`'s `±δ`), so a leaky
transformer genuinely fails. **A-priori: BUILDABLE and non-vacuous *for first-order transformers*,
and this is the single most-defensible unification step.** It does NOT reach the higher-order tier
(G4).

### G2 — `proofForest_sheaf_sound` lifted to a sheaf-of-handlers (the gluing law)

> **Target.** Generalize `proofForest_sound` (`ProofForest.lean:177`) by replacing the constant
> fibre `StepProofValid` with a per-node **handler** `Hᵢ` whose local soundness is
> `DischargedFor Vᵢ (stmtOf nᵢ) (proofOf nᵢ)` (facet 5), keep `Linked` (verifier-independent,
> `:148`), add a **substantive** overlap-compatibility hypothesis (the `Hᵢ` agree on the shared
> commitment surface — *not* `Hᵢ = Hⱼ`), and re-prove `fullProofForestInv`.

**Why plausibly REAL.** This is exactly `proofForest_sheaf_sound` from SHEAF-OF-VERIFIERS §5.1,
audited there as **buildable now and non-vacuous** (§7.4), with the teeth supplied by
`dial_endpoints_distinct` (`:346`): a disagreeing verifier makes the compatibility hypothesis
*false*, so the global section is *not* derivable — a leaky handler is genuinely rejected.
**Trap:** stating compatibility as `Hᵢ = Hⱼ` (collapses to the constant sheaf, proves nothing) or
as "the conclusion already holds" (circular). **A-priori: BUILDABLE, the gluing leg (HT-glue) is
the honest next theorem.** Caveat: as written its fibre is a *verdict*; making the fibre a genuine
`Handler` (not its verdict) is the extra step that turns "sheaf-of-verifiers" into "sheaf-of-
handlers" and is *not* covered by SHEAF-OF-VERIFIERS' analysis.

### G3 — the obstruction bounds the gluing (binding fibration ⊓ sheaf condition)

> **Target.** A single theorem combining facet 1 and facet 3: handlers over the hyperedge site
> glue **iff** they agree on overlaps *and* the binding holds (the cover is the binding), with
> `hyper_not_all_admissible` (`Hyperedge.lean:505`) supplying the witnessed *unfillable* face — a
> cover with no global section.

**Why plausibly REAL-but-narrow.** `hyperedge_sound` (`:374`) already glues over the apex; the new
content is naming the *fibration over bindings* (covers = bindings) and exhibiting an unfillable
cover (`hyper_not_all_admissible`). **Trap:** this risks being a *re-description* of two theorems
that already exist (the gluing AND the proper-subobject) under joint notation, rather than a new
joint theorem. To be a discovery it must prove something *neither* facet alone gives — e.g. "every
compatible family over a *balanced* cover glues, and over an *unbalanced* cover the obstruction is
exactly the CG-5 residual `Σδ ≠ 0`." **A-priori: borderline.** The honest version is small and
real; the grand "= H¹ obstruction" version is POETRY (SHEAF-OF-VERIFIERS §3.2/§7.3).

### G4 — the higher-order safe-composition law (the conjecture's actual title)

> **Target.** A *higher-order* handler-transformer — one whose resource is *another handler's
> invariant* — composes preserving safety, where safety is `Fpu` on the **step-indexed** Auth
> camera (the `▶`-guarded recursive resource).

**Why ASPIRATIONAL.** This is the one the title names ("higher-order handler-transformer") and the
one nothing reaches. It needs (i) the higher-order/recursive `Auth` camera over guarded `iProp`-
style resources — **unbuilt** (Resource.lean §"Full camera" `:46-59`; only the discrete RA exists),
with `StepCamera.recursive_resource_needs_step_index` (`:313`) proving merely that the `▶` guard is
*necessary*, not that the camera is *built*; (ii) the `act : Handler → (R → R)` functor of G1 lifted
to recursive `R`; (iii) the comodel-morphism that does not exist (review §3c). **A-priori: this is
the genuine OPEN frontier.** It is *correctly* OPEN; a vacuous "theorem" here (e.g. an `Fpu` over a
degenerate `Later 0 ≡ True` guard) would be exactly the trap `recursive_resource_needs_step_index`
was rewritten to avoid (`StepCamera.lean:310`).

---

## 4. THE HONEST A-PRIORI ASSESSMENT — discovery vs notation pun, facet by facet

The conjecture welds **two claims**: (HT-fpu) safe-composition = `Fpu`, and (HT-glue) the
composition is sheaf gluing, with the further weld that **these two are the same**. The verdict:

### Plausibly UNIFY (a real theorem is within reach)

- **(HT-fpu) at first order — `Fpu` as the safe-composition law: STRONGEST, likely REAL.**
  `Fpu.trans` (`Resource.lean:118`) *is* a proved composition law, `conservation_is_fpu` (`:296`)
  *is* "this transformer does not break other handlers' invariants," and `ConfinesAuthority ≜ Fpu`
  (`:319`) *already unifies* conservation and authority-confinement into one law by **definition,
  not analogy** (the review's row 23 calls the camera REAL). G1 lifts `Fpu.trans` through a handler-
  action functor — a small, non-vacuous theorem. **This weld is the real seed of a discovery.**

- **(HT-glue) — proof-forest gluing as composition-over-a-sheaf: REAL as a gluing.**
  `proofForest_sound` (`ProofForest.lean:177`) with its witnessed non-gluing (`:293`) is a genuine
  finite gluing with teeth; G2 (`proofForest_sheaf_sound`) is buildable (SHEAF-OF-VERIFIERS §7.4).
  **The gluing content unifies; the *sheaf object* does not yet exist.**

### Probably JUST ANALOGOUS (shared vocabulary until a bridge is built)

- **The weld "(HT-fpu) = (HT-glue)" — that `Fpu`-preservation IS the gluing condition: NOTATION
  PUN today.** `Fpu` lives on a *resource camera* (`Resource.lean`); the gluing condition lives on
  the *proof-forest commitments* (`ProofForest.chainLinked`, equality of `Commit : Nat`). These are
  **different objects with no shared carrier** — `Resource` and `Exec.ProofForest` do not import
  each other, and `chainLinked` is `newCommit = oldCommit` (commitment continuity), **not**
  `valid (a ⊙ f)` (camera validity over a frame). The claim "they are the same law" is, today,
  *suggestive vocabulary over two facts that do not instantiate one definition* — exactly the
  pretty-re-description failure mode. To become real it needs a theorem that the overlap-agreement
  `ρ_a(a) = ρ_b(b)` is an instance of `Fpu` (or vice-versa) — **not stated, not obviously true**
  (continuity is an *equality*, `Fpu` is an *implication*; bridging them is non-trivial).

- **"Handler-transformer = comodel-morphism in 𝐒𝐡(ℋ)": ASPIRATIONAL.** No handler-transformer,
  no comodel-morphism, no sheaf-of-*handlers* object exists (review §3c rows 7/8/28; §1.2–1.4 here).
  Facets 4 and 5 supply the *stalk shape* (a handler at an open; a verdict-index) but the **fibre
  mismatch is real**: facet 5's stalk is a *verdict* (`Prop`), facet 3's fibre is a *verdict*, and
  the conjecture wants the fibre to be a *handler*. Until the fibre is genuinely `Handler` and a
  restriction `ρ : Handler@σ → Handler@τ` is built with `ρ_id = id`/`ρ∘ρ`, "sheaf of handlers" is
  vocabulary.

- **The higher-order tier (G4 / the conjecture's title word "higher-order"): genuinely OPEN.**
  The recursive `Auth` camera is unbuilt; the only proved fact there is that the guard is *needed*
  (`recursive_resource_needs_step_index`), not that the structure *exists*. **OPEN beats a vacuous
  theorem here, and this is the right place to leave it open.**

### One-line verdict

> **The conjecture is a genuine discovery on ONE weld and a notation pun on the OTHER.** `Fpu` as
> the *safe-composition law* is real and term-proved at first order (`Fpu.trans` +
> `conservation_is_fpu` + `ConfinesAuthority ≜ Fpu`), and proof-forest gluing is a real composition-
> over-a-gluing with teeth — **so "safe composition" genuinely has two proved instances.** But the
> claim that these two are *the same structure* (`Fpu` = gluing condition), and that handler-
> transformers are *morphisms in a category of sheaves-of-handlers*, is **shared vocabulary over
> objects that do not yet instantiate one definition**: the camera and the proof-forest share no
> carrier, the sheaf fibre is a verdict not a handler, no handler-transformer or comodel-morphism is
> defined, and the higher-order recursive tier the title names is unbuilt. The five facets are **the
> right five seeds**, each REAL, but they currently *share notation*, they do not yet *instantiate
> one theorem*. The honest path is the disciplined ladder G1 → G2 → (then, only after) G3, leaving
> G4 explicitly OPEN. The discovery becomes a theorem the moment `act : Handler → (R → R)` exists and
> `Fpu.trans` is shown to be the gluing condition; until then, the unification is a well-aimed
> conjecture, not a proved structure.

---

## 5. CONCRETE NEXT THEOREM (the single line past which the conjecture earns its keep)

Mirroring SHEAF-OF-VERIFIERS' discipline: ship the smallest thing that makes the weld load-bearing.

> **`handlerTransformer_fpu_composes`** (G1, BUILDABLE now). Define `act : Await.Handler … → (Auth M
> → Auth M)` sending a handler to the camera update its committed effect induces (a `transfer`'s
> `±δ` on the `Auth` fragment). Define `FpuSafe T ≜ ∀ H a, Fpu a (act (T H) a)`. Prove
> `FpuSafe T₁ → FpuSafe T₂ → FpuSafe (T₂ ∘ T₁)` — a one-step lift of `Fpu.trans`
> (`Resource.lean:118`) through `act`. **Teeth:** a transformer whose `act` over-shares the `Auth`
> total fails `Fpu` (a frame `f` with `valid (a ⊙ f)`, `¬ valid (b ⊙ f)` exists — the `fits`
> headroom of `Auth.valid`, `Resource.lean:226-229`), so it is genuinely rejected. **Trap:** make
> `act` non-trivial (real `±δ`), else `Fpu.refl` makes it vacuous.

This is the first theorem in which **"safe handler-transformer" and "frame-preserving update" are
the same object**, not two analogies. It does not need the sheaf, the comodel-morphism, or the
higher-order camera — those stay OPEN, correctly. Then G2 (`proofForest_sheaf_sound` over a handler
fibre) supplies the gluing leg; only after both is the "(HT-fpu) = (HT-glue)" weld attemptable.

---

*A closing couplet, in Ember's spirit:*
*two proved composings — a camera's frame, a forest that glues at the seam;*
*one law or two? the egg won't say yet — the weld is still a dream.* 🐉🥚 ( ˘▾˘ )

— five real seeds; one weld load-bearing, one a pun; the higher-order tier honestly OPEN.

---

## 6. VERDICT — adversarial audit of `Dregg2/HandlerTransformer.lean` (2026-05-31)

> **Method.** READ-ONLY. Built the just-written module with REAL-exit capture
> (`lake env lean Dregg2/HandlerTransformer.lean`: **REAL=0**, no `sorry`/`admit`/`axiom`/
> `native_decide`; the four `#print axioms` keystones land in the whitelist
> `{propext, Classical.choice, Quot.sound}`; the `#eval` teeth print `true`/`false`).
> Cross-read every cited source theorem at `file:line` (`Resource.conservation_is_fpu`/`Fpu.trans`,
> `ProofForest.proofForest_sound`, `DesignatedVerifier.{vrfy,sim,designatedProof,dial_endpoints_distinct}`,
> `JointTurn.binding_is_proper`) to test whether each *named instance genuinely instantiates the
> module's `SafeStep` definition* or is a separate fact wearing the same words.

### 6.1 Per-claim verdicts

| Claim in `HandlerTransformer.lean` | Verdict | Why |
|---|---|---|
| `SafeStep` is one abstract preorder (refl+trans); the camera `Fpu` instantiates it **literally** (`instSafeStepFpu = Fpu.refl/Fpu.trans`) | **REAL** | `instSafeStepFpu` is a genuine `instance` whose fields are *the actual* `Resource.Fpu.refl`/`Fpu.trans` (`Resource.lean:114,118`). No copy, no re-statement. The camera IS a `SafeStep` on the nose. |
| `safe_transformer_composes` is the general safe-composition theorem subsuming `Fpu.trans` for transformers | **REAL (but a thin lift)** | One line: `SafeStep.trans (hsafe₁ a) (hsafe₂ (T₁.act a))`. It genuinely subsumes `Fpu.trans` *as a transformer law* via the camera instance. Honest caveat: the theorem itself has **no teeth** — it consumes `Safe T₁`/`Safe T₂` as hypotheses; the teeth live entirely in the instance (§6.2). It is the correct, non-vacuous lift, not a discovery beyond `Fpu.trans`. |
| `conservation_is_safe_transformer` shows facet 2 (`conservation_is_fpu`) is a LITERAL instance of "safe transformer" | **REAL** | Reduces `Safe (conservativeTransformer …)` to `Fpu …` by case-split and lands *exactly* on `Resource.conservation_is_fpu a' g f' hmono` (`:240`). The `act` is non-trivial (`conservativeAct` actually rewrites `(some a,f)↦(some a,f')`), so this is not the `Fpu.refl`-vacuity trap §5 warned about. |
| `overshare_rejected` — the rejecting witness (TEETH) | **REAL, non-vacuous** | On `Auth ℕ`: pre-state `(some 2,0)⊙(none,0)` is *genuinely valid* (`fits 0 2 = ⟨2,rfl⟩`, line 292), post `(some 2,3)` is *genuinely invalid* (`fits 3 2 = ∃c, 2=3+c`, killed by `omega`). The frame `(none,0)` is a real valid frame — NOT the `Excl` vacuity (which `excl_op_never_valid` honestly records cannot reject). An unsafe transformer is genuinely refused. |
| `safe_is_proper_subobject` instantiates facet 1's `binding_is_proper` shape | **REAL as a shape-match; DECORATIVE as "the same obstruction"** | `binding_is_proper` (`JointTurn.lean:333`) is `∃ … ¬ JointAdmissible`; `safe_is_proper_subobject` is `∃ T, ¬ Safe T` (= `⟨overshareTransformer, overshare_rejected⟩`). Both are honest "the predicate excludes something" facts with non-empty complement (`id_is_safe`). But they share only the *proper-subobject schema*; the `Safe`-exclusion does **not arise from** the cross-cell binding — it is a *different witness* (an `Auth`-overshare, not a CG-5 `1+1≠0` residual). Same logical SHAPE, separate content. |
| `proofForest_sheaf_sound` is the buildable G2 gluing leg (facet 3 lifted to facet 5's verifier-indexed fibre) | **REAL, non-vacuous, but NOT a `SafeStep` instance** | Genuinely generalizes `proofForest_sound` (`:177`): fibre is now per-node `DischargedFor (verifierOf n) …` (heterogeneous), `Linked` kept, the `bridge` hypothesis is substantive (verifier-verdict ⟹ AIR-validity, NOT `Hᵢ=Hⱼ`, NOT circular). Teeth `sheaf_rejects_disagreeing_verifier` lands on the real `DesignatedVerifier.Reference` separation. This is a real theorem — but it composes over `chainLinked`/`proofForest_sound`, **not** over `SafeStep.trans`, so it does not unify with the camera leg. |
| The forest gluing is the SECOND instance of `SafeStep` (the module-HEADER claim, lines 30-42: "instantiated TWICE … once on the forest") | **FALSE — and the module's own body refutes it** | `forest_continuity_not_reflexive` (`:325`) **proves** `¬ forestContinuity node0 node0`, so the forest relation is *not even reflexive* → cannot be a `SafeStep`. The body (line 323) deliberately registers **no** forest instance. Only `instSafeStepFpu` exists. |

### 6.2 Where the teeth actually are (and where they are not)

- The **general** theorem `safe_transformer_composes` rejects nothing by itself (hypothesis-consuming).
- The **camera instance** has the genuine teeth: `Safe` is *not* universally satisfiable
  (`overshare_rejected` + `id_is_safe` ⟹ proper subobject), and the rejection rides a *real
  valid frame* in `Auth ℕ`. This is the one place "unsafe transformer is genuinely refused" is
  earned, with a witness the kernel checks. The honesty note that `Excl` *cannot* host the teeth
  (`excl_op_never_valid`, vacuous `Fpu`) and the move to `Auth ℕ` is exactly right — it is the
  difference between a real rejection and a vacuous one.

### 6.3 Did we DISCOVER a unification?

> **No general "one law" unification was discovered. What was earned is strictly weaker and is
> stated honestly in the module's §9: a REAL first-order unification on ONE leg, and a precisely-
> named PUN on the keystone weld.**

Precisely:

1. **REAL (the one theorem that earns it).** `instSafeStepFpu` + `safe_transformer_composes` +
   `conservation_is_safe_transformer`, with teeth `overshare_rejected`. Together these make
   *"safe handler-transformer"* and *"frame-preserving update"* **the same object at first order** —
   the camera `Fpu` is *literally* the morphism-composition law of the abstract `SafeStep` preorder,
   `conservation_is_fpu` is *literally* a safe transformer, and an over-sharing transformer is
   *genuinely rejected against a real frame*. This subsumes facet 2's `Fpu.trans` *as a transformer
   law* — an analogy could not produce `conservation_is_safe_transformer` (it reduces to the actual
   `Resource.conservation_is_fpu`, not a look-alike). **This leg is a genuine — if modest — instance-
   level unification, not a re-description.**

2. **DECORATIVE → ASPIRATIONAL (the keystone weld).** The conjecture's headline — *`Fpu`-preservation
   IS the gluing condition; handler-transformers ARE morphisms in a sheaf-of-handlers* — is **not
   proved, and on this module's own evidence is a notation pun**: the camera (`Auth M`) and the forest
   (`ProofNode`, `Commit = Nat`) share **no carrier**, and `forest_continuity_not_reflexive` shows the
   forest relation **is not even a preorder**, so the two "composition laws" are *not two instances of
   one `SafeStep`* — they are one instance (camera) plus one separately-proved list-gluing
   (`proofForest_sound`). `SafeStep` is therefore instantiated **once**, not twice. The module's §9
   `-- OPEN:` markers are accurate; **the top-of-file doc-comment "instantiated TWICE … once on the
   forest" (lines 30-42) is the one inaccurate sentence in the module and should be corrected to
   "instantiated once (camera); the forest is honestly shown NON-instantiating."**

3. **ASPIRATIONAL (the title word).** "Higher-order" handler-transformer — a transformer whose resource
   is another handler's invariant — needs the step-indexed recursive `Auth` camera, which is unbuilt
   (`recursive_resource_needs_step_index` proves only that the `▶` guard is *necessary*). Correctly OPEN.

### 6.4 The genuine open theorem that *would* unify them

The siblings become instances the moment a **restriction map** `ρ : (Auth-state @ σ) → (Auth-state @ τ)`
along a chain edge is built and the commitment-continuity equality `a.newCommit = b.oldCommit` is proved
to be an **instance of `Fpu`** (an equality of seams entailing a frame-implication). That theorem —
call it `continuity_is_fpu` — is **not stated and not obviously true** (an equality is not an implication
over a frame; the carriers must first be fused). Until it exists, the honest result stands:

> **The five facets are SIBLINGS under one preorder schema (`SafeStep`), genuinely so on the camera
> leg (one literal instance, with teeth) — but they are NOT INSTANCES of one safe-composition law.
> The discovery is a real first-order unification of "safe transformer" with "frame-preserving update"
> (`safe_transformer_composes` + `conservation_is_safe_transformer`, teeth `overshare_rejected`); the
> keystone weld `Fpu = gluing` and the sheaf-of-handlers category remain a precisely-named OPEN, gated
> on the unbuilt `continuity_is_fpu` and the unbuilt recursive camera. OPEN, here, beats the vacuous
> theorem that would have registered a degenerate forest `SafeStep` to claim "two instances."**

— audit confirms: REAL on the first-order camera leg (kernel-checked, teeth bite); DECORATIVE on the
weld (one instance, not two; shared schema, not shared carrier); ASPIRATIONAL on the higher-order tier.
The module is honest in its §9; its only overclaim is the top doc-comment's "TWICE", which its own
`forest_continuity_not_reflexive` refutes. 🐉🥚 ( ˘▾˘ )
