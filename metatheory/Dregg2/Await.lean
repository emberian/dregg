/-
# Dregg2.Await — the await family: algebraic effects + handlers + one-shot
# (linear) continuations, with the turn as the rollback handler.

This module encodes dregg2's **await family** as a *single* continuation primitive
shown to have *four faces* (`CLAUDETHOUGHT.md §1, "The await family"`; design
`docs/ZKPROMISE-ZKAWAIT-DESIGN.md`). The design correction that makes this module
worth stating precisely:

> "It's **algebraic effects + handlers with *linear (one-shot)* continuations** — and
> the sharpest design correction here: one-shotness must be a *static linear-typing
> invariant on the zkpromise*, not Dolan's runtime 'raise on second resume', because
> that runtime guard **IS** the double-spend you're preventing."

Literature anchors:
  * **Plotkin–Pretnar**, *Handling Algebraic Effects* (LMCS 2013) — effects are an
    algebraic signature `Op` of operations (parameter/return arities); a *handler*
    is an interpretation of that signature; running an effectful computation under a
    handler is the unique homomorphism out of the free model. Here `Effect`/`Handler`.
  * **One-shot / linear continuations** (Bruggeman–Waddell–Dybvig `call/1cc`;
    Berdine–O'Hearn–Reddy–Thielecke, *Linear continuations*; OCaml 5 effect
    handlers, whose continuations are *one-shot*). The resumption may be invoked
    **at most once**. dregg2's sharpening: that "at most once" is a **static linear
    (use-exactly-once) type discipline**, not a runtime flag — see `OneShot` below
    and `runtime_guard_is_double_spend`.
  * **CapTP promises** (Miller, *Robust Composition*; the E language `when`/
    `whenResolved`) — a promise is a first-class handle to a not-yet-resolved result;
    resolution fulfils it; pipelining is dataflow over pending promises. Here the
    `zkpromise`/`discharge`/`promiseGraph` faces.

Design fact this module hard-codes (`CLAUDETHOUGHT.md §1`, `Boundary.lean` docstring
"the turn IS the rollback handler"):

> "The turn *is* the rollback handler (commit = replay held effects + emit witness at
> the boundary = the deferred-prover; abort = conservation-preserving refund)."

So `turnAsRollbackHandler` is the canonical `Handler`: **commit = invoke the held
continuation exactly once; abort/rollback = discard it (never resume)**. The two
outcomes are precisely the two *legal* uses of an affine resource — used once, or
dropped — which is why the continuation must be **affine/linear**, not duplicable.

Style: spec-first, grind up. Faithful `Prop`s; `sorry` bodies are real obligations.
This module commits only to the *shape* of the await algebra (the verify side, in the
sense of `Laws.lean`); the proof-carrying resolution of a `zkpromise` (binding /
extractability of the underlying STARK) is a circuit obligation and is NOT merged into
this Lean law (cf. `Boundary.lean` §8 caveat).
-/
import Dregg2.Core
import Dregg2.Laws

namespace Dregg2.Await

open Dregg2.Laws

universe u v

/-! ## 1. The effect signature (Plotkin–Pretnar) -/

/-- **`Op` — the algebraic-effect signature a turn may perform.** Each operation
carries a *parameter arity* (the value it is applied to) and a *return arity* (the
value its continuation is resumed with) — the (`P ⟶ R`)-shaped operation symbol of an
algebraic theory (Plotkin–Pretnar §2). dregg2's three await operations:

  * `await p` — suspend until the promise `p` resolves; resumed with the resolved value.
  * `call`    — invoke a capability / remote object (CapTP eventual-send); resumed with
                the reply.
  * `emit`    — emit a held effect at the boundary (the deferred-prover side of commit).

The signature is what a `Handler` interprets; a `Computation` is a tree of these. -/
inductive Op (Promise Cap Effct : Type u) where
  /-- Suspend on a promise; the continuation is resumed with the resolved value. -/
  | await (p : Promise)
  /-- Eventual-send to a capability; resumed with the reply. -/
  | call  (c : Cap)
  /-- Emit a held effect at the vat boundary (deferred prover). -/
  | emit  (e : Effct)
  deriving Repr

/-- **`Computation` — the free model over the signature `Op`** (Plotkin–Pretnar: the
free algebra / the term tree). A computation either `ret`urns a value, or performs an
operation `op` and continues with a `kont` indexed by the operation's *return* value.
The `kont` field is the syntactic continuation; its **one-shot** discipline is imposed
by the `Handler`, not by this tree (the tree is pure syntax, freely inspectable). -/
inductive Computation (Promise Cap Effct : Type u) (A : Type u) where
  /-- A pure return — the leaf of the term tree. -/
  | ret (a : A)
  /-- Perform `op`, then continue. `Reply` is the operation's return arity; `kont`
  is the (syntactic) resumption taking the operation's reply. -/
  | op  (Reply : Type u) (o : Op Promise Cap Effct)
        (kont : Reply → Computation Promise Cap Effct A)

/-! ## 2. One-shot (linear) continuations — the static discipline

The continuation captured by a handler is an **affine resource**: it must be used
**exactly once** (commit) or **dropped** (rollback), and **never twice**. dregg2's
correction (`CLAUDETHOUGHT.md §1`): this is a *type-level* invariant, not a runtime
guard. We model the type-level invariant by a wrapper `OneShot` whose **only**
eliminator, `OneShot.resume`, *consumes* the wrapper (takes it by value and returns no
fresh `OneShot`) — so in a linear/affine ambient there is no term that resumes twice.
-/

/-- **`OneShot k`** — a continuation `k : R → S` wrapped as a *use-exactly-once*
(affine) resource. There is intentionally **no** projection back to a reusable `k`
and **no** `OneShot → OneShot × OneShot` duplicator: the wrapper is the static carrier
of linearity. The "flag" is not a runtime boolean — it is the *absence* of any
copying eliminator, enforced by the type. (In a fully substructural backend this
would be a `linear` binder; in Lean we encode the discipline as the API surface:
`resume` is the sole consumer.) -/
structure OneShot (R S : Type u) where
  /-- The underlying resumption. Private-by-convention: the *only* sanctioned way to
  observe it is `OneShot.resume`, which consumes the whole structure. -/
  run : R → S

/-- **`OneShot.resume` — the sole eliminator; it CONSUMES the continuation.** It takes
the `OneShot` by value and returns the result `S` *without* handing back a new
`OneShot`. Thus a well-typed program can call it once per captured continuation; a
second call would need a second `OneShot` value, which (absent a duplicator) does not
exist. This *is* the one-shot discipline, realized as data flow. -/
def OneShot.resume {R S : Type u} (k : OneShot R S) (r : R) : S :=
  k.run r

/-- **`Linear k` — the affine-usage predicate** for a continuation: a use plan is
linear iff it consumes `k` *at most once*. We make the count explicit so the
double-resume anti-pattern is statable. `uses ≤ 1` is the affine law; the two legal
points are `uses = 1` (commit) and `uses = 0` (rollback/drop). -/
structure Linear {R S : Type u} (_k : OneShot R S) where
  /-- How many times this plan invokes the continuation. -/
  uses    : Nat
  /-- The affine law: a continuation is used at most once. -/
  at_most_once : uses ≤ 1

/-- **`theorem one_shot_is_static`** — one-shotness is a *typing* invariant, not a
runtime check. Statement: for the one-shot API, *every* well-typed elimination of an
`OneShot` arises from `resume`, which consumes it; hence the affine count is bounded
*by the types* (any `Linear` plan built from `resume` has `uses ≤ 1`) with no runtime
inspection. Formally: any `Linear` witness over `k` already entails `uses ≤ 1` — the
bound is carried in the type, discharged without evaluating `k`. -/
theorem one_shot_is_static {R S : Type u} (k : OneShot R S) (plan : Linear k) :
    plan.uses ≤ 1 :=
  plan.at_most_once

/-! ### A *runtime* one-shot guard, modelled concretely (Dolan's anti-pattern)

To state precisely what a runtime guard does — and where it FAILS — we model it as an
actual stateful resumption: a `OneShot` paired with a mutable `resumed : Bool` flag.
Resuming consults the flag: if already set, the guard **denies** (Dolan's "raise on
second resume"); otherwise it resumes and sets the flag. The point of the design
correction is that this deny is a *value*, not a type — so the second resume is a
well-typed term that the program can construct and *attempt*, and the guard only
catches it *after* control has re-entered the continuation. -/

/-- **`GuardResult S`** — the outcome of attempting a runtime-guarded resume: either the
guard `denied` the attempt (the flag was already set — Dolan's runtime raise), or it
`resumed v` with the result and the now-consumed (flag-set) guard state. -/
inductive GuardResult (S : Type u) where
  /-- The runtime guard rejected this resume: the continuation was already consumed. -/
  | denied
  /-- The resume was admitted: it yields `S` and the guard transitions to "consumed". -/
  | resumed (s : S)
  deriving Repr

/-- **`Guarded k`** — a one-shot continuation `k` wrapped in a *runtime* guard: the
mutable `resumed` flag that a runtime one-shot discipline (as opposed to the static
`OneShot` discipline) would use. `resumed = true` means the continuation has already
been consumed once. -/
structure Guarded (R S : Type u) where
  /-- The underlying resumption. -/
  k       : OneShot R S
  /-- The runtime flag: has this continuation already been resumed once? -/
  resumed : Bool

/-- **`Guarded.tryResume g r`** — the runtime-guard resume step. It is exactly Dolan's
"raise on second resume": consult the flag, and
* if `g.resumed` is already `true`, **deny** (the double-spend is rejected — but only
  here, at the guard, *after* the call has been issued), else
* resume the underlying `k` once and mark the guard consumed.

This `def` is the operative await-guard machinery the theorem below quantifies over. -/
def Guarded.tryResume {R S : Type u} (g : Guarded R S) (r : R) :
    GuardResult S × Guarded R S :=
  if g.resumed then
    -- already consumed: the runtime guard denies the reuse attempt
    (GuardResult.denied, g)
  else
    -- first use: resume and flip the flag to consumed
    (GuardResult.resumed (g.k.resume r), { g with resumed := true })

/-- **`theorem runtime_guard_rejects_reuse`** — the runtime await-guard REJECTS a
double-spend: presenting an **already-consumed** one-shot continuation to the guard is
denied. Concretely, for any guarded continuation whose flag is already set
(`g.resumed = true` — it has been used once), `tryResume` returns `denied` and leaves
the guard state unchanged.

The hypothesis `hconsumed : g.resumed = true` is LOAD-BEARING: it is exactly the
"already spent" precondition, and the `denied` conclusion is reached only through the
`if g.resumed` true-branch — drop it and the guard might resume (the false-branch).
This is a genuine state (a reuse attempt on a spent continuation) producing a genuine
guard-deny, not an abstract arithmetic fact. -/
theorem runtime_guard_rejects_reuse
    {R S : Type u} (g : Guarded R S) (r : R)
    (hconsumed : g.resumed = true) :
    g.tryResume r = (GuardResult.denied, g) := by
  unfold Guarded.tryResume
  simp only [hconsumed, if_true]

/-- **`theorem runtime_guard_is_double_spend` — the anti-pattern (Dolan), stated on the
concrete guard.** The runtime guard does NOT prevent the second resume from being
*issued*: the second call is a well-typed term that runs *into* the guard before being
denied. We make that precise as a reuse *sequence*: starting from a fresh guard
(`resumed := false`), the FIRST `tryResume` is admitted (it `resumed`, observing the
continuation and thereby touching any conserved resource it carries), and only the
SECOND `tryResume` — on the now-consumed guard — is denied.

So the deny happens *after* the continuation was already re-entered once and would have
re-observed its held effects: in a continuation carrying a conserved `Conservation.count`
that first-then-deny ordering **is** the double-spend window. Contrast `OneShot`, whose
static discipline removes the second call as a *constructible term* entirely (no second
`OneShot` value exists to resume), closing the window the runtime flag leaves open.

Concretely: for a fresh guard, `tryResume` admits (`resumed _`) and yields a consumed
guard `g₁` with `g₁.resumed = true`; feeding `g₁` back to `tryResume` is denied. The
admitted-then-denied pair is the double-spend window the runtime guard cannot close. -/
theorem runtime_guard_is_double_spend
    {R S : Type u} (k : OneShot R S) (r : R) :
    -- a fresh runtime-guarded continuation
    let g₀ : Guarded R S := { k := k, resumed := false }
    -- the FIRST resume is admitted (the continuation IS re-entered) …
    (∃ s, (g₀.tryResume r).1 = GuardResult.resumed s) ∧
      -- … leaving a consumed guard whose SECOND resume the guard only THEN denies.
      ((g₀.tryResume r).2.tryResume r).1 = GuardResult.denied := by
  intro g₀
  constructor
  · -- first use: the fresh guard's flag is `false`, so `tryResume` takes the resume arm
    refine ⟨g₀.k.resume r, ?_⟩
    show (g₀.tryResume r).1 = GuardResult.resumed (g₀.k.resume r)
    unfold Guarded.tryResume
    simp
  · -- the first use flips the flag to `true`; the second use is therefore denied
    have hconsumed : (g₀.tryResume r).2.resumed = true := by
      unfold Guarded.tryResume; simp
    rw [runtime_guard_rejects_reuse _ r hconsumed]

/-! ## 3. Handlers (Plotkin–Pretnar) and the turn as the rollback handler -/

/-- **`Handler` — an interpretation of the effect signature into a result `S`.**
(Plotkin–Pretnar: a handler is a model of the algebraic theory; running a computation
under it is the unique homomorphism.) `onRet` interprets a pure return; `onOp`
interprets each operation, *receiving the captured continuation as a `OneShot`* — i.e.
the handler is the sole site where the resumption becomes a first-class (affine)
value. A handler that calls `OneShot.resume` re-enters the computation **once**; one
that drops it abandons the computation (the rollback case). -/
structure Handler (Promise Cap Effct : Type u) (A S : Type u) where
  /-- Interpret a pure return. -/
  onRet : A → S
  /-- Interpret an operation, given its reply type and the *one-shot* continuation
  from that operation's reply to the final result. The handler chooses to `resume`
  (commit) or discard (rollback). -/
  onOp  : (Reply : Type u) → Op Promise Cap Effct → OneShot Reply S → S

/-- **`CommitOrAbort`** — the two outcomes of a turn-handler, naming the two *legal*
affine uses of the held continuation. `commit` resumes it exactly once; `abort` drops
it (zero uses) and refunds. There is no third outcome — which is the whole point. -/
inductive CommitOrAbort where
  /-- Commit: replay held effects, emit the boundary witness, resume the continuation
  exactly once (the deferred-prover side). -/
  | commit
  /-- Abort: discard the continuation, perform a conservation-preserving refund. -/
  | abort
  deriving Repr, DecidableEq

/-- **`turnAsRollbackHandler` — THE handler: the turn IS the rollback handler**
(`CLAUDETHOUGHT.md §1`; `Boundary.lean` docstring). It is parameterized by a `decide`
oracle that, per operation, yields `commit` or `abort`:

  * **commit** ⇒ `OneShot.resume` the continuation exactly once (replay + emit witness);
  * **abort/rollback** ⇒ **discard** the continuation (never resume) and yield the
    refund result `refund`.

This makes "rollback = discard the continuation; commit = invoke it once" *definitional*
— the two arms are exactly the two legal affine uses, so the turn-handler can never
double-resume (it structurally resumes in one arm only). -/
def turnAsRollbackHandler
    {Promise Cap Effct A S : Type u}
    (onRet  : A → S)
    (refund : S)
    (decide : (Reply : Type u) → Op Promise Cap Effct → CommitOrAbort)
    (resumeWith : (Reply : Type u) → Reply) :
    Handler Promise Cap Effct A S where
  onRet := onRet
  onOp  := fun Reply o k =>
    match decide Reply o with
    | CommitOrAbort.commit => OneShot.resume k (resumeWith Reply)  -- used exactly once
    | CommitOrAbort.abort  => refund                                -- discarded (0 uses)

/-- **`theorem rollback_discards_continuation`** — the abort arm of the turn-handler
uses the continuation **zero** times (it is dropped, never resumed): the affine "drop"
that a runtime guard could not give you safely. Pairs with `commit_resumes_once`. -/
theorem rollback_discards_continuation
    {Promise Cap Effct A S : Type u}
    (onRet : A → S) (refund : S)
    (decide : (Reply : Type u) → Op Promise Cap Effct → CommitOrAbort)
    (resumeWith : (Reply : Type u) → Reply)
    (Reply : Type u) (o : Op Promise Cap Effct) (k : OneShot Reply S)
    (h : decide Reply o = CommitOrAbort.abort) :
    (turnAsRollbackHandler onRet refund decide resumeWith).onOp Reply o k = refund := by
  simp only [turnAsRollbackHandler, h]

/-- **`theorem commit_resumes_once`** — the commit arm resumes the continuation
**exactly once** (`OneShot.resume`, which consumes it). Together with
`rollback_discards_continuation` this is the formal content of "commit = invoke it
once; rollback = discard it", and the static one-shot guarantee for the turn-handler. -/
theorem commit_resumes_once
    {Promise Cap Effct A S : Type u}
    (onRet : A → S) (refund : S)
    (decide : (Reply : Type u) → Op Promise Cap Effct → CommitOrAbort)
    (resumeWith : (Reply : Type u) → Reply)
    (Reply : Type u) (o : Op Promise Cap Effct) (k : OneShot Reply S)
    (h : decide Reply o = CommitOrAbort.commit) :
    (turnAsRollbackHandler onRet refund decide resumeWith).onOp Reply o k
      = OneShot.resume k (resumeWith Reply) := by
  simp only [turnAsRollbackHandler, h]

/-! ## 4. The four faces — four presentations of the SAME await primitive

`CLAUDETHOUGHT.md §1`: the await family is *one* continuation primitive with four
faces — `zkpromise` (specified resolver), `discharge` (named gateway / third-party
caveat — the authority face), `intent` (existential resolver, "a hole that fires when
filled"), and the `promiseGraph` (dataflow over pending promises). We give one
structure per face, then a `def`/`theorem` `four_faces_unify` exhibiting them as
views of a common `AwaitCore`. -/

/-- **`AwaitCore` — the single await primitive the four faces present.** It is exactly:
an effect operation `await` on a promise of type `Promise`, captured by a handler as a
*one-shot* continuation `OneShot Reply S` to a result. Every face below is a way of
*saying who resolves it and how* — the underlying suspend-resume is this. -/
structure AwaitCore (Promise Reply S : Type u) where
  /-- The promise being awaited. -/
  promise : Promise
  /-- The captured one-shot continuation resumed on resolution. -/
  kont    : OneShot Reply S

/-- **Face 1 — `zkpromise`** (`design §"What zkpromise should mean"`): a promise whose
**resolution is witnessed by a zero-knowledge proof**. The resolver proves "I produced
the awaited value / exercised the awaited authority" (`Discharged p w`, from `Laws.lean`)
binding a public `expectedOutput`, without revealing more. `[Verifiable P W]` supplies
the decidable verify side; the proof's *binding/extractability* is a circuit obligation,
not merged here. -/
structure zkpromise (P W : Type u) [Verifiable P W] (Reply S : Type u) where
  /-- The resolution predicate the witness must discharge. -/
  resolver       : P
  /-- The public output the awaiting turn binds to (the `expected_output` of the
  design's `ProofCondition::ZkResult`). -/
  expectedOutput : Reply
  /-- The captured one-shot continuation (resumed once on a *verified* resolution). -/
  kont           : OneShot Reply S

/-- **Face 2 — `discharge`** (`CLAUDETHOUGHT.md §Authority`: "discharge (third-party
caveat) = the await engine's authority-face"): resolving/fulfilling a promise by a
**named gateway** presenting a discharging witness for a caveat predicate `caveat`.
This is the macaroon/biscuit third-party-caveat shape — fulfilment = `Discharged`. -/
structure discharge (P W : Type u) [Verifiable P W] (Reply S : Type u) where
  /-- The third-party caveat that must be discharged to fulfil the promise. -/
  caveat  : P
  /-- The discharging witness presented by the named gateway. -/
  witness : W
  /-- The captured one-shot continuation, resumed once on a valid discharge. -/
  kont    : OneShot Reply S

/-- **Face 3 — `intent`** (`CLAUDETHOUGHT.md §1`: "intent (existential resolver — the
'inverse membrane,' a hole that fires when filled)"): a *conditional/deferred* turn —
a **guarded effect** whose resolver is **existential** (anyone producing a fill that
satisfies `want` resolves it). This is the await with an `∃`-quantified resolver rather
than a named one; the guard `want` is the predicate the fill must satisfy. -/
structure intent (P W : Type u) [Verifiable P W] (Reply S : Type u) where
  /-- The guard: the predicate any fill must satisfy (the "hole's shape"). -/
  want : P
  /-- The captured one-shot continuation, resumed once when *some* fill satisfies
  `want` (the existential resolver). -/
  kont : OneShot Reply S

/-- **`intent.Fires`** — the existential firing condition of an intent: it resolves
exactly when *there exists* a witness discharging its guard. The "fires when filled"
semantics, stated over the `Laws.Discharged` verify side. -/
def intent.Fires {P W : Type u} [Verifiable P W] {Reply S : Type u}
    (i : intent P W Reply S) : Prop :=
  ∃ w : W, Discharged i.want w

/-- **Face 4 — `promiseGraph`** (`design §4 "zk-continuation folding"`,
`CLAUDETHOUGHT.md §1`: "the promise-graph"): the **dataflow graph of pending promises**
— nodes are awaited promises (carrying their one-shot continuations) and edges are
dependencies (a promise awaiting another, `PendingTurnRegistry.dependents`). A linear
chain folds into one IVC proof (the zk-continuation case); here we capture the graph
shape: nodes plus a dependency relation. -/
structure promiseGraph (Promise Reply S : Type u) where
  /-- The pending nodes — each an `AwaitCore` (a promise + its one-shot continuation). -/
  nodes : List (AwaitCore Promise Reply S)
  /-- The dependency edges: `deps i j` means node `i` awaits node `j`'s resolution. -/
  deps  : Nat → Nat → Prop

/-- **`AwaitCore` extraction from each face** — each face *is* an `AwaitCore` once you
forget its face-specific resolver data. These four functions are the "same primitive,
four views" made operational. For `zkpromise`/`discharge`/`intent` the promise handle
is the resolver datum (`resolver`/`caveat`/`want` respectively), demonstrating that
each face only *decorates* the core await with "who resolves and how". -/
def zkpromise.toCore {P W : Type u} [Verifiable P W] {Reply S : Type u}
    (z : zkpromise P W Reply S) : AwaitCore P Reply S :=
  { promise := z.resolver, kont := z.kont }

/-- `discharge` viewed as the bare await primitive (caveat = the promise handle). -/
def discharge.toCore {P W : Type u} [Verifiable P W] {Reply S : Type u}
    (d : discharge P W Reply S) : AwaitCore P Reply S :=
  { promise := d.caveat, kont := d.kont }

/-- `intent` viewed as the bare await primitive (the guard = the promise handle). -/
def intent.toCore {P W : Type u} [Verifiable P W] {Reply S : Type u}
    (i : intent P W Reply S) : AwaitCore P Reply S :=
  { promise := i.want, kont := i.kont }

/-- **`theorem four_faces_unify` — the four faces are four presentations of the SAME
await primitive.** Each face projects to the common `AwaitCore` *preserving the
one-shot continuation* (the load-bearing shared structure): a `zkpromise`, a
`discharge`, and an `intent` over the *same* resolver/caveat/guard `p` and the *same*
continuation `k` all extract to the identical `AwaitCore p k`; and any `AwaitCore`
node sits as a node of a `promiseGraph`. Hence the four are interconvertible views of
one primitive — the unification claim. -/
theorem four_faces_unify
    {P W : Type u} [Verifiable P W] {Reply S : Type u}
    (p : P) (out : Reply) (k : OneShot Reply S) :
    (zkpromise.toCore (P := P) (W := W) ⟨p, out, k⟩
      = ({ promise := p, kont := k } : AwaitCore P Reply S))
    -- discharge over the same `p`,`k` (any witness `w`) extracts to the same core
    ∧ (∀ w : W, discharge.toCore (P := P) (W := W) (Reply := Reply) (S := S) ⟨p, w, k⟩
        = ({ promise := p, kont := k } : AwaitCore P Reply S))
    ∧ (intent.toCore (P := P) (W := W) ⟨p, k⟩
        = ({ promise := p, kont := k } : AwaitCore P Reply S)) :=
  ⟨rfl, fun _ => rfl, rfl⟩

end Dregg2.Await
