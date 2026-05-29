# LEARNINGS — Continuations, effects & the await/intent family

> Axis: continuations & algebraic effects as the formal home of dregg's await / intent /
> zkpromise / discharge / ConditionalTurn family. Read against `docs/rebuild/00-synthesis.md`
> §1 (turn-as-generator), §2.4 (held-until-commit), §3 (universal gate + await family), §3.3
> (W3-I unification), §8/§9 (Lean metatheory, live-session-then-attest).
> Tags: **[grounded]** = stated/derivable from a paper read here or a synthesis `file:line`;
> **[forward]** = my design proposal, not yet in paper or code.

## Papers read

1. **Plotkin & Power, "Handlers of Algebraic Effects"** (ESOP 2009) — and its journal version
   **Plotkin & Pretnar, "Handling Algebraic Effects"** (LMCS 2013). Core: an effect = a set of
   *operations* + an *equational theory*; the free model of the theory is exactly Moggi's
   computation monad. An operation `op(x₁:α₁.T₁, …)` *suspends*, and its arguments are the
   *possible continuations*. A **handler is a (not-necessarily-free) model** of the theory; the
   handling construct `handle t with H` is the **unique homomorphism** from the free model to
   that model, guaranteed by universality. Examples that matter to us: **timeout** (a handler
   carrying a parameter `T`, discharging the continuation to `z_p` when `T` runs out),
   **rollback** (a state+exception handler that "passes around a list of changes to the memory,
   committed only after the computation has returned a value" — §6.8), **nondeterminism**
   (`pick` handler that invokes *both* continuation arguments), exceptions/stream-redirection.
   Two load-bearing facts: **continuations are the one effect that is NOT algebraic** (Intro;
   "with the notable exception of continuations") so a handler-only account of dregg's await
   has a known seam; and **handler correctness can be undecidable** (Pretnar §6).

2. **Dolan, White, Sivaramakrishnan, Yallop, Madhavapeddy, "Effective Concurrency through
   Algebraic Effects"** (OCaml workshop). The operational, linear realization of #1: `perform`
   suspends to the nearest matching `effect e k` handler, capturing the **delimited
   continuation** `k`; `continue k v` resumes it. Fork/Yield scheduler is ~20 lines. Crucially:
   **"Our continuations are linear (one-shot) … once captured, they may be resumed at most
   once,"** enforced at runtime by raising on the second `continue`; multi-shot requires an
   *explicit copy*. Continuations = heap-allocated resizable stacks ("fibers").

3. **Bruggeman, Waddell & Dybvig, "Representing Control in the Presence of One-Shot
   Continuations"** (PLDI 1996). `call/1cc`: a one-shot continuation differs from multi-shot
   *only* in that **invoking it more than once is an error**. Suffices for non-local exit,
   non-blind backtracking, coroutines, thread systems. **Cannot** implement nondeterminism
   (Prolog) — that needs invoking a continuation *multiple* times to yield more values. When a
   one-shot is captured inside a multi-shot it must be **promoted** to multi-shot. One-shot is
   cheap (a stack-segment pointer, no copy); multi-shot pays the copy.

4. **Dybvig, Peyton Jones & Sabry, "A Monadic Framework for Delimited Continuations."**
   Delimited continuations from four primitives: `newPrompt` (fresh control delimiter),
   `pushPrompt` (delimit), `withSubCont` (capture+abort up to a named prompt), `pushSubCont`
   (reinstate). Plain CPS suffices to explain them. Two things matter for us: **prompts are
   first-class, dynamically generated names** — capture is *relative to a named delimiter*, not
   the whole stack; and **`runCC` encapsulates** a computation that uses control internally but
   is "purely functional when viewed externally" — a typed boundary that confines control
   effects (they note a built-in top-level prompt would be *bad* design because it "gives
   subprograms undesirable control over the main program").

5. **Miller, Tribble & Shapiro, "Concurrency Among Strangers"** (TGC 2005) — E. The zkpromise
   ancestor. **eventual-send `<-`** queues a *pending delivery* and returns a **promise**; the
   pending delivery carries a **resolver** (the right to choose the promise's value). A **turn**
   = one dequeued pending-delivery run to completion (no interleaving, no blocking, can't
   deadlock — only *datalock*). **Promise pipelining**: messages eventual-sent to an *unresolved*
   promise are buffered and stream toward the resolver, so a chain `x<-a()<-c(y<-b())` costs one
   round trip not three — composing awaits across latency *before* resolution. **when-catch**
   "turns data-flow back into control-flow": registers a handler `when(p)->{…} catch e {…}` that
   fires on resolution — exactly an await with a success-continuation and a failure-continuation.
   **Broken-promise contagion** (data-flow exceptions, non-signalling-NaN-style) vs control-flow
   exceptions. **Offline capabilities** (swiss-number password-caps) survive partition and let a
   fresh reference be re-minted — the live-session↔durable-attestation hinge.

## Key ideas (attributed)

- **An effect operation is a suspended morphism with its continuation in its arguments**
  (Plotkin-Power). This is *literally* synthesis §3.2's "a suspended morphism awaiting a …
  resolution." The operation names a hole; the handler fills it. The await family is the
  algebraic-effects pattern wearing a crypto hat.
- **A handler is a model + the handling is a homomorphism** (Plotkin-Pretnar). The "engine" of
  the universal gate (§3.1: Datalog | WitnessedPredicate | Await) is precisely a *choice of
  model*: each engine reinterprets the suspending operation differently, and a turn is the
  homomorphic image. This is a sharper statement than the synthesis's "binding-site + engine."
- **Held-until-commit = a handler that buffers the continuation's effects and replays them only
  on return** (Plotkin-Power rollback §6.8, *verbatim*: "a list of changes to the memory,
  committed only after the computation has returned a value"). dregg's "outgoing effects fire
  only if the turn commits" (§2.4, Spritely) is this exact handler, generalized from state to
  the effect-log.
- **One-shot is the default; multi-shot is the exception you pay for** (Dolan et al.; Dybvig
  et al.). Linear continuations are cheap and are *enough* for exits, coroutines, threads,
  backtracking — i.e. for everything except duplicating-the-world nondeterminism.
- **Resolver = the right to choose; promise = the eventual reference** (E). The resolver is a
  *first-class capability* distinct from the promise — exactly dregg's separation of "who may
  fulfill" from "who is waiting." Pipelining = composing un-resolved awaits across a trust/
  latency boundary. when-catch = the await's two continuations (fill / break).
- **A prompt is a first-class, freshly-named control boundary** (Dybvig et al.); `runCC` is a
  membrane that confines control effects. Maps onto dregg's cell-as-membrane.

## Takeaways for dregg (idea → move; map to synthesis §/code/Lean)

1. **The await family literally IS one effect operation parameterized by resolver-kind.**
   [grounded on Plotkin-Power structure + synthesis §3.2 table] Define one operation
   `await : Predicate; Resolver → Effect` whose *single argument-continuation* is `λ(fill
   satisfying P). effects`. The four faces of §3.2 are not four primitives — they are one
   operation with a `Resolver` parameter:
   - `Resolver::Named(party)` → zkpromise / CapTP-promise (the resolver capability is held by
     one party; `ConditionalTurn` + `ProofCondition`, `turn/src/conditional.rs`).
   - `Resolver::Gateway(g)` → discharge / 3rd-party caveat (`macaroon` 3p + `discharge_gateway`).
   - `Resolver::Exists(P)` → intent (∃ filler; `intent/`). The hole's *type* is P (the
     "inverse membrane" of §3.2).
   - `Resolver::Registry(cascade)` → promise-graph (`PendingTurnRegistry` + `ResolutionCondition`,
     `turn/src/pending.rs`).
   **Move:** this is W3-I §3.3 step 1 (`ResolutionCondition::AwaitFiller`) *re-justified
   categorically* — it's not adding a fourth variant, it's exposing the resolver as the only
   varying parameter of one operation. Map to Lean: the `Resolver` enum (artifact A below).

2. **Make held-until-commit a *handler*, not ad-hoc executor logic.** [grounded: rollback §6.8;
   E turn-to-completion] The turn-runner is the handler that interprets every *outgoing-effect*
   operation by **appending to a pending log instead of performing it**, and at the homomorphism's
   "return" point either **replays** the log (commit) or **discards** it (abort). This *is* a
   correct algebraic handler (it's exactly the rollback model, with the effect-log as the carried
   parameter). **Move:** the deferred-prover keystone (synthesis §6, "Missing #1") becomes "the
   commit-replay handler also emits the witness segment when crossing a membrane." Map to §2.4,
   §6; Lean artifact B.

3. **Adopt one-shot (linear) continuations as the default await typing; conservation forces it.**
   [grounded: Dolan one-shot enforcement; Dybvig one→multi promotion; synthesis Law 1
   conservation / `LinearityClass`] If a turn awaits a fill that *consumes a linear resource*
   (a Token, a held amount under `check_settlement_conservation`), the continuation must be
   resumable **at most once** — resuming twice would double-spend the resource, exactly the
   double-`continue` error Dolan raises at runtime. So **conservation = the linear-typing
   discipline on the await-continuation**, and dregg's `LinearityClass` is the static face of
   Dolan's runtime one-shot check. **Move:** type `AwaitFiller`'s continuation as one-shot for
   any `LinearityClass::Linear` resource; permit multi-shot *only* for `Copy`/non-conserved
   payloads (read-only predicates, broadcast intents that don't pre-commit a resource).
   Map to Law 1 / `action.rs:698`; Lean artifact C.

4. **Pipelining ⇒ live-session-then-attest is the right shape.** [grounded: E pipelining +
   when-catch + offline-caps; synthesis §9.4] During a live session (E *near*/pipelined, dregg
   caps-as-caps interior) you compose un-resolved awaits with one round trip and only data-flow
   contagion on failure — no proofs. At the membrane you *resolve*, and the resolution is where
   the witness crystallizes (the deferred-prover). when-catch's two continuations map to the
   gate outcome: **fill** (resolution → discharge the turn, emit proof) vs **break** (predicate
   unsatisfiable / partition → broken-promise contagion = the conservation-preserving abort).
   Offline-caps = the durable attestation that re-mints a reference after partition. **Move:**
   model the membrane as `runCC`/prompt: the prompt name = the cell/trust-root id; capture is
   relative to *that* boundary, so a turn composing within one root captures no proof (synthesis
   §8 membrane law) and only a cross-prompt resolution forces the witness side of
   `Predicate ⊣ Witness`.

5. **FIND-vs-VERIFY is the algebraic-vs-search seam, and the papers confirm the asymmetry.**
   [grounded: Pretnar undecidability of handler correctness §6; synthesis §3.2 VERIFY/FIND]
   *Verifying* a claimed fill = applying the homomorphism (handler) once = tractable. *Finding*
   a fill = constructing a model that satisfies P = the general handler-correctness /
   existential-search problem Pretnar shows undecidable. This independently grounds the
   synthesis claim that "a *general* matcher is provably out of reach" and that `RingSolver`
   must be a **bounded, pluggable, domain-specific** solver. **Move:** keep matching as a
   pluggable solver (like finality is a pluggable phase); never promise a universal `fulfill`.

## Tensions & corrections

- **Continuations are NOT an algebraic effect** (Plotkin-Power Intro; Pretnar). This is the one
  honest hole: the await family *uses* continuations (the suspended morphism), so a pure
  "handlers model everything" claim over-reaches. **Correction to a tempting over-claim:** do
  *not* assert in Lean that the turn category is the free model of an algebraic theory of await
  — await's continuation is the non-algebraic part. The clean statement is narrower: the
  *gate-engine choice* is a handler (a model), and *held-until-commit* is a handler (rollback),
  but the *continuation capture* itself is a delimited-continuation primitive (Dybvig), modelled
  by prompts/CPS, not by an algebraic operation. Two layers, not one. [grounded]

- **"One continuation primitive" needs the one-shot/multi-shot split or it's unsound.**
  [grounded: Dybvig promotion rule] A single undifferentiated await type that allowed
  multi-shot resumption of a linear-resource continuation would let conservation be violated
  silently. The unification in §3.3 is correct *only* with the linearity tag from takeaway 3.
  So "one primitive" = one *shape* with a linearity parameter, not one untyped thing. Mild
  correction to §3.3's framing.

- **Resolver authority is itself a capability and must be conserved/non-forgeable.**
  [grounded: E resolver = "the right to choose"] The synthesis treats the resolver as
  metadata ("WHO resolves"). It is actually a *capability* — leaking it is leaking the right to
  fill the hole. For `Resolver::Exists(P)` (intent) the resolver is *public* (anyone satisfying
  P), which is fine; but for `Named`/`Gateway` the resolver-cap must travel under the same
  cap discipline as everything else (and survive partition via an offline-cap, per E §9.2).
  **Move:** the resolver is a first-class cap in the model, not a label.

- **when-catch shows we owe a *break* path, not just a *fill* path.** [grounded: E broken-promise
  contagion] dregg's await faces are described mostly by their success resolver. Every await
  also needs a *break* continuation (predicate provably unsatisfiable, timeout, partition) that
  is **conservation-preserving** (returns/refunds held resources). The held-until-commit handler
  already gives this for free (abort = discard log = refund). Make it explicit in the type.

- **Datalock, not deadlock, is the live-session failure mode.** [grounded: E §8.3] An await
  whose own resolution depends (transitively) on itself never blocks the vat but never
  progresses. dregg's promise-graph cascade (`PendingTurnRegistry`) can form the same cycle.
  This is a *liveness* obligation for the Lean model's ordering law (Law 2), not a safety one;
  worth a noted theorem ("a well-founded resolution order ⇒ no datalock").

## Proposed Lean/metatheory artifacts

(All **[forward]**; align with synthesis §8's "smallest adversarial seed" and §9.1 "Lean core
first." Keep crypto out of Lean per §8 note.)

**A. The one continuation type + resolver enum.** One inductive for the whole await family:

```lean
inductive Resolver where
  | named   (party  : Principal)        -- zkpromise / CapTP-promise
  | gateway (g      : Principal)        -- discharge / 3rd-party caveat
  | exists  (P      : Predicate)        -- intent (∃ filler; hole-type = P)
  | registry (cascade : List PendingId) -- promise-graph

structure Await (Γ : CellState) where
  predicate    : Predicate               -- the type of the hole
  resolver     : Resolver                -- WHO/HOW it gets filled
  conservation : LinearityClass          -- forces one-shot when Linear
  onFill       : Fill → Turn Γ           -- success continuation  (λ fill. effects)
  onBreak      : BreakReason → Turn Γ    -- conservation-preserving abort
```
Theorem target: each `Resolver` case is a *retract* of the others' verify-side (one gate
machinery), and `exists` is the categorical *inverse* (hole on the domain) of a membrane
crossing (hole on the codomain) — formalizes "intent = inverse membrane" (§3.2).

**B. Held-until-commit as a handler (rollback model).** Define a `runTurn` interpreter that
threads a `pendingEffects : List Effect` parameter; the outgoing-effect operation appends, and
`commit`/`abort` either folds the log into the world or drops it. Prove it is a *correct
handler* (a model of the effect theory) by exhibiting it as the rollback handler of
Plotkin-Power §6.8 specialized to the effect-log. **Membrane law (§8 sharp target):** a turn
all of whose await-prompts are the *same* trust-root captures no cross-prompt subcontinuation ⇒
needs no witness; a turn whose resolution crosses a prompt forces the `Witness` side of
`Predicate ⊣ Witness`. Model the trust-root as a `newPrompt`-style fresh delimiter (Dybvig);
`runCC`-style encapsulation = the cell membrane.

**C. Linear-continuation typing of await.** A typing judgment `Γ ⊢ Await ⊣ Δ` where a
continuation over a `LinearityClass::Linear` resource is **one-shot** (resumable ≤ 1). Theorem:
under one-shot typing, composing awaits *preserves the per-class conservation sum* (synthesis
Law 1) — i.e. Dolan's "raise on second `continue`" is *derivable* as a corollary of conservation,
not an ad-hoc runtime guard. Corollary: multi-shot await is sound **iff** its payload is in a
non-conserved (Copy) class — the Dybvig promotion rule, typed.

**D. (stretch) No-datalock liveness lemma.** If the registry's resolution dependency relation is
well-founded, every submitted await eventually resolves-or-breaks. Ties Law 2 (ordering) to the
promise-graph cascade.

## Open questions / what to read next

1. **Where does the non-algebraic-ness of continuations actually bite us?** Plotkin-Power punt
   to Hyland-Levy-Plotkin-Power "Combining algebraic effects with continuations" (TCS 2007).
   Read it before claiming any "turn = free model" theorem; it tells us *which* equations the
   await layer can and cannot have.
2. **Typed encapsulation of control = the membrane type.** Dybvig et al.'s typed `runCC` and the
   "where can control effects occur" type system is the closest existing thing to dregg's
   first-class trust-boundary type (synthesis §6 "Missing #2"). Worth a deeper pass to see if
   their answer-type / effect-type machinery prefigures `Predicate ⊣ Witness`.
3. **Effect rows vs the gate-engine coproduct.** Is `engine = Datalog | WitnessedPredicate |
   Await` better modelled as an *effect row* (Koka/Frank style) than a flat enum? Would let a
   turn declare exactly which gate-effects it may perform — closer to capability discipline.
   (Bauer-Pretnar "Programming with Algebraic Effects and Handlers" is the reference Dolan cites;
   not in this corpus — fetch.)
4. **Multi-party turns and the binary-handler gap.** Plotkin-Power flag that *parallel* (CCS `|`,
   UNIX pipe) resists their handlers because it's "recursively defined on two structures" — a
   binary handler they couldn't give. dregg's `CommitmentMode::Full|Partial` multi-party turn is
   exactly a two-structure composition. Open: is partial-commit a binary handler, and is the
   open CCS-parallel problem the *reason* multi-party atomic turns are hard (synthesis §6
   "Missing #3")?
5. **Resolver-as-capability under revocation.** E's offline-caps expire (TTL / revocable /
   transient). Map to dregg's revocation substrate (synthesis §5.2 "unify revocation"): a
   `Named`/`Gateway` resolver-cap should live in the same Merkle non-membership accumulator. Not
   yet designed.
</content>
</invoke>
