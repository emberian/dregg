# PATH B — Coinductive soundness, streaming VC & rejuvenation

**Scope.** The worry: do dregg's "bounded-depth aggregation" per-turn proofs witness only a *fixed
past*, leaving a continually-evolving cell unattested? This doc tests/sharpens/refutes the working
resolution: a live cell is **codata** (an element of the final coalgebra of the turn functor);
soundness is a **step-preserved (guarded-corecursive) invariant / bisimulation**, not one proof of an
infinite past; the per-turn proof + hash-chained receipt log **is** that guarded structure — *iff* the
per-turn proof discharges the **full** step invariant. Succinct verification of unbounded history
(late-join / audit / teleport) is a separate **efficiency** axis (IVC). Rejuvenation = re-prove/re-fold
from the retained log, optionally with controlled malleability to reset accumulator slack.

Tags: **[G]** grounded in a cited paper · **[F]** forward-design (dregg-specific, my construction) ·
**[T]** theorizing/conjecture (flagged explicitly).

Sources ground-read via `pdftotext`: mixing-induction-coinduction (Danielsson–Altenkirch),
guarded-recursion-coinductive (Birkedal et al.), coalgebraic-semantics-silva,
verifiable-streaming-computation-2025-251 (Afshar–Goyal, IVsC), streaming-zero-knowledge-proofs-2301.02161
(Cormode et al.), coinductive-proofs-regex-zk-2504.01198 (Kolesar et al., Crêpe),
malleable-snarks-2025-311 (Chakraborty et al.), sumcheck-zksnarks-non-malleable-2026-335 (Faonio–Russo),
valiant-conjecture-ivc-impossibility-2022-542 (Hall-Andersen–Nielsen). Project ground:
`docs/rebuild/00-synthesis.md` §1/§8, `pdfs/discoveries.md`.

---

## Coinductive soundness made precise (the turn functor, the guarded invariant, the bisimulation)

### The turn functor F

**[G/F]** Silva's notes give the dictionary exactly: a system whose behaviour is "circular / infinite,
much like streams" is a **coalgebra** `c : X → F X` of a `Set`-endofunctor `F`; the canonical object is
the **final coalgebra** `νF` (the greatest fixpoint, the *codata*), and the canonical proof technique
for "two such things agree forever" is a **bisimulation** (`induction:proof / coinduction:bisimulation,
least:greatest fixpoint, initial algebra : final coalgebra` — her duality table, lines 132–141). A DFA
is her running coalgebra `(S, o, t)` with `o : S → 2` (output/observation) and `t : S → S^A`
(one transition per input letter).

A dregg cell is the same shape. Let:

- `S` = cell-state (the 8-field / Preserves `Record` state of `00-synthesis §5`),
- the *input letter* at each step = an **admissible turn** `τ` (a morphism in the categorical skeleton
  of §1: an arrow over a flat action sequence), drawn from the set `T(s)` of turns admissible in state
  `s` (gated by the `WitnessedCondition` of §3.1),
- the *observation* `o(s)` = the publicly-committed digest of the cell: its state-root /
  `previous_receipt_hash` head, the per-class conservation sums `Σ_k`, and the authority bound.

Then the **turn functor** is

```
F X  =  o-Observation  ×  ( AdmissibleTurn ⇒ X )          -- a Moore/DFA-shaped coalgebra
```

and a cell is a coalgebra `step : CellState → F CellState`, `step(s) = ( commit(s) , λτ. apply(τ, s) )`.
The **running cell** — the thing the worry is about — is the image of `s₀` in the **final coalgebra**
`ν F = ν X. Obs × (Turn ⇒ X)`: an element of `νF` is exactly "an observation now, and for every
admissible next turn, another such element forever." That object is **codata**; it has *no* finite
construction, and that is the point. **The cell is not a finite turn-list; it is a stream of turns over
an inductively-built per-turn payload.**

### The inductive turn inside the coinductive stream — the nested fixpoint

**[G]** This is the precise structure Danielsson–Altenkirch name. A *purely* coinductive reading is
"too infinite" (their §1: a coinductive transitivity rule makes *everything* related); a *purely*
inductive reading can't carry an unbounded future. The fix is **mixed induction/coinduction = a nested
fixpoint** `ν C. µ I. F C I` (their stream-processor example, lines 228–235:
`νC. µI. (A → I) + B × C`, the type `SP A B` with an **inductive** `get` and a **coinductive** `put` —
"a stream processor can only read a *finite* number of elements before producing output").

Map onto dregg **[F]**:

```
Cell  =  ν C.  µ I.  StepProof I  ×  ( AdmissibleTurn ⇒ C )
              └────────┬────────┘                  └─ coinductive: the next cell, "later"
        inductive: ONE turn's proof  (a finite STARK/fold over a flat action list)
```

- The **inner µ** is one turn: a finite, bounded-depth object — the per-action effect-fold, the
  conservation check, the auth-AIR (`00-synthesis §1`, the 6-clause auth-in-proof STARK statement). It
  is *legitimately inductive* and *legitimately bounded*. The "bounded-depth aggregation" worry is a
  worry about the **inner µ**, and at that layer bounded depth is **correct**, not a defect — exactly as
  `get` consuming finitely many inputs is correct.
- The **outer ν** is the unbounded life of the cell. It is never "proven all at once"; it is
  *corecursively produced*, one guarded step at a time.

So: **bounded per-turn proof is not a witness to a fixed past — it is the µ-payload guarding one ν-step.**
The category error in the original worry is reading the whole cell as a single inductive (or single
flat-aggregated) object. It is a nested fixpoint, and the bound lives only in the inner layer.

### The guard = the chain link (the `▶`/"later" modality)

**[G]** Birkedal et al. give the operational meaning of the guard. Their guarded λ-calculus adds a
modality `▶` ("later", written `I` in the OCR; lines 44–53): `▶A` is "data we have only **later**, not
now." Guarded streams are `Str = Nat × ▶Str` — *head now, tail later* — and the fixpoint combinator has
type `(▶A → A) → A` with reasoning by **Löb induction** (line 86). The whole purpose of `▶` is to
guarantee **productivity**: every finite approximation (head; first two; first three; …) is computable
in finitely many steps, and self-reference is *only* allowed under a `▶`. Their non-example
`interleave s toggle` and the paperfolding stream (lines 34–41, 314) show that **without the guard you
get equations with no unique solution** — i.e., the corecursion is unsound.

**[F]** In dregg the guard is the **`previous_receipt_hash` link**. The next cell-state is literally
defined *under* a commitment to the current one:

```
sₙ₊₁  :  ▶CellState        -- only available after, and cryptographically pinned to, sₙ
         link(sₙ₊₁) = H( previous_receipt_hash = root(sₙ) , turnₙ , … )
```

The hash-chain *is* the `▶`: it makes `sₙ` "now" and `sₙ₊₁` "later," and it makes the corecursion
**productive and uniquely-solved** — you cannot fabricate a tail that doesn't extend this exact head,
because the head's hash is an input to the tail. `00-synthesis §2.4` already states this operationally
("cheap eager pin — append-only, causally-pinned receipt chain … prevents history-rewriting before
proving"). The metatheory reading: **`previous_receipt_hash` is the syntactic realization of the `▶`
guard that makes the cell a well-defined element of `νF`.**

### The bisimulation: soundness as a coinductive invariant

**[G]** Silva, Def. 4 + Thm. 1: a relation `R ⊆ S×T` is a **bisimulation** iff for all `x R y`,
(i) `o(x) = o(y)` (same observation now) and (ii) for every input `a`, `t(x)(a) R t(y)(a)` (the
successors stay related); and the **coinduction principle** is: *if such an `R` exists with `x R y`,
they agree forever* (`ℓ(x) = ℓ(y)`).

**[F]** dregg soundness is the bisimulation between the **real cell** and an **idealized law-abiding
cell** `Spec` (the Lean golden oracle of `00-synthesis §9` / decision 1). Define the candidate relation

```
R(s, σ)  ≜  StepInvariant holds at s  ∧  obs(s) = obs(σ)
```

and `Sound` = the **greatest** `R` closed under: for every admissible turn `τ`,
`apply(τ,s) R apply(τ,σ)`. Soundness of dregg = *the diagonal `{(s,s) | reachable s}` is a
bisimulation for `StepInvariant`* — i.e., **`StepInvariant` is a coinductive invariant of the
turn-coalgebra**: it holds now and is preserved into every guarded successor. This is the on-the-nose
precedent **[G]**: Kolesar et al.'s Crêpe proves PSPACE-complete *regex equivalence* by exhibiting a
**bisimulation between derivative-coalgebras** as a *finite* certificate, verified **inside a ZK
circuit** — their `Sync`/`Coinduction` rules close a cycle (lines 360–377): the derivatives "fall into a
finite number of equivalence classes," so the infinite behaviour is witnessed by a finite cyclic
bisimulation. **Coinduction inside a succinct proof is not exotic; it is published and implemented.**

What does the per-turn proof have to attest for this to work? Exactly the bisimulation **step
condition**: that `obs` is preserved-up-to-the-step (the chain link advances correctly) and that
`StepInvariant` is re-established at the successor. That is the content of the next section.

---

## Confirm/refute: bounded per-turn proof + guarded chain = coinductive soundness iff step-complete

**VERDICT: CONFIRMED, with the iff made sharp. The "iff step-complete" condition is load-bearing and is
the real theorem.**

The coinduction principle (Silva Thm. 1) and Löb induction (Birkedal et al.) both have the *same* shape:
to conclude an `νF`/guarded property holds **forever**, it suffices to show **one** step preserves it,
*provided the step shows the full property* (the guarded hypothesis you may assume is `▶P`, and you must
re-establish `P`). Translating:

> **Theorem (coinductive soundness, [F] modelled on Silva Thm.1 + Birkedal Löb).**
> If every admissible turn's proof discharges the **complete** step invariant
> `StepInv(s, τ, s′) ≜ Conservation(s,τ,s′) ∧ Authority(s,τ) ∧ ChainLink(s,τ,s′)`
> and the genesis satisfies `StepInv₀`, then the diagonal is a bisimulation and
> **`StepInvariant` holds along every (even infinite) run of the cell** — i.e. the cell's image in
> `νF` is sound. No proof of the infinite past is required.

Spelling out the three conjuncts the **inner-µ proof must contain** (this *is* the "step-complete"
predicate; it is the union of `00-synthesis §1`'s two laws + §2.4's pin):

1. **Conservation** — `Σ_k(s′) = Σ_k(s)` off mint/burn generators (the strong-monoidal-functor law,
   `discoveries §3.2`). The local effect-fold alone does **not** imply this; it must be asserted over
   the *whole* turn's net.
2. **Authority** — the actor was *permitted*: the auth-AIR / `WitnessedCondition` discharged (the
   cross-vat clause of `00-synthesis §8`). (Caveat, `discoveries §3.6`: this is de-jure *permission*,
   not de-facto *authority*; the latter is BA-behavioural, recovered from the log — so the coinductive
   invariant is over **permission + log**, not over a static cap-graph.)
3. **ChainLink** — `s′.previous_receipt_hash = root(s)` (the `▶` guard) **and** the proof's public input
   *binds* both `root(s)` and `root(s′)` (cross-PI binding, the 6th clause of §1's STARK statement).

**Why "iff," not "if":** drop **any** conjunct and the bisimulation breaks at exactly the dropped
coordinate, and — crucially — **coinduction makes the failure unbounded, not local.** This is
Danielsson–Altenkirch's own warning made cryptographic: their §4.5 (lines 69–75) — "in the presence of
coinduction, [adding] an admissible rule **may not be sound if the admissible rule does not have a
sufficiently contractive proof**." A per-turn proof that attests only the *local effect* (e.g. "this one
action's arithmetic is right") is the **non-contractive admissible rule**: it looks fine inductively per
turn, but corecursively it lets you build an infinite run that drifts — e.g. a chain each of whose links
locally type-checks but whose `Σ_k` slowly leaks (no per-step conservation), or which forks off an
unpinned tail (no ChainLink). The guard alone (chain link) stops history-*rewriting* but **not**
invariant-*drift*; only attesting the *full* `StepInv` stops drift. Conversely, if `StepInv` is complete
and guarded, the coinduction principle discharges the infinite obligation **for free** — that is the
entire payoff.

**Refutation of the strawman:** "bounded-depth aggregation proves only a fixed past." *Refuted.* The
bounded proof is the inner-µ payload of a guarded ν-step; bounded depth is correct *there* (cf. `get`
reading finitely many inputs). What would be unsound is a bounded proof that is **step-incomplete** —
and that unsoundness is not "only sees a fixed past," it is "permits an unboundedly-drifting future."
The fix is not "make the proof see more history" (that's the efficiency axis below); the fix is **make
each step's proof complete.** History-succinctness and step-completeness are orthogonal.

---

## Metatheory: stating the laws coinductively (Lean signatures)

**Why coinductive, not inductive over finite turn-lists [F+G]:** an inductive statement
`∀ (ts : List Turn), Invariant (foldl apply s₀ ts)` quantifies over **finite** pasts only — it is
literally the "fixed past" the worry feared, and it says *nothing* about a never-terminating cell.
Danielsson–Altenkirch's stream-processor and Silva's `N∞`/`A* ∪ Aω` examples are exactly the gap: the
*greatest* fixpoint contains the infinite elements the *least* fixpoint omits. Stating the law over
`νF` (a) covers non-terminating cells, (b) turns "preserved forever" into a **one-step** proof
obligation via the coinduction principle (no induction on an unbounded list), and (c) makes the
hash-chain guard a *typed* object (`▶`) rather than a side-comment. mathlib4 supports this: it has
greatest-fixpoint / coinductive machinery (`GreatestFixpoint`, the `CoInductive`/`Stream'` and the
`.coinduction`/`bisim` elimination idioms, and `Quot`-based final-coalgebra constructions).

```lean
-- The turn functor as a Moore/DFA coalgebra (Silva's (S,o,t), uncurried t : S × A → S).
structure TurnCoalg where
  State : Type
  Obs   : Type
  admissible : State → Turn → Prop
  obs   : State → Obs                     -- committed digest: state-root, Σ_k sums, authority bound
  step  : (s : State) → (τ : Turn) → admissible s τ → State

-- The live cell is CODATA: an element of the final coalgebra ν X. Obs × (Turn ⇒ X).
-- (In Lean, a coinductive record / greatest fixpoint; the `tail` field is the guarded `▶`.)
structure Cell (C : TurnCoalg) where
  now  : C.Obs
  next : (τ : Turn) → (h : C.admissibleHere τ) → Cell C       -- guarded self-reference = the ▶

-- The COMPLETE step invariant the per-turn proof must discharge (the inner-µ payload).
structure StepInv (C : TurnCoalg) (s : C.State) (τ : Turn)
    (h : C.admissible s τ) (s' : C.State) : Prop where
  conservation : ∀ k, Sigma k s' = Sigma k s                  -- off mint/burn (Law 1)
  authority    : Permitted s τ                                -- auth-AIR / WitnessedCondition
  chainLink    : s'.prevReceiptHash = stateRoot s             -- the ▶ guard, cross-PI-bound
  obsAdvance   : C.obs s' = commitAfter (C.obs s) τ           -- observation evolves correctly

-- SOUNDNESS AS A COINDUCTIVE PREDICATE (greatest fixpoint): holds now ∧ preserved into every successor.
coinductive Sound (C : TurnCoalg) : C.State → Prop where
  | step (s) :
      LocalOK s →
      (∀ τ (h : C.admissible s τ),
          StepInv C s τ h (C.step s τ h) ∧ Sound C (C.step s τ h)) →     -- guarded recursive call
      Sound C s

-- SOUNDNESS AS A BISIMULATION to the Lean golden-oracle Spec (Silva Def.4 + the §9 differential oracle).
def IsBisim (C : TurnCoalg) (R : C.State → Spec → Prop) : Prop :=
  ∀ s σ, R s σ →
    C.obs s = Spec.obs σ ∧                                   -- (i) same observation now
    ∀ τ (h : C.admissible s τ),
      ∃ hσ, R (C.step s τ h) (Spec.step σ τ hσ)              -- (ii) successors stay related

-- The headline theorem: STEP-COMPLETE  ⇒  COINDUCTIVELY SOUND  (the iff of the previous section).
theorem sound_of_step_complete (C : TurnCoalg) (s₀ : C.State)
    (genesis  : LocalOK s₀)
    (stepGood : ∀ s τ h, Reachable C s₀ s → StepInv C s τ h (C.step s τ h)) :
    Sound C s₀ := by
  coinduction                                                -- Löb / greatest-fixpoint intro
  sorry   -- discharge each conjunct from `stepGood`; the GUARDED hypothesis is `Sound (step …)`
```

### The vat-boundary law, coinductively

`00-synthesis §8`'s membrane law is currently phrased per-transition (intra-vat needs no witness;
crossing needs the witness side of `Predicate ⊣ Witness`). Coinductively it becomes an invariant of the
**boundary coalgebra**: along *every* run, every turn whose effect-set escapes the trust-root carries a
discharged witness, and no run ever exports unheld authority (the §2.4 capability-sealing pin).

```lean
-- Boundary law as a coinductive invariant of the turn-coalgebra (not a List fold).
coinductive BoundaryRespecting (C : TurnCoalg) : C.State → Prop where
  | step (s) :
      (∀ τ (h : C.admissible s τ),
          ( Crosses s τ → Discharged (witnessOf τ) ) ∧        -- cross-vat: witness mandatory
          ( ¬ Crosses s τ → True ) ∧                          -- intra-vat: trivial witness
          NoUnheldExport s τ ∧                                -- §2.4 capability-sealed serialization
          BoundaryRespecting C (C.step s τ h)) →               -- guarded: holds forever after
      BoundaryRespecting C s
```

**What's gained vs the inductive statement:** (1) covers cells that never halt (the actual deployment
case); (2) the proof obligation collapses to **one guarded step** by the coinduction principle, instead
of induction over an unbounded `List Turn`; (3) the `▶`/`ChainLink` guard is a *typed* object, so
"the chain link is what makes corecursion productive" is checked, not asserted; (4) it composes with
`00-synthesis §9`'s differential-oracle plan: `IsBisim … Spec` is *exactly* the contract
"Rust impl ≈ Lean golden oracle, forever," and a bisimulation is the right shape for a coinductive
refinement (IGLOO's "verifier accepts ⇒ impl refines spec," lifted from finite traces to streams).
**Caveat [G/§8]:** none of this establishes *cryptographic* soundness (that the STARK actually attests
`StepInv`) — that stays a circuit obligation; the Lean law assumes a sound `Verify`. Conflating them
would be its own error (the §8 README caveat).

---

## Streaming VC: the unbounded-stream-incremental primitive & its relation to IVC

**There is a clean published primitive, and it is a near-perfect fit for log-is-truth.**

**[G] Afshar–Goyal, IVsC = "Incrementally Verifiable *Streaming* Computation"** (verifiable-streaming-
computation-2025-251). The exact upgrade over IVC dregg needs: IVC requires the *full input available
when computation begins* (their lines 174–177); IVsC handles a **streaming input `x₁, x₂, …` available
only on-the-fly** (lines 8–9, 132–138) — which is precisely a continually-evolving cell whose future
turns *do not exist yet*. The mechanism (lines 186–193): an **incrementally-computable input Digest**;
each step `t` carries proof `πₜ` *and* the input-digest-so-far, the next party updates **both**, and
`πₜ` verifies in time **independent of the stream length** given the digest. The digest is **independent
of the step function `M`** (line 193), so it can be precomputed/shared — matching dregg's
state-root-as-digest. Built from **standard falsifiable assumptions** (DLIN / sub-exp DDH/LWE,
seBARGs + somewhere-extractable hashing) — *not* a random oracle, *not* a SNARK-of-SNARK
(their lines 6–13, 128–131). This is the principled "prove an unbounded stream incrementally" object.

**[G] Cormode et al., Streaming Interactive Proofs (SIPs) + zero-knowledge SIPs** (streaming-zero-
knowledge): a **space-bounded** (`polylog(n)`) verifier with **one-pass** access to a massive stream
verifies a heavy computation by talking to an untrusted prover; they add ZK and, notably, a **temporal
commitment protocol**. This is the *complementary* axis: IVsC keeps the **proof** small as the stream
grows; SIPs keep the **verifier's space** small over a one-pass stream. For a dregg auditor/late-joiner
who streams the receipt log once, SIP-style temporal/algebraic-streaming commitments are the right tool
for "verify the whole log in sublinear space without materializing it."

**Relation to IVC, and the placement [G+F]:**

- **IVsC is the strict generalization of IVC** dregg's *outer ν* wants for **late-join / audit /
  teleport**: succinct verification of an **unbounded, still-growing** history. It is the
  *efficiency/succinctness* axis — orthogonal to step-completeness/soundness (the previous sections).
- **log-is-truth fit [F]:** dregg's receipt log *is* the streaming input `x₁,x₂,…`; the cell state-root
  *is* the incrementally-computed Digest; a turn proof is the `πₜ`. IVsC says: you can let a late
  joiner verify the *entire* cell history against the current digest in time independent of how long the
  cell has lived — **without re-reading the whole log** — which is exactly what "truth is the log, but I
  don't want to ship/replay the whole log across a boundary" needs. The per-turn proof handles
  *soundness*; IVsC handles *succinct unbounded verification* on top.
- **step-by-step ZK is a bonus dregg should want [G]:** Afshar–Goyal's "step-by-step zero-knowledge" —
  the prover's **entire internal memory is simulatable at *any* step**, not just the final proof
  (lines 16, 139) — defends a cell whose prover is **corrupted mid-life**. A long-lived cell is exactly
  the corrupt-before-finish threat model they motivate; this is a strong reason to target zk-IVsC over a
  vanilla recursive SNARK for the cross-boundary export format.

**The cost, named [G] — Valiant impossibility.** Hall-Andersen–Nielsen prove Valiant's 14-year
conjecture: **IVC from a *standard* random oracle is impossible** (under mild extra assumptions —
specifically if the proof system is *zero-knowledge*, or if it can tell whether an RO query is fresh).
Valiant's own RO-methodology was non-standard (the hash is "sometimes a random oracle, sometimes a
short circuit"). **Consequence for dregg:** unbounded succinct history-verification is **not free** —
it *requires* computational assumptions (which is exactly the regime IVsC lives in: falsifiable
assumptions + seBARGs, *not* "just a hash"). This is the formal teeth behind "the unbounded-history
axis is distinct from soundness and you pay for it." It also means: **do not bolt history-succinctness
into the Lean soundness law** — soundness is a coinductive invariant (free, by the coinduction
principle); succinctness is a cryptographic IVsC obligation (costed, assumption-laden, circuit-side).

---

## Rejuvenation: controlled-malleability vs re-prove-from-log; the safe definition + freshness-context

**The two horns, and the reconciliation [G]:** dregg wants *both* (a) **non-malleability** for soundness
— a proof for statement `X` must not be maulable into a proof for an unrelated `X′` you don't have a
witness for (the malleability attacks Faonio–Russo cite: ~300k BTC, and the **Nova/Lurk** SE
vulnerability, their intro); *and* (b) **controlled malleability** for rejuvenation — the *intended*
ability to transform/refresh an existing proof. These are not in conflict; they are the two ends of one
dial, and the literature names the safe middle:

- **Full non-malleability = simulation-extractability (SE).** Faonio–Russo: SE = "any adversary
  producing a valid proof must possess a witness, even after seeing simulated proofs for false
  statements" — the property that *prevents* malleability attacks. This is what dregg's **soundness**
  posture needs by default.
- **Controlled malleability (Chase et al. EUROCRYPT'12 notion).** Faonio–Russo's key result: the
  sumcheck/PST-based zkSNARKs (HyperPlonk, Spartan, **Libra** — the multilinear-PIOP family) **cannot**
  be SE because PST's commitment is **linearly homomorphic** — but they satisfy *controlled
  malleability*: **"linear homomorphism is essentially the only admissible malleability,"** and that
  suffices for security inside the PIOP→zkSNARK paradigm. So the maulability is *bounded to a named,
  benign transformation class `T`*.
- **Malleable SNARKs (Chakraborty et al.).** The general theory: a malleable SNARK permits modifying a
  proof of `X` to a proof of `X′ = T(X)` for `T` in a **restricted allowed class `T`**, such that mauled
  proofs are **indistinguishable from freshly generated** ones (**derivation privacy**, their §1.1).
  The danger they confront head-on: derivation privacy vs recursion are "at odds" — a naive depth
  counter distinguishes mauled from fresh — so they need an **adversarial one-way function (AOWF)** to
  hide depth while keeping **bounded-depth extractability** (extraction must *eventually* bottom out at
  a "proper" witness not referring to a previous proof, their abstract + lines 116–147). **That
  extraction-must-terminate condition is the cryptographic mirror of the contractivity/guard from the
  coinduction sections** — both say "the unbounded structure must be re-grounded in a real witness, not
  an infinite regress of references."

**So: which is rejuvenation? [F] — Both, layered, and the choice is a freshness-context decision:**

> **Definition (rejuvenation, [F]).** *Rejuvenation* of a cell's proof state is the operation
> `Rejuvenate : (Proof, FreshnessCtx) → Proof′` that restores verifiability of the *current* digest
> against a *current* validity context, taken from the **retained log** as ground truth. Two admissible
> implementations, picked by the freshness context:
>
> 1. **Re-prove / re-fold from log (always available; the soundness-safe default).** Because
>    **log-is-truth**, the cell can always recompute `StepInv` over the retained receipt chain and emit a
>    *genuinely fresh* proof / IVsC accumulator. This needs **no** malleability at all — it is ordinary
>    proving — so it inherits the **full SE / non-malleability** of the base system. Cost: re-folding
>    work (bounded by log length, or by the IVsC digest if available). This is the **fail-safe**: even a
>    degraded/expired/parameter-rotated proof is recoverable because the inputs were never thrown away
>    (`00-synthesis §2.4`, §0 orthogonal persistence).
> 2. **Controlled malleability (the efficiency option, only for `T`-admissible refreshes).** When the
>    only change is within the **named transformation class `T`** — re-randomization to unlink, an
>    accumulator-slack reset (Nova-style compression/decider at a boundary), a context/epoch re-binding —
>    use a malleable transform: `Proof′ = Maul_T(Proof)`, indistinguishable-from-fresh (derivation
>    privacy), **bounded-depth-extractable** (AOWF). This is *cheaper* than re-proving but is sound
>    **only** for `T` in the admissible class (e.g. PST's linear homomorphism, per Faonio–Russo).

**The freshness/validity context** that parameterizes which is legal:

```
FreshnessCtx = {
  epoch / block_height       : the §3.1 BindingSite `when` — re-bind to current canonical time,
  verification_key version   : did the circuit/params rotate? (rotation ⇒ must re-prove, not maul),
  accumulator_slack_budget   : Nova-style — reset by a decider/compression step at the boundary,
  allowed_transform_class T  : the ONLY mauls permitted (re-randomize, re-bind epoch, fold-compress),
  cross_PI binding           : the new proof must bind the *current* state-root (the ▶ guard, §1 cl.6),
}
```

**The safety rule [F], reconciling (a) and (b):** *a rejuvenation is sound iff its transform lies in the
context's admissible class `T` AND extraction terminates at a real witness over the retained log.* For
anything outside `T` — and **always** across a trust boundary where an adversary could supply the prior
proof — **fall back to re-prove-from-log**, which is unconditionally SE-safe. In dregg terms: **maul for
intra-vat refresh / unlinkability / slack-reset; re-prove for cross-vat export and for any vk rotation.**
This mirrors the caps-inside/keys-between seam (`discoveries §2,§3.6`): cheap controlled transforms
*inside* the boundary, full non-malleable re-grounding *across* it.

---

## Tensions & open questions

1. **[T] Is the per-turn proof *actually* step-complete in current dregg?** The whole "iff" rests on the
   inner-µ proof attesting all of `{Conservation, Authority, ChainLink, ObsAdvance}`. `00-synthesis §1`
   states the **6-clause** auth-in-proof STARK as a *target*, and `MEMORY`/soundness-audit notes flag
   "intent predicates unenforced," "graph-folding flat/non-recursive." **Action:** audit the live AIR —
   if it attests local effects but not the net `Σ_k` conservation or the cross-PI `ChainLink` binding,
   the coinductive soundness theorem **does not yet hold**, and the fix is step-completion, not more
   history. This is the single most load-bearing open check.

2. **[T] De-jure vs de-facto in the bisimulation.** The Authority conjunct attests *permission* (BA-vs-TP,
   `discoveries §3.6`); de-facto authority is behavioural, recovered from the log. So the coinductive
   invariant must be stated over **(permission ∧ log)**, and a caretaker/forwarder that makes the
   cap-graph "lie" is *outside* the bisimulation unless the log is in `R`. Does `Spec` observe the log,
   or only the cap-graph? Must be the former.

3. **[T] Does conservation need the *guarded* fixpoint or just the chain?** Conjecture: ChainLink (the
   `▶`) gives productivity/uniqueness of the *successor*, but Conservation is what makes the invariant
   *contractive* (Danielsson–Altenkirch §4.5). Open whether mathlib's coinduction tactic discharges the
   `Sound` greatest-fixpoint cleanly or needs an explicit `▶`/`Löb` encoding (Birkedal) — the latter is
   heavier but makes the guard a typed obligation.

4. **[G→T] IVsC's assumptions vs dregg's PQ posture.** Afshar–Goyal's zk-IVsC is from DLIN/DDH/LWE +
   seBARGs; dregg's STARK substrate is hash/PQ-oriented. The *existence* of standard-assumption IVsC is
   the proof that unbounded succinct streaming verification is achievable, but a **PQ** IVsC (LWE-only,
   or a STARK-recursion analogue) is the real target. Valiant-impossibility says a plain-RO/hash-only
   construction *cannot* exist (if ZK), so a hash-only PQ IVsC is ruled out — there must be a
   lattice/structured assumption. Open: reconcile with the lattice-folding line already in the library
   (LatticeFold/Neo) as the PQ IVsC candidate.

5. **[T] Controlled-malleability transform class for dregg.** Faonio–Russo give *linear homomorphism* as
   the admissible `T` for sumcheck/PST SNARKs; dregg's accumulator-slack-reset and epoch-rebind need to
   be shown to *lie inside* such a `T` (or to be re-proves in disguise). Until that class is pinned,
   **default rejuvenation = re-prove-from-log** (option 1), which is unconditionally safe.

6. **[T] Bisimulation finiteness / cyclicity.** Crêpe works because regex derivatives have *finitely
   many* equivalence classes, so the bisimulation certificate is finite/cyclic. A dregg cell's state
   space is **not** finite — so the soundness bisimulation is *not* exhibited as a finite cycle; it is
   discharged *coinductively* (one guarded step) à la Löb, **not** enumerated. Crêpe is the precedent
   that "coinduction lives in a ZK proof," but dregg's instance is the corecursive (Löb) form, not the
   finite-cycle form. Worth stating explicitly so no one tries to enumerate the bisimulation in-circuit.
