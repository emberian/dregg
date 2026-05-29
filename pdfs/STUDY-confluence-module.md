# STUDY — `Metatheory/Confluence.lean`: the third judgement, formally

**For:** the rebuild-driving agent (author of `docs/rebuild/dregg2.md` + `ROADMAP.md`).
**What this is:** the module design for the missing Lean home of dregg2's third judgement.
`dregg2 §2.3` declares **I-confluence a co-equal third judgement** (conservation ⊥ ordering ⊥
I-confluence) and `§2.2` makes tier-1 finality eligibility *depend* on it (`I(x) ∧ I(y) ⇒ I(x⊔y)`
⟹ tier-1-eligible, else a **static type error**). But `§8`'s module map (Core / Laws /
Authority / Boundary) has **no module for it** — so the "three judgements" framing is, as
`discoveries-2 §0` flags, *2-in-Lean-plus-1-in-prose*. This closes that. Tags `[G]`
(grounded-in-paper) / `[C]` (grounded-in-dregg-code) / `[F]` (forward-design).

**Grounding:** Bailis (`coordination-avoidance-bailis-vldb`, Def 1–6 + Thm 1, lines 449–650 of
the extracted text) for the I-confluence definition; Gomes–Kleppmann
(`verifying-strong-eventual-consistency-crdt-isabelle`, OOPSLA'17 — Isabelle locales
`happens-before` / `network` / `interp` + the abstract convergence theorem) for the
"prove-once / instantiate-per-type" template; Burckhardt
(`replicated-data-types-spec-verification-optimality-popl14`) for the abstract-state /
visibility model; Kaki/Nagar (`certified-mergeable-replicated-data-types-pldi22`,
reduce-to-sequential-spec) and Katara (`katara-...-verified-lifting`, synthesize-the-merge) for
the constructive classifier; CALM (`keeping-calm-distributed-consistency`, Thm 1: consistent +
coordination-free ⟺ monotonic) and CryptoConcurrency (`cryptoconcurrency.pdf`) for the
consensus-reduction link.

---

## Exec summary (~10 lines)

1. **The judgement.** I-confluence is a predicate over a cell's **state join-semilattice ×
   write-set**: `IConfluent I` ≝ for all reachable `x y` with a common ancestor,
   `I x → I y → I (x ⊔ y)` (Bailis Def 6, restricted to `I-T`-reachable states — the
   common-ancestor side-condition is **load-bearing**, not decorative).
2. **Tier-1-eligibility** is the *classifier* `tier1_ok : CellProgram → Prop` = "the cell's state
   forms a `BoundedJoinSemilattice` **and** its `StateConstraint` invariant is `IConfluent`."
   Decidable on the structured fragment of the catalog; an explicit `Searchable` plugin (the
   §1 verify/find seam) on the rest.
3. **Independence theorems (the §2.3 claims).** Concrete witnesses: a two-withdrawal pool gives
   `linear ∧ ¬IConfluent`; a grow-only counter gives `IConfluent ∧ ¬linear`. Both `sorry`-stated
   day-1, dischargeable with finite models.
4. **Gomes–Kleppmann template.** A Lean `class NetworkModel` (happens-before preorder +
   delivery + an `interp` interpretation) + `concurrent_ops_commute`, proved once; **each
   `CellProgram` instantiates it.** The `StateConstraint` catalog splits: `Monotonic` /
   `WriteOnce` / `CapabilityUniqueness` / set-union are I-confluent *by construction*;
   `Gte`/`Lte`/`SumEquals`/`BoundedBy`/`RateLimitBySum` provably are **not** (the overspend).
5. **Consensus-reduction link.** I-confluence *reduces from consensus* (CryptoConcurrency):
   tier-1-ineligibility is **exactly** "this write needs agreement." `Confluence.lean` exposes
   `needsConsensus := ¬ tier1_ok`, which `Boundary.lean`'s JointTurn consumes to pick the commit
   tier at the cells' **join** (`§2.2` cross-tier rule).
6. **Placement.** `Confluence.lean` sits **parallel to `Laws.lean`**, depends only on `Core.lean`
   (it reuses the `Cell`/`CellProgram`/`StateConstraint` types and the conservation `count`), and
   **feeds `Boundary.lean`** (the JointTurn's tier-selection premise) — it is *not* downstream of
   Authority. Risk: the common-ancestor restriction and the decidability boundary of the
   classifier are the two places this can quietly become unsound.

---

## 1. The judgement, formally `[G/F]`

### 1.1 The state lattice

A cell whose state can be merged concurrency-safely is one whose state space is a **bounded
join-semilattice** with a least element (`⊥` = the genesis/empty state) — the CvRDT shape
(`discoveries §4`: the blocklace is a join-semilattice CvRDT, join = set/DAG union, proven via
Merkle-CRDT). mathlib4 supplies this directly; we do **not** roll our own order theory.

```lean
-- Metatheory/Confluence.lean
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder
import Metatheory.Core              -- Cell, CellProgram, StateConstraint, count

namespace Dregg.Confluence

/-- A cell's mergeable state is a bounded join-semilattice: `⊔` is the CvRDT merge,
    `⊥` the genesis state. (Bailis's `D` with `⊔`; the CvRDT of `discoveries §4`.) -/
class CellLattice (σ : Type*) extends SemilatticeSup σ, OrderBot σ

/-- The invariant a `StateConstraint` denotes, as a state predicate. The classifier of
    §1.2 is what computes this from a `CellProgram`; here it is the abstract `I`. -/
abbrev Invariant (σ : Type*) := σ → Prop
```

The write-set enters through *reachability*: I-confluence is not quantified over **all** lattice
pairs (that is Bailis's strictly-stronger "join-closure of validity," which fails for almost
everything), but over states **actually reachable by the cell's transactions from a common
ancestor**. This is the part a prose statement always drops and the part that makes the theorem
true. We model it with an inductive reachability relation parameterized by the write-set `W`
(the set of admissible single-turn transformations the `CellProgram` permits):

```lean
/-- The admissible single-turn transformations of a cell — its write-set.
    Derived from the `CellProgram`'s admissibility filter (`dregg2 §1.5`):
    `W = { t : σ → σ | program admits t }`. -/
abbrev WriteSet (σ : Type*) := Set (σ → σ)

/-- `I-T`-reachable (Bailis): reachable from `⊥` by applying write-set transactions and
    merging, with every intermediate state I-valid. The common-ancestor structure is the
    `merge` constructor's two-premise shape. -/
inductive Reachable {σ} [CellLattice σ] (I : Invariant σ) (W : WriteSet σ) : σ → Prop
  | init : I ⊥ → Reachable I W ⊥
  | step {x t} : Reachable I W x → t ∈ W → I (t x) → Reachable I W (t x)
  | merge {x y} : Reachable I W x → Reachable I W y → I (x ⊔ y) → Reachable I W (x ⊔ y)
```

### 1.2 `IConfluent` and the tier-1 classifier

```lean
/-- **The judgement.** Bailis Def 6, scoped to reachable states with a common ancestor.
    For dregg: do concurrent admissible writes merge invariant-safely? -/
def IConfluent {σ} [CellLattice σ] (I : Invariant σ) (W : WriteSet σ) : Prop :=
  ∀ x y, Reachable I W x → Reachable I W y →
         (∃ a, Reachable I W a ∧ a ≤ x ∧ a ≤ y) →   -- common ancestor (Bailis fn.4)
         I (x ⊔ y)

/-- The denotation of a cell program: its state lattice carrier, its write-set, its invariant.
    Produced from a `CellProgram` + `StateConstraint` catalog (`dregg2 §1.5`). -/
structure CellSemantics where
  σ        : Type*
  inst     : CellLattice σ
  W        : WriteSet σ
  I        : Invariant σ

/-- **The tier-1-eligibility classifier** (`§2.2` well-formedness side-condition).
    `tier1_ok p` ⟺ the cell's state is a bounded join-semilattice with invariant-preserving
    joins. PROP form (the soundness gate); a `Bool`/`Decidable` form exists on the
    structured fragment (§3). -/
def tier1_ok (s : CellSemantics) : Prop :=
  @IConfluent s.σ s.inst s.I s.W

/-- The §2.2 static-type-error: selecting tier-1 for a non-I-confluent cell is unrealizable.
    `FinalityTier` is the §2.2 enum {causal, ackThreshold, bft, constitutional}. -/
def tierAdmissible (s : CellSemantics) : FinalityTier → Prop
  | .causal        => tier1_ok s        -- tier-1 ⟹ MUST be I-confluent (else type error)
  | _              => True              -- tiers ≥ 2 carry no I-confluence obligation
```

**Note on `Bool` vs `Prop` (the §1 verify/find seam, honestly typed).** `tier1_ok` is `Prop`
because `IConfluent` quantifies over an infinite reachable set — *not generally decidable*. The
**eligibility check the compiler runs** is a `Decidable`/`Bool` *classifier over the structured
constraint fragment* (§3) plus a `Searchable` escape hatch for the rest — exactly the `Verify` /
`Searchable` split of `Laws.lean`. This keeps the TCB the *verifier*: a plugin may *prove* a cell
I-confluent (emit a witness — e.g. "this state is a semilattice and this invariant is a downward-/
upward-closed monotone predicate"), and `Confluence.lean` only *checks* the witness; it never has
to *search* for the merge. The constructive synthesis side (Katara) is the untrusted solver.

---

## 2. Independence theorems (the §2.3 claims, as Lean targets) `[G/F]`

`§2.3` asserts the two axes are genuinely independent: `linear ⇏ I-confluent` and
`I-confluent ⇏ linear`. These are the *defining* sanity checks of the third judgement — if either
fails the module collapses back into Core (conservation) or Laws. Both are provable with **finite
concrete witnesses** (no `sorry` needed once the scaffolding lands; state them day-1 with `sorry`).

`linear` here is the Core conservation predicate: `count` is invariant on the turn
(`Core.conservation_ordinary`).

### 2.1 `linear ⇏ I-confluent` — the two-pool-withdrawal witness

The canonical Bailis/CryptoConcurrency overspend: a shared pool with `balance ≥ 0`. Two
withdrawals are *each* linear (conserve value — the withdrawn amount leaves the pool and lands in
the actor) and *each* I-valid, yet their merge violates the invariant. Conflict is **not
pairwise** (`discoveries §4`): the escalation predicate is a *sum over the whole concurrent set*.

```lean
/-- Pool state: a single balance. Lattice = max (the natural CvRDT join for "how much was taken"
    is on the *withdrawal multiset*; here we model the divergent-balance merge directly). -/
abbrev Pool := ℤ
instance : CellLattice Pool := ⟨⟩   -- ℤ is not bounded-below; use the withdrawal-set encoding (below)

/-- Invariant: balance never negative. -/
def poolInv (start : ℤ) : Invariant (Multiset ℤ) := fun ws => start - ws.sum ≥ 0

/-- The two withdrawals: each linear (the withdrawn value is conserved), each individually valid. -/
theorem linear_not_iconfluent :
    ∃ (W : WriteSet (Multiset ℤ)) (start : ℤ),
      -- each write conserves value across the (pool ⊗ actor) boundary  [Core.count invariant]
      (∀ t ∈ W, ConservesValue t) ∧
      -- but the joint merge of two individually-valid withdrawals is invalid
      ¬ IConfluent (poolInv start) W := by
  sorry  -- witness: start = 10; W = {withdraw 6}; two concurrent withdraws ⇒ merge sum 12 > 10
```

The witness: `start = 10`, two replicas each withdraw `6` (each leaves `4 ≥ 0`, valid), merge =
`-2 < 0`. Linear throughout (value is conserved into the two actors); not I-confluent. This is the
formal content of `§2.2`'s "`balance≥0` is not [tier-1-safe] (needs ≥tier-2 or single-owner per
CryptoConcurrency)."

### 2.2 `I-confluent ⇏ linear` — the grow-only counter witness

A monotone counter (G-Counter) merges freely (`⊔ = max` per replica; or pairwise-max of vectors)
— provably I-confluent under any invariant of the form `value ≥ k` (upward-closed under `⊔`) — but
**increment is not conservation-preserving**: it *creates* count from nothing (no mint/burn
generator). So it satisfies the third judgement while failing Law 1.

```lean
abbrev GCounter := ℕ
instance : CellLattice GCounter := { sup := max, bot := 0, /- … -/ }

def counterInv : Invariant GCounter := fun n => n ≥ 0   -- trivially upward-closed

theorem iconfluent_not_linear :
    ∃ (W : WriteSet GCounter),
      IConfluent counterInv W ∧
      ¬ (∀ t ∈ W, ConservesValue t) := by
  sorry  -- witness: W = {incr}; max-merge preserves `≥ k` (I-confluent);
         -- incr changes `count` with no mint/burn generator (¬ conserves)
```

Together these are the **`independence` corollary**: `IConfluent` is logically independent of
`ConservesValue` — neither implies the other — so the third judgement carries information neither
Core nor Laws has. State it as the headline export of the module:

```lean
theorem judgements_independent :
    (∃ W I, (∀ t ∈ W, ConservesValue t) ∧ ¬ IConfluent I W) ∧
    (∃ W I, IConfluent I W ∧ ¬ (∀ t ∈ W, ConservesValue t)) :=
  ⟨linear_not_iconfluent', iconfluent_not_linear'⟩
```

---

## 3. The Gomes–Kleppmann template + StateConstraint mapping `[G/C]`

### 3.1 Prove-SEC-once, instantiate-per-`CellProgram`

Gomes–Kleppmann's contribution is *structural*: they prove an **abstract convergence theorem**
once over a parameterized network, then every concrete CRDT instantiates the locale. We mirror
their three Isabelle locales as Lean classes (their `happens-before`, `network`, and the `interp`
interpretation — extracted text lines 336–340, 393–395, 530):

```lean
/-- G-K's `happens-before = preorder hb-weak hb`: a causal preorder on operations. -/
class HappensBefore (op : Type*) extends Preorder op

/-- G-K's `network` locale: an interpretation `interp : op → σ → σ` (their `h-i`),
    operations delivered in an hb-consistent order. Parameterized; proved once. -/
class NetworkModel (op σ : Type*) [HappensBefore op] [CellLattice σ] where
  interp        : op → σ → σ
  /-- G-K `concurrent-ops-commute`: concurrent ops commute (the SEC hypothesis). This is the
      ONE obligation each cell discharges; everything else is inherited. -/
  concComm      : ∀ x y : op, ¬ (x ≤ y) → ¬ (y ≤ x) →
                    interp x ∘ interp y = interp y ∘ interp x

/-- G-K's abstract convergence theorem, dregg form: if concurrent ops commute and delivery is
    hb-consistent, any two replicas that have seen the same op-set converge — AND the converged
    state is the lattice join. Proved ONCE over the class; `sorry` day-1. -/
theorem sec_of_commute {op σ} [HappensBefore op] [CellLattice σ] [NetworkModel op σ]
    (xs ys : List op) (hperm : xs.Perm ys) (hxs : HbConsistent xs) (hys : HbConsistent ys) :
    applyOps xs ⊥ = applyOps ys ⊥ := by
  sorry

/-- **The bridge to I-confluence (the dregg-specific step G-K do not take):**
    commutativity + an invariant preserved by each op ⟹ `IConfluent`. This is what makes
    `sec_of_commute` *imply tier-1 eligibility*, not just convergence. -/
theorem iconfluent_of_commute_inv {op σ} [HappensBefore op] [CellLattice σ] [NetworkModel op σ]
    (I : Invariant σ) (hpres : ∀ o s, I s → I (NetworkModel.interp o s)) :
    IConfluent I (Set.range (fun o => NetworkModel.interp o)) := by
  sorry
```

So **each `CellProgram` instantiates `NetworkModel`** (supplies `interp` from its effect-semantics
and discharges `concComm`), and tier-1-eligibility falls out of `iconfluent_of_commute_inv` —
"prove SEC once, instantiate per type" becomes "prove `iconfluent_of_commute_inv` once, instantiate
per `CellProgram`." Burckhardt's abstract-state/visibility model is the *justification* for keeping
`op`/`hb` abstract (we quantify over visibility, not a concrete log); Kaki/Nagar's
reduce-to-sequential-spec and Katara's synthesize-the-merge are the **untrusted constructive
side** — given a sequential `CellProgram` they *produce* the `interp` + a candidate `concComm`
proof obligation, which `Confluence.lean` checks. (TCB = checker, never synthesizer — `§1` seam.)

### 3.2 The `StateConstraint` catalog mapping (the concrete classifier table)

dregg's ~29-variant `StateConstraint` catalog (`cell/src/program.rs:597-829`, enumerated in
`dregg2 §1.5`) partitions cleanly. This table **is** the decidable core of `tier1_ok`:

| `StateConstraint` | I-confluent? | why (lattice + merge argument) |
|---|---|---|
| `Monotonic` / `StrictMonotonic` / `MonotonicSequence` | **YES, by construction** | grow-only; `⊔ = max`; invariant `≥ k` is upward-closed (the §2.2 G-counter). The CALM-monotone fragment. |
| `WriteOnce` / `Immutable` | **YES** | once-set; `⊔` = "the set value" (LWW-degenerate / single-writer); concurrent writes either agree or are excluded by uniqueness. |
| `CapabilityUniqueness` (hash-keyed nullifier) | **YES** | a **G-Set** keyed by hash; `⊔` = set union; "this nullifier appears at most once" is preserved by union **because keys are collision-free** (`§2.2`: "hash-keyed nullifier uniqueness is tier-1-safe"). |
| `AllowedTransitions` (state machine) | **YES iff** the transition relation is a join-semilattice-monotone (confluent rewriting); else NO | needs the per-cell `concComm` discharge. |
| `PreimageGate` / `TemporalGate` / `Witnessed` / `TemporalPredicate` | **YES** (guard-only) | a pure admission guard that does not constrain the *merge*; commutes trivially. |
| `FieldGte`/`FieldLte`/`BoundedBy` | **NO** | a *threshold* invariant: `x,y` each below the bound can merge above it (the overspend shape). Not closed under `⊔`. |
| `SumEquals` / `SumEqualsAcross` / `BoundDelta(EqualAndOpposite)` | **NO** (needs consensus or single-owner) | a *conservation-coupled* invariant; the merge double-counts. **This is exactly the JointTurn / CG-5 territory** — see §4. |
| `RateLimit` / `RateLimitBySum` | **NO** | rate is a sum-over-window; two replicas each under-limit jointly exceed. |
| `FieldDelta` / `FieldDeltaInRange` / `BoundDelta` | **case-split** | a *relative* bound on one turn is fine; an *absolute* bound on the merged delta is not. |
| `SenderAuthorized` / `Renounced` | **orthogonal** | an authority gate (Positional), not a state-merge property — does not enter `IConfluent`. |
| `AnyOf` (Heyting ⊔) | **YES iff** all disjuncts are; the join of I-confluent invariants is I-confluent | reuses `Laws.lean`'s Heyting algebra. |
| `Custom { ir_hash }` / `Circuit { circuit_hash }` | **opaque ⟹ `Searchable`** | classifier cannot decide; requires a plugin-emitted I-confluence witness (or defaults to ineligible — *fail-closed*, matching `Cases` default-deny, `program.rs:1106`). |

**The decidable classifier** is the function that reads a `Predicate([c…])`'s constraint vector,
looks each up in this table, and returns `tier1_ok` iff **every** constraint is in the YES column
(with the case-splits resolved by their parameters). `AnyOf`/`Predicate` compose by the
join/meet rules. The opaque `Circuit`/`Custom` cases **fail closed** (ineligible unless a witness
is supplied) — the conservative, sound default.

```lean
/-- Decidable eligibility over the structured catalog. Returns `false` (fail-closed) on opaque
    constraints unless an `IConfluenceWitness` plugin supplies a checked proof. -/
def classifyTier1 : CellProgram → Bool
  | .none                  => true                       -- terminal: trivially mergeable
  | .predicate cs          => cs.all constraintIsIConfluent
  | .cases tcs             => tcs.all (fun c => c.constraints.all constraintIsIConfluent)
  | .circuit _             => false                      -- opaque ⟹ fail-closed
where
  constraintIsIConfluent : StateConstraint → Bool := /- the table above -/ sorry

/-- Soundness of the classifier: `classifyTier1 p = true → tier1_ok (denote p)`.
    (Completeness is NOT claimed — the verify/find seam: a `false` may be a true-but-unproven
    I-confluent cell, recoverable only via a witness plugin.) -/
theorem classifyTier1_sound (p : CellProgram) :
    classifyTier1 p = true → tier1_ok (denote p) := by sorry
```

---

## 4. The CryptoConcurrency link — I-confluence *reduces from consensus* `[G/F]`

CryptoConcurrency's result (`cryptoconcurrency.pdf`; cross-confirmed by `discoveries §4`):
**single-owner state never needs consensus; shared state needs it only on an actual conflict —
dynamically detected.** CALM (`keeping-calm`, Thm 1) gives the static converse: *monotonic ⟺
coordination-free*. Together they pin the meaning of tier-1-ineligibility precisely:

> **tier-1-ineligible (`¬ tier1_ok`) ⟺ "this write needs agreement."** A non-I-confluent
> invariant is exactly one whose safe execution *reduces from consensus* — the merge can produce
> an invalid state, so some replica must *agree* on a serialization before committing.

This is the formal hinge that makes `Confluence.lean` *do something* rather than just classify. We
export the consensus obligation as a derived predicate and connect it to `§2.2`'s tier selection:

```lean
/-- CryptoConcurrency: ineligibility for coordination-free commit ⟺ a consensus obligation.
    This is the negation of the classifier, lifted to the finality-tier selection. -/
def needsConsensus (s : CellSemantics) : Prop := ¬ tier1_ok s

/-- The §2.2 cross-tier rule, formally: a cell's *minimum admissible tier* is causal (tier-1)
    iff I-confluent, else it must escalate to ≥ tier-2 (ack/BFT). The "static type error" of
    §2.2 is `tierAdmissible s .causal` being *false* — a type-level, not runtime, rejection. -/
theorem tier_floor (s : CellSemantics) :
    tierAdmissible s .causal ↔ ¬ needsConsensus s := by
  unfold tierAdmissible needsConsensus; simp

/-- **Conflict is not pairwise** (`discoveries §4`, CryptoConcurrency): the escalation trigger is
    a sum/coverage predicate over the WHOLE concurrent write-set, not pairwise checks. The
    `IConfluent` quantifier ranges over arbitrary reachable `x y` (whose merge may aggregate many
    concurrent writes) — this captures the n-way overspend the pairwise check misses. -/
theorem conflict_is_setwise : True := trivial  -- documentary: encoded in the `Reachable.merge` shape
```

**Why this is `reduces-from`, not `equals`.** dregg never *builds* a consensus object in Lean —
the actual agreement is `§2.2`'s tier-2/3/4 finality plugins (Cordial-Miners τ-BFT etc.), discharged
empirically/operationally, **not** in the metatheory (`§8`: liveness + crypto-soundness are *not*
in the Lean law). `Confluence.lean` only proves the **reduction direction**: *if* `needsConsensus s`
*then* a tier-1 commit is unsound — i.e. it generates the *obligation* that a higher tier must
discharge. The tier-1 *eligibility* direction (`tier1_ok ⟹ safe coordination-free commit`) is the
provable, in-Lean half (via `iconfluent_of_commute_inv` + Bailis Thm 1's necessary-and-sufficient).

---

## 5. Module placement & dependencies `[F]`

### 5.1 Where it sits

```
Metatheory/Core.lean ───────────────┐  (Cell, CellProgram, StateConstraint, count/ConservesValue)
   │                                 │
   ├──► Metatheory/Laws.lean         ├──► Metatheory/Confluence.lean   ◄── NEW, parallel to Laws
   │      (Galois, Heyting, Verify)  │      (CellLattice, IConfluent, tier1_ok, NetworkModel,
   │            ▲                     │       classifyTier1, needsConsensus, judgements_independent)
   │            └─── reuses Heyting ──┘            │
   │                  for AnyOf                    │
   ├──► Metatheory/Authority/Positional.lean       │  (independent — Confluence does NOT depend on it;
   │                                               │   SenderAuthorized/Renounced are orthogonal)
   └──► Metatheory/Boundary.lean  ◄────────────────┘
          (JointTurn tier-selection consumes `needsConsensus`/`tierAdmissible`)
```

- **Depends on `Core.lean` only.** It reuses `Cell` / `CellProgram` / the `StateConstraint`
  catalog and the conservation `count`/`ConservesValue` (needed for the independence theorems,
  which compare against linearity). It does **not** depend on Authority — the `SenderAuthorized`/
  `Renounced` constraints are *orthogonal* (an authority gate, not a state-merge property), so
  Confluence sits **parallel to `Laws.lean`**, both fed by Core.
- **Reuses `Laws.lean`'s Heyting algebra** for the `AnyOf` composition rule (the join of
  I-confluent invariants), but only as a light import — no circular dependency (Laws does not need
  Confluence).
- **Discharge order:** slots between Laws and Boundary in the `§8`/ROADMAP table. It can be
  scaffolded **in parallel with Laws** (both are Core-only), and its `sorry`s discharged *before*
  Boundary, because Boundary's JointTurn needs `needsConsensus`/`tierAdmissible` as a premise. So
  the updated discharge order is: **Core + Laws + Confluence (parallel) → Authority/Positional →
  Boundary (+ JointTurn)**.

### 5.2 How it feeds `Boundary.lean`'s JointTurn (the cross-tier commit at the join)

`§1.6` + ROADMAP Phase 3 + the Boundary `sorry`-list: a turn over N cells is a morphism on
`C₁ ⊗ … ⊗ Cₙ`, and the JointTurn binding (CG-2 turn-identity pullback ⊗ CG-5 cross-side
conservation) is an **explicit premise, never derived** (`νF₁ ⊗ νF₂` is not final — `§1.6`). The
`§2.2` cross-tier rule states the *commit tier* is the **join of the written cells' tiers**, with
effects held until the join-tier commits. `Confluence.lean` supplies precisely the per-cell input
that join needs:

```lean
-- in Metatheory/Boundary.lean, the JointTurn object gains a tier-selection field:
structure JointBinding (cells : List CellSemantics) where
  sharedTurnId : TurnId                                  -- CG-2 pullback
  crossSideConservation : ConservesValueAcross cells     -- CG-5 equalizer (Core)
  /-- the commit tier is the JOIN of each cell's required tier; a cell is causal iff I-confluent,
      else it pulls the whole JointTurn up to its tier (the §2.2 "commit at the join"). -/
  commitTier : FinalityTier := cells.foldr (fun c acc => max (requiredTier c) acc) .causal

/-- `requiredTier` is the Confluence export: causal if I-confluent, else escalated. -/
def requiredTier (s : CellSemantics) : FinalityTier :=
  if Confluence.tier1_ok s then .causal else .ackThreshold   -- ≥ tier-2; concrete tier from §2.2 config

/-- The joint-soundness theorem (Boundary, BUILD-NEW): per-cell step-completeness + the binding
    + EACH cell committed at ≥ its requiredTier ⟹ the JointTurn is sound. The Confluence premise
    is what forbids a non-I-confluent cell from riding the tier-1 fast path inside a JointTurn. -/
theorem joint_sound (cells : List CellSemantics) (b : JointBinding cells)
    (hsc : ∀ c ∈ cells, StepComplete c)
    (htier : ∀ c ∈ cells, committedTier c ≥ requiredTier c) :
    Sound (JointTurn cells b) := by sorry
```

So the seam is: **`Confluence.requiredTier` → `Boundary.JointBinding.commitTier`**. Confluence
classifies *each cell's* fast-path eligibility; Boundary takes the **join** over the tuple and
makes it a soundness premise of the cross-cell turn. This is the §2.2 cross-tier rule wired into
the §1.6 tensor: the I-confluent cells in a JointTurn stay coordination-free; one non-I-confluent
cell forces the whole atomic step up to its tier (held until that tier commits, no downgrade).

---

## 6. Risks `[F]`

1. **The common-ancestor restriction is load-bearing and easy to drop.** Bailis's footnote-4
   common-ancestor condition (`Reachable.merge`'s two-premise shape) is what makes `Uniqueness`
   I-confluent at all — without it, two independently-generated unique-ID sets merge to an invalid
   state (his own counterexample). If the Lean `IConfluent` quantifies over *all* lattice pairs
   instead of *reachable-with-common-ancestor* pairs, the classifier under-approximates wildly and
   `CapabilityUniqueness` mis-classifies as ineligible. **Mitigation:** keep `Reachable` and the
   `∃ a` ancestor premise in the definition; do not "simplify" to `∀ x y, I x → I y → I (x⊔y)`.

2. **The decidable/undecidable boundary of the classifier.** `classifyTier1` is sound but **not
   complete** by design (the verify/find seam). The risk is someone "fixing" the incompleteness by
   making `Circuit`/`Custom` default to *eligible* — silently admitting a non-I-confluent cell to
   tier-1, the exact unsoundness `§2.2` forbids. **Mitigation:** opaque constraints **fail
   closed** (return `false`); eligibility is recoverable only via a *checked* witness plugin, never
   by a permissive default. Mirror `Cases` default-deny (`program.rs:1106`).

3. **`reduces-from-consensus` is a one-directional obligation, not an equivalence.** The Lean law
   proves only `needsConsensus ⟹ tier-1-unsound`. The *converse* (tier-1-eligible ⟹ the
   coordination-free runtime is actually safe) leans on Bailis Thm 1's sufficiency **and** on the
   runtime's tier-1 plugin actually being a correct CvRDT merge — the latter is the Gomes–Kleppmann
   `concComm` discharge per cell, **not** automatic. **Mitigation:** require each `CellProgram`'s
   `NetworkModel` instance to *prove* `concComm` (no axiomatizing it); the structured catalog
   entries (§3.2) come with their `concComm` proof built in, the `Custom` ones must supply it.

4. **`CellLattice` may not exist for every cell.** A cell whose `Preserves` state has no natural
   bounded join-semilattice (e.g. a free-form mutable record with `Gte` thresholds) simply has no
   `CellLattice` instance — which is *correct* (it's tier-1-ineligible) but means `tier1_ok` is
   only *defined* where the instance exists. **Mitigation:** make the eligibility classifier total
   by returning `false` (ineligible) wherever a `CellLattice` instance cannot be synthesized — the
   absence of a lattice *is* the type error `§2.2` wants. Tie this to `classifyTier1`'s
   `StateConstraint`-driven instance search.

5. **Crypto-soundness must stay out (the §8 invariant).** `needsConsensus` generates an obligation
   a *finality plugin* discharges; the binding/extractability of the consensus certificate is a
   circuit/operational obligation, **never** merged into `Confluence.lean` — same discipline as
   `Verify`-as-decidable-oracle in `§8`. The module proves the *reduction*, not the consensus.

---

## Net

Adding `Metatheory/Confluence.lean` makes the third judgement real-in-Lean: a
`BoundedJoinSemilattice`-based `IConfluent` predicate (Bailis Def 6, common-ancestor-scoped), a
fail-closed `classifyTier1` classifier over the `StateConstraint` catalog (the §3.2 table is its
decidable core), the two `§2.3` independence theorems as finite-witness targets, a Gomes–Kleppmann
`NetworkModel` class proved-once-instantiated-per-`CellProgram`, and a `needsConsensus` export that
wires the CryptoConcurrency consensus-reduction into `Boundary.lean`'s JointTurn tier-selection at
the **join** of the written cells' tiers. It depends only on Core, sits parallel to Laws, and is
dischargeable before Boundary — restoring the "three co-equal judgements" framing to three-in-Lean.
