/-
# Dregg2.Spec.ExecRefinement — the FIRST refinement square: `Exec ⊑ Spec`.

Until now the executable kernel (`Dregg2.Exec.Kernel`) and the matured abstract spec
(`Dregg2.Spec.*`) were two disjoint worlds: `Exec` proved its OWN conservation
(`exec_conserves`) and its OWN authority gate (`exec_authorized` / `authorizedB`), but it
never *touched* `Spec` (grep: NONE). This module is the beachhead that turns "Exec does not
touch Spec" into "**Exec ⊑ Spec** (first square proved)" — the start of re-founding `Exec` as
a *refinement of* the matured `Spec`, exactly the l4v `Design ⊑ Abstract` move, here
`Dregg2.Exec.Kernel ⊑ Dregg2.Spec.{Conservation,Guard,Authority}`.

A refinement square is the commuting diagram

```
        Refines
   k  ───────────▶  a            (the simulation relation: balances + caps correspond)
   │                │
   │ exec k t       │ abstract step (Spec law)
   ▼                ▼
   k' ───────────▶  a'
        Refines
```

We do NOT prove the *full* operational diagram (that needs an abstract small-step relation —
the same residue `Proof/Refine` and `Spec.Authority.only_connectivity_…` already flag). We DO
prove the two tractable PROJECTIONS of the square — conservation and authority — cleanly:

  1. **Conservation refinement** (`exec_refines_conservation`, PROVED-clean): an
     `exec`-committed step's per-cell balance deltas satisfy `Spec`'s
     `conservedInDomain Domain.balance` — i.e. `Exec.exec_conserves` IS `Spec`'s `Σδ = 0` law
     over `Bal = ℤ`. The toy single-domain ℤ ledger is *exactly* the `balance` domain of the
     multi-domain abstract conservation; the executable `Finset.sum` debit/credit cancellation
     is the `Bal = ℤ` instance of `Spec.conservation_over_monoid`.

  2. **Authority refinement** (`exec_authz_refines_guard`, PROVED-clean): the executable cap
     gate `Exec.authorizedB` admitting a turn ⇒ the corresponding abstract `Spec.Guard.admits`
     (a `firstParty` gate over the turn) is `true`. The decidable kernel gate REFINES the
     abstract `Guard` demand. We additionally tie `authorizedB`-by-ownership to
     `Spec.Authority.Graph.has` / `confers` on a graph reconstructed from `Exec.caps`, in the
     same shape `Coherence.guard_is_authority_conferral` uses (conferral-is-a-`Guard`). We do
     NOT import `Coherence` (it is not pre-built); we re-derive the slice directly from
     `Spec.Guard`/`Spec.Authority`.

  3. **The simulation relation + commuting square** (`Refines`, `exec_step_refines`): the
     conservation+authority PROJECTIONS of the square are PROVED; the residual operational
     thread (the abstract small-step relation that would let us *construct* `a'` from `a` and
     show full bisimulation) is honestly `-- OPEN:`-marked with a precise statement of what is
     missing.

## Discipline (matching the lib)
Abstract value types where the Spec side is abstract; faithful `Prop`s; `#assert_axioms` on
the clean keystones; honest `-- OPEN:` only on the genuine operational gap; NO
`axiom`/`admit`/`native_decide`/`:True`/`Iff.rfl`-as-content/sorry-alias except the single
localized operational residue. Imports ONLY existing built modules. Does NOT modify any
existing file — it only *consumes* `Exec.Kernel` and the `Spec.*` web.
-/
import Dregg2.Exec.Kernel
import Dregg2.Exec.RecordKernel
import Dregg2.Spec.Conservation
import Dregg2.Spec.Guard
import Dregg2.Spec.Authority
import Dregg2.Tactics
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Dregg2.Spec

open Dregg2.Exec
-- NB: `Cap`/`Caps`/`Auth`/`Label` here are the EXECUTABLE authority carriers
-- (`Dregg2.Authority.Cap`, the `node`/`endpoint` inductive). They are deliberately NOT
-- `open`ed unqualified, because inside `Dregg2.Spec` the bare name `Cap` must resolve to the
-- ABSTRACT `Spec.Cap CellId Rights` (the rights-labelled-edge structure) that `confers`/`Graph`
-- read. We open only the non-conflicting names; the executable `Cap` is written `Authority.Cap`
-- and its constructors `Authority.Cap.node`/`Authority.Cap.endpoint` at the few sites that need
-- the inductive. (This is the load-bearing disambiguation of the refinement: two `Cap`s, one
-- executable and one abstract, are exactly what `Exec ⊑ Spec` must bridge.)
open Dregg2.Authority (Caps Auth Label capAuthConferred)
open Dregg2.Laws

open scoped BigOperators

/-! ## §1 — Conservation refinement: `Exec.exec_conserves` IS `Spec`'s `Σδ = 0` over ℤ.

The executable kernel conserves a SINGLE cleartext-ℤ ledger (`Exec.total`, a `Finset.sum`).
`Spec.Conservation` states `Σδ = 0` per `Domain`, parametric over a value monoid `Bal`, and
consumes the deltas as a `List Bal`. We exhibit the kernel's per-cell balance deltas as the
`List ℤ` that `conservedInDomain Domain.balance` reads, and prove a committed step's deltas
conserve — bridging `Exec.total`/`Finset.sum` to `Spec`'s `List.sum` exactly as `Coherence`
bridged the hyperedge (`Finset.sum_map_toList`).

So the toy single-ℤ ledger conservation is the `balance`-domain case of the multi-domain
abstract law: `Bal := ℤ`, `Domain := Domain.balance`. -/

/-- **`refineConservation s s'`** — the per-cell balance deltas of a step `s ⟶ s'`, packaged
as the `List ℤ` that `Spec.conservedInDomain` consumes. We enumerate the live accounts of the
*pre*-state (`exec` never changes `accounts`, only `bal`) and read off `s'.bal c - s.bal c`
per cell. This is the kernel's debit/credit ledger viewed as a conservation `deltas` list —
the `Bal = ℤ` instance of the abstract delta list. -/
noncomputable def refineConservation (s s' : KernelState) : List ℤ :=
  s.accounts.toList.map (fun c => s'.bal c - s.bal c)

/-- The list-sum of the per-cell deltas equals `total s' - total s` (over the SHARED account
set — `exec` preserves `accounts`). The `Finset.sum_map_toList` bridge from `Spec.Coherence`,
applied to the ℤ ledger: it turns the `List.sum` `Spec` reads into the `Finset.sum` `Exec`
uses. -/
theorem refineConservation_sum (s s' : KernelState) (hacc : s'.accounts = s.accounts) :
    (refineConservation s s').sum = total s' - total s := by
  unfold refineConservation total
  rw [Finset.sum_map_toList s.accounts (fun c => s'.bal c - s.bal c),
      Finset.sum_sub_distrib, hacc]

/-- **KEYSTONE 1 — `exec_refines_conservation` (PROVED-clean).** An `exec`-committed step's
per-cell balance deltas satisfy `Spec`'s balance-domain conservation
(`conservedInDomain Domain.balance`, i.e. `Σδ = 0` over `Bal = ℤ`). This is the conservation
PROJECTION of the refinement square: `Exec.exec_conserves` (the single-ℤ ledger preserves
`total`) IS, with no remainder, `Spec`'s `Σδ = 0` law instantiated at `Bal = ℤ`,
`Domain.balance`. The toy single-domain ledger is the `balance` case of multi-domain
conservation. -/
theorem exec_refines_conservation (k k' : KernelState) (turn : Turn)
    (h : exec k turn = some k') :
    conservedInDomain Domain.balance (refineConservation k k') := by
  -- `exec` preserves the account set (it only rewrites `bal`), and `total` (exec_conserves).
  have hacc : k'.accounts = k.accounts := by
    unfold exec at h
    by_cases hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src
        ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; rw [← h]
    · rw [if_neg hg] at h; exact absurd h (by simp)
  have htot : total k' = total k := exec_conserves k k' turn h
  unfold conservedInDomain
  rw [refineConservation_sum k k' hacc, htot, sub_self]

/-- The same conservation projection cast through the abstract monoid keystone: a committed
step's prior balance-domain total `pre` is unchanged by adding the step's deltas — the
`Bal = ℤ` instance of `Spec.conservation_over_monoid`. Confirms the executable refinement is
literally the abstract law's ℤ specialization, not a parallel re-proof. -/
theorem exec_refines_conservation_over_monoid (k k' : KernelState) (turn : Turn)
    (h : exec k turn = some k') (pre : ℤ) :
    pre + (refineConservation k k').sum = pre :=
  conservation_over_monoid Domain.balance pre (refineConservation k k')
    (exec_refines_conservation k k' turn h)

/-- Multi-domain placement (PROVED): a committed `exec` step conserves the `balance` domain of
the four-domain abstract law. We package the step's deltas as `TurnDeltas` that are the
kernel's ℤ ledger in the `balance` slot and empty (vacuously conserving) elsewhere, and read
off `turnConserves`-style balance conservation. This is the precise sense in which the
executable kernel inhabits ONE domain of `Spec.multi_domain_independent`. -/
theorem exec_inhabits_balance_domain (k k' : KernelState) (turn : Turn)
    (h : exec k turn = some k') :
    conservedInDomain (Bal := ℤ) Domain.balance
      ((fun dom => match dom with
                   | Domain.balance => refineConservation k k'
                   | _ => ([] : List ℤ)) Domain.balance) :=
  exec_refines_conservation k k' turn h

/-! ## §2 — Authority refinement: `Exec.authorizedB` refines `Spec.Guard` / `Spec.Authority`.

The executable cap gate `Exec.authorizedB caps turn : Bool` checks ownership-or-held-cap,
fail-closed. `Spec.Guard` says every gate is a `Guard.admits`; `Spec.Authority` says authority
is a capability `Graph` with `confers`/`Holds`. We refine the executable gate onto BOTH:

  * onto `Spec.Guard` — `authorizedB` is realized, with no remainder, as a `firstParty`
    `Guard` over the turn (the decidable intra/cross-vat gate of `VatBoundary.Positional`);
  * onto `Spec.Authority` — the ownership branch (`actor = src`) is the reflexive conferral
    `confers c c` (`Authority.confers_refl`), and the held-cap branch witnesses
    `Graph.has actor src` on a graph reconstructed from `Exec.caps`. -/

section AuthorityRefinement

-- The verify oracle for the `Guard`. The executable gate is FIRST-PARTY (decidable now), so
-- the witnessed branch is never used; we take the oracle as a parameter exactly as `Guard`
-- and `Coherence` do, so the refinement is stated over the same seam.
variable {Statement Witness : Type} [Verifiable Statement Witness]

/-- The `Request` the executable authority gate reads is exactly the `Turn` (the actor / src /
dst / amount facts) — NOT a `Nat`. The abstract `Guard` reads it first-party. -/
abbrev ExecRequest := Turn

/-- **`execAuthGuard caps`** — the executable cap gate as a first-party `Spec.Guard`.
`Guard.firstParty (fun t => Exec.authorizedB caps t)`: it admits a turn iff the kernel's
decidable ownership-or-held-cap check passes. The `Statement` carrier is free (no witnessed
branch — the gate is decided *now*, the positional regime). -/
def execAuthGuard (caps : Caps) : Guard ExecRequest Statement :=
  Guard.firstParty (fun t => authorizedB caps t)

/-- **KEYSTONE 2 — `exec_authz_refines_guard` (PROVED-clean).** The executable gate
`authorizedB` admitting a turn ⇒ the corresponding abstract `Spec.Guard.admits` is `true`. The
decidable kernel gate REFINES the abstract `Guard` demand: every turn the machine admits, the
abstract gate admits. (The `↔` even holds — the refinement is exact, not merely sound — but
the soundness direction is the load-bearing one for `Exec ⊑ Spec`.) -/
theorem exec_authz_refines_guard (caps : Caps) (turn : Turn) (w : Statement → Witness)
    (h : authorizedB caps turn = true) :
    Guard.admits (execAuthGuard (Statement := Statement) caps) turn w = true := by
  unfold execAuthGuard
  rw [Guard.admits_firstParty]
  exact h

/-- The refinement is EXACT (`↔`): the executable gate admits *iff* the abstract `firstParty`
guard admits. So `authorizedB` is realized as a `Spec.Guard.admits` with no remainder — the
same single gate object that unifies authorization / preconditions / program-constraints /
caveats (`Spec.Guard`'s thesis). PROVED. -/
theorem exec_authz_iff_guard (caps : Caps) (turn : Turn) (w : Statement → Witness) :
    Guard.admits (execAuthGuard (Statement := Statement) caps) turn w = true
      ↔ authorizedB caps turn = true := by
  unfold execAuthGuard
  rw [Guard.admits_firstParty]

/-- A *committed* `exec` step's turn passes the abstract authority `Guard` — composing
`Exec.exec_authorized` (no state change without authority) with the gate refinement. So the
fact "the kernel only moves resource under authority" is, on the abstract side, "the authority
`Guard` admitted the turn". PROVED. -/
theorem exec_step_passes_guard (k k' : KernelState) (turn : Turn) (w : Statement → Witness)
    (h : exec k turn = some k') :
    Guard.admits (execAuthGuard (Statement := Statement) k.caps) turn w = true :=
  exec_authz_refines_guard k.caps turn w (exec_authorized k k' turn h)

/-! ### §2.1 — Refining onto `Spec.Authority`: ownership = reflexive `confers`, held cap =
`Graph.has`.

`Spec.Authority` models authority as a `Graph CellId Rights` with `confers` (non-amplifying
delegation) and `Graph.has` (the holder reaches a target). We reconstruct a Spec graph from
`Exec.caps` and show the executable gate's two branches land on it: ownership is the reflexive
self-conferral `confers c c`, and a held node/endpoint-write cap witnesses `Graph.has`. -/

/-- The abstract rights carrier for the reconstructed graph: `Unit` with the trivial
meet-semilattice (every cap confers the same, full authority). This suffices to witness the
*connectivity* skeleton of `Exec.caps` — the executable model carries no rights lattice of its
own (its caps are `node`/`endpoint`-with-`List Auth`), so the faithful Spec image is the
connectivity graph, with rights abstracted to the trivial order. (A richer image keyed on
`List Auth` is possible; the connectivity skeleton is what the authority *gate* reads.) -/
abbrev ExecRights := Unit

/-- **`execGraph caps`** — the `Spec.Authority.Graph` reconstructed from the executable cap
table: cell `h` holds a Spec edge to `t` iff, in `Exec.caps`, `h` holds a `node t` cap or an
`endpoint t` cap carrying `write` (the two branches `authorizedB` accepts). The rights are
`Unit` (the connectivity skeleton). -/
def execGraph (caps : Caps) : Graph Label ExecRights :=
  fun h c =>
    -- the `.any` reads `c.target`, so the edge genuinely depends on the cap `c`.
    (caps h).any (fun cap =>
      (cap == Authority.Cap.node c.target) ||
      (match cap with
       | .endpoint t rights => (t == c.target) && rights.contains Auth.write
       | _ => false)) = true

/-- **`exec_owns_self_confers` (PROVED)** — the authority object the ownership branch lands on
is the **reflexive self-conferral**, a CONNECTIVITY-skeleton fact (rights = `ExecRights = Unit`).
When a turn is admitted via ownership (`turn.actor = turn.src`), the self-cap `⟨turn.src, ⊤⟩` confers
itself: the ownership hypothesis `hown` is load-bearing — it is what collapses the two endpoints to
one, so this is `Authority.confers`-reflexivity specialised to the self-edge.

SCOPE (honesty): this is a connectivity statement — the rights conjunct is the trivial `⊤ ≤ ⊤` over
the `Unit` skeleton, NOT a genuine rights non-amplification. The GENUINE rights non-amplification —
`granted ⊆ held` over the REAL `List Auth` lattice, with teeth (an amplifying grant rejected) — lives
in `Dregg2.Exec.EffectsAuthority.introduce_non_amplifying`/`amplifying_grant_rejected` (via
`Caps.attenuate_subset`) and in `AuthModes.captp_granted_le_held`. This lemma names ONLY the
connectivity object (it does NOT witness the gate's acceptance — that is `exec_authz_grounds_in_graph`
below, which consumes `authorizedB`). -/
theorem exec_owns_self_confers (turn : Turn) (hown : turn.actor = turn.src) :
    confers (⟨turn.actor, (⊤ : ExecRights)⟩ : Cap Label ExecRights)
            (⟨turn.src, (⊤ : ExecRights)⟩ : Cap Label ExecRights) := by
  -- ownership makes `actor = src`, so the conferred edge is the reflexive self-cap.
  rw [hown]
  exact confers_refl _

/-- **`exec_heldcap_is_graph_has` (PROVED)** — the held-cap branch of `authorizedB` refines
`Graph.has` on the reconstructed graph. If the actor is NOT the owner yet `authorizedB` admits
the turn, then the actor holds a `node src` / `endpoint src write` cap, i.e. on `execGraph` the
actor `Graph.has` the source: the executable held-cap acceptance witnesses abstract
connectivity (`Granovetter`'s "you can reach what you hold a cap to"). -/
theorem exec_heldcap_is_graph_has (caps : Caps) (turn : Turn)
    (h : authorizedB caps turn = true) (hne : turn.actor ≠ turn.src) :
    (execGraph caps).has turn.actor turn.src := by
  -- `authorizedB` is `(actor == src) || (caps actor).any …`; ownership is excluded, so the
  -- `any` branch holds.
  unfold authorizedB at h
  rw [Bool.or_eq_true] at h
  rcases h with hown | hcap
  · -- `actor == src = true` contradicts `actor ≠ src`.
    rw [beq_iff_eq] at hown; exact absurd hown hne
  · -- the held-cap branch: exhibit the Spec edge `actor ⟶ src`.
    refine ⟨(), ?_⟩
    unfold execGraph
    exact hcap

/-- **`exec_authz_grounds_in_graph` (PROVED)** — the FULL authority refinement disjunction:
every turn the executable gate admits is grounded in the reconstructed Spec authority graph —
either by ownership (refining the reflexive conferral `confers (·) (·)`) or by a held cap
(refining `Graph.has`). This is the authority projection of the simulation: `authorizedB`'s
acceptance set is contained in the abstract authority graph's reachability. PROVED. -/
theorem exec_authz_grounds_in_graph (caps : Caps) (turn : Turn)
    (h : authorizedB caps turn = true) :
    turn.actor = turn.src ∨ (execGraph caps).has turn.actor turn.src := by
  by_cases hne : turn.actor = turn.src
  · exact Or.inl hne
  · exact Or.inr (exec_heldcap_is_graph_has caps turn h hne)

end AuthorityRefinement

/-! ## §3 — The simulation relation + the commuting square.

`Refines k a` ties the executable `KernelState` `k` to an abstract Spec state `a` — the
balances correspond (the ℤ ledger IS the `balance`-domain total) and the caps correspond (the
executable cap table reconstructs the abstract authority `Graph`). The abstract state is the
pair (the conserved balance-domain total over the live accounts, the reconstructed authority
graph) — the two Spec projections the squares above prove. -/

section Square

variable {Statement Witness : Type} [Verifiable Statement Witness]

/-- **`AbstractState`** — the abstract Spec state a kernel refines: the conserved
`balance`-domain total over the live accounts (an `ℤ`, the `Spec.Conservation` measure at
`Bal = ℤ`) together with the reconstructed authority `Graph` (the `Spec.Authority` graph the
caps confer). These are exactly the two projections squares §1 and §2 prove. -/
structure AbstractState where
  /-- the conserved `balance`-domain total (the `Spec.Conservation` measure at `Bal = ℤ`). -/
  balanceTotal : ℤ
  /-- the reconstructed authority graph (the `Spec.Authority` graph the caps confer). -/
  authGraph    : Graph Label ExecRights

/-- The abstract state a kernel state denotes: its `total` (balance-domain conserved measure)
and its `execGraph` (reconstructed authority graph). The simulation's abstraction function. -/
def absOf (k : KernelState) : AbstractState :=
  { balanceTotal := total k
    authGraph    := execGraph k.caps }

/-- **`Refines k a`** — the simulation relation: the kernel's conserved balance total IS the
abstract `balanceTotal`, and its reconstructed authority graph IS the abstract `authGraph`.
(`Refines k (absOf k)` holds by `rfl`; the relation is `a = absOf k` unfolded into its two
corresponding projections, stated as a relation so the square below reads as a diagram.) -/
def Refines (k : KernelState) (a : AbstractState) : Prop :=
  a.balanceTotal = total k ∧ a.authGraph = execGraph k.caps

/-- `absOf` realizes `Refines` (the abstraction function is a refinement witness). PROVED. -/
theorem refines_absOf (k : KernelState) : Refines k (absOf k) :=
  ⟨rfl, rfl⟩

/-- **The conservation projection of the commuting square (PROVED-clean).** If `Refines k a`
and `exec k turn = some k'`, then the abstract `balanceTotal` is PRESERVED across the step:
`a'.balanceTotal = a.balanceTotal` for `a' := absOf k'`. The square commutes on the
conservation projection — the abstract step is the identity on the conserved total, which is
`exec_conserves` read through the abstraction. PROVED. -/
theorem exec_step_refines_conservation (k k' : KernelState) (a : AbstractState) (turn : Turn)
    (hsim : Refines k a) (h : exec k turn = some k') :
    (absOf k').balanceTotal = a.balanceTotal := by
  have htot : total k' = total k := exec_conserves k k' turn h
  simp only [absOf]
  rw [htot, hsim.1]

/-- **The authority projection of the commuting square (PROVED-clean).** If `Refines k a` and
`exec k turn = some k'`, then the committed turn is admitted by the abstract authority gate
over `a`'s graph-conferring caps — and the post-state's authority graph is UNCHANGED (`exec`
moves only `bal`, never `caps`), so `Refines k' a'` holds on the authority projection. The
square commutes on authority: the executable gate's acceptance is the abstract gate's
acceptance, and the abstract authority state is preserved. PROVED. -/
theorem exec_step_refines_authority (k k' : KernelState) (a : AbstractState) (turn : Turn)
    (w : Statement → Witness)
    (hsim : Refines k a) (h : exec k turn = some k') :
    Guard.admits (execAuthGuard (Statement := Statement) k.caps) turn w = true ∧
      (absOf k').authGraph = a.authGraph := by
  refine ⟨exec_step_passes_guard k k' turn w h, ?_⟩
  -- `exec` preserves `caps` (it rewrites only `bal`), so the reconstructed graph is unchanged.
  have hcaps : k'.caps = k.caps := by
    unfold exec at h
    by_cases hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src
        ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; rw [← h]
    · rw [if_neg hg] at h; exact absurd h (by simp)
  simp only [absOf]
  rw [hcaps, hsim.2]

/-- **`exec_step_refines` (the commuting square — conservation+authority projections PROVED,
operational thread OPEN).** If `Refines k a` and `exec k turn = some k'`, then there is an
abstract successor `a'` with `Refines k' a'`, AND the step preserves both Spec projections:
the conserved balance total is unchanged (`exec_conserves`, §1) and the committed turn passed
the abstract authority gate with the authority graph unchanged (§2). We take `a' := absOf k'`
(the canonical abstraction of the post-state) and discharge the two projections cleanly.

This is the conservation+authority projection of the full simulation diagram — exactly the two
tractable squares — assembled into one commuting statement. PROVED-clean. -/
theorem exec_step_refines (k k' : KernelState) (a : AbstractState) (turn : Turn)
    (w : Statement → Witness)
    (hsim : Refines k a) (h : exec k turn = some k') :
    ∃ a', Refines k' a' ∧
      -- conservation projection: the abstract balance total is preserved.
      a'.balanceTotal = a.balanceTotal ∧
      -- authority projection: the turn passed the abstract gate, the auth graph is preserved.
      (Guard.admits (execAuthGuard (Statement := Statement) k.caps) turn w = true ∧
        a'.authGraph = a.authGraph) := by
  refine ⟨absOf k', refines_absOf k', ?_, ?_⟩
  · exact exec_step_refines_conservation k k' a turn hsim h
  · exact exec_step_refines_authority k k' a turn w hsim h

/-- **The conservation invariant of the square, lifted to a whole kernel run (PROVED).**
Composing `exec_step_refines`'s conservation projection with `Exec.kernel_run_conserves`: an
abstract state refining the initial kernel state refines the final one on the conserved total
across an ENTIRE `kernelSystem` run. So the refinement square's conservation projection is
stable under iteration — the abstract `balanceTotal` is a run invariant. PROVED. -/
theorem run_refines_conservation {k k' : KernelState} (a : AbstractState)
    (hsim : Refines k a) (hrun : Dregg2.Execution.Run kernelSystem k k') :
    (absOf k').balanceTotal = a.balanceTotal := by
  have htot : total k' = total k := kernel_run_conserves hrun
  simp only [absOf]
  rw [htot, hsim.1]

end Square

/-! ## §3.5 — The SECOND refinement square: the CONTENT-ADDRESSED record kernel `⊑ Spec`.

§1–§3 refine the toy scalar kernel (`Exec.Kernel`, `bal : CellId → ℤ`). The construction study's
single-highest-leverage move (`PHASE-CONSTRUCTION.md §1`) replaces that scalar ledger with the
content-addressed `Value` record cell (`Exec.RecordKernel`, `cell : CellId → Value`), conserving a
NAMED FIELD (`balance`) rather than the whole-state ℤ. Here we exhibit that as a SECOND refinement
square onto the SAME abstract law — `Spec.conservedInDomain Domain.balance` — proving the record
kernel's `balance`-field conservation IS the `Bal = ℤ`, `Domain.balance` instance of the abstract
multi-domain conservation, exactly as §1 does for the scalar kernel. So the abstract `Domain.balance`
law is now refined by BOTH the toy scalar ledger AND the concrete record cell — the latter being the
seam toward "verified dregg". -/

/-- **`refineRecordConservation s s'`** — the per-cell `balance`-FIELD deltas of a record-kernel step
`s ⟶ s'`, packaged as the `List ℤ` that `Spec.conservedInDomain` consumes (the record-cell analog of
`refineConservation`). It reads `balOf` — the named-field measure — off each live account. -/
noncomputable def refineRecordConservation (s s' : RecordKernelState) : List ℤ :=
  s.accounts.toList.map (fun c => balOf (s'.cell c) - balOf (s.cell c))

/-- The list-sum of the per-cell `balance`-field deltas equals `recTotal s' - recTotal s` over the
shared account set (`recKExec` preserves `accounts`). The `Finset.sum_map_toList` bridge applied to
the record cell's `balance`-field measure. -/
theorem refineRecordConservation_sum (s s' : RecordKernelState) (hacc : s'.accounts = s.accounts) :
    (refineRecordConservation s s').sum = recTotal s' - recTotal s := by
  unfold refineRecordConservation recTotal
  rw [Finset.sum_map_toList s.accounts (fun c => balOf (s'.cell c) - balOf (s.cell c)),
      Finset.sum_sub_distrib, hacc]

/-- **KEYSTONE (second square) — `recExec_refines_conservation` (PROVED-clean).** A committed
record-kernel step's per-cell `balance`-field deltas satisfy `Spec`'s balance-domain conservation
(`conservedInDomain Domain.balance`, i.e. `Σδ = 0` over `Bal = ℤ`). This is the conservation
PROJECTION of the SECOND refinement square: `RecordKernel.recKExec_conserves` (the content-addressed
record cell preserves the total `balance` field) IS, with no remainder, `Spec`'s `Σδ = 0` law over
`Bal = ℤ`, `Domain.balance` — the SAME abstract law §1 refines the scalar kernel onto, now refined by
the concrete record cell. -/
theorem recExec_refines_conservation (k k' : RecordKernelState) (turn : Turn)
    (h : recKExec k turn = some k') :
    conservedInDomain Domain.balance (refineRecordConservation k k') := by
  have hacc : k'.accounts = k.accounts := (recKExec_frame k k' turn h).1
  have htot : recTotal k' = recTotal k := recKExec_conserves k k' turn h
  unfold conservedInDomain
  rw [refineRecordConservation_sum k k' hacc, htot, sub_self]

/-- The record-kernel conservation projection cast through the abstract monoid keystone: a committed
record step's prior balance-domain total `pre` is unchanged by adding the step's `balance`-field
deltas — the `Bal = ℤ` instance of `Spec.conservation_over_monoid`, now for the content-addressed
cell. PROVED. -/
theorem recExec_refines_conservation_over_monoid (k k' : RecordKernelState) (turn : Turn)
    (h : recKExec k turn = some k') (pre : ℤ) :
    pre + (refineRecordConservation k k').sum = pre :=
  conservation_over_monoid Domain.balance pre (refineRecordConservation k k')
    (recExec_refines_conservation k k' turn h)

/-- **`recExec_authz_refines_guard` (PROVED-clean)** — the record kernel's authority gate is the
SAME `authorizedB` the scalar kernel uses, so it refines the SAME abstract `Spec.Guard.firstParty`
gate (authority is orthogonal to the state representation). A committed record step's turn passes the
abstract authority `Guard`. -/
theorem recExec_step_passes_guard {Statement Witness : Type} [Verifiable Statement Witness]
    (k k' : RecordKernelState) (turn : Turn) (w : Statement → Witness)
    (h : recKExec k turn = some k') :
    Guard.admits (execAuthGuard (Statement := Statement) k.caps) turn w = true :=
  exec_authz_refines_guard k.caps turn w (recKExec_authorized k k' turn h)

/-- **The record refinement square (PROVED-clean projections).** A committed record-kernel step
preserves BOTH Spec projections over the content-addressed cell: the `balance`-domain conservation
(`recKExec_conserves`, the named-field measure) and the authority `Guard` (the same gate). Assembled
as one commuting statement, mirroring §3's `exec_step_refines` but for `RecordKernel`. The operational
LTS residue (§4) is shared and remains the single OPEN. -/
theorem recExec_step_refines {Statement Witness : Type} [Verifiable Statement Witness]
    (k k' : RecordKernelState) (turn : Turn) (w : Statement → Witness)
    (h : recKExec k turn = some k') :
    conservedInDomain Domain.balance (refineRecordConservation k k') ∧
      Guard.admits (execAuthGuard (Statement := Statement) k.caps) turn w = true :=
  ⟨recExec_refines_conservation k k' turn h, recExec_step_passes_guard k k' turn w h⟩

#assert_axioms refineRecordConservation_sum
#assert_axioms recExec_refines_conservation
#assert_axioms recExec_refines_conservation_over_monoid
#assert_axioms recExec_step_passes_guard
#assert_axioms recExec_step_refines

/-! ## §4 — OPEN: the operational residue (the abstract small-step relation).

What §3 PROVES is the conservation+authority PROJECTION of the simulation square: the two Spec
laws (`Σδ = 0` over the `balance` domain, the authority `Guard`/`Graph` gate) are preserved by
`exec`, with the abstraction `absOf` as the refinement witness. What it does NOT prove — and
what the FULL l4v-style `Exec ⊑ Spec` forward simulation needs — is an *abstract small-step
relation* `AbsStep : AbstractState → AbstractState → Prop` (the spec's own operational
transition), such that:

  * every executable `exec k turn = some k'` is matched by an `AbsStep (absOf k) (absOf k')`
    (the FULL square's bottom edge is an abstract STEP, not merely the identity-on-projections
    we use here); and
  * `AbsStep` is exactly the `Spec.Conservation` + `Spec.Authority` dynamics — a turn that
    moves balance-domain ℤ conservatively AND fires an authorized `Spec.Authority.AuthStep` /
    `GenAct`/`RestrictAct` on the graph.

This is the SAME residue already flagged by `Proof/Refine` (the operational diagram) and by
`Spec.Authority.only_connectivity_begets_connectivity`'s OPEN (the whole-history graph
bookkeeping). It needs the abstract LTS, not just the two static projections; until that LTS
is named, the bottom edge of the square is the projection-preserving abstraction, not a full
abstract transition. The honest residual obligation:

-- OPEN (operational residue, NOT proved here): define `AbsStep : AbstractState → AbstractState
--   → Prop` as the `Spec.Conservation`-conservative, `Spec.Authority`-authorized abstract turn
--   relation, and prove `exec k turn = some k' → AbsStep (absOf k) (absOf k')` (forward
--   simulation: every executable step is an abstract step). With that, `exec_step_refines`
--   strengthens from "preserves the two projections" to "commutes with a genuine abstract
--   step" — full `Exec ⊑ Spec` forward simulation. The projections proved above are the
--   conserved/authority CONTENT of that step; the missing piece is the LTS that packages them
--   as one transition relation (the same thread `Spec.Authority`'s headline leaves OPEN).
-/

/-! ## §5 — Axiom-hygiene tripwires.

The conservation and authority squares (§1, §2) and the projection-assembled commuting square
(§3) are PROVED-clean: each depends ONLY on the three standard kernel axioms (no `sorryAx`).
Pinning them here certifies the FIRST `Exec ⊑ Spec` square is genuinely proved, not a
`sorry`-alias. The operational residue (§4) is an `-- OPEN:` PROSE obligation, not a `sorry`
declaration — so there is nothing axiom-dirty to exclude; the whole file is clean. -/

#assert_axioms refineConservation_sum
#assert_axioms exec_refines_conservation
#assert_axioms exec_refines_conservation_over_monoid
#assert_axioms exec_inhabits_balance_domain
#assert_axioms exec_authz_refines_guard
#assert_axioms exec_authz_iff_guard
#assert_axioms exec_step_passes_guard
#assert_axioms exec_owns_self_confers
#assert_axioms exec_heldcap_is_graph_has
#assert_axioms exec_authz_grounds_in_graph
#assert_axioms refines_absOf
#assert_axioms exec_step_refines_conservation
#assert_axioms exec_step_refines_authority
#assert_axioms exec_step_refines
#assert_axioms run_refines_conservation

end Dregg2.Spec
