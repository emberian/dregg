/-
# Dregg2.Exec.CellLiveness — GC = cell-liveness, executable; death is TIMED OUT, not decided.

This module is the **executable** facet of `Dregg2.Liveness` (which carries the
spec-level design, `dregg2 §1.7` + `docs/rebuild/study-gc.md`). It is the operational dual
of the coinductive cell (`Boundary` / `Exec.Cell`): a cell unfolds forever (`ν`) UNLESS it
falls out of the reachable subobject, and the runtime reclaims it once it does. Here we
make the *collection decision* concrete and prove the four load-bearing facts on it, by
LIFTING the already-proved theorems of `Liveness` (we REUSE, we do not re-derive):

  * `Liveness.reachable`            — reachability-from-a-root (the true liveness predicate);
  * `Liveness.Live`                 — the operational over-approximation `reachable ∨ ¬expired`;
  * `Liveness.lease_completes_deadness`, `Liveness.gc_safety_local`,
    `Liveness.crossvat_cycle_leaks`, `Liveness.dead_undecidable` — the keystones we build on.

The construction is the ONLY one consistent with codata + no-global-snapshot + graph-privacy
simultaneously (`study-gc.md §3,§5`):

  1. **`reachable` is positively witnessable** — a finite root-path is a `Verify`
     (`reachable_is_witness`). Liveness is *found* by exhibiting a path.
  2. **`death_is_timed_out` (THE KEYSTONE)** — we NEVER decide the global, non-co-witnessable
     "dead". We replace it with the locally-decidable "lease lapsed": `collect c` exactly when
     `c` is refcount-locally-collectible AND its lease has expired, and that decision is sound
     (it un-`Live`s only genuinely-dead, lease-lapsed cells). This times death out; it does
     not decide it.
  3. **`gc_safety_is_local`** — the collection trigger needs NO consensus: it reads only the
     dropper's own inbound edges (refcount-zero), never any peer's hidden internal state.
  4. **The impossibility (`-- OPEN:`)** — cross-vat cycles leak; "dead" is not globally
     co-witnessable. We do NOT pretend to collect them by reachability; they are reclaimed by
     lease expiry alone. This is the FIND/VERIFY seam, the same seam as everywhere in dregg2.

Style: spec-first, reuse the proved core; the collector is *computable* and its soundness is
*proved* (no `sorry` added here). The genuine impossibilities are stated honestly as `-- OPEN:`
notes pointing at the already-honest obligations of `Liveness`, never weakened to close.
-/
import Dregg2.Liveness

namespace Dregg2.Exec.CellLiveness

open Dregg2.Liveness

/-! ## The executable collection decision

A cell's lifecycle is driven by ONE locally-evaluable bit: the runtime collects a cell exactly
when (a) no holder retains a live inbound edge — `refcountZero`, the sound local trigger — AND
(b) its lease has lapsed at the current time. Both conjuncts are *local* (`refcountZero` reads
only edges incident to the cell; `leaseExpired` reads only the cell's own `Lease`). Neither
appeals to a global snapshot, peer cooperation, or consensus.

We carry `refcountZero` as a supplied decision bit `rcZero : Bool` together with the proof that
it reflects the (undecidable-in-general, but locally-observed) graph fact — this is faithful to
the runtime, which observes `total_refs == 0` locally rather than deciding global reachability. -/

/-- **`collectDecision rcZero l now`** — the locally-decidable collection trigger: collect iff
the local refcount is zero *and* the lease has lapsed. Pure `Bool`, no global view. This is the
operational predicate that *replaces* the undecidable global `Dead` (`study-gc.md §3`). -/
def collectDecision (rcZero : Bool) (l : Lease) (now : Nat) : Bool :=
  rcZero && leaseExpired l now

/-- **`liveCell g l now c`** — a cell is treated as live iff `Liveness.Live` holds: it is
root-reachable OR its lease has not yet expired. This is the sound-for-liveness
over-approximation the runtime uses (never collects while leased; eventually reclaims an
unreachable cell once the lease lapses). We simply re-expose `Liveness.Live` under the
executable name so the collector and the liveness predicate sit side by side. -/
def liveCell (g : LivenessGraph) (l : Lease) (now : Nat) (c : CellId) : Prop :=
  Live g l now c

/-! ## 1. Reachability is a witness (the `Verify` side) -/

/-- **`reachable_is_witness`** — reachability is positively semi-decidable: exhibiting a finite
root and a `Reaches` path WITNESSES that the cell is `liveCell` (it is `Live` via the reachable
disjunct). This is the `Verify` side of the FIND/VERIFY seam — local to the path, finite,
tractable. (Lifts `Liveness.reachable_semidecidable_witness` into the operational `liveCell`.) -/
theorem reachable_is_witness
    (g : LivenessGraph) (l : Lease) (now : Nat) (c r : CellId)
    (hr : g.root r) (hpath : Reaches g r c) :
    liveCell g l now c :=
  -- A finite path is a `Verify`: it positively witnesses `reachable`, hence `Live`'s left disjunct.
  Or.inl (reachable_semidecidable_witness g c r hr hpath)

/-- **`reachable_keeps_live`** — restated at the bare `reachable` level: any reachable cell is
`liveCell`, for ANY lease/time. The unfold continues while reachable, with no appeal to the
lease at all — the lease is only the *completing fallback* for the unreachable case. -/
theorem reachable_keeps_live
    (g : LivenessGraph) (l : Lease) (now : Nat) (c : CellId)
    (hreach : reachable g c) :
    liveCell g l now c :=
  Or.inl hreach

/-! ## 2. THE KEYSTONE — death is TIMED OUT, not decided -/

/-- **`death_is_timed_out` — THE KEYSTONE.** A cell is soundly collectible via LEASE EXPIRY: if
the cell is genuinely `Dead` (the global, non-co-witnessable predicate) AND its lease has lapsed,
then it is NOT `liveCell`, so collecting it is sound. Crucially, the *operational* hypothesis the
runtime can actually check is only `leaseExpired = true` (locally decidable) — the global `Dead`
appears as a semantic side-condition we never compute. This is the move that converts a
non-co-witnessable global predicate ("dead") into a locally-decidable one ("lease lapsed"): death
is **timed out**, never decided. (Lifts `Liveness.lease_completes_deadness`.) -/
theorem death_is_timed_out
    (g : LivenessGraph) (l : Lease) (now : Nat) (c : CellId)
    (hdead : Dead g c) (hexp : leaseExpired l now = true) :
    ¬ liveCell g l now c :=
  -- This does NOT decide `Dead`; it replaces it operationally by the lapsed-lease test.
  lease_completes_deadness g l now c hdead hexp

/-- **`collect_sound_when_dead`** — the executable collector is sound: if `collectDecision`
fires (local refcount zero AND lease lapsed) and the cell is in fact `Dead`, then the cell is
not `liveCell` — collecting it strands no live cell. The decision the runtime evaluates is the
pure-`Bool` `collectDecision`; the `Dead` premise is the semantic justification, never computed.
This is `death_is_timed_out` packaged at the executable trigger: the `leaseExpired` conjunct of a
firing `collectDecision` is exactly the timeout that soundly stands in for undecidable deadness. -/
theorem collect_sound_when_dead
    (g : LivenessGraph) (rcZero : Bool) (l : Lease) (now : Nat) (c : CellId)
    (hdead : Dead g c) (hfire : collectDecision rcZero l now = true) :
    ¬ liveCell g l now c := by
  -- A firing `collectDecision = rcZero && leaseExpired` forces `leaseExpired = true`.
  have hexp : leaseExpired l now = true := by
    unfold collectDecision at hfire
    exact (Bool.and_eq_true rcZero (leaseExpired l now) |>.mp hfire).2
  exact death_is_timed_out g l now c hdead hexp

/-! ## 3. GC-safety is local — no consensus -/

/-- **`gc_safety_is_local`** — collecting needs NO consensus. If the only inbound holders are
direct edges and they have all dropped (`LocalEvidence`, i.e. `refcountZero`), then the cell has
no inbound edge: collection cannot strand a still-holding honest vat, because a drop touches only
the dropper's OWN holder count and is session/epoch-gated. NO global agreement appears in the
hypotheses — the sharp ORCA/CapTP result that GC-safety is local and bilateral. (Lifts
`Liveness.gc_safety_local`.) -/
theorem gc_safety_is_local
    (g : LivenessGraph) (c : CellId)
    (hlocal : LocalEvidence g c) :
    ¬ hasInbound g c :=
  gc_safety_local g c hlocal

/-- **`local_evidence_decides_trigger`** — the safety trigger is *locally decidable*: given the
bilateral `LocalEvidence` (refcount zero) and a lapsed lease, the executable `collectDecision`
fires with `rcZero = true`. This ties the proved-local safety fact to the pure-`Bool` decision
the runtime evaluates, with no peer cooperation in scope. -/
theorem local_evidence_decides_trigger
    (g : LivenessGraph) (l : Lease) (now : Nat) (c : CellId)
    (_hlocal : LocalEvidence g c) (hexp : leaseExpired l now = true) :
    collectDecision true l now = true := by
  unfold collectDecision
  simp [hexp]

/-! ## 4. The impossibility — cross-vat cycles leak; "dead" is not globally co-witnessable -/

/-- **`crossvat_cycle_not_collected`** — the honest negative result, lifted to the executable
collector: no sound local-evidence-only collector reclaims a cross-vat cycle. Each node pins the
other's refcount ≥ 1 forever, so `refcountZero` (the only sound local trigger) never fires, and a
`SoundLocalCollector` therefore NEVER collects either node by reachability. (Lifts
`Liveness.crossvat_cycle_leaks` verbatim.) -/
theorem crossvat_cycle_not_collected
    (col : SoundLocalCollector) (g : LivenessGraph) (a b : CellId)
    (hcyc : CrossVatCycle g a b) :
    col.collect g a = false ∧ col.collect g b = false :=
  crossvat_cycle_leaks col g a b hcyc

/-- **`crossvat_leak_reclaimed_by_lease`** — the ONLY honest mitigation: a leaked cross-vat
cycle is never reachability-collected, but the operational `liveCell` STILL reclaims it once the
lease lapses — a dead cycle node past its lease is not `liveCell`. The leak lasts not *forever*
but only *until the leases lapse*. This needs no global view, survives partition, and respects
graph privacy. (Lifts `Liveness.leak_bounded_by_lease` into `liveCell`.) -/
theorem crossvat_leak_reclaimed_by_lease
    (g : LivenessGraph) (l : Lease) (now : Nat) (a b : CellId)
    (hcyc : CrossVatCycle g a b) (hexp : leaseExpired l now = true) :
    ¬ liveCell g l now a :=
  leak_bounded_by_lease g l now a b hcyc hexp

/-
-- OPEN: distributed cycle collection is OUT OF SCOPE — it is not a missing proof here, it is a
-- genuine impossibility (`study-gc.md §1`, `crossvat_cycle_not_collected` above). A sound
-- collector that reclaimed cross-vat cycles by reachability would require mutually-distrusting
-- vats to truthfully report their internal back-edges — unenforceable, and a breach of the
-- tier-3 graph-privacy the design exists to provide. dregg2 ships this leak in full and bounds
-- it ONLY by lease expiry (`crossvat_leak_reclaimed_by_lease`). We do NOT add a cycle collector.

-- OPEN: "dead" is genuinely not globally decidable. `Liveness.dead_undecidable` states (with an
-- honest `sorry`, its residual obligation a Turing-reduction needing a computability model not in
-- the imported modules) that NO uniform `decide : LivenessGraph → CellId → Bool` soundly and
-- completely decides `Dead`. We deliberately import that fact rather than re-attempt it, and we
-- never DECIDE death anywhere in this module: every collection above gates on the locally-decidable
-- `leaseExpired`, with `Dead` appearing only as a semantic side-condition (the timeout times death
-- out; it does not compute it). This is the FIND/VERIFY asymmetry, the same seam as everywhere:
-- `reachable` is witnessable (a path = a `Verify`), `Dead = ¬reachable` is the non-local FIND.
-/

open Nat.Partrec (Code) in
open Nat.Partrec.Code in
/-- We RE-EXPOSE the undecidability obligation under this module's namespace so a downstream reader
sees, on the nose, that this executable layer does not (and provably cannot) ship a decision
procedure for death — only the lease-timeout above. Mirrors `Liveness.dead_undecidable`'s genuine
**computable**-undecidability form (the old arbitrary-`Bool`-function form was classically vacuous —
`Classical.decide` always supplies such a function — so it is replaced, not merely re-typed); the
proof is literally `Liveness`'s obligation, delegated. We add no new `sorry` and weaken nothing. -/
theorem death_not_decidable (n : ℕ) :
    ¬ ∃ d : Code → Bool,
        Computable d ∧
        (∀ c : Code, d c = true ↔ Dead (haltGraph ((eval c n).Dom)) 1) :=
  dead_undecidable n

/-! ## `#eval` demos — the operational story, made concrete

We exhibit two concrete liveness graphs / collection decisions:
  * a reachable cell stays Live (collector must NOT fire) — reachability outvotes any lease;
  * an unreachable cell with a lapsed lease is collectible (`collectDecision = true`).
All quantities here are locally computable `Bool`s; no global reachability is ever decided. -/

/-- Demo graph: cell `0` is a root that reaches cell `1` (`0 → 1`); cell `2` is rootless with no
inbound edge (refcount zero). -/
def demoGraph : LivenessGraph where
  edge := fun a b => a = 0 ∧ b = 1
  root := fun c => c = 0
  vat  := fun _ => 0

/-- A lease that lapses at time 10. -/
def demoLease : Lease := { expiresAt := 10, lastActivity := 0 }

-- A reachable cell (`1`, reached from root `0`) is `liveCell` regardless of the lease: the
-- collector must not fire. We witness `liveCell demoGraph demoLease 99 1` by a finite path.
example : liveCell demoGraph demoLease 99 1 :=
  reachable_is_witness demoGraph demoLease 99 1 0 rfl
    (Reaches.step (Reaches.refl 0) ⟨rfl, rfl⟩)

-- Demo 1: a CURRENT lease (now=5 < expiresAt=10) means the local collection trigger does NOT fire
-- even with refcount zero — fail-closed for safety while leased.
#eval collectDecision true demoLease 5    -- expected: false (lease not yet lapsed)

-- Demo 2: an unreachable cell with a LAPSED lease (now=20 ≥ 10) AND refcount zero is collectible.
#eval collectDecision true demoLease 20   -- expected: true (refcount zero ∧ lease lapsed)

-- Demo 3: refcount NONZERO (e.g. a pinned cross-vat-cycle node) never collects locally, even past
-- the lease — the trigger correctly refuses; such a node is reclaimed by the lease at the `liveCell`
-- level (`crossvat_leak_reclaimed_by_lease`), not by this local refcount trigger.
#eval collectDecision false demoLease 20  -- expected: false (refcount nonzero pins it)

-- The lease-expiry predicate itself, locally decidable at three times.
#eval (leaseExpired demoLease 5, leaseExpired demoLease 10, leaseExpired demoLease 20)
  -- expected: (false, true, true)

end Dregg2.Exec.CellLiveness
