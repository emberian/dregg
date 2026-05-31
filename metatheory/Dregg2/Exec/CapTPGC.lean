/-
# Dregg2.Exec.CapTPGC — closing the CapTP distributed-GC OPEN by LEASE-BASED RECLAIM.

`Dregg2.Exec.CapTP` §4 left distributed GC as a documented `-- OPEN:` residue:

  > -- OPEN: distributed_gc_liveness — eventual reclamation of unreachable exported caps.
  > --   Reason: cross-vat reference cycles cannot be decided dead by one vat (CellLiveness's
  > --   death_is_timed_out / cross-vat-cycle impossibility); needs a cross-vat lease model.

This module supplies that cross-vat lease model and closes the OPEN *honestly* — NOT by
faking a "decide dead across vats" theorem (that decision is **impossible**, and
`Liveness.dead_undecidable` PROVES it), but by REALIZING the only sound resolution the design
and `Liveness` already endorse: **lease-based reclaim**. An exported cap's local import
handle carries a lease (`gc.rs`'s `last_activity + max_idle_blocks` idle window — see
`ExportGcManager::stale_exports`, `gc.rs:219`); the runtime reclaims a handle once its lease
has expired, and *never* reclaims a handle whose lease is still current (fail-closed). The
cross-vat reference CYCLE leaks — and that leak is a PROVED CONSEQUENCE of the impossibility,
the price of soundness, not a bug to fix.

The faithful `gc.rs` correspondence (the lease IS the idle window):

  * `RefCount.last_activity` (`gc.rs:43`) + a `maxIdle` window  ⟶  a `Liveness.Lease`
    whose `expiresAt = lastActivity + maxIdle`;
  * `stale_exports`' predicate `current_height - last_activity > max_idle_blocks`
    (`gc.rs:226`)  ⟶  `Liveness.leaseExpired` at `now`;
  * `record_export_with_session` bumping `last_activity = current_height` (`gc.rs:136`)
    ⟶  lease RENEWAL (a fresh, un-expired lease as of `now`);
  * `crossvat_cycle_leaks` / `dead_undecidable`  ⟶  why proven-death reclaim is impossible
    and lease-expiry is the ONLY sound trigger.

This module REUSES `Liveness`/`Exec.CellLiveness` and `Exec.CapTP.ImportHandle` directly; it
invents no new verify side, no new decision procedure, and adds no `axiom`/`admit`/
`native_decide`/`sorry`. Keystones pinned with `#assert_axioms`.
-/
import Dregg2.Liveness
import Dregg2.Exec.CellLiveness
import Dregg2.Exec.CapTP
import Dregg2.Tactics

namespace Dregg2.Exec.CapTPGC

open Dregg2.Liveness
open Dregg2.Exec.CapTP (ImportHandle)

/-! ## §1 — The leased import handle.

An import handle (`Exec.CapTP.ImportHandle` — the local face of a cap exported to a remote
vat) is reclaimed not by proving it dead (impossible across vats) but by **lease expiry**.
We attach to it the `gc.rs` idle window as a `Liveness.Lease`: the lease lapses at
`lastActivity + maxIdle`, exactly `stale_exports`' `current_height - last_activity >
max_idle_blocks` boundary. -/

/-- **`leaseOf last maxIdle`** — the `Liveness.Lease` realizing `gc.rs`'s idle window for a
handle last active at block `last` with idle threshold `maxIdle`. The lease lapses at
`last + maxIdle`; `leaseExpired (leaseOf last maxIdle) now` is `decide (last + maxIdle ≤ now)`,
the locally-decidable stale-export test (`gc.rs:226`, modulo `>` vs `≤` at the boundary, which
`stale_exports` resolves with strict `>`; we use the `Lease`'s own `≤` convention — the
honest, locally-decidable timeout either way). -/
def leaseOf (last maxIdle : Nat) : Lease :=
  { expiresAt := last + maxIdle, lastActivity := last }

/-- **`LeasedHandle`** — an `ImportHandle` together with the lease that governs its reclaim.
This is the local bookkeeping `ImportGcManager` keeps (`gc.rs`): the handle stands in for the
remote cap, and the lease (the idle window over `last_activity`) is the ONLY sound reclaim
trigger across vats. -/
structure LeasedHandle (CellId Rights : Type*) where
  /-- The import handle (the local proxy for the remote cap). -/
  handle : ImportHandle CellId Rights
  /-- The lease governing reclaim (the `gc.rs` idle window as a `Liveness.Lease`). -/
  lease  : Lease

/-- **`Reclaimable lh now`** — the locally-decidable reclaim trigger: the handle's lease has
expired at `now`. This is `stale_exports`' verdict — a handle whose idle window has lapsed is
a candidate for reclaim — lifted to the `Liveness.leaseExpired` test. It NEVER decides global
deadness; it times the handle out. Pure `Bool`, no cross-vat cooperation, no global snapshot. -/
def Reclaimable {CellId Rights : Type*} (lh : LeasedHandle CellId Rights) (now : Nat) : Bool :=
  leaseExpired lh.lease now

/-- **`renew lh now`** — lease RENEWAL: `record_export_with_session` bumping `last_activity`
to the current block (`gc.rs:136`). The renewed handle's lease is fresh as of `now` (lapses at
`now + maxIdle`), so it is NOT reclaimable at `now` for any positive idle window. -/
def renew {CellId Rights : Type*} (lh : LeasedHandle CellId Rights) (now maxIdle : Nat) :
    LeasedHandle CellId Rights :=
  { lh with lease := leaseOf now maxIdle }

/-! ## §2 — The two reclaim laws: expired ⇒ reclaimable, renewed ⇒ NOT reclaimed. -/

/-- **`captp_gc_by_lease` (PROVED) — an expired-lease import handle is reclaimable.**
If the handle's lease has lapsed at `now` (`leaseExpired lh.lease now = true` — the
`stale_exports` idle window has elapsed), then the handle IS `Reclaimable`. This is the sound
distributed-GC trigger that CLOSES the `Exec.CapTP` §4 OPEN: reclamation is driven by lease
expiry, the locally-decidable timeout, never by deciding global deadness. The honest
realization of "eventual reclamation of unreachable exported caps" — eventual, because every
handle's lease eventually lapses unless renewed. -/
theorem captp_gc_by_lease {CellId Rights : Type*}
    (lh : LeasedHandle CellId Rights) (now : Nat)
    (hexp : leaseExpired lh.lease now = true) :
    Reclaimable lh now = true :=
  hexp

/-- **`captp_no_premature_reclaim` (PROVED) — a current-lease handle is NOT reclaimed.**
Fail-closed safety: if the handle's lease has NOT yet lapsed at `now`
(`leaseExpired lh.lease now = false` — the holder is still within its idle window), then the
handle is NOT `Reclaimable`. The runtime never reclaims a handle whose lease is current, so a
live-leased cap is never stranded — exactly `stale_exports` refusing to list a recently-active
export. This is the safety dual of `captp_gc_by_lease`. -/
theorem captp_no_premature_reclaim {CellId Rights : Type*}
    (lh : LeasedHandle CellId Rights) (now : Nat)
    (hcur : leaseExpired lh.lease now = false) :
    Reclaimable lh now = false :=
  hcur

/-- **`captp_renewed_not_reclaimed` (PROVED) — a leased-AND-renewed handle is NOT reclaimed.**
The headline no-premature-reclaim law on RENEWAL: renewing a handle at block `now` with a
positive idle window (`0 < maxIdle`) yields a handle that is NOT reclaimable at `now`. Renewal
(`record_export_with_session` bumping `last_activity = now`, `gc.rs:136`) sets the lease to
lapse at `now + maxIdle > now`, so `leaseExpired` is `false` and reclaim is refused. Activity
keeps a cross-vat cap alive precisely as long as the holder keeps touching it — the lease is
the liveness bound, renewed by use. -/
theorem captp_renewed_not_reclaimed {CellId Rights : Type*}
    (lh : LeasedHandle CellId Rights) (now maxIdle : Nat)
    (hpos : 0 < maxIdle) :
    Reclaimable (renew lh now maxIdle) now = false := by
  unfold Reclaimable renew leaseOf leaseExpired
  -- The renewed lease lapses at `now + maxIdle`; `now + maxIdle ≤ now` is false since `0 < maxIdle`.
  simp only [decide_eq_false_iff_not, Nat.not_le]
  omega

/-! ## §3 — The cross-vat cycle leak is THE PRICE of the impossibility.

The reason CapTP cannot reclaim by proven-death — and must fall back to lease expiry — is the
PROVED impossibility of `Liveness`: deadness is undecidable (`dead_undecidable`) and a sound
local collector NEVER reclaims a cross-vat cycle (`crossvat_cycle_leaks`). We connect both
here: the leak is a CONSEQUENCE of soundness, and lease-reclaim is the honest workaround. -/

/-- **`captp_cycle_leak_is_the_price` (PROVED, reuses `Liveness.crossvat_cycle_leaks`).**
The cross-vat reference CYCLE leaks under any sound local-evidence collector: given a
`SoundLocalCollector` and a `CrossVatCycle g a b`, the collector reclaims NEITHER node by
reachability (`collect g a = false ∧ collect g b = false`). Each node pins the other's
refcount ≥ 1 forever, so the only sound local trigger (`refcountZero`) never fires — yet both
cells are genuinely dead. This is precisely WHY CapTP cannot close its §4 GC by proven-death:
no sound vat-local collector can decide the cycle dead. The leak is the PROVED PRICE of
soundness, not a bug — and lease expiry (`captp_gc_by_lease`) is the only honest reclaim. -/
theorem captp_cycle_leak_is_the_price
    (col : SoundLocalCollector) (g : LivenessGraph) (a b : CellId)
    (hcyc : CrossVatCycle g a b) :
    col.collect g a = false ∧ col.collect g b = false :=
  crossvat_cycle_leaks col g a b hcyc

/-- **`captp_death_undecidable_so_lease` (PROVED, reuses `Liveness.dead_undecidable`) — the
deep reason lease-reclaim is forced.** There is NO computable procedure deciding deadness of
the gadget cell across the halting-reduction family: a computable decider would solve the
halting problem. So CapTP distributed GC CANNOT be "decide dead, then reclaim" — that decision
does not exist as an algorithm. Lease expiry (`captp_gc_by_lease`) is not a convenience; it is
the ONLY locally-decidable reclaim trigger available once proven-death is off the table. We
re-expose `Liveness.dead_undecidable` to make the entailment "undecidable ⇒ lease" explicit at
the CapTP layer. -/
theorem captp_death_undecidable_so_lease (n : ℕ) :
    ¬ ∃ d : Nat.Partrec.Code → Bool,
        Computable d ∧
        (∀ c : Nat.Partrec.Code, d c = true ↔ Dead (haltGraph ((Nat.Partrec.Code.eval c n).Dom)) 1) :=
  dead_undecidable n

/-- **`captp_leaked_handle_reclaimed_by_lease` (PROVED, reuses `Liveness.leak_bounded_by_lease`)
— the leak is bounded, not forever.** A leaked cross-vat-cycle node, never reachability-
collected (`captp_cycle_leak_is_the_price`), is STILL reclaimed at the operational `Live` level
once its lease lapses: a dead cycle node past its lease is not `Live`. So an import handle on a
cross-vat cycle leaks not *forever* but only *until its lease expires* — the dregg2-coherent
bound that needs no global view, survives partition, and respects graph privacy. This is the
exact sense in which lease-reclaim CLOSES the §4 OPEN: the leak is real and proved, and the
lease bounds it. -/
theorem captp_leaked_handle_reclaimed_by_lease
    (g : LivenessGraph) (l : Lease) (now : Nat) (a b : CellId)
    (hcyc : CrossVatCycle g a b) (hexp : leaseExpired l now = true) :
    ¬ Live g l now a :=
  leak_bounded_by_lease g l now a b hcyc hexp

/-! ## §4 — Non-vacuity: concrete expired-lease reclaim and renewed-no-reclaim. -/

section NonVacuity

/-- A concrete leased handle: holder cell `0`, exported cap to target `1` with unit rights,
last active at block 100 with a 50-block idle window (lease lapses at 150). -/
def demoLeased : LeasedHandle Nat Unit :=
  { handle := { holder := 0, exported := { target := 1, rights := () } }
  , lease  := leaseOf 100 50 }

/-- At `now = 200` the lease (lapse at 150) has expired, so the handle IS reclaimable —
concrete `captp_gc_by_lease`. -/
example : Reclaimable demoLeased 200 = true :=
  captp_gc_by_lease demoLeased 200 (by decide)

/-- At `now = 120` the lease (lapse at 150) is current, so the handle is NOT reclaimed —
concrete `captp_no_premature_reclaim` (fail-closed while leased). -/
example : Reclaimable demoLeased 120 = false :=
  captp_no_premature_reclaim demoLeased 120 (by decide)

/-- Renewing at `now = 120` with a positive idle window leaves the handle NOT reclaimable at
`120` — concrete `captp_renewed_not_reclaimed` (activity renews the lease). -/
example : Reclaimable (renew demoLeased 120 50) 120 = false :=
  captp_renewed_not_reclaimed demoLeased 120 50 (by decide)

-- Expired lease ⇒ reclaimable; current lease ⇒ not. Locally-decidable, no global view.
#eval Reclaimable demoLeased 200                 -- expected: true  (200 ≥ 150, lease lapsed)
#eval Reclaimable demoLeased 120                 -- expected: false (120 < 150, lease current)
#eval Reclaimable (renew demoLeased 120 50) 120  -- expected: false (renewed: lapses at 170)
#eval s!"demo handle holder={demoLeased.handle.holder}, lease expiresAt={demoLeased.lease.expiresAt}: \
reclaim@200={Reclaimable demoLeased 200}, reclaim@120={Reclaimable demoLeased 120}"

end NonVacuity

/-! ## §5 — Axiom-hygiene tripwires.

Every PROVED keystone depends ONLY on the three standard kernel axioms (no `sorryAx`). The
cross-vat-cycle leak and deadness-undecidability are REUSED from `Liveness` (themselves
`sorry`-free), so the entailment "undecidable ⇒ lease-reclaim" carries no hidden residue. -/

#assert_axioms captp_gc_by_lease
#assert_axioms captp_no_premature_reclaim
#assert_axioms captp_renewed_not_reclaimed
#assert_axioms captp_cycle_leak_is_the_price
#assert_axioms captp_death_undecidable_so_lease
#assert_axioms captp_leaked_handle_reclaimed_by_lease

end Dregg2.Exec.CapTPGC
