# DRIFT-STABILITY SPECTRUM — caveats, concurrency, CRDTs, and the coordination dial

> Captured 2026-05-31 from a design conversation (ember + Claude) while building the wholesale-swap
> waves. The thread: *cross-cell state caveats* → *what if state drifts during composition* →
> *finer structure of I-confluence* → *CRDTs as a dregg2 library* → *conditional drift-stability*.
> Anchored on what is **built** (`Dregg2/Exec/CrossCaveat.lean`, `Dregg2/Exec/JointCell.lean`,
> `Dregg2/Confluence.lean`, `Dregg2/Authority/ThirdPartyDischarge.lean`) vs **proposed**.

## 0. The two windows (don't conflate them)

A caveat `φ` that reads state has TWO distinct soundness windows:

- **Commit-instant (TOCTOU).** Is `φ` checked on the same snapshot the turn commits against?
  **SOLVED, built** — `CrossCaveat.caveated_check_eq_use`: in an atomic (joint) turn the check-state
  and use-state are the identical `(A,B)`, indivisibly. This is the **equalizer** window (a limit).
- **Composition-window drift.** While parties *compose* a turn (negotiate / sign / await), the cells
  drift forward underneath them. Is a turn composed against `v₀` still valid at commit against
  `v₀ ⊔ Δ`? **This is the merge question**, and it is governed by the spectrum below (a colimit /
  monotone-merge property — the *dual* of the equalizer window).

## 1. Cross-cell caveats = a further equalizer on the joint turn (BUILT)

`Dregg2/Exec/CrossCaveat.lean` (committed `6fbd2e43`). A cross-cell caveat `φ : KernelState →
KernelState → Bool` *factors through the turn*: its type needs BOTH cells, so a caveat reading `B`
*forces* the turn to be a bilateral `JointCell.BiTurn` over `{A,B}`. Admissibility =
`SharedBinding ⊓ {φ holds}` — the CG-2 equalizer (`SharedBinding.agree`, "the two legs collapse")
refined by one more equalizer condition. Keystones (all `#assert_axioms`-clean):
`crossCaveat_sound` (= CG-5 conservation ∧ CG-2 single-identity ∧ φ), `caveated_check_eq_use`
(no TOCTOU), `crossCaveat_rejects` + `covenant_rejects_high` (teeth: a real B-reading covenant gates;
the raw turn commits regardless, the caveated one rejects when B violates it). It is an **equalizer
(limit), NOT a coequalizer** (that is FORK, the dual). The `f^* ⊣ f_*` base-change adjunction is the
*sheaf packaging* — deliberately NOT claimed (aspirational). This is the construct dregg1 deliberately
**refused** (`authorize.rs:1608`, "a macaroon is only sound where the verifier holds the cell's
secret") — correctly, without a metatheory; now sound.

## 2. The drift-stability spectrum (the coordination-cost ladder)

I-confluence is NOT binary. "Compatible forward drift" is a **merge** `x ⊔ Δ`, and the cheapest
structure under which `φ` survives it is a ladder:

| # | Tier | survives the merge because… | coordination | dregg2 today |
|---|---|---|---|---|
| 0 | **Independent** | `φ` ignores the drifting state | none | — |
| 1 | **Monotone / CRDT-native** | `φ` is an **up-set** in the join-semilattice; updates inflationary | none ever | `Confluence.IConfluent` + `admits_sound` |
| 2 | **Confluent-after-lifting** | non-monotone *net*, but a projection off a monotone lattice (track components) | none, over richer state | — (proposed) |
| 3 | **Reservation-conditional** | a bounded resource made local-safe by **reserving quota** | only to rebalance reservations | **escrow holding-store** (built) |
| 4 | **Lock-conditional** | exclusive access cuts drift to a **chain** (no incomparable merge) | acquiring the lock | `turn/src/fast_path` cell-locking |
| 5 | **Per-op coordinated** | genuinely non-monotone, no rep | the atomic **equalizer** per use; blocks under partition | `CrossCaveat`/`jointApply` |

**Tier 2 is the deep move:** most non-confluent invariants become confluent if you *enrich the state
to restore monotonicity*. `balance` isn't monotone, but `(deposits, withdrawals)` is a pair of
monotone counters and the value is a non-monotone *projection*. "Is `φ` I-confluent?" ≡ "is there a
monotone lattice this observable is an up-set of?"

## 3. CRDTs = `MergeState` instances; the library (PROPOSED, foundation-first)

A CRDT is *exactly* `(join-semilattice, inflationary updates)` = `Confluence.MergeState` + a monotone
invariant. So **a CRDT library = a catalog of `MergeState` instances + their proved `IConfluent`
invariants**, dropping straight into existing machinery — no new foundation. It:

- **composes into proofs trivially**: lattices compose (product / function-into / lexicographic) and
  I-confluence is preserved by the combinators (`IConfluent A × IConfluent B → IConfluent (A×B)`), so
  a cell built from CRDT parts inherits tier-1 coordination-freedom *compositionally*;
- **is the userspace story** (storage-as-cell-programs over a small verified core): an app declares
  its cell state as a library CRDT and gets drift-stable, partition-tolerant behavior *with the proof
  attached*;
- **subsumes escrow**: dregg's escrow holding-store IS the **bounded-counter / reservation CRDT**
  (tier 3) — the canonical answer to "`balance ≥ 0` isn't confluent." Reserve quota → spend locally
  drift-stably → coordinate only to rebalance. Per-asset escrow = a per-asset reservation lattice.

Catalog: G-Counter, PN-Counter (= two G-counters, tier-2 lift), G/2P/OR-Set, LWW-Register,
MV-Register, Bounded-Counter/Escrow (tier-3), + composition combinators.

**ember's preference: pull an existing Lean4 CRDT development if one exists (saves work); else build
thin on mathlib's `SemilatticeSup`/`Order`/`Finset` + `Confluence.MergeState`.** (Kagi sweep
`w2qc3605i` in flight to find pullable libs / port candidates [Isabelle AFP "Verifying Strong
Eventual Consistency", Coq Verdi] / the mathlib foundation.)

## 4. Conditional drift-stability (the lock / reservation), formalized (PROPOSED)

Drift-stability is *relative to which merges are reachable*; an environment guarantee restricts them,
enlarging what's stable:

```
IConfluentUnder (E φ : Invariant S) : Prop := ∀ x y, E x → E y → φ x → φ y → φ (x ⊔ y)
```
— confluence in the **sublattice cut out by `E`**. A **lock** sets `E = single-writer` → reachable
drift is a **chain** (totally ordered → no incomparable merge → *every* `φ` confluent there). A
**reservation** sets `E = my-quota-reserved`. More guarantee (lock ⊃ reservation ⊃ nothing) → higher
on the ladder → less per-op coordination — but establishing the guarantee costs the coordination once
(at the lock/reservation), not per op.

## 5. Caveats declare their tier (PROPOSED — and it IS computable)

The caveat type should carry its drift-stability tier **as a dependent record**:
```
structure TieredCaveat where
  φ      : Ctx → Bool
  tier   : DriftTier            -- monotone | lifted | reservation | locked | coordinated
  proof  : DriftWitness φ tier  -- e.g. for `monotone`: a Tier1Eligible/IConfluent proof of φ
```
**Why this is sound + computable (the verify-not-find discipline):** "is `φ` I-confluent?" is NOT
decidable in general (∀ over all merges) — so we DON'T decide it. The tier is **carried as a
witness** (supplied at construction — the CRDT library hands it over *for free*), and the executor
just **reads the tag and dispatches** (monotone → run coordination-free; coordinated → take the
equalizer). Dispatch is computable (read data); soundness is the carried proof; inference is never
attempted. This is exactly dregg's load-bearing seam: *the tier is a checked witness, never a
search.* Useful: the executor pays the **minimal sound coordination per caveat** (free for monotone,
equalizer only for genuinely-coordinated), and it's programmable (userspace picks a tier via the CRDT
library). Verdict: **yes, we should; yes we can (dispatch-computable via the carried witness); yes
it's useful.**

## 6. It's all the Agreement dial / single-machine principle

The ladder IS the topology-parametrized coordination cost. Single machine: merges are *serialized*
→ effectively tier-4-for-free → even non-confluent invariants are safe with zero ceremony.
Distributed: only tiers 1–2 are free; 3–5 cost progressively more (reservation < lock < equalizer),
and tier-5 blocks under partition. **CALM is the 1↔5 boundary; tiers 2/3/4 are the interesting middle
where real apps live**, and the CRDT+reservation+lock library is the kit for occupying them
deliberately. For non-monotone reads composed over time, the OCC staleness bound is already built:
`ThirdPartyDischarge`'s `MAX_DISCHARGE_AGE = 300`s (`stale_discharge_rejected`) — use a read for a
bounded window, else it's stale and rejected.

## 7. Decisions taken (this conversation)

1. **Escrow = the reservation CRDT (tier 3).** Wave-4 models escrow explicitly via
   `Confluence`/`MergeState` (a per-asset reservation lattice), not "a side-table that conserves."
2. **CRDT library is foundation-first** — built before/with wave-3/4 — but **pull an existing Lean4
   development if Kagi finds one** (else thin-on-mathlib). 
3. **Caveats declare their drift tier** (the `TieredCaveat` dependent record; dispatch-computable via
   the carried witness — §5). Enters with META-FILL D (caveat-into-the-gate).
4. **Asset-type the `EscrowRecord` now** ("asset-typing for free") — falls out of escrow-as-
   reservation-lattice (Q1), gives the per-asset combined measure `recTotalAsset b + escrowHeldAsset b`.

## 8. Built vs proposed (honesty ledger)

- **BUILT:** `CrossCaveat` (cross-cell caveat = equalizer; commit-instant TOCTOU solved);
  `JointCell` (CG-2 equalizer `SharedBinding`, CG-5 `joint_cg5_conserves`, `binding_is_proper`);
  `Confluence` (`MergeState` ⊔, `IConfluent`, `admits_sound`, `nonpairwise_escalation`, the
  `balance≥0` non-confluent witness); escrow holding-store; `ThirdPartyDischarge` freshness (the OCC
  bound); `fast_path` locks (Rust).
- **PROPOSED:** the CRDT library (tier-1/2 `MergeState` catalog + combinators); `IConfluentUnder`
  (conditional drift-stability); tier-2 lifting; the `TieredCaveat` record + the drift-stable
  composition theorem (compose under drift via `admits_sound`, no re-check); escrow-as-reservation-
  lattice (asset-typed). The lattice/up-set/limit-vs-colimit framing is **real order theory**
  (faithful), NOT a built categorical-limit object.
