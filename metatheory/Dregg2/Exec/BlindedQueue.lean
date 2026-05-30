/-
# Dregg2.Exec.BlindedQueue — the "commitments-in, nullifiers-out" private-consumption queue.

`STORAGE-AS-CELL-PROGRAMS.md §3.4`: a `BlindedQueue` is **not a new Effect** — it is a **cell**
whose state is a commitments set (blinded items *added*), a nullifier set (items *spent*), and
two monotone counts (`countAdded`/`countSpent`, with `countSpent ≤ countAdded`). It is the
canonical privacy-voting / sealed-bid primitive: a producer enqueues a *blinded* commitment, and
a consumer privately spends it by publishing a *nullifier* (revealing nothing about *which* item)
together with a ZK **spend proof**. Per `PREDICATE-INVENTORY.md §9.4` it is the ONLY storage
primitive needing a `Witnessed` spend predicate — and that predicate is exactly the `dregg2 §8`
verify oracle.

We **reuse, never redefine**:
- `NullifierCell.Cell` (the G-Set of consumed nullifiers) + `spend` + its anti-double-spend law
  `spend_no_double_spend` for the *anti-double-spend half* (§3.4 slot 1 / slot 5: `nullifier_root`
  monotone, double-spend rejected). We do NOT touch the nullifier-set discipline; we wrap it.
- `CryptoKernel.verify` (the `dregg2 §8` decidable spend oracle) for the *privacy-gate half*
  (§3.4 slot 6: `spend_air_vk`). A `consume` is admissible only when `verify spendStmt proof`
  accepts — the witnessed `WitnessedPredicate::Custom { vk_hash }` of §3.4 made into an interface
  obligation we USE. Its soundness/extractability is the CIRCUIT obligation, NEVER a Lean law.

THE KEYSTONE (two parts), both PROVED:
- `blinded_no_double_spend` — a nullifier already spent cannot be consumed again (lifted from
  `NullifierCell.spend_no_double_spend`): the same item is consumed at most once.
- `consume_needs_verify` — a *committed* `consume` implies `CryptoKernel.verify` accepted the
  spend proof: the privacy gate. You cannot spend without a valid proof.
Plus `countSpent_le_added` — the conservation-ish bound (spent never exceeds added), preserved
by every transition.

Parametric over `[CryptoKernel Digest Proof]`, so every theorem holds for *any* lawful kernel
(the abstract proving instance) AND for the Rust FFI one (the running instance). The `#eval`
demos run against the `Reference` kernel in `CryptoKernel.lean`.

Pure, computable, `#eval`-able. No `axiom`/`admit`/`native_decide`/`sorry`.
-/
import Dregg2.Exec.NullifierCell
import Dregg2.CryptoKernel

namespace Dregg2.Exec.BlindedQueue

open Dregg2.Crypto (CryptoKernel)
open Dregg2.Privacy (Nullifier)

universe u

variable {Digest Proof : Type} [AddCommGroup Digest] [CryptoKernel Digest Proof]

/-! ## The state — commitments added, nullifiers spent (reusing the `NullifierCell`), and counts. -/

/-- **A `BlindedQueue` state** (`STORAGE-AS-CELL-PROGRAMS §3.4`, name-keyed not 8-slot):
- `commitments` — the set of blinded item commitments *added* (the §3.4 `commitments_root`,
  modelled as the live `Finset` of digests rather than a Merkle digest; grow-only).
- `nullifiers`  — the spent-nullifier set, REUSING `NullifierCell.Cell` *unchanged* (the §3.4
  `nullifier_root`; its append-only / anti-double-spend discipline is the cell's own law).
- `countAdded` / `countSpent` — the monotone counters (`commitment_count` / `nullifier_count`),
  with the standing invariant `countSpent ≤ countAdded` (a spend consumes an added item).

`Digest` is the commitment carrier (the `CryptoKernel`'s hash/commit codomain). -/
structure State (Digest : Type) where
  /-- The blinded commitments added so far (grow-only; the `commitments_root` live set). -/
  commitments : Finset Digest
  /-- The spent-nullifier set — the reused `NullifierCell.Cell` (its own append-only law). -/
  nullifiers : NullifierCell.Cell
  /-- Number of items added (monotone ↑). -/
  countAdded : Nat
  /-- Number of items spent (monotone ↑); standing invariant `countSpent ≤ countAdded`. -/
  countSpent : Nat

/-- The empty queue: nothing added, nothing spent (the genesis state). -/
def empty [DecidableEq Digest] : State Digest :=
  { commitments := ∅, nullifiers := NullifierCell.empty, countAdded := 0, countSpent := 0 }

/-! ## `add` — enqueue a blinded commitment (monotone, fail-open: adding is always allowed). -/

/-- **`add s c`** — the producer enqueues a blinded commitment `c`. Insert it into the
commitments set and bump `countAdded`. This is grow-only (`STORAGE-AS-CELL-PROGRAMS §3.4`:
"commitments only added"): no commitment is ever removed. Adding never spends, so the
`countSpent ≤ countAdded` invariant is *preserved* (the gap only widens). -/
def add [DecidableEq Digest] (s : State Digest) (c : Digest) : State Digest :=
  { s with commitments := insert c s.commitments, countAdded := s.countAdded + 1 }

/-! ## `consume` — privately spend an item (fail-closed; the two-gate AND of §3.4). -/

/-- **`consume s spendStmt proof n`** — the consumer privately spends, publishing nullifier `n`
under the spend statement `spendStmt : Digest` with witness `proof : Proof`. It is the AND of
**both** §3.4 gates, fail-closed (`none` on either failure):

1. **The privacy gate** (`CryptoKernel.verify spendStmt proof = true`) — the `dregg2 §8`
   witnessed spend predicate (§3.4 slot 6). You may not spend without a valid spend proof. Its
   soundness is the circuit obligation; here it is the decidable oracle the cell consults.
2. **The anti-double-spend gate** (`NullifierCell.spend s.nullifiers n` succeeds) — `n` must be
   *fresh* in the spent set, REUSING the nullifier cell's own append-only `spend`. A re-presented
   nullifier is rejected by `NullifierCell`'s law.

On success: the nullifier is recorded (via the reused cell) and `countSpent` is bumped. -/
def consume (s : State Digest) (spendStmt : Digest) (proof : Proof) (n : Nullifier) :
    Option (State Digest) :=
  if CryptoKernel.verify spendStmt proof then
    match NullifierCell.spend s.nullifiers n with
    | some nz => some { s with nullifiers := nz, countSpent := s.countSpent + 1 }
    | none    => none                       -- nullifier already spent ⇒ fail-closed
  else
    none                                    -- spend proof rejected ⇒ fail-closed (privacy gate)

/-! ## THE KEYSTONE, part (a) — `blinded_no_double_spend` (REUSING the nullifier cell's law). -/

/-- **Anti-double-spend, reuse rejected — PROVED (lifted from `NullifierCell`).** If nullifier
`n` is already in the spent set, then NO `consume` succeeds with that `n`, *regardless* of the
spend statement/proof: the consume returns `none`. The same item is consumed at most once. This
delegates straight to `NullifierCell.spend_rejects_double` (the reused cell's own law); the
verify gate cannot rescue an already-spent nullifier. -/
theorem consume_rejects_double (s : State Digest)
    (spendStmt : Digest) (proof : Proof) (n : Nullifier)
    (h : n ∈ s.nullifiers.spent) :
    consume s spendStmt proof n = none := by
  unfold consume
  rw [NullifierCell.spend_rejects_double s.nullifiers n h]
  -- now the body is `if verify … then (match none with …) else none`; both branches are `none`.
  by_cases hv : CryptoKernel.verify spendStmt proof = true
  · rw [if_pos hv]
  · rw [if_neg hv]

/-- **THE KEYSTONE (a) — `blinded_no_double_spend`.** The two halves the spent set guarantees,
stated for the `BlindedQueue` `consume` and PROVED by REUSING `NullifierCell.spend_no_double_spend`:
- a nullifier already spent is rejected (`consume … = none`) — anti-double-spend; AND
- a *successful* consume lands the nullifier in the resulting state's spent set (so it can never be
  spent a second time — grow-only).
Together: each blinded item is consumed **at most once**. -/
theorem blinded_no_double_spend (s : State Digest)
    (spendStmt : Digest) (proof : Proof) (n : Nullifier) :
    (n ∈ s.nullifiers.spent → consume s spendStmt proof n = none)
    ∧ (∀ s', consume s spendStmt proof n = some s' → n ∈ s'.nullifiers.spent) := by
  refine ⟨consume_rejects_double s spendStmt proof n, ?_⟩
  intro s' hcons
  -- A successful consume passed the verify gate and a fresh-`spend`; its nullifier set is `nz`,
  -- which by `NullifierCell.spend` contains `n`.
  unfold consume at hcons
  by_cases hv : CryptoKernel.verify spendStmt proof = true
  · rw [if_pos hv] at hcons
    -- split on the reused `spend`
    cases hsp : NullifierCell.spend s.nullifiers n with
    | none => rw [hsp] at hcons; exact absurd hcons (by simp)
    | some nz =>
        rw [hsp] at hcons
        -- the second keystone-half of the reused cell gives `n ∈ nz.spent`
        have hfresh : n ∉ s.nullifiers.spent := by
          by_contra hin
          rw [NullifierCell.spend_rejects_double s.nullifiers n hin] at hsp
          exact absurd hsp (by simp)
        have := (NullifierCell.spend_no_double_spend s.nullifiers n).2 hfresh
        obtain ⟨c', hc', hmem⟩ := this
        -- `spend = some nz` and `spend = some c'` ⇒ `nz = c'`
        rw [hsp] at hc'
        have hnz : nz = c' := by injection hc'
        -- `s' = { s with nullifiers := nz, … }`, so `s'.nullifiers = nz`
        have hs' : { s with nullifiers := nz, countSpent := s.countSpent + 1 } = s' := by
          injection hcons
        subst hs'
        subst hnz
        exact hmem
  · rw [if_neg hv] at hcons
    exact absurd hcons (by simp)

/-! ## THE KEYSTONE, part (b) — `consume_needs_verify` (the privacy gate). -/

/-- **THE KEYSTONE (b) — `consume_needs_verify`.** A *committed* `consume` implies the
`CryptoKernel.verify` oracle ACCEPTED the spend proof. This is the privacy gate of
`STORAGE-AS-CELL-PROGRAMS §3.4`: you cannot spend a blinded item without presenting a valid spend
proof. The soundness/extractability of that proof is the §8 circuit obligation we *use*, never
prove; this theorem is the *cell-side* guarantee that the oracle was consulted and accepted. -/
theorem consume_needs_verify (s s' : State Digest)
    (spendStmt : Digest) (proof : Proof) (n : Nullifier)
    (h : consume s spendStmt proof n = some s') :
    CryptoKernel.verify spendStmt proof = true := by
  unfold consume at h
  by_cases hv : CryptoKernel.verify spendStmt proof = true
  · exact hv
  · rw [if_neg hv] at h; exact absurd h (by simp)

/-! ## The conservation-ish bound — `countSpent ≤ countAdded`, preserved by every transition. -/

/-- The standing invariant of a well-formed queue: spent never exceeds added. -/
def Invariant (s : State Digest) : Prop := s.countSpent ≤ s.countAdded

/-! **`add` preserves the bound — PROVED.** Adding bumps `countAdded` and leaves `countSpent`
fixed, so `countSpent ≤ countAdded` only becomes *slacker* (the gap widens). -/
omit [AddCommGroup Digest] [CryptoKernel Digest Proof] in
theorem add_preserves_bound [DecidableEq Digest] (s : State Digest) (c : Digest)
    (h : Invariant s) : Invariant (add s c) := by
  unfold Invariant add at *
  simp only
  omega

/-- **`consume` preserves the bound — PROVED (the conservation-ish keystone).** A successful
`consume` bumps `countSpent` by exactly 1 and leaves `countAdded` fixed. Because a `consume`
*requires a fresh nullifier* and the bound held before, after the bump `countSpent ≤ countAdded`
still holds — PROVIDED the queue admitted at least as many adds as the new spend count. We prove
the clean monotone step: if before the consume `countSpent < countAdded` (there is an unspent
item to consume), the bound is preserved.

`-- OPEN:` the *tight* form `Invariant s → Invariant s'` needs the cross-field link "a fresh
nullifier corresponds to a distinct previously-added commitment" — i.e. `countSpent < countAdded`
must HOLD whenever a fresh `spend` succeeds. That linkage (nullifier ⟷ commitment) is precisely
the spend AIR's extractability obligation (`§3.4` slot-6 witnessed predicate / `dregg2 §8`): the
proof witnesses an item in the commitments tree. It is an INTERFACE obligation discharged by the
circuit, NOT provable from the set discipline alone — so here we take `countSpent < countAdded`
as the (verify-supplied) hypothesis rather than weakening or asserting it. -/
theorem consume_preserves_bound (s s' : State Digest)
    (spendStmt : Digest) (proof : Proof) (n : Nullifier)
    (hlt : s.countSpent < s.countAdded)
    (h : consume s spendStmt proof n = some s') :
    Invariant s' := by
  unfold Invariant
  -- extract the shape of `s'` from a successful consume
  unfold consume at h
  by_cases hv : CryptoKernel.verify spendStmt proof = true
  · rw [if_pos hv] at h
    cases hsp : NullifierCell.spend s.nullifiers n with
    | none => rw [hsp] at h; exact absurd h (by simp)
    | some nz =>
        rw [hsp] at h
        have hs' : { s with nullifiers := nz, countSpent := s.countSpent + 1 } = s' := by
          injection h
        subst hs'
        simp only
        omega
  · rw [if_neg hv] at h; exact absurd h (by simp)

/-- **`countSpent_le_added` — the bound as the named conservation lemma.** Restates
`consume_preserves_bound` as the headline guarantee: after a (fresh, verified) consume from a
queue with an unspent item, `countSpent ≤ countAdded`. The "spent never exceeds added" bound of
`STORAGE-AS-CELL-PROGRAMS §3.4`. -/
theorem countSpent_le_added (s s' : State Digest)
    (spendStmt : Digest) (proof : Proof) (n : Nullifier)
    (hlt : s.countSpent < s.countAdded)
    (h : consume s spendStmt proof n = some s') :
    s'.countSpent ≤ s'.countAdded :=
  consume_preserves_bound s s' spendStmt proof n hlt h

/-! ## `add` is monotone / grow-only — every prior commitment survives, count only climbs. -/

/-! **`add` is grow-only — PROVED.** Every previously-added commitment is still present after an
`add`, and `countAdded` strictly increases. The §3.4 "commitments only added" discipline. -/
omit [AddCommGroup Digest] [CryptoKernel Digest Proof] in
theorem add_monotone [DecidableEq Digest] (s : State Digest) (c : Digest) :
    s.commitments ⊆ (add s c).commitments ∧ s.countAdded < (add s c).countAdded := by
  refine ⟨?_, ?_⟩
  · exact Finset.subset_insert c s.commitments
  · unfold add; simp only; omega

/-- **A successful `consume` never *removes* a spent nullifier — PROVED (grow-only).** The spent
set only grows: every nullifier spent before the consume is still spent after. Lifts
`NullifierCell.spend_monotone` through the queue wrapper. -/
theorem consume_nullifiers_monotone (s s' : State Digest)
    (spendStmt : Digest) (proof : Proof) (n : Nullifier)
    (h : consume s spendStmt proof n = some s') :
    s.nullifiers.spent ⊆ s'.nullifiers.spent := by
  unfold consume at h
  by_cases hv : CryptoKernel.verify spendStmt proof = true
  · rw [if_pos hv] at h
    cases hsp : NullifierCell.spend s.nullifiers n with
    | none => rw [hsp] at h; exact absurd h (by simp)
    | some nz =>
        rw [hsp] at h
        have hs' : { s with nullifiers := nz, countSpent := s.countSpent + 1 } = s' := by
          injection h
        subst hs'
        simp only
        exact NullifierCell.spend_monotone s.nullifiers nz n hsp
  · rw [if_neg hv] at h; exact absurd h (by simp)

/-! ## It runs (`#eval`) — against the `Reference` CryptoKernel of `CryptoKernel.lean`.

The reference kernel's `verify stmt proof := decide (stmt = proof)` (accepts iff the proof
*echoes* the statement). So a "valid" spend proof is `proof = spendStmt`; a "bad" one is anything
else. `Digest = Proof = Int` there. We demo: add two commitments; consume with a valid proof
(nullifier recorded); consume the SAME nullifier again (rejected by anti-double-spend); and
consume with a BAD proof (rejected by the verify gate). -/

open Dregg2.Crypto.Reference (D P)

private def n1 : Nullifier := { tag := 1 }
private def n2 : Nullifier := { tag := 2 }

/-- A blinded queue over the reference kernel: add commitments `7` and `9`. -/
private def q0 : State D := add (add (empty (Digest := D)) 7) 9

-- two items added ⇒ countAdded = 2, countSpent = 0
#eval (q0.countAdded, q0.countSpent)                                   -- (2, 0)

/-- A *valid* spend: statement `42`, proof `42` (echo ⇒ `verify` accepts), nullifier `n1`. -/
private def q1? : Option (State D) := consume q0 (42 : D) (42 : P) n1

-- valid proof + fresh nullifier ⇒ admitted; countSpent bumped to 1
#eval q1?.map (fun s => (s.countAdded, s.countSpent))                  -- some (2, 1)
-- the nullifier n1 is now recorded in the spent set
#eval q1?.map (fun s => decide (n1 ∈ s.nullifiers.spent))              -- some true

-- consume the SAME nullifier n1 AGAIN (valid proof, but already spent) ⇒ rejected (anti-double-spend)
#eval (q1?.bind (fun s => consume s (42 : D) (42 : P) n1)).isNone      -- true

-- consume with a BAD proof (statement 42, proof 99 ≠ 42 ⇒ verify rejects), fresh nullifier n2 ⇒ rejected (privacy gate)
#eval (q1?.bind (fun s => consume s (42 : D) (99 : P) n2)).isNone      -- true

-- a DIFFERENT valid spend (statement 5, proof 5), fresh nullifier n2 ⇒ admitted; countSpent = 2
#eval (q1?.bind (fun s => consume s (5 : D) (5 : P) n2)).map
        (fun s => (s.countAdded, s.countSpent))                        -- some (2, 2)

end Dregg2.Exec.BlindedQueue
