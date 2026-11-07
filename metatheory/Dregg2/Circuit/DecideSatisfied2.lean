/-
# Dregg2.Circuit.DecideSatisfied2 — THE KERNEL BRIDGE for the deployed v2 denotation.

`Argus/InterpCore.decideVm`/`decideVm_iff_satisfiedVm` is the verified total reference for the v1
PER-ROW denotation `satisfiedVm`. This module is its v2 analog over the WHOLE-TRACE deployed object
`DescriptorIR2.Satisfied2`: an executable `decideSatisfied2 : … → Bool` plus the kernel-proven
`decideSatisfied2_iff_Satisfied2` (`decideSatisfied2 … = true ↔ Satisfied2 …`). This is the tiny
verified core a Rust ENUMERATOR runs against — it decides, for a CONCRETE multi-table witness, whether
the deployed `verify_vm_descriptor2`/`Ir2Air`/`Satisfied2` accept-set contains it.

## Why an ORACLE for the map-op leg (and ONLY that leg)

`Satisfied2`'s legs are decidable over a concrete trace EXCEPT the `mapOp` row leg `MapOp.holdsAt`,
whose denotation is an EXISTENTIAL opening of a sorted Poseidon2 heap (`opensTo`/`writesTo` —
`∃ h : FeltHeap, …`). The heap is unbounded, so the existential is not decidable in general (the spike
finding). We ORACLE-PARAMETERIZE exactly that leg: `decideSatisfied2` takes a `mapDec : VmRowEnv →
MapOp → Bool` (the supplied-witness / openings-table form — the SAME shape the deployment's prover
carries the opening path as a witness, and the SAME shape the existing differential test supplies it)
together with its faithfulness hypothesis `hmapDec : ∀ env m, mapDec env m = true ↔ m.holdsAt hash
env`. Everything ELSE is genuinely `Decidable`:

  * per-row `.base` / range — reuse `InterpCore.decideConstraint` / `VmRange.holds` (`DecidableEq ℤ`);
  * per-row `.lookup` — list membership in the concrete table (`DecidableEq` on `List ℤ`);
  * per-row `.window` — the two-row polynomial vanishes (`DecidableEq ℤ`);
  * per-row `.memOp` / `.umemOp` — row-locally `True` (their content is the GLOBAL leg);
  * per-row `.proofBind` — ⚑ the row-local recursion seam, three decidable congruences (its RECURSION
    content is still the global `Satisfied2Custom` leg);
  * the memory legs `memAddrsNodup` / `memClosed` / `memDisciplined` / `memBalanced` — the proved
    `MemoryChecking` predicates carry `Decidable` instances (Blum's discipline + the `Multiset`
    balance over a concrete log);
  * the table-faithfulness legs `memTableFaithful` / `mapTableFaithful` — list equality.

So `decideSatisfied2 mapDec … = true ↔ Satisfied2 …` holds UNDER `hmapDec`, with no other floor: the
ONLY undecidable content is the named heap-opening oracle, exactly as the spike found.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The
abstract `hash` enters only as a compared value (never inverted); `mapDec` is a SUPPLIED oracle, its
faithfulness a NAMED hypothesis (the heap-opening floor — the v2 analog of the v1 reference's totality).
NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Argus.InterpCore

namespace Dregg2.Circuit.DecideSatisfied2

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmHashSite VmRange siteHoldsAll)
open Dregg2.Circuit.Argus.InterpCore (decideConstraint decideConstraint_iff decideRanges
  decideRanges_iff decideSites decideSites_iff)
open Dregg2.Crypto

set_option autoImplicit false

/-! ## §1 — deciding ONE v2 constraint on a row window (the oracle rides the `mapOp` arm). -/

/-- **`decideLookup tf env l`** — the `.lookup` arm: the evaluated tuple is a row of the named table.
List membership over `List ℤ` is decidable (`DecidableEq`). Mirrors `Lookup.holdsAt`. -/
def decideLookup (tf : TraceFamily) (env : VmRowEnv) (l : Lookup) : Bool :=
  decide (l.tuple.map (·.eval env.loc) ∈ tf l.table)

theorem decideLookup_iff (tf : TraceFamily) (env : VmRowEnv) (l : Lookup) :
    decideLookup tf env l = true ↔ l.holdsAt tf env := by
  simp only [decideLookup, decide_eq_true_eq, Lookup.holdsAt]

/-- **`decideWindow env isLast w`** — the `.windowGate` arm: on `onTransition` the body need only
vanish off the last row, else on every row. Mirrors `WindowConstraint.holdsAt` exactly. -/
def decideWindow (env : VmRowEnv) (isLast : Bool) (w : WindowConstraint) : Bool :=
  if w.onTransition then isLast || decide (w.body.eval env ≡ 0 [ZMOD 2013265921])
  else decide (w.body.eval env ≡ 0 [ZMOD 2013265921])

theorem decideWindow_iff (env : VmRowEnv) (isLast : Bool) (w : WindowConstraint) :
    decideWindow env isLast w = true ↔ w.holdsAt env isLast := by
  unfold decideWindow WindowConstraint.holdsAt
  by_cases ht : w.onTransition
  · simp only [ht, if_true]
    cases isLast <;> simp
  · simp only [ht, if_false]
    simp

/-- ⚑ **`decideChal env isLast w`** — the `.chalGate` arm. Identical guard structure to
`decideWindow`; the body is a `ChalExpr`, which additionally reads `env.chal`. Decidable because the
drawn challenge slice is part of the row environment (the verifier's value, carried in the witness),
not an oracle. -/
def decideChal (env : VmRowEnv) (isLast : Bool) (w : ChalConstraint) : Bool :=
  if w.onTransition then isLast || decide (w.body.eval env ≡ 0 [ZMOD 2013265921])
  else decide (w.body.eval env ≡ 0 [ZMOD 2013265921])

theorem decideChal_iff (env : VmRowEnv) (isLast : Bool) (w : ChalConstraint) :
    decideChal env isLast w = true ↔ w.holdsAt env isLast := by
  unfold decideChal ChalConstraint.holdsAt
  by_cases ht : w.onTransition
  · simp only [ht, if_true]
    cases isLast <;> simp
  · simp only [ht, if_false]
    simp

/-- **`decideProofBind env m`** — the `.proofBind` arm: the ROW-LOCAL recursion seam. Decidable
congruences mirroring `ProofBind.holdsAt`: the guard is a bit, the attested program VK is the
DECLARED `vkPin`, the bound commitment is the DECLARED `bound`. ⚑ This arm used to be the constant
`true`, which is what made every enumeration over a `proofBind`-carrying descriptor blind to the one
kind that denoted nothing. -/
def decideZeroLanes (g : ℤ) (xs ys : List ℤ) : Bool :=
  (xs.length == ys.length) &&
    (xs.zip ys).all (fun p => decide (g * (p.1 - p.2) ≡ 0 [ZMOD 2013265921]))

theorem decideZeroLanes_iff (g : ℤ) (xs ys : List ℤ) :
    decideZeroLanes g xs ys = true ↔ zeroLanes g xs ys := by
  unfold decideZeroLanes zeroLanes
  simp [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]

def decideProofBind (env : VmRowEnv) (m : ProofBind) : Bool :=
  decide (m.guard.eval env.loc * (m.guard.eval env.loc - 1) ≡ 0 [ZMOD 2013265921]) &&
  (match m.vkPin with
   | none    => true
   | some vs => decideZeroLanes (m.guard.eval env.loc) (m.vk.map (·.eval env.loc)) vs) &&
  (match m.bound with
   | .port _   => true
   | .bound bs => decideZeroLanes (m.guard.eval env.loc) (m.commit.map (·.eval env.loc))
                    (bs.map (·.eval env.loc)))

theorem decideProofBind_iff (env : VmRowEnv) (m : ProofBind) :
    decideProofBind env m = true ↔ ProofBind.holdsAt env m := by
  unfold decideProofBind ProofBind.holdsAt
  cases hv : m.vkPin <;> cases hb : m.bound <;>
    simp [Bool.and_eq_true, decide_eq_true_eq, decideZeroLanes_iff, and_assoc]

/-- **`decideConstraint2 mapDec hash tf env isFirst isLast c`** — the Boolean decision of one v2
constraint's per-row denotation `c.holdsAt hash tf env isFirst isLast`. CASE-COMPLETE over the seven
`VmConstraint2` arms: `.base` rides the verified `decideConstraint`; `.lookup` rides `decideLookup`;
`.windowGate` rides `decideWindow`; `.proofBind` rides `decideProofBind` (⚑ NO LONGER `true`);
`.memOp`/`.umemOp` are row-locally `True`; `.mapOp` rides the SUPPLIED oracle `mapDec`. -/
def decideConstraint2 (mapDec : VmRowEnv → MapOp → Bool) (hash : List ℤ → ℤ)
    (tf : TraceFamily) (env : VmRowEnv) (isFirst isLast : Bool) : VmConstraint2 → Bool
  | .base c       => decideConstraint env isFirst isLast c
  | .lookup l     => decideLookup tf env l
  | .memOp _      => true
  | .mapOp m      => mapDec env m
  | .umemOp _     => true
  | .proofBind m  => decideProofBind env m
  | .windowGate w => decideWindow env isLast w
  -- ⚑ The challenge gate decides exactly like a window gate: same guard, same `≡ 0 [ZMOD p]`
  -- body, with `ChalExpr.eval` reading the row's challenge slice. Decidable because the challenge
  -- slice is part of the witness, not an oracle.
  | .chalGate w   => decideChal env isLast w

/-- **`decideConstraint2_iff`** — one v2 constraint is decided, under the oracle's faithfulness.
For EVERY `VmConstraint2 c`: `decideConstraint2 … c = true ↔ c.holdsAt hash tf env isFirst isLast`.
The seven arms dispatch through the verified per-arm reductions; the `.mapOp` arm consumes `hmapDec`. -/
theorem decideConstraint2_iff (mapDec : VmRowEnv → MapOp → Bool) (hash : List ℤ → ℤ)
    (hmapDec : ∀ (env : VmRowEnv) (m : MapOp), mapDec env m = true ↔ m.holdsAt hash env)
    (tf : TraceFamily) (env : VmRowEnv) (isFirst isLast : Bool) (c : VmConstraint2) :
    decideConstraint2 mapDec hash tf env isFirst isLast c = true
      ↔ c.holdsAt hash tf env isFirst isLast := by
  cases c with
  | base c       => exact decideConstraint_iff env isFirst isLast c
  | lookup l     => exact decideLookup_iff tf env l
  | memOp _      => simp [decideConstraint2, VmConstraint2.holdsAt]
  | mapOp m      => exact hmapDec env m
  | umemOp _     => simp [decideConstraint2, VmConstraint2.holdsAt]
  | proofBind m  => exact decideProofBind_iff env m
  | windowGate w => exact decideWindow_iff env isLast w
  | chalGate w   => exact decideChal_iff env isLast w

/-! ## §2 — the per-row constraint conjunct (over the whole main trace). -/

/-- **`decideRowConstraints2 mapDec hash d t`** — every declared constraint holds on every row
window: the `Satisfied2.rowConstraints` leg, as a Bool. The outer `List.range t.rows.length` walks
the rows; the inner `List.all` walks the constraints (matching the `∀ i < length, ∀ c ∈ constraints`
quantifier shape). -/
def decideRowConstraints2 (mapDec : VmRowEnv → MapOp → Bool) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (t : VmTrace) : Bool :=
  (List.range t.rows.length).all fun i =>
    d.constraints.all fun c =>
      decideConstraint2 mapDec hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) c

theorem decideRowConstraints2_iff (mapDec : VmRowEnv → MapOp → Bool) (hash : List ℤ → ℤ)
    (hmapDec : ∀ (env : VmRowEnv) (m : MapOp), mapDec env m = true ↔ m.holdsAt hash env)
    (d : EffectVmDescriptor2) (t : VmTrace) :
    decideRowConstraints2 mapDec hash d t = true
      ↔ ∀ i < t.rows.length, ∀ c ∈ d.constraints,
          c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  simp only [decideRowConstraints2, List.all_eq_true, List.mem_range,
    decideConstraint2_iff mapDec hash hmapDec]

/-! ## §3 — the per-row hash-site / range conjuncts. -/

/-- The v1 hash-site layer holds on every row (the `Satisfied2.rowHashes` leg). Reuses
`InterpCore.decideSites` through the `siteHoldsAll` decider. -/
def decideRowHashes2 (hash : List ℤ → ℤ) (d : EffectVmDescriptor2) (t : VmTrace) : Bool :=
  (List.range t.rows.length).all fun i =>
    decideSites hash (envAt t i) d.hashSites

theorem decideRowHashes2_iff (hash : List ℤ → ℤ) (d : EffectVmDescriptor2) (t : VmTrace) :
    decideRowHashes2 hash d t = true
      ↔ ∀ i < t.rows.length, siteHoldsAll hash (envAt t i) d.hashSites := by
  simp only [decideRowHashes2, List.all_eq_true, List.mem_range, decideSites_iff]

/-- The v1 range teeth hold on every row (the `Satisfied2.rowRanges` leg). -/
def decideRowRanges2 (d : EffectVmDescriptor2) (t : VmTrace) : Bool :=
  (List.range t.rows.length).all fun i => decideRanges (envAt t i) d.ranges

theorem decideRowRanges2_iff (d : EffectVmDescriptor2) (t : VmTrace) :
    decideRowRanges2 d t = true ↔ ∀ i < t.rows.length, ∀ r ∈ d.ranges, r.holds (envAt t i) := by
  simp only [decideRowRanges2, List.all_eq_true, List.mem_range, decideRanges_iff]

/-! ## §4 — the global memory / table-faithfulness conjuncts (the proved-decidable legs). -/

/-- The memory legs + table-faithfulness, as a Bool (every leg carries a `Decidable` instance: the
`Multiset` balance, the `MemoryChecking.Disciplined` discipline, `List.Nodup`, list membership, and
the table list equalities). The `mfin`-pinned `MemCheck` is over a CONCRETE log/boundary. -/
def decideMemLegs (d : EffectVmDescriptor2) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) : Bool :=
  decide maddrs.Nodup
    && (memLog d t).all (fun op => decide (op.addr ∈ maddrs))
    && decide (MemoryChecking.Disciplined (memLog d t))
    && decide (MemoryChecking.MemCheck minit mfin maddrs (memLog d t))
    && decide (t.tf .memory = (memLog d t).map opRow)
    && decide (t.tf .mapOps = mapLog d t)

theorem decideMemLegs_iff (d : EffectVmDescriptor2) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) :
    decideMemLegs d minit mfin maddrs t = true
      ↔ (maddrs.Nodup
          ∧ (∀ op ∈ memLog d t, op.addr ∈ maddrs)
          ∧ MemoryChecking.Disciplined (memLog d t)
          ∧ MemoryChecking.MemCheck minit mfin maddrs (memLog d t)
          ∧ t.tf .memory = (memLog d t).map opRow
          ∧ t.tf .mapOps = mapLog d t) := by
  simp only [decideMemLegs, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    decide_eq_true_eq]
  tauto

/-! ## §5 — `decideSatisfied2` — the assembled WHOLE-TRACE kernel bridge, and its correctness. -/

/-- **`decideSatisfied2 mapDec hash d minit mfin maddrs t`** — the total Boolean decision of the
deployed v2 denotation `Satisfied2`. ANDs the per-row constraint / hash-site / range conjuncts (over
every row window) with the global memory / table-faithfulness legs. The ONLY non-`Decidable` content
— the `mapOp` heap-opening existential — rides the SUPPLIED oracle `mapDec`. The faithful Lean twin of
the Rust enumerator's accept/reject decision on a concrete multi-table witness. -/
def decideSatisfied2 (mapDec : VmRowEnv → MapOp → Bool) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) : Bool :=
  decideRowConstraints2 mapDec hash d t
    && decideRowHashes2 hash d t
    && decideRowRanges2 d t
    && decideMemLegs d minit mfin maddrs t

/-- **`decideSatisfied2_iff_Satisfied2` — THE deliverable.** Under the oracle's faithfulness
`hmapDec` (the named heap-opening floor — the ONLY undecidable leg, the spike finding), the total
reference DECIDES the deployed accept-set: `decideSatisfied2 mapDec hash d minit mfin maddrs t = true
↔ Satisfied2 hash d minit mfin maddrs t`. So membership in the deployed `verify_vm_descriptor2`
accept-set is computable by `decideSatisfied2` — the tiny verified core the Rust enumerator runs. -/
theorem decideSatisfied2_iff_Satisfied2 (mapDec : VmRowEnv → MapOp → Bool) (hash : List ℤ → ℤ)
    (hmapDec : ∀ (env : VmRowEnv) (m : MapOp), mapDec env m = true ↔ m.holdsAt hash env)
    (d : EffectVmDescriptor2) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) :
    decideSatisfied2 mapDec hash d minit mfin maddrs t = true
      ↔ Satisfied2 hash d minit mfin maddrs t := by
  rw [decideSatisfied2, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    decideRowConstraints2_iff mapDec hash hmapDec, decideRowHashes2_iff, decideRowRanges2_iff,
    decideMemLegs_iff]
  constructor
  · rintro ⟨⟨⟨hrc, hrh⟩, hrr⟩, hnd, hcl, hdi, hba, hmf, hmpf⟩
    exact ⟨hrc, hrh, hrr, hnd, hcl, hdi, hba, hmf, hmpf⟩
  · intro h
    exact ⟨⟨⟨h.rowConstraints, h.rowHashes⟩, h.rowRanges⟩,
      h.memAddrsNodup, h.memClosed, h.memDisciplined, h.memBalanced,
      h.memTableFaithful, h.mapTableFaithful⟩

#assert_axioms decideSatisfied2_iff_Satisfied2

/-! ## §6 — `Decidable (Satisfied2 …)` under the oracle (the formal computability statement). -/

/-- **`Satisfied2` is a DECIDABLE predicate UNDER the supplied heap-opening oracle.** Built from
`decideSatisfied2` and the correctness iff: the formal content of "the deployed accept-set is
computable by a tiny core, modulo the one named heap-opening floor". The instance form, so the Rust
enumerator's accept/reject resolves through the verified core. -/
def instDecidableSatisfied2 (mapDec : VmRowEnv → MapOp → Bool) (hash : List ℤ → ℤ)
    (hmapDec : ∀ (env : VmRowEnv) (m : MapOp), mapDec env m = true ↔ m.holdsAt hash env)
    (d : EffectVmDescriptor2) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) :
    Decidable (Satisfied2 hash d minit mfin maddrs t) :=
  decidable_of_iff _ (decideSatisfied2_iff_Satisfied2 mapDec hash hmapDec d minit mfin maddrs t)

/-! ## §7 — Non-vacuity: the reference REJECTS as well as accepts (a constantly-true decider is
useless). On a one-row trace with NO declared content (`constraints = []`, `hashSites = []`,
`ranges = []`, no mem/map ops) the decider ACCEPTS; flipping a single declared range tooth to a
violated wire REJECTS. -/

/-- The empty v2 descriptor (a 1-PI, 1-wide thin main; no constraints/sites/ranges/tables). -/
def emptyDescriptor2 : EffectVmDescriptor2 :=
  { name := "dregg-decide-sat2-empty-v0", traceWidth := 1, piCount := 0,
    tables := [], constraints := [], hashSites := [], ranges := [] }

/-- A trivial oracle: rejects every map op (the empty descriptor has none, so it is never consulted). -/
def trivialMapDec : VmRowEnv → MapOp → Bool := fun _ _ => false

/-- A one-row witness whose memory tables are empty (no declared mem/map ops). -/
def emptyTrace : VmTrace :=
  { rows := [zeroAsg], pub := zeroAsg, tf := fun _ => [] }

/-- **Non-vacuity (accept).** The empty descriptor's denotation is satisfied by the one-row empty
witness, and `decideSatisfied2` ACCEPTS it — through the verified core. (`memLog`/`mapLog` of a
descriptor with no mem/map ops are empty, so the table-faithfulness legs read the empty tables.) -/
theorem decideSatisfied2_empty_accepts (hash : List ℤ → ℤ) :
    decideSatisfied2 trivialMapDec hash emptyDescriptor2 (fun _ => 0) (fun _ => (0, 0)) []
      emptyTrace = true := by
  -- the descriptor declares NO constraints / sites / ranges / mem-map ops, so EVERY conjunct of
  -- `decideSatisfied2` reduces to `true` on the one-row empty witness — the oracle is never consulted.
  rw [decideSatisfied2, decideRowConstraints2, decideRowHashes2, decideRowRanges2, decideMemLegs]
  have hml : memLog emptyDescriptor2 emptyTrace = [] := by
    simp only [memLog, emptyDescriptor2, memOpsOf, List.filterMap_nil]; rfl
  have hmpl : mapLog emptyDescriptor2 emptyTrace = [] := by
    simp only [mapLog, emptyDescriptor2, mapOpsOf, List.filterMap_nil]; rfl
  rw [hml, hmpl]
  simp only [emptyDescriptor2, emptyTrace, List.length_cons, List.length_nil, List.all_nil,
    List.map_nil, decideSites, Dregg2.Circuit.Argus.InterpCore.decideSitesGo, decideRanges,
    Bool.and_true]
  -- the remaining concrete Bool legs (Nodup [], MemCheck of [], the empty-table equalities) decide.
  simp [List.range, List.range.loop, decide_eq_true_eq, MemoryChecking.MemCheck,
    MemoryChecking.initSet, MemoryChecking.finalSet, MemoryChecking.readSet,
    MemoryChecking.writeSetFrom, MemoryChecking.boundarySet, MemoryChecking.Disciplined,
    MemoryChecking.DisciplinedFrom, emptyTrace]
  exact decide_eq_true trivial

/-- A one-range descriptor: a single 30-bit range tooth on column 0. -/
def oneRangeDescriptor2 : EffectVmDescriptor2 :=
  { name := "dregg-decide-sat2-onerange-v0", traceWidth := 1, piCount := 0,
    tables := [], constraints := [], hashSites := [], ranges := [⟨0, 30⟩] }

/-- A trace whose only row carries a wire OUT of `[0, 2^30)` at column 0 (so the range tooth is
VIOLATED). -/
def badRangeTrace : VmTrace :=
  { rows := [fun _ => (2 : ℤ) ^ 30], pub := zeroAsg, tf := fun _ => [] }

/-- **Non-vacuity (reject).** On the one-range descriptor, a row whose column-0 wire is `2^30`
(out of range) makes `decideSatisfied2` REJECT — the decider SEPARATES satisfying from violating
witnesses, so it is not constantly `true`. -/
theorem decideSatisfied2_badRange_rejects (hash : List ℤ → ℤ) :
    decideSatisfied2 trivialMapDec hash oneRangeDescriptor2 (fun _ => 0) (fun _ => (0, 0)) []
      badRangeTrace = false := by
  -- the `decideRowRanges2` conjunct is `false`: on row 0 the wire at column 0 is `2^30`, and
  -- `decideRanges` for the ⟨0, 30⟩ tooth demands `2^30 < 2^30` — so the whole AND is `false`.
  have hrng : decideRowRanges2 oneRangeDescriptor2 badRangeTrace = false := by
    -- the single tooth ⟨0,30⟩ on row 0 reads `loc 0 = 2^30 ∉ [0, 2^30)`, so the per-row decider is
    -- `false` and the `List.all` over the one row is `false`.
    have hloc : (envAt badRangeTrace 0).loc 0 = (2 : ℤ) ^ 30 := by
      simp [envAt, badRangeTrace, List.getD]
    have hrow : decideRanges (envAt badRangeTrace 0) oneRangeDescriptor2.ranges = false := by
      -- `decideRanges` for ⟨0,30⟩: `decide (0 ≤ 2^30) && decide (2^30 < 2^30)` = `true && false`.
      simp only [oneRangeDescriptor2, decideRanges, List.all_cons, List.all_nil, Bool.and_true, hloc]
      have h1 : decide ((0 : ℤ) ≤ (2 : ℤ) ^ 30) = true := by decide
      have h2 : decide ((2 : ℤ) ^ 30 < (2 : ℤ) ^ 30) = false := by
        rw [decide_eq_false_iff_not]; exact lt_irrefl _
      rw [h1, h2, Bool.true_and]
    rw [decideRowRanges2]
    have hlen : badRangeTrace.rows.length = 1 := by simp [badRangeTrace]
    rw [hlen, show (List.range 1) = [0] from rfl, List.all_cons, List.all_nil, Bool.and_true, hrow]
  rw [decideSatisfied2, hrng]
  simp

#assert_axioms decideSatisfied2_empty_accepts
#assert_axioms decideSatisfied2_badRange_rejects

end Dregg2.Circuit.DecideSatisfied2
