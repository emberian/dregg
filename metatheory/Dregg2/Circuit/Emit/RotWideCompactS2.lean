/-
# Dregg2.Circuit.Emit.RotWideCompactS2 — DELETE the S2 dead stratum from the WIDE members
(the rotated 1-felt Merkle–Damgård chains), by verified column compaction.

## What this module is

`docs/ARCH-REVIEW-rotated-commitment-chip.md` §1.1: in every WIDE registry member the two
rotated 1-felt commitment chains (S2 — 124 chip sites, 124 carrier/digest columns, 868 exposed
lane columns) are DEAD — `wideAppend` retired their two `STATE_COMMIT` PI pins, the 8-felt wide
chains are self-rooted in the raw limb columns, and zero constraints outside the 1-felt lookups
themselves read the S2 columns (constraint-level verified, registry-wide). They persist only
because the wide composition is conjunctive.

`compactS2` is the value-preserving deletion: drop exactly the 124 S2 chip lookups and REMOVE
their 992 columns, remapping every surviving column reference through the verified index map
(`dropIdx`). The result is what the wide member always meant.

## The soundness bridge (`compactS2_expand`)

The keystone tower (`wideAppend_binds_published`, `rotV3FrozenWide_sound_v1`, the per-member
refinement collapses) is stated over the UNCOMPACTED member `M`. `compactS2_expand` re-connects
every one of them to the deployed compact object in one move: a `Satisfied2` witness of
`compactS2 M …` EXPANDS to a `Satisfied2` witness of `M` itself — the deleted chain columns are
recomputed from the surviving limb columns (they were always a function of them; that is what
"dead" means), and the chip table is extended with exactly the genuine permutation rows the
recomputed chains absorb (`ChipTableSoundN` is preserved: the extension is genuine-by-
construction). The expanded trace agrees with the compact trace on every surviving column
(`dropIdx`-composed), so every conclusion a keystone draws about surviving columns — the face
gates, the welds, the wide 8-felt binding, the caveat chain — transfers verbatim.

Every side condition is DECIDABLE (`compactOk`), discharged per member at emit time: the emit
driver refuses to emit a compacted member whose S2 stratum is not EXACTLY the expected dead
chain shape or whose surviving constraints touch a dead column. That check is the live
falsifier of the review's "S2 is dead" verdict — if any member's S2 were load-bearing, the emit
fails closed.

## What this module does NOT touch

The BARE V3 registry (`rotation-v3-staged-registry.tsv`) keeps its 1-felt chains: its members
still publish PIs 42/43 through them and are consumed at HEAD (the SDK cap-open fallback,
`verifier/src/rotated_replay.rs`, the joint-turn mint weld). S3 (the caveat 1-felt chain,
publishing PI 45) is KEPT — it is alive. S1/host-v1 (col 88 → PI 8) is KEPT — load-bearing.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no new hypotheses — the bridge is
unconditional given the decidable shape checks.
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationWide

namespace Dregg2.Circuit.Emit.RotWideCompactS2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitV2 (Satisfied2FaithfulWide)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (rotV3SitesAt rotV3SitesAt_admitted colOnly colOnlyInput)

set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxRecDepth 8000

/-! ## §0 — column-reference collectors (decidable surface for the side conditions). -/

/-- Every column an `EmittedExpr` reads. -/
def refsE : EmittedExpr → List Nat
  | .var v => [v]
  | .const _ => []
  | .add a b => refsE a ++ refsE b
  | .mul a b => refsE a ++ refsE b

/-- Every column a `WindowExpr` reads (current OR next row). -/
def refsW : WindowExpr → List Nat
  | .loc c => [c]
  | .nxt c => [c]
  | .const _ => []
  | .add a b => refsW a ++ refsW b
  | .mul a b => refsW a ++ refsW b

/-- Every column a v1 constraint reads. A `.transition hi lo` reads through the FIXED face
bases (`sbCol`/`saCol`) — those are recorded so the side condition can demand they sit BELOW
every deleted column (the compaction is the identity there). -/
def refsC : VmConstraint → List Nat
  | .gate b => refsE b
  | .transition hi lo => [sbCol hi, saCol lo]
  | .boundary _ b => refsE b
  | .piBinding _ col _ => [col]

/-- Columns read by a `ChalExpr`. The `chal` leaf reads none — it is a verifier value, not a
column — which is the same reason it costs no constraint degree. -/
def refsChal : ChalExpr → List Nat
  | .loc c | .nxt c => [c]
  | .const _ | .chal _ => []
  | .add a b | .mul a b => refsChal a ++ refsChal b

/-- Every column a v2 constraint reads (mem/map/umem/proofBind through their SEMANTICALLY READ
expressions — the same ones `holdsAt`/`memLog`/`mapLog` evaluate, plus the full 8-felt root
lanes the wire realization recomposes). -/
def refs2 : VmConstraint2 → List Nat
  -- ⚑ A `chal` leaf reads NO column, so a challenge gate's column set is exactly its `loc`/`nxt`
  -- leaves. Inventing a column for the challenge would over-count the forced set.
  | .chalGate w => refsChal w.body
  | .base c => refsC c
  | .lookup l => l.tuple.flatMap refsE
  | .memOp m => refsE m.guard ++ refsE m.addr ++ refsE m.value ++ refsE m.prevValue
      ++ refsE m.prevSerial
  | .mapOp m => refsE m.guard ++ refsE m.key ++ refsE m.value
      ++ (List.ofFn m.root).flatMap refsE ++ (List.ofFn m.newRoot).flatMap refsE
  | .umemOp m => refsE m.guard ++ refsE m.key ++ refsE m.present ++ refsE m.value
      ++ refsE m.prevPresent ++ refsE m.prevValue ++ refsE m.prevSerial
  | .proofBind m => refsE m.guard ++ m.commit.flatMap refsE ++ m.vk.flatMap refsE
      ++ m.bound.lanes.flatMap refsE
  | .windowGate w => refsW w.body

/-- The columns a hash site reads or writes. -/
def refsSite (s : VmHashSite) : List Nat :=
  s.digestCol :: s.inputs.filterMap (fun i => match i with | .col c => some c | _ => none)

/-! ## §1 — the column remap and its application to every constraint kind. -/

/-- Rewrite every `.var` through `g`. -/
def mapVarE (g : Nat → Nat) : EmittedExpr → EmittedExpr
  | .var v => .var (g v)
  | .const k => .const k
  | .add a b => .add (mapVarE g a) (mapVarE g b)
  | .mul a b => .mul (mapVarE g a) (mapVarE g b)

/-- Rewrite a window expression's row reads through `g`. -/
def mapVarW (g : Nat → Nat) : WindowExpr → WindowExpr
  | .loc c => .loc (g c)
  | .nxt c => .nxt (g c)
  | .const k => .const k
  | .add a b => .add (mapVarW g a) (mapVarW g b)
  | .mul a b => .mul (mapVarW g a) (mapVarW g b)

/-- Rewrite a v1 constraint through `g`. `.transition` is offset-encoded (reads through the
fixed face bases), and the compaction is the identity below every deleted column, so it maps to
itself — the side condition (`refsBelowDead`) makes that exact. -/
def mapC (g : Nat → Nat) : VmConstraint → VmConstraint
  | .gate b => .gate (mapVarE g b)
  | .transition hi lo => .transition hi lo
  | .boundary r b => .boundary r (mapVarE g b)
  | .piBinding r col k => .piBinding r (g col) k

/-- Rewrite a hash site through `g` (result column and `.col` inputs; `.digest`/`.zero` are
column-free). -/
def mapSite (g : Nat → Nat) (s : VmHashSite) : VmHashSite :=
  { digestCol := g s.digestCol
  , inputs := s.inputs.map (fun i => match i with
      | .col c => .col (g c)
      | .digest k => .digest k
      | .zero => .zero)
  , arity := s.arity }

/-- Rewrite a range tooth through `g`. -/
def mapRange (g : Nat → Nat) (r : VmRange) : VmRange := { wire := g r.wire, bits := r.bits }

/-- Rewrite a memory op through `g`. -/
def mapMemF (g : Nat → Nat) (m : MemOp) : MemOp :=
  { m with
    guard := mapVarE g m.guard, addr := mapVarE g m.addr, value := mapVarE g m.value,
    prevValue := mapVarE g m.prevValue, prevSerial := mapVarE g m.prevSerial }

/-- Rewrite a map op through `g`. -/
def mapMapF (g : Nat → Nat) (m : MapOp) : MapOp :=
  { guard := mapVarE g m.guard
  , root := (fun i => mapVarE g (m.root i))
  , key := mapVarE g m.key
  , value := mapVarE g m.value
  , newRoot := (fun i => mapVarE g (m.newRoot i))
  , op := m.op }

/-- Rewrite a `ChalExpr`'s COLUMN leaves through `g`. `chal i` is untouched. -/
def mapChal (g : Nat → Nat) : ChalExpr → ChalExpr
  | .loc c => .loc (g c)
  | .nxt c => .nxt (g c)
  | .const k => .const k
  | .chal i => .chal i
  | .add a b => .add (mapChal g a) (mapChal g b)
  | .mul a b => .mul (mapChal g a) (mapChal g b)

/-- Rewrite a v2 constraint through `g`. -/
def mapC2 (g : Nat → Nat) : VmConstraint2 → VmConstraint2
  -- ⚑ The challenge gate's COLUMNS remap; its `chal` leaves do not, because a challenge index is
  -- not a column index. Remapping it would silently retarget the gate onto a different draw.
  | .chalGate w => .chalGate { w with body := mapChal g w.body }
  | .base c => .base (mapC g c)
  | .lookup l => .lookup { table := l.table, tuple := l.tuple.map (mapVarE g) }
  | .memOp m => .memOp (mapMemF g m)
  | .mapOp m => .mapOp (mapMapF g m)
  | .umemOp m => .umemOp { m with
      guard := mapVarE g m.guard, key := mapVarE g m.key, present := mapVarE g m.present,
      value := mapVarE g m.value, prevPresent := mapVarE g m.prevPresent,
      prevValue := mapVarE g m.prevValue, prevSerial := mapVarE g m.prevSerial }
  | .proofBind m => .proofBind
      { guard := mapVarE g m.guard
      , commit := m.commit.map (mapVarE g)
      , vk := m.vk.map (mapVarE g)
        -- ⚑ the seam's two declared halves ride the remap: `vkPin` is a LITERAL carried unchanged;
        -- `bound` is an expression over the row and its columns must be renamed with everything
        -- else, or a compacted descriptor would bind a different column than it says.
      , vkPin := m.vkPin
      , bound := m.bound.map (mapVarE g) }
  | .windowGate w => .windowGate { body := mapVarW g w.body, onTransition := w.onTransition }

/-! ## §2 — the S2 dead-column geometry and the index map. -/

/-- One rotated block's S2 carrier/digest columns: the 1-felt `state_commit` digest at
`base + B_STATE_COMMIT` and the chain carriers up to `base + B_SPAN - 1`. The pre-iroot limbs and
the iroot (`base + 0 .. base + B_IROOT`) are NOT here — the wide chain absorbs them; they stay.

⚑ The band literals here stay LITERAL rather than `B_STATE_COMMIT`/`B_SPAN`: every proof in §2 is
discharged by `omega`, which treats a `def` as an opaque atom and so cannot see that
`B_SPAN - B_STATE_COMMIT = 62`. The `#guard`-shaped pins below hold them to the flag day. -/
-- ⚑ RE-TYPED FOR 187, AND THE RE-TYPING IS THE REVIEW. These are deliberately literal (`omega`
-- treats a `def` as an opaque atom here), which means they do NOT follow the layout — they must be
-- moved by hand every epoch, and a missed one does not go RED, it goes WRONG: at 187 the old
-- `185 / 247 / 432 / 494 / 868` band names contract_hash's ninth lane, THE OWNER KEY'S NINTH LANE
-- and the iroot, and would delete four real carriers. The detector is
-- `EmitLayoutManifest.lean:100-101` (`s2CarrierOff == B_STATE_COMMIT`,
-- `s2CarrierSpan == bNumChain + 1`) — two genuinely independent readings, and it is what caught
-- this. 185->188 (B_STATE_COMMIT), 62->63 carriers, 247->251 (B_SPAN), 432->439, 494->502,
-- 868->882 (126*7), 992->1008.
-- ⚑ RE-TYPED FOR 196 (the iroot-widening flag day): 188->197, 63->66 carriers, 251->263,
-- 439->460, 502->526, 882->924 (132*7), 1008->1056. The two-source weld below is what checks it.
def s2CarrierCols (base : Nat) : List Nat := (List.range 66).map (base + 197 + ·)

/-- ALL columns the S2 deletion removes from a member whose rotated BEFORE block sits at `bb`
(AFTER at `bb + B_SPAN`) and whose S2 chip-lane region starts at `laneBase`: the two carrier bands
plus the contiguous `2 · (rotV3SitesAt 0).length × 7` graduated lane columns. -/
def s2DeadCols (bb laneBase : Nat) : List Nat :=
  s2CarrierCols bb ++ s2CarrierCols (bb + 263) ++ (List.range 924).map (laneBase + ·)

theorem s2DeadCols_length (bb laneBase : Nat) : (s2DeadCols bb laneBase).length = 1056 := by
  simp [s2DeadCols, s2CarrierCols]

/-- O(1) membership in the dead-column set (the list `s2DeadCols` is the SPEC; this is the
computable form the emit-time gates and the index map run on). -/
def isDeadCol (bb laneBase c : Nat) : Bool :=
  (decide (bb + 197 ≤ c) && decide (c < bb + 263))
    || (decide (bb + 460 ≤ c) && decide (c < bb + 526))
    || (decide (laneBase ≤ c) && decide (c < laneBase + 924))

theorem isDeadCol_eq_mem (bb laneBase c : Nat) :
    isDeadCol bb laneBase c = true ↔ c ∈ s2DeadCols bb laneBase := by
  unfold isDeadCol s2DeadCols s2CarrierCols
  simp only [List.mem_append, List.mem_map, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
    · exact Or.inl (Or.inl ⟨c - (bb + 197), by omega, by omega⟩)
    · exact Or.inl (Or.inr ⟨c - (bb + 263 + 197), by omega, by omega⟩)
    · exact Or.inr ⟨c - laneBase, by omega, by omega⟩
  · rintro ((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
    · exact Or.inl (Or.inl ⟨by omega, by omega⟩)
    · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
    · exact Or.inr ⟨by omega, by omega⟩

/-- How many columns of the `span`-wide cut at `lo` sit strictly below `c`. -/
def cutBelow (lo span c : Nat) : Nat := if c ≤ lo then 0 else min span (c - lo)

/-- The compaction index map: a surviving column falls by the number of deleted columns below
it. O(1); strictly monotone on survivors; the identity below the first deleted column. -/
def dropIdx (bb laneBase c : Nat) : Nat :=
  c - (cutBelow (bb + 197) 66 c + cutBelow (bb + 460) 66 c + cutBelow laneBase 924 c)

theorem dropIdx_id_of_low (bb laneBase c : Nat) (h1 : c ≤ bb + 197) (h2 : c ≤ laneBase) :
    dropIdx bb laneBase c = c := by
  unfold dropIdx cutBelow
  have h3 : c ≤ bb + 460 := by omega
  rw [if_pos h1, if_pos h3, if_pos h2]
  omega

/-- How many S2-dead columns sit strictly below `c` — the SPEC form, walked off the explicit
`s2DeadCols` list. -/
private def deadBelow (bb laneBase c : Nat) : Nat :=
  ((s2DeadCols bb laneBase).filter (fun d => decide (d < c))).length

/-! ⚑ **THE GATE THIS FILE DID NOT HAVE, AND THE DEFECT IT WOULD HAVE CAUGHT.**

§2's band offsets are deliberately LITERAL — every proof here is discharged by `omega`, which treats
a `def` as an opaque atom and so cannot see `B_SPAN - B_STATE_COMMIT`. That is a real constraint, but
it made every one of them a hand-carried number with no gate, and on 2026-08-01 (`rotatedNumPreLimbs`
184 → 187) the file was re-typed HALF WAY: `s2CarrierCols`, `s2DeadCols` and `isDeadCol` moved to
188 / 251 / 882 / 1008 while `dropIdx`, `isS2LookupL`, `s2Plan`, `keptOk` and `compactOk` stayed at
185 / 247 / 432 / 494 / 868 / 992. ONE FILE, TWO GEOMETRIES, and every `#guard` in it still passed —
the compaction would have deleted one band and remapped survivors through another.

The weld below is the two-source form that cannot be half-typed: `dropIdx`'s O(1) arithmetic against
the explicit `s2DeadCols` list, sampled across the whole width. They agree only when every cut base
and every cut span in `dropIdx` is the band `s2DeadCols` actually deletes. -/
#guard (List.range 130).all
  (fun k => decide (dropIdx 0 1200 (k * 10) == k * 10 - deadBelow 0 1200 (k * 10)))

-- ...and the bands themselves are the EMITTER's, not this file's opinion of them.
#guard (s2CarrierCols 0).head? == some Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_STATE_COMMIT
#guard (s2CarrierCols 0).length
  == Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_SPAN - Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_STATE_COMMIT
#guard (s2DeadCols 0 1200).take
    (2 * (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_SPAN - Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_STATE_COMMIT))
  == s2CarrierCols 0 ++ s2CarrierCols Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_SPAN

/-! ## §3 — the EXPECTED S2 stratum (what the member must carry for the deletion to be sound).

The graduated S2 lookups are the chip lookups of the two block chains `rotV3SitesAt bb` /
`rotV3SitesAt (bb + 247)`, the `j`-th site's 7 lane columns at `laneBase + 7·j`. The emit gate
checks the member's poseidon2 lookups whose out0 lands in the carrier bands are EXACTLY this
list — order, tuples, lanes, everything. -/

instance : DecidableEq Lookup := fun a b =>
  if h : a.table = b.table ∧ a.tuple = b.tuple then
    .isTrue (by obtain ⟨h1, h2⟩ := h; cases a; cases b; simp_all)
  else .isFalse (by intro he; cases he; exact h ⟨rfl, rfl⟩)

/-- The out0 (digest) column of a graduated chip lookup: tuple slot `1 + CHIP_RATE`. -/
def lookupOut0? (l : Lookup) : Option Nat :=
  match l.tuple.getD (1 + CHIP_RATE) (.const 0) with
  | .var c => some c
  | _ => none

/-- Is this lookup an S2 chain lookup of the member at block base `bb`? (poseidon2, out0 in one
of the two carrier bands). -/
def isS2LookupL (bb : Nat) (l : Lookup) : Bool :=
  l.table == TableId.poseidon2 &&
    match lookupOut0? l with
    | some c => (decide (bb + 197 ≤ c) && decide (c < bb + 263))
        || (decide (bb + 460 ≤ c) && decide (c < bb + 526))
    | none => false

/-- Is this constraint an S2 chain lookup? -/
def isS2 (bb : Nat) : VmConstraint2 → Bool
  | .lookup l => isS2LookupL bb l
  | _ => false

/-- The member's S2 lookups, in constraint order. -/
def s2LookupsOf (M : EffectVmDescriptor2) (bb : Nat) : List Lookup :=
  M.constraints.filterMap fun c => match c with
    | .lookup l => if isS2LookupL bb l then some l else none
    | _ => none

/-- The S2 walk plan: the 124 sites with their graduated lane bases. -/
def s2Plan (bb laneBase : Nat) : List (VmHashSite × Nat) :=
  (rotV3SitesAt bb ++ rotV3SitesAt (bb + 263)).mapIdx (fun j s => (s, laneBase + 7 * j))

/-- **Every S2 walk site asks the chip for an ADMITTED arity, at every base.** The plan's sites come
from `rotV3SitesAt`, whose input lists are literal spines — the ARITY does not depend on `bb` or
`laneBase`, so this holds for a symbolic base. Proving it HERE keeps `s2Lookups` TOTAL, rather than
conditioning the emit gate on its own later `planOk` leg (which is declared below it). -/
theorem s2Plan_admitted (bb laneBase : Nat) :
    ∀ p ∈ s2Plan bb laneBase, ChipArityAdmitted p.1.inputs.length := by
  intro p hp
  simp only [s2Plan, List.mem_mapIdx] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  have hsite : (rotV3SitesAt bb ++ rotV3SitesAt (bb + 263))[j] ∈
      (rotV3SitesAt bb ++ rotV3SitesAt (bb + 263)) := List.getElem_mem hj
  rcases List.mem_append.mp hsite with h | h <;>
    exact rotV3SitesAt_admitted _ _ h

/-- The EXPECTED graduated S2 lookups (the S2 sites are col-only, so the `sites` resolution
argument of `siteLookup` is irrelevant — `[]` emits the same tuple the full-list graduation
emitted). -/
def s2Lookups (bb laneBase : Nat) : List Lookup :=
  (s2Plan bb laneBase).attach.map
    (fun p => siteLookup [] p.1.1 p.1.2 (s2Plan_admitted bb laneBase p.1 p.2))

/-- The 8 columns one walk step overrides: the site's digest column and its 7 lane columns. -/
def overrideColsOf (s : VmHashSite) (lb : Nat) : List Nat := s.digestCol :: siteLaneCols lb

/-- The `.col` input columns of a site. -/
def inputColsOf (s : VmHashSite) : List Nat :=
  s.inputs.filterMap (fun i => match i with | .col c => some c | _ => none)

/-- The walk plan is well-formed: every step's override block is disjoint from every LATER
step's override block and internally duplicate-free; every step's inputs are col-only, fit the
chip rate, and are never overridden at this or any later step (so input values survive to the
final assignment). -/
def planOk : List (VmHashSite × Nat) → Bool
  | [] => true
  | (s, lb) :: rest =>
    let laterOv := rest.flatMap (fun p => overrideColsOf p.1 p.2)
    (overrideColsOf s lb).all (fun c => !laterOv.contains c)
      && (overrideColsOf s lb).Nodup
      && (inputColsOf s).all (fun c => !laterOv.contains c && !(overrideColsOf s lb).contains c)
      && s.inputs.all colOnlyInput
      -- ⚑ ADMITTED, not merely `≤ CHIP_RATE`: this is the compaction's own fail-closed gate, and
      -- the expanded trace's chip table has to be `ChipTableSoundN`, whose rows now carry an
      -- admitted arity. `≤ CHIP_RATE` would let the compaction bless a site the chip AIR refuses.
      && decide (ChipArityAdmitted s.inputs.length)
      && planOk rest

/-- One surviving constraint is compatible with the deletion: it reads no dead column, and if
it is a `.transition` (offset-encoded through the face bases) its columns sit BELOW every dead
column, so the remap is the identity there. -/
def keptOk (bb laneBase : Nat) (c : VmConstraint2) : Bool :=
  (refs2 c).all (fun r => !isDeadCol bb laneBase r)
    && (match c with
        | .base (.transition hi lo) =>
            decide (sbCol hi < bb + 197) && decide (saCol lo < bb + 197)
              && decide (sbCol hi ≤ laneBase) && decide (saCol lo ≤ laneBase)
        | _ => true)

/-- **The whole decidable side-condition bundle** — the emit gate AND the bridge hypothesis:
  * the member's S2 lookups are EXACTLY the expected two block chains (shape check — the live
    falsifier of the "dead stratum" verdict);
  * every surviving constraint / hash site / range tooth avoids the dead columns;
  * the walk plan is well-formed;
  * the three dead bands are pairwise disjoint (`bb + 526 ≤ laneBase` — exact width bookkeeping);
  * every override column is a dead column (the expansion touches nothing that survives). -/
def compactOk (M : EffectVmDescriptor2) (bb laneBase : Nat) : Bool :=
  s2LookupsOf M bb == s2Lookups bb laneBase
    && M.constraints.all (fun c => isS2 bb c || keptOk bb laneBase c)
    && M.hashSites.all (fun s => (refsSite s).all (fun r => !isDeadCol bb laneBase r))
    && M.ranges.all (fun r => !isDeadCol bb laneBase r.wire)
    && planOk (s2Plan bb laneBase)
    && decide (bb + 526 ≤ laneBase)
    && (s2Plan bb laneBase).all
        (fun p => (overrideColsOf p.1 p.2).all (isDeadCol bb laneBase))
    && decide (1056 ≤ M.traceWidth)

/-! ## §4 — `compactS2`: the deletion itself. -/

/-- **`compactS2 M bb laneBase`** — the S2-deleted member: the chain lookups dropped, every
surviving column reference remapped through `dropIdx`, the width down by exactly `s2DeadCols`, the main
table arity following. Name, PI count, and every published value are UNCHANGED (the retired
PI slots 42/43 stay as producer-zeroed slots — they bound nothing before and bind nothing now). -/
def compactS2 (M : EffectVmDescriptor2) (bb laneBase : Nat) : EffectVmDescriptor2 :=
  let g := dropIdx bb laneBase
  { name := M.name
  , traceWidth := M.traceWidth - 1056
  , piCount := M.piCount
  , tables := M.tables.map (fun td =>
      if td.id = TableId.main then { td with arity := td.arity - 1056 } else td)
  , constraints := (M.constraints.filter (fun c => !isS2 bb c)).map (mapC2 g)
  , hashSites := M.hashSites.map (mapSite g)
  , ranges := M.ranges.map (mapRange g) }

/-! ## §5 — evaluation transport: mapped syntax on the compact row ≡ original syntax on any
row that agrees through the map. -/

theorem evalE_map (g : Nat → Nat) (e : EmittedExpr) (a : Assignment) :
    (mapVarE g e).eval a = e.eval (fun c => a (g c)) := by
  induction e with
  | var v => rfl
  | const k => rfl
  | add x y ihx ihy => simp [mapVarE, EmittedExpr.eval, ihx, ihy]
  | mul x y ihx ihy => simp [mapVarE, EmittedExpr.eval, ihx, ihy]

theorem evalE_congr (e : EmittedExpr) (a b : Assignment) (h : ∀ r ∈ refsE e, a r = b r) :
    e.eval a = e.eval b := by
  induction e with
  | var v => exact h v (by simp [refsE])
  | const k => rfl
  | add x y ihx ihy =>
      simp only [EmittedExpr.eval]
      rw [ihx (fun r hr => h r (by simp [refsE, hr])),
          ihy (fun r hr => h r (by simp [refsE, hr]))]
  | mul x y ihx ihy =>
      simp only [EmittedExpr.eval]
      rw [ihx (fun r hr => h r (by simp [refsE, hr])),
          ihy (fun r hr => h r (by simp [refsE, hr]))]

/-- The combined form every transport step uses: the mapped expression on the compact row
evaluates to the original expression on the expanded row, given ref-wise agreement. -/
theorem evalE_map_agree (g : Nat → Nat) (e : EmittedExpr) (a aX : Assignment)
    (h : ∀ r ∈ refsE e, aX r = a (g r)) :
    (mapVarE g e).eval a = e.eval aX := by
  rw [evalE_map]
  exact (evalE_congr e aX (fun c => a (g c)) h).symm

/-- ⚑ **THE LANE-VECTOR TWIN of `evalE_map_agree`** (2026-08-05, the `ProofBind` widening). A
recursion seam reads LISTS of expressions now, and a remap must carry every lane — not the first
one with the rest silently agreeing. Stated over the whole list so the seam's transport is one
rewrite per vector instead of one per felt. -/
theorem evalE_map_agree_list (g : Nat → Nat) (es : List EmittedExpr) (a aX : Assignment)
    (h : ∀ e ∈ es, ∀ r ∈ refsE e, aX r = a (g r)) :
    (es.map (mapVarE g)).map (fun e => e.eval a) = es.map (fun e => e.eval aX) := by
  rw [List.map_map]
  exact List.map_congr_left (fun e he => evalE_map_agree g e a aX (h e he))

/-- ⚑ The challenge-expression twin of `evalW_map_agree`. It needs the extra hypothesis
`envX.chal = env.chal`: a column REMAP does not touch the verifier's drawn randomness, so the two
environments must carry the SAME challenge slice for the two evaluations to agree. Compaction
preserves it (it rewrites column indices only), which is why the hypothesis is dischargeable — but
it is a hypothesis rather than an assumption, because a transport that silently re-drew the
challenge would be transporting a different gate. -/
theorem evalChal_map_agree (g : Nat → Nat) (w : ChalExpr) (env envX : VmRowEnv)
    (hloc : ∀ r ∈ refsChal w, envX.loc r = env.loc (g r))
    (hnxt : ∀ r ∈ refsChal w, envX.nxt r = env.nxt (g r))
    (hchal : envX.chal = env.chal) :
    (mapChal g w).eval env = w.eval envX := by
  induction w with
  | loc c => exact (hloc c (by simp [refsChal])).symm
  | nxt c => exact (hnxt c (by simp [refsChal])).symm
  | const k => rfl
  | chal i => simp [mapChal, ChalExpr.eval, hchal]
  | add x y ihx ihy =>
      simp only [mapChal, ChalExpr.eval]
      rw [ihx (fun r hr => hloc r (by simp [refsChal, hr])) (fun r hr => hnxt r (by simp [refsChal, hr])),
          ihy (fun r hr => hloc r (by simp [refsChal, hr])) (fun r hr => hnxt r (by simp [refsChal, hr]))]
  | mul x y ihx ihy =>
      simp only [mapChal, ChalExpr.eval]
      rw [ihx (fun r hr => hloc r (by simp [refsChal, hr])) (fun r hr => hnxt r (by simp [refsChal, hr])),
          ihy (fun r hr => hloc r (by simp [refsChal, hr])) (fun r hr => hnxt r (by simp [refsChal, hr]))]

theorem evalW_map_agree (g : Nat → Nat) (w : WindowExpr) (env envX : VmRowEnv)
    (hloc : ∀ r ∈ refsW w, envX.loc r = env.loc (g r))
    (hnxt : ∀ r ∈ refsW w, envX.nxt r = env.nxt (g r)) :
    (mapVarW g w).eval env = w.eval envX := by
  induction w with
  | loc c => exact (hloc c (by simp [refsW])).symm
  | nxt c => exact (hnxt c (by simp [refsW])).symm
  | const k => rfl
  | add x y ihx ihy =>
      simp only [WindowExpr.eval, mapVarW]
      rw [ihx (fun r hr => hloc r (by simp [refsW, hr])) (fun r hr => hnxt r (by simp [refsW, hr])),
          ihy (fun r hr => hloc r (by simp [refsW, hr])) (fun r hr => hnxt r (by simp [refsW, hr]))]
  | mul x y ihx ihy =>
      simp only [WindowExpr.eval, mapVarW]
      rw [ihx (fun r hr => hloc r (by simp [refsW, hr])) (fun r hr => hnxt r (by simp [refsW, hr])),
          ihy (fun r hr => hloc r (by simp [refsW, hr])) (fun r hr => hnxt r (by simp [refsW, hr]))]

/-! ## §6 — the expansion: recompute the deleted chain columns from the survivors. -/

/-- Pointwise override: `c ∈ cols` reads its paired value, everything else reads `a`. -/
def overrideMany (a : Assignment) (cols : List Nat) (vals : List ℤ) : Assignment :=
  fun c => match (cols.zip vals).find? (fun p => p.1 == c) with
    | some p => p.2
    | none => a c

theorem overrideMany_not_mem (a : Assignment) (cols : List Nat) (vals : List ℤ) (c : Nat)
    (h : c ∉ cols) : overrideMany a cols vals c = a c := by
  unfold overrideMany
  have : (cols.zip vals).find? (fun p => p.1 == c) = none := by
    rw [List.find?_eq_none]
    intro p hp hbeq
    exact h (by
      have := List.of_mem_zip hp
      have hc : p.1 = c := by simpa using hbeq
      exact hc ▸ this.1)
  rw [this]

/-- With duplicate-free columns and matching lengths, the override block reads back exactly the
value list. -/
theorem overrideMany_map (a : Assignment) (cols : List Nat) (vals : List ℤ)
    (hnd : cols.Nodup) (hlen : cols.length = vals.length) :
    cols.map (overrideMany a cols vals) = vals := by
  induction cols generalizing vals a with
  | nil => cases vals with
    | nil => rfl
    | cons v vs => simp at hlen
  | cons c cs ih =>
    cases vals with
    | nil => simp at hlen
    | cons v vs =>
      simp only [List.map_cons]
      have hhead : overrideMany a (c :: cs) (v :: vs) c = v := by
        unfold overrideMany
        simp [List.zip_cons_cons, List.find?]
      have hnd' := List.nodup_cons.mp hnd
      have htail : cs.map (overrideMany a (c :: cs) (v :: vs))
          = cs.map (overrideMany a cs vs) := by
        apply List.map_congr_left
        intro x hx
        have hcx : (c == x) = false := by
          simp only [beq_eq_false_iff_ne]
          intro hceq
          exact hnd'.1 (hceq ▸ hx)
        unfold overrideMany
        rw [List.zip_cons_cons]
        simp [List.find?_cons, hcx]
      rw [hhead, htail, ih a vs hnd'.2 (by simpa using hlen)]

/-- The values one walk step absorbs: `.col` inputs read the assignment, `.zero`/`.digest`
read 0 (the S2 sites are col-only — `planOk` checks it — so the `.digest` arm never fires). -/
def insVals (a : Assignment) (s : VmHashSite) : List ℤ :=
  s.inputs.map (fun i => match i with | .col c => a c | _ => 0)

theorem insVals_congr (a b : Assignment) (s : VmHashSite)
    (h : ∀ c ∈ inputColsOf s, a c = b c) : insVals a s = insVals b s := by
  unfold insVals
  apply List.map_congr_left
  intro i hi
  cases i with
  | col c => exact h c (by
      unfold inputColsOf
      exact List.mem_filterMap.mpr ⟨.col c, hi, rfl⟩)
  | digest k => rfl
  | zero => rfl

/-- The chained walk: process the S2 sites in order, overriding each site's digest + lane
columns with the genuine permutation output of its (already-final) inputs. -/
def expandGo (permOut : List ℤ → List ℤ) : Assignment → List (VmHashSite × Nat) → Assignment
  | a, [] => a
  | a, (s, lb) :: rest =>
      expandGo permOut (overrideMany a (overrideColsOf s lb) (permOut (insVals a s))) rest

theorem expandGo_notin (permOut : List ℤ → List ℤ) (a : Assignment)
    (plan : List (VmHashSite × Nat)) (c : Nat)
    (h : ∀ p ∈ plan, c ∉ overrideColsOf p.1 p.2) :
    expandGo permOut a plan c = a c := by
  induction plan generalizing a with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨s, lb⟩ := p
    show expandGo permOut _ rest c = a c
    rw [ih _ (fun q hq => h q (List.mem_cons_of_mem _ hq)),
        overrideMany_not_mem _ _ _ _ (h (s, lb) List.mem_cons_self)]

/-- **The walk invariant, discharged**: on a well-formed plan, every site's override block in
the FINAL assignment carries exactly the genuine permutation output of its inputs — ALSO read
from the final assignment (inputs are never overridden at or after their site). -/
theorem expandGo_site (permOut : List ℤ → List ℤ)
    (hperm : ∀ ins, (permOut ins).length = CHIP_OUT_LANES)
    (a : Assignment) (plan : List (VmHashSite × Nat)) (hok : planOk plan = true) :
    ∀ p ∈ plan, (overrideColsOf p.1 p.2).map (expandGo permOut a plan)
        = permOut (insVals (expandGo permOut a plan) p.1) := by
  induction plan generalizing a with
  | nil => intro p hp; cases hp
  | cons q rest ih =>
    obtain ⟨s, lb⟩ := q
    have hok' := hok
    unfold planOk at hok'
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok'
    obtain ⟨⟨⟨⟨⟨hovLater, hovNodup⟩, hinp⟩, _hcolOnly⟩, _hfit⟩, hrest⟩ := hok'
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    · -- the head site: its block is set now and never touched again.
      set a₁ := overrideMany a (overrideColsOf s lb) (permOut (insVals a s)) with ha₁
      have hnotLater : ∀ c, c ∈ overrideColsOf s lb ∨ c ∈ inputColsOf s →
          ∀ q ∈ rest, c ∉ overrideColsOf q.1 q.2 := by
        intro c hc q hq hcq
        have hmem : c ∈ rest.flatMap (fun q => overrideColsOf q.1 q.2) :=
          List.mem_flatMap.mpr ⟨q, hq, hcq⟩
        rcases hc with hov | hin
        · have := hovLater c hov
          simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at this
          exact this hmem
        · have := (hinp c hin).1
          simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at this
          exact this hmem
      have hfinal_ov : (overrideColsOf s lb).map (expandGo permOut a₁ rest)
          = (overrideColsOf s lb).map a₁ := by
        apply List.map_congr_left
        intro c hc
        exact expandGo_notin permOut a₁ rest c (hnotLater c (Or.inl hc))
      have hset : (overrideColsOf s lb).map a₁ = permOut (insVals a s) := by
        rw [ha₁]
        apply overrideMany_map a _ _ hovNodup
        rw [hperm]
        simp [overrideColsOf, siteLaneCols, CHIP_OUT_LANES]
      have hins : insVals (expandGo permOut a₁ rest) s = insVals a s := by
        apply insVals_congr
        intro c hc
        rw [expandGo_notin permOut a₁ rest c (hnotLater c (Or.inr hc))]
        have hcOwn := (hinp c hc).2
        simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hcOwn
        rw [ha₁, overrideMany_not_mem _ _ _ _ hcOwn]
      show (overrideColsOf s lb).map (expandGo permOut a₁ rest)
          = permOut (insVals (expandGo permOut a₁ rest) s)
      rw [hfinal_ov, hset, hins]
    · exact ih _ hrest p hp'

/-- The expanded OLD-geometry row of a compact row: survivors read through the index map `g`,
the dead chain columns are recomputed by the walk. -/
def expandRow (permOut : List ℤ → List ℤ) (g : Nat → Nat) (plan : List (VmHashSite × Nat))
    (a : Assignment) : Assignment :=
  expandGo permOut (fun c => a (g c)) plan

/-- On any column outside the plan's override blocks (in particular any surviving column), the
expanded row reads the compact row through the index map. -/
theorem expandRow_agree (permOut : List ℤ → List ℤ) (g : Nat → Nat)
    (plan : List (VmHashSite × Nat)) (a : Assignment) (c : Nat)
    (h : ∀ p ∈ plan, c ∉ overrideColsOf p.1 p.2) :
    expandRow permOut g plan a c = a (g c) :=
  expandGo_notin permOut _ plan c h

/-- The expanded trace: rows expanded, PIs untouched, and the chip table EXTENDED with exactly
the genuine permutation rows the recomputed chains absorb (every other table untouched). -/
def expandTrace (permOut : List ℤ → List ℤ) (bb laneBase : Nat) (t : VmTrace) : VmTrace :=
  let plan := s2Plan bb laneBase
  let rows := t.rows.map (expandRow permOut (dropIdx bb laneBase) plan)
  { rows := rows
  , pub := t.pub
  -- ⚑ The expansion rewrites COLUMNS and grows the chip table; the verifier's drawn randomness is
  -- CARRIED, never re-derived. Defaulting it here would have made `holdsAt_transport`'s `hchal`
  -- true only for challenge-free traces while looking general.
  , chal := t.chal
  , tf := fun tid => if tid = TableId.poseidon2
      then t.tf TableId.poseidon2
        ++ rows.flatMap (fun aX => plan.map (fun p => chipRowN permOut (insVals aX p.1)))
      else t.tf tid }

/-- `planOk` pins every site's input tuple inside the chip rate. -/
theorem planOk_admitted (plan : List (VmHashSite × Nat)) (hok : planOk plan = true) :
    ∀ p ∈ plan, ChipArityAdmitted p.1.inputs.length := by
  induction plan with
  | nil => intro p hp; cases hp
  | cons q rest ih =>
    intro p hp
    unfold planOk at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact hok.1.2
    · exact ih hok.2 p hp'

/-- The chip-table extension is GENUINE: `ChipTableSoundN` survives (every appended row is a
`chipRowN permOut` of rate-fitting inputs, by construction). -/
theorem expandTrace_chipSoundN (permOut : List ℤ → List ℤ) (bb laneBase : Nat) (t : VmTrace)
    (hplan : planOk (s2Plan bb laneBase) = true)
    (hsound : ChipTableSoundN permOut (t.tf TableId.poseidon2)) :
    ChipTableSoundN permOut ((expandTrace permOut bb laneBase t).tf TableId.poseidon2) := by
  intro r hr
  simp only [expandTrace, if_pos rfl] at hr
  rcases List.mem_append.mp hr with hold | hnew
  · exact hsound r hold
  · obtain ⟨aX, _, hrow⟩ := List.mem_flatMap.mp hnew
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hrow
    refine ⟨insVals aX p.1, ?_, rfl⟩
    have := planOk_admitted _ hplan p hp
    simpa [insVals] using this

/-! ## §7a — per-kind transport: a mapped constraint holding on the compact row IS the original
constraint holding on the expanded row. -/

/-- Table access used by the transport: every table of the compact trace embeds into the
expanded trace's (the chip table is extended on the right; every other table is untouched). -/
theorem expandTrace_table_mono (permOut : List ℤ → List ℤ) (bb laneBase : Nat) (t : VmTrace) :
    ∀ tid : TableId, ∀ row ∈ t.tf tid, row ∈ (expandTrace permOut bb laneBase t).tf tid := by
  intro tid row hrow
  by_cases h : tid = TableId.poseidon2
  · subst h
    simp only [expandTrace, if_pos rfl]
    exact List.mem_append_left _ hrow
  · simpa [expandTrace, if_neg h] using hrow

/-- **The kept-constraint transport.** -/
theorem holdsAt_transport (hash : List ℤ → ℤ) (g : Nat → Nat)
    (tfC tfX : TraceFamily) (E EX : VmRowEnv) (isF isL : Bool) (c : VmConstraint2)
    (hloc : ∀ r ∈ refs2 c, EX.loc r = E.loc (g r))
    (hnxt : ∀ r ∈ refs2 c, EX.nxt r = E.nxt (g r))
    (hpub : EX.pub = E.pub)
    -- ⚑ A column remap does not re-draw the verifier's randomness; the challenge slice is carried,
    -- not rebuilt. Named as a hypothesis so a transport that DID change it cannot be proved here.
    (hchal : EX.chal = E.chal)
    (htrans : ∀ hi lo, c = .base (.transition hi lo) →
        g (sbCol hi) = sbCol hi ∧ g (saCol lo) = saCol lo)
    (htbl : ∀ tid : TableId, ∀ row ∈ tfC tid, row ∈ tfX tid)
    (h : (mapC2 g c).holdsAt hash tfC E isF isL) :
    c.holdsAt hash tfX EX isF isL := by
  cases c with
  | base b =>
    cases b with
    | gate body =>
      cases isL with
      | true => trivial
      | false =>
        have heq : (mapVarE g body).eval E.loc = body.eval EX.loc :=
          evalE_map_agree g body E.loc EX.loc (fun r hr => hloc r (by simpa [refs2, refsC] using hr))
        simpa only [VmConstraint2.holdsAt, VmConstraint.holdsVm, mapC2, mapC, heq] using h
    | transition hi lo =>
      cases isL with
      | true => trivial
      | false =>
        obtain ⟨h1, h2⟩ := htrans hi lo rfl
        have hn : EX.nxt (sbCol hi) = E.nxt (sbCol hi) := by
          rw [hnxt (sbCol hi) (by simp [refs2, refsC]), h1]
        have hl : EX.loc (saCol lo) = E.loc (saCol lo) := by
          rw [hloc (saCol lo) (by simp [refs2, refsC]), h2]
        simpa only [VmConstraint2.holdsAt, VmConstraint.holdsVm, mapC2, mapC, hn, hl] using h
    | boundary r body =>
      have heq : (mapVarE g body).eval E.loc = body.eval EX.loc :=
        evalE_map_agree g body E.loc EX.loc (fun r' hr => hloc r' (by simpa [refs2, refsC] using hr))
      cases r with
      | first => simpa only [VmConstraint2.holdsAt, VmConstraint.holdsVm, mapC2, mapC, heq] using h
      | last => simpa only [VmConstraint2.holdsAt, VmConstraint.holdsVm, mapC2, mapC, heq] using h
    | piBinding r col k =>
      have heq : EX.loc col = E.loc (g col) := hloc col (by simp [refs2, refsC])
      cases r with
      | first =>
        simpa only [VmConstraint2.holdsAt, VmConstraint.holdsVm, mapC2, mapC, heq, hpub] using h
      | last =>
        simpa only [VmConstraint2.holdsAt, VmConstraint.holdsVm, mapC2, mapC, heq, hpub] using h
  | lookup l =>
    show l.tuple.map (·.eval EX.loc) ∈ tfX l.table
    have heq : (l.tuple.map (mapVarE g)).map (·.eval E.loc) = l.tuple.map (·.eval EX.loc) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro e he
      exact evalE_map_agree g e E.loc EX.loc
        (fun r hr => hloc r (by
          simp only [refs2]
          exact List.mem_flatMap.mpr ⟨e, he, hr⟩))
    have h' : (l.tuple.map (mapVarE g)).map (·.eval E.loc) ∈ tfC l.table := h
    rw [heq] at h'
    exact htbl l.table _ h'
  | memOp m => trivial
  | umemOp m => trivial
  | proofBind m =>
    -- ⚑ NO LONGER `trivial`, and since 2026-08-05 the seam reads LANE VECTORS: every lane
    -- transports through `evalE_map_agree_list`, exactly like a gate body; `vkPin` is a literal
    -- vector and needs no transport.
    have hg : (mapVarE g m.guard).eval E.loc = m.guard.eval EX.loc :=
      evalE_map_agree g m.guard E.loc EX.loc
        (fun r hr => hloc r (by simp only [refs2, List.mem_append]; tauto))
    have hv : (m.vk.map (mapVarE g)).map (fun e => e.eval E.loc)
        = m.vk.map (fun e => e.eval EX.loc) :=
      evalE_map_agree_list g m.vk E.loc EX.loc
        (fun e he r hr => hloc r (by
          simp only [refs2, List.mem_append]
          exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨e, he, hr⟩))))
    have hc : (m.commit.map (mapVarE g)).map (fun e => e.eval E.loc)
        = m.commit.map (fun e => e.eval EX.loc) :=
      evalE_map_agree_list g m.commit E.loc EX.loc
        (fun e he r hr => hloc r (by
          simp only [refs2, List.mem_append]
          exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨e, he, hr⟩)))))
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨by rwa [hg] at h1, ?_, ?_⟩
    · cases hvp : m.vkPin with
      | none => show True; trivial
      | some vs =>
        simp only [mapC2, hvp] at h2
        show zeroLanes (m.guard.eval EX.loc) (m.vk.map (fun e => e.eval EX.loc)) vs
        rw [← hg, ← hv]; exact h2
    · cases hbd : m.bound with
      | port _ => show True; trivial
      | bound bs =>
        have hb : (bs.map (mapVarE g)).map (fun e => e.eval E.loc)
            = bs.map (fun e => e.eval EX.loc) :=
          evalE_map_agree_list g bs E.loc EX.loc
            (fun e he r hr => hloc r (by
              simp only [refs2, hbd, CommitBindingOf.lanes, List.mem_append]
              exact Or.inr (List.mem_flatMap.mpr ⟨e, he, hr⟩)))
        simp only [mapC2, hbd, Option.map_some] at h3
        show zeroLanes (m.guard.eval EX.loc) (m.commit.map (fun e => e.eval EX.loc))
          (bs.map (fun e => e.eval EX.loc))
        rw [← hg, ← hc, ← hb]; exact h3
  | mapOp m =>
    intro hg
    have hmem0 : ∀ e ∈ [m.guard, m.key, m.value, m.root 0, m.newRoot 0],
        ∀ r ∈ refsE e, EX.loc r = E.loc (g r) := by
      intro e he r hr
      apply hloc
      simp only [refs2, List.mem_append]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl (Or.inl (Or.inl hr)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr hr)))
      · exact Or.inl (Or.inl (Or.inr hr))
      · exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨m.root 0, by
          exact List.mem_ofFn.mpr ⟨0, rfl⟩, hr⟩))
      · exact Or.inr (List.mem_flatMap.mpr ⟨m.newRoot 0, by
          exact List.mem_ofFn.mpr ⟨0, rfl⟩, hr⟩)
    have hgd : (mapVarE g m.guard).eval E.loc = 1 := by
      rw [evalE_map_agree g m.guard E.loc EX.loc (hmem0 m.guard (by simp))]
      exact hg
    have h' := h hgd
    have hr0 : (mapVarE g (m.root 0)).eval E.loc = (m.root 0).eval EX.loc :=
      evalE_map_agree g _ _ _ (hmem0 (m.root 0) (by simp))
    have hk0 : (mapVarE g m.key).eval E.loc = m.key.eval EX.loc :=
      evalE_map_agree g _ _ _ (hmem0 m.key (by simp))
    have hv0 : (mapVarE g m.value).eval E.loc = m.value.eval EX.loc :=
      evalE_map_agree g _ _ _ (hmem0 m.value (by simp))
    have hn0 : (mapVarE g (m.newRoot 0)).eval E.loc = (m.newRoot 0).eval EX.loc :=
      evalE_map_agree g _ _ _ (hmem0 (m.newRoot 0) (by simp))
    cases hop : m.op <;>
      simp only [MapOp.holdsAt, mapC2, mapMapF, hop] at h' ⊢ <;>
      · simp only [hr0, hk0, hv0, hn0] at h'
        exact h'
  | windowGate w =>
    have heq : (mapVarW g w.body).eval E = w.body.eval EX :=
      evalW_map_agree g w.body E EX
        (fun r hr => hloc r (by simpa [refs2] using hr))
        (fun r hr => hnxt r (by simpa [refs2] using hr))
    cases how : w.onTransition <;>
      simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt, mapC2, how] at h ⊢ <;>
      rwa [heq] at h
  | chalGate w =>
    have heq : (mapChal g w.body).eval E = w.body.eval EX :=
      evalChal_map_agree g w.body E EX
        (fun r hr => hloc r (by simpa [refs2] using hr))
        (fun r hr => hnxt r (by simpa [refs2] using hr))
        hchal
    cases how : w.onTransition <;>
      simp only [VmConstraint2.holdsAt, ChalConstraint.holdsAt, mapC2, how] at h ⊢ <;>
      rwa [heq] at h

/-- Hash-site transport: the mapped site list holding on the compact row is the original list
holding on the expanded row. -/
theorem siteHoldsAll_transport (hash : List ℤ → ℤ) (E EX : VmRowEnv) (g : Nat → Nat)
    (sites : List VmHashSite)
    (hagree : ∀ s ∈ sites, ∀ r ∈ refsSite s, EX.loc r = E.loc (g r)) :
    siteHoldsAll hash E (sites.map (mapSite g)) → siteHoldsAll hash EX sites := by
  suffices hgo : ∀ acc, siteHoldsAll.go hash E acc (sites.map (mapSite g))
      → siteHoldsAll.go hash EX acc sites from hgo []
  induction sites with
  | nil => intro acc h; trivial
  | cons s ss ih =>
    intro acc h
    obtain ⟨hd, hrest⟩ := h
    have hres : (mapSite g s).resolvedInputs E acc = s.resolvedInputs EX acc := by
      unfold VmHashSite.resolvedInputs mapSite
      simp only [List.map_map]
      apply List.map_congr_left
      intro i hi
      cases i with
      | col c =>
        simp only [Function.comp_apply, HashInput.resolve]
        exact (hagree s List.mem_cons_self c (by
          unfold refsSite
          exact List.mem_cons_of_mem _ (List.mem_filterMap.mpr ⟨.col c, hi, rfl⟩))).symm
      | digest k => rfl
      | zero => rfl
    have hdig : EX.loc s.digestCol = E.loc (g s.digestCol) :=
      hagree s List.mem_cons_self s.digestCol (by unfold refsSite; exact List.mem_cons_self)
    refine ⟨by rw [hdig]; rw [← hres]; exact hd, ?_⟩
    rw [← hres]
    exact ih (fun s' hs' => hagree s' (List.mem_cons_of_mem _ hs')) _ hrest

/-! ## §7b — the global (mem/map-log) legs, and the MASTER BRIDGE. -/

theorem memOpsOf_compactS2 (M : EffectVmDescriptor2) (bb laneBase : Nat) :
    memOpsOf (compactS2 M bb laneBase)
      = (memOpsOf M).map (mapMemF (dropIdx bb laneBase)) := by
  show ((M.constraints.filter (fun c => !isS2 bb c)).map
      (mapC2 (dropIdx bb laneBase))).filterMap _ = _
  unfold memOpsOf
  induction M.constraints with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | lookup l =>
      by_cases hl : isS2LookupL bb l
      · simpa [isS2, hl] using ih
      · simpa [isS2, hl, mapC2] using ih
    | base b => simpa [isS2, mapC2] using ih
    | memOp m => simpa [isS2, mapC2] using ih
    | mapOp m => simpa [isS2, mapC2] using ih
    | umemOp m => simpa [isS2, mapC2] using ih
    | proofBind m => simpa [isS2, mapC2] using ih
    | windowGate w => simpa [isS2, mapC2] using ih
    | chalGate w => simpa [isS2, mapC2] using ih

theorem mapOpsOf_compactS2 (M : EffectVmDescriptor2) (bb laneBase : Nat) :
    mapOpsOf (compactS2 M bb laneBase)
      = (mapOpsOf M).map (mapMapF (dropIdx bb laneBase)) := by
  show ((M.constraints.filter (fun c => !isS2 bb c)).map
      (mapC2 (dropIdx bb laneBase))).filterMap _ = _
  unfold mapOpsOf
  induction M.constraints with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | lookup l =>
      by_cases hl : isS2LookupL bb l
      · simpa [isS2, hl] using ih
      · simpa [isS2, hl, mapC2] using ih
    | base b => simpa [isS2, mapC2] using ih
    | memOp m => simpa [isS2, mapC2] using ih
    | mapOp m => simpa [isS2, mapC2] using ih
    | umemOp m => simpa [isS2, mapC2] using ih
    | proofBind m => simpa [isS2, mapC2] using ih
    | windowGate w => simpa [isS2, mapC2] using ih
    | chalGate w => simpa [isS2, mapC2] using ih

/-- Per-row, per-op transport of the instrumented memory row. -/
theorem opAt?_transport (g : Nat → Nat) (m : MemOp) (a aX : Assignment)
    (hag : ∀ r ∈ refs2 (.memOp m), aX r = a (g r)) :
    MemOp.opAt? aX m = MemOp.opAt? a (mapMemF g m) := by
  have hfield : ∀ e ∈ [m.guard, m.addr, m.value, m.prevValue, m.prevSerial],
      (mapVarE g e).eval a = e.eval aX := by
    intro e he
    apply evalE_map_agree g e a aX
    intro r hr
    apply hag
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    simp only [refs2, List.mem_append]
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl (Or.inl (Or.inl hr)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr hr)))
    · exact Or.inl (Or.inl (Or.inr hr))
    · exact Or.inl (Or.inr hr)
    · exact Or.inr hr
  unfold MemOp.opAt? mapMemF
  simp only [hfield m.guard (by simp), hfield m.addr (by simp), hfield m.value (by simp),
    hfield m.prevValue (by simp), hfield m.prevSerial (by simp)]

/-- Per-row, per-op transport of the map-ops table row. -/
theorem mapRowAt_transport (g : Nat → Nat) (m : MapOp) (a aX : Assignment)
    (hag : ∀ r ∈ refs2 (.mapOp m), aX r = a (g r)) :
    (if m.guard.eval aX = 1 then some (m.rowAt aX) else none)
      = (if (mapMapF g m).guard.eval a = 1 then some ((mapMapF g m).rowAt a) else none) := by
  have hfield : ∀ e ∈ [m.guard, m.key, m.value, m.root 0, m.newRoot 0],
      (mapVarE g e).eval a = e.eval aX := by
    intro e he
    apply evalE_map_agree g e a aX
    intro r hr
    apply hag
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    simp only [refs2, List.mem_append]
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl (Or.inl (Or.inl hr)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr hr)))
    · exact Or.inl (Or.inl (Or.inr hr))
    · exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨m.root 0, List.mem_ofFn.mpr ⟨0, rfl⟩, hr⟩))
    · exact Or.inr (List.mem_flatMap.mpr ⟨m.newRoot 0, List.mem_ofFn.mpr ⟨0, rfl⟩, hr⟩)
  unfold MapOp.rowAt mapMapF
  simp only [hfield m.guard (by simp), hfield m.key (by simp), hfield m.value (by simp),
    hfield (m.root 0) (by simp), hfield (m.newRoot 0) (by simp)]

/-- `planOk` pins every site col-only. -/
theorem planOk_colOnly (plan : List (VmHashSite × Nat)) (hok : planOk plan = true) :
    ∀ p ∈ plan, p.1.inputs.all colOnlyInput = true := by
  induction plan with
  | nil => intro p hp; cases hp
  | cons q rest ih =>
    intro p hp
    unfold planOk at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact hok.1.1.2
    · exact ih hok.2 p hp'

/-- Col-only inputs evaluate through `toExpr []` exactly as `insVals` reads them. -/
theorem inputsEval_colOnly (aX : Assignment) (s : VmHashSite)
    (hcol : s.inputs.all colOnlyInput = true) :
    (s.inputs.map (HashInput.toExpr [])).map (·.eval aX) = insVals aX s := by
  unfold insVals
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  cases i with
  | col c => rfl
  | zero => rfl
  | digest k =>
    have := List.all_eq_true.mp hcol _ hi
    simp [colOnlyInput] at this

/-- The S2 lookup's tuple, evaluated on the expanded row, IS the genuine wide chip row of its
(recomputed) inputs. -/
theorem s2Lookup_tuple_eval (permOut : List ℤ → List ℤ) (p : VmHashSite × Nat)
    {aX : Assignment}
    (hAdm : ChipArityAdmitted p.1.inputs.length)
    (hcol : p.1.inputs.all colOnlyInput = true)
    (hov : (overrideColsOf p.1 p.2).map aX = permOut (insVals aX p.1)) :
    (siteLookup [] p.1 p.2 hAdm).tuple.map (·.eval aX) = chipRowN permOut (insVals aX p.1) := by
  show (chipLookupTuple (p.1.inputs.map (HashInput.toExpr [])) p.1.digestCol
      (siteLaneCols p.2) (by simpa [List.length_map] using hAdm)).map (·.eval aX) = _
  unfold chipLookupTuple chipRowN
  simp only [List.map_append, List.map_cons, map_eval_padToE, EmittedExpr.eval]
  rw [inputsEval_colOnly aX p.1 hcol]
  have hlanes : ((siteLaneCols p.2).map EmittedExpr.var).map (fun e => e.eval aX)
      = (siteLaneCols p.2).map aX := by
    rw [List.map_map]; rfl
  rw [hlanes]
  have hov' : aX p.1.digestCol :: (siteLaneCols p.2).map aX = permOut (insVals aX p.1) := by
    simpa [overrideColsOf] using hov
  rw [hov']
  simp [insVals]

/-- Generic per-row mem-op list transport. -/
theorem filterMap_opAt?_map (g : Nat → Nat) (a aX : Assignment) (ops : List MemOp)
    (hag : ∀ m ∈ ops, ∀ r ∈ refs2 (.memOp m), aX r = a (g r)) :
    ops.filterMap (MemOp.opAt? aX) = (ops.map (mapMemF g)).filterMap (MemOp.opAt? a) := by
  induction ops with
  | nil => rfl
  | cons m ms ih =>
    rw [List.map_cons, List.filterMap_cons, List.filterMap_cons,
        opAt?_transport g m a aX (hag m List.mem_cons_self),
        ih (fun m' hm' => hag m' (List.mem_cons_of_mem _ hm'))]

/-- Generic per-row map-op list transport. -/
theorem filterMap_rowAt_map (g : Nat → Nat) (a aX : Assignment) (ops : List MapOp)
    (hag : ∀ m ∈ ops, ∀ r ∈ refs2 (.mapOp m), aX r = a (g r)) :
    ops.filterMap (fun m => if m.guard.eval aX = 1 then some (m.rowAt aX) else none)
      = (ops.map (mapMapF g)).filterMap
          (fun m => if m.guard.eval a = 1 then some (m.rowAt a) else none) := by
  induction ops with
  | nil => rfl
  | cons m ms ih =>
    rw [List.map_cons, List.filterMap_cons, List.filterMap_cons,
        mapRowAt_transport g m a aX (hag m List.mem_cons_self),
        ih (fun m' hm' => hag m' (List.mem_cons_of_mem _ hm'))]

/-- Generic rows-level flatMap transport. -/
theorem flatMap_map_rows {α : Type} (rows : List Assignment) (f : Assignment → Assignment)
    (F : Assignment → List α) (G : Assignment → List α)
    (h : ∀ a, F (f a) = G a) :
    (rows.map f).flatMap F = rows.flatMap G := by
  induction rows with
  | nil => rfl
  | cons a rest ih => rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, h a, ih]

/-- The memory log of the ORIGINAL member over the expanded trace is the compact member's log
over the compact trace (the mem ops read only surviving columns). -/
theorem memLog_expand (permOut : List ℤ → List ℤ) (M : EffectVmDescriptor2)
    (bb laneBase : Nat) (t : VmTrace)
    (hsub : ∀ p ∈ s2Plan bb laneBase, ∀ x ∈ overrideColsOf p.1 p.2, x ∈ s2DeadCols bb laneBase)
    (hops : ∀ m ∈ memOpsOf M, ∀ r ∈ refs2 (.memOp m), r ∉ s2DeadCols bb laneBase) :
    memLog M (expandTrace permOut bb laneBase t) = memLog (compactS2 M bb laneBase) t := by
  unfold memLog
  rw [memOpsOf_compactS2]
  have hrows : (expandTrace permOut bb laneBase t).rows
      = t.rows.map (expandRow permOut (dropIdx bb laneBase) (s2Plan bb laneBase)) := rfl
  rw [hrows]
  apply flatMap_map_rows
  intro a
  apply filterMap_opAt?_map
  intro m hm r hr
  exact expandRow_agree permOut _ _ a r
    (fun p hp hcp => hops m hm r hr (hsub p hp r hcp))

/-- The map-ops log, same shape. -/
theorem mapLog_expand (permOut : List ℤ → List ℤ) (M : EffectVmDescriptor2)
    (bb laneBase : Nat) (t : VmTrace)
    (hsub : ∀ p ∈ s2Plan bb laneBase, ∀ x ∈ overrideColsOf p.1 p.2, x ∈ s2DeadCols bb laneBase)
    (hops : ∀ m ∈ mapOpsOf M, ∀ r ∈ refs2 (.mapOp m), r ∉ s2DeadCols bb laneBase) :
    mapLog M (expandTrace permOut bb laneBase t) = mapLog (compactS2 M bb laneBase) t := by
  unfold mapLog
  rw [mapOpsOf_compactS2]
  have hrows : (expandTrace permOut bb laneBase t).rows
      = t.rows.map (expandRow permOut (dropIdx bb laneBase) (s2Plan bb laneBase)) := rfl
  rw [hrows]
  apply flatMap_map_rows
  intro a
  apply filterMap_rowAt_map
  intro m hm r hr
  exact expandRow_agree permOut _ _ a r
    (fun p hp hcp => hops m hm r hr (hsub p hp r hcp))

/-- Row-agreement, at the trace level, on every surviving column. -/
theorem expandTrace_getD_agree (permOut : List ℤ → List ℤ) (bb laneBase : Nat) (t : VmTrace)
    (hsub : ∀ p ∈ s2Plan bb laneBase, ∀ x ∈ overrideColsOf p.1 p.2, x ∈ s2DeadCols bb laneBase)
    (i : Nat) (c : Nat) (hc : c ∉ s2DeadCols bb laneBase) :
    (expandTrace permOut bb laneBase t).rows.getD i zeroAsg c
      = t.rows.getD i zeroAsg (dropIdx bb laneBase c) := by
  show (t.rows.map (expandRow permOut (dropIdx bb laneBase) (s2Plan bb laneBase))).getD
      i zeroAsg c = _
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : t.rows[i]? with
  | none => rfl
  | some a =>
    simp only [Option.map_some, Option.getD_some]
    exact expandRow_agree permOut _ _ a c (fun p hp hcp => hc (hsub p hp c hcp))

/-- **THE MASTER BRIDGE (`compactS2_expand`).** A `Satisfied2` witness of the compacted member
expands to a `Satisfied2` witness of the ORIGINAL member: the deleted chain columns are
recomputed from the surviving limbs, the chip table is extended with exactly the genuine
permutation rows those chains absorb, and every surviving column agrees through the index map.
Every keystone stated over `M` therefore speaks about the deployed compact object, through this
expansion. -/
theorem compactS2_expand (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (hperm : ∀ ins, (permOut ins).length = CHIP_OUT_LANES)
    (M : EffectVmDescriptor2) (bb laneBase : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hok : compactOk M bb laneBase = true)
    (hsat : Satisfied2 hash (compactS2 M bb laneBase) minit mfin maddrs t) :
    Satisfied2 hash M minit mfin maddrs (expandTrace permOut bb laneBase t) := by
  -- unpack the decidable side-condition bundle
  unfold compactOk at hok
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    Bool.or_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hshape, hkeptAll⟩, hsitesOk⟩, hrangesOk⟩, hplan⟩, hdisj⟩, hsubAll⟩, hwidth⟩ := hok
  set dead := s2DeadCols bb laneBase with hdead
  set g := dropIdx bb laneBase with hg
  set plan := s2Plan bb laneBase with hplanDef
  set tX := expandTrace permOut bb laneBase t with htX
  have hDeadOf : ∀ r, isDeadCol bb laneBase r = true → r ∈ dead :=
    fun r hr => (isDeadCol_eq_mem bb laneBase r).mp hr
  have hNotDeadOf : ∀ r, (!isDeadCol bb laneBase r) = true → r ∉ dead := by
    intro r hr hmem
    rw [Bool.not_eq_true'] at hr
    exact absurd ((isDeadCol_eq_mem bb laneBase r).mpr hmem) (by simp [hr])
  have hsub : ∀ p ∈ plan, ∀ x ∈ overrideColsOf p.1 p.2, x ∈ dead := by
    intro p hp x hx
    exact hDeadOf x (hsubAll p hp x hx)
  have hlen : tX.rows.length = t.rows.length := by
    simp [htX, expandTrace]
  have hlocAg : ∀ i, ∀ c, c ∉ dead → (envAt tX i).loc c = (envAt t i).loc (g c) :=
    fun i c hc => expandTrace_getD_agree permOut bb laneBase t hsub i c hc
  have hnxtAg : ∀ i, ∀ c, c ∉ dead → (envAt tX i).nxt c = (envAt t i).nxt (g c) :=
    fun i c hc => expandTrace_getD_agree permOut bb laneBase t hsub (i + 1) c hc
  have hpubAg : ∀ i, (envAt tX i).pub = (envAt t i).pub := fun _ => rfl
  -- ⚑ The expansion rewrites COLUMNS; it carries the challenge slice unchanged, which is what
  -- `holdsAt_transport`'s `hchal` asks for.
  have hchalAg : ∀ i, (envAt tX i).chal = (envAt t i).chal := fun _ => rfl
  have hnotdead : ∀ (c : VmConstraint2), keptOk bb laneBase c = true →
      ∀ r ∈ refs2 c, r ∉ dead := by
    intro c hk r hr
    unfold keptOk at hk
    simp only [Bool.and_eq_true, List.all_eq_true] at hk
    exact hNotDeadOf r (hk.1 r hr)
  -- kept-constraint membership in the compact object
  have hkeptMem : ∀ c ∈ M.constraints, isS2 bb c = false →
      mapC2 g c ∈ (compactS2 M bb laneBase).constraints := by
    intro c hc hs2
    show mapC2 g c ∈ (M.constraints.filter (fun c => !isS2 bb c)).map (mapC2 g)
    exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hc, by simp [hs2]⟩)
  -- the mem/map-op ref discipline, from the kept bundle
  have hmemRefs : ∀ m ∈ memOpsOf M, ∀ r ∈ refs2 (.memOp m), r ∉ dead := by
    intro m hm r hr
    obtain ⟨c, hcmem, hproj⟩ := List.mem_filterMap.mp hm
    cases c with
    | memOp m' =>
      have hme : m' = m := by simpa using hproj
      subst hme
      rcases hkeptAll _ hcmem with ht | hk
      · simp [isS2] at ht
      · exact hnotdead _ hk r hr
    | base b => simp at hproj
    | lookup l => simp at hproj
    | mapOp m' => simp at hproj
    | umemOp m' => simp at hproj
    | proofBind m' => simp at hproj
    | windowGate w => simp at hproj
    | chalGate w => simp at hproj
  have hmapRefs : ∀ m ∈ mapOpsOf M, ∀ r ∈ refs2 (.mapOp m), r ∉ dead := by
    intro m hm r hr
    obtain ⟨c, hcmem, hproj⟩ := List.mem_filterMap.mp hm
    cases c with
    | mapOp m' =>
      have hme : m' = m := by simpa using hproj
      subst hme
      rcases hkeptAll _ hcmem with ht | hk
      · simp [isS2] at ht
      · exact hnotdead _ hk r hr
    | base b => simp at hproj
    | lookup l => simp at hproj
    | memOp m' => simp at hproj
    | umemOp m' => simp at hproj
    | proofBind m' => simp at hproj
    | windowGate w => simp at hproj
    | chalGate w => simp at hproj
  have hml : memLog M tX = memLog (compactS2 M bb laneBase) t :=
    memLog_expand permOut M bb laneBase t hsub hmemRefs
  have hmpl : mapLog M tX = mapLog (compactS2 M bb laneBase) t :=
    mapLog_expand permOut M bb laneBase t hsub hmapRefs
  have htfmem : tX.tf TableId.memory = t.tf TableId.memory := by
    simp [htX, expandTrace]
  have htfmap : tX.tf TableId.mapOps = t.tf TableId.mapOps := by
    simp [htX, expandTrace]
  refine ⟨?_, ?_, ?_, hsat.memAddrsNodup, ?_, ?_, ?_, ?_, ?_⟩
  · -- rowConstraints
    intro i hi c hc
    rw [hlen] at hi
    rw [hlen]
    by_cases hs2 : isS2 bb c = true
    · -- the S2 chain lookups: recomputed columns + the extended chip table
      cases c with
      | lookup l =>
        have hl : isS2LookupL bb l = true := by simpa [isS2] using hs2
        have hmemS2 : l ∈ s2LookupsOf M bb := by
          unfold s2LookupsOf
          exact List.mem_filterMap.mpr ⟨.lookup l, hc, by simp [hl]⟩
        rw [hshape] at hmemS2
        obtain ⟨p, -, rfl⟩ := List.mem_map.mp hmemS2
        have hp : p.1 ∈ plan := by rw [hplanDef]; exact p.2
        show Lookup.holdsAt tX.tf (envAt tX i)
          (siteLookup [] p.1.1 p.1.2 (s2Plan_admitted bb laneBase p.1 p.2))
        unfold Lookup.holdsAt
        have haXeq : (envAt tX i).loc
            = expandRow permOut g plan (t.rows.getD i zeroAsg) := by
          show tX.rows.getD i zeroAsg = _
          have hrows : tX.rows = t.rows.map (expandRow permOut g plan) := rfl
          rw [hrows, List.getD_eq_getElem?_getD, List.getElem?_map,
              List.getElem?_eq_getElem hi]
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
        have hov := expandGo_site permOut hperm
          (fun c => t.rows.getD i zeroAsg (g c)) plan hplan p.1 hp
        have hcol := planOk_colOnly plan hplan p.1 hp
        have htuple : (siteLookup [] p.1.1 p.1.2
              (s2Plan_admitted bb laneBase p.1 p.2)).tuple.map (·.eval ((envAt tX i).loc))
            = chipRowN permOut (insVals ((envAt tX i).loc) p.1.1) := by
          rw [haXeq]
          exact s2Lookup_tuple_eval permOut p.1 (s2Plan_admitted bb laneBase p.1 p.2) hcol hov
        rw [htuple]
        show _ ∈ tX.tf TableId.poseidon2
        have htbl : tX.tf TableId.poseidon2 = t.tf TableId.poseidon2
            ++ tX.rows.flatMap
                (fun aX => plan.map (fun p => chipRowN permOut (insVals aX p.1))) := by
          simp [htX, expandTrace, hplanDef]
        rw [htbl]
        apply List.mem_append_right
        apply List.mem_flatMap.mpr
        refine ⟨(envAt tX i).loc, ?_, List.mem_map.mpr ⟨p, hp, rfl⟩⟩
        have hilt : i < tX.rows.length := by rw [hlen]; exact hi
        show tX.rows.getD i zeroAsg ∈ tX.rows
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hilt]
        simpa using List.getElem_mem hilt
      | base b => simp [isS2] at hs2
      | memOp m => simp [isS2] at hs2
      | mapOp m => simp [isS2] at hs2
      | umemOp m => simp [isS2] at hs2
      | proofBind m => simp [isS2] at hs2
      | windowGate w => simp [isS2] at hs2
      | chalGate w => simp [isS2] at hs2
    · -- the kept constraints: transported through the index map
      have hs2f : isS2 bb c = false := by simpa using hs2
      have hkept : keptOk bb laneBase c = true := by
        rcases hkeptAll c hc with ht | hk
        · rw [hs2f] at ht; cases ht
        · exact hk
      have hcompact := hsat.rowConstraints i hi (mapC2 g c) (hkeptMem c hc hs2f)
      apply holdsAt_transport hash g t.tf tX.tf (envAt t i) (envAt tX i)
        (i == 0) (i + 1 == t.rows.length) c
        (fun r hr => hlocAg i r (hnotdead c hkept r hr))
        (fun r hr => hnxtAg i r (hnotdead c hkept r hr))
        (hpubAg i)
        (hchalAg i)
        ?_ (expandTrace_table_mono permOut bb laneBase t) hcompact
      intro hi' lo' hceq
      subst hceq
      unfold keptOk at hkept
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hkept
      obtain ⟨-, ⟨⟨⟨hb1, hb2⟩, hl1⟩, hl2⟩⟩ := hkept
      exact ⟨dropIdx_id_of_low bb laneBase _ (by omega) hl1,
             dropIdx_id_of_low bb laneBase _ (by omega) hl2⟩
  · -- rowHashes
    intro i hi
    rw [hlen] at hi
    have hcompact := hsat.rowHashes i hi
    apply siteHoldsAll_transport hash (envAt t i) (envAt tX i) g M.hashSites
    · intro s hs r hr
      exact hlocAg i r (hNotDeadOf r (hsitesOk s hs r hr))
    · exact hcompact
  · -- rowRanges
    intro i hi r hr
    rw [hlen] at hi
    have hcompact := hsat.rowRanges i hi (mapRange g r) (List.mem_map_of_mem hr)
    have hrd : r.wire ∉ dead := hNotDeadOf r.wire (hrangesOk r hr)
    unfold VmRange.holds at hcompact ⊢
    simp only [mapRange] at hcompact
    rw [hlocAg i r.wire hrd]
    exact hcompact
  · -- memClosed
    rw [hml]
    exact hsat.memClosed
  · -- memDisciplined
    rw [hml]
    exact hsat.memDisciplined
  · -- memBalanced
    rw [hml]
    exact hsat.memBalanced
  · -- memTableFaithful
    rw [htfmem, hml]
    exact hsat.memTableFaithful
  · -- mapTableFaithful
    rw [htfmap, hmpl]
    exact hsat.mapTableFaithful

#assert_axioms compactS2_expand
#assert_axioms expandTrace_chipSoundN
#assert_axioms holdsAt_transport

/-- The expanded trace keeps the compact trace's row count and public inputs, and agrees with
it on every surviving column (through the index map) — the transport surface downstream
keystone corollaries read their conclusions back through. -/
theorem expandTrace_shape (permOut : List ℤ → List ℤ) (bb laneBase : Nat) (t : VmTrace)
    (hsub : ∀ p ∈ s2Plan bb laneBase, ∀ x ∈ overrideColsOf p.1 p.2, x ∈ s2DeadCols bb laneBase) :
    (expandTrace permOut bb laneBase t).rows.length = t.rows.length
    ∧ (expandTrace permOut bb laneBase t).pub = t.pub
    ∧ ∀ i c, c ∉ s2DeadCols bb laneBase →
        (envAt (expandTrace permOut bb laneBase t) i).loc c
          = (envAt t i).loc (dropIdx bb laneBase c) :=
  ⟨by simp [expandTrace], rfl,
   fun i c hc => expandTrace_getD_agree permOut bb laneBase t hsub i c hc⟩

/-! ## §8 — the CHECKED emit entry point (the live falsifier of the "dead stratum" verdict).

The emit drivers do not hand-tabulate the lane geometry: `s2LaneBaseOf` reads the first S2
lookup's first lane column out of the member itself, and `compactS2Checked` refuses to produce
a compact member unless the ENTIRE decidable bundle `compactOk` holds — the member's S2 stratum
is exactly the two expected chains, no surviving constraint touches a dead column, the plan is
well-formed. If any member's S2 were load-bearing, the emit FAILS CLOSED, there and then. -/

/-- The graduated lane base, read off the member's own first S2 lookup (tuple slot
`2 + CHIP_RATE` = the first lane column). Cross-checked wholesale by `compactOk`'s shape
equality, so a misread here cannot silently produce a wrong compaction. -/
def s2LaneBaseOf (M : EffectVmDescriptor2) (bb : Nat) : Option Nat :=
  match s2LookupsOf M bb with
  | l :: _ =>
    match l.tuple.getD (2 + CHIP_RATE) (.const 0) with
    | .var c => some c
    | _ => none
  | [] => none

/-- Compact a wide member at block base `bb`, deriving the lane base from the member and
REFUSING (`none`) unless every decidable side condition holds. -/
def compactS2Checked (M : EffectVmDescriptor2) (bb : Nat) : Option EffectVmDescriptor2 :=
  match s2LaneBaseOf M bb with
  | some lb => if compactOk M bb lb then some (compactS2 M bb lb) else none
  | none => none

/-- A checked compaction only ever returns `compactS2` under a TRUE `compactOk` — the bridge's
hypothesis is discharged by construction for every emitted member. -/
theorem compactS2Checked_ok (M : EffectVmDescriptor2) (bb : Nat) (cm : EffectVmDescriptor2)
    (h : compactS2Checked M bb = some cm) :
    ∃ lb, compactOk M bb lb = true ∧ cm = compactS2 M bb lb := by
  unfold compactS2Checked at h
  cases hlb : s2LaneBaseOf M bb with
  | none => rw [hlb] at h; cases h
  | some lb =>
    rw [hlb] at h
    dsimp only at h
    by_cases hok : compactOk M bb lb
    · rw [if_pos hok] at h
      exact ⟨lb, hok, (Option.some_inj.mp h).symm⟩
    · rw [if_neg hok] at h; cases h

#assert_axioms compactS2Checked_ok

end Dregg2.Circuit.Emit.RotWideCompactS2
