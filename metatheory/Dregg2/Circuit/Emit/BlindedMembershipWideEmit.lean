/-
# Dregg2.Circuit.Emit.BlindedMembershipWideEmit — the WIDE (8-lane node-fold) BLINDED membership
(E2 #2b — the real ~124-bit federation membership)

**This is Lean-authored AIR.** This module authors the algebra; Rust parses the emitted IR2 bytes
and supplies witnesses — it constructs no constraints.

## What this file IS

The WIDE additive replacement for the deployed depth-general blinded ring-membership descriptor
`BlindedMembershipEmit.blindedMembership4aryDesc` (staged-additive-then-cutover). The deployed
family is the HARD residual of felt-width finding **#2** (federation;
`docs/WOUND-felt-width-boundaries-2026-07-19.md`): its node fold chains on **lane 0 only** — each
level absorbs the four children as four SINGLE felts (`gParentLookup`, arity 4), the continuity
window ties one column (`next.cur = this.par` at `gCUR`/`gPAR`), and the blinding tooth absorbs
the member digest as ONE felt (`gBlindLookup`, arity 2) — so the interior of the tree, the root
PI, and the published blinded leaf are all ~31-bit (2^15.5-collidable) commitments, regardless of
how many permutation lanes the chip witnesses.

⚠ ANTI-MASQUERADE: `gPATH_LANES = [11..17]` — the 8 permutation lanes are ALREADY in the deployed
trace. Exposing them (or the top node's lanes) as PIs while the tree still chains lane-0 buys
NOTHING: the interior stays ~31-bit. This descriptor therefore widens the **fold** and the
**blinding preimage**, not the PI surface alone — a genuine Merkle-scheme change, the same one
`MerkleMembership4aryWideEmit` made for the plain membership family. E2 #2a
(`BoundPresentationWideEmit`) exposed the 8-felt federation root as PIs; together with THIS file
the membership side of wound #2 closes at ~124-bit — at the DEFERRED coordinated cutover below,
not before.

## The widened scheme

* Every node of the tree is a FULL 8-felt Poseidon2 digest (`Digest8`), not a lane-0 squeeze.
* The 4-ary node fold absorbs all 8 lanes of each child. Four 8-felt children are 32 felts —
  double the chip rate (`CHIP_RATE = 16`) — so the fold is realized as a balanced pair of
  arity-16 absorbs, all three bound at full output width by `chipLookupTupleN`:

      node8W(c0,c1,c2,c3) = A16( A16(c0 ‖ c1) ‖ A16(c2 ‖ c3) )

  where `A16` is the same arity-16 pack8 absorb the deployed heap/cap `node8` rows already ride
  (one chip, arity-tag-separated domains — inherited deployed practice, not new sharing).
* Chain continuity is 8 window gates — `next.cur[k] = this.par[k]` for EVERY lane k — where the
  deployed family has one.
* The position/arrangement gates are the deployed family's algebra (`gArrangeList`, the
  `child0Body..child3Body` shapes) applied per lane with SHARED position bits: the 8-felt running
  node sits at its `b0 + 2·b1` slot among the 8-felt siblings.
* **THE BLINDING IS PRESERVED.** The fresh blinding factor still rides the leaf, and leaf +
  blinding stay HIDDEN (the hiddenness is the unlinkability). What widens is the PREIMAGE: the
  wide blinding tooth absorbs all 8 leaf lanes plus the blinding felt in ONE absorb (arity 9 —
  9 ≤ CHIP_RATE — domain-separated from the arity-16 fold rows and every deployed arity 2/4/7 by
  the chip's arity tag) and publishes an 8-FELT blinded leaf, every output lane bound.
* PI layout `[blinded0..blinded7, root0..root7]` (piCount 16): the row-0 blinded leaf group is
  pinned to PIs 0..7, the last-row parent to PIs 8..15. The published commitment is widened WITH
  the root (the class-D lesson: an 8-felt root behind a 1-felt published commitment re-pins a
  31-bit key and buys nothing).

## What is proved here (and the named residual)

* `wChildren_arranged_lane` / `wGroups_arranged` — the arrangement gates pin the four 8-felt
  children to the positional arrangement of the 8-felt running node and siblings, every lane.
* `wideNodeFold_sound` — under a sound WIDE chip table (`ChipTableSoundN`), the three fold
  lookups force the parent group to the genuine two-stage fold `wideFold4` of the four child
  groups: the full 8-felt node binding, per row.
* `wideBlind_sound` — the wide blinding lookup forces the 8 published blinded-leaf columns to the
  genuine absorb of (all 8 leaf lanes ‖ blinding): the published commitment binds the WHOLE
  member digest, not its lane 0.
* `wCont_all_zero_iff` — the 8 continuity windows hold iff the NEXT row's 8-felt running node IS
  this row's 8-felt parent (the widened chain, stated at `Digest8`).
* **The anti-masquerade teeth**, in the collision-extraction discipline (`Coll8`; the
  injectivity-hypothesis style is refuted at deployed parameters — `Compress8CR` is false for the
  real chip — so a bare `∃` would be a free pass):
  - `interior_forge_narrow_admits_wide_refuses` — child quadruples agreeing on every lane 0 but
    differing at some lane j: (1) the deployed lane-0 blinded fold yields EQUAL parents at zero
    cost (the forge the deployed descriptor admits); (2) equal WIDE parents hand back the
    specific, named, full-width chip collision `wideFoldColl8Find` returns — as DATA.
  - `blinded_leaf_forge_narrow_admits_wide_refuses` — the same class at the BLINDING boundary:
    two member digests agreeing at lane 0 publish the SAME deployed blinded leaf under the same
    blinding factor for free; equal WIDE blinded leaves extract the named collision on the full
    9-felt preimage.

NAMED RESIDUAL: the full multi-row `Satisfied2 ⇒` recomposed-blinded-path refinement (the
`*Refine`-tier walk composing `wideNodeFold_sound` + `wideBlind_sound` + `wCont_all_zero_iff` +
`wGroups_arranged` across the trace) is deferred to a `BlindedMembershipWideRefine` module. The
deployed depth-general narrow family (`blindedMembership4aryDesc`) carries no such refinement
either; the per-row teeth here are strictly more than parity.

## DEFERRED coordinated deploy (integrator, one epoch)

The Rust consumer repoint (`blinded_membership_witness_4ary`, `circuit/src/poseidon2_air.rs`'s
`generate_blinded_*`, `bridge/present.rs`), the descriptor-JSON golden regen into
`circuit/descriptors/`, and the `vk_hash` registry rotation are the coordinated cutover; nothing
here changes the deployed descriptor or its registry entry.

## Axiom hygiene

Definitional descriptor + byte-pinned `#guard` on the wire string + non-vacuous shape/semantic
lemmas. `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.BlindedMembershipEmit
import Dregg2.Circuit.DeployedCapTree
import Dregg2.Circuit.GateExpr

namespace Dregg2.Circuit.Emit.BlindedMembershipWideEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId Table chipLookupTupleN ChipTableSoundN
   chip_lookup_sound_N CHIP_RATE emitVmJson2 WindowExpr WindowConstraint ChipArityAdmitted chipArity_le_rate)
open Dregg2.Circuit.Emit.BlindedMembershipEmit
  (bitBinaryBody gArrangeList ev ek eadd emul eneg esub eoneMinus blindedMembership4aryDesc)
open Dregg2.Circuit.DeployedCapTree (Digest8 Coll8)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (pack8 pack8_inj)

set_option autoImplicit false

/-! ## §1 — the trace column layout: every Merkle value is an 8-lane group; the blinding rides.

One 4-ary level per trace row (depth = trace height), as in the deployed family — but the running
node, the three siblings, the four ordered children, and the parent are each a FULL 8-felt digest
group. The path block (columns 0..89) is laid out identically to `MerkleMembership4aryWideEmit`;
past it sit the blinding felt and the 8-felt published blinded leaf. UNLIKE the plain wide
membership, the row-0 running node (the member leaf digest) is NOT PI-pinned — it stays HIDDEN;
only its blinded image is published. -/

/-- The 8-felt running node (row 0 = the HIDDEN 8-felt member leaf digest). -/
def wCUR : Fin 8 → Nat := fun k => k.val
/-- The three 8-felt co-path siblings at this level (HIDDEN). -/
def wSIB0 : Fin 8 → Nat := fun k => 8 + k.val
def wSIB1 : Fin 8 → Nat := fun k => 16 + k.val
def wSIB2 : Fin 8 → Nat := fun k => 24 + k.val
/-- The two position bits (`position = b0 + 2·b1 ∈ {0,1,2,3}`) — per-row scalars. -/
def wB0 : Nat := 32
def wB1 : Nat := 33
/-- The four ordered 8-felt children (`children[position] = cur8`, siblings fill in order). -/
def wC0 : Fin 8 → Nat := fun k => 34 + k.val
def wC1 : Fin 8 → Nat := fun k => 42 + k.val
def wC2 : Fin 8 → Nat := fun k => 50 + k.val
def wC3 : Fin 8 → Nat := fun k => 58 + k.val
/-- Stage-1 left digest `A16(c0 ‖ c1)` — all 8 lanes bound. -/
def wH01 : Fin 8 → Nat := fun k => 66 + k.val
/-- Stage-1 right digest `A16(c2 ‖ c3)` — all 8 lanes bound. -/
def wH23 : Fin 8 → Nat := fun k => 74 + k.val
/-- The 8-felt parent `A16(h01 ‖ h23)`; last row pinned to the 8 root PIs. -/
def wPAR : Fin 8 → Nat := fun k => 82 + k.val
/-- The fresh blinding factor — one felt, HIDDEN (this hiddenness gives unlinkability). -/
def wBLINDING : Nat := 90
/-- The published 8-felt blinded leaf `A9(cur8 ‖ blinding)`; row 0 pinned to PIs 0..7. -/
def wBLINDED : Fin 8 → Nat := fun k => 91 + k.val
/-- Total main-trace width: 10 8-lane groups + 2 bits + the blinding felt. -/
def BLINDED_WIDE_WIDTH : Nat := 99

/-- PI slots 0..7: the published 8-felt blinded leaf (the unlinkable commitment). -/
def wPI_BLINDED (k : Fin 8) : Nat := k.val
/-- PI slots 8..15: the committed 8-felt federation root. -/
def wPI_ROOT (k : Fin 8) : Nat := 8 + k.val
/-- Number of public inputs: `[blinded0..blinded7, root0..root7]`. -/
def BLINDED_WIDE_PI_COUNT : Nat := 16

/-- The 8 columns of a lane group, in lane order (the wide lookup's `digestCols`). -/
def wCols (g : Fin 8 → Nat) : List Nat := (List.finRange 8).map g

/-- Read a lane group under an assignment as a `Digest8`. -/
def wVal (a : Assignment) (g : Fin 8 → Nat) : Digest8 := fun k => a (g k)

/-- The 8 group columns read under `a` ARE `List.ofFn (wVal a g)` — the bridge between the wide
lever's `digestCols.map a` conclusion and the `Digest8` carrier the fold model consumes. -/
theorem wCols_map (a : Assignment) (g : Fin 8 → Nat) :
    (wCols g).map a = List.ofFn (wVal a g) := by
  unfold wCols wVal
  rw [List.map_map, List.ofFn_eq_map]
  rfl

/-! ## §2 — the per-row position/arrangement gates (the deployed algebra, per lane, shared bits).

The gate BODIES are the deployed blinded family's `child0Body..child3Body` term-for-term,
instantiated at each lane's columns with the SHARED indicator polynomials over `wB0/wB1`. The
arrangement they enforce is the same `gArrangeList` — now holding lane-by-lane, i.e. of the whole
8-felt values. -/

-- The four Lagrange position indicators over the shared bits (degree 2, integer coefficients).
def wIndL0 : EmittedExpr := emul (eoneMinus (ev wB0)) (eoneMinus (ev wB1))
def wIndL1 : EmittedExpr := emul (ev wB0) (eoneMinus (ev wB1))
def wIndL2 : EmittedExpr := emul (eoneMinus (ev wB0)) (ev wB1)
def wIndL3 : EmittedExpr := emul (ev wB0) (ev wB1)

-- The per-lane child-selection gate bodies `c_j[k] - selection_j[k]` (the deployed arrangement).
def wChild0Body (k : Fin 8) : EmittedExpr :=
  esub (esub (ev (wC0 k)) (ev (wSIB0 k))) (emul wIndL0 (esub (ev (wCUR k)) (ev (wSIB0 k))))
def wChild1Body (k : Fin 8) : EmittedExpr :=
  esub (ev (wC1 k))
    (eadd (eadd (emul (ev (wSIB0 k)) wIndL0) (emul (ev (wCUR k)) wIndL1))
      (emul (ev (wSIB1 k)) (eadd wIndL2 wIndL3)))
def wChild2Body (k : Fin 8) : EmittedExpr :=
  esub (ev (wC2 k))
    (eadd (eadd (emul (ev (wSIB1 k)) (eadd wIndL0 wIndL1)) (emul (ev (wCUR k)) wIndL2))
      (emul (ev (wSIB2 k)) wIndL3))
def wChild3Body (k : Fin 8) : EmittedExpr :=
  esub (esub (ev (wC3 k)) (ev (wSIB2 k))) (emul wIndL3 (esub (ev (wCUR k)) (ev (wSIB2 k))))

/-- The four child-selection bodies at lane `k`, in the deployed order. -/
def wChildBodiesAt (k : Fin 8) : List EmittedExpr :=
  [wChild0Body k, wChild1Body k, wChild2Body k, wChild3Body k]

/-- The per-row constraint bodies: the two bit-binary gates, then the four child-selection gates
for each of the 8 lanes (lane-major). 2 + 8·4 = 34 bodies. -/
def wPerRowBodies : List EmittedExpr :=
  [bitBinaryBody wB0, bitBinaryBody wB1] ++ ((List.finRange 8).map wChildBodiesAt).flatten

/-- **`wChildren_arranged_lane`** — at EVERY lane `k`, a row satisfying the two bit-binary gates
and lane `k`'s four child-selection gates has its lane-`k` child slice equal to the positional
arrangement of the lane-`k` running-node/sibling slice. The per-lane port of the deployed
`gChildren_arranged`; the bits are shared, so all 8 lanes arrange at ONE position. -/
theorem wChildren_arranged_lane (a : Assignment) (k : Fin 8)
    (hb0 : (bitBinaryBody wB0).eval a = 0) (hb1 : (bitBinaryBody wB1).eval a = 0)
    (h0 : (wChild0Body k).eval a = 0) (h1 : (wChild1Body k).eval a = 0)
    (h2 : (wChild2Body k).eval a = 0) (h3 : (wChild3Body k).eval a = 0) :
    [a (wC0 k), a (wC1 k), a (wC2 k), a (wC3 k)]
      = gArrangeList (a (wCUR k)) (a (wSIB0 k)) (a (wSIB1 k)) (a (wSIB2 k))
          (a wB0) (a wB1) := by
  simp only [Dregg2.Circuit.Emit.BlindedMembershipEmit.bitBinaryBody_eq, ev, ek, eadd, emul,
    eneg, EmittedExpr.eval] at hb0 hb1
  have e0 : a wB0 = 0 ∨ a wB0 = 1 := by
    have h : a wB0 * (a wB0 - 1) = 0 := by linear_combination hb0
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have e1 : a wB1 = 0 ∨ a wB1 = 1 := by
    have h : a wB1 * (a wB1 - 1) = 0 := by linear_combination hb1
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  simp only [wChild0Body, wChild1Body, wChild2Body, wChild3Body,
    wIndL0, wIndL1, wIndL2, wIndL3, ev, ek, eadd, emul, eneg, esub, eoneMinus,
    EmittedExpr.eval] at h0 h1 h2 h3
  rcases e0 with hb0v | hb0v <;> rcases e1 with hb1v | hb1v
  · have hr : gArrangeList (a (wCUR k)) (a (wSIB0 k)) (a (wSIB1 k)) (a (wSIB2 k))
        (a wB0) (a wB1)
        = [a (wCUR k), a (wSIB0 k), a (wSIB1 k), a (wSIB2 k)] := by
      simp [gArrangeList, hb0v, hb1v]
    rw [hb0v, hb1v] at h0 h1 h2 h3
    ring_nf at h0 h1 h2 h3
    rw [hr]; simp only [List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · have hr : gArrangeList (a (wCUR k)) (a (wSIB0 k)) (a (wSIB1 k)) (a (wSIB2 k))
        (a wB0) (a wB1)
        = [a (wSIB0 k), a (wSIB1 k), a (wCUR k), a (wSIB2 k)] := by
      simp [gArrangeList, hb0v, hb1v]
    rw [hb0v, hb1v] at h0 h1 h2 h3
    ring_nf at h0 h1 h2 h3
    rw [hr]; simp only [List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · have hr : gArrangeList (a (wCUR k)) (a (wSIB0 k)) (a (wSIB1 k)) (a (wSIB2 k))
        (a wB0) (a wB1)
        = [a (wSIB0 k), a (wCUR k), a (wSIB1 k), a (wSIB2 k)] := by
      simp [gArrangeList, hb0v, hb1v]
    rw [hb0v, hb1v] at h0 h1 h2 h3
    ring_nf at h0 h1 h2 h3
    rw [hr]; simp only [List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · have hr : gArrangeList (a (wCUR k)) (a (wSIB0 k)) (a (wSIB1 k)) (a (wSIB2 k))
        (a wB0) (a wB1)
        = [a (wSIB0 k), a (wSIB1 k), a (wSIB2 k), a (wCUR k)] := by
      simp [gArrangeList, hb0v, hb1v]
    rw [hb0v, hb1v] at h0 h1 h2 h3
    ring_nf at h0 h1 h2 h3
    rw [hr]; simp only [List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- The positional arrangement lifted to whole `Digest8` children (the level step at width 8). -/
def wArrange8 (cur s0 s1 s2 : Digest8) (b0 b1 : ℤ) : List Digest8 :=
  if b1 = 0 then (if b0 = 0 then [cur, s0, s1, s2] else [s0, cur, s1, s2])
  else (if b0 = 0 then [s0, s1, cur, s2] else [s0, s1, s2, cur])

/-- **`wGroups_arranged`** — the GROUP-level keystone: on any row satisfying the bit-binary gates
and all 32 child-selection gates, the four 8-FELT children ARE the positional arrangement of the
8-FELT running node and siblings. A forger cannot place arbitrary 8-felt children under a level;
they must be the whole running digest (at its slot) plus the whole real siblings — every lane,
not lane 0. -/
theorem wGroups_arranged (a : Assignment)
    (hb0 : (bitBinaryBody wB0).eval a = 0) (hb1 : (bitBinaryBody wB1).eval a = 0)
    (hc : ∀ k : Fin 8, (wChild0Body k).eval a = 0 ∧ (wChild1Body k).eval a = 0
      ∧ (wChild2Body k).eval a = 0 ∧ (wChild3Body k).eval a = 0) :
    [wVal a wC0, wVal a wC1, wVal a wC2, wVal a wC3]
      = wArrange8 (wVal a wCUR) (wVal a wSIB0) (wVal a wSIB1) (wVal a wSIB2)
          (a wB0) (a wB1) := by
  have hlane : ∀ k : Fin 8,
      [a (wC0 k), a (wC1 k), a (wC2 k), a (wC3 k)]
        = gArrangeList (a (wCUR k)) (a (wSIB0 k)) (a (wSIB1 k)) (a (wSIB2 k))
            (a wB0) (a wB1) :=
    fun k => wChildren_arranged_lane a k hb0 hb1 (hc k).1 (hc k).2.1 (hc k).2.2.1 (hc k).2.2.2
  simp only [Dregg2.Circuit.Emit.BlindedMembershipEmit.bitBinaryBody_eq, ev, ek, eadd, emul,
    eneg, EmittedExpr.eval] at hb0 hb1
  have e0 : a wB0 = 0 ∨ a wB0 = 1 := by
    have h : a wB0 * (a wB0 - 1) = 0 := by linear_combination hb0
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have e1 : a wB1 = 0 ∨ a wB1 = 1 := by
    have h : a wB1 * (a wB1 - 1) = 0 := by linear_combination hb1
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases e0 with hb0v | hb0v <;> rcases e1 with hb1v | hb1v
  · rw [hb0v, hb1v]
    have harr : wArrange8 (wVal a wCUR) (wVal a wSIB0) (wVal a wSIB1) (wVal a wSIB2) 0 0
        = [wVal a wCUR, wVal a wSIB0, wVal a wSIB1, wVal a wSIB2] := by simp [wArrange8]
    rw [harr]
    have hcomp : ∀ k : Fin 8, a (wC0 k) = a (wCUR k) ∧ a (wC1 k) = a (wSIB0 k)
        ∧ a (wC2 k) = a (wSIB1 k) ∧ a (wC3 k) = a (wSIB2 k) := by
      intro k
      have h := hlane k
      rw [hb0v, hb1v] at h
      simpa [gArrangeList] using h
    simp only [List.cons.injEq, and_true]
    exact ⟨funext fun k => (hcomp k).1, funext fun k => (hcomp k).2.1,
           funext fun k => (hcomp k).2.2.1, funext fun k => (hcomp k).2.2.2⟩
  · rw [hb0v, hb1v]
    have harr : wArrange8 (wVal a wCUR) (wVal a wSIB0) (wVal a wSIB1) (wVal a wSIB2) 0 1
        = [wVal a wSIB0, wVal a wSIB1, wVal a wCUR, wVal a wSIB2] := by simp [wArrange8]
    rw [harr]
    have hcomp : ∀ k : Fin 8, a (wC0 k) = a (wSIB0 k) ∧ a (wC1 k) = a (wSIB1 k)
        ∧ a (wC2 k) = a (wCUR k) ∧ a (wC3 k) = a (wSIB2 k) := by
      intro k
      have h := hlane k
      rw [hb0v, hb1v] at h
      simpa [gArrangeList] using h
    simp only [List.cons.injEq, and_true]
    exact ⟨funext fun k => (hcomp k).1, funext fun k => (hcomp k).2.1,
           funext fun k => (hcomp k).2.2.1, funext fun k => (hcomp k).2.2.2⟩
  · rw [hb0v, hb1v]
    have harr : wArrange8 (wVal a wCUR) (wVal a wSIB0) (wVal a wSIB1) (wVal a wSIB2) 1 0
        = [wVal a wSIB0, wVal a wCUR, wVal a wSIB1, wVal a wSIB2] := by simp [wArrange8]
    rw [harr]
    have hcomp : ∀ k : Fin 8, a (wC0 k) = a (wSIB0 k) ∧ a (wC1 k) = a (wCUR k)
        ∧ a (wC2 k) = a (wSIB1 k) ∧ a (wC3 k) = a (wSIB2 k) := by
      intro k
      have h := hlane k
      rw [hb0v, hb1v] at h
      simpa [gArrangeList] using h
    simp only [List.cons.injEq, and_true]
    exact ⟨funext fun k => (hcomp k).1, funext fun k => (hcomp k).2.1,
           funext fun k => (hcomp k).2.2.1, funext fun k => (hcomp k).2.2.2⟩
  · rw [hb0v, hb1v]
    have harr : wArrange8 (wVal a wCUR) (wVal a wSIB0) (wVal a wSIB1) (wVal a wSIB2) 1 1
        = [wVal a wSIB0, wVal a wSIB1, wVal a wSIB2, wVal a wCUR] := by simp [wArrange8]
    rw [harr]
    have hcomp : ∀ k : Fin 8, a (wC0 k) = a (wSIB0 k) ∧ a (wC1 k) = a (wSIB1 k)
        ∧ a (wC2 k) = a (wSIB2 k) ∧ a (wC3 k) = a (wCUR k) := by
      intro k
      have h := hlane k
      rw [hb0v, hb1v] at h
      simpa [gArrangeList] using h
    simp only [List.cons.injEq, and_true]
    exact ⟨funext fun k => (hcomp k).1, funext fun k => (hcomp k).2.1,
           funext fun k => (hcomp k).2.2.1, funext fun k => (hcomp k).2.2.2⟩

/-! ## §3 — the WIDE node fold: three arity-16 chip lookups, all 8 output lanes BOUND.

The deployed blinded family's `gParentLookup` absorbs the four children as four SINGLE felts
(arity 4) and binds out0 only, WITNESSING lanes 1..7 without chaining them — that is the wound.
Here every absorb input is a whole 8-lane group and every output lane is bound by
`chipLookupTupleN`. -/

/-- The 16 input expressions of one fold stage: the two 8-lane groups, in lane order. -/
def wStageIns (gL gR : Fin 8 → Nat) : List EmittedExpr :=
  (wCols gL ++ wCols gR).map EmittedExpr.var

/-- A fold-stage input list evaluates to exactly `pack8` of the two group values — the same
`L8 ‖ R8` block the deployed heap/cap `node8` absorbs. -/
theorem wStageIns_eval (a : Assignment) (gL gR : Fin 8 → Nat) :
    (wStageIns gL gR).map (·.eval a) = pack8 (wVal a gL) (wVal a gR) := by
  have hcomp : ∀ g : Fin 8 → Nat,
      ((wCols g).map EmittedExpr.var).map (·.eval a) = (wCols g).map a := by
    intro g
    rw [List.map_map]
    rfl
  simp only [wStageIns, List.map_append, hcomp, wCols_map]
  rfl

/-- Stage 1 left: `A16(c0 ‖ c1)` → the 8 `wH01` columns, every lane bound. -/
def wStageLLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTupleN (wStageIns wC0 wC1) (wCols wH01)⟩
/-- Stage 1 right: `A16(c2 ‖ c3)` → the 8 `wH23` columns, every lane bound. -/
def wStageRLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTupleN (wStageIns wC2 wC3) (wCols wH23)⟩
/-- Stage 2: `A16(h01 ‖ h23)` → the 8 `wPAR` columns — the 8-felt parent, every lane bound. -/
def wParentLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTupleN (wStageIns wH01 wH23) (wCols wPAR)⟩

/-- The wide permutation output of an 8-output absorb, as the `List ℤ` block a sound wide chip
table carries (the `heapPermOut` shape, scheme-free). -/
def wPermOut (absorb : List ℤ → Digest8) : List ℤ → List ℤ := fun xs => List.ofFn (absorb xs)

/-- **`wideFold4`** — the widened 4-ary node function: the balanced two-stage arity-16 fold over
whole 8-felt children. This is the Merkle-scheme change: all 32 child felts enter the preimage. -/
def wideFold4 (absorb : List ℤ → Digest8) (c0 c1 c2 c3 : Digest8) : Digest8 :=
  absorb (pack8 (absorb (pack8 c0 c1)) (absorb (pack8 c2 c3)))

/-- **`wideNodeFold_sound`** — under a SOUND WIDE chip table, a row whose three fold lookups hold
carries the genuine `wideFold4` of its four 8-felt children in the 8 parent columns. The wide
lever (`chip_lookup_sound_N`) forces every stage column-for-column; nothing rides lane 0 alone. -/
theorem wideNodeFold_sound (absorb : List ℤ → Digest8) (tbl : Table)
    (hChip : ChipTableSoundN (wPermOut absorb) tbl) (a : Assignment)
    (hL : (chipLookupTupleN (wStageIns wC0 wC1) (wCols wH01)).map (·.eval a) ∈ tbl)
    (hR : (chipLookupTupleN (wStageIns wC2 wC3) (wCols wH23)).map (·.eval a) ∈ tbl)
    (hP : (chipLookupTupleN (wStageIns wH01 wH23) (wCols wPAR)).map (·.eval a) ∈ tbl) :
    wVal a wPAR = wideFold4 absorb (wVal a wC0) (wVal a wC1) (wVal a wC2) (wVal a wC3) := by
  -- The stage block is 8 + 8 = 16 lanes, and 16 IS an admitted chip arity (the `node8`
  -- full-width compression row). The spine is literal, so this reduces regardless of `gL`/`gR`.
  have hadm : ∀ gL gR : Fin 8 → Nat, ChipArityAdmitted (wStageIns gL gR).length := by
    intro gL gR; exact of_decide_eq_true (Eq.refl true)
  have h1 := chip_lookup_sound_N (wPermOut absorb) tbl hChip a _ _ (hadm wC0 wC1) hL
  have h2 := chip_lookup_sound_N (wPermOut absorb) tbl hChip a _ _ (hadm wC2 wC3) hR
  have h3 := chip_lookup_sound_N (wPermOut absorb) tbl hChip a _ _ (hadm wH01 wH23) hP
  rw [wCols_map, wStageIns_eval] at h1 h2 h3
  have e1 : wVal a wH01 = absorb (pack8 (wVal a wC0) (wVal a wC1)) := List.ofFn_inj.mp h1
  have e2 : wVal a wH23 = absorb (pack8 (wVal a wC2) (wVal a wC3)) := List.ofFn_inj.mp h2
  have e3 : wVal a wPAR = absorb (pack8 (wVal a wH01) (wVal a wH23)) := List.ofFn_inj.mp h3
  rw [e3, e1, e2]
  rfl

/-! ## §3b — the WIDE blinding tooth: one arity-11 chip lookup, all 8 output lanes BOUND.

The deployed `gBlindLookup` absorbs `[gCUR, gBLINDING]` (arity 2): the published blinded leaf
commits to lane 0 of the member digest only. Here the absorb takes ALL 8 leaf lanes plus the
blinding felt. The blinding factor stays a HIDDEN fresh felt: unlinkability is untouched; only the
preimage widens.

⚠ **THE ARITY IS 11, NOT 9, AND THAT IS FORCED BY THE DEPLOYED CHIP.** This block asked for arity
9 until 2026-08-01. The chip AIR admits `arity ∈ {0, 2, 3, 4, 7, 11, 16}` — it asserts
`arity·(a−2)(a−3)(a−4)(a−7)(a−11)(a−16) = 0` (`circuit/src/descriptor_ir2.rs`, degree 7 = the whole
S-box budget, so an eighth factor cannot be added). At `a = 9` that product is `52920 ≠ 0`, so the
row was UNSAT: the honest witness could never prove. Worse, the witness generator
`chip_absorb_all_lanes` seeds lanes 4/5/6 from the inputs only when
`arity ∈ {7, 11, 16}` — at 9 it writes the arity TAG into lane 4 and zeros 5 and 6, so three of the
eight member lanes were silently dropped from the preimage and the tooth bound 5 lanes, not 8.

So the absorb is the deployed wide arity **11**: `cur8 ‖ blinding ‖ 0 ‖ 0`. The two trailing zero
lanes are binding-preserving (`packBlind` stays injective in `(leaf, r)` — `packBlind_inj`), the
seeding is the genuine `seed456` path so every one of the 8 leaf lanes enters the permutation, and
11 is the arity the wide MD commit step already rides.

⚑ **BOTH HALVES OF THIS PARAGRAPH WERE STALE — CORRECTED 2026-08-03, EACH RE-MEASURED.**

It read: "NOTHING GATES A LEAN EMITTER'S CHOSEN ABSORB ARITY AGAINST THE CHIP'S ADMITTED SET. That
missing gate is why an unprovable descriptor sat here byte-pinned and green. A second instance is
already on disk: `guarded-hiding-span-m0-wide-blinded-commit-blind5-v1.json` carries TID_P2 lookups
at arity 8 and 14."

* **The gate exists now.** All four tuple constructors (`chipLookupTuple`, `chipLookupTupleN`,
  `chipLookupTupleNarrow`, `TableAirIR.chipAbsorbTuple`) and both site-level constructors
  (`siteLookup`, `siteLookupNarrow`) carry `ChipArityAdmitted` as an `autoParam`, so an absorb at 8,
  9 or 14 FAILS TO ELABORATE. `Dregg2.Circuit.ChipArityBite` asserts that refusal on every rail, with
  positive controls at every admitted arity.
* **The named descriptor no longer carries 8 and 14.** Re-read on 2026-08-03: its three `table: 1`
  (`TID_P2`) lookups carry arity tags **11, 16, 16** — it was re-emitted by the §3b padding this
  very docstring describes, and the sentence accusing it was simply never updated. Swept across
  ALL of `circuit/descriptors/by-name/*.json`, the whole `TID_P2` arity histogram is
  `{16: 90, 11: 127, 7: 19, 4: 11}` — **every on-disk descriptor is at an admitted arity, none
  inadmissible.** -/

/-- The 11 input expressions of the wide blinding absorb: the 8 leaf lanes, the blinding, then the
two zero pads that put the row on the deployed wide arity (see §3b). -/
def wBlindIns : List EmittedExpr :=
  (wCols wCUR).map EmittedExpr.var ++ [.var wBLINDING, ek 0, ek 0]

/-- Pack an 8-felt leaf and the blinding felt into the arity-11 absorb block `leaf8 ‖ [r, 0, 0]`. -/
def packBlind (leaf : Digest8) (r : ℤ) : List ℤ := List.ofFn leaf ++ [r, 0, 0]

/-- `packBlind` is injective in `(leaf, r)`: the length-8 prefix splits uniquely and `List.ofFn`
is injective — the structural twin of `pack8_inj` at the blinding arity. -/
theorem packBlind_inj {l₁ l₂ : Digest8} {r₁ r₂ : ℤ}
    (h : packBlind l₁ r₁ = packBlind l₂ r₂) : l₁ = l₂ ∧ r₁ = r₂ := by
  unfold packBlind at h
  have hlen : (List.ofFn l₁).length = (List.ofFn l₂).length := by simp
  obtain ⟨hl, hr⟩ := List.append_inj h hlen
  exact ⟨List.ofFn_inj.mp hl, by simpa using hr⟩

/-- The blind input list evaluates to exactly `packBlind` of the leaf group and blinding felt. -/
theorem wBlindIns_eval (a : Assignment) :
    wBlindIns.map (·.eval a) = packBlind (wVal a wCUR) (a wBLINDING) := by
  have hcomp : ((wCols wCUR).map EmittedExpr.var).map (·.eval a) = (wCols wCUR).map a := by
    rw [List.map_map]
    rfl
  simp only [wBlindIns, List.map_append, hcomp, wCols_map, List.map_cons, List.map_nil, ek,
    EmittedExpr.eval]
  rfl

/-- The wide blinding lookup: `A11(cur8 ‖ blinding ‖ 0 ‖ 0)` → the 8 `wBLINDED` columns, every lane
bound. Fires per row; the row-0 image (of the member leaf digest) is the one the PIs pin. -/
def wBlindLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTupleN wBlindIns (wCols wBLINDED)⟩

/-- **`wideBlind`** — the widened blinding function: the whole 8-felt member digest and the
blinding felt enter one absorb. The published commitment binds every lane of the member. -/
def wideBlind (absorb : List ℤ → Digest8) (leaf : Digest8) (r : ℤ) : Digest8 :=
  absorb (packBlind leaf r)

/-- **`wideBlind_sound`** — under a SOUND WIDE chip table, a row whose blind lookup holds carries
the genuine `wideBlind` of its 8-felt running node and blinding felt in the 8 published columns:
the blinded leaf is forced to commit to the WHOLE member digest, per row. -/
theorem wideBlind_sound (absorb : List ℤ → Digest8) (tbl : Table)
    (hChip : ChipTableSoundN (wPermOut absorb) tbl) (a : Assignment)
    (hB : (chipLookupTupleN wBlindIns (wCols wBLINDED)).map (·.eval a) ∈ tbl) :
    wVal a wBLINDED = wideBlind absorb (wVal a wCUR) (a wBLINDING) := by
  have hadm : ChipArityAdmitted wBlindIns.length := of_decide_eq_true (Eq.refl true)
  have h := chip_lookup_sound_N (wPermOut absorb) tbl hChip a _ _ hadm hB
  rw [wCols_map, wBlindIns_eval] at h
  exact List.ofFn_inj.mp h

/-! ## §4 — the 8-lane chain continuity + the 16 PI pins. -/

/-- Lane `k`'s cross-row continuity window: `next.cur[k] - this.par[k]`. ⚑ `GateExpr.gThread`. -/
def wContWindow (k : Fin 8) : WindowExpr :=
  Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toWindow
    (Dregg2.Circuit.GateExpr.gThread (wCUR k) (wPAR k))

theorem wContWindow_eq (k : Fin 8) :
    wContWindow k = WindowExpr.add (.nxt (wCUR k)) (.mul (.const (-1)) (.loc (wPAR k))) := rfl

/-- The 8 continuity window gates — the level chain rides EVERY lane of the digest, where the
deployed family chains lane 0 only. -/
def wContinuity : List VmConstraint2 :=
  (List.finRange 8).map fun k => .windowGate ⟨wContWindow k, true⟩

/-- Lane `k`'s continuity body vanishes exactly when that lane chains. -/
theorem wCont_zero_iff (k : Fin 8) (env : VmRowEnv) :
    (wContWindow k).eval env = 0 ↔ env.nxt (wCUR k) = env.loc (wPAR k) := by
  simp only [wContWindow_eq, WindowExpr.eval]
  constructor <;> intro h <;> omega

/-- **The widened chain, at `Digest8`**: all 8 continuity windows vanish iff the next row's
8-felt running node IS this row's 8-felt parent. The interior of the tree is chained at full
digest width — the property whose absence made the deployed interior ~31-bit. -/
theorem wCont_all_zero_iff (env : VmRowEnv) :
    (∀ k : Fin 8, (wContWindow k).eval env = 0)
      ↔ wVal env.nxt wCUR = wVal env.loc wPAR := by
  constructor
  · intro h
    funext k
    exact (wCont_zero_iff k env).mp (h k)
  · intro h k
    exact (wCont_zero_iff k env).mpr (congrFun h k)

/-- The 8 blinded-leaf pins: row-0 published blinded lane `k` = PI `k` (leaf + blinding HIDDEN;
only the blinded image is public — the unlinkable commitment, now full-width). -/
def wBlindedLeafPins : List VmConstraint2 :=
  (List.finRange 8).map fun k => .base (.piBinding VmRow.first (wBLINDED k) (wPI_BLINDED k))
/-- The 8 root pins: last-row parent lane `k` = PI `8 + k`. -/
def wRootPins : List VmConstraint2 :=
  (List.finRange 8).map fun k => .base (.piBinding VmRow.last (wPAR k) (wPI_ROOT k))

/-! ## §5 — the descriptor. -/

/-- The per-row transition gates (bit-binary + the 32 per-lane child selections). -/
def wPerRowGates : List VmConstraint2 :=
  wPerRowBodies.map fun b => .base (.gate b)

/-- The last-row re-lowering of the per-row bodies (transition gates are vacuous on the last row;
without this the top level's bits + children would be unconstrained — the deployed family's
last-row-repair shape). -/
def wLastRowBoundaries : List VmConstraint2 :=
  wPerRowBodies.map fun b => .base (.boundary VmRow.last b)

/-- The complete wide blinded constraint block: per-row gates, the three fold lookups + the wide
blinding tooth, the 8-lane continuity, the 16 PI pins, the last-row re-lowerings. -/
def wideConstraints : List VmConstraint2 :=
  wPerRowGates ++ [wStageLLookup, wStageRLookup, wParentLookup, wBlindLookup]
    ++ wContinuity ++ wBlindedLeafPins ++ wRootPins ++ wLastRowBoundaries

/-- **`blindedMembershipWideDesc`** — the WIDE, depth-general, 4-ary BLINDED ring-membership
descriptor: 8-felt nodes, 8-lane node fold, 8-lane chain, full-preimage blinding tooth,
`[blinded0..7, root0..7]` PIs; leaf digest and blinding factor HIDDEN (unlinkability preserved).
Tree depth is the trace height; the algebra is uniform for every supported power-of-two depth,
exactly as the deployed narrow family's. The staged-additive twin of
`blindedMembership4aryDesc`. -/
def blindedMembershipWideDesc : EffectVmDescriptor2 :=
  { name        := "dregg-blinded-membership-4ary-wide-general::v1"
  , traceWidth  := BLINDED_WIDE_WIDTH
  , piCount     := BLINDED_WIDE_PI_COUNT
  , tables      := []
  , constraints := wideConstraints
  , hashSites   := []
  , ranges      := [] }

theorem descriptor_has_complete_shape :
    blindedMembershipWideDesc.constraints =
      wPerRowGates ++ [wStageLLookup, wStageRLookup, wParentLookup, wBlindLookup]
        ++ wContinuity ++ wBlindedLeafPins ++ wRootPins ++ wLastRowBoundaries := rfl

-- Non-vacuous structural pins.
#guard blindedMembershipWideDesc.traceWidth == 99
#guard blindedMembershipWideDesc.piCount == 16
#guard blindedMembershipWideDesc.constraints.length == 96
#guard blindedMembershipWideDesc.tables.length == 0
#guard wPerRowBodies.length == 34
#guard (wStageIns wC0 wC1).length == 16
#guard wBlindIns.length == 11
#guard (chipLookupTupleN (wStageIns wC0 wC1) (wCols wH01)).length == 25
#guard (chipLookupTupleN wBlindIns (wCols wBLINDED)).length == 25
#guard wCols wCUR == [0, 1, 2, 3, 4, 5, 6, 7]
#guard wCols wPAR == [82, 83, 84, 85, 86, 87, 88, 89]
#guard wCols wBLINDED == [91, 92, 93, 94, 95, 96, 97, 98]

-- The staged-additive adjacency: the deployed narrow family this file replaces-at-cutover pins
-- ONE felt each for blinded leaf and root; the wide twin pins 8 + 8. Distinct names, distinct VKs.
#guard (blindedMembership4aryDesc 8).piCount == 2
#guard (blindedMembership4aryDesc 8).traceWidth == 27
#guard (blindedMembership4aryDesc 8).name != blindedMembershipWideDesc.name

-- Continuity non-vacuity: lane 0 accepts a chained window and rejects an unchained one.
#guard decide ((wContWindow 0).eval
  ⟨fun i => if i = wPAR 0 then 7 else 0, fun i => if i = wCUR 0 then 7 else 0, fun _ => 0, fun _ => 0⟩ = 0)
#guard decide (¬ ((wContWindow 0).eval
  ⟨fun _ => 0, fun i => if i = wCUR 0 then 7 else 0, fun _ => 0, fun _ => 0⟩ = 0))
-- The emitted-level interior canary: a next row that copies the parent's lane 0 but drops its
-- lane 7 satisfies the lane-0 window and FAILS the lane-7 window — the assignment class the
-- deployed single-window continuity admits wholesale is refused by the wide block.
#guard decide ((wContWindow 0).eval
  ⟨fun i => if i = wPAR 0 then 7 else if i = wPAR 7 then 9 else 0,
   fun i => if i = wCUR 0 then 7 else 0, fun _ => 0, fun _ => 0⟩ = 0)
#guard decide (¬ ((wContWindow 7).eval
  ⟨fun i => if i = wPAR 0 then 7 else if i = wPAR 7 then 9 else 0,
   fun i => if i = wCUR 0 then 7 else 0, fun _ => 0, fun _ => 0⟩ = 0))

/-! ## §6 — the byte-pinned wire golden (generated once via `#eval repr (emitVmJson2 …)`;
the Rust decoder ingests THIS string at the coordinated cutover). -/

/-- Exact emitted-wire golden (generated via `#eval repr (emitVmJson2 blindedMembershipWideDesc)`).
Rust includes these bytes verbatim at the coordinated cutover. -/
def BLINDED_MEMBERSHIP_WIDE_GOLDEN : String :=
  "{\"name\":\"dregg-blinded-membership-4ary-wide-general::v1\",\"ir\":2,\"trace_width\":99,\"public_input_count\":16,\"challenges\":0,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"var\",\"v\":33}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":34},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":58},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":24}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":24}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":51},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":25}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":25}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":36},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":60},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":26}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":26}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":11}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":27}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":27}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":12}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":46},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":54},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":28}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":28}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":13}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":47},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":55},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":29}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":29}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":40},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":14}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":56},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":30}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":30}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":41},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":15}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":49},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":57},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":65},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":31}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":31}}}}}}},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":16},{\"t\":\"var\",\"v\":34},{\"t\":\"var\",\"v\":35},{\"t\":\"var\",\"v\":36},{\"t\":\"var\",\"v\":37},{\"t\":\"var\",\"v\":38},{\"t\":\"var\",\"v\":39},{\"t\":\"var\",\"v\":40},{\"t\":\"var\",\"v\":41},{\"t\":\"var\",\"v\":42},{\"t\":\"var\",\"v\":43},{\"t\":\"var\",\"v\":44},{\"t\":\"var\",\"v\":45},{\"t\":\"var\",\"v\":46},{\"t\":\"var\",\"v\":47},{\"t\":\"var\",\"v\":48},{\"t\":\"var\",\"v\":49},{\"t\":\"var\",\"v\":66},{\"t\":\"var\",\"v\":67},{\"t\":\"var\",\"v\":68},{\"t\":\"var\",\"v\":69},{\"t\":\"var\",\"v\":70},{\"t\":\"var\",\"v\":71},{\"t\":\"var\",\"v\":72},{\"t\":\"var\",\"v\":73}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":16},{\"t\":\"var\",\"v\":50},{\"t\":\"var\",\"v\":51},{\"t\":\"var\",\"v\":52},{\"t\":\"var\",\"v\":53},{\"t\":\"var\",\"v\":54},{\"t\":\"var\",\"v\":55},{\"t\":\"var\",\"v\":56},{\"t\":\"var\",\"v\":57},{\"t\":\"var\",\"v\":58},{\"t\":\"var\",\"v\":59},{\"t\":\"var\",\"v\":60},{\"t\":\"var\",\"v\":61},{\"t\":\"var\",\"v\":62},{\"t\":\"var\",\"v\":63},{\"t\":\"var\",\"v\":64},{\"t\":\"var\",\"v\":65},{\"t\":\"var\",\"v\":74},{\"t\":\"var\",\"v\":75},{\"t\":\"var\",\"v\":76},{\"t\":\"var\",\"v\":77},{\"t\":\"var\",\"v\":78},{\"t\":\"var\",\"v\":79},{\"t\":\"var\",\"v\":80},{\"t\":\"var\",\"v\":81}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":16},{\"t\":\"var\",\"v\":66},{\"t\":\"var\",\"v\":67},{\"t\":\"var\",\"v\":68},{\"t\":\"var\",\"v\":69},{\"t\":\"var\",\"v\":70},{\"t\":\"var\",\"v\":71},{\"t\":\"var\",\"v\":72},{\"t\":\"var\",\"v\":73},{\"t\":\"var\",\"v\":74},{\"t\":\"var\",\"v\":75},{\"t\":\"var\",\"v\":76},{\"t\":\"var\",\"v\":77},{\"t\":\"var\",\"v\":78},{\"t\":\"var\",\"v\":79},{\"t\":\"var\",\"v\":80},{\"t\":\"var\",\"v\":81},{\"t\":\"var\",\"v\":82},{\"t\":\"var\",\"v\":83},{\"t\":\"var\",\"v\":84},{\"t\":\"var\",\"v\":85},{\"t\":\"var\",\"v\":86},{\"t\":\"var\",\"v\":87},{\"t\":\"var\",\"v\":88},{\"t\":\"var\",\"v\":89}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":11},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":1},{\"t\":\"var\",\"v\":2},{\"t\":\"var\",\"v\":3},{\"t\":\"var\",\"v\":4},{\"t\":\"var\",\"v\":5},{\"t\":\"var\",\"v\":6},{\"t\":\"var\",\"v\":7},{\"t\":\"var\",\"v\":90},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":91},{\"t\":\"var\",\"v\":92},{\"t\":\"var\",\"v\":93},{\"t\":\"var\",\"v\":94},{\"t\":\"var\",\"v\":95},{\"t\":\"var\",\"v\":96},{\"t\":\"var\",\"v\":97},{\"t\":\"var\",\"v\":98}]},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":82}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":83}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":84}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":85}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":86}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":87}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":88}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":89}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":91,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":92,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":93,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":94,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":95,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":96,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":97,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":98,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":82,\"pi_index\":8},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":83,\"pi_index\":9},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":84,\"pi_index\":10},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":85,\"pi_index\":11},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":86,\"pi_index\":12},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":87,\"pi_index\":13},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":88,\"pi_index\":14},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":89,\"pi_index\":15},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"var\",\"v\":33}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":34},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":42},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":58},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":24}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":24}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":43},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":51},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":59},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":25}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":25}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":36},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":44},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":60},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":26}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":26}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":11}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":45},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":61},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":27}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":27}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":12}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":46},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":54},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":62},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":28}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":28}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":13}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":47},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":55},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":63},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":29}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":29}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":40},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":14}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":48},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":56},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":64},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":30}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":30}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":41},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":15}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":49},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":57},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}}},\"r\":{\"t\":\"var\",\"v\":33}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}}}}}}},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":65},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":31}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":31}}}}}}}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 blindedMembershipWideDesc == BLINDED_MEMBERSHIP_WIDE_GOLDEN

/-! ## §7 — the anti-masquerade teeth (collision-extraction discipline).

The injectivity-hypothesis style is REFUTED at deployed parameters (`Compress8CR` is false for
the real chip — it compresses `List ℤ` into 8 bounded lanes), so both teeth follow the
`DeployedCapTree` `…_binds_or_collides` discipline: conclusions hand back the SPECIFIC colliding
pair a total extractor returns, never a bare `∃`. -/

/-- The deployed 1-felt blinded node fold, stated of the same 8-felt data: absorb ONLY lane 0 of
each child (the deployed `gParentLookup` absorbs the four single child columns; arity 4). Lanes
1..7 never enter the preimage. -/
def narrowFold4Lane0 (absorb : List ℤ → Digest8) (c0 c1 c2 c3 : Digest8) : Digest8 :=
  absorb [c0 0, c1 0, c2 0, c3 0]

/-- The wide-fold collision extractor: given two child quadruples with equal wide parents but
unequal data, returns the specific stage preimage pair that collides. Total; branches are
decidable. -/
def wideFoldColl8Find (absorb : List ℤ → Digest8)
    (c0 c1 c2 c3 c0' c1' c2' c3' : Digest8) : List ℤ × List ℤ :=
  if pack8 c0 c1 ≠ pack8 c0' c1' ∧ absorb (pack8 c0 c1) = absorb (pack8 c0' c1') then
    (pack8 c0 c1, pack8 c0' c1')
  else if pack8 c2 c3 ≠ pack8 c2' c3' ∧ absorb (pack8 c2 c3) = absorb (pack8 c2' c3') then
    (pack8 c2 c3, pack8 c2' c3')
  else
    (pack8 (absorb (pack8 c0 c1)) (absorb (pack8 c2 c3)),
     pack8 (absorb (pack8 c0' c1')) (absorb (pack8 c2' c3')))

/-- **`wideFold4_binds_or_collides`** — equal wide parents EITHER force all four 8-felt children
equal, OR the extractor's pair is a genuine full-width chip collision, handed back by name. The
blinded family's fold rides the identical two-stage algebra, so the lemma is the same object as
the plain wide membership's. -/
theorem wideFold4_binds_or_collides (absorb : List ℤ → Digest8)
    (c0 c1 c2 c3 c0' c1' c2' c3' : Digest8)
    (heq : wideFold4 absorb c0 c1 c2 c3 = wideFold4 absorb c0' c1' c2' c3') :
    (c0 = c0' ∧ c1 = c1' ∧ c2 = c2' ∧ c3 = c3')
      ∨ Coll8 absorb (wideFoldColl8Find absorb c0 c1 c2 c3 c0' c1' c2' c3') := by
  by_cases hb : c0 = c0' ∧ c1 = c1' ∧ c2 = c2' ∧ c3 = c3'
  · exact Or.inl hb
  right
  unfold wideFoldColl8Find
  by_cases hL : pack8 c0 c1 ≠ pack8 c0' c1' ∧ absorb (pack8 c0 c1) = absorb (pack8 c0' c1')
  · rw [if_pos hL]
    exact ⟨hL.1, hL.2⟩
  rw [if_neg hL]
  by_cases hR : pack8 c2 c3 ≠ pack8 c2' c3' ∧ absorb (pack8 c2 c3) = absorb (pack8 c2' c3')
  · rw [if_pos hR]
    exact ⟨hR.1, hR.2⟩
  rw [if_neg hR]
  refine ⟨?_, heq⟩
  intro hpk
  obtain ⟨hLL, hRR⟩ := pack8_inj hpk
  have hxy : pack8 c0 c1 = pack8 c0' c1' := by
    by_contra hne
    exact hL ⟨hne, hLL⟩
  have hzw : pack8 c2 c3 = pack8 c2' c3' := by
    by_contra hne
    exact hR ⟨hne, hRR⟩
  obtain ⟨h0, h1⟩ := pack8_inj hxy
  obtain ⟨h2, h3⟩ := pack8_inj hzw
  exact hb ⟨h0, h1, h2, h3⟩

/-- **⚑ THE ANTI-MASQUERADE TOOTH (interior fold).** Fix two child quadruples that agree on EVERY
lane 0 (so the deployed 1-felt blinded fold cannot tell them apart) but differ at lane `j` of the
first child — the interior-forge class wound #2 names. Field-faithfully:

1. the deployed lane-0 fold is BLIND: its outputs are literally equal — the forge is free; and
2. the WIDE fold REFUSES: if the wide parents are equal too, the extractor's pair is a genuine
   full-width chip collision. The forge now costs a real Poseidon2 collision over the full
   32-felt preimage domain instead of nothing.

(The hypotheses are jointly satisfiable exactly for `j ≠ 0` — the canaries below exhibit a
satisfying instance at `j = 1`.) -/
theorem interior_forge_narrow_admits_wide_refuses (absorb : List ℤ → Digest8)
    {c0 c1 c2 c3 c0' c1' c2' c3' : Digest8} (j : Fin 8)
    (hlane0 : c0 0 = c0' 0 ∧ c1 0 = c1' 0 ∧ c2 0 = c2' 0 ∧ c3 0 = c3' 0)
    (hdiff : c0 j ≠ c0' j) :
    narrowFold4Lane0 absorb c0 c1 c2 c3 = narrowFold4Lane0 absorb c0' c1' c2' c3'
    ∧ (wideFold4 absorb c0 c1 c2 c3 = wideFold4 absorb c0' c1' c2' c3' →
        Coll8 absorb (wideFoldColl8Find absorb c0 c1 c2 c3 c0' c1' c2' c3')) := by
  constructor
  · unfold narrowFold4Lane0
    rw [hlane0.1, hlane0.2.1, hlane0.2.2.1, hlane0.2.2.2]
  · intro heq
    rcases wideFold4_binds_or_collides absorb c0 c1 c2 c3 c0' c1' c2' c3' heq with hbind | hcoll
    · exact absurd (congrFun hbind.1 j) hdiff
    · exact hcoll

/-- The deployed 1-felt blinding tooth, stated of the same 8-felt leaf: absorb ONLY lane 0 (the
deployed `gBlindLookup` absorbs `[gCUR, gBLINDING]`; arity 2). Lanes 1..7 of the member digest
never enter the published commitment's preimage. -/
def narrowBlindLane0 (absorb : List ℤ → Digest8) (leaf : Digest8) (r : ℤ) : Digest8 :=
  absorb [leaf 0, r]

/-- The blinding collision extractor: single stage, so the pair IS the two absorb blocks. -/
def wideBlindColl8Find (leaf leaf' : Digest8) (r r' : ℤ) : List ℤ × List ℤ :=
  (packBlind leaf r, packBlind leaf' r')

/-- **`wideBlind_binds_or_collides`** — equal wide blinded leaves EITHER force leaf and blinding
equal, OR the extractor's pair is a genuine full-width chip collision, handed back by name. -/
theorem wideBlind_binds_or_collides (absorb : List ℤ → Digest8)
    (leaf leaf' : Digest8) (r r' : ℤ)
    (heq : wideBlind absorb leaf r = wideBlind absorb leaf' r') :
    (leaf = leaf' ∧ r = r') ∨ Coll8 absorb (wideBlindColl8Find leaf leaf' r r') := by
  by_cases hb : leaf = leaf' ∧ r = r'
  · exact Or.inl hb
  · right
    refine ⟨?_, heq⟩
    intro hpk
    exact hb (packBlind_inj hpk)

/-- **⚑ THE ANTI-MASQUERADE TOOTH (blinding boundary).** Fix two member digests agreeing at lane
0 but differing at lane `j`, and any blinding factor. Field-faithfully:

1. the deployed lane-0 blinding is BLIND: both members publish the SAME blinded leaf under the
   same factor — a lane-0-colliding non-member presents as the member for free; and
2. the WIDE blinding REFUSES: equal wide blinded leaves hand back a genuine chip collision on the
   full 9-felt preimage `leaf8 ‖ blinding`. The published commitment now binds all ~124 bits of
   the member digest. -/
theorem blinded_leaf_forge_narrow_admits_wide_refuses (absorb : List ℤ → Digest8)
    {leaf leaf' : Digest8} (r : ℤ) (j : Fin 8)
    (hlane0 : leaf 0 = leaf' 0) (hdiff : leaf j ≠ leaf' j) :
    narrowBlindLane0 absorb leaf r = narrowBlindLane0 absorb leaf' r
    ∧ (wideBlind absorb leaf r = wideBlind absorb leaf' r →
        Coll8 absorb (wideBlindColl8Find leaf leaf' r r)) := by
  constructor
  · unfold narrowBlindLane0
    rw [hlane0]
  · intro heq
    rcases wideBlind_binds_or_collides absorb leaf leaf' r r heq with hbind | hcoll
    · exact absurd (congrFun hbind.1 j) hdiff
    · exact hcoll

-- Satisfiability canaries for the teeth's hypothesis class (a lane-0-agreeing, lane-1-differing
-- pair EXISTS), plus concrete runs of both extractors returning genuine collisions under a toy
-- absorb — the collision disjuncts are inhabited, not free passes.
def toyAbsorb : List ℤ → Digest8 := fun _ _ => 0
def laneForged : Digest8 := fun k => if k.val = 1 then 5 else 0
def laneZero : Digest8 := fun _ => 0
#guard decide (laneForged 0 = laneZero 0)
#guard decide (laneForged 1 ≠ laneZero 1)
#guard decide (wideFold4 toyAbsorb laneForged laneZero laneZero laneZero
  = wideFold4 toyAbsorb laneZero laneZero laneZero laneZero)
#guard decide (Coll8 toyAbsorb
  (wideFoldColl8Find toyAbsorb laneForged laneZero laneZero laneZero
    laneZero laneZero laneZero laneZero))
-- And the blindness half on the same pair: the narrow fold literally cannot see the forge.
#guard decide (narrowFold4Lane0 toyAbsorb laneForged laneZero laneZero laneZero
  = narrowFold4Lane0 toyAbsorb laneZero laneZero laneZero laneZero)
-- The blinding-boundary tooth on the same pair: the deployed lane-0 blinding publishes the SAME
-- commitment for both members (free forge), and the wide extractor's pair is a genuine collision.
#guard decide (narrowBlindLane0 toyAbsorb laneForged 3 = narrowBlindLane0 toyAbsorb laneZero 3)
#guard decide (wideBlind toyAbsorb laneForged 3 = wideBlind toyAbsorb laneZero 3)
#guard decide (Coll8 toyAbsorb (wideBlindColl8Find laneForged laneZero 3 3))

/-! ## §8 — axiom hygiene on the keystones. -/

#assert_axioms descriptor_has_complete_shape
#assert_axioms wChildren_arranged_lane
#assert_axioms wGroups_arranged
#assert_axioms wCont_all_zero_iff
#assert_axioms wideNodeFold_sound
#assert_axioms wideBlind_sound
#assert_axioms wideFold4_binds_or_collides
#assert_axioms wideBlind_binds_or_collides
#assert_axioms interior_forge_narrow_admits_wide_refuses
#assert_axioms blinded_leaf_forge_narrow_admits_wide_refuses

/-! ## §ROM — ⚑ THE ROM SUCCESSORS: the wide blinded surface as REDUCTIONS on the PROVED keyed
floor.

⚑ STATUS (2026-07-24). `wideFold4_binds_or_collides` and `wideBlind_binds_or_collides` are
EXTRACTOR WITNESSES (each hands back the specific colliding pair; the anti-masquerade teeth
`rcases` on them), but as EXPORTED security statements they are shirks: at deployed BabyBear
parameters a chip collision EXISTS by pigeonhole, so each disjunction holds through its right
branch with NO binding. The security statements are THIS section's reductions over ONE sampled
tag-separated oracle (`Crypto.RomHashedLeafOpening.hlFam` with the blinded-leaf block as the leaf
message): `wideBlind_binds_rom` is the single-absorb LEAF carrier binding (the 9-felt
`leaf8 ‖ blinding` block at the ideal width — member digest AND blinding factor both bound), and
`wideFold4_binds_rom` is the TWO-LEVEL 4-ary fold as a chained forgery, closed by the union bound
(`chained_rom_binds`) with the node carrier on BOTH legs — outer pair differs ⇒ outer node
equivocation (the extractor re-queries the two inner digests per side, budget `Q + 4`); outer pair
agrees ⇒ the first differing inner child pair is an inner node equivocation (`mapOut`, budget
`Q`). Floor: `keyedRom_hard` (the birthday bound, a THEOREM). NO refuted floor, NO bare
disjunction; the modelling step is `RomCarrierSites`' labelled idealisation — one 8-felt child
digest is ONE ideal `Fin (2 ^ l)` value, the ~124-bit reading carried in prose, said out loud. -/

section RomSuccessor

open Dregg2.Crypto.RomHashedLeafOpening
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomBindingReduction
  (RomCarrier romCarrierGame RomCarrierEff RomCarrierComp romCarrierAdv)
open Dregg2.Crypto.RomCarrierSites
  (RomForgery RomForgeryEff chained_rom_binds polyBounded_sq_add_two babyBearP babyBearP_pos)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.FloorGames (Adversary gameAdv gameAdv_mem_unit)
open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)

/-- The truncated blinded-leaf block at the ideal width: ONE member digest (an ideal value — the
8-felt `leaf8` idealised, the §-header modelling step) and the BabyBear blinding felt. The
`packBlind leaf r = leaf8 ‖ [r]` layout content: both coordinates bound, by constructor. -/
abbrev BlindLeafRomBlock (l : ℕ) : Type := Fin (2 ^ l) × Fin babyBearP

/-- **THE BLINDED-MEMBERSHIP ROM FAMILY** at tag space `Key`: blinded-leaf blocks ⊕ ordered
node pairs (the deployed 9-vs-16 arity separation, by constructor). -/
abbrev blindRomFamily (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) : KeyedRomFamily :=
  hlFam Key kF kD kN BlindLeafRomBlock (fun _ => inferInstance) (fun _ => inferInstance)

/-- **⚑⚑ THE WIDE BLINDED-LEAF BINDING, AS A REDUCTION ON THE PROVED FLOOR** — the ROM successor
of `wideBlind_binds_or_collides`: every query-bounded forger that equivocates one published
blinded commitment between two DISTINCT `(member digest, blinding)` blocks has NEGLIGIBLE
advantage. The single-absorb leaf carrier (`hlLeaf_binds_rom`); both the member digest AND the
blinding factor are bound. -/
theorem wideBlind_binds_rom (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (romCarrierGame (blindRomFamily Key kF kD kN)
      (hlLeafCarrier Key kF kD kN BlindLeafRomBlock (fun _ => inferInstance)
        (fun _ => inferInstance))))
    (hA : RomCarrierEff (blindRomFamily Key kF kD kN)
      (hlLeafCarrier Key kF kD kN BlindLeafRomBlock (fun _ => inferInstance)
        (fun _ => inferInstance)) Q A) :
    Negl (gameAdv (romCarrierGame (blindRomFamily Key kF kD kN)
      (hlLeafCarrier Key kF kD kN BlindLeafRomBlock (fun _ => inferInstance)
        (fun _ => inferInstance))) A) :=
  hlLeaf_binds_rom Key kF kD kN _ _ _ Q hQ A hA

/-- The node carrier of the blinded family (the `pack8` two-child absorb at the ideal width). -/
abbrev blindNodeCarrier (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) : RomCarrier (blindRomFamily Key kF kD kN) :=
  hlNodeCarrier Key kF kD kN BlindLeafRomBlock (fun _ => inferInstance) (fun _ => inferInstance)

/-- **THE TWO-LEVEL 4-ARY FOLD AT THE SAMPLED ORACLE** — the ROM restatement of
`wideFold4 absorb c0 c1 c2 c3 = absorb (pack8 (absorb (pack8 c0 c1)) (absorb (pack8 c2 c3)))`:
the two inner node digests are genuinely re-absorbed by the outer node query. -/
def fold4Rom (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key) (kN : Nonempty Key)
    (l : ℕ)
    (H : (blindRomFamily Key kF kD kN).toRomFamily.D l
      → (blindRomFamily Key kF kD kN).toRomFamily.R l)
    (t : Key) (q : Fin (2 ^ l) × Fin (2 ^ l) × Fin (2 ^ l) × Fin (2 ^ l)) :
    (blindRomFamily Key kF kD kN).toRomFamily.R l :=
  H (t, Sum.inr (H (t, Sum.inr (q.1, q.2.1)), H (t, Sum.inr (q.2.2.1, q.2.2.2))))

/-- **THE WIDE-FOLD ROM FORGERY** — two DISTINCT child quadruples, one nested wide parent, at the
sampled oracle. -/
def wideFold4RomForgery (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) : RomForgery (blindRomFamily Key kF kD kN) where
  Ans := fun l => Key × (Fin (2 ^ l) × Fin (2 ^ l) × Fin (2 ^ l) × Fin (2 ^ l))
    × (Fin (2 ^ l) × Fin (2 ^ l) × Fin (2 ^ l) × Fin (2 ^ l))
  wins := fun l H a =>
    a.2.1 ≠ a.2.2 ∧ fold4Rom Key kF kD kN l H a.1 a.2.1 = fold4Rom Key kF kD kN l H a.1 a.2.2
  winsDec := fun l _ _ => by
    letI := ((blindRomFamily Key kF kD kN).toRomFamily).rDec l
    exact instDecidableAnd

/-- The inner-leg selection — the first differing inner child pair (a pure post-map; whether it
actually collides is decided by the sampled oracle in the union bound's case split). -/
def fold4InnerSelect (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key) (kN : Nonempty Key)
    (l : ℕ) (a : (wideFold4RomForgery Key kF kD kN).Ans l) :
    (blindNodeCarrier Key kF kD kN).Ctx l
      × (blindNodeCarrier Key kF kD kN).Val l × (blindNodeCarrier Key kF kD kN).Val l :=
  if (a.2.1.1, a.2.1.2.1) ≠ (a.2.2.1, a.2.2.2.1)
  then ((a.1, ()), (a.2.1.1, a.2.1.2.1), (a.2.2.1, a.2.2.2.1))
  else ((a.1, ()), (a.2.1.2.2.1, a.2.1.2.2.2), (a.2.2.2.2.1, a.2.2.2.2.2))

/-- The outer-leg extraction — run the forger, re-query the four inner node points, answer with
the two outer pairs (`bindComp`, budget `Q + 4`). -/
def fold4OuterComp (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key) (kN : Nonempty Key)
    (M : ∀ l, OracleComp ((blindRomFamily Key kF kD kN).toRomFamily.D l)
      ((blindRomFamily Key kF kD kN).toRomFamily.R l)
      ((wideFold4RomForgery Key kF kD kN).Ans l)) :
    RomCarrierComp (blindRomFamily Key kF kD kN) (blindNodeCarrier Key kF kD kN) :=
  fun l => Dregg2.Crypto.RomCarrierSites.OracleComp.bindComp (M l) (fun a =>
    OracleComp.query (a.1, Sum.inr (a.2.1.1, a.2.1.2.1)) (fun d₁ =>
    OracleComp.query (a.1, Sum.inr (a.2.1.2.2.1, a.2.1.2.2.2)) (fun d₂ =>
    OracleComp.query (a.1, Sum.inr (a.2.2.1, a.2.2.2.1)) (fun e₁ =>
    OracleComp.query (a.1, Sum.inr (a.2.2.2.2.1, a.2.2.2.2.2)) (fun e₂ =>
    OracleComp.pure ((a.1, ()), (d₁, d₂), (e₁, e₂)))))))

/-- **⚑⚑ THE WIDE 4-ARY FOLD BINDING, AS A REDUCTION ON THE PROVED FLOOR** — the ROM successor of
`wideFold4_binds_or_collides`: every query-bounded forger that equivocates one nested wide parent
between two DISTINCT child quadruples has NEGLIGIBLE advantage. The union bound over ONE sampled
oracle, node carrier on both legs: outer pairs differ → outer equivocation (re-queried, `Q + 4`);
outer pairs agree → the first differing inner pair is an inner equivocation (`mapOut`, `Q`). -/
theorem wideFold4_binds_rom (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (wideFold4RomForgery Key kF kD kN).game)
    (hA : RomForgeryEff (blindRomFamily Key kF kD kN) (wideFold4RomForgery Key kF kD kN) Q A) :
    Negl (gameAdv (wideFold4RomForgery Key kF kD kN).game A) := by
  obtain ⟨M, hM, hrun⟩ := hA
  refine chained_rom_binds (wideFold4RomForgery Key kF kD kN)
    (blindNodeCarrier Key kF kD kN) (blindNodeCarrier Key kF kD kN)
    Q (fun l => Q l + 2 + 2) hQ
    (polyBounded_sq_add_two _ (polyBounded_sq_add_two _ hQ))
    (hlFam_card_R Key kF kD kN BlindLeafRomBlock (fun _ => inferInstance)
      (fun _ => inferInstance)) A
    (romCarrierAdv _ _ (fun l => Dregg2.Crypto.RomBindingReduction.OracleComp.mapOut
      (fold4InnerSelect Key kF kD kN l) (M l)))
    (romCarrierAdv _ _ (fold4OuterComp Key kF kD kN M))
    ?_
    ⟨fun l => Dregg2.Crypto.RomBindingReduction.OracleComp.mapOut
        (fold4InnerSelect Key kF kD kN l) (M l),
      fun l => Dregg2.Crypto.RomBindingReduction.OracleComp.mapOut_queryBounded _ (hM l),
      fun _ _ => rfl⟩
    ⟨fold4OuterComp Key kF kD kN M,
      fun l => (Dregg2.Crypto.RomCarrierSites.OracleComp.bindComp_queryBounded (hM l)
        (fun a => QueryBounded.query 3 _ _ (fun _ => QueryBounded.query 2 _ _
          (fun _ => QueryBounded.query 1 _ _ (fun _ => QueryBounded.query 0 _ _
          (fun _ => QueryBounded.pure 0 _)))))).mono
        (by show Q l + 4 ≤ Q l + 2 + 2; omega),
      fun _ _ => rfl⟩
  intro l H hwin
  have hArun : A.run l H = (M l).eval H := hrun l H
  set a := A.run l H with ha
  obtain ⟨hne, heq⟩ := hwin
  have hB₁run : (romCarrierAdv _ _ (fun l => Dregg2.Crypto.RomBindingReduction.OracleComp.mapOut
      (fold4InnerSelect Key kF kD kN l) (M l))).run l H
      = fold4InnerSelect Key kF kD kN l a := by
    show (Dregg2.Crypto.RomBindingReduction.OracleComp.mapOut
      (fold4InnerSelect Key kF kD kN l) (M l)).eval H = _
    erw [Dregg2.Crypto.RomBindingReduction.OracleComp.mapOut_eval]
    rw [← hArun]
  have hB₂run : (romCarrierAdv _ _ (fold4OuterComp Key kF kD kN M)).run l H
      = ((a.1, ()),
          (H (a.1, Sum.inr (a.2.1.1, a.2.1.2.1)), H (a.1, Sum.inr (a.2.1.2.2.1, a.2.1.2.2.2))),
          (H (a.1, Sum.inr (a.2.2.1, a.2.2.2.1)),
            H (a.1, Sum.inr (a.2.2.2.2.1, a.2.2.2.2.2)))) := by
    show (fold4OuterComp Key kF kD kN M l).eval H = _
    unfold fold4OuterComp
    erw [Dregg2.Crypto.RomCarrierSites.OracleComp.bindComp_eval]
    rw [← hArun]
    rfl
  by_cases hT :
      ((H (a.1, Sum.inr (a.2.1.1, a.2.1.2.1)), H (a.1, Sum.inr (a.2.1.2.2.1, a.2.1.2.2.2)))
        : Fin (2 ^ l) × Fin (2 ^ l))
      = (H (a.1, Sum.inr (a.2.2.1, a.2.2.2.1)), H (a.1, Sum.inr (a.2.2.2.2.1, a.2.2.2.2.2)))
  · -- the outer pairs AGREE: both inner digests collide pairwise; the first differing inner
    -- child pair is a genuine inner node equivocation.
    refine Or.inl ?_
    rw [hB₁run]
    have h1 : H (a.1, Sum.inr (a.2.1.1, a.2.1.2.1)) = H (a.1, Sum.inr (a.2.2.1, a.2.2.2.1)) :=
      congrArg Prod.fst hT
    have h2 : H (a.1, Sum.inr (a.2.1.2.2.1, a.2.1.2.2.2))
        = H (a.1, Sum.inr (a.2.2.2.2.1, a.2.2.2.2.2)) := congrArg Prod.snd hT
    unfold fold4InnerSelect
    by_cases hL : ((a.2.1.1, a.2.1.2.1) : Fin (2 ^ l) × Fin (2 ^ l))
        ≠ (a.2.2.1, a.2.2.2.1)
    · rw [if_pos hL]
      exact ⟨hL, h1⟩
    · rw [if_neg hL]
      push_neg at hL
      have hR : ((a.2.1.2.2.1, a.2.1.2.2.2) : Fin (2 ^ l) × Fin (2 ^ l))
          ≠ (a.2.2.2.2.1, a.2.2.2.2.2) := by
        intro hr
        apply hne
        have h01 := congrArg Prod.fst hL
        have h02 := congrArg Prod.snd hL
        have h03 := congrArg Prod.fst hr
        have h04 := congrArg Prod.snd hr
        exact Prod.ext h01 (Prod.ext h02 (Prod.ext h03 h04))
      exact ⟨hR, h2⟩
  · -- the outer pairs DIFFER: the two outer node messages are distinct with one digest.
    refine Or.inr ?_
    rw [hB₂run]
    exact ⟨hT, heq⟩

end RomSuccessor

#assert_axioms wideBlind_binds_rom
#assert_axioms wideFold4_binds_rom

end Dregg2.Circuit.Emit.BlindedMembershipWideEmit
