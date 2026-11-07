/-
# `Dregg2.Circuit.StateCommitFloorRegrounded` — the `StateCommit` leaf/log injective floors proved
FALSE at deployed parameters, and their consumers RE-GROUNDED onto a REAL collision-game reduction
carrying an explicit `Eff`.

## The bug this closes (`VACUITY-SWEEP.md` FINDING 2, cluster 2)

`HashFloorHonesty` (2026-07) proved FOUR injectivity floors FALSE for any range-bounded hash and
doc-marked them BROKEN. **It did not sweep the class.** `VACUITY-SWEEP.md` FINDING 2 found ~20 more
carriers with the identical predicate shape, still doc-marked "REALIZABLE", none pointing at the teeth,
**none re-grounded**. Two of them live in `StateCommit.lean` itself — *the same file as two already-flagged
siblings*:

  * `StateCommit.cellLeafInjective CH := ∀ c v w, CH c v = CH c w → v = w`   (`StateCommit.lean:230`)
  * `StateCommit.logHashInjective LH := ∀ xs ys, LH xs = LH ys → xs = ys`    (`StateCommit.lean:238`)

Both are **FALSE at deployed parameters** and §1 proves it: `Value` is infinite (`Value.int` injects `ℤ`),
`List Turn` is infinite, and a real leaf/log hash lands in a BOUNDED BabyBear field — so pigeonhole forces
collisions and the injective floor is unsatisfiable (`cellLeafInjective_false_babyBear`,
`logHashInjective_false_babyBear`). Their consumers — `MovedDigestBindsCells`, `FrameDigestBindsCells`,
`cellDigest_binds_cells`, `recStateCommit_binds_kernel`, `transfer_circuit_full_sound`, and the
`EffectInstances2` / `EffectRefinement` log-growing effects — are therefore **VACUOUSLY TRUE at real
parameters**. `#assert_axioms` is blind to it: the proofs are clean; the *hypothesis* is the flaw.

## ⚑ The `*Realization` bundles are NON-INHABITABLE, which is worse than a hypothesis

`Poseidon2Binding.LeafRealization CH` / `LogRealization LH` carry `spongeCR : Poseidon2SpongeCR sponge`
as a **structure FIELD**, and `HashFloorHonesty.poseidon2SpongeCR_false_babyBear` had **already proved
that field's type FALSE** at BabyBear. So §1's `leafRealization_uninhabitable_babyBear` /
`logRealization_uninhabitable_babyBear` prove a deployed `LeafRealization`/`LogRealization` **value cannot
exist** — this is the `Compress8CR`-in-`Cap8Scheme` shape the sweep flagged as the priority. Every
discharge routed through them (`cellLeafInjective_of_realization`, `logHashInjective_of_realization`, and
`Verify/KeystoneAuditArgusReceipt.LH₀_inj`) is satisfied only by the TOY injective sponge
(`Reference.refLogRealization`, `Encodable.encode`) — verbatim the **FALSE COMFORT**
`HashFloorHonesty`'s own header named: *"toy witness satisfiable; real instantiation false."*

## ⚑ The re-grounding does NOT go through the `⊤`-class floor — that floor is false too

`FloorGames.hashCRHardQuant_top_false_of_compressing` proves `HashCRHardQuant F (fun _ => True)` is
ITSELF FALSE at deployed parameters (the `Classical.choice` finder wins with probability `1` on a
compressing family). That floor used to be spelled `HashFloorHonesty.CollisionResistant F`, which hid
the `⊤` the reader has to see to price the assumption; the `def` is DELETED (2026-07-28) and the tooth
is carried through under the name above, with the `⊤` written out. At the **unrestricted** adversary
class every floor is false-at-deployed or vacuous — `hard_top_iff_solvableFrac_negl` is an `↔`, so no
restatement of the win relation escapes. **The only honest escape is the `Eff` parameter**
(`FloorGames` §8), and this file takes it, exactly as `HermineHashCRRegrounded` does.

So the re-grounded consumers below condition on `HashCRHardQuant F Eff` — the collision floor at a
NAMED, EXPLICIT adversary class — and carry the `Eff`-membership obligation for the finder the reduction
builds, in the open, at the use site.

## The re-grounding, per consumer (§3–§5)

The deployed consumer is `StateCommit.cellDigest_binds_cells` / `recStateCommit_binds_kernel`: "equal
cell-digests force equal cell maps". Its BREAK is a **state-commitment equivocator** — two kernels with
the SAME accounts, both `AccountsWF`, whose cell maps DIFFER yet whose `cellDigest`s agree. §3 makes that
a first-class `Game` (`scEquivGame`) read directly off the deployed `cellDigest`; nothing here is a
docstring.

§4 is the reduction, as four maps of adversaries into three collision games over the SAME sampled
instance space:

  * **`scToOuterNodeAdv`** — the equivocator's two `(frameDigest, movedDigest)` children: a collision of
    the 2-to-1 node hash at the cell-digest root.
  * **`scToMovedNodeAdv`** — its two `(CH src, CH dst)` children: a node collision inside `movedDigest`.
  * **`scToSpongeAdv`** — its two sorted leaf lists: a collision of the frame sponge.
  * **`scToLeafAdv`** — the two `Value`s at the cell where the maps differ (`diffCell`): a collision of
    the LEAF hash — the horn `cellLeafInjective` was carrying for free.

`sc_wins_imp` is the dichotomy: every instance the equivocator wins, one of the four derived finders wins
a genuine collision game — proved by the exhaustive `{src} ∪ {dst} ∪ (accounts \ {src,dst}) ∪ dead`
partition, with the dead-cell case closed by `AccountsWF` on both states (the SAME partition
`cellDigest_binds_cells` runs, contraposed into an extractor). `sc_adv_le` is the union bound over the
shared instance space; `stateCommit_equivocation_advantage_bound` is the keystone: under the collision
floor at the three families the reduction attacks, an equivocator has NEGLIGIBLE advantage.

**This statement is FALSE if you delete the reduction** — the conclusion is about the equivocation game,
the hypotheses about the collision games, and `sc_adv_le` is the only bridge. §6's canary compiles that
fact; it was unwritable under the free `cellLeafInjective` hypothesis.

## Non-fake

The floors are SATISFIABLE (`hard_bot_vacuous`, recorded honestly and worth nothing on its own — the
value of a satisfiability witness is nothing without the refutation beside it) and the derived collision
floors are priced exactly by §7: `Eff := ⊤` makes them FALSE at compressing parameters,
`Eff := ⊥` vacuous. `valueDecEq` is COMPUTABLE, derived from the proven-injective `Poseidon2Binding.Reference.encV`
— no `Classical.decEq` smuggled into the counting. Old injective-floor consumers KEPT untouched; siblings
ADDED. `#assert_all_clean`; no `sorry`, no fresh `axiom`.

## Coordination

This is the COMMIT-STATE lane of the FINDING-2 sweep (`cellLeafInjective`/`logHashInjective`). The factory
content-hash, the 2-to-1 `Compress1CR` and the macaroon binding hash are
`Crypto.FactoryBindingFloorRegrounded` (sibling file, same cluster); `compress4Injective` /
`Poseidon2WideCR` / `Compress8CR` are other lanes'. The commit-reveal side is
`Crypto.HermineHashCRRegrounded`, whose `winProb_le_add_of_imp` union bound this file REUSES rather than
duplicates.
-/
import Dregg2.Crypto.HermineHashCRRegrounded
import Dregg2.Crypto.FloorGames
import Dregg2.Crypto.CostAdversary
import Dregg2.Crypto.CostTactics
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.SpongeForgeReduction
import Dregg2.Circuit.StateCommit

namespace Dregg2.Circuit.StateCommitFloorRegrounded

open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble negl_add negl_zero)
open Dregg2.Crypto.ProbCrypto (winProb negl_of_le)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder collisionAdv not_injective_of_finite_range)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv gameAdv_mem_unit Hard hard_bot_vacuous hashGame HashCRHardQuant
   not_hard_top_of_always_solvable)
open Dregg2.Crypto.HermineHashCRRegrounded (winProb_le_add_of_imp)
open Dregg2.Circuit.StateCommit
  (cellLeafInjective logHashInjective AccountsWF cellDigest frameDigest movedDigest)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR LeafRealization LogRealization)
open Dregg2.Exec
open Dregg2.Crypto.CostAdversary (AnsSize IsPolyTime isPolyTime_inhabited idAdv)

set_option autoImplicit false

/-! ## §1 — FALSIFIABILITY TEETH: the two `StateCommit` floors are FALSE at deployed parameters.

The counting core is `HashFloorHonesty.not_injective_of_finite_range` — an injective function from an
INFINITE domain has an INFINITE range, and a real hash's range is a bounded field. Nobody had tried to
prove THESE two false, which is why the sweep found them still doc-marked "REALIZABLE". -/

/-- A function into a bounded integer window has finite range (`⊆ Ico 0 q`). The general form of
`HashFloorHonesty.finite_range_of_field_bound`, which is specialized to `List ℤ → ℤ`; both leaf
(`Value → ℤ`) and log (`List Turn → ℤ`) hashes need it. -/
theorem finite_range_of_field_window {α : Type*} (f : α → ℤ) (q : ℤ)
    (hb : ∀ x, 0 ≤ f x ∧ f x < q) : (Set.range f).Finite := by
  refine (Set.finite_Ico (0 : ℤ) q).subset ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨(hb x).1, (hb x).2⟩

/-- `Value` is INFINITE — `Value.int` injects all of `ℤ`. This is what makes the leaf floor false: a
cell's `Value` is unbounded data, and a leaf hash pins it into ONE field element. -/
instance : Infinite Value :=
  Infinite.of_injective Value.int (fun _ _ h => by injection h)

/-- `List Turn` is INFINITE (the length-`n` constant lists are distinct). This is what makes the log
floor false: the receipt chain GROWS without bound, and the log hash pins it into ONE field element. -/
instance : Infinite (List Turn) :=
  Infinite.of_injective (fun n : ℕ => List.replicate n (⟨0, 0, 0, 0⟩ : Turn))
    (fun n m h => by have := congrArg List.length h; simpa using this)

/-- **TOOTH 1 — `cellLeafInjective` is FALSE for a range-bounded leaf hash.** At any FIXED cell `c`, the
leaf map `CH c : Value → ℤ` runs the infinite `Value` into a finite set of field elements, so pigeonhole
forces two distinct `Value`s to one leaf — and the floor claims there are none. -/
theorem cellLeafInjective_false_of_finite_range (CH : CellId → Value → ℤ) (c : CellId)
    (hfin : (Set.range (CH c)).Finite) : ¬ cellLeafInjective CH := fun hinj =>
  not_injective_of_finite_range (CH c) hfin (fun v w h => hinj c v w h)

/-- **TOOTH 1 (deployed form) — `cellLeafInjective` is FALSE at the REAL BabyBear parameters.** A leaf
hash whose output is a BabyBear field element (`0 ≤ · < p`, `p = 2³¹ − 2²⁷ + 1`) — i.e. every real
Poseidon2 leaf hash the deployed `recStateCommit` runs — refutes the floor. The floor is not merely
un-proven for the real hash; it is provably FALSE there, exactly as
`HashFloorHonesty.poseidon2SpongeCR_false_babyBear` is for its already-flagged sibling in the same
file. -/
theorem cellLeafInjective_false_babyBear (CH : CellId → Value → ℤ) (c : CellId)
    (hb : ∀ v, 0 ≤ CH c v ∧ CH c v < (2013265921 : ℤ)) : ¬ cellLeafInjective CH :=
  cellLeafInjective_false_of_finite_range CH c (finite_range_of_field_window (CH c) _ hb)

/-- **TOOTH 2 — `logHashInjective` is FALSE for a range-bounded log hash.** The receipt chain
`List Turn` is infinite; a bounded-range accumulator cannot inject it. -/
theorem logHashInjective_false_of_finite_range (LH : List Turn → ℤ)
    (hfin : (Set.range LH).Finite) : ¬ logHashInjective LH := fun hinj =>
  not_injective_of_finite_range LH hfin (fun xs ys h => hinj xs ys h)

/-- **TOOTH 2 (deployed form) — `logHashInjective` is FALSE at the REAL BabyBear parameters.** Every real
Poseidon2 receipt-chain accumulator lands in a BabyBear field element, so the growing-log effects
(`EffectInstances2`, `EffectRefinement`) carry an unsatisfiable hypothesis. -/
theorem logHashInjective_false_babyBear (LH : List Turn → ℤ)
    (hb : ∀ xs, 0 ≤ LH xs ∧ LH xs < (2013265921 : ℤ)) : ¬ logHashInjective LH :=
  logHashInjective_false_of_finite_range LH (finite_range_of_field_window LH _ hb)

/-! ### ⚑ The `*Realization` bundles are NON-INHABITABLE at deployed parameters.

Worse than a false hypothesis on a theorem: `Poseidon2Binding.LeafRealization` / `LogRealization` carry
`spongeCR : Poseidon2SpongeCR sponge` as a structure FIELD, whose type `HashFloorHonesty` had ALREADY
proved false at BabyBear. So a deployed realization VALUE cannot exist, and every discharge routed
through one is satisfied only by the toy injective `Encodable.encode` sponge. This is the
`Compress8CR`-in-`Cap8Scheme` shape the sweep named the priority — here, twice, in the leaf/log tree. -/

/-- **(TOOTH — a deployed `LeafRealization` CANNOT EXIST.)** If the sponge a `LeafRealization` factors
through is BabyBear-range-bounded — which every real Poseidon2 `hash_many` is — the bundle is
uninhabitable: its `spongeCR` field's type is FALSE. So
`Poseidon2Binding.cellLeafInjective_of_realization` discharges `cellLeafInjective` only at a sponge no
deployment runs. -/
theorem leafRealization_uninhabitable_babyBear {CH : CellId → Value → ℤ} (R : LeafRealization CH)
    (hb : ∀ xs, 0 ≤ R.sponge xs ∧ R.sponge xs < (2013265921 : ℤ)) : False :=
  Dregg2.Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear R.sponge hb R.spongeCR

/-- **(TOOTH — a deployed `LogRealization` CANNOT EXIST.)** Same for the log side. In particular
`Verify/KeystoneAuditArgusReceipt.LH₀_inj` — which discharges `logHashInjective` via
`logHashInjective_of_realization refLogRealization` — stands on `Reference.refLogRealization`, whose
sponge IS `Encodable.encode` (injective into ALL of `ℤ`, range NOT bounded). The receipt's carrier is
discharged, and at BabyBear it could not be. -/
theorem logRealization_uninhabitable_babyBear {LH : List Turn → ℤ} (R : LogRealization LH)
    (hb : ∀ xs, 0 ≤ R.sponge xs ∧ R.sponge xs < (2013265921 : ℤ)) : False :=
  Dregg2.Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear R.sponge hb R.spongeCR

/-! ## §2 — the honest floor's carriers: decidable equality, and the union bound.

`KeyedHashFamily` needs `DecidableEq` on its input (the game checks `x ≠ x'`). The tree deliberately has
NO `DecidableEq Value` (`FinKernelStep`, `EffectsAsDataProto`, `FlowRefine` each note the absence). We do
NOT reach for `Classical.decEq`: `Poseidon2Binding.Reference.encV_inj` already proves `encV : Value → ℕ` injective,
so decidable equality on `Value` is COMPUTABLE, and the collision game's counting stays a real finite
count. Kept a plain `def` (NOT an instance) so the tree's deliberate absence is not disturbed. -/

/-- **Decidable equality on `Value`, COMPUTED** — via the proven-injective `Poseidon2Binding.Reference.encV`. Not
an instance (the tree deliberately has none); supplied explicitly to the leaf family below. -/
def valueDecEq : DecidableEq Value := fun v w =>
  decidable_of_iff (Dregg2.Circuit.Poseidon2Binding.Reference.encV v = Dregg2.Circuit.Poseidon2Binding.Reference.encV w)
    ⟨fun h => Dregg2.Circuit.Poseidon2Binding.Reference.encV_inj v w h, fun h => by rw [h]⟩

/-- **THE THREE-HORN UNION BOUND.** `HermineHashCRRegrounded.winProb_le_add_of_imp` peeled once: if every
winning outcome of `f` wins one of `g`, `h`, `k`, then `winProb f ≤ winProb g + (winProb h + winProb k)`.
Reused, not re-proved — the two-horn lemma is the general fact. -/
theorem winProb_le_add3_of_imp {Ω : Type*} [Fintype Ω] {f g h k : Ω → Bool}
    (himp : ∀ o, f o = true → g o = true ∨ h o = true ∨ k o = true) :
    winProb f ≤ winProb g + (winProb h + winProb k) := by
  refine le_trans (winProb_le_add_of_imp (f := f) (g := g) (h := fun o => h o || k o) ?_) ?_
  · intro o ho
    rcases himp o ho with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr (by simp [h2])
    · exact Or.inr (by simp [h3])
  · gcongr
    exact winProb_le_add_of_imp (f := fun o => h o || k o) (g := h) (h := k) (fun o ho => by
      simpa using ho)

/-- **THE FOUR-HORN UNION BOUND.** The same peel once more — the equivocation reduction below has four
horns (two node-hash sites, the frame sponge, and the leaf hash). -/
theorem winProb_le_add4_of_imp {Ω : Type*} [Fintype Ω] {f g h k m : Ω → Bool}
    (himp : ∀ o, f o = true → g o = true ∨ h o = true ∨ k o = true ∨ m o = true) :
    winProb f ≤ winProb g + (winProb h + (winProb k + winProb m)) := by
  refine le_trans (winProb_le_add_of_imp (f := f) (g := g)
    (h := fun o => h o || (k o || m o)) ?_) ?_
  · intro o ho
    rcases himp o ho with h1 | h2 | h3 | h4
    · exact Or.inl h1
    · exact Or.inr (by simp [h2])
    · exact Or.inr (by simp [h3])
    · exact Or.inr (by simp [h4])
  · gcongr
    exact winProb_le_add3_of_imp (f := fun o => h o || (k o || m o)) (g := h) (h := k) (k := m)
      (fun o ho => by
        simp only [Bool.or_eq_true] at ho
        rcases ho with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr h3))

/-! ## §3 — the state-commitment equivocator, as a first-class λ-indexed game.

The deployed consumer is `StateCommit.cellDigest_binds_cells`: equal `cellDigest`s force equal cell maps,
GIVEN `compressInjective compress`, `compressNInjective compressN` and `cellLeafInjective CH` — all three
false at deployed parameters (§1 and `HashFloorHonesty`). Its BREAK is an equivocator: two kernels over
the same accounts, both `AccountsWF`, with DIFFERENT cell maps and EQUAL cell-digests. This section makes
that adversary a `Game` played over a SAMPLED instance, exactly as `HermineHashCRRegrounded`'s
`concurrentForgeryGame` makes a rushing forger one. -/

/-- **THE STATE-COMMITMENT FAMILY.** At each security parameter `l`: a FINITE space of sampled instances,
and per instance the deployed commitment surface — the leaf hash `CH`, the 2-to-1 node hash `compress`,
the frame sponge `compressN`, and the `turn` the commitment is taken at. This carries the deployed data of
`StateCommit.cellDigest` and nothing else. (The instance is the honest home of the domain-separation the
deployed unkeyed Poseidon2 uses as its effective key — `HashFloorHonesty` §2.) -/
structure StateCommitFamily where
  /-- The instance space (domain-separation / commitment-surface sampling). -/
  Inst : ℕ → Type
  /-- The instance space is finite (the game samples a uniform instance). -/
  instFin : ∀ l, Fintype (Inst l)
  /-- The instance space is inhabited (a non-empty outcome space). -/
  instNe : ∀ l, Nonempty (Inst l)
  /-- The per-cell leaf hash at parameter `l`, instance `i`. -/
  CH : ∀ l, Inst l → CellId → Value → ℤ
  /-- The 2-to-1 Merkle node hash at parameter `l`, instance `i`. -/
  compress : ∀ l, Inst l → ℤ → ℤ → ℤ
  /-- The frame sponge over a list of leaves at parameter `l`, instance `i`. -/
  compressN : ∀ l, Inst l → List ℤ → ℤ
  /-- The turn the commitment is taken at (it pins the moved/frame partition). -/
  turn : ∀ l, Inst l → Turn

/-- **THE LEAF-HASH KEYED FAMILY.** Inputs are `(cell, value)` pairs, outputs field elements, and the
keyed hash is the deployed `CH`. A `cellLeafInjective` break at cell `c` — two distinct `Value`s with
equal leaves — IS a collision of this family (the pair `((c,v),(c,w))`). Keys are the SAME sampled
instances as the equivocation game, so the union bound below is over ONE `Ω`. -/
def scLeafFamily (F : StateCommitFamily) : KeyedHashFamily where
  Key := F.Inst
  Input := CellId × Value
  Out := ℤ
  H := fun l i p => F.CH l i p.1 p.2
  keyFintype := F.instFin
  keyNonempty := F.instNe
  inputDecEq := letI := valueDecEq; inferInstance
  outDecEq := inferInstance

/-- **THE NODE-HASH KEYED FAMILY.** Inputs are the 2-to-1 hash's input pairs; the keyed hash is the
deployed `compress`. Both node sites the reduction attacks (the cell-digest root and the `movedDigest`
node) collide in THIS family. -/
def scNodeFamily (F : StateCommitFamily) : KeyedHashFamily where
  Key := F.Inst
  Input := ℤ × ℤ
  Out := ℤ
  H := fun l i p => F.compress l i p.1 p.2
  keyFintype := F.instFin
  keyNonempty := F.instNe
  inputDecEq := inferInstance
  outDecEq := inferInstance

/-- **THE FRAME-SPONGE KEYED FAMILY.** Inputs are sorted leaf lists; the keyed hash is the deployed
`compressN`. The frame horn of the reduction collides here. -/
def scSpongeFamily (F : StateCommitFamily) : KeyedHashFamily where
  Key := F.Inst
  Input := List ℤ
  Out := ℤ
  H := fun l i xs => F.compressN l i xs
  keyFintype := F.instFin
  keyNonempty := F.instNe
  inputDecEq := inferInstance
  outDecEq := inferInstance

/-- The frame carrier at an instance: the live accounts MINUS the two moved cells — the carrier
`StateCommit.cellDigest` partitions over. -/
def scCarrier (F : StateCommitFamily) (l : ℕ) (i : F.Inst l) (k : RecordKernelState) : Finset CellId :=
  k.accounts \ {(F.turn l i).src, (F.turn l i).dst}

/-- The two children of the cell-digest ROOT node: `(frameDigest, movedDigest)`. `scCellDigest_eq` pins
that `cellDigest` IS `compress` of this pair — so an equivocation is a collision at THIS node whenever the
pairs differ. -/
def scOuterPair (F : StateCommitFamily) (l : ℕ) (i : F.Inst l) (k : RecordKernelState) : ℤ × ℤ :=
  (frameDigest (F.CH l i) (F.compressN l i) k (scCarrier F l i k),
   movedDigest (F.CH l i) (F.compress l i) k.cell (F.turn l i).src (F.turn l i).dst)

/-- The two children of the `movedDigest` node: the `src`/`dst` LEAVES. -/
def scMovedPair (F : StateCommitFamily) (l : ℕ) (i : F.Inst l) (f : CellId → Value) : ℤ × ℤ :=
  (F.CH l i (F.turn l i).src (f (F.turn l i).src),
   F.CH l i (F.turn l i).dst (f (F.turn l i).dst))

/-- The frame sponge's INPUT: the untouched cells' leaves in CANONICAL (sorted) order. -/
def scFrameList (F : StateCommitFamily) (l : ℕ) (i : F.Inst l) (k : RecordKernelState) : List ℤ :=
  ((scCarrier F l i k).sort (· ≤ ·)).map (fun c => F.CH l i c (k.cell c))

/-- **THE DEPLOYED `cellDigest` IS `compress` OF THE OUTER PAIR** — by `rfl`, straight off
`StateCommit.cellDigest`. The reduction's node horn attacks this equation, not a paraphrase of it. -/
theorem scCellDigest_eq (F : StateCommitFamily) (l : ℕ) (i : F.Inst l) (k : RecordKernelState) :
    cellDigest (F.CH l i) (F.compress l i) (F.compressN l i) k (F.turn l i)
      = F.compress l i (scOuterPair F l i k).1 (scOuterPair F l i k).2 := rfl

/-- **THE DEPLOYED `movedDigest` IS `compress` OF THE MOVED PAIR** — by `rfl`. -/
theorem scMovedDigest_eq (F : StateCommitFamily) (l : ℕ) (i : F.Inst l) (f : CellId → Value) :
    movedDigest (F.CH l i) (F.compress l i) f (F.turn l i).src (F.turn l i).dst
      = F.compress l i (scMovedPair F l i f).1 (scMovedPair F l i f).2 := rfl

/-- **THE DEPLOYED `frameDigest` IS `compressN` OF THE FRAME LIST** — by `rfl`. -/
theorem scFrameDigest_eq (F : StateCommitFamily) (l : ℕ) (i : F.Inst l) (k : RecordKernelState) :
    frameDigest (F.CH l i) (F.compressN l i) k (scCarrier F l i k)
      = F.compressN l i (scFrameList F l i k) := rfl

/-- **THE STATE-COMMITMENT EQUIVOCATION GAME.** The adversary is handed a sampled commitment surface and
WINS iff it outputs two kernels that are `AccountsWF`, agree on `accounts`, DIFFER on the cell map, and
yet have EQUAL `cellDigest`s. Winning this game is exactly breaking the deployed binding
`StateCommit.cellDigest_binds_cells` claims — the break is IN the win predicate, read off the real
`cellDigest`. (`winsDec` is classical: `AccountsWF` and cell-map inequality quantify over the infinite
`CellId`, so they are genuine propositions with no computable decider. The counting is unaffected — the
instance space is what is finite and sampled.) -/
noncomputable def scEquivGame (F : StateCommitFamily) : Game where
  Inst := F.Inst
  Ans := fun _ => RecordKernelState × RecordKernelState
  instFin := F.instFin
  instNe := F.instNe
  wins := fun l i p =>
    AccountsWF p.1 ∧ AccountsWF p.2 ∧ p.1.accounts = p.2.accounts ∧ p.1.cell ≠ p.2.cell ∧
      cellDigest (F.CH l i) (F.compress l i) (F.compressN l i) p.1 (F.turn l i)
        = cellDigest (F.CH l i) (F.compress l i) (F.compressN l i) p.2 (F.turn l i)
  winsDec := fun _ _ _ => Classical.propDecidable _

/-- **THE PROBLEM IS IN THE STATEMENT** — the equivocation game's win relation is a genuine break of the
deployed cell-digest binding. -/
theorem scEquivGame_wins_iff (F : StateCommitFamily) (l : ℕ) (i : F.Inst l)
    (p : RecordKernelState × RecordKernelState) :
    (scEquivGame F).wins l i p ↔
      (AccountsWF p.1 ∧ AccountsWF p.2 ∧ p.1.accounts = p.2.accounts ∧ p.1.cell ≠ p.2.cell ∧
        cellDigest (F.CH l i) (F.compress l i) (F.compressN l i) p.1 (F.turn l i)
          = cellDigest (F.CH l i) (F.compress l i) (F.compressN l i) p.2 (F.turn l i)) :=
  Iff.rfl

/-! ## §4 — the reduction: four maps of adversaries, and the dichotomy.

`StateCommit.cellDigest_binds_cells` walks the exhaustive partition `{src} ∪ {dst} ∪ (accounts\{src,dst})
∪ dead` and uses the three injectivity floors to force equality at each. CONTRAPOSED, that walk is an
EXTRACTOR: wherever the cell maps differ, the equal digests hand back a collision at one of three real
hash sites. These are the maps. -/

/-- A cell where two cell maps DIFFER. `Classical.epsilon` on the `∃` that `funext` contraposes to — the
adversary must be TOTAL, so on agreeing maps this is junk, which is real and harmless (the reduction only
ever reads it under a winning `p.1.cell ≠ p.2.cell`). -/
noncomputable def diffCell (f g : CellId → Value) : CellId :=
  Classical.epsilon (fun c => f c ≠ g c)

/-- `diffCell` really does find a difference when there is one — `funext`, contraposed. -/
theorem diffCell_spec {f g : CellId → Value} (hne : f ≠ g) :
    f (diffCell f g) ≠ g (diffCell f g) := by
  have hex : ∃ c, f c ≠ g c := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  exact Classical.epsilon_spec hex

/-- **HORN 1 — the ROOT node collision, as a map of adversaries.** The equivocator's two
`(frameDigest, movedDigest)` children. Equal cell-digests mean `compress` agrees on them; if the pairs
differ, that IS a node-hash collision. -/
noncomputable def scToOuterNodeAdv (F : StateCommitFamily) (A : Adversary (scEquivGame F)) :
    Adversary (hashGame (scNodeFamily F)) where
  run := fun l i => let p := A.run l i; (scOuterPair F l i p.1, scOuterPair F l i p.2)

/-- **HORN 2 — the `movedDigest` node collision, as a map of adversaries.** The two `(CH src, CH dst)`
leaf pairs of the moved node. -/
noncomputable def scToMovedNodeAdv (F : StateCommitFamily) (A : Adversary (scEquivGame F)) :
    Adversary (hashGame (scNodeFamily F)) where
  run := fun l i => let p := A.run l i; (scMovedPair F l i p.1.cell, scMovedPair F l i p.2.cell)

/-- **HORN 3 — the frame-sponge collision, as a map of adversaries.** The two sorted leaf lists over the
untouched carrier. -/
noncomputable def scToSpongeAdv (F : StateCommitFamily) (A : Adversary (scEquivGame F)) :
    Adversary (hashGame (scSpongeFamily F)) where
  run := fun l i => let p := A.run l i; (scFrameList F l i p.1, scFrameList F l i p.2)

/-- **HORN 4 — the LEAF collision, as a map of adversaries — the horn `cellLeafInjective` was carrying
for free.** At the cell where the two maps differ, the two `Value`s. When the node/sponge horns close,
these two DISTINCT values have EQUAL leaves: precisely a `cellLeafInjective` counterexample, now a
collision the floor must pay for. -/
noncomputable def scToLeafAdv (F : StateCommitFamily) (A : Adversary (scEquivGame F)) :
    Adversary (hashGame (scLeafFamily F)) where
  run := fun l i =>
    let p := A.run l i
    let c := diffCell p.1.cell p.2.cell
    ((c, p.1.cell c), (c, p.2.cell c))

/-- **⚑ THE DICHOTOMY, ON A CLAIM — and this is `cellDigest_binds_cells`, contraposed.** Wherever an
equivocator wins, the equal cell-digests force a collision at ONE of the four real hash sites: the root
node, the moved node, the frame sponge, or the LEAF. Proved by the SAME exhaustive partition
`StateCommit.cellDigest_binds_cells` runs — `{src}`, `{dst}`, the untouched carrier, and the dead cells
(closed by `AccountsWF` on BOTH states, so a dead cell cannot be the difference). The hash content lives
in proof terms, not in a sentence about them. -/
theorem sc_claim_wins_imp (F : StateCommitFamily) (l : ℕ) (i : F.Inst l)
    (p : RecordKernelState × RecordKernelState) (hwin : (scEquivGame F).wins l i p) :
    (scOuterPair F l i p.1 ≠ scOuterPair F l i p.2 ∧
        F.compress l i (scOuterPair F l i p.1).1 (scOuterPair F l i p.1).2
          = F.compress l i (scOuterPair F l i p.2).1 (scOuterPair F l i p.2).2)
      ∨ (scMovedPair F l i p.1.cell ≠ scMovedPair F l i p.2.cell ∧
        F.compress l i (scMovedPair F l i p.1.cell).1 (scMovedPair F l i p.1.cell).2
          = F.compress l i (scMovedPair F l i p.2.cell).1 (scMovedPair F l i p.2.cell).2)
      ∨ (scFrameList F l i p.1 ≠ scFrameList F l i p.2 ∧
        F.compressN l i (scFrameList F l i p.1) = F.compressN l i (scFrameList F l i p.2))
      ∨ (let c := diffCell p.1.cell p.2.cell
         ((c, p.1.cell c) ≠ (c, p.2.cell c) ∧ F.CH l i c (p.1.cell c) = F.CH l i c (p.2.cell c))) := by
  obtain ⟨hwf, hwf', hAcc, hcellne, hcd⟩ := hwin
  set c := diffCell p.1.cell p.2.cell with hcdef
  have hc : p.1.cell c ≠ p.2.cell c := diffCell_spec hcellne
  -- the cell-digest equality, read at the root node.
  have hroot : F.compress l i (scOuterPair F l i p.1).1 (scOuterPair F l i p.1).2
      = F.compress l i (scOuterPair F l i p.2).1 (scOuterPair F l i p.2).2 := by
    rw [← scCellDigest_eq, ← scCellDigest_eq]; exact hcd
  by_cases houter : scOuterPair F l i p.1 = scOuterPair F l i p.2
  · -- ROOT node children AGREE: the frame digests agree AND the moved digests agree.
    have hframeD : (scOuterPair F l i p.1).1 = (scOuterPair F l i p.2).1 := by rw [houter]
    have hmovedD : (scOuterPair F l i p.1).2 = (scOuterPair F l i p.2).2 := by rw [houter]
    have hmovedNode : F.compress l i (scMovedPair F l i p.1.cell).1 (scMovedPair F l i p.1.cell).2
        = F.compress l i (scMovedPair F l i p.2.cell).1 (scMovedPair F l i p.2.cell).2 := by
      rw [← scMovedDigest_eq, ← scMovedDigest_eq]; exact hmovedD
    have hspongeEq : F.compressN l i (scFrameList F l i p.1) = F.compressN l i (scFrameList F l i p.2) := by
      rw [← scFrameDigest_eq, ← scFrameDigest_eq]; exact hframeD
    -- the exhaustive partition on where the difference `c` lives.
    by_cases hcsrc : c = (F.turn l i).src
    · -- MOVED cell (src): either the moved node collides, or its `src` leaf does.
      by_cases hmp : scMovedPair F l i p.1.cell = scMovedPair F l i p.2.cell
      · refine Or.inr (Or.inr (Or.inr ?_))
        have hleaf : F.CH l i (F.turn l i).src (p.1.cell (F.turn l i).src)
            = F.CH l i (F.turn l i).src (p.2.cell (F.turn l i).src) := congrArg Prod.fst hmp
        exact ⟨by simp only [ne_eq, Prod.mk.injEq, true_and]; exact hc, by rw [hcsrc]; exact hleaf⟩
      · exact Or.inr (Or.inl ⟨hmp, hmovedNode⟩)
    · by_cases hcdst : c = (F.turn l i).dst
      · -- MOVED cell (dst): symmetric.
        by_cases hmp : scMovedPair F l i p.1.cell = scMovedPair F l i p.2.cell
        · refine Or.inr (Or.inr (Or.inr ?_))
          have hleaf : F.CH l i (F.turn l i).dst (p.1.cell (F.turn l i).dst)
              = F.CH l i (F.turn l i).dst (p.2.cell (F.turn l i).dst) := congrArg Prod.snd hmp
          exact ⟨by simp only [ne_eq, Prod.mk.injEq, true_and]; exact hc, by rw [hcdst]; exact hleaf⟩
        · exact Or.inr (Or.inl ⟨hmp, hmovedNode⟩)
      · by_cases hcacc : c ∈ p.1.accounts
        · -- UNTOUCHED live cell: either the frame sponge collides, or the leaf at `c` does.
          by_cases hfl : scFrameList F l i p.1 = scFrameList F l i p.2
          · refine Or.inr (Or.inr (Or.inr ?_))
            -- equal sorted-leaf lists over the SAME carrier ⇒ per-position leaves agree.
            have hcarr : scCarrier F l i p.2 = scCarrier F l i p.1 := by
              unfold scCarrier; rw [hAcc]
            have hmap : ((scCarrier F l i p.1).sort (· ≤ ·)).map (fun x => F.CH l i x (p.1.cell x))
                = ((scCarrier F l i p.1).sort (· ≤ ·)).map (fun x => F.CH l i x (p.2.cell x)) := by
              unfold scFrameList at hfl; rw [hcarr] at hfl; exact hfl
            have hpt : ∀ x ∈ (scCarrier F l i p.1).sort (· ≤ ·),
                F.CH l i x (p.1.cell x) = F.CH l i x (p.2.cell x) := List.map_inj_left.mp hmap
            have hmem : c ∈ scCarrier F l i p.1 := by
              unfold scCarrier
              simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hcacc, hcsrc, hcdst⟩
            exact ⟨by simp only [ne_eq, Prod.mk.injEq, true_and]; exact hc,
              hpt c ((Finset.mem_sort (· ≤ ·)).mpr hmem)⟩
          · exact Or.inr (Or.inr (Or.inl ⟨hfl, hspongeEq⟩))
        · -- DEAD cell: `AccountsWF` on BOTH states makes both default — it cannot be the difference.
          exact absurd (by rw [hwf c hcacc, hwf' c (by rw [← hAcc]; exact hcacc)]) hc
  · -- ROOT node children DIFFER: a genuine node-hash collision at the cell-digest root.
    exact Or.inl ⟨houter, hroot⟩

/-- **⚑ THE DICHOTOMY AT THE GAME LEVEL.** `sc_claim_wins_imp` at the equivocator's actual output: every
instance it wins, one of the four derived finders wins its collision game. The derived runs are
DEFINITIONALLY the four extractors, so this is `sc_claim_wins_imp` transported by `rfl`. -/
theorem sc_wins_imp (F : StateCommitFamily) (A : Adversary (scEquivGame F)) (l : ℕ) (i : F.Inst l)
    (hwin : (scEquivGame F).wins l i (A.run l i)) :
    (hashGame (scNodeFamily F)).wins l i ((scToOuterNodeAdv F A).run l i) ∨
      (hashGame (scNodeFamily F)).wins l i ((scToMovedNodeAdv F A).run l i) ∨
      (hashGame (scSpongeFamily F)).wins l i ((scToSpongeAdv F A).run l i) ∨
      (hashGame (scLeafFamily F)).wins l i ((scToLeafAdv F A).run l i) :=
  sc_claim_wins_imp F l i (A.run l i) hwin

/-- **THE ADVANTAGE INEQUALITY.** The equivocator's advantage is at most the SUM of the four extracted
finders' advantages, at every parameter — all five play over the SAME sampled instance space, and every
instance the equivocator wins one of the four derived finders wins. A genuine union-bound reduction
inequality over real game advantages. -/
theorem sc_adv_le (F : StateCommitFamily) (A : Adversary (scEquivGame F)) (l : ℕ) :
    gameAdv (scEquivGame F) A l ≤
      gameAdv (hashGame (scNodeFamily F)) (scToOuterNodeAdv F A) l +
        (gameAdv (hashGame (scNodeFamily F)) (scToMovedNodeAdv F A) l +
          (gameAdv (hashGame (scSpongeFamily F)) (scToSpongeAdv F A) l +
            gameAdv (hashGame (scLeafFamily F)) (scToLeafAdv F A) l)) := by
  refine @winProb_le_add4_of_imp _ (F.instFin l) _ _ _ _ _ (fun i hi => ?_)
  replace hi := (Adversary.hit_eq_true _ _ _).mp hi
  rcases sc_wins_imp F A l i hi with h1 | h2 | h3 | h4
  · exact Or.inl ((Adversary.hit_eq_true (scToOuterNodeAdv F A) l i).mpr h1)
  · exact Or.inr (Or.inl ((Adversary.hit_eq_true (scToMovedNodeAdv F A) l i).mpr h2))
  · exact Or.inr (Or.inr (Or.inl ((Adversary.hit_eq_true (scToSpongeAdv F A) l i).mpr h3)))
  · exact Or.inr (Or.inr (Or.inr ((Adversary.hit_eq_true (scToLeafAdv F A) l i).mpr h4)))

/-! ## §5 — the RE-GROUNDED keystone. -/

/-- **⚑ RE-GROUNDED `StateCommit.cellDigest_binds_cells` / `recStateCommit_binds_kernel` — from
COLLISION HARDNESS at the three families the reduction attacks, VIA the reduction.**

Under the collision floor at the node hash, the frame sponge and the LEAF hash — each at a NAMED adversary
class `Eff` — a state-commitment equivocator whose four extracted finders lie in those classes has
NEGLIGIBLE advantage: the published cell-digest pins the whole cell map EXCEPT with negligible
probability. The Boolean "equal digests ⇒ equal cell maps", which needed the FALSE `cellLeafInjective`
(§1) and its two already-flagged siblings, becomes an honest advantage bound.

⚑ **THE `hEff*` OBLIGATIONS ARE UNDISCHARGED AND THAT IS THE HONEST STATE.** They say the extracted
finders are in the classes the floors quantify over — the standard "the reduction is efficient". They are
PARAMETERS here, in the open, at the use site, because this tree has no cost model (`FloorGames` §8). The
floors are priced exactly by §7: `Eff := ⊤` makes them FALSE at compressing parameters (which is why this
file does NOT route through `HashCRHardQuant _ (fun _ => True)` — refuted by
`FloorGames.hashCRHardQuant_top_false_of_compressing`, and the floor the DELETED
`HashFloorHonesty.CollisionResistant` was a name for), `Eff := ⊥` vacuous. -/
theorem stateCommit_equivocation_advantage_bound (F : StateCommitFamily)
    (EffNode : Adversary (hashGame (scNodeFamily F)) → Prop)
    (EffSponge : Adversary (hashGame (scSpongeFamily F)) → Prop)
    (EffLeaf : Adversary (hashGame (scLeafFamily F)) → Prop)
    (A : Adversary (scEquivGame F))
    (hEffOuter : EffNode (scToOuterNodeAdv F A))
    (hEffMoved : EffNode (scToMovedNodeAdv F A))
    (hEffSponge : EffSponge (scToSpongeAdv F A))
    (hEffLeaf : EffLeaf (scToLeafAdv F A))
    (hNode : HashCRHardQuant (scNodeFamily F) EffNode)
    (hSponge : HashCRHardQuant (scSpongeFamily F) EffSponge)
    (hLeaf : HashCRHardQuant (scLeafFamily F) EffLeaf) :
    Negl (gameAdv (scEquivGame F) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (scEquivGame F) A l).1)
    (sc_adv_le F A)
    (negl_add (hNode _ hEffOuter)
      (negl_add (hNode _ hEffMoved)
        (negl_add (hSponge _ hEffSponge) (hLeaf _ hEffLeaf))))

/-! ## §5b — the LOG-HASH consumer, re-grounded (`logHashInjective`).

⚑ **The honest scope of this one is smaller than §3–§5, and saying so is the point.** The leaf floor
needed a four-horn reduction because `cellDigest` is a TREE: an equivocation there could be paid for at any
of four hash sites, and only the walk of the partition says which. The log floor is not a tree.
`logHashInjective LH := ∀ xs ys, LH xs = LH ys → xs = ys` is consumed by `EffectInstances2` /
`EffectRefinement` (`effect2_circuit_full_sound`, `effect_refines_*`) for exactly one thing: recovering the
receipt chain from its digest. Its BREAK — two distinct turn lists with one log hash — **IS definitionally
a collision of the log hash**, so there is no multi-horn dichotomy to build and inventing one would be
theatre.

What the re-grounding buys here is therefore precise and it is not nothing: the consumer moves off a
hypothesis that is FALSE at deployed parameters (`logHashInjective_false_babyBear`, and
`logRealization_uninhabitable_babyBear` for the bundle that discharges it) onto a floor about an
adversary FINDING a collision, at a NAMED `Eff` class. Existence → advantage. That is the entire content.

⚑ **A `scLogFamily_CR_of_logHashInjective` bridge used to stand below, and it is DELETED (2026-07-28).**
It read `logHashInjective` at every instance ⟹ the log family's floor at the UNRESTRICTED class, and the
finding it was half of was stated as "the old carrier was STRICTLY STRONGER than needed AND
unsatisfiable". The first half does not survive contact with its own target: that target is
`HashCRHardQuant (scLogFamily F) (fun _ => True)`, which `sc_log_floor_top_false_of_compressing` — right
below, in this same file — proves FALSE for a compressing log hash, and §1's counting core forces the
collision it asks for at exactly the BabyBear parameters that refute the source. Both ends refuted; the
implication is true and empty. What carries the finding now is
`logHashInjective_false_babyBear` alone (the old carrier is unsatisfiable, so its consumers were
vacuous), with the honest floor stated at a named `Eff` here and PROVED at §10's keyed-ROM successor
`log_equivocation_rom`. -/

/-- **THE LOG-HASH FAMILY.** Inputs are receipt chains, outputs field elements, the keyed hash the deployed
`LH`. A `logHashInjective` break IS a collision of this family. -/
structure LogCommitFamily where
  /-- The instance space (domain-separation sampling). -/
  Inst : ℕ → Type
  /-- The instance space is finite. -/
  instFin : ∀ l, Fintype (Inst l)
  /-- The instance space is inhabited. -/
  instNe : ∀ l, Nonempty (Inst l)
  /-- The receipt-chain hash at parameter `l`, instance `i`. -/
  LH : ∀ l, Inst l → List Turn → ℤ

/-- The log hash as a `KeyedHashFamily` — the collision game the honest floor lives over. -/
def scLogFamily (F : LogCommitFamily) : KeyedHashFamily where
  Key := F.Inst
  Input := List Turn
  Out := ℤ
  H := F.LH
  keyFintype := F.instFin
  keyNonempty := F.instNe
  inputDecEq := inferInstance
  outDecEq := inferInstance

/-- **THE PROBLEM IS IN THE STATEMENT** — the log game's win relation is a genuine collision of the real
receipt-chain hash: two DISTINCT turn lists, one digest. This is exactly the event `logHashInjective`
declared impossible and §1 proves pigeonhole FORCES. -/
theorem scLogGame_wins_iff (F : LogCommitFamily) (l : ℕ) (i : F.Inst l) (p : List Turn × List Turn) :
    (hashGame (scLogFamily F)).wins l i p ↔ (p.1 ≠ p.2 ∧ F.LH l i p.1 = F.LH l i p.2) :=
  Iff.rfl

/-- **⚑ RE-GROUNDED `logHashInjective` CONSUMER (`EffectInstances2.effect2_circuit_full_sound`,
`EffectRefinement.effect_refines_*`).** Under the collision floor at the log family, at a NAMED `Eff`
class, a receipt-chain equivocator has NEGLIGIBLE advantage: the published log digest pins the chain
EXCEPT with negligible probability. The Boolean "equal log hashes ⇒ equal chains", which needed the FALSE
`logHashInjective`, becomes an honest advantage bound.

⚑ `hEff` is UNDISCHARGED and that is the honest state (`FloorGames` §8) — priced by
`sc_log_floor_top_false_of_compressing` / `sc_log_floor_satisfiable_vacuously`. -/
theorem log_equivocation_advantage_bound (F : LogCommitFamily)
    (Eff : Adversary (hashGame (scLogFamily F)) → Prop)
    (A : Adversary (hashGame (scLogFamily F))) (hEff : Eff A)
    (hLog : HashCRHardQuant (scLogFamily F) Eff) :
    Negl (gameAdv (hashGame (scLogFamily F)) A) :=
  hLog A hEff

/-- **(TOOTH — the log floor is SATISFIABLE, vacuously.)** At the empty class it holds for any log hash,
including a constant one. Recorded honestly; worth nothing without the refutation beside it. -/
theorem sc_log_floor_satisfiable_vacuously (F : LogCommitFamily) :
    HashCRHardQuant (scLogFamily F) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(TOOTH — the log floor is FALSE at the unrestricted class, when the log hash is compressing.)** The
price of `hEff`, as a theorem: §1 proves pigeonhole forces such a collision at BabyBear, so at `Eff := ⊤`
the floor is FALSE and `log_equivocation_advantage_bound` is vacuous there. This is why the consumer must
NOT be re-grounded onto this floor at `⊤` — the floor the DELETED `HashFloorHonesty.CollisionResistant`
was a name for, and the reason the `logHashInjective` bridge onto it was deleted with it (§5b). -/
theorem sc_log_floor_top_false_of_compressing (F : LogCommitFamily)
    (hcol : ∀ l (i : F.Inst l), ∃ xs ys : List Turn, xs ≠ ys ∧ F.LH l i xs = F.LH l i ys) :
    ¬ HashCRHardQuant (scLogFamily F) (fun _ => True) := by
  refine not_hard_top_of_always_solvable (hashGame (scLogFamily F)) (fun _ => ⟨([], [])⟩) ?_
  intro l i
  obtain ⟨xs, ys, hne, heq⟩ := hcol l i
  exact ⟨(xs, ys), hne, heq⟩

/-! ## §6 — the CANARY: break the reduction and the keystone goes RED.

The sweep's lesson is that a floor consumer must be checked by asking whether it survives the WRONG
hypothesis. Under the OLD statement — `cellDigest_binds_cells (hLeaf : cellLeafInjective CH) …` — the
hypothesis was a FREE `Prop` that the conclusion never mentions, so no such canary was writable: the
floor and the conclusion did not share an object to disconnect. Here they cannot avoid it. -/

/-- **(CANARY — the keystone does NOT follow from the floors applied at OTHER adversaries.)** Strip the
reduction — try to conclude the equivocator's negligibility from the collision floors applied at some
OTHER finders `B`, `C`, `D`, `E`, NOT the ones extracted from it — and the proof does not go through: the
floors bound `B`/`C`/`D`/`E`, and only `sc_adv_le` connects the EXTRACTED four to the equivocation game.
The `negl_add` chain proves `Negl` of the WRONG advantage sum, so it cannot close
`Negl (gameAdv (scEquivGame F) A)`. This tooth was impossible to write under the old free
`cellLeafInjective` hypothesis; it compiles now, and REDS if a future edit reconnects the games. -/
example (F : StateCommitFamily)
    (EffNode : Adversary (hashGame (scNodeFamily F)) → Prop)
    (EffSponge : Adversary (hashGame (scSpongeFamily F)) → Prop)
    (EffLeaf : Adversary (hashGame (scLeafFamily F)) → Prop)
    (A : Adversary (scEquivGame F))
    (B C : Adversary (hashGame (scNodeFamily F))) (hB : EffNode B) (hC : EffNode C)
    (D : Adversary (hashGame (scSpongeFamily F))) (hD : EffSponge D)
    (E : Adversary (hashGame (scLeafFamily F))) (hE : EffLeaf E)
    (hNode : HashCRHardQuant (scNodeFamily F) EffNode)
    (hSponge : HashCRHardQuant (scSpongeFamily F) EffSponge)
    (hLeaf : HashCRHardQuant (scLeafFamily F) EffLeaf) : True := by
  fail_if_success
    (have : Negl (gameAdv (scEquivGame F) A) :=
      negl_add (hNode B hB) (negl_add (hNode C hC) (negl_add (hSponge D hD) (hLeaf E hE))))
  trivial

/-- **THE POSITIVE POLE — the RIGHT floors DO discharge it.** A gate that refuses everything is a broken
keystone, not a fixed one. With the collision floors at the EXTRACTED finders the keystone fires. Refusal
is discrimination only if acceptance still happens. -/
theorem the_repaired_bound_fires_on_the_right_floors (F : StateCommitFamily)
    (EffNode : Adversary (hashGame (scNodeFamily F)) → Prop)
    (EffSponge : Adversary (hashGame (scSpongeFamily F)) → Prop)
    (EffLeaf : Adversary (hashGame (scLeafFamily F)) → Prop)
    (A : Adversary (scEquivGame F))
    (hEffOuter : EffNode (scToOuterNodeAdv F A)) (hEffMoved : EffNode (scToMovedNodeAdv F A))
    (hEffSponge : EffSponge (scToSpongeAdv F A)) (hEffLeaf : EffLeaf (scToLeafAdv F A))
    (hNode : HashCRHardQuant (scNodeFamily F) EffNode)
    (hSponge : HashCRHardQuant (scSpongeFamily F) EffSponge)
    (hLeaf : HashCRHardQuant (scLeafFamily F) EffLeaf) :
    Negl (gameAdv (scEquivGame F) A) :=
  stateCommit_equivocation_advantage_bound F EffNode EffSponge EffLeaf A
    hEffOuter hEffMoved hEffSponge hEffLeaf hNode hSponge hLeaf

/-! ## §7 — the derived floors, priced honestly (both poles PROVED).

`FloorGames` §8's residual is that the tree has no cost model, so `Eff` cannot be given honest content
here. What CAN be proved is the price of both extremes — and that is what makes the `hEff*` parameters an
honest name for "the reduction is efficient" rather than a decoration. -/

/-- **(TOOTH — the leaf floor is SATISFIABLE, vacuously.)** At the empty adversary class it holds for any
leaf hash, including a completely broken one. Recorded HONESTLY, and it is not evidence of anything:
`hard_bot_vacuous` is exactly the statement that this satisfiability is vacuous. -/
theorem sc_leaf_floor_satisfiable_vacuously (F : StateCommitFamily) :
    HashCRHardQuant (scLeafFamily F) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(TOOTH — the node floor is SATISFIABLE, vacuously.)** Likewise. -/
theorem sc_node_floor_satisfiable_vacuously (F : StateCommitFamily) :
    HashCRHardQuant (scNodeFamily F) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(TOOTH — the sponge floor is SATISFIABLE, vacuously.)** Likewise. -/
theorem sc_sponge_floor_satisfiable_vacuously (F : StateCommitFamily) :
    HashCRHardQuant (scSpongeFamily F) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(TOOTH — the LEAF floor is FALSE at the unrestricted class, when the leaf hash is compressing.)**
The real content, and the reason `Eff` is not decoration: if at every sampled instance two distinct
`Value`s share a leaf — which §1 proves pigeonhole FORCES at BabyBear — then the floor at `Eff := ⊤` is
FALSE, and the keystone is vacuous there. This is the price of `hEffLeaf`, stated as a theorem instead of
a promise. -/
theorem sc_leaf_floor_top_false_of_compressing (F : StateCommitFamily)
    (hcol : ∀ l (i : F.Inst l), ∃ (c : CellId) (v : Value) (w : Value),
      v ≠ w ∧ F.CH l i c v = F.CH l i c w) :
    ¬ HashCRHardQuant (scLeafFamily F) (fun _ => True) := by
  refine not_hard_top_of_always_solvable (hashGame (scLeafFamily F))
    (fun _ => ⟨((0, default), (0, default))⟩) ?_
  intro l i
  obtain ⟨c, v, w, hne, heq⟩ := hcol l i
  exact ⟨((c, v), (c, w)), fun h => hne (congrArg Prod.snd h), heq⟩

/-- **(TOOTH — the NODE floor is FALSE at the unrestricted class, when the node hash is compressing.)**
Same price for the 2-to-1 horn: two field elements do not fit in one
(`HashFloorHonesty.compressInjective_false_of_finite_range` is the injective-shape sibling of this). -/
theorem sc_node_floor_top_false_of_compressing (F : StateCommitFamily)
    (hcol : ∀ l (i : F.Inst l), ∃ a b : ℤ × ℤ, a ≠ b ∧ F.compress l i a.1 a.2 = F.compress l i b.1 b.2) :
    ¬ HashCRHardQuant (scNodeFamily F) (fun _ => True) := by
  refine not_hard_top_of_always_solvable (hashGame (scNodeFamily F))
    (fun _ => ⟨((0, 0), (0, 0))⟩) ?_
  intro l i
  obtain ⟨a, b, hne, heq⟩ := hcol l i
  exact ⟨(a, b), hne, heq⟩

/-- **(TOOTH — the SPONGE floor is FALSE at the unrestricted class, when the sponge is compressing.)**
The third horn's price — `List ℤ` is infinite and the squeeze is one field element. -/
theorem sc_sponge_floor_top_false_of_compressing (F : StateCommitFamily)
    (hcol : ∀ l (i : F.Inst l), ∃ xs ys : List ℤ, xs ≠ ys ∧ F.compressN l i xs = F.compressN l i ys) :
    ¬ HashCRHardQuant (scSpongeFamily F) (fun _ => True) := by
  refine not_hard_top_of_always_solvable (hashGame (scSpongeFamily F)) (fun _ => ⟨([], [])⟩) ?_
  intro l i
  obtain ⟨xs, ys, hne, heq⟩ := hcol l i
  exact ⟨(xs, ys), hne, heq⟩

/-! ## §8 — ⚑ the OLD floor is WEAKER than its family, and the reduction stays on the DIAGONAL.

The usual re-grounding note is "the old injective floor implies the new one, so it was strictly stronger
and, being false, empty" (`Crypto.HermineHashCRRegrounded.commitRevealFamily_CR_of_hashcr` for the
flagged siblings — and §5b records why that note buys less than it reads: the floor such a bridge lands
on is the `⊤`-class one, refuted at a real hash by §7's teeth).
**Here it is FALSE outright, and saying so is the point.** `cellLeafInjective CH` is injectivity in the
`Value` at a FIXED cell — it says NOTHING about `CH c v = CH c' w` for `c ≠ c'`. So it does NOT discharge
`HashCRHardQuant (scLeafFamily F) (fun _ => True)`, whose game admits cross-cell collisions: the old
carrier is not merely false, it is not even the right shape for its own family.

What saves the reduction is that it never needs the cross-cell case: `scToLeafAdv` outputs a DIAGONAL
pair by construction (`scToLeafAdv_diagonal`), because the cell where two maps differ is ONE cell. So the
leaf floor is consumed exactly on the diagonal — precisely the property `cellLeafInjective` was claiming
for free, now paid for as a collision advantage. The `EffLeaf` class the keystone quantifies over may
therefore be taken to contain only diagonal finders without weakening the bound. -/

/-- **The extracted leaf finder is DIAGONAL** — it always outputs two `(cell, value)` pairs at the SAME
cell. So `stateCommit_equivocation_advantage_bound` consumes the leaf collision floor only on the
diagonal, which is exactly the surface `cellLeafInjective` claimed to cover — no cross-cell strength is
smuggled in, and the floor may be restricted to diagonal finders without weakening the keystone. -/
theorem scToLeafAdv_diagonal (F : StateCommitFamily) (A : Adversary (scEquivGame F)) (l : ℕ)
    (i : F.Inst l) : ((scToLeafAdv F A).run l i).1.1 = ((scToLeafAdv F A).run l i).2.1 := rfl

/-! ## §9 — the answer-size cost model (the honest record), and ⚑ the DELETED `IsPolyTime` discharges.

`stateCommit_equivocation_from_polyTime` and `log_equivocation_from_polyTime` stood here: all four
`hEff*` legs (resp. the log leg) DERIVED at `Eff := IsPolyTime` by `poly_time`. Their floors
`HashCRHardQuant … (IsPolyTime …)` are REFUTED at deployed parameters
(`Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear`: `IsPolyTime` prices answer
SIZE, so a `.pure` answerer with a hardcoded short collision is in the class and wins with probability
`1`) — the derivations derived nothing real. BOTH ARE DELETED; §10 lands the successors on the PROVED
keyed-ROM floor. The answer-size encodings and `scFrameList_length_le` below are KEPT as the honest
record of what that cost model can price (and the frame horn's linear-output fact is real).

§5's keystone carried FOUR bare `hEff*` parameters, one per extracted finder — the honest name for "the
reduction is efficient", undischarged because `FloorGames` §8 had no cost model.
`Dregg2.Crypto.CostAdversary` supplies one at COST-VECTOR resolution (intrinsic instructions +
per-oracle call counts, DERIVED from a deep-embedded program's syntax), and every one of the four horns
is a pure output reshaping of the equivocator's answer with the sampled instance passed through — i.e.
an `Adversary.postMap` — so `isPolyTime_postMap` turns all four parameters into CONSEQUENCES of ONE
hypothesis: that the equivocator itself is efficient.

The only per-site inputs left are the reshapers' DECLARED work `(cw, bw)` (a Lean `fun` has no runtime;
that number is CHARGED in the program's syntax) and each horn's OUTPUT SIZE, PROVED here:

  * the two NODE horns and the LEAF horn write a FIXED-WIDTH answer (two `ℤ×ℤ` pairs / two
    `(cell, value)` pairs), so their growth constants are `(0, 4)`;
  * the SPONGE horn writes the two frame lists, whose length is the untouched carrier's cardinality —
    bounded by the kernel's own `accounts` (`scFrameList_length_le`, `scCarrier` is a SUBSET), so its
    growth constants are `(1, 0)` against the game's own answer measure. Nothing here is asserted: the
    frame horn is the one horn that could have blown up, and it provably does not. -/

/-- **THE EQUIVOCATION GAME'S ANSWER ENCODING.** A forged pair of kernels costs, to write down, its two
account sets. Concrete on purpose: the size measure belongs to the GAME (`CostAdversary` design
commitment 4), and leaving it open would let a degenerate `sz := 0` make the frame horn's output free. -/
def scAnsSize (F : StateCommitFamily) : AnsSize (scEquivGame F) :=
  fun _ (p : RecordKernelState × RecordKernelState) => p.1.accounts.card + p.2.accounts.card

/-- **THE NODE COLLISION GAME'S ANSWER ENCODING** — the two claimed 2-to-1 input pairs. -/
def scNodeAnsSize (F : StateCommitFamily) : AnsSize (hashGame (scNodeFamily F)) :=
  fun _ (_ : (ℤ × ℤ) × (ℤ × ℤ)) => 4

/-- **THE SPONGE COLLISION GAME'S ANSWER ENCODING** — the two claimed absorbed leaf lists. -/
def scSpongeAnsSize (F : StateCommitFamily) : AnsSize (hashGame (scSpongeFamily F)) :=
  fun _ (p : List ℤ × List ℤ) => p.1.length + p.2.length

/-- **THE LEAF COLLISION GAME'S ANSWER ENCODING** — the two claimed `(cell, value)` pairs. -/
def scLeafAnsSize (F : StateCommitFamily) : AnsSize (hashGame (scLeafFamily F)) :=
  fun _ (_ : (CellId × Value) × (CellId × Value)) => 4

/-- **⚑ THE FRAME HORN DOES NOT BLOW UP ITS INPUT.** The sponge's absorbed list is one leaf per
UNTOUCHED cell, and the untouched carrier is `accounts \ {src, dst}` — a SUBSET of the kernel's own
account set. So the frame horn's output is bounded by the game's own answer measure, linearly with
slope `1`: the one horn whose output is not fixed-width is still size-linear, PROVED off `scCarrier`. -/
theorem scFrameList_length_le (F : StateCommitFamily) (l : ℕ) (i : F.Inst l)
    (k : RecordKernelState) : (scFrameList F l i k).length ≤ k.accounts.card := by
  simp only [scFrameList, List.length_map, Finset.length_sort]
  exact Finset.card_le_card (Finset.sdiff_subset)

/-- **THE LOG GAME'S ANSWER ENCODING** — the two claimed receipt chains. -/
def scLogAnsSize (F : LogCommitFamily) : AnsSize (hashGame (scLogFamily F)) :=
  fun _ (p : List Turn × List Turn) => p.1.length + p.2.length

/-- **(TOOTH — the node floor's class is NOT EMPTY.)** -/
theorem scNodeFloor_isPolyTime_inhabited (F : StateCommitFamily) :
    IsPolyTime (scNodeAnsSize F)
      (idAdv (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ _ => (((0 : ℤ), (0 : ℤ)), ((0 : ℤ), (0 : ℤ))))).toAdversary :=
  isPolyTime_inhabited _ _ ⟨4, 0, fun _ _ => by simp [scNodeAnsSize]⟩

/-- **(TOOTH — the sponge floor's class is NOT EMPTY.)** -/
theorem scSpongeFloor_isPolyTime_inhabited (F : StateCommitFamily) :
    IsPolyTime (scSpongeAnsSize F)
      (idAdv (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ _ => (([] : List ℤ), ([] : List ℤ)))).toAdversary :=
  isPolyTime_inhabited _ _ ⟨0, 0, fun _ _ => by simp [scSpongeAnsSize]⟩

/-- **(TOOTH — the leaf floor's class is NOT EMPTY.)** -/
theorem scLeafFloor_isPolyTime_inhabited (F : StateCommitFamily) :
    IsPolyTime (scLeafAnsSize F)
      (idAdv (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ _ => (((0 : CellId), (default : Value)),
                     ((0 : CellId), (default : Value))))).toAdversary :=
  isPolyTime_inhabited _ _ ⟨4, 0, fun _ _ => by simp [scLeafAnsSize]⟩

/-- **(TOOTH — the log floor's class is NOT EMPTY.)** -/
theorem scLogFloor_isPolyTime_inhabited (F : LogCommitFamily) :
    IsPolyTime (scLogAnsSize F)
      (idAdv (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ _ => (([] : List Turn), ([] : List Turn)))).toAdversary :=
  isPolyTime_inhabited _ _ ⟨0, 0, fun _ _ => by simp [scLogAnsSize]⟩

/-! ## §10 — ⚑⚑ THE DISCHARGED SUCCESSORS: the state-commit equivocation and the log binding on the
PROVED keyed-ROM floor.

⚑ **THE MODELLING STEP, STATED (not smuggled).** The three deployed hash surfaces — the leaf hash
`CH`, the 2-to-1 node hash `compress`, the frame sponge `compressN` — are idealised as ONE SAMPLED
oracle `H` over a THREE-shape, constructor-separated message domain (`ScRomMsg`): leaf messages are
truncated `(cell, encV value)` pairs, node messages are pairs of `λ`-bit digests (the chained
re-absorption, carried in the type exactly as `Exec.SystemRootsBindingReduction`'s `SysRomMsg`), and
sponge messages are length-tagged vectors of at most `m` digests. `scRomFamily` is that surface AS a
`StateCommitFamily` INSTANCE — so §3–§5's game, extractors, dichotomy and union bound apply VERBATIM;
nothing about the reduction is re-authored, only WHO evaluates the absorbed messages changes. The
floors §5's keystone consumes are then PROVED (`scNodeRom_hard` / `scSpongeRom_hard` /
`scLeafRom_hard`, each `KeyedRomFloor.keyedRom_hard` through a query-preserving `mapOut` extraction),
where the deleted `IsPolyTime` instantiation consumed floors that are REFUTED.

⚑ **WHAT STAYS OPEN, NAMED.** The keystone `stateCommit_equivocation_rom` carries its four
extracted-finder class memberships (`hOuter`/`hMoved`/`hSponge`/`hLeaf`) as HYPOTHESES — the honest
`hEff` shape of §5, now at classes whose floors are PROVED. Deriving them from the equivocator's own
query budget needs the CHAINED walk (the extracted digests are ORACLE outputs, so the extractor must
re-query — `RomCarrierSites.OracleComp.bindComp` is the tool and the kernel's account count prices the
walk); that derivation is the named residual. It is NOT vacuous conditioning:
`stateCommit_equivocation_rom_fires` exhibits a REAL equivocator (with hand-built query trees for all
four extracted finders) satisfying every hypothesis, end-to-end to a genuine `Negl`. The truncation
windows (`InD`, `babyBearP`) are win-conditional side conditions in the classes — the deployed felt
shapes satisfy them by layout, the felt-width wound carried visibly
(`docs/WOUND-felt-width-boundaries-2026-07-19.md`). -/

section RomSuccessor

open Dregg2.Crypto.ConcreteSecurity (PolyBounded)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp)
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily keyedRomGame KeyedRomEff keyedRom_hard)
open Dregg2.Crypto.RomQueryFloor (romCollisionGame RomEff)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.RomBindingReduction
  (OracleComp.mapOut OracleComp.mapOut_eval OracleComp.mapOut_queryBounded RomCarrierEff)
open Dregg2.Crypto.RomCarrierSites (babyBearP babyBearP_pos flatFamily BVec)
open Dregg2.Circuit.SpongeForgeReduction
  (GoodCode codeRomFamily codeRomCarrier codeForgeRomGame codeForge_binds_rom)
open Dregg2.Circuit.Poseidon2KeyedBridge (DomainSeparatedSponge)
open Dregg2.Circuit.Poseidon2Binding.Reference (encV encV_inj)

/-! ### The clamps, their losslessness on the deployed windows, and the message domain. -/

/-- Clamp a natural id/encoding into the BabyBear window — total; the identity below `babyBearP`. -/
def natBB (n : ℕ) : Fin babyBearP := ⟨n % babyBearP, Nat.mod_lt _ babyBearP_pos⟩

theorem natBB_inj {a b : ℕ} (ha : a < babyBearP) (hb : b < babyBearP) (h : natBB a = natBB b) :
    a = b := by
  have hv : a % babyBearP = b % babyBearP := congrArg Fin.val h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv

/-- The `λ`-bit digest window on `ℤ` — what every oracle output satisfies (`liftD_inD`). -/
def InD (l : ℕ) (x : ℤ) : Prop := 0 ≤ x ∧ x < ((2 ^ l : ℕ) : ℤ)

/-- Clamp an integer digest limb into the `λ`-bit window — total; lossless on `InD` limbs. -/
def clampD (l : ℕ) (x : ℤ) : Fin (2 ^ l) :=
  ⟨x.toNat % 2 ^ l, Nat.mod_lt _ (Nat.two_pow_pos l)⟩

/-- Read a sampled digest back as the felt-shaped integer the deployed surfaces pass around. -/
def liftD {l : ℕ} (r : Fin (2 ^ l)) : ℤ := ((r.val : ℕ) : ℤ)

theorem liftD_inj {l : ℕ} {r s : Fin (2 ^ l)} (h : liftD r = liftD s) : r = s := by
  simp only [liftD] at h
  have hv : r.val = s.val := by exact_mod_cast h
  exact Fin.ext hv

theorem liftD_inD (l : ℕ) (r : Fin (2 ^ l)) : InD l (liftD r) := by
  refine ⟨Int.natCast_nonneg _, ?_⟩
  simp only [liftD]
  exact_mod_cast r.isLt

theorem clampD_inj {l : ℕ} {x y : ℤ} (hx : InD l x) (hy : InD l y)
    (h : clampD l x = clampD l y) : x = y := by
  have hvx : x.toNat % 2 ^ l = x.toNat := Nat.mod_eq_of_lt ((Int.toNat_lt hx.1).mpr hx.2)
  have hvy : y.toNat % 2 ^ l = y.toNat := Nat.mod_eq_of_lt ((Int.toNat_lt hy.1).mpr hy.2)
  have hv : x.toNat % 2 ^ l = y.toNat % 2 ^ l := congrArg Fin.val h
  rw [hvx, hvy] at hv
  have hcast : ((x.toNat : ℕ) : ℤ) = ((y.toNat : ℕ) : ℤ) := by exact_mod_cast hv
  rwa [Int.toNat_of_nonneg hx.1, Int.toNat_of_nonneg hy.1] at hcast

/-- Embed an integer digest list into the finite length-tagged vector shape (total; lossless on
bounded `InD` lists by `bvecD_inj`). -/
def bvecD (m l : ℕ) (xs : List ℤ) : BVec (Fin (2 ^ l)) m :=
  (⟨min xs.length m, by omega⟩, fun i => (xs[i.val]?).map (clampD l))

/-- **THE SPONGE TRUNCATION LOSES NOTHING** on bounded in-window lists. -/
theorem bvecD_inj (m l : ℕ) {xs ys : List ℤ}
    (hxl : xs.length ≤ m) (hyl : ys.length ≤ m)
    (hxr : ∀ x ∈ xs, InD l x) (hyr : ∀ x ∈ ys, InD l x)
    (h : bvecD m l xs = bvecD m l ys) : xs = ys := by
  have hlen : xs.length = ys.length := by
    have h1 : min xs.length m = min ys.length m :=
      congrArg (fun p : BVec (Fin (2 ^ l)) m => p.1.val) h
    omega
  refine List.ext_getElem? (fun n => ?_)
  by_cases hn : n < m
  · have h2 : (xs[n]?).map (clampD l) = (ys[n]?).map (clampD l) :=
      congrFun (congrArg Prod.snd h) ⟨n, hn⟩
    by_cases hnx : n < xs.length
    · have hny : n < ys.length := hlen ▸ hnx
      rw [List.getElem?_eq_getElem hnx, List.getElem?_eq_getElem hny] at h2 ⊢
      simp only [Option.map_some] at h2
      exact congrArg some (clampD_inj (hxr _ (List.getElem_mem hnx)) (hyr _ (List.getElem_mem hny))
        (Option.some.inj h2))
    · have hny : ¬ n < ys.length := hlen ▸ hnx
      rw [List.getElem?_eq_none (Nat.le_of_not_lt hnx),
        List.getElem?_eq_none (Nat.le_of_not_lt hny)]
  · rw [List.getElem?_eq_none (le_trans hxl (Nat.le_of_not_lt hn)),
      List.getElem?_eq_none (le_trans hyl (Nat.le_of_not_lt hn))]

/-- **THE THREE-SHAPE ORACLE MESSAGE DOMAIN** — leaf `(cell, encV value)` pairs, node digest pairs
(the chained re-absorption, `λ`-bit limbs IN THE TYPE), and length-tagged sponge vectors — one
sampled oracle, constructor-separated. -/
abbrev ScRomMsg (m : ℕ) (l : ℕ) : Type :=
  (Fin babyBearP × Fin babyBearP) ⊕ ((Fin (2 ^ l) × Fin (2 ^ l)) ⊕ BVec (Fin (2 ^ l)) m)

/-- The keyed ROM family of the state-commit surface (trivial `Unit` tag: the three surfaces are
domain-separated by constructor inside ONE oracle domain). -/
def scRomOracle (m : ℕ) : KeyedRomFamily :=
  flatFamily Unit inferInstance inferInstance inferInstance (fun l => ScRomMsg m l)
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => ⟨Sum.inl (⟨0, babyBearP_pos⟩, ⟨0, babyBearP_pos⟩)⟩)

/-- The family's width obligation, closed by construction. -/
theorem scRomOracle_card_R (m l : ℕ) :
    letI := (scRomOracle m).rFin l
    Fintype.card ((scRomOracle m).R l) = 2 ^ l := by
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  simp

/-- The sampled-oracle space at parameter `l` — the instance the ROM games run over. -/
abbrev ScOracle (m l : ℕ) : Type :=
  (scRomOracle m).toRomFamily.D l → (scRomOracle m).toRomFamily.R l

/-- **⚑ THE ROM STATE-COMMIT SURFACE, AS A `StateCommitFamily` INSTANCE.** The instance space is the
sampled oracle; the three hashes are oracle calls at the three constructor-separated shapes. Because
§3–§5 are proven for EVERY `StateCommitFamily`, the equivocation game, the four extractors, the
dichotomy `sc_wins_imp` and the union bound `sc_adv_le` apply to THIS surface verbatim. -/
def scRomFamily (t₀ : Turn) (m : ℕ) : StateCommitFamily where
  Inst := fun l => ScOracle m l
  instFin := fun l => (romCollisionGame (scRomOracle m).toRomFamily).instFin l
  instNe := fun l => (romCollisionGame (scRomOracle m).toRomFamily).instNe l
  CH := fun l H c v => liftD (H ((), Sum.inl (natBB c, natBB (encV v))))
  compress := fun l H a b => liftD (H ((), Sum.inr (Sum.inl (clampD l a, clampD l b))))
  compressN := fun l H xs => liftD (H ((), Sum.inr (Sum.inr (bvecD m l xs))))
  turn := fun _ _ => t₀

/-! ### The three floors, PROVED, at query-counted classes with win-conditional windows. -/

/-- **THE QUERY-COUNTED NODE CLASS** — factors through a `Q`-query tree fixed before the oracle is
sampled, and (win-conditionally) answers inside the `λ`-bit window. The extracted node finders satisfy
the window UNCONDITIONALLY (their answers are oracle outputs); an arbitrary member only needs it where
it wins, which is where the floor reads it. -/
def ScNodeRomEff (t₀ : Turn) (m : ℕ) (Q : ℕ → ℕ)
    (B : Adversary (hashGame (scNodeFamily (scRomFamily t₀ m)))) : Prop :=
  (∃ M : ∀ l, OracleComp ((scRomOracle m).toRomFamily.D l) ((scRomOracle m).toRomFamily.R l)
      ((ℤ × ℤ) × (ℤ × ℤ)),
    (∀ l, QueryBounded (Q l) (M l)) ∧ ∀ l (H : ScOracle m l), B.run l H = (M l).eval H)
  ∧ ∀ l (H : ScOracle m l),
      (hashGame (scNodeFamily (scRomFamily t₀ m))).wins l H (B.run l H) →
        InD l (B.run l H).1.1 ∧ InD l (B.run l H).1.2
          ∧ InD l (B.run l H).2.1 ∧ InD l (B.run l H).2.2

/-- **THE QUERY-COUNTED SPONGE CLASS** — same shape at the list answers: bounded length, in-window
limbs, win-conditionally. -/
def ScSpongeRomEff (t₀ : Turn) (m : ℕ) (Q : ℕ → ℕ)
    (B : Adversary (hashGame (scSpongeFamily (scRomFamily t₀ m)))) : Prop :=
  (∃ M : ∀ l, OracleComp ((scRomOracle m).toRomFamily.D l) ((scRomOracle m).toRomFamily.R l)
      (List ℤ × List ℤ),
    (∀ l, QueryBounded (Q l) (M l)) ∧ ∀ l (H : ScOracle m l), B.run l H = (M l).eval H)
  ∧ ∀ l (H : ScOracle m l),
      (hashGame (scSpongeFamily (scRomFamily t₀ m))).wins l H (B.run l H) →
        ((show List ℤ from (B.run l H).1).length ≤ m
            ∧ ∀ x ∈ (show List ℤ from (B.run l H).1), InD l x)
          ∧ ((show List ℤ from (B.run l H).2).length ≤ m
            ∧ ∀ x ∈ (show List ℤ from (B.run l H).2), InD l x)

/-- **THE QUERY-COUNTED LEAF CLASS** — win-conditionally, cells and value encodings inside the
BabyBear window (the deployed kernels' genuine layout). -/
def ScLeafRomEff (t₀ : Turn) (m : ℕ) (Q : ℕ → ℕ)
    (B : Adversary (hashGame (scLeafFamily (scRomFamily t₀ m)))) : Prop :=
  (∃ M : ∀ l, OracleComp ((scRomOracle m).toRomFamily.D l) ((scRomOracle m).toRomFamily.R l)
      ((CellId × Value) × (CellId × Value)),
    (∀ l, QueryBounded (Q l) (M l)) ∧ ∀ l (H : ScOracle m l), B.run l H = (M l).eval H)
  ∧ ∀ l (H : ScOracle m l),
      (hashGame (scLeafFamily (scRomFamily t₀ m))).wins l H (B.run l H) →
        (B.run l H).1.1 < babyBearP ∧ (B.run l H).2.1 < babyBearP
          ∧ encV (B.run l H).1.2 < babyBearP ∧ encV (B.run l H).2.2 < babyBearP

/-- **⚑ THE NODE FLOOR, PROVED** — `keyedRom_hard` (the birthday bound) through a query-preserving
`mapOut` extraction: a node collision in the window IS a collision of the sampled oracle at two
distinct node messages. -/
theorem scNodeRom_hard (t₀ : Turn) (m : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1))) :
    HashCRHardQuant (scNodeFamily (scRomFamily t₀ m)) (ScNodeRomEff t₀ m Q) := by
  intro B hB
  obtain ⟨⟨M, hMQ, hrun⟩, hwr⟩ := hB
  let C : Adversary (keyedRomGame (scRomOracle m)) :=
    ⟨fun l H =>
      (((), Sum.inr (Sum.inl (clampD l (B.run l H).1.1, clampD l (B.run l H).1.2))),
       ((), Sum.inr (Sum.inl (clampD l (B.run l H).2.1, clampD l (B.run l H).2.2))))⟩
  have hle : ∀ l, gameAdv (hashGame (scNodeFamily (scRomFamily t₀ m))) B l
      ≤ gameAdv (keyedRomGame (scRomOracle m)) C l := by
    intro l
    refine @winProb_le_of_imp _
      ((hashGame (scNodeFamily (scRomFamily t₀ m))).instFin l) _ _ (fun H hH => ?_)
    replace hH := (Adversary.hit_eq_true _ _ _).mp hH
    refine (Adversary.hit_eq_true _ _ _).mpr ?_
    obtain ⟨hne, heq⟩ := hH
    obtain ⟨h11, h12, h21, h22⟩ := hwr l H ⟨hne, heq⟩
    refine ⟨fun hc => ?_, liftD_inj heq⟩
    have hp : (clampD l (B.run l H).1.1, clampD l (B.run l H).1.2)
        = (clampD l (B.run l H).2.1, clampD l (B.run l H).2.2) :=
      Sum.inl.inj (Sum.inr.inj (congrArg Prod.snd hc))
    exact hne (Prod.ext (clampD_inj h11 h21 (congrArg Prod.fst hp))
      (clampD_inj h12 h22 (congrArg Prod.snd hp)))
  have hC : KeyedRomEff (scRomOracle m) Q C := by
    refine ⟨fun l => OracleComp.mapOut (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
        ((((), Sum.inr (Sum.inl (clampD l p.1.1, clampD l p.1.2))) :
            (scRomOracle m).toRomFamily.D l),
         (((), Sum.inr (Sum.inl (clampD l p.2.1, clampD l p.2.2))) :
            (scRomOracle m).toRomFamily.D l))) (M l), ?_, ?_⟩
    · exact fun l => OracleComp.mapOut_queryBounded _ (hMQ l)
    · intro l H
      show (((), Sum.inr (Sum.inl (clampD l (B.run l H).1.1, clampD l (B.run l H).1.2))),
          ((), Sum.inr (Sum.inl (clampD l (B.run l H).2.1, clampD l (B.run l H).2.2)))) = _
      erw [OracleComp.mapOut_eval, hrun l H]
      rfl
  exact negl_of_le
    (fun l => (gameAdv_mem_unit (hashGame (scNodeFamily (scRomFamily t₀ m))) B l).1)
    hle (keyedRom_hard (scRomOracle m) Q hQ (scRomOracle_card_R m) C hC)

/-- **⚑ THE SPONGE FLOOR, PROVED** — same extraction at the vector shape; `bvecD_inj` is the
distinctness step. -/
theorem scSpongeRom_hard (t₀ : Turn) (m : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1))) :
    HashCRHardQuant (scSpongeFamily (scRomFamily t₀ m)) (ScSpongeRomEff t₀ m Q) := by
  intro B hB
  obtain ⟨⟨M, hMQ, hrun⟩, hwr⟩ := hB
  let C : Adversary (keyedRomGame (scRomOracle m)) :=
    ⟨fun l H =>
      (((), Sum.inr (Sum.inr (bvecD m l (B.run l H).1))),
       ((), Sum.inr (Sum.inr (bvecD m l (B.run l H).2))))⟩
  have hle : ∀ l, gameAdv (hashGame (scSpongeFamily (scRomFamily t₀ m))) B l
      ≤ gameAdv (keyedRomGame (scRomOracle m)) C l := by
    intro l
    refine @winProb_le_of_imp _
      ((hashGame (scSpongeFamily (scRomFamily t₀ m))).instFin l) _ _ (fun H hH => ?_)
    replace hH := (Adversary.hit_eq_true _ _ _).mp hH
    refine (Adversary.hit_eq_true _ _ _).mpr ?_
    obtain ⟨hne, heq⟩ := hH
    obtain ⟨⟨hl1, hr1⟩, ⟨hl2, hr2⟩⟩ := hwr l H ⟨hne, heq⟩
    refine ⟨fun hc => ?_, liftD_inj heq⟩
    have hp : bvecD m l (B.run l H).1 = bvecD m l (B.run l H).2 :=
      Sum.inr.inj (Sum.inr.inj (congrArg Prod.snd hc))
    exact hne (bvecD_inj m l hl1 hl2 hr1 hr2 hp)
  have hC : KeyedRomEff (scRomOracle m) Q C := by
    refine ⟨fun l => OracleComp.mapOut (fun p : List ℤ × List ℤ =>
        ((((), Sum.inr (Sum.inr (bvecD m l p.1))) : (scRomOracle m).toRomFamily.D l),
         (((), Sum.inr (Sum.inr (bvecD m l p.2))) : (scRomOracle m).toRomFamily.D l))) (M l),
      ?_, ?_⟩
    · exact fun l => OracleComp.mapOut_queryBounded _ (hMQ l)
    · intro l H
      show (((), Sum.inr (Sum.inr (bvecD m l (B.run l H).1))),
          ((), Sum.inr (Sum.inr (bvecD m l (B.run l H).2)))) = _
      erw [OracleComp.mapOut_eval, hrun l H]
      rfl
  exact negl_of_le
    (fun l => (gameAdv_mem_unit (hashGame (scSpongeFamily (scRomFamily t₀ m))) B l).1)
    hle (keyedRom_hard (scRomOracle m) Q hQ (scRomOracle_card_R m) C hC)

/-- **⚑ THE LEAF FLOOR, PROVED** — the horn `cellLeafInjective` carried for free, now paid by the
birthday bound: a leaf collision in the BabyBear window is an oracle collision at two distinct leaf
messages (`natBB_inj` on the cell and, via the PROVEN-injective `encV`, on the value). -/
theorem scLeafRom_hard (t₀ : Turn) (m : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1))) :
    HashCRHardQuant (scLeafFamily (scRomFamily t₀ m)) (ScLeafRomEff t₀ m Q) := by
  intro B hB
  obtain ⟨⟨M, hMQ, hrun⟩, hwr⟩ := hB
  let C : Adversary (keyedRomGame (scRomOracle m)) :=
    ⟨fun l H =>
      (((), Sum.inl (natBB (B.run l H).1.1, natBB (encV (B.run l H).1.2))),
       ((), Sum.inl (natBB (B.run l H).2.1, natBB (encV (B.run l H).2.2))))⟩
  have hle : ∀ l, gameAdv (hashGame (scLeafFamily (scRomFamily t₀ m))) B l
      ≤ gameAdv (keyedRomGame (scRomOracle m)) C l := by
    intro l
    refine @winProb_le_of_imp _
      ((hashGame (scLeafFamily (scRomFamily t₀ m))).instFin l) _ _ (fun H hH => ?_)
    replace hH := (Adversary.hit_eq_true _ _ _).mp hH
    refine (Adversary.hit_eq_true _ _ _).mpr ?_
    obtain ⟨hne, heq⟩ := hH
    obtain ⟨hc1, hc2, hv1, hv2⟩ := hwr l H ⟨hne, heq⟩
    refine ⟨fun hc => ?_, liftD_inj heq⟩
    have hp : (natBB (B.run l H).1.1, natBB (encV (B.run l H).1.2))
        = (natBB (B.run l H).2.1, natBB (encV (B.run l H).2.2)) :=
      Sum.inl.inj (congrArg Prod.snd hc)
    exact hne (Prod.ext (natBB_inj hc1 hc2 (congrArg Prod.fst hp))
      (encV_inj _ _ (natBB_inj hv1 hv2 (congrArg Prod.snd hp))))
  have hC : KeyedRomEff (scRomOracle m) Q C := by
    refine ⟨fun l => OracleComp.mapOut (fun p : (CellId × Value) × (CellId × Value) =>
        ((((), Sum.inl (natBB p.1.1, natBB (encV p.1.2))) : (scRomOracle m).toRomFamily.D l),
         (((), Sum.inl (natBB p.2.1, natBB (encV p.2.2))) : (scRomOracle m).toRomFamily.D l)))
        (M l), ?_, ?_⟩
    · exact fun l => OracleComp.mapOut_queryBounded _ (hMQ l)
    · intro l H
      show (((), Sum.inl (natBB (B.run l H).1.1, natBB (encV (B.run l H).1.2))),
          ((), Sum.inl (natBB (B.run l H).2.1, natBB (encV (B.run l H).2.2)))) = _
      erw [OracleComp.mapOut_eval, hrun l H]
      rfl
  exact negl_of_le
    (fun l => (gameAdv_mem_unit (hashGame (scLeafFamily (scRomFamily t₀ m))) B l).1)
    hle (keyedRom_hard (scRomOracle m) Q hQ (scRomOracle_card_R m) C hC)

/-! ### The keystone, and its non-vacuity at a REAL end-to-end witness. -/

/-- **⚑⚑ THE RE-GROUNDED STATE-COMMIT EQUIVOCATION BOUND, floors PROVED.** §5's keystone at the ROM
surface: a state-commitment equivocator whose four extracted finders are query-bounded (the labelled
open obligation — the chained walk, see the §10 header) has NEGLIGIBLE advantage, with the three
collision floors DISCHARGED by the birthday bound instead of carried refutable. Successor of the
DELETED `stateCommit_equivocation_from_polyTime` (whose floors were refuted, so its `poly_time`
derivation transported nothing). -/
theorem stateCommit_equivocation_rom (t₀ : Turn) (m : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (scEquivGame (scRomFamily t₀ m)))
    (hOuter : ScNodeRomEff t₀ m Q (scToOuterNodeAdv (scRomFamily t₀ m) A))
    (hMoved : ScNodeRomEff t₀ m Q (scToMovedNodeAdv (scRomFamily t₀ m) A))
    (hSponge : ScSpongeRomEff t₀ m Q (scToSpongeAdv (scRomFamily t₀ m) A))
    (hLeaf : ScLeafRomEff t₀ m Q (scToLeafAdv (scRomFamily t₀ m) A)) :
    Negl (gameAdv (scEquivGame (scRomFamily t₀ m)) A) :=
  stateCommit_equivocation_advantage_bound (scRomFamily t₀ m)
    (ScNodeRomEff t₀ m Q) (ScSpongeRomEff t₀ m Q) (ScLeafRomEff t₀ m Q)
    A hOuter hMoved hSponge hLeaf
    (scNodeRom_hard t₀ m Q hQ) (scSpongeRom_hard t₀ m Q hQ) (scLeafRom_hard t₀ m Q hQ)

/-- The empty kernel — the fires witness's answer. -/
def scRomK₀ : RecordKernelState :=
  { accounts := ∅, cell := fun _ => default, caps := fun _ => [] }

/-- The empty kernel's frame list is empty at EVERY sampled oracle. -/
theorem scFrameList_k₀ (t₀ : Turn) (m l : ℕ) (H : ScOracle m l) :
    scFrameList (scRomFamily t₀ m) l H scRomK₀ = [] := by
  simp [scFrameList, scCarrier, scRomK₀]

/-- The constant (hardcoded-answer) equivocator — the `IsPolyTime`-refuter's SHAPE, admitted here. -/
def scRomConstAdv (t₀ : Turn) (m : ℕ) : Adversary (scEquivGame (scRomFamily t₀ m)) :=
  ⟨fun _ _ => (scRomK₀, scRomK₀)⟩

/-- **(WITNESS — the OUTER extracted finder factors through a 4-query tree.)** The hand-built walk:
absorb the (empty) frame, the two moved leaves, then the moved node ON THE ANSWERS — a genuine
chained query tree, with the win-conditional window vacuous (the answer pair is reflexive, and a
collision needs distinct sides). -/
theorem scRomConst_outer_eff (t₀ : Turn) (m : ℕ) :
    ScNodeRomEff t₀ m (fun _ => 4) (scToOuterNodeAdv (scRomFamily t₀ m) (scRomConstAdv t₀ m)) := by
  constructor
  · refine ⟨fun l =>
      .query ((), Sum.inr (Sum.inr (bvecD m l []))) (fun rF =>
      .query ((), Sum.inl (natBB t₀.src, natBB (encV (default : Value)))) (fun r1 =>
      .query ((), Sum.inl (natBB t₀.dst, natBB (encV (default : Value)))) (fun r2 =>
      .query ((), Sum.inr (Sum.inl (clampD l (liftD r1), clampD l (liftD r2)))) (fun rM =>
      .pure ((liftD rF, liftD rM), (liftD rF, liftD rM)))))), ?_, ?_⟩
    · intro l
      exact QueryBounded.query 3 _ _ fun rF => QueryBounded.query 2 _ _ fun r1 =>
        QueryBounded.query 1 _ _ fun r2 => QueryBounded.query 0 _ _ fun rM =>
          QueryBounded.pure 0 _
    · intro l H
      show (scOuterPair (scRomFamily t₀ m) l H scRomK₀,
          scOuterPair (scRomFamily t₀ m) l H scRomK₀) = _
      unfold scOuterPair
      erw [scFrameDigest_eq, scFrameList_k₀]
      rfl
  · intro l H hw
    exact (hw.1 rfl).elim

/-- **(WITNESS — the MOVED extracted finder factors through a 2-query tree.)** -/
theorem scRomConst_moved_eff (t₀ : Turn) (m : ℕ) :
    ScNodeRomEff t₀ m (fun _ => 4) (scToMovedNodeAdv (scRomFamily t₀ m) (scRomConstAdv t₀ m)) := by
  constructor
  · refine ⟨fun l =>
      .query ((), Sum.inl (natBB t₀.src, natBB (encV (default : Value)))) (fun r1 =>
      .query ((), Sum.inl (natBB t₀.dst, natBB (encV (default : Value)))) (fun r2 =>
      .pure ((liftD r1, liftD r2), (liftD r1, liftD r2)))), ?_, ?_⟩
    · intro l
      exact (QueryBounded.query 1 _ _ fun r1 => QueryBounded.query 0 _ _ fun r2 =>
        QueryBounded.pure 0 _).mono (show (2 : ℕ) ≤ 4 by omega)
    · intro l H
      show (scMovedPair (scRomFamily t₀ m) l H scRomK₀.cell,
          scMovedPair (scRomFamily t₀ m) l H scRomK₀.cell) = _
      simp only [OracleComp.eval]
      rfl
  · intro l H hw
    exact (hw.1 rfl).elim

/-- **(WITNESS — the SPONGE extracted finder is a `0`-query tree at the empty kernel.)** -/
theorem scRomConst_sponge_eff (t₀ : Turn) (m : ℕ) :
    ScSpongeRomEff t₀ m (fun _ => 4) (scToSpongeAdv (scRomFamily t₀ m) (scRomConstAdv t₀ m)) := by
  constructor
  · refine ⟨fun l => .pure (([] : List ℤ), ([] : List ℤ)), fun l => QueryBounded.pure 4 _, ?_⟩
    intro l H
    show (scFrameList (scRomFamily t₀ m) l H scRomK₀,
        scFrameList (scRomFamily t₀ m) l H scRomK₀) = _
    simp only [OracleComp.eval, scFrameList_k₀]
  · intro l H hw
    exact (hw.1 rfl).elim

/-- **(WITNESS — the LEAF extracted finder is a `0`-query tree.)** -/
theorem scRomConst_leaf_eff (t₀ : Turn) (m : ℕ) :
    ScLeafRomEff t₀ m (fun _ => 4) (scToLeafAdv (scRomFamily t₀ m) (scRomConstAdv t₀ m)) := by
  constructor
  · exact ⟨fun l => .pure
      ((diffCell scRomK₀.cell scRomK₀.cell, scRomK₀.cell (diffCell scRomK₀.cell scRomK₀.cell)),
       (diffCell scRomK₀.cell scRomK₀.cell, scRomK₀.cell (diffCell scRomK₀.cell scRomK₀.cell))),
      fun l => QueryBounded.pure 4 _, fun l H => rfl⟩
  · intro l H hw
    exact (hw.1 rfl).elim

/-- **⚑ (TOOTH — the keystone FIRES end-to-end.)** Every hypothesis of
`stateCommit_equivocation_rom` is satisfied at a REAL equivocator: the hardcoded-answer shape that
refutes the `IsPolyTime` floor is ADMITTED by the query classes (with genuine hand-built query trees
for all four extracted finders) and the keystone concludes a genuine `Negl` — the class is not empty,
the conditioning is not vacuous. -/
theorem stateCommit_equivocation_rom_fires (t₀ : Turn) (m : ℕ) :
    Negl (gameAdv (scEquivGame (scRomFamily t₀ m)) (scRomConstAdv t₀ m)) := by
  refine stateCommit_equivocation_rom t₀ m (fun _ => 4) ⟨1, 17, ?_⟩ (scRomConstAdv t₀ m)
    (scRomConst_outer_eff t₀ m) (scRomConst_moved_eff t₀ m)
    (scRomConst_sponge_eff t₀ m) (scRomConst_leaf_eff t₀ m)
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [abs_of_nonneg (by positivity)]
  push_cast
  nlinarith

/-- **(TOOTH — the ROM equivocation game is WINNABLE, so the keystone bounds something real.)** Two
`AccountsWF` kernels over ONE live account with DIFFERENT cell maps collide at the CONSTANT oracle
(every digest is the constant answer), so the equivocator that answers them wins with positive
probability at every parameter. -/
theorem scRomEquiv_winnable (m : ℕ) (l : ℕ) :
    0 < gameAdv (scEquivGame (scRomFamily ⟨0, 1, 2, 0⟩ m))
      ⟨fun _ _ => (({ accounts := {0}, cell := fun _ => Value.int 0, caps := fun _ => [] } :
            RecordKernelState),
          ({ accounts := {0},
             cell := fun c => if c = 0 then Value.int 1 else Value.int 0,
             caps := fun _ => [] } : RecordKernelState))⟩ l := by
  obtain ⟨r₀⟩ := (scRomOracle m).rNe l
  refine @Dregg2.Crypto.RomCarrierSites.winProb_pos_of_witness _
    ((scEquivGame (scRomFamily ⟨0, 1, 2, 0⟩ m)).instFin l) _ (fun _ => r₀) ?_
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  refine ⟨fun c hc => rfl, fun c hc => ?_, rfl, ?_, rfl⟩
  · have h0 : ¬ c = 0 := by
      intro h
      subst h
      exact hc (Finset.mem_singleton_self 0)
    show (if c = 0 then Value.int 1 else Value.int 0) = default
    rw [if_neg h0]
    rfl
  · intro h
    have h0 := congrFun h 0
    simp at h0

/-! ### The LOG consumer's successor — §5b's honest shape at the sampled oracle: the break IS the
collision, so the successor is the generic bounded-code carrier (`SpongeForgeReduction` §8) at the
receipt-chain serialization; no tree, no walk, nothing re-authored. -/

/-- The fixed-width receipt code: ALL FOUR fields, in order — the `Poseidon2Surface.encTurnRec`
shape (`src`/`dst` bound, unlike the toy fold this file's §1 indicts). -/
def encTurnCode (t : Turn) : List ℤ := [(t.actor : ℤ), (t.src : ℤ), (t.dst : ℤ), t.amt]

theorem encTurnCode_length (t : Turn) : (encTurnCode t).length = 4 := rfl

/-- Fixed-width blocks concatenate injectively (given equal chain lengths). -/
theorem flatMap_encTurnCode_inj : ∀ {xs ys : List Turn}, xs.length = ys.length →
    xs.flatMap encTurnCode = ys.flatMap encTurnCode → xs = ys := by
  intro xs
  induction xs with
  | nil =>
    intro ys h _
    exact (List.length_eq_zero_iff.mp h.symm).symm
  | cons t ts ih =>
    intro ys hlen hf
    cases ys with
    | nil => simp at hlen
    | cons u us =>
      rw [List.flatMap_cons, List.flatMap_cons] at hf
      obtain ⟨hblk, hrest⟩ := List.append_inj hf
        (by rw [encTurnCode_length, encTurnCode_length])
      have hlen' : ts.length = us.length := by simpa using hlen
      have ht : t = u := by
        obtain ⟨a, s0, d0, mm⟩ := t
        obtain ⟨a', s', d', mm'⟩ := u
        simp only [encTurnCode, List.cons.injEq, and_true] at hblk
        obtain ⟨h1, h2, h3, h4⟩ := hblk
        have e1 : a = a' := by exact_mod_cast h1
        have e2 : s0 = s' := by exact_mod_cast h2
        have e3 : d0 = d' := by exact_mod_cast h3
        subst e1; subst e2; subst e3; subst h4
        rfl
      rw [ht, ih hlen' hrest]

/-- The length-prefixed receipt-chain code — the absorbed limb list. -/
def turnChainCode (ts : List Turn) : List ℤ := ((ts.length : ℕ) : ℤ) :: ts.flatMap encTurnCode

/-- **THE CHAIN CODE IS INJECTIVE, unconditionally** — the length prefix pins the block count and
fixed-width blocks recover turn-by-turn. The structural fact `logHashInjective` never was. -/
theorem turnChainCode_injective : Function.Injective turnChainCode := by
  intro xs ys h
  simp only [turnChainCode, List.cons.injEq] at h
  obtain ⟨hlen, hflat⟩ := h
  exact flatMap_encTurnCode_inj (by exact_mod_cast hlen) hflat

theorem flatMap_encTurnCode_length (ts : List Turn) :
    (ts.flatMap encTurnCode).length = 4 * ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [List.flatMap_cons, List.length_append, encTurnCode_length, ih, List.length_cons]
    omega

/-- The deployed felt window on a receipt — every field a genuine BabyBear-range value. -/
def TurnInWindow (t : Turn) : Prop :=
  (t.actor : ℤ) < babyBearP ∧ (t.src : ℤ) < babyBearP ∧ (t.dst : ℤ) < babyBearP
    ∧ 0 ≤ t.amt ∧ t.amt < babyBearP

/-- Receipt chains of at most `n` in-window turns — the truncated deployed payload shape. -/
abbrev BoundedChain (n : ℕ) : Type := {ts : List Turn // ts.length ≤ n ∧ ∀ t ∈ ts, TurnInWindow t}

/-- The bounded chain's code satisfies the ROM carrier's deployed-shape side condition. -/
theorem boundedChain_code_good (n m : ℕ) (hm : 4 * n + 1 ≤ m) (hn : (n : ℤ) < (babyBearP : ℤ))
    (s : BoundedChain n) : GoodCode m (turnChainCode s.val) := by
  obtain ⟨hlen, hwin⟩ := s.property
  constructor
  · simp only [turnChainCode, List.length_cons, flatMap_encTurnCode_length]
    omega
  · intro x hx
    simp only [turnChainCode, List.mem_cons] at hx
    rcases hx with rfl | hx
    · refine ⟨Int.natCast_nonneg _, ?_⟩
      have hcast : ((s.val.length : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hlen
      linarith
    · obtain ⟨t, ht, hxt⟩ := List.mem_flatMap.mp hx
      obtain ⟨h1, h2, h3, h4, h5⟩ := hwin t ht
      simp only [encTurnCode, List.mem_cons, List.not_mem_nil, or_false] at hxt
      rcases hxt with rfl | rfl | rfl | rfl
      · exact ⟨Int.natCast_nonneg _, h1⟩
      · exact ⟨Int.natCast_nonneg _, h2⟩
      · exact ⟨Int.natCast_nonneg _, h3⟩
      · exact ⟨h4, h5⟩

/-- **⚑⚑ THE RE-GROUNDED LOG BINDING — floor PROVED, nothing refutable carried.** Every
query-bounded receipt-chain equivocator has NEGLIGIBLE advantage: the log digest pins the WHOLE
ordered chain — `src`/`dst` included — except with negligible probability, in the keyed ROM model.
Successor of the DELETED `log_equivocation_from_polyTime` (floor refuted); the reduction is the
generic bounded-code carrier of `SpongeForgeReduction` §8 at the length-prefixed receipt code. -/
theorem log_equivocation_rom (D : DomainSeparatedSponge) (tagDec : DecidableEq D.Tag)
    (n m : ℕ) (hm : 4 * n + 1 ≤ m) (hn : (n : ℤ) < (babyBearP : ℤ)) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (adv : Adversary (codeForgeRomGame D tagDec m (BoundedChain n) inferInstance
      (fun s => turnChainCode s.val) (fun _ _ h => Subtype.ext (turnChainCode_injective h))
      (boundedChain_code_good n m hm hn)))
    (hA : RomCarrierEff (codeRomFamily D tagDec m)
      (codeRomCarrier D tagDec m (BoundedChain n) inferInstance
        (fun s => turnChainCode s.val) (fun _ _ h => Subtype.ext (turnChainCode_injective h))
        (boundedChain_code_good n m hm hn)) Q adv) :
    Negl (gameAdv (codeForgeRomGame D tagDec m (BoundedChain n) inferInstance
      (fun s => turnChainCode s.val) (fun _ _ h => Subtype.ext (turnChainCode_injective h))
      (boundedChain_code_good n m hm hn)) adv) :=
  codeForge_binds_rom D tagDec m (BoundedChain n) _ _ _ _ Q hQ adv hA

end RomSuccessor

#assert_all_clean [
  scFrameList_length_le,
  natBB_inj,
  clampD_inj,
  bvecD_inj,
  scRomOracle_card_R,
  scNodeRom_hard,
  scSpongeRom_hard,
  scLeafRom_hard,
  stateCommit_equivocation_rom,
  scRomConst_outer_eff,
  scRomConst_moved_eff,
  scRomConst_sponge_eff,
  scRomConst_leaf_eff,
  stateCommit_equivocation_rom_fires,
  scRomEquiv_winnable,
  turnChainCode_injective,
  log_equivocation_rom,
  scNodeFloor_isPolyTime_inhabited,
  scSpongeFloor_isPolyTime_inhabited,
  scLeafFloor_isPolyTime_inhabited,
  scLogFloor_isPolyTime_inhabited
]

#assert_all_clean [
  finite_range_of_field_window,
  cellLeafInjective_false_of_finite_range,
  cellLeafInjective_false_babyBear,
  logHashInjective_false_of_finite_range,
  logHashInjective_false_babyBear,
  leafRealization_uninhabitable_babyBear,
  logRealization_uninhabitable_babyBear,
  winProb_le_add3_of_imp,
  winProb_le_add4_of_imp,
  scCellDigest_eq,
  scMovedDigest_eq,
  scFrameDigest_eq,
  scEquivGame_wins_iff,
  diffCell_spec,
  sc_claim_wins_imp,
  sc_wins_imp,
  sc_adv_le,
  stateCommit_equivocation_advantage_bound,
  the_repaired_bound_fires_on_the_right_floors,
  sc_leaf_floor_satisfiable_vacuously,
  sc_node_floor_satisfiable_vacuously,
  sc_sponge_floor_satisfiable_vacuously,
  sc_leaf_floor_top_false_of_compressing,
  sc_node_floor_top_false_of_compressing,
  sc_sponge_floor_top_false_of_compressing,
  scToLeafAdv_diagonal,
  scLogGame_wins_iff,
  log_equivocation_advantage_bound,
  sc_log_floor_satisfiable_vacuously,
  sc_log_floor_top_false_of_compressing
]

end Dregg2.Circuit.StateCommitFloorRegrounded
