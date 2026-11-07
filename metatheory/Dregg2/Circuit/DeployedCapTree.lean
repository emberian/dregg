/-
# Dregg2.Circuit.DeployedCapTree — THE FAITHFUL model of the DEPLOYED 7-field cap-tree.

## Why this file exists (the authority-leg ground-truth correction)

The kernel-authority bridge (`Dregg2.Circuit.CapRootBridge`) and the in-circuit non-amplification
proofs (`EffectVmEmitRotationV3.attenuateV3_non_amp`) discharge their cap-openings against
`DescriptorIR2.opensTo`, whose denotation is `Dregg2.Substrate.Heap`:

    opensTo hash r k o := ∃ h : FeltHeap, SortedKeys h ∧ Heap.root hash h = r ∧ Heap.get h k = o
    Heap.root hash h   := hash (h.map (fun e => hash [e.1, e.2]))           -- FLAT sponge, 2-field leaf

That model is a FLAT SPONGE of a sorted list of **2-field** leaves `hash[addr, value]`.

The value the CELL actually commits (and the EffectVM circuit seeds `cap_root` from) is
`dregg_cell::compute_canonical_capability_root_felt` → `circuit/src/cap_root.rs::CanonicalCapTree`:

    leaf  = cap_chip_absorb[slot_hash, target, auth_tag, mask_lo, mask_hi, expiry, breadstuff] -- 7 fields
    node  = cap_chip_absorb[FACT_MARK, left, right]                                            -- arity-3
    root  = the depth-16 BINARY MERKLE fold of the sorted-by-slot_hash padded leaf list

## The unification (THIS revision — decision #1, the chip-rate gap CLOSED)

`circuit/src/cap_root.rs::cap_chip_absorb` is now the SINGLE in-circuit hash the cap-tree commits to:
ONE width-16 Poseidon2 permutation, byte-identical to the IR-v2 Poseidon2 chip's BUS_P2 absorb
(`descriptor_ir2.rs::Ir2Air::Chip`). The chip distinguishes two seedings by `big = [arity == 7]`:

  * `arity ≤ 4` (rate-4 regime): `state[0..len] = ins`, `state[4] = len` (the length tag),
    `state[5..] = 0`. The cap NODE rides this as the arity-3 absorb of `[FACT_MARK, l, r]`.
  * `arity == 7` (rate-8 leaf): `state[0..7] = ins`, NO tag lane (`state[7..] = 0`). The cap LEAF
    rides this as the arity-7 absorb of the 7 leaf fields.

So the deployed leaf and node are BOTH a single chip-realizable permutation call. We model the one
hash as `Dregg2.Crypto.CommitmentBinding.Compress1CR` — ONE permutation call (`squeeze ∘ perm ∘
absorb`), the same primitive #4 the 2-to-1 Merkle node `hash_2_to_1` rides — and define BOTH
`capLeafDigest` and `nodeOf` OVER it. Because the leaf-field list (length 7) and the node block
`[FACT_MARK, l, r]` (length 3) are length-disjoint, the chip's per-row `(arity, padded ins)` seeding
separates the two domains for free; `Compress1CR` (equal output ⇒ equal input list) is exactly the
chip's per-row collision-resistance.

This makes the IR-v2 chip GENUINELY realize the deployed cap hash: `DeployedCapOpen`'s
`SchemeRealizedByChip sponge S` is now PROVABLE (the chip's rate-8 absorb IS the deployed scheme, by
construction), so it is DISCHARGED, not carried. The prior revision's rate-4 `hash_many` leaf +
capacity-tagged `hash_fact` node (the source of the gap) are GONE.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Compress1CR` floor (the SAME single-permutation-call floor #4 the whole commitment tower carries).
-/
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Crypto.CommitmentBinding
import Dregg2.Exec.Kernel
import Dregg2.Exec.FacetAuthority
import Dregg2.Circuit.Emit.EffectVmEmitCapReshape
import Dregg2.Circuit.CapMerkleGeneric
import Dregg2.Crypto.RomHashedLeafOpening

namespace Dregg2.Circuit.DeployedCapTree

open Dregg2.Crypto.CommitmentBinding (Compress1CR Compress1Coll compress1Coll_refutable_of_injective)
open Dregg2.Authority (Cap Auth Caps Label capAuthConferred)
open Dregg2.Circuit.Emit.EffectVmEmitCapReshape (authBitN rightsMaskOf)
open Dregg2.Exec.FacetAuthority
  (AuthTier AuthProvided FacetCap FacetCaps EffectMask EFFECT_TRANSFER isEffectPermitted
   authorizedFacetB authorizedFacetB_holds_transfer_cap turnEffectBit capAuthorizesFacet
   authorizedFacetEffB authorizedFacetEffB_holds_cap)

set_option autoImplicit false

/-! ## §0 — the deployed leaf (the 7-field `CapLeaf`, byte-faithful to `cap_root.rs`). -/

/-- The 7 canonical leaf fields, in `cap_root.rs::CapLeaf` order. The deployed tree stores
`capLeafDigest` of these at each leaf position. (`slot_hash` is the sort key; here we keep the
fields abstract `ℤ` — the deployment instance is BabyBear.) -/
structure CapLeaf where
  /-- The sort key: a Poseidon2 image of the (unique) c-list slot (`cap_root.rs:95`). -/
  slot_hash : ℤ
  /-- The capability's target cell id, folded to one felt (`cap_root.rs:98`). -/
  target : ℤ
  /-- The `AuthRequired` tier (+ absorbed vk_hash for `Custom`), one felt (`cap_root.rs:99`). -/
  auth_tag : ℤ
  /-- `EffectMask` low 16 bits (`cap_root.rs:101`). -/
  mask_lo : ℤ
  /-- `EffectMask` high 16 bits (`cap_root.rs:103`). -/
  mask_hi : ℤ
  /-- Optional expiry height (`NONE_SENTINEL` when absent) (`cap_root.rs:105`). -/
  expiry : ℤ
  /-- Optional breadstuff hash folded to one felt (`cap_root.rs:107`). -/
  breadstuff : ℤ
  deriving DecidableEq

/-- The 7 leaf fields in canonical `cap_root.rs::CapLeaf::digest` order — the EXACT list `hash_many`
absorbs (`cap_root.rs:115-124`). The leaf digest is the rate-4 sponge over THIS list. -/
def leafFields (l : CapLeaf) : List ℤ :=
  [l.slot_hash, l.target, l.auth_tag, l.mask_lo, l.mask_hi, l.expiry, l.breadstuff]

/-- `leafFields` is injective in the whole `CapLeaf` (it is just the seven fields in order). -/
theorem leafFields_inj {l₁ l₂ : CapLeaf} (h : leafFields l₁ = leafFields l₂) : l₁ = l₂ := by
  simp only [leafFields, List.cons.injEq] at h
  cases l₁; cases l₂; simp_all

/-! ## §1 — the deployed node layout (the arity-3 chip absorb `[FACT_MARK, l, r]`).

`cap_root.rs::cap_node` folds each internal node as `cap_chip_absorb(&[CAP_FACT_MARK, l, r])` — the
arity-3 (rate-4 regime) single chip absorb. `FACT_MARK = 0xFACF` rides RATE lane 0 (a genuine rate
input, NOT a capacity tag), `l` lane 1, `r` lane 2, the length tag `3` in lane 4. So
`nodeOf l r = chipAbsorb [FACT_MARK, l, r]`, one permutation call over the length-3 block. -/

/-- The cap-node domain-separation marker `0xFACF` (`cap_root.rs::CAP_FACT_MARK`), absorbed as the
FIRST RATE input of the arity-3 node block (NOT a capacity tag). -/
def FACT_MARK : ℤ := 0xFACF

/-- **`packNode l r`** — the deployed `cap_node` chip-absorb input block `[FACT_MARK, l, r]`
(`cap_root.rs::cap_node` = `cap_chip_absorb(&[CAP_FACT_MARK, l, r])`). `FACT_MARK` at rate lane 0,
`l` at 1, `r` at 2 — a genuine rate-input list, length 3 (length-disjoint from the length-7 leaf
block, so the chip's per-row arity seeding separates the two domains). -/
def packNode (l r : ℤ) : List ℤ := [FACT_MARK, l, r]

/-- `packNode` is injective in `(l, r)` (`FACT_MARK` is the constant head; the two children sit at
fixed positions 1, 2). The STRUCTURAL half of node injectivity. -/
theorem packNode_inj {l₁ r₁ l₂ r₂ : ℤ} (h : packNode l₁ r₁ = packNode l₂ r₂) :
    l₁ = l₂ ∧ r₁ = r₂ := by
  simp only [packNode, List.cons.injEq] at h
  exact ⟨h.2.1, h.2.2.1⟩

/-! ## §2 — the `CapHashScheme` bundle: the ONE deployed chip-absorb carrier.

The deployed cap tree commits ONE hash everywhere — `cap_root.rs::cap_chip_absorb`, the IR-v2 chip's
single rate-8 absorb. Both the leaf (arity 7) and the node (arity 3) ride this one permutation call.
We bundle exactly that carrier. -/

/-- **`CapHashScheme State`** — the deployed cap-tree's SINGLE Poseidon2 carrier: the chip absorb
`chipAbsorb : List ℤ → ℤ` (`cap_root.rs::cap_chip_absorb` = the IR-v2 chip's `squeeze ∘ perm ∘
(state from arity+inputs)`). The `State` parameter is vestigial (the carrier is the per-row
compression); the deployment instance is the real BabyBear width-16 permutation.
`nodeOf`/`capLeafDigest` are defined over it.

⚑ **ONE FIELD, AND IT IS INHABITED (2026-07-25 bundle cutover).** The `chipCR : Compress1CR
chipAbsorb` field is GONE. It asserted that the single permutation call is injective from the
INFINITE `List ℤ` into ONE bounded BabyBear felt — which `FactoryBindingFloorRegrounded.
compress1CR_false_babyBear` REFUTES for every real chip absorb, so no deployed `CapHashScheme`
value could be constructed and every `∀ S : CapHashScheme State, …` theorem below was VACUOUS.
`CapHashScheme` was the LAST `Compress1CR` field in the tree (its 8-felt sibling `Cap8Scheme`
shed `chip8CR` on 07-20, `Compress2` shed `compress1CR` earlier today). §7b constructs
`deployedCapHashScheme`, a real value whose own chip this tree's teeth REFUTE
(`CapHashBundleCutoverCheck.deployedCapHashScheme_chip_not_Compress1CR`).

The collision resistance the tree used to assume is now EXTRACTED AS DATA: each consumer below
keeps its NAME and CONCLUSION under a PER-INSTANCE `¬ Compress1Coll chipAbsorb (extractor args)`
at the exact blocks its own extractor hands back, and each has an UNCONDITIONAL `…_or_collides`
sibling that holds OF the deployed chip. Design decision for the whole bundle family (DELETE the
field; never swap in a `noColl` field — a field has no argument position to be per-instance AT)
is recorded at `Dregg2.Shielded.RealCrypto` §2.0. -/
structure CapHashScheme (State : Type) where
  /-- The single chip-absorb compression (`cap_chip_absorb`, `squeeze ∘ perm ∘ stateFromArityInputs`),
  shared by the leaf (arity 7) and the node (arity 3). -/
  chipAbsorb : List ℤ → ℤ

namespace CapHashScheme

variable {State : Type} (S : CapHashScheme State)

/-! ## §3 — the re-grounded primitives (`capLeafDigest`/`nodeOf` BOTH ride `chipAbsorb`). -/

/-- **`capLeafDigest S l`** — the 7-field deployed leaf digest, the SINGLE rate-8 chip absorb over the
7 leaf fields in canonical order. BYTE-IDENTICAL to `cap_root.rs::CapLeaf::digest`
(`cap_chip_absorb(&[slot_hash, target, auth_tag, mask_lo, mask_hi, expiry, breadstuff])` — ONE
permute, lanes 0..6 the genuine fields, no length tag, the chip's `big` row). -/
def capLeafDigest (l : CapLeaf) : ℤ := S.chipAbsorb (leafFields l)

/-- **`nodeOf S l r`** — the internal node hash, the arity-3 chip absorb over `packNode l r =
[FACT_MARK, l, r]`. BYTE-IDENTICAL to `cap_root.rs::cap_node` (`cap_chip_absorb(&[CAP_FACT_MARK, l,
r])` — ONE permute, `FACT_MARK` at rate lane 0). The SAME `chipAbsorb` carrier as the leaf — one cap
hash everywhere. -/
def nodeOf (l r : ℤ) : ℤ := S.chipAbsorb (packNode l r)

/-! ## §4 — binding, EXTRACTED AS DATA (the sound replacement for the deleted `chipCR` field).

Each theorem here used to be discharged by PROJECTING `chipCR`, i.e. from `Compress1CR chipAbsorb`,
which the deployed chip refutes — so each said nothing about the deployed system. Each is now a TOTAL
EXTRACTOR plus two forms:

  * `…_or_collides` — UNCONDITIONAL. Equal images EITHER force the inputs equal, OR the pair the
    extractor hands back IS a genuine collision of the deployed chip. This holds OF the deployment.
  * `…_injective` — the ORIGINAL NAME and the ORIGINAL CONCLUSION, under a PER-INSTANCE
    `¬ Compress1Coll S.chipAbsorb (extractor args)` about the EXACT blocks the old proof fed the
    floor. Implied by the deleted field at every pair (`compress1Coll_refutable_of_injective`), hence
    strictly stronger — see the `…_of_injective` bridges in §4b. -/

/-- The leaf extractor: the two 7-field blocks the arity-7 chip absorbed. TOTAL, no search — the two
claimed leaves ARE the candidate collision, because `capLeafDigest` applies the chip to them directly. -/
def leafCollFind (l₁ l₂ : CapLeaf) : List ℤ × List ℤ := (leafFields l₁, leafFields l₂)

/-- **Leaf binding, UNCONDITIONAL.** Equal 1-felt leaf digests EITHER force the whole 7-field `CapLeaf`
equal, OR the two `leafFields` blocks ARE a genuine collision of the deployed chip — handed back by
name rather than asserted impossible. No injectivity hypothesis anywhere: this holds OF the deployed
system, which is exactly what the `chipCR`-projecting original never did. -/
theorem capLeafDigest_binds_or_collides {l₁ l₂ : CapLeaf}
    (h : capLeafDigest S l₁ = capLeafDigest S l₂) :
    l₁ = l₂ ∨ Compress1Coll S.chipAbsorb (leafCollFind l₁ l₂) := by
  by_cases hl : l₁ = l₂
  · exact Or.inl hl
  · exact Or.inr ⟨fun hf => hl (leafFields_inj hf), h⟩

/-- **Leaf injectivity** — SAME NAME, SAME CONCLUSION as the version that projected the deleted
`chipCR` field; the crypto content is now a PER-INSTANCE side condition at the EXACT pair of absorbed
blocks the proof is about, rather than a universally-false injectivity claim baked into the type. -/
theorem capLeafDigest_injective {l₁ l₂ : CapLeaf}
    (h : capLeafDigest S l₁ = capLeafDigest S l₂)
    (hnc : ¬ Compress1Coll S.chipAbsorb (leafCollFind l₁ l₂)) : l₁ = l₂ :=
  (capLeafDigest_binds_or_collides S h).resolve_right hnc

/-- The node extractor: the two arity-3 `[FACT_MARK, l, r]` input blocks. -/
def nodeCollFind (l₁ r₁ l₂ r₂ : ℤ) : List ℤ × List ℤ := (packNode l₁ r₁, packNode l₂ r₂)

/-- **Node binding, UNCONDITIONAL.** Equal node images EITHER force equal children, OR the two packed
arity-3 blocks ARE a genuine chip collision. The per-level peel of the membership recompose's
anti-ghost, restated so the failure branch produces a WITNESS instead of consuming a refuted floor. -/
theorem nodeOf_binds_or_collides {l₁ r₁ l₂ r₂ : ℤ}
    (h : nodeOf S l₁ r₁ = nodeOf S l₂ r₂) :
    (l₁ = l₂ ∧ r₁ = r₂) ∨ Compress1Coll S.chipAbsorb (nodeCollFind l₁ r₁ l₂ r₂) := by
  by_cases hn : l₁ = l₂ ∧ r₁ = r₂
  · exact Or.inl hn
  · exact Or.inr ⟨fun hp => hn (packNode_inj hp), h⟩

/-- **Node injectivity** — SAME NAME, SAME CONCLUSION as the `chipCR`-projecting original, under the
per-instance non-collision of the two arity-3 blocks the node absorb actually ran on. -/
theorem nodeOf_injective {l₁ r₁ l₂ r₂ : ℤ}
    (h : nodeOf S l₁ r₁ = nodeOf S l₂ r₂)
    (hnc : ¬ Compress1Coll S.chipAbsorb (nodeCollFind l₁ r₁ l₂ r₂)) : l₁ = l₂ ∧ r₁ = r₂ :=
  (nodeOf_binds_or_collides S h).resolve_right hnc

/-! ## §5 — the membership opening (the depth-16 binary-Merkle recompose up a sibling path).

A membership witness is a list of `(sibling, direction)` steps (`cap_root.rs::prove_membership`
returns exactly `(siblings, directions)`; `directions[i] = 0` ⇔ the current node is the LEFT child
at level `i`). Recomposing folds `nodeOf` up the path, mixing `(cur, sib)` by the direction bit —
LITERALLY the `descriptor_ir2` MapOps AIR's `mix` closure (`descriptor_ir2.rs:2109`):
`left = (1-dir)·cur + dir·sib`, `right = (1-dir)·sib + dir·cur`. -/

/-- One Merkle path step: the sibling digest at this level + the direction bit. -/
structure Step where
  /-- The sibling digest at this level (`cap_root.rs` `siblings[level]`). -/
  sib : ℤ
  /-- The direction bit: `0` ⇒ `cur` is the LEFT child (sibling right), `1` ⇒ right child. -/
  dir : Bool
  deriving DecidableEq

/-- **`recomposeUp S cur path`** — fold the held digest up the sibling/direction path to the root. At
each level, if `dir = false` (LEFT child) the node is `nodeOf cur sib`, else `nodeOf sib cur`. This is
the exact `attenuation_witness` / MapOps-AIR fold (`cap_root.rs:425-431`, `descriptor_ir2.rs:2116`),
now over the deployed capacity-tagged `nodeOf`. -/
def recomposeUp (cur : ℤ) : List Step → ℤ
  | [] => cur
  | s :: rest =>
    recomposeUp (if s.dir then nodeOf S s.sib cur else nodeOf S cur s.sib) rest

/-- **`MembersAt S root leaf`** — the deployed-tree membership statement: there is a sibling/direction
path recomposing `root` from the 7-field leaf's digest. The witness is the path
(`cap_root.rs::prove_membership`); the relation hides it behind the existential, exactly as the
in-circuit opening realizes it. The HONEST replacement for `Substrate.Heap`'s flat-sponge `opensTo` —
the REAL rate-4 leaf digest and the REAL capacity-tagged `hash_fact` binary fold. -/
def MembersAt (root : ℤ) (leaf : CapLeaf) : Prop :=
  ∃ path : List Step, recomposeUp S (capLeafDigest S leaf) path = root

/-- `Step` → the width-agnostic `CapMerkleGeneric.StepG ℤ` (structural identity: same `(sib, dir)`).
The bridge that lets the 1-felt tree DELEGATE its membership soundness to the generic spine. -/
def Step.toG (s : Step) : CapMerkleGeneric.StepG ℤ := ⟨s.sib, s.dir⟩

/-- **The 1-felt recompose IS the generic recompose at `D := ℤ`, `node := nodeOf S`.** Definitional
modulo the `Step ↔ StepG ℤ` repack; proved by a one-line structural induction. This is what makes the
1-felt anti-ghost a RE-INSTANTIATION of `CapMerkleGeneric.recomposeG_inj_of_path`, not a re-proof. -/
theorem recomposeUp_eq_recomposeG (cur : ℤ) (path : List Step) :
    recomposeUp S cur path
      = CapMerkleGeneric.recomposeG (nodeOf S) cur (path.map Step.toG) := by
  induction path generalizing cur with
  | nil => rfl
  | cons s rest ih =>
    simp only [recomposeUp, List.map_cons, CapMerkleGeneric.recomposeG, Step.toG, ih]

/-- **The 1-felt spine EXTRACTOR** — the generic path walk (`CapMerkleGeneric.recomposeGFind`) at
`node := nodeOf S`, with the colliding child-pair it lands on mapped through `packNode` into the two
arity-3 chip input blocks. A TOTAL function of the two starting digests and the path; the SAME generic
walk the native-8-felt `recomposeUp8Find` re-instantiates, at the other width. -/
def recomposeUpFind (a b : ℤ) (path : List Step) : List ℤ × List ℤ :=
  (packNode (CapMerkleGeneric.recomposeGFind (nodeOf S) a b (path.map Step.toG)).1.1
            (CapMerkleGeneric.recomposeGFind (nodeOf S) a b (path.map Step.toG)).1.2,
   packNode (CapMerkleGeneric.recomposeGFind (nodeOf S) a b (path.map Step.toG)).2.1
            (CapMerkleGeneric.recomposeGFind (nodeOf S) a b (path.map Step.toG)).2.2)

/-- **The 1-felt anti-ghost spine, UNCONDITIONAL.** Equal recomposed roots along a FIXED path EITHER
force equal starting digests, OR the walk LANDS on a level whose two arity-3 `nodeOf` blocks are a
genuine chip collision, returned by name. A prover cannot keep the published root while swapping the
opened leaf UNLESS the deployed chip actually collides at the two blocks this extractor hands back.
Still a PURE RE-INSTANTIATION — `CapMerkleGeneric.recomposeGFind_spec` is proved once, generically. -/
theorem recomposeUp_binds_or_collides (path : List Step) {a b : ℤ}
    (h : recomposeUp S a path = recomposeUp S b path) :
    a = b ∨ Compress1Coll S.chipAbsorb (recomposeUpFind S a b path) := by
  rw [recomposeUp_eq_recomposeG, recomposeUp_eq_recomposeG] at h
  rcases CapMerkleGeneric.recomposeGFind_spec (nodeOf S) (path.map Step.toG) h with heq | ⟨hne, himg⟩
  · exact Or.inl heq
  · refine Or.inr ⟨fun hp => hne ?_, himg⟩
    exact Prod.ext (packNode_inj hp).1 (packNode_inj hp).2

/-- **`recomposeUp` is injective in its STARTING digest** — equal recomposed roots from the SAME path
force the same starting leaf digest. The anti-ghost spine: a prover cannot keep the published root
while swapping the opened leaf along a fixed path. SAME NAME, SAME CONCLUSION as the version that rode
the deleted `chipCR` field through `nodeOf_injective`; the crypto content is now the per-instance
non-collision at the ONE level pair the walk actually lands on. -/
theorem recomposeUp_inj_of_path (path : List Step) {a b : ℤ}
    (h : recomposeUp S a path = recomposeUp S b path)
    (hnc : ¬ Compress1Coll S.chipAbsorb (recomposeUpFind S a b path)) : a = b :=
  (recomposeUp_binds_or_collides S path h).resolve_right hnc

/-! ## §5.1 — THE STRENGTH RELATION: carried ONCE, by a bridge that already exists.

Deleting a carrier and restating its consumers under a side condition invites two fair objections.

1. *"You weakened the theorems to make the deletion easy."* — ANSWERED, and answered without minting
   a single new declaration: `CommitmentBinding.compress1Coll_refutable_of_injective` is exactly
   `Compress1CR c1 → ∀ p, ¬ Compress1Coll c1 p` — the deleted field's own type implies the new side
   condition AT EVERY PAIR. So each cured theorem above, applied with that bridge in its `hnc` slot,
   IS its own pre-cutover statement; the three ports are the injective special case of nothing lost.
   ⚑ Deliberately NOT restated as three per-theorem `…_of_injective` bridges. Each such restatement
   would be a NEW declaration taking a hypothesis this tree PROVES FALSE at deployed BabyBear
   parameters — i.e. a new VACUOUS declaration, which is the accrual `#floor_ratchet` exists to stop.
   The 8-felt sibling's `…8_injective_of_injective` family predates the gate and is grandfathered;
   this one does not get to add to that pile to make the same point a fourth time. One bridge, used.
2. *"The right disjunct is a free pass, so the disjunction says nothing."* —
   `compress1Coll_refutable_of_injective` answers this too, in the other direction: at an injective
   chip the extracted pair is NOT a collision, so the binding half has to do the work. And at the
   DEPLOYED chip the disjunct is genuinely reachable — `CapHashBundleCutoverCheck` §4 exhibits the
   collision at a degenerate carrier and proves the unconditional forms FALSE.

Neither bridge is a hypothesis on any keystone here: `Compress1CR` is FALSE at deployed BabyBear
parameters, so a keystone carrying it would be right back where the repair started. -/

/-! ## §6 — the FAITHFUL commitment relation + the authority bridge against THIS tree.

The replacement for `CapRootBridge.CapsEncodes` (which is over `Substrate.Heap`). `DeployedEncodes`
says `cap_root` is the deployed `CanonicalCapTree`-root of a leaf set that FAITHFULLY realizes the
kernel `caps`: a write-rights membership opening of an authority-edge leaf witnesses a real held
endpoint cap. We carry the faithfulness as the runtime-encoding contract, exactly the
`compute_canonical_capability_root_felt` discipline. -/

/-! ### §6.0 — the FAITHFUL two-axis leaf decode (THE CUTOVER, FacetAuthority §10(C)).

The deployed leaf commits the authority on TWO axes, both in the 7-field leaf (`cap_root.rs:41-51`):
a FACET (`mask_lo`/`mask_hi`, two 16-bit limbs of one `EffectMask` u32) and a TIER (`auth_tag`, the
`AuthRequired` byte None=0…Custom=5). The cutover decodes BOTH off the leaf and gates the turn on
`authorizedFacetB` — NOT the toy `mask_lo == write-mask` shadow. -/

/-- **`maskOfLimbs lo hi`** — recombine the deployed split mask `(mask_lo, mask_hi)` into the one
`EffectMask` `u32`: `mask = mask_lo + mask_hi · 2^16` (`cap_root.rs::split_effect_mask`: `lo = mask &
0xFFFF`, `hi = (mask >> 16) & 0xFFFF`). The leaf-faithful inverse of the deployed limb split. -/
def maskOfLimbs (lo hi : ℤ) : ℤ := lo + hi * 65536

/-- **`tierOfTag tag`** — decode the deployed `auth_tag` BYTE to an `AuthTier` (`cap_root.rs:46`:
None=0…Custom=5; `AuthTier.tierByte` is the forward map). The IPC tiers (None…Impossible) decode by
the discriminant byte; tag `5` decodes to a `Custom` whose `vkHash` is the residual felt-absorb
(carried as `vkOfTag`, the one named crypto residual — transfers never use `Custom`, see §10). -/
def tierOfTag (vkOfTag : ℤ → Nat) : ℤ → AuthTier
  | 0 => .none
  | 1 => .signature
  | 2 => .proof
  | 3 => .either
  | 4 => .impossible
  | tag => .custom (vkOfTag tag)   -- tag = 5 (Custom): vkHash absorbed (NAMED residual `vkOfTag`)

/-- **`facetOfLeaf l`** — the leaf's decoded `Option EffectMask` facet: `some (maskOfLimbs mask_lo
mask_hi)` (the deployed `allowed_effects`; here always `some` — the leaf commits a concrete mask). -/
def facetOfLeaf (l : CapLeaf) : Option EffectMask := some (maskOfLimbs l.mask_lo l.mask_hi).toNat

/-- **`confersTransferLeaf vkOfTag provided l`** — THE FAITHFUL two-axis leaf gate (replaces the toy
`confersWriteLeaf`). The leaf confers TRANSFER authority iff (1) its decoded FACET permits the
`EFFECT_TRANSFER` bit (`isEffectPermitted`, `facet.rs:123`) AND (2) its decoded TIER (`tierOfTag
auth_tag`) is satisfied by the auth the turn `provided` (`AuthTier.isSatisfiedBy`, `permissions.rs:33`).
This is the deployed `(allowed_effects, permissions)` authority core, decoded off the committed leaf. -/
def confersTransferLeaf (vkOfTag : ℤ → Nat) (provided : AuthProvided) (l : CapLeaf) : Prop :=
  isEffectPermitted (facetOfLeaf l) EFFECT_TRANSFER = true
    ∧ (tierOfTag vkOfTag l.auth_tag).isSatisfiedBy provided = true

/-- **`confersLeaf vkOfTag provided effectBit l`** (F6 — the GENERAL two-axis leaf gate). The
generalization of `confersTransferLeaf` from the pinned `EFFECT_TRANSFER` constant to an ARBITRARY
effect-kind bit `effectBit`: the leaf confers `effectBit` authority iff (1) its decoded FACET
(`facetOfLeaf`, the genuine `maskOfLimbs mask_lo mask_hi`) permits `effectBit` AND (2) its decoded
TIER (`tierOfTag auth_tag`, the genuine committed byte — NOT a constant) is satisfied by `provided`.
`confersTransferLeaf vkOfTag provided = confersLeaf vkOfTag provided EFFECT_TRANSFER` (by `rfl`). -/
def confersLeaf (vkOfTag : ℤ → Nat) (provided : AuthProvided) (effectBit : EffectMask)
    (l : CapLeaf) : Prop :=
  isEffectPermitted (facetOfLeaf l) effectBit = true
    ∧ (tierOfTag vkOfTag l.auth_tag).isSatisfiedBy provided = true

/-- `confersTransferLeaf` is the `EFFECT_TRANSFER` instance of the general `confersLeaf`. -/
theorem confersTransferLeaf_eq_general (vkOfTag : ℤ → Nat) (provided : AuthProvided) (l : CapLeaf) :
    confersTransferLeaf vkOfTag provided l = confersLeaf vkOfTag provided EFFECT_TRANSFER l := rfl

/-- **`DeployedFaithful S vkOfTag provided caps root leafAt`** — the leaf-set `leafAt` faithfully
realizes the FACET caps `caps`: every TRANSFER-conferring member leaf at an `(actor ⇒ src)` edge is
backed by a real held `FacetCap` over `src` whose facet permits TRANSFER and whose tier is satisfied by
`provided`. The forward encoding contract (caps ⇒ tree); the bridge below reads it backward through one
opening into `authorizedFacetB`. -/
structure DeployedFaithful (vkOfTag : ℤ → Nat) (provided : AuthProvided)
    (caps : FacetCaps) (root : ℤ) (leafAt : Label → Label → CapLeaf) : Prop where
  /-- FAITHFULNESS: a transfer-conferring member opening witnesses a REAL held `FacetCap` whose facet
  permits TRANSFER under a tier the `provided` auth satisfies. -/
  backed : ∀ (actor src : Label),
    MembersAt S root (leafAt actor src) →
    confersTransferLeaf vkOfTag provided (leafAt actor src) →
    ∃ c : FacetCap, c ∈ caps actor ∧ c.target = src
      ∧ isEffectPermitted c.facet EFFECT_TRANSFER = true
      ∧ c.tier.isSatisfiedBy provided = true

/-- **`DeployedEncodes S vkOfTag provided caps root`** — THE deployed commitment relation: `root` is
the deployed cap-tree root of SOME leaf assignment that faithfully realizes the FACET caps `caps`. -/
def DeployedEncodes (vkOfTag : ℤ → Nat) (provided : AuthProvided) (caps : FacetCaps) (root : ℤ) : Prop :=
  ∃ leafAt : Label → Label → CapLeaf, DeployedFaithful S vkOfTag provided caps root leafAt

/-- **`deployedCapOpen_implies_authorizedB` — THE FAITHFUL AUTHORITY BRIDGE against the deployed tree.**
GIVEN the deployed commitment relation, AND an in-circuit membership opening whose leaf confers TRANSFER
on BOTH axes (facet permits `EFFECT_TRANSFER`, tier satisfied by `provided`) — THEN the kernel's FAITHFUL
`authorizedFacetB` PASSES for the turn `⟨actor, src, dst, amt⟩`. The circuit's depth-16 binary-Merkle
membership proof discharges the deployed two-axis (tier × facet) authority gate, reusing
`authorizedFacetB_holds_transfer_cap`. -/
theorem deployedCapOpen_implies_authorizedB
    (vkOfTag : ℤ → Nat) (provided : AuthProvided)
    (caps : FacetCaps) (root : ℤ) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithful S vkOfTag provided caps root leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hopen : MembersAt S root (leafAt actor src))
    (hconf : confersTransferLeaf vkOfTag provided (leafAt actor src)) :
    authorizedFacetB caps provided { actor := actor, src := src, dst := dst, amt := amt } = true := by
  obtain ⟨c, hmem, htgt, hfacet, htier⟩ := hfaith.backed actor src hopen hconf
  exact authorizedFacetB_holds_transfer_cap caps provided
    { actor := actor, src := src, dst := dst, amt := amt } c hmem htgt
    (by simpa [turnEffectBit] using hfacet) htier

/-! ### §6.G — the EFFECT-GENERAL faithfulness + bridge (residual (a): the facet axis over the turn's
ACTUAL effect, not the constant `EFFECT_TRANSFER`).

`DeployedFaithful`/`deployedCapOpen_implies_authorizedB` above pin the facet to `EFFECT_TRANSFER`, so
they only ever authorize transfer-facet caps. `DeployedFaithfulEff` carries the turn's ACTUAL
effect-kind bit `effectBit` and backs a `confersLeaf … effectBit` opening with a held cap whose facet
permits THAT bit; `deployedCapOpen_implies_authorizedEffB` concludes the GENERAL
`authorizedFacetEffB … effectBit`. The transfer case is the `EFFECT_TRANSFER` instance. -/

/-- **`DeployedFaithfulEff S vkOfTag provided effectBit caps root leafAt`** — the effect-general
faithfulness: every member leaf at an `(actor ⇒ src)` edge that confers `effectBit` (decoded facet
permits `effectBit`, decoded tier satisfied) is backed by a real held `FacetCap` over `src` whose facet
permits `effectBit`. `DeployedFaithful` is the `EFFECT_TRANSFER` instance. -/
structure DeployedFaithfulEff (vkOfTag : ℤ → Nat) (provided : AuthProvided) (effectBit : EffectMask)
    (caps : FacetCaps) (root : ℤ) (leafAt : Label → Label → CapLeaf) : Prop where
  /-- FAITHFULNESS: an `effectBit`-conferring member opening witnesses a REAL held `FacetCap` whose
  facet permits `effectBit` under a tier the `provided` auth satisfies. -/
  backed : ∀ (actor src : Label),
    MembersAt S root (leafAt actor src) →
    confersLeaf vkOfTag provided effectBit (leafAt actor src) →
    ∃ c : FacetCap, c ∈ caps actor ∧ c.target = src
      ∧ isEffectPermitted c.facet effectBit = true
      ∧ c.tier.isSatisfiedBy provided = true

/-- **`deployedCapOpen_implies_authorizedEffB` — THE EFFECT-GENERAL AUTHORITY BRIDGE.** Given the
effect-general commitment relation, AND an in-circuit opening whose leaf confers `effectBit` on BOTH
axes — THEN the GENERAL `authorizedFacetEffB … effectBit` PASSES. The cap-open membership discharges the
deployed two-axis gate over the turn's ACTUAL effect-kind, reusing `authorizedFacetEffB_holds_cap`. The
transfer bridge is `effectBit := EFFECT_TRANSFER`. -/
theorem deployedCapOpen_implies_authorizedEffB
    (vkOfTag : ℤ → Nat) (provided : AuthProvided) (effectBit : EffectMask)
    (caps : FacetCaps) (root : ℤ) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff S vkOfTag provided effectBit caps root leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hopen : MembersAt S root (leafAt actor src))
    (hconf : confersLeaf vkOfTag provided effectBit (leafAt actor src)) :
    authorizedFacetEffB caps provided effectBit
      { actor := actor, src := src, dst := dst, amt := amt } = true := by
  obtain ⟨c, hmem, htgt, hfacet, htier⟩ := hfaith.backed actor src hopen hconf
  exact authorizedFacetEffB_holds_cap caps provided effectBit
    { actor := actor, src := src, dst := dst, amt := amt } c hmem htgt hfacet htier

/-! ### §6.D — DISCHARGE: `DeployedFaithful*` is a CONSTRUCTION consequence, not a carried field.

`DeployedFaithful`/`DeployedFaithfulEff` carry a `backed` hypothesis: a conferring member opening at an
`(actor ⇒ src)` edge is backed by a REAL held `FacetCap`. The apex (`RotatedKernelRefinementFacet.
TransferAuthoritySource.hfaith`) consumes this as an ASSUMED structure field over a FREE `leafAt`. That
is the soundness analog of the ledger's faithfulness — and the ledger does NOT assume it: it BUILDS the
commitment from the kernel (`recStateCommit k` is a function OF `k`) and recovers `k` by CR injectivity
(`recStateCommit_binds_kernel`). The cap-tree side was MISSING that canonical builder, so `leafAt` floated
free and `backed` had to be carried.

This section supplies the missing builder. `canonicalLeafAt caps` is the leaf function the cap-tree
COMMITS — the deployed `compute_canonical_capability_root_felt` discipline (the cell builds its cap-tree
FROM its c-list, leaf-per-held-cap). For THAT canonical `leafAt`, `backed` is no longer a hypothesis: a
conferring leaf EXISTS only when it was built from a held conferring cap, so the witness is read off the
construction. `deployedFaithfulEff_canonical` discharges `DeployedFaithfulEff … (canonicalLeafAt caps)`
UNCONDITIONALLY (for ANY root — the faithfulness is structural in the encoding, the root binding is the
SEPARATE membership leg already discharged from CR by `capOpen_membership`). The carried `hfaith` field is
thereby reduced to "the prover opens against the CANONICAL leaf function" (the `hedge` identification the
source already carries), not an independent semantic contract over a free `leafAt`. -/

/-- **`tierTag t`** — the canonical `auth_tag` felt for a tier: the deployed `AuthTier.tierByte`
discriminant cast to ℤ (None=0…Custom=5; `cap_root.rs:46`). This is THE canonical forward encode the
cap-tree commits; `tierOfTag` is its inverse (`tierOfTag_tierTag` for the IPC tiers, `tierOfTag_tierByte`
for ALL tiers incl. `Custom` under the matching `vkOfTier`). Defined off `AuthTier.tierByte` so there is
ONE tier-byte map in the codebase. -/
def tierTag (t : AuthTier) : ℤ := (t.tierByte : ℤ)

/-- **`vkOfTier t`** — the vk-decode that recovers a tier's `Custom` vk-hash (constant; inert on the IPC
tiers, where `tierOfTag` ignores it). For `t = .custom vk` this makes `tierOfTag (vkOfTier t) 5 =
.custom vk`, so the tier round-trip `tierOfTag_tierByte` covers `Custom` too — the canonical tier decode
is total, the `vkOfTag` residual supplied by THIS witness on the `Custom` branch. -/
def vkOfTier : AuthTier → (ℤ → Nat)
  | .custom vk => fun _ => vk
  | _          => fun _ => 0

/-- **`tierOfTag_tierByte` — the tier decode INVERTS its own byte (with the matching vk-decode), for ALL
tiers.** Decoding `t.tierByte` under `vkOfTier t` recovers `t` — including `Custom` (the `vkOfTier`
witness supplies the vk on tag `5`). The canonical-leaf tier round-trip; the shared total inverse both
soundness (`canonicalLeaf`) and completeness (`authLeafAt`) read off. -/
theorem tierOfTag_tierByte (t : AuthTier) :
    tierOfTag (vkOfTier t) (t.tierByte : ℤ) = t := by
  cases t with
  | none => rfl
  | signature => rfl
  | proof => rfl
  | either => rfl
  | impossible => rfl
  | custom vk => rfl

/-- `tierOfTag` inverts `tierTag` on the five IPC tiers — the canonical tier encode round-trips through
the deployed `auth_tag` decode (so the decoded tier of a canonical leaf IS the cap's tier). The IPC
corollary of `tierOfTag_tierByte`: on a non-`Custom` tier `vkOfTier t` and any `vkOfTag` agree (both
ignored by `tierOfTag` on tags 0..4), so the round-trip holds for ANY `vkOfTag`. -/
theorem tierOfTag_tierTag (vkOfTag : ℤ → Nat) :
    ∀ t : AuthTier, (∀ vk, t ≠ .custom vk) →
      tierOfTag vkOfTag (tierTag t) = t := by
  intro t hipc
  cases t with
  | none => rfl
  | signature => rfl
  | proof => rfl
  | either => rfl
  | impossible => rfl
  | custom v =>
    -- the IPC side condition `hipc` excludes `Custom` (the named `vkOfTag` felt-absorb residual): a
    -- `Custom`-tier cap rides the `vkOfTag` residual, exactly as elsewhere. So this branch is vacuous.
    exact absurd rfl (hipc v)

/-- The canonical full mask for a cap's `Option EffectMask` facet: `none` (unrestricted) encodes as
`EFFECT_ALL` (`0xFFFF_FFFF`), `some m` encodes as `m`. For any single effect bit `1 <<< n` (`n < 32`),
`isEffectPermitted (some (canonMask facet)) (1<<<n) = isEffectPermitted facet (1<<<n)` — the encode is
facet-faithful on the bits the gate reads. -/
def canonMask : Option EffectMask → ℤ
  | .none   => ((0xFFFF_FFFF : Nat) : ℤ)
  | .some m => (m : ℤ)

/-- **`canonicalLeaf c`** — the canonical `CapLeaf` the deployed cap-tree commits for a held `FacetCap`
`c`: `target := c.target`, `auth_tag := tierTag c.tier`, the low/high 16-bit limbs of `canonMask c.facet`,
slot/expiry/breadstuff structural. This is the leaf `compute_canonical_capability_root_felt` builds from
a c-list entry. -/
def canonicalLeaf (c : FacetCap) : CapLeaf :=
  { slot_hash  := 0
  , target     := (c.target : ℤ)
  , auth_tag   := tierTag c.tier
  , mask_lo    := canonMask c.facet % 65536
  , mask_hi    := canonMask c.facet / 65536
  , expiry     := 0
  , breadstuff := 0 }

/-- The deny-all leaf (no cap held at an edge): `mask = 0` ⇒ `isEffectPermitted (some 0) _ = false`, so a
deny-all leaf NEVER confers — faithfulness off the held edges is vacuous. -/
def denyAllLeaf : CapLeaf :=
  { slot_hash := 0, target := 0, auth_tag := 0, mask_lo := 0, mask_hi := 0, expiry := 0, breadstuff := 0 }

/-- **`canonicalLeafAt caps`** — the leaf function the deployed cap-tree COMMITS (built FROM the c-list):
at edge `(actor, src)`, the canonical leaf of the FIRST held `FacetCap` over `src` in `caps actor` (the
c-list entry), or the deny-all leaf when the actor holds no cap over `src`. This is the cap-tree analog of
`recStateCommit`'s "build the leaves from the kernel" — the `leafAt` is no longer free; it is a FUNCTION
of `caps`. -/
def canonicalLeafAt (caps : FacetCaps) : Label → Label → CapLeaf := fun actor src =>
  match (caps actor).find? (fun c => decide (c.target = src)) with
  | some c => canonicalLeaf c
  | none   => denyAllLeaf

/-- The canonical leaf's decoded facet permits exactly the bits the cap's facet permits, on any single
effect bit `1 <<< n` (`n < 32`). The low/high limb split recomposes `canonMask`, so `facetOfLeaf
(canonicalLeaf c)` is `some (canonMask c.facet).toNat`, and `(1<<<n) &&& canonMask = (1<<<n) &&& (cap
mask)` agrees with the cap's `isEffectPermitted` on that bit. -/
theorem facetOfLeaf_canonical_permits (c : FacetCap) (n : Nat) (hn : n < 32)
    (hperm : isEffectPermitted c.facet (1 <<< n) = true) :
    isEffectPermitted (facetOfLeaf (canonicalLeaf c)) (1 <<< n) = true := by
  -- the limb split recomposes `canonMask c.facet` (a Nat `< 2^32`), so the decoded facet is its `.toNat`.
  have hrecomp : maskOfLimbs (canonicalLeaf c).mask_lo (canonicalLeaf c).mask_hi = canonMask c.facet := by
    simp only [canonicalLeaf, maskOfLimbs]
    have h := Int.emod_add_ediv_mul (canonMask c.facet) 65536
    linarith [h]
  have hfacet : facetOfLeaf (canonicalLeaf c) = some (canonMask c.facet).toNat := by
    simp only [facetOfLeaf, hrecomp]
  rw [hfacet]
  -- now compare to the cap's facet on bit `n`.
  cases hf : c.facet with
  | none =>
      -- canonMask none = EFFECT_ALL; isEffectPermitted (some 0xFFFFFFFF) (1<<<n) = true for n < 32.
      simp only [canonMask]
      show isEffectPermitted (some (((0xFFFF_FFFF : Nat) : ℤ)).toNat) (1 <<< n) = true
      have hcast : (((0xFFFF_FFFF : Nat) : ℤ)).toNat = (0xFFFF_FFFF : Nat) := Int.toNat_natCast _
      rw [hcast]
      unfold isEffectPermitted
      have hand : (1 <<< n) &&& (0xFFFF_FFFF : Nat) ≠ 0 := by
        have hpow : (1 <<< n : Nat) = 2 ^ n := by rw [Nat.shiftLeft_eq, Nat.one_mul]
        rw [hpow]
        intro hz
        have htb := Nat.testBit_and (2 ^ n) (0xFFFF_FFFF) n
        rw [hz] at htb
        simp only [Nat.zero_testBit, Nat.testBit_two_pow_self, Bool.true_and] at htb
        -- bit n of 0xFFFFFFFF is set for n < 32.
        have : (0xFFFF_FFFF : Nat).testBit n = true := by
          have : (0xFFFF_FFFF : Nat) = 2 ^ 32 - 1 := by norm_num
          rw [this, Nat.testBit_two_pow_sub_one]
          simp [hn]
        rw [this] at htb; exact Bool.noConfusion htb
      cases hm : (0xFFFF_FFFF : Nat) with
      | zero => simp at hm
      | succ k => simp only [hm] at hand ⊢; simp [hand]
  | some m =>
      -- canonMask (some m) = m; (m : ℤ).toNat = m; agrees with cap's isEffectPermitted.
      simp only [canonMask]
      show isEffectPermitted (some ((m : ℤ)).toNat) (1 <<< n) = true
      rw [Int.toNat_natCast]
      rw [hf] at hperm
      exact hperm

/-- The canonical leaf's decoded tier IS the cap's tier (on the IPC tiers; `Custom` rides `vkOfTag`),
so a `provided` satisfying the cap's tier satisfies the decoded tier. -/
theorem tierOfTag_canonical (vkOfTag : ℤ → Nat) (c : FacetCap)
    (hipc : ∀ vk, c.tier ≠ .custom vk) :
    tierOfTag vkOfTag (canonicalLeaf c).auth_tag = c.tier := by
  simp only [canonicalLeaf]
  exact tierOfTag_tierTag vkOfTag c.tier hipc

/-- **`deployedFaithfulEff_canonical` — THE DISCHARGE (`backed` from the CONSTRUCTION, not assumed).**
For the CANONICAL leaf function `canonicalLeafAt caps` (the leaves the cap-tree actually commits, built
from the c-list), `DeployedFaithfulEff` holds for ANY root and ANY single effect bit `1 <<< n` (`n < 32`)
— with NO carried faithfulness hypothesis. The `backed` obligation is discharged STRUCTURALLY: a leaf at
`(actor, src)` confers `1<<<n` only when it is `canonicalLeaf` of a held cap over `src` whose facet
permits `1<<<n` and whose decoded tier (= the cap's tier on the IPC tiers) is satisfied — so the held cap
IS the witness, read off `find?`. (The IPC-tier side condition `hipc` excludes the named `Custom`/`vkOfTag`
residual.) This turns the apex's `hfaith` FIELD into a consequence of "the prover opens the CANONICAL
tree". -/
theorem deployedFaithfulEff_canonical {State : Type} (S : CapHashScheme State)
    (vkOfTag : ℤ → Nat) (provided : AuthProvided) (n : Nat) (hn : n < 32)
    (caps : FacetCaps) (root : ℤ)
    (hipc : ∀ (actor src : Label) (c : FacetCap),
      c ∈ caps actor → c.target = src → ∀ vk, c.tier ≠ .custom vk) :
    DeployedFaithfulEff S vkOfTag provided (1 <<< n) caps root (canonicalLeafAt caps) := by
  refine ⟨?_⟩
  intro actor src _hopen hconf
  obtain ⟨hfacetConf, htierConf⟩ := hconf
  -- the canonical leaf at (actor, src) is either a held cap's leaf or the deny-all leaf.
  unfold canonicalLeafAt at hfacetConf htierConf
  cases hfind : (caps actor).find? (fun c => decide (c.target = src)) with
  | none =>
      -- deny-all leaf: mask 0 ⇒ isEffectPermitted (some 0) _ = false, contradicting hfacetConf.
      exfalso
      rw [hfind] at hfacetConf
      simp only [denyAllLeaf, facetOfLeaf, maskOfLimbs] at hfacetConf
      -- mask 0 + 0*65536 = 0 ⇒ (0 : ℤ).toNat = 0 ⇒ isEffectPermitted (some 0) _ = false.
      rw [show ((0 : ℤ) + 0 * 65536).toNat = 0 by decide] at hfacetConf
      simp only [isEffectPermitted] at hfacetConf
      exact Bool.noConfusion hfacetConf
  | some c =>
      rw [hfind] at hfacetConf htierConf
      -- `find?` found a held cap `c` over `src`.
      have hmem : c ∈ caps actor := List.mem_of_find?_eq_some hfind
      have htgt : c.target = src := by
        have := List.find?_some hfind
        simpa using of_decide_eq_true this
      -- the cap's facet permits 1<<<n: the canonical leaf's decoded facet permits it (hfacetConf), and
      -- the encode agrees with the cap's facet on the bit.
      have hcapFacet : isEffectPermitted c.facet (1 <<< n) = true := by
        cases hf : c.facet with
        | none =>
            -- none (unrestricted) always permits.
            simp [isEffectPermitted]
        | some m =>
            -- some m: the canonical leaf decodes facet to (m).toNat, agreeing with the cap on the bit.
            have hrecomp : maskOfLimbs (canonicalLeaf c).mask_lo (canonicalLeaf c).mask_hi
                = canonMask c.facet := by
              simp only [canonicalLeaf, maskOfLimbs]
              have h := Int.emod_add_ediv_mul (canonMask c.facet) 65536
              linarith [h]
            have hfacetEq : facetOfLeaf (canonicalLeaf c) = some (canonMask c.facet).toNat := by
              simp only [facetOfLeaf, hrecomp]
            rw [hfacetEq, hf] at hfacetConf
            simp only [canonMask] at hfacetConf
            rw [Int.toNat_natCast] at hfacetConf
            exact hfacetConf
      -- the decoded tier IS the cap's tier (IPC), so `provided` satisfies the cap's tier.
      have htierEq : tierOfTag vkOfTag (canonicalLeaf c).auth_tag = c.tier :=
        tierOfTag_canonical vkOfTag c (hipc actor src c hmem htgt)
      rw [htierEq] at htierConf
      exact ⟨c, hmem, htgt, hcapFacet, htierConf⟩

end CapHashScheme

/-! ## §5b — the NATIVE 8-FELT cap tree (Phase H-CAP-8): the `node8` arity-16 chip compression.

The deployed `cap_root.rs` cap tree is now 8-FELT (`CAP_DIGEST_W = 8`): a leaf/node/root is a
length-8 vector. `CapLeaf::digest = chip_absorb_all_lanes(7, leafFields)` (8 squeezed lanes) and
`cap_node8 = chip_absorb_all_lanes(16, L8 ‖ R8)` (the arity-16 `node8` compression). The per-node
collision floor is the FULL 8-felt width (~124-bit), matching the deployed FRI/STARK soundness — vs
the lossy 1-felt `nodeOf` (kept above for the out-of-scope DSL AIR).

THE MIGRATION IS A RE-INSTANTIATION: the membership anti-ghost rides the SAME
`CapMerkleGeneric.recomposeG_inj_of_path` the 1-felt tree now delegates to — there is NO spine
re-proof. The ONLY new obligation is `nodeOf8_injective` (the arity-16 chip's collision-resistance),
discharged from the named `Compress8CR` floor exactly as `nodeOf_injective` rides `Compress1CR`. -/

/-- The 8-felt cap-tree digest carrier (`cap_root.rs::CAP_DIGEST_W = 8`): a leaf / node / root is a
length-8 felt vector (`[BabyBear; 8]`), modeled as `Fin 8 → ℤ`. -/
abbrev Digest8 := Fin 8 → ℤ

/-- ⚠ **NOT A FLOOR — FALSE AT DEPLOYED PARAMETERS. It is no longer a field of anything in this file.**

`Compress8CR f` says the 8-output chip absorb `f : List ℤ → Digest8`
(`descriptor_ir2::chip_absorb_all_lanes`, all 8 squeezed lanes) is INJECTIVE: equal 8-felt output
vectors force equal input lists. `VacuitySweepTeeth.compress8CR_false_babyBear` proves this FALSE for
the deployed chip — it compresses the infinite `List ℤ` into 8 BOUNDED BabyBear lanes, so collisions
EXIST by pigeonhole.

⚑ **IT USED TO BE THE `Cap8Scheme.chip8CR` FIELD, and that made `Cap8Scheme` UNINHABITABLE**: not
merely a hypothesis on a theorem but a non-constructible field, so EVERY theorem of the form
`∀ S8 : Cap8Scheme, …` — the whole cap-family surface — was VACUOUS. The field is DELETED (§5b below);
`Cap8Scheme` now carries the chip and nothing false about it, and §5b.D exhibits a real deployed
inhabitant. The old "non-vacuity" argument (`Reference8` exhibits an injective chip, `badChip8_not_CR`
falsifies a colliding one) was exactly the FALSE COMFORT `HashFloorHonesty`'s header named: **toy
witness satisfiable, real compressing Poseidon2 false.**

**WHAT IT IS RETAINED FOR — two honest jobs, neither of them a deployed keystone:**
  1. the INJECTIVE SPECIAL CASE in the strength-relation bridges (`…_of_injective` in §5b), which show
     the deleted theorems fall straight out of the new disjunctions once you assume it — so nothing
     genuinely proved was given up by the deletion; and
  2. the refutability canaries (`coll8_refutable_of_injective`), which show the collision disjunct is
     not a free pass.
⚑ **AND THE CLASS IS NOW CLOSED (2026-07-20).** The sibling `DeployedHeapTree.Heap8Scheme` and
`DeployedFieldsTree.Fields8Scheme` carried the IDENTICAL field; both are deleted, both structures have
constructed deployed inhabitants (`deployedHeap8Scheme` / `deployedFields8Scheme`), and
`VacuitySweepTeeth` §1‴-HF fires the refutation tooth at each. `Compress8CR` is a field of NOTHING.

**RE-GROUNDED (probabilistic residual):** `Circuit.InjectiveFloorRegrounded` §1 — `Chip8Keyed` is the
deployed chip carrying no CR field, and `node8_injective_advantage_bound` /
`leaf8_injective_advantage_bound` bound the probability that an adversary in a named class `Eff`
produces the collision disjunct, with the `Eff` obligation in the open. -/
def Compress8CR (f : List ℤ → Digest8) : Prop :=
  ∀ a b : List ℤ, f a = f b → a = b

/-- **`Coll8 f p`** — the pair of input lists `p` is a GENUINE collision of the 8-output chip absorb:
two DISTINCT lists with the SAME 8-felt image.

Note what this is NOT: it is not `∃ a b, f a = f b ∧ a ≠ b`. At deployed parameters that existence
claim is UNCONDITIONALLY TRUE by pigeonhole (`compress8CR_false_babyBear` proves precisely it), so a
disjunct of that shape would be a free pass carrying no more content than `True`. `Coll8` is a
predicate about the SPECIFIC pair an extractor RETURNS, so a theorem concluding it EXHIBITS the
collision rather than asserting one exists — and it is REFUTABLE (`coll8_refutable_of_injective`). -/
def Coll8 (f : List ℤ → Digest8) (p : List ℤ × List ℤ) : Prop :=
  p.1 ≠ p.2 ∧ f p.1 = f p.2

/-- "Is this pair a genuine chip collision?" is DECIDABLE (`List ℤ` and `Digest8` both have decidable
equality) — so the extractors may branch on it and stay TOTAL functions, no `Classical.choice` in the
reduction. -/
instance decidableColl8 (f : List ℤ → Digest8) (p : List ℤ × List ℤ) : Decidable (Coll8 f p) := by
  unfold Coll8
  infer_instance

/-- **`Cap8Scheme`** — the native-8-felt cap-tree's SINGLE Poseidon2 carrier: the 8-output chip absorb
`chipAbsorb8 : List ℤ → Digest8`. BOTH the leaf (`capLeafDigest8`, arity 7) and the node
(`nodeOf8`, arity 16) ride it; the input lists are length-disjoint (7 vs 16), so the chip's per-row
`(arity, padded inputs)` seeding separates the two domains for free.

⚑ **ONE FIELD, AND IT IS INHABITED.** The `chip8CR : Compress8CR chipAbsorb8` field is GONE. It
asserted injectivity of a map that squeezes an infinite domain into 8 bounded BabyBear lanes, which the
deployed chip refutes — so no deployed `Cap8Scheme` value could be constructed and every theorem
quantifying over this type was vacuous. §5b.D constructs `deployedCap8Scheme`, a real value whose chip
is deployed-shaped (BabyBear-bounded lanes) and whose own chip therefore REFUTES the deleted field
(`VacuitySweepTeeth.deployedCap8Scheme_chip_not_Compress8CR`). The collision resistance the tree used
to assume is now EXTRACTED AS DATA instead: see `Coll8` and the `…_binds_or_collides` family. -/
structure Cap8Scheme where
  /-- The single 8-output chip-absorb compression (`cap_root.rs::cap_node8`/`CapLeaf::digest`). -/
  chipAbsorb8 : List ℤ → Digest8

namespace Cap8Scheme

variable (S8 : Cap8Scheme)

/-- Pack two 8-felt children into the arity-16 `node8` input block `L8 ‖ R8`
(`cap_root.rs::cap_node8`: `ins[..8] = l; ins[8..] = r`). -/
def pack8 (l r : Digest8) : List ℤ := List.ofFn l ++ List.ofFn r

/-- `pack8` is injective in `(l, r)`: the two length-8 halves split uniquely (equal lengths) and
`List.ofFn` is injective. The structural twin of `packNode_inj`, at vector width 8. -/
theorem pack8_inj {l₁ r₁ l₂ r₂ : Digest8} (h : pack8 l₁ r₁ = pack8 l₂ r₂) :
    l₁ = l₂ ∧ r₁ = r₂ := by
  unfold pack8 at h
  have hlen : (List.ofFn l₁).length = (List.ofFn l₂).length := by simp
  obtain ⟨hl, hr⟩ := List.append_inj h hlen
  exact ⟨List.ofFn_inj.mp hl, List.ofFn_inj.mp hr⟩

/-- **`capLeafDigest8 S8 l`** — the 8-felt deployed leaf digest, the SINGLE 8-output chip absorb over
the 7 leaf fields. BYTE-IDENTICAL to `cap_root.rs::CapLeaf::digest`. -/
def capLeafDigest8 (l : CapLeaf) : Digest8 := S8.chipAbsorb8 (leafFields l)

/-- **`nodeOf8 S8 l r`** — the native 8-felt internal node, the arity-16 chip absorb over
`pack8 l r = L8 ‖ R8`. BYTE-IDENTICAL to `cap_root.rs::cap_node8`. The SAME `chipAbsorb8` carrier as
the leaf — one cap hash everywhere. -/
def nodeOf8 (l r : Digest8) : Digest8 := S8.chipAbsorb8 (pack8 l r)

/-! ### §5b.X — BINDING, EXTRACTED AS DATA (the sound replacement for the deleted injectivity family).

The three theorems this section replaces — `capLeafDigest8_injective`, `nodeOf8_injective`,
`recomposeUp8_inj_of_path` — were all discharged from the `chip8CR` FIELD, i.e. from
`Compress8CR chipAbsorb8`, which the deployed chip refutes. They are DELETED, not kept beside the new
forms: keeping them is what made the earlier regrounding additive and therefore inert.

Each is replaced by a TOTAL EXTRACTOR plus a theorem that what it returns is a genuine collision. The
conclusions are disjunctions `binding ∨ Coll8 chipAbsorb8 (the pair the extractor returned)`. As
FORMULAS they are weaker than the equalities they replace; as CONTENT AT DEPLOYED PARAMETERS they are
strictly stronger, because the deleted premise is unsatisfiable by the real chip — the old theorems
said nothing about the deployed system, and these hold OF it. §5b.S proves that relation in both
directions. -/

/-- The leaf extractor: the two 7-field blocks the arity-7 chip absorbed. -/
def leafColl8Find (l₁ l₂ : CapLeaf) : List ℤ × List ℤ := (leafFields l₁, leafFields l₂)

/-- **Leaf binding at 8-felt width, UNCONDITIONAL** (replaces `capLeafDigest8_injective`). Equal 8-felt
leaf digests EITHER force the whole 7-field `CapLeaf` equal, OR the two `leafFields` blocks ARE a
genuine collision of the deployed chip — handed back by name. -/
theorem capLeafDigest8_binds_or_collides {l₁ l₂ : CapLeaf}
    (h : capLeafDigest8 S8 l₁ = capLeafDigest8 S8 l₂) :
    l₁ = l₂ ∨ Coll8 S8.chipAbsorb8 (leafColl8Find l₁ l₂) := by
  by_cases hl : l₁ = l₂
  · exact Or.inl hl
  · exact Or.inr ⟨fun hf => hl (leafFields_inj hf), h⟩

/-- The node extractor: the two arity-16 `L8 ‖ R8` input blocks. -/
def nodeColl8Find (l₁ r₁ l₂ r₂ : Digest8) : List ℤ × List ℤ := (pack8 l₁ r₁, pack8 l₂ r₂)

/-- **Node binding at 8-felt width, UNCONDITIONAL** (replaces `nodeOf8_injective`, the "SOLE
width-specific obligation" the whole native-8-felt tree used to ride). Equal `node8` images EITHER force
equal 8-felt children, OR the two packed arity-16 blocks ARE a genuine chip collision. -/
theorem nodeOf8_binds_or_collides {l₁ r₁ l₂ r₂ : Digest8}
    (h : nodeOf8 S8 l₁ r₁ = nodeOf8 S8 l₂ r₂) :
    (l₁ = l₂ ∧ r₁ = r₂) ∨ Coll8 S8.chipAbsorb8 (nodeColl8Find l₁ r₁ l₂ r₂) := by
  by_cases hn : l₁ = l₂ ∧ r₁ = r₂
  · exact Or.inl hn
  · exact Or.inr ⟨fun hp => hn (pack8_inj hp), h⟩

/-- **`recomposeUp8 S8 cur path`** — the native-8-felt membership recompose, DEFINED as the generic
`CapMerkleGeneric.recomposeG` at `D := Digest8`, `node := nodeOf8 S8`. No bespoke recursion. -/
def recomposeUp8 (cur : Digest8) (path : List (CapMerkleGeneric.StepG Digest8)) : Digest8 :=
  CapMerkleGeneric.recomposeG (nodeOf8 S8) cur path

/-- **The native-8-felt spine EXTRACTOR** — the generic path walk
(`CapMerkleGeneric.recomposeGFind`) at `node := nodeOf8 S8`, with the colliding child-pairs it lands on
mapped through `pack8` into the two arity-16 chip input blocks. A TOTAL function of the two starting
digests and the path. -/
def recomposeUp8Find (a b : Digest8) (path : List (CapMerkleGeneric.StepG Digest8)) :
    List ℤ × List ℤ :=
  (pack8 (CapMerkleGeneric.recomposeGFind (nodeOf8 S8) a b path).1.1
         (CapMerkleGeneric.recomposeGFind (nodeOf8 S8) a b path).1.2,
   pack8 (CapMerkleGeneric.recomposeGFind (nodeOf8 S8) a b path).2.1
         (CapMerkleGeneric.recomposeGFind (nodeOf8 S8) a b path).2.2)

/-- **The native-8-felt anti-ghost spine, UNCONDITIONAL** (replaces `recomposeUp8_inj_of_path`). Equal
recomposed roots along a FIXED path EITHER force equal starting 8-felt digests, OR the walk LANDS on a
level whose two arity-16 `node8` blocks are a genuine chip collision, returned by name. A prover cannot
keep the published root while swapping the opened leaf UNLESS the deployed chip actually collides at
the two blocks this extractor hands back.

Still a PURE RE-INSTANTIATION — `CapMerkleGeneric.recomposeGFind_spec` is proved once, generically. -/
theorem recomposeUp8_binds_or_collides (path : List (CapMerkleGeneric.StepG Digest8))
    {a b : Digest8} (h : recomposeUp8 S8 a path = recomposeUp8 S8 b path) :
    a = b ∨ Coll8 S8.chipAbsorb8 (recomposeUp8Find S8 a b path) := by
  rcases CapMerkleGeneric.recomposeGFind_spec (nodeOf8 S8) path h with heq | ⟨hne, himg⟩
  · exact Or.inl heq
  · refine Or.inr ⟨fun hp => hne ?_, himg⟩
    exact Prod.ext (pack8_inj hp).1 (pack8_inj hp).2

/-- **THE CAP-OPEN EXTRACTOR** — the SINGLE named pair the whole cap-open peel hands back. Run the
spine walk over the two leaf digests; if it found a genuine collision that is the answer, otherwise the
walk has already forced the two leaf DIGESTS equal, so the collision (if any) is at the leaf absorb and
the two `leafFields` blocks are the pair. -/
def capOpen8Find (nl₁ nl₂ : CapLeaf) (path : List (CapMerkleGeneric.StepG Digest8)) :
    List ℤ × List ℤ :=
  if Coll8 S8.chipAbsorb8
      (recomposeUp8Find S8 (capLeafDigest8 S8 nl₁) (capLeafDigest8 S8 nl₂) path)
  then recomposeUp8Find S8 (capLeafDigest8 S8 nl₁) (capLeafDigest8 S8 nl₂) path
  else leafColl8Find nl₁ nl₂

/-- **`CapOpenColl S8 nl₁ nl₂ path`** — the pair `capOpen8Find` RETURNS on this equivocation is a
genuine collision of the deployed arity-16 chip. The ONE named disjunct every cap-open consumer carries
in place of the deleted `chip8CR` floor. -/
def CapOpenColl (nl₁ nl₂ : CapLeaf) (path : List (CapMerkleGeneric.StepG Digest8)) : Prop :=
  Coll8 S8.chipAbsorb8 (capOpen8Find S8 nl₁ nl₂ path)

/-- **⚑ THE CAP-OPEN ANTI-GHOST TOOTH, UNCONDITIONAL.** Two leaves opening to the SAME 8-felt root
along the SAME committed path are EITHER the same leaf, OR the deployed chip genuinely collides at the
two blocks `capOpen8Find` hands back. This is the composition
`recomposeUp8_binds_or_collides ∘ capLeafDigest8_binds_or_collides` the whole cap family rides, with the
two possible collision sites resolved into one named pair. -/
theorem capOpen8_binds_leaf_or_collides (path : List (CapMerkleGeneric.StepG Digest8))
    {nl₁ nl₂ : CapLeaf}
    (h : recomposeUp8 S8 (capLeafDigest8 S8 nl₁) path
       = recomposeUp8 S8 (capLeafDigest8 S8 nl₂) path) :
    nl₁ = nl₂ ∨ CapOpenColl S8 nl₁ nl₂ path := by
  by_cases hif : Coll8 S8.chipAbsorb8
      (recomposeUp8Find S8 (capLeafDigest8 S8 nl₁) (capLeafDigest8 S8 nl₂) path)
  · refine Or.inr ?_
    show Coll8 S8.chipAbsorb8 (capOpen8Find S8 nl₁ nl₂ path)
    rw [capOpen8Find, if_pos hif]
    exact hif
  · rcases recomposeUp8_binds_or_collides S8 path h with hdig | hc
    · rcases capLeafDigest8_binds_or_collides S8 hdig with hl | hlc
      · exact Or.inl hl
      · refine Or.inr ?_
        show Coll8 S8.chipAbsorb8 (capOpen8Find S8 nl₁ nl₂ path)
        rw [capOpen8Find, if_neg hif]
        exact hlc
    · exact absurd hc hif

/-! ### §5b.S — THE STRENGTH RELATION, both directions (no strength was lost; no free pass was gained).

Deleting a carrier and restating its consumers as disjunctions invites two fair objections. Both are
answered here in Lean rather than in prose.

1. *"You weakened the theorems to make the deletion easy."* — the `…_of_injective` bridges assume
   exactly the injectivity the deleted field asserted, and the deleted theorems fall straight out. They
   are precisely the injective special case of the new ones.
2. *"The right disjunct is a free pass, so the disjunction says nothing."* — `coll8_refutable_of_injective`
   shows the collision disjunct is REFUTABLE: at an injective chip the extracted pair is NOT a
   collision, so the binding half has to do the work.

These are STANDALONE bridges, deliberately NOT hypotheses on any deployed keystone: `Compress8CR` is
FALSE at deployed BabyBear parameters, so a keystone carrying it would be right back where this repair
started. -/

/-- **(CANARY — the collision disjunct is REFUTABLE.)** At an injective chip NO pair is a collision, so
none of the `…_or_collides` theorems can discharge itself by taking the right branch. -/
theorem coll8_refutable_of_injective {f : List ℤ → Digest8} (hCR : Compress8CR f)
    (p : List ℤ × List ℤ) : ¬ Coll8 f p := by
  rintro ⟨hne, himg⟩
  exact hne (hCR _ _ himg)

/-- **(CANARY at the cap-open composite.)** `CapOpenColl` is refutable at an injective chip. -/
theorem capOpenColl_refutable_of_injective (hCR : Compress8CR S8.chipAbsorb8)
    (nl₁ nl₂ : CapLeaf) (path : List (CapMerkleGeneric.StepG Digest8)) :
    ¬ CapOpenColl S8 nl₁ nl₂ path :=
  coll8_refutable_of_injective hCR _

/-- **NO STRENGTH LOST — the deleted `capLeafDigest8_injective` is the injective special case.** -/
theorem capLeafDigest8_injective_of_injective (hCR : Compress8CR S8.chipAbsorb8)
    {l₁ l₂ : CapLeaf} (h : capLeafDigest8 S8 l₁ = capLeafDigest8 S8 l₂) : l₁ = l₂ := by
  rcases capLeafDigest8_binds_or_collides S8 h with hl | hc
  · exact hl
  · exact absurd hc (coll8_refutable_of_injective hCR _)

/-- **NO STRENGTH LOST — the deleted `nodeOf8_injective` is the injective special case.** -/
theorem nodeOf8_injective_of_injective (hCR : Compress8CR S8.chipAbsorb8)
    {l₁ r₁ l₂ r₂ : Digest8} (h : nodeOf8 S8 l₁ r₁ = nodeOf8 S8 l₂ r₂) : l₁ = l₂ ∧ r₁ = r₂ := by
  rcases nodeOf8_binds_or_collides S8 h with hn | hc
  · exact hn
  · exact absurd hc (coll8_refutable_of_injective hCR _)

/-- **NO STRENGTH LOST — the deleted `recomposeUp8_inj_of_path` is the injective special case.** -/
theorem recomposeUp8_inj_of_path_of_injective (hCR : Compress8CR S8.chipAbsorb8)
    (path : List (CapMerkleGeneric.StepG Digest8)) {a b : Digest8}
    (h : recomposeUp8 S8 a path = recomposeUp8 S8 b path) : a = b := by
  rcases recomposeUp8_binds_or_collides S8 path h with heq | hc
  · exact heq
  · exact absurd hc (coll8_refutable_of_injective hCR _)

/-- **NO STRENGTH LOST at the composite** — the cap-open peel the cap family used to perform
(`capLeafDigest8_injective ∘ recomposeUp8_inj_of_path`) is the injective special case of
`capOpen8_binds_leaf_or_collides`. -/
theorem capOpen8_binds_leaf_of_injective (hCR : Compress8CR S8.chipAbsorb8)
    (path : List (CapMerkleGeneric.StepG Digest8)) {nl₁ nl₂ : CapLeaf}
    (h : recomposeUp8 S8 (capLeafDigest8 S8 nl₁) path
       = recomposeUp8 S8 (capLeafDigest8 S8 nl₂) path) : nl₁ = nl₂ := by
  rcases capOpen8_binds_leaf_or_collides S8 path h with hl | hc
  · exact hl
  · exact absurd hc (capOpenColl_refutable_of_injective S8 hCR _ _ _)

/-! ### §5b.M — the NATIVE 8-FELT membership predicate + the effect-general authority bridge.

The 8-felt twin of `CapHashScheme.MembersAt` / `deployedCapOpen_implies_authorizedEffB`. The membership
predicate `MembersAt8` opens against the FULL 8-felt root (so a colliding 1-felt-lane-0 leaf no longer
opens — the GENTIAN tooth bites at ~124-bit), and the authority bridge is a PURE RE-INSTANTIATION: the
backward read (`backed`) into `authorizedFacetEffB` is leaf-based and width-agnostic, so the body is the
1-felt proof verbatim with `MembersAt → MembersAt8`, `root : ℤ → Digest8`, `S → S8`. -/

open CapHashScheme
  (confersLeaf canonicalLeaf denyAllLeaf canonicalLeafAt facetOfLeaf maskOfLimbs canonMask tierTag
   tierOfTag tierOfTag_canonical)

/-- **`MembersAt8 S8 root leaf`** — the native-8-felt deployed-tree membership: a sibling/direction
path recomposes the FULL 8-felt `root` from the 8-felt leaf digest. The HONEST 8-felt replacement for
the lossy 1-felt `CapHashScheme.MembersAt` — opens against ~124-bit of root, not lane-0. -/
def MembersAt8 (root : Digest8) (leaf : CapLeaf) : Prop :=
  ∃ path : List (CapMerkleGeneric.StepG Digest8),
    recomposeUp8 S8 (capLeafDigest8 S8 leaf) path = root

/-- **`DeployedFaithfulEff8`** — the 8-felt effect-general faithfulness: every member leaf at an
`(actor ⇒ src)` edge conferring `effectBit` is backed by a real held `FacetCap` permitting `effectBit`.
The 8-felt twin of `CapHashScheme.DeployedFaithfulEff` (membership over `MembersAt8`, root 8-felt). -/
structure DeployedFaithfulEff8 (vkOfTag : ℤ → Nat) (provided : AuthProvided) (effectBit : EffectMask)
    (caps : FacetCaps) (root : Digest8) (leafAt : Label → Label → CapLeaf) : Prop where
  /-- FAITHFULNESS: an `effectBit`-conferring 8-felt member opening witnesses a REAL held `FacetCap`. -/
  backed : ∀ (actor src : Label),
    MembersAt8 S8 root (leafAt actor src) →
    confersLeaf vkOfTag provided effectBit (leafAt actor src) →
    ∃ c : FacetCap, c ∈ caps actor ∧ c.target = src
      ∧ isEffectPermitted c.facet effectBit = true
      ∧ c.tier.isSatisfiedBy provided = true

/-- **`DeployedFaithful8`** — the 8-felt TRANSFER-facet faithfulness (the `EFFECT_TRANSFER` instance of
`DeployedFaithfulEff8`). Membership over `MembersAt8`, root 8-felt. -/
structure DeployedFaithful8 (vkOfTag : ℤ → Nat) (provided : AuthProvided)
    (caps : FacetCaps) (root : Digest8) (leafAt : Label → Label → CapLeaf) : Prop where
  /-- FAITHFULNESS: a transfer-conferring 8-felt member opening witnesses a REAL held `FacetCap`. -/
  backed : ∀ (actor src : Label),
    MembersAt8 S8 root (leafAt actor src) →
    CapHashScheme.confersTransferLeaf vkOfTag provided (leafAt actor src) →
    ∃ c : FacetCap, c ∈ caps actor ∧ c.target = src
      ∧ isEffectPermitted c.facet EFFECT_TRANSFER = true
      ∧ c.tier.isSatisfiedBy provided = true

/-- **`deployedCapOpen8_implies_authorizedB` — THE 8-FELT TRANSFER AUTHORITY BRIDGE.** The 8-felt twin
of `CapHashScheme.deployedCapOpen_implies_authorizedB`. -/
theorem deployedCapOpen8_implies_authorizedB
    (vkOfTag : ℤ → Nat) (provided : AuthProvided)
    (caps : FacetCaps) (root : Digest8) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithful8 S8 vkOfTag provided caps root leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hopen : MembersAt8 S8 root (leafAt actor src))
    (hconf : CapHashScheme.confersTransferLeaf vkOfTag provided (leafAt actor src)) :
    authorizedFacetB caps provided { actor := actor, src := src, dst := dst, amt := amt } = true := by
  obtain ⟨c, hmem, htgt, hfacet, htier⟩ := hfaith.backed actor src hopen hconf
  exact authorizedFacetB_holds_transfer_cap caps provided
    { actor := actor, src := src, dst := dst, amt := amt } c hmem htgt
    (by simpa [turnEffectBit] using hfacet) htier

/-- **`deployedCapOpen8_implies_authorizedEffB` — THE 8-FELT EFFECT-GENERAL AUTHORITY BRIDGE.** Given
the 8-felt commitment relation AND an 8-felt opening whose leaf confers `effectBit` on BOTH axes, the
GENERAL `authorizedFacetEffB … effectBit` PASSES. A RE-INSTANTIATION of the 1-felt bridge — the
backward read is identical; only the membership width changes. -/
theorem deployedCapOpen8_implies_authorizedEffB
    (vkOfTag : ℤ → Nat) (provided : AuthProvided) (effectBit : EffectMask)
    (caps : FacetCaps) (root : Digest8) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff8 S8 vkOfTag provided effectBit caps root leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hopen : MembersAt8 S8 root (leafAt actor src))
    (hconf : confersLeaf vkOfTag provided effectBit (leafAt actor src)) :
    authorizedFacetEffB caps provided effectBit
      { actor := actor, src := src, dst := dst, amt := amt } = true := by
  obtain ⟨c, hmem, htgt, hfacet, htier⟩ := hfaith.backed actor src hopen hconf
  exact authorizedFacetEffB_holds_cap caps provided effectBit
    { actor := actor, src := src, dst := dst, amt := amt } c hmem htgt hfacet htier

/-- **`deployedFaithfulEff_canonical8` — THE 8-FELT DISCHARGE (`backed` from the CONSTRUCTION).** For
the CANONICAL leaf function `canonicalLeafAt caps`, `DeployedFaithfulEff8` holds for ANY 8-felt root and
ANY single effect bit `1 <<< n` (`n < 32`) with NO carried faithfulness hypothesis — the membership
witness is ignored (the conferring leaf existence is structural in the c-list encoding). Verbatim the
1-felt `deployedFaithfulEff_canonical` proof (which already discards `_hopen`). -/
theorem deployedFaithfulEff_canonical8
    (vkOfTag : ℤ → Nat) (provided : AuthProvided) (n : Nat) (hn : n < 32)
    (caps : FacetCaps) (root : Digest8)
    (hipc : ∀ (actor src : Label) (c : FacetCap),
      c ∈ caps actor → c.target = src → ∀ vk, c.tier ≠ .custom vk) :
    DeployedFaithfulEff8 S8 vkOfTag provided (1 <<< n) caps root (canonicalLeafAt caps) := by
  refine ⟨?_⟩
  intro actor src _hopen hconf
  obtain ⟨hfacetConf, htierConf⟩ := hconf
  unfold canonicalLeafAt at hfacetConf htierConf
  cases hfind : (caps actor).find? (fun c => decide (c.target = src)) with
  | none =>
      exfalso
      rw [hfind] at hfacetConf
      simp only [denyAllLeaf, facetOfLeaf, maskOfLimbs] at hfacetConf
      rw [show ((0 : ℤ) + 0 * 65536).toNat = 0 by decide] at hfacetConf
      simp only [isEffectPermitted] at hfacetConf
      exact Bool.noConfusion hfacetConf
  | some c =>
      rw [hfind] at hfacetConf htierConf
      have hmem : c ∈ caps actor := List.mem_of_find?_eq_some hfind
      have htgt : c.target = src := by
        have := List.find?_some hfind
        simpa using of_decide_eq_true this
      have hcapFacet : isEffectPermitted c.facet (1 <<< n) = true := by
        cases hf : c.facet with
        | none => simp [isEffectPermitted]
        | some m =>
            have hrecomp : maskOfLimbs (canonicalLeaf c).mask_lo (canonicalLeaf c).mask_hi
                = canonMask c.facet := by
              simp only [canonicalLeaf, maskOfLimbs]
              have h := Int.emod_add_ediv_mul (canonMask c.facet) 65536
              linarith [h]
            have hfacetEq : facetOfLeaf (canonicalLeaf c) = some (canonMask c.facet).toNat := by
              simp only [facetOfLeaf, hrecomp]
            rw [hfacetEq, hf] at hfacetConf
            simp only [canonMask] at hfacetConf
            rw [Int.toNat_natCast] at hfacetConf
            exact hfacetConf
      have htierEq : tierOfTag vkOfTag (canonicalLeaf c).auth_tag = c.tier :=
        tierOfTag_canonical vkOfTag c (hipc actor src c hmem htgt)
      rw [htierEq] at htierConf
      exact ⟨c, hmem, htgt, hcapFacet, htierConf⟩

end Cap8Scheme

/-! ### §5b.D — ⚑ THE ACCEPTANCE TEST: a REAL DEPLOYED `Cap8Scheme` VALUE.

The whole point of deleting the `chip8CR` field is measured HERE, not by a green build. With the field
present, `Cap8Scheme` had no deployed inhabitant (`VacuitySweepTeeth.compress8CR_false_babyBear` refutes
the field for any function that lands in bounded BabyBear lanes, which the deployed chip does), so every
`∀ S8 : Cap8Scheme, …` theorem — the entire cap-family surface — was vacuously true.

`deployedCap8Scheme` below is a VALUE. Its chip is DEPLOYED-SHAPED in the only respect this argument
ever turned on: it squeezes an arbitrary-length `List ℤ` into eight lanes each reduced into `[0, p)` for
the deployed BabyBear prime, exactly like `descriptor_ir2::chip_absorb_all_lanes`. Nothing about a real
Poseidon2 round schedule is relevant to inhabitation — and, decisively, its own chip REFUTES the deleted
field (`VacuitySweepTeeth.deployedCap8Scheme_chip_not_Compress8CR`, which is where `compress8CR_false_babyBear`
is available). That is the tightest possible statement of what changed: **the very function the teeth
refute now INHABITS the structure.**

⚑ Honest scope: this is not a KAT-faithful Poseidon2 model (none exists in Lean here), so it is not a
byte-differential against the Rust chip. It is a deployed-SHAPED inhabitant, and shape is precisely what
the vacuity argument was about. -/

/-- The deployed BabyBear prime `p = 2^31 - 2^27 + 1` — the modulus every lane of
`descriptor_ir2::chip_absorb_all_lanes` reduces into. (`VacuitySweepTeeth.babyBearP` is the same
literal; it is restated here because that module imports THIS one.) -/
def BABYBEAR_P : ℤ := 2013265921

/-- **A DEPLOYED-SHAPED 8-output chip absorb.** An arbitrary-length input list, eight output lanes,
every lane reduced into `[0, p)`. This is the shape of `chip_absorb_all_lanes`, and it is the shape
`compress8CR_false_babyBear` refutes injectivity for. -/
def deployedShapedChip8 (xs : List ℤ) : Digest8 :=
  fun i => (xs.foldl (fun acc x => (acc * 31 + x) % BABYBEAR_P) ((i : ℤ) + 1)) % BABYBEAR_P

/-- Every lane of the deployed-shaped chip lands in `[0, p)` — the hypothesis
`VacuitySweepTeeth.compress8CR_false_babyBear` consumes. -/
theorem deployedShapedChip8_bounded (xs : List ℤ) (i : Fin 8) :
    0 ≤ deployedShapedChip8 xs i ∧ deployedShapedChip8 xs i < BABYBEAR_P :=
  ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩

/-- ⚑ **THE CONSTRUCTED INHABITANT — a real deployed `Cap8Scheme` VALUE.** This term is what the old
structure could not have. Every theorem in §5b now has an instance to be applied at. -/
def deployedCap8Scheme : Cap8Scheme := ⟨deployedShapedChip8⟩

/-- The inhabitant's chip IS the deployed-shaped chip (definitional — the projection fires). -/
theorem deployedCap8Scheme_chip : deployedCap8Scheme.chipAbsorb8 = deployedShapedChip8 := rfl

/-- ⚑ **THE TOOTH FIRES AT THE INHABITANT.** The cap-open anti-ghost, INSTANTIATED at a real value —
the operation the `∀ S8 : Cap8Scheme` form could never actually be performed for. -/
theorem deployed_capOpen8_binds_leaf_or_collides
    (path : List (CapMerkleGeneric.StepG Digest8)) {nl₁ nl₂ : CapLeaf}
    (h : Cap8Scheme.recomposeUp8 deployedCap8Scheme
           (Cap8Scheme.capLeafDigest8 deployedCap8Scheme nl₁) path
       = Cap8Scheme.recomposeUp8 deployedCap8Scheme
           (Cap8Scheme.capLeafDigest8 deployedCap8Scheme nl₂) path) :
    nl₁ = nl₂ ∨ Cap8Scheme.CapOpenColl deployedCap8Scheme nl₁ nl₂ path :=
  Cap8Scheme.capOpen8_binds_leaf_or_collides deployedCap8Scheme path h

/-! ### §7b — ⚑ THE ACCEPTANCE TEST FOR THE 1-FELT BUNDLE: a REAL DEPLOYED `CapHashScheme` VALUE.

What deleting the `chipCR` field bought is measured HERE, not by a green build. With the field present
`CapHashScheme` had NO inhabitant AT ALL — not merely no deployed one: nothing in this tree ever
constructed a `CapHashScheme` value, because `Compress1CR` is refuted for every chip absorb landing in
a bounded BabyBear felt (`FactoryBindingFloorRegrounded.compress1CR_false_babyBear`), which the real
`cap_chip_absorb` does. So every `∀ S : CapHashScheme State, …` theorem in §3–§6 was VACUOUSLY true.

`deployedCapHashScheme` is a VALUE. Its chip is DEPLOYED-SHAPED in the only respect the vacuity
argument ever turned on: it takes an arbitrary-length `List ℤ` to ONE felt reduced into `[0, p)`.
Decisively, its own chip REFUTES the deleted field — the refutation tooth is
`CapHashBundleCutoverCheck.deployedCapHashScheme_chip_not_Compress1CR` (stated downstream, where the
refutation lives), so **the very function the teeth refute now INHABITS the structure.**

⚑ Honest scope, same as `deployedCap8Scheme`: not a KAT-faithful Poseidon2 (none exists in Lean here),
so this is not a byte differential against the Rust `cap_chip_absorb`. It is a deployed-SHAPED
inhabitant, and shape is exactly what the vacuity argument was about.

⚑ DEBT REPORTED, NOT PROVEN AROUND: `CapHashScheme.chipAbsorb : List ℤ → ℤ` is a ONE-FELT (~31-bit,
2^15.5-collidable) cap-tree digest. That narrowing is the felt-width wound
(`docs/WOUND-felt-width-boundaries-2026-07-19.md`), pre-existing in this module and NOT introduced
here; the 8-felt repair is `Cap8Scheme`, §5b, already in the tree. This section models the width the
1-felt tree deploys so the refutation bites the deployed object. -/

/-- **A DEPLOYED-SHAPED 1-output chip absorb.** Arbitrary-length input list, ONE output felt reduced
into `[0, p)` for the deployed BabyBear prime. This is the shape of `cap_root.rs::cap_chip_absorb`,
and it is the shape `compress1CR_false_babyBear` refutes injectivity for. -/
def deployedShapedChip1 (xs : List ℤ) : ℤ :=
  (xs.foldl (fun acc x => (acc * 31 + x) % BABYBEAR_P) 7) % BABYBEAR_P

/-- The deployed-shaped 1-felt chip lands in `[0, p)` — the hypothesis the refutation consumes. -/
theorem deployedShapedChip1_bounded (xs : List ℤ) :
    0 ≤ deployedShapedChip1 xs ∧ deployedShapedChip1 xs < BABYBEAR_P :=
  ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩

/-- ⚑ **THE CONSTRUCTED INHABITANT — a real deployed `CapHashScheme` VALUE.** This term is what the old
structure could not have. Every theorem in §3–§6 now has a deployed instance to be applied at. -/
def deployedCapHashScheme : CapHashScheme Unit := ⟨deployedShapedChip1⟩

/-- The inhabitant's chip IS the deployed-shaped chip (definitional — the projection fires). -/
theorem deployedCapHashScheme_chip : deployedCapHashScheme.chipAbsorb = deployedShapedChip1 := rfl

/-- ⚑ **THE TOOTH FIRES AT THE INHABITANT.** The 1-felt spine anti-ghost, INSTANTIATED at a real
deployed value — the operation the `∀ S : CapHashScheme State` form could never actually be performed
for. -/
theorem deployed_recomposeUp_binds_or_collides
    (path : List (CapHashScheme.Step)) {a b : ℤ}
    (h : CapHashScheme.recomposeUp deployedCapHashScheme a path
       = CapHashScheme.recomposeUp deployedCapHashScheme b path) :
    a = b ∨ Compress1Coll deployedCapHashScheme.chipAbsorb
      (CapHashScheme.recomposeUpFind deployedCapHashScheme a b path) :=
  CapHashScheme.recomposeUp_binds_or_collides deployedCapHashScheme path h

/-! #### §7b-guards — the inhabitant RUNS (computable witnesses, no `native_decide`). -/

-- The deployed inhabitant's leaf digest is a genuine BabyBear-range felt.
#guard 0 ≤ deployedShapedChip1 [1, 2, 3] && deployedShapedChip1 [1, 2, 3] < 2013265921

-- NON-VACUITY at the inhabitant: distinct absorbed blocks MOVE the deployed digest.
#guard deployedShapedChip1 [1, 2, 3] != deployedShapedChip1 [3, 2, 1]

-- ... and the node fold COMPUTES on the constructed value.
#guard CapHashScheme.nodeOf deployedCapHashScheme 5 7
         != CapHashScheme.nodeOf deployedCapHashScheme 7 5

/-! #### §5b.D-guards — the inhabitant RUNS (computable witnesses, no `native_decide`). -/

/-- A concrete 7-field cap leaf. -/
def demoLeaf8A : CapLeaf :=
  { slot_hash := 11, target := 22, auth_tag := 1, mask_lo := 3, mask_hi := 0,
    expiry := 0, breadstuff := 0 }

/-- The SAME leaf with a different rights felt (`mask_lo`) — the authority-residue mutation. -/
def demoLeaf8B : CapLeaf := { demoLeaf8A with mask_lo := 7 }

/-- A concrete two-level sibling/direction path. -/
def demoPath8 : List (CapMerkleGeneric.StepG Digest8) :=
  [⟨fun _ => 101, false⟩, ⟨fun _ => 202, true⟩]

-- The deployed inhabitant's leaf digest is a genuine 8-lane vector.
#guard (List.ofFn (Cap8Scheme.capLeafDigest8 deployedCap8Scheme demoLeaf8A)).length == 8

-- Every lane lands inside the BabyBear range.
#guard (List.ofFn (Cap8Scheme.capLeafDigest8 deployedCap8Scheme demoLeaf8A)).all
    (fun x => 0 ≤ x && x < BABYBEAR_P)

-- NON-VACUITY, at the inhabitant: flipping the rights felt MOVES the 8-felt leaf digest.
#guard (List.ofFn (Cap8Scheme.capLeafDigest8 deployedCap8Scheme demoLeaf8A))
    != (List.ofFn (Cap8Scheme.capLeafDigest8 deployedCap8Scheme demoLeaf8B))

-- ... and MOVES the recomposed 8-felt cap ROOT along a real path: the whole `node8` membership
-- machinery COMPUTES on the constructed value.
#guard (List.ofFn (Cap8Scheme.recomposeUp8 deployedCap8Scheme
        (Cap8Scheme.capLeafDigest8 deployedCap8Scheme demoLeaf8A) demoPath8))
    != (List.ofFn (Cap8Scheme.recomposeUp8 deployedCap8Scheme
        (Cap8Scheme.capLeafDigest8 deployedCap8Scheme demoLeaf8B) demoPath8))

/-! ### §5b.R — the REFUTABILITY reference chip (what `Reference8` is now FOR).

`Reference8` used to be offered as the "non-vacuity" argument for the `chip8CR` field — an injective toy
chip satisfying it. That was the FALSE COMFORT: a toy witness satisfies the field, the real compressing
Poseidon2 refutes it, and the structure had no deployed value. `Compress8CR` is no longer a field, so
`refChip8CR`'s job now is to make the §5b.S refutability canaries CONCRETE: at this chip the collision
disjunct really is unavailable. -/

namespace Reference8

/-- A toy CR 8-output absorb: every lane carries the injective `Encodable` encoding of the input list.
Injective because `f a = f b` evaluated at lane `0` gives `encode a = encode b`. NOT deployed-shaped —
its lanes are unbounded, which is exactly why it can be injective and the real chip cannot. -/
def refChipAbsorb8 (xs : List ℤ) : Digest8 := fun _ => (Encodable.encode xs : ℕ)

theorem refChip8CR : Compress8CR refChipAbsorb8 := by
  intro a b h
  have h0 := congrFun h 0
  unfold refChipAbsorb8 at h0
  exact Encodable.encode_injective (by exact_mod_cast h0)

/-- The reference 8-felt scheme (no CR field to supply any more). -/
def refScheme8 : Cap8Scheme := ⟨refChipAbsorb8⟩

/-- **THE CANARY, CONCRETE: at this chip NO extracted pair is a collision.** So
`capOpen8_binds_leaf_or_collides` cannot discharge itself on the right — the binding half does the work,
and the disjunction carries strictly more than `True`. -/
theorem refScheme8_capOpenColl_refutable (nl₁ nl₂ : CapLeaf)
    (path : List (CapMerkleGeneric.StepG Digest8)) :
    ¬ Cap8Scheme.CapOpenColl refScheme8 nl₁ nl₂ path :=
  Cap8Scheme.capOpenColl_refutable_of_injective refScheme8 refChip8CR nl₁ nl₂ path

/-- **AND THE OLD CONCLUSION IS RECOVERED THERE.** At the injective reference chip the deleted
`capLeafDigest8_injective ∘ recomposeUp8_inj_of_path` peel falls straight out of the new disjunction. -/
theorem refScheme8_capOpen_binds (path : List (CapMerkleGeneric.StepG Digest8)) {nl₁ nl₂ : CapLeaf}
    (h : Cap8Scheme.recomposeUp8 refScheme8 (Cap8Scheme.capLeafDigest8 refScheme8 nl₁) path
       = Cap8Scheme.recomposeUp8 refScheme8 (Cap8Scheme.capLeafDigest8 refScheme8 nl₂) path) :
    nl₁ = nl₂ :=
  Cap8Scheme.capOpen8_binds_leaf_of_injective refScheme8 refChip8CR path h

/-- A COLLIDING 8-output absorb (constant zero vector) FALSIFIES `Compress8CR` — the predicate is not
`True`: a real collision (`[0] ≠ [1]`, same image) is exhibited. -/
def badChipAbsorb8 (_ : List ℤ) : Digest8 := fun _ => 0

theorem badChip8_not_CR : ¬ Compress8CR badChipAbsorb8 := by
  intro hCR
  have : ([0] : List ℤ) = [1] := hCR [0] [1] rfl
  simp at this

/-- The colliding chip is a `Cap8Scheme` too — and at it the `Coll8` disjunct is genuinely INHABITED,
so the two branches of every `…_or_collides` theorem are both reachable across schemes. -/
def badScheme8 : Cap8Scheme := ⟨badChipAbsorb8⟩

theorem badScheme8_has_coll8 : Coll8 badScheme8.chipAbsorb8 ([0], [1]) :=
  ⟨by simp, rfl⟩

end Reference8

/-! ## §7 — NON-VACUITY: the deployed-tree bridge FIRES on a concrete edge, and the gate is REAL.

Mirrors `CapRootBridge.bridge_fires`/`empty_caps_unauthorized`, re-seated on the deployed tree. We
exhibit a concrete `caps` (actor 5 holds a read+write cap over src 9), a faithful leaf assignment for
that edge, and the bridge firing; plus a witness-FALSE where the empty cap-table backs no opening. -/

open CapHashScheme

/-- A trivial vk-decode (no `Custom` leaf in the demo; transfers never use `Custom`). -/
def demoVkOfTag : ℤ → Nat := fun _ => 0

/-- A single-edge FACET cap-table: actor 5 holds a TRANSFER-facet, `Signature`-tier cap over src 9;
everyone else holds nothing. -/
def oneEdgeCaps : FacetCaps := fun a =>
  if a = 5 then [{ target := 9, tier := .signature, facet := some EFFECT_TRANSFER }] else []

/-- The faithful leaf assignment for `oneEdgeCaps`: the `(5 ⇒ 9)` edge carries a TRANSFER-facet,
`Signature`-tier (`auth_tag = 1`) leaf; every other edge carries a deny-all (`mask = 0` ⇒ facet rejects)
leaf, so `confersTransferLeaf` is false there and faithfulness is vacuously met. -/
def oneEdgeLeaf : Label → Label → CapLeaf := fun actor src =>
  if actor = 5 ∧ src = 9 then
    { slot_hash := 0, target := 9, auth_tag := 1,   -- tier = Signature
      mask_lo := EFFECT_TRANSFER, mask_hi := 0, expiry := 0, breadstuff := 0 }
  else
    { slot_hash := 0, target := 0, auth_tag := 1,
      mask_lo := 0, mask_hi := 0, expiry := 0, breadstuff := 0 }   -- mask 0 ⇒ deny-all

/-- **`oneEdge_faithful`** — `oneEdgeLeaf` faithfully realizes `oneEdgeCaps` (under a provided signature)
against any root: the ONLY transfer-conferring edge is `(5 ⇒ 9)`, where actor 5 holds the matching
`FacetCap`. The deny-all leaf elsewhere makes `confersTransferLeaf` false (facet rejects), so the
faithfulness obligation is vacuous off the edge. -/
theorem oneEdge_faithful {State : Type} (S : CapHashScheme State) (root : ℤ) :
    DeployedFaithful S demoVkOfTag .signature oneEdgeCaps root oneEdgeLeaf := by
  refine ⟨?_⟩
  intro actor src _hopen hconf
  by_cases hedge : actor = 5 ∧ src = 9
  · obtain ⟨ha, hs⟩ := hedge
    subst ha; subst hs
    refine ⟨{ target := 9, tier := .signature, facet := some EFFECT_TRANSFER }, by simp [oneEdgeCaps], rfl, ?_, rfl⟩
    decide
  · exfalso
    obtain ⟨hfacet, _⟩ := hconf
    simp only [oneEdgeLeaf, if_neg hedge, facetOfLeaf, maskOfLimbs] at hfacet
    -- the off-edge leaf has mask 0 ⇒ `isEffectPermitted (some 0) _ = false`.
    revert hfacet; decide

/-- **`deployedEncodes_inhabited`** — the deployed commitment relation is INHABITED. -/
theorem deployedEncodes_inhabited {State : Type} (S : CapHashScheme State) (root : ℤ) :
    DeployedEncodes S demoVkOfTag .signature oneEdgeCaps root :=
  ⟨oneEdgeLeaf, oneEdge_faithful S root⟩

/-- **NON-VACUITY (the bridge FIRES on a real edge).** Given a membership opening of the `(5 ⇒ 9)`
transfer leaf against the deployed tree (with a provided signature), the bridge yields
`authorizedFacetB oneEdgeCaps .signature ⟨5,9,…⟩ = true`. -/
theorem bridge_fires {State : Type} (S : CapHashScheme State) (root : ℤ)
    (hopen : MembersAt S root (oneEdgeLeaf 5 9)) :
    authorizedFacetB oneEdgeCaps .signature { actor := 5, src := 9, dst := 0, amt := 0 } = true := by
  apply deployedCapOpen_implies_authorizedB S demoVkOfTag .signature oneEdgeCaps root oneEdgeLeaf
      (oneEdge_faithful S root) 5 9 0 0 hopen
  have hleaf : oneEdgeLeaf 5 9
      = { slot_hash := 0, target := 9, auth_tag := 1,
          mask_lo := EFFECT_TRANSFER, mask_hi := 0, expiry := 0, breadstuff := 0 } := by
    unfold oneEdgeLeaf; simp
  rw [hleaf]
  refine ⟨?_, ?_⟩ <;> decide

/-- **NON-VACUITY (witness FALSE — the gate is real).** Over the EMPTY FACET cap-table, the faithful gate
rejects a non-owned src — so the bridge's conclusion is NOT vacuously always-true. -/
theorem empty_caps_unauthorized :
    authorizedFacetB (fun _ => []) .signature { actor := 5, src := 9, dst := 0, amt := 0 } = false := by
  decide

/-! ## §7R — ⚑ THE ROM SUCCESSORS: the cap-tree binding surface as REDUCTIONS on the PROVED
keyed floor.

⚑ STATUS OF THE `…_binds_or_collides` FAMILY (2026-07-24). The §5b.X disjunctions are EXTRACTOR
MACHINERY — each hands back the specific pair a break would collide at, which is exactly what a
reduction consumes — but as EXPORTED security statements they are shirks: at deployed BabyBear
parameters a collision EXISTS by pigeonhole (`VacuitySweepTeeth.compress8CR_false_babyBear`), so
each disjunction is satisfiable through its right branch with NO binding. The security statements
are THIS section's `…_binds_rom` reductions: the forger is an ORACLE PROGRAM fixed before the
tag-separated oracle is sampled, and every export closes from `KeyedRomFloor.keyedRom_hard` (the
birthday bound — a THEOREM), with no refuted floor, no cost model, and the extractor's queries PAID.
The disjunctions are RETAINED below them as the reduction-internal witnesses and for their
downstream `rcases` consumers (`VacuitySweepTeeth`, `Emit.EffectVmEmitRotationV3`,
`RotatedKernelRefinementCapFamily`, `Emit.MerkleMembership4aryWideEmit`,
`Emit.EffectVmCapFamilyComplete`, `InjectiveFloorRegrounded`), whose re-point is the remaining
mechanical work — deleting them before that re-point would break files owned by other lanes.

⚑ THE MODELLING STEP, STATED (the `Crypto.RomCarrierSites` header discipline, not smuggled): the
fixed public 8-output chip is idealised as a keyed random oracle into `Fin (2 ^ l)`; an 8-felt child
digest is ONE sampled ideal value, and the ordered node PAIR `(x, y)` carries exactly the layout
content `pack8` carries (order preserved, both children bound — compare `InjectiveFloorRegrounded`'s
`node8RomCarrier`, which states the SAME node binding at the 16-felt packed-block truncation). There
is NO `l` at which `Fin (2 ^ l)` is the deployed 8×~31-bit digest; at the deployed width the honest
reading stays "binds exactly as well as ~124 bits allow". Collision resistance of the fixed public
chip itself remains a conjecture, not a Lean theorem. -/

section RomSuccessor

open Dregg2.Crypto.RomHashedLeafOpening
open Dregg2.Crypto.RomBindingReduction (RomCarrier romCarrierGame RomCarrierEff)
open Dregg2.Crypto.RomCarrierSites (RomForgeryEff)
open Dregg2.Crypto.FloorGames (Adversary gameAdv)
open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)

/-- The truncated 7-field cap-leaf block — the `leafFields` image at the deployed BabyBear range
(`cap_root.rs::CapLeaf`'s seven felts, in order). -/
abbrev CapLeafRomBlock : Type := Fin 7 → Fin Dregg2.Crypto.RomCarrierSites.babyBearP

/-- **THE CAP-TREE ROM FAMILY** at domain-separation tag space `Key`: messages are truncated
7-field leaf blocks ⊕ ordered ideal-digest node pairs, the ROM image of the deployed chip's
7-vs-16 arity separation. -/
abbrev capRomFamily (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key) (kN : Nonempty Key) :
    Dregg2.Crypto.KeyedRomFloor.KeyedRomFamily :=
  hlFam Key kF kD kN (fun _ => CapLeafRomBlock) (fun _ => inferInstance) (fun _ => inferInstance)

/-- The cap-leaf carrier — `H (t, inl block)` binds all seven leaf fields. -/
abbrev capLeafRomCarrier (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) : RomCarrier (capRomFamily Key kF kD kN) :=
  hlLeafCarrier Key kF kD kN (fun _ => CapLeafRomBlock) (fun _ => inferInstance)
    (fun _ => inferInstance)

/-- The cap-node carrier — `H (t, inr (l, r))` binds BOTH ordered 8-felt children (the `pack8`
layout content at the ideal width). -/
abbrev capNodeRomCarrier (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) : RomCarrier (capRomFamily Key kF kD kN) :=
  hlNodeCarrier Key kF kD kN (fun _ => CapLeafRomBlock) (fun _ => inferInstance)
    (fun _ => inferInstance)

/-- **⚑⚑ THE CAP-LEAF BINDING, AS A REDUCTION ON THE PROVED FLOOR** — the ROM successor of
`capLeafDigest8_binds_or_collides`'s left disjunct: every query-bounded forger that equivocates one
leaf digest between two DISTINCT 7-field blocks has NEGLIGIBLE advantage. NO bare disjunction, NO
refuted floor — `flatSite_binds`, hence `keyedRom_hard` (the birthday bound). -/
theorem capLeafDigest8_binds_rom (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (romCarrierGame (capRomFamily Key kF kD kN)
      (capLeafRomCarrier Key kF kD kN)))
    (hA : RomCarrierEff (capRomFamily Key kF kD kN) (capLeafRomCarrier Key kF kD kN) Q A) :
    Negl (gameAdv (romCarrierGame (capRomFamily Key kF kD kN)
      (capLeafRomCarrier Key kF kD kN)) A) :=
  hlLeaf_binds_rom Key kF kD kN _ _ _ Q hQ A hA

/-- **⚑⚑ THE CAP-NODE BINDING, AS A REDUCTION ON THE PROVED FLOOR** — the ROM successor of
`nodeOf8_binds_or_collides`'s left disjunct (the "SOLE width-specific obligation" the native-8-felt
tree rides): every query-bounded forger that equivocates one `node8` digest between two DISTINCT
ordered child pairs has NEGLIGIBLE advantage. -/
theorem capNodeOf8_binds_rom (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (romCarrierGame (capRomFamily Key kF kD kN)
      (capNodeRomCarrier Key kF kD kN)))
    (hA : RomCarrierEff (capRomFamily Key kF kD kN) (capNodeRomCarrier Key kF kD kN) Q A) :
    Negl (gameAdv (romCarrierGame (capRomFamily Key kF kD kN)
      (capNodeRomCarrier Key kF kD kN)) A) :=
  hlNode_binds_rom Key kF kD kN _ _ _ Q hQ A hA

/-- **⚑⚑ THE SPINE BINDING, AS A REDUCTION** — the ROM successor of
`recomposeUp8_binds_or_collides`: a query-bounded forger that folds two DISTINCT starting digests
up one SHARED `(sibling, direction)` schedule (`CapMerkleGeneric.StepG`'s `(sib, dir)`, as the
kit's `(bit, sibling)` blocks) to one root has NEGLIGIBLE advantage; the extractor re-walks the
schedule, `2·depth` queries PAID (`hlPathRom_binds`). -/
theorem capRecomposeUp8_binds_rom (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (dep Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + 2 * dep l ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (hlPathForgery Key kF kD kN (fun _ => CapLeafRomBlock)
      (fun _ => inferInstance) (fun _ => inferInstance) dep).game)
    (hA : RomForgeryEff (capRomFamily Key kF kD kN)
      (hlPathForgery Key kF kD kN (fun _ => CapLeafRomBlock)
        (fun _ => inferInstance) (fun _ => inferInstance) dep) Q A) :
    Negl (gameAdv (hlPathForgery Key kF kD kN (fun _ => CapLeafRomBlock)
      (fun _ => inferInstance) (fun _ => inferInstance) dep).game A) :=
  hlPathRom_binds Key kF kD kN _ _ _ dep Q Q' hle hQ' A hA

/-- **⚑⚑ THE CAP-OPEN ANTI-GHOST, AS A REDUCTION** — the ROM successor of
`capOpen8_binds_leaf_or_collides` (and, since the ROM statement is about the SAMPLED oracle rather
than a scheme value, of its `deployed_capOpen8_binds_leaf_or_collides` instantiation too): a
query-bounded forger that opens one root to two DISTINCT 7-field leaves along one shared path has
NEGLIGIBLE advantage. The extractor queries both leaf points and walks the shared schedule —
`Q + 2·depth + 2` queries, PAID. -/
theorem capOpen8_binds_leaf_rom (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (dep Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + (2 * dep l + 2) ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (hlOpenForgery Key kF kD kN (fun _ => CapLeafRomBlock)
      (fun _ => inferInstance) (fun _ => inferInstance) dep).game)
    (hA : RomForgeryEff (capRomFamily Key kF kD kN)
      (hlOpenForgery Key kF kD kN (fun _ => CapLeafRomBlock)
        (fun _ => inferInstance) (fun _ => inferInstance) dep) Q A) :
    Negl (gameAdv (hlOpenForgery Key kF kD kN (fun _ => CapLeafRomBlock)
      (fun _ => inferInstance) (fun _ => inferInstance) dep).game A) :=
  hlOpenRom_binds Key kF kD kN _ _ _ dep Q Q' hle hQ' A hA

/-- **⚑ THE PUBLISHED-ROOT FORM** — the `MembersAt8`-functional shape: two query-bounded openings
of ONE published root to two DISTINCT leaves succeed with negligible probability. -/
theorem capOpenRoot8_binds_rom (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (dep Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + (2 * dep l + 2) ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (hlOpenRootForgery Key kF kD kN (fun _ => CapLeafRomBlock)
      (fun _ => inferInstance) (fun _ => inferInstance) dep).game)
    (hA : RomForgeryEff (capRomFamily Key kF kD kN)
      (hlOpenRootForgery Key kF kD kN (fun _ => CapLeafRomBlock)
        (fun _ => inferInstance) (fun _ => inferInstance) dep) Q A) :
    Negl (gameAdv (hlOpenRootForgery Key kF kD kN (fun _ => CapLeafRomBlock)
      (fun _ => inferInstance) (fun _ => inferInstance) dep).game A) :=
  hlOpenRootRom_binds Key kF kD kN _ _ _ dep Q Q' hle hQ' A hA

/-! ### The truncation pin — the deployed range-bounded leaf embeds LOSSLESSLY, so a distinct pair
of deployed leaves stays a distinct pair of ROM payloads (the `bvecOfList_inj` discipline). -/

/-- Truncate a range-bounded deployed felt into the ROM alphabet. Injective on `[0, p)` —
`feltTrunc_inj`; the `%` keeps it TOTAL off-range, where the injectivity claim is not made. -/
def feltTrunc (x : ℤ) : Fin Dregg2.Crypto.RomCarrierSites.babyBearP :=
  ⟨x.toNat % Dregg2.Crypto.RomCarrierSites.babyBearP,
    Nat.mod_lt _ (by norm_num [Dregg2.Crypto.RomCarrierSites.babyBearP])⟩

theorem feltTrunc_inj {x y : ℤ} (hx0 : 0 ≤ x) (hx1 : x < BABYBEAR_P) (hy0 : 0 ≤ y)
    (hy1 : y < BABYBEAR_P) (h : feltTrunc x = feltTrunc y) : x = y := by
  have hv : x.toNat % Dregg2.Crypto.RomCarrierSites.babyBearP
      = y.toNat % Dregg2.Crypto.RomCarrierSites.babyBearP := congrArg Fin.val h
  have hbb : Dregg2.Crypto.RomCarrierSites.babyBearP = 2013265921 := rfl
  have hBB : BABYBEAR_P = (2013265921 : ℤ) := rfl
  rw [hbb] at hv
  rw [hBB] at hx1 hy1
  omega

/-- The deployed 7-field cap leaf, truncated into the ROM leaf block (field order preserved). -/
def capLeafRomBlockOf (leaf : CapLeaf) : CapLeafRomBlock :=
  ![feltTrunc leaf.slot_hash, feltTrunc leaf.target, feltTrunc leaf.auth_tag,
    feltTrunc leaf.mask_lo, feltTrunc leaf.mask_hi, feltTrunc leaf.expiry,
    feltTrunc leaf.breadstuff]

/-- **THE TRUNCATION LOSES NOTHING** — two range-bounded deployed leaves with one ROM block are
EQUAL, so the ROM forgery games quantify over everything the deployed prover can absorb. -/
theorem capLeafRomBlockOf_inj {l₁ l₂ : CapLeaf}
    (h₁ : ∀ x ∈ leafFields l₁, 0 ≤ x ∧ x < BABYBEAR_P)
    (h₂ : ∀ x ∈ leafFields l₂, 0 ≤ x ∧ x < BABYBEAR_P)
    (h : capLeafRomBlockOf l₁ = capLeafRomBlockOf l₂) : l₁ = l₂ := by
  have hmem : ∀ l : CapLeaf, ∀ x ∈ [l.slot_hash, l.target, l.auth_tag, l.mask_lo, l.mask_hi,
      l.expiry, l.breadstuff], x ∈ leafFields l := by
    intro l x hx
    simpa [leafFields] using hx
  have hf : ∀ (f : CapLeaf → ℤ) (i : Fin 7),
      (∀ l, capLeafRomBlockOf l i = feltTrunc (f l)) →
      f l₁ ∈ leafFields l₁ → f l₂ ∈ leafFields l₂ → f l₁ = f l₂ := by
    intro f i hproj hm₁ hm₂
    obtain ⟨ha0, ha1⟩ := h₁ _ hm₁
    obtain ⟨hb0, hb1⟩ := h₂ _ hm₂
    refine feltTrunc_inj ha0 ha1 hb0 hb1 ?_
    rw [← hproj l₁, ← hproj l₂, h]
  apply leafFields_inj
  have h0 := hf (fun l => l.slot_hash) 0 (fun _ => rfl)
    (hmem l₁ _ (by simp)) (hmem l₂ _ (by simp))
  have h1 := hf (fun l => l.target) 1 (fun _ => rfl)
    (hmem l₁ _ (by simp)) (hmem l₂ _ (by simp))
  have h2 := hf (fun l => l.auth_tag) 2 (fun _ => rfl)
    (hmem l₁ _ (by simp)) (hmem l₂ _ (by simp))
  have h3 := hf (fun l => l.mask_lo) 3 (fun _ => rfl)
    (hmem l₁ _ (by simp)) (hmem l₂ _ (by simp))
  have h4 := hf (fun l => l.mask_hi) 4 (fun _ => rfl)
    (hmem l₁ _ (by simp)) (hmem l₂ _ (by simp))
  have h5 := hf (fun l => l.expiry) 5 (fun _ => rfl)
    (hmem l₁ _ (by simp)) (hmem l₂ _ (by simp))
  have h6 := hf (fun l => l.breadstuff) 6 (fun _ => rfl)
    (hmem l₁ _ (by simp)) (hmem l₂ _ (by simp))
  simp [leafFields, h0, h1, h2, h3, h4, h5, h6]

/-! ### Deployed-shape instantiation + teeth: the ∀-key surface is INHABITED at the deployed
single-tag shape, the game is winnable, and the admitted refuter-shape is DEFANGED. -/

/-- The deployed cap tree runs ONE domain-separated absorb family (no adversary-chosen tag), so the
deployed-shape instantiation pins `Key := Unit`. The tooth: the whole ∀-key export elaborates at a
concrete value. -/
theorem deployedShape_capOpen8_binds_leaf_rom (dep Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + (2 * dep l + 2) ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (hlOpenForgery Unit inferInstance inferInstance inferInstance
      (fun _ => CapLeafRomBlock) (fun _ => inferInstance) (fun _ => inferInstance) dep).game)
    (hA : RomForgeryEff (capRomFamily Unit inferInstance inferInstance inferInstance)
      (hlOpenForgery Unit inferInstance inferInstance inferInstance (fun _ => CapLeafRomBlock)
        (fun _ => inferInstance) (fun _ => inferInstance) dep) Q A) :
    Negl (gameAdv (hlOpenForgery Unit inferInstance inferInstance inferInstance
      (fun _ => CapLeafRomBlock) (fun _ => inferInstance) (fun _ => inferInstance) dep).game A) :=
  capOpen8_binds_leaf_rom Unit inferInstance inferInstance inferInstance dep Q Q' hle hQ' A hA

/-- **(TOOTH — the admitted refuter-shape is DEFANGED at the cap open, not excluded.)** The
`0`-query constant answerer — the exact shape that wins probability `1` against the FIXED chip and
refutes the `IsPolyTime` floors — is IN the class, WINS at the constant oracle on distinct leaves
(positive advantage), and is NEGLIGIBLE against the sampled oracle. -/
theorem capOpenRom_constAnswer_defanged (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (dep Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + (2 * dep l + 2) ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (c : ∀ l, Key × (Fin (dep l) → Bool × Fin (2 ^ l))) (v w : ∀ l, CapLeafRomBlock)
    (hvw : ∀ l, v l ≠ w l) :
    RomForgeryEff (capRomFamily Key kF kD kN)
        (hlOpenForgery Key kF kD kN (fun _ => CapLeafRomBlock)
          (fun _ => inferInstance) (fun _ => inferInstance) dep) Q
        (hlConstOpenAdv Key kF kD kN (fun _ => CapLeafRomBlock)
          (fun _ => inferInstance) (fun _ => inferInstance) dep c v w)
      ∧ Negl (gameAdv (hlOpenForgery Key kF kD kN (fun _ => CapLeafRomBlock)
          (fun _ => inferInstance) (fun _ => inferInstance) dep).game
        (hlConstOpenAdv Key kF kD kN (fun _ => CapLeafRomBlock)
          (fun _ => inferInstance) (fun _ => inferInstance) dep c v w))
      ∧ ∀ l, 0 < gameAdv (hlOpenForgery Key kF kD kN (fun _ => CapLeafRomBlock)
          (fun _ => inferInstance) (fun _ => inferInstance) dep).game
        (hlConstOpenAdv Key kF kD kN (fun _ => CapLeafRomBlock)
          (fun _ => inferInstance) (fun _ => inferInstance) dep c v w) l :=
  ⟨hlConstOpenAdv_in_eff Key kF kD kN _ _ _ dep c v w Q,
   hlConstOpenAdv_negl Key kF kD kN _ _ _ dep Q Q' hle hQ' c v w,
   fun l => hlConstOpenAdv_gameAdv_pos Key kF kD kN _ _ _ dep c v w l (hvw l)⟩

end RomSuccessor

/-! ## §8 — Axiom hygiene. -/

#assert_axioms CapHashScheme.capLeafDigest_injective
#assert_axioms CapHashScheme.nodeOf_injective
#assert_axioms CapHashScheme.recomposeUp_eq_recomposeG
#assert_axioms CapHashScheme.recomposeUp_inj_of_path
-- 1-felt bundle cutover (`chipCR` DELETED): the unconditional forms + the strength bridges.
#assert_axioms CapHashScheme.capLeafDigest_binds_or_collides
#assert_axioms CapHashScheme.nodeOf_binds_or_collides
#assert_axioms CapHashScheme.recomposeUp_binds_or_collides
#assert_axioms deployedShapedChip1_bounded
#assert_axioms deployed_recomposeUp_binds_or_collides
-- Native-8-felt (Phase H-CAP-8): the node8 obligation + the re-instantiated recompose spine.
#assert_axioms Cap8Scheme.pack8_inj
#assert_axioms Cap8Scheme.capLeafDigest8_binds_or_collides
#assert_axioms Cap8Scheme.nodeOf8_binds_or_collides
#assert_axioms Cap8Scheme.recomposeUp8_binds_or_collides
#assert_axioms Cap8Scheme.capOpen8_binds_leaf_or_collides
#assert_axioms Cap8Scheme.coll8_refutable_of_injective
#assert_axioms Cap8Scheme.capOpenColl_refutable_of_injective
#assert_axioms Cap8Scheme.capLeafDigest8_injective_of_injective
#assert_axioms Cap8Scheme.nodeOf8_injective_of_injective
#assert_axioms Cap8Scheme.recomposeUp8_inj_of_path_of_injective
#assert_axioms Cap8Scheme.capOpen8_binds_leaf_of_injective
#assert_axioms deployedShapedChip8_bounded
#assert_axioms deployedCap8Scheme_chip
#assert_axioms deployed_capOpen8_binds_leaf_or_collides
#assert_axioms Reference8.refScheme8_capOpenColl_refutable
#assert_axioms Reference8.refScheme8_capOpen_binds
#assert_axioms Reference8.badScheme8_has_coll8
#assert_axioms Cap8Scheme.deployedCapOpen8_implies_authorizedB
#assert_axioms Cap8Scheme.deployedCapOpen8_implies_authorizedEffB
#assert_axioms Cap8Scheme.deployedFaithfulEff_canonical8
#assert_axioms Reference8.refChip8CR
#assert_axioms Reference8.badChip8_not_CR
#assert_axioms CapHashScheme.deployedCapOpen_implies_authorizedB
#assert_axioms CapHashScheme.deployedCapOpen_implies_authorizedEffB
#assert_axioms CapHashScheme.tierOfTag_tierByte
#assert_axioms CapHashScheme.tierOfTag_tierTag
#assert_axioms CapHashScheme.facetOfLeaf_canonical_permits
#assert_axioms CapHashScheme.tierOfTag_canonical
#assert_axioms CapHashScheme.deployedFaithfulEff_canonical
#assert_axioms oneEdge_faithful
#assert_axioms deployedEncodes_inhabited
#assert_axioms bridge_fires
#assert_axioms empty_caps_unauthorized
-- §7R — the ROM successors (reductions on the proved keyed floor; no bare disjunction).
#assert_axioms capLeafDigest8_binds_rom
#assert_axioms capNodeOf8_binds_rom
#assert_axioms capRecomposeUp8_binds_rom
#assert_axioms capOpen8_binds_leaf_rom
#assert_axioms capOpenRoot8_binds_rom
#assert_axioms feltTrunc_inj
#assert_axioms capLeafRomBlockOf_inj
#assert_axioms deployedShape_capOpen8_binds_leaf_rom
#assert_axioms capOpenRom_constAnswer_defanged

end Dregg2.Circuit.DeployedCapTree
