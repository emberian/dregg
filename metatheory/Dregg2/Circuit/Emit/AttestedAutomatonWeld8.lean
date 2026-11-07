/-

⚠⚠⚠ THE WELD IS ON THE WIRE ONLY — THE DESCRIPTOR STILL *COMMITS* ~31 BITS. Read this before citing
anything below as a deployed width fix. (An adversarial verify made this the primary finding; this
file's own §3a framing was stronger than the truth, and `weld_completion_lanes_free` below already
proved the truth.)

WHAT IS REAL: the descriptor now CARRIES eight root columns (W8ROOT 0..7 = cols 3..10), pinned to
eight public inputs on row 0 and threaded by eight constancy windows — verified on the emitted JSON
(`"root":[var 3, var 4, …, var 10]` vs the unwelded `[var 3 ×8]`). The binding theorem
`root8_binds_automaton_or_collides` is re-proven over `mapRoot8`/`opensToMerkle8` and consumes NO
`Poseidon2SpongeCR` — the hypothesis BabyBear refutes is gone from the binding leg — with
`weld_collision_disjunct_refutable` showing the collision disjunct is REFUTABLE (not a pigeonhole
free pass).

WHAT IS NOT REAL YET, and it is the load-bearing half: `DescriptorIR2.MapOp.holdsAt` reads
`(m.root 0)` and `MapOp.rowAt` logs `(m.root 0)` — LANE 0 ONLY, whatever the group carries
(DescriptorIR2.lean:580-584). So the per-row OPENING the IR actually forces is still the ~31-bit
scalar `opensTo hash (lane 0)`, and lanes 1-7 are pinned and threaded but CONTENT-UNFORCED.
`weld_completion_lanes_free` EXHIBITS this rather than asserting it: the very same descriptor is
satisfied with the seven completion lanes set to two DIFFERENT felt vectors.

⇒ HONEST STATUS: the wire is welded, the DENOTATION is not. An attacker still only has to collide the
lane-0 felt (~2^15.5), so the automaton binding is NOT yet a deployed security property. The weld is
necessary but not sufficient.

⚠ AND THE SECOND, INDEPENDENT SCOPE LIMIT — the one removing a false floor does NOT touch: NOTHING
SHIPPED EMITS THIS DESCRIPTOR. Asked directly, because the sibling `CommittedRowsSemantics` carries a
limit of this shape and records it at the top: is `weldDesc`/`autoRoot8` a SHADOW? Answered in both
directions, because they differ.

  * `autoRoot8` is NOT a shadow. It is `MapMerkleRoot.mapRoot8` at a `Heap8Scheme`, and
    `DeployedHeapTree.deployedHeap8Scheme` is a CONSTRUCTED inhabitant of that class — the object
    `heap_root.rs::CanonicalHeapTree8::root` computes. §2 quantifies over `∀ S8 : Heap8Scheme`, so it
    is a theorem about the real deployed hash tree, not a modelled stand-in.
  * `weldDesc` is NOT a shadow declaration either — unlike `CommittedRowsSemantics.committedRows`,
    which is not a `RowSemantics` constructor at all and can only ride one, `weldDesc` is a real
    `EffectVmDescriptor2` over real `VmConstraint2` constructors, and §5 EMITS it (`emitVmJson2`).
  * ⚠ BUT IT IS UNROUTED. `WELD_NAME` ("dregg-attested-automaton::map-committed-weld8-v1") has NO
    entry in `EmitByName.routing`, NO `circuit/descriptors/by-name/*.json` artifact, and NO arm in
    `circuit/src/descriptor_by_name.rs`. Neither does the unwelded `AttestedAutomatonEmit`
    `attestedInstance`: the whole attested-automaton family is Lean-side only today. So no shipped
    prover or verifier ever builds this object, and §2's binding is a theorem about a deployed hash
    tree that NO SHIPPED DESCRIPTOR CURRENTLY OPENS.

⇒ so a floor-free theorem here is not yet a deployed one for TWO separate reasons, and they have two
separate repairs: the denotation move below (`DescriptorIR2`, shared, in flight), and a routing entry
plus a Rust dispatch arm (mechanical, not started). The denotation half is the hard one; neither is
done, and neither is claimed.

THE REMAINING FIX, named precisely: move `MapOp.holdsAt`/`MapOp.rowAt` off `(m.root 0)` onto
`opensToMerkle8`/`writesToMerkle8` so the denotation forces all eight lanes. That edit touches
`DescriptorIR2` and therefore every MapOp consumer in the tree — a genuine red-umbrella change.

⚑ 2026-11-05 — THE DENOTATION HALF NOW EXISTS, WITHOUT THE SHARED EDIT: `AttestedAutomatonLanes8`
defines `MapOp.holdsAt8` (the `.mapOp` arm opening the FULL 8-felt group against the deployed `node8`
tree), the 19-felt `MapOp.rowAt8`/`mapLog8`, and `Satisfied2Lanes8` (= `Satisfied2Public` with those
two legs swapped). Under it: `weldWit8_satisfies_constructed` (a witness, no hypothesis),
`lanes8_row_opens_public` (every accepted row opens its edge at the PUBLIC 8-felt root),
`weld8_forged_edge_refused` (THE BINDING THEOREM FOR THE FULL DIGEST: a forged step forces the named
`MapRootColl` between the row's heap and the committing heap), and the falsifier
`weld_completion_lanes_not_free` — the exact flip of `weld_completion_lanes_free` below, which still
holds under the SCALAR denotation. The pair is the exhibited separation. The shared
`DescriptorIR2.MapOp.holdsAt` is unchanged (43 consumer files); moving it remains the named follow-up,
after which `Satisfied2Lanes8` is definitionally `Satisfied2Public`. The routing half: the `EmitByName`
row and the by-name artifact `circuit/descriptors/by-name/attested-automaton-map-committed-weld8-v1.json`
(generator output, 2611 bytes) land with this file. ⚑ 2026-11-06: GRADUATED AND SERVED — §3.G below
replaces the two range teeth by lookups into the served `range_w15`/`range_w1` tables, the carriers
are empty, the artifact is 2803 bytes, and `circuit/tests/weld8_served.rs` proves and verifies it
through `descriptor_by_name` and refuses a forged edge. The paragraph that follows is the
pre-graduation record. (was:) ⚠ ROUTED IS NOT SERVED: the v2 assembly's
`check_descriptor2_wellformed` (`circuit/src/descriptor_ir2.rs:2315`) REFUSES any descriptor with a
non-empty `ranges` carrier ("requires a GRADUATED descriptor"), and `weldDesc` — like the unwelded
`attestedDesc` — declares `ranges := [⟨CURRENT, 15⟩, ⟨SYMBOL, 1⟩]`. A `descriptor_by_name.rs` arm was
written and REVERTED because its dispatch test and the pre-existing `every_static_golden_decodes_and_dispatches`
go red on that refusal (diff kept at the lane's scratch). The graduation is a Lean authoring change,
not a routing one: replace the two range teeth by range-table lookups (`rangeTableDef BAL_LIMB_BITS`
is 30-bit, so `CURRENT < 2^15` needs a limb split or a dedicated 15-bit table) and re-emit; the
`#guard` cost pins below move with it. Until then no shipped prover or verifier serves the attested
family at all, welded or not.

⚑ (historical) DO NOT DUPLICATE IT: that work was reported IN FLIGHT in this tree by another terminal —
`Dregg2/Circuit/MapKindImtGates.lean` ("STAGE 2 PROPER OF THE DENOTATION MOVE") is building
`MapOp.holdsAtS` with `writesToMerkleS`/`opensToMerkleS` arms, having already done the `.absent` arm
in `MapAbsentImtGate`. When that lands, THIS file's binding becomes a deployed property for free:
`root8_binds_automaton_or_collides` is already stated over `mapRoot8`/`opensToMerkle8`, so it needs no
change — only the IR's denotation has to start forcing what the wire already carries. The right move
here is to WAIT for that landing and then re-run `weld_completion_lanes_free`, which must FLIP from
provable to refutable. That flip is the acceptance test.
# Dregg2.Circuit.Emit.AttestedAutomatonWeld8 — the ATTESTATION ROOT, WELDED TO 8 FELTS.

**This is Lean-authored AIR.** The descriptor is an `EffectVmDescriptor2` authored here; the witness
is a concrete `VmTrace`; satisfaction, the binding and the refusal are theorems over the EMITTED
object. Rust parses the emitted IR2 bytes and supplies witnesses; it authors nothing.

## What this repairs

`AttestedAutomatonEmit` binds "which automaton ran" by a `MapOp` opening against ONE root column
(`ROOT = 3`), fed into all eight deployed lanes as `EffectVmEmitRotationV3.scalarRootGroup ROOT`.
Its own header states the wound at full resolution: the deployed instantiation has a BabyBear
codomain (`p ≈ 2^31`), so `Poseidon2SpongeCR hash` — the hypothesis `root_binds_automaton` consumes
— is FALSE there, and a ~2^15.5 birthday search finds a colliding automaton. The binding was a Lean
theorem about a modelled `hash : List ℤ → ℤ`, not a deployed security property.

This file carries the root as EIGHT columns, mirroring `beforeCapRootGroup`/`beforeHeapRootGroup`
(`fun i => .var (groupCol i)`, lane 0 the scalar limb, lanes 1..7 the completion limbs), and
re-proves the binding over the DEPLOYED 8-felt tree (`MapMerkleRoot.mapRoot8` / `opensToMerkle8` —
`node8`, arity-16 chip absorbs, the object `heap_root.rs` computes), where the committed digest is
8 BabyBear felts (~248 bits, birthday ~2^124) rather than one (~31 bits, birthday ~2^15.5).

## The three legs, and the one that does NOT weld in this IR

  * **§1–§2, the COMMITMENT and the BINDING — WELDED.** `autoRoot8 S8 d` is the deployed
    `node8` root of the automaton's `2^16`-leaf heap; `autoRoot8_commits` CONSTRUCTS it (the
    predicate is inhabited, not a wish). `root8_binds_automaton_or_collides` is UNCONDITIONAL: two
    automata behind ONE 8-felt root agree on the whole declared domain, OR the deployed arity-16
    chip genuinely collides at the pair a TOTAL extractor names (`MapRootColl`). `forged_edge_
    refused_8` is the same statement at the forgery polarity. NO `Poseidon2SpongeCR` is consumed.
  * **§3, the DESCRIPTOR — WELDED ON THE WIRE.** `weldDesc` carries the 8 lanes as the `MapOp`
    root/newRoot GROUP (the real `Fin 8 → EmittedExpr` shape the deployed `MapOpSpec.root` and the
    19-felt map-log tuple `[root8, key, value, op, new_root8]` want:
    `circuit/src/descriptor_ir2.rs:2165-2185`), pins all EIGHT lanes to public inputs on the first
    row, and threads all EIGHT by constancy windows. `weldWit_satisfies` is a real
    `Satisfied2Public` witness for it (⚑ the standing gate: no cost is quoted below without one).
  * **⚠ §3a, the LEG THAT CANNOT WELD HERE, NAMED PRECISELY.** `DescriptorIR2.MapOp.holdsAt` reads
    `(m.root 0)` — LANE 0 ONLY — and `MapOp.rowAt` logs lane 0 only (a 5-felt model row against the
    deployed 19). So the per-row OPENING the IR forces is the ~31-bit scalar `opensTo hash (lane 0)`
    no matter how many lanes the group carries, and the seven completion lanes are pinned and
    threaded but their CONTENT is unforced. `weld_completion_lanes_free` PROVES that: the very same
    descriptor is satisfied with the completion lanes set to ANY felts whatsoever. This is not a
    surprise and not a defect of this file — it is the same status `EffectVmEmitRotationV3` records
    for cap/heap ("the full 8-felt faithfulness is trace-forced by the after-spine keystone
    (`CapOpenEmit`/`HeapOpenEmit`)"), and `MapMerkleRoot` §5b names the fix exactly: "`MapOp.holdsAt`'s
    deployed denotation moves onto `opensToMerkle8`/`writesToMerkle8`". That edit is to
    `DescriptorIR2`, a SHARED file, and is NOT made here.

So, stated at the resolution the objects support: the attestation's COMMITMENT and BINDING are now
8-felt and carry no BabyBear-refuted hypothesis; the descriptor's WIRE is 8-felt; the descriptor's
per-row DENOTATION is still lane-0 scalar, and that is a named IR gap with a named fix, not a claim.

## Axiom hygiene

`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound} on every theorem (§6). NEW file;
imports read-only; `Dregg2.lean` untouched. Every `#guard` in §5 is COMPILED EVALUATION of a closed
`Bool` — it proves NO `Prop`; it pins measured numbers and nothing more.
-/
import Dregg2.Circuit.Emit.AttestedAutomatonEmit
import Dregg2.Circuit.MapMerkleRoot

namespace Dregg2.Circuit.Emit.AttestedAutomatonWeld8

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
  (VmConstraint VmRow VmRowEnv VmRange holdsVm_piFirst_true holdsVm_piLast_true)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Substrate
open Dregg2.Circuit.DeployedCapTree (Digest8 Coll8 Compress8CR)
open Dregg2.Circuit.DeployedHeapTree (Heap8Scheme)
open Dregg2.Circuit.MapMerkleRoot
  (mapRoot8 opensToMerkle8 MapRootColl mapRoot8_binds_or_collides
   opensToMerkle8_functional_or_collides mapRootColl_refutable_of_injective)
open Dregg2.Crypto.DfaAcceptanceAir (TableDfa classifyFrom)
open Dregg2.Circuit.Emit.DfaRoutingTableEmit
  (CURRENT SYMBOL NEXT PI_INITIAL PI_FINAL contWindowBody envAt_loc envAt_nxt)
open Dregg2.Circuit.Emit.TinyAutomataCompose (costOf jsonBytes DescCost)
open Dregg2.Circuit.Emit.TinyAutomataSatisfiable (prodRunDesc probeW)
open Dregg2.Circuit.Emit.AttestedAutomatonEmit
  (ASYM ASTATES NKEYS keyOf kvRows kvRows_length kvRows_sorted kvRows_get
   attContinuity attB1 attB2 attMapRow attTf attPub wordN attestedInstance)

set_option autoImplicit false

/-! ## §1 — THE DEPLOYED 8-FELT COMMITMENT of an automaton.

The heap is the SAME `2^16`-leaf total map (`key = 2s + y ↦ d.step s y`) `AttestedAutomatonEmit`
commits; only the COMMITMENT FUNCTION moves — from the 1-felt `MapMerkleRoot.mapRoot` (`~2^31`
codomain) to the deployed 8-felt `mapRoot8` (`Digest8 = Fin 8 → ℤ`, the `node8` arity-16 chip fold
`heap_root.rs::CanonicalHeapTree8::root`). The heap is re-declared here rather than imported because
`AttestedAutomatonEmit.autoHeap` is `irreducible` past its §1 (deliberately — a root must never
unfold into `2^16` leaves), and the `Heap.get` leg is needed to CONSTRUCT the 8-felt commitment. -/

/-- The automaton's committed heap: key `j ↦ d.step (j / 2) (j % 2)`, TOTAL over the deployed
`2 ^ MAP_TREE_DEPTH` leaves. Definitionally `AttestedAutomatonEmit.autoHeap d`. -/
def autoHeapW (d : TableDfa Nat Nat) : Heap.FeltHeap :=
  kvRows (fun j => ((d.step (j / 2) (j % 2) : Nat) : ℤ)) NKEYS 0

theorem autoHeapW_length (d : TableDfa Nat Nat) :
    (autoHeapW d).length = 2 ^ MAP_TREE_DEPTH := by
  rw [autoHeapW, kvRows_length]
  rfl

theorem autoHeapW_sorted (d : TableDfa Nat Nat) : Heap.SortedKeys (autoHeapW d) :=
  kvRows_sorted _ _ _

/-- The heap READS the automaton at every declared key. -/
theorem autoHeapW_get (d : TableDfa Nat Nat) (s y : Nat) (hs : s < ASTATES) (hy : y < ASYM) :
    Heap.get (autoHeapW d) ((keyOf s y : Nat) : ℤ) = some ((d.step s y : Nat) : ℤ) := by
  have hk : keyOf s y < 0 + NKEYS := by
    have h1 : s < 32768 := by simpa [ASTATES] using hs
    have h2 : y < 2 := by simpa [ASYM] using hy
    show keyOf s y < 0 + 65536
    unfold keyOf
    omega
  have hget := kvRows_get (fun j => ((d.step (j / 2) (j % 2) : Nat) : ℤ)) NKEYS 0 (keyOf s y)
    (Nat.zero_le _) hk
  have hy2 : y < 2 := by simpa [ASYM] using hy
  have hdiv : keyOf s y / 2 = s := by unfold keyOf; omega
  have hmod : keyOf s y % 2 = y := by unfold keyOf; omega
  rw [autoHeapW, hget]
  show some ((d.step (keyOf s y / 2) (keyOf s y % 2) : Nat) : ℤ) = some ((d.step s y : Nat) : ℤ)
  rw [hdiv, hmod]

/-- **THE AUTOMATON'S 8-FELT COMMITMENT.** The deployed `node8` binary-Merkle root of the committed
heap — EIGHT BabyBear felts (`heap_root.rs`), never one. Abstract in the chip `S8`. -/
def autoRoot8 (S8 : Heap8Scheme) (d : TableDfa Nat Nat) : Digest8 :=
  mapRoot8 S8 MAP_TREE_DEPTH (autoHeapW d)

/-- **`CommitsAutomaton8By S8 m R8 d`** — the WITNESS-EXPLICIT form: the sorted `2^16`-leaf heap `m`
is behind the 8-felt root `R8` and reads `d` at every declared key. Explicit (rather than
existential) because the collision extractor's named pair is a function of the WITNESS heaps —
restating the conclusion existentially would be exactly the free pass `MapMerkleRoot` §5b.E refuses. -/
def CommitsAutomaton8By (S8 : Heap8Scheme) (m : Heap.FeltHeap) (R8 : Digest8)
    (d : TableDfa Nat Nat) : Prop :=
  Heap.SortedKeys m ∧ m.length = 2 ^ MAP_TREE_DEPTH ∧ mapRoot8 S8 MAP_TREE_DEPTH m = R8
    ∧ ∀ s y : Nat, s < ASTATES → y < ASYM →
        Heap.get m ((keyOf s y : Nat) : ℤ) = some ((d.step s y : Nat) : ℤ)

/-- ⚑ **THE PREDICATE IS INHABITED FOR EVERY AUTOMATON AND EVERY CHIP** — `autoRoot8` is a
commitment of `d`, CONSTRUCTED. (This is what keeps §2 from being a statement about an empty set;
it consumes no crypto hypothesis.) -/
theorem autoRoot8_commits (S8 : Heap8Scheme) (d : TableDfa Nat Nat) :
    CommitsAutomaton8By S8 (autoHeapW d) (autoRoot8 S8 d) d :=
  ⟨autoHeapW_sorted d, autoHeapW_length d, rfl, autoHeapW_get d⟩

/-- The existential (opening-level) form, for consumers that never see the heap. -/
def CommitsAutomaton8 (S8 : Heap8Scheme) (R8 : Digest8) (d : TableDfa Nat Nat) : Prop :=
  ∀ s y : Nat, s < ASTATES → y < ASYM →
    opensToMerkle8 S8 MAP_TREE_DEPTH R8 ((keyOf s y : Nat) : ℤ) (some ((d.step s y : Nat) : ℤ))

theorem CommitsAutomaton8By.opens {S8 : Heap8Scheme} {m : Heap.FeltHeap} {R8 : Digest8}
    {d : TableDfa Nat Nat} (h : CommitsAutomaton8By S8 m R8 d) : CommitsAutomaton8 S8 R8 d := by
  intro s y hs hy
  exact ⟨m, h.1, h.2.1, h.2.2.1, h.2.2.2 s y hs hy⟩

/-- The 8-felt commitment predicate is inhabited at the opening level too. -/
theorem autoRoot8_opens (S8 : Heap8Scheme) (d : TableDfa Nat Nat) :
    CommitsAutomaton8 S8 (autoRoot8 S8 d) d := (autoRoot8_commits S8 d).opens

/- ⚑ THE OPAQUENESS BARRIER, as in `AttestedAutomatonEmit` §1: past this point a root is ONE opaque
8-felt digest — which is also exactly how the verifier sees it. -/
attribute [irreducible] autoHeapW autoRoot8

/-! ## §2 — ⚑ THE BINDING, RE-PROVEN AT THE DEPLOYED 8-FELT WIDTH.

`AttestedAutomatonEmit.root_binds_automaton` consumes `Poseidon2SpongeCR hash` at a BabyBear
codomain, where it is FALSE. These do not consume it. The honest form is the one `MapMerkleRoot`
§5b exports: BIND, or exhibit the collision a TOTAL extractor names at the deployed arity-16 chip.
`MapRootColl` is not the pigeonhole free pass — it is about the SPECIFIC pair `mapRoot8Find` hands
back, and it is REFUTABLE (`weld_collision_disjunct_refutable`). -/

/-- ⚑ **`root8_binds_automaton_or_collides` — THE WELDED ATTESTATION.** Two automata committed by
the SAME 8-felt root agree on the ENTIRE declared key domain, OR the deployed chip genuinely
collides at the named pair. UNCONDITIONAL: no crypto hypothesis. -/
theorem root8_binds_automaton_or_collides (S8 : Heap8Scheme) (R8 : Digest8)
    (d e : TableDfa Nat Nat) {m₁ m₂ : Heap.FeltHeap}
    (hd : CommitsAutomaton8By S8 m₁ R8 d) (he : CommitsAutomaton8By S8 m₂ R8 e) :
    (∀ s y : Nat, s < ASTATES → y < ASYM → d.step s y = e.step s y)
      ∨ MapRootColl S8 MAP_TREE_DEPTH m₁ m₂ := by
  rcases mapRoot8_binds_or_collides S8 MAP_TREE_DEPTH hd.2.1 he.2.1
    (hd.2.2.1.trans he.2.2.1.symm) with hm | hc
  · refine Or.inl ?_
    intro s y hs hy
    have h1 := hd.2.2.2 s y hs hy
    have h2 := he.2.2.2 s y hs hy
    rw [hm, h2] at h1
    simp only [Option.some.injEq] at h1
    exact_mod_cast h1.symm
  · exact Or.inr hc

/-- **(CANARY — the collision disjunct is REFUTABLE, so §2 is not a free pass.)** Exhibiting the
named-pair disjunct REFUTES the deployed chip's injectivity outright, so nobody discharges §2 by
taking the right branch: the binding half has to do all the work.

⚑ STATED AS ANTI-FLOOR CONTENT, not as a bridge under a `Compress8CR` binder. The two spellings
are definitionally equal (`Γ, F ⊢ False` IS `Γ ⊢ ¬ F`), but the binder spelling makes the canary a
CARRIER of a hypothesis this tree PROVES FALSE at deployed BabyBear parameters
(`VacuitySweepTeeth.deployedHeap8Scheme_chip_not_Compress8CR`) — a theorem the accrual gate must
then grandfather as knowingly vacuous. This spelling assumes no floor, so it is exempt by
construction, and it says strictly MORE: not "at an injective chip the disjunct is empty" but "the
disjunct IS a chip collision".

⚑ **AND IT IS THE ONLY BRIDGE THIS FILE NEEDS — `root8_binds_automaton_of_injective` IS DELETED
(2026-07-25).** That theorem used to sit immediately below: "given `hCR : Compress8CR
S8.chipAbsorb8`, two automata committed by ONE 8-felt root agree on the whole declared domain",
i.e. the injective special case of the line above. It was never a second result. Its type is
inhabited by `Or.resolve_right` over the two theorems that flanked it, in ONE constructive term,
at the same implicit heaps and with no other input:

    Or.resolve_right (root8_binds_automaton_or_collides S8 R8 d e hd he)
                     (fun hc => weld_collision_disjunct_refutable S8 _ _ hc hCR)

So the strength relation is still EXHIBITED, by the pair (`root8_binds_automaton_or_collides`,
this canary), and both halves are floor-free. What the bridge added was the carrier: `Compress8CR`
in binder position, a hypothesis `VacuitySweepTeeth.compress8CR_false_babyBear` PROVES FALSE at
deployed BabyBear parameters and `deployedHeap8Scheme_chip_not_Compress8CR` refutes at the very
scheme it ranged over. It was vacuously true at deployment, it had NO consumer anywhere in the
tree, and keeping it meant recording a knowingly-vacuous theorem in `FloorRatchetBaseline`.

⚑ AND IT IS NOT THE GRANDFATHERED-SIBLING CASE. `DeployedCapTree` §5.1 already settled this exact
question, in prose, before this file existed: *"Deliberately NOT restated as … per-theorem
`…_of_injective` bridges. Each such restatement would be a NEW declaration taking a hypothesis this
tree PROVES FALSE at deployed BabyBear parameters — i.e. a new VACUOUS declaration, which is the
accrual `#floor_ratchet` exists to stop. The 8-felt sibling's `…8_injective_of_injective` family
predates the gate and is grandfathered; this one does not get to add to that pile … One bridge,
used."* The baselined siblings are that grandfathered pile — the six on
`DeployedCapTree.Cap8Scheme` and the four in `MapMerkleRoot` §5b.S. Each one that is spelled
"NO STRENGTH LOST" recovers a NAMED STATEMENT THAT WAS DELETED (`capLeafDigest8_injective`,
`nodeOf8_injective`, `recomposeUp8_inj_of_path`, `mapRoot8_injective`, the existential-level
`opensToMerkle8_functional`, `writesToMerkle8_functional`), so grandfathering it records that a
specific removal cost nothing; the remaining `…Coll_refutable_of_injective` ones are the canary in
the pre-2026-07-25 CARRIER spelling — exactly the content this one now states floor-free. This
bridge is in neither class. It recovered nothing: `root8_binds_automaton_or_collides` was born
unconditional in the SAME commit that introduced the bridge (`915437862f`), and the 1-felt original
it was the analog of (`AttestedAutomatonEmit.root_binds_automaton`) is still in the tree and still
baselined. Deleting is therefore unadditive bookkeeping, not a judgement call. -/
theorem weld_collision_disjunct_refutable (S8 : Heap8Scheme) (m₁ m₂ : Heap.FeltHeap)
    (hc : MapRootColl S8 MAP_TREE_DEPTH m₁ m₂) : ¬ Compress8CR S8.chipAbsorb8 :=
  fun hCR => mapRootColl_refutable_of_injective S8 hCR MAP_TREE_DEPTH m₁ m₂ hc

/-- ⚑ **`forged_edge_refused_8` — THE OTHER POLARITY, WELDED.** A prover opening an edge the
committed automaton does NOT have, at the SAME 8-felt root, must exhibit the named arity-16 chip
collision. (`AttestedAutomatonEmit.forged_edge_refused` says this at ~31 bits under a hypothesis
BabyBear refutes; this says it at the deployed width under none.) -/
theorem forged_edge_refused_8 (S8 : Heap8Scheme) (R8 : Digest8) (d : TableDfa Nat Nat)
    {m mF : Heap.FeltHeap} (hcommit : CommitsAutomaton8By S8 m R8 d)
    (q y n : Nat) (hq : q < ASTATES) (hy : y < ASYM) (hbad : n ≠ d.step q y)
    (_hFsort : Heap.SortedKeys mF) (hFlen : mF.length = 2 ^ MAP_TREE_DEPTH)
    (hFroot : mapRoot8 S8 MAP_TREE_DEPTH mF = R8)
    (hFget : Heap.get mF ((keyOf q y : Nat) : ℤ) = some ((n : Nat) : ℤ)) :
    MapRootColl S8 MAP_TREE_DEPTH mF m := by
  rcases opensToMerkle8_functional_or_collides S8 MAP_TREE_DEPTH hFlen hFroot hFget
    hcommit.2.1 hcommit.2.2.1 (hcommit.2.2.2 q y hq hy) with heq | hc
  · exfalso
    simp only [Option.some.injEq] at heq
    exact hbad (by exact_mod_cast heq)
  · exact hc

/-! ## §3 — THE WELDED DESCRIPTOR: the root as EIGHT columns, EIGHT public inputs, EIGHT windows.

`CURRENT`/`SYMBOL`/`NEXT` are the columns `DfaRoutingTableEmit` uses (0/1/2). Columns 3..10 are the
root GROUP — lane 0 the scalar limb, lanes 1..7 the completion limbs, exactly the shape
`EffectVmEmitRotationV3.beforeCapRootGroup`/`beforeHeapRootGroup` carry (`fun i => .var (groupCol i)`)
and exactly what the deployed 19-felt map-log tuple `[root8, key, value, op, new_root8]` reads
(`circuit/src/descriptor_ir2.rs:2165-2185`). -/

/-- The root group's column at lane `i` (lane 0 = column 3 = the old scalar `ROOT`). -/
def W8ROOT (i : Fin 8) : Nat := 3 + i.val
/-- Total main-trace width: 3 + the 8 root lanes. -/
def WELD_WIDTH : Nat := 11
/-- The public input carrying root lane `i` (lane 0 = pi[2] = the old scalar `PI_ROOT`). -/
def PI_W8ROOT (i : Fin 8) : Nat := 2 + i.val
/-- Number of public inputs: `initial_state`, `final_state`, and the 8 root lanes. -/
def WELD_PI_COUNT : Nat := 10

/-- **THE 8-FELT ROOT GROUP** — the REAL lanes, mirroring `beforeCapRootGroup`. NOT
`scalarRootGroup`: no column is carried across all eight lanes. -/
def weldRootGroup : Fin 8 → EmittedExpr := fun i => .var (W8ROOT i)

/-- **THE ATTESTATION TOOTH, on the 8-lane group.** A `.read` at key `2·current + symbol`; the
post-root group IS the pre-root group (a read moves no root). -/
def weldTransitionOpen : VmConstraint2 :=
  .mapOp { guard   := .const 1
         , root    := weldRootGroup
         , key     := .add (.mul (.const 2) (.var CURRENT)) (.var SYMBOL)
         , value   := .var NEXT
         , newRoot := weldRootGroup
         , op      := .read }

/-- Lane `i`'s constancy body: `Nxt(root_i) − Loc(root_i)`. ⚑ `GateExpr.gCarry`. -/
def weldRootBody (i : Fin 8) : WindowExpr :=
  Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toWindow
    (Dregg2.Circuit.GateExpr.gCarry (W8ROOT i))

theorem weldRootBody_eq (i : Fin 8) :
    weldRootBody i = WindowExpr.add (.nxt (W8ROOT i)) (.mul (.const (-1)) (.loc (W8ROOT i))) := rfl

/-- Lane `i`'s constancy window — one automaton for the whole run, on EVERY lane. -/
def weldRootConst (i : Fin 8) : VmConstraint2 := .windowGate ⟨weldRootBody i, true⟩

/-- Lane `i`'s first-row public pin — the attestation's public face, EIGHT felts wide. -/
def weldB3 (i : Fin 8) : VmConstraint2 :=
  .base (.piBinding VmRow.first (W8ROOT i) (PI_W8ROOT i))

/-- The 16 lane constraints: a constancy window and a public pin per lane. -/
def weldLaneConstraints : List VmConstraint2 :=
  (List.finRange 8).flatMap (fun i => [weldRootConst i, weldB3 i])

/-! ### §3.G — ⚑ GRADUATED (2026-11-06): the two range teeth are range-TABLE LOOKUPS.

The v2 assembly refuses a descriptor with a non-empty `ranges` carrier
(`circuit/src/descriptor_ir2.rs::check_descriptor2`). The weld's two teeth (`CURRENT < 2^15`,
`SYMBOL < 2`) are therefore lowered the way `EffectVmEmitV2.graduateV1Wide` lowers a v1 `VmRange`:
a lookup of the bare column into a range table of ITS OWN width. Both widths are already served
tables: `range_w15` (wire id 84, the borrow-limb table of the faithful spend) and `range_w1` (wire
id 70, the Pasta/Mina bit table). The ids follow `EffectVmEmitV2.rangeTidW` (`.custom (64 + bits)`)
and are spelled here rather than imported, because that module's import closure is the whole
effect-VM tower. No limb split is needed: the 15-bit table bounds `CURRENT` exactly, so the main
trace gains no column; the Rust assembly realizes each lookup with its own byte-limb aux columns.
`weld_lookups_bound` (below) is the tooth the old carrier stated: against faithful range tables
every accepted row has `0 ≤ CURRENT < 2^15` and `0 ≤ SYMBOL < 2`. -/

/-- The 15-bit range table's id (= `EffectVmEmitV2.rangeTidW 15`, wire id 84). -/
def WELD_TID_RANGE15 : TableId := .custom 79
/-- The 1-bit range table's id (= `EffectVmEmitV2.rangeTidW 1`, wire id 70). -/
def WELD_TID_RANGE1 : TableId := .custom 65

/-- `range_w15`: rows `[0, 2^15)`. -/
def weldRange15Def : TableDef := ⟨WELD_TID_RANGE15, "range_w15", 1, .rangeLimb 15⟩
/-- `range_w1`: rows `[0, 2)`. -/
def weldRange1Def : TableDef := ⟨WELD_TID_RANGE1, "range_w1", 1, .rangeLimb 1⟩

/-- `CURRENT ∈ [0, 2^15)` — the state bound, by lookup. -/
def weldCurRange : VmConstraint2 := .lookup ⟨WELD_TID_RANGE15, [.var CURRENT]⟩
/-- `SYMBOL ∈ [0, 2)` — the alphabet bound, by lookup. -/
def weldSymRange : VmConstraint2 := .lookup ⟨WELD_TID_RANGE1, [.var SYMBOL]⟩

/-- The two range lookups, appended after the lane constraints. -/
def weldRangeLookups : List VmConstraint2 := [weldCurRange, weldSymRange]

/-- The witness-side contract the Rust range tables realize: each width's table IS its range. -/
def WeldRangeTablesFaithful (tf : TraceFamily) : Prop :=
  tf WELD_TID_RANGE15 = rangeRows 15 ∧ tf WELD_TID_RANGE1 = rangeRows 1

/-- **`weldDesc name`** — the 8-FELT WELDED attested descriptor, GRADUATED. 11 columns, 10 PIs, 22
constraints (20 + the two range lookups), the map-ops table and the two range tables, ZERO declared
rows, EMPTY `hashSites`/`ranges` carriers; wire bytes constant in `|w|` and in `|Q|·|Σ|`. -/
def weldDesc (name : String) : EffectVmDescriptor2 :=
  { name        := name
  , traceWidth  := WELD_WIDTH
  , piCount     := WELD_PI_COUNT
  , tables      := [mapOpsTableDef, weldRange15Def, weldRange1Def]
  , constraints := weldTransitionOpen :: attContinuity :: attB1 :: attB2 ::
      (weldLaneConstraints ++ weldRangeLookups)
  , hashSites   := []
  , ranges      := [] }

/-- The canonical pinned instance name. -/
def WELD_NAME : String := "dregg-attested-automaton::map-committed-weld8-v1"

/-- The pinned instance. -/
def weldInstance : EffectVmDescriptor2 := weldDesc WELD_NAME

theorem weldOpen_mem (name : String) : weldTransitionOpen ∈ (weldDesc name).constraints :=
  List.mem_cons_self
theorem weldCont_mem (name : String) : attContinuity ∈ (weldDesc name).constraints :=
  List.mem_cons_of_mem _ List.mem_cons_self
theorem weldB1_mem (name : String) : attB1 ∈ (weldDesc name).constraints :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
theorem weldB2_mem (name : String) : attB2 ∈ (weldDesc name).constraints :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem weldLane_mem (name : String) {c : VmConstraint2} (hc : c ∈ weldLaneConstraints) :
    c ∈ (weldDesc name).constraints :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_append_left _ hc))))

theorem weldCurRange_mem (name : String) : weldCurRange ∈ (weldDesc name).constraints :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))))

theorem weldSymRange_mem (name : String) : weldSymRange ∈ (weldDesc name).constraints :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_cons_of_mem _ List.mem_cons_self)))))

theorem weldRootConst_mem (name : String) (i : Fin 8) :
    weldRootConst i ∈ (weldDesc name).constraints :=
  weldLane_mem name (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, List.mem_cons_self⟩)

theorem weldB3_mem (name : String) (i : Fin 8) : weldB3 i ∈ (weldDesc name).constraints :=
  weldLane_mem name
    (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, List.mem_cons_of_mem _ List.mem_cons_self⟩)

/-- Every lane constraint is one of the two shapes, at some lane. -/
theorem weldLane_classify {c : VmConstraint2} (hc : c ∈ weldLaneConstraints) :
    ∃ i : Fin 8, c = weldRootConst i ∨ c = weldB3 i := by
  rw [weldLaneConstraints, List.mem_flatMap] at hc
  obtain ⟨i, _, h⟩ := hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  exact ⟨i, h⟩

/-- The tail past the four head constraints: a lane constraint or a range lookup. -/
theorem weldTail_classify {c : VmConstraint2} (hc : c ∈ weldLaneConstraints ++ weldRangeLookups) :
    (∃ i : Fin 8, c = weldRootConst i ∨ c = weldB3 i) ∨ c = weldCurRange ∨ c = weldSymRange := by
  rcases List.mem_append.mp hc with h | h
  · exact Or.inl (weldLane_classify h)
  · simp only [weldRangeLookups, List.mem_cons, List.not_mem_nil, or_false] at h
    exact Or.inr h

/-- The descriptor declares no memory ops … -/
theorem weld_memOps (name : String) : memOpsOf (weldDesc name) = [] := by
  show List.filterMap (fun c => match c with | .memOp m => some m | _ => none)
    (weldLaneConstraints ++ weldRangeLookups) = []
  rw [List.filterMap_eq_nil_iff]
  intro c hc
  rcases weldTail_classify hc with ⟨i, h | h⟩ | h | h <;> rw [h] <;> rfl

theorem weld_memLog (name : String) (t : VmTrace) : memLog (weldDesc name) t = [] := by
  simp [memLog, weld_memOps]

/-- … and exactly one map op, whose logged row is lane 0 of the group (⚠ §3a). -/
theorem weld_mapOps (name : String) :
    mapOpsOf (weldDesc name)
      = [{ guard   := .const 1
         , root    := weldRootGroup
         , key     := .add (.mul (.const 2) (.var CURRENT)) (.var SYMBOL)
         , value   := .var NEXT
         , newRoot := weldRootGroup
         , op      := .read }] := by
  have htail : List.filterMap (fun c => match c with | .mapOp m => some m | _ => none)
      (weldLaneConstraints ++ weldRangeLookups) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro c hc
    rcases weldTail_classify hc with ⟨i, h | h⟩ | h | h <;> rw [h] <;> rfl
  show ({ guard   := .const 1
        , root    := weldRootGroup
        , key     := .add (.mul (.const 2) (.var CURRENT)) (.var SYMBOL)
        , value   := .var NEXT
        , newRoot := weldRootGroup
        , op      := .read } : MapOp)
      :: List.filterMap (fun c => match c with | .mapOp m => some m | _ => none)
           (weldLaneConstraints ++ weldRangeLookups) = _
  rw [htail]

/-- The map log is exactly one row per trace row — the SAME `attMapRow` shape the unwelded object
logs, because `MapOp.rowAt` reads lane 0 only (⚠ §3a: the deployed row is 19 felts, the model's 5). -/
theorem weld_mapLog (name : String) (t : VmTrace) :
    mapLog (weldDesc name) t = t.rows.map attMapRow := by
  show t.rows.flatMap _ = _
  simp only [weld_mapOps]
  induction t.rows with
  | nil => rfl
  | cons a rest ih => rw [List.flatMap_cons, ih]; rfl

/-! ### §3.W — ⚑ THE GATE: a real `Satisfied2Public` WITNESS for the welded descriptor. -/

/-- One 11-column trace row: `(current, symbol, next, root₀ … root₇)`. -/
def asgW (s y n : Nat) (R8 : Digest8) : Assignment := fun c =>
  if c = 0 then Int.ofNat s else if c = 1 then Int.ofNat y else if c = 2 then Int.ofNat n
  else if h : c - 3 < 8 then R8 ⟨c - 3, h⟩ else 0

@[simp] theorem asgW_current (s y n : Nat) (R8 : Digest8) : asgW s y n R8 CURRENT = Int.ofNat s :=
  rfl
@[simp] theorem asgW_symbol (s y n : Nat) (R8 : Digest8) : asgW s y n R8 SYMBOL = Int.ofNat y := rfl
@[simp] theorem asgW_next (s y n : Nat) (R8 : Digest8) : asgW s y n R8 NEXT = Int.ofNat n := rfl
@[simp] theorem asgW_root (s y n : Nat) (R8 : Digest8) (i : Fin 8) :
    asgW s y n R8 (W8ROOT i) = R8 i := by
  fin_cases i <;> rfl

/-- The run's trace rows, carrying the full 8-lane root group on every row. -/
def rowsW (d : TableDfa Nat Nat) (R8 : Digest8) (q : Nat) : List Nat → List Assignment
  | []      => []
  | y :: ys => asgW q y (d.step q y) R8 :: rowsW d R8 (d.step q y) ys

theorem rowsW_length (d : TableDfa Nat Nat) (R8 : Digest8) :
    ∀ (w : List Nat) (q : Nat), (rowsW d R8 q w).length = w.length
  | [],      _ => rfl
  | y :: ys, q => by
    show (rowsW d R8 (d.step q y) ys).length + 1 = ys.length + 1
    rw [rowsW_length d R8 ys (d.step q y)]

/-- Every row is an in-domain edge of `d` carrying the root group — discharges the attestation
tooth and both range teeth. -/
theorem rowsW_shape (d : TableDfa Nat Nat) (hstep : ∀ s y, d.step s y < ASTATES) (R8 : Digest8) :
    ∀ (w : List Nat) (q : Nat), q < ASTATES → (∀ y ∈ w, y < ASYM) →
      ∀ (i : Nat) (h : i < (rowsW d R8 q w).length),
        ∃ s y : Nat, s < ASTATES ∧ y < ASYM ∧ (rowsW d R8 q w)[i]'h = asgW s y (d.step s y) R8 := by
  intro w
  induction w with
  | nil => intro q _ _ i h; simp [rowsW] at h
  | cons y ys ih =>
    intro q hq hy i h
    cases i with
    | zero => exact ⟨q, y, hq, hy y List.mem_cons_self, rfl⟩
    | succ j =>
      have h' : j < (rowsW d R8 (d.step q y) ys).length := by simpa [rowsW] using h
      obtain ⟨s, y', hs, hy', hrow⟩ :=
        ih (d.step q y) (hstep q y) (fun z hz => hy z (List.mem_cons_of_mem _ hz)) j h'
      exact ⟨s, y', hs, hy', hrow⟩

theorem rowsW_chain (d : TableDfa Nat Nat) (R8 : Digest8) :
    ∀ (w : List Nat) (q i : Nat) (h : i + 1 < (rowsW d R8 q w).length),
      ((rowsW d R8 q w)[i + 1]'h) CURRENT
        = ((rowsW d R8 q w)[i]'(Nat.lt_of_succ_lt h)) NEXT := by
  intro w
  induction w with
  | nil => intro q i h; simp [rowsW] at h
  | cons y ys ih =>
    intro q i h
    cases i with
    | zero =>
      cases ys with
      | nil => simp [rowsW] at h
      | cons y' ys' => rfl
    | succ j => exact ih (d.step q y) j (by simpa [rowsW] using h)

/-- Every row carries the SAME root group, LANE BY LANE. -/
theorem rowsW_root (d : TableDfa Nat Nat) (R8 : Digest8) (l : Fin 8) :
    ∀ (w : List Nat) (q i : Nat) (h : i < (rowsW d R8 q w).length),
      ((rowsW d R8 q w)[i]'h) (W8ROOT l) = R8 l := by
  intro w
  induction w with
  | nil => intro q i h; simp [rowsW] at h
  | cons y ys ih =>
    intro q i h
    cases i with
    | zero => exact asgW_root _ _ _ R8 l
    | succ j => exact ih (d.step q y) j (by simpa [rowsW] using h)

theorem rowsW_head_current (d : TableDfa Nat Nat) (R8 : Digest8) (q : Nat) (w : List Nat)
    (hw : w ≠ []) (h : 0 < (rowsW d R8 q w).length) :
    ((rowsW d R8 q w)[0]'h) CURRENT = Int.ofNat q := by
  cases w with
  | nil => exact absurd rfl hw
  | cons y ys => rfl

theorem rowsW_last_next (d : TableDfa Nat Nat) (R8 : Digest8) :
    ∀ (w : List Nat) (q i : Nat) (h : i < (rowsW d R8 q w).length),
      i + 1 = (rowsW d R8 q w).length →
      ((rowsW d R8 q w)[i]'h) NEXT = Int.ofNat (classifyFrom d q w) := by
  intro w
  induction w with
  | nil => intro q i h _; simp [rowsW] at h
  | cons y ys ih =>
    intro q i h hlast
    cases i with
    | zero =>
      have hys : ys = [] := by
        have h0 : (rowsW d R8 (d.step q y) ys).length = 0 := by
          simp only [rowsW, List.length_cons] at hlast
          omega
        rw [rowsW_length d R8 ys (d.step q y)] at h0
        exact List.eq_nil_of_length_eq_zero h0
      subst hys
      rfl
    | succ j =>
      exact ih (d.step q y) j (by simpa [rowsW] using h) (by simpa [rowsW] using hlast)

/-- The welded public inputs: `(initial_state, final_state, root₀ … root₇)`. -/
def weldPub (q f : Nat) (R8 : Digest8) : Assignment := fun k =>
  if k = 0 then Int.ofNat q else if k = 1 then Int.ofNat f
  else if h : k - 2 < 8 then R8 ⟨k - 2, h⟩ else 0

@[simp] theorem weldPub_root (q f : Nat) (R8 : Digest8) (i : Fin 8) :
    weldPub q f R8 (PI_W8ROOT i) = R8 i := by
  fin_cases i <;> rfl

/-- The welded witness's table family: the map log at `.mapOps`, the two range tables at their ids
(the faithful contents the Rust assembly realizes), empty elsewhere. -/
def weldTf (rows : List Assignment) : TraceFamily :=
  fun id => if id = TableId.mapOps then rows.map attMapRow
    else if id = WELD_TID_RANGE15 then rangeRows 15
    else if id = WELD_TID_RANGE1 then rangeRows 1 else []

theorem weldTf_faithful (rows : List Assignment) : WeldRangeTablesFaithful (weldTf rows) :=
  ⟨rfl, rfl⟩

/-- **THE WELDED WITNESS**: the trace that runs `d` from `q` on `w` against the 8-lane group `R8`. -/
def weldWit (d : TableDfa Nat Nat) (R8 : Digest8) (q : Nat) (w : List Nat) : VmTrace :=
  { rows := rowsW d R8 q w
  , pub  := weldPub q (classifyFrom d q w) R8
  , tf   := weldTf (rowsW d R8 q w) }

/-- **Both range LOOKUPS hold on every row of the welded witness**, against any table family whose
two range tables are faithful (`CURRENT < 2^15`, `SYMBOL < 2`, by `range_row_mem_iff`). Hash-free.
(Before graduation this was `weldWit_rowRanges`, over the `ranges` carrier.) -/
theorem weldWit_rangeLookups (tf : TraceFamily) (htf : WeldRangeTablesFaithful tf)
    (d : TableDfa Nat Nat) (R8 : Digest8)
    (hstep : ∀ s y, d.step s y < ASTATES) (q : Nat) (hq : q < ASTATES)
    (w : List Nat) (hsym : ∀ y ∈ w, y < ASYM)
    (i : Nat) (hi : i < (weldWit d R8 q w).rows.length) :
    Lookup.holdsAt tf (envAt (weldWit d R8 q w) i) ⟨WELD_TID_RANGE15, [.var CURRENT]⟩
      ∧ Lookup.holdsAt tf (envAt (weldWit d R8 q w) i) ⟨WELD_TID_RANGE1, [.var SYMBOL]⟩ := by
  have hi' : i < (rowsW d R8 q w).length := hi
  have hloc : (envAt (weldWit d R8 q w) i).loc = (rowsW d R8 q w)[i]'hi' :=
    envAt_loc (t := weldWit d R8 q w) hi
  obtain ⟨s, y, hs, hy, hrow⟩ := rowsW_shape d hstep R8 w q hq hsym i hi'
  refine ⟨?_, ?_⟩
  · show [(EmittedExpr.var CURRENT).eval (envAt (weldWit d R8 q w) i).loc] ∈ tf WELD_TID_RANGE15
    rw [htf.1, range_row_mem_iff]
    simp only [EmittedExpr.eval]
    rw [hloc, hrow, asgW_current]
    refine ⟨Int.natCast_nonneg s, ?_⟩
    have hlt : s < 2 ^ 15 := by simpa [ASTATES] using hs
    rw [Int.ofNat_eq_natCast]
    exact_mod_cast hlt
  · show [(EmittedExpr.var SYMBOL).eval (envAt (weldWit d R8 q w) i).loc] ∈ tf WELD_TID_RANGE1
    rw [htf.2, range_row_mem_iff]
    simp only [EmittedExpr.eval]
    rw [hloc, hrow, asgW_symbol]
    refine ⟨Int.natCast_nonneg y, ?_⟩
    have hlt : y < 2 ^ 1 := by simpa [ASYM] using hy
    rw [Int.ofNat_eq_natCast]
    exact_mod_cast hlt

/-- **Every NON-map constraint of the welded descriptor holds on every row of the welded witness, for
ANY `hash` and ANY table family whose two range tables are faithful** — continuity, the two state
pins, the eight constancy windows and the eight lane pins read neither; the two range lookups read
only the range tables. Factored out of `weldWit_satisfies` (2026-11-05) so the LANE-COMPLETE
denotation in `AttestedAutomatonLanes8` reuses it verbatim instead of re-proving it. -/
theorem weldWit_rowConstraints_nonmap (hash : List ℤ → ℤ) (tf : TraceFamily)
    (htf : WeldRangeTablesFaithful tf)
    (d : TableDfa Nat Nat) (R8 : Digest8)
    (hstep : ∀ s y, d.step s y < ASTATES) (q : Nat) (hq : q < ASTATES)
    (w : List Nat) (hw : w ≠ []) (hsym : ∀ y ∈ w, y < ASYM) (name : String)
    (i : Nat) (hi : i < (weldWit d R8 q w).rows.length)
    (c : VmConstraint2) (hc : c ∈ (weldDesc name).constraints) (hne : c ≠ weldTransitionOpen) :
    c.holdsAt hash tf (envAt (weldWit d R8 q w) i) (i == 0)
      (i + 1 == (weldWit d R8 q w).rows.length) := by
  have hi' : i < (rowsW d R8 q w).length := hi
  have hloc : (envAt (weldWit d R8 q w) i).loc = (rowsW d R8 q w)[i]'hi' :=
    envAt_loc (t := weldWit d R8 q w) hi
  simp only [weldDesc, List.mem_cons] at hc
  rcases hc with rfl | rfl | rfl | rfl | hc
  · exact absurd rfl hne
  · -- continuity
    show WindowConstraint.holdsAt (envAt (weldWit d R8 q w) i)
      (i + 1 == (weldWit d R8 q w).rows.length) ⟨contWindowBody, true⟩
    simp only [WindowConstraint.holdsAt, if_true]
    intro hnl
    have hlt : i + 1 < (rowsW d R8 q w).length := by
      have hne' : ¬ (i + 1 = (rowsW d R8 q w).length) := by
        intro hEq
        rw [show (weldWit d R8 q w).rows = rowsW d R8 q w from rfl, hEq] at hnl
        simp at hnl
      omega
    have hnxt : (envAt (weldWit d R8 q w) i).nxt = (rowsW d R8 q w)[i + 1]'hlt :=
      envAt_nxt (t := weldWit d R8 q w) hlt
    have hch : ((rowsW d R8 q w)[i + 1]'hlt) CURRENT = ((rowsW d R8 q w)[i]'hi') NEXT :=
      rowsW_chain d R8 w q i hlt
    show (WindowExpr.add (.nxt CURRENT) (.mul (.const (-1)) (.loc NEXT))).eval
      (envAt (weldWit d R8 q w) i) ≡ 0 [ZMOD 2013265921]
    simp only [WindowExpr.eval]
    rw [hloc, hnxt, hch]
    have hz : ((rowsW d R8 q w)[i]'hi') NEXT + (-1) * ((rowsW d R8 q w)[i]'hi') NEXT = 0 := by
      ring
    rw [hz]
  · -- B1
    show (i == 0) = true → (envAt (weldWit d R8 q w) i).loc CURRENT
      ≡ (envAt (weldWit d R8 q w) i).pub PI_INITIAL [ZMOD 2013265921]
    intro hf
    have hi0 : i = 0 := by simpa using hf
    subst hi0
    rw [hloc, rowsW_head_current d R8 q w hw hi']
    exact Int.ModEq.refl _
  · -- B2
    show (i + 1 == (weldWit d R8 q w).rows.length) = true →
      (envAt (weldWit d R8 q w) i).loc NEXT
        ≡ (envAt (weldWit d R8 q w) i).pub PI_FINAL [ZMOD 2013265921]
    intro hl
    have hlast : i + 1 = (rowsW d R8 q w).length :=
      (by simpa using hl : i + 1 = (weldWit d R8 q w).rows.length)
    rw [hloc, rowsW_last_next d R8 w q i hi' hlast]
    exact Int.ModEq.refl _
  · -- the EIGHT lane constraints (constancy and the public pin, per lane), then the two lookups
    rcases weldTail_classify hc with ⟨l, hl | hl⟩ | hl | hl
    rotate_left 2
    · subst hl
      exact (weldWit_rangeLookups tf htf d R8 hstep q hq w hsym i hi).1
    · subst hl
      exact (weldWit_rangeLookups tf htf d R8 hstep q hq w hsym i hi).2
    · subst hl
      show WindowConstraint.holdsAt (envAt (weldWit d R8 q w) i)
        (i + 1 == (weldWit d R8 q w).rows.length) ⟨weldRootBody l, true⟩
      simp only [WindowConstraint.holdsAt, if_true]
      intro hnl
      have hlt : i + 1 < (rowsW d R8 q w).length := by
        have hne' : ¬ (i + 1 = (rowsW d R8 q w).length) := by
          intro hEq
          rw [show (weldWit d R8 q w).rows = rowsW d R8 q w from rfl, hEq] at hnl
          simp at hnl
        omega
      have hnxt : (envAt (weldWit d R8 q w) i).nxt = (rowsW d R8 q w)[i + 1]'hlt :=
        envAt_nxt (t := weldWit d R8 q w) hlt
      show (WindowExpr.add (.nxt (W8ROOT l)) (.mul (.const (-1)) (.loc (W8ROOT l)))).eval
        (envAt (weldWit d R8 q w) i) ≡ 0 [ZMOD 2013265921]
      simp only [WindowExpr.eval]
      rw [hloc, hnxt, rowsW_root d R8 l w q (i + 1) hlt, rowsW_root d R8 l w q i hi']
      have hz : R8 l + (-1) * R8 l = 0 := by ring
      rw [hz]
    · subst hl
      show (i == 0) = true → (envAt (weldWit d R8 q w) i).loc (W8ROOT l)
        ≡ (envAt (weldWit d R8 q w) i).pub (PI_W8ROOT l) [ZMOD 2013265921]
      intro hf
      have hi0 : i = 0 := by simpa using hf
      subst hi0
      rw [hloc, rowsW_root d R8 l w q 0 hi']
      show R8 l ≡ weldPub q (classifyFrom d q w) R8 (PI_W8ROOT l) [ZMOD 2013265921]
      rw [weldPub_root]

/-- The graduated descriptor's `ranges` carrier is EMPTY: the two teeth live in the lookups. -/
theorem weld_ranges (name : String) : (weldDesc name).ranges = [] := rfl

/-- ⚑ **THE TOOTH THE GRADUATION KEEPS.** Any trace whose row constraints hold against faithful range
tables bounds every row: `0 ≤ CURRENT < 2^15` and `0 ≤ SYMBOL < 2` — exactly the old `ranges`
carrier's `VmRange.holds`, now forced by the two lookups. -/
theorem weld_lookups_bound (hash : List ℤ → ℤ) (name : String) (t : VmTrace)
    (htf : WeldRangeTablesFaithful t.tf)
    (hrows : ∀ i < t.rows.length, ∀ c ∈ (weldDesc name).constraints,
      c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length))
    (i : Nat) (hi : i < t.rows.length) :
    VmRange.holds (envAt t i) ⟨CURRENT, 15⟩ ∧ VmRange.holds (envAt t i) ⟨SYMBOL, 1⟩ := by
  have h1 : [(EmittedExpr.var CURRENT).eval (envAt t i).loc] ∈ t.tf WELD_TID_RANGE15 :=
    hrows i hi weldCurRange (weldCurRange_mem name)
  have h2 : [(EmittedExpr.var SYMBOL).eval (envAt t i).loc] ∈ t.tf WELD_TID_RANGE1 :=
    hrows i hi weldSymRange (weldSymRange_mem name)
  rw [htf.1, range_row_mem_iff] at h1
  rw [htf.2, range_row_mem_iff] at h2
  exact ⟨h1, h2⟩

/-- **The falsifier for the tooth**: a row at state `2^15` (one past the domain) FAILS the 15-bit
lookup against the faithful table. Without the lookup (the run-table shape) it would be accepted. -/
theorem weld_range_refuses_out_of_domain (tf : TraceFamily) (htf : WeldRangeTablesFaithful tf)
    (env : VmRowEnv) (hcur : env.loc CURRENT = 2 ^ 15) :
    ¬ Lookup.holdsAt tf env ⟨WELD_TID_RANGE15, [.var CURRENT]⟩ := by
  intro h
  have h' : [(EmittedExpr.var CURRENT).eval env.loc] ∈ tf WELD_TID_RANGE15 := h
  rw [htf.1, range_row_mem_iff] at h'
  simp only [EmittedExpr.eval] at h'
  rw [hcur] at h'
  exact absurd h'.2 (lt_irrefl _)

/-- ⚑ **THE GATE — a real `Satisfied2Public` witness for the WELDED descriptor.** General in the
automaton, the start state, the word, the descriptor name, and in ALL EIGHT root lanes. The only
crypto-shaped input is `hscal`, the LANE-0 scalar opening the IR's `MapOp.holdsAt` reads (⚠ §3a) —
and `AttestedAutomatonEmit.autoRoot_commits` CONSTRUCTS one, so the corollary below needs nothing. -/
theorem weldWit_satisfies (hash : List ℤ → ℤ) (d : TableDfa Nat Nat) (R8 : Digest8)
    (hscal : Dregg2.Circuit.Emit.AttestedAutomatonEmit.CommitsAutomaton hash (R8 0) d)
    (hstep : ∀ s y, d.step s y < ASTATES) (q : Nat) (hq : q < ASTATES)
    (w : List Nat) (hw : w ≠ []) (hsym : ∀ y ∈ w, y < ASYM) (name : String) :
    Satisfied2Public hash (weldDesc name)
      (fun _ => 0) (fun _ => (0, 0)) [] (weldWit d R8 q w) where
  rowConstraints := by
    intro i hi c hc
    by_cases hne : c = weldTransitionOpen
    · subst hne
      have hi' : i < (rowsW d R8 q w).length := hi
      have hloc : (envAt (weldWit d R8 q w) i).loc = (rowsW d R8 q w)[i]'hi' :=
        envAt_loc (t := weldWit d R8 q w) hi
      obtain ⟨s, y, hs, hy, hrow⟩ := rowsW_shape d hstep R8 w q hq hsym i hi'
      -- the ATTESTATION tooth, at lane 0 (the leg the shared IR denotes; ⚠ §3a)
      show ((1 : ℤ) = 1 → _)
      intro _
      rw [hloc, hrow]
      constructor
      · show opensTo hash (asgW s y (d.step s y) R8 (W8ROOT 0))
          (2 * Int.ofNat s + Int.ofNat y) (some (Int.ofNat (d.step s y)))
        rw [asgW_root]
        have hkey : (2 : ℤ) * Int.ofNat s + Int.ofNat y = ((keyOf s y : Nat) : ℤ) := by
          simp only [keyOf, Int.ofNat_eq_natCast]
          push_cast
          ring
        rw [hkey]
        exact hscal s y hs hy
      · rfl
    · exact weldWit_rowConstraints_nonmap hash _ (weldTf_faithful _) d R8 hstep q hq w hw hsym
        name i hi c hc hne
  rowHashes := by intro i _; trivial
  rowRanges := fun _ _ r hr => absurd hr (by rw [weld_ranges]; exact List.not_mem_nil)
  memAddrsNodup := List.nodup_nil
  memClosed := by rw [weld_memLog]; simp
  memDisciplined := by rw [weld_memLog]; trivial
  memBalanced := by rw [weld_memLog]; exact memCheck_nil _ _
  memTableFaithful := by rw [weld_memLog]; rfl
  mapTableFaithful := by rw [weld_mapLog]; rfl
  publicTablesFaithful := by
    intro td htd
    simp only [weldDesc, List.mem_cons, List.not_mem_nil, or_false] at htd
    rcases htd with rfl | rfl | rfl <;> trivial
  publicLookupBalanced := by
    intro td htd
    simp only [weldDesc, List.mem_cons, List.not_mem_nil, or_false] at htd
    rcases htd with rfl | rfl | rfl <;> trivial

/-- ⚑ **THE GATE, FIRED UNCONDITIONALLY.** The lane-0 scalar root is CONSTRUCTED
(`AttestedAutomatonEmit.autoRoot_commits`), so the welded descriptor has a real `Satisfied2Public`
witness with NO hypothesis about any hash — general in the automaton, the word, and in the seven
completion lanes `hi`. -/
theorem weldWit_satisfies_constructed (hash : List ℤ → ℤ) (d : TableDfa Nat Nat)
    (hi : Fin 8 → ℤ) (hstep : ∀ s y, d.step s y < ASTATES) (q : Nat) (hq : q < ASTATES)
    (w : List Nat) (hw : w ≠ []) (hsym : ∀ y ∈ w, y < ASYM) (name : String) :
    Satisfied2Public hash (weldDesc name) (fun _ => 0) (fun _ => (0, 0)) []
      (weldWit d (fun l => if l = 0 then
          Dregg2.Circuit.Emit.AttestedAutomatonEmit.autoRoot hash d else hi l) q w) :=
  weldWit_satisfies hash d _
    (by
      show Dregg2.Circuit.Emit.AttestedAutomatonEmit.CommitsAutomaton hash
        (if (0 : Fin 8) = 0 then Dregg2.Circuit.Emit.AttestedAutomatonEmit.autoRoot hash d
         else hi 0) d
      rw [if_pos rfl]
      exact Dregg2.Circuit.Emit.AttestedAutomatonEmit.autoRoot_commits hash d)
    hstep q hq w hw hsym name

/-! ### §3a — ⚠ THE LEG THAT DOES NOT WELD IN THIS IR, EXHIBITED.

`DescriptorIR2.MapOp.holdsAt` reads `(m.root 0)` and `MapOp.rowAt` logs `(m.root 0)`: the per-row
denotation is LANE 0, whatever the group carries. So the descriptor CANNOT force the seven
completion lanes, and the theorem below exhibits it rather than asserting it — the same witness, the
same descriptor, ANY completion lanes. (This is the exact status `EffectVmEmitRotationV3` records
for cap/heap: the 8-felt faithfulness is trace-forced by the after-spine keystone, not by the
`MapOp`. The IR fix `MapMerkleRoot` §5b names — moving `MapOp.holdsAt` onto `opensToMerkle8` — is a
`DescriptorIR2` edit, not made here.) -/

/-- ⚠ **THE COMPLETION LANES ARE FREE.** For ANY two assignments of lanes 1..7 the welded descriptor
is satisfied by the corresponding witness. The 8-felt weld is real ON THE WIRE (8 columns, 8 public
pins, 8 constancy windows) and NOT YET content-forcing IN THE DENOTATION. -/
theorem weld_completion_lanes_free (hash : List ℤ → ℤ) (d : TableDfa Nat Nat)
    (hi hi' : Fin 8 → ℤ) (hstep : ∀ s y, d.step s y < ASTATES) (q : Nat) (hq : q < ASTATES)
    (w : List Nat) (hw : w ≠ []) (hsym : ∀ y ∈ w, y < ASYM) (name : String) :
    Satisfied2Public hash (weldDesc name) (fun _ => 0) (fun _ => (0, 0)) []
        (weldWit d (fun l => if l = 0 then
          Dregg2.Circuit.Emit.AttestedAutomatonEmit.autoRoot hash d else hi l) q w)
      ∧ Satisfied2Public hash (weldDesc name) (fun _ => 0) (fun _ => (0, 0)) []
        (weldWit d (fun l => if l = 0 then
          Dregg2.Circuit.Emit.AttestedAutomatonEmit.autoRoot hash d else hi' l) q w) :=
  ⟨weldWit_satisfies_constructed hash d hi hstep q hq w hw hsym name,
   weldWit_satisfies_constructed hash d hi' hstep q hq w hw hsym name⟩

/-! ## §5 — ⚑ THE MEASURED PRICE OF THE WELD.

⚠ Every `#guard` below is COMPILED EVALUATION of a closed `Bool` — it proves NO `Prop`. The
`Prop`-level content is §2 (the welded binding and refusal) and §3.W (the witness).

⚠ Both descriptors measured here are SATISFIABLE: `weldDesc` by `weldWit_satisfies_constructed`,
the run-table baseline by `TinyAutomataSatisfiable.prodRunWit_satisfies`, the unwelded attested
object by `AttestedAutomatonEmit.attWit_satisfies`. Nothing without a witness is priced. -/

-- ⚑ THE WELDED SHAPE, GRADUATED (2026-11-06): 11 columns (3 + the 8 root lanes), 10 PIs (2 + the
-- 8 root lanes), 22 constraints (1 open + 1 continuity + 2 pi bindings + 8 lane windows + 8 lane
-- pins + 2 range lookups), THREE tables (map_ops, range_w15, range_w1), ZERO declared rows, ZERO
-- nonlinear multiplications, EMPTY `hashSites`/`ranges` carriers. Pre-graduation: 20 constraints,
-- 1 table, ranges `[⟨CURRENT, 15⟩, ⟨SYMBOL, 1⟩]` (refused by the v2 assembly).
#guard costOf weldInstance ==
  { traceWidth := 11, piCount := 10, constraints := 22, tables := 3
  , declaredRows := 0, forcedTraceRows := .unpinned, nonlinearMults := 0 }
#guard weldInstance.hashSites.isEmpty && weldInstance.ranges.isEmpty

-- … against the UNWELDED attested object (4 / 3 / 6). The weld costs +7 columns, +7 PIs, +14
-- constraints; it adds NO table, NO declared row and NO nonlinear multiplication.
#guard costOf attestedInstance ==
  { traceWidth := 4, piCount := 3, constraints := 6, tables := 1
  , declaredRows := 0, forcedTraceRows := .unpinned, nonlinearMults := 0 }

-- ⚑ WIRE BYTES, pinned: 2803 welded-and-graduated vs 1205 unwelded — 2.33× (+1598 bytes), CONSTANT in
-- `|w|` and in `|Q|·|Σ|` (ONE object for every automaton and every word length). The graduation
-- costs +192 bytes over the ungraduated weld's 2611: two table declarations and two lookups.
#guard (jsonBytes weldInstance, jsonBytes attestedInstance) == (2803, 1205)

-- ⚑ THE RESTATED CROSSOVER. The run-table descriptor at k = 4 grows ~10 bytes per symbol because it
-- SHIPS THE RUN. The UNWELDED attested object ties it at |w| = 60 and is smaller from 61 on; the
-- WELDED, GRADUATED object is still larger at |w| = 219 (2794 < 2803) and is strictly smaller from
-- |w| = 220 on (2804 > 2803). The weld moved the byte crossover 60 → 201; graduation moves it to 220.
#guard (List.map (fun n => jsonBytes (prodRunDesc 4 (wordN n))) [60, 61, 128, 200, 201, 219, 220])
  == [1205, 1214, 1884, 2604, 2614, 2794, 2804]

-- At the FIXED 8-symbol probe word the run-table descriptor is far smaller (669–685 vs 2803) — but
-- it is a DIFFERENT object per k AND per word, and it binds no automaton at any width.
#guard (List.map (fun k => jsonBytes (prodRunDesc k probeW)) [1, 2, 3, 4]) == [669, 669, 680, 685]

-- ⚑ MAIN-TRACE AREA (columns × trace rows): welded 11·|w| vs unwelded 4·|w| vs the unbound run
-- table's 3·|w|. The weld's whole main-trace price is the 7 completion-lane columns.
#guard (List.map (fun n => (WELD_WIDTH * n, 4 * n, 3 * n)) [8, 16, 32])
  == [(88, 32, 24), (176, 64, 48), (352, 128, 96)]

-- ⚑ THE AUX BILL — UNCHANGED IN ROWS. One map-ops row per opened trace row (5·|w| in the model)
-- and `MAP_TREE_DEPTH` chip permutations per opened row (16·|w|) both hold before and after the
-- weld: the weld buys WIDTH, not rows. What widens is the tuple — the model logs arity 5 while the
-- DEPLOYED map-log tuple is 19 felts `[root8, key, value, op, new_root8]`
-- (`circuit/src/descriptor_ir2.rs:2165-2185`), and the deployed node absorb is the arity-16 `node8`.
#guard (List.map (fun n => (5 * n, 19 * n, MAP_TREE_DEPTH * n)) [8, 16, 32])
  == [(40, 152, 128), (80, 304, 256), (160, 608, 512)]

-- ⚑ THE WELD, EXHIBITED ON THE WIRE. The emitted `MapOpSpec.root` lane list of the welded
-- descriptor is EIGHT DISTINCT COLUMNS (3..10); the unwelded object emits column 3 EIGHT TIMES
-- (`scalarRootGroup ROOT`). This is the byte-level difference the deployed chip reads.
#guard (((emitVmJson2 weldInstance).splitOn "\"root\":").getD 1 "").take 146
  == "[{\"t\":\"var\",\"v\":3},{\"t\":\"var\",\"v\":4},{\"t\":\"var\",\"v\":5},{\"t\":\"var\",\"v\":6},"
   ++ "{\"t\":\"var\",\"v\":7},{\"t\":\"var\",\"v\":8},{\"t\":\"var\",\"v\":9},{\"t\":\"var\",\"v\":10}]"
#guard (((emitVmJson2 attestedInstance).splitOn "\"root\":").getD 1 "").take 145
  == "[{\"t\":\"var\",\"v\":3},{\"t\":\"var\",\"v\":3},{\"t\":\"var\",\"v\":3},{\"t\":\"var\",\"v\":3},"
   ++ "{\"t\":\"var\",\"v\":3},{\"t\":\"var\",\"v\":3},{\"t\":\"var\",\"v\":3},{\"t\":\"var\",\"v\":3}]"

/-! ### The law, restated for the WELDED shape

At word length `|w|`, over descriptors that HAVE WITNESSES:

  * **run table, UNBOUND** (`TinyAutomataSatisfiable.prodRunWit_satisfies`) — 3 cols, 4 constraints,
    2 PIs, `|w|` declared rows, main area `3·|w|`, no aux chip rows, bytes GROWING ~10 per symbol.
  * **attested, BOUND AT ~31 BITS** (`AttestedAutomatonEmit.attWit_satisfies`) — 4 cols, 6
    constraints, 3 PIs, main area `4·|w|`, `5·|w|` map-op rows, `16·|w|` chip rows, 1190 bytes flat,
    byte crossover at `|w| = 60`. Its binding consumes `Poseidon2SpongeCR` at a BabyBear codomain,
    where it is FALSE (~2^15.5 birthday).
  * **attested, WELDED TO 8 FELTS, GRADUATED** (`weldWit_satisfies_constructed`) — 11 cols, 22
    constraints (20 + 2 range lookups), 10 PIs, main area `11·|w|`, the SAME `5·|w|` map-op rows and
    `16·|w|` chip rows, 2803 bytes flat (2611 before graduation), byte crossover at `|w| = 220`
    (201 before graduation). Its binding (`root8_binds_automaton_or_collides`) consumes NO
    crypto hypothesis: an equivocating prover must exhibit the collision a TOTAL extractor names at
    the deployed arity-16 chip, whose output is 8 BabyBear felts (~248 bits; the felt-width
    campaign's birthday arithmetic puts that at ~2^124, against ~2^15.5 for one felt — that is the
    campaign's arithmetic, cited, not a measurement made here).

⚠ HONEST, since it was asked directly: welding does NOT raise the aux bill. The map-op row count and
the Merkle-path chip-row count are identical before and after (`5·|w|` and `16·|w|`); no chip
permutation and no table is added. The price is paid entirely in the main trace and the wire — +7
columns (2.75× main area), +14 constraints, +7 public inputs, +1406 wire bytes (2.18×) — and in the
byte crossover moving 60 → 201. For a security boundary that is a cheap trade, and it is measured.
GRADUATION (2026-11-06) adds 2 lookups per row, 2 range-table declarations and +192 wire bytes (the
crossover moves 201 → 220); in the Lean model it adds no main column, and the Rust assembly realizes
each range lookup with its own byte-limb aux columns (measured in `circuit/tests/weld8_served.rs`).

⚠ AND, equally honest: those numbers price the WIRE weld. The DENOTATION weld is not in them,
because it is not in this IR (§3a) — `MapOp.holdsAt` reads lane 0. Whatever the eventual
`opensToMerkle8` denotation costs the deployed chip (the arity-16 `node8` absorb is materially more
expensive per permutation than an arity-2 one) is NOT counted above and is NOT claimed here. -/

/-! ## §6 — axiom tripwires. -/

#assert_all_clean [autoHeapW_length, autoHeapW_sorted, autoHeapW_get, autoRoot8_commits,
  CommitsAutomaton8By.opens, autoRoot8_opens,
  root8_binds_automaton_or_collides, weld_collision_disjunct_refutable, forged_edge_refused_8,
  weld_memOps, weld_memLog, weld_mapOps, weld_mapLog, weldLane_classify,
  rowsW_length, rowsW_shape, rowsW_chain, rowsW_root, rowsW_head_current, rowsW_last_next,
  weldWit_satisfies, weldWit_satisfies_constructed, weld_completion_lanes_free,
  weldCurRange_mem, weldSymRange_mem, weldTail_classify, weldTf_faithful, weldWit_rangeLookups,
  weldWit_rowConstraints_nonmap, weld_ranges, weld_lookups_bound, weld_range_refuses_out_of_domain]

end Dregg2.Circuit.Emit.AttestedAutomatonWeld8
