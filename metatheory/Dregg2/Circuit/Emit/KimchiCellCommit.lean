/-
# Dregg2.Circuit.Emit.KimchiCellCommit — the GROUP-4 COMMITMENT BINDING for route B

## ⚑ SAY THE SUBSTRATE OUT LOUD

This is **Lean-authored AIR**. Nothing below is hand-written: the four `hash_4_to_1` sub-circuits
are `KimchiPoseidon2.permGen` — a `def`-generator folded over the imported round constants, 141
S-boxes and not one of them spelled out — and the WIRING between them is `def`-generated from the
DEPLOYED site list (`EffectVmEmitIncrementNonce.incNonceHashSites`, which is
`EffectVmEmitTransfer.transferHashSites`) rather than restated. The o1js consumer transcribes the
emitted instruction stream and the Lean-computed witness; it authors no constraint and holds no
dregg semantics.

## THE GAP THIS CLOSES, in the words of the lane that named it

> The commitment binding is ABSENT. The 4 GROUP-4 hash sites are not emitted, so the circuit
> relates two bare 13-tuples and **does not prove they are the pre-image of any commitment** —
> i.e. that they are a dregg cell.

`KimchiEffectIncNonce` proves *these two 13-tuples stand in the `incrementNonceA` relation*. That
is a statement about arithmetic. This file adds the sentence that makes it a statement about a
**cell**: the after-state tuple is the pre-image, under the deployed `hash_4_to_1` tree, of the felt
sitting in the `state_commit` column — the same felt `boundaryLastPins` publishes as `NEW_COMMIT`
and `cell_state.rs::compute_commitment` computes.

## ⚑ AND THE SENTENCE IT STILL DOES NOT ADD

Route B is now a **cell-transition checker**. It is still **not a membership checker.** Even fully
bound, B says "this is a valid transition of a real, well-formed cell". It says **nothing whatever
about whether dregg's chain contains that cell or that transition.** A well-formed transition of a
cell that never existed satisfies every row below — invent a 13-tuple, hash it honestly, present
the pair. Membership is route A's job: A consumes a dregg proof and therefore inherits dregg's
accumulator and commitment structure (and its undischarged FRI/STARK floor). That asymmetry is the
honest core of route B and **nothing here narrows it.**

## The shape: TWO ARROWS, ONE `def`

  * **`cellCommitOf hash a`** (§2) is the one `def` — literally the right-hand side of the deployed
    forcing lemma `EffectVmEmitTransfer.transferHash_binds`: an `H4`-of-`H4` over the after-state
    block and the record-digest residue.
  * **ARROW TWO** — `babybear_forces_cellCommit`: the deployed BabyBear descriptor's hash layer
    (`siteHoldsAll hash env incNonceHashSites`) forces `cellCommitOf`. This is
    `transferHash_binds`, restated at the increment-nonce site list; nothing new is proved.
  * **ARROW ONE** — `kimchi_forces_cellCommit`: the EMITTED Kimchi rows, under the ONE named digest
    carrier, force the SAME `def`, at the same column.

⚑ **The asymmetry runs the same way it does for the arithmetic — the BabyBear side is again the
weaker one.** There, `siteHoldsAll` is an ASSUMPTION about the deployed TRACE: the descriptor
carries `VmHashSite`s whose denotation is "the digest column holds the hash of these inputs", and
no gate in `incrementNonceVmDescriptor.constraints` establishes it — the Poseidon2 chip is outside
the constraint list. Here `siteHoldsAll` is DERIVED (`commit_rows_force_siteHoldsAll`): the emitted
circuit CONTAINS the permutation, and what stays assumed is strictly narrower — `DigestCarrier`,
that a satisfying assignment of the emitted permutation sub-circuit puts `hash` of its input lanes
in its output lane. So the Kimchi emission again discharges more, and the residual is named in §9
rather than folded into a hypothesis that looks like a definition.

## ⚑ THE ONE UNDISCHARGED LEG, named precisely

`DigestCarrier` is `KimchiPoseidon2`'s own §5 remainder, quoted:

> `permGen_forces` — the composition all the way to "a satisfying assignment forces the output
> lanes to be `perm` of the input lanes" — is NOT proved here and is the first item of the named
> remainder.

It is not proved here either, and §9 says exactly what blocks it — it is not merely unproved: at
the emitted object two of `bbRange64`'s columns are unpinned and the reduction's remainder is
checked to 64 bits behind a `2^31` bound claim, so the statement needs those repaired before it
could even be true. **Nothing below assumes it away**; it is a hypothesis of every theorem that
needs it, and §6 shows it HOLDS at the honest cell so it demands nothing an honest instance does
not supply.

## Anti-vacuity, at birth (§6)

Over the ACTUAL emitted rows, evaluated: (a) every one of the 10,570 rows is satisfied by the
honest cell's witness — so nothing here is true for want of a satisfying assignment; (b) each site's
digest lane carries exactly `hash4to1Real` of the columns the DEPLOYED site absorbs, i.e.
`DigestCarrier hash4to1Real` HOLDS at the honest instance; (c) the last lane is exactly
`cellCommitOf hash4to1Real` of the honest cell — the emitted circuit computes the deployed cell
commitment, `841295468`, and the reference value comes from `hash4to1Real`, which the circuit never
sees. `tamper_non_preimage_refused` is the GENERAL refutation: **no assignment whatever** satisfies
the emitted circuit while carrying a `state_commit` that is not `cellCommitOf hash` of its own
after-state.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; `#guard`/`rfl`/`decide` only, no
`sorry`/`native_decide`. NEW file. Imports read-only.
-/
import Dregg2.Circuit.Emit.KimchiEffectIncNonce
import Dregg2.Circuit.Emit.KimchiPoseidon2
import Dregg2.Circuit.Emit.CommitmentTreeAppendEmit

namespace Dregg2.Circuit.Emit.KimchiCellCommit

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.KimchiTarget
open Dregg2.Circuit.Emit.KimchiLower
open Dregg2.Circuit.Emit.KimchiPoseidon2
open Dregg2.Circuit.Emit.KimchiEffectIncNonce
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferHash_binds)
open Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce
open Dregg2.Circuit.Emit.CommitmentTreeAppendEmit (hash4to1Real)

set_option autoImplicit false
set_option maxRecDepth 40000

/-! ## §1 — THE WIRING, `def`-generated from the DEPLOYED site list.

`incNonceHashSites` is what the running descriptor carries. Restating its columns here would make
this file a second opinion about the deployed layout, so the column lists below are COMPUTED from
it: `inColsGo` is `HashInput.resolve` lifted from VALUES to COLUMN INDICES, with a `.digest k` input
resolving to the column the `k`-th site's digest was pinned into. That substitution is exactly what
makes the emitted circuit read the same values `siteDigestsAcc` accumulates. -/

/-- Resolve a site's inputs to COLUMN indices, given the digest columns of the earlier sites. -/
def inColsGo : List Nat → List VmHashSite → List (List Nat)
  | _, [] => []
  | acc, s :: ss =>
      (s.inputs.map (fun i => match i with
        | .col c => c
        | .digest k => acc.getD k 0
        | .zero => 0)) :: inColsGo (acc ++ [s.digestCol]) ss

/-- **The absorbed COLUMNS of each deployed site, in the deployed order.** -/
def siteInCols : List (List Nat) := inColsGo [] incNonceHashSites

/-- **The digest COLUMN of each deployed site.** Site 3's is `state_after.state_commit` itself. -/
def siteDigestCols : List Nat := incNonceHashSites.map (fun s => s.digestCol)

/-- The absorbed columns of site `i`. -/
def inCols (i : Nat) : List Nat := siteInCols.getD i []

/-- The digest column of site `i`. -/
def digCol (i : Nat) : Nat := siteDigestCols.getD i 0

/-! The wiring, pinned. `saCol off = 76 + off`, `auxCol i = 90 + i`: sites 0/1/2 absorb the twelve
committed after-state cells, site 3 absorbs their three digest columns and the record-digest residue
(`auxCol 96 = 186`, audit P0-2) and lands on `saCol state.STATE_COMMIT = 88`. -/
#guard siteInCols == [[76, 77, 78, 79], [80, 81, 82, 83], [84, 85, 86, 87], [98, 99, 100, 186]]
#guard siteDigestCols == [98, 99, 100, 88]
#guard incNonceHashSites.length == 4
#guard incNonceHashSites.all (fun s => s.arity == 4)
-- No deployed site absorbs a literal `.zero`, so `inColsGo`'s zero case (which would resolve to
-- column 0) never fires: the legacy `H4(…, 0)` form is gone and the residue column is real.
#guard incNonceHashSites.all (fun s => s.inputs.all (fun i => i != HashInput.zero))
#guard digCol 3 == saCol state.STATE_COMMIT
#guard siteInCols.length == 4

/-! ## §2 — THE SHARED `def`, and ARROW TWO. -/

/-- **THE ONE `def`** — the deployed GROUP-4 cell commitment of an assignment's after-state block.
`hash` is abstract, exactly as the deployed hash layer keeps it. This is the right-hand side of
`EffectVmEmitTransfer.transferHash_binds` verbatim. -/
def cellCommitOf (hash : List ℤ → ℤ) (a : Nat → ℤ) : ℤ :=
  hash [ hash [ a (saCol state.BALANCE_LO), a (saCol state.BALANCE_HI)
              , a (saCol state.NONCE), a (saCol (state.FIELD_BASE + 0)) ]
       , hash [ a (saCol (state.FIELD_BASE + 1)), a (saCol (state.FIELD_BASE + 2))
              , a (saCol (state.FIELD_BASE + 3)), a (saCol (state.FIELD_BASE + 4)) ]
       , hash [ a (saCol (state.FIELD_BASE + 5)), a (saCol (state.FIELD_BASE + 6))
              , a (saCol (state.FIELD_BASE + 7)), a (saCol state.CAP_ROOT) ]
       , a (auxCol aux_off.STATE_RECORD_DIGEST) ]

/-- **ARROW TWO — the deployed BabyBear descriptor's hash layer forces `cellCommitOf`.**

⚑ Note what its hypothesis IS: `siteHoldsAll` asserts, of the DEPLOYED trace, that the digest
columns already carry the genuine hash. No gate of the deployed constraint list establishes that —
it is the hash layer, assumed. §4 DERIVES it on the Kimchi side. -/
theorem babybear_forces_cellCommit (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env incNonceHashSites) :
    env.loc (saCol state.STATE_COMMIT) = cellCommitOf hash env.loc :=
  transferHash_binds hash env h

/-! ## §3 — THE EMISSION.

One `hash_4_to_1` site is: range-check the four absorbed columns as BabyBear lanes, seed the
sixteen-lane Poseidon2 state `[x₀,x₁,x₂,x₃, 4, 0…0]` (`circuit/src/poseidon2.rs:349-362` — the
arity domain tag at position 4, capacity zero), run `KimchiPoseidon2.permGen`, and reduce output
lane 0 to its canonical representative. The digest is lane 0 of the permuted state, canonically —
which is precisely what the Rust returns. -/

/-- The first fresh variable of the COMMITMENT emission: past the EffectVM row AND past the
arithmetic emission's own 45 intermediates (`NV0 + 45 = 233`), so no commitment intermediate can
alias an arithmetic one. -/
def NVC : Nat := NV0 + 45

#guard NVC == 233

/-- Seed a `Ctx` whose variables `[0, NVC)` already hold the row and the arithmetic emission's
intermediates. The commitment emission allocates from `NVC` up. -/
def ctxOf (a : Assignment) : Ctx := ⟨((List.range NVC).map a).toArray, #[]⟩

/-- **ONE DEPLOYED `hash_4_to_1` SITE, GENERATED.** `xs` are the absorbed COLUMNS. -/
def h4Gen (c : Ctx) (xs : List Nat) : BB × Ctx :=
  let lanes : List BB := xs.map (fun v => ⟨v, 2 ^ 31⟩)
  let c := lanes.foldl (fun c l => bbRange64 c l) c
  let (tag, c) := bbConst c 4
  let (zs, c) := (List.range 11).foldl
      (fun (st : List BB × Ctx) _ => let (z, c') := bbConst st.2 0; (st.1 ++ [z], c')) ([], c)
  let (out, c) := permGen c (lanes ++ tag :: zs)
  bbReduce c (out.getD 0 ⟨0, 0⟩)

/-! ### §3a — the honest cell, and its commitment.

`goodIncNonceRow` (the row `KimchiEffectIncNonce` proved the arithmetic accepts: bal 100→100, nonce
5→6) carries ZERO in all four digest columns, because the arithmetic emission never touched them.
The honest CELL row fills them with the genuine `hash_4_to_1` chain — computed by the deployed
`hash4to1Real`, which the circuit never sees, so §6's agreement between the two is a check and not
a tautology. -/

def honestD0 : ℤ := hash4to1Real ((inCols 0).map satAssign)
def honestD1 : ℤ := hash4to1Real ((inCols 1).map satAssign)
def honestD2 : ℤ := hash4to1Real ((inCols 2).map satAssign)
def honestD3 : ℤ :=
  hash4to1Real [honestD0, honestD1, honestD2, satAssign (auxCol aux_off.STATE_RECORD_DIGEST)]

/-- **The honest CELL assignment** — `satAssign` with the four GROUP-4 digest columns filled. None
of `state.STATE_COMMIT` or the three `STATE_INTER` aux columns is a frozen offset, so this still
satisfies every arithmetic row. -/
def cellAssign : Assignment := fun v =>
  if v = auxCol aux_off.STATE_INTER1 then honestD0
  else if v = auxCol aux_off.STATE_INTER2 then honestD1
  else if v = auxCol aux_off.STATE_INTER3 then honestD2
  else if v = saCol state.STATE_COMMIT then honestD3
  else satAssign v

/-- The honest cell's commitment IS the deployed `cellCommitOf` of its own after-state. ⚠ NOT a
`#guard` and NOT proved by `rfl` here: either forces four Poseidon2 permutations through `whnf` in
the elaborator. `CheckKimchiCellCommit` checks the STRONGER statement — that the emitted circuit's
own digest lane equals BOTH `honestD3` and `cellCommitOf hash4to1Real cellAssign` (measured:
`841295468`) — through the compiler. -/
def honestD3_is_cellCommit : Bool := decide (honestD3 = cellCommitOf hash4to1Real cellAssign)

/-! ### §3b — the emitted object. -/

/-- Fold the four sites over one `Ctx`, collecting the digest LANE variable of each. -/
def commitBuild : List Nat × Ctx :=
  siteInCols.foldl
    (fun (st : List Nat × Ctx) xs => let (d, c) := h4Gen st.2 xs; (st.1 ++ [d.v], c))
    ([], ctxOf cellAssign)

/-- The digest LANE variables — the canonical reduction of each permutation's lane 0. -/
def digestLaneVars : List Nat := commitBuild.1

/-- The digest lane variable of site `i`. -/
def digLane (i : Nat) : Nat := digestLaneVars.getD i 0

/-! ⚑ **There is deliberately no `digestLaneVars.length = 4` THEOREM here.** Proving it needs
`(l.foldl step st).1`, and `step` destructures `h4Gen`'s pair — so projecting `.1` forces `whnf`
through four Poseidon2 permutations and the KERNEL reports "deep recursion detected". Measured, not
guessed. The fact is pinned instead by `costPinsHold`, which fixes `digestLaneVars` to the four
literal indices the emission produces and is checked through the compiler. Nothing rests on the
length: `pinGens` is a four-element literal over `digLane 0..3`, and a short list would only make
`digLane i` read `0` — a silly circuit the pin check catches, never an unsound one. -/

theorem siteInCols_length : siteInCols.length = 4 := rfl

/-- The compiler state after the four sites: the witness and the instruction stream. -/
def siteCtx : Ctx := commitBuild.2

/-- The four permutation sub-circuits, as an instruction stream. -/
def siteOps : List KOp := siteCtx.ops.toList

/-- The four permutation sub-circuits, as Kimchi rows. -/
def siteRows : List KRow := renderOps siteOps

/-- **THE PINS** — one sub-gate per site, forcing the site's DIGEST COLUMN to its digest lane. This
is the join between the permutation sub-circuits and the deployed trace layout, and it is what makes
site 3's absorption read sites 0/1/2's digests through the very columns `VmHashSite.digestCol`
names. -/
def pinGens : List Gen1 :=
  [ Gen1.scale (digLane 0) (digCol 0) 1, Gen1.scale (digLane 1) (digCol 1) 1
  , Gen1.scale (digLane 2) (digCol 2) 1, Gen1.scale (digLane 3) (digCol 3) 1 ]

/-- The pins, as Kimchi rows: four sub-gates, two rows. -/
def pinRows : List KRow := packGen pinGens

/-- **THE EMITTED GROUP-4 COMMITMENT CIRCUIT.** -/
def commitRows : List KRow := siteRows ++ pinRows

/-- **THE WHOLE ROUTE-B CIRCUIT** — the arithmetic emission and the commitment binding. -/
def routeBRows : List KRow := incNonceKimchiRows ++ commitRows

/-- Every emitted row carries a MODELLED gate, so nothing below is discharged by `KimchiTarget`'s
fail-closed `False` on an unmodelled gate. -/
theorem commitRows_all_modelled : ∀ r ∈ commitRows, r.gate.modelled = true := by
  intro r hr
  rcases List.mem_append.1 hr with h | h
  · exact renderOps_all_modelled _ r h
  · exact packGen_all_modelled _ r h

theorem routeBRows_all_modelled : ∀ r ∈ routeBRows, r.gate.modelled = true := by
  intro r hr
  rcases List.mem_append.1 hr with h | h
  · exact incNonceRows_all_modelled r h
  · exact commitRows_all_modelled r h

/-! ## §4 — THE FORCING, in the two-arrows shape. -/

/-- **⚑ THE ONE UNDISCHARGED LEG.** `DigestCarrier hash A` says: at each of the four emitted
permutation sub-circuits, the assignment `A` puts `hash` of the absorbed COLUMNS into that site's
digest LANE.

This is `KimchiPoseidon2`'s first named remainder (`permGen_forces`) specialised to the four sites.
It is the SAME object the BabyBear side folds into `siteHoldsAll` — with one difference in this
route's favour: there the hash layer is assumed of the deployed TRACE, here it is assumed of a
sub-circuit that is actually EMITTED and whose completeness is checked row by row in §6. -/
def DigestCarrier (hash : List ℤ → ℤ) (A : Nat → ℤ) : Prop :=
  ∀ i, i < 4 → A (digLane i) = hash ((inCols i).map A)

/-- The pins force each digest COLUMN to its digest LANE. -/
theorem pins_force (A : Nat → ℤ) (hr : rowsHold A commitRows) :
    ∀ i, i < 4 → A (digCol i) = A (digLane i) := by
  have hp : rowsHold A pinRows := (rowsHold_append hr).2
  have hg : gensHold A pinGens := (packGen_holds_iff A pinGens).mp hp
  intro i hi
  -- ⚑ the membership is proved CONSTRUCTIVELY, not by `simp [pinGens]`: simp normalises closed
  -- `Nat` terms, and `digLane 0` is closed — it would evaluate four Poseidon2 permutations to
  -- learn a variable index it never needed.
  have hmem : Gen1.scale (digLane i) (digCol i) 1 ∈ pinGens := by
    show _ ∈ [Gen1.scale (digLane 0) (digCol 0) 1, Gen1.scale (digLane 1) (digCol 1) 1,
              Gen1.scale (digLane 2) (digCol 2) 1, Gen1.scale (digLane 3) (digCol 3) 1]
    interval_cases i
    · exact List.Mem.head _
    · exact List.Mem.tail _ (List.Mem.head _)
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have h := Gen1.scale_forces A (digLane i) (digCol i) 1 (hg _ hmem)
  rw [h, Int.cast_one, one_mul]

/-- **THE WIRING THEOREM — the emitted rows DERIVE the deployed hash layer.**

Under the digest carrier, an assignment satisfying the emitted commitment rows satisfies
`siteHoldsAll hash env incNonceHashSites`: the very hypothesis `transferHash_binds` takes as GIVEN
on the BabyBear side. The content is the WIRING — that site `i` absorbs the deployed columns in the
deployed order, and that site 3 reads sites 0/1/2's digests through the columns the pins forced. -/
theorem commit_rows_force_siteHoldsAll (hash : List ℤ → ℤ) (env : VmRowEnv)
    (hcar : DigestCarrier hash env.loc) (hr : rowsHold env.loc commitRows) :
    siteHoldsAll hash env incNonceHashSites := by
  have hp := pins_force env.loc hr
  have e0 : env.loc (auxCol aux_off.STATE_INTER1)
      = hash [ env.loc (saCol state.BALANCE_LO), env.loc (saCol state.BALANCE_HI)
             , env.loc (saCol state.NONCE), env.loc (saCol (state.FIELD_BASE + 0)) ] :=
    (hp 0 (by norm_num)).trans (hcar 0 (by norm_num))
  have e1 : env.loc (auxCol aux_off.STATE_INTER2)
      = hash [ env.loc (saCol (state.FIELD_BASE + 1)), env.loc (saCol (state.FIELD_BASE + 2))
             , env.loc (saCol (state.FIELD_BASE + 3)), env.loc (saCol (state.FIELD_BASE + 4)) ] :=
    (hp 1 (by norm_num)).trans (hcar 1 (by norm_num))
  have e2 : env.loc (auxCol aux_off.STATE_INTER3)
      = hash [ env.loc (saCol (state.FIELD_BASE + 5)), env.loc (saCol (state.FIELD_BASE + 6))
             , env.loc (saCol (state.FIELD_BASE + 7)), env.loc (saCol state.CAP_ROOT) ] :=
    (hp 2 (by norm_num)).trans (hcar 2 (by norm_num))
  have e3 : env.loc (saCol state.STATE_COMMIT)
      = hash [ env.loc (auxCol aux_off.STATE_INTER1), env.loc (auxCol aux_off.STATE_INTER2)
             , env.loc (auxCol aux_off.STATE_INTER3)
             , env.loc (auxCol aux_off.STATE_RECORD_DIGEST) ] :=
    (hp 3 (by norm_num)).trans (hcar 3 (by norm_num))
  refine ⟨e0, e1, e2, ?_, trivial⟩
  show env.loc (saCol state.STATE_COMMIT) = cellCommitOf hash env.loc
  simp only [cellCommitOf]
  rw [← e0, ← e1, ← e2]
  exact e3

/-- **ARROW ONE — the EMITTED Kimchi rows force `cellCommitOf`.** -/
theorem kimchi_forces_cellCommit (hash : List ℤ → ℤ) (env : VmRowEnv)
    (hcar : DigestCarrier hash env.loc) (hr : rowsHold env.loc commitRows) :
    env.loc (saCol state.STATE_COMMIT) = cellCommitOf hash env.loc :=
  babybear_forces_cellCommit hash env (commit_rows_force_siteHoldsAll hash env hcar hr)

/-- **THE DELIVERABLE — TWO EMISSIONS, ONE COMMITMENT `def`.**

The emitted Kimchi commitment circuit and the deployed BabyBear hash layer both force
`cellCommitOf hash env.loc` — the same Lean `def`, at the same column, over the same after-state.
The commitment binding is therefore not a third implementation; it is the deployed one, emitted. -/
theorem two_emissions_one_commit (hash : List ℤ → ℤ) (env : VmRowEnv) :
    (DigestCarrier hash env.loc → rowsHold env.loc commitRows →
        env.loc (saCol state.STATE_COMMIT) = cellCommitOf hash env.loc)
    ∧ (siteHoldsAll hash env incNonceHashSites →
        env.loc (saCol state.STATE_COMMIT) = cellCommitOf hash env.loc) :=
  ⟨fun hcar hr => kimchi_forces_cellCommit hash env hcar hr,
   fun h => babybear_forces_cellCommit hash env h⟩

/-! ## §5 — THE FULL ROUTE-B CLAIM: an `incrementNonceA` transition OF A CELL. -/

/-- **⚑ WHAT A VERIFIED ROUTE-B PROOF NOW SAYS.**

An assignment satisfying the WHOLE emitted circuit (arithmetic ++ commitment) forces BOTH

  * `CellIncNonceSpec pre post` — the economic block frozen and the nonce ticked, the deployed
    per-effect spec `EffectVmEmitIncrementNonce` names and `incNonceVm_faithful` reaches on the
    BabyBear side; AND
  * `state_commit = cellCommitOf hash (after-state)` — the after-state 13-tuple is the pre-image,
    under the deployed GROUP-4 tree, of the published commitment felt.

⚠ **It still says nothing about membership.** `pre`/`post` are decoded from the row the prover
supplied. Nothing here ties `state_commit` to any root dregg's chain ever published — the
`piBinding` that would (`boundaryLastPins`: `saCol STATE_COMMIT = pi.NEW_COMMIT`) is NOT emitted,
and even it would only name a public input the same prover chose. A well-formed transition of a cell
that never existed satisfies every row. -/
theorem routeB_forces_cell_transition (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : EffectVmEmitTransferSound.CellState)
    (hnoop : env.loc sel.NOOP = 0) (henc : RowEncodesIncNonce env pre post)
    (hcar : DigestCarrier hash env.loc) (hr : rowsHold env.loc routeBRows) :
    CellIncNonceSpec pre post
    ∧ env.loc (saCol state.STATE_COMMIT) = cellCommitOf hash env.loc :=
  ⟨kimchi_forces_cellSpec env pre post hnoop henc (rowsHold_append hr).1,
   kimchi_forces_cellCommit hash env hcar (rowsHold_append hr).2⟩

/-! ## §6 — ANTI-VACUITY: satisfiable at birth, digest-exact, and refutable in general.

⚑ **WHERE THESE CHECKS RUN, and why it is not `#guard`.** The emitted object is 15,600
instructions, 76,489 witness values and 10,570 rows. `#guard` evaluates at ELABORATION time through
`whnf`, which builds the whole `List KRow` as an expression: measured, that took this module past
20 GB and was still climbing. So the computational checks live in **`CheckKimchiCellCommit.lean`**,
a `lake env lean --run` executable that evaluates the SAME `def`s through the compiler and **exits
nonzero** on any failure — and `EmitKimchiCellCommit` runs it before it will write an artifact, so
the JSON the o1js side consumes cannot be produced from an emission that fails one. The checks are
the `def`s below; the gate is `scripts/check-kimchi-cellcommit.sh`. This is a relocation of the
instrument, not a weakening of it: it can still go red, and it is the same predicate.

The cheap facts — the ones that do not touch the permutation — stay as `#guard`s here. -/

/-- Evaluate one emitted row at an ℤ-valued assignment — the `Bool` mirror of `KRow.holds`, so a
satisfying witness can be exhibited over the emitted ROWS rather than over the instruction stream. -/
def rowAcceptB (a : Nat → ℤ) (r : KRow) : Bool :=
  match r.gate with
  | .zero => true
  | .generic => decide (genericBody1 a r = 0) && decide (genericBody2 a r = 0)
  | .rangeCheck0 => (rc0Bodies a r).all (fun b => decide (b = 0)) && decide (r.coeffs.getD 0 0 = 0)
  | _ => false

/-- `rowAcceptB` is SOUND for `KRow.holds`: a `true` is a proof the row holds. So the `#guard`s
below are statements about `rowsHold`, not about a lookalike predicate. -/
theorem rowAcceptB_sound (a : Nat → ℤ) (r : KRow) (h : rowAcceptB a r = true) : r.holds a := by
  unfold rowAcceptB at h
  unfold KRow.holds
  cases hg : r.gate <;> rw [hg] at h <;>
    first
      | trivial
      | (simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
         exact ⟨fun b hb => h.1 b hb, h.2⟩)
      | (simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h)

theorem rowsAcceptB_sound (a : Nat → ℤ) (rs : List KRow) (h : rs.all (rowAcceptB a) = true) :
    rowsHold a rs := by
  simp only [List.all_eq_true] at h
  exact fun r hr => rowAcceptB_sound a r (h r hr)

/-- The rows the honest cell's witness FAILS, kept legible: a `#guard` on a conjunction tells you
nothing about WHICH row went red, and this generator's ancestor has already been wrong once in a way
only the row-level check caught. -/
def badRowCount : Nat := (commitRows.filter (fun r => ! rowAcceptB siteCtx.asg r)).length

def firstBadRow : Option Nat :=
  (commitRows.zipIdx.find? (fun q => ! rowAcceptB siteCtx.asg q.1)).map (fun q => q.2)

/-- ⚑ **SATISFIABLE AT BIRTH, over the emitted ROWS.** The honest cell — `goodIncNonceRow` with its
genuine GROUP-4 digests — satisfies EVERY row of the emitted commitment circuit. So
`commit_rows_force_siteHoldsAll`, `routeB_forces_cell_transition` and the tamper theorems are not
true for want of a satisfying assignment. `rowAcceptB_sound` is what makes this a statement about
`rowsHold` rather than about a lookalike predicate. MEASURED: `badRowCount = 0`. -/
def rowsAcceptHonestCell : Bool := commitRows.all (rowAcceptB siteCtx.asg)

/-- ⚑ **THE DIGEST IS THE DEPLOYED ONE — `DigestCarrier` HOLDS at the honest cell.** Each emitted
site's digest lane carries exactly `hash4to1Real` of the columns the DEPLOYED site absorbs. The
carrier therefore demands nothing an honest cell does not supply; it is an obligation the emitted
circuit MEETS here, not a hypothesis chosen to make a theorem close. MEASURED: `true`. -/
def digestCarrierHoldsB : Bool :=
  (List.range 4).all (fun i =>
    decide (siteCtx.asg (digLane i) = hash4to1Real ((inCols i).map siteCtx.asg)))

/-- ⚑ **THE EMITTED CIRCUIT COMPUTES THE DEPLOYED CELL COMMITMENT.** The last site's digest lane is
`cellCommitOf hash4to1Real` of the honest cell's after-state — the felt
`cell_state.rs::compute_commitment` produces and `boundaryLastPins` publishes as `NEW_COMMIT`. The
reference side comes from `hash4to1Real`, whose own KAT is `#guard`ed bit-exact against the deployed
`hash_4_to_1` in `CommitmentTreeAppendEmit`; the circuit never sees it. MEASURED: both are
`841295468`. -/
def commitLaneIsCellCommit : Bool :=
  decide (siteCtx.get (digLane 3) = cellCommitOf hash4to1Real cellAssign)
    && decide (siteCtx.get (digLane 3) = honestD3)
    && decide (siteCtx.get (digCol 3) = siteCtx.get (digLane 3))

/-- Every value the COMMITMENT emission witnesses is a non-negative integer representative strictly
below the Pasta modulus. ⚠ This is a check on the WITNESS at one cell, not the bound argument:
`KimchiPoseidon2.boundsSafe` is the statement about the tracked BOUNDS, and it is a `#guard` there
too. The arithmetic emission's own intermediates (`[0, NVC)`) are deliberately NOT covered —
`satAssign 194 = -1` by design, the nonce-tick head's constant, which over Pallas is `p − 1`. -/
def commitValsInPasta : Bool :=
  (siteCtx.vals.toList.drop NVC).all (fun v => decide (0 ≤ v) && decide (v < pastaN))

/-- **⚑ REFUTABLE IN GENERAL — a valid transition that is NOT the pre-image of its commitment.**

NO assignment whatever satisfies the emitted circuit while carrying a `state_commit` felt that is
not `cellCommitOf hash` of its own after-state block. This is the theorem that separates "checks a
transition's arithmetic" from "checks a cell": the arithmetic rows say nothing about column 88, and
before this file ANY felt at all could sit there and every row still held. -/
theorem tamper_non_preimage_refused (hash : List ℤ → ℤ) (A : Nat → ℤ)
    (hcar : DigestCarrier hash A) (hwrong : A (saCol state.STATE_COMMIT) ≠ cellCommitOf hash A) :
    ¬ rowsHold A commitRows := by
  intro hr
  refine hwrong ?_
  have hp := pins_force A hr
  have e0 : A (auxCol aux_off.STATE_INTER1)
      = hash [ A (saCol state.BALANCE_LO), A (saCol state.BALANCE_HI)
             , A (saCol state.NONCE), A (saCol (state.FIELD_BASE + 0)) ] :=
    (hp 0 (by norm_num)).trans (hcar 0 (by norm_num))
  have e1 : A (auxCol aux_off.STATE_INTER2)
      = hash [ A (saCol (state.FIELD_BASE + 1)), A (saCol (state.FIELD_BASE + 2))
             , A (saCol (state.FIELD_BASE + 3)), A (saCol (state.FIELD_BASE + 4)) ] :=
    (hp 1 (by norm_num)).trans (hcar 1 (by norm_num))
  have e2 : A (auxCol aux_off.STATE_INTER3)
      = hash [ A (saCol (state.FIELD_BASE + 5)), A (saCol (state.FIELD_BASE + 6))
             , A (saCol (state.FIELD_BASE + 7)), A (saCol state.CAP_ROOT) ] :=
    (hp 2 (by norm_num)).trans (hcar 2 (by norm_num))
  have e3 : A (saCol state.STATE_COMMIT)
      = hash [ A (auxCol aux_off.STATE_INTER1), A (auxCol aux_off.STATE_INTER2)
             , A (auxCol aux_off.STATE_INTER3), A (auxCol aux_off.STATE_RECORD_DIGEST) ] :=
    (hp 3 (by norm_num)).trans (hcar 3 (by norm_num))
  simp only [cellCommitOf]
  rw [← e0, ← e1, ← e2]
  exact e3

/-- **REFUTABLE — the SUBSTITUTED commitment**, with NO carrier hypothesis at all. A row that
carries some OTHER cell's commitment in `state_commit` while its own permutation lane computed
something else is UNSAT: this is the pin's own content, and it is the tamper the o1js run exercises
against a real `prove()`. -/
theorem tamper_substituted_commit_refused (A : Nat → ℤ)
    (hwrong : A (saCol state.STATE_COMMIT) ≠ A (digLane 3)) : ¬ rowsHold A commitRows := by
  intro hr
  exact hwrong (pins_force A hr 3 (by norm_num))

/-! ## §7 — THE COST, MEASURED, and the RE-PRICE.

`docs/MINA-DREGG-SEMANTICS-NATIVE.md` §3 PROJECTED route B at ≈ 1.05 × 10⁴ rows per effect row,
with **98.8% of it being exactly these four permutations** (10,402 of ~10,534, at the measured
o1js marginal 2,600.5 rows per Poseidon2-w16 permutation × 4). Everything below is the EMISSION,
so it is the projection MEASURED rather than repeated — and the o1js side is measured against it
in the same session (`bridge/mina-zkapp/scripts/cellcommit-native.ts`). -/

/-- Emitted rows: the four permutation sub-circuits. -/
def siteRowCount : Nat := siteRows.length

/-- Emitted rows: the whole GROUP-4 commitment binding (sites + the two pin rows). -/
def commitRowCount : Nat := commitRows.length

/-- Emitted rows: the WHOLE route-B circuit — arithmetic and commitment. -/
def routeBRowCount : Nat := routeBRows.length

/-- The emitted gate mix of the commitment binding. -/
def commitHistogram : List (KGateType × Nat) := gateHistogram commitRows

/-- Effect rows that fit in ONE Pickles step at the emitted price. -/
def effectRowsPerPickleStep : Nat := PICKLES_MAX_ROWS / routeBRowCount

/-- ⚑ The emitted cost, PINNED. Moving any of these is a deliberate act, and
`CheckKimchiCellCommit` fails on any drift. -/
def costPinsHold : Bool :=
  (siteRowCount == 10568) && (commitRowCount == 10570) && (routeBRowCount == 10600)
    && (siteOps.length == 15600) && (siteCtx.vals.size == 76489)
    && (effectRowsPerPickleStep == 6)
    && (digestLaneVars == [19282, 38346, 57410, 76474])
    && (commitHistogram.filter (fun x => x.2 != 0)
          == [(KGateType.generic, 6154), (KGateType.rangeCheck0, 4416)])

/-! ⚑ The emitted cost, MEASURED. Moving any of these is a deliberate act and `costPinsHold`
fails on drift.

| | rows | |
|---|---:|---|
| four `hash_4_to_1` sites | 10,568 | this emission |
| + the four digest pins | 10,570 | the commitment binding |
| + the 30-row arithmetic core | **10,600** | the whole route-B circuit |
| the §3 PROJECTION it replaces | ~10,534 | `MINA-DREGG-SEMANTICS-NATIVE.md` |

**⚑ AND WHAT SNARKY ACTUALLY REPORTS: 10,010** (`npm run cellcommit-native`, o1js 2.15.0,
`Provable.constraintSystem` over the transcribed stream). The Lean count is 560 rows HIGH, and
the cause is exact rather than approximate:

  * the emission is 11,188 generic sub-gates and 4,416 range checks;
  * packed two to a row, the generics need `⌈11188/2⌉ = 5,594` rows — which is EXACTLY what
    snarky reports, `5,594 + 4,416 = 10,010`;
  * `KimchiLower.renderOpsGo` **flushes its pending generic half-row before every `rc0`**, and
    snarky's double-generic packing carries the pending half ACROSS the range check. 560 of the
    4,416 range checks interrupt an odd-parity run, and 560 is the gap.

This is the SAFE direction — the Lean model is an upper bound the deployed circuit beats, not a
count the circuit exceeds — and it names a real optimisation: let `renderOpsGo` keep `pending`
across a non-generic op. Its correctness statement is the same `packGen_holds_iff` shape the
pure-generic backend already carries. NOT done here; an optimisation whose equivalence is
unproved is exactly what `KimchiLower` exists not to do.

**Against the §3 projection: −5% for the four sites** (10,010 measured against 10,402 = 4 ×
2,600.5 projected). The generated tree comes in under the hand-tuned marginal because it
replaces `inputLanes`' 16 range-check rows per permutation with 4 (the absorbed columns) plus a
handful of constant pins.

**The commitment binding is 99.7% of the emitted circuit** (10,570 / 10,600) — slightly MORE
dominant than the 98.8% projected, because the arithmetic core came in at 30 rows rather than
the ~127 the projection allowed for gates it does not emit.

**Effect rows per Pickles step: 6**, not the ~5 the projection gave (`65,536 / 10,040 = 6.5` at
the measured snarky price; on the usable ~55,000 after `zk_rows` and the wrapper it is 5.4, so
"5 to 6" is the honest reading and 6 is the ceiling). The re-price does not move the geometry:
a small turn is still one step.

The emitted gate mix is `Generic 6,154 · RangeCheck0 4,416` and **no other gate type** — every
row is one `KimchiTarget` MODELS, which is what `commitRows_all_modelled` proves and what keeps
the fail-closed `False` from discharging anything. -/

/-- **THE WHOLE COMPUTATIONAL GATE**, in one `def` so `CheckKimchiCellCommit` and
`EmitKimchiCellCommit` cannot drift apart on what "green" means. -/
def emissionChecksHold : Bool :=
  rowsAcceptHonestCell && digestCarrierHoldsB && commitLaneIsCellCommit && commitValsInPasta
    && costPinsHold && honestD3_is_cellCommit && (honestD3 == (841295468 : ℤ))

/-! ## §8 — THE EMITTED ARTIFACT.

The o1js consumer must not re-author anything, so it reads the instruction stream and the
Lean-computed witness. A `gen` op is `Gates.generic`'s five coefficients verbatim; an `rc0` op is
`Gates.rangeCheck0`'s value column plus its twelve limb/crumb columns. Coefficients are rendered as
DECIMAL STRINGS: the reduction's `p·2^{53i}` coefficients exceed 2⁵³ and a JSON number would
silently round them. -/

private def i2s (z : ℤ) : String := toString z

/-- One instruction, as JSON. -/
def opJson : KOp → String
  | .gen g =>
      "{\"k\":\"g\",\"l\":" ++ toString g.l ++ ",\"r\":" ++ toString g.r ++ ",\"o\":" ++ toString g.o
        ++ ",\"cl\":\"" ++ i2s g.cl ++ "\",\"cr\":\"" ++ i2s g.cr ++ "\",\"co\":\"" ++ i2s g.co
        ++ "\",\"cm\":\"" ++ i2s g.cm ++ "\",\"cc\":\"" ++ i2s g.cc ++ "\"}"
  | .rc0 v c1 c2 p3 p4 p5 p6 k7 k8 k9 k10 k11 k12 k13 k14 =>
      "{\"k\":\"r\",\"w\":[" ++ toString v ++ "," ++ toString c1 ++ "," ++ toString c2 ++ ","
        ++ toString p3 ++ "," ++ toString p4 ++ "," ++ toString p5 ++ "," ++ toString p6 ++ ","
        ++ toString k7 ++ "," ++ toString k8 ++ "," ++ toString k9 ++ "," ++ toString k10 ++ ","
        ++ toString k11 ++ "," ++ toString k12 ++ "," ++ toString k13 ++ "," ++ toString k14
        ++ "]}"
  | .zeroRow => "{\"k\":\"z\"}"

/-- The commitment emission's whole instruction stream, pins included. -/
def commitOps : List KOp := siteOps ++ pinGens.map KOp.gen

/-- The Lean-computed honest witness. Index `i` is variable `i`; `[0, NVC)` is the row and the
arithmetic intermediates, the rest are the generator's own. -/
def commitWitness : List ℤ := siteCtx.vals.toList

/-- The named columns the o1js driver binds, so it never restates a layout. -/
def commitCols : List (String × Nat) :=
  [ ("stateCommit", saCol state.STATE_COMMIT)
  , ("inter1", digCol 0), ("inter2", digCol 1), ("inter3", digCol 2)
  , ("recordDigest", auxCol aux_off.STATE_RECORD_DIGEST)
  , ("digestLane0", digLane 0), ("digestLane1", digLane 1)
  , ("digestLane2", digLane 2), ("digestLane3", digLane 3) ]

/-! ## §9 — WHAT REMAINS, precisely.

1. **`DigestCarrier` is undischarged**, and it is `KimchiPoseidon2`'s own first remainder. Closing
   it needs three repairs this file did not make, and the first two are DEFECTS of the emitted
   object rather than missing proof:
     * `bbRange64` allocates its two 12-bit COPY columns (`rc0CopyCols`, places 2⁷⁶/2⁶⁴) as fresh
       variables holding `0` and emits **no gate pinning them**, so the emitted `RangeCheck0`
       recomposition bounds its value by ~2⁸⁸, not 2⁶⁴. The fix is one shared pinned-zero variable
       and costs one sub-gate for the whole circuit.
     * `bbReduce`'s remainder carries a TRACKED bound of `2³¹` while the emitted check is the
       64-bit one. The `2³¹` is load-bearing: the S-box chain's Pasta safety is `35·2³¹ = 2³⁶·¹³`
       into `x⁷ < 2²⁵³·²`, and at a `2³²` lane it is `2²⁵⁹·⁹ > p_Pasta`. A genuine 31-bit check is
       two crumbs-only `RangeCheck0` rows plus a boolean sub-gate and costs rows.
     * The four 12-bit plookup columns are constrained by the lookup ARGUMENT, which `KimchiTarget`
       models as `False` and no forcing lemma may therefore assume. A real statement takes the
       lookup as a HYPOTHESIS, as `rc0PlookupCols`' own docstring says.
   Until then the carrier is a hypothesis, exhibited holding at the honest cell (§6) and nowhere
   assumed away.
2. **`transitionAll` is still unemitted** — 14 of the deployed descriptor's 35 constraints. Route B
   does not chain row to row: one valid, fully-bound cell transition is not a sequence, and a
   sequence of individually-valid rows is not a trace.
3. **The boundary PI pins are still unemitted** (7 of 35), so `state_commit` is not published as
   `NEW_COMMIT`. §5's warning stands even if they were: a public input the prover chose is not
   membership.
4. **The Lean forcing lemmas cover the rows this file emits, not the whole o1js circuit.** The o1js
   program adds `Poseidon.hash` for its claim binding and `Gadgets.rangeCheck32` for the envelope,
   and those rows are outside every theorem here — as are the `Lookup` gates `KimchiTarget` models
   as `False`. The argument that extra constraints cannot weaken soundness (they only shrink the
   satisfying set) is STATED, not proved.
5. **No freshness theorem for the emitted allocation.** Soundness needs none — each sub-gate forces
   its output from its inputs — but COMPLETENESS (that a witness exists for every honest cell) is
   exhibited at ONE cell, not proved for all.
6. **The field-accurate statement is ℤ.** §4 reads the emitted rows over ℤ. The deployed circuit
   runs over Pallas, and the step between them for the COMMITMENT rows is the integer-bound argument
   that `commitValsInPasta` only checks at the honest witness.
   `KimchiEffectIncNonce.kimchi_pallas_forces_intent` does that step for the ARITHMETIC rows; the
   commitment rows have no counterpart yet. ⚑ This is the one place the BabyBear/Kimchi asymmetry
   moves the OTHER way: the BabyBear hash layer is stated mod `p` and needs no bound argument at
   all, because it never emits the permutation.
-/

#assert_axioms babybear_forces_cellCommit
#assert_axioms pins_force
#assert_axioms commit_rows_force_siteHoldsAll
#assert_axioms kimchi_forces_cellCommit
#assert_axioms two_emissions_one_commit
#assert_axioms routeB_forces_cell_transition
#assert_axioms rowAcceptB_sound
#assert_axioms rowsAcceptB_sound
#assert_axioms tamper_non_preimage_refused
#assert_axioms tamper_substituted_commit_refused
#assert_axioms commitRows_all_modelled
#assert_axioms routeBRows_all_modelled
#assert_axioms siteInCols_length

end Dregg2.Circuit.Emit.KimchiCellCommit
