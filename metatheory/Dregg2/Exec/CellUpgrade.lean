/-
# Dregg2.Exec.CellUpgrade — the anti-brick `set_program` upgrade as an EXECUTABLE turn.

This module makes `Dregg2.Upgrade`'s anti-brick *law* into a concrete, computable
**upgrade transition** on a versioned cell (`dregg2-multicell-privacy §3`, `study-mina-relink §4`).
The previous module (`Upgrade.lean`) supplies the decidable admissibility relation
`setProgramAdmissible` and the keystone *existence* law `upgrade_never_bricks`. Here we wire
that relation into an actual state-transition function `execUpgrade : VersionedCell →
UpgradeRequest → Option VersionedCell` and re-derive — for the EXECUTABLE turn — the three
load-bearing facts:

* **`execUpgrade_never_bricks`** — for any cell and any live verifier version, there is an
  admissible upgrade that `execUpgrade` *actually performs* (returns `some`). The signature
  fallback always works, so no cell is ever stranded by a backend swap. (Lifts
  `Upgrade.upgrade_never_bricks`.)
* **`execUpgrade_stale_needs_signature`** — when the cell's pinned `airVersion` is `stale` vs
  the live verifier, a proof-authorized request against the stored version is **rejected**
  (`execUpgrade … = none`), and the signature fallback is the *operative* admitting arm.
  (Lifts `Upgrade.stale_version_falls_back_to_signature`.)
* **`execUpgrade_is_authorized_intra`** — an admitted `execUpgrade` by a control-holding owner
  both satisfies the version-pin admissibility AND is the owner's own (`intra`) authority act,
  connecting to the vat-boundary integrity case-split.
  (Lifts `Upgrade.upgrade_is_authorized_intra`.)

**The pinned program id.** Per `study-mina-relink §4`/§5: AIR-id `= H(canonical(schema_decl))`,
and `Circuit{circuit_hash}` *is* its content hash — a content-addressed object the CDT names.
We pin it as `ProgramId := Nat` (the circuit hash), keeping admissibility decidable and the
upgrade transition computable, faithful to "the cell's `CellProgram` IS the side-loaded VK."

Spec-and-executable-first: every theorem here is PROVED with no `sorry` (the heavy existential
content lives in the reused `Upgrade` lemmas). The crypto-soundness of any actual proof check is
the §8 circuit obligation, NOT merged into this semantic law — `setProgramAdmissible` is the
decidable *oracle* `byProof v ⇒ v = live`, not a binding/extractability claim.
-/
import Dregg2.Upgrade

namespace Dregg2.Exec.CellUpgrade

open Dregg2.Upgrade
open Dregg2.Authority

/-! ## The versioned cell -/

/-- **`ProgramId`** — the content-addressed identifier of a cell's pinned program / side-loaded
VK: `Circuit{circuit_hash}`, i.e. `H(canonical(schema_decl))` (`study-mina-relink §4`). A `Nat`
hash; swapping the program installs a new id. Distinct from `Exec.RecordProgram` (the program
*body*); here we track only the *which-program* an upgrade re-pins, since admissibility is gated
by the AIR *version*, not the body. -/
abbrev ProgramId := Nat

/-- **`VersionedCell`** — a cell carrying the three things the anti-brick clause needs: the
content-addressed `program` it currently pins, the `airVersion` (`AirVersion`) its verifier was
pinned to, and its sovereign `owner` (a `Label`). The cell is *bricked* exactly when no
authorized `set_program` can move it off a `program`/`airVersion` the live verifier no longer
accepts — which `execUpgrade_never_bricks` rules out. -/
structure VersionedCell where
  /-- The content-addressed program / side-loaded VK currently pinned. -/
  program    : ProgramId
  /-- The pinned proof-system / AIR version the cell's verifier expects. -/
  airVersion : AirVersion
  /-- The sovereign owner authorized to re-pin the program. -/
  owner      : Label
  deriving DecidableEq, Repr

/-- **`UpgradeRequest`** — a reified `set_program` turn applied to a `VersionedCell`: the new
program id to install, the AIR version it will be pinned to, and the `UpgradeAuth` backing it
(a current-version `byProof`, or the owner's `bySignature` fallback). -/
structure UpgradeRequest where
  /-- The new content-addressed program / VK to install. -/
  newProgram    : ProgramId
  /-- The AIR version the upgraded cell will pin (the post-state version). -/
  newAirVersion : AirVersion
  /-- The authority backing the upgrade (`byProof` / `bySignature`). -/
  auth          : UpgradeAuth
  deriving Repr

/-! ## The executable upgrade transition -/

/-- **`execUpgrade live cell req`** — the executable anti-brick `set_program` turn. Against the
*live* verifier version, it admits `req` **iff** `setProgramAdmissible live cell.airVersion
req.auth` holds (a current-version proof OR an owner signature), and on admission re-pins the
cell to `req.newProgram` at `req.newAirVersion`; otherwise it is **fail-closed** (`none`).

This is the function form of Mina's `set_verification_key` check: the decidable disjunction
gates the write, and the `bySignature` arm is the always-available owner edge that keeps the
write reachable across any backend swap. The owner field is preserved — an upgrade re-pins the
program, it does not transfer the cell (`set_verification_key` does not change the account
holder; continuity is by the permission, `study-mina-relink §4`). -/
def execUpgrade (live : AirVersion) (cell : VersionedCell)
    (req : UpgradeRequest) : Option VersionedCell :=
  if setProgramAdmissible live cell.airVersion req.auth then
    some { program := req.newProgram, airVersion := req.newAirVersion, owner := cell.owner }
  else
    none

/-- **`sigRequest newProgram newAir`** — the canonical owner-signature `set_program` request:
re-pin to `newProgram` at `newAir` under the `bySignature` fallback. This is the request the
anti-brick guarantee is built on — it is admissible at *every* version pair. -/
def sigRequest (newProgram : ProgramId) (newAir : AirVersion) : UpgradeRequest :=
  { newProgram := newProgram, newAirVersion := newAir, auth := UpgradeAuth.bySignature }

/-- **`execUpgrade` on a signature request always fires** — a direct computation: the
`bySignature` arm reduces `setProgramAdmissible … = True`, so the `if` takes the `some` branch.
The computable kernel of `execUpgrade_never_bricks`. -/
theorem execUpgrade_signature_fires (live : AirVersion) (cell : VersionedCell)
    (newProgram : ProgramId) (newAir : AirVersion) :
    execUpgrade live cell (sigRequest newProgram newAir) =
      some { program := newProgram, airVersion := newAir, owner := cell.owner } := by
  -- `sigRequest`'s `auth = bySignature`, whose admissibility is `True` (decided affirmatively).
  unfold execUpgrade sigRequest
  simp only [setProgramAdmissible, if_true]

/-! ## THE KEYSTONE: no backend swap can brick a versioned cell -/

/-- **`execUpgrade_never_bricks`** — THE keystone, executable form. For *any* versioned cell and
*any* live verifier version (the recursion backend may bump `live` arbitrarily —
`RecursionBackend`/`FriRecursionBackend`, design §7), there **exists** an `UpgradeRequest` that
`execUpgrade` actually performs (returns `some`). Hence no cell is ever stranded / bricked: the
owner-signature fallback is always a path out of any dead pinned version.

The existential is non-vacuous content — it asserts the executable transition is *total over
version pairs* (admit-and-perform is always reachable), exactly what fails for a naive proof-only
`set_program` (where `stale stored live` would make every request fail-closed and brick the
cell). The chosen witness is `sigRequest`, and admissibility is lifted directly from
`Upgrade.upgrade_never_bricks` (whose witness is `bySignature`). -/
theorem execUpgrade_never_bricks (live : AirVersion) (cell : VersionedCell) :
    ∃ req : UpgradeRequest, (execUpgrade live cell req).isSome := by
  -- Reuse the *law*: `Upgrade.upgrade_never_bricks` gives an admissible authorization at this
  -- version pair; its witness is `bySignature`. We package it as a concrete request that fires.
  obtain ⟨auth, hauth⟩ := Upgrade.upgrade_never_bricks live cell.airVersion
  refine ⟨{ newProgram := cell.program, newAirVersion := live, auth := auth }, ?_⟩
  unfold execUpgrade
  simp only [hauth, if_true, Option.isSome_some]

/-- **`execUpgrade_never_bricks_concrete`** — the same keystone with the witness named: the
owner-signature re-pin to any target program/version *always* produces a `some` post-state. This
is the operational reading — "the owner can always re-key by signature" — discharged by the
direct computation `execUpgrade_signature_fires`. -/
theorem execUpgrade_never_bricks_concrete (live : AirVersion) (cell : VersionedCell)
    (newProgram : ProgramId) (newAir : AirVersion) :
    (execUpgrade live cell (sigRequest newProgram newAir)).isSome := by
  rw [execUpgrade_signature_fires]
  exact Option.isSome_some

/-! ## The stale branch: older version ⇒ signature fallback (executable) -/

/-- **`execUpgrade_stale_needs_signature`** — the `older_version ⇒ signature_fallback` rule, in
executable form (verbatim Mina `fallback_to_signature_with_older_version`). When the cell's
pinned `airVersion` is `stale` against the live verifier, the proof arm against the *stored*
(stale) version is **rejected** by `execUpgrade` (it returns `none` — fail-closed, never a
silent accept), WHILE the signature fallback is admitted and *performs* the re-pin. Three
conjuncts, mirroring `Upgrade.stale_version_falls_back_to_signature` but at the transition level:

1. a proof request against the stale stored version yields `none` (the proof arm is dead), and
2. the signature request yields `some` (the fallback is the operative, reachable arm), and
3. that `some` is the correctly re-pinned post-state.

So a verifier upgrade past a cell's pinned version never strands it — it routes the cell's owner
to the signature path rather than bricking the cell. -/
theorem execUpgrade_stale_needs_signature (live : AirVersion) (cell : VersionedCell)
    (newProgram : ProgramId) (newAir : AirVersion)
    (h : stale cell.airVersion live) :
    execUpgrade live cell
        { newProgram := newProgram, newAirVersion := newAir,
          auth := UpgradeAuth.byProof cell.airVersion } = none ∧
      execUpgrade live cell (sigRequest newProgram newAir) =
        some { program := newProgram, airVersion := newAir, owner := cell.owner } := by
  -- Lift the *law*: in the stale branch, `bySignature` is admissible and `byProof stored` is not.
  obtain ⟨_hsig, hproof⟩ := Upgrade.stale_version_falls_back_to_signature live cell.airVersion h
  refine ⟨?_, execUpgrade_signature_fires live cell newProgram newAir⟩
  -- The proof arm is inadmissible (`hproof`), so the `if` takes the `none` branch.
  unfold execUpgrade
  simp only [hproof, if_false]

/-! ## The complementary branch: a current-version cell admits a proof upgrade (executable) -/

/-- **`execUpgrade_current_admits_proof`** — the non-stale branch, executable. When the cell's
pinned version is up to date (`cell.airVersion = live`), a proof request against it is admitted
and `execUpgrade` performs the re-pin *without* needing the signature fallback. Together with
`execUpgrade_stale_needs_signature` this exhausts Mina's `if stored < current then … else …`
branch over the executable transition (lifts `Upgrade.current_version_admits_proof`). -/
theorem execUpgrade_current_admits_proof (live : AirVersion) (cell : VersionedCell)
    (newProgram : ProgramId) (newAir : AirVersion)
    (h : cell.airVersion = live) :
    execUpgrade live cell
        { newProgram := newProgram, newAirVersion := newAir,
          auth := UpgradeAuth.byProof cell.airVersion } =
      some { program := newProgram, airVersion := newAir, owner := cell.owner } := by
  -- Lift the law: the current-version proof arm is admissible, so the `if` fires `some`.
  have hadm := Upgrade.current_version_admits_proof live cell.airVersion h
  unfold execUpgrade
  simp only [hadm, if_true]

/-! ## Link to authority: an admitted `execUpgrade` is the owner's intra-authority act -/

/-- **`ownerSubjects req` / the acting-subject set.** For an `execUpgrade` we model the acting
subjects as exactly the cell's `owner` (the sovereign re-keying its own program); we expose the
singleton so the intra-authority precondition `owner ∈ subjects` is discharged structurally. -/
def ownerSubjects (cell : VersionedCell) : List Label := [cell.owner]

/-- The owner is always among `ownerSubjects` — trivial membership for the intra arm. -/
theorem owner_mem_ownerSubjects (cell : VersionedCell) :
    cell.owner ∈ ownerSubjects cell := by
  unfold ownerSubjects; exact List.mem_singleton.mpr rfl

/-- **`execUpgrade_is_authorized_intra`** — the link to the vat-boundary integrity case-split,
stated so the authorization preconditions are LOAD-BEARING (mirror of
`Upgrade.upgrade_is_authorized_intra`). When `execUpgrade` admits a request (it returned
`some cell'`) and the owner holds `control` on itself, that `set_program` both

* **satisfies the version-pin / admissibility** — the post-state was reached only because the
  offered authority cleared `setProgramAdmissible live cell.airVersion req.auth` (a current-version
  proof OR the owner signature); a stale `byProof cell.airVersion` would have failed-closed to
  `none`, so this conjunct could not hold (`hfired` is operative), and
* **stands in the `intra` arm of `Authority.Integrity`** (l4v `troa_lrefl`: the owning subject may
  make an arbitrary change to its own object — here, re-pin its own program).

The `bySignature` fallback is exactly what keeps the admissibility conjunct *satisfiable* across a
backend swap, so the cell's owner never loses the authority to re-pin its verifier.

This replaces the earlier `execUpgrade_is_intra_authority`, whose conclusion was the bare
`Integrity` (making `hctrl` and the recovered admissibility decorative). Here `hctrl` is consumed
when assembling `AuthorizedUpgrade`, and the recovered admissibility is returned as the first
conjunct. `W`, `P`, `KO`, `p`, `ko`, `ko'` are the `Integrity` parameters; `KO` is the abstract
cell-object state, unconnected to the upgrade data. -/
theorem execUpgrade_is_authorized_intra
    {P : Type*} (W : Type*) [Dregg2.Laws.Verifiable P W] {KO : Type*}
    (live : AirVersion) (cell cell' : VersionedCell) (req : UpgradeRequest)
    (caps : Caps) (p : KO → KO → P) (ko ko' : KO)
    (hctrl : Upgrade.ownerHoldsControl caps cell.owner)
    (hfired : execUpgrade live cell req = some cell') :
    setProgramAdmissible live cell.airVersion req.auth ∧
      Integrity W cell.owner (ownerSubjects cell) p ko ko' := by
  -- `execUpgrade` returned `some`, so its `if` guard — i.e. `setProgramAdmissible` — held.
  have hadm : setProgramAdmissible live cell.airVersion req.auth := by
    by_contra hna
    -- If inadmissible, `execUpgrade` would have taken the `none` branch, contradicting `hfired`.
    unfold execUpgrade at hfired
    simp only [hna, if_false] at hfired
    exact Option.some_ne_none cell' hfired.symm
  -- Assemble the `UpgradeTurn` and its full `AuthorizedUpgrade` precondition: the owner holds
  -- `control` (`hctrl`), is its own subject (`owner_mem_ownerSubjects`), and `req.auth` is
  -- admissible (`hadm`). All three are load-bearing for `upgrade_is_authorized_intra`.
  let t : Upgrade.UpgradeTurn :=
    { owner := cell.owner, subjects := ownerSubjects cell,
      live := live, stored := cell.airVersion, auth := req.auth }
  have hauth : Upgrade.AuthorizedUpgrade caps t :=
    ⟨hctrl, owner_mem_ownerSubjects cell, hadm⟩
  exact Upgrade.upgrade_is_authorized_intra W t caps p ko ko' hauth

/-! ## `#eval` demos — the executable upgrade turn, run.

A current-version cell admits a proof upgrade; a stale cell rejects the proof but admits the
signature fallback. (`Option.isSome` projected to `Bool` so the demos print cleanly.) -/

/-- A demo cell, pinned to program `7` at AIR version `3`, owned by label `42`. -/
def demoCell : VersionedCell := { program := 7, airVersion := 3, owner := 42 }

/-- A current-version proof request: re-pin to program `8`, proof against the *live* version `3`
(matches `demoCell.airVersion`). Admitted because the proof is current. -/
def demoProofCurrent : UpgradeRequest :=
  { newProgram := 8, newAirVersion := 3, auth := UpgradeAuth.byProof 3 }

/-- A proof request against the cell's *stale* pinned version, evaluated when the live verifier
has moved to version `5`. The proof arm (`byProof 3`) is no longer current ⇒ rejected. -/
def demoProofStale : UpgradeRequest :=
  { newProgram := 9, newAirVersion := 5, auth := UpgradeAuth.byProof 3 }

/-- The owner-signature fallback re-pin: program `9` at the new live version `5`. Always admitted. -/
def demoSig : UpgradeRequest := sigRequest 9 5

-- live = 3 (current): a current-version PROOF upgrade is admitted and performed.
-- Expect: `some { program := 8, airVersion := 3, owner := 42 }`.
#eval execUpgrade 3 demoCell demoProofCurrent

-- live = 5 (verifier swapped past the cell's pinned v3 ⇒ stale): the PROOF upgrade is REJECTED.
-- Expect: `none`.
#eval execUpgrade 5 demoCell demoProofStale

-- live = 5 (stale): the owner-SIGNATURE fallback is admitted — the cell is NOT bricked.
-- Expect: `some { program := 9, airVersion := 5, owner := 42 }`.
#eval execUpgrade 5 demoCell demoSig

-- The keystone, demonstrated: at the stale live version, an admissible upgrade EXISTS (true).
#eval (execUpgrade 5 demoCell demoSig).isSome

end Dregg2.Exec.CellUpgrade
