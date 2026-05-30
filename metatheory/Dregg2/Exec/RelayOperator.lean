/-
# Dregg2.Exec.RelayOperator — the bonded relay operator as an *economic* cell-program.

`STORAGE-AS-CELL-PROGRAMS §3.5`: dregg1's `RelayOperator` (`storage/src/operator.rs`, 738 LOC +
`relay.rs`, 365 LOC) is the **bonded store-and-forward** primitive — a relay that hosts
`CapInbox`es on behalf of others, prices delivery by TTL, and is held honest by an economic
discipline: it posts a **bond** that may only ever DECREASE on a recorded **dispute** (slash),
and it is rate-limited to a **per-epoch byte quota**. The doc's plan collapses the 1100 LOC of
imperative bond/slash/quota bookkeeping into a handful of `StateConstraint`s on the cell's record
state. This module is the faithful Lean transcription of that collapse — name-keyed over the
Preserves `Value` (`Exec/Value.lean`), gated by `RecordProgram.admits` (`Exec/Program.lean`),
driven by the executable `recExec` arrow (`Exec/RecordCell.lean`).

**The economic invariant, stated and PROVED:** a malicious operator cannot silently drain its own
bond. Two keystones —
  • `bond_floor_held`: every committed transition keeps `bond ≥ bondMin` (the bond floor, modelled
    cross-slot against the *immutable* `bondMin` via `fieldLeField` — the clean §7.2 encoding, so
    no OPEN is needed for the floor itself);
  • `bond_decrease_needs_dispute`: a committed transition that LOWERS the bond *forces*
    `disputeCount` to have strictly advanced (the `BoundedBy { index: 0, witness_index: 7 }`
    discipline of §3.5, encoded as `anyOf [monotonic "bond", strictMono "disputeCount"]`).
And `quota_enforced`: a committed relay keeps `bytesThisEpoch ≤ quota`.

## The §3.5 slot layout, name-keyed
| §3.5 slot | this record field | constraint |
|---|---|---|
| 1 `bond_min` | `"bondMin"` | `immutable` |
| 2 `quota` | `"quota"` | `immutable` |
| 5 `operator_pk` | `"operator"` | `immutable` (modelled scalar, the id) |
| 0 `bond_amount` | `"bond"` | floor `bondMin ≤ bond` + anti-drain |
| 3 `bytes_this_epoch` | `"bytesThisEpoch"` | `bytesThisEpoch ≤ quota` (RateLimitBySum) |
| 7 `dispute_count` | `"disputeCount"` | `monotonic` (disputes only increase) |

## Honest bounds carried as `-- OPEN:`
This is the single-cell economic skeleton; the genuinely cross-tier obligations of §3.5 are
declared and routed to their seams (per the doc), NOT faked here. See the `-- OPEN:` notes at the
program definition (epoch-reset of `bytesThisEpoch`; the DFA route-table WitnessedPredicate; the
SenderAuthorized gate; the multi-cell dispatch to the target inbox). The floor and anti-drain are
NOT open — they are proved.

Pure, computable, `#eval`-able; imports only `Exec.RecordCell` (which pulls `Program`/`Value`,
Lean-core), so it type-checks fast.
-/
import Dregg2.Exec.RecordCell

namespace Dregg2.Exec.RelayOperator

open Dregg2.Exec
open Dregg2.Exec.RecordCell

/-! ## The relay program — the §3.5 `StateConstraint` vector, name-keyed. -/

/-- **`relayProgram` — the bonded-relay coalgebra structure-map (the §3.5 constraint vector).**
A conjunction of the economic constraints on a relay-operator cell's record state:

* `immutable "bondMin"`, `immutable "quota"`, `immutable "operator"` — the §3.5 `Immutable`s on
  slots 1, 2, 5 (the bond floor, the quota, and the operator identity never change after init);
* `fieldLeField "bondMin" "bond"` — the **bond floor** (`§3.5 FieldGte { index 0, value slot 1 }`).
  The §3.5 floor is *cross-slot* against the immutable `bondMin`; `fieldLe`/`fieldGe` only compare
  against a *constant*, so we use the catalog's clean cross-slot variant `fieldLeField` (≡ the §7.2
  `FieldLteOther` it recommends) reading `new.bondMin ≤ new.bond`. Combined with `immutable
  "bondMin"` this is exactly "bond never below the (fixed) minimum" — no OPEN needed;
* `monotonic "disputeCount"` — the §3.5 `Monotonic { index 7 }` (disputes only ever increase);
* `fieldLe "bytesThisEpoch" quotaCap` — the **per-epoch quota** (`§3.5 RateLimitBySum { index 3,
  max slot 2 }`), modelled against the (immutable) quota cap value;
* the **anti-bond-drain** rule (`§3.5 BoundedBy { index 0, witness_index 7 }`): bond may DECREASE
  only when `disputeCount` advanced. Encoded as `anyOf [monotonic "bond", strictMono
  "disputeCount"]` — every commit either keeps the bond non-decreasing OR records a strict dispute
  bump. This is the discipline that makes silent bond-drain impossible (`bond_decrease_needs_dispute`).

`quotaCap` is the cell's fixed `quota` (immutable, so a constant for the life of the cell). -/
def relayProgram (quotaCap : Int) : RecordProgram :=
  .predicate
    [ .simple (.immutable "bondMin")
    , .simple (.immutable "quota")
    , .simple (.immutable "operator")
    , .fieldLeField "bondMin" "bond"                              -- bond floor (cross-slot)
    , .simple (.monotonic "disputeCount")                        -- disputes only increase
    , .simple (.fieldLe "bytesThisEpoch" quotaCap)               -- per-epoch quota
    , .anyOf [.monotonic "bond", .strictMono "disputeCount"]     -- anti-bond-drain (BoundedBy)
    ]
-- OPEN: the per-epoch RESET of `bytesThisEpoch` (§3.5 says `RateLimitBySum` resets internally each
--   epoch). The base constraint catalog has no epoch counter / clock, so `quota_enforced` below is
--   the *within-epoch* bound only; the reset is a clock-tier obligation (a turn that advances the
--   epoch and zeroes the counter), discharged when the kernel grows an epoch clock.
-- OPEN: the §3.5 DFA route-table caveat (`WitnessedPredicate { kind: Dfa, commitment:
--   route_table_root }`) — the relay only dispatches messages matching its declared route table.
--   That is a `Laws.Verifiable`/`CryptoKernel` verify/find-seam obligation (an untrusted classifier
--   emitting a checkable witness), routed to the crypto portal, NOT into this Lean law (REORIENT §6).
-- OPEN: the §3.5 `SenderAuthorized { PublicRoot slot 5 }` gate (only the operator may register a
--   hosted inbox) — a sender/witnessed constraint deferred to the authority boundary
--   (`Authority/Positional`), exactly as dregg1's scalar evaluator defers `Witnessed`/sender checks.
-- OPEN: the §3.5 multi-cell `relay` dispatch (the turn touches BOTH the relay cell AND the target
--   inbox) — a cross-cell `JointTurn` obligation (`boundDelta` half-edge), discharged by the forest
--   aggregate (Build 4), not by this single-cell program.

/-! ## The gated operations — `slash` / `relay` / `registerInbox`, all gated by `relayProgram`. -/

/-- The relay-cell method ids (the §3.5 actions). -/
def methodRegisterInbox : Nat := 1
def methodRelay         : Nat := 2
def methodSlash         : Nat := 3

/-- **`relayStep quotaCap method old op`** — the gated relay-cell transition: apply the raw
record-update `op`, and commit iff `relayProgram` admits it (fail-closed, via `RecordCell.recExec`).
This is the executable structure-map arrow for the bonded relay; `none` = the program rejected the
turn (a constraint failed / the bond would drain without a dispute / quota exceeded). All three
§3.5 actions flow through this one gate; they differ only in the `op` they carry. -/
def relayStep (quotaCap : Int) (method : Nat) (old : Value) (op : RecOp) : Option Value :=
  recExec (relayProgram quotaCap) method old op

/-- A `registerInbox` op: grow the hosted-inbox root commitment (modelled as a monotone scalar;
the §3.5 `Monotonic { index 4 }` on `hosted_inbox_root`). -/
def opRegisterInbox (newRoot : Int) : RecOp := .setScalar "hostedRoot" newRoot

/-- A `relay` op: add `nbytes` to the per-epoch byte counter (§3.5 `Effect::SetField slot 3`). -/
def opRelay (nbytes : Int) : RecOp := .addScalar "bytesThisEpoch" nbytes

/-- A `slash` op: lower the bond by `amount` (§3.5 `Effect::SetField slot 0, bond - slash`). To
*commit*, the accompanying disputeCount bump must already be in `old`/`new` — i.e. a slash is a
two-field turn; here we model the bond half and pair it with `opBumpDispute` in the demos. -/
def opSlash (amount : Int) : RecOp := .addScalar "bond" (-amount)

/-- A dispute bump: strictly increase `disputeCount` (§3.5 `Effect::SetField slot 7, +1`). -/
def opBumpDispute (newCount : Int) : RecOp := .setScalar "disputeCount" newCount

/-! ## Constraint-membership helpers — `relayProgram` admits ⇒ each listed constraint holds. -/

/-- `relayProgram.admits` unfolds to the conjunction of `evalConstraint` over its constraint list.
This is the bridge from a committed transition (`admits = true`) to each individual constraint
being satisfied on the committed `(old, new)`. PROVED definitionally. -/
theorem admits_iff_all (quotaCap : Int) (m : Nat) (old new : Value) :
    (relayProgram quotaCap).admits m old new = true
      ↔ [ StateConstraint.simple (.immutable "bondMin")
        , .simple (.immutable "quota")
        , .simple (.immutable "operator")
        , .fieldLeField "bondMin" "bond"
        , .simple (.monotonic "disputeCount")
        , .simple (.fieldLe "bytesThisEpoch" quotaCap)
        , .anyOf [.monotonic "bond", .strictMono "disputeCount"]
        ].all (fun c => evalConstraint c old new) = true := by
  rfl

/-! ## THE KEYSTONE (a) — the bond floor invariant. -/

/-- **`bond_floor_held` (KEYSTONE a — PROVED).** A *committed* relay transition keeps the bond at
or above the (immutable) minimum: if `relayStep` commits, then `new.bondMin ≤ new.bond` with both
present. This is the §3.5 bond floor (`FieldGte { index 0, value slot 1 }`) holding on the codomain
point — reasoned from the `fieldLeField "bondMin" "bond"` constraint post-commit. The relay can
never be admitted into a state where its bond sits below the floor. -/
theorem bond_floor_held
    {quotaCap : Int} {method : Nat} {old : Value} {op : RecOp} {new : Value}
    (h : relayStep quotaCap method old op = some new) :
    ∃ lo hi, new.scalar "bondMin" = some lo ∧ new.scalar "bond" = some hi ∧ lo ≤ hi := by
  have hadm : (relayProgram quotaCap).admits method old new = true := recExec_admitted h
  -- Pull out the `fieldLeField "bondMin" "bond"` conjunct.
  simp only [relayProgram, RecordProgram.admits, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, evalConstraint] at hadm
  obtain ⟨_, _, _, hfloor, _, _, _⟩ := hadm
  -- `hfloor : match new.scalar "bondMin", new.scalar "bond" with | some a, some b => decide (a ≤ b) | _ => false`.
  cases hlo : new.scalar "bondMin" with
  | none => rw [hlo] at hfloor; simp at hfloor
  | some lo =>
      cases hhi : new.scalar "bond" with
      | none => rw [hlo, hhi] at hfloor; simp at hfloor
      | some hi =>
          rw [hlo, hhi] at hfloor
          exact ⟨lo, hi, rfl, rfl, of_decide_eq_true hfloor⟩

/-! ## THE KEYSTONE (b) — bond may decrease only with a dispute (the slash discipline). -/

/-- **`bond_decrease_needs_dispute` (KEYSTONE b — PROVED).** A *committed* relay transition that
LOWERS the bond *forces* the dispute counter to have strictly advanced: if `relayStep` commits and
`new.bond < old.bond` (with both present as `a`/`b`), then there exist `da < db` with
`old.disputeCount = da`, `new.disputeCount = db`. This is the §3.5 `BoundedBy { index 0,
witness_index 7 }` discipline — a malicious operator **cannot silently drain its own bond**; every
bond decrease is gated on a recorded dispute. Reasoned from the `anyOf [monotonic "bond",
strictMono "disputeCount"]` conjunct: a strict bond decrease refutes the `monotonic "bond"` disjunct,
so the `strictMono "disputeCount"` disjunct must be the one that fired. -/
theorem bond_decrease_needs_dispute
    {quotaCap : Int} {method : Nat} {old : Value} {op : RecOp} {new : Value}
    {a b : Int}
    (h : relayStep quotaCap method old op = some new)
    (hoa : old.scalar "bond" = some a) (hnb : new.scalar "bond" = some b)
    (hdec : b < a) :
    ∃ da db, old.scalar "disputeCount" = some da ∧ new.scalar "disputeCount" = some db ∧ da < db := by
  have hadm : (relayProgram quotaCap).admits method old new = true := recExec_admitted h
  -- Pull out the anti-drain `anyOf` conjunct.
  simp only [relayProgram, RecordProgram.admits, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, evalConstraint] at hadm
  obtain ⟨_, _, _, _, _, _, hany⟩ := hadm
  -- `hany : (evalSimple (monotonic "bond") ∨ evalSimple (strictMono "disputeCount")) = true`
  -- (via `List.any` over the two disjuncts).
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at hany
  -- The `monotonic "bond"` disjunct is FALSE because `b < a` (a strict decrease).
  have hmono_false : evalSimple (.monotonic "bond") old new = false := by
    simp only [evalSimple, hoa, hnb]
    exact decide_eq_false (Int.not_le.mpr hdec)
  -- So the `strictMono "disputeCount"` disjunct must be the true one.
  have hstrict : evalSimple (.strictMono "disputeCount") old new = true := by
    rcases hany with hl | hr
    · rw [hmono_false] at hl; exact absurd hl (by simp)
    · exact hr
  -- Unfold `strictMono` to recover the honest `da < db`.
  simp only [evalSimple] at hstrict
  cases hda : old.scalar "disputeCount" with
  | none => rw [hda] at hstrict; simp at hstrict
  | some da =>
      cases hdb : new.scalar "disputeCount" with
      | none => rw [hda, hdb] at hstrict; simp at hstrict
      | some db =>
          rw [hda, hdb] at hstrict
          exact ⟨da, db, rfl, rfl, of_decide_eq_true hstrict⟩

/-! ## `quota_enforced` — the per-epoch byte counter stays within the quota cap. -/

/-- **`quota_enforced` (PROVED, within-epoch).** A *committed* relay transition keeps the
per-epoch byte counter at or below the quota cap: if `relayStep quotaCap` commits, then
`new.bytesThisEpoch ≤ quotaCap` (present). This is the §3.5 `RateLimitBySum { index 3, max slot 2 }`
holding on the codomain point — reasoned from the `fieldLe "bytesThisEpoch" quotaCap` conjunct.
-- OPEN: this is the *within-epoch* bound; the per-epoch RESET of the counter (the `RateLimitBySum`
   internal epoch boundary) is a clock-tier obligation deferred above — once the kernel has an epoch
   clock, the "resets each epoch" half is an epoch-advancing turn, and the conjunction of the two
   gives the full §3.5 rate limit. -/
theorem quota_enforced
    {quotaCap : Int} {method : Nat} {old : Value} {op : RecOp} {new : Value}
    (h : relayStep quotaCap method old op = some new) :
    ∃ used, new.scalar "bytesThisEpoch" = some used ∧ used ≤ quotaCap := by
  have hadm : (relayProgram quotaCap).admits method old new = true := recExec_admitted h
  simp only [relayProgram, RecordProgram.admits, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, evalConstraint] at hadm
  obtain ⟨_, _, _, _, _, hquota, _⟩ := hadm
  -- `hquota : evalSimple (fieldLe "bytesThisEpoch" quotaCap) old new = true`.
  simp only [evalSimple] at hquota
  cases hu : new.scalar "bytesThisEpoch" with
  | none => rw [hu] at hquota; simp at hquota
  | some used =>
      rw [hu] at hquota
      exact ⟨used, rfl, of_decide_eq_true hquota⟩

/-! ## `#eval` demos — the economic discipline, executable. -/

/-- A relay-operator cell at rest: bond 1000, floor 100, quota 1_000_000, 500 bytes used this
epoch, operator id 7, 0 disputes, hosted-root 0. (Quota cap = 1_000_000.) -/
def relayCell : Value :=
  .record
    [ ("bond",           .int 1000)
    , ("bondMin",        .int 100)
    , ("quota",          .int 1000000)
    , ("bytesThisEpoch", .int 500)
    , ("operator",       .int 7)
    , ("disputeCount",   .int 0)
    , ("hostedRoot",     .int 0) ]

/-- The fixed quota cap for `relayCell`. -/
def cap : Int := 1000000

-- A relay WITHIN quota commits: 500 + 1000 = 1500 ≤ 1_000_000, bond unchanged (non-decreasing),
-- disputes unchanged, all immutables held ⇒ admitted.
#eval relayStep cap methodRelay relayCell (opRelay 1000)
-- some (... bytesThisEpoch = 1500 ...)

-- A relay EXCEEDING quota is rejected: 500 + 2_000_000 = 2_000_500 > 1_000_000 ⇒ none (fail-closed).
#eval relayStep cap methodRelay relayCell (opRelay 2000000)
-- none

-- A slash that lowers bond AND bumps disputeCount commits. We model the two-field turn by applying
-- the dispute bump first (a state where disputeCount = 1), then the bond decrease; the combined new
-- state has bond ↓ AND disputeCount ↑, satisfying the anti-drain `anyOf`, the floor (900 ≥ 100),
-- and leaving immutables/quota intact ⇒ admitted.
def slashedOld : Value := relayCell                                   -- disputeCount = 0
def slashedNew : Value :=                                             -- bond 1000→900, dispute 0→1
  setField (setField relayCell "bond" (.int 900)) "disputeCount" (.int 1)
#eval (relayProgram cap).admits methodSlash slashedOld slashedNew
-- true  (bond decreased, but disputeCount advanced 0→1 ⇒ the BoundedBy discipline is satisfied)

-- A bond-drain WITHOUT a dispute is REJECTED: bond 1000→900 but disputeCount stays 0 ⇒ the anti-drain
-- `anyOf [monotonic bond, strictMono disputeCount]` fails (bond decreased AND no dispute) ⇒ none.
#eval relayStep cap methodSlash relayCell (opSlash 100)
-- none  (silent bond drain blocked)

-- Bond can't go below the floor: dropping bond to 50 (< bondMin 100), even WITH a dispute bump, is
-- rejected by the floor constraint `bondMin ≤ bond` (100 ≤ 50 is false) ⇒ none.
def underfloorNew : Value :=
  setField (setField relayCell "bond" (.int 50)) "disputeCount" (.int 1)
#eval (relayProgram cap).admits methodSlash relayCell underfloorNew
-- false  (50 < 100 floor ⇒ rejected even though a dispute was recorded)

-- A legitimate slash all the way (bond 1000→100 = exactly the floor) WITH a dispute commits.
def slashToFloorNew : Value :=
  setField (setField relayCell "bond" (.int 100)) "disputeCount" (.int 1)
#eval (relayProgram cap).admits methodSlash relayCell slashToFloorNew
-- true  (100 ≥ 100 floor, dispute recorded)

-- Mutating an immutable (changing the operator id) is rejected.
def tamperNew : Value := setField relayCell "operator" (.int 99)
#eval (relayProgram cap).admits methodRelay relayCell tamperNew
-- false  (operator is immutable)

end Dregg2.Exec.RelayOperator
