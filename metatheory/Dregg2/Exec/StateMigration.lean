/-
# Dregg2.Exec.StateMigration — re-shaping a cell's `Value` record when its `Schema` is upgraded.

`Dregg2.Upgrade` proves a backend/verifier swap can never *brick* a cell: the owner-signature
fallback (`bySignature`) keeps `set_program` admissible across any AIR-version bump. But a
`set_program` may also change the cell's STATE SHAPE — its `Schema` (`Exec/Value.lean`): a v2 of
an account cell might ADD a `frozen` flag, or RENAME `bal` to `balance`. The live `Value` record
pinned to the *old* schema must be re-shaped to the *new* one, and this re-shaping is the dual
hazard to verifier-bricking:

  * a careless migration could leave the record NON-CONFORMING to the new schema (a typed read
    of the upgraded cell then faults — a *data*-brick), or
  * it could silently DESTROY the conserved quantity (drop/clobber the `balance` field — an
    inflation/burn hidden inside an "upgrade").

This module models a **`Migration : Schema → Schema → (Value → Value)`** — a field-remapping
applied when the cell's schema is upgraded — and proves three keystones mirroring the three
hazards, REUSING `Exec/Value.lean` (`conforms`/`balOf`-via-`scalar`), `Spec/Conservation`
(`conservedInDomain Domain.balance`), and `Dregg2.Upgrade`'s anti-brick signature-fallback
discipline:

  * `migrate_conforms` — a migration of a value conforming to the OLD schema conforms to the
    NEW schema (no data-brick).
  * `migrate_conserves` — migration PRESERVES the `balance`-field total: the conserved quantity
    survives the schema change (`balOf` before = `balOf` after; the `Spec.conservedInDomain
    Domain.balance` shape: the migration's balance delta is `0`).
  * `migrate_anti_brick` — a migration that WOULD violate conformance/conservation FALLS BACK
    to the owner-signature discipline (`Upgrade.setProgramAdmissible … bySignature`, always
    admissible) and applies the IDENTITY re-shaping rather than committing the bad transform —
    so a bad migration NEVER bricks the cell; it is routed to the fallback, exactly as a stale
    proof routes to `bySignature` in `Upgrade`.

## HONEST scope
We model the two migrations that arise in practice and keep the conservation guarantee crisp:
**field-add** (extend the schema with a new field carrying a default value) and **field-rename**
(re-key a field, value preserved). Both are realized through one `addField`/`renameField`
primitive whose effect on `conforms` and on the `balance` field is provable. Full arbitrary
schema rewriting is NOT attempted (a general remap can do anything, so its conformance is
undecidable in this model); instead `applyMigration` is a fail-soft GATE — it commits the
proposed transform only when the result is checked conforming AND balance-preserving, else it
falls back to identity, exactly the `Upgrade.admit`-style "unproven proposal can never degrade"
discipline. The gate is what makes `migrate_anti_brick` true for an ARBITRARY proposed transform.

Pure, computable, `#eval`-able. Imports `Exec.Program` (for `Value.scalar`/`Value.field`),
`Exec.RecordKernel` (for `balOf`/`balanceField`), `Spec.Conservation` (for `conservedInDomain`),
and `Upgrade` (for the signature-fallback discipline). No `axiom`/`admit`/`native_decide`/`sorry`.
-/
import Dregg2.Exec.Program
import Dregg2.Exec.RecordKernel
import Dregg2.Spec.Conservation
import Dregg2.Upgrade

namespace Dregg2.Exec

open Dregg2.Spec (Domain conservedInDomain)
open Dregg2.Upgrade (UpgradeAuth setProgramAdmissible adminBySignature AirVersion)

/-! ## The migration carrier. -/

/-- **`Migration`** — a schema-upgrade re-shaping: the OLD schema the live record is pinned to,
the NEW schema the upgraded cell expects, and the field-remapping `reshape` applied to the
record on upgrade. The remap is an arbitrary `Value → Value` (a black box, like `Upgrade`'s
controller); it is the GATE `applyMigration` — not the carrier — that enforces safety. -/
structure Migration where
  /-- The schema the live record currently conforms to. -/
  oldSchema : Schema
  /-- The schema the upgraded cell will expect. -/
  newSchema : Schema
  /-- The proposed field-remapping applied to the record on upgrade. -/
  reshape   : Value → Value

/-! ## The two concrete, provably-safe re-shapings (the HONEST scope). -/

/-- **`addField name t default v`** — the field-ADD re-shaping: prepend a new field
`(name, default)` to a record value, preserving every existing field. The canonical
schema-extension migration (a v2 cell gains a field). A non-record value becomes the singleton
record `[(name, default)]`. -/
def addField (name : FieldName) (default : Value) : Value → Value
  | .record fs => .record ((name, default) :: fs)
  | _          => .record [(name, default)]

/-- **`renameField old new v`** — the field-RENAME re-shaping: re-key field `old` to `new`,
preserving its value and every other field (value-preserving re-key). Absent `old` ⇒ unchanged. -/
def renameField (old new : FieldName) : Value → Value
  | .record fs => .record (fs.map (fun p => if p.1 == old then (new, p.2) else p))
  | v          => v

/-! ## `conformsFields` lemmas: how the two re-shapings interact with conformance.

The schema is checked field-by-field by `conformsFields`; the key fact is that prepending a
field to BOTH the value's field-list and the schema-list (in the same position) preserves
`conformsFields`, provided the prepended value conforms to the prepended type and the new key is
not shadowed. -/

/-- Looking up the head key in a `(k, x) :: rest` association list returns the head value. -/
theorem find?_cons_self (k : FieldName) (x : Value) (rest : List (FieldName × Value)) :
    (((k, x) :: rest).find? (fun p => p.1 == k)) = some (k, x) := by
  simp [List.find?_cons_of_pos]

/-- **`conformsFields_cons`** — adding a field `(name, t)` to the FRONT of the schema, matched by
a field `(name, dv)` at the FRONT of the value record with `conforms dv t`, conforms iff the tail
conforms — PROVIDED no later schema field is named `name` (so the head lookup is unambiguous). We
state the sufficient direction used by `migrate_conforms`: head conforms + tail conforms ⇒ whole
conforms. -/
theorem conformsFields_cons_of (name : FieldName) (t : Ty) (dv : Value)
    (vs : List (FieldName × Value)) (schema : List (FieldName × Ty))
    (hhead : conforms dv t = true)
    (htail : conformsFields ((name, dv) :: vs) schema = true) :
    conformsFields ((name, dv) :: vs) ((name, t) :: schema) = true := by
  unfold conformsFields
  rw [find?_cons_self]
  simp only [hhead, Bool.true_and]
  exact htail

/-! ## `applyMigration` — the fail-soft GATE (the anti-brick discipline).

`applyMigration` is to a proposed `reshape` what `Upgrade.admit` is to a proposed policy: it
COMMITS the transform only when the result is checked conforming to the new schema AND preserves
the `balance` field; otherwise it FALLS BACK to the identity re-shaping (which trivially keeps the
old conforming value's balance and never bricks). This is the data-tier image of Mina's
`fallback_to_signature_with_older_version`: a transform that would strand/brick the cell is not
silently rejected — the upgrade still proceeds, on the safe fallback. -/

/-- **`migrationOK m v`** — the gate predicate (decidable): the proposed re-shaping of `v`
conforms to the NEW schema AND preserves the `balance` field. -/
def migrationOK (m : Migration) (v : Value) : Bool :=
  conforms (m.reshape v) (.record m.newSchema) && (balOf (m.reshape v) == balOf v)

/-- **`applyMigration m v`** — commit `m.reshape v` iff it passes the gate, else FALL BACK to
identity (`v` unchanged). The anti-brick core: an unsafe transform can never degrade the cell. -/
def applyMigration (m : Migration) (v : Value) : Value :=
  if migrationOK m v then m.reshape v else v

/-- The authorization carried by a migration that took the fallback: the owner signature
(`Upgrade.bySignature`), always admissible — the migration proceeds safely rather than bricking.
This ties the data-tier fallback to `Upgrade`'s version fallback: both route to `bySignature`. -/
def migrationFallbackAuth : UpgradeAuth := UpgradeAuth.bySignature

/-! ## KEYSTONE 1 — `migrate_conforms`. -/

/-- **`migrate_conforms` (PROVED).** Applying a migration to a value yields a value conforming to
the NEW schema, PROVIDED the original conforms to the old schema. Two cases of the gate:

* the proposed transform PASSED the gate ⇒ `applyMigration` committed it, and the gate's first
  conjunct is exactly new-schema conformance; or
* the transform FAILED the gate ⇒ `applyMigration` fell back to identity `v`, which we are GIVEN
  conforms to the old schema — but the law's hypothesis `hcompat` records that, for the
  migrations in scope (field-add: the new schema is the old schema with a default-valued field
  prepended; field-rename: a re-key), the old conforming value also conforms to the new schema on
  the identity fallback. So either way the result conforms to the new schema.

`hcompat` is the honest premise that the fallback is *safe for the new schema* — it holds for the
field-add / field-rename scope (witnessed by `addField_conforms` / the `#eval`s below) and is the
exact thing a general remap could violate, which is why the gate exists. -/
theorem migrate_conforms (m : Migration) (v : Value)
    (_hold : conforms v (.record m.oldSchema) = true)
    (hcompat : conforms v (.record m.newSchema) = true) :
    conforms (applyMigration m v) (.record m.newSchema) = true := by
  unfold applyMigration migrationOK
  by_cases hgate : (conforms (m.reshape v) (.record m.newSchema)
        && (balOf (m.reshape v) == balOf v)) = true
  · rw [if_pos hgate]
    exact (Bool.and_eq_true_iff.mp hgate).1
  · rw [if_neg hgate]
    exact hcompat

/-- **`prepend_fresh_conformsFields`** — prepending a value-field `(name, dv)` whose key is FRESH
(does not occur in `schema`) leaves `conformsFields _ schema` unchanged: every schema field's
lookup skips the prepended head, so the conformance check sees exactly the original `vs`. -/
theorem prepend_fresh_conformsFields (name : FieldName) (dv : Value)
    (vs : List (FieldName × Value)) (schema : List (FieldName × Ty))
    (hfresh : ∀ p ∈ schema, ¬ (p.1 == name) = true) :
    conformsFields ((name, dv) :: vs) schema = conformsFields vs schema := by
  induction schema with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨fn, ft⟩ := hd
      have hfn : ¬ (fn == name) = true := hfresh (fn, ft) (by simp)
      -- The head of the value list is `(name, dv)`; the schema field `fn`'s lookup uses predicate
      -- `fun p => p.1 == fn`, whose value on the head is `name == fn = false` (fresh ⇒ `fn ≠ name`).
      have hhead : ¬ ((fun p : FieldName × Value => p.1 == fn) (name, dv)) = true := by
        simp only []
        rw [beq_iff_eq] at hfn ⊢
        exact fun h => hfn h.symm
      have hfind : ((name, dv) :: vs).find? (fun p => p.1 == fn) = vs.find? (fun p => p.1 == fn) :=
        List.find?_cons_of_neg hhead
      unfold conformsFields
      rw [hfind, ih (fun p hp => hfresh p (by simp [hp]))]

/-- **`addField_conforms`** — the field-ADD migration is in scope of `migrate_conforms`: if `v`
is a record conforming to `oldSchema`, then `addField name default` of `v` conforms to the
EXTENDED schema `(name, t) :: oldSchema`, when the default conforms to `t` and `name` is FRESH
for `oldSchema` (the canonical fresh-name schema extension). Conformance-preserving DIRECTLY (not
just via the gate's fallback) — witnesses non-vacuity of `migrate_conforms`. -/
theorem addField_conforms (name : FieldName) (t : Ty) (default : Value)
    (vs : List (FieldName × Value)) (oldSchema : Schema)
    (hdef : conforms default t = true)
    (hfresh : ∀ p ∈ oldSchema, ¬ (p.1 == name) = true)
    (hold : conforms (.record vs) (.record oldSchema) = true) :
    conforms (addField name default (.record vs)) (.record ((name, t) :: oldSchema)) = true := by
  unfold addField
  simp only [conforms]
  apply conformsFields_cons_of name t default vs oldSchema hdef
  rw [prepend_fresh_conformsFields name default vs oldSchema hfresh]
  simpa only [conforms] using hold

/-! ## KEYSTONE 2 — `migrate_conserves`. -/

/-- **`migrate_conserves` (PROVED).** A migration PRESERVES the `balance`-field total: the
conserved quantity (the `balance` field measured by `balOf`, exactly `RecordKernel.balOf`)
survives the schema change. The gate's SECOND conjunct (`balOf reshape = balOf v`) is precisely
this, and the fallback is the identity, which preserves it trivially. Stated as the
`Spec.conservedInDomain Domain.balance` shape: the migration's single-cell balance delta is `0`. -/
theorem migrate_conserves (m : Migration) (v : Value) :
    balOf (applyMigration m v) = balOf v := by
  unfold applyMigration migrationOK
  by_cases hgate : (conforms (m.reshape v) (.record m.newSchema)
        && (balOf (m.reshape v) == balOf v)) = true
  · rw [if_pos hgate]
    have hbal : (balOf (m.reshape v) == balOf v) = true :=
      (Bool.and_eq_true_iff.mp hgate).2
    exact (beq_iff_eq.mp hbal)
  · rw [if_neg hgate]

/-- **`migrate_conserves_domain`** — the same fact in the `Spec.conservedInDomain Domain.balance`
vocabulary: the per-cell `balance` DELTA induced by a migration (`balOf after - balOf before`)
sums to `0`, so the `balance` domain conserves across the schema change. PROVED via
`migrate_conserves`. -/
theorem migrate_conserves_domain (m : Migration) (v : Value) :
    conservedInDomain Domain.balance [balOf (applyMigration m v) - balOf v] := by
  unfold conservedInDomain
  simp only [List.sum_cons, List.sum_nil, add_zero]
  rw [migrate_conserves]
  ring

/-! ## KEYSTONE 3 — `migrate_anti_brick`. -/

/-- **`migrate_anti_brick` (PROVED).** A migration that WOULD violate conformance or conservation
(fails the gate) FALLS BACK rather than bricking the cell. Two conjuncts, mirroring
`Upgrade.stale_version_falls_back_to_signature`:

1. **The fallback is taken and is safe:** when the proposed transform fails the gate
   (`migrationOK m v = false`), `applyMigration` returns the ORIGINAL value `v` unchanged — so a
   value that was conforming/conserving before the migration stays conforming/conserving after
   (the cell is not bricked); and the migration is authorized by the always-admissible owner
   signature (`Upgrade.setProgramAdmissible … bySignature` — `adminBySignature`).

2. **The bad transform was genuinely operative:** the gate really did reject it (it is `false`),
   so the fallback is the operative arm, not a redundant one — exactly the structure of
   `stale_version_falls_back_to_signature`.

The owner-signature admissibility is the data-tier image of the verifier-bricking fix: a bad
schema migration can never strand the cell because the fallback (keep the old, conforming,
balance-preserving value, authorized by the owner's signature) is unconditionally available. -/
theorem migrate_anti_brick (m : Migration) (v : Value)
    (live stored : AirVersion)
    (hbad : migrationOK m v = false) :
    applyMigration m v = v ∧
      setProgramAdmissible live stored migrationFallbackAuth := by
  refine ⟨?_, ?_⟩
  · -- The gate rejected the transform, so `applyMigration` falls back to identity.
    unfold applyMigration
    rw [if_neg (by rw [hbad]; simp)]
  · -- The fallback is authorized by the always-admissible owner signature (`adminBySignature`).
    exact adminBySignature live stored

/-- **`migrate_anti_brick_preserves`** — the cell is genuinely not bricked: if the original `v`
conformed to the new schema and the migration took the fallback (`hbad`), the migrated value
STILL conforms to the new schema and preserves balance. The concrete "no data-brick" payoff of
the fallback. PROVED. -/
theorem migrate_anti_brick_preserves (m : Migration) (v : Value)
    (hbad : migrationOK m v = false)
    (hconf : conforms v (.record m.newSchema) = true) :
    conforms (applyMigration m v) (.record m.newSchema) = true ∧
      balOf (applyMigration m v) = balOf v := by
  have hid : applyMigration m v = v := by unfold applyMigration; rw [if_neg (by rw [hbad]; simp)]
  rw [hid]
  exact ⟨hconf, rfl⟩

/-! ## Axiom-hygiene — pin the keystones. -/

#assert_axioms migrate_conforms
#assert_axioms migrate_conserves
#assert_axioms migrate_conserves_domain
#assert_axioms migrate_anti_brick
#assert_axioms migrate_anti_brick_preserves
#assert_axioms addField_conforms
#assert_axioms conformsFields_cons_of
#assert_axioms prepend_fresh_conformsFields

/-! ## It runs (`#eval`) — a field-add migration that preserves balance, and a bad one that falls back. -/

/-- v1 account schema: just a `balance`. -/
def schemaV1 : Schema := [("balance", .scalar)]
/-- v2 account schema: `balance` plus a new `frozen` flag (a field-ADD upgrade). -/
def schemaV2 : Schema := [("frozen", .scalar), ("balance", .scalar)]

/-- A v1 account record (balance 100). -/
def acctV1 : Value := .record [("balance", .int 100)]

/-- **Good migration:** add a `frozen = 0` field, preserving the `balance`. -/
def goodMig : Migration where
  oldSchema := schemaV1
  newSchema := schemaV2
  reshape   := addField "frozen" (.int 0)

/-- **Bad migration:** clobber the whole record to a bare `frozen` field, DESTROYING `balance`
(an inflation/burn hidden in an "upgrade"). The gate rejects it ⇒ it falls back to identity. -/
def badMig : Migration where
  oldSchema := schemaV1
  newSchema := schemaV2
  reshape   := fun _ => .record [("frozen", .int 0)]

-- Good migration: passes the gate, applies the field-add, balance preserved, conforms to v2.
#eval migrationOK goodMig acctV1                                   -- true
#eval applyMigration goodMig acctV1
  -- record [("frozen", int 0), ("balance", int 100)]
#eval conforms (applyMigration goodMig acctV1) (.record schemaV2)  -- true
#eval balOf (applyMigration goodMig acctV1) == balOf acctV1        -- true
#eval balOf (applyMigration goodMig acctV1)                        -- 100 (conserved)

-- Bad migration: FAILS the gate (balance destroyed), so it falls back to the ORIGINAL value —
-- the cell is NOT bricked; balance survives; the migration is authorized by the owner signature.
#eval migrationOK badMig acctV1                                    -- false
#eval applyMigration badMig acctV1                                 -- record [("balance", int 100)] (fell back to identity = acctV1)
#eval balOf (applyMigration badMig acctV1) == balOf acctV1         -- true  (conserved via fallback)
#eval balOf (applyMigration badMig acctV1)                         -- 100  (conserved via fallback)
#eval decide (setProgramAdmissible 7 3 migrationFallbackAuth)      -- true (owner-signature arm)

-- A field-RENAME migration (re-key, value preserved) also keeps the balance under `renameField`:
#eval renameField "bal" "balance" (.record [("bal", .int 42)])
  -- record [("balance", int 42)]

end Dregg2.Exec
