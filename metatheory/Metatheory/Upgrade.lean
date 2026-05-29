/-
# Metatheory.Upgrade — the anti-brick `set_program` upgrade law.

This module encodes dregg2's **anti-brick upgrade clause** (`dregg2-multicell-privacy.md §3`):
the #1 thing the design was missing, ADOPTED from Mina's `permissions.ml`.

**The hazard.** dregg2 *will* swap its recursion backend / AIR encoding (the deferred
`RecursionBackend` / `FriRecursionBackend` trait swap; `circuit/src/plonky3_recursion_impl.rs`,
design §7: depth-as-security-parameter, recursion deferrable). The instant that happens, every
live `Circuit{circuit_hash}` cell pinned to the *old* proof system becomes unverifiable —
**bricked**: it can no longer produce a proof its own verifier will accept, so it can never be
upgraded out of the dead state. A sovereign cell stranded forever.

**The fix, grounded in Mina `permissions.ml` (the `set_verification_key` clause, ~line 77).**
Mina's `Verification_key_perm.fallback_to_signature_with_older_version` pins a *transaction/AIR
version* on the `set_verification_key` permission. The rule:

```
set_verification_key =
  ( Auth_required  (* the proof-or-signature authority required *)
  , Mina_numbers.Txn_version.t )   (* the pinned version *)

(* and the check, paraphrased: *)
if stored_txn_version < current_txn_version
then  (* the pinned proof system is STALE: a proof against it can't be trusted/checked *)
      fall back to requiring the OWNER'S SIGNATURE
else  require the configured (proof) authority
```

i.e. **`older_version ⇒ signature_fallback`**: when the cell's pinned version is behind the live
verifier, authorization to `set_program` falls back to a signature by the cell's owner — so a
backend/verifier swap can never strand a sovereign cell. (dregg2's migration is otherwise
*stronger* than Mina's — transparent + conservative + content-hash-preserving, `study-mina-relink §4`.)

**Tie to authority.** A `set_program` is itself an authority-bearing turn: it mutates the cell's
own admissibility coalgebra, so it requires the owner subject / a `control`-conferring cap. We link
to `Metatheory.Authority.Positional`: an admitted upgrade is exactly the `intra` arm of the
`Integrity` case-split (the owner acting on its own object), and the `bySignature` fallback is the
*always-available* owner-edge that keeps that arm reachable.

Spec-first: the data (`AirVersion`, `UpgradeAuth`, `setProgramAdmissible`) is real and computable;
the keystone obligations (`upgrade_never_bricks`, `stale_version_falls_back_to_signature`) are
faithful Props with `sorry` bodies.
-/
import Metatheory.Authority.Positional
import Mathlib.Algebra.Order.Group.Nat

namespace Metatheory.Upgrade

open Metatheory.Authority

/-! ## The pinned proof-system version -/

/-- **`AirVersion`** — the pinned proof-system / AIR (algebraic intermediate representation)
version a cell's verifier expects. Lift of Mina's `Mina_numbers.Txn_version.t` carried by the
`set_verification_key` permission. A cell's `Circuit{circuit_hash}` is sound only against a
verifier of the version it was pinned to; a backend/recursion swap bumps the *live* version. -/
abbrev AirVersion := Nat

/-- **`stale stored live`** — the staleness predicate driving Mina's fallback. The cell's
*stored* (pinned) AIR version is older than the *live* verifier's version, so a proof produced
against the stored proof system can no longer be checked/trusted by the live verifier. This is
exactly Mina's `stored_txn_version < current_txn_version` guard. -/
def stale (stored live : AirVersion) : Prop := stored < live

instance (stored live : AirVersion) : Decidable (stale stored live) :=
  inferInstanceAs (Decidable (stored < live))

/-! ## How a `set_program` is authorized -/

/-- **`UpgradeAuth`** — the authority backing a `set_program` upgrade, mirroring Mina's two
admissible arms for `set_verification_key`:

* `byProof v` — the new program carries a proof against AIR version `v` (the proof arm); admissible
  only when `v` matches the live verifier (a *current*-version proof).
* `bySignature` — the **owner-signature fallback** (`fallback_to_signature_with_older_version`):
  the cell's owner signs the upgrade. Always available to the owner, independent of any proof
  system, so it is the arm that survives every backend swap. -/
inductive UpgradeAuth where
  /-- A proof against the carried AIR version (Mina's `Proof` authority). -/
  | byProof (provedVersion : AirVersion)
  /-- The owner-signature fallback (Mina's `Signature`/`fallback_to_signature…`). -/
  | bySignature
  deriving DecidableEq, Repr

/-! ## Admissibility of a `set_program` turn -/

/-- **`setProgramAdmissible live stored auth`** — a `set_program` turn is admissible iff EITHER
the upgrade carries a **valid current-version proof** (`byProof v` with `v = live`), OR it carries
the **owner's signature** (`bySignature`). This is the disjunction Mina's permission check
computes, and it is *fail-open to the owner*: the signature arm is unconditionally admissible.

The companion `older_version ⇒ signature_fallback` rule (Mina's actual branch) is the lemma
`stale_version_falls_back_to_signature` below: when `stale stored live`, the proof arm against the
stored version is *not* admissible (its version ≠ live), so the only remaining admissible arm is
`bySignature` — the check never silently rejects, it routes to the fallback. -/
def setProgramAdmissible (live _stored : AirVersion) : UpgradeAuth → Prop
  | .byProof v   => v = live              -- a *current*-version proof
  | .bySignature => True                  -- owner-signature fallback, always available

instance (live stored : AirVersion) (auth : UpgradeAuth) :
    Decidable (setProgramAdmissible live stored auth) := by
  cases auth <;> unfold setProgramAdmissible
  · exact inferInstanceAs (Decidable (_ = _))
  · exact inferInstanceAs (Decidable True)

/-- **`adminBySignature`** — the always-true witness that the signature arm is admissible at any
versions. The computable core of the anti-brick guarantee: regardless of `live`/`stored`, the
owner can sign. (Cheap, so proved, not `sorry`'d.) -/
theorem adminBySignature (live _stored : AirVersion) :
    setProgramAdmissible live _stored UpgradeAuth.bySignature := trivial

/-! ## The keystone: no backend swap can brick a cell -/

/-- **`upgrade_never_bricks`** — THE keystone law. For *any* backend/verifier swap, i.e. any pair
of pinned/live AIR versions `stored`, `live` (the recursion backend may bump the live version
arbitrarily — `RecursionBackend`/`FriRecursionBackend`, design §7), there **exists** an admissible
`set_program` authorization. Hence a cell can never become permanently unupgradeable / bricked:
the signature fallback is always a path out.

The honest existential here is non-trivial content: it asserts the admissibility *relation is total
over version pairs*, which is precisely what fails for a naive proof-only permission (where
`stale stored live` would make every `byProof` arm inadmissible and strand the cell). -/
theorem upgrade_never_bricks (live stored : AirVersion) :
    ∃ auth : UpgradeAuth, setProgramAdmissible live stored auth :=
  ⟨UpgradeAuth.bySignature, adminBySignature live stored⟩

/-- **`stale_version_falls_back_to_signature`** — the `older_version ⇒ signature_fallback` rule,
verbatim from Mina's `fallback_to_signature_with_older_version`. When the stored AIR version is
stale (older than the live verifier's), the ONLY admissible authorization is `bySignature`:
the proof arm against any non-live version is inadmissible, so the check **falls back to a
signature rather than silently rejecting**. Two conjuncts:

1. `bySignature` is admissible (the fallback is reachable), and
2. a proof against the *stored* (stale) version is **not** admissible — establishing that the
   fallback is genuinely the operative arm, not a redundant one. -/
theorem stale_version_falls_back_to_signature (live stored : AirVersion)
    (h : stale stored live) :
    setProgramAdmissible live stored UpgradeAuth.bySignature ∧
      ¬ setProgramAdmissible live stored (UpgradeAuth.byProof stored) := by
  refine ⟨trivial, ?_⟩
  -- `setProgramAdmissible … (byProof stored)` reduces to `stored = live`,
  -- which contradicts `stale stored live = stored < live`.
  intro hadm
  simp only [setProgramAdmissible, AirVersion] at hadm
  simp only [stale, AirVersion] at h
  -- `hadm : stored = live` contradicts `h : stored < live`.
  exact absurd hadm (Nat.ne_of_lt h)

/-- **`current_version_admits_proof`** — the complementary (non-stale) branch: when the stored
version is up to date (`stored = live`), a proof against it is admissible without needing the
signature fallback. Together with `stale_version_falls_back_to_signature` this exhausts Mina's
`if stored < current then … else …` branch, showing the disjunction is decidable and total. -/
theorem current_version_admits_proof (live stored : AirVersion)
    (h : stored = live) :
    setProgramAdmissible live stored (UpgradeAuth.byProof stored) := by
  -- The proof arm reduces to `stored = live`, which is exactly `h`.
  unfold setProgramAdmissible
  exact h

/-! ## Link to authority: a `set_program` is an authority-bearing turn -/

/-- **`UpgradeTurn`** — a reified `set_program` turn: it carries the cell's `owner`, the set of
acting `subjects`, the live/stored versions, and the offered `UpgradeAuth`. A `set_program` mutates
the cell's *own* admissibility coalgebra, so it is an authority-bearing turn on the cell-as-object,
to be discharged through the `Integrity` case-split of `Authority.Positional`. -/
structure UpgradeTurn where
  owner    : Label
  subjects : List Label
  live     : AirVersion
  stored   : AirVersion
  auth     : UpgradeAuth

/-- **`ownerHoldsControl caps owner`** — the cell-side precondition that the owner holds a
`control`-conferring cap on itself (a `.node owner` cap, `capAuthConferred = [control]`). A
`set_program` is admissible *as an authority matter* only if the actor holds `control`, exactly
as a `node`/`Control` cap is required in l4v for a self-modifying operation. -/
def ownerHoldsControl (caps : Caps) (owner : Label) : Prop :=
  Cap.node owner ∈ caps owner

/-- **`upgrade_is_intra_authority`** — the link to the integrity case-split. An admitted
`set_program` by the cell's owner is the `intra` arm of `Integrity` (l4v `troa_lrefl`: the owning
subject may make an arbitrary change to its own object — here, swap its own program), provided the
owner is among the acting subjects. The `bySignature` fallback is what keeps this arm *reachable*
across a backend swap: it is the owner's always-available self-edge, so the cell's owner never
loses the authority to re-pin its verifier.

`W`, `P`, `KO`, `p` are the witness/predicate/cell-object parameters of `Integrity`; the `intra`
arm consults no policy edge, so they are unconstrained here. -/
theorem upgrade_is_intra_authority
    {P : Type*} (W : Type*) [Metatheory.Laws.Verifiable P W] {KO : Type*}
    (t : UpgradeTurn) (caps : Caps) (p : KO → KO → P) (ko ko' : KO)
    (hctrl : ownerHoldsControl caps t.owner)
    (hsub  : t.owner ∈ t.subjects)
    (hadm  : setProgramAdmissible t.live t.stored t.auth) :
    Integrity W t.owner t.subjects p ko ko' :=
  -- l4v `troa_lrefl`: the owner acting on its own object is the `intra` arm,
  -- whose only side condition is `owner ∈ subjects` (here `hsub`).
  Integrity.intra hsub

end Metatheory.Upgrade
