/-
# Dregg2.Deos.Affordance — an agent fires only the affordances its caps authorize (leg 4 of the crown).

`docs/deos/DEOS.md` §"the verified-deos program", target 4 (**Affordance soundness**):

  > A cell-affordance interaction is a verified turn; prove an agent can only fire affordances its caps
  > authorize (gateOK on the affordance effect-template), and the post-state surface binds the attested
  > root.

`docs/deos/DEOS.md` §"htmx on crack": a `CellAffordance` is a named `dregg_turn::Effect` template, "the
render/fire gate is the GENUINE `is_attenuation` (`required ⊆ held`, the proven lattice — not a new
gate)", "an unauthorized fire is REFUSED in-band, an authorized one yields a verified-turn
`AffordanceIntent`". The realization is `starbridge-web-surface::affordance` (15 module tests); this is
the proof.

## ⚑ FLAG DAY 2026-08-07 — the attested-root binding was an IDENTITY CARRIER; `fire` changed shape.

The previous `fire` built its receipt as `let _receipt : Receipt := mkReceipt 0 s post aff.name` —
**underscore-prefixed and DISCARDED** — and then set the surface's `boundRoot := post` from the same
free `post` the caller handed in. `firedSurface_binds_attested_root` re-derived
`mkReceipt 0 s post aff.name` *in its own statement* and concluded `boundRoot = that.newCommit`, i.e.
**`post = post`**. Nothing was attested. Three further defects rode along:

  * `effectsHash := aff.name` — the receipt committed to the affordance's **display name**, not to the
    effect. Two affordances with one name produced byte-identical receipts (see
    `docs/audit` / the display-name-collision class); the thing that fired was not bound at all.
  * `prevHash := 0` (= `genesisSentinel`) — **every** fire's receipt claimed to be genesis, so no fire
    could ever be linked into the receipt chain the tamper-evidence law speaks about.
  * `post : Nat` was a **free parameter the verifier consumed** — an over-naming, in the sense of
    `minted-over-naming-migrates-into-transcript-geometry`: the caller chose the attested root.

The repair: `fire` takes a `FireCtx` (a §8 **effect digest**, the prior chain head's digest, and the
pre/post commitments), **produces a real `Receipt` and RETURNS it** in the `AffordanceIntent`, and the
post-state surface binds **that receipt's** `newCommit`. Everything downstream of `fire`
(`Deos.GatedAffordance`, `Deos.Reactive`) re-emits against the new shape; the old `(s post : Nat)`
argument pair no longer exists and a call in the old shape does not typecheck.

## What is proven

  * `fireGate required held` — the affordance gate: `required ⊆ held` (the genuine `is_attenuation`,
    decidable). Reflexive; transitive along projection.
  * `fire aff held fc` — the fire dispatch: iff `held` authorizes `aff.required`, yields an
    `AffordanceIntent` carrying the REAL effect, the RECEIPT the turn produced, and the post-state
    surface bound to that receipt's `newCommit`; otherwise `none` (refused in-band).
  * `fire_authorized_iff` — ⓘ **DEFINITIONAL** (it is `(if c then some _ else none).isSome ↔ c`, the
    shape of `fire`). The content lives one step out, in `fire_authorized_iff_subset`.
  * **`fire_authorized_iff_subset` (KEYSTONE)** — a fire commits IFF `aff.required ⊆ held`, the
    ORDER RELATION on rights (not the boolean gate restated). Rides `fireGate_iff_subset`, which is a
    real `List.all`/membership proof, not `rfl`.
  * **`firedSurface_binds_attested_root`** — the post-state surface's `boundRoot` equals
    **`intent.receipt.newCommit`** — the receipt the fire ACTUALLY produced and RETURNED, not one the
    statement re-derives.
  * **`firedReceipt_commits_to_effect`** — the receipt's `effectsHash` is the §8 digest of the effect
    that fired (never the display name).
  * **`firedReceipt_determines_effect` (the attestation with teeth)** — under the NAMED §8 hypothesis
    that the effect digest is injective, two committed fires with the SAME receipt fired the SAME
    effect. The receipt binds *what happened*. `determines_effect_needs_injectivity` proves the
    hypothesis is load-bearing: with a degenerate (constant) digest the conclusion is FALSE.
  * **`firedReceipt_extends_chain`** — the produced receipt links onto a well-linked chain
    (`Exec.Receipts.wellLinked_append`), so a fire is an append to the real receipt log rather than a
    free-floating genesis claim.
  * `unauthorized_fire_refused` / `unauthorized_fire_no_surface` — fail-closed, anti-ghost.
  * `projectFor_monotone` / `projectFor_all_fireable` — progressive enhancement → progressive
    ATTENUATION.

## Non-vacuity (registered, `metatheory/CLAIMS.md` §Deos)

`firedSurface_binds_attested_root_satisfiable` (fires: a concrete committed fire, root ≠ pre-state,
effectsHash = the real effect's digest) · `firedReceipt_determines_effect_bites` (bites: two
affordances with DIFFERENT effects produce DIFFERENT receipts) · `determines_effect_needs_injectivity`
(the §8 hypothesis is not droppable).

Discipline: axiom-clean (`#assert_all_clean` at the close). The fire gate IS `required ⊆ held`; the
attested root IS the EXISTING `Receipts.Receipt.newCommit`. No new gate, no new commitment. The effect
digest is a §8 portal (a hypothesis, never a Lean axiom), exactly as `Receipt`'s chain digest `H` is.
-/
import Dregg2.Exec.Receipt
import Dregg2.Authority.Positional
import Dregg2.Tactics

namespace Dregg2.Deos.Affordance

open Dregg2.Authority (Auth)
open Dregg2.Exec.Receipts (Receipt ReceiptChain mkReceipt wellLinked wellLinked_append
  genesisSentinel)

/-! ## §1 — The affordance gate IS `is_attenuation` (`required ⊆ held`).

The render/fire gate is the GENUINE `is_attenuation` — `required ⊆ held`, the SAME lattice the cap
crown proves (`Dregg2.Exec.attenuate_subset` narrows ALONG it; here it GATES). We use the decidable
`required.all (held.contains ·)` form and bridge it to `List.Subset`. NO new gate. -/

/-- **`fireGate required held`** — may an agent holding `held` rights fire an affordance requiring
`required`? Iff `required ⊆ held` — the genuine `is_attenuation` (`required ⊆ held`, the Rust
`cell/src/capability.rs:461` order), decidable as `required.all (held.contains ·)`. This is NOT a new
gate: it is the SAME subset order the cap crown's attenuation narrows along. -/
def fireGate (required held : List Auth) : Bool := required.all (fun a => held.contains a)

/-- **The gate IS the subset relation** — `fireGate required held = true ↔ required ⊆ held`. Ties the
decidable gate to the `List.Subset` the lattice laws speak in, so the affordance gate is literally
`is_attenuation`, not a look-alike. This is the file's one genuinely non-definitional gate lemma; every
"an agent fires only what it may" statement below routes through it. -/
theorem fireGate_iff_subset (required held : List Auth) :
    fireGate required held = true ↔ required ⊆ held := by
  unfold fireGate
  constructor
  · intro hg a ha
    have := List.all_eq_true.mp hg a ha
    simpa [List.contains_eq_mem] using this
  · intro hsub
    rw [List.all_eq_true]
    intro a ha
    simpa [List.contains_eq_mem] using hsub ha

/-- **The gate is REFLEXIVE** — an agent holding exactly the required rights may fire (`fireGate r r`).
An affordance is always fireable by the holder of precisely its rights. -/
theorem fireGate_refl (required : List Auth) : fireGate required required = true := by
  rw [fireGate_iff_subset]

/-- **The gate is TRANSITIVE along projection** — if `held₁ ⊆ held₂` (a viewer holds less than a
grantor) and the viewer can fire (`fireGate required held₁`), the grantor can too. So the fireable set
only shrinks under attenuation — the bridge to the per-viewer projection (§5). -/
theorem fireGate_trans {required held₁ held₂ : List Auth}
    (h12 : held₁ ⊆ held₂) (hfire : fireGate required held₁ = true) :
    fireGate required held₂ = true := by
  rw [fireGate_iff_subset] at hfire ⊢
  exact List.Subset.trans hfire h12

/-! ## §2 — A `CellAffordance`: a named effect-template carrying a REAL effect.

A `CellAffordance` is the deos "htmx on crack" element — a named `dregg_turn::Effect` template, gated
by `required` rights. The effect type `φ` is abstract (so ANY real effect fits — the
`starbridge-web-surface` realization carries a `dregg_turn::Effect`); the affordance carries a REAL
`effect : φ`, not a stand-in. -/

variable {φ : Type}

/-- **`CellAffordance φ`** — a named, cap-gated effect-template: the rights `required` to fire it, plus
the REAL `effect : φ` it carries (the `dregg_turn::Effect`). The "button" of the deos surface — and
who may press it is decided by `required ⊆ held`, not a session cookie.

⚠ `name` is a DISPLAY LABEL and nothing else. It is deliberately NOT what the receipt commits to (see
`FireCtx.effectDigest`): display names collide, and the previous version of this module committed the
name in place of the effect. -/
structure CellAffordance (φ : Type) where
  /-- The rights an agent must hold to fire this affordance (the `is_attenuation` template). -/
  required : List Auth
  /-- The REAL effect this affordance fires — abstract so any `dregg_turn::Effect` fits. -/
  effect   : φ
  /-- A display name (the affordance label shown in the surface). NOT an identity; see the note. -/
  name     : Nat
deriving DecidableEq

/-- **`FireCtx φ`** — everything a verified turn needs that the affordance itself does not carry.
Threaded, not invented: the caller supplies the turn context, and `fire` builds the receipt from it.

  * `effectDigest` — the **§8 portal**: a commitment to the effect that fires. Exactly the same kind of
    object as `Dregg2.Exec.Receipts`'s chain digest `H` (a parameter, with its collision-resistance
    entering downstream theorems as a NAMED `Function.Injective` hypothesis — never a Lean axiom).
  * `prevDigest` — `H` of the receipt this turn chains onto (`genesisSentinel` only at genesis).
  * `pre` / `post` — the state commitments before/after the turn (`oldCommit` / `newCommit`). -/
structure FireCtx (φ : Type) where
  /-- The §8 effect-commitment used as the receipt's `effectsHash`. -/
  effectDigest : φ → Nat
  /-- `H` of the prior chain head — the `previous_receipt_hash` this turn links onto. -/
  prevDigest   : Nat
  /-- The state commitment BEFORE the turn (the receipt's `oldCommit`). -/
  pre          : Nat
  /-- The state commitment AFTER the turn (the receipt's `newCommit`). -/
  post         : Nat

/-- **`FiredSurface φ`** — the post-state surface a committed fire yields: the REAL effect that fired
plus the attested root it bound. The `boundRoot` is set from the PRODUCED receipt's `newCommit`
(`fire`, §3) — it is not a field the caller fills in. -/
structure FiredSurface (φ : Type) where
  /-- The effect that actually fired (the affordance's real effect, verbatim). -/
  firedEffect : φ
  /-- The attested root the post-state binds: the produced receipt's `newCommit`. -/
  boundRoot   : Nat
deriving DecidableEq

/-- **`AffordanceIntent φ`** — the verified-turn intent an authorized fire produces: the affordance
that fired, **the receipt the turn produced**, and the resulting attested post-state surface.
(`docs/deos/DEOS.md`: "an authorized one yields a verified-turn `AffordanceIntent`".)

⚑ The `receipt` field is the flag-day repair: the previous version discarded the receipt into a
`let _receipt`, which is why its root-binding theorem reduced to `post = post`. -/
structure AffordanceIntent (φ : Type) where
  /-- The affordance that fired. -/
  affordance : CellAffordance φ
  /-- The receipt this verified turn PRODUCED — returned, not discarded. -/
  receipt    : Receipt
  /-- The attested post-state surface it produced. -/
  surface    : FiredSurface φ
deriving DecidableEq

/-! ## §3 — `fire`: the cap-gated, receipt-producing dispatch.

`fire aff held fc` runs the affordance ONLY when `held` authorizes `aff.required` (`fireGate`), and on
commit BUILDS the verified turn's receipt from `fc` — linking onto `fc.prevDigest`, carrying
`fc.pre → fc.post`, and committing to `fc.effectDigest aff.effect` — then binds the post-state surface
to THAT receipt's `newCommit`. An unauthorized fire is REFUSED in-band (`none`). -/

/-- **`receiptOf fc aff`** — the receipt a fire of `aff` under `fc` produces: `prevHash = fc.prevDigest`
(the append-only link), `oldCommit → newCommit = fc.pre → fc.post`, and `effectsHash =
fc.effectDigest aff.effect` — a commitment to the EFFECT, not to `aff.name`. -/
def receiptOf (fc : FireCtx φ) (aff : CellAffordance φ) : Receipt :=
  mkReceipt fc.prevDigest fc.pre fc.post (fc.effectDigest aff.effect)

/-- **`fire aff held fc`** — fire affordance `aff` for an agent holding `held` rights in turn context
`fc`. IF `fireGate aff.required held` (the agent's caps authorize the affordance), yields `some` of the
verified-turn `AffordanceIntent` carrying the produced receipt and a surface bound to that receipt's
`newCommit`; ELSE `none` (refused in-band). The `gateOK`-on-the-affordance-template dispatch. -/
def fire (aff : CellAffordance φ) (held : List Auth) (fc : FireCtx φ) :
    Option (AffordanceIntent φ) :=
  if fireGate aff.required held then
    some { affordance := aff,
           receipt := receiptOf fc aff,
           surface := { firedEffect := aff.effect, boundRoot := (receiptOf fc aff).newCommit } }
  else
    none

/-! ## §4 — TARGET 4: an agent fires ONLY what its caps authorize, and the surface binds the root. -/

/-- ⓘ **DEFINITIONAL — this is the SHAPE of `fire`, not a security property.** `fire` is
`if fireGate … then some _ else none`, so this theorem is `(if c then some _ else none).isSome ↔ c`.
It is true, it is `#assert_axioms`-clean, and it says only that the `if` is the `if`. **The content is
`fire_authorized_iff_subset`** (immediately below), which relates the dispatch to the ORDER on rights
through the non-definitional `fireGate_iff_subset`. Kept because downstream modules
(`Deos.GatedAffordance`, `Deos.Reactive`) route their own gate proofs through it. -/
theorem fire_authorized_iff (aff : CellAffordance φ) (held : List Auth) (fc : FireCtx φ) :
    (fire aff held fc).isSome = true ↔ fireGate aff.required held = true := by
  unfold fire
  by_cases hg : fireGate aff.required held = true
  · rw [if_pos hg]; exact ⟨fun _ => hg, fun _ => rfl⟩
  · have hgf : fireGate aff.required held = false := by
      cases hb : fireGate aff.required held with
      | true => exact absurd hb hg
      | false => rfl
    rw [if_neg hg]
    constructor
    · intro h; simp only [Option.isSome_none, Bool.false_eq_true] at h
    · intro h; rw [hgf] at h; exact absurd h (by simp)

/-- **THE KEYSTONE — `fire_authorized_iff_subset`.** A fire COMMITS if and only if the affordance's
required rights are a SUBSET of the rights the agent holds — the `is_attenuation` ORDER itself, not the
boolean gate restated. Both polarities: an agent whose held rights cover `required` fires; one whose do
not is REFUSED. So an agent can fire ONLY the affordances its caps authorize — target 4's first clause,
against the lattice the cap crown proves on. (Routes through `fireGate_iff_subset`, whose proof is a
real `List.all`/membership argument.) -/
theorem fire_authorized_iff_subset (aff : CellAffordance φ) (held : List Auth) (fc : FireCtx φ) :
    (fire aff held fc).isSome = true ↔ aff.required ⊆ held :=
  (fire_authorized_iff aff held fc).trans (fireGate_iff_subset aff.required held)

/-- **AN UNAUTHORIZED FIRE IS REFUSED** (the negative tooth, explicit): if the agent does NOT hold the
required rights, `fire` returns `none` — no turn, no receipt, no surface, fail-closed. -/
theorem unauthorized_fire_refused (aff : CellAffordance φ) (held : List Auth) (fc : FireCtx φ)
    (hunauth : fireGate aff.required held = false) :
    fire aff held fc = none := by
  unfold fire; rw [if_neg (by rw [hunauth]; decide)]

/-- **A COMMITTED FIRE CARRIES THE REAL EFFECT** — when `fire` commits, the resulting intent's surface
fires the affordance's REAL effect verbatim (not a stand-in). -/
theorem fire_carries_real_effect (aff : CellAffordance φ) (held : List Auth) (fc : FireCtx φ)
    (intent : AffordanceIntent φ) (h : fire aff held fc = some intent) :
    intent.surface.firedEffect = aff.effect := by
  unfold fire at h
  by_cases hg : fireGate aff.required held = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **A COMMITTED FIRE RETURNS THE RECEIPT IT PRODUCED** — the intent's `receipt` is exactly
`receiptOf fc aff`. This is the fact the previous version could not state, because the receipt was
discarded into a `let _receipt`. -/
theorem fire_returns_receipt (aff : CellAffordance φ) (held : List Auth) (fc : FireCtx φ)
    (intent : AffordanceIntent φ) (h : fire aff held fc = some intent) :
    intent.receipt = receiptOf fc aff := by
  unfold fire at h
  by_cases hg : fireGate aff.required held = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **THE POST-STATE SURFACE BINDS THE ATTESTED ROOT** — target 4's second clause, repaired. When
`fire` commits, the surface's `boundRoot` EQUALS **the `newCommit` of the receipt the intent carries** —
the receipt this fire produced and returned, not one the statement re-derives from the same free
variable. So the fragment the witness-graph records is pinned to the commitment of the turn that
actually ran.

⚠ **Say what this is and is not.** It is still a STRUCTURAL AGREEMENT between two fields of the
returned intent, and its proof is `rfl` once the `some` is destructed. What changed is that it is now
**refutable**: an implementation that bound `fc.pre`, or a root the receipt did not produce, makes it
FALSE — whereas the old statement re-derived its own right-hand side from the caller's free `post` and
was satisfied by an implementation with no receipt at all. The load-bearing content of "the surface
binds an ATTESTED root" lives in the three theorems below it —
`firedReceipt_commits_to_effect`, `firedReceipt_extends_chain`, `firedReceipt_determines_effect` —
which say what the receipt commits to, that it is linked, and that it pins what fired. -/
theorem firedSurface_binds_attested_root (aff : CellAffordance φ) (held : List Auth) (fc : FireCtx φ)
    (intent : AffordanceIntent φ) (h : fire aff held fc = some intent) :
    intent.surface.boundRoot = intent.receipt.newCommit := by
  unfold fire at h
  by_cases hg : fireGate aff.required held = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **THE RECEIPT COMMITS TO THE EFFECT THAT FIRED** — its `effectsHash` is the §8 digest of
`aff.effect`. ⚠ The previous version put `aff.name` here: a DISPLAY LABEL, which collides across
affordances, so the receipt said nothing about what happened. -/
theorem firedReceipt_commits_to_effect (aff : CellAffordance φ) (held : List Auth) (fc : FireCtx φ)
    (intent : AffordanceIntent φ) (h : fire aff held fc = some intent) :
    intent.receipt.effectsHash = fc.effectDigest aff.effect := by
  rw [fire_returns_receipt aff held fc intent h]; rfl

/-- **THE RECEIPT CHAINS FROM THE PRE-STATE** — `oldCommit = fc.pre` and `prevHash = fc.prevDigest`.
The attestation is anchored at both ends: the state it started from and the receipt it links onto. -/
theorem firedReceipt_anchors (aff : CellAffordance φ) (held : List Auth) (fc : FireCtx φ)
    (intent : AffordanceIntent φ) (h : fire aff held fc = some intent) :
    intent.receipt.oldCommit = fc.pre ∧ intent.receipt.prevHash = fc.prevDigest := by
  rw [fire_returns_receipt aff held fc intent h]; exact ⟨rfl, rfl⟩

/-- **THE FIRE'S RECEIPT EXTENDS THE REAL CHAIN** — given a well-linked chain whose head digests to
`fc.prevDigest`, prepending the produced receipt keeps it well-linked
(`Dregg2.Exec.Receipts.wellLinked_append`). So an affordance fire is an APPEND to the append-only
receipt log, inheriting `chain_tamper_evident`; it is not a free-floating genesis claim. ⚠ The previous
version hard-coded `prevHash := 0 = genesisSentinel`, under which this statement is unprovable for any
non-empty chain (`HFresh` forbids it). -/
theorem firedReceipt_extends_chain {H : Receipt → Nat}
    (aff : CellAffordance φ) (held : List Auth) (fc : FireCtx φ)
    (intent : AffordanceIntent φ) (h : fire aff held fc = some intent)
    (head : Receipt) (tail : ReceiptChain)
    (hwl : wellLinked H (head :: tail)) (hlink : fc.prevDigest = H head) :
    wellLinked H (intent.receipt :: head :: tail) := by
  have hprev : intent.receipt.prevHash = fc.prevDigest := (firedReceipt_anchors aff held fc intent h).2
  exact wellLinked_append hwl (hprev.trans hlink)

/-- **THE RECEIPT DETERMINES WHAT FIRED** (the attestation, with teeth). Under the NAMED §8 hypothesis
that the effect digest is injective — the same kind of obligation `chain_tamper_evident` carries as
`HInj`, discharged by the circuit, never a Lean axiom — two committed fires in the SAME turn context
that produced the SAME receipt fired the SAME effect. So a receipt cannot be re-presented as evidence
of a different interaction: the post-state surface's attested root is bound to *what happened*.

`determines_effect_needs_injectivity` (§6) exhibits a degenerate digest under which this is FALSE, so
the hypothesis is genuinely load-bearing. -/
theorem firedReceipt_determines_effect (fc : FireCtx φ)
    (hinj : Function.Injective fc.effectDigest)
    (aff₁ aff₂ : CellAffordance φ) (held₁ held₂ : List Auth)
    (i₁ i₂ : AffordanceIntent φ)
    (h₁ : fire aff₁ held₁ fc = some i₁) (h₂ : fire aff₂ held₂ fc = some i₂)
    (heq : i₁.receipt = i₂.receipt) :
    aff₁.effect = aff₂.effect := by
  have e₁ : i₁.receipt.effectsHash = fc.effectDigest aff₁.effect :=
    firedReceipt_commits_to_effect aff₁ held₁ fc i₁ h₁
  have e₂ : i₂.receipt.effectsHash = fc.effectDigest aff₂.effect :=
    firedReceipt_commits_to_effect aff₂ held₂ fc i₂ h₂
  exact hinj (e₁.symm.trans (congrArg Receipt.effectsHash heq |>.trans e₂))

/-- **THE BOUND ROOT IS THE NEW STATE, NOT THE OLD** (non-vacuity of the binding): when the turn moved
the commitment (`fc.post ≠ fc.pre`), the surface's bound root genuinely DIFFERS from the pre-state. So
the surface binds the POST-state, not a relabelled pre-state. -/
theorem firedSurface_root_is_new (aff : CellAffordance φ) (held : List Auth) (fc : FireCtx φ)
    (intent : AffordanceIntent φ) (h : fire aff held fc = some intent) (hne : fc.post ≠ fc.pre) :
    intent.surface.boundRoot ≠ fc.pre := by
  rw [firedSurface_binds_attested_root aff held fc intent h,
      fire_returns_receipt aff held fc intent h]
  exact hne

/-- **AN UNAUTHORIZED FIRE BINDS NO ROOT** (the anti-ghost): an unauthorized fire yields `none`, so
there is NO receipt and NO surface — an agent who lacks the rights cannot forge a post-state surface or
its attested root. Confinement before relation: no authority ⇒ no attestation. -/
theorem unauthorized_fire_no_surface (aff : CellAffordance φ) (held : List Auth) (fc : FireCtx φ)
    (hunauth : fireGate aff.required held = false) :
    ∀ intent : AffordanceIntent φ, fire aff held fc ≠ some intent := by
  intro intent
  rw [unauthorized_fire_refused aff held fc hunauth]
  exact fun h => absurd h (by simp)

/-! ## §5 — PROGRESSIVE ENHANCEMENT → PROGRESSIVE ATTENUATION (the per-viewer affordance set).

`starbridge-web-surface`'s `project_for` returns the affordances a viewer may fire — and as a viewer's
authority shrinks, that set only shrinks (monotone via `fireGate`). Two viewers over one surface
diverge by exactly what their caps authorize. -/

/-- **`projectFor held affs`** — the affordances a viewer holding `held` rights may fire: those whose
`required ⊆ held` (the per-viewer `project_for`). Progressive enhancement becomes progressive
attenuation — a viewer sees exactly the affordances its caps authorize. -/
def projectFor (held : List Auth) (affs : List (CellAffordance φ)) : List (CellAffordance φ) :=
  affs.filter (fun aff => fireGate aff.required held)

/-- **THE PROJECTION IS MONOTONE** — a viewer holding FEWER rights (`held₁ ⊆ held₂`) is offered a
SUBSET of the affordances the more-authorized viewer is. So progressive attenuation never GROWS the
fireable set as authority shrinks; two viewers over one surface diverge by exactly their authority.
(Via `fireGate_trans`: anything the weaker viewer can fire, the stronger can too.) -/
theorem projectFor_monotone {held₁ held₂ : List Auth} (h12 : held₁ ⊆ held₂)
    (affs : List (CellAffordance φ)) :
    projectFor held₁ affs ⊆ projectFor held₂ affs := by
  intro aff ha
  unfold projectFor at ha ⊢
  rw [List.mem_filter] at ha ⊢
  exact ⟨ha.1, fireGate_trans h12 ha.2⟩

/-- **EVERY PROJECTED AFFORDANCE IS FIREABLE** — a viewer is only ever offered affordances it can
actually fire (`fire` commits for each one in `projectFor held affs`). The projected set is sound: no
offered-but-refused buttons. -/
theorem projectFor_all_fireable (held : List Auth) (affs : List (CellAffordance φ))
    (aff : CellAffordance φ) (fc : FireCtx φ) (hmem : aff ∈ projectFor held affs) :
    (fire aff held fc).isSome = true := by
  unfold projectFor at hmem
  rw [List.mem_filter] at hmem
  rw [fire_authorized_iff]
  exact hmem.2

/-! ## §6 — NON-VACUITY: NAMED companions (fires / bites / the §8 hypothesis is load-bearing).

`docs/audit/NON-VACUITY-MANIFEST.md` discipline: a green only counts if it reds when the thing it
guards breaks. Each companion below is a NAMED theorem (never a `def`, never a bare `#guard`), so it is
registrable and `#assert_axioms`-accountable. -/

section Witnesses

/-- A concrete effect type for the witnesses: a tag carrying a Nat payload. -/
inductive DemoEffect where | transfer (amt : Nat) | post (msg : Nat)
deriving DecidableEq, Repr

/-- A concrete **injective** effect digest — the §8 obligation MET (odd/even domain separation). -/
def demoDigest : DemoEffect → Nat
  | .transfer a => 2 * a
  | .post m     => 2 * m + 1

/-- The demo digest really is injective — so `firedReceipt_determines_effect`'s hypothesis is
SATISFIABLE (a floor that no instance satisfies constrains nothing). -/
theorem demoDigest_injective : Function.Injective demoDigest := by
  intro a b h
  cases a with
  | transfer x =>
    cases b with
    | transfer y => simp only [demoDigest] at h; simp only [DemoEffect.transfer.injEq]; omega
    | post m     => simp only [demoDigest] at h; exact absurd h (by omega)
  | post x =>
    cases b with
    | transfer y => simp only [demoDigest] at h; exact absurd h (by omega)
    | post m     => simp only [demoDigest] at h; simp only [DemoEffect.post.injEq]; omega

/-- An affordance requiring `{write}` to fire a transfer (the "send" button). -/
def sendAff : CellAffordance DemoEffect := { required := [Auth.write], effect := .transfer 50, name := 1 }
/-- An affordance requiring `{read}` to fire a (read-only) post (the "view" button). -/
def viewAff : CellAffordance DemoEffect := { required := [Auth.read], effect := .post 7, name := 2 }

/-- An agent holding only `{read}` — may fire the view button, NOT the send button. -/
def readerHeld : List Auth := [Auth.read]
/-- An agent holding `{read, write}` — may fire both. -/
def writerHeld : List Auth := [Auth.read, Auth.write]

/-- A concrete turn context: an injective digest, chaining onto digest `9`, moving `100 → 70`. -/
def demoCtx : FireCtx DemoEffect :=
  { effectDigest := demoDigest, prevDigest := 9, pre := 100, post := 70 }

/-- ⚠ A DEGENERATE turn context — the §8 effect digest is CONSTANT, i.e. the obligation is UNMET. -/
def collidingCtx : FireCtx DemoEffect :=
  { effectDigest := fun _ => 0, prevDigest := 9, pre := 100, post := 70 }

/-- **FIRES (non-vacuity of `firedSurface_binds_attested_root`).** A concrete authorized fire COMMITS,
and its conclusion is EXERCISED on that instance: the surface's bound root is the produced receipt's
`newCommit`, the receipt commits to the REAL effect's digest (not to `aff.name = 1`), it anchors at the
pre-state and the prior chain digest, and the bound root is genuinely NOT the pre-state. Every conjunct
is about the receipt the fire RETURNED. -/
theorem firedSurface_binds_attested_root_satisfiable :
    ∃ intent : AffordanceIntent DemoEffect,
      fire sendAff writerHeld demoCtx = some intent
        ∧ intent.surface.boundRoot = intent.receipt.newCommit
        ∧ intent.receipt.effectsHash = demoDigest (DemoEffect.transfer 50)
        ∧ intent.receipt.effectsHash ≠ sendAff.name
        ∧ intent.receipt.oldCommit = demoCtx.pre
        ∧ intent.receipt.prevHash = demoCtx.prevDigest
        ∧ intent.receipt.prevHash ≠ genesisSentinel
        ∧ intent.surface.boundRoot ≠ demoCtx.pre := by
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **BITES (the binding is two-valued).** Two affordances with DIFFERENT effects, fired in the SAME
turn context by the SAME viewer, produce DIFFERENT receipts — so `firedReceipt_determines_effect` is
refutable in the only way that matters: swap the effect and the attestation changes. (Under the OLD
`effectsHash := aff.name` these two would still differ only because their *names* differ — rename
either and the receipts collide while the effects do not. The digest closes that.) -/
theorem firedReceipt_determines_effect_bites :
    ∃ i₁ i₂ : AffordanceIntent DemoEffect,
      fire sendAff writerHeld demoCtx = some i₁
        ∧ fire viewAff writerHeld demoCtx = some i₂
        ∧ i₁.receipt ≠ i₂.receipt
        ∧ i₁.surface.firedEffect ≠ i₂.surface.firedEffect := by
  refine ⟨_, _, rfl, rfl, ?_, ?_⟩ <;> decide

/-- **THE §8 HYPOTHESIS IS LOAD-BEARING** (`firedReceipt_determines_effect` is NOT PROVABLE without
`hinj`). Under a DEGENERATE constant effect digest, two committed fires of affordances with DIFFERENT
effects produce IDENTICAL receipts — so the conclusion `aff₁.effect = aff₂.effect` is FALSE. The
injectivity obligation cannot be dropped, and a digest that fails it makes the attestation meaningless
rather than merely weaker. -/
theorem determines_effect_needs_injectivity :
    ∃ i₁ i₂ : AffordanceIntent DemoEffect,
      fire sendAff writerHeld collidingCtx = some i₁
        ∧ fire viewAff readerHeld collidingCtx = some i₂
        ∧ i₁.receipt = i₂.receipt
        ∧ sendAff.effect ≠ viewAff.effect := by
  refine ⟨_, _, rfl, rfl, ?_, ?_⟩ <;> decide

/-- **THE GATE BITES, BOTH POLARITIES** (non-vacuity of `fire_authorized_iff_subset`): the reader
CANNOT fire the write-gated send (refused in-band, nothing produced) but CAN fire the read-gated view;
the writer can fire both. Progressive attenuation is exercised too: the reader is offered exactly one
affordance, the writer both. -/
theorem fire_authorized_iff_subset_satisfiable :
    (fire sendAff readerHeld demoCtx).isNone = true
      ∧ (fire sendAff writerHeld demoCtx).isSome = true
      ∧ (fire viewAff readerHeld demoCtx).isSome = true
      ∧ (projectFor readerHeld [sendAff, viewAff]).length = 1
      ∧ (projectFor writerHeld [sendAff, viewAff]).length = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

#assert_all_clean [
  demoDigest_injective,
  firedSurface_binds_attested_root_satisfiable,
  firedReceipt_determines_effect_bites,
  determines_effect_needs_injectivity,
  fire_authorized_iff_subset_satisfiable
]

end Witnesses

/-! ## §7 — Axiom hygiene. -/

#assert_all_clean [
  fireGate_iff_subset,
  fireGate_refl,
  fireGate_trans,
  fire_authorized_iff,
  fire_authorized_iff_subset,
  unauthorized_fire_refused,
  fire_carries_real_effect,
  fire_returns_receipt,
  firedSurface_binds_attested_root,
  firedReceipt_commits_to_effect,
  firedReceipt_anchors,
  firedReceipt_extends_chain,
  firedReceipt_determines_effect,
  firedSurface_root_is_new,
  unauthorized_fire_no_surface,
  projectFor_monotone,
  projectFor_all_fireable
]

end Dregg2.Deos.Affordance
