/-
# Dregg2.Authority.Intent — the intent face: the ∃-resolver / INVERSE vat boundary.

dregg2's await family has four faces (`Await.lean §4`); this module gives the
*intent* face its own authority-grade development: an **existentially-quantified
hole**. Where the vat boundary (`Authority/Positional.lean`, `Exec/VatBoundary.lean`)
gates a **complete turn crossing OUT** — a proof of what passes — an intent gates the
**MISSING HALF**: a predicate `want : P` on the filler, fired when *any* filler `w : W`
with `Verify want w = true` arrives. The intent is the *inverse* membrane:

  * vat boundary : gates an **outgoing morphism** (a settled turn leaving the vat);
  * intent       : gates an **incoming filler** (`λ(fill satisfying P). effects`).

(`cand-A §3`: "Intent is the inverse boundary: a vat boundary gates a *complete* turn
crossing out; an intent gates the *filler* crossing in." `dregg2 §4`; the intent face
is named in `Await.lean` as Face 3, here developed to its own keystone.)

## THE DESIGN LAW — the asymmetry lives in the TYPES (read this).

The VERIFY/FIND seam (`Laws.lean`) is *sharpest* at the intent. The two sides of the
hole have categorically different status, and that status is carried by their **types**,
not by any runtime flag:

  * **VERIFY a claimed fill is TRACTABLE and IN-TCB.** `Verifiable.Verify : P → W → Bool`
    — a total, decidable function. The cell that owns the intent runs it to *accept or
    reject* a proposed fill. We witness "VERIFY is decidable" by the `Decidable
    (Discharged want w)` instance below: the cell can always decide acceptance.

  * **FIND a fill is UNDECIDABLE and UNTRUSTED.** `Searchable.find : P → Option W` — an
    opaque plugin (the *matcher*). Finding a `w` that satisfies an arbitrary predicate is
    undecidable in general: matching the existential hole is at least higher-order
    unification, which is undecidable (`cand-A §3`: `no_general_matcher` via
    `HOU ⪯ GeneralMatch`, machine-checked in Coq; winner-determination is NP-hard, no
    PTAS). So `find` carries **NO completeness, NO termination, NO `Decidable` promise** —
    it may return `none`, may loop (modelled by `Option`), may even return a *wrong*
    fill. The matcher is a bounded, pluggable, untrusted plugin emitting a checkable
    witness; its only contract is **soundness-by-verification** (`Laws.search_sound`).

The keystone (`intent_fill_verifies`) is that this asymmetry is *safe*: whatever an
untrusted, possibly-adversarial matcher returns, IF the cell's VERIFY accepts it, the
fill genuinely satisfies the predicate. Soundness rests on VERIFY alone; FIND is never
trusted. The `#eval` demos exhibit this against both a correct and an adversarial
matcher.

We do NOT redefine `Verifiable`/`Discharged`/`Searchable`/`find`/`search_sound`/`Await`;
we *import* and build the intent keystone on top of them.
-/
import Dregg2.Laws
import Dregg2.Await
import Dregg2.Authority.Positional

namespace Dregg2.Authority

open Dregg2.Laws
open Dregg2.Await (intent)

universe u

/-! ## 1. The intent — an existentially-quantified hole over the verify side. -/

/-- **`Intent P W` — an existentially-quantified hole.** It carries only its *shape*:
the predicate `want : P` that any filler must discharge. It is *not* a named promise to a
specified party (that is `zkpromise`/`discharge`, `Await.lean` Faces 1–2) — it fires for
*any* `w : W` with `Verify want w = true`. This is the structural minimum of the intent
face; the captured one-shot continuation lives on `Await.intent` (Face 3), to which this
connects via `ofAwait`/`toAwait` below. -/
structure Intent (P : Type u) (W : Type u) where
  /-- The hole's shape: the predicate any incoming filler must satisfy. -/
  want : P

/-- **`Intent.Fires i`** — the existential firing condition: the intent resolves exactly
when *there exists* a filler discharging its predicate. This is the `∃`-resolver
semantics ("a hole that fires when filled") stated over the `Laws.Discharged` verify
side — deliberately a `Prop` (it asserts existence), NOT a `Bool` (deciding it is the
undecidable FIND problem, not the tractable VERIFY problem). -/
def Intent.Fires [Verifiable P W] (i : Intent P W) : Prop :=
  ∃ w : W, Discharged i.want w

/-- **`Intent.Accepts i w`** — the *decidable* acceptance check the owning cell runs on a
**claimed** fill `w`. Unlike `Fires` (an existential `Prop`), this is grounded at a
specific `w` and is therefore exactly `Discharged i.want w`, which is decidable. This is
the VERIFY side made local to the intent. -/
def Intent.Accepts [Verifiable P W] (i : Intent P W) (w : W) : Prop :=
  Discharged i.want w

/-- **VERIFY is decidable (the in-TCB half of the seam).** The owning cell can *always*
decide whether to accept a claimed fill. This instance is the type-level witness that
`Verify`/`Accepts` is tractable; the matcher `find` below carries NO analogous instance,
which is the asymmetry made precise. -/
instance [Verifiable P W] (i : Intent P W) (w : W) : Decidable (Intent.Accepts i w) := by
  unfold Intent.Accepts; infer_instance

/-! ## 2. The fill / resolve mechanism — untrusted matcher proposes, cell verifies. -/

/-- **`Intent.propose i` — the matcher proposes a fill.** The matcher plugin is the
`Searchable.find` of `Laws.lean`, applied to the intent's predicate. It returns
`Option W`: `some w` is a *proposed* fill (NOT yet trusted — the cell must still VERIFY
it), `none` is "I found nothing / I gave up" (the plugin may be partial or
nonterminating; `Option` models that). Crucially there is no `Decidable`/completeness
guarantee on this: `find` is opaque. -/
def Intent.propose [Searchable P W] (i : Intent P W) : Option W :=
  Searchable.find i.want

/-- **`Intent.resolve i` — the cell resolves the intent.** The two-step protocol made
one function: (1) the untrusted matcher *proposes* a fill via `propose`; (2) the cell
*verifies* it with the decidable `Verify`, keeping it only if it actually discharges the
predicate. The result is `some w` ONLY for a fill that both the matcher returned *and*
the cell accepted. A matcher that returns a non-satisfying (or adversarial) fill is
filtered out here — soundness is enforced by VERIFY, never by trusting FIND. -/
def Intent.resolve [Verifiable P W] [Searchable P W] (i : Intent P W) : Option W :=
  match Searchable.find i.want with
  | none   => none
  | some w => if Verifiable.Verify i.want w then some w else none

/-! ## 3. THE KEYSTONE — soundness-by-verification at the intent. -/

/-- **`intent_fill_verifies` (KEYSTONE part (a)) — an ACCEPTED fill genuinely satisfies
the predicate.** If `resolve` yields `some w`, then `w` discharges the intent's
predicate. The matcher (`find`) is untrusted and may be buggy or adversarial, yet the
fill the cell *accepts* is sound, because acceptance gates on the decidable `Verify`.
This is the intent-face instance of soundness-by-verification — the same content as
`Laws.search_sound`, but recovered here from the *cell's own VERIFY step* (no appeal to
the `search_sound` contract is needed, because `resolve` re-checks `Verify` itself). -/
theorem intent_fill_verifies
    [Verifiable P W] [Searchable P W] (i : Intent P W) (w : W)
    (h : i.resolve = some w) :
    Discharged i.want w := by
  unfold Intent.resolve at h
  cases hf : (Searchable.find i.want : Option W) with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some v =>
    rw [hf] at h
    simp only at h  -- reduce the `match some v with …` to its `some` arm
    by_cases hv : Verifiable.Verify i.want v = true
    · -- accepted: `h : some v = some w` ⇒ `v = w`; `Verify want v = true` is `Discharged`.
      simp only [hv, if_pos] at h
      have : v = w := by injection h
      subst this
      exact hv
    · -- rejected by VERIFY: the if-branch is `none`, contradicting `… = some w`.
      rw [Bool.not_eq_true] at hv
      rw [hv] at h
      simp only [Bool.false_eq_true, if_false] at h
      exact absurd h (by simp)

/-- **`intent_accepts_discharged_def`** — a definitional unfold, NOT a theorem with
content. `Intent.Accepts` is *defined* as `Discharged i.want w` (see §1), so this `Iff` is
`Iff.rfl`: it records, for callers, that `Accepts` is a transparent alias adding nothing
beyond the verify-side `Discharged` — the intent trusts only the verifier. Named `_def` to
be honest that it discharges by unfolding a definition, not by a proof step. -/
theorem intent_accepts_discharged_def
    [Verifiable P W] (i : Intent P W) (w : W) :
    i.Accepts w ↔ Discharged i.want w := Iff.rfl

/-- **`intent_resolve_fires` — a resolved intent has fired.** If the cell accepted a fill,
then the existential firing condition holds (a witness exists). The converse does NOT
hold and is deliberately left open below: `Fires` asserting *some* filler exists does not
let the cell *produce* one — that is the undecidable FIND direction. -/
theorem intent_resolve_fires
    [Verifiable P W] [Searchable P W] (i : Intent P W) (w : W)
    (h : i.resolve = some w) :
    i.Fires :=
  ⟨w, intent_fill_verifies i w h⟩

/-- **`intent_sound_against_adversary` — soundness holds even against an adversarial
matcher.** For ANY `Searchable P W` instance whatsoever (including one engineered to
return wrong fills), every fill the cell *accepts* still discharges the predicate. The
statement quantifies over the matcher being arbitrary by simply not constraining it: the
instance is a free parameter, and the conclusion holds regardless. This is the formal
content of "VERIFY in the TCB, FIND outside it." -/
theorem intent_sound_against_adversary
    [Verifiable P W] [Searchable P W] (i : Intent P W) :
    ∀ w : W, i.resolve = some w → Discharged i.want w :=
  fun w h => intent_fill_verifies i w h

/-! ## KEYSTONE part (b) — the asymmetry is in the TYPES.

The design law in this module's header is realized concretely:

  * VERIFY is decidable — witnessed by the `Decidable (Intent.Accepts i w)` instance in
    §1 (and `Laws`' own `Decidable (Discharged p w)`). The cell can ALWAYS decide
    acceptance.
  * FIND carries NO such guarantee — `Searchable.find : P → Option W` is an opaque
    typeclass method with no `Decidable`/`DecidableEq`/completeness/termination law. There
    is intentionally **no** instance `Decidable (Intent.Fires i)` in this module: deciding
    *whether any filler exists* is the undecidable FIND problem (HOU-undecidable), and
    asserting it would be the dishonest "general matcher" the design forbids.

  -- OPEN: `Decidable (Intent.Fires i)` is NOT provided and MUST NOT be — `Fires` is
  -- `∃ w, Discharged want w`, whose decision is general fill-finding (higher-order
  -- unification), undecidable (`cand-A §3`, `no_general_matcher` via `HOU ⪯ GeneralMatch`).
  -- The matcher is an untrusted plugin (`Intent.propose`); we never claim to decide `Fires`.
-/

/-! ## 4. The duality — an intent is the INVERSE of the vat-boundary cross case. -/

/-- **`ofAwait` / `toAwait`** — the intent developed here is *the same object* as
`Await.intent` (Face 3 of the await family), forgetting/restoring the continuation and
witness-typing decoration. This connects the authority-grade `Intent` to the await
family without redefining it: the existential hole is one primitive, viewed two ways.
`ofAwait` reads the predicate off an `Await.intent`; `toAwait` re-attaches a
continuation. -/
def ofAwait {P W Reply S : Type u} [Verifiable P W]
    (a : intent P W Reply S) : Intent P W :=
  { want := a.want }

/-- Re-attach a continuation, recovering the await-family Face-3 view. -/
def toAwait {P W Reply S : Type u} [Verifiable P W]
    (i : Intent P W) (k : Dregg2.Await.OneShot Reply S) : intent P W Reply S :=
  { want := i.want, kont := k }

/-- **`intent_face_agrees_def`** — a definitional unfold, NOT a theorem with content.
`ofAwait` is defined to copy `want` on the nose (`(ofAwait a).want = a.want` by `rfl`), and
both `Fires` predicates are `∃ w, Discharged ·.want w`; so the two firing conditions are the
*same* `Prop` up to unfolding, and this `Iff` is `Iff.rfl`. It records, for callers, that the
forgetful map `ofAwait` preserves the `∃`-resolver semantics definitionally — the agreement
is by construction, not a proved correspondence. Named `_def` to be honest about that. -/
theorem intent_face_agrees_def {P W Reply S : Type u} [Verifiable P W]
    (a : intent P W Reply S) :
    Dregg2.Await.intent.Fires a ↔ (ofAwait a).Fires := Iff.rfl

/-- **The outgoing-boundary predicate of an intent.** To state the duality against the
*actual* vat-boundary object (`Authority.Integrity`, the lift of l4v `integrity_obj_atomic`,
`Positional.lean`) rather than against a copy of `Discharged`, we view an intent `i` as a
boundary whose admissibility predicate is, on every cell-object change, exactly `i.want`. The
boundary then admits a **cross** change iff some witness discharges `i.want` — the same hole
the intent gates, but presented as an *outgoing* membrane over abstract object-states `KO`. -/
def Intent.boundaryPred (i : Intent P W) : KO → KO → P := fun _ _ => i.want

/-- **`intent_inverts_boundary` (the duality lemma) — intent is the INVERSE vat boundary
(PROVED, non-trivially).**

The two faces are genuinely *different objects*, not the same `Discharged` twice:

  * **OUTGOING** is the real vat-boundary relation `Authority.Integrity` (`Positional.lean`,
    the lift of l4v `integrity_obj_atomic`). Its `cross` constructor admits a non-owner
    object change `ko ⟶ ko'` *iff* SOME witness discharges the boundary predicate, i.e. the
    **existential** admissibility `∃ w, Discharged (i.boundaryPred ko ko') w`.
  * **INCOMING** is the intent's own existential firing `i.Fires = ∃ w, Discharged i.want w`
    — the filler-crossing-*in* condition.

The duality is the equivalence of these two *distinct* faces, going through the inductive
`Integrity.cross` introduction (NOT `Iff.rfl`): **an outgoing cross-vat change is admissible
exactly when the intent fires.** The forward direction destructs the `Integrity` proof — but
`intra` (own-vat, l4v `troa_lrefl`) is unavailable because we take a genuinely cross actor
(`owner ∉ subjects`, here `subjects = []`), so admissibility can *only* come from a discharged
witness, which is precisely a firing of the intent. The reverse direction takes a firing
witness and builds the `cross` constructor.

The pointwise companion `intent_accepts_witnesses_boundary` then shows the INCOMING local
acceptance `i.Accepts w` is exactly a *witness producing* the OUTGOING admissibility: an
accepted incoming filler is what lets the outgoing turn cross. Together: the intent is the vat
boundary with the morphism direction reversed — the incoming filler-gate and the outgoing
turn-gate are inverse, and each side's witness is the other side's admission proof. -/
theorem intent_inverts_boundary [Verifiable P W] (i : Intent P W)
    (owner : Label) (ko ko' : KO) :
    Integrity W owner ([] : List Label) (i.boundaryPred) ko ko' ↔ i.Fires := by
  constructor
  · intro hcross
    cases hcross with
    | intra hmem => exact absurd hmem (by simp)   -- no `intra`: owner ∉ [] (genuinely cross)
    | cross w hw => exact ⟨w, hw⟩                  -- the cross witness IS a firing of the intent
  · rintro ⟨w, hw⟩
    exact Integrity.cross w hw                     -- a firing builds the outgoing `cross` admission

/-- **`intent_accepts_witnesses_boundary` — the incoming filler IS the outgoing admission
witness (PROVED).** A specific filler `w` that the intent *accepts* on the incoming side
(`i.Accepts w`, the decidable local VERIFY) is exactly a witness that admits the *outgoing*
cross-vat change via `Integrity.cross`. The two faces share their witness, in opposite
directions across the membrane — the concrete content of "intent is the inverse boundary." -/
theorem intent_accepts_witnesses_boundary [Verifiable P W] (i : Intent P W)
    (owner : Label) (ko ko' : KO) (w : W) (hacc : i.Accepts w) :
    Integrity W owner ([] : List Label) (i.boundaryPred) ko ko' :=
  Integrity.cross w hacc

/-! ## 5. `#eval` demos — soundness against a correct AND an adversarial matcher.

A concrete intent: "find a `Nat` with `check w = true`", where `check w := w % 3 == 0`
(any multiple of 3 fills the hole). VERIFY = run `check`. We exhibit:
  * a CORRECT matcher returning `6` (a satisfying fill — ACCEPTED);
  * an ADVERSARIAL matcher returning `7` (NOT a multiple of 3 — REJECTED by VERIFY);
  * a GIVE-UP matcher returning `none` (no fill — resolves to `none`).
Soundness (`intent_fill_verifies`) means `resolve` yields `some w` ONLY in the first case.
-/

/-- Demo predicate space: a single predicate "is a multiple of 3". -/
inductive DivBy3 where
  | mult3
  deriving Repr, DecidableEq

/-- Demo witness space: a natural number (the proposed fill). -/
abbrev Fill := Nat

/-- VERIFY (in TCB): a fill discharges `mult3` iff it is divisible by 3. Decidable,
total, cheap — exactly the verify side. -/
instance demoVerifiable : Verifiable DivBy3 Fill where
  Verify := fun _ w => w % 3 == 0

/-- The concrete intent: a hole wanting a multiple of 3. -/
def demoIntent : Intent DivBy3 Fill := { want := DivBy3.mult3 }

/-- A CORRECT matcher: proposes `6` (a genuine fill). UNTRUSTED, but happens to be right. -/
@[reducible] def goodMatcher : Searchable DivBy3 Fill where
  find := fun _ => some 6

/-- An ADVERSARIAL matcher: proposes `7` (NOT a multiple of 3). The cell must reject it. -/
@[reducible] def evilMatcher : Searchable DivBy3 Fill where
  find := fun _ => some 7

/-- A GIVE-UP matcher: finds nothing (models partiality/nontermination). -/
@[reducible] def emptyMatcher : Searchable DivBy3 Fill where
  find := fun _ => none

/-! ### A discriminating witness that `Laws.SoundSearchable`'s `find_sound` contract is
non-vacuous. The `goodMatcher` (proposes `6`) SATISFIES the soundness-by-verification
contract — every fill it returns verifies — so it lifts to a `SoundSearchable`. The
`evilMatcher` (proposes `7`) does NOT (`7 % 3 ≠ 0`), which we prove below: the contract has
teeth, it is a genuine constraint that not every untrusted `Searchable` meets. -/

/-- **`goodMatcher` IS a contracted plugin (`SoundSearchable`).** Its only return `6`
verifies (`6 % 3 == 0`), so the soundness-by-verification field is provable: a discriminating
witness that the `find_sound` assumption is satisfiable (not vacuous). -/
instance goodSoundMatcher : SoundSearchable DivBy3 Fill where
  find := goodMatcher.find
  find_sound := fun p w h => by
    -- `goodMatcher.find p` reduces to `some 6`, so `h : some 6 = some w` gives `w = 6`;
    -- `Discharged mult3 6` unfolds to `Verify mult3 6 = true`, i.e. `(6 % 3 == 0) = true`.
    have hw : (6 : Fill) = w := Option.some.inj h
    rw [← hw]
    unfold Discharged
    rfl

/-- **TEETH — `evilMatcher` CANNOT be a contracted plugin.** No `SoundSearchable` instance
agreeing with `evilMatcher.find` can exist: it returns `7`, which does NOT verify
(`7 % 3 ≠ 0`), so any `find_sound` for it would prove the false `Discharged mult3 7`. The
soundness contract is therefore a genuine (non-trivial) constraint — exactly the honest
content of "FIND is untrusted; the contract is an assumption a real plugin must EARN." -/
theorem evilMatcher_not_sound
    (s : SoundSearchable DivBy3 Fill) (hagree : s.find = evilMatcher.find) :
    False := by
  have hfound : s.find DivBy3.mult3 = some 7 := by rw [hagree]; rfl
  have hd : Discharged DivBy3.mult3 7 := s.find_sound DivBy3.mult3 7 hfound
  -- `Discharged mult3 7` IS (defeq) `Verify mult3 7 = true`; but `Verify mult3 7` computes to
  -- `false` (`7 % 3 = 1 ≠ 0`), so `hd : false = true` — absurd.
  have hd2 : Verifiable.Verify DivBy3.mult3 (7 : Fill) = true := hd
  have hfalse : Verifiable.Verify DivBy3.mult3 (7 : Fill) = false := rfl
  rw [hfalse] at hd2
  exact Bool.false_ne_true hd2

-- The good matcher proposes 6, a genuine fill: ACCEPTED → `some 6`.
#eval (@Intent.resolve DivBy3 Fill demoVerifiable goodMatcher demoIntent)   -- some 6
-- The adversarial matcher proposes 7, NOT a multiple of 3: REJECTED by VERIFY → `none`.
-- Soundness holds against a buggy/adversarial matcher: the bad fill never escapes.
#eval (@Intent.resolve DivBy3 Fill demoVerifiable evilMatcher demoIntent)   -- none
-- The give-up matcher finds nothing: `none`.
#eval (@Intent.resolve DivBy3 Fill demoVerifiable emptyMatcher demoIntent)  -- none
-- The untrusted PROPOSE step (pre-verification) does surface the adversarial 7 …
#eval (@Intent.propose DivBy3 Fill evilMatcher demoIntent)                  -- some 7
-- … but the cell's own VERIFY rejects it (decidable, in-TCB):
#eval (@Intent.Accepts DivBy3 Fill demoVerifiable demoIntent 7 : Bool)      -- false
#eval (@Intent.Accepts DivBy3 Fill demoVerifiable demoIntent 6 : Bool)      -- true

end Dregg2.Authority
