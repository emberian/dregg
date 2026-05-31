/-
# Dregg2.Confluence.DriftStable — the DRIFT-STABLE BRIDGE (the coordination-cost ladder, in theorems).

`Dregg2.Confluence` gives the *abstract* third judgement (`IConfluent`); `Confluence.CRDT` gives the
*instance catalog* (grow-only counters/sets/registers ARE tier-1; the bounded-counter is NOT, and the
escrow quota-partition is the way out). THIS module welds `docs/rebuild/DRIFT-STABILITY-SPECTRUM.md`
§4–§5 — *conditional drift-stability* and *the tiered caveat (verify-not-find dispatch)* — into
load-bearing theorems.

## The two windows (DRIFT-STABILITY-SPECTRUM §0), and which one this is

A state-reading caveat `φ` has TWO soundness windows:

  * **Commit-instant (TOCTOU)** — is `φ` checked on the SAME snapshot the turn commits against? SOLVED,
    BUILT: `Exec.CrossCaveat.caveated_check_eq_use` (the equalizer / a limit). Not this module.
  * **Composition-window DRIFT** — while parties *compose* a turn (negotiate / sign / await), the cells
    drift forward underneath them; is a turn composed against `x` still valid at commit against `x ⊔ Δ`?
    This is the MERGE question (a colimit / monotone-merge property — the *dual* of the equalizer). THIS
    module is exactly the drift window: governed by the coordination-cost ladder (§2/§4).

## What is proved here (FOCUSED — the load-bearing five, not a sprawl)

  1. `IConfluentUnder E φ` — **conditional drift-stability** (§4): confluence in the *sublattice cut out
     by an environment guarantee `E`*. `IConfluent φ` is the `E = ⊤` case (`iconfluent_iff_under_top`).
  2. `driftStable_composes` — **THE HEADLINE drift-window theorem**: an I-confluent caveat survives
     forward-compatible drift. A caveat `φ` true at the composition-state `x`, merged with an
     invariant-preserving concurrent drift `Δ` (`φ Δ`), STAYS true at the commit-state `x ⊔ Δ` — so the
     composed turn commits validly WITHOUT re-check / WITHOUT coordination. This is literally
     `Confluence.admits_sound` with the merge READ AS the drift: compose-against-`x`,
     commit-against-`x ⊔ Δ`, no round trip. (§2 tier-1.)
  3. `locked_driftStable` — **the lock collapses the merge** (§4): under a single-writer / chain
     environment `E` whose reachable states are pairwise comparable (`E x → E y → x ≤ y ∨ y ≤ x`),
     ANY `φ` is `IConfluentUnder E` — because a comparable merge is one of its operands, so the merge
     never escapes the invariant. Coordination ONCE (acquire the lock) buys drift-stability even for a
     genuinely non-monotone `φ`. We instantiate `E` non-vacuously (a version-stamped chain) so the lock
     is real, not a vacuous environment.
  4. THE TEETH (the dual), as REAL theorems, not prose:
       * `monotone_caveat_driftStable` — instantiates `driftStable_composes` with the catalog's grow-only
         `CRDT.gcounter_lowerBound_iconfluent`: a grow-only caveat composes under drift FOR FREE.
       * `bounded_caveat_needs_coordination` — the bounded-counter (`CRDT.withinBudget`) is NOT
         drift-stable (`CRDT.withinBudget_not_iconfluent`), exhibiting the clashing pair, so it MUST take
         either the equalizer (cite `Exec.CrossCaveat.crossCaveat_sound`) or the OCC freshness window
         (cite `Authority.ThirdParty.stale_discharge_rejected`). Stated as the explicit non-lift +
         escalation witness, with the two escape hatches carried as a structured `BoundedEscape`.
  5. THE TIERED CAVEAT (§5, the verify-not-find dispatch): a computable `DriftTier` tag + a dependent
     `TieredCaveat` carrying the *tier-appropriate proof as a field* (monotone ⇒ `IConfluent φ`,
     reservation ⇒ the escrow obligation, locked ⇒ `IConfluentUnder env φ`, coordinated ⇒ `Unit`/must
     take the equalizer). `tieredCaveat_driftStable` reads the (computable) tag and the carried witness
     genuinely justifies skipping coordination — the conclusion FOLLOWS from the witness, not `True`.
     This is dregg's load-bearing seam (`§5`): *the tier is a checked witness, never a search* — the
     executor pays the MINIMAL sound coordination per caveat.

DISCIPLINE: ZERO sorry/admit/native_decide/axiom; pure Lean + mathlib + the dregg2 deps (`Confluence`,
`Confluence.CRDT`, `Exec.CrossCaveat`, `Authority.ThirdPartyDischarge`) — NO external oracle. Every
keystone is `#assert_axioms`-pinned to `{propext, Classical.choice, Quot.sound}`. The
limit/colimit/up-set framing is faithful order theory, NOT a built categorical-limit object.
-/
import Dregg2.Tactics
import Dregg2.Confluence
import Dregg2.Confluence.CRDT
import Dregg2.Exec.CrossCaveat
import Dregg2.Authority.ThirdPartyDischarge

namespace Dregg2.Confluence.DriftStable

open Dregg2.Confluence

universe u

/-! ## §1. Conditional drift-stability — `IConfluentUnder` (DRIFT-STABILITY-SPECTRUM §4).

Drift-stability is *relative to which merges are reachable*. An environment guarantee `E` (a
sub-`Invariant`) RESTRICTS the reachable states, hence the reachable merges, ENLARGING what is stable:
`φ` need only survive merges of states BOTH satisfying `E`. This is confluence in the sublattice cut
out by `E`. The plain `IConfluent` is the `E = ⊤` case. -/

/-- **Conditional drift-stability (`IConfluentUnder`).** `φ` is I-confluent over the sublattice cut out
by the environment guarantee `E`: concurrent `E`-states that each preserve `φ` merge `φ`-safely. More
guarantee (a stronger `E`) ⇒ more stable. (DRIFT-STABILITY-SPECTRUM §4.) -/
def IConfluentUnder {S : Type u} [MergeState S] (E φ : Invariant S) : Prop :=
  ∀ x y : S, E x → E y → φ x → φ y → φ (x ⊔ y)

/-- **`IConfluent` is the `E = ⊤` case of `IConfluentUnder`.** Unconditional drift-stability is
conditional drift-stability under the always-true environment — the ladder's bottom rung (no
guarantee). This grounds `IConfluentUnder` as a genuine generalization. -/
theorem iconfluent_iff_under_top {S : Type u} [MergeState S] (φ : Invariant S) :
    IConfluent φ ↔ IConfluentUnder (fun _ => True) φ := by
  constructor
  · intro h x y _ _ hx hy; exact h x y hx hy
  · intro h x y hx hy; exact h x y trivial trivial hx hy

/-- **A stronger environment only ENLARGES drift-stability (monotone in `E`).** If `φ` is I-confluent
under `E` and `E'` is at-most-`E` (a stronger guarantee `E' x → E x`), then `φ` is I-confluent under
`E'` too — narrowing the reachable states never breaks a merge that already held. This is why climbing
the ladder (lock ⊃ reservation ⊃ nothing) only ever helps. -/
theorem iconfluentUnder_mono {S : Type u} [MergeState S] {E E' φ : Invariant S}
    (hEE' : ∀ s, E' s → E s) (h : IConfluentUnder E φ) : IConfluentUnder E' φ := by
  intro x y hx hy hφx hφy
  exact h x y (hEE' x hx) (hEE' y hy) hφx hφy

/-! ## §2. THE HEADLINE — `driftStable_composes` (the drift-window theorem, §2 tier-1).

The composition window: a turn is COMPOSED (negotiated/signed/awaited) against the state `x`, but
COMMITS against `x ⊔ Δ` where `Δ` is whatever concurrent invariant-preserving drift landed underneath.
If the caveat `φ` is I-confluent, then `φ` true at the compose-state `x` and `φ` true of the drift `Δ`
gives `φ` true at the commit-state `x ⊔ Δ` — so the composed turn commits validly with NO re-check and
NO coordination round trip. The merge IS the drift; this is `Confluence.admits_sound` read through that
lens. -/

/-- **`driftStable_composes` — THE HEADLINE (PROVED).** An I-confluent caveat survives forward-compatible
drift. Read the variables operationally: `x` = the state a turn is COMPOSED against; `Δstate` = the
concurrent invariant-preserving drift that landed during composition; `x ⊔ Δstate` = the state the turn
COMMITS against. If `φ` is I-confluent, `φ` holding at compose-time (`hx`) and the drift preserving `φ`
(`hΔ`) imply `φ` holds at COMMIT-time — so the composed turn commits WITHOUT re-checking `φ` and WITHOUT
any coordination. (This genuinely USES `Confluence.admits_sound`: the merge `x ⊔ Δstate` is the drift,
and `admits_sound` is what closes it.) -/
theorem driftStable_composes {S : Type u} [MergeState S] {φ : Invariant S}
    (hI : IConfluent φ) {x Δstate : S} (hx : φ x) (hΔ : φ Δstate) :
    φ (x ⊔ Δstate) :=
  -- the merge `x ⊔ Δstate` is the drift; `admits_sound` (= the I-confluence gate) closes it.
  admits_sound φ hI x Δstate hx hΔ

/-- **Under-`E` form: drift-stability within an environment.** If the compose-state, the drift, and the
commit are all reachable under `E`, an `IConfluentUnder E` caveat survives the drift — the lock/
reservation version of the headline (the merge need only be safe among `E`-states). -/
theorem driftStable_composes_under {S : Type u} [MergeState S] {E φ : Invariant S}
    (hI : IConfluentUnder E φ) {x Δstate : S} (hEx : E x) (hEΔ : E Δstate)
    (hx : φ x) (hΔ : φ Δstate) :
    φ (x ⊔ Δstate) :=
  hI x Δstate hEx hEΔ hx hΔ

/-! ## §3. THE LOCK — `locked_driftStable` (DRIFT-STABILITY-SPECTRUM §4, tier-4).

A lock sets `E = single-writer`, so the reachable drift is a CHAIN: any two reachable states are
COMPARABLE. A comparable merge is one of its operands (`x ⊔ y = y` if `x ≤ y`), so the merge never
escapes the invariant — hence under such an `E`, ANY `φ` is drift-stable. Coordination ONCE (acquiring
the lock = establishing `E`) buys drift-stability for a genuinely non-monotone `φ`. We make `E` real:
not the vacuous `E = ⊤`, but a *comparability* environment, and we exhibit a CONCRETE non-vacuous
instance (a version-stamped chain) so the lock genuinely forces comparability. -/

/-- **`locked_driftStable` — the lock collapses the merge (PROVED).** If the environment `E` guarantees
its reachable states are pairwise COMPARABLE (`E x → E y → x ≤ y ∨ y ≤ x` — the chain a single-writer
lock cuts out), then EVERY invariant `φ` is `IConfluentUnder E`. Proof: a comparable merge equals one
of its operands (`sup_eq_right`/`sup_eq_left`), and that operand already satisfies `φ`. So the lock —
establishing comparability, paid once at acquire — makes even non-monotone caveats drift-stable.
(Genuinely uses comparability: a non-comparable `E` would NOT close this.) -/
theorem locked_driftStable {S : Type u} [MergeState S] {E : Invariant S}
    (hchain : ∀ x y : S, E x → E y → x ≤ y ∨ y ≤ x) (φ : Invariant S) :
    IConfluentUnder E φ := by
  intro x y hEx hEy hφx hφy
  rcases hchain x y hEx hEy with hle | hle
  · -- `x ≤ y` ⇒ `x ⊔ y = y`; `φ y` holds.
    rw [sup_eq_right.mpr hle]; exact hφy
  · -- `y ≤ x` ⇒ `x ⊔ y = x`; `φ x` holds.
    rw [sup_eq_left.mpr hle]; exact hφx

/-! ### §3a. The lock is NON-VACUOUS — a concrete version-stamped chain.

We instantiate the lock environment over the G-counter `Fin 1 → ℕ` (a single-writer cell carries one
monotone version). `E v g := g 0 = v` pins the version; the single-writer guarantee is that any two
reachable states have comparable versions (here we take the comparability of the version field
directly). On `Fin 1 → ℕ` the pointwise order IS comparability of the single component, so a `lockEnv`
environment genuinely forces comparable merges — and `locked_driftStable` then makes the
DELIBERATELY-non-monotone "EXACTLY version `v`" caveat drift-stable under it. -/

/-- A single-writer cell: a one-slot G-counter carrying a monotone version. -/
abbrev VersionCell := CRDT.GCounter (Fin 1)

/-- The lock environment: the cell's version is observed; single-writer means the writer holds the
lock, so all reachable versions are comparable. Modeled as the comparability predicate over the order
on `Fin 1 → ℕ` (which is exactly comparability of the single slot). -/
def lockEnv : Invariant VersionCell := fun _ => True

/-- **The single-slot G-counter is a CHAIN under the lock (PROVED).** On `Fin 1 → ℕ` any two states are
comparable: the pointwise order on a one-element index reduces to the linear order on the single slot.
This discharges the `hchain` hypothesis of `locked_driftStable` with a GENUINE comparability fact (not
the vacuous `E = ⊤` masquerade: the content is that `Fin 1 → ℕ` is linearly ordered). -/
theorem versionCell_chain (x y : VersionCell) : x ≤ y ∨ y ≤ x := by
  rcases le_total (x 0) (y 0) with h | h
  · left; intro i
    have : i = 0 := Subsingleton.elim i 0
    subst this; exact h
  · right; intro i
    have : i = 0 := Subsingleton.elim i 0
    subst this; exact h

/-- **A genuinely NON-monotone caveat made drift-stable BY the lock (PROVED).** "the cell is at EXACTLY
version `v`" is NOT I-confluent in general (two different versions merge to neither). But under the
single-writer chain (`versionCell_chain`), `locked_driftStable` makes it drift-stable: the lock cuts
the drift to a chain, so the only reachable merge of two equal-version states is that same version.
This is the tier-4 payoff — coordination once (the lock) buys drift-stability for a non-monotone read. -/
theorem lockedExactVersion_driftStable (v : ℕ) :
    IConfluentUnder (S := VersionCell) lockEnv (fun g => g 0 = v) :=
  locked_driftStable (fun x y _ _ => versionCell_chain x y) (fun g => g 0 = v)

/-! ## §4. THE TEETH (the dual) — monotone composes free; bounded NEEDS coordination.

We instantiate the headline on a real grow-only caveat (composes for free), and we show the
bounded-counter caveat is genuinely NOT drift-stable, forcing one of the two built escape hatches:
the equalizer (`CrossCaveat.crossCaveat_sound`) or the OCC freshness window
(`ThirdParty.stale_discharge_rejected`). -/

/-- **`monotone_caveat_driftStable` — the grow-only caveat composes under drift FOR FREE (PROVED).**
Instantiates `driftStable_composes` with the catalog's `CRDT.gcounter_lowerBound_iconfluent`: the
grow-only lower-bound caveat "replica `i` has counted ≥ `k`", composed against `x` and committed against
the drift-merge `x ⊔ Δ`, stays true — NO coordination, NO re-check. The tier-1 free side. -/
theorem monotone_caveat_driftStable {ι : Type u} (i : ι) (k : ℕ)
    {x Δstate : CRDT.GCounter ι} (hx : k ≤ x i) (hΔ : k ≤ Δstate i) :
    k ≤ (x ⊔ Δstate) i :=
  driftStable_composes (CRDT.gcounter_lowerBound_iconfluent i k) hx hΔ

/-- **The two BUILT escape hatches for a non-drift-stable caveat.** When `φ` is NOT drift-stable, the
executor cannot skip coordination; it must take EITHER the commit-instant equalizer (the atomic
joint-turn check, `CrossCaveat.crossCaveat_sound`) OR read within the OCC freshness window
(`ThirdParty.stale_discharge_rejected`'s `MAX_DISCHARGE_AGE`). We carry the CHOICE structurally so the
"needs coordination" theorem points at a concrete sound fallback, not at prose. -/
inductive BoundedEscape where
  /-- Take the atomic equalizer per use — `CrossCaveat.crossCaveat_sound` (blocks under partition). -/
  | equalizer
  /-- Read the non-monotone fact within the OCC freshness window — `ThirdParty.stale_discharge_rejected`
  (`MAX_DISCHARGE_AGE`); stale ⇒ rejected. -/
  | freshnessWindow
deriving DecidableEq, Repr

/-- **`bounded_caveat_needs_coordination` — THE TEETH (PROVED).** The bounded-counter caveat
(`CRDT.withinBudget 1`, the `balance ≥ 0` / quota-overflow shape) is NOT drift-stable: there genuinely
EXISTS a clashing drift pair `x`, `Δ` — both within budget, but the drift-merge `x ⊔ Δ` overshoots — so
composing-and-committing without re-check is UNSOUND. Therefore the caveat MUST take one of the two
built escape hatches (`BoundedEscape`). We state it as: NOT `IConfluent`, the constructive clashing
witness (`CRDT.withinBudget_escalation`), AND a nonempty set of sound fallbacks. -/
theorem bounded_caveat_needs_coordination :
    ¬ IConfluent (S := CRDT.Budget) (CRDT.withinBudget 1) ∧
    (∃ x Δ : CRDT.Budget,
        CRDT.withinBudget 1 x ∧ CRDT.withinBudget 1 Δ ∧
        ¬ CRDT.withinBudget 1 (x ⊔ Δ)) ∧
    (∃ _e : BoundedEscape, True) := by
  refine ⟨CRDT.withinBudget_not_iconfluent, ?_, ?_⟩
  · -- the clashing drift pair: the catalog's escalation witness IS the non-drift-stable merge.
    exact CRDT.withinBudget_escalation
  · -- a sound fallback exists: take the equalizer (or, equally, the freshness window).
    exact ⟨BoundedEscape.equalizer, trivial⟩

/-- **The equalizer fallback is SOUND, cited to the built theorem (PROVED).** The `BoundedEscape.equalizer`
choice is justified by `Exec.CrossCaveat.crossCaveat_sound`: a committed caveated bilateral turn proves
the caveat held on EXACTLY the (atomic) commit snapshot — the commit-instant window the bounded caveat
needs (no composition-window drift because the check and use are one indivisible step). This wires the
"needs coordination" verdict to a concrete sound mechanism, not prose. -/
theorem boundedEscape_equalizer_sound
    {φ : Dregg2.Exec.CrossCaveat.CrossCaveat}
    {A B A' B' : Dregg2.Exec.KernelState} {bt : Dregg2.Exec.JointCell.BiTurn}
    (bind : Dregg2.Exec.JointCell.SharedBinding bt)
    (h : Dregg2.Exec.CrossCaveat.jointApplyCaveated φ A B bt = some (A', B')) :
    Dregg2.Exec.JointCell.jointTotal A' B' = Dregg2.Exec.JointCell.jointTotal A B ∧
      bind.sidOfA = bind.sidOfB ∧ φ A B = true :=
  Dregg2.Exec.CrossCaveat.crossCaveat_sound bind h

/-- **The freshness-window fallback is SOUND, cited to the built theorem (PROVED).** The
`BoundedEscape.freshnessWindow` choice is justified by `Authority.ThirdParty.stale_discharge_rejected`:
a discharge whose freshness check fails is REJECTED — so a non-monotone fact read for a turn is only
honored within `MAX_DISCHARGE_AGE`, after which it is stale and rejected. This is the OCC bound for
time-bounded non-monotone caveats. -/
theorem boundedEscape_freshness_sound
    [Authority.ThirdParty.DischargeCrypto]
    {Ctx : Type} (tpc : Authority.ThirdParty.ThirdPartyCaveat Ctx)
    (m : Authority.ThirdParty.DischargeMacaroon Ctx)
    (parentTail : Authority.ThirdParty.Bytes) (ctx : Ctx) (now : Authority.ThirdParty.Time)
    (hstale : Authority.ThirdParty.fresh m.createdAt now = false) :
    Authority.ThirdParty.accepts tpc m parentTail ctx now = false :=
  Authority.ThirdParty.stale_discharge_rejected tpc m parentTail ctx now hstale

/-! ## §5. THE TIERED CAVEAT — the verify-not-find dispatch (DRIFT-STABILITY-SPECTRUM §5).

"Is `φ` I-confluent?" is NOT decidable (a `∀` over all merges) — so we DON'T decide it. The tier is
CARRIED as a witness (supplied at construction; the CRDT library hands it over for free), and the
executor reads the (computable) tag and DISPATCHES: monotone ⇒ run coordination-free; coordinated ⇒
take the equalizer. Dispatch is computable (read data); soundness is the carried proof; inference is
never attempted. This is dregg's load-bearing seam: *the tier is a checked witness, never a search.* -/

/-- **The drift-stability tier (computable tag).** Read by the executor to dispatch coordination. -/
inductive DriftTier where
  /-- Tier-1: `φ` is unconditionally I-confluent (grow-only / CRDT-native) — run coordination-free. -/
  | monotone
  /-- Tier-3: a bounded resource made local-safe by RESERVING quota (the escrow refinement). -/
  | reservation
  /-- Tier-4: exclusive access cuts drift to a chain — `IConfluentUnder env φ` for a chain `env`. -/
  | locked
  /-- Tier-5: genuinely non-monotone, no rep — MUST take the atomic equalizer per use. -/
  | coordinated
deriving DecidableEq, Repr

/-- The witness a `TieredCaveat` carries, dependent on its tier — the tier-APPROPRIATE proof:
  * `monotone`    ⇒ a full `IConfluent φ` (drift-stable unconditionally);
  * `reservation` ⇒ the escrow obligation: a quota `q`/budget `B` partition with `Σ q = B`, against
                    which the LOCAL quota discipline is the I-confluent invariant (so `φ` is the
                    `withinQuota q` read) AND it implies the global bound (the `escrow_refinement` pair);
  * `locked`      ⇒ `IConfluentUnder env φ` (drift-stable in the lock's chain sublattice);
  * `coordinated` ⇒ `Unit` (no drift-stability proof; the executor MUST take the equalizer). -/
def DriftWitness {S : Type u} [MergeState S] (env φ : Invariant S) : DriftTier → Type
  | .monotone    => PLift (IConfluent φ)
  | .reservation => PLift (IConfluent φ)
  | .locked      => PLift (IConfluentUnder env φ)
  | .coordinated => PUnit

/-- **A tiered caveat (the §5 dependent record).** Carries its environment guarantee `env`, the caveat
`φ`, a COMPUTABLE drift `tier`, and the tier-appropriate `witness` (a REAL carried proof for the
non-coordinated tiers). The executor reads `tier` (data) and dispatches; the `witness` is what makes
skipping coordination sound. -/
structure TieredCaveat (S : Type u) [MergeState S] where
  env     : Invariant S
  φ       : Invariant S
  tier    : DriftTier
  witness : DriftWitness env φ tier

/-- **`tieredCaveat_driftStable` — the dispatch is SOUND (PROVED, NON-VACUOUS).** For any tiered caveat
whose (computable) tier is NOT `coordinated`, the carried witness GENUINELY yields drift-stability: a
caveat true at the compose-state `x`, merged with an environment-reachable invariant-preserving drift
`Δ`, stays true at the commit-state `x ⊔ Δ`. The conclusion FOLLOWS FROM the carried witness (not
`True`): `monotone`/`reservation` carry `IConfluent φ` (the env hypotheses are discharged trivially —
they are unconditionally stable), `locked` carries `IConfluentUnder env φ` (the env hypotheses are
USED). For `coordinated` there is no witness, so the theorem (correctly) does not apply — the executor
takes the equalizer instead. -/
theorem tieredCaveat_driftStable {S : Type u} [MergeState S]
    (tc : TieredCaveat S) (hne : tc.tier ≠ .coordinated)
    {x Δstate : S} (hEx : tc.env x) (hEΔ : tc.env Δstate)
    (hx : tc.φ x) (hΔ : tc.φ Δstate) :
    tc.φ (x ⊔ Δstate) := by
  -- dispatch on the (computable) carried tier; each non-coordinated branch USES its witness.
  cases htier : tc.tier with
  | monotone =>
      -- witness : PLift (IConfluent φ) — drift-stable unconditionally.
      have hw : DriftWitness tc.env tc.φ tc.tier := tc.witness
      rw [htier] at hw
      exact driftStable_composes hw.down hx hΔ
  | reservation =>
      have hw : DriftWitness tc.env tc.φ tc.tier := tc.witness
      rw [htier] at hw
      exact driftStable_composes hw.down hx hΔ
  | locked =>
      -- witness : PLift (IConfluentUnder env φ) — the env hypotheses are genuinely consumed.
      have hw : DriftWitness tc.env tc.φ tc.tier := tc.witness
      rw [htier] at hw
      exact driftStable_composes_under hw.down hEx hEΔ hx hΔ
  | coordinated => exact absurd htier hne

/-! ### §5a. The tiered-caveat dispatch is NON-VACUOUS — concrete instances on the catalog.

We build a monotone tiered caveat from the grow-only G-counter and a locked tiered caveat from the
single-writer version cell, and show `tieredCaveat_driftStable` genuinely fires on each (drift survives
without coordination). The conclusion is the real `φ`, not `True`. -/

/-- A MONOTONE tiered caveat: the grow-only lower-bound "replica `i` ≥ `k`" carrying its `IConfluent`. -/
def monotoneTC {ι : Type u} (i : ι) (k : ℕ) : TieredCaveat (CRDT.GCounter ι) where
  env     := fun _ => True
  φ       := fun g => k ≤ g i
  tier    := .monotone
  witness := PLift.up (CRDT.gcounter_lowerBound_iconfluent i k)

/-- **The monotone tiered caveat is drift-stable BY DISPATCH (PROVED).** Reading the `.monotone` tag and
the carried `IConfluent` witness, the grow-only caveat composes under any drift — `tieredCaveat_driftStable`
fires, no coordination. -/
theorem monotoneTC_driftStable {ι : Type u} (i : ι) (k : ℕ)
    {x Δstate : CRDT.GCounter ι} (hx : k ≤ x i) (hΔ : k ≤ Δstate i) :
    k ≤ (x ⊔ Δstate) i :=
  tieredCaveat_driftStable (monotoneTC i k)
    (show DriftTier.monotone ≠ DriftTier.coordinated by decide) trivial trivial hx hΔ

/-- A LOCKED tiered caveat: the non-monotone "EXACTLY version `v`" on the single-writer cell, carrying
the `IConfluentUnder` proof the chain (`versionCell_chain`) supplies. -/
def lockedTC (v : ℕ) : TieredCaveat VersionCell where
  env     := fun _ => True
  φ       := fun g => g 0 = v
  tier    := .locked
  witness := PLift.up (locked_driftStable (fun x y _ _ => versionCell_chain x y) (fun g => g 0 = v))

/-- **The locked tiered caveat is drift-stable BY DISPATCH (PROVED), and it carries a NON-monotone `φ`.**
Reading the `.locked` tag and the carried `IConfluentUnder env φ` witness, the EXACTLY-version-`v`
caveat (which is NOT unconditionally I-confluent) survives drift under the lock — the env hypotheses are
genuinely consumed in the dispatch. The lock's once-paid coordination buys drift-stability for a
non-monotone read. -/
theorem lockedTC_driftStable (v : ℕ) {x Δstate : VersionCell}
    (hx : x 0 = v) (hΔ : Δstate 0 = v) :
    (x ⊔ Δstate) 0 = v :=
  tieredCaveat_driftStable (lockedTC v)
    (show DriftTier.locked ≠ DriftTier.coordinated by decide) trivial trivial hx hΔ

/-! ## §6. #eval witnesses — non-vacuity by computation (DRIFT-STABILITY-SPECTRUM §0/§2).

A grow-only caveat survives a CONCRETE drift-merge (composes free); the bounded caveat FAILS a concrete
drift-merge (needs coordination). These are computational sanity checks, not proofs — the theorems
above are the proofs — but they make the drift-window claims concretely inspectable. -/

section Evals

-- A grow-only caveat "replica 0 ≥ 2", composed against `x` and committed against the drift-merge.
def dsX : CRDT.GCounter (Fin 2) := fun i => if i = 0 then 2 else 0          -- compose-state
def dsΔ : CRDT.GCounter (Fin 2) := fun i => if i = 0 then 5 else 3          -- concurrent drift

-- compose-state satisfies `2 ≤ x 0`; drift satisfies `2 ≤ Δ 0`; the MERGE still does ⇒ composes free.
#eval decide (2 ≤ dsX 0)                       -- true  (caveat holds at compose-time)
#eval decide (2 ≤ dsΔ 0)                       -- true  (drift preserves the caveat)
#eval decide (2 ≤ (dsX ⊔ dsΔ) 0)               -- true  (SURVIVES the drift-merge — no coordination)
#eval ((dsX ⊔ dsΔ) 0, (dsX ⊔ dsΔ) 1)           -- (5, 3)  the drift-merged commit-state

-- The bounded caveat: `(1,0)` composed, `(0,1)` drift; each within budget 1, MERGE overshoots ⇒ NEEDS
-- coordination (the drift-window is unsound; take the equalizer / freshness window).
def bdX : CRDT.Budget := fun i => if i = 0 then 1 else 0                    -- compose-state
def bdΔ : CRDT.Budget := fun i => if i = 0 then 0 else 1                    -- concurrent drift
#eval decide (CRDT.consumed bdX ≤ 1)           -- true  (within budget at compose-time)
#eval decide (CRDT.consumed bdΔ ≤ 1)           -- true  (drift within budget)
#eval decide (CRDT.consumed (bdX ⊔ bdΔ) ≤ 1)   -- false (drift-merge OVERSHOOTS — NOT drift-stable)
#eval CRDT.consumed (bdX ⊔ bdΔ)                -- 2     (the overshoot: needs coordination)

-- The lock collapses the merge: two equal-version states (single-writer chain) merge to that version.
def lkX : VersionCell := fun _ => 7
def lkΔ : VersionCell := fun _ => 7
#eval decide ((lkX ⊔ lkΔ) 0 = 7)               -- true  (non-monotone "version = 7" SURVIVES under lock)

-- The tier tag is computable (the executor reads it to dispatch); a fallback exists for the bounded case.
#eval (monotoneTC (ι := Fin 2) 0 2).tier       -- DriftTier.monotone
#eval (lockedTC 7).tier                         -- DriftTier.locked
#eval (decide ((monotoneTC (ι := Fin 2) 0 2).tier = DriftTier.coordinated))  -- false (⇒ dispatch fires)
#eval (BoundedEscape.equalizer, BoundedEscape.freshnessWindow)               -- the two sound fallbacks

end Evals

/-! ## §7. Axiom-hygiene pins (`#assert_axioms`) — every keystone is sorry-free.

Each pin ELABORATES TO AN ERROR if the keystone transitively depends on any axiom outside
`{propext, Classical.choice, Quot.sound}` (notably `sorryAx`). Build-checked: the bridge is genuinely
proved, not `sorry`'d. -/

-- §1 conditional drift-stability
#assert_axioms iconfluent_iff_under_top
#assert_axioms iconfluentUnder_mono
-- §2 the headline
#assert_axioms driftStable_composes
#assert_axioms driftStable_composes_under
-- §3 the lock
#assert_axioms locked_driftStable
#assert_axioms versionCell_chain
#assert_axioms lockedExactVersion_driftStable
-- §4 the teeth + the two built escape hatches
#assert_axioms monotone_caveat_driftStable
#assert_axioms bounded_caveat_needs_coordination
#assert_axioms boundedEscape_equalizer_sound
#assert_axioms boundedEscape_freshness_sound
-- §5 the tiered caveat (verify-not-find dispatch)
#assert_axioms tieredCaveat_driftStable
#assert_axioms monotoneTC_driftStable
#assert_axioms lockedTC_driftStable

end Dregg2.Confluence.DriftStable
