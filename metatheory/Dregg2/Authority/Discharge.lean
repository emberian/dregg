/-
# Dregg2.Authority.Discharge — the await engine's AUTHORITY face (discharge monotonicity).

A **third-party caveat** is a turn that *cannot* become admissible until a named gateway
**DISCHARGES** it. This is the authority-face of the await family (`dregg2 §3`, `cand-A §3`,
GLOSSARY "await family"): a suspended cross-vat turn — a `zkpromise` / `ConditionalTurn` —
holds open until the gateway settles. Crucially, **discharges only ACCUMULATE**: a settled
gateway stays settled, so resolution moves strictly *forward*. This module proves the
▶-guarded "resolve forward, never un-resolve" property as a clean monotonicity law on
`Token.admits` in the `Discharges` parameter, building on `Authority.Caveat`.

## The four await faces (one resolver primitive, four projections)

The await family is **one** suspension/resolution primitive seen through four faces:
- **zkpromise** — the *data* face: a value that will exist (a future cell-state head).
- **discharge** — **THIS module: the *authority* face** — a gateway settling a third-party
  caveat so a suspended turn becomes admissible. The other three faces resolve a *value*,
  an *intent*, a *call*; this one resolves *standing*.
- **intent** — the *invariant* face: an I-confluent predicate the merge must satisfy.
- **settled-call** — the *control* face: the cross-vat method return that wakes the caller.

Each face is monotone in its accumulating evidence (`zkpromise`: the value, once known,
stays known; `discharge`: a settled gateway stays settled). `admits_mono_discharge` is that
fact for the authority face — the keystone — and it is exactly what makes await *sound*: the
suspended turn resolves and never spontaneously un-resolves.

Pure, computable, `#eval`-able.
-/
import Dregg2.Authority.Caveat

namespace Dregg2.Authority

open Dregg2.Laws

variable {Ctx : Type}
variable {Gateway : Type}

/-! ## The order on discharges: discharges only accumulate (a settled gateway stays settled). -/

/-- **`Discharges.le d d'`** — `d'` has *at least as many* discharges as `d`: every gateway
that has settled under `d` is still settled under `d'`. This is the forward-only order on the
await authority-face — time can add discharges but never retract one (a settled gateway is
permanent, the ▶-guarded "resolve forward"). -/
def Discharges.le (d d' : Discharges Gateway) : Prop :=
  ∀ g, d g = true → d' g = true

/-- `Discharges.le` is reflexive (the present moment has the discharges it has). -/
theorem Discharges.le_refl (d : Discharges Gateway) : Discharges.le d d :=
  fun _ h => h

/-- `Discharges.le` is transitive (discharges accumulated across two intervals accumulate). -/
theorem Discharges.le_trans {d d' d'' : Discharges Gateway}
    (h₁ : Discharges.le d d') (h₂ : Discharges.le d' d'') : Discharges.le d d'' :=
  fun g hg => h₂ g (h₁ g hg)

/-! ## A satisfied caveat stays satisfied as discharges accumulate. -/

/-- **`caveat_ok_mono` (PROVED)** — a satisfied caveat stays satisfied as discharges
accumulate. A **local** caveat ignores discharges entirely (its truth is context-only, hence
trivially preserved); a **third-party** caveat is satisfied iff its gateway has discharged, and
discharges only grow — so by `Discharges.le` it stays satisfied. This is the single-caveat
seed of the keystone. -/
theorem caveat_ok_mono (c : Caveat Ctx Gateway) (ctx : Ctx)
    {d d' : Discharges Gateway} (hle : Discharges.le d d')
    (h : c.ok ctx d = true) : c.ok ctx d' = true := by
  cases c with
  | «local» check =>
    -- the local check is independent of the discharges
    simpa [Caveat.ok] using h
  | thirdParty g =>
    -- a discharged gateway stays discharged
    simp only [Caveat.ok] at h ⊢
    exact hle g h

/-! ## THE KEYSTONE — admissibility resolves FORWARD, never un-resolves. -/

/-- **`admits_mono_discharge` (PROVED) — THE KEYSTONE.** If `d'` accumulates the discharges of
`d` (`Discharges.le d d'`), then any request the token admits under `d` it still admits under
`d'`. This is *"the await resolves FORWARD, never un-resolves"*: a suspended cross-vat turn,
once a gateway settles it, stays admissible — and additional settlements can only ever keep it
(or other turns) admissible. Monotonicity of admissibility in discharges.

Proof: `Token.admits` is the conjunction (`List.all`) of `Caveat.ok` over the caveat chain;
each conjunct is monotone by `caveat_ok_mono`, and `List.all_eq_true` lets us push the
monotonicity through the conjunction memberwise. -/
theorem admits_mono_discharge (tok : Token Ctx Gateway) (ctx : Ctx)
    {d d' : Discharges Gateway} (hle : Discharges.le d d')
    (h : tok.admits ctx d = true) : tok.admits ctx d' = true := by
  simp only [Token.admits, List.all_eq_true] at h ⊢
  intro c hc
  exact caveat_ok_mono c ctx hle (h c hc)

/-- **`admits_mono_subset` (PROVED)** — the set form of the keystone: as discharges accumulate,
the admissible-request set only *grows* (the suspended turns that become live). Dual in
polarity to `attenuate_subset` (where authority *shrinks* down a delegation chain): along the
delegation axis authority narrows, along the discharge/time axis admissibility widens. -/
theorem admits_mono_subset (tok : Token Ctx Gateway)
    {d d' : Discharges Gateway} (hle : Discharges.le d d') :
    {ctx | tok.admits ctx d = true} ⊆ {ctx | tok.admits ctx d' = true} :=
  fun ctx h => admits_mono_discharge tok ctx hle h

/-! ## Awaiting — a suspended / blocked cross-vat turn (a zkpromise / ConditionalTurn). -/

/-- **`Awaiting tok ctx d`** — the token does NOT admit the request under the current
discharges: a *suspended* cross-vat turn, blocked waiting for a gateway to settle. This is the
proposition-level `zkpromise` / `ConditionalTurn` — the turn exists but is not yet live. -/
def Awaiting (tok : Token Ctx Gateway) (ctx : Ctx) (d : Discharges Gateway) : Prop :=
  tok.admits ctx d = false

/-- `Awaiting` is decidable (admissibility is a `Bool`), so "is this turn still suspended?" is a
runnable check — the scheduler can poll it. -/
instance (tok : Token Ctx Gateway) (ctx : Ctx) (d : Discharges Gateway) :
    Decidable (Awaiting tok ctx d) :=
  inferInstanceAs (Decidable (_ = false))

/-! ## The resolution theorem — a suspended turn becomes admissible once gateways discharge. -/

/-- The single gateway-discharge step: flip gateway `g` to settled, leaving every other
gateway as it was. The forward-only update that resolves a third-party caveat. -/
def Discharges.settle (d : Discharges Gateway) [DecidableEq Gateway] (g : Gateway) :
    Discharges Gateway :=
  fun g' => if g' = g then true else d g'

/-- **`settle_le` (PROVED)** — settling a gateway is a forward step: `d ≤ d.settle g`. Settling
can only ADD the discharge of `g`; it retracts nothing. So `settle` is always a legal move in
the accumulating-discharge order, and the keystone applies to it. -/
theorem settle_le [DecidableEq Gateway] (d : Discharges Gateway) (g : Gateway) :
    Discharges.le d (d.settle g) := by
  intro g' hg'
  simp only [Discharges.settle]
  split <;> simp_all

/-- **`settle_discharges` (PROVED)** — after settling `g`, gateway `g` reads as discharged. The
resolution actually happens. -/
theorem settle_discharges [DecidableEq Gateway] (d : Discharges Gateway) (g : Gateway) :
    (d.settle g) g = true := by
  simp [Discharges.settle]

/-- **`resolve_forward` (PROVED) — the clean resolution theorem.** A turn suspended on a single
third-party gateway `g` (its *only* unmet caveat) becomes admissible the moment that gateway
discharges. Concretely: if the parent token already admits the request under `d`, then attaching
a third-party caveat on `g` (the await suspension) yields a token that admits the request *after*
`g` settles (`d.settle g`). This is the await authority-face closing the loop: suspend on a
gateway, the gateway discharges, the turn resolves — forward, by `admits_mono_discharge`.

It is a *clean provable instance* of resolution: we do not need to know which other caveats the
token carries, only that the parent admitted and the new suspension is exactly the gateway we
then settle. -/
theorem resolve_forward [DecidableEq Gateway]
    (tok : Token Ctx Gateway) (ctx : Ctx) (d : Discharges Gateway) (g : Gateway)
    (hpar : tok.admits ctx d = true) :
    (tok.attenuate (.thirdParty g)).admits ctx (d.settle g) = true := by
  -- the suspended turn = parent ∧ (third-party g)
  simp only [Token.admits, Token.attenuate, List.all_append, List.all_cons, List.all_nil,
    Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · -- the parent's caveats stay satisfied as `d → d.settle g` (the keystone, applied to the chain)
    have hpar' : tok.admits ctx (d.settle g) = true :=
      admits_mono_discharge tok ctx (settle_le d g) hpar
    simpa [Token.admits, List.all_eq_true] using hpar'
  · -- the new third-party caveat: gateway g has now discharged
    simp only [Caveat.ok]
    exact ⟨settle_discharges d g, trivial⟩

/-- **`awaiting_resolves` (PROVED)** — the same fact stated through `Awaiting`: a turn that was
suspended (`Awaiting`) on gateway `g` is no longer suspended after `g` discharges, *provided* the
parent admitted. The `zkpromise`/`ConditionalTurn` becomes a live turn. -/
theorem awaiting_resolves [DecidableEq Gateway]
    (tok : Token Ctx Gateway) (ctx : Ctx) (d : Discharges Gateway) (g : Gateway)
    (hpar : tok.admits ctx d = true) :
    ¬ Awaiting (tok.attenuate (.thirdParty g)) ctx (d.settle g) := by
  unfold Awaiting
  rw [resolve_forward tok ctx d g hpar]
  simp

/-! ## It runs (`#eval`): blocked on a gateway → admitted after discharge → never un-admitted. -/

/- `Height` (= the current block height) is reused from `Caveat`'s demos — a toy request
context. -/

/-- Two gateways resolving third-party caveats (an oracle and a co-signer, say). -/
inductive GW where
  | oracle
  | cosigner
  deriving DecidableEq, Repr

/-- A root biscuit windowed to `[100,200]`, then **suspended** on gateway `oracle`: a cross-vat
turn that cannot become live until the oracle gateway discharges it. -/
def suspendedTurn : Token Height GW :=
  ((({ kind := .biscuit, caveats := [] } : Token Height GW)
      |>.attenuate (.local (fun h => decide (100 ≤ h))))
      |>.attenuate (.local (fun h => decide (h ≤ 200))))
      |>.attenuate (.thirdParty .oracle)

/-- No gateway discharged yet. -/
def none' : Discharges GW := fun _ => false

/-- The oracle gateway has discharged (and only it). -/
def oracleSettled : Discharges GW := none'.settle .oracle

/-- Both gateways discharged. -/
def bothSettled : Discharges GW := oracleSettled.settle .cosigner

#eval suspendedTurn.admits 150 none'          -- false: blocked, oracle has not discharged
#eval suspendedTurn.admits 150 oracleSettled  -- true:  oracle discharged ⇒ the turn resolves forward
#eval suspendedTurn.admits 150 bothSettled    -- true:  MORE discharges never un-admit (keystone)

-- the height-window caveat still bites: discharge resolves the gateway, not the local gate
#eval suspendedTurn.admits 50  oracleSettled  -- false: 50 < 100 — a local caveat narrowed it out

-- `Awaiting` as a runnable scheduler poll: suspended under none', live under oracleSettled
#eval decide (Awaiting suspendedTurn 150 none')          -- true:  still suspended
#eval decide (Awaiting suspendedTurn 150 oracleSettled)  -- false: resolved

-- forward-only order witnesses: settling adds a discharge, retracts none
#eval (none'.settle GW.oracle) GW.oracle      -- true:  oracle now settled
#eval (none'.settle GW.oracle) GW.cosigner    -- false: untouched gateway unchanged

end Dregg2.Authority
