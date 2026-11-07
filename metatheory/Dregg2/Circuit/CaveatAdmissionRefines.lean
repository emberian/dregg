/-
# Dregg2.Circuit.CaveatAdmissionRefines — the in-circuit caveat-admission gadget REFINES the
  reified `CaveatPred` metatheory (the DREGGFI §7 caveat-in-circuit weld, Lean half).

This is the Lean refinement obligation (`docs/deos/EFFECTVM-SIDESTRUCTURE-ABI.md §3.6`) for the
in-circuit caveat-admission leaf
(`circuit-prove/src/caveat_admission_leaf_adapter.rs`). That leaf makes the DECIDABLE caveat
atoms a genuine IN-CIRCUIT admission: it WITNESSES a per-atom slack `s = ceiling − request` and
RANGE-CHECKS `s ∈ [0, 2^BOUND_BITS)`, so an OVER-authorized trade (past expiry / over budget /
wrong asset) has a wrapped-negative slack the range lookup REFUSES ⇒ UNSAT ⇒ no foldable leaf.

## What this file proves (the bridge circuit ⟷ Caveat.lean)

The gadget's arithmetic admission — the conjunction of `0 ≤ ceiling − request` slack facts — is
EQUIVALENT to `Token.admits` of the mandate's reified caveat chain (each atom a `Caveat.pred`
carrying its own request `view`, exactly `Dregg2/Authority/Caveat.lean`'s `CaveatPred` vocabulary):

  * `validUntil t`  — the expiry ceiling  (`req_time  ≤ t`), the circuit's `slack_vu ≥ 0`;
  * `heightLt   h`  — the strict ceiling  (`req_height < h`), the circuit's `slack_hl ≥ 0`;
  * `budget     b`  — the spend ceiling   (`trade_value ≤ b`), a `validUntil`-shaped `≤` atom
                      over the value view (the `Dregg2/Agent/Mandate.lean` budget);
  * asset scope     — `trade_asset = a`, expressed inside the reified vocabulary as
                      `validAfter a ∧ validUntil a` over the asset view (`a ≤ asset ∧ asset ≤ a`).

So the AIR FAITHFULLY EVALUATES the caveat predicate: `inCircuitAdmits ↔ token.admits`
(`inCircuit_iff_tokenAdmits`, BOTH poles, non-vacuous). And the in-circuit-admitted request is IN
the token's admissible set — with `attenuate_narrows`, it is in the LESS-attenuated parent's set
too (`inCircuit_admitted_narrows`), and an admitting token is a `Laws.Discharged` verify/find
witness (`inCircuit_admitted_discharges`, reusing `token_discharges`). This is the refinement
"the admitted request is in the attenuated set" the weld owes — turning the decidable-caveat slice
of "the mandate IS the proof" from executor-trusted into venue-verifiable.

## HONEST SCOPE (named, not overclaimed)

This refines the DECIDABLE atoms only. `Caveat.opaque` (an arbitrary `Ctx → Bool`) and
`Caveat.thirdParty` (a gateway discharge) are NOT reified and NOT forced in-circuit — a mandate
carrying such an atom stays executor-trusted for that atom. Pure, `#eval`-able, `sorry`-free.
-/
import Dregg2.Authority.Caveat

namespace Dregg2.Circuit.CaveatAdmission

open Dregg2.Authority

/-- The per-trade request context the gadget binds: the trade's `(time, height, value, asset)`,
each an `Int` (the circuit's range-bounded felt operand, lifted to `Int` for the ≤/< reasoning). -/
structure ReqCtx where
  time   : Int
  height : Int
  value  : Int
  asset  : Int
deriving Repr, DecidableEq

/-- The four request `view`s the reified caveat atoms read (`Caveat.pred p view` carries its own
seam — so a single token chain evaluates atoms over DIFFERENT request fields, exactly the gadget's
four operand pairs). -/
@[reducible] def timeView   : ReqCtx → Time := fun c => c.time
@[reducible] def heightView : ReqCtx → Time := fun c => c.height
@[reducible] def valueView  : ReqCtx → Time := fun c => c.value
@[reducible] def assetView  : ReqCtx → Time := fun c => c.asset

/-! ## The gadget's arithmetic admission — the SLACK-nonneg conjunction the AIR range-checks. -/

/-- **`inCircuitAdmits t h b a c`** — the gadget's in-circuit admission decision, as the exact
conjunction of the slack-nonneg facts the AIR proves (`0 ≤ ceiling − request` for each `≤`/`<`
atom, plus the asset equality). `t`/`h`/`b`/`a` are the caveat's `(validUntil, heightLt, budget,
asset)` params; `c` is the request. Every clause is the integer twin of one range-checked slack:
  * `slack_vu = t − c.time     ≥ 0`  (validUntil, inclusive ceiling)
  * `slack_hl = h − c.height − 1 ≥ 0` (heightLt, STRICT — the `−1` is the strictness)
  * `slack_bd = b − c.value    ≥ 0`  (budget)
  * asset equality `c.asset = a`. -/
def inCircuitAdmits (t h b a : Int) (c : ReqCtx) : Prop :=
  0 ≤ t - c.time ∧ 0 ≤ h - c.height - 1 ∧ 0 ≤ b - c.value ∧ c.asset = a

instance (t h b a : Int) (c : ReqCtx) : Decidable (inCircuitAdmits t h b a c) := by
  unfold inCircuitAdmits; infer_instance

/-! ## The mandate's reified caveat chain — the token the gadget's admission mirrors. -/

/-- A root biscuit over the request context (full authority; the mandate before attenuation). -/
def rootMandate : Token ReqCtx Unit := { kind := .biscuit, caveats := [] }

/-- **`caveatMandate t h b a`** — the mandate attenuated by the decidable caveat chain: the
`validUntil`/`heightLt`/`budget`/asset atoms, each a reified `Caveat.pred` carrying its own view.
Authority = the meet of all caveats (`Token.admits` conjoins them), exactly the gadget's four
operand pairs. The asset scope is `validAfter a ∧ validUntil a` over the asset view (i.e.
`a ≤ asset ∧ asset ≤ a` ⟺ `asset = a`), authored inside the reified vocabulary. -/
def caveatMandate (t h b a : Int) : Token ReqCtx Unit :=
  ((((rootMandate.attenuate (.pred (.validUntil t) timeView)).attenuate
      (.pred (.heightLt h) heightView)).attenuate
      (.pred (.validUntil b) valueView)).attenuate
      (.pred (.validAfter a) assetView)).attenuate
      (.pred (.validUntil a) assetView)

/-! ## THE BRIDGE — the AIR admission ⟺ the reified caveat token admission (both poles). -/

/-- **`inCircuit_iff_tokenAdmits`** — the gadget's slack-nonneg admission is EXACTLY the reified
caveat mandate's decision. The circuit's range-checked `0 ≤ ceiling − request` conjunction holds
IFF `Token.admits` of the reified chain returns `true` — so the AIR faithfully evaluates the
`CaveatPred` predicate `Caveat.lean` proves the metatheory of (not a trusted aggregate bit). -/
theorem inCircuit_iff_tokenAdmits (t h b a : Int) (c : ReqCtx) :
    inCircuitAdmits t h b a c ↔ (caveatMandate t h b a).admits c noDischarges = true := by
  unfold inCircuitAdmits caveatMandate rootMandate
  -- `Time` unfolds to `Int` so omega reads the caveat-eval atoms as linear-arithmetic facts.
  simp only [Token.admits, Token.attenuate, Caveat.ok, CaveatPred.eval, Time,
    timeView, heightView, valueView, assetView, List.all_cons, List.all_nil,
    List.cons_append, List.nil_append, Bool.and_eq_true, Bool.and_true,
    decide_eq_true_eq]
  -- The goal is an iff of two linear-arithmetic conjunctions (the asset equality ⟺ the
  -- `a ≤ asset ∧ asset ≤ a` double-bound); omega closes each direction.
  constructor
  · intro h; omega
  · intro h; omega

/-! ### Non-vacuity — the bridge is a GENUINE equivalence (both poles inhabited). -/

/-- A within-caveat request: time 150 ≤ 200, height 90 < 100, value 40 ≤ 100, asset 7 = 7. The
POSITIVE pole of the tests' `within_caveat` fixture. -/
def withinReq : ReqCtx := ⟨150, 90, 40, 7⟩

/-- POSITIVE: the within-caveat request is admitted in-circuit AND by the reified mandate. -/
theorem within_admits : inCircuitAdmits 200 100 100 7 withinReq := by
  unfold inCircuitAdmits withinReq; refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem within_token_admits : (caveatMandate 200 100 100 7).admits withinReq noDischarges = true :=
  (inCircuit_iff_tokenAdmits 200 100 100 7 withinReq).mp within_admits

/-- NEGATIVE — past expiry: time 250 > validUntil 200. Neither the AIR nor the token admits. -/
def pastExpiryReq : ReqCtx := ⟨250, 90, 40, 7⟩
theorem pastExpiry_refused : ¬ inCircuitAdmits 200 100 100 7 pastExpiryReq := by
  unfold inCircuitAdmits pastExpiryReq; decide
theorem pastExpiry_token_refused :
    (caveatMandate 200 100 100 7).admits pastExpiryReq noDischarges = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  exact pastExpiry_refused ((inCircuit_iff_tokenAdmits 200 100 100 7 pastExpiryReq).mpr h)

/-- NEGATIVE — over budget: value 500 > budget 100. Refused both ways. -/
def overBudgetReq : ReqCtx := ⟨150, 90, 500, 7⟩
theorem overBudget_refused : ¬ inCircuitAdmits 200 100 100 7 overBudgetReq := by
  unfold inCircuitAdmits overBudgetReq; decide

/-- NEGATIVE — over height (STRICT): height 100 is NOT `< heightLt 100`. Refused both ways. -/
def overHeightReq : ReqCtx := ⟨150, 100, 40, 7⟩
theorem overHeight_refused : ¬ inCircuitAdmits 200 100 100 7 overHeightReq := by
  unfold inCircuitAdmits overHeightReq; decide

/-- NEGATIVE — wrong asset: asset 9 ≠ scoped asset 7. Refused both ways. -/
def wrongAssetReq : ReqCtx := ⟨150, 90, 40, 9⟩
theorem wrongAsset_refused : ¬ inCircuitAdmits 200 100 100 7 wrongAssetReq := by
  unfold inCircuitAdmits wrongAssetReq; decide

/-- **`inCircuit_bridge_nonvacuous`** — the bridge is a genuine, non-trivial equivalence: a
within-caveat request is admitted, and each over-authorized request (past expiry / over budget /
over height / wrong asset) is REFUSED. No laundered vacuity. -/
theorem inCircuit_bridge_nonvacuous :
    inCircuitAdmits 200 100 100 7 withinReq ∧
    ¬ inCircuitAdmits 200 100 100 7 pastExpiryReq ∧
    ¬ inCircuitAdmits 200 100 100 7 overBudgetReq ∧
    ¬ inCircuitAdmits 200 100 100 7 overHeightReq ∧
    ¬ inCircuitAdmits 200 100 100 7 wrongAssetReq :=
  ⟨within_admits, pastExpiry_refused, overBudget_refused, overHeight_refused, wrongAsset_refused⟩

/-! ## THE REFINEMENT — an in-circuit-admitted request is IN the attenuated admissible set. -/

/-- **`inCircuit_admitted_narrows`** — the refinement `attenuate_narrows` gives: a request the
gadget admits in-circuit (so the fully-attenuated `caveatMandate` admits it) is ALSO admitted by
the LESS-attenuated parent (the mandate before its last asset-caveat edge). The admitted request
lies in the parent's admissible set — the "admitted ⊆ the attenuated set" direction the weld owes,
proved by chaining the circuit bridge with the proven `attenuate_narrows`. -/
theorem inCircuit_admitted_narrows (t h b a : Int) (c : ReqCtx)
    (hadm : inCircuitAdmits t h b a c) :
    ((((rootMandate.attenuate (.pred (.validUntil t) timeView)).attenuate
        (.pred (.heightLt h) heightView)).attenuate
        (.pred (.validUntil b) valueView)).attenuate
        (.pred (.validAfter a) assetView)).admits c noDischarges = true :=
  attenuate_narrows _ _ c noDischarges
    ((inCircuit_iff_tokenAdmits t h b a c).mp hadm)

/-- **`inCircuit_admitted_discharges`** — an in-circuit-admitted request makes the reified caveat
mandate a `Laws.Discharged` verify/find-seam witness (`token_discharges`): the venue-checkable
authorization is a `Verify`. The circuit's range-checked admission IS the discharge — not an
executor-trusted `caveatBit`. -/
theorem inCircuit_admitted_discharges (t h b a : Int) (c : ReqCtx)
    (hadm : inCircuitAdmits t h b a c) :
    Laws.Discharged (P := ReqCtx) (W := Token ReqCtx Unit × Discharges Unit)
      c (caveatMandate t h b a, noDischarges) :=
  token_discharges (caveatMandate t h b a) c noDischarges
    ((inCircuit_iff_tokenAdmits t h b a c).mp hadm)

/-! ### It runs (`#guard`). -/

#guard decide (inCircuitAdmits 200 100 100 7 withinReq)
#guard decide (inCircuitAdmits 200 100 100 7 pastExpiryReq) == false
#guard decide (inCircuitAdmits 200 100 100 7 overBudgetReq) == false
#guard decide (inCircuitAdmits 200 100 100 7 overHeightReq) == false
#guard decide (inCircuitAdmits 200 100 100 7 wrongAssetReq) == false
#guard (caveatMandate 200 100 100 7).admits withinReq noDischarges

#assert_axioms inCircuit_iff_tokenAdmits
#assert_axioms inCircuit_bridge_nonvacuous
#assert_axioms inCircuit_admitted_narrows
#assert_axioms inCircuit_admitted_discharges

end Dregg2.Circuit.CaveatAdmission
