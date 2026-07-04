import Cache

/-!
# Correctness of HTTP cache freshness (RFC 9111 §4.2)

`Cache.lean` establishes *safety* facts about the freshness machinery — the
freshness/age arithmetic is total, age is monotone in the clock, a 304 resets
age to zero. Those constrain how the numbers move. They do **not**, on their
own, say that `Cache.isFresh` returns the answer the RFC *mandates* for a
response as received off the wire.

This file upgrades that to a *correctness* claim: the freshness decision the
implementation computes MATCHES the one RFC 9111 §4.2 dictates.

## The specification, taken from the RFC

RFC 9111 §4.2 defines a stored response to be fresh exactly when

    response_is_fresh = (freshness_lifetime > current_age)          (§4.2, l.621)

and §4.2.3 ("Calculating Age") fixes `current_age` from the response's own
headers and two clocks — the request time and the receive time — by the
named-variable recipe (§4.2.3, l.765–782):

    apparent_age          = max(0, response_time - date_value);
    response_delay        = response_time - request_time;
    corrected_age_value   = age_value + response_delay;
    corrected_initial_age = max(apparent_age, corrected_age_value);
    resident_time         = now - response_time;
    current_age           = corrected_initial_age + resident_time;

The spec below is a *direct transcription* of those formulas over the raw
response inputs (`date_value`, `age_value`, `request_time`, `response_time`,
`freshness_lifetime`) and the query clock `now`. It is written WITHOUT reference
to `Cache.mkMeta`, `Cache.Meta.currentAge`, or `Cache.Meta.isFresh` — it says
what the freshness answer SHOULD be, not what the implementation computes. In
particular the `max(0, …)` clamp on `apparent_age` is written out explicitly,
whereas the implementation elides it by relying on `Nat` truncated subtraction;
closing that gap is the content of the refinement proof.

## What is proven

* `specCurrentAge_eq` — the RFC's `current_age` recipe agrees with the age the
  implementation stores via `Cache.mkMeta` and reads via `Cache.Meta.currentAge`.
* `isFresh_refines_spec` — **the refinement theorem**: for every response `r`,
  receive time, and query clock, the implementation's freshness Bool equals the
  spec's. The implementation refines the RFC.
* `isFresh_spec_iff` — the same as an `iff` over the strict `<` boundary.

## Non-vacuity (a wrong implementation FAILS the spec)

* `boundary_is_stale` — at the boundary `current_age = freshness_lifetime` the
  spec is `false` (STALE). RFC 9111 §4.2 uses strict `>`, so the boundary is not
  fresh; `boundary_witness` is a closed instance and, with the refinement, so is
  `impl_boundary_stale` for the real `Cache` code.
* `reject_always_fresh` — an implementation that reported everything fresh
  disagrees with the spec on `boundary_witness`; the spec is not the constant
  `true`.
* `age_header_matters` — a response whose `Age` header alone pushes it stale is
  reported stale by the spec; an implementation that ignored `age_value` (used
  only `apparent_age`) would call it fresh, so it would fail. This pins the
  §4.2.3 `corrected_age_value` branch.
* `clock_matters` — the spec flips from fresh to stale as `now` advances; an
  implementation that dropped `resident_time` from `current_age` would answer
  the same for both clocks and so fail one. This pins the §4.2.3 `resident_time`
  term.
-/

namespace CacheFreshCorrect

open Cache

/-! ## The independent specification (RFC 9111 §4.2, §4.2.3) -/

/-- RFC 9111 §4.2.3 `current_age`, transcribed directly from the named-variable
recipe (l.765–782) over the raw response inputs. Independent of `Cache.Meta`.
The `max 0` on `apparent_age` is the RFC's explicit non-negativity clamp. -/
def specCurrentAge (dateValue ageValue requestTime responseTime now : Nat) : Nat :=
  let apparent_age          := max 0 (responseTime - dateValue)
  let response_delay        := responseTime - requestTime
  let corrected_age_value   := ageValue + response_delay
  let corrected_initial_age := max apparent_age corrected_age_value
  let resident_time         := now - responseTime
  corrected_initial_age + resident_time

/-- RFC 9111 §4.2 (l.621): `response_is_fresh = (freshness_lifetime > current_age)`.
The RFC's `>` is transcribed as the strict `current_age < freshness_lifetime`. -/
def specIsFresh
    (freshnessLifetime dateValue ageValue requestTime responseTime now : Nat) : Bool :=
  decide (specCurrentAge dateValue ageValue requestTime responseTime now < freshnessLifetime)

/-! ## The refinement: `Cache.isFresh` computes exactly the RFC quantity -/

/-- The RFC's `current_age` recipe agrees with the age the implementation stores
(`Cache.mkMeta`) and reads (`Cache.Meta.currentAge`). The `max 0` clamp is
discharged against `Nat` truncated subtraction here. -/
theorem specCurrentAge_eq (r : Resp) (responseTime now : Nat) :
    specCurrentAge r.dateValue r.ageValue r.requestTime responseTime now
      = (mkMeta r responseTime).currentAge now := by
  simp only [specCurrentAge, Meta.currentAge, mkMeta]
  omega

/-- **Refinement theorem.** For every response as received and every query
clock, the implementation's freshness Bool (`Cache.mkMeta` then
`Cache.Meta.isFresh`) equals the RFC-mandated answer. The real code refines the
spec on ALL inputs. -/
theorem isFresh_refines_spec (r : Resp) (responseTime now : Nat) :
    (mkMeta r responseTime).isFresh now
      = specIsFresh r.freshnessLifetime r.dateValue r.ageValue r.requestTime responseTime now := by
  unfold Meta.isFresh specIsFresh
  rw [specCurrentAge_eq]
  rfl

/-- The refinement as an `iff` over the strict boundary. -/
theorem isFresh_spec_iff (r : Resp) (responseTime now : Nat) :
    (mkMeta r responseTime).isFresh now = true
      ↔ specCurrentAge r.dateValue r.ageValue r.requestTime responseTime now
          < r.freshnessLifetime := by
  rw [isFresh_refines_spec]
  unfold specIsFresh
  exact decide_eq_true_iff

/-! ## Non-vacuity -/

/-- **The boundary is stale.** When `current_age = freshness_lifetime` the spec
returns `false`: RFC 9111 §4.2 uses strict `>`, so equality is NOT fresh. -/
theorem boundary_is_stale
    (L dateValue ageValue requestTime responseTime now : Nat)
    (h : specCurrentAge dateValue ageValue requestTime responseTime now = L) :
    specIsFresh L dateValue ageValue requestTime responseTime now = false := by
  unfold specIsFresh
  rw [h]
  simp

/-- A closed boundary instance: `current_age = 5 = freshness_lifetime` ⇒ stale.
(date=0, age=0, request=0, response=0, now=5, lifetime=5 ⇒ current_age = 5.) -/
theorem boundary_witness : specIsFresh 5 0 0 0 0 5 = false := by decide

/-- Just past the boundary is fresh (`current_age = 5 < 6`) — so the spec is not
the constant `false` either. -/
theorem fresh_witness : specIsFresh 6 0 0 0 0 5 = true := by decide

/-- The real `Cache` code inherits the stale boundary through the refinement:
the response with lifetime 5, all clocks 0, received at time 0, queried at
`now = 5` is reported STALE. An "everything is fresh" implementation would
report `true` here and thus violate `isFresh_refines_spec`. -/
theorem impl_boundary_stale :
    (mkMeta { body := ⟨0⟩, dateValue := 0, ageValue := 0, requestTime := 0,
              freshnessLifetime := 5, etag := none } 0).isFresh 5 = false := by
  rw [isFresh_refines_spec]; exact boundary_witness

/-- The spec is not the constant `true`: there is an input it rejects, so any
"always fresh" implementation disagrees with it. -/
theorem reject_always_fresh : specIsFresh 5 0 0 0 0 5 ≠ true := by
  rw [boundary_witness]; decide

/-- **The `Age` header matters (§4.2.3 `corrected_age_value`).** With
`age_value = 5`, `freshness_lifetime = 3`, and all clocks 0, `apparent_age = 0`
but `corrected_age_value = 5`, so `current_age = 5 ≥ 3`: STALE. An implementation
that ignored `age_value` (took `current_age = apparent_age = 0 < 3`) would call
it fresh and fail. -/
theorem age_header_matters : specIsFresh 3 0 5 0 0 0 = false := by decide

/-- **The clock matters (§4.2.3 `resident_time`).** The same response is fresh at
`now = 0` and stale at `now = 5`: `current_age` grows with the clock. An
implementation that dropped `resident_time` would answer identically for both
and fail one. -/
theorem clock_matters :
    specIsFresh 3 0 0 0 0 0 = true ∧ specIsFresh 3 0 0 0 0 5 = false := by
  constructor <;> decide

end CacheFreshCorrect

#print axioms CacheFreshCorrect.isFresh_refines_spec
#print axioms CacheFreshCorrect.specCurrentAge_eq
#print axioms CacheFreshCorrect.isFresh_spec_iff
#print axioms CacheFreshCorrect.boundary_is_stale
#print axioms CacheFreshCorrect.age_header_matters
#print axioms CacheFreshCorrect.clock_matters
