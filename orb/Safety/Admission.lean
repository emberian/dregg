/-
Safety.Admission — no-bypass of the admission surface.

Composition theorem: whatever reaches a handler was (a) selected by first-match
route dispatch from the declared route table, and (b) admitted by the cold-plane
serve gate — hence served on a *declared, bound* listener and matched a route the
*live config declares*. Nothing reaches a handler off the declared surface.

This composes two prior-wave results:

  * `Route.Match.bestMatch` — the total, deterministic first-match dispatcher,
    with `bestMatch_sound` (the chosen route matches) and `bestMatch_mem` (the
    chosen route is in the table);
  * `Policy.serveDecision` — the enforce-or-refuse serve gate, whose successful
    outcome is characterized here by `serveDecision_admits`: it fires only on a
    declared-and-bound listener for a declared route key.

The composed dispatcher `admit` runs them in series: pick the route, then gate
on its declared key.

Granularity note. The listener-declared / route-declared conclusions below are
stated at the *admission step* — checked against the config in force at that
moment. That is the correct granularity: `Policy.reload` may change the declared
route set freely (a bound listener's parameters are carried across identically,
but routes are not), so "route declared by the current config" is a per-request
gate property, not a standing property of past log entries. The listener half
*is* a standing log invariant, restated here as `admitted_listener_on_surface`
from `Policy.served_on_declared_listener`.
-/

import Policy.Invariant
import Route.Match

namespace Safety.Admission

open Policy Route.Match

/-- A request arriving at the composed surface: the listener it landed on, the
(already normalized) request path used for matching, and whether it is
plaintext. -/
structure Incoming where
  lid : Nat
  reqPath : List String
  plaintext : Bool

/-- The compiled route table: each route's handler payload is the declared
`Policy.RouteKey` it dispatches to, so dispatch and the policy gate speak the
same route identity. -/
abbrev RouteTable := List (Route.Match.Route Policy.RouteKey)

/-- Composed admission. Select the route by first-match; if one is found, run the
cold-plane serve gate on its declared key. Returns the recorded observation, or
`none` if either stage refuses. -/
def admit (rt : RouteTable) (inc : Incoming) (st : Running) : Option Served :=
  match bestMatch rt inc.reqPath with
  | some r => serveDecision inc.lid r.handler inc.plaintext st
  | none => none

/-! ### The serve gate, characterized -/

/-- A successful serve gate fires only on a declared, bound listener, for a
declared route key, and records exactly the request it admitted. This is the
cold-plane half of the no-bypass theorem, read off `Policy.serveDecision`. -/
theorem serveDecision_admits {lid : Nat} {rk : RouteKey} {pt : Bool}
    {st : Running} {s : Served} (h : serveDecision lid rk pt st = some s) :
    (st.cfg.listener? lid).isSome = true
      ∧ lid ∈ st.bound
      ∧ st.cfg.declaresRoute rk = true
      ∧ s = ⟨lid, rk, pt⟩ := by
  cases hl : st.cfg.listener? lid with
  | none => simp [serveDecision, hl] at h
  | some l =>
    simp only [serveDecision, hl] at h
    by_cases hb : lid ∈ st.bound
    · rw [if_neg (not_not_intro hb)] at h
      by_cases h1 : l.tlsRequired = true ∧ pt = true
      · rw [if_pos h1] at h; simp at h
      · rw [if_neg h1] at h
        by_cases h2 : l.tlsRequired = true ∧ lid ∉ st.tlsCtx
        · rw [if_pos h2] at h; simp at h
        · rw [if_neg h2] at h
          by_cases h3 : st.cfg.declaresRoute rk = false
          · rw [if_pos h3] at h; simp at h
          · rw [if_neg h3] at h
            have hs : (⟨lid, rk, pt⟩ : Served) = s := Option.some.inj h
            refine ⟨rfl, hb, ?_, hs.symm⟩
            cases hd : st.cfg.declaresRoute rk with
            | true => rfl
            | false => exact absurd hd h3
    · rw [if_pos hb] at h; simp at h

/-! ### The no-bypass theorem -/

/-- **No off-surface handler (per admission).** Anything the composed surface
admits was selected by first-match dispatch from a route in the declared table,
that route actually matches the request, and it was served on a declared, bound
listener for a route the live config declares. There is no path to a handler that
skips either the route table or the serve gate. -/
theorem admit_on_surface {rt : RouteTable} {inc : Incoming} {st : Running}
    {s : Served} (h : admit rt inc st = some s) :
    ∃ r : Route.Match.Route Policy.RouteKey,
      bestMatch rt inc.reqPath = some r
      ∧ r ∈ rt
      ∧ matchesAny inc.reqPath r = true
      ∧ st.cfg.declaresListener inc.lid
      ∧ inc.lid ∈ st.bound
      ∧ st.cfg.declaresRoute r.handler = true
      ∧ s = ⟨inc.lid, r.handler, inc.plaintext⟩ := by
  unfold admit at h
  split at h
  next r hbm =>
    obtain ⟨hls, hbnd, hrt, hs⟩ := serveDecision_admits h
    exact ⟨r, hbm, bestMatch_mem hbm, bestMatch_sound hbm, hls, hbnd, hrt, hs⟩
  next hbm => exact absurd h (by simp)

/-- Determinism corollary: the reached route is a highest-precedence match — no
matching route in the table outranks it (exact ≻ prefix ≻ default). Reuses
`Route.Match.bestMatch_class_max`. -/
theorem admit_route_is_max {rt : RouteTable} {inc : Incoming} {st : Running}
    {s : Served} (h : admit rt inc st = some s) :
    ∃ r, bestMatch rt inc.reqPath = some r ∧
      ∀ r' ∈ rt, matchesAny inc.reqPath r' = true →
        classRank r'.pat ≤ classRank r.pat := by
  obtain ⟨r, hbm, _, _, _, _, _, _⟩ := admit_on_surface h
  exact ⟨r, hbm, bestMatch_class_max hbm⟩

/-! ### The standing log invariant (listener half) -/

/-- **No off-surface listener in the observation log.** In every reachable state,
every recorded observation is attributed to a listener the live config declares —
the confinement invariant, composed from `Policy.reachable_wf` and
`Policy.served_on_declared_listener`. (The route-declared half is per-admission,
not a log invariant, because reload may change the declared routes.) -/
theorem admitted_listener_on_surface {c : Config} {st : Running}
    (h : Reachable c st) :
    ∀ s ∈ st.served, st.cfg.declaresListener s.lid :=
  served_on_declared_listener (reachable_wf h)

end Safety.Admission
