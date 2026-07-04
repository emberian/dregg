/-
Safety.EarlyData — early-data (0-RTT / 0.5-RTT) admission safety.

Composition theorem: early application data reaches a handler only when BOTH

  * the TLS record machine actually accepted early data — its `earlyDataAccepted`
    flag is set (else the drained early plaintext is dropped and never surfaces),
    established by `Tls.early_data_needs_flag`; and
  * the route it dispatches to is marked early-data-safe by the config surface.

`earlyDispatch` runs the route table over the parsed early request and admits the
result only through the `safe` gate. The end-to-end theorem chains the TLS flag
lemma (the transport hook) to the route + safe gate (the dispatch hook):

    Tls delivered early bytes  →  earlyDataAccepted = true          (Tls hook)
    earlyDispatch admitted r   →  r ∈ table ∧ r matches ∧ safe r     (Route + gate)

so a handler is reached with early data only via an accepted-and-safe route.

Hooks used, and what is owed
----------------------------
Present and used:
  * `Tls.Config.earlyDataAccepted : Bool` and `Tls.early_data_needs_flag` — the
    TLS machine emits `deliverEarly` only under the flag. USED.
  * `Route.Match.bestMatch` + `bestMatch_sound` + `bestMatch_mem` — first-match
    dispatch is sound and in-table. USED.

Supplied here (surface annotation, not a lower-lib field): `safe : H → Bool`, the
config marking of which routes/handlers may run on early data. The `Route.Match`
library carries no early-data-safe field, so this marking lives at the composed
surface; it is exactly "a route whose handler the config marks early-data-safe".

UNCLOSED (named, with what is owed):
  * `earlySafe_handler_idempotent` — that a `safe`-marked handler's effect is
    genuinely replay-tolerant (idempotent) is a per-handler *semantic* obligation,
    not provable over the abstract handler type `H`. It is discharged either
    per concrete handler, or by bounding the number of accepted early-data units
    to at most one via the transport anti-replay lane
    (`Quic.Replay.accepted_at_most_once`, F-9) — which caps replays but does not by
    itself make a non-idempotent handler safe. This theorem proves the *gate*
    (early data reaches a handler only when flag ∧ safe); the idempotence of a
    gated handler is owed separately.
-/

import Tls.Theorems
import Route.Match

namespace Safety.EarlyData

open Route.Match

/-- Dispatch parsed early-data bytes to a handler, gated by the config's
early-data-safe marking. `parse` turns the early bytes into the request path
used for matching; `safe` is the per-handler early-data-safe flag. A route is
admitted only if it matches AND is marked safe. -/
def earlyDispatch {H : Type} (parse : Tls.Bytes → List String)
    (rt : List (Route.Match.Route H)) (safe : H → Bool)
    (d : Tls.Bytes) : Option (Route.Match.Route H) :=
  match bestMatch rt (parse d) with
  | some r => if safe r.handler = true then some r else none
  | none => none

/-- The dispatch gate, characterized: a route it admits is in the table, actually
matches the parsed early request, and is marked early-data-safe. -/
theorem earlyDispatch_gate {H : Type} {parse : Tls.Bytes → List String}
    {rt : List (Route.Match.Route H)} {safe : H → Bool} {d : Tls.Bytes}
    {r : Route.Match.Route H} (h : earlyDispatch parse rt safe d = some r) :
    r ∈ rt ∧ matchesAny (parse d) r = true ∧ safe r.handler = true := by
  unfold earlyDispatch at h
  split at h
  next r' hbm =>
    split at h
    next hsafe =>
      obtain rfl := Option.some.inj h
      exact ⟨bestMatch_mem hbm, bestMatch_sound hbm, hsafe⟩
    next _ => exact absurd h (by simp)
  next _ => exact absurd h (by simp)

/-- **Early-data admission safety (end-to-end).** If the TLS record machine
delivered early plaintext `d` in a step, and the early dispatcher admitted it to
route `r`, then the acceptance flag was set AND `r` is a table route that matches
and is marked early-data-safe. Early data reaches a handler only via an
accepted-and-safe route.

Composes `Tls.early_data_needs_flag` (the flag) with `earlyDispatch_gate`
(Route soundness/membership + the safe marking). -/
theorem early_reaches_requires_flag_and_safe {H : Type}
    (tcfg : Tls.Config) (ts : Tls.St) (ti : Tls.Input)
    (parse : Tls.Bytes → List String) (rt : List (Route.Match.Route H))
    (safe : H → Bool) {d : Tls.Bytes} {r : Route.Match.Route H}
    (hemit : Tls.Output.deliverEarly d ∈ (Tls.step tcfg ts ti).2.out)
    (hdisp : earlyDispatch parse rt safe d = some r) :
    tcfg.earlyDataAccepted = true
      ∧ safe r.handler = true
      ∧ r ∈ rt
      ∧ matchesAny (parse d) r = true := by
  have hflag := Tls.early_data_needs_flag tcfg ts ti d hemit
  obtain ⟨hmem, hmatch, hsafe⟩ := earlyDispatch_gate hdisp
  exact ⟨hflag, hsafe, hmem, hmatch⟩

/-- Contrapositive, flag form: with the acceptance flag off, the TLS machine
delivers no early plaintext at all — so the dispatcher is never even reached. A
route not marked safe is likewise never admitted (`earlyDispatch` returns `none`).
Both refusals are visible in `earlyDispatch`'s definition; this states the flag
half as a standing fact. -/
theorem no_early_delivery_without_flag (tcfg : Tls.Config) (ts : Tls.St)
    (ti : Tls.Input) (d : Tls.Bytes)
    (hoff : tcfg.earlyDataAccepted = false) :
    Tls.Output.deliverEarly d ∉ (Tls.step tcfg ts ti).2.out := by
  intro hemit
  have := Tls.early_data_needs_flag tcfg ts ti d hemit
  rw [hoff] at this
  exact Bool.noConfusion this

/-- Unsafe routes are never admitted for early data: if the matched route is not
marked safe, `earlyDispatch` refuses. -/
theorem earlyDispatch_refuses_unsafe {H : Type} (parse : Tls.Bytes → List String)
    (rt : List (Route.Match.Route H)) (safe : H → Bool) (d : Tls.Bytes)
    {r : Route.Match.Route H} (h : earlyDispatch parse rt safe d = some r) :
    safe r.handler = true :=
  (earlyDispatch_gate h).2.2

end Safety.EarlyData
