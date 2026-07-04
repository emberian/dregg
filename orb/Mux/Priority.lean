/-!
# Mux.Priority — RFC 9218 Extensible Priorities

The scheduling signal shared by HTTP/2 and HTTP/3 stream multiplexing
(RFC 9218 §4):

* **urgency** — an integer 0..7 (default 3); *lower values are higher
  priority* (scheduled first).
* **incremental** — a boolean (default false); an incremental resource
  benefits from interleaved delivery, a non-incremental one should be
  completed before starting others of the same urgency (RFC 9218 §10).

We collapse the two-field signal into a single **rank** natural number,

```
rank ⟨u, i⟩ = 2 * u + (if i then 1 else 0)
```

so that "scheduled before" is exactly `rank · < rank ·`. This encoding is
*injective* (`rank_inj`): distinct priorities get distinct ranks, so the
induced order is a genuine linear order on `(urgency, incremental)` pairs, and
a *strictly lower urgency always outranks*, regardless of the incremental flag
(`rank_lt_of_urgency_lt`) — the headline invariant behind priority respect.
-/

namespace Mux

/-- A stream identifier. HTTP/2 uses a 31-bit space (RFC 9113 §5.1.1); we do
not need the bound for any scheduling theorem, so we model it as `Nat`. -/
abbrev StreamId := Nat

/-- RFC 9218 §4 priority parameters. `urgency` 0..7 (lower = higher priority),
`incremental` the interleaving hint. We do not enforce the 0..7 bound in the
type; every theorem here holds for arbitrary `urgency : Nat`, and the RFC's
clamp is a parser concern, not a scheduler one. -/
structure Priority where
  urgency : Nat
  incremental : Bool
deriving Repr, DecidableEq

namespace Priority

/-- The scheduling rank: lower rank = scheduled first. Urgency dominates;
within an urgency, non-incremental (`i = false`, contributing `0`) precedes
incremental (`i = true`, contributing `1`). -/
def rank (p : Priority) : Nat := 2 * p.urgency + (if p.incremental then 1 else 0)

/-- The default priority (RFC 9218 §4): urgency 3, non-incremental. -/
def default : Priority := ⟨3, false⟩

/-- **Strict-urgency dominance.** A strictly lower urgency value always yields a
strictly lower rank — i.e. a strictly-higher-priority stream, no matter the
incremental flags on either side. This is the arithmetic core of "priority
respected". -/
theorem rank_lt_of_urgency_lt {p q : Priority} (h : p.urgency < q.urgency) :
    rank p < rank q := by
  have hp : (if p.incremental then 1 else 0) ≤ 1 := by
    cases p.incremental <;> simp
  have hq : (0 : Nat) ≤ (if q.incremental then 1 else 0) := Nat.zero_le _
  unfold rank
  omega

/-- The incremental contribution `if i then 1 else 0` recovers the flag: this
0/1 encoding of a boolean is injective. -/
theorem incBit_inj {a b : Bool}
    (h : (if a then (1 : Nat) else 0) = (if b then 1 else 0)) : a = b := by
  cases a <;> cases b <;> simp_all

/-- **Rank is injective.** Distinct `(urgency, incremental)` pairs have distinct
ranks, so `rank` induces a genuine linear order (no priority collisions beyond
true equality). -/
theorem rank_inj {p q : Priority} (h : rank p = rank q) : p = q := by
  obtain ⟨pu, pi⟩ := p
  obtain ⟨qu, qi⟩ := q
  simp only [rank] at h
  have hip : (if pi then (1 : Nat) else 0) ≤ 1 := by cases pi <;> simp
  have hiq : (if qi then (1 : Nat) else 0) ≤ 1 := by cases qi <;> simp
  have hb : (if pi then (1 : Nat) else 0) = (if qi then 1 else 0) := by omega
  have hu : pu = qu := by omega
  have hpi : pi = qi := incBit_inj hb
  subst hu; subst hpi; rfl

end Priority
end Mux
