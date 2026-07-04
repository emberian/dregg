/-
Trace.W3C — the W3C `traceparent` structure, a total parser, and the
child-span derivation used to propagate a trace across a hop.

A `traceparent` value is a fixed-shape token stream

    version(2) '-' traceId(32) '-' parentId(16) '-' flags(2)

over hex nibbles and `-` delimiters (`Tok`).  `parse` consumes that shape and
rejects an all-zero trace-id or parent-id (per the spec); it is a *total*
function into `Except ParseErr (TraceParent × List Tok)`, returning the
structure and the unconsumed tail.

Propagation across a hop keeps the trace-id, keeps the flags, and installs a
freshly generated span id as the new parent-id — that is `childSpan`.  When the
inbound value is malformed, `parse` errors and the hop falls back to a brand-new
trace (`freshTrace`).  The `Step` relation names those two transitions; the
total function `propagate` realizes it.

Headline results:

  * `parse_suffix` / `parse_consumed_monotone` (**theorem 3, parse half**) —
    the parser is consumed-monotone: the returned tail is a suffix of the
    input, so it never grows the input.  Totality is definitional
    (`parse_total`).
  * `childSpan_traceId`, `childSpan_parentId`, `childSpan_fresh`,
    `chain_traceId` (**theorem 3, span half**) — a child span preserves the
    trace-id and installs the fresh parent-id; along any propagation chain the
    trace-id is invariant.
  * `propagate_ok_traceId` (**theorem 2 for traces**) — the outbound trace-id
    equals the inbound trace-id when the inbound value parses.
  * `propagate_step`, `propagate_malformed` (**theorem 4**) — every input steps
    (totality of the transition); a malformed inbound value is a total error and
    falls back to a fresh trace, which is exactly the `Step.fallback`
    transition.
-/

import Trace.Basic

namespace Trace

/-- A hex nibble: one of sixteen values. -/
abbrev Nibble := Fin 16

/-- A single token of a `traceparent` value: a hex nibble or the `-` field
delimiter. -/
inductive Tok where
  /-- The `-` field delimiter. -/
  | dash
  /-- A hex nibble. -/
  | nib (n : Nibble)
deriving Repr, DecidableEq

/-- The parsed W3C `traceparent` structure — each field a fixed-width run of hex
nibbles. -/
structure TraceParent where
  /-- Version: 2 nibbles (spec version `00`). -/
  version : List Nibble
  /-- Trace id: 32 nibbles (16 bytes). -/
  traceId : List Nibble
  /-- Parent id (this span): 16 nibbles (8 bytes). -/
  parentId : List Nibble
  /-- Trace flags: 2 nibbles. -/
  flags : List Nibble
deriving Repr, DecidableEq

/-- A parse error. -/
inductive ParseErr where
  /-- The version field was missing or short. -/
  | badVersion
  /-- A `-` delimiter was missing. -/
  | badDelim
  /-- The trace-id field was missing or short. -/
  | badTraceId
  /-- The parent-id field was missing or short. -/
  | badParentId
  /-- The flags field was missing or short. -/
  | badFlags
  /-- The trace-id was all zero (forbidden by the spec). -/
  | zeroTraceId
  /-- The parent-id was all zero (forbidden by the spec). -/
  | zeroParentId
deriving Repr, DecidableEq

/-- Consume exactly `n` nibble tokens off the front; fail on a delimiter or
short input. -/
def takeNibs : Nat → List Tok → Option (List Nibble × List Tok)
  | 0, ts => some ([], ts)
  | n + 1, (.nib x :: ts) =>
      match takeNibs n ts with
      | some (xs, r) => some (x :: xs, r)
      | none => none
  | _ + 1, _ => none

/-- Consume a single `-` delimiter. -/
def expectDash : List Tok → Option (List Tok)
  | .dash :: ts => some ts
  | _ => none

/-- Whether a nibble run is entirely zero (the all-zero id the spec rejects). -/
def allZero (xs : List Nibble) : Bool := xs.all (fun n => n == 0)

/-- Total parse of a `traceparent` token stream:
`version(2) - traceId(32) - parentId(16) - flags(2)`, rejecting an all-zero
trace-id or parent-id.  On success returns the structure and the unconsumed
tail. -/
def parse (ts : List Tok) : Except ParseErr (TraceParent × List Tok) :=
  match takeNibs 2 ts with
  | none => .error .badVersion
  | some (ver, ts1) =>
  match expectDash ts1 with
  | none => .error .badDelim
  | some ts2 =>
  match takeNibs 32 ts2 with
  | none => .error .badTraceId
  | some (tid, ts3) =>
  match expectDash ts3 with
  | none => .error .badDelim
  | some ts4 =>
  match takeNibs 16 ts4 with
  | none => .error .badParentId
  | some (pid, ts5) =>
  match expectDash ts5 with
  | none => .error .badDelim
  | some ts6 =>
  match takeNibs 2 ts6 with
  | none => .error .badFlags
  | some (fl, ts7) =>
  match allZero tid, allZero pid with
  | true, _ => .error .zeroTraceId
  | false, true => .error .zeroParentId
  | false, false => .ok (⟨ver, tid, pid, fl⟩, ts7)

/-! ### Fresh material and the two propagation constructions -/

/-- Freshly generated material for a hop: a new trace id (used only on the
fallback path), a new span id (the new parent-id), and flags. -/
structure Fresh where
  /-- A brand-new trace id (fallback path only). -/
  traceId : List Nibble
  /-- A freshly generated span id — the child's new parent-id. -/
  spanId : List Nibble
  /-- Flags to stamp onto a brand-new trace. -/
  flags : List Nibble
deriving Repr, DecidableEq

/-- Derive the child span: keep version, trace-id and flags; install the fresh
span id as the new parent-id. -/
def childSpan (span : List Nibble) (tp : TraceParent) : TraceParent :=
  { tp with parentId := span }

/-- Construct a brand-new trace context (the fallback when no valid inbound
traceparent exists).  Version is the current spec version `00`. -/
def freshTrace (f : Fresh) : TraceParent :=
  { version := [0, 0], traceId := f.traceId, parentId := f.spanId, flags := f.flags }

/-! ### Consumed-monotonicity building blocks -/

/-- `takeNibs` returns a suffix of its input. -/
theorem takeNibs_suffix : ∀ (n : Nat) (ts : List Tok) (xs : List Nibble) (r : List Tok),
    takeNibs n ts = some (xs, r) → r <:+ ts := by
  intro n
  induction n with
  | zero =>
    intro ts xs r h
    simp only [takeNibs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact List.suffix_refl _
  | succ n ih =>
    intro ts xs r h
    cases ts with
    | nil => simp [takeNibs] at h
    | cons t ts' =>
      cases t with
      | dash => simp [takeNibs] at h
      | nib x =>
        simp only [takeNibs] at h
        cases hn : takeNibs n ts' with
        | none => simp [hn] at h
        | some p =>
          obtain ⟨xs', r'⟩ := p
          simp only [hn, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, hr⟩ := h
          have hsuf : r' <:+ ts' := ih ts' xs' r' hn
          have hstep : r' <:+ Tok.nib x :: ts' := hsuf.trans (List.suffix_cons (Tok.nib x) ts')
          exact hr ▸ hstep

/-- `expectDash` returns a suffix of its input. -/
theorem expectDash_suffix {ts r : List Tok} (h : expectDash ts = some r) : r <:+ ts := by
  cases ts with
  | nil => simp [expectDash] at h
  | cons t ts' =>
    cases t with
    | dash =>
      simp only [expectDash, Option.some.injEq] at h
      rw [← h]
      exact List.suffix_cons Tok.dash ts'
    | nib x => simp [expectDash] at h

/-! ### Theorem 3 (parse half) — parse is total and consumed-monotone -/

/-- Totality: `parse` returns a result on every input. -/
theorem parse_total (ts : List Tok) :
    (∃ v, parse ts = .ok v) ∨ (∃ e, parse ts = .error e) := by
  cases h : parse ts with
  | ok v => exact Or.inl ⟨v, rfl⟩
  | error e => exact Or.inr ⟨e, rfl⟩

/-- The unconsumed tail is a suffix of the input: the parser never grows its
input. -/
theorem parse_suffix {ts : List Tok} {tp : TraceParent} {rest : List Tok}
    (h : parse ts = .ok (tp, rest)) : rest <:+ ts := by
  unfold parse at h
  cases h2 : takeNibs 2 ts with
  | none => simp [h2] at h
  | some p2 =>
    obtain ⟨ver, ts1⟩ := p2
    simp only [h2] at h
    cases h3 : expectDash ts1 with
    | none => simp [h3] at h
    | some ts2 =>
      simp only [h3] at h
      cases h4 : takeNibs 32 ts2 with
      | none => simp [h4] at h
      | some p4 =>
        obtain ⟨tid, ts3⟩ := p4
        simp only [h4] at h
        cases h5 : expectDash ts3 with
        | none => simp [h5] at h
        | some ts4 =>
          simp only [h5] at h
          cases h6 : takeNibs 16 ts4 with
          | none => simp [h6] at h
          | some p6 =>
            obtain ⟨pid, ts5⟩ := p6
            simp only [h6] at h
            cases h7 : expectDash ts5 with
            | none => simp [h7] at h
            | some ts6 =>
              simp only [h7] at h
              cases h8 : takeNibs 2 ts6 with
              | none => simp [h8] at h
              | some p8 =>
                obtain ⟨fl, ts7⟩ := p8
                simp only [h8] at h
                cases hz1 : allZero tid with
                | true => simp [hz1] at h
                | false =>
                  cases hz2 : allZero pid with
                  | true => simp [hz1, hz2] at h
                  | false =>
                    simp only [hz1, hz2, Except.ok.injEq, Prod.mk.injEq] at h
                    obtain ⟨-, hrest⟩ := h
                    have s2 := takeNibs_suffix 2 ts ver ts1 h2
                    have s3 := expectDash_suffix h3
                    have s4 := takeNibs_suffix 32 ts2 tid ts3 h4
                    have s5 := expectDash_suffix h5
                    have s6 := takeNibs_suffix 16 ts4 pid ts5 h6
                    have s7 := expectDash_suffix h7
                    have s8 := takeNibs_suffix 2 ts6 fl ts7 h8
                    have hchain : ts7 <:+ ts :=
                      (((((s8.trans s7).trans s6).trans s5).trans s4).trans s3).trans s2
                    exact hrest ▸ hchain

/-- **Theorem 3 (consumed-monotone).**  On success the tail is no longer than
the input. -/
theorem parse_consumed_monotone {ts : List Tok} {tp : TraceParent} {rest : List Tok}
    (h : parse ts = .ok (tp, rest)) : rest.length ≤ ts.length :=
  (parse_suffix h).length_le

/-! ### Theorem 3 (span half) — child span preserves the trace-id -/

@[simp] theorem childSpan_traceId (span : List Nibble) (tp : TraceParent) :
    (childSpan span tp).traceId = tp.traceId := rfl

@[simp] theorem childSpan_parentId (span : List Nibble) (tp : TraceParent) :
    (childSpan span tp).parentId = span := rfl

@[simp] theorem childSpan_flags (span : List Nibble) (tp : TraceParent) :
    (childSpan span tp).flags = tp.flags := rfl

@[simp] theorem childSpan_version (span : List Nibble) (tp : TraceParent) :
    (childSpan span tp).version = tp.version := rfl

/-- The installed parent-id is genuinely fresh: if the new span id differs from
the old parent-id, the parent-id changed. -/
theorem childSpan_fresh {span : List Nibble} {tp : TraceParent}
    (h : span ≠ tp.parentId) : (childSpan span tp).parentId ≠ tp.parentId := by
  simpa using h

/-- Fold `childSpan` along a chain of freshly generated span ids. -/
def chain (tp : TraceParent) : List (List Nibble) → TraceParent
  | [] => tp
  | s :: ss => chain (childSpan s tp) ss

/-- **Theorem 3 (trace-id invariant).**  The trace-id is invariant along any
propagation chain. -/
theorem chain_traceId (tp : TraceParent) (ss : List (List Nibble)) :
    (chain tp ss).traceId = tp.traceId := by
  induction ss generalizing tp with
  | nil => rfl
  | cons s ss ih => rw [chain, ih]; exact childSpan_traceId s tp

/-! ### The propagation transition and theorems 2 & 4 -/

/-- The propagation transition across one hop.  `adopt` keeps the inbound
trace-id and installs the fresh span; `fallback` is taken on a malformed inbound
value and produces a brand-new trace. -/
inductive Step (f : Fresh) : List Tok → TraceParent → Prop where
  /-- A parsable inbound value: keep its trace-id, install the fresh span. -/
  | adopt {inbound : List Tok} {tp : TraceParent} {rest : List Tok} :
      parse inbound = .ok (tp, rest) → Step f inbound (childSpan f.spanId tp)
  /-- A malformed inbound value: fall back to a brand-new trace. -/
  | fallback {inbound : List Tok} {e : ParseErr} :
      parse inbound = .error e → Step f inbound (freshTrace f)

/-- The propagation transition realized as a total function. -/
def propagate (f : Fresh) (inbound : List Tok) : TraceParent :=
  match parse inbound with
  | .ok (tp, _) => childSpan f.spanId tp
  | .error _ => freshTrace f

/-- Every input steps: the transition is defined on every inbound value
(totality of the transition). -/
theorem propagate_step (f : Fresh) (inbound : List Tok) :
    Step f inbound (propagate f inbound) := by
  unfold propagate
  cases h : parse inbound with
  | error e => simp only [h]; exact Step.fallback h
  | ok v =>
    obtain ⟨tp, rest⟩ := v
    simp only [h]; exact Step.adopt h

/-- **Theorem 2 (propagation faithfulness for traces).**  When the inbound
value parses, the outbound trace-id equals the inbound trace-id. -/
theorem propagate_ok_traceId {f : Fresh} {inbound : List Tok} {tp : TraceParent}
    {rest : List Tok} (h : parse inbound = .ok (tp, rest)) :
    (propagate f inbound).traceId = tp.traceId := by
  simp only [propagate, h, childSpan_traceId]

/-- **Theorem 4.**  A malformed inbound value is a total error and the hop falls
back to a fresh trace — exactly the `Step.fallback` transition. -/
theorem propagate_malformed {f : Fresh} {inbound : List Tok} {e : ParseErr}
    (h : parse inbound = .error e) : propagate f inbound = freshTrace f := by
  simp only [propagate, h]

/-- The fallback is genuinely the named transition on malformed input. -/
theorem step_fallback_of_malformed {f : Fresh} {inbound : List Tok} {e : ParseErr}
    (h : parse inbound = .error e) : Step f inbound (freshTrace f) :=
  Step.fallback h

/-- Propagation is a function of its inputs (determinism). -/
theorem propagate_deterministic (f : Fresh) {i₁ i₂ : List Tok} (h : i₁ = i₂) :
    propagate f i₁ = propagate f i₂ := by rw [h]

end Trace
