/-
# Dregg2.Exec.PubSubTopic — the append-only event log with subscriber cursors, as a CELL.

`STORAGE-AS-CELL-PROGRAMS §3.3`: a `PubSubTopic` is **one publisher, multi-subscriber cursors
over a shared append-only event log**. dregg1 realizes it as a `MerkleQueue` + a `BTreeMap` of
subscriber cursors guarded by a hand-written executor (`storage/src/pubsub.rs`, 531 LOC). The
storage-as-cell-programs thesis is that this is *not* a bespoke service — it is **a CELL**: a
record state whose `RecordProgram` declares exactly the invariants the hand-written executor
enforced, so that the executable structure-map arrow (`RecordCell.recExec`) *is* the topic.

We model the topic NAME-KEYED over `Exec/Value.lean`'s Preserves record (not §3.3's 8 fixed
bit-positioned slots — the `dregg2 §5` fix), keeping the load-bearing four fields:

| §3.3 slot | this field    | role |
|---|---|---|
| 0 `head_seq`               | `headSeq`     | publisher's seq counter — **strictly increases per publish**. |
| 5 `event_root`             | `eventRoot`   | Merkle root over published events — **only GROWS (append-only)**. |
| 1 `subscriber_cursors_root`| `cursorsRoot` | root over `(pk, last_read_seq)` — **cursors only ADVANCE**. |
| 2 `publisher_pk_hash`      | `publisher`   | publisher identity — **immutable**. |

The Merkle roots are scalar **size/version** stand-ins: a monotone `Nat` that grows iff the
committed set grows (a root that has absorbed more leaves has a strictly larger size). This is
exactly the quantity `monotonic` needs — "the event log only grows" is "its size only grows", and
a real `event_root` commitment is paired with such a monotone counter at the circuit tier. The
genuine cryptographic "this root extends that root" obligation is the §8 circuit interface,
discharged separately (NEVER merged into the Lean law — `REORIENT §6`); here we prove the
*ordering law* the cell declares.

The `RecordProgram` is method-keyed (`cases`, default-deny): a **publish** (method `publishM`)
advances `headSeq` strictly and grows `eventRoot`, holding `publisher` immutable and the cursors
unchanged; a **subscribe** (method `subscribeM`) advances `cursorsRoot` monotonically, holding the
log (`headSeq`/`eventRoot`) and `publisher` fixed. Any other method has no matching arm and is
**default-denied** (the partial, fail-closed arrow).

THE KEYSTONE `pubsub_append_only`: every *committed* transition advances the log monotonically
(`eventRoot` new ≥ old) and the publish-seq strictly, and every committed subscribe advances
cursors only-forward — proved by lifting `RecordCell.recExec_admitted` through the
`monotonic`/`strictMono` `evalConstraint`/`evalSimple` definitions. Append-only is a *theorem* of
the cell, not a property of an executor we have to trust.

Pure, computable, `#eval`-able; imports only `Exec.RecordCell` (which pulls `Exec.Program` /
`Exec.Value`, all Lean-core), so it type-checks fast.
-/
import Dregg2.Exec.RecordCell

namespace Dregg2.Exec.PubSubTopic

open Dregg2.Exec
open Dregg2.Exec.RecordCell

/-! ## The method tags (`Action`'s named handler, §3.3 — "the executor differentiates by handler"). -/

/-- The `publish` handler — only the publisher advances the log. -/
def publishM : Nat := 1
/-- The `subscribe` handler — a subscriber advances its cursor. -/
def subscribeM : Nat := 2

/-! ## The topic schema + the cell program (the §3.3 `StateConstraints`, name-keyed). -/

/-- The topic's record shape: head sequence, event-log size, cursors size, publisher id. The
Merkle roots (`eventRoot`/`cursorsRoot`) are their monotone *size* scalars (see the header). -/
def topicSchema : Schema :=
  [("headSeq",     .scalar),
   ("eventRoot",   .scalar),
   ("cursorsRoot", .scalar),
   ("publisher",   .digest)]

/-- **The publish arm's constraints** — `headSeq` strictly advances, the event log only grows,
the cursors are untouched, and the publisher is immutable. (`§3.3`: `MonotonicSequence{0}` +
`Monotonic{5}` + `Immutable{2}`, with the publish handler leaving slot 1 fixed.) -/
def publishConstraints : List StateConstraint :=
  [.simple (.strictMono "headSeq"),     -- publisher seq advances per publish
   .simple (.monotonic "eventRoot"),    -- append-only: the log only GROWS
   .simple (.immutable "cursorsRoot"),  -- publish does not touch subscriber cursors
   .simple (.immutable "publisher")]    -- publisher identity is fixed

/-- **The subscribe arm's constraints** — the subscriber cursor only advances, while the log
(`headSeq`/`eventRoot`) and the publisher stay fixed. (`§3.3`: `Monotonic{1}`, with subscribe
leaving slots 0/5/2 fixed.) -/
def subscribeConstraints : List StateConstraint :=
  [.simple (.monotonic "cursorsRoot"),  -- subscriber cursors only ADVANCE
   .simple (.immutable "headSeq"),      -- subscribe does not advance the publish seq
   .simple (.immutable "eventRoot"),    -- subscribe does not rewrite the log
   .simple (.immutable "publisher")]    -- publisher identity is fixed

/-- **`topicProgram` — the PubSubTopic coalgebra structure-map.** Method-keyed, default-deny:
`publish` (method `publishM`) binds `publishConstraints`; `subscribe` (method `subscribeM`) binds
`subscribeConstraints`; **any other method matches no arm and is rejected** (the fail-closed
arrow). This is §3.3's `StateConstraints` block, realized as the cell's gating program. -/
def topicProgram : RecordProgram :=
  .cases [⟨.methodIs publishM,   publishConstraints⟩,
          ⟨.methodIs subscribeM, subscribeConstraints⟩]

/-! ## `publish` / `subscribe` — gated transitions over the record.

`§3.3`: a **publish** is an ATOMIC two-field action — `Effect::SetField{slot 0}` (advance
`headSeq`) AND `Effect::SetField{slot 5}` (grow `eventRoot`) in ONE turn; a **subscribe** is a
single `Effect::SetField{slot 1}` (advance `cursorsRoot`). The publish arm's program conjoins
`strictMono "headSeq"` ∧ `monotonic "eventRoot"`, so it is admissible only of a candidate that
moves BOTH fields together — exactly the two-field move. `RecordCell.recExec` commits a single
`RecOp`; the subscribe (one field) reuses it verbatim, while the publish builds the two-field
candidate and routes it through the SAME `topicProgram.admits` filter (the gating discipline is
identical — the filter is the structure-map's domain either way). -/

/-- **`pubApply old newSeq newRootSize`** — the raw (un-gated) atomic publish candidate: set
`headSeq := newSeq` and `eventRoot := newRootSize` together. Total/computable; the two-field
`applyOp` shadow for §3.3's two-`SetField` publish action. -/
def pubApply (old : Value) (newSeq newRootSize : Int) : Value :=
  setField (setField old "headSeq" (.int newSeq)) "eventRoot" (.int newRootSize)

/-- **`publish topic newSeq newRootSize`** — the GATED atomic publish arrow: build the two-field
candidate and commit it (`some new`) iff `topicProgram.admits publishM topic new` (i.e. `headSeq`
advanced strictly AND `eventRoot` grew, with cursors/publisher untouched); else `none`
(fail-closed). The `RecordProgram` is the structure-map's domain filter, exactly as in `recExec`. -/
def publish (topic : Value) (newSeq newRootSize : Int) : Option Value :=
  let new := pubApply topic newSeq newRootSize
  if topicProgram.admits publishM topic new = true then some new else none

/-- **`subscribe topic newCursorsSize`** — the gated subscribe arrow (single field): advance
`cursorsRoot` to `newCursorsSize`, gated by `topicProgram` under `subscribeM`. A single-field move,
so it reuses `recExec` verbatim. Commits iff `monotonic "cursorsRoot"` holds (cursors only-forward,
and the log/publisher untouched — which the `setScalar` leaves fixed). -/
def subscribe (topic : Value) (newCursorsSize : Int) : Option Value :=
  recExec topicProgram subscribeM topic (.setScalar "cursorsRoot" newCursorsSize)

/-! ## THE KEYSTONE — `pubsub_append_only`.

A committed transition obeys the cell's declared law. We lift admissibility (`recExec_admitted`
for subscribe; its two-field shadow `publish_admitted` for publish — nothing commits the program
rejects) through the `cases`/`methodIs`/`evalConstraint`/`evalSimple` definitions to recover the
honest `Int` (in)equalities. Three faces:
  • a committed **publish** advances `headSeq` STRICTLY  (`new > old`);
  • a committed **publish** grows `eventRoot` MONOTONICALLY (`new ≥ old`) — APPEND-ONLY;
  • a committed **subscribe** advances `cursorsRoot` only-forward (`new ≥ old`).
Together: no committed transition rewinds the publish-seq or SHRINKS the event log; the log is
append-only by THEOREM. -/

/-- **`publish_admitted` (PROVED)** — a committed publish was admitted by `topicProgram` (the
`recExec_admitted` shadow for the two-field publish arrow: the filter is load-bearing, never
bypassed). -/
theorem publish_admitted {topic : Value} {newSeq newRootSize : Int} {topic' : Value}
    (h : publish topic newSeq newRootSize = some topic') :
    topicProgram.admits publishM topic topic' = true := by
  unfold publish at h
  by_cases ha : topicProgram.admits publishM topic (pubApply topic newSeq newRootSize) = true
  · rw [if_pos ha, Option.some.injEq] at h; rw [← h]; exact ha
  · rw [if_neg ha] at h; exact absurd h (by simp)

/-- A `cases` arm whose single `methodIs m` guard matches `m` reduces `admits` to that arm's
constraint conjunction — the bridge from `topicProgram.admits` to a `List.all evalConstraint`. -/
private theorem admits_arm
    {m : Nat} {cs : List StateConstraint} {old new : Value}
    (h : RecordProgram.admits (.cases [⟨.methodIs m, cs⟩]) m old new = true) :
    cs.all (fun c => evalConstraint c old new) = true := by
  simp only [RecordProgram.admits, List.filter, TransitionGuard.matches,
    beq_self_eq_true, List.all_cons, List.all_nil, Bool.and_true] at h
  exact h

/-- From `monotonic f` admitted, recover the honest inequality `a ≤ b` with both scalars present. -/
private theorem monotonic_holds {f : FieldName} {old new : Value}
    (h : evalSimple (.monotonic f) old new = true) :
    ∃ a b, old.scalar f = some a ∧ new.scalar f = some b ∧ a ≤ b := by
  simp only [evalSimple] at h
  cases hoa : old.scalar f with
  | none => rw [hoa] at h; simp at h
  | some a =>
      cases hnb : new.scalar f with
      | none => rw [hoa, hnb] at h; simp at h
      | some b =>
          rw [hoa, hnb] at h
          exact ⟨a, b, rfl, rfl, of_decide_eq_true h⟩

/-- From `strictMono f` admitted, recover the strict inequality `a < b` with both scalars present. -/
private theorem strictMono_holds {f : FieldName} {old new : Value}
    (h : evalSimple (.strictMono f) old new = true) :
    ∃ a b, old.scalar f = some a ∧ new.scalar f = some b ∧ a < b := by
  simp only [evalSimple] at h
  cases hoa : old.scalar f with
  | none => rw [hoa] at h; simp at h
  | some a =>
      cases hnb : new.scalar f with
      | none => rw [hoa, hnb] at h; simp at h
      | some b =>
          rw [hoa, hnb] at h
          exact ⟨a, b, rfl, rfl, of_decide_eq_true h⟩

/-- The four publish-arm facts, recovered from a committed publish as honest `Bool`s. -/
private theorem publish_facts {topic : Value} {newSeq newRootSize : Int} {topic' : Value}
    (h : publish topic newSeq newRootSize = some topic') :
    evalSimple (.strictMono "headSeq") topic topic' = true
      ∧ evalSimple (.monotonic "eventRoot") topic topic' = true
      ∧ evalSimple (.immutable "cursorsRoot") topic topic' = true
      ∧ evalSimple (.immutable "publisher") topic topic' = true := by
  have hadm := publish_admitted h
  have harm := admits_arm (m := publishM) (cs := publishConstraints) hadm
  simp only [publishConstraints, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, evalConstraint] at harm
  exact harm

/-- **`pubsub_publish_strict_seq` (PROVED).** A committed `publish` advances the publish sequence
STRICTLY: `new.headSeq > old.headSeq`. The publisher's seq counter can never rewind. -/
theorem pubsub_publish_strict_seq
    {topic : Value} {newSeq newRootSize : Int} {topic' : Value}
    (h : publish topic newSeq newRootSize = some topic') :
    ∃ a b, topic.scalar "headSeq" = some a ∧ topic'.scalar "headSeq" = some b ∧ a < b :=
  strictMono_holds (publish_facts h).1

/-- **`pubsub_publish_append_only` (THE KEYSTONE, publish half — PROVED).** A committed `publish`
grows the event log MONOTONICALLY: `new.eventRoot ≥ old.eventRoot`. The log is APPEND-ONLY — no
committed publish can SHRINK it (a publish to a smaller root size fails the `monotonic "eventRoot"`
gate and returns `none`, so `some topic'` forces `≥`). The append-only discipline as a *theorem* of
the cell, not a trusted executor. -/
theorem pubsub_publish_append_only
    {topic : Value} {newSeq newRootSize : Int} {topic' : Value}
    (h : publish topic newSeq newRootSize = some topic') :
    ∃ a b, topic.scalar "eventRoot" = some a ∧ topic'.scalar "eventRoot" = some b ∧ a ≤ b :=
  monotonic_holds (publish_facts h).2.1

/-- **`pubsub_subscribe_only_forward` (THE KEYSTONE, subscribe half — PROVED).** A committed
`subscribe` advances the subscriber cursors only-forward: `new.cursorsRoot ≥ old.cursorsRoot`. A
subscribe can never rewind a cursor below where it was — monotone subscriber cursors by theorem. -/
theorem pubsub_subscribe_only_forward
    {topic : Value} {newCursorsSize : Int} {topic' : Value}
    (h : subscribe topic newCursorsSize = some topic') :
    ∃ a b, topic.scalar "cursorsRoot" = some a ∧ topic'.scalar "cursorsRoot" = some b ∧ a ≤ b := by
  have hadm : topicProgram.admits subscribeM topic topic' = true := recExec_admitted h
  have harm := admits_arm (m := subscribeM) (cs := subscribeConstraints) hadm
  simp only [subscribeConstraints, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, evalConstraint] at harm
  exact monotonic_holds harm.1

/-- **`pubsub_append_only` (THE KEYSTONE — PROVED).** The full append-only / only-forward law,
bundled: a committed `publish` grows the event log (`eventRoot` ≥) AND advances `headSeq` strictly
(`>`); a committed `subscribe` advances cursors only-forward (`cursorsRoot` ≥). The log is
APPEND-ONLY and the publish-seq MONOTONE *by the cell-program's law*, holding on every committed
codomain point — no committed transition rewinds or rewrites. -/
theorem pubsub_append_only :
    (∀ {topic topic' : Value} {newSeq newRootSize : Int},
        publish topic newSeq newRootSize = some topic' →
        (∃ a b, topic.scalar "eventRoot" = some a ∧ topic'.scalar "eventRoot" = some b ∧ a ≤ b)
          ∧ (∃ a b, topic.scalar "headSeq" = some a ∧ topic'.scalar "headSeq" = some b ∧ a < b))
    ∧ (∀ {topic topic' : Value} {newCursorsSize : Int},
        subscribe topic newCursorsSize = some topic' →
        ∃ a b, topic.scalar "cursorsRoot" = some a ∧ topic'.scalar "cursorsRoot" = some b ∧ a ≤ b) :=
  ⟨fun h => ⟨pubsub_publish_append_only h, pubsub_publish_strict_seq h⟩,
   pubsub_subscribe_only_forward⟩

/-! ## Publisher authority — the only-the-publisher-may-publish law.

`§3.3`: `StateConstraint::SenderAuthorized { set: PublicRoot { slot: 2 } }` — only the holder of
the key whose hash equals `publisher` may emit a publish. That gate compares the TURN's *sender*
against the cell's `publisher` field. Our `RecOp`/`recExec` turn carries no sender principal yet
(the auth gate is the verify/find seam — `Laws.Verifiable`/`CryptoKernel` — added downstream, per
`REORIENT §6`: "the Lean cell proves *if* Verify accepts *then* admissible"). So we discharge the
*half we can*: a committed publish leaves `publisher` UNCHANGED, hence whatever authority is keyed
on it is stable across the turn (the gate's reference target can't be moved by the publish). The
sender-equals-publisher check itself is the honest OPEN below. -/

/-- **`pubsub_publisher_immutable` (PROVED)** — a committed publish leaves `publisher` unchanged
(when it was present): the authority target the `SenderAuthorized{slot 2}` gate keys on cannot be
rebound by a publish. This is the *state half* of publisher-authority; the sender-check is the
OPEN below. -/
theorem pubsub_publisher_immutable
    {topic : Value} {newSeq newRootSize : Int} {topic' : Value} {p : Int}
    (h : publish topic newSeq newRootSize = some topic')
    (hp : topic.scalar "publisher" = some p) :
    topic'.scalar "publisher" = some p := by
  have himm := (publish_facts h).2.2.2
  simp only [evalSimple, hp] at himm
  exact eq_of_beq (by simpa using himm)

-- OPEN: `pubsub_publisher_authorized` — only-the-publisher-may-publish, the SENDER half.
-- The full law is `committed publish ⇒ sender.keyHash = old.publisher` (§3.3's
-- `SenderAuthorized{PublicRoot{slot 2}}`). It requires the turn to carry a SENDER principal and
-- the program to evaluate that principal against the `publisher` field — the verify/find seam
-- (`Laws.Verifiable`/`CryptoKernel`), which `RecOp`/`recExec`/`topicProgram` do not yet model (no
-- sender field on the op, and `StateConstraint` here has no sender-keyed variant). Stating the
-- theorem now would be vacuous over a sender we cannot reference, so it is left UNWRITTEN rather
-- than asserted with a `sorry`. The *state half* IS discharged (`pubsub_publisher_immutable`: the
-- gate's authority target is fixed across every committed publish); the sender-side enforcement is
-- deferred honestly to the auth-gate build, per REORIENT §6 ("the Lean cell proves *if* Verify
-- accepts *then* admissible"; the sender-signature check routes through the authority seam, NOT
-- into this semantic law).

/-! ## It runs (`#eval`) — publishes grow the log + advance the seq; a subscribe advances a
cursor; a shrink / rewind is rejected. -/

/-- A fresh topic at seq 0, empty log (size 0), no cursors (size 0), publisher-hash 7. -/
def topic0 : Value :=
  .record [("headSeq", .int 0), ("eventRoot", .int 0),
           ("cursorsRoot", .int 0), ("publisher", .dig 7)]

-- A publish: advance the head seq (0 → 1) AND grow the event log (0 → 3) together — strictMono +
-- monotonic both hold ⇒ commits.
#eval publish topic0 1 3
  -- some (record [headSeq 1, eventRoot 3, cursorsRoot 0, publisher 7])
-- A subscribe ADVANCES a cursor (size 0 → 2) — monotonic holds ⇒ commits.
#eval subscribe topic0 2
  -- some (record […, cursorsRoot 2, …])

-- REJECTED: a publish that GROWS the log but REWINDS the head seq (0 → 0, not strict) — strictMono
-- fails ⇒ none.
#eval publish topic0 0 3
  -- none  (0 > 0 is false)
-- REJECTED: a publish that advances the seq but SHRINKS the event log (size 5 → 2) — monotonic
-- fails ⇒ none (APPEND-ONLY enforced).
#eval publish (.record [("headSeq", .int 1), ("eventRoot", .int 5),
                        ("cursorsRoot", .int 0), ("publisher", .dig 7)]) 2 2
  -- none  (2 ≥ 5 is false — the log cannot shrink)
-- REJECTED: a subscribe that REWINDS a cursor (size 4 → 1) — monotonic fails ⇒ none.
#eval subscribe (.record [("headSeq", .int 1), ("eventRoot", .int 3),
                          ("cursorsRoot", .int 4), ("publisher", .dig 7)]) 1
  -- none  (1 ≥ 4 is false)
-- REJECTED (default-deny): an unknown method (3) matches no arm ⇒ none.
#eval recExec topicProgram 3 topic0 (.setScalar "headSeq" 99)
  -- none  (no matching case → default-deny)

-- Two successive publishes: the head advances (1, then 2) and the log grows (3, then 7) — the
-- append-only stream of §3.3, each a gated turn through the same program.
#eval (do
  let t1 ← publish topic0 1 3     -- seq 0→1, log 0→3
  let t2 ← publish t1 2 7         -- seq 1→2, log 3→7
  pure t2 : Option Value)
  -- some (record [headSeq 2, eventRoot 7, cursorsRoot 0, publisher 7])

end Dregg2.Exec.PubSubTopic
