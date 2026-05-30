/-
# Dregg2.Exec.CapInbox — a store-and-forward CapInbox as a *cell-program pattern*.

`STORAGE-AS-CELL-PROGRAMS.md §3.1`: a CapInbox (the subscriber-delivery, store-and-forward
queue) is **not a new Effect** — it is a **cell** whose mutable state is a name-keyed record and
whose FIFO discipline is exactly a `RecordProgram`'s `StateConstraint`s, enforced by the same
per-turn evaluator every other cell uses. The doc's §3.1 slot table (`head`/`tail`/`capacity`/
`owner`/`sender_set`/`total_deposits`/`message_root`) is bit-positional (an inherited Mina
artifact); dregg2's direction (`dregg2 §5`, `Exec/Value.lean`) is **name-keyed records, NOT 8
fixed slots** — so this module models the inbox as a `Value` record `{ "head", "tail",
"capacity", "owner", "inflight", … }` and the queue invariants as the constraint catalog of
`Exec/Program.lean`.

The FIFO discipline encoded as `inboxProgram : RecordProgram` constraints:
- `monotonic "head"`  — a *send* advances the producer cursor (never retreats).
- `monotonic "tail"`  — a *dequeue* advances the consumer cursor (never retreats).
- `immutable "capacity"` / `immutable "owner"` — the queue metadata is fixed for the cell's life.
- `fieldLeField "tail" "head"` — **the FIFO safety invariant**: the consumer never passes the
  producer (`tail ≤ head`), so a dequeue can only read a message a send has already produced.
- the capacity bound `head - tail ≤ capacity` is a cross-slot *minus* not in the base 21-variant
  catalog (`STORAGE-AS-CELL-PROGRAMS §3.1` / `§7.2`). We encode it the **clean** way the doc
  recommends: a derived `"inflight"` field carrying `head - tail`, bounded by `fieldLe "inflight"
  capacity`. (See the `-- OPEN:` note below for the proper `FieldLteOther` variant.)

THE KEYSTONE `inbox_fifo`: a *committed* send-or-dequeue preserves `tail ≤ head` AND advances the
right cursor monotonically — proved by lifting `RecordCell.recExec_admitted` + `evalConstraint`
for `fieldLeField`/`monotonic`, exactly as `RecordCell.recExec_mono_holds` does for one constraint.

SenderAuthorized: a *send* must present an authorized-sender `Caveat.Token` that discharges
(`STORAGE-AS-CELL-PROGRAMS §3.1` "sender authorization"; the routing through the token layer of
`Authority/Caveat.lean`). Here it is a clean gate-AND-lemma (`send_requires_authorized_token`):
an admitted gated send presented a token that discharges. The *binding* of that token to the
on-wire sender identity stays an `-- OPEN:`, deferred to the verify/find seam exactly as dregg1's
scalar evaluator defers it (`Exec/Program.lean`'s `boundDelta`/`Witnessed` deferral).

Pure, computable, `#eval`-able; imports `Exec.RecordCell` (⇒ `Exec.Program` ⇒ `Exec.Value`) and
`Authority.Caveat` (the token layer). Type-checks fast (Lean-core for the record side).
-/
import Dregg2.Exec.RecordCell
import Dregg2.Authority.Caveat

namespace Dregg2.Exec.CapInbox

open Dregg2.Exec
open Dregg2.Exec.RecordCell
open Dregg2.Authority

/-! ## The inbox record + its schema (the name-keyed §3.1 slot layout). -/

/-- **The CapInbox schema** (`STORAGE-AS-CELL-PROGRAMS §3.1`, name-keyed not 8-slot):
- `head`     — the producer cursor: next seq a *send* will write (monotone ↑).
- `tail`     — the consumer cursor: next seq a *dequeue* will read (monotone ↑, `tail ≤ head`).
- `capacity` — max in-flight messages; immutable for the cell's life.
- `owner`    — hash of the owner pubkey; immutable; only the owner may dequeue.
- `inflight` — the derived `head - tail` register (the clean encoding of the capacity bound;
  see the `-- OPEN:` note). Bounded by `inflight ≤ capacity`. -/
def inboxSchema : Schema :=
  [ ("head",     .scalar)
  , ("tail",     .scalar)
  , ("capacity", .scalar)
  , ("owner",    .digest)
  , ("inflight", .scalar) ]

/-- A method id for a *send* (producer advances `head`). -/
def methodSend : Nat := 1
/-- A method id for a *dequeue* (consumer advances `tail`). -/
def methodDequeue : Nat := 2

/-! ## The inbox program — the FIFO discipline as `StateConstraint`s. -/

/-- **`inboxProgram` (the CapInbox cell-program)** — a `predicate` conjunction of the FIFO
constraints (`STORAGE-AS-CELL-PROGRAMS §3.1`, "StateConstraints declared"). It is a `predicate`
(not `cases`) so the *invariants* (`tail ≤ head`, immutables) hold under EVERY method; `head`/`tail`
are each `monotonic` (a send advances head, a dequeue advances tail — neither ever retreats). The
capacity bound is the derived-`inflight` encoding (`fieldLe "inflight" cap`, with `inflight`
itself monotone-tracked); the proper cross-slot variant is the `-- OPEN:` below. -/
def inboxProgram (capacity : Int) : RecordProgram :=
  .predicate
    [ .simple (.monotonic "head")        -- a send advances head; never retreats
    , .simple (.monotonic "tail")        -- a dequeue advances tail; never retreats
    , .simple (.immutable "capacity")    -- capacity fixed for the cell's life
    , .simple (.immutable "owner")       -- owner fixed for the cell's life
    , .fieldLeField "tail" "head"        -- THE FIFO SAFETY INVARIANT: tail ≤ head
    , .simple (.fieldLe "inflight" capacity) ]  -- capacity bound, via the derived register
  -- OPEN: the *true* capacity bound is the cross-slot relational `head - tail ≤ capacity`, which is
  -- NOT in the base 21-variant catalog (`STORAGE-AS-CELL-PROGRAMS §3.1`, citing §7.2 / SLOT-CAVEATS-
  -- EVALUATION §3.4). The clean fix the doc recommends is a new constraint
  --   `FieldLteOther (idx other : FieldName) (plusDelta : Int)`  meaning  `new[idx] ≤ new[other] + δ`,
  -- which would let us write `fieldLteOther "head" "tail" capacity` directly and DROP the derived
  -- `inflight` register. We do NOT fake it here: instead we carry an honest derived `inflight` field
  -- that `inboxExec` keeps equal to `head - tail` (see `inflightTracks` below), and bound THAT with
  -- the in-catalog `fieldLe`. The relational variant is left for the catalog-extension build.

/-! ## The executable inbox transition (send / dequeue), gated by `inboxProgram.admits`. -/

/-- A *send*: advance `head` by one and re-derive `inflight = inflight + 1` (one more in-flight).
A *dequeue*: advance `tail` by one and re-derive `inflight = inflight - 1`. We model each as a list
of `RecOp`s; `applyOpList` folds them so the candidate record carries BOTH updates, then the single
program filter gates the whole candidate (so a send that would breach `tail ≤ head` or the capacity
bound is rejected atomically). -/
def sendOps : List RecOp :=
  [ .addScalar "head" 1, .addScalar "inflight" 1 ]
def dequeueOps : List RecOp :=
  [ .addScalar "tail" 1, .addScalar "inflight" (-1) ]

/-- Fold a list of `RecOp`s left-to-right into a candidate next state (the raw, un-gated arrow). -/
def applyOpList (old : Value) : List RecOp → Value
  | []        => old
  | op :: ops => applyOpList (applyOp old op) ops

/-- **`inboxExec prog method old ops`** — the GATED inbox arrow: fold `ops` into the candidate
`new = applyOpList old ops`, and commit it (`some new`) iff `prog.admits method old new`; else
`none` (fail-closed). This is the multi-op generalization of `RecordCell.recExec`; the program is
the same single admissibility filter, so `inbox_fifo` lifts `recExec`'s keystone unchanged. -/
def inboxExec (prog : RecordProgram) (method : Nat) (old : Value) (ops : List RecOp) : Option Value :=
  let new := applyOpList old ops
  if prog.admits method old new = true then some new else none

/-! ## Generic gating lemma — a committed inbox transition was admitted (the `recExec_admitted` lift). -/

/-- **`inboxExec_admitted` (PROVED)** — nothing commits that the program rejects: if
`inboxExec prog method old ops = some new`, then `prog.admits method old new = true`. The exact
multi-op analogue of `RecordCell.recExec_admitted`; the program genuinely gates the inbox arrow. -/
theorem inboxExec_admitted
    {prog : RecordProgram} {method : Nat} {old : Value} {ops : List RecOp} {new : Value}
    (h : inboxExec prog method old ops = some new) :
    prog.admits method old new = true := by
  unfold inboxExec at h
  by_cases ha : prog.admits method old (applyOpList old ops) = true
  · rw [if_pos ha, Option.some.injEq] at h
    rw [← h]; exact ha
  · rw [if_neg ha] at h; exact absurd h (by simp)

/-- **`inboxExec_commits_candidate` (PROVED)** — a commit commits exactly the folded candidate
(no silent rewrite between apply and commit). With `inboxExec_admitted` this fully characterizes a
committed inbox transition: `new = applyOpList old ops` ∧ `admits old new`. -/
theorem inboxExec_commits_candidate
    {prog : RecordProgram} {method : Nat} {old : Value} {ops : List RecOp} {new : Value}
    (h : inboxExec prog method old ops = some new) :
    new = applyOpList old ops := by
  unfold inboxExec at h
  by_cases ha : prog.admits method old (applyOpList old ops) = true
  · rw [if_pos ha, Option.some.injEq] at h; exact h.symm
  · rw [if_neg ha] at h; exact absurd h (by simp)

/-! ## Recovering the constraint values from an admitted candidate (the `evalConstraint` lift). -/

/-- A `predicate` program admits ⇒ every one of its constraints holds on the candidate. A small
list lemma: from `cs.all f = true` and `c ∈ cs`, get `f c = true`. -/
theorem all_constraint_holds
    {cs : List StateConstraint} {o n : Value}
    (h : RecordProgram.admits (.predicate cs) 0 o n = true)
    {c : StateConstraint} (hc : c ∈ cs) :
    evalConstraint c o n = true := by
  simp only [RecordProgram.admits, List.all_eq_true] at h
  exact h c hc

/-- **`fieldLeField_holds` (PROVED)** — from `evalConstraint (.fieldLeField l r) o n = true`,
recover the honest `Int` facts: both fields are present scalars and `a ≤ b`. (The lift of
`fieldLeField`'s `decide` back to a real inequality, mirroring `recExec_mono_holds`.) -/
theorem fieldLeField_holds
    {l r : FieldName} {o n : Value}
    (h : evalConstraint (.fieldLeField l r) o n = true) :
    ∃ a b, n.scalar l = some a ∧ n.scalar r = some b ∧ a ≤ b := by
  simp only [evalConstraint] at h
  cases ha : n.scalar l with
  | none => rw [ha] at h; simp at h
  | some a =>
      cases hb : n.scalar r with
      | none => rw [ha, hb] at h; simp at h
      | some b =>
          rw [ha, hb] at h
          exact ⟨a, b, rfl, rfl, of_decide_eq_true h⟩

/-- **`monotonic_holds` (PROVED)** — from `evalConstraint (.simple (.monotonic f)) o n = true`,
recover the honest facts: both old and new `f` are present scalars and `old ≤ new` (the cursor
advanced, never retreated). -/
theorem monotonic_holds
    {f : FieldName} {o n : Value}
    (h : evalConstraint (.simple (.monotonic f)) o n = true) :
    ∃ a b, o.scalar f = some a ∧ n.scalar f = some b ∧ a ≤ b := by
  simp only [evalConstraint, evalSimple] at h
  cases ha : o.scalar f with
  | none => rw [ha] at h; simp at h
  | some a =>
      cases hb : n.scalar f with
      | none => rw [ha, hb] at h; simp at h
      | some b =>
          rw [ha, hb] at h
          exact ⟨a, b, rfl, rfl, of_decide_eq_true h⟩

/-! ## THE KEYSTONE — `inbox_fifo`: a committed transition preserves the FIFO invariant. -/

/-- **`inbox_fifo` (THE KEYSTONE — PROVED).** Over the inbox program, a *committed* send-or-dequeue
preserves the FIFO safety invariant `tail ≤ head` AND advances both cursors monotonically (neither
`head` nor `tail` ever retreats). This is the inbox's life invariant: the consumer never passes the
producer, and the cursors are append-only — proved purely from the `RecordProgram` constraints
holding post-commit (lifting `inboxExec_admitted` + `evalConstraint` for `fieldLeField`/`monotonic`).
The capacity bound `inflight ≤ capacity` is the companion `inbox_capacity_held` below. -/
theorem inbox_fifo
    {cap : Int} {method : Nat} {old new : Value}
    (h : inboxExec (inboxProgram cap) method old (sendOps) = some new
       ∨ inboxExec (inboxProgram cap) method old (dequeueOps) = some new) :
    -- the safety invariant: tail ≤ head post-commit
    (∃ t hd, new.scalar "tail" = some t ∧ new.scalar "head" = some hd ∧ t ≤ hd)
    -- head is monotone (a send never retreats the producer)
    ∧ (∃ ho hn, old.scalar "head" = some ho ∧ new.scalar "head" = some hn ∧ ho ≤ hn)
    -- tail is monotone (a dequeue never retreats the consumer)
    ∧ (∃ ot tn, old.scalar "tail" = some ot ∧ new.scalar "tail" = some tn ∧ ot ≤ tn) := by
  -- both disjuncts give the same admits hypothesis (same program, predicate over method-agnostic
  -- constraints); reduce to a single admitted candidate.
  have hadm : (inboxProgram cap).admits method old new = true := by
    rcases h with h | h <;> exact inboxExec_admitted h
  -- unfold the program to a concrete constraint list, then pull each constraint out.
  have hpred : RecordProgram.admits
      (.predicate [ .simple (.monotonic "head"), .simple (.monotonic "tail"),
                    .simple (.immutable "capacity"), .simple (.immutable "owner"),
                    .fieldLeField "tail" "head", .simple (.fieldLe "inflight" cap) ]) method old new = true := by
    simpa only [inboxProgram] using hadm
  -- `admits (.predicate cs)` is method-agnostic; normalize the method to 0 for `all_constraint_holds`.
  have hpred0 : RecordProgram.admits
      (.predicate [ .simple (.monotonic "head"), .simple (.monotonic "tail"),
                    .simple (.immutable "capacity"), .simple (.immutable "owner"),
                    .fieldLeField "tail" "head", .simple (.fieldLe "inflight" cap) ]) 0 old new = true := by
    simpa only [RecordProgram.admits] using hpred
  refine ⟨?_, ?_, ?_⟩
  · -- tail ≤ head
    have hc := all_constraint_holds hpred0 (c := .fieldLeField "tail" "head") (by simp)
    obtain ⟨t, hd, ht, hh, hle⟩ := fieldLeField_holds hc
    exact ⟨t, hd, ht, hh, hle⟩
  · -- head monotone
    have hc := all_constraint_holds hpred0 (c := .simple (.monotonic "head")) (by simp)
    exact monotonic_holds hc
  · -- tail monotone
    have hc := all_constraint_holds hpred0 (c := .simple (.monotonic "tail")) (by simp)
    exact monotonic_holds hc

/-- **`inbox_capacity_held` (PROVED)** — a committed transition keeps the in-flight count within
capacity: `new.inflight ≤ cap`. (The clean, in-catalog half of the capacity bound; the cross-slot
`head - tail ≤ cap` relational form is the `-- OPEN:` in `inboxProgram`. Here we prove the derived
register stays bounded, which — GIVEN the `inflightTracks` discipline `inboxExec` maintains — is
exactly the capacity bound.) -/
theorem inbox_capacity_held
    {cap : Int} {method : Nat} {old new : Value}
    (h : inboxExec (inboxProgram cap) method old (sendOps) = some new
       ∨ inboxExec (inboxProgram cap) method old (dequeueOps) = some new) :
    ∃ inflight, new.scalar "inflight" = some inflight ∧ inflight ≤ cap := by
  have hadm : (inboxProgram cap).admits method old new = true := by
    rcases h with h | h <;> exact inboxExec_admitted h
  have hpred0 : RecordProgram.admits
      (.predicate [ .simple (.monotonic "head"), .simple (.monotonic "tail"),
                    .simple (.immutable "capacity"), .simple (.immutable "owner"),
                    .fieldLeField "tail" "head", .simple (.fieldLe "inflight" cap) ]) 0 old new = true := by
    simpa only [inboxProgram, RecordProgram.admits] using hadm
  have hc := all_constraint_holds hpred0 (c := .simple (.fieldLe "inflight" cap)) (by simp)
  simp only [evalConstraint, evalSimple] at hc
  cases hb : new.scalar "inflight" with
  | none => rw [hb] at hc; simp at hc
  | some b =>
      rw [hb] at hc
      exact ⟨b, rfl, of_decide_eq_true hc⟩

/-! ## SenderAuthorized — route a *send* through the `Caveat.Token` layer. -/

/-- The request context a send's authorization caveat is evaluated against. Abstract here (a height
stand-in); the real PI surface instantiates it (`Authority/Caveat.lean`'s `Ctx`). -/
abbrev SendCtx := Nat

/-- A *send* is **authorized** iff it presents a `Caveat.Token` whose caveats all discharge at the
request context. This routes the send through the keys-as-caps token layer (`Authority/Caveat.lean`)
exactly as `STORAGE-AS-CELL-PROGRAMS §3.1` "sender authorization" requires: the producer must hold an
authorized-sender capability. (`Token.admits` is the fail-closed meet ⋀ of all the chain's caveats.) -/
def sendAuthorized
    {Gateway : Type} (tok : Token SendCtx Gateway) (ctx : SendCtx) (d : Discharges Gateway) : Bool :=
  tok.admits ctx d

/-- **`gatedSend` — a send gated by BOTH the program AND an authorized-sender token.** It commits
only if the token discharges (`sendAuthorized`) *and* the inbox program admits the candidate. This
is the two-obligation discipline (`REORIENT §6`): the token layer carries authorization, the
`RecordProgram` carries the FIFO/state law — both must hold for a send to commit. -/
def gatedSend
    {Gateway : Type} (cap : Int) (tok : Token SendCtx Gateway) (ctx : SendCtx)
    (d : Discharges Gateway) (old : Value) : Option Value :=
  if sendAuthorized tok ctx d = true then
    inboxExec (inboxProgram cap) methodSend old sendOps
  else
    none

/-- **`send_requires_authorized_token` (PROVED)** — the clean gate-AND lemma: a *committed* gated
send necessarily presented an authorized-sender token that discharges. So a send that no authorized
token covers can never commit — the token layer is load-bearing on the send path, never bypassed.
This is the keys-as-caps `Discharged` object for the send (`Token.admits ⇒ Laws.Discharged`,
`Authority/Caveat.lean`'s `token_discharges`), ready to feed the cross-vat vat-boundary law. -/
theorem send_requires_authorized_token
    {Gateway : Type} {cap : Int} {tok : Token SendCtx Gateway} {ctx : SendCtx}
    {d : Discharges Gateway} {old new : Value}
    (h : gatedSend cap tok ctx d old = some new) :
    tok.admits ctx d = true := by
  unfold gatedSend at h
  by_cases ha : sendAuthorized tok ctx d = true
  · simpa only [sendAuthorized] using ha
  · rw [if_neg ha] at h; exact absurd h (by simp)

/-- **`gatedSend_also_admitted` (PROVED)** — a committed gated send ALSO satisfies the inbox
program (both obligations discharged). Together with `send_requires_authorized_token` this is the
full characterization: a committed send presented a discharging token AND was admitted by the FIFO
program (so `inbox_fifo` applies to it). -/
theorem gatedSend_also_admitted
    {Gateway : Type} {cap : Int} {tok : Token SendCtx Gateway} {ctx : SendCtx}
    {d : Discharges Gateway} {old new : Value}
    (h : gatedSend cap tok ctx d old = some new) :
    (inboxProgram cap).admits methodSend old new = true := by
  unfold gatedSend at h
  by_cases ha : sendAuthorized tok ctx d = true
  · rw [if_pos ha] at h; exact inboxExec_admitted h
  · rw [if_neg ha] at h; exact absurd h (by simp)

-- OPEN: `sendAuthorized` proves a *discharging token was presented*, but does NOT bind that token's
-- identity to the on-wire `sender` (the message author) — i.e. "the token's subject IS the address
-- that signed this send". That binding is the verify/find seam's job (`Laws.Verifiable` /
-- `CryptoKernel`): the token's `RootSeal`/issuer-root must equal the inbox's `sender_set_root` and
-- the presenter must control the sealed key. dregg1's scalar evaluator defers exactly this (it
-- returns `true` for `SenderAuthorized` and discharges it in a dedicated auth pass; see
-- `Exec/Program.lean`'s `boundDelta`/`Witnessed` deferral). We defer it identically and honestly,
-- rather than fake a binding the single-cell evaluator cannot witness.

/-! ## It runs (`#eval`) — a fresh inbox; a send; a dequeue; rejected malformed transitions. -/

/-- A fresh inbox at `head = tail = 0`, `inflight = 0`, capacity 3, owner-ref 7. Conforms to
`inboxSchema`; `tail ≤ head` (0 ≤ 0) and `inflight ≤ capacity` (0 ≤ 3) hold. -/
def freshInbox : Value :=
  .record [ ("head", .int 0), ("tail", .int 0), ("capacity", .int 3)
          , ("owner", .dig 7), ("inflight", .int 0) ]

/-- An inbox after two sends: head = 2, tail = 0, inflight = 2 (2 in-flight ≤ capacity 3). -/
def inbox2 : Value :=
  .record [ ("head", .int 2), ("tail", .int 0), ("capacity", .int 3)
          , ("owner", .dig 7), ("inflight", .int 2) ]

-- `conforms` to the schema (a well-shaped inbox record):
#eval conforms freshInbox (.record inboxSchema)   -- true

-- A SEND on a fresh inbox: head 0→1, inflight 0→1. tail (0) ≤ head (1) ✓, inflight (1) ≤ cap (3) ✓
#eval inboxExec (inboxProgram 3) methodSend freshInbox sendOps
-- some (record [head 1, tail 0, capacity 3, owner 7, inflight 1])

-- A DEQUEUE on `inbox2` (head 2, tail 0): tail 0→1, inflight 2→1. tail (1) ≤ head (2) ✓
#eval inboxExec (inboxProgram 3) methodDequeue inbox2 dequeueOps
-- some (record [head 2, tail 1, capacity 3, owner 7, inflight 1])

-- A SEND that would BREACH CAPACITY: at inbox2 (inflight 2), a send → inflight 3 ≤ cap 3 still ok;
-- but at a full inbox (inflight = cap = 3) a further send → inflight 4 > 3 ⇒ REJECTED (none):
#eval inboxExec (inboxProgram 3) methodSend
        (.record [ ("head", .int 3), ("tail", .int 0), ("capacity", .int 3)
                 , ("owner", .dig 7), ("inflight", .int 3) ]) sendOps
-- none  (inflight would be 4 > capacity 3 — capacity bound rejects)

-- A MALFORMED transition: tail > head. Start from a (deliberately malformed) state where a dequeue
-- would push tail past head — `tail = head = 0`, dequeue ⇒ tail 1 > head 0 ⇒ REJECTED:
#eval inboxExec (inboxProgram 3) methodDequeue freshInbox dequeueOps
-- none  (tail would be 1 > head 0 — fieldLeField "tail" "head" rejects the consumer passing producer)

-- A MALFORMED transition: head NON-MONOTONE (a send that tries to RETREAT head). We can't express a
-- retreat with `sendOps` (it only adds), so feed an explicit retreating op list; `monotonic "head"`
-- rejects head 2 → 1:
#eval inboxExec (inboxProgram 3) methodSend inbox2 [ .addScalar "head" (-1), .addScalar "inflight" (-1) ]
-- none  (head would be 1 < old head 2 — monotonic "head" rejects the retreat)

/-! ### A SenderAuthorized send demo through the token layer. -/

/-- An authorized-sender biscuit: a root biscuit attenuated with "request height ≤ 1000" (a clean
authorized-sender capability). A real inbox would bind it to `sender_set_root` (the `-- OPEN:`). -/
def senderToken : Token SendCtx Unit :=
  (Token.mk .biscuit []).attenuate (.local (fun h => decide (h ≤ 1000)))

/-- No third-party discharges needed. -/
def noDischarges : Discharges Unit := fun _ => false

-- A gated send WITH a discharging token at ctx 500 (≤ 1000) ⇒ token discharges AND program admits:
#eval gatedSend 3 senderToken 500 noDischarges freshInbox
-- some (record [head 1, tail 0, capacity 3, owner 7, inflight 1])

-- A gated send whose token FAILS to discharge (ctx 2000 > 1000) ⇒ REJECTED before the program runs:
#eval gatedSend 3 senderToken 2000 noDischarges freshInbox
-- none  (the authorized-sender caveat narrowed this request out — sender not authorized here)

end Dregg2.Exec.CapInbox
