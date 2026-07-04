/-
Captp.Session — the capability session: bidirectional import/export tables with
epoch tagging, reference-counted GC, and one-shot answer resolution.

A session is the state shared by two peers of the capability transport.  It
maps between local object identities (`Obj`) and the wire positions carried by
descriptors (`Captp.Descriptor`), in three tables:

* **export** — objects *we* offer the peer.  `exportObject` allocates a fresh
  wire position, reference-counted for GC (`refs`), and tagged with the current
  session epoch.
* **import** — objects the peer offered us, bound to a local proxy at a
  peer-chosen position (`importObject`).
* **answer** — the (initially unresolved) results of pending deliveries, the
  vehicle of promise pipelining (`allocateAnswer`); each carries a one-shot
  `resolved` flag.

The **epoch** is a monotone session-reset counter, tagged onto every entry — the
exact shape of the Slab file-descriptor generation guard.  A descriptor
observed on the wire is *stamped* with the epoch under which it was captured
(`resolveStamped`); resolution succeeds only when the live entry's epoch matches
the stamp.  A session reset bumps the epoch (`bumpEpoch`) and rebinds positions;
a stamp from a prior epoch therefore never resolves to a current-epoch object —
the ABA defense, transcribed from the connection-generation guard to the
capability layer.

Theorem groups:
* round-trip / inverse: an exported (imported) object, re-read through its own
  wire descriptor within the same epoch, resolves to the identical object;
* epoch guard: a prior-epoch stamp never resolves to a current-epoch entry;
* GC: an export entry is dropped exactly when its reference count reaches zero —
  never a live-reference drop;
* one-shot: a delivered answer/promise resolves at most once (the linear
  discipline of the ring lease).
-/
import Captp.Basic

namespace Captp

/-! ### Pointwise-updated total functions (positions ⇀ entries) -/

variable {α : Type}

/-- Point update of a total function. -/
def upd (f : Nat → α) (i : Nat) (v : α) : Nat → α :=
  fun j => if j = i then v else f j

@[simp] theorem upd_self (f : Nat → α) (i : Nat) (v : α) : upd f i v i = v := by
  simp [upd]

theorem upd_ne (f : Nat → α) (v : α) {i j : Nat} (h : j ≠ i) : upd f i v j = f j := by
  simp [upd, h]

/-! ### Table entries and the session -/

/-- An export-table entry: the object we offer, its GC weight, and the epoch it
was assigned under. -/
structure ExportEntry where
  obj : Obj
  refs : Int
  epoch : Nat
deriving Repr

/-- An import-table entry: the object we bound a proxy to, epoch-tagged. -/
structure ImportEntry where
  obj : Obj
  epoch : Nat
deriving Repr

/-- An answer-table entry: the promise, its one-shot resolution flag, and the
epoch it was allocated under. -/
structure AnswerEntry where
  promise : Obj
  resolved : Bool
  epoch : Nat
deriving Repr

/-- A capability session between two peers. -/
structure Session where
  exports : Nat → Option ExportEntry
  imports : Nat → Option ImportEntry
  answers : Nat → Option AnswerEntry
  nextExport : Position
  nextAnswer : Position
  epoch : Nat

namespace Session

/-- The initial session: empty tables, positions at 0, epoch at 1 (epoch 0 is
the reserved "no-epoch" sentinel — no live entry ever carries it). -/
def init : Session where
  exports := fun _ => none
  imports := fun _ => none
  answers := fun _ => none
  nextExport := 0
  nextAnswer := 0
  epoch := 1

/-! ### Operations -/

/-- Export a local object: allocate a fresh export position (weight 1, current
epoch), returning the position and the updated session. -/
def exportObject (s : Session) (o : Obj) : Position × Session :=
  (s.nextExport,
   { s with
      exports := upd s.exports s.nextExport (some { obj := o, refs := 1, epoch := s.epoch }),
      nextExport := s.nextExport + 1 })

/-- Import an object the peer named at wire position `pos`: bind a local proxy,
epoch-tagged. -/
def importObject (s : Session) (pos : Position) (o : Obj) : Session :=
  { s with imports := upd s.imports pos (some { obj := o, epoch := s.epoch }) }

/-- Allocate a fresh answer position for a pending delivery (unresolved,
current epoch), returning the position and the updated session. -/
def allocateAnswer (s : Session) (promise : Obj) : Position × Session :=
  (s.nextAnswer,
   { s with
      answers := upd s.answers s.nextAnswer (some { promise := promise, resolved := false, epoch := s.epoch }),
      nextAnswer := s.nextAnswer + 1 })

/-- Deliver a resolution to an answer position: succeeds (marking it resolved)
iff the position holds an as-yet-unresolved answer; a second delivery fails.
This is the one-shot gate. -/
def tryResolve (s : Session) (pos : Position) : Option Session :=
  match s.answers pos with
  | some e => if e.resolved then none
      else some { s with answers := upd s.answers pos (some { e with resolved := true }) }
  | none => none

/-- Apply a GC weight delta to an export position.  Returns whether the entry
was removed (weight fell to zero or below) and the updated session. -/
def applyGcExport (s : Session) (pos : Position) (d : Int) : Bool × Session :=
  match s.exports pos with
  | none => (false, s)
  | some e =>
      if e.refs + d ≤ 0 then
        (true, { s with exports := upd s.exports pos none })
      else
        (false, { s with exports := upd s.exports pos (some { e with refs := e.refs + d }) })

/-- Release an answer position (GC answer). -/
def releaseAnswer (s : Session) (pos : Position) : Session :=
  { s with answers := upd s.answers pos none }

/-- Bump the epoch: a session reset.  Positions rebound after a bump carry the
new epoch, so prior-epoch stamps no longer match. -/
def bumpEpoch (s : Session) : Session :=
  { s with epoch := s.epoch + 1 }

/-! ### Resolution -/

/-- Resolve an export position to its object. -/
def resolveExport (s : Session) (pos : Position) : Option Obj :=
  match s.exports pos with | some e => some e.obj | none => none

/-- Resolve an import position to its object. -/
def resolveImport (s : Session) (pos : Position) : Option Obj :=
  match s.imports pos with | some e => some e.obj | none => none

/-- Resolve an answer position to its promise. -/
def resolveAnswerObj (s : Session) (pos : Position) : Option Obj :=
  match s.answers pos with | some e => some e.promise | none => none

/-- Resolve a descriptor against the local tables.  Handoff tokens do not
resolve locally — they route to the third-party-handoff protocol. -/
def resolveDescriptor (s : Session) (d : Descriptor) : Option Obj :=
  match d with
  | .Export pos => resolveExport s pos
  | .ImportObject pos => resolveImport s pos
  | .ImportPromise pos => resolveImport s pos
  | .Answer pos => resolveAnswerObj s pos
  | .HandoffGive .. => none
  | .HandoffReceive .. => none

/-- The epoch of the entry a descriptor points at (`none` if the position is
empty or the descriptor is a handoff token). -/
def descEpoch (s : Session) (d : Descriptor) : Option Nat :=
  match d with
  | .Export pos => match s.exports pos with | some e => some e.epoch | none => none
  | .ImportObject pos => match s.imports pos with | some e => some e.epoch | none => none
  | .ImportPromise pos => match s.imports pos with | some e => some e.epoch | none => none
  | .Answer pos => match s.answers pos with | some e => some e.epoch | none => none
  | .HandoffGive .. => none
  | .HandoffReceive .. => none

/-- Resolve an epoch-*stamped* descriptor: the captured epoch `e` must match the
live entry's epoch, else resolution is rejected.  This is the generation guard
lifted to descriptors. -/
def resolveStamped (s : Session) (d : Descriptor) (e : Nat) : Option Obj :=
  match descEpoch s d with
  | some e' => if e' = e then resolveDescriptor s d else none
  | none => none

/-- A successful stamped resolution pins the live entry's epoch to the stamp. -/
theorem resolveStamped_epoch {s : Session} {d : Descriptor} {e : Nat} {o : Obj}
    (h : resolveStamped s d e = some o) : descEpoch s d = some e := by
  unfold resolveStamped at h
  cases hd : descEpoch s d with
  | none => simp [hd] at h
  | some e' =>
    simp only [hd] at h
    by_cases he : e' = e
    · subst he; rfl
    · simp [he] at h

/-! ### Well-formedness

Every live entry carries an epoch in `[1, s.epoch]` (never the sentinel 0,
never a future epoch), and every live answer sits below the answer allocator —
the freshness facts the epoch guard and the one-shot discipline rest on. -/

structure WF (s : Session) : Prop where
  epoch_pos : 1 ≤ s.epoch
  exp_epoch : ∀ p e, s.exports p = some e → 1 ≤ e.epoch ∧ e.epoch ≤ s.epoch
  imp_epoch : ∀ p e, s.imports p = some e → 1 ≤ e.epoch ∧ e.epoch ≤ s.epoch
  ans_epoch : ∀ p e, s.answers p = some e → 1 ≤ e.epoch ∧ e.epoch ≤ s.epoch
  ans_bound : ∀ p e, s.answers p = some e → p < s.nextAnswer

protected theorem WF.init : (init).WF where
  epoch_pos := Nat.le_refl 1
  exp_epoch := by intro p e h; exact absurd h (by simp [init])
  imp_epoch := by intro p e h; exact absurd h (by simp [init])
  ans_epoch := by intro p e h; exact absurd h (by simp [init])
  ans_bound := by intro p e h; exact absurd h (by simp [init])

/-- A captured stamp's epoch was assigned in the past. -/
theorem descEpoch_le {s : Session} (h : s.WF) {d : Descriptor} {e : Nat}
    (hd : descEpoch s d = some e) : e ≤ s.epoch := by
  cases d with
  | Export pos =>
    simp only [descEpoch] at hd
    cases hx : s.exports pos with
    | none => rw [hx] at hd; exact absurd hd (by simp)
    | some entry =>
      rw [hx] at hd
      simp only [Option.some.injEq] at hd
      have := (h.exp_epoch pos entry hx).2; omega
  | ImportObject pos =>
    simp only [descEpoch] at hd
    cases hx : s.imports pos with
    | none => rw [hx] at hd; exact absurd hd (by simp)
    | some entry =>
      rw [hx] at hd
      simp only [Option.some.injEq] at hd
      have := (h.imp_epoch pos entry hx).2; omega
  | ImportPromise pos =>
    simp only [descEpoch] at hd
    cases hx : s.imports pos with
    | none => rw [hx] at hd; exact absurd hd (by simp)
    | some entry =>
      rw [hx] at hd
      simp only [Option.some.injEq] at hd
      have := (h.imp_epoch pos entry hx).2; omega
  | Answer pos =>
    simp only [descEpoch] at hd
    cases hx : s.answers pos with
    | none => rw [hx] at hd; exact absurd hd (by simp)
    | some entry =>
      rw [hx] at hd
      simp only [Option.some.injEq] at hd
      have := (h.ans_epoch pos entry hx).2; omega
  | HandoffGive k l ss => simp only [descEpoch] at hd; exact absurd hd (by simp)
  | HandoffReceive rs sd => simp only [descEpoch] at hd; exact absurd hd (by simp)

/-- A captured stamp's epoch is a real epoch: never the sentinel 0.  (The lower
half of the epoch invariant, the mirror of `descEpoch_le`.) -/
theorem descEpoch_pos {s : Session} (h : s.WF) {d : Descriptor} {e : Nat}
    (hd : descEpoch s d = some e) : 1 ≤ e := by
  cases d with
  | Export pos =>
    simp only [descEpoch] at hd
    cases hx : s.exports pos with
    | none => rw [hx] at hd; exact absurd hd (by simp)
    | some entry =>
      rw [hx] at hd
      simp only [Option.some.injEq] at hd
      have := (h.exp_epoch pos entry hx).1; omega
  | ImportObject pos =>
    simp only [descEpoch] at hd
    cases hx : s.imports pos with
    | none => rw [hx] at hd; exact absurd hd (by simp)
    | some entry =>
      rw [hx] at hd
      simp only [Option.some.injEq] at hd
      have := (h.imp_epoch pos entry hx).1; omega
  | ImportPromise pos =>
    simp only [descEpoch] at hd
    cases hx : s.imports pos with
    | none => rw [hx] at hd; exact absurd hd (by simp)
    | some entry =>
      rw [hx] at hd
      simp only [Option.some.injEq] at hd
      have := (h.imp_epoch pos entry hx).1; omega
  | Answer pos =>
    simp only [descEpoch] at hd
    cases hx : s.answers pos with
    | none => rw [hx] at hd; exact absurd hd (by simp)
    | some entry =>
      rw [hx] at hd
      simp only [Option.some.injEq] at hd
      have := (h.ans_epoch pos entry hx).1; omega
  | HandoffGive k l ss => simp only [descEpoch] at hd; exact absurd hd (by simp)
  | HandoffReceive rs sd => simp only [descEpoch] at hd; exact absurd hd (by simp)

/-! ### Round-trip / inverse within an epoch

An exported object, re-read through its own `Export` descriptor within the same
epoch, resolves to the identical object; likewise for imports and answers.  This
is the import/export inverse across a session. -/

/-- Exporting then resolving the produced position returns the same object, and
export does not move the epoch. -/
theorem export_resolves (s : Session) (o : Obj) :
    resolveExport (s.exportObject o).2 (s.exportObject o).1 = some o
    ∧ (s.exportObject o).2.epoch = s.epoch := by
  refine ⟨?_, rfl⟩
  simp only [exportObject, resolveExport, upd_self]

/-- The stamped round-trip: the freshly exported descriptor, stamped with the
current epoch, resolves to the exported object. -/
theorem export_stamped_resolves (s : Session) (o : Obj) :
    resolveStamped (s.exportObject o).2 (Descriptor.Export (s.exportObject o).1) s.epoch
      = some o := by
  simp [exportObject, resolveStamped, descEpoch, resolveDescriptor, resolveExport, upd_self]

/-- Importing an object at `pos` then resolving `pos` returns the same object. -/
theorem import_resolves (s : Session) (pos : Position) (o : Obj) :
    resolveImport (s.importObject pos o) pos = some o
    ∧ resolveStamped (s.importObject pos o) (Descriptor.ImportObject pos) s.epoch = some o := by
  refine ⟨?_, ?_⟩
  · simp only [importObject, resolveImport, upd_self]
  · simp [importObject, resolveStamped, descEpoch, resolveDescriptor, resolveImport, upd_self]

/-- Allocating an answer then resolving that position returns the promise. -/
theorem allocate_resolves (s : Session) (pr : Obj) :
    resolveAnswerObj (s.allocateAnswer pr).2 (s.allocateAnswer pr).1 = some pr := by
  simp only [allocateAnswer, resolveAnswerObj, upd_self]

/-! ### The epoch guard -/

/-- **A prior-epoch stamp is rejected against a current-epoch entry.** If the
live entry at `d` carries epoch `ecur` and the stamp names a different epoch,
resolution returns `none`.  (Core generation-guard lemma.) -/
theorem stale_stamp_rejected {s : Session} {d : Descriptor} {ecur e : Nat}
    (hcur : descEpoch s d = some ecur) (hne : ecur ≠ e) :
    resolveStamped s d e = none := by
  unfold resolveStamped
  simp only [hcur, if_neg hne]

/-- The sentinel epoch 0 never resolves: no live entry carries it. -/
theorem resolveStamped_zero {s : Session} (h : s.WF) (d : Descriptor) :
    resolveStamped s d 0 = none := by
  cases hd : descEpoch s d with
  | none => simp only [resolveStamped, hd]
  | some e' =>
    have he : 1 ≤ e' := descEpoch_pos h hd
    simp only [resolveStamped, hd, if_neg (show ¬ e' = 0 by omega)]

/-! ### Runs: arbitrary futures after a capture point -/

/-- The session operations a run is made of. -/
inductive Op where
  | exportObject (o : Obj)
  | importObject (pos : Position) (o : Obj)
  | allocateAnswer (promise : Obj)
  | tryResolve (pos : Position)
  | gcExport (pos : Position) (d : Int)
  | releaseAnswer (pos : Position)
  | bumpEpoch

/-- One operation (a failed `tryResolve` is a no-op). -/
def step (s : Session) : Op → Session
  | .exportObject o => (s.exportObject o).2
  | .importObject pos o => s.importObject pos o
  | .allocateAnswer pr => (s.allocateAnswer pr).2
  | .tryResolve pos => (s.tryResolve pos).getD s
  | .gcExport pos d => (s.applyGcExport pos d).2
  | .releaseAnswer pos => s.releaseAnswer pos
  | .bumpEpoch => s.bumpEpoch

/-- A run: operations applied in order. -/
def run (s : Session) : List Op → Session
  | [] => s
  | op :: ops => (s.step op).run ops

/-- The epoch never moves backward across one step. -/
theorem epoch_mono_step (s : Session) (op : Op) : s.epoch ≤ (s.step op).epoch := by
  cases op with
  | exportObject o => exact Nat.le_refl _
  | importObject pos o => exact Nat.le_refl _
  | allocateAnswer pr => exact Nat.le_refl _
  | tryResolve pos =>
    simp only [step, tryResolve]
    cases hp : s.answers pos with
    | none => simp
    | some e =>
      by_cases hr : e.resolved <;> simp [hp, hr]
  | gcExport pos d =>
    simp only [step, applyGcExport]
    cases hx : s.exports pos with
    | none => simp
    | some e => by_cases hc : e.refs + d ≤ 0 <;> simp [hx, hc]
  | releaseAnswer pos => exact Nat.le_refl _
  | bumpEpoch => simp only [step, bumpEpoch]; omega

/-- The epoch never moves backward across a whole run. -/
theorem epoch_mono_run (s : Session) (ops : List Op) : s.epoch ≤ (s.run ops).epoch := by
  induction ops generalizing s with
  | nil => exact Nat.le_refl _
  | cons op ops ih => exact Nat.le_trans (epoch_mono_step s op) (ih (s.step op))

/-- **An epoch bump invalidates stale descriptors.** A descriptor stamped at
epoch `e` and valid at capture never resolves, after a run that advanced the
epoch, to a current-epoch entry now bound at that descriptor's position.  The
capability-layer analog of the Slab stale-token guard. -/
theorem bump_invalidates {s : Session} (h : s.WF) {d : Descriptor} {e : Nat} {o : Obj}
    (hcap : resolveStamped s d e = some o)
    (ops : List Op)
    (hcur : descEpoch (s.run ops) d = some ((s.run ops).epoch))
    (hbumped : s.epoch < (s.run ops).epoch) :
    resolveStamped (s.run ops) d e = none := by
  have hde : descEpoch s d = some e := resolveStamped_epoch hcap
  have hle : e ≤ s.epoch := descEpoch_le h hde
  exact stale_stamp_rejected hcur (by omega)

/-- Concrete instantiation: reset the epoch (a reconnect) and rebind the *same*
import position to a new object.  The old stamp — captured under the prior
epoch — no longer resolves.  (Import positions are peer-chosen, so a reset can
legitimately reuse a position; the epoch is what tells the incarnations apart.) -/
theorem bump_then_reimport_invalidates {s : Session} (_h : s.WF)
    {pos : Position} {o o' : Obj}
    (_hcap : resolveStamped s (Descriptor.ImportObject pos) s.epoch = some o) :
    resolveStamped ((s.bumpEpoch).importObject pos o') (Descriptor.ImportObject pos) s.epoch
      = none := by
  apply stale_stamp_rejected (ecur := s.epoch + 1)
  · simp only [importObject, bumpEpoch, descEpoch, resolveImport, upd_self]
  · omega

/-! ### GC: no live-reference drop -/

/-- **GC removes an entry only when its resulting reference count is ≤ 0.** A
removal witnesses a dead entry; a live-reference drop is impossible. -/
theorem gc_removes_only_dead {s : Session} {pos : Position} {d : Int}
    (hrm : (s.applyGcExport pos d).1 = true) :
    ∃ e, s.exports pos = some e ∧ e.refs + d ≤ 0 := by
  cases hx : s.exports pos with
  | none => simp [applyGcExport, hx] at hrm
  | some e =>
    by_cases hc : e.refs + d ≤ 0
    · exact ⟨e, rfl, hc⟩
    · simp [applyGcExport, hx, hc] at hrm

/-- **A live entry (strictly positive resulting count) is never dropped**, and
after GC still resolves to the same object with the debited count. -/
theorem gc_preserves_positive {s : Session} {pos : Position} {d : Int} {e : ExportEntry}
    (hx : s.exports pos = some e) (hpos : 0 < e.refs + d) :
    (s.applyGcExport pos d).1 = false
    ∧ (s.applyGcExport pos d).2.exports pos = some { e with refs := e.refs + d }
    ∧ resolveExport (s.applyGcExport pos d).2 pos = some e.obj := by
  have hc : ¬ (e.refs + d ≤ 0) := by omega
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [applyGcExport, hx, hc, if_false, resolveExport, upd_self]

/-- GC on an absent position is a no-op. -/
theorem gc_absent_noop {s : Session} {pos : Position} {d : Int}
    (hx : s.exports pos = none) : s.applyGcExport pos d = (false, s) := by
  simp only [applyGcExport, hx]

/-! ### One-shot answer resolution — a delivered promise resolves at most once -/

/-- Computation lemma: a `tryResolve` on an unresolved answer succeeds, marking
it resolved in place. -/
theorem tryResolve_success {s : Session} {pos : Position} {e : AnswerEntry}
    (hp : s.answers pos = some e) (hr : e.resolved = false) :
    s.tryResolve pos
      = some { s with answers := upd s.answers pos (some { e with resolved := true }) } := by
  simp [tryResolve, hp, hr]

/-- Computation lemma: a `tryResolve` on an already-resolved answer fails. -/
theorem tryResolve_fail_resolved {s : Session} {pos : Position} {e : AnswerEntry}
    (hp : s.answers pos = some e) (hr : e.resolved = true) : s.tryResolve pos = none := by
  simp [tryResolve, hp, hr]

/-- Computation lemma: a `tryResolve` on an empty position fails. -/
theorem tryResolve_fail_absent {s : Session} {pos : Position}
    (hp : s.answers pos = none) : s.tryResolve pos = none := by
  simp [tryResolve, hp]

/-- `tryResolve` succeeds exactly when the position holds an unresolved answer. -/
theorem tryResolve_isSome_iff {s : Session} {pos : Position} :
    (s.tryResolve pos).isSome ↔ ∃ e, s.answers pos = some e ∧ e.resolved = false := by
  constructor
  · intro hh
    cases hp : s.answers pos with
    | none => rw [tryResolve_fail_absent hp] at hh; simp at hh
    | some e =>
      cases hr : e.resolved with
      | true => rw [tryResolve_fail_resolved hp hr] at hh; simp at hh
      | false => exact ⟨e, rfl, hr⟩
  · rintro ⟨e, hp, hr⟩
    rw [tryResolve_success hp hr]; simp

/-- After a successful resolution, the answer position is marked resolved. -/
theorem tryResolve_marks_resolved {s s' : Session} {pos : Position}
    (h : s.tryResolve pos = some s') :
    ∃ e, s'.answers pos = some e ∧ e.resolved = true := by
  cases hp : s.answers pos with
  | none => rw [tryResolve_fail_absent hp] at h; exact absurd h (by simp)
  | some e =>
    cases hr : e.resolved with
    | true => rw [tryResolve_fail_resolved hp hr] at h; exact absurd h (by simp)
    | false =>
      rw [tryResolve_success hp hr] at h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨{ e with resolved := true }, by simp only [upd_self], rfl⟩

/-- **One-shot linearity (headline).** A delivered answer cannot be delivered
again: a second `tryResolve` on the same position fails.  The linear
acquire-once discipline of the ring lease, on the promise layer. -/
theorem tryResolve_once {s s' : Session} {pos : Position}
    (h : s.tryResolve pos = some s') : s'.tryResolve pos = none := by
  obtain ⟨e, he, hres⟩ := tryResolve_marks_resolved h
  exact tryResolve_fail_resolved he hres

/-- Handoff descriptors never resolve against the local tables — they are
routed to the third-party-handoff protocol, so they cannot alias a local
export/import/answer.  (Well-formedness of the handoff path.) -/
theorem handoff_resolves_none (s : Session)
    (a : Descriptor) (ha : a.isHandoff = true) :
    resolveDescriptor s a = none ∧ (∀ e, resolveStamped s a e = none) := by
  cases a with
  | HandoffGive k l ss =>
    refine ⟨rfl, fun e => ?_⟩
    simp only [resolveStamped, descEpoch]
  | HandoffReceive rs sd =>
    refine ⟨rfl, fun e => ?_⟩
    simp only [resolveStamped, descEpoch]
  | _ => simp [Descriptor.isHandoff] at ha

end Session

end Captp
