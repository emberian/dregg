import Quic.Fsm

/-!
# QUIC connection FSM — theorems (deterministic half)

* `step_total`, `step_deterministic` — the machine is a total function;
  stated on the relational graph for the record.
* `draining_absorbing` / `run_draining` — the draining phase is absorbing
  **and silent** on every input (RFC 9000 §10.2.2's MUST NOT send).
* `no_appdata_before_established` — the machine never delivers
  application data up the stack unless the connection is established
  (the early-data path that would relax this lives in `Quic.Replay`).
* `step_largestAcked_mono` / `run_largestAcked_mono` — per-space
  largest-acked tracking is monotone.
* `step_wf` / `run_wf` / `init_wf` — every acknowledged packet number was
  sent, and the stream-count sandwich `closed ≤ opened ≤ limit` holds, in
  every reachable state.
* `run_emitted_pairwise` — **monotone packet numbers per space**: along
  any run, the packet numbers spent on the wire in each space are
  strictly increasing; a number is never reused (RFC 9000 §12.3).

The proofs factor through one classification lemma (`step_classify`):
every step is space-quiet, an ACK fold into one space, or a spend of
exactly one packet number in one space; and the stream counters move by
at most one, under their guards.
-/

namespace Quic

/-! ## Space plumbing -/

@[simp] theorem space_setSpace_same (c : Conn) (sp : PnSpace) (v : SpaceSt) :
    (c.setSpace sp v).space sp = v := by
  cases sp <;> rfl

theorem space_setSpace_ne (c : Conn) {sp sp' : PnSpace} (h : sp' ≠ sp)
    (v : SpaceSt) : (c.setSpace sp v).space sp' = c.space sp' := by
  cases sp <;> cases sp' <;> first | rfl | exact absurd rfl h

@[simp] theorem space_phaseSet (c : Conn) (p : Phase) (sp : PnSpace) :
    ({ c with phase := p } : Conn).space sp = c.space sp := by
  cases sp <;> rfl

@[simp] theorem space_streamsOpenedSet (c : Conn) (n : Nat) (sp : PnSpace) :
    ({ c with streamsOpened := n } : Conn).space sp = c.space sp := by
  cases sp <;> rfl

@[simp] theorem space_streamsClosedSet (c : Conn) (n : Nat) (sp : PnSpace) :
    ({ c with streamsClosed := n } : Conn).space sp = c.space sp := by
  cases sp <;> rfl

@[simp] theorem streamsOpened_setSpace (c : Conn) (sp : PnSpace) (v : SpaceSt) :
    (c.setSpace sp v).streamsOpened = c.streamsOpened := by
  cases sp <;> rfl

@[simp] theorem streamsClosed_setSpace (c : Conn) (sp : PnSpace) (v : SpaceSt) :
    (c.setSpace sp v).streamsClosed = c.streamsClosed := by
  cases sp <;> rfl

@[simp] theorem maxStreams_setSpace (c : Conn) (sp : PnSpace) (v : SpaceSt) :
    (c.setSpace sp v).maxStreams = c.maxStreams := by
  cases sp <;> rfl

@[simp] theorem onAck_nextPn (s : SpaceSt) (l : Nat) :
    (s.onAck l).nextPn = s.nextPn := by
  unfold SpaceSt.onAck
  split
  · split <;> rfl
  · rfl

theorem space_bump' (c : Conn) (sp sp' : PnSpace) :
    (c.bump sp).space sp' =
      if sp = sp' then { c.space sp with nextPn := (c.space sp).nextPn + 1 }
      else c.space sp' := by
  by_cases h : sp = sp'
  · rw [if_pos h]; subst h; exact space_setSpace_same c sp _
  · rw [if_neg h]; exact space_setSpace_ne c (fun he => h he.symm) _

theorem emittedPns_append (sp : PnSpace) (l₁ l₂ : List Output) :
    emittedPns sp (l₁ ++ l₂) = emittedPns sp l₁ ++ emittedPns sp l₂ := by
  induction l₁ with
  | nil => rfl
  | cons o os ih =>
      simp only [List.cons_append, emittedPns]
      cases Output.pnOf sp o <;> simp [ih]

theorem emittedPns_emit (sp spx : PnSpace) (n : Nat) :
    emittedPns sp [Output.emit spx n] = if spx = sp then [n] else [] := by
  by_cases h : spx = sp <;> simp [emittedPns, Output.pnOf, h]

theorem emittedPns_emitClose (sp spx : PnSpace) (n : Nat) :
    emittedPns sp [Output.emitClose spx n] = if spx = sp then [n] else [] := by
  by_cases h : spx = sp <;> simp [emittedPns, Output.pnOf, h]

/-! ## The step classification -/

/-- The output list spends no packet number in any space. -/
abbrev NoSpend (os : List Output) : Prop := ∀ sp, emittedPns sp os = []

/-- The step left every packet-number space untouched. -/
abbrev SpaceQuiet (c : Conn) (r : Conn × List Output) : Prop :=
  (∀ sp, r.1.space sp = c.space sp) ∧ NoSpend r.2

/-- The step folded an ACK for `l` into space `sp` and spent nothing. -/
abbrev AckIn (c : Conn) (r : Conn × List Output) (sp : PnSpace) (l : Nat) :
    Prop :=
  (∀ sp', r.1.space sp' =
      if sp = sp' then (c.space sp).onAck l else c.space sp') ∧ NoSpend r.2

/-- The step spent exactly one packet number — the current counter — in
space `sp`, advancing the counter past it, and touched no other space. -/
abbrev SpendsIn (c : Conn) (r : Conn × List Output) (sp : PnSpace) : Prop :=
  (∀ sp', emittedPns sp' r.2 =
      if sp = sp' then [(c.space sp).nextPn] else []) ∧
  (∀ sp', r.1.space sp' =
      if sp = sp' then { c.space sp with nextPn := (c.space sp).nextPn + 1 }
      else c.space sp')

/-- What one step may do to the stream counters: nothing, open one under
the limit, or close one under the open count; the limit never moves. -/
abbrev StreamAct (c c' : Conn) : Prop :=
  c'.maxStreams = c.maxStreams ∧
    (c'.streamsOpened = c.streamsOpened ∧ c'.streamsClosed = c.streamsClosed ∨
     c.streamsOpened < c.maxStreams ∧
       c'.streamsOpened = c.streamsOpened + 1 ∧
       c'.streamsClosed = c.streamsClosed ∨
     c.streamsClosed < c.streamsOpened ∧
       c'.streamsClosed = c.streamsClosed + 1 ∧
       c'.streamsOpened = c.streamsOpened)

theorem noSpend_nil : NoSpend [] := fun _ => rfl

theorem noSpend_deliver (pn : Nat) : NoSpend [Output.deliverApp pn] :=
  fun _ => rfl

theorem spaceQuiet_id (c : Conn) (os : List Output) (h : NoSpend os) :
    SpaceQuiet c (c, os) := ⟨fun _ => rfl, h⟩

theorem spaceQuiet_phase (c : Conn) (p : Phase) :
    SpaceQuiet c (({ c with phase := p } : Conn), []) :=
  ⟨fun sp => space_phaseSet c p sp, noSpend_nil⟩

theorem spaceQuiet_open (c : Conn) :
    SpaceQuiet c (({ c with streamsOpened := c.streamsOpened + 1 } : Conn), []) :=
  ⟨fun sp => space_streamsOpenedSet c _ sp, noSpend_nil⟩

theorem spaceQuiet_close (c : Conn) :
    SpaceQuiet c (({ c with streamsClosed := c.streamsClosed + 1 } : Conn), []) :=
  ⟨fun sp => space_streamsClosedSet c _ sp, noSpend_nil⟩

theorem ackIn_onAck (c : Conn) (sp : PnSpace) (l : Nat) :
    AckIn c (c.onAck sp l, []) sp l := by
  refine ⟨fun sp' => ?_, noSpend_nil⟩
  by_cases h : sp = sp'
  · rw [if_pos h]; subst h; exact space_setSpace_same c sp _
  · rw [if_neg h]; exact space_setSpace_ne c (fun he => h he.symm) _

theorem spendsIn_sendPkt (c : Conn) (sp : PnSpace) :
    SpendsIn c (c.sendPkt sp) sp :=
  ⟨fun sp' => by simp [Conn.sendPkt, emittedPns_emit],
   fun sp' => by simpa [Conn.sendPkt] using space_bump' c sp sp'⟩

theorem spendsIn_closeIn (c : Conn) (sp : PnSpace) :
    SpendsIn c (c.closeIn sp) sp :=
  ⟨fun sp' => by simp [Conn.closeIn, emittedPns_emitClose],
   fun sp' => by simpa [Conn.closeIn] using space_bump' c sp sp'⟩

theorem spendsIn_replyClose (c : Conn) (sp : PnSpace) :
    SpendsIn c (c.replyClose sp) sp :=
  ⟨fun sp' => by simp [Conn.replyClose, emittedPns_emitClose],
   fun sp' => by simpa [Conn.replyClose] using space_bump' c sp sp'⟩

theorem streamAct_refl (c : Conn) : StreamAct c c := ⟨rfl, .inl ⟨rfl, rfl⟩⟩

theorem streamAct_phase (c : Conn) (p : Phase) :
    StreamAct c ({ c with phase := p } : Conn) := ⟨rfl, .inl ⟨rfl, rfl⟩⟩

theorem streamAct_onAck (c : Conn) (sp : PnSpace) (l : Nat) :
    StreamAct c (c.onAck sp l) := by
  refine ⟨?_, .inl ⟨?_, ?_⟩⟩ <;> simp [Conn.onAck]

theorem streamAct_bump (c : Conn) (sp : PnSpace) :
    StreamAct c (c.bump sp) := by
  refine ⟨?_, .inl ⟨?_, ?_⟩⟩ <;> simp [Conn.bump]

theorem streamAct_bumpPhase (c : Conn) (sp : PnSpace) (p : Phase) :
    StreamAct c ({ c.bump sp with phase := p } : Conn) := by
  refine ⟨?_, .inl ⟨?_, ?_⟩⟩ <;> simp [Conn.bump]

/-- **The classification.** Every step is space-quiet, one ACK fold, or a
spend of exactly one packet number in one space; the stream counters move
by at most one under their guards; the stream limit is static. -/
theorem step_classify (c : Conn) (i : Input) :
    (SpaceQuiet c (step c i) ∨ (∃ sp l, AckIn c (step c i) sp l) ∨
      (∃ sp, SpendsIn c (step c i) sp)) ∧
    StreamAct c (step c i).1 := by
  unfold step
  cases c.phase with
  | draining =>
      exact ⟨.inl (spaceQuiet_id c [] noSpend_nil), streamAct_refl c⟩
  | idle =>
    cases i with
    | start => exact ⟨.inl (spaceQuiet_phase c _), streamAct_phase c _⟩
    | pktReceived sp pn =>
        exact ⟨.inl (spaceQuiet_id c [] noSpend_nil), streamAct_refl c⟩
    | ackReceived sp l =>
        exact ⟨.inl (spaceQuiet_id c [] noSpend_nil), streamAct_refl c⟩
    | sendReady sp =>
        exact ⟨.inl (spaceQuiet_id c [] noSpend_nil), streamAct_refl c⟩
    | handshakeDone =>
        exact ⟨.inl (spaceQuiet_id c [] noSpend_nil), streamAct_refl c⟩
    | streamOpened =>
        exact ⟨.inl (spaceQuiet_id c [] noSpend_nil), streamAct_refl c⟩
    | streamClosed =>
        exact ⟨.inl (spaceQuiet_id c [] noSpend_nil), streamAct_refl c⟩
    | appClose =>
        exact ⟨.inl (spaceQuiet_id c [] noSpend_nil), streamAct_refl c⟩
    | closeReceived => exact ⟨.inl (spaceQuiet_phase c _), streamAct_phase c _⟩
  | handshaking =>
    cases i with
    | start => exact ⟨.inl (spaceQuiet_id c [] noSpend_nil), streamAct_refl c⟩
    | pktReceived sp pn =>
        exact ⟨.inl (spaceQuiet_id c [] noSpend_nil), streamAct_refl c⟩
    | ackReceived sp l =>
        exact ⟨.inr (.inl ⟨sp, l, ackIn_onAck c sp l⟩), streamAct_onAck c sp l⟩
    | sendReady sp =>
        exact ⟨.inr (.inr ⟨sp, spendsIn_sendPkt c sp⟩), streamAct_bump c sp⟩
    | handshakeDone =>
        exact ⟨.inl (spaceQuiet_phase c _), streamAct_phase c _⟩
    | streamOpened =>
        exact ⟨.inl (spaceQuiet_id c [] noSpend_nil), streamAct_refl c⟩
    | streamClosed =>
        exact ⟨.inl (spaceQuiet_id c [] noSpend_nil), streamAct_refl c⟩
    | appClose =>
        exact ⟨.inr (.inr ⟨.handshake, spendsIn_closeIn c .handshake⟩),
          streamAct_bumpPhase c .handshake .closing⟩
    | closeReceived => exact ⟨.inl (spaceQuiet_phase c _), streamAct_phase c _⟩
  | established =>
    cases i with
    | start => exact ⟨.inl (spaceQuiet_id c [] noSpend_nil), streamAct_refl c⟩
    | pktReceived sp pn =>
      cases sp with
      | initial => exact ⟨.inl (spaceQuiet_id c [] noSpend_nil), streamAct_refl c⟩
      | handshake =>
          exact ⟨.inl (spaceQuiet_id c [] noSpend_nil), streamAct_refl c⟩
      | appData =>
          exact ⟨.inl (spaceQuiet_id c _ (noSpend_deliver pn)), streamAct_refl c⟩
    | ackReceived sp l =>
        exact ⟨.inr (.inl ⟨sp, l, ackIn_onAck c sp l⟩), streamAct_onAck c sp l⟩
    | sendReady sp =>
        exact ⟨.inr (.inr ⟨sp, spendsIn_sendPkt c sp⟩), streamAct_bump c sp⟩
    | handshakeDone =>
        exact ⟨.inl (spaceQuiet_id c [] noSpend_nil), streamAct_refl c⟩
    | streamOpened =>
      by_cases hlt : c.streamsOpened < c.maxStreams
      · rw [if_pos hlt]
        exact ⟨.inl (spaceQuiet_open c), rfl, .inr (.inl ⟨hlt, rfl, rfl⟩)⟩
      · rw [if_neg hlt]
        exact ⟨.inr (.inr ⟨.appData, spendsIn_closeIn c .appData⟩),
          streamAct_bumpPhase c .appData .closing⟩
    | streamClosed =>
      by_cases hlt : c.streamsClosed < c.streamsOpened
      · rw [if_pos hlt]
        exact ⟨.inl (spaceQuiet_close c), rfl, .inr (.inr ⟨hlt, rfl, rfl⟩)⟩
      · rw [if_neg hlt]
        exact ⟨.inl (spaceQuiet_id c [] noSpend_nil), streamAct_refl c⟩
    | appClose =>
        exact ⟨.inr (.inr ⟨.appData, spendsIn_closeIn c .appData⟩),
          streamAct_bumpPhase c .appData .closing⟩
    | closeReceived => exact ⟨.inl (spaceQuiet_phase c _), streamAct_phase c _⟩
  | closing =>
    cases i with
    | start => exact ⟨.inl (spaceQuiet_id c [] noSpend_nil), streamAct_refl c⟩
    | pktReceived sp pn =>
        exact ⟨.inr (.inr ⟨sp, spendsIn_replyClose c sp⟩), streamAct_bump c sp⟩
    | ackReceived sp l =>
        exact ⟨.inl (spaceQuiet_id c [] noSpend_nil), streamAct_refl c⟩
    | sendReady sp =>
        exact ⟨.inl (spaceQuiet_id c [] noSpend_nil), streamAct_refl c⟩
    | handshakeDone =>
        exact ⟨.inl (spaceQuiet_id c [] noSpend_nil), streamAct_refl c⟩
    | streamOpened =>
        exact ⟨.inl (spaceQuiet_id c [] noSpend_nil), streamAct_refl c⟩
    | streamClosed =>
        exact ⟨.inl (spaceQuiet_id c [] noSpend_nil), streamAct_refl c⟩
    | appClose =>
        exact ⟨.inl (spaceQuiet_id c [] noSpend_nil), streamAct_refl c⟩
    | closeReceived => exact ⟨.inl (spaceQuiet_phase c _), streamAct_phase c _⟩

/-! ## Totality and determinism (by construction; for the record) -/

/-- The relational graph of `step`. -/
def Steps (c : Conn) (i : Input) (c' : Conn) (os : List Output) : Prop :=
  step c i = (c', os)

theorem step_total (c : Conn) (i : Input) : ∃ c' os, Steps c i c' os :=
  ⟨(step c i).1, (step c i).2, rfl⟩

theorem step_deterministic {c : Conn} {i : Input} {c₁ c₂ : Conn}
    {os₁ os₂ : List Output} (h₁ : Steps c i c₁ os₁) (h₂ : Steps c i c₂ os₂) :
    c₁ = c₂ ∧ os₁ = os₂ := by
  unfold Steps at h₁ h₂
  rw [h₁] at h₂
  exact ⟨congrArg Prod.fst h₂, congrArg Prod.snd h₂⟩

/-! ## Draining is absorbing and silent -/

theorem draining_absorbing {c : Conn} (h : c.phase = .draining) (i : Input) :
    step c i = (c, []) := by
  unfold step
  rw [h]

theorem run_draining {c : Conn} (h : c.phase = .draining) (is : List Input) :
    run c is = (c, []) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      show ((run (step c i).1 is).1, (step c i).2 ++ (run (step c i).1 is).2)
        = (c, [])
      rw [draining_absorbing h i]
      simp [ih]

/-! ## No app-data delivery before established -/

theorem no_appdata_before_established {c : Conn} {i : Input} {pn : Nat}
    (h : Output.deliverApp pn ∈ (step c i).2) : c.phase = .established := by
  cases hp : c.phase with
  | established => rfl
  | idle =>
      unfold step at h; rw [hp] at h
      cases i <;> simp at h
  | handshaking =>
      unfold step at h; rw [hp] at h
      cases i <;>
        simp [Conn.sendPkt, Conn.closeIn, Conn.onAck] at h
  | closing =>
      unfold step at h; rw [hp] at h
      cases i <;> simp [Conn.replyClose] at h
  | draining =>
      unfold step at h; rw [hp] at h
      simp at h

/-! ## Largest-acked monotonicity (per space) -/

/-- Order on the largest-acked tracker: `none` below everything, `some`
ordered by `≤`. -/
def ackLe : Option Nat → Option Nat → Prop
  | none, _ => True
  | some _, none => False
  | some a, some b => a ≤ b

theorem ackLe_refl (o : Option Nat) : ackLe o o := by
  cases o <;> simp [ackLe]

theorem ackLe_trans {o₁ o₂ o₃ : Option Nat}
    (h₁ : ackLe o₁ o₂) (h₂ : ackLe o₂ o₃) : ackLe o₁ o₃ := by
  cases o₁ with
  | none => trivial
  | some a =>
    cases o₂ with
    | none => exact h₁.elim
    | some b =>
      cases o₃ with
      | none => exact h₂.elim
      | some d => exact Nat.le_trans h₁ h₂

theorem SpaceSt.onAck_mono (s : SpaceSt) (l : Nat) :
    ackLe s.largestAcked (s.onAck l).largestAcked := by
  unfold SpaceSt.onAck
  split
  · cases hla : s.largestAcked with
    | none => simp [hla, ackLe]
    | some a => simp [hla, ackLe, Nat.le_max_left]
  · exact ackLe_refl _

theorem step_largestAcked_mono (c : Conn) (i : Input) (sp : PnSpace) :
    ackLe (c.space sp).largestAcked ((step c i).1.space sp).largestAcked := by
  obtain ⟨hspace, -⟩ := step_classify c i
  rcases hspace with ⟨hs, -⟩ | ⟨sp', l, hs, -⟩ | ⟨sp', -, hs⟩
  · rw [hs sp]; exact ackLe_refl _
  · rw [hs sp]
    by_cases h : sp' = sp
    · rw [if_pos h]; subst h; exact SpaceSt.onAck_mono _ _
    · rw [if_neg h]; exact ackLe_refl _
  · rw [hs sp]
    by_cases h : sp' = sp
    · rw [if_pos h]; subst h; exact ackLe_refl _
    · rw [if_neg h]; exact ackLe_refl _

theorem run_largestAcked_mono (c : Conn) (is : List Input) (sp : PnSpace) :
    ackLe (c.space sp).largestAcked ((run c is).1.space sp).largestAcked := by
  induction is generalizing c with
  | nil => exact ackLe_refl _
  | cons i is ih =>
      exact ackLe_trans (step_largestAcked_mono c i sp) (ih (step c i).1)

/-! ## Well-formedness: acked ⇒ sent, and the stream-count sandwich -/

theorem SpaceSt.onAck_wf {s : SpaceSt} (h : s.Wf) (l : Nat) :
    (s.onAck l).Wf := by
  unfold SpaceSt.onAck
  split
  next hl =>
    cases hla : s.largestAcked with
    | none =>
        intro a ha
        simp only [hla] at ha
        cases ha
        exact hl
    | some a₀ =>
        intro a ha
        simp only [hla] at ha
        cases ha
        exact Nat.max_lt.mpr ⟨h a₀ hla, hl⟩
  next => exact h

theorem SpaceSt.wf_bump {s : SpaceSt} (h : s.Wf) :
    SpaceSt.Wf { s with nextPn := s.nextPn + 1 } :=
  fun a ha => Nat.lt_succ_of_lt (h a ha)

theorem step_wf {c : Conn} (h : c.Wf) (i : Input) : ((step c i).1).Wf := by
  obtain ⟨hsp, hco, hom⟩ := h
  obtain ⟨hspace, hmax, hstr⟩ := step_classify c i
  refine ⟨fun sp => ?_, ?_, ?_⟩
  · rcases hspace with ⟨hs, -⟩ | ⟨sp', l, hs, -⟩ | ⟨sp', -, hs⟩
    · rw [hs sp]; exact hsp sp
    · rw [hs sp]
      by_cases he : sp' = sp
      · rw [if_pos he]; subst he; exact SpaceSt.onAck_wf (hsp sp') l
      · rw [if_neg he]; exact hsp sp
    · rw [hs sp]
      by_cases he : sp' = sp
      · rw [if_pos he]; subst he; exact SpaceSt.wf_bump (hsp sp')
      · rw [if_neg he]; exact hsp sp
  · rcases hstr with ⟨ho, hc⟩ | ⟨-, ho, hc⟩ | ⟨hg, hc, ho⟩ <;> omega
  · rw [hmax]
    rcases hstr with ⟨ho, -⟩ | ⟨hg, ho, -⟩ | ⟨-, -, ho⟩ <;> omega

theorem run_wf {c : Conn} (h : c.Wf) (is : List Input) : ((run c is).1).Wf := by
  induction is generalizing c with
  | nil => exact h
  | cons i is ih => exact ih (step_wf h i)

theorem init_wf (m : Nat) : (Conn.init m).Wf := by
  refine ⟨fun sp => ?_, Nat.le_refl 0, Nat.zero_le m⟩
  cases sp <;> exact fun a ha => Option.noConfusion ha

/-! ## Monotone packet numbers per space -/

theorem step_nextPn_mono (c : Conn) (i : Input) (sp : PnSpace) :
    (c.space sp).nextPn ≤ ((step c i).1.space sp).nextPn := by
  obtain ⟨hspace, -⟩ := step_classify c i
  rcases hspace with ⟨hs, -⟩ | ⟨sp', l, hs, -⟩ | ⟨sp', -, hs⟩
  · rw [hs sp]; exact Nat.le_refl _
  · rw [hs sp]
    by_cases h : sp' = sp
    · rw [if_pos h]; subst h; rw [onAck_nextPn]; exact Nat.le_refl _
    · rw [if_neg h]; exact Nat.le_refl _
  · rw [hs sp]
    by_cases h : sp' = sp
    · rw [if_pos h]; subst h; exact Nat.le_succ _
    · rw [if_neg h]; exact Nat.le_refl _

theorem run_nextPn_mono (c : Conn) (is : List Input) (sp : PnSpace) :
    (c.space sp).nextPn ≤ ((run c is).1.space sp).nextPn := by
  induction is generalizing c with
  | nil => exact Nat.le_refl _
  | cons i is ih =>
      exact Nat.le_trans (step_nextPn_mono c i sp) (ih (step c i).1)

/-- Shape of one step's spend in space `sp`: either nothing (and the
counter does not decrease), or exactly the current counter value (and the
counter advances past it). -/
theorem step_emitted_shape (c : Conn) (i : Input) (sp : PnSpace) :
    (emittedPns sp (step c i).2 = [] ∧
       (c.space sp).nextPn ≤ ((step c i).1.space sp).nextPn) ∨
    (emittedPns sp (step c i).2 = [(c.space sp).nextPn] ∧
       ((step c i).1.space sp).nextPn = (c.space sp).nextPn + 1) := by
  have hm := step_nextPn_mono c i sp
  obtain ⟨hspace, -⟩ := step_classify c i
  rcases hspace with ⟨-, hns⟩ | ⟨sp', l, -, hns⟩ | ⟨sp', hout, hs⟩
  · exact .inl ⟨hns sp, hm⟩
  · exact .inl ⟨hns sp, hm⟩
  · by_cases h : sp' = sp
    · subst h
      refine .inr ⟨?_, ?_⟩
      · rw [hout sp', if_pos rfl]
      · rw [hs sp', if_pos rfl]
    · exact .inl ⟨by rw [hout sp, if_neg h], hm⟩

/-- **Monotone packet numbers per space**: along any run, the packet
numbers spent on the wire in space `sp` strictly increase — a packet
number is never reused (RFC 9000 §12.3). -/
theorem run_emitted_pairwise (c : Conn) (is : List Input) (sp : PnSpace) :
    (emittedPns sp (run c is).2).Pairwise (· < ·) ∧
    ∀ pn ∈ emittedPns sp (run c is).2,
      (c.space sp).nextPn ≤ pn ∧ pn < ((run c is).1.space sp).nextPn := by
  induction is generalizing c with
  | nil =>
      exact ⟨List.Pairwise.nil, fun pn hpn => by simp [run, emittedPns] at hpn⟩
  | cons i is ih =>
      obtain ⟨ihp, ihb⟩ := ih (step c i).1
      have hrm := run_nextPn_mono (step c i).1 is sp
      have hsplit : emittedPns sp (run c (i :: is)).2
          = emittedPns sp (step c i).2
            ++ emittedPns sp (run (step c i).1 is).2 :=
        emittedPns_append sp _ _
      have h1 : (run c (i :: is)).1 = (run (step c i).1 is).1 := rfl
      rw [hsplit, h1]
      rcases step_emitted_shape c i sp with ⟨he, hle⟩ | ⟨he, hnext⟩
      · rw [he, List.nil_append]
        exact ⟨ihp, fun pn hpn =>
          ⟨Nat.le_trans hle (ihb pn hpn).1, (ihb pn hpn).2⟩⟩
      · rw [he, List.singleton_append]
        constructor
        · rw [List.pairwise_cons]
          refine ⟨fun pn hpn => ?_, ihp⟩
          have := (ihb pn hpn).1
          omega
        · intro pn hpn
          rcases List.mem_cons.mp hpn with hh | hh
          · subst hh
            refine ⟨Nat.le_refl _, ?_⟩
            omega
          · have hb := ihb pn hh
            exact ⟨by omega, hb.2⟩

end Quic
