import Proto.Step

/-!
# Connection state machine — theorems

All theorems quantify over every `Config`, i.e. over every behavior of the
abstract codecs.

1. `step_total` — the step is total (every state/input pair has a unique
   successor; immediate from the functional presentation).
2. `step_deterministic` — the step relation is functional.
3. `no_output_after_close` / `closed_absorbing` — the closed state is
   silent and absorbing.
4. `h1Loop_suffix`, `h1Loop_no_progress_no_drop`,
   `residual_bytes_plainH1`, `residual_suffix_plainH1` — the keep-alive /
   pipelining residual-bytes invariant: the receive accumulation is only
   ever shortened from the front by parse consumption, and if the step
   neither dispatches a request nor closes, every byte (old accumulation
   plus new data) is retained.
5. `send_block_monotone` — once send-blocked, the machine emits no
   peer-socket sends and stays blocked, for every input other than
   `writeReady`.
6. `step_preserves_wf` — the send gate's structural invariant (no parked
   sends unless blocked) is preserved by every step.
-/

namespace Proto

/-! ## Totality and determinism -/

/-- Every state/input pair steps. -/
theorem step_total (cfg : Config) (s : State) (i : Input) :
    ∃ s' outs, Steps cfg s i s' outs :=
  ⟨(step cfg s i).1, (step cfg s i).2, rfl⟩

/-- The step relation is functional. -/
theorem step_deterministic (cfg : Config) (s : State) (i : Input)
    {s₁ s₂ : State} {o₁ o₂ : List Output}
    (h₁ : Steps cfg s i s₁ o₁) (h₂ : Steps cfg s i s₂ o₂) :
    s₁ = s₂ ∧ o₁ = o₂ := by
  have h := h₁.symm.trans h₂
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-! ## The closed state is silent and absorbing -/

/-- A closed connection produces no outputs and stays closed, on every
input. -/
theorem no_output_after_close (cfg : Config) (i : Input) :
    step cfg .closed i = (.closed, []) := rfl

/-- Corollary, split for direct use. -/
theorem closed_absorbing (cfg : Config) (i : Input) :
    (step cfg .closed i).1 = .closed ∧ (step cfg .closed i).2 = [] :=
  ⟨rfl, rfl⟩

/-! ## Send-block gate lemmas -/

theorem gate_false (outs : List Output) : gate false outs = (outs, []) := by
  simp [gate]

theorem gate_true_no_send (outs : List Output) (b : Bytes) :
    Output.send b ∉ (gate true outs).1 := by
  simp [gate, List.mem_filter, Output.isSend]

/-- Non-send outputs pass the gate unchanged (membership, both ways). -/
theorem mem_gate_of_not_send {o : Output} (ho : o.isSend = false)
    (blocked : Bool) (outs : List Output) :
    o ∈ (gate blocked outs).1 ↔ o ∈ outs := by
  cases blocked with
  | false => simp [gate]
  | true => simp [gate, List.mem_filter, ho]

theorem close_mem_gate (blocked : Bool) (outs : List Output) :
    Output.close ∈ (gate blocked outs).1 ↔ Output.close ∈ outs :=
  mem_gate_of_not_send rfl blocked outs

theorem dispatch_mem_gate (r : Request) (blocked : Bool)
    (outs : List Output) :
    Output.dispatch r ∈ (gate blocked outs).1 ↔ Output.dispatch r ∈ outs :=
  mem_gate_of_not_send rfl blocked outs

/-! ## `finish` plumbing lemmas -/

/-- A closing effect always emits an explicit `close`. -/
theorem finish_close_mem (c : Conn) (e : Eff) (he : e.closeNow = true) :
    Output.close ∈ (finish c e).2 := by
  simp [finish, he]

/-- A closing effect yields the closed state. -/
theorem finish_close_state (c : Conn) (e : Eff) (he : e.closeNow = true) :
    (finish c e).1 = .closed := by
  simp [finish, he]

/-- Shape of a non-closing `finish`. -/
theorem finish_not_close (c : Conn) (e : Eff) (he : e.closeNow = false) :
    (finish c e).1 = .active { c with
        proto := e.proto,
        pendingSend := c.pendingSend ++ (gate c.sendBlocked e.outs).2,
        timers := e.timers.getD c.timers }
    ∧ (finish c e).2 = (gate c.sendBlocked e.outs).1 := by
  simp [finish, he]

/-! ## The keep-alive / pipelining residual-bytes invariant -/

/-- The loop only ever shortens the accumulation from the front: the
residual is a drop of the input buffer. Bytes are never invented,
reordered, or removed from anywhere but the consumed prefix. -/
theorem h1Loop_suffix (cfg : Config) (fuel : Nat) (buf : Bytes) :
    ∃ k, (h1Loop cfg fuel buf).residual = buf.drop k := by
  induction fuel generalizing buf with
  | zero => exact ⟨0, by simp [h1Loop]⟩
  | succ n ih =>
    unfold h1Loop
    by_cases hb : buf.isEmpty
    · exact ⟨0, by simp [hb]⟩
    · simp only [hb, Bool.false_eq_true, if_false]
      cases hp : cfg.h1Parse buf with
      | incomplete => exact ⟨0, by simp⟩
      | error => exact ⟨0, by simp⟩
      | reject m resp => exact ⟨m, rfl⟩
      | request m req ka =>
        by_cases hka : ka
        · obtain ⟨k, hk⟩ := ih (buf.drop m)
          refine ⟨m + k, ?_⟩
          simp [hka, hk, List.drop_drop]
        · exact ⟨m, by simp [hka]⟩

/-- If the loop neither closes nor dispatches, it consumed nothing — the
accumulation survives intact. (Unconsumed input is never dropped except
through an explicit close.) -/
theorem h1Loop_no_progress_no_drop (cfg : Config) (fuel : Nat) (buf : Bytes)
    (hcl : (h1Loop cfg fuel buf).closing = false)
    (hnd : ∀ r, Output.dispatch r ∉ (h1Loop cfg fuel buf).outs) :
    (h1Loop cfg fuel buf).residual = buf := by
  cases fuel with
  | zero => simp [h1Loop]
  | succ n =>
    unfold h1Loop at hcl hnd ⊢
    by_cases hb : buf.isEmpty
    · simp [hb]
    · simp only [hb, Bool.false_eq_true, if_false] at hcl hnd ⊢
      cases hp : cfg.h1Parse buf with
      | incomplete => simp
      | error => simp [hp] at hcl
      | reject m resp => simp [hp] at hcl
      | request m req ka =>
        by_cases hka : ka
        · exact absurd (by simp [hp, hka] : Output.dispatch req ∈ _) (hnd req)
        · simp [hp, hka] at hcl

/-- `runH1` on an oversized accumulation closes. -/
theorem runH1_closeNow_of_over (cfg : Config) (frame : Bytes → ProtoState)
    (buf : Bytes) (pre : List Output)
    (h : buf.length > cfg.maxHeaderBytes) :
    (runH1 cfg frame buf pre).closeNow = true := by
  unfold runH1
  rw [if_pos h]

/-- `runH1` within the header cap is exactly the pipelining loop. -/
theorem runH1_eq_of_not_over (cfg : Config) (frame : Bytes → ProtoState)
    (buf : Bytes) (pre : List Output)
    (h : ¬ buf.length > cfg.maxHeaderBytes) :
    runH1 cfg frame buf pre =
      { proto := frame (h1Loop cfg (buf.length + 1) buf).residual,
        outs := pre ++ (h1Loop cfg (buf.length + 1) buf).outs,
        closeNow := (h1Loop cfg (buf.length + 1) buf).closing } := by
  unfold runH1
  rw [if_neg h]

/-- Residual-bytes invariant, top level (HTTP/1.1 state): if a step on
received bytes neither emits `close` nor dispatches a request, the entire
accumulation — prior residual plus the new data — is retained verbatim in
the successor state. -/
theorem residual_bytes_plainH1 (cfg : Config) (c : Conn) (buf data : Bytes)
    (hp : c.proto = .plainH1 buf)
    (hclose : Output.close ∉ (step cfg (.active c) (.bytesReceived data)).2)
    (hdisp : ∀ r,
      Output.dispatch r ∉ (step cfg (.active c) (.bytesReceived data)).2) :
    ∃ c', (step cfg (.active c) (.bytesReceived data)).1 = .active c'
      ∧ c'.proto = .plainH1 (buf ++ data) := by
  have hstep : step cfg (.active c) (.bytesReceived data)
      = finish c (runH1 cfg .plainH1 (buf ++ data) []) := by
    simp [step, hp, onBytes]
  by_cases hover : (buf ++ data).length > cfg.maxHeaderBytes
  · exact absurd
      (hstep ▸ finish_close_mem c _ (runH1_closeNow_of_over cfg _ _ _ hover))
      hclose
  · rw [runH1_eq_of_not_over cfg _ _ _ hover] at hstep
    rw [hstep] at hclose hdisp ⊢
    cases hcl : (h1Loop cfg ((buf ++ data).length + 1) (buf ++ data)).closing with
    | true =>
      rw [hcl] at hclose
      exact absurd (finish_close_mem c _ rfl) hclose
    | false =>
      rw [hcl] at hclose hdisp
      obtain ⟨hs, ho⟩ := finish_not_close c
        { proto := ProtoState.plainH1
            (h1Loop cfg ((buf ++ data).length + 1) (buf ++ data)).residual,
          outs := []
            ++ (h1Loop cfg ((buf ++ data).length + 1) (buf ++ data)).outs,
          closeNow := false }
        rfl
      refine ⟨_, hs, ?_⟩
      have hnd : ∀ rq, Output.dispatch rq
          ∉ (h1Loop cfg ((buf ++ data).length + 1) (buf ++ data)).outs := by
        intro rq hmem
        apply hdisp rq
        rw [ho]
        exact (dispatch_mem_gate rq c.sendBlocked _).mpr (by simpa using hmem)
      show ProtoState.plainH1
          (h1Loop cfg ((buf ++ data).length + 1) (buf ++ data)).residual
        = ProtoState.plainH1 (buf ++ data)
      rw [h1Loop_no_progress_no_drop cfg ((buf ++ data).length + 1)
        (buf ++ data) hcl hnd]

/-- Residual-bytes invariant, suffix form: on received bytes the HTTP/1.1
state either closes or retains a suffix of the total accumulation obtained
by dropping exactly the consumed prefix. -/
theorem residual_suffix_plainH1 (cfg : Config) (c : Conn) (buf data : Bytes)
    (hp : c.proto = .plainH1 buf) :
    (step cfg (.active c) (.bytesReceived data)).1 = .closed
    ∨ ∃ c' k, (step cfg (.active c) (.bytesReceived data)).1 = .active c'
        ∧ c'.proto = .plainH1 ((buf ++ data).drop k) := by
  have hstep : step cfg (.active c) (.bytesReceived data)
      = finish c (runH1 cfg .plainH1 (buf ++ data) []) := by
    simp [step, hp, onBytes]
  by_cases hover : (buf ++ data).length > cfg.maxHeaderBytes
  · exact .inl
      (hstep ▸ finish_close_state c _ (runH1_closeNow_of_over cfg _ _ _ hover))
  · rw [runH1_eq_of_not_over cfg _ _ _ hover] at hstep
    rw [hstep]
    cases hcl : (h1Loop cfg ((buf ++ data).length + 1) (buf ++ data)).closing with
    | true => exact .inl (finish_close_state c _ rfl)
    | false =>
      obtain ⟨hs, _⟩ := finish_not_close c
        { proto := ProtoState.plainH1
            (h1Loop cfg ((buf ++ data).length + 1) (buf ++ data)).residual,
          outs := []
            ++ (h1Loop cfg ((buf ++ data).length + 1) (buf ++ data)).outs,
          closeNow := false }
        rfl
      obtain ⟨k, hk⟩ :=
        h1Loop_suffix cfg ((buf ++ data).length + 1) (buf ++ data)
      refine .inr ⟨_, k, hs, ?_⟩
      show ProtoState.plainH1
          (h1Loop cfg ((buf ++ data).length + 1) (buf ++ data)).residual
        = ProtoState.plainH1 ((buf ++ data).drop k)
      rw [hk]

/-! ## Send-block monotonicity -/

/-- While blocked, `finish` emits no peer-socket sends. -/
theorem finish_blocked_no_send (c : Conn) (e : Eff)
    (hb : c.sendBlocked = true) (b : Bytes) :
    Output.send b ∉ (finish c e).2 := by
  unfold finish
  by_cases hcl : e.closeNow
  · simp only [hcl, if_true]
    intro hmem
    rcases List.mem_append.mp hmem with h | h
    · exact gate_true_no_send e.outs b (hb ▸ h)
    · simp at h
  · simp only [hcl, if_false]
    intro hmem
    exact gate_true_no_send e.outs b (hb ▸ hmem)

/-- While blocked, `finish` never unblocks. -/
theorem finish_blocked_stays (c : Conn) (e : Eff)
    (hb : c.sendBlocked = true) (c' : Conn)
    (h : (finish c e).1 = .active c') : c'.sendBlocked = true := by
  unfold finish at h
  by_cases hcl : e.closeNow
  · simp [hcl] at h
  · simp only [hcl, if_false] at h
    cases h
    exact hb

/-- **Send-block monotonicity.** Once the send path is blocked, no input
other than `writeReady` can produce a peer-socket send, and the connection
(if still active) remains blocked. Combined with the in-order flush at
`writeReady`, no byte overtakes the parked remainder of a partial write. -/
theorem send_block_monotone (cfg : Config) (c : Conn) (i : Input)
    (hb : c.sendBlocked = true) (hi : i ≠ .writeReady) :
    (∀ b, Output.send b ∉ (step cfg (.active c) i).2)
    ∧ (∀ c', (step cfg (.active c) i).1 = .active c'
        → c'.sendBlocked = true) := by
  cases i with
  | bytesReceived data =>
    exact ⟨fun b => finish_blocked_no_send c _ hb b,
           fun c' h => finish_blocked_stays c _ hb c' h⟩
  | upstreamEvent ev =>
    exact ⟨fun b => finish_blocked_no_send c _ hb b,
           fun c' h => finish_blocked_stays c _ hb c' h⟩
  | writeReady => exact absurd rfl hi
  | writeBlocked =>
    constructor
    · intro b hmem
      simp only [step] at hmem
      by_cases ha : c.recvArmed <;> simp [ha] at hmem
    · intro c' h
      simp only [step] at h
      cases h
      rfl
  | sendComplete =>
    constructor
    · intro b hmem
      simp only [step] at hmem
      cases hcp : c.proto <;> simp [hcp] at hmem
    · intro c' h
      simp only [step] at h
      cases hcp : c.proto <;> rw [hcp] at h <;> first
        | (cases h; exact hb)
        | simp at h
  | timerFired slot =>
    constructor
    · intro b hmem
      simp only [step] at hmem
      by_cases ht : c.timers.contains slot <;> simp [ht] at hmem
    · intro c' h
      simp only [step] at h
      by_cases ht : c.timers.contains slot <;> simp [ht] at h
      cases h
      exact hb
  | closeRequested =>
    exact ⟨fun b hmem => by simp [step] at hmem,
           fun c' h => by simp [step] at h⟩
  | peerClosed =>
    exact ⟨fun b hmem => by simp [step] at hmem,
           fun c' h => by simp [step] at h⟩

/-! ## The gate's structural invariant -/

/-- Well-formedness: an unblocked connection holds no parked sends. -/
def Conn.WF (c : Conn) : Prop := c.sendBlocked = false → c.pendingSend = []

/-- Well-formedness lifted to the lifecycle state. -/
def State.WF : State → Prop
  | .closed => True
  | .active c => c.WF

theorem finish_preserves_wf (c : Conn) (e : Eff) (h : c.WF) :
    (finish c e).1.WF := by
  unfold finish
  by_cases hcl : e.closeNow
  · simp [hcl, State.WF]
  · simp only [hcl, if_false]
    intro hnb
    cases hsb : c.sendBlocked
    · simp only [hsb] at hnb ⊢
      simp [gate_false, h hsb]
    · simp [hsb] at hnb

/-- Every step preserves well-formedness. -/
theorem step_preserves_wf (cfg : Config) (s : State) (i : Input)
    (h : s.WF) : (step cfg s i).1.WF := by
  cases s with
  | closed => exact trivial
  | active c =>
    cases i with
    | bytesReceived data => exact finish_preserves_wf c _ h
    | upstreamEvent ev => exact finish_preserves_wf c _ h
    | writeReady => intro _; rfl
    | writeBlocked => intro hnb; cases hnb
    | sendComplete =>
      simp only [step]
      cases c.proto <;> first | exact trivial | exact h
    | timerFired slot =>
      simp only [step]
      by_cases ht : c.timers.contains slot <;> simp [ht, State.WF]
      exact h
    | closeRequested => exact trivial
    | peerClosed => exact trivial

/-- The initial connection states are well-formed. -/
theorem mkPlain_wf : Conn.mkPlain.WF := fun _ => rfl
theorem mkTls_wf (tc : TlsConn) : (Conn.mkTls tc).WF := fun _ => rfl
theorem mkPrefixed_wf (t : Option TlsConn) : (Conn.mkPrefixed t).WF :=
  fun _ => rfl
theorem mkSocks_wf : Conn.mkSocks.WF := fun _ => rfl

end Proto
