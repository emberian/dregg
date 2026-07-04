import Tls.Step

/-!
# TLS record/handshake machine — theorems

All theorems quantify over every `Config`, i.e. over every behavior of
the crypto effects behind the axiom boundary.

1. `step_total` / `step_deterministic` — the step is a total function
   and the induced relation is functional.
2. **No plaintext after close.** `close_absorbing` +
   `no_plain_in_close_step` + the trace form `no_plain_after_close`:
   once the machine is closing or closed, no input sequence can ever
   produce a plaintext-carrying output. The named edge lemmas make the
   offload cases explicit: `half_configured_teardown_*` (a key-install
   failure emits exactly `close` — the parked plaintext is dropped),
   `attach_no_plain` / `installingTx_no_plain` /
   `installingRx_no_plain` (the offload window emits plaintext only on
   the edge that completes configuration), and `offloaded_close_*`
   (closing an offloaded connection emits exactly `close`).
3. **Secrets-consumption linearity.** `consume_at_most_once` (the ghost
   consumed-set never exceeds one element) and `no_use_after_consume`
   (+ trace form): once a userspace connection's secrets are extracted,
   no record-layer effect is ever applied to it again. The supporting
   facts are `uses_live` / `consumes_live` (every effect application in
   a step is to the phase's live connection) and the reachability
   invariant `LinInv`.
4. **Early data needs the flag.** `early_data_needs_flag`: a
   `deliverEarly` output can only occur when `cfg.earlyDataAccepted`
   is set — with the flag off, drained 0.5-RTT plaintext is dropped,
   and it never leaks through any other output constructor.
-/

namespace Tls

/-! ## Membership shapes of the gated-output helpers -/

theorem mem_sendIf {o : Output} {b : Bytes} (h : o ∈ sendIf b) :
    o = .send b := by
  unfold sendIf at h
  split at h <;> simp_all

theorem mem_deliverIf {o : Output} {b : Bytes} (h : o ∈ deliverIf b) :
    o = .deliverPlain b := by
  unfold deliverIf at h
  split at h <;> simp_all

theorem mem_sendPlainIf {o : Output} {b : Bytes}
    (h : o ∈ sendPlainIf b) : o = .sendPlain b := by
  unfold sendPlainIf at h
  split at h <;> simp_all

/-- Anything coming out of `earlyIf` is early data **and** carries a
proof that the acceptance flag is set. -/
theorem mem_earlyIf {o : Output} {cfg : Config} {b : Bytes}
    (h : o ∈ earlyIf cfg b) :
    cfg.earlyDataAccepted = true ∧ o = .deliverEarly b := by
  unfold earlyIf at h
  split at h <;> simp_all

@[simp] theorem not_early_mem_sendIf {d b : Bytes} :
    Output.deliverEarly d ∉ sendIf b :=
  fun h => Output.noConfusion (mem_sendIf h)

@[simp] theorem not_early_mem_deliverIf {d b : Bytes} :
    Output.deliverEarly d ∉ deliverIf b :=
  fun h => Output.noConfusion (mem_deliverIf h)

@[simp] theorem not_early_mem_sendPlainIf {d b : Bytes} :
    Output.deliverEarly d ∉ sendPlainIf b :=
  fun h => Output.noConfusion (mem_sendPlainIf h)

theorem sendIf_no_plain {b : Bytes} :
    ∀ o ∈ sendIf b, o.carriesPlain = false := by
  intro o h
  rw [mem_sendIf h]
  rfl

/-! ## Totality and determinism -/

/-- Every state/input pair steps. -/
theorem step_total (cfg : Config) (s : St) (i : Input) :
    ∃ s' e, Steps cfg s i s' e :=
  ⟨(step cfg s i).1, (step cfg s i).2, rfl⟩

/-- The step relation is functional. -/
theorem step_deterministic (cfg : Config) (s : St) (i : Input)
    {s₁ s₂ : St} {e₁ e₂ : Eff}
    (h₁ : Steps cfg s i s₁ e₁) (h₂ : Steps cfg s i s₂ e₂) :
    s₁ = s₂ ∧ e₁ = e₂ := by
  have h := h₁.symm.trans h₂
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-! ## No plaintext after close -/

/-- The dying region: closing or closed. -/
def Phase.closingOrClosed : Phase → Bool
  | .closing => true
  | .closed => true
  | _ => false

/-- A closed connection is silent and stays closed, on every input. -/
theorem no_output_after_closed (cfg : Config) (s : St)
    (h : s.phase = .closed) (i : Input) :
    (step cfg s i).1.phase = .closed ∧ (step cfg s i).2 = {} := by
  rcases s with ⟨p, g⟩
  cases h
  cases i <;> exact ⟨rfl, rfl⟩

/-- The dying region is absorbing. -/
theorem close_absorbing (cfg : Config) (s : St) (i : Input)
    (h : s.phase.closingOrClosed = true) :
    (step cfg s i).1.phase.closingOrClosed = true := by
  rcases s with ⟨p, g⟩
  cases p <;> simp [Phase.closingOrClosed] at h <;> cases i <;>
    simp [step, stepPhase, Phase.closingOrClosed]

/-- No step out of the dying region emits a plaintext-carrying
output. -/
theorem no_plain_in_close_step (cfg : Config) (s : St) (i : Input)
    (h : s.phase.closingOrClosed = true) :
    ∀ o ∈ (step cfg s i).2.out, o.carriesPlain = false := by
  rcases s with ⟨p, g⟩
  cases p <;> simp [Phase.closingOrClosed] at h <;> cases i <;>
    simp [step, stepPhase, Output.carriesPlain]

/-- **No plaintext after close**, trace form: from any closing or
closed state — however it was reached, including through the offloaded
and half-configured phases — no input sequence ever produces a
plaintext-carrying output again. -/
theorem no_plain_after_close (cfg : Config) (s : St)
    (h : s.phase.closingOrClosed = true) (is : List Input) :
    ∀ e ∈ (run cfg s is).2, ∀ o ∈ e.out, o.carriesPlain = false := by
  induction is generalizing s with
  | nil => simp [run]
  | cons i is ih =>
    intro e he o ho
    simp only [run, List.mem_cons] at he
    rcases he with rfl | he
    · exact no_plain_in_close_step cfg s i h o ho
    · exact ih _ (close_absorbing cfg s i h) e he o ho

/-! ## The offload window: named edge lemmas -/

/-- The half-configured teardown edge (RX pending): a key-install
failure on the half-configured socket produces exactly `close` — no
send, no plaintext, and in particular not the parked `pend` — and the
machine is closed. -/
theorem half_configured_teardown_rx (cfg : Config) (s : St)
    {alpn : Alpn} {pend : Bytes}
    (h : s.phase = .installingRx alpn pend) :
    (step cfg s .installFailed).1.phase = .closed ∧
    (step cfg s .installFailed).2.out = [.close] := by
  rcases s with ⟨p, g⟩
  cases h
  exact ⟨rfl, rfl⟩

/-- Same teardown edge from the TX-install phase (secrets are already
extracted there too). -/
theorem half_configured_teardown_tx (cfg : Config) (s : St)
    {alpn : Alpn} {rx : KeyMat} {pend : Bytes}
    (h : s.phase = .installingTx alpn rx pend) :
    (step cfg s .installFailed).1.phase = .closed ∧
    (step cfg s .installFailed).2.out = [.close] := by
  rcases s with ⟨p, g⟩
  cases h
  exact ⟨rfl, rfl⟩

/-- A hard ULP-attach error also tears down immediately (the
connection is dropped unconsumed; parked plaintext is discarded). -/
theorem attach_teardown (cfg : Config) (s : St)
    {alpn : Alpn} {rc : RecConn} {buf pend : Bytes}
    (h : s.phase = .offloadAttach alpn rc buf pend) :
    (step cfg s .installFailed).1.phase = .closed ∧
    (step cfg s .installFailed).2.out = [.close] := by
  rcases s with ⟨p, g⟩
  cases h
  exact ⟨rfl, rfl⟩

/-- The attach-pending phase emits no plaintext on any input (the
fallback flush goes through the seal path and comes out as a wire
`send`). -/
theorem attach_no_plain (cfg : Config) (s : St) (i : Input)
    {alpn : Alpn} {rc : RecConn} {buf pend : Bytes}
    (h : s.phase = .offloadAttach alpn rc buf pend) :
    ∀ o ∈ (step cfg s i).2.out, o.carriesPlain = false := by
  rcases s with ⟨p, g⟩
  cases h
  cases i <;>
    simp [step, stepPhase, Output.carriesPlain] <;>
    exact fun o ho => sendIf_no_plain o ho

/-- The TX-install phase emits no plaintext on any input. -/
theorem installingTx_no_plain (cfg : Config) (s : St) (i : Input)
    {alpn : Alpn} {rx : KeyMat} {pend : Bytes}
    (h : s.phase = .installingTx alpn rx pend) :
    ∀ o ∈ (step cfg s i).2.out, o.carriesPlain = false := by
  rcases s with ⟨p, g⟩
  cases h
  cases i <;> simp [step, stepPhase, Output.carriesPlain]

/-- The half-configured phase emits plaintext **only** on the edge
that completes configuration (`installOk`); on every other input —
the teardown edge included — nothing plaintext-carrying comes out. -/
theorem installingRx_no_plain (cfg : Config) (s : St) (i : Input)
    {alpn : Alpn} {pend : Bytes}
    (h : s.phase = .installingRx alpn pend) (hi : i ≠ .installOk) :
    ∀ o ∈ (step cfg s i).2.out, o.carriesPlain = false := by
  rcases s with ⟨p, g⟩
  cases h
  cases i <;> first
    | exact absurd rfl hi
    | simp [step, stepPhase, Output.carriesPlain]

/-- Closing an offloaded connection (local request) emits exactly
`close` and is immediately closed. -/
theorem offloaded_close_local (cfg : Config) (s : St) {alpn : Alpn}
    (h : s.phase = .estabOffload alpn) :
    (step cfg s .closeRequested).1.phase = .closed ∧
    (step cfg s .closeRequested).2.out = [.close] := by
  rcases s with ⟨p, g⟩
  cases h
  exact ⟨rfl, rfl⟩

/-- Peer EOF on an offloaded connection: same. -/
theorem offloaded_close_peer (cfg : Config) (s : St) {alpn : Alpn}
    (h : s.phase = .estabOffload alpn) :
    (step cfg s .peerClosed).1.phase = .closed ∧
    (step cfg s .peerClosed).2.out = [.close] := by
  rcases s with ⟨p, g⟩
  cases h
  exact ⟨rfl, rfl⟩

/-! ## Secrets-consumption linearity -/

/-- The userspace record connection the machine may still legitimately
use, if any. -/
def Phase.live : Phase → Option RecConn
  | .estabUser _ rc _ => some rc
  | .offloadAttach _ rc _ _ => some rc
  | _ => none

/-- Phases at or past the consuming edge: no userspace connection is
held, and none can ever be held again. -/
def Phase.postWindow : Phase → Bool
  | .installingTx _ _ _ => true
  | .installingRx _ _ => true
  | .estabOffload _ => true
  | .closing => true
  | .closed => true
  | _ => false

theorem live_none_of_postWindow (p : Phase)
    (h : p.postWindow = true) : p.live = none := by
  cases p <;> simp_all [Phase.postWindow, Phase.live]

/-- Once past the window, always past the window. -/
theorem postWindow_step (cfg : Config) (s : St) (i : Input)
    (h : s.phase.postWindow = true) :
    (step cfg s i).1.phase.postWindow = true := by
  rcases s with ⟨p, g⟩
  cases p <;> simp [Phase.postWindow] at h <;> cases i <;>
    simp [step, stepPhase, Phase.postWindow]

theorem finishHs_uses {cfg : Config} {alpn : Alpn} {rc : RecConn}
    {rest snd early : Bytes} :
    (finishHs cfg alpn rc rest snd early).2.uses = [] := by
  unfold finishHs
  split <;> rfl

theorem finishHs_consumes {cfg : Config} {alpn : Alpn} {rc : RecConn}
    {rest snd early : Bytes} :
    (finishHs cfg alpn rc rest snd early).2.consumes = [] := by
  unfold finishHs
  split <;> rfl

theorem hsDrive_uses {cfg : Config} {hs : HsConn} {buf : Bytes}
    {stay : HsConn → Bytes → Phase} :
    (hsDrive cfg hs buf stay).2.uses = [] := by
  unfold hsDrive
  split <;> first | rfl | exact finishHs_uses

theorem hsDrive_consumes {cfg : Config} {hs : HsConn} {buf : Bytes}
    {stay : HsConn → Bytes → Phase} :
    (hsDrive cfg hs buf stay).2.consumes = [] := by
  unfold hsDrive
  split <;> first | rfl | exact finishHs_consumes

theorem recDrive_uses {cfg : Config} {alpn : Alpn} {rc : RecConn}
    {buf : Bytes} :
    (recDrive cfg alpn rc buf).2.uses = [rc] := by
  unfold recDrive
  split <;> rfl

theorem recDrive_consumes {cfg : Config} {alpn : Alpn} {rc : RecConn}
    {buf : Bytes} :
    (recDrive cfg alpn rc buf).2.consumes = [] := by
  unfold recDrive
  split <;> rfl

/-- Every record-layer effect application in a step is to the phase's
live connection. -/
theorem uses_live (cfg : Config) (s : St) (i : Input) :
    ∀ rc ∈ (step cfg s i).2.uses, s.phase.live = some rc := by
  rcases s with ⟨p, g⟩
  cases p <;> cases i <;>
    simp [step, stepPhase, Phase.live, hsDrive_uses, recDrive_uses]

/-- Every consumption in a step is of the phase's live connection. -/
theorem consumes_live (cfg : Config) (s : St) (i : Input) :
    ∀ rc ∈ (step cfg s i).2.consumes, s.phase.live = some rc := by
  rcases s with ⟨p, g⟩
  cases p <;> cases i <;>
    simp [step, stepPhase, Phase.live, hsDrive_consumes,
      recDrive_consumes]

/-- Past the window, steps consume nothing further. -/
theorem postWindow_no_consumes (cfg : Config) (s : St) (i : Input)
    (h : s.phase.postWindow = true) :
    (step cfg s i).2.consumes = [] := by
  rcases s with ⟨p, g⟩
  cases p <;> simp [Phase.postWindow] at h <;> cases i <;> rfl

/-- The linearity invariant: before the window closes nothing has been
consumed, and the consumed-set never exceeds one element. -/
def LinInv (s : St) : Prop :=
  (s.phase.postWindow = false → s.consumed = []) ∧
  s.consumed.length ≤ 1

theorem linInv_init (cfg : Config) : LinInv (init cfg) := by
  exact ⟨fun _ => rfl, by simp [init]⟩

theorem linInv_step (cfg : Config) (s : St) (i : Input)
    (h : LinInv s) : LinInv (step cfg s i).1 := by
  obtain ⟨h1, h2⟩ := h
  rcases s with ⟨p, g⟩
  by_cases hpw : p.postWindow = true
  · -- past the window: nothing more is consumed, the region persists
    have hnext := postWindow_step cfg ⟨p, g⟩ i hpw
    have hcs := postWindow_no_consumes cfg ⟨p, g⟩ i hpw
    refine ⟨fun hf => by simp [hf] at hnext, ?_⟩
    have hc : (step cfg ⟨p, g⟩ i).1.consumed
        = g ++ (step cfg ⟨p, g⟩ i).2.consumes := rfl
    rw [hc, hcs, List.append_nil]
    exact h2
  · -- before the window: the consumed-set is empty, and at most the
    -- single consuming edge can fire
    have hpw' : p.postWindow = false := by
      cases hb : p.postWindow
      · rfl
      · exact absurd hb hpw
    have hg : g = [] := h1 hpw'
    subst hg
    cases p <;> simp [Phase.postWindow] at hpw' <;> cases i <;>
      simp [LinInv, step, stepPhase, Phase.postWindow,
        hsDrive_consumes, recDrive_consumes]

theorem linInv_reachable (cfg : Config) {s : St}
    (h : Reachable cfg s) : LinInv s := by
  induction h with
  | init => exact linInv_init cfg
  | step _ i ih => exact linInv_step cfg _ i ih

/-- **Consumed at most once.** In every reachable state, at most one
userspace connection has ever had its secrets extracted. -/
theorem consume_at_most_once (cfg : Config) {s : St}
    (h : Reachable cfg s) : s.consumed.length ≤ 1 :=
  (linInv_reachable cfg h).2

/-- **Never used after consumption**, step form: once a connection is
in the consumed-set of a reachable state, no step out of that state
applies a record-layer effect to it. -/
theorem no_use_after_consume (cfg : Config) {s : St}
    (hr : Reachable cfg s) {rc : RecConn} (hc : rc ∈ s.consumed)
    (i : Input) : rc ∉ (step cfg s i).2.uses := by
  intro hu
  have hlive := uses_live cfg s i rc hu
  have hpw : s.phase.postWindow = true := by
    obtain ⟨h1, _⟩ := linInv_reachable cfg hr
    cases hb : s.phase.postWindow
    · rw [h1 hb] at hc
      exact absurd hc (List.not_mem_nil rc)
    · rfl
  rw [live_none_of_postWindow s.phase hpw] at hlive
  cases hlive

/-- **Never used after consumption**, trace form: from a reachable
state that has consumed `rc`, no input sequence ever uses `rc` again. -/
theorem no_use_after_consume_run (cfg : Config) {s : St}
    (hr : Reachable cfg s) {rc : RecConn} (hc : rc ∈ s.consumed)
    (is : List Input) :
    ∀ e ∈ (run cfg s is).2, rc ∉ e.uses := by
  induction is generalizing s with
  | nil => simp [run]
  | cons i is ih =>
    intro e he
    simp only [run, List.mem_cons] at he
    rcases he with rfl | he
    · exact no_use_after_consume cfg hr hc i
    · exact ih (hr.step i)
        (List.mem_append_left _ hc) e he

/-! ## Early data needs the flag -/

theorem finishHs_early_flag {cfg : Config} {alpn : Alpn}
    {rc : RecConn} {rest snd early d : Bytes}
    (h : Output.deliverEarly d
      ∈ (finishHs cfg alpn rc rest snd early).2.out) :
    cfg.earlyDataAccepted = true := by
  unfold finishHs at h
  split at h <;> simp only [List.mem_append] at h
  · rcases h with (h | h) | h
    · exact absurd h not_early_mem_sendIf
    · exact (mem_earlyIf h).1
    · simp at h
  · rcases h with h | h
    · exact absurd h not_early_mem_sendIf
    · exact (mem_earlyIf h).1

theorem hsDrive_early_flag {cfg : Config} {hs : HsConn}
    {buf : Bytes} {stay : HsConn → Bytes → Phase} {d : Bytes}
    (h : Output.deliverEarly d ∈ (hsDrive cfg hs buf stay).2.out) :
    cfg.earlyDataAccepted = true := by
  unfold hsDrive at h
  split at h
  · exact absurd h (List.not_mem_nil _)
  · rcases List.mem_append.mp h with h | h
    · exact absurd h not_early_mem_sendIf
    · exact (mem_earlyIf h).1
  · exact finishHs_early_flag h
  · simp at h

theorem recDrive_no_early {cfg : Config} {alpn : Alpn} {rc : RecConn}
    {buf d : Bytes} :
    Output.deliverEarly d ∉ (recDrive cfg alpn rc buf).2.out := by
  unfold recDrive
  split
  · exact not_early_mem_deliverIf
  · intro h
    rcases List.mem_append.mp h with h | h
    · exact absurd h not_early_mem_deliverIf
    · simp at h
  · intro h
    simp at h

/-- **Early data is delivered only under the explicit acceptance
flag.** For every configuration, state, and input: if a step emits
early plaintext, the flag is set. Contrapositively, with the flag off
no early data is ever delivered — the drained 0.5-RTT bytes are
dropped, and they cannot leak through any other output constructor
(`deliverEarly` is the only early-carrying output). -/
theorem early_data_needs_flag (cfg : Config) (s : St) (i : Input)
    (d : Bytes)
    (h : Output.deliverEarly d ∈ (step cfg s i).2.out) :
    cfg.earlyDataAccepted = true := by
  rcases s with ⟨p, g⟩
  cases p <;> cases i <;>
    first
      | exact hsDrive_early_flag h
      | exact absurd h recDrive_no_early
      | simp [step, stepPhase] at h

/-! ## Small structural remarks -/

/-- The fully offloaded phase holds no userspace TLS state. -/
theorem estabOffload_no_userspace (alpn : Alpn) :
    (Phase.estabOffload alpn).live = none := rfl

/-- The install window holds no userspace TLS state either — the
secrets exist only as kernel-destined key material. -/
theorem installing_no_userspace (alpn : Alpn) (rx : KeyMat)
    (pend : Bytes) :
    (Phase.installingTx alpn rx pend).live = none ∧
    (Phase.installingRx alpn pend).live = none :=
  ⟨rfl, rfl⟩

end Tls
