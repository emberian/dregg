/-
Resume — session-resumption tickets over a time-and-epoch input.

A resumption ticket lets a returning client abbreviate the handshake.  The
acceptance decision is modeled as a total, deterministic function of the
ticket, the current wall-clock time, and the current key epoch:

    accept : Ticket → (now : Nat) → (epoch : Nat) → Bool

Two independent gates decide acceptance, and each theorem pins one of them:

  * the **validity window** `[issued, issued + lifetime)` — a ticket is
    accepted only inside its own lifetime; an expired ticket (or one presented
    before its issue time) is refused.
  * the **key epoch** — a ticket names the key generation that minted it and is
    accepted only while that generation is current.  Rotating the key (a fresh
    start / SIGHUP) advances the epoch in one atomic step and thereby
    invalidates every prior-epoch ticket at once.  This is the single-owner
    property: at any instant exactly one epoch owns the acceptance decision.
    The epoch is carried here as a plain `Nat` flag so the transport lane can
    key its own 0-RTT anti-replay on the same generation without this file
    depending on it.

Time and epoch are the only inputs, so acceptance is deterministic: the same
ticket at the same time under the same epoch always yields the same verdict.
-/

namespace Resume

/-- A resumption ticket.  `issued` is the wall-clock time it was minted,
`lifetime` its validity duration (`0` ⇒ never valid), and `epoch` the key
generation that may accept it. -/
structure Ticket where
  issued : Nat
  lifetime : Nat
  epoch : Nat
deriving DecidableEq, Repr

/-- The exclusive upper end of the validity window: the first instant at which
the ticket is expired. -/
def Ticket.expiry (t : Ticket) : Nat := t.issued + t.lifetime

/-- Prop-level specification of acceptance: inside the half-open validity
window and under the ticket's own key epoch. -/
def Ticket.Accepts (t : Ticket) (now epoch : Nat) : Prop :=
  t.issued ≤ now ∧ now < t.expiry ∧ epoch = t.epoch

/-- The acceptance decision: a total Bool function of the ticket, the current
time, and the current key epoch. -/
def accept (t : Ticket) (now epoch : Nat) : Bool :=
  decide (t.issued ≤ now) && decide (now < t.expiry) && decide (epoch = t.epoch)

/-- The Bool decision agrees with the Prop specification exactly. -/
theorem accept_iff (t : Ticket) (now epoch : Nat) :
    accept t now epoch = true ↔ t.Accepts now epoch := by
  simp only [accept, Ticket.Accepts, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- A ticket is refused whenever it is outside the accepted set. -/
theorem accept_false_of_not (t : Ticket) (now epoch : Nat)
    (h : ¬ t.Accepts now epoch) : accept t now epoch = false := by
  cases hb : accept t now epoch with
  | false => rfl
  | true => exact absurd ((accept_iff t now epoch).mp hb) h

/-- **Validity window.**  Acceptance implies the current time lies in the
half-open window `[issued, issued + lifetime)`. -/
theorem accept_in_window {t : Ticket} {now epoch : Nat}
    (h : accept t now epoch = true) : t.issued ≤ now ∧ now < t.expiry :=
  let hA := (accept_iff t now epoch).mp h
  ⟨hA.1, hA.2.1⟩

/-- **Expired tickets are refused.**  At or past `issued + lifetime` the ticket
is never accepted — the resumption validity window is closed on the right. -/
theorem expired_refused (t : Ticket) (now epoch : Nat)
    (h : t.expiry ≤ now) : accept t now epoch = false :=
  accept_false_of_not t now epoch (fun hA => by have := hA.2.1; omega)

/-- Symmetrically, a ticket presented before its issue time is refused — the
window is closed on the left. -/
theorem premature_refused (t : Ticket) (now epoch : Nat)
    (h : now < t.issued) : accept t now epoch = false :=
  accept_false_of_not t now epoch (fun hA => by have := hA.1; omega)

/-- **Wrong epoch is refused.**  A ticket outside the current key epoch is
never accepted. -/
theorem wrong_epoch_refused (t : Ticket) (now epoch : Nat)
    (h : epoch ≠ t.epoch) : accept t now epoch = false :=
  accept_false_of_not t now epoch (fun hA => h hA.2.2)

/-- **Acceptance is deterministic.**  The verdict is a function of the ticket,
the time, and the epoch alone — no hidden state can make two evaluations at the
same inputs disagree. -/
theorem accept_deterministic (t : Ticket) (now epoch : Nat) {b₁ b₂ : Bool}
    (h₁ : accept t now epoch = b₁) (h₂ : accept t now epoch = b₂) : b₁ = b₂ :=
  h₁ ▸ h₂

/-- **Single-owner.**  A ticket is accepted under at most one epoch: any epoch
that accepts it must equal the ticket's own generation, so two accepting epochs
coincide. -/
theorem accept_single_epoch {t : Ticket} {now e₁ e₂ : Nat}
    (h₁ : accept t now e₁ = true) (h₂ : accept t now e₂ = true) : e₁ = e₂ := by
  have hA₁ := (accept_iff t now e₁).mp h₁
  have hA₂ := (accept_iff t now e₂).mp h₂
  rw [hA₁.2.2, hA₂.2.2]

/-! ### The issuing server: minting under an epoch, and atomic rotation

The server holds the current key epoch and the lifetime it stamps on tickets.
Minting a ticket stamps the current time and epoch; rotating the key advances
the epoch in one atomic step (mirroring the config reload's whole-value swap),
which invalidates every ticket minted under the prior epoch at once. -/

/-- The issuing server: the current key `epoch`, the `lifetime` it stamps on
new tickets, and a ghost log of `minted` tickets. -/
structure Server where
  epoch : Nat
  lifetime : Nat
  minted : List Ticket
deriving Repr

/-- Cold start: epoch 0, nothing minted. -/
def Server.init (lifetime : Nat) : Server :=
  { epoch := 0, lifetime := lifetime, minted := [] }

/-- The ticket the server mints at time `now`: current time, configured
lifetime, current epoch. -/
def Server.mkTicket (s : Server) (now : Nat) : Ticket :=
  { issued := now, lifetime := s.lifetime, epoch := s.epoch }

/-- Mint a ticket at time `now`, logging it.  Returns the updated server and
the ticket. -/
def Server.mint (s : Server) (now : Nat) : Server × Ticket :=
  ({ s with minted := s.mkTicket now :: s.minted }, s.mkTicket now)

/-- Rotate the key: advance the epoch by one, atomically.  Only the `epoch`
field moves; the stamped lifetime and the mint log are untouched. -/
def Server.rotate (s : Server) : Server := { s with epoch := s.epoch + 1 }

/-- A minted ticket carries the server's current epoch. -/
theorem mint_epoch (s : Server) (now : Nat) : (s.mint now).2.epoch = s.epoch := rfl

/-- A freshly minted ticket (positive lifetime) is accepted at its mint time
under the minting epoch — resumption works the instant a ticket is issued. -/
theorem mint_accepted_now (s : Server) (now : Nat) (hl : 0 < s.lifetime) :
    accept (s.mint now).2 now s.epoch = true := by
  rw [accept_iff]
  refine ⟨?_, ?_, ?_⟩
  · show now ≤ now
    exact Nat.le_refl now
  · show now < now + s.lifetime
    omega
  · rfl

/-- **Rotation invalidates prior-epoch tickets.**  After a key rotation, a
ticket minted under the old epoch is refused under the new epoch, regardless of
time — the single-owner handover is atomic and complete. -/
theorem rotate_invalidates (s : Server) (t : Ticket) (now : Nat)
    (h : t.epoch = s.epoch) : accept t now s.rotate.epoch = false := by
  apply wrong_epoch_refused
  show s.epoch + 1 ≠ t.epoch
  omega

/-- **Rotation is atomic.**  A rotate replaces only the epoch field, as one
whole value: the stamped lifetime and the mint log are unchanged, and the epoch
becomes exactly `epoch + 1` — never a torn intermediate. -/
theorem rotate_atomic (s : Server) :
    s.rotate.lifetime = s.lifetime
  ∧ s.rotate.minted = s.minted
  ∧ s.rotate.epoch = s.epoch + 1 :=
  ⟨rfl, rfl, rfl⟩

/-- Across a rotation the epoch cell is observed as exactly the old value or the
new one — the two-valued image that "atomic swap, never torn" means for the
epoch. -/
theorem rotate_epoch_old_or_new (s : Server) (obs : Nat)
    (h : obs = s.epoch ∨ obs = s.rotate.epoch) : obs = s.epoch ∨ obs = s.epoch + 1 := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr h

namespace Server

/-- One step of the issuing server: mint a ticket, or rotate the key. -/
inductive Step : Server → Server → Prop where
  | mint (now : Nat) (s : Server) : Step s (s.mint now).1
  | rotate (s : Server) : Step s s.rotate

/-- States reachable from a cold start by any sequence of steps. -/
inductive Reachable (lifetime : Nat) : Server → Prop where
  | init : Reachable lifetime (Server.init lifetime)
  | step {s s' : Server} : Reachable lifetime s → Step s s' → Reachable lifetime s'

/-- Server invariant: every minted ticket's epoch is at most the current epoch.
Minting stamps the current epoch; rotation only increases it — so once the
epoch has advanced past a ticket's generation it never returns, and
`wrong_epoch_refused` refuses that ticket forever. -/
def Wf (s : Server) : Prop := ∀ t ∈ s.minted, t.epoch ≤ s.epoch

theorem wf_init (lifetime : Nat) : Wf (init lifetime) := by
  intro t ht
  simp [init] at ht

theorem wf_step {s s' : Server} (h : Wf s) (hstep : Step s s') : Wf s' := by
  cases hstep with
  | mint now s =>
    intro t ht
    show t.epoch ≤ s.epoch
    have hm : (s.mint now).1.minted = s.mkTicket now :: s.minted := rfl
    rw [hm] at ht
    rcases List.mem_cons.mp ht with h1 | h1
    · rw [h1]; exact Nat.le_refl _
    · exact h t h1
  | rotate s =>
    intro t ht
    show t.epoch ≤ s.epoch + 1
    exact Nat.le_succ_of_le (h t ht)

/-- **The invariant holds throughout every run.** -/
theorem reachable_wf {lifetime : Nat} {s : Server} (h : Reachable lifetime s) :
    Wf s := by
  induction h with
  | init => exact wf_init lifetime
  | step _ hstep ih => exact wf_step ih hstep

end Server

end Resume
