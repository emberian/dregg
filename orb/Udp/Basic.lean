/-
Udp.Basic — a per-client UDP datagram relay as a pure transition system.

A UDP relay owns no connections: it keeps a **session table** keyed by the
client's source address, each entry naming the dedicated **upstream binding**
(the per-session upstream socket) that the client's datagrams are forwarded to,
plus the timestamp of the last datagram forwarded in either direction. Three
transitions drive it, all pure functions over explicit state with time as an
*input*, never a clock read inside the machine:

  * `onClient a p now` — a datagram from client `a` with payload `p` at instant
    `now`. If `a` already has a session, the datagram is forwarded to that
    session's recorded binding and the session's activity clock is refreshed —
    **the binding is never re-chosen** (session affinity). If `a` has no
    session, a *fresh* binding is allocated from a monotonic counter
    (`nextBinding`) and the session is opened.
  * `sweep timeout now` — idle eviction. Every session whose idle gap
    (`now - lastActive`) has reached `timeout` is removed; every session still
    inside its window is left untouched. Eviction is **deadline-honored**: a
    session is dropped only once idle ≥ timeout, never earlier.
  * `onUpstream u p now` — a reply arriving on binding `u`. It is delivered back
    to exactly the client whose session owns `u` (and refreshes that session),
    or dropped if no live session owns `u`.

The session table is an association list with a **key-unique** invariant (a
client has at most one session) and a **binding-injective** invariant (distinct
clients hold distinct bindings) together with an **allocator-dominates**
invariant (every live binding is `< nextBinding`). The three together are
`Relay.Inv`, preserved by every transition (`upsert_refresh_inv`,
`open_fresh_inv`, `sweep_inv`, hence `run_inv`). Allocator-dominance is the
freshness fact behind *no stale binding reuse*, and it also discharges
binding-injectivity when a fresh session opens.
-/

namespace Udp

/-- A client source address. Abstract identity; equality is all the relay
inspects. -/
abbrev Addr := Nat

/-- A datagram payload — the relay treats it as opaque bytes and never mutates
it. -/
abbrev Payload := List Nat

/-- Per-client session state. `binding` is the dedicated upstream binding id
(the per-session upstream socket) this client is pinned to for the session's
lifetime; `lastActive` is the timestamp of the last datagram forwarded in either
direction (the idle-timeout clock). -/
structure Session where
  binding : Nat
  lastActive : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The session table: a client address mapped to its session. Modeled as an
association list carrying a key-unique invariant (`KeyUnique`), the finite
key-unique-map view. -/
abbrev Table := List (Addr × Session)

/-- The keys (client addresses) of a table, in order. -/
def keys (t : Table) : List Addr := t.map Prod.fst

/-- **Key-uniqueness**: no client appears twice. This is the "a client has at
most one session" invariant that makes `lookup` single-valued. -/
def KeyUnique (t : Table) : Prop := (keys t).Nodup

/-- Look up a client's session — the first entry with a matching key. Under
`KeyUnique` it is the *only* such entry. -/
def lookup (t : Table) (a : Addr) : Option Session :=
  match t with
  | [] => none
  | (b, s) :: rest => if b = a then some s else lookup rest a

/-- Insert-or-replace client `a`'s session: drop any existing entry for `a`,
then prepend the new one. Keeps keys unique by construction. -/
def upsert (t : Table) (a : Addr) (s : Session) : Table :=
  (a, s) :: t.filter (fun p => decide (p.1 ≠ a))

/-- Remove client `a`'s session. -/
def remove (t : Table) (a : Addr) : Table :=
  t.filter (fun p => decide (p.1 ≠ a))

/-- Reverse index: the entry whose session owns binding `u`, if any. Under
binding-injectivity it is unique. -/
def findByBinding (t : Table) (u : Nat) : Option (Addr × Session) :=
  match t with
  | [] => none
  | (b, s) :: rest => if s.binding = u then some (b, s) else findByBinding rest u

/-- The binding a client is currently pinned to, if it has a live session. -/
def bindingOf (t : Table) (a : Addr) : Option Nat :=
  (lookup t a).map Session.binding

/-! ### lookup / upsert / remove lemmas -/

@[simp] theorem lookup_upsert_self (t : Table) (a : Addr) (s : Session) :
    lookup (upsert t a s) a = some s := by
  simp [upsert, lookup]

/-- Filtering out key `a` leaves the lookup of any *other* key untouched. -/
theorem lookup_filter_ne (t : Table) {a b : Addr} (h : b ≠ a) :
    lookup (t.filter (fun p => decide (p.1 ≠ a))) b = lookup t b := by
  induction t with
  | nil => rfl
  | cons c rest ih =>
    obtain ⟨cb, cs⟩ := c
    by_cases hca : cb = a
    · -- head has key a: dropped by the filter; original skips it too (b ≠ a)
      have hfilt : ((cb, cs) :: rest).filter (fun p => decide (p.1 ≠ a))
          = rest.filter (fun p => decide (p.1 ≠ a)) := by
        simp [List.filter_cons, hca]
      have hab : cb ≠ b := by rw [hca]; exact fun e => h e.symm
      rw [hfilt, ih, lookup, if_neg hab]
    · -- head has key ≠ a: kept by the filter; both sides inspect it identically
      have hfilt : ((cb, cs) :: rest).filter (fun p => decide (p.1 ≠ a))
          = (cb, cs) :: rest.filter (fun p => decide (p.1 ≠ a)) := by
        simp [List.filter_cons, hca]
      rw [hfilt, lookup, lookup]
      by_cases hcb : cb = b
      · rw [if_pos hcb, if_pos hcb]
      · rw [if_neg hcb, if_neg hcb, ih]

theorem lookup_upsert_other (t : Table) {a b : Addr} (s : Session) (h : b ≠ a) :
    lookup (upsert t a s) b = lookup t b := by
  simp only [upsert, lookup]
  have hab : a ≠ b := fun e => h e.symm
  simp only [hab, if_false]
  exact lookup_filter_ne t h

@[simp] theorem lookup_remove_self (t : Table) (a : Addr) :
    lookup (remove t a) a = none := by
  induction t with
  | nil => simp [remove, lookup]
  | cons c rest ih =>
    obtain ⟨cb, cs⟩ := c
    by_cases hca : cb = a
    · simp only [remove, List.filter_cons, hca, ne_eq, not_true_eq_false,
        decide_false, Bool.false_eq_true, if_false]
      simpa [remove] using ih
    · have hkeep : decide (cb ≠ a) = true := by simp [hca]
      simp only [remove, List.filter_cons, hkeep, if_true, lookup, hca, if_false]
      simpa [remove] using ih

theorem lookup_remove_other (t : Table) {a b : Addr} (h : b ≠ a) :
    lookup (remove t a) b = lookup t b :=
  lookup_filter_ne t h

/-- A successful lookup witnesses membership. -/
theorem lookup_mem {t : Table} {a : Addr} {s : Session}
    (h : lookup t a = some s) : (a, s) ∈ t := by
  induction t with
  | nil => simp [lookup] at h
  | cons c rest ih =>
    obtain ⟨cb, cs⟩ := c
    simp only [lookup] at h
    by_cases hca : cb = a
    · rw [if_pos hca] at h
      cases h; subst hca; exact List.mem_cons_self _ _
    · rw [if_neg hca] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- `KeyUnique` decomposes on cons. -/
theorem keyUnique_cons {b : Addr} {s : Session} {rest : Table} :
    KeyUnique ((b, s) :: rest) ↔ b ∉ keys rest ∧ KeyUnique rest := by
  simp [KeyUnique, keys, List.nodup_cons]

/-- Under key-uniqueness, membership is recovered by lookup: a member entry is
*the* lookup result for its key. -/
theorem mem_lookup {t : Table} {a : Addr} {s : Session}
    (hk : KeyUnique t) (hmem : (a, s) ∈ t) : lookup t a = some s := by
  induction t with
  | nil => cases hmem
  | cons c rest ih =>
    obtain ⟨cb, cs⟩ := c
    rw [keyUnique_cons] at hk
    simp only [lookup]
    rcases List.mem_cons.mp hmem with heq | hrest
    · cases heq; simp
    · have hane : cb ≠ a := by
        intro e
        apply hk.1
        have : a ∈ keys rest := by
          simpa [keys] using List.mem_map_of_mem Prod.fst hrest
        rwa [e]
      rw [if_neg hane]
      exact ih hk.2 hrest

/-- `lookup` is single-valued under key-uniqueness. -/
theorem lookup_unique {t : Table} {a : Addr} {s s' : Session}
    (hk : KeyUnique t) (h : (a, s) ∈ t) (h' : (a, s') ∈ t) : s = s' := by
  have e1 := mem_lookup hk h
  have e2 := mem_lookup hk h'
  rw [e1] at e2; exact Option.some.inj e2

/-! ### findByBinding lemmas -/

theorem findByBinding_mem {t : Table} {u : Nat} {a : Addr} {s : Session}
    (h : findByBinding t u = some (a, s)) : (a, s) ∈ t ∧ s.binding = u := by
  induction t with
  | nil => simp [findByBinding] at h
  | cons c rest ih =>
    obtain ⟨cb, cs⟩ := c
    simp only [findByBinding] at h
    by_cases hb : cs.binding = u
    · rw [if_pos hb] at h
      cases h
      exact ⟨List.mem_cons_self _ _, hb⟩
    · rw [if_neg hb] at h
      obtain ⟨hmem, hbind⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hmem, hbind⟩

theorem findByBinding_none {t : Table} {u : Nat}
    (h : findByBinding t u = none) : ∀ p ∈ t, p.2.binding ≠ u := by
  induction t with
  | nil => intro p hp; cases hp
  | cons c rest ih =>
    obtain ⟨cb, cs⟩ := c
    simp only [findByBinding] at h
    by_cases hb : cs.binding = u
    · rw [if_pos hb] at h; exact absurd h (by simp)
    · rw [if_neg hb] at h
      intro p hp
      rcases List.mem_cons.mp hp with heq | hrest
      · cases heq; exact hb
      · exact ih h p hrest

/-! ### The relay state and its invariant -/

/-- The relay: the session table plus the monotonic binding allocator. Every
binding ever handed out is `< nextBinding`. -/
structure Relay where
  sessions : Table
  nextBinding : Nat
  deriving Repr

/-- Every live binding is strictly below the allocator counter. -/
def Dominated (t : Table) (bound : Nat) : Prop := ∀ p ∈ t, p.2.binding < bound

/-- **Binding-injectivity**: distinct entries hold distinct bindings — a binding
names at most one client. -/
def BindingInj (t : Table) : Prop :=
  ∀ p q, p ∈ t → q ∈ t → p.2.binding = q.2.binding → p = q

/-- The relay invariant: key-unique table, allocator dominates, bindings
injective. -/
structure Relay.Inv (r : Relay) : Prop where
  keyUnique : KeyUnique r.sessions
  dominated : Dominated r.sessions r.nextBinding
  bindingInj : BindingInj r.sessions

/-- The empty relay. -/
def Relay.init : Relay := { sessions := [], nextBinding := 0 }

theorem Relay.init_inv : Relay.init.Inv where
  keyUnique := by simp [KeyUnique, keys, Relay.init]
  dominated := by intro p hp; cases hp
  bindingInj := by intro p q hp; cases hp

/-! ### Structural preservation lemmas for the table operations -/

/-- `upsert` preserves key-uniqueness. -/
theorem upsert_keyUnique {t : Table} (a : Addr) (s : Session) (h : KeyUnique t) :
    KeyUnique (upsert t a s) := by
  rw [upsert, keyUnique_cons]
  refine ⟨?_, ?_⟩
  · intro hmem
    rcases List.mem_map.mp hmem with ⟨q, hq, hqa⟩
    have hne : q.1 ≠ a := by
      have := (List.mem_filter.mp hq).2
      simpa [decide_eq_true_eq] using this
    exact hne hqa
  · have hsub : ((t.filter (fun p => decide (p.1 ≠ a))).map Prod.fst).Sublist
        (t.map Prod.fst) := (List.filter_sublist t).map Prod.fst
    exact hsub.nodup h

/-- Filtering preserves key-uniqueness (the sweep and remove case). -/
theorem filter_keyUnique {t : Table} (q : Addr × Session → Bool) (h : KeyUnique t) :
    KeyUnique (t.filter q) := by
  have hsub : ((t.filter q).map Prod.fst).Sublist (t.map Prod.fst) :=
    (List.filter_sublist t).map Prod.fst
  exact hsub.nodup h

/-- Every entry of `upsert t a s` is either the new `(a, s)` or an old entry of
`t` (with key ≠ a). -/
theorem mem_upsert {t : Table} {a : Addr} {s : Session} {p : Addr × Session}
    (h : p ∈ upsert t a s) : p = (a, s) ∨ (p ∈ t ∧ p.1 ≠ a) := by
  rw [upsert] at h
  rcases List.mem_cons.mp h with heq | hf
  · exact Or.inl heq
  · rcases List.mem_filter.mp hf with ⟨hmem, hdec⟩
    exact Or.inr ⟨hmem, by simpa [decide_eq_true_eq] using hdec⟩

/-! ### The three transitions -/

/-- The relay's forwarding decision, recorded for the theorems. -/
inductive Out where
  /-- Client→upstream: forward `p` to binding `u` on behalf of client `a`. -/
  | forward (a : Addr) (u : Nat) (p : Payload)
  /-- Upstream→client: deliver `p` back to client `a`. -/
  | deliver (a : Addr) (p : Payload)
  /-- Nothing forwarded (a reply with no live session). -/
  | drop
  deriving Repr, DecidableEq

/-- The payload an output carries, if any. The relay copies the datagram body
verbatim; this projection reads it back for the integrity theorems. -/
def Out.payload? : Out → Option Payload
  | .forward _ _ p => some p
  | .deliver _ p => some p
  | .drop => none

/-- A datagram from client `a`. Affinity: an existing session forwards to its
recorded binding (never re-chosen) and refreshes its clock; a new client opens a
session with a freshly allocated binding. -/
def onClient (r : Relay) (a : Addr) (p : Payload) (now : Nat) : Relay × Out :=
  match lookup r.sessions a with
  | some s =>
    ({ r with sessions := upsert r.sessions a { s with lastActive := now } },
     Out.forward a s.binding p)
  | none =>
    ({ sessions := upsert r.sessions a { binding := r.nextBinding, lastActive := now },
       nextBinding := r.nextBinding + 1 },
     Out.forward a r.nextBinding p)

/-- Idle eviction. Keep exactly the sessions still inside their window
(`now < lastActive + timeout`); evict the rest. Time is the explicit input
`now`. -/
def sweep (timeout now : Nat) (r : Relay) : Relay :=
  { r with sessions :=
      r.sessions.filter (fun p => decide (now < p.2.lastActive + timeout)) }

/-- A reply arriving on binding `u`. Delivered to the client whose session owns
`u` (refreshing its clock), or dropped if no live session owns `u`. -/
def onUpstream (r : Relay) (u : Nat) (p : Payload) (now : Nat) : Relay × Out :=
  match findByBinding r.sessions u with
  | some (a, s) =>
    ({ r with sessions := upsert r.sessions a { s with lastActive := now } },
     Out.deliver a p)
  | none => (r, Out.drop)

/-! ### Invariant preservation -/

/-- Refreshing an existing entry's clock (binding unchanged) preserves the
invariant. Shared by `onClient` on a live session and `onUpstream` on a hit. -/
theorem upsert_refresh_inv {r : Relay} {a : Addr} {s : Session} {now : Nat}
    (hinv : r.Inv) (hmem : (a, s) ∈ r.sessions) :
    Relay.Inv { r with sessions := upsert r.sessions a { s with lastActive := now } } where
  keyUnique := upsert_keyUnique a _ hinv.keyUnique
  dominated := by
    intro p hp
    rcases mem_upsert hp with heq | ⟨hmemp, _⟩
    · subst heq; exact hinv.dominated (a, s) hmem
    · exact hinv.dominated p hmemp
  bindingInj := by
    intro p q hp hq hbind
    -- new entry binding = s.binding; a live-refresh cannot collide with a
    -- surviving old entry (they'd share s.binding, forcing key a via BindingInj)
    rcases mem_upsert hp with hpeq | ⟨hpm, hpne⟩ <;>
      rcases mem_upsert hq with hqeq | ⟨hqm, hqne⟩
    · rw [hpeq, hqeq]
    · -- p = new, q survivor: q would share s.binding, so q = (a,s), key a, contra
      exfalso
      rw [hpeq] at hbind
      have hqb : q.2.binding = s.binding := hbind.symm
      have : q = (a, s) := hinv.bindingInj q (a, s) hqm hmem hqb
      exact hqne (by rw [this])
    · exfalso
      rw [hqeq] at hbind
      have hpb : p.2.binding = s.binding := hbind
      have : p = (a, s) := hinv.bindingInj p (a, s) hpm hmem hpb
      exact hpne (by rw [this])
    · exact hinv.bindingInj p q hpm hqm hbind

/-- Opening a fresh session with a freshly allocated binding preserves the
invariant. Allocator-dominance gives the fresh binding distinctness. -/
theorem open_fresh_inv {r : Relay} {a : Addr} {now : Nat} (hinv : r.Inv) :
    Relay.Inv
      { sessions := upsert r.sessions a { binding := r.nextBinding, lastActive := now },
        nextBinding := r.nextBinding + 1 } where
  keyUnique := upsert_keyUnique a _ hinv.keyUnique
  dominated := by
    intro p hp
    rcases mem_upsert hp with heq | ⟨hmemp, _⟩
    · subst heq
      show r.nextBinding < r.nextBinding + 1
      omega
    · have hlt := hinv.dominated p hmemp
      show p.2.binding < r.nextBinding + 1
      omega
  bindingInj := by
    intro p q hp hq hbind
    -- fresh binding = nextBinding, strictly above every old binding
    rcases mem_upsert hp with hpeq | ⟨hpm, _⟩ <;>
      rcases mem_upsert hq with hqeq | ⟨hqm, _⟩
    · rw [hpeq, hqeq]
    · exfalso
      rw [hpeq] at hbind
      have hb : r.nextBinding = q.2.binding := hbind
      have hlt := hinv.dominated q hqm
      omega
    · exfalso
      rw [hqeq] at hbind
      have hb : p.2.binding = r.nextBinding := hbind
      have hlt := hinv.dominated p hpm
      omega
    · exact hinv.bindingInj p q hpm hqm hbind

/-- The idle sweep preserves the invariant (it only shrinks the table). -/
theorem sweep_inv {timeout now : Nat} {r : Relay} (hinv : r.Inv) :
    (sweep timeout now r).Inv where
  keyUnique := by
    simp only [sweep]; exact filter_keyUnique _ hinv.keyUnique
  dominated := by
    intro p hp
    simp only [sweep] at hp
    exact hinv.dominated p ((List.mem_filter.mp hp).1)
  bindingInj := by
    intro p q hp hq hbind
    simp only [sweep] at hp hq
    exact hinv.bindingInj p q ((List.mem_filter.mp hp).1) ((List.mem_filter.mp hq).1) hbind

/-- `onClient` preserves the invariant. -/
theorem onClient_inv {r : Relay} {a : Addr} {p : Payload} {now : Nat}
    (hinv : r.Inv) : (onClient r a p now).1.Inv := by
  simp only [onClient]
  cases h : lookup r.sessions a with
  | some s => exact upsert_refresh_inv hinv (lookup_mem h)
  | none => exact open_fresh_inv hinv

/-- `onUpstream` preserves the invariant. -/
theorem onUpstream_inv {r : Relay} {u : Nat} {p : Payload} {now : Nat}
    (hinv : r.Inv) : (onUpstream r u p now).1.Inv := by
  simp only [onUpstream]
  cases h : findByBinding r.sessions u with
  | some as =>
    obtain ⟨a, s⟩ := as
    exact upsert_refresh_inv hinv (findByBinding_mem h).1
  | none => exact hinv

/-! ### The event trace -/

/-- The events driving the relay. Time enters only through the explicit `now`
fields. -/
inductive Ev where
  | client (a : Addr) (p : Payload) (now : Nat)
  | upstream (u : Nat) (p : Payload) (now : Nat)
  | sweep (now : Nat)

/-- Is this a sweep (an eviction event)? Client/upstream events never evict. -/
def Ev.isSweep : Ev → Bool
  | .sweep _ => true
  | _ => false

/-- One event step. -/
def stepEv (timeout : Nat) (r : Relay) : Ev → Relay
  | .client a p now => (onClient r a p now).1
  | .upstream u p now => (onUpstream r u p now).1
  | .sweep now => sweep timeout now r

theorem stepEv_inv (timeout : Nat) {r : Relay} (e : Ev) (hinv : r.Inv) :
    (stepEv timeout r e).Inv := by
  cases e with
  | client a p now => exact onClient_inv hinv
  | upstream u p now => exact onUpstream_inv hinv
  | sweep now => exact sweep_inv hinv

/-- Run a whole trace of events. -/
def run (timeout : Nat) (r : Relay) : List Ev → Relay
  | [] => r
  | e :: es => run timeout (stepEv timeout r e) es

/-- **The invariant is a genuine invariant**: it survives every reachable
schedule of events. In particular the session table stays a finite key-unique
map (`(run …).Inv.keyUnique`) and bindings stay injective for every reachable
state. -/
theorem run_inv (timeout : Nat) {r : Relay} (es : List Ev) (hinv : r.Inv) :
    (run timeout r es).Inv := by
  induction es generalizing r with
  | nil => exact hinv
  | cons e es ih => exact ih (stepEv_inv timeout e hinv)

theorem run_init_inv (timeout : Nat) (es : List Ev) :
    (run timeout Relay.init es).Inv :=
  run_inv timeout es Relay.init_inv

end Udp
