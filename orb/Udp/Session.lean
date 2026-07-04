/-
Udp.Session — session affinity, datagram integrity, and the finite key-unique
map, over the relay machine of `Udp.Basic`.

  * **Affinity** (theorem 1). A live client's datagram is forwarded to the
    *recorded* binding (`onClient_existing_forward`), and that binding never
    changes while the session lives: it is invariant under a datagram from any
    client (`binding_stable_onClient`), under an upstream reply
    (`binding_stable_onUpstream`), and hence across any eviction-free schedule
    (`affinity_run`). Two consecutive datagrams from the same client hit the
    same binding (`affinity_two_datagrams`) — a client is never split across
    upstreams mid-session.

  * **Integrity** (theorem 2). The forwarded/delivered datagram carries the
    input payload byte-for-byte (`onClient_forward_payload`,
    `onUpstream_deliver_payload`): the relay never mutates the body.

  * **Finite key-unique map** (theorem 4). The table is a finite list with
    unique keys, and both invariants survive every transition
    (`onClient_keyUnique`, `sweep_keyUnique`; `Relay.Inv` via `run_inv`), with
    bounded growth per event (`onClient_length_le`, `sweep_length_le`).
-/

import Udp.Basic

namespace Udp

/-! ### Affinity: the forwarded binding, and its stability -/

/-- **Affinity (step).** A datagram from a client with a live session is
forwarded to that session's *recorded* binding — the binding is read, never
re-chosen. -/
theorem onClient_existing_forward {r : Relay} {a : Addr} {p : Payload} {now : Nat}
    {s : Session} (h : lookup r.sessions a = some s) :
    (onClient r a p now).2 = Out.forward a s.binding p := by
  simp only [onClient, h]

/-- A datagram from a client with *no* session is forwarded to a freshly
allocated binding (`nextBinding`). -/
theorem onClient_fresh_forward {r : Relay} {a : Addr} {p : Payload} {now : Nat}
    (h : lookup r.sessions a = none) :
    (onClient r a p now).2 = Out.forward a r.nextBinding p := by
  simp only [onClient, h]

/-- **Affinity (binding stable under a datagram).** A datagram from *any* client
`a` leaves the binding of every already-live client `b` unchanged — including
`b = a` (a refresh reuses the binding) and `b ≠ a` (untouched). The binding,
once assigned, is a fixed point of the datagram transition. -/
theorem binding_stable_onClient (r : Relay) (a b : Addr) (p : Payload) (now : Nat)
    {u : Nat} (hb : bindingOf r.sessions b = some u) :
    bindingOf (onClient r a p now).1.sessions b = some u := by
  by_cases hab : b = a
  · subst hab
    unfold bindingOf at hb ⊢
    cases h : lookup r.sessions b with
    | none => rw [h] at hb; simp at hb
    | some s =>
      rw [h] at hb
      simp only [onClient, h, lookup_upsert_self]
      simpa using hb
  · unfold bindingOf at hb ⊢
    cases h : lookup r.sessions a with
    | some s =>
      simp only [onClient, h]
      rw [lookup_upsert_other _ _ hab]; exact hb
    | none =>
      simp only [onClient, h]
      rw [lookup_upsert_other _ _ hab]; exact hb

/-- **Affinity (binding stable under a reply).** An upstream reply (to any
binding) leaves the binding of every already-live client `b` unchanged. Uses the
invariant to identify the refreshed session when `b` owns the replied binding. -/
theorem binding_stable_onUpstream {r : Relay} (hinv : r.Inv) {v : Nat}
    {q : Payload} {now : Nat} {b : Addr} {u : Nat}
    (hb : bindingOf r.sessions b = some u) :
    bindingOf (onUpstream r v q now).1.sessions b = some u := by
  simp only [onUpstream]
  cases h : findByBinding r.sessions v with
  | none => exact hb
  | some cs =>
    obtain ⟨c, s⟩ := cs
    have hcmem : (c, s) ∈ r.sessions := (findByBinding_mem h).1
    by_cases hbc : b = c
    · subst hbc
      -- b owns the replied session; its lookup and the found session coincide
      unfold bindingOf at hb ⊢
      have hlk : lookup r.sessions b = some s := mem_lookup hinv.keyUnique hcmem
      rw [hlk] at hb
      simp only [lookup_upsert_self]
      simpa using hb
    · unfold bindingOf at hb ⊢
      rw [lookup_upsert_other _ _ hbc]; exact hb

/-- **Affinity (two datagrams).** Two datagrams from the same live client are
forwarded to the *same* binding — the recorded `s.binding` both times. The
client is not split across upstreams between the two datagrams. -/
theorem affinity_two_datagrams (r : Relay) (a : Addr) (p1 p2 : Payload)
    (now1 now2 : Nat) {s : Session} (h : lookup r.sessions a = some s) :
    (onClient r a p1 now1).2 = Out.forward a s.binding p1 ∧
    (onClient (onClient r a p1 now1).1 a p2 now2).2 = Out.forward a s.binding p2 := by
  refine ⟨onClient_existing_forward h, ?_⟩
  have h1 : lookup (onClient r a p1 now1).1.sessions a = some { s with lastActive := now1 } := by
    simp only [onClient, h, lookup_upsert_self]
  have := onClient_existing_forward (r := (onClient r a p1 now1).1)
    (a := a) (p := p2) (now := now2) h1
  simpa using this

/-- **Affinity (session lifetime).** Over any eviction-free schedule (no sweep
event), a live client's binding is constant. This is "a client is never split
across upstreams mid-session": for the whole span between opening and eviction,
every datagram routes to the same upstream binding. -/
theorem affinity_run (timeout : Nat) (r : Relay) (es : List Ev)
    (hns : ∀ e ∈ es, e.isSweep = false) (hinv : r.Inv) {b u : Nat}
    (hb : bindingOf r.sessions b = some u) :
    bindingOf (run timeout r es).sessions b = some u := by
  induction es generalizing r with
  | nil => exact hb
  | cons e es ih =>
    have hns_e : e.isSweep = false := hns e (List.mem_cons_self _ _)
    have hstep : bindingOf (stepEv timeout r e).sessions b = some u := by
      cases e with
      | client a p now => exact binding_stable_onClient r a b p now hb
      | upstream v q now => exact binding_stable_onUpstream hinv hb
      | sweep now => simp [Ev.isSweep] at hns_e
    exact ih (stepEv timeout r e) (fun e' he' => hns e' (List.mem_cons_of_mem _ he'))
      (stepEv_inv timeout e hinv) hstep

/-! ### Integrity: the relay does not mutate the datagram body -/

/-- **Integrity (client→upstream).** The forwarded datagram carries the input
payload verbatim, for a live *or* a fresh client. -/
theorem onClient_forward_payload (r : Relay) (a : Addr) (p : Payload) (now : Nat) :
    (onClient r a p now).2.payload? = some p := by
  cases h : lookup r.sessions a with
  | some s => simp [onClient, h, Out.payload?]
  | none => simp [onClient, h, Out.payload?]

/-- **Integrity (upstream→client).** A delivered reply carries the input payload
verbatim. -/
theorem onUpstream_deliver_payload (r : Relay) (u : Nat) (p : Payload) (now : Nat)
    {a : Addr} {s : Session} (h : findByBinding r.sessions u = some (a, s)) :
    (onUpstream r u p now).2 = Out.deliver a p ∧
    (onUpstream r u p now).2.payload? = some p := by
  constructor
  · simp only [onUpstream, h]
  · simp only [onUpstream, h, Out.payload?]

/-! ### The finite key-unique map -/

/-- `onClient` keeps the table key-unique (a client keeps at most one session). -/
theorem onClient_keyUnique (r : Relay) (a : Addr) (p : Payload) (now : Nat)
    (h : KeyUnique r.sessions) : KeyUnique (onClient r a p now).1.sessions := by
  cases hl : lookup r.sessions a with
  | some s => simp only [onClient, hl]; exact upsert_keyUnique a _ h
  | none => simp only [onClient, hl]; exact upsert_keyUnique a _ h

/-- The idle sweep keeps the table key-unique. -/
theorem sweep_keyUnique (timeout now : Nat) (r : Relay)
    (h : KeyUnique r.sessions) : KeyUnique (sweep timeout now r).sessions := by
  simp only [sweep]; exact filter_keyUnique _ h

/-- `upsert` grows the table by at most one entry. -/
theorem upsert_length_le (t : Table) (a : Addr) (s : Session) :
    (upsert t a s).length ≤ t.length + 1 := by
  simp only [upsert, List.length_cons]
  have := List.length_filter_le (fun p => decide (p.1 ≠ a)) t
  omega

/-- `onClient` grows the table by at most one entry (bounded finiteness). -/
theorem onClient_length_le (r : Relay) (a : Addr) (p : Payload) (now : Nat) :
    (onClient r a p now).1.sessions.length ≤ r.sessions.length + 1 := by
  cases hl : lookup r.sessions a with
  | some s => simp only [onClient, hl]; exact upsert_length_le _ _ _
  | none => simp only [onClient, hl]; exact upsert_length_le _ _ _

/-- The idle sweep never grows the table. -/
theorem sweep_length_le (timeout now : Nat) (r : Relay) :
    (sweep timeout now r).sessions.length ≤ r.sessions.length := by
  simp only [sweep]; exact List.length_filter_le _ _

end Udp
