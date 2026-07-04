/-
Udp.Correlation — bidirectional correlation (theorem 5).

A reply arriving on an upstream binding is routed back to *exactly* the client
whose session produced that binding — never to another client, and never to a
stale client whose session has since been evicted.

  * `findByBinding_owner` — under the invariant, the reverse index resolves a
    binding to *the* client that owns it (binding-injectivity makes it unique).
  * `reply_routes_to_owner` — a reply on `s.binding` is delivered to the session
    owner `a`.
  * `reply_owner_unique` — the client a reply is delivered to is uniquely the
    binding's owner: no reply is ever split to two clients.
  * `roundtrip` — the correlation crown: a client's datagram forwards to its
    binding, and a reply on that binding returns to that same client.
  * `stale_reply_dropped` — after a session is evicted, a reply to its *old*
    binding finds no live session and is dropped: no misdelivery, and (with the
    fresh-binding law of `Udp.Eviction`) no reuse can resurrect it.
-/

import Udp.Eviction

namespace Udp

/-- If every entry misses binding `u`, the reverse index reports absence. -/
theorem findByBinding_none_of_all {t : Table} {u : Nat}
    (h : ∀ p ∈ t, p.2.binding ≠ u) : findByBinding t u = none := by
  induction t with
  | nil => rfl
  | cons c rest ih =>
    obtain ⟨cb, cs⟩ := c
    simp only [findByBinding]
    have hcne : cs.binding ≠ u := h (cb, cs) (List.mem_cons_self _ _)
    rw [if_neg hcne]
    exact ih (fun p hp => h p (List.mem_cons_of_mem _ hp))

/-- **The reverse index is exact.** Under the invariant, a binding owned by a
live session `(a, s)` resolves — via `findByBinding` — to that very session, and
to no other: binding-injectivity makes the owner unique. -/
theorem findByBinding_owner {r : Relay} {a : Addr} {s : Session} {u : Nat}
    (hinv : r.Inv) (hmem : (a, s) ∈ r.sessions) (hu : s.binding = u) :
    findByBinding r.sessions u = some (a, s) := by
  cases hf : findByBinding r.sessions u with
  | none =>
    exact absurd hu (findByBinding_none hf (a, s) hmem)
  | some bs =>
    obtain ⟨b, s'⟩ := bs
    obtain ⟨hbmem, hb⟩ := findByBinding_mem hf
    have heq : (b, s') = (a, s) := by
      refine hinv.bindingInj (b, s') (a, s) hbmem hmem ?_
      show s'.binding = s.binding
      rw [hb, hu]
    rw [heq]

/-- **Bidirectional correlation (theorem 5).** A reply arriving on a live
session's binding is delivered back to that session's client — the exact client
whose datagrams produced the binding. -/
theorem reply_routes_to_owner {r : Relay} {a : Addr} {s : Session} {u : Nat}
    {p : Payload} {now : Nat} (hinv : r.Inv)
    (h : lookup r.sessions a = some s) (hu : s.binding = u) :
    (onUpstream r u p now).2 = Out.deliver a p := by
  have hfind : findByBinding r.sessions u = some (a, s) :=
    findByBinding_owner hinv (lookup_mem h) hu
  simp only [onUpstream, hfind]

/-- **Reply uniqueness.** Whatever client a reply on binding `u` is delivered to
is the unique owner of `u`: it must be `a`, the client whose session holds `u`.
A reply is never split across two clients. -/
theorem reply_owner_unique {r : Relay} {a b : Addr} {s : Session} {u : Nat}
    {p p' : Payload} {now : Nat} (hinv : r.Inv)
    (h : lookup r.sessions a = some s) (hu : s.binding = u)
    (hdel : (onUpstream r u p now).2 = Out.deliver b p') : b = a := by
  -- unfold the delivery: it names the found owner, forced to (a, s) by injectivity
  rw [reply_routes_to_owner hinv h hu] at hdel
  cases hdel
  rfl

/-- **The correlation crown.** For a live session `(a, s)`: a datagram from `a`
forwards to `s.binding`, and a reply on `s.binding` returns to `a`. The forward
and reverse paths agree on the client↔binding pairing. -/
theorem roundtrip {r : Relay} {a : Addr} {s : Session} {p q : Payload}
    {now now' : Nat} (hinv : r.Inv) (h : lookup r.sessions a = some s) :
    (onClient r a p now).2 = Out.forward a s.binding p ∧
    (onUpstream r s.binding q now').2 = Out.deliver a q :=
  ⟨onClient_existing_forward h, reply_routes_to_owner hinv h rfl⟩

/-- **No stale binding on the reply path (theorem 5 ∧ theorem 3).** After an
expired session is swept, a reply to that client's *old* binding finds no live
session and is dropped — it is never misdelivered. (Binding-injectivity means
only the evicted session ever held that binding.) -/
theorem stale_reply_dropped {timeout now now' : Nat} {r : Relay} {a : Addr}
    {sOld : Session} {p : Payload} (hinv : r.Inv)
    (hpre : lookup r.sessions a = some sOld)
    (hexp : sOld.lastActive + timeout ≤ now) :
    (onUpstream (sweep timeout now r) sOld.binding p now').2 = Out.drop := by
  have hamem : (a, sOld) ∈ r.sessions := lookup_mem hpre
  have hnone : findByBinding (sweep timeout now r).sessions sOld.binding = none := by
    apply findByBinding_none_of_all
    intro q hq hqb
    -- q survived the sweep and (supposedly) carries sOld's binding
    obtain ⟨hqmem, hqsurv⟩ := mem_sweep_iff.mp hq
    have heq : q = (a, sOld) := hinv.bindingInj q (a, sOld) hqmem hamem hqb
    rw [heq] at hqsurv
    -- but (a, sOld) is expired, so it could not have survived
    have : now < sOld.lastActive + timeout := hqsurv
    omega
  simp only [onUpstream, hnone]

end Udp
