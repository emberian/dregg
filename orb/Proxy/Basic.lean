/-
Proxy — cold-plane policy machinery for a reverse proxy.

Shared vocabulary for the four Proxy models:

  * `Proxy.Balance`   — load-balancer selection algebra (weighted round-robin,
                        least-connections, rendezvous hashing) with tiered
                        fallback (primary → backup) and policy chains;
  * `Proxy.Health`    — the probe-driven up/down machine with hysteresis
                        (rise/fall thresholds);
  * `Proxy.Connect`   — the upstream-connect machine (resolve → connect with
                        deadline → retry-with-backoff over the balancer →
                        established | exhausted);
  * `Proxy.ConnPool`  — per-backend connection checkout/checkin with a cap and
                        the reuse-before-create rule.

Everything is a pure function over an explicit state. All selection policy is
cold-plane: it runs once per request (or per connection attempt), never per
byte, so the model optimizes for provability, not for the constant factor.

A `Backend` is one upstream target as the balancer sees it: a stable identity,
a configured weight, the current in-flight connection count, a fallback tier
(0 = primary, 1 = first backup tier, …), the health verdict produced by the
`Health` machine, and the administrative status. Selection *policy* never
mutates a `Backend`; the fields `conns` and `healthy` are inputs computed by
other machines and snapshotted into the selection call.
-/

namespace Proxy

/-- Administrative status of a backend. `draining` keeps existing connections
but receives no new ones; `down` is excluded entirely. Both are excluded from
*selection* — the distinction matters only to connection teardown, which is
outside this model. -/
inductive Status where
  | active
  | draining
  | down
deriving DecidableEq, Repr

/-- One upstream target, as snapshotted at selection time. -/
structure Backend where
  /-- Stable identity (config index / hash-ring identity). -/
  id : Nat
  /-- Configured relative weight (weighted policies). -/
  weight : Nat
  /-- Current in-flight connections (least-connections input). -/
  conns : Nat
  /-- Fallback tier: 0 = primary, higher = later backup tiers. -/
  tier : Nat
  /-- Health verdict from the probe machine (`Proxy.Health`). -/
  healthy : Bool
  /-- Administrative status (admin API / drain). -/
  status : Status
deriving DecidableEq, Repr

/-- A backend is eligible for new connections iff it is probe-healthy and
administratively active. `draining` and `down` are both ineligible. -/
def Backend.eligible (b : Backend) : Bool :=
  b.healthy && decide (b.status = .active)

/-- Sum of configured weights. The weighted-round-robin cycle length. -/
def totalWeight : List Backend → Nat
  | [] => 0
  | b :: bs => b.weight + totalWeight bs

@[simp] theorem totalWeight_nil : totalWeight [] = 0 := rfl

@[simp] theorem totalWeight_cons (b : Backend) (bs : List Backend) :
    totalWeight (b :: bs) = b.weight + totalWeight bs := rfl

/-- A member with positive weight makes the total positive. -/
theorem totalWeight_pos {bs : List Backend} {b : Backend}
    (hmem : b ∈ bs) (hw : 0 < b.weight) : 0 < totalWeight bs := by
  induction bs with
  | nil => cases hmem
  | cons c rest ih =>
    rcases List.mem_cons.mp hmem with h | h
    · subst h; simp; omega
    · have := ih h; simp; omega

/-- If the total weight is zero, every member's weight is zero. -/
theorem weight_eq_zero_of_totalWeight_eq_zero {bs : List Backend} {b : Backend}
    (h : totalWeight bs = 0) (hmem : b ∈ bs) : b.weight = 0 := by
  induction bs with
  | nil => cases hmem
  | cons c rest ih =>
    simp at h
    rcases List.mem_cons.mp hmem with hb | hb
    · subst hb; omega
    · exact ih h.2 hb

/-- The backend list has pairwise-distinct identities. Selection theorems that
speak about *the* backend with a given identity assume this; the engine's
config loader guarantees it (backends are keyed by config index). -/
def idsNodup (bs : List Backend) : Prop :=
  (bs.map Backend.id).Nodup

/-- Under `idsNodup`, identity determines the element. -/
theorem eq_of_id_eq {bs : List Backend} {b c : Backend} (hnd : idsNodup bs)
    (hb : b ∈ bs) (hc : c ∈ bs) (hid : b.id = c.id) : b = c := by
  induction bs with
  | nil => cases hb
  | cons a rest ih =>
    have hnd' : a.id ∉ rest.map Backend.id ∧ idsNodup rest := by
      simpa [idsNodup] using hnd
    rcases List.mem_cons.mp hb with hb' | hb' <;>
      rcases List.mem_cons.mp hc with hc' | hc'
    · rw [hb', hc']
    · exfalso
      apply hnd'.1
      have : c.id ∈ rest.map Backend.id := List.mem_map_of_mem Backend.id hc'
      rw [hb'] at hid
      rwa [hid]
    · exfalso
      apply hnd'.1
      have : b.id ∈ rest.map Backend.id := List.mem_map_of_mem Backend.id hb'
      rw [hc'] at hid
      rwa [← hid]
    · exact ih hnd'.2 hb' hc'

end Proxy
