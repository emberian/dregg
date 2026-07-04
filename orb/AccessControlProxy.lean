/-!
# Forward-proxy access control: IP allowlist, connection cap, destination policy

Before a forward proxy will service a request or open a CONNECT tunnel, it
consults an access-control policy. This file models that policy as a total
admission function and proves the two guarantees that matter for it: a
default-deny stance actually refuses unlisted destinations, and a per-client
concurrent-connection cap is never exceeded across any sequence of opens and
closes.

## RFC grounding

RFC 9110 §9.3.6 (CONNECT) warns: "There are significant risks in establishing a
tunnel to arbitrary servers ... Proxies that support CONNECT SHOULD restrict its
use to a limited set of known ports or a configurable list of safe request
targets." This file is the enforcement surface for that recommendation:

* **Client-IP allowlist (CIDR).** A client address is admitted only if it falls
  inside one of the configured CIDR blocks. CIDR containment is the classic
  "top `plen` bits agree" test; addresses are 32-bit values (an IPv4 model).
* **Destination host/port allow/deny.** A destination is refused if it is on the
  denylist; under *default-deny* it is refused unless it is on the allowlist.
* **Default-deny toggle.** Flips the destination stance from allow-by-default to
  deny-by-default.
* **Per-client connection cap.** The number of concurrent connections for a
  single client never exceeds a configured cap.

## Key theorems

* `acl_default_deny` — with `defaultDeny`, a destination absent from the
  allowlist is never admitted.
* `acl_conn_cap` — starting within the cap, no sequence of open/close events
  drives a client's concurrent-connection count above the cap.
* Supporting: `admit_under_cap` (admission implies headroom),
  `acl_empty_allowlist_denies` (an empty IP allowlist admits no one),
  `inCidr_base` / `inCidr_slash32` (CIDR containment sanity).

## Boundaries / UNCLOSED

* Addresses are 32-bit `Nat` values; IPv6 (128-bit) is not modeled, though the
  containment test generalizes by changing the bit width `32`.
* Reason codes (`clientBlocked` / `dstBlocked` / `capReached`) name *why*
  admission failed but are not themselves load-bearing in the theorems.
* Connection accounting is a per-client counter; it does not model which
  concrete connection closes, only that a close decrements the count.
-/

namespace AccessControlProxy

def version : String := "0.1.0"

/-! ## CIDR membership (IPv4 model) -/

/-- A CIDR block: a 32-bit base address and a prefix length `plen ≤ 32`. -/
structure Cidr where
  base : Nat
  plen : Nat
deriving Repr

/-- Is `ip` inside CIDR block `c`? The top `plen` bits must agree, i.e. the two
addresses coincide after dropping the low `32 - plen` host bits. -/
def inCidr (c : Cidr) (ip : Nat) : Bool :=
  decide (ip >>> (32 - c.plen) = c.base >>> (32 - c.plen))

/-- **A block contains its own base address.** -/
theorem inCidr_base (c : Cidr) : inCidr c c.base = true := by
  simp [inCidr]

/-- **A `/32` block matches exactly its address.** -/
theorem inCidr_slash32 (ip : Nat) : inCidr { base := ip, plen := 32 } ip = true := by
  simp [inCidr]

/-! ## Destinations and policy -/

/-- A connection destination: host name and port. -/
structure Dest where
  host : String
  port : Nat
deriving DecidableEq, BEq, Repr

/-- The access-control policy. -/
structure Policy where
  /-- Client-IP allowlist: a client is admitted only if inside one of these. -/
  allowCidrs  : List Cidr
  /-- Destination denylist: these are always refused. -/
  denyDst     : List Dest
  /-- Destination allowlist: consulted under `defaultDeny`. -/
  allowDst    : List Dest
  /-- Per-client concurrent connection cap. -/
  connCap     : Nat
  /-- When true, a destination must be on `allowDst` to be reached. -/
  defaultDeny : Bool
deriving Repr

/-- Why an admission was refused. -/
inductive Reason where
  | clientBlocked | dstBlocked | capReached
deriving DecidableEq, Repr

/-- The admission outcome. -/
inductive Decision where
  | admit
  | refuse (r : Reason)
deriving DecidableEq, Repr

/-- Is the client IP inside the allowlist? An empty allowlist admits no one. -/
def clientOk (pol : Policy) (ip : Nat) : Bool :=
  pol.allowCidrs.any (fun c => inCidr c ip)

/-- Is the destination permitted? Denylist first, then (under default-deny) the
allowlist; otherwise allowed. -/
def dstOk (pol : Policy) (dst : Dest) : Bool :=
  if pol.denyDst.contains dst then false
  else if pol.defaultDeny then pol.allowDst.contains dst else true

/-- **Admission.** Check the client IP, then the destination, then the cap
(`n` is the client's current concurrent-connection count). The `.admit` outcome
is reached only when all three pass. -/
def admit (pol : Policy) (ip : Nat) (dst : Dest) (n : Nat) : Decision :=
  if clientOk pol ip then
    if dstOk pol dst then
      if n < pol.connCap then .admit
      else .refuse .capReached
    else .refuse .dstBlocked
  else .refuse .clientBlocked

/-! ## Client-IP allowlist -/

/-- An empty allowlist matches no client. -/
theorem client_empty_denies (pol : Policy) (ip : Nat) (h : pol.allowCidrs = []) :
    clientOk pol ip = false := by
  simp [clientOk, h]

/-- **Empty allowlist ⇒ nothing is admitted.** -/
theorem acl_empty_allowlist_denies (pol : Policy) (ip : Nat) (dst : Dest) (n : Nat)
    (h : pol.allowCidrs = []) : admit pol ip dst n ≠ .admit := by
  have hc := client_empty_denies pol ip h
  simp [admit, hc]

/-! ## Default-deny on destinations -/

/-- Under default-deny, a destination not on the allowlist fails the check. -/
theorem dstOk_default_deny {pol : Policy} {dst : Dest}
    (hdd : pol.defaultDeny = true) (hun : pol.allowDst.contains dst = false) :
    dstOk pol dst = false := by
  unfold dstOk
  by_cases hden : pol.denyDst.contains dst = true
  · simp [hden]
  · simp only [Bool.not_eq_true] at hden
    simp [hden, hdd, hun]

/-- **Default-deny refuses unlisted destinations.** With `defaultDeny` set, a
destination absent from the allowlist is never admitted, for any client or
connection count. -/
theorem acl_default_deny {pol : Policy} {ip : Nat} {dst : Dest} {n : Nat}
    (hdd : pol.defaultDeny = true) (hun : pol.allowDst.contains dst = false) :
    admit pol ip dst n ≠ .admit := by
  have hdo := dstOk_default_deny hdd hun
  by_cases hc : clientOk pol ip = true
  · simp [admit, hc, hdo]
  · simp only [Bool.not_eq_true] at hc
    simp [admit, hc]

/-! ## Per-client connection cap -/

/-- **Admission implies headroom.** If a connection is admitted, the client was
strictly below the cap. -/
theorem admit_under_cap {pol : Policy} {ip : Nat} {dst : Dest} {n : Nat}
    (h : admit pol ip dst n = .admit) : n < pol.connCap := by
  unfold admit at h
  by_cases hc : clientOk pol ip = true
  · by_cases hd : dstOk pol dst = true
    · by_cases hn : n < pol.connCap
      · exact hn
      · simp [hc, hd, hn] at h
    · simp only [Bool.not_eq_true] at hd; simp [hc, hd] at h
  · simp only [Bool.not_eq_true] at hc; simp [hc] at h

/-- A connection event for one client: `start` attempts to open to a destination,
`stop` closes one connection. -/
inductive CEv where
  | start (dst : Dest)
  | stop
deriving Repr

/-- Opening a connection increments the count only if the attempt is admitted. -/
def openStep (pol : Policy) (ip : Nat) (dst : Dest) (n : Nat) : Nat :=
  if admit pol ip dst n = .admit then n + 1 else n

/-- **One open never breaches the cap.** If the count is within the cap, it
remains within the cap after an open attempt. -/
theorem openStep_le_cap {pol : Policy} {ip : Nat} {dst : Dest} {n : Nat}
    (hn : n ≤ pol.connCap) : openStep pol ip dst n ≤ pol.connCap := by
  unfold openStep
  by_cases h : admit pol ip dst n = .admit
  · rw [if_pos h]; exact admit_under_cap h
  · rw [if_neg h]; exact hn

/-- Apply one connection event to a client's count. -/
def cstep (pol : Policy) (ip : Nat) (n : Nat) : CEv → Nat
  | .start dst => openStep pol ip dst n
  | .stop => n - 1

/-- The client's concurrent-connection count after a sequence of events. -/
def crun (pol : Policy) (ip : Nat) (n : Nat) (evs : List CEv) : Nat :=
  evs.foldl (cstep pol ip) n

/-- **The per-client concurrent-connection cap is never exceeded.** Starting
from any count within the cap, no sequence of open/close events drives the
client's concurrent-connection count above `connCap` — admission gates every
increment, and closes only decrement. -/
theorem acl_conn_cap (pol : Policy) (ip : Nat) (evs : List CEv) :
    ∀ n, n ≤ pol.connCap → crun pol ip n evs ≤ pol.connCap := by
  unfold crun
  induction evs with
  | nil => intro n hn; simpa using hn
  | cons e es ih =>
    intro n hn
    rw [List.foldl_cons]
    apply ih
    cases e with
    | start dst => exact openStep_le_cap hn
    | stop => exact Nat.le_trans (Nat.sub_le n 1) hn

/-- **Corollary.** A client that starts with no open connections never exceeds
the cap. -/
theorem acl_conn_cap_from_zero (pol : Policy) (ip : Nat) (evs : List CEv) :
    crun pol ip 0 evs ≤ pol.connCap :=
  acl_conn_cap pol ip evs 0 (Nat.zero_le _)

end AccessControlProxy
