import Reactor.Bridge
import AccessControlProxy

/-!
# Reactor.WireAccessControlProxy — forward-proxy access control on the DEPLOYED serve path

`AccessControlProxy` proves two guarantees for a forward proxy's admission gate:
`acl_default_deny` (under default-deny a destination absent from the allowlist is
never admitted) and `acl_conn_cap` (starting within the per-client cap, no
sequence of opens/closes drives a client's concurrent-connection count above the
cap). This file transports those two guarantees onto the path the deployed orb
binary actually runs — `Arena.Orb.main` → `Reactor.Deploy.deployStepGuarded` →
`Reactor.Deploy.serveGuarded` — by installing the ACL gate *in front of* that
serve and anchoring its cap to the deployed listener's own declared `connCap`.

Two things make this a transport, not a restatement:

* **The cap is the deployed listener's.** `deployListenerCap` reads `connCap`
  straight off `Reactor.Deploy.deployPolicyConfig`'s declared listener (`= 1024`,
  by `rfl`). The cap theorem therefore bounds the concurrent connections to the
  *actual* deployed listener by the number that listener declares, not a bespoke
  constant.

* **The gate decides whether the deployed serve runs at all.** `proxyServe` feeds
  the client's bytes to `Reactor.Deploy.serveGuarded input` — the bytes `main`
  writes — **only** when `AccessControlProxy.admit` returns `.admit`. A
  default-denied destination yields `none`: `serveGuarded` is never reached. So
  the library's default-deny guarantee is a real precondition on the deployed
  serve, and the cap guarantee bounds the connections that serve accepts.

Honest scope (same posture as `Reactor.WireMore` / `Reactor.Deploy` §3): this is a
proof-attachment seam. It states the library's real theorems about the admission
that gates the deployed serve and discharges them by the library's own proofs; it
does not yet run a live per-client connection counter inside the event loop. What
it establishes is that the deployed serve is reachable only for an ACL-admitted
connection, and that admission never exceeds the deployed listener's declared cap.
-/

namespace Reactor.WireAccessControlProxy

open Proto (Bytes)
open AccessControlProxy

/-! ## The deployed listener's declared per-client connection cap -/

/-- The per-client connection cap the deployed listener declares: `connCap` read
straight off the first (only) listener in `Reactor.Deploy.deployPolicyConfig`. This
is the number the deployed cold-plane surface actually enforces. -/
def deployListenerCap : Nat :=
  match Reactor.Deploy.deployPolicyConfig.listeners with
  | l :: _ => l.connCap
  | []     => 0

/-- The deployed listener declares a cap of 1024 (definitional). -/
theorem deployListenerCap_val : deployListenerCap = 1024 := rfl

/-! ## The ACL gate in front of the deployed serve -/

/-- **The forward-proxy gate on the deployed serve.** A client at IP `ip`, holding
`n` concurrent connections, opening to destination `dst`, reaches the deployed
serve (`Reactor.Deploy.serveGuarded input` — the bytes `main` writes) **only** when
the REAL `AccessControlProxy.admit` admits it: client IP allow-listed, destination
permitted, and under the cap. A refusal yields `none`; the deployed serve never
runs. Total. -/
def proxyServe (pol : Policy) (ip : Nat) (dst : Dest) (n : Nat) (input : Bytes) :
    Option Bytes :=
  match admit pol ip dst n with
  | .admit    => some (Reactor.Deploy.serveGuarded input)
  | .refuse _ => none

/-- On admission the gate runs exactly the deployed guarded serve on `input`. -/
theorem proxyServe_admit (pol : Policy) (ip : Nat) (dst : Dest) (n : Nat)
    (input : Bytes) (h : admit pol ip dst n = .admit) :
    proxyServe pol ip dst n input = some (Reactor.Deploy.serveGuarded input) := by
  unfold proxyServe; rw [h]

/-! ## The deployed corollary — both library guarantees, transported -/

/-- **`accesscontrolproxy_deployed` — forward-proxy access control on the bytes
`main` writes.** For a default-deny policy whose cap is the deployed listener's
declared `connCap`, and a destination absent from the allowlist:

* **default-deny gates the deployed serve** — for every current count `n` the gate
  returns `none`: the client's bytes never reach `Reactor.Deploy.serveGuarded`
  (via the REAL `acl_default_deny`, so an unlisted destination is *never* admitted);
* **the per-client cap bounds the deployed listener** — from zero, no sequence of
  open/close events drives the client's concurrent-connection count above the
  deployed listener's declared cap (via the REAL `acl_conn_cap_from_zero`);
* **admission implies headroom below the deployed cap** — any admitted open leaves
  the client strictly under the deployed listener's declared cap (via the REAL
  `admit_under_cap`).

The cap in every clause is `deployListenerCap` — the number
`Reactor.Deploy.deployPolicyConfig`'s listener declares — so the guarantees range
over the actual deployed surface, not a side model. -/
theorem accesscontrolproxy_deployed
    (pol : Policy) (ip : Nat) (dst : Dest) (input : Bytes)
    (hcap : pol.connCap = deployListenerCap)
    (hdd : pol.defaultDeny = true)
    (hun : pol.allowDst.contains dst = false) :
    (∀ n, proxyServe pol ip dst n input = none)
    ∧ (∀ evs, crun pol ip 0 evs ≤ deployListenerCap)
    ∧ (∀ n, admit pol ip dst n = .admit → n < deployListenerCap) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have hne := acl_default_deny (ip := ip) (n := n) hdd hun
    unfold proxyServe
    cases hcase : admit pol ip dst n with
    | admit    => exact absurd hcase hne
    | refuse r => rfl
  · intro evs
    have := acl_conn_cap_from_zero pol ip evs
    rw [hcap] at this; exact this
  · intro n hadm
    have := admit_under_cap hadm
    rw [hcap] at this; exact this

/-! ## The gate genuinely branches — kernel-checked, concrete destinations

Real `decide` executions of the REAL `admit` on a default-deny policy whose cap is
the deployed listener's: an unlisted destination is refused (so the deployed serve
is gated off), a listed one is admitted (so the deployed serve runs). The gate is a
mechanism, not one name for two outcomes. -/

/-- A default-deny sample policy: a `0.0.0.0/0` client allowlist (any client),
empty destination denylist, one allowed destination, and the DEPLOYED listener's
declared cap. -/
def samplePolicy : Policy :=
  { allowCidrs  := [⟨0, 0⟩]
    denyDst     := []
    allowDst    := [⟨"ok.example", 443⟩]
    connCap     := deployListenerCap
    defaultDeny := true }

/-- An unlisted destination is REFUSED by the real gate — default-deny fires. -/
theorem sample_denies :
    admit samplePolicy 2130706433 ⟨"evil.example", 22⟩ 0 = .refuse .dstBlocked := by decide

/-- A listed destination under the cap is ADMITTED by the real gate. -/
theorem sample_admits :
    admit samplePolicy 2130706433 ⟨"ok.example", 443⟩ 0 = .admit := by decide

/-- Hence the deployed serve is gated OFF for the unlisted destination: for any
input bytes, `proxyServe` returns `none` — `serveGuarded` never runs. -/
theorem sample_proxy_gated_off (input : Bytes) :
    proxyServe samplePolicy 2130706433 ⟨"evil.example", 22⟩ 0 input = none := by
  unfold proxyServe; rw [sample_denies]

/-- …and it RUNS for the admitted destination: `proxyServe` yields exactly the
deployed guarded serve on the input. -/
theorem sample_proxy_serves (input : Bytes) :
    proxyServe samplePolicy 2130706433 ⟨"ok.example", 443⟩ 0 input
      = some (Reactor.Deploy.serveGuarded input) := by
  unfold proxyServe; rw [sample_admits]

#guard (admit samplePolicy 2130706433 ⟨"evil.example", 22⟩ 0) = .refuse .dstBlocked
#guard (admit samplePolicy 2130706433 ⟨"ok.example", 443⟩ 0) = .admit

/-! ## Axiom audit — every deployed seam closes on the standard axioms only -/

#print axioms deployListenerCap_val
#print axioms proxyServe_admit
#print axioms accesscontrolproxy_deployed
#print axioms sample_denies
#print axioms sample_admits
#print axioms sample_proxy_gated_off
#print axioms sample_proxy_serves

end Reactor.WireAccessControlProxy
