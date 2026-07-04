/-
SocksCorrect — SOCKS5 handshake *correctness*: a refinement of the client
handshake FSM (`Socks.hstep`) against an independent specification of the two
decisions RFC 1928 mandates, the METHOD negotiation (§3) and the CONNECT reply
(§4/§6).

`Socks.Handshake` proves SAFETY-flavoured facts about `hstep`: it is total and
deterministic, has no stuck state, `established` is reached only via a success
reply, and the relay gate stays closed until then. Those pin down the *shape* of
the transition system, but on their own they do not say the FSM makes the
decision the RFC dictates: a client that also accepted an unsupported method, or
opened the tunnel on a malformed / non-success reply, could satisfy several of
them in isolation.

This file closes that gap. It defines, *without any reference to* `hstep`,
`parseMethod`, or `parseReply`, what the two decisions SHOULD be:

  * `negotiate` — the METHOD-negotiation outcome (§3): given what the client
    advertised (encoded by `advertised` / the `hasAuth` capability), a selected
    method either drives a direct CONNECT (`0x00`, NO AUTHENTICATION), an
    auth sub-negotiation (`0x02`, USERNAME/PASSWORD — RFC 1929, requires
    credentials), or aborts. Anything the client did not advertise — in
    particular `0xFF`, NO ACCEPTABLE METHODS — aborts.
  * `replyGrants` — the CONNECT-reply grant condition (§6): a reply buffer opens
    the tunnel iff it is a well-formed SOCKS5 reply, `VER=5 REP RSV ATYP
    BND.ADDR BND.PORT` with a parseable BND address, whose `REP` field is
    `X'00'` (succeeded). Any other `REP`, and any malformed reply, grants
    nothing.

The correctness theorems are two equations/equivalences that hold for every
input:

  * `negotiate_refines` — on any greeting that decodes to a method, the FSM's
    transition equals the spec-directed one, `negTransition hasAuth (negotiate
    hasAuth m)`; corollaries `selected_supported` (proceeding implies the method
    was advertised) and `none_acceptable_aborts` (`0xFF` always aborts).
  * `reply_refines` — from `awaitReply`, the FSM reaches `established` iff the
    reply `replyGrants`.

Non-vacuity. The spec is not the implementation renamed, and a wrong client
fails the theorems: `negotiate false 0x02 = .abort` forbids accepting
USERNAME/PASSWORD with no credentials, and `¬ replyGrants` for a `REP=0x01`
reply forbids opening the tunnel on a failure code. The evaluated witnesses at
the end (`neg_no_creds_rejects_userpass`, `reply_failure_no_tunnel`,
`reply_malformed_no_tunnel`, `reply_success_opens`) exhibit concrete inputs on
which any FSM violating the spec would disagree with `hstep`.

RFC basis. RFC 1928 §3: the client sends `VER NMETHODS METHODS`; the server
replies `VER METHOD`, selecting one of the offered methods, or `X'FF'` if none
are acceptable, in which case the client MUST close. RFC 1929 §2: the
USERNAME/PASSWORD method requires a credential sub-negotiation. RFC 1928 §4/§6:
the CONNECT request and reply carry `ATYP ADDR PORT`; a reply's `REP` field is
`X'00'` on success and a nonzero failure code otherwise.
-/

import Socks.Handshake

namespace SocksCorrect

open Socks

/-! ## Independent specification of RFC 1928 §3 method negotiation -/

/-- The three RFC-1928 §3 outcomes of receiving the server's selected METHOD,
from the client's viewpoint: proceed directly to the CONNECT request, run the
USERNAME/PASSWORD auth sub-negotiation first, or abort the handshake. -/
inductive NegOutcome where
  | connect
  | auth
  | abort
deriving DecidableEq, Repr

/-- The methods this client advertises in its greeting (RFC 1928 §3 `METHODS`).
`0x00` (NO AUTHENTICATION) is always offered; `0x02` (USERNAME/PASSWORD) is
offered exactly when credentials are configured. Written independently of the
FSM — it is the client's capability set. -/
def advertised (hasAuth : Bool) : List UInt8 :=
  if hasAuth then [0x00, 0x02] else [0x00]

/-- **The negotiation spec (RFC 1928 §3, RFC 1929 §2).** Given the client's
capability and the server's selected METHOD, the mandated outcome: `0x00` drives
a direct CONNECT; `0x02` requires the auth sub-negotiation, which is only
possible with credentials (else the client cannot proceed and aborts); every
other selection — including `0xFF`, NO ACCEPTABLE METHODS — aborts. Defined by
case on the method byte; it does not consult `hstep` or `parseMethod`. -/
def negotiate (hasAuth : Bool) (selected : UInt8) : NegOutcome :=
  if selected = 0x00 then .connect
  else if selected = 0x02 then (if hasAuth then .auth else .abort)
  else .abort

/-- A method is *negotiable* iff the spec does not abort on it. -/
def negotiable (hasAuth : Bool) (selected : UInt8) : Bool :=
  match negotiate hasAuth selected with
  | .abort => false
  | _ => true

/-- **Negotiable exactly means advertised.** The spec proceeds on precisely the
methods the client offered — nothing more, nothing less. -/
theorem negotiable_iff_advertised (hasAuth : Bool) (m : UInt8) :
    negotiable hasAuth m = true ↔ m ∈ advertised hasAuth := by
  unfold negotiable negotiate advertised
  by_cases h0 : m = 0x00
  · subst h0; cases hasAuth <;> simp
  · by_cases h2 : m = 0x02
    · subst h2; cases hasAuth <;> simp
    · cases hasAuth <;> simp [h0, h2]

/-- `0xFF` (NO ACCEPTABLE METHODS) is never advertised, hence never negotiable:
if the server signals that none of the offered methods are acceptable, the spec
aborts, regardless of client capability. -/
theorem none_acceptable_not_negotiable (hasAuth : Bool) :
    negotiable hasAuth 0xFF = false := by
  cases hasAuth <;> rfl

/-! ## The spec-directed transition, and the negotiation refinement -/

/-- The transition the FSM MUST make from the fresh (`awaitGreeting`) state once
the negotiation outcome is known: `connect` sends the CONNECT request and waits
for the reply; `auth` sends the auth message and waits for its status; `abort`
tears the connection down. Written from the spec outcome alone. -/
def negTransition (hasAuth : Bool) : NegOutcome → HState × Out
  | .connect => (⟨.awaitReply, hasAuth⟩, .sendConnect)
  | .auth    => (⟨.awaitAuth, hasAuth⟩, .sendAuth)
  | .abort   => (⟨.failed, hasAuth⟩, .closeErr)

/-- **Negotiation refinement (RFC 1928 §3).** On any greeting buffer that
decodes to a selected method `m`, the FSM's step from the initial state equals
the transition the spec dictates. The FSM does not implement some other
selection rule: its move is exactly `negTransition hasAuth (negotiate hasAuth
m)`. -/
theorem negotiate_refines (hasAuth : Bool) (buf : Bytes) (m : UInt8) (k : Nat)
    (hm : parseMethod buf = .complete m k) :
    hstep (HState.init hasAuth) buf = negTransition hasAuth (negotiate hasAuth m) := by
  simp only [HState.init, hstep, hm]
  by_cases h0 : m = 0x00
  · subst h0; simp [negotiate, negTransition]
  · by_cases h2 : m = 0x02
    · subst h2; cases hasAuth <;> simp [negotiate, negTransition]
    · simp only [if_neg h0, if_neg h2, negotiate, negTransition]

/-- **The selected method is a supported one.** If the FSM proceeds (does not
land in `failed`) after decoding a method, that method was one the client
advertised. Combined with `none_acceptable_not_negotiable`, this is the RFC's
"the server selects from one of the methods given in METHODS, or `0xFF` if none
are acceptable" read on the client side. -/
theorem selected_supported (hasAuth : Bool) (buf : Bytes) (m : UInt8) (k : Nat)
    (hm : parseMethod buf = .complete m k)
    (hproceed : (hstep (HState.init hasAuth) buf).1.phase ≠ .failed) :
    m ∈ advertised hasAuth := by
  rw [negotiate_refines hasAuth buf m k hm] at hproceed
  rw [← negotiable_iff_advertised]
  unfold negotiable
  cases hn : negotiate hasAuth m with
  | connect => rfl
  | auth => rfl
  | abort => rw [hn, negTransition] at hproceed; exact absurd rfl hproceed

/-- **NO ACCEPTABLE METHODS aborts.** A greeting that decodes to `0xFF` drives
the FSM to `failed`: the client closes, as RFC 1928 §3 requires. -/
theorem none_acceptable_aborts (hasAuth : Bool) (buf : Bytes) (k : Nat)
    (hm : parseMethod buf = .complete 0xFF k) :
    (hstep (HState.init hasAuth) buf).1.phase = .failed := by
  rw [negotiate_refines hasAuth buf 0xFF k hm]
  cases hasAuth <;> rfl

/-! ## Independent specification of the RFC 1928 §6 CONNECT reply -/

/-- **The reply grant condition (RFC 1928 §6).** A server reply is
`VER REP RSV ATYP BND.ADDR BND.PORT`. This buffer *grants the tunnel* iff it is
well-formed — `VER = X'05'`, followed by a `RSV` byte and a parseable BND
address field (`Socks.parseAddr`, the shared RFC §4 address grammar) — and its
`REP` field is `X'00'` (succeeded). The `REP` byte is pinned to `0x00` here:
this is the predicate the client's tunnel decision is measured against, defined
without reference to `parseReply` or `hstep`. -/
def replyGrants (buf : Bytes) : Prop :=
  ∃ rsv rest t c, buf = 0x05 :: 0x00 :: rsv :: rest ∧ parseAddr rest = .complete t c

/-- **Reply refinement (RFC 1928 §6).** From `awaitReply`, the FSM opens the
tunnel (reaches `established`) if and only if the reply `replyGrants`: it is a
well-formed reply whose `REP` field is the success code. The forward direction
forbids opening the tunnel on any failure code or malformed reply; the backward
direction forbids stalling on a genuine grant. -/
theorem reply_refines {s : HState} (buf : Bytes) (hph : s.phase = .awaitReply) :
    (hstep s buf).1.phase = .established ↔ replyGrants buf := by
  obtain ⟨ph, ha⟩ := s
  simp only at hph; subst hph
  constructor
  · intro hpost
    simp only [hstep] at hpost
    cases hp : parseReply buf with
    | incomplete => rw [hp] at hpost; exact absurd hpost (by simp)
    | error => rw [hp] at hpost; exact absurd hpost (by simp)
    | complete code c =>
      rw [hp] at hpost
      by_cases hc0 : code = 0x00
      · -- decoded a success reply; recover the field layout from parseReply
        subst hc0
        match buf, hp with
        | v :: rep :: rsv :: rest, hp =>
          simp only [parseReply] at hp
          by_cases hv : v = 0x05
          · rw [if_pos hv] at hp
            cases hpa : parseAddr rest with
            | incomplete => rw [hpa] at hp; exact absurd hp (by simp)
            | error => rw [hpa] at hp; exact absurd hp (by simp)
            | complete t ca =>
              rw [hpa] at hp
              obtain ⟨hrep, -⟩ := Res.complete.inj hp
              subst hv; subst hrep
              exact ⟨rsv, rest, t, ca, rfl, hpa⟩
          · rw [if_neg hv] at hp; exact absurd hp (by simp)
      · simp only [if_neg hc0] at hpost; exact absurd hpost (by simp)
  · rintro ⟨rsv, rest, t, c, rfl, hpa⟩
    simp [hstep, parseReply, hpa]

/-! ## Non-vacuity witnesses (evaluated) -/

/-- The spec rejects USERNAME/PASSWORD when no credentials are configured: a
client that accepted method `0x02` here would have selected an unusable method.
-/
example : negotiate false 0x02 = NegOutcome.abort := rfl

/-- The FSM agrees: with `hasAuth = false`, a `VER=5 METHOD=0x02` greeting drives
it to `failed`. An FSM that instead advanced would break `negotiate_refines`. -/
theorem neg_no_creds_rejects_userpass :
    (hstep (HState.init false) [0x05, 0x02]).1.phase = Phase.failed := rfl

/-- A `REP=0x01` (general failure) reply does not grant: the FSM stays out of
`established`. An FSM opening the tunnel on a failure code would break the
forward direction of `reply_refines`. -/
theorem reply_failure_no_tunnel :
    (hstep ⟨.awaitReply, false⟩ [0x05, 0x01, 0x00, 0x01, 0, 0, 0, 0, 0, 0]).1.phase
      ≠ Phase.established := by decide

/-- A malformed reply (unknown ATYP `0x09`, so the BND address fails to parse)
does not grant, even with `REP=0x00`: the FSM does not reach `established`. -/
theorem reply_malformed_no_tunnel :
    (hstep ⟨.awaitReply, false⟩ [0x05, 0x00, 0x00, 0x09]).1.phase
      ≠ Phase.established := by decide

/-- A well-formed success reply (`REP=0x00`, IPv4 BND address) grants: the FSM
reaches `established`. -/
theorem reply_success_opens :
    (hstep ⟨.awaitReply, false⟩ [0x05, 0x00, 0x00, 0x01, 0, 0, 0, 0, 0, 0]).1.phase
      = Phase.established := rfl

end SocksCorrect
