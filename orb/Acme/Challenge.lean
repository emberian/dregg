/-
Acme.Challenge — the challenge lifecycle and the two challenge encodings.

Two independent responsibilities live here:

1.  **The challenge FSM** (RFC 8555 §7.1.6, §8): `pending → processing →
    {valid, invalid}`. The client responds to a challenge (`respond`,
    `pending → processing`); the CA then validates it. Validation is the
    *named abstract interface*: a `Bool` result (`validated ok`) the
    environment injects. `ok = true` sends the challenge to `valid`; `ok =
    false` sends it to `invalid`. There is no third door into `valid`.

2.  **The two encodings** (RFC 8555 §8.1, §8.3, §8.4). Both start from the
    key authorization `keyAuthorization = token ‖ "." ‖ thumbprint`.
      * HTTP-01 serves the key authorization *verbatim* at the well-known
        path `/.well-known/acme-challenge/<token>`.
      * DNS-01 publishes `base64url(SHA-256(keyAuthorization))` as a TXT
        record at `_acme-challenge.<domain>`.
    `SHA-256`/`base64url` are folded into a single abstract `digest`
    parameter; every encoding theorem holds for *every* `digest`, so nothing
    about correctness of the path or the published value rests on the
    cryptography.

Theorems:
  * `chal_into_valid` / `chal_fail_not_valid` / `validateStep_valid_needs_success`
    — **no-bypass**: the only transition into `valid` is a *successful*
    validation from `processing`; a failed validation lands in `invalid`.
  * `chal_valid_absorbing` — a valid challenge stays valid.
  * `http01Path_eq` / `http01Path_injective` / `provision_http`
    — **HTTP-01 path correctness**: the key authorization is served at
    exactly `/.well-known/acme-challenge/<token>`, and that path determines
    the token (no cross-serving).
  * `keyAuth_ne_token` — the served content is the key authorization, never
    the bare token (the classic HTTP-01 implementation bug, ruled out).
  * `dns01RecordName_eq` / `dns01RecordName_injective` / `provision_dns`
    — **DNS-01 value correctness**: exactly `digest(keyAuthorization)` is
    published at exactly `_acme-challenge.<domain>`.
-/

import Acme.Basic

namespace Acme

/-! ### Left-cancellation of concatenation

The one general fact the encoding proofs need: a fixed prefix can be peeled
off. Proven here rather than assumed so the development stays core-only. -/

theorem appendLeftCancel {α} :
    ∀ (p : List α) {a b : List α}, p ++ a = p ++ b → a = b
  | [], _, _, h => by simpa using h
  | _ :: xs, _, _, h => by
      simp only [List.cons_append, List.cons.injEq, true_and] at h
      exact appendLeftCancel xs h

/-! ### Key authorization (RFC 8555 §8.1) -/

/-- `keyAuthorization = token ‖ "." ‖ thumbprint`. -/
def keyAuthorization (token thumbprint : Bytes) : Bytes :=
  token ++ ['.'] ++ thumbprint

theorem keyAuth_len (token thumbprint : Bytes) :
    (keyAuthorization token thumbprint).length
      = token.length + 1 + thumbprint.length := by
  simp [keyAuthorization]
  omega

/-- **The key authorization is never the bare token.** Its length exceeds the
token's by at least the separator, so an HTTP-01 responder that serves the key
authorization can never be serving just the token. -/
theorem keyAuth_ne_token (token thumbprint : Bytes) :
    keyAuthorization token thumbprint ≠ token := by
  intro heq
  have hlen := congrArg List.length heq
  rw [keyAuth_len] at hlen
  omega

/-! ### HTTP-01 encoding (RFC 8555 §8.3) -/

/-- The RFC well-known prefix. `/.well-known/acme-challenge/` verbatim. -/
def wellKnownPrefix : Bytes := "/.well-known/acme-challenge/".toList

/-- The HTTP-01 resource path for a token. -/
def http01Path (token : Bytes) : Bytes := wellKnownPrefix ++ token

/-- The path is exactly the RFC prefix followed by the token. -/
theorem http01Path_eq (token : Bytes) :
    http01Path token = wellKnownPrefix ++ token := rfl

/-- **Path correctness / no cross-serving.** The path determines the token:
serving at token `t₁`'s path is serving at token `t₂`'s path only if
`t₁ = t₂`. A responder keyed by path therefore answers each token only at its
own resource. -/
theorem http01Path_injective {t₁ t₂ : Bytes}
    (h : http01Path t₁ = http01Path t₂) : t₁ = t₂ :=
  appendLeftCancel wellKnownPrefix h

/-! ### DNS-01 encoding (RFC 8555 §8.4) -/

/-- The RFC record-name prefix. `_acme-challenge.` verbatim. -/
def dnsLabelPrefix : Bytes := "_acme-challenge.".toList

/-- The DNS-01 record name for a domain. -/
def dns01RecordName (domain : Bytes) : Bytes := dnsLabelPrefix ++ domain

/-- The TXT value: `base64url(SHA-256(keyAuthorization))`, with the crypto
folded into the abstract `digest`. -/
def dns01TxtValue (digest : Bytes → Bytes) (token thumbprint : Bytes) : Bytes :=
  digest (keyAuthorization token thumbprint)

theorem dns01RecordName_eq (domain : Bytes) :
    dns01RecordName domain = dnsLabelPrefix ++ domain := rfl

/-- The record name determines the domain. -/
theorem dns01RecordName_injective {d₁ d₂ : Bytes}
    (h : dns01RecordName d₁ = dns01RecordName d₂) : d₁ = d₂ :=
  appendLeftCancel dnsLabelPrefix h

/-! ### The challenge object and what it provisions -/

/-- One challenge: its type, its token, the identifier (domain) it is for, and
its status. -/
structure Challenge where
  ty : ChallengeType
  token : Bytes
  domain : Bytes
  status : ChalStatus
deriving DecidableEq, Repr

/-- What the responder must place to answer a challenge: an HTTP resource
(path, content) or a DNS record (name, TXT value). -/
inductive Provision where
  | http (path : Bytes) (content : Bytes)
  | dns (name : Bytes) (value : Bytes)
deriving DecidableEq, Repr

/-- The provisioning the responder performs for a challenge, given the
account's `thumbprint` and the crypto `digest`. -/
def Challenge.provision (digest : Bytes → Bytes) (c : Challenge)
    (thumbprint : Bytes) : Provision :=
  match c.ty with
  | .http01 => .http (http01Path c.token) (keyAuthorization c.token thumbprint)
  | .dns01 => .dns (dns01RecordName c.domain) (dns01TxtValue digest c.token thumbprint)

/-- **HTTP-01 provisioning is exactly right.** For an HTTP-01 challenge the
responder serves the key authorization at exactly the well-known path for the
token. -/
theorem provision_http {digest : Bytes → Bytes} {c : Challenge}
    {thumbprint : Bytes} (h : c.ty = .http01) :
    c.provision digest thumbprint
      = .http (wellKnownPrefix ++ c.token)
              (keyAuthorization c.token thumbprint) := by
  simp [Challenge.provision, h, http01Path]

/-- **DNS-01 provisioning is exactly right.** For a DNS-01 challenge the
responder publishes exactly `digest(keyAuthorization)` at exactly the
`_acme-challenge.<domain>` record. -/
theorem provision_dns {digest : Bytes → Bytes} {c : Challenge}
    {thumbprint : Bytes} (h : c.ty = .dns01) :
    c.provision digest thumbprint
      = .dns (dnsLabelPrefix ++ c.domain)
             (digest (keyAuthorization c.token thumbprint)) := by
  simp [Challenge.provision, h, dns01RecordName, dns01TxtValue]

/-! ### The challenge FSM (RFC 8555 §7.1.6, §8.2) -/

/-- Challenge events. `respond` is the client POSTing the challenge (asking the
CA to validate); `validated ok` is the CA's validation result — the named
abstract interface. -/
inductive ChalEvent where
  | respond
  | validated (ok : Bool)
deriving DecidableEq, Repr

/-- The challenge step. Total and deterministic; out-of-order events stutter.
`valid`/`invalid` are absorbing. -/
def Challenge.step (c : Challenge) (e : ChalEvent) : Challenge :=
  match c.status, e with
  | .pending, .respond => { c with status := .processing }
  | .processing, .validated true => { c with status := .valid }
  | .processing, .validated false => { c with status := .invalid }
  | _, _ => c

/-- Totality of the transition relation: every (challenge, event) has a
successor. -/
theorem chalStep_total (c : Challenge) (e : ChalEvent) :
    ∃ c', c.step e = c' := ⟨_, rfl⟩

/-- Determinism: the successor is unique (it is a function). -/
theorem chalStep_deterministic {c : Challenge} {e : ChalEvent} {c₁ c₂ : Challenge}
    (h₁ : c.step e = c₁) (h₂ : c.step e = c₂) : c₁ = c₂ := by
  rw [← h₁, ← h₂]

/-- **No-bypass (into `valid`).** The only way a challenge acquires status
`valid` is: it was already `valid`, or it was `processing` and received a
*successful* validation. No `respond`, no failed validation, no other status
opens that door. -/
theorem chal_into_valid {c : Challenge} {e : ChalEvent}
    (h : (c.step e).status = .valid) :
    c.status = .valid ∨ (c.status = .processing ∧ e = .validated true) := by
  obtain ⟨ty, tok, dom, st⟩ := c
  cases st <;> cases e <;>
    first
      | (rename_i ok; cases ok <;> simp_all [Challenge.step])
      | simp_all [Challenge.step]

/-- **A failed validation never reaches `valid`.** From any non-valid status,
`validated false` cannot produce a valid challenge (it produces `invalid` from
`processing`, and stutters elsewhere). -/
theorem chal_fail_not_valid {c : Challenge} (h : c.status ≠ .valid) :
    (c.step (.validated false)).status ≠ .valid := by
  obtain ⟨ty, tok, dom, st⟩ := c
  cases st <;> simp_all [Challenge.step]

/-- A failed validation of a `processing` challenge lands in `invalid`
specifically. -/
theorem chal_fail_to_invalid {c : Challenge} (h : c.status = .processing) :
    (c.step (.validated false)).status = .invalid := by
  obtain ⟨ty, tok, dom, st⟩ := c
  simp_all [Challenge.step]

/-- **A valid challenge stays valid** — every event stutters. -/
theorem chal_valid_absorbing {c : Challenge} (h : c.status = .valid)
    (e : ChalEvent) : c.step e = c := by
  obtain ⟨ty, tok, dom, st⟩ := c
  simp only at h; subst h
  cases e <;> rfl

/-- An `invalid` challenge stays invalid. -/
theorem chal_invalid_absorbing {c : Challenge} (h : c.status = .invalid)
    (e : ChalEvent) : c.step e = c := by
  obtain ⟨ty, tok, dom, st⟩ := c
  simp only at h; subst h
  cases e <;> rfl

/-! ### The validation interface, tied in

`validateStep` draws the challenge's fate from an abstract validator
`validate : Challenge → Bool` — the model's stand-in for the CA's HTTP fetch
(§8.3) or DNS lookup (§8.4). It only acts on a `processing` challenge, so a
challenge cannot be validated before the client has responded. -/

def Challenge.validateStep (validate : Challenge → Bool) (c : Challenge) :
    Challenge :=
  match c.status with
  | .processing => c.step (.validated (validate c))
  | _ => c

/-- **A challenge reaches `valid` through the validator only when the
validator succeeds.** If a `processing` challenge becomes `valid` under
`validateStep`, then `validate c = true`. There is no bypass of the
(axiomatized) validation. -/
theorem validateStep_valid_needs_success {validate : Challenge → Bool}
    {c : Challenge} (hp : c.status = .processing)
    (hv : (c.validateStep validate).status = .valid) : validate c = true := by
  obtain ⟨ty, tok, dom, st⟩ := c
  simp only at hp; subst hp
  cases hb : validate ⟨ty, tok, dom, .processing⟩ with
  | true => rfl
  | false =>
      simp [Challenge.validateStep, Challenge.step, hb] at hv

/-- Dually: a failing validator sends a `processing` challenge to `invalid`,
never `valid`. -/
theorem validateStep_fail_invalid {validate : Challenge → Bool}
    {c : Challenge} (hp : c.status = .processing)
    (hf : validate c = false) :
    (c.validateStep validate).status = .invalid := by
  obtain ⟨ty, tok, dom, st⟩ := c
  simp only at hp; subst hp
  simp [Challenge.validateStep, Challenge.step, hf]

end Acme
