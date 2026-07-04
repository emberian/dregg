/-
JwtValidCorrect — JWT bearer-token validation *correctness*: a refinement of
`Jwt.authenticate` against an independent specification of the RFC validation
rule.

`Jwt.lean` proves SAFETY-flavoured facts about `authenticate`: an admit forces a
verified signature (`jwt_rejects_bad_sig`), a key-pinned non-`none` algorithm
(`jwt_alg_confusion_safe`), an unexpired token (`jwt_rejects_expired`), and the
issuer/audience policy (`jwt_claims_checked`). Each is a one-directional
*necessary condition* on an admit. Individually they do not say the machine
admits EXACTLY the tokens the RFC calls valid: a degenerate decision that
additionally rejected some perfectly valid token would still satisfy every one
of them (they only constrain the admit branch, never force it).

This file closes that gap with a single biconditional. It defines, *without any
reference to* `authenticate`, `afterKey`, or the Bool helpers `notExpired` /
`issOk` / `critOk` / `temporalOk` / `claimsOk`, what makes a decoded token
valid — a structure `RfcValid` of nine plain logical conditions transcribed
directly from the RFCs (∈, ≤, =), the JWS validation of RFC 7515 §5.2 step 8
plus the claim checks of RFC 7519 §4.1. The correctness theorem
`afterKey_admits_iff` proves the machine's post-key decision admits a token IFF
that RFC predicate holds, in BOTH directions; `authenticate_admits_iff` lifts it
across the (boundary) extract/parse/key-selection plumbing to the whole decision.

RFC basis.
  * RFC 7515 §5.2 step 8 — the signature is validated in the manner defined for
    the algorithm, which MUST be accurately represented by `alg`; combined with
    RFC 7518 §3.6 / §8.5 (the unsecured `none` MUST NOT be accepted by default),
    validity requires a non-`none` algorithm equal to the selected key's own
    algorithm (`algSecured`, `algPinned`) and a verifying signature
    (`sigVerified`).
  * RFC 7515 §4.1.11 — every extension parameter named in `crit` MUST be
    understood by the recipient (`critUnderstood`).
  * RFC 7519 §4.1.4 `exp` — the current time MUST be before expiry, modulo a
    small clock-skew leeway (`notExpired`: `now ≤ exp + skew`).
  * RFC 7519 §4.1.5 `nbf` — the token MUST NOT be accepted before `nbf`, modulo
    skew (`notBefore`: `nbf ≤ now + skew`).
  * RFC 7519 §4.1.6 `iat` — the issued-at time, checked not to lie in the future
    beyond skew (`iatSane`: `iat ≤ now + skew`).
  * RFC 7519 §4.1.1 `iss` / §4.1.3 `aud` — when the server pins an issuer the
    token's `iss` MUST equal it (`issMatches`); when it requires an audience,
    that audience MUST appear in the token's `aud` (`audMatches`).

Non-vacuity. The biconditional has teeth in both directions:
  * `→` is strictly stronger than the safety theorems — it re-derives
    `jwt_alg_confusion_safe` and `jwt_rejects_expired` as immediate corollaries
    (`confusion_safe_via_spec`, `rejects_expired_via_spec`). An implementation
    that TRUSTED the token's `alg` (the classic RS256/HS256 confusion) or that
    SKIPPED the `exp` check would admit a token for which `RfcValid` is false,
    breaking `→`.
  * `←` forces the admit branch: dropping any single conjunct from the machine
    (e.g. never checking `exp`) makes some token with `RfcValid` false still
    admit, contradicting `→`; conversely a machine that spuriously rejected a
    valid token would break `←`.
  * A concrete distinguishing witness (`spec_true_admits` / `spec_false_rejects`
    / `expired_flips_decision`) exhibits one fixed token that the same machine
    ADMITS at a clock where `RfcValid` holds and REJECTS one second past expiry,
    where `RfcValid` fails — so the specification is contingent, not a constant,
    and the machine tracks it exactly.
-/

import Jwt

namespace JwtValidCorrect

open Jwt

/-! ## Independent specification of the RFC validation predicate

Every field is a plain logical proposition read off the RFC text. None of them
mentions `authenticate`, `afterKey`, or the machine's Bool helpers; the only
shared symbol is `Config.sigValid`, the uninterpreted cryptographic trust
boundary itself (RFC 7515 §5.2 step 8), which is a parameter of the problem, not
part of the implementation's control flow. -/

/-- **The RFC validation predicate.** A decoded compact JWS `jws`, verified under
the selected `key` at clock `now`, is valid exactly when all nine conditions
hold. Stated directly from RFC 7515 §5.2 / §4.1.11 and RFC 7519 §4.1. -/
structure RfcValid (cfg : Config) (now : Nat) (jws : Jws) (key : Key) : Prop where
  /-- RFC 7518 §3.6 / §8.5: the unsecured `none` algorithm is not acceptable. -/
  algSecured : jws.header.alg ≠ Alg.none
  /-- RFC 7515 §5.2 step 8: the verification algorithm is the selected key's own
  algorithm, never one taken on trust from the token. -/
  algPinned : jws.header.alg = key.alg
  /-- RFC 7515 §4.1.11: every `crit` extension name is understood. -/
  critUnderstood : ∀ name, name ∈ jws.header.crit → name ∈ cfg.understoodCrit
  /-- RFC 7515 §5.2 step 8: the signature verifies under the pinned key/alg. -/
  sigVerified :
    cfg.sigValid jws.header.alg key.material jws.signingInput jws.signature = true
  /-- RFC 7519 §4.1.4: the token is not expired (with clock-skew leeway). -/
  notExpired : ∀ e, jws.claims.exp = some e → now ≤ e + cfg.skew
  /-- RFC 7519 §4.1.5: the token is already valid (with clock-skew leeway). -/
  notBefore : ∀ n, jws.claims.nbf = some n → n ≤ now + cfg.skew
  /-- RFC 7519 §4.1.6: the issued-at time is not in the future beyond skew. -/
  iatSane : ∀ i, jws.claims.iat = some i → i ≤ now + cfg.skew
  /-- RFC 7519 §4.1.1: the token's issuer matches the pinned one, when required. -/
  issMatches : ∀ want, cfg.expectedIss = some want → jws.claims.iss = some want
  /-- RFC 7519 §4.1.3: the required audience appears in the token, when required. -/
  audMatches : ∀ want, cfg.requiredAud = some want → want ∈ jws.claims.aud

/-! ## Bridging the machine's Bool gates to the specification's propositions

Each lemma shows one Bool helper of the implementation equals `true` exactly when
the corresponding RFC proposition holds. These are the non-trivial content: they
say the machine's chosen encoding really decides the RFC condition. -/

theorem critOk_iff (cfg : Config) (h : Header) :
    critOk cfg h = true ↔ ∀ name, name ∈ h.crit → name ∈ cfg.understoodCrit := by
  unfold critOk
  rw [List.all_eq_true]
  constructor
  · intro hall name hmem
    have := hall name hmem
    exact (List.contains_iff_mem).1 this
  · intro hall name hmem
    exact (List.contains_iff_mem).2 (hall name hmem)

theorem notExpired_iff (skew now : Nat) (exp : Option Nat) :
    notExpired skew now exp = true ↔ ∀ e, exp = some e → now ≤ e + skew := by
  cases exp with
  | none => simp [notExpired]
  | some e => simp [notExpired]

theorem notBefore_iff (skew now : Nat) (nbf : Option Nat) :
    notBefore skew now nbf = true ↔ ∀ n, nbf = some n → n ≤ now + skew := by
  cases nbf with
  | none => simp [notBefore]
  | some n => simp [notBefore]

theorem iatSane_iff (skew now : Nat) (iat : Option Nat) :
    iatSane skew now iat = true ↔ ∀ i, iat = some i → i ≤ now + skew := by
  cases iat with
  | none => simp [iatSane]
  | some i => simp [iatSane]

theorem issOk_iff (cfg : Config) (iss : Option String) :
    issOk cfg iss = true ↔ ∀ want, cfg.expectedIss = some want → iss = some want := by
  unfold issOk
  cases hEx : cfg.expectedIss with
  | none => simp
  | some want =>
    cases iss with
    | none => simp
    | some got => simp [eq_comm]

theorem audOk_iff (cfg : Config) (aud : List String) :
    audOk cfg aud = true ↔ ∀ want, cfg.requiredAud = some want → want ∈ aud := by
  unfold audOk
  cases hReq : cfg.requiredAud with
  | none => simp
  | some want => simp [List.contains_iff_mem]

/-- The composite temporal gate decides all three RFC time conditions. -/
theorem temporalOk_iff (cfg : Config) (now : Nat) (c : Claims) :
    temporalOk cfg now c = true ↔
      (∀ e, c.exp = some e → now ≤ e + cfg.skew) ∧
      (∀ n, c.nbf = some n → n ≤ now + cfg.skew) ∧
      (∀ i, c.iat = some i → i ≤ now + cfg.skew) := by
  unfold temporalOk
  rw [Bool.and_eq_true, Bool.and_eq_true,
      notExpired_iff, notBefore_iff, iatSane_iff]
  exact and_assoc

/-- The composite claims gate decides both RFC registered-claim conditions. -/
theorem claimsOk_iff (cfg : Config) (c : Claims) :
    claimsOk cfg c = true ↔
      (∀ want, cfg.expectedIss = some want → c.iss = some want) ∧
      (∀ want, cfg.requiredAud = some want → want ∈ c.aud) := by
  unfold claimsOk
  rw [Bool.and_eq_true, issOk_iff, audOk_iff]

/-! ## The core refinement: the post-key decision admits IFF the token is RFC-valid -/

/-- **`afterKey` refines the RFC predicate.** Given a decoded token and its
selected key, the machine reaches an admit outcome if and only if the token
satisfies every RFC validation condition. Both directions. -/
theorem afterKey_admits_iff (cfg : Config) (ctx : Ctx) (jws : Jws) (key : Key) :
    (∃ hdrs, afterKey cfg ctx jws key = .admit hdrs) ↔ RfcValid cfg ctx.now jws key := by
  constructor
  · rintro ⟨hdrs, hadm⟩
    obtain ⟨a1, a2, hcr, hs, ht, hcl, -⟩ := afterKey_admit cfg ctx jws key hadm
    obtain ⟨he, hn, hi⟩ := (temporalOk_iff cfg ctx.now jws.claims).1 ht
    obtain ⟨hiss, haud⟩ := (claimsOk_iff cfg jws.claims).1 hcl
    exact ⟨a1, a2, (critOk_iff cfg jws.header).1 hcr, hs, he, hn, hi, hiss, haud⟩
  · intro hv
    have hcr : critOk cfg jws.header = true :=
      (critOk_iff cfg jws.header).2 hv.critUnderstood
    have ht : temporalOk cfg ctx.now jws.claims = true :=
      (temporalOk_iff cfg ctx.now jws.claims).2 ⟨hv.notExpired, hv.notBefore, hv.iatSane⟩
    have hcl : claimsOk cfg jws.claims = true :=
      (claimsOk_iff cfg jws.claims).2 ⟨hv.issMatches, hv.audMatches⟩
    refine ⟨inject jws.claims, ?_⟩
    unfold afterKey
    rw [if_neg hv.algSecured, if_neg (fun h => h hv.algPinned),
        if_neg (by rw [hcr]; exact Bool.noConfusion), if_pos hv.sigVerified,
        if_pos ht, if_pos hcl]

/-! ## Lifting to the whole decision -/

/-- **The RFC admit condition for a whole request.** The request yields (through
the decode/parse/key-lookup boundary — RFC 7515 §5.2 steps 1-7, §4.1.4) a token
and key for which the RFC validation predicate holds. -/
def RfcAdmits (cfg : Config) (ctx : Ctx) : Prop :=
  ∃ raw jws key,
    extract cfg ctx.req = some raw ∧
    parse cfg raw = some jws ∧
    selectKey cfg jws.header = some key ∧
    RfcValid cfg ctx.now jws key

/-- **`authenticate` refines the RFC predicate.** The whole request-authentication
decision admits IFF a token can be extracted, parsed, and keyed, and that token
is RFC-valid. Both directions. -/
theorem authenticate_admits_iff (cfg : Config) (ctx : Ctx) :
    (∃ hdrs, authenticate cfg ctx = .admit hdrs) ↔ RfcAdmits cfg ctx := by
  constructor
  · rintro ⟨hdrs, hadm⟩
    obtain ⟨raw, jws, key, hex, hp, hk, ha⟩ := authenticate_admit cfg ctx hadm
    exact ⟨raw, jws, key, hex, hp, hk,
      (afterKey_admits_iff cfg ctx jws key).1 ⟨hdrs, ha⟩⟩
  · rintro ⟨raw, jws, key, hex, hp, hk, hv⟩
    obtain ⟨hdrs, ha⟩ := (afterKey_admits_iff cfg ctx jws key).2 hv
    exact ⟨hdrs, by simp only [authenticate, hex, hp, hk]; exact ha⟩

/-! ## Non-vacuity, part 1: the biconditional subsumes the safety theorems

The `→` direction is strictly stronger than the hand-proved safety lemmas — it
re-derives them. An implementation that trusted the token `alg` or skipped `exp`
would admit a token whose `RfcValid` is false, so it could not satisfy `→`. -/

/-- Algorithm-confusion safety, obtained purely from the refinement. -/
theorem confusion_safe_via_spec (cfg : Config) (ctx : Ctx)
    {hdrs : List (String × String)} (h : authenticate cfg ctx = .admit hdrs) :
    ∃ (jws : Jws) (key : Key), selectKey cfg jws.header = some key ∧
      jws.header.alg ≠ Alg.none ∧ jws.header.alg = key.alg := by
  obtain ⟨_, jws, key, _, _, hk, hv⟩ := (authenticate_admits_iff cfg ctx).1 ⟨hdrs, h⟩
  exact ⟨jws, key, hk, hv.algSecured, hv.algPinned⟩

/-- Expiry safety, obtained purely from the refinement. -/
theorem rejects_expired_via_spec (cfg : Config) (ctx : Ctx)
    {hdrs : List (String × String)} (h : authenticate cfg ctx = .admit hdrs) :
    ∃ (jws : Jws) (key : Key), selectKey cfg jws.header = some key ∧
      ∀ e, jws.claims.exp = some e → ctx.now ≤ e + cfg.skew := by
  obtain ⟨_, jws, key, _, _, hk, hv⟩ := (authenticate_admits_iff cfg ctx).1 ⟨hdrs, h⟩
  exact ⟨jws, key, hk, hv.notExpired⟩

/-! ## Non-vacuity, part 2: a concrete token whose decision flips with the clock

The specification is contingent — neither always true nor always false — and the
machine tracks it exactly. Below, one fixed token verifies against a demo config
whose signature boundary accepts; at a clock inside the token's validity window
`RfcValid` holds and the machine admits, and one second past expiry `RfcValid`
fails and the machine rejects. A machine that ignored `exp` could not produce
this flip. -/

/-- A demo config: one HS256 key, signature boundary always accepts, no issuer or
audience pinned, no skew. -/
def demoCfg : Config where
  keys := [{ kid := "k1", alg := Alg.hs256, material := ⟨0⟩ }]
  sources := [.bearer]
  skew := 0
  expectedIss := none
  requiredAud := none
  understoodCrit := []
  parseBearer := fun _ => none
  segments := fun _ => []
  decodeHeader := fun _ => none
  decodeClaims := fun _ => none
  decodeSig := fun _ => none
  signingInput := fun _ _ => []
  verifyHmac := fun _ _ _ _ => true
  verifyRsaPkcs1 := fun _ _ _ _ => false
  verifyRsaPss := fun _ _ _ _ => false
  verifyEcdsa := fun _ _ _ _ => false
  edPubKey := fun _ => []

/-- The demo key. -/
def demoKey : Key := { kid := "k1", alg := Alg.hs256, material := ⟨0⟩ }

/-- One fixed token, expiring at `t = 100`. -/
def demoJws : Jws where
  header := { alg := Alg.hs256, kid := some "k1", crit := [] }
  claims := { iss := none, sub := none, aud := [], exp := some 100, nbf := none, iat := none }
  signingInput := []
  signature := [1]

/-- Inside the window (`now = 100 ≤ exp`), the RFC predicate holds. -/
theorem spec_true_admits :
    RfcValid demoCfg 100 demoJws demoKey where
  algSecured := by decide
  algPinned := rfl
  critUnderstood := by intro name h; simp [demoJws] at h
  sigVerified := rfl
  notExpired := by intro e he; simp [demoJws] at he; subst he; decide
  notBefore := by intro n h; simp [demoJws] at h
  iatSane := by intro i h; simp [demoJws] at h
  issMatches := by intro want h; simp [demoCfg] at h
  audMatches := by intro want h; simp [demoCfg] at h

/-- Past expiry (`now = 101 > exp = 100`), the RFC predicate fails. -/
theorem spec_false_rejects :
    ¬ RfcValid demoCfg 101 demoJws demoKey := by
  intro hv
  have h : (101 : Nat) ≤ 100 + 0 := hv.notExpired 100 rfl
  omega

/-- The SAME machine admits the token at `t = 100` and rejects it at `t = 101`:
the decision flips exactly with the specification. This is impossible for a
machine that ignores `exp`. -/
theorem expired_flips_decision :
    (∃ hdrs, afterKey demoCfg ⟨⟨none, [], [], []⟩, 100⟩ demoJws demoKey = .admit hdrs) ∧
    afterKey demoCfg ⟨⟨none, [], [], []⟩, 101⟩ demoJws demoKey = .reject .expired := by
  constructor
  · exact (afterKey_admits_iff demoCfg ⟨⟨none, [], [], []⟩, 100⟩ demoJws demoKey).2
      spec_true_admits
  · decide

end JwtValidCorrect

#print axioms JwtValidCorrect.afterKey_admits_iff
#print axioms JwtValidCorrect.authenticate_admits_iff
#print axioms JwtValidCorrect.confusion_safe_via_spec
#print axioms JwtValidCorrect.rejects_expired_via_spec
#print axioms JwtValidCorrect.expired_flips_decision
