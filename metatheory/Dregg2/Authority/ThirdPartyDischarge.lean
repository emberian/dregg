/-
# Dregg2.Authority.ThirdPartyDischarge — the REAL third-party discharge protocol.

The existing `Authority.Discharge` models the *await* authority-face at the granularity of a
**Bool flip**: a gateway is `Discharges g = true` or not, and admissibility resolves forward.
That is the correct *monotonicity* law, but it is a **shadow** of the actual Rust protocol — it
throws away the cryptographic substance that makes a discharge *unforgeable* and *non-replayable*.

This module carries the **REAL** protocol from the Rust, faithfully, citing it line-by-line:

  • `macaroon/src/caveat_3p.rs:33-46` — a `ThirdPartyCaveat` stores `(location, verifier_key, ticket)`:
       - `ticket  = seal(K_A, {discharge_key r, caveats_for_3p})`   (caveat_3p.rs:80-89)
       - `verifier_key (VID) = seal(current_tail, r)`               (caveat_3p.rs:91-92)
    so ONLY the 3P (holding `K_A`) recovers the ticket, and ONLY the verifier (who can replay the
    HMAC chain to `current_tail`) recovers `r` (`caveat_3p.rs:39-45`, `:117-141`).
  • `macaroon/src/macaroon.rs:383-404` (`create_discharge`) — the 3P mints a discharge macaroon
    keyed by the recovered `r`, stamping `created_at = now` into the nonce (`:392-396`).
  • `macaroon/src/macaroon.rs:341-347` (`bind_discharge`) — BIND-TO-PARENT: append a
    `CAV_BIND_TO_PARENT` caveat whose body is `binding_hash(root_tail) = SHA256(root_tail)`
    (`:342`), extending the discharge's HMAC chain (`:345`).
  • `macaroon/src/macaroon.rs:267-332` (`verify_discharge`) — ACCEPTANCE requires, in order:
       (FRESH)  `created_at ≠ 0`  (`:275-279`, fail-closed) AND `0 ≤ now-created_at ≤ 300`
                (`:284-289`, `MAX_DISCHARGE_AGE = 300` at `:35`);
       (CHAIN)  replay the HMAC chain from `r` over the discharge's caveats and constant-time
                compare to the stored tail (`:294-318`, `:320-322`) — this is what proves the 3P
                actually checked its predicate / the caveats are intact;
       (BOUND)  a `CAV_BIND_TO_PARENT` caveat must be present AND its body must equal
                `binding_hash(expected_parent_tail)` (`:300-307`); a MISMATCH is `DischargeUnbound`
                (`:306`), and ABSENCE is `DischargeUnbound` fail-closed even for empty discharges
                (`:324-329`).

## What is REAL here vs the §8 portal

FAITHFULLY MODELED (the protocol logic, grounded above):
  - the ticket/VID two-key split and who-can-decrypt-what (recovery of `r`);
  - the HMAC-chain replay that authenticates the discharge body under `r`;
  - the three-conjunct acceptance gate (fresh ∧ chain-valid ∧ bound-to-the-right-parent);
  - the TEETH: a replayed (stale) discharge and a cross-bound (wrong-parent) discharge are REJECTED.

§8 PROP-PORTAL (NEVER faked as proved — `dregg2 §8`, like `CryptoKernel`):
  - the AEAD `seal`/`unseal` (XChaCha20-Poly1305, `macaroon/src/crypto.rs:5-8,59-61`) and the
    keyed hash `hmac_sha256` / `binding_hash = SHA256` are **uninterpreted opaque functions**
    with only the laws an honest impl satisfies (correctness of unseal∘seal; the keyed hash is a
    function). Their *cryptographic soundness* (unforgeability, collision-resistance, that an
    adversary without `r` cannot fabricate a chain to a target tail) is an ASSUMED carrier `Prop`,
    discharged by the Rust impl + circuits, **never** a Lean theorem. We do NOT prove "no forgery";
    we prove the protocol's acceptance predicate is exactly the conjunction above, and that the
    teeth bite, GIVEN the keyed hash is a function and unseal inverts seal.

DISCIPLINE: no `sorry`/`admit`/`axiom`/`native_decide`. Pure, computable, `#eval`-able.
-/
import Dregg2.Authority.Caveat

namespace Dregg2.Authority.ThirdParty

set_option autoImplicit false

/-! ## §8 portal: the crypto kernel this protocol stands on (opaque, lawful, NEVER proved sound).

We keep the algebra *concrete and computable* (`Key`/`Cipher`/`Digest` are `List Nat`) so the
module is `#eval`-able, but the OPERATIONS (`seal`, `unseal`, the keyed hash) are supplied by a
`DischargeCrypto` interface — exactly the `CryptoKernel`/§8 boundary. The interface carries only
the *correctness* law (`unseal` inverts `seal` under the same key). Crypto SOUNDNESS — that an
adversary cannot forge a `seal` or find a keyed-hash collision — is the carrier `Prop`
`cryptoSound`, asserted by the impl, never a Lean theorem. -/

/-- Bytes: keys, plaintexts, ciphertexts, digests are all byte-lists (concrete ⇒ `#eval`-able). -/
abbrev Bytes := List Nat

/-- **The §8 discharge-crypto portal.** Mirrors `macaroon/src/crypto.rs`:
`seal`/`unseal` = XChaCha20-Poly1305 AEAD (`crypto.rs:5-8,59-61`); `keyedHash` = `hmac_sha256`
(the HMAC tail, `macaroon.rs:295,317`); `bindingHash` = `binding_hash = SHA256` (`macaroon.rs:342`).
All opaque. The ONLY law is AEAD correctness; soundness is the `cryptoSound` carrier `Prop`. -/
class DischargeCrypto where
  /-- Authenticated encryption (`crypto::seal`). `aeadSeal k m` = ciphertext of `m` under key `k`.
  (Named `aeadSeal`, not `seal`, because `seal` is a reserved Lean command keyword.) -/
  aeadSeal    : Bytes → Bytes → Bytes
  /-- Authenticated decryption (`crypto::unseal`): `some m` on success, `none` on auth failure. -/
  aeadUnseal  : Bytes → Bytes → Option Bytes
  /-- The HMAC keyed hash advancing the chain tail (`crypto::hmac_sha256`). -/
  keyedHash   : Bytes → Bytes → Bytes
  /-- `binding_hash` = `SHA256` of a tail, the bind-to-parent body (`macaroon.rs:342`). -/
  bindingHash : Bytes → Bytes
  /-- **LAW — AEAD correctness** (the only proved-against obligation): honest `aeadUnseal` inverts
  honest `aeadSeal` under the same key. (An impl satisfies this exactly.) -/
  unseal_seal : ∀ k m, aeadUnseal k (aeadSeal k m) = some m
  /-- **CARRIER — crypto soundness** (`Prop`, §8): no PPT adversary forges a `seal` under an
  unknown key, finds a `keyedHash`/`bindingHash` collision, or fabricates a chain to a target
  tail without the key. ASSUMED, discharged by the Rust impl + circuits — NEVER a Lean theorem. -/
  cryptoSound : Prop

section Protocol
variable [DischargeCrypto]

open DischargeCrypto

/-! ## Time, modeled abstractly (the freshness window). -/

/-- Abstract time = `Int` seconds since epoch (`macaroon.rs:280-283` reads `SystemTime` as `i64`).
We do NOT model a real clock; `now` is a parameter, exactly as the Rust reads it at verify time. -/
abbrev Time := Int

/-- `MAX_DISCHARGE_AGE` (`macaroon/src/macaroon.rs:35`) — 300 seconds = 5 minutes. -/
def maxDischargeAge : Time := 300

/-- **Freshness** (`macaroon.rs:275-289`): `created_at ≠ 0` (fail-closed, `:275-279`) AND
`0 ≤ now − created_at ≤ MAX_DISCHARGE_AGE` (`:284-289`). A `created_at` of 0 is rejected to force
upgrade; a too-old (replayed) or future discharge is rejected. -/
def fresh (createdAt now : Time) : Bool :=
  decide (createdAt ≠ 0) && decide (0 ≤ now - createdAt) && decide (now - createdAt ≤ maxDischargeAge)

/-! ## The protocol data: the third-party caveat and the discharge macaroon.

`Ctx`/`Gateway` are reused from `Authority.Caveat`; the 3P caveat's enforced obligation is a
`CaveatSet` modeled as a list of `Caveat Ctx Gateway` (the `caveats_for_3p` of `caveat_3p.rs:54-56`,
which the 3P must check). A discharge macaroon carries its own caveat chain (incl. the bind caveat),
keyed by the discharge key `r`. -/

variable {Ctx : Type} {Gateway : Type}

/-- **A third-party caveat** (`caveat_3p.rs:33-46`). `vid = seal(parentTail, r)` and
`ticket = seal(K_A, encode(r, predicate))`. `location` is informational. The `predicate` is the
obligation the 3P must enforce (`caveat_3p.rs:54`), here as a local check over `Ctx`. -/
structure ThirdPartyCaveat (Ctx : Type) where
  location  : Bytes
  /-- VID: `seal(parentTail, r)` (`caveat_3p.rs:91-92`). -/
  vid       : Bytes
  /-- Ticket (CID): `seal(K_A, encode(r ++ predicate-id))` (`caveat_3p.rs:80-89`). -/
  ticket    : Bytes
  /-- The third-party predicate the discharge must satisfy (`caveat_3p.rs:54`, the enforced check). -/
  predicate : Ctx → Bool

/-- One caveat in a discharge's chain: either an ordinary first-party check, or the
**bind-to-parent** caveat carrying `binding_hash(parentTail)` in its body (`CAV_BIND_TO_PARENT`,
`macaroon.rs:300-307`, body set at `:342-343`). -/
inductive DCaveat (Ctx : Type) where
  /-- A first-party caveat: an enforced check + its wire body (the bytes fed to the HMAC chain). -/
  | firstParty (check : Ctx → Bool) (body : Bytes)
  /-- The bind-to-parent caveat: its body is `binding_hash(someParentTail)` (`macaroon.rs:342`). -/
  | bindToParent (body : Bytes)

/-- The wire bytes a caveat contributes to the HMAC chain (`wire_caveat.encode()`, `macaroon.rs:298`). -/
def DCaveat.body : DCaveat Ctx → Bytes
  | .firstParty _ b => b
  | .bindToParent b => b

/-- **A discharge macaroon** (`create_discharge`, `macaroon.rs:383-404`). Keyed by the discharge
key `r`; carries a nonce (here just `created_at`, `macaroon.rs:392-396`), the caveat chain, and the
stored `tail`. The honest minting computes `tail` by replaying the chain from `r` over the nonce. -/
structure DischargeMacaroon (Ctx : Type) where
  /-- The discharge key `r` this macaroon was signed under (the ticket's `discharge_key`). -/
  dischargeKey : Bytes
  /-- `created_at` (`macaroon.rs:392-396`); 0 means "no timestamp" ⇒ fail-closed at verify. -/
  createdAt    : Time
  /-- The nonce bytes seeding the chain (`self.nonce.encode()`, `macaroon.rs:294`). -/
  nonceBytes   : Bytes
  /-- The append-only caveat chain. -/
  caveats      : List (DCaveat Ctx)
  /-- The stored HMAC tail (`self.tail`, `macaroon.rs:320`). -/
  tail         : Bytes

/-! ## Honest construction (the 3P side: `create_discharge` + `bind_discharge`). -/

/-- The HMAC tail obtained by replaying the chain from key `r` over `nonceBytes ++ caveat bodies`
(`macaroon.rs:294-318`): `t₀ = keyedHash r nonceBytes`, `tᵢ = keyedHash tᵢ₋₁ (body Cᵢ)`. -/
def replayTail (r : Bytes) (nonceBytes : Bytes) (cs : List (DCaveat Ctx)) : Bytes :=
  cs.foldl (fun t c => keyedHash t c.body) (keyedHash r nonceBytes)

/-- **`bindCaveat parentTail`** — the bind-to-parent caveat for a parent whose tail is `parentTail`
(`bind_discharge`, `macaroon.rs:341-347`; body = `binding_hash(parentTail)`). -/
def bindCaveat (parentTail : Bytes) : DCaveat Ctx :=
  .bindToParent (bindingHash parentTail)

/-- **`mintDischarge`** — the 3P honestly mints a discharge bound to `parentTail`
(`create_discharge` then `bind_discharge`): key `r`, timestamp `createdAt`, the 3P's own enforced
caveats `cs`, then append the bind caveat, computing the tail by honest replay. -/
def mintDischarge (r : Bytes) (createdAt : Time) (nonceBytes : Bytes)
    (cs : List (DCaveat Ctx)) (parentTail : Bytes) : DischargeMacaroon Ctx :=
  let chain := cs ++ [bindCaveat parentTail]
  { dischargeKey := r, createdAt, nonceBytes, caveats := chain,
    tail := replayTail r nonceBytes chain }

/-! ## Verification (the verifier side: `verify_discharge`, `macaroon.rs:267-332`).

The verifier recovers `r` from the VID using the parent's tail it replayed (`caveat_3p.rs:128-141`),
then checks the three conjuncts. We split acceptance into its named pieces so the soundness law can
state the iff exactly. -/

/-- **(CHAIN)** the discharge's stored tail equals the honest replay from `r` (`macaroon.rs:320-322`,
constant-time compare). This is what authenticates the body under `r` — a tampered caveat or a body
not signed by the 3P fails here. -/
def chainValid (m : DischargeMacaroon Ctx) (r : Bytes) : Bool :=
  decide (m.tail = replayTail r m.nonceBytes m.caveats)

/-- **(BOUND)** the chain contains a `bindToParent` caveat whose body equals
`binding_hash(expectedParentTail)` (`macaroon.rs:300-307`); absence ⇒ `DischargeUnbound`
fail-closed (`:324-329`); a wrong-parent body ⇒ `DischargeUnbound` (`:306`). -/
def boundTo (m : DischargeMacaroon Ctx) (expectedParentTail : Bytes) : Bool :=
  m.caveats.any (fun c => match c with
    | .bindToParent b => decide (b = bindingHash expectedParentTail)
    | _ => false)

/-- **(PREDICATE)** every first-party caveat the 3P stamped into the discharge holds at the request
context (`caveat_3p.rs:54`: the 3P's enforced caveats; the discharge "satisfies the 3P predicate"). -/
def predicateHolds (m : DischargeMacaroon Ctx) (ctx : Ctx) : Bool :=
  m.caveats.all (fun c => match c with
    | .firstParty check _ => check ctx
    | .bindToParent _ => true)

/-- **`recoverKey tpc parentTail`** — the verifier recovers `r = unseal(parentTail, vid)`
(`caveat_3p.rs:128-141`): decrypt the VID under the parent tail it replayed. `none` ⇒ wrong tail /
auth failure ⇒ no discharge key ⇒ rejection. -/
def recoverKey (tpc : ThirdPartyCaveat Ctx) (parentTail : Bytes) : Option Bytes :=
  aeadUnseal parentTail tpc.vid

/-- **`accepts` — THE acceptance predicate** (`verify_discharge`, `macaroon.rs:267-332`).
A discharge `m` for caveat `tpc`, against a parent whose replayed tail is `parentTail`, evaluated at
request `ctx` and verifier-clock `now`, is ACCEPTED iff ALL of:
  recover `r` from the VID under `parentTail`  (the ticket's key, `caveat_3p.rs:128-141`); AND
  the macaroon was actually keyed by that `r` (`m.dischargeKey = r`); AND
  (FRESH) `fresh m.createdAt now`              (`macaroon.rs:275-289`); AND
  (CHAIN) `chainValid m r`                     (`macaroon.rs:320-322`); AND
  (BOUND) `boundTo m parentTail`               (`macaroon.rs:300-307,324-329`); AND
  (PRED)  `predicateHolds m ctx`               (`caveat_3p.rs:54`).
Fail-closed: any failure ⇒ `false`. -/
def accepts (tpc : ThirdPartyCaveat Ctx) (m : DischargeMacaroon Ctx)
    (parentTail : Bytes) (ctx : Ctx) (now : Time) : Bool :=
  match recoverKey tpc parentTail with
  | none   => false
  | some r =>
      decide (m.dischargeKey = r)
        && fresh m.createdAt now
        && chainValid m r
        && boundTo m parentTail
        && predicateHolds m ctx

/-! ## THE SOUNDNESS LAW — acceptance is EXACTLY the four-conjunct gate. -/

/-- **`accepts_iff` (PROVED) — the integrity/soundness law.** A discharge is accepted IFF it
discharges the right ticket (the recovered `r` keys the macaroon), AND binds to the correct parent,
AND is fresh, AND satisfies the third-party predicate. This is the faithful statement of
`verify_discharge` (`macaroon.rs:267-332`): there is NO other way to be accepted — no hidden bypass.

(`chainValid` is folded in as the authentication that the body is genuinely keyed by `r`; we expose
it as its own conjunct so the law is the literal protocol gate.) -/
theorem accepts_iff (tpc : ThirdPartyCaveat Ctx) (m : DischargeMacaroon Ctx)
    (parentTail : Bytes) (ctx : Ctx) (now : Time) :
    accepts tpc m parentTail ctx now = true ↔
      (∃ r, recoverKey tpc parentTail = some r ∧
            m.dischargeKey = r ∧
            fresh m.createdAt now = true ∧
            chainValid m r = true ∧
            boundTo m parentTail = true ∧
            predicateHolds m ctx = true) := by
  cases hrec : recoverKey tpc parentTail with
  | none =>
    simp only [accepts, hrec, Bool.false_eq_true, false_iff, not_exists]
    rintro r ⟨h, _⟩
    exact absurd h (by simp)
  | some r =>
    simp only [accepts, hrec, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨⟨⟨hk, hf⟩, hc⟩, hb⟩, hp⟩
      exact ⟨r, rfl, hk, hf, hc, hb, hp⟩
    · rintro ⟨r', hrec', hk, hf, hc, hb, hp⟩
      obtain rfl : r = r' := Option.some.inj hrec'
      exact ⟨⟨⟨⟨hk, hf⟩, hc⟩, hb⟩, hp⟩

/-! ## COMPLETENESS — an honestly-minted, fresh, in-context discharge is accepted. -/

/-- **`honest_discharge_accepted` (PROVED).** If the 3P honestly minted the discharge bound to the
parent (`mintDischarge`), the verifier recovers exactly that key from the VID (AEAD correctness:
`vid = seal(parentTail, r)` so `unseal parentTail vid = some r`), the discharge is fresh and its
predicate holds, THEN it is accepted. This closes the loop: the honest protocol run succeeds. -/
theorem honest_discharge_accepted
    (r : Bytes) (createdAt now : Time) (nonceBytes : Bytes)
    (cs : List (DCaveat Ctx)) (parentTail : Bytes)
    (tpc : ThirdPartyCaveat Ctx)
    (hvid : tpc.vid = aeadSeal parentTail r)
    (hfresh : fresh createdAt now = true)
    (ctx : Ctx)
    (hpred : (mintDischarge r createdAt nonceBytes cs parentTail).caveats.all
              (fun c => match c with | .firstParty check _ => check ctx | .bindToParent _ => true) = true) :
    accepts tpc (mintDischarge r createdAt nonceBytes cs parentTail) parentTail ctx now = true := by
  unfold accepts recoverKey
  rw [hvid, DischargeCrypto.unseal_seal]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨?_, hfresh⟩, ?_⟩, ?_⟩, hpred⟩
  · rfl                       -- m.dischargeKey = r   (mintDischarge keys by r)
  · -- chainValid: the stored tail IS the honest replay (definitional in mintDischarge)
    show chainValid (mintDischarge r createdAt nonceBytes cs parentTail) r = true
    unfold chainValid mintDischarge replayTail
    simp only [decide_eq_true_eq]
  · -- boundTo: the appended bind caveat carries binding_hash parentTail
    unfold boundTo mintDischarge bindCaveat
    simp [List.any_append]

/-! ## TEETH — the negative laws: stale (replay) and cross-bound (wrong-parent) are REJECTED. -/

/-- **`stale_discharge_rejected` (PROVED) — REPLAY TEETH.** A discharge whose freshness check FAILS
(stale = replayed beyond `MAX_DISCHARGE_AGE`, or `created_at = 0`) is REJECTED, no matter what else
holds. This is the replay protection of `macaroon.rs:275-289`: an attacker who captures a valid
discharge cannot replay it after the 300-second window. -/
theorem stale_discharge_rejected (tpc : ThirdPartyCaveat Ctx) (m : DischargeMacaroon Ctx)
    (parentTail : Bytes) (ctx : Ctx) (now : Time)
    (hstale : fresh m.createdAt now = false) :
    accepts tpc m parentTail ctx now = false := by
  unfold accepts
  cases recoverKey tpc parentTail with
  | none => rfl
  | some r => simp [hstale]

/-- **`unbound_discharge_rejected` (PROVED) — CROSS-BIND TEETH (the headline).** A discharge that is
NOT bound to the parent it is presented against (`boundTo m parentTail = false`: no bind caveat, or a
bind caveat carrying `binding_hash` of a DIFFERENT parent) is REJECTED. This is `DischargeUnbound`
(`macaroon.rs:306,324-329`): a discharge minted for parent A cannot be replayed against parent B —
the bind-to-parent step defeats cross-context replay. -/
theorem unbound_discharge_rejected (tpc : ThirdPartyCaveat Ctx) (m : DischargeMacaroon Ctx)
    (parentTail : Bytes) (ctx : Ctx) (now : Time)
    (hunbound : boundTo m parentTail = false) :
    accepts tpc m parentTail ctx now = false := by
  unfold accepts
  cases recoverKey tpc parentTail with
  | none => rfl
  | some r => simp [hunbound]

/-- **`cross_bound_rejected` (PROVED) — the SHARP form of the cross-bind teeth.** Suppose `m` was
honestly minted bound to parent `tailA` (`mintDischarge … tailA`), and an attacker presents it
against a DIFFERENT parent `tailB` whose binding hash differs (`bindingHash tailB ≠ bindingHash tailA`
— honest, since a collision is exactly the §8 `cryptoSound` carrier we do NOT assume away). Then the
discharge is REJECTED against `tailB`. This is the precise "wrong-parent ⇒ rejected" teeth on a real
honest discharge. -/
theorem cross_bound_rejected
    (r : Bytes) (createdAt : Time) (nonceBytes : Bytes) (cs : List (DCaveat Ctx))
    (tailA tailB : Bytes) (ctx : Ctx) (now : Time) (tpc : ThirdPartyCaveat Ctx)
    -- the 3P's own caveats carry no spurious bind-to-`tailB` (they are first-party):
    (hcs : cs.all (fun c => match c with | .bindToParent _ => false | _ => true) = true)
    (hneq : bindingHash tailB ≠ bindingHash tailA) :
    accepts tpc (mintDischarge r createdAt nonceBytes cs tailA) tailB ctx now = false := by
  apply unbound_discharge_rejected
  -- the only bind caveat in the honest discharge binds to tailA, whose hash ≠ binding_hash tailB
  unfold boundTo mintDischarge bindCaveat
  simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_false_iff]
  refine ⟨?_, ?_⟩
  · -- the 3P's first-party caveats never match a bindToParent test
    rw [List.any_eq_false]
    intro c hc
    have hc' := List.all_eq_true.mp hcs c hc
    cases c with
    | firstParty _ _ => simp
    | bindToParent _ => simp at hc'
  · -- the appended bind caveat carries binding_hash tailA ≠ binding_hash tailB
    simp only [decide_eq_false_iff_not]
    exact fun h => hneq h.symm

end Protocol

/-! ## It runs (`#eval`): a reference §8 instance + an honest run, a stale replay, a cross-bind. -/

/-- A trivial REFERENCE crypto kernel for `#eval` ONLY (NOT a soundness claim — `seal` is identity-
tagged, which is obviously forgeable; it exists solely so the protocol logic is executable). The
real instance is the Rust FFI (`crypto.rs`). `cryptoSound := False` here HONESTLY records "this toy
is not sound" — the law statements never depend on `cryptoSound`. -/
instance refCrypto : DischargeCrypto where
  aeadSeal k m    := 0 :: k.length :: m         -- tag with key length so different keys differ
  aeadUnseal k c  := match c with
                     | 0 :: n :: rest => if n = k.length then some rest else none
                     | _ => none
  keyedHash t b   := 1 :: (t ++ b)              -- a deterministic function (a keyed hash IS one)
  bindingHash t   := 2 :: t
  unseal_seal k m := by simp
  cryptoSound     := False

/-- A height-windowed request context (reuse the demo flavor from `Caveat`). -/
abbrev Height := Nat

/-- The 3P's enforced caveat: "height ≥ 100" (a first-party check the 3P stamps in). -/
def cavGe100 : DCaveat Height := .firstParty (fun h => decide (100 ≤ h)) [9, 100]

/-- Parent A's replayed tail, and a different parent B's tail. -/
def tailA : Bytes := [42]
def tailB : Bytes := [43]

/-- The discharge key recovered from the ticket. -/
def rKey : Bytes := [7, 7, 7]

/-- An honestly-minted discharge bound to parent A, stamped at t=1000. -/
def honestM : DischargeMacaroon Height :=
  mintDischarge rKey 1000 [0] [cavGe100] tailA

/-- The 3P caveat whose VID seals `rKey` under parent A's tail (so the verifier recovers it). -/
def tpcA : ThirdPartyCaveat Height :=
  { location := [], vid := DischargeCrypto.aeadSeal tailA rKey, ticket := [], predicate := fun _ => true }

-- honest run at t=1100 (age 100s ≤ 300), height 150 ≥ 100, bound to A ⇒ ACCEPTED
#eval accepts tpcA honestM tailA 150 1100        -- true
-- STALE replay at t=2000 (age 1000s > 300) ⇒ REJECTED (replay teeth)
#eval accepts tpcA honestM tailA 150 2000         -- false
-- created_at = 0 ⇒ REJECTED fail-closed
#eval fresh 0 100                                 -- false
-- CROSS-BIND: present A's discharge against parent B ⇒ REJECTED (wrong-parent teeth)
--   (recoverKey fails under tailB anyway, AND boundTo would fail — double fail-closed)
#eval accepts tpcA honestM tailB 150 1100         -- false
-- predicate bites: height 50 < 100 ⇒ REJECTED even though fresh+bound
#eval accepts tpcA honestM tailA 50 1100          -- false
-- the bound check in isolation: honest discharge is bound to A, not to B
#eval boundTo honestM tailA                       -- true
#eval boundTo honestM tailB                       -- false

end Dregg2.Authority.ThirdParty
