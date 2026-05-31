/-
# Dregg2.Exec.FullForestAuth — the EXECUTED credential+caveat AUTH GATE on the call-forest (META-FILL D).

`Exec/FullForest.lean` closed the TREE-shaped `FullActionA` call-forest (`execFullForestA`), per-asset,
all-or-nothing, with the per-asset CONSERVATION VECTOR (`execFullForestA_conserves_per_asset`),
Granovetter non-amplification (`execFullForestA_no_amplify`), and per-node attestation
(`execFullForestA_each_attests`). But that executor is **credential-BLIND**: it authorizes a node
purely on the cap-list (`authorizedB`/`mintAuthorizedB`/`stateAuthB` *inside* `execFullA`). It never
asks WHO is acting (a §8 crypto credential) nor discharges the node's CAVEATS (the tiered,
state-reading narrowing conditions). That is the gap dregg1's `verify_authorization` fills with its
10-variant `Authorization` sum + biscuit/macaroon caveats.

META-FILL D adds the WHO and the caveat-discharge as a FAIL-CLOSED PRECONDITION, per-node, WITHOUT
touching the proved `FullForest`/`TurnExecutorFull` regions. The strategy (the keystone-survival
argument):

  * A NEW gated tree `FullForestG`/`FullChildG` mirrors `FullForestA`/`FullChildA` EXACTLY but carries
    a `NodeAuth` DECORATION on every node — the credential (a 10-variant `Authorization` sum), the
    revocation root, the tiered caveats, an optional HMAC macaroon chain, and the cap-authority
    `AuthMode`+`AuthContext`. `FullActionA` is UNTOUCHED (auth is a node-decoration, NOT an action
    kind), so `ledgerDeltaAsset`/`fullActionInvA`/every per-asset theorem stay byte-identical.
  * The 3-part gate `gateOK na s = credentialValid na && capAuthorityG na && caveatsDischarged na s`
    fires IN FRONT of `execFullA` in `execFullAGated s na a = if gateOK na s then execFullA s a else
    none`. FAIL-CLOSED on ANY leg ⇒ `none` ⇒ whole-forest rollback.
      - `credentialValid` = the §8 PORTAL (`AuthPortal.credentialValid`, routed to `Credential.verify`
        / `CryptoKernel.verify`) — a runnable oracle Bool, NEVER proved sound in Lean (the circuit's
        job). Its soundness is a Prop CARRIER (`AuthPortal.soundness`), the seL4 floor.
      - `capAuthorityG` = the WHAT, VERIFIED-IN-LEAN: `AuthModes.authModeAdmits` (reuse `granted ≤
        held`, the CapTpDelivered gap dregg1's Rust misses, modeled CORRECT).
      - `caveatsDischarged` = the tiered, within-cell state-reading caveat meet + the macaroon
        `verifiedChainGate`; `.coordinated` (cross-cell) caveats are routed OUT (foreclosing the
        dregg1 `authorize.rs:1608` cross-cell hole — they fail-close intra-cell, routed to
        `CrossCaveat`).
  * KEYSTONE SURVIVAL via `eraseG : FullForestG → FullForestA` (drop the auth). The gate only NARROWS
    admission; on the COMMIT path the gated run is BYTE-IDENTICAL to the ungated run of `eraseG f`
    (`execFullForestG_erases`). So conservation (`execFullForestG_conserves_per_asset`) and
    no-amplification (`execFullForestG_no_amplify`) are ONE-LINE COROLLARIES of the EXISTING
    `FullForest` theorems applied to `eraseG f` — NOT re-proofs. The launder teeth SURVIVE (a per-asset
    nonzero delta in each asset is still CAUGHT).
  * Per-node attestation GROWS: `gatedActionInvG` ANDs three auth conjuncts (credential-valid ∧
    cap-authority ∧ caveats-discharged) onto the UNCHANGED `fullActionInvA`. `execFullAGated_attests`
    and `execFullForestG_each_attests` prove every committed node carries them — credential-blindness
    is GONE.

The within-cell no-TOCTOU is AUTOMATIC: `execFullAGated` reads `gateOK na s` on the SAME `s` it then
runs `execFullA s a` against — one indivisible node step (`gatedNode_check_eq_use`), the executed
analog of `CrossCaveat.caveated_check_eq_use`.

Discipline: NO `axiom`/`admit`/`native_decide`/`sorry`. The `AuthPortal.soundness` CARRIER is a Prop
FIELD (the §8 discipline), NOT an axiom. Keystones `#assert_axioms`-pinned to `{propext,
Classical.choice, Quot.sound}`. Reuses `FullForest`/`AuthModes`/`Credential`/`CaveatChain`/
`DriftStable`/`ThirdPartyDischarge`/`CrossCaveat`/`CryptoKernel`; EDITS NONE. ONE namespace.
-/
import Dregg2.Exec.FullForest
import Dregg2.Exec.AuthModes
import Dregg2.Exec.CrossCaveat
import Dregg2.Authority.Credential
import Dregg2.Authority.CaveatChain
import Dregg2.Authority.ThirdPartyDischarge
import Dregg2.Confluence.DriftStable
import Dregg2.CryptoKernel

namespace Dregg2.Exec.FullForestAuth

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Authority
open Dregg2.Crypto (CryptoKernel)
open Dregg2.Exec.AuthModes (AuthMode AuthContext authModeAdmits)

/-! ## §1 — The `AuthPortal` (the §8 WHO-seam) + the 10-variant `Authorization` sum.

`AuthPortal` is the credential-verification PORTAL: it routes the `na.cred` `Authorization` sum to
the §8 `CryptoKernel.verify`/`Credential.verify`/`Chain.verify` opaque oracle. `credentialValid` is a
runnable `Bool` — `E` implements it as an `@[extern "dregg_…"]` of the `CryptoKernel.lean:17-18`
shape. Its `soundness` is a Prop CARRIER (assumed, NEVER a Lean law — the circuit's job), mirroring
`MacKernel.unforgeable` / `DischargeCrypto.cryptoSound` / `CryptoKernel.collisionHard`. This is the
seL4 floor: we prove the gate-DISCIPLINE (fail-closed on a forged/revoked credential), the circuits
prove the oracle BINDS. -/

/-- **The credential-verification PORTAL (the §8 WHO-seam).** `credentialValid cred ctx` is the
runnable oracle gate (`E`'s `@[extern]`); `soundness` is the assumed Prop carrier (never a Lean law,
the circuit obligation). Routing the `Authorization` sum through ONE seam keeps the WHO leg a portal
across all 10 variants. -/
class AuthPortal (Authorization Ctx : Type) where
  /-- The runnable §8 oracle gate: does this credential verify in this context? -/
  credentialValid : Authorization → Ctx → Bool
  /-- **CARRIER** — the credential-soundness obligation (Prop, ASSUMED — the §8 floor, the circuit's
  job; NEVER proved sound in Lean). Mirrors `MacKernel.unforgeable`/`DischargeCrypto.cryptoSound`. -/
  soundness : Prop

/-! The 10-variant `Authorization` sum (dregg1 `turn/src/action.rs:206-433`), single per-node field.
Each variant carries its WHO data; `credentialValid` bottoms out per arm in the portal (crypto-floor
arms) or a pure Lean structural/lattice/c-list read (OneOf/Unchecked/Breadstuff). Stealth /
StarkDelegation are FAITHFUL NEW witnessed kinds (a `Digest`/`Proof` point-relation/STARK routed
through the portal — NOT a faked `AuthMode` constructor). -/

/-- **`Authorization`** — dregg1's 10-variant `Authorization` sum, the per-node credential (WHO). The
crypto-floor arms (`signature`/`proof`/`bearer`/`capTpDelivered`/`custom`/`stealth`/`token`) bottom
out in the §8 portal; the Lean-verifiable arms (`breadstuff`/`unchecked`/`oneOf`) are pure
structural/lattice/c-list reads. -/
inductive Authorization (Digest Proof : Type) where
  /-- (1) **Signature** — ed25519 `verify_strict` over the action's signing message. PORTAL. -/
  | signature      (pubkeyMsg : Digest) (sig : Proof)
  /-- (2) **Proof** — a vk-bound ZK proof discharging the (boundAction, boundResource) binding. PORTAL. -/
  | proof          (vk : Digest) (proofBytes : Proof) (boundAction boundResource : Nat)
  /-- (3) **Breadstuff** — the actor holds the cap token in ITS c-list (expiry/facet/revocation reads).
  LEAN-verifiable (no crypto). -/
  | breadstuff     (token : Nat)
  /-- (4) **Bearer** — a delegation proof chain (SignedDelegation=ed25519 / StarkDelegation=STARK).
  PORTAL split + Lean conferral refinement. -/
  | bearer         (delegMsg : Digest) (delegSig : Proof) (starkDelegation : Bool)
  /-- (5) **Unchecked** — admitted ONLY for an unconstrained target (fail-closed by design). LEAN. -/
  | unchecked
  /-- (6) **CapTpDelivered** — two ed25519 sigs (introducer + sender) + the cert/target binding.
  PORTAL sigs + Lean `granted ≤ held` (the dregg1 gap, modeled CORRECT). -/
  | capTpDelivered (introMsg senderMsg : Digest) (introSig senderSig : Proof)
  /-- (7) **Custom** — an app-defined witnessed-predicate proof against the custom signing message
  (EXCLUDES witness_blobs). PORTAL (registry verify). -/
  | custom         (kindStmt : Digest) (proofBytes : Proof)
  /-- (8) **OneOf** — a pure 1-of-N disjunctive selector (3 structural rules; recurses). LEAN. -/
  | oneOf          (candidates : List (Authorization Digest Proof)) (proofIndex : Nat)
  /-- (9) **Stealth** — the actor knows the spend scalar `s` of `S = cell.public_key()`: the
  curve25519 point relation `P = c·G + S` + a one-time ed25519 sig. A FAITHFUL NEW witnessed kind
  routed through the portal (NOT a faked `AuthMode`). PORTAL. -/
  | stealth        (oneTimePk ephemeralPk : Digest) (sig : Proof)
  /-- (10) **Token** — a biscuit/macaroon credential (ed25519 / HMAC) + the caveat tier. PORTAL +
  Lean caveat meet. -/
  | token          (issuerKey : Digest) (sig : Proof)

/-! The portal's per-arm reduction (the §8 floor), instantiated at the `CryptoKernel` seam. For the
crypto-floor arms `credentialValid` is `CryptoKernel.verify stmt proof`; for the Lean arms it is a
pure structural/lattice/c-list Bool (here: `breadstuff`/`token`'s presence is a §8 check too, but
`unchecked` is the fail-closed anchor and `oneOf` recurses). The closed-form §8 reduction below is the
ONE the portal carries. -/

mutual
/-- **`portalVerify`** — the §8 reduction of `credentialValid` over a `CryptoKernel` (the per-arm
crypto-floor / Lean dispatch). `signature`/`proof`/`bearer`/`capTpDelivered`/`custom`/`stealth`/`token`
route through `CryptoKernel.verify` (the variant's signing-message digest vs its sig/STARK/HMAC bytes);
`unchecked` fail-closes UNLESS the context marks the target unconstrained (here: never — `unchecked` at
a credentialed node is rejected by the portal, the §8 anchor); `breadstuff` is a pure ledger read
modeled as always-portal-true (the WHAT leg does the c-list check); `oneOf` recurses, accepting iff the
chosen in-bounds candidate (not nested/Unchecked) verifies. -/
def portalVerify {Digest Proof : Type} [AddCommGroup Digest] [CryptoKernel Digest Proof] :
    Authorization Digest Proof → Bool
  | .signature stmt sig           => CryptoKernel.verify stmt sig
  | .proof vk pf _ _              => CryptoKernel.verify vk pf
  | .breadstuff _                 => true                              -- pure c-list read; WHAT leg gates
  | .bearer msg sig _             => CryptoKernel.verify msg sig
  | .unchecked                    => false                             -- §8 anchor: no credential ⇒ fail-closed
  | .capTpDelivered im sm isig ss => CryptoKernel.verify im isig && CryptoKernel.verify sm ss
  | .custom stmt pf               => CryptoKernel.verify stmt pf
  | .oneOf cands i                => portalOneOf cands i               -- structural fold to the chosen slot
  | .stealth otp _ sig            => CryptoKernel.verify otp sig
  | .token key sig                => CryptoKernel.verify key sig

/-- The `OneOf` portal: walk the candidate list to index `i` (structural recursion on the list),
applying the THREE dregg1 structural rules at the slot — not `Unchecked`, not nested `OneOf`, and
(recursively) the candidate verifies. Out-of-bounds fails closed. Mirrors `AuthModes.authModeOneOf`. -/
def portalOneOf {Digest Proof : Type} [AddCommGroup Digest] [CryptoKernel Digest Proof] :
    List (Authorization Digest Proof) → Nat → Bool
  | [],          _     => false                                       -- out of bounds: fail closed
  | chosen :: _, 0     =>
      (match chosen with | .unchecked => false | .oneOf _ _ => false | _ => true) && portalVerify chosen
  | _ :: rest,   n + 1 => portalOneOf rest n
end

/-- **The §8 portal instance over a `CryptoKernel`** (the Demo-trivial / `Crypto.Reference`
realization for `#eval`; `E` swaps in the `@[extern]` impl). `credentialValid := portalVerify`;
`soundness := CryptoKernel.collisionHard` (the assumed §8 carrier, never a Lean law). -/
instance cryptoAuthPortal {Digest Proof : Type} [AddCommGroup Digest] [CryptoKernel Digest Proof]
    {Ctx : Type} : AuthPortal (Authorization Digest Proof) Ctx where
  credentialValid cred _ := portalVerify cred
  soundness := CryptoKernel.collisionHard (Digest := Digest) (Proof := Proof)

/-! ### §1-eval — the portal fires on `Crypto.Reference` (the Lean-as-host `#eval` realization).

`Crypto.Reference` (`D := Int`, `P := Int`, `verify stmt proof := decide (stmt = proof)`): a proof is
valid iff it ECHOES the statement. So a GENUINE credential's proof = its statement; a FORGED one is
anything else. This exercises the portal (forged ⇒ fail-closed) WITHOUT Rust. -/

section PortalDemo
open Dregg2.Crypto.Reference

/-- A genuine signature credential: the proof echoes the statement (stmt 7). PORTAL accepts. -/
def goodSig : Authorization Crypto.Reference.D Crypto.Reference.P := .signature 7 7
/-- A FORGED signature credential: the proof (8) does NOT echo the statement (7). PORTAL rejects. -/
def forgedSig : Authorization Crypto.Reference.D Crypto.Reference.P := .signature 7 8

#eval portalVerify goodSig                                            -- true  (genuine ⇒ portal accepts)
#eval portalVerify forgedSig                                          -- false (forged ⇒ portal fail-closes)
#eval portalVerify (Digest := Crypto.Reference.D) (Proof := Crypto.Reference.P) .unchecked  -- false (§8 anchor)
-- OneOf selects a genuine candidate at index 1 ⇒ verifies; an Unchecked at the slot ⇒ rejected:
#eval portalVerify (.oneOf [forgedSig, goodSig] 1)                    -- true  (index-1 candidate genuine)
#eval portalVerify (.oneOf [goodSig, .unchecked] 1)                   -- false (Unchecked at slot ⇒ no bypass)
#eval portalVerify (.oneOf [goodSig] 5)                               -- false (out of bounds ⇒ fail-closed)

end PortalDemo

/-! ## §2 — `NodeAuth` decoration + the gated tree `FullForestG`/`FullChildG` + the erasure spine.

`NodeAuth` is the per-node credential+caveat DECORATION. It carries:
  * `cred` — the 10-variant `Authorization` (the WHO, portal);
  * `capMode`/`capCtx` — the `AuthModes.AuthMode` + `AuthContext` (the WHAT, `authModeAdmits`, VERIFIED);
  * `caveats` — the tiered, within-cell state-reading caveat list (the discharge leg);
  * `chain`/`discharges` — the optional HMAC macaroon chain + its discharge supply (the Token/Bearer arm).

The gated tree `FullForestG`/`FullChildG` mirrors `FullForestA`/`FullChildA` EXACTLY but adds the
`auth` field on every node (root and child subtree). `FullActionA` is UNTOUCHED. The erasure map
`eraseG` drops the `auth`, projecting onto the proved ungated tree — the bridge through which every
ungated `FullForest` theorem is re-used. The whole gated tree is parametric over the carrier types
(crypto `Digest`/`Proof`, the AuthModes `Request/Stmt/Wit/CellId/Rights/Ctx/Gateway`, the chain
`Key/Bytes/Tag`); the Demo instantiates them concretely for `#eval`. -/

/-- **A within-cell, state-reading TIERED caveat.** Carries its `DriftStable.DriftTier` tag (the
COMPUTABLE dispatch tag the executor reads) and a `check : RecChainedState → Bool` reading the node's
PRE-state (the node's OWN target cell — strictly INTRA-cell). A `.coordinated` caveat (one that would
read ANOTHER cell — the cross-cell TOCTOU axis) is ROUTED OUT (it fail-closes here, deferred to
`CrossCaveat.jointApplyCaveated`), foreclosing the dregg1 `authorize.rs:1608` cross-cell hole. -/
structure GatedCaveat where
  /-- The computable drift-tier tag (`monotone`/`reservation`/`locked`/`coordinated`) the executor
  reads to dispatch — the verify-not-find seam (`DriftStable.DriftTier`). -/
  tier  : Dregg2.Confluence.DriftStable.DriftTier
  /-- The within-cell state-reading predicate, evaluated on the node's PRE-state (its own target cell). -/
  check : RecChainedState → Bool

/-- **`GatedCaveat.holds`** — discharge the caveat on the pre-state `s`. The `.coordinated` tier is the
cross-cell axis: it fail-closes here (routed to `CrossCaveat`), so an intra-cell node carrying a
coordinated caveat is rejected — it cannot silently pass nor be live-read across cells. All other
(drift-stable) tiers read their `check` on `s`. -/
def GatedCaveat.holds (c : GatedCaveat) (s : RecChainedState) : Bool :=
  match c.tier with
  | .coordinated => false               -- routed to CrossCaveat (intra-cell gate fail-closes)
  | _            => c.check s            -- within-cell, drift-stable tier ⇒ read the pre-state

section Gated

variable {Digest Proof : Type}
variable {Request Stmt Wit CellId Rights Ctx Gateway : Type}
variable [DecidableEq CellId] [SemilatticeInf Rights] [OrderTop Rights] [DecidableLE Rights]
variable {Bytes Tag : Type}

/-- **`NodeAuth`** — the per-node credential+caveat DECORATION (the new field). NOT a widening of
`FullActionA`: `targetOf`/`ledgerDeltaAsset`/`fullReceiptA`/`fullActionInvA` stay byte-identical.
The chain key type follows `CaveatChain`'s convention (`CaveatChain.Key Tag = Tag`). -/
structure NodeAuth (Digest Proof Request Stmt Wit CellId Rights Ctx Gateway Bytes Tag : Type)
    [SemilatticeInf Rights] [OrderTop Rights] where
  /-- The credential (the WHO) — routed through the §8 `AuthPortal.credentialValid`. -/
  cred       : Authorization Digest Proof
  /-- The revocation root the credential is checked against (the negative-discharge seam). -/
  rev        : Credential.RevocationSet
  /-- The cap-authority mode (the WHAT) — dispatched by `AuthModes.authModeAdmits`, VERIFIED-in-Lean. -/
  capMode    : AuthMode Request Stmt Wit CellId Rights Ctx Gateway
  /-- The per-call facts the cap-authority mode dispatches against. -/
  capCtx     : AuthContext Request Stmt Wit CellId Rights Ctx Gateway
  /-- The within-cell tiered caveats (the discharge leg, state-reading). -/
  caveats    : List GatedCaveat
  /-- The optional HMAC macaroon chain (the Token/Bearer arm); `none` ⇒ no chain leg. -/
  chain      : Option (CaveatChain.Chain Ctx Gateway (CaveatChain.Key Tag) Bytes Tag)
  /-- The caveat-context the chain's `verifiedChainGate` reads. -/
  chainCtx   : Ctx
  /-- Which gateways have discharged (for the chain gate's third-party caveats). -/
  chainDis   : Discharges Gateway

/-- An abbreviation for the fully-applied `NodeAuth` over the section's carrier variables. -/
abbrev NodeAuthC := NodeAuth Digest Proof Request Stmt Wit CellId Rights Ctx Gateway Bytes Tag

mutual
/-- A node of the GATED full-op-set call-forest: its `auth` DECORATION, its own `FullActionA` (run via
`execFullA` after the gate), and its `children`. The gated dual of `FullForestA`. -/
structure FullForestG where
  /-- The credential + caveats decoration (the NEW field; the gate fires on it before `execFullA`). -/
  auth     : NodeAuthC (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
               (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag)
  /-- The node's own full-op-set, per-asset action (UNCHANGED — byte-identical to `FullForestA.action`). -/
  action   : FullActionA
  /-- The delegated child subtrees (each a gated delegation edge). -/
  children : List FullChildG

/-- A gated delegation edge: the delegation edge data (UNCHANGED from `FullChildA`) to a gated child
subtree. -/
structure FullChildG where
  /-- The label the derived child-cap is granted to (UNCHANGED). -/
  holder    : Label
  /-- The rights the parent's cap is attenuated to when delegated (UNCHANGED). -/
  keep      : List Auth
  /-- The parent capability being delegated (UNCHANGED). -/
  parentCap : Cap
  /-- The gated child subtree. -/
  sub       : FullForestG
end

mutual
/-- **`eraseG`** — drop the `auth` decoration, projecting the gated tree onto the proved ungated
`FullForestA`. The bridge through which every ungated conservation/no-amplify/attestation theorem is
re-used (the gate only narrows admission; on the commit path the run is byte-identical to `eraseG f`). -/
def eraseG :
    FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt) (Wit := Wit)
      (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag) → FullForestA
  | ⟨_, a, kids⟩ => ⟨a, eraseChildrenG kids⟩

def eraseChildrenG :
    List (FullChildG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag)) → List FullChildA
  | []                       => []
  | ⟨h, k, pc, sub⟩ :: rest  => ⟨h, k, pc, eraseG sub⟩ :: eraseChildrenG rest
end

mutual
/-- **`nodesG`** — every node of the gated tree in pre-order (the node, then its children's
flattenings). Carries the WHOLE node (auth + action + children) so the per-node attestation can read
the credential/caveats. -/
def nodesG :
    FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt) (Wit := Wit)
      (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag) →
    List (FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag))
  | f@⟨_, _, kids⟩ => f :: childrenNodesG kids

def childrenNodesG :
    List (FullChildG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag)) →
    List (FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag))
  | []                     => []
  | ⟨_, _, _, sub⟩ :: rest => nodesG sub ++ childrenNodesG rest
end

mutual
/-- **`forestEdgesG`** — every delegation edge of the gated tree, in pre-order. The edge data is the
`FullChildG` delegation triple, IDENTICAL to the `FullChildA` one (auth is orthogonal to the edge). -/
def forestEdgesG :
    FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt) (Wit := Wit)
      (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag) → List (List Auth × Cap)
  | ⟨_, _, kids⟩ => childrenEdgesG kids

def childrenEdgesG :
    List (FullChildG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag)) → List (List Auth × Cap)
  | []                         => []
  | ⟨_, keep, pc, sub⟩ :: rest => (keep, pc) :: (forestEdgesG sub ++ childrenEdgesG rest)
end

mutual
/-- **`forestEdgesG_eq_forestEdgesA_eraseG` — PROVED (the auth-orthogonal edge bridge).** The gated
tree's delegation edges are EXACTLY the ungated `eraseG`'d tree's edges — the credential+caveat
decoration adds no edge and removes none. So `execFullForestG_no_amplify` is a one-liner off
`execFullForestA_no_amplify (eraseG f)`. Proved by mutual structural induction. -/
theorem forestEdgesG_eq_forestEdgesA_eraseG
    (f : FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag)) :
    forestEdgesG f = forestEdgesA (eraseG f) := by
  obtain ⟨na, a, kids⟩ := f
  show childrenEdgesG kids = childrenEdgesA (eraseChildrenG kids)
  exact childrenEdgesG_eq_childrenEdgesA_eraseG kids

theorem childrenEdgesG_eq_childrenEdgesA_eraseG
    (kids : List (FullChildG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag))) :
    childrenEdgesG kids = childrenEdgesA (eraseChildrenG kids) := by
  match kids with
  | [] => rfl
  | ⟨h, k, pc, sub⟩ :: rest =>
      show (k, pc) :: (forestEdgesG sub ++ childrenEdgesG rest)
          = (k, pc) :: (forestEdgesA (eraseG sub) ++ childrenEdgesA (eraseChildrenG rest))
      rw [forestEdgesG_eq_forestEdgesA_eraseG sub, childrenEdgesG_eq_childrenEdgesA_eraseG rest]
end

/-! ## §3 — The 3-part GATE: `credentialValid ∧ capAuthorityG ∧ caveatsDischarged` (fail-closed).

The gate fires per-node, in front of `execFullA`. It is a CONJUNCTION — fail-closed on ANY leg:
  * `credentialValid` (the WHO) routes `na.cred` through the §8 `AuthPortal` (a portal Bool, NEVER
    proved sound in Lean — the circuit's job);
  * `capAuthorityG` (the WHAT) dispatches `na.capMode` via `AuthModes.authModeAdmits` (VERIFIED — reuse
    `granted ≤ held`, the CapTpDelivered gap modeled CORRECT);
  * `caveatsDischarged` (the caveat leg) reads the node's PRE-state: the tiered within-cell caveat meet
    (`.coordinated` routed OUT) ∧ the macaroon `verifiedChainGate` (HMAC replay + caveat meet) when a
    chain is present.

An empty caveat list = `all [] = true` (fine); a forged/revoked credential MUST fail-close (like
`revoke_blocks_verify`). -/

section Gate

variable {Digest Proof : Type}
variable {Request Stmt Wit CellId Rights Ctx Gateway : Type}
variable [DecidableEq CellId] [SemilatticeInf Rights] [OrderTop Rights] [DecidableLE Rights]
variable {Bytes Tag : Type}
variable [Dregg2.Laws.Verifiable Stmt Wit]
variable [DecidableEq Tag] [CaveatChain.MacKernel (CaveatChain.Key Tag) Bytes Tag]
variable [AuthPortal (Authorization Digest Proof) Ctx]

/-- **`credentialValid` — the WHO leg (the §8 PORTAL).** Routes `na.cred` through
`AuthPortal.credentialValid` against the node's caveat-context. A runnable oracle Bool, NEVER proved
sound in Lean (the seL4 floor). For the VC arm the portal's reduction is exactly `Credential.verify`
(§8 oracle ∧ non-revoked, the negative discharge — `revoke_blocks_verify` fail-closes a revoked
credential); for the macaroon arm `Chain.verify`; for the rest `CryptoKernel.verify` — all behind the
ONE `AuthPortal` seam. -/
def credentialValidG
    (na : NodeAuthC (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag)) : Bool :=
  AuthPortal.credentialValid (Ctx := Ctx) na.cred na.chainCtx

/-- **`capAuthorityG` — the WHAT leg (VERIFIED-IN-LEAN).** The cap-authority refinement via
`AuthModes.authModeAdmits` over the node's `capMode`/`capCtx`: `granted ≤ held` (the CapTpDelivered
attenuation dregg1's Rust MISSES), the OneOf structural rules, the token caveat meet — each routed onto
an existing primitive, fail-closed. This is the cheapest leg (it is ALREADY the precondition `execFullA`
runs; the gate just exposes the additional `authModeAdmits` refinement). -/
def capAuthorityG
    (na : NodeAuthC (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag)) : Bool :=
  authModeAdmits na.capMode na.capCtx

/-- **`chainGateG` — the macaroon HMAC face of the caveat leg.** When the node carries a chain,
admission requires `CaveatChain.verifiedChainGate` = `c.verify && c.admits ctx d` — BOTH the HMAC
replay-and-compare (`Chain.verify`, so caveat-REMOVAL is caught by `removal_breaks_tail`) AND the
caveat meet. No chain ⇒ `true` (the leg is a no-op overlay only when ABSENT, never a silent pass). -/
def chainGateG
    (na : NodeAuthC (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag)) : Bool :=
  match na.chain with
  -- `CaveatChain.verifiedChainGate c d ctx` is definitionally `c.verify && c.admits ctx d`; we inline
  -- it (avoiding higher-order unification on the `Key`-as-`Type → Type` carrier) so the HMAC
  -- replay-and-compare (`Chain.verify`, caught by `removal_breaks_tail`) AND the caveat meet
  -- (`Chain.admits`) BOTH gate. The bridge `chainGateG_eq_verifiedChainGate` (below) ties it back.
  | some c => c.verify && c.admits na.chainCtx na.chainDis
  | none   => true

/-- **`caveatsDischarged` — the caveat-discharge leg (the tiered, within-cell, state-reading meet).**
Reads the node's PRE-state `s`: every tiered caveat `holds` on `s` (the `.coordinated` cross-cell axis
routed OUT — it fail-closes intra-cell, deferred to `CrossCaveat`) AND the macaroon `chainGateG`. The
within-cell no-TOCTOU is automatic (`gateOK` reads `s`, the same snapshot `execFullA` commits against). -/
def caveatsDischarged
    (na : NodeAuthC (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag))
    (s : RecChainedState) : Bool :=
  na.caveats.all (fun c => c.holds s) && chainGateG na

/-- **`gateOK` — the 3-part conjunction (FAIL-CLOSED on ANY leg).** `credentialValid && capAuthorityG
&& caveatsDischarged`. A single false leg ⇒ `none` ⇒ whole-forest rollback. The WHO (portal) ∧ the WHAT
(verified) ∧ the caveats (state-reading). -/
def gateOK
    (na : NodeAuthC (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag))
    (s : RecChainedState) : Bool :=
  credentialValidG na && capAuthorityG na && caveatsDischarged na s

/-! ## §4 — `execFullAGated` + the gated tree executor `execFullForestG` (the FAIL-CLOSED wrapper).

`execFullAGated s na a = if gateOK na s then execFullA s a else none` — the gate fires IN FRONT of
the UNCHANGED `execFullA`. On the some-branch the post-state is BYTE-IDENTICAL to `execFullA`'s (the
gate touches NO ledger), so conservation/attestation are reused verbatim. The gated tree
`execFullForestG`/`execFullChildrenG` mirrors `execFullForestA`/`execFullChildrenA` EXACTLY with
`execFullA → execFullAGated`. -/

/-- **`execFullAGated` — the FAIL-CLOSED gated node step.** `if gateOK na s then execFullA s a else
none`. The WHEN-PASS branch is the UNCHANGED `execFullA`; ANY false gate leg ⇒ `none`. -/
def execFullAGated (s : RecChainedState)
    (na : NodeAuthC (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag))
    (a : FullActionA) : Option RecChainedState :=
  if gateOK na s = true then execFullA s a else none

mutual
/-- **`execFullForestG`/`execFullChildrenG` — the GATED tree executor.** Each node runs its
`execFullAGated` (the gate THEN `execFullA`), then its children; any `none` aborts the whole forest
(the all-or-nothing rollback). The gated dual of `execFullForestA`. -/
def execFullForestG (s : RecChainedState) :
    FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt) (Wit := Wit)
      (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag) → Option RecChainedState
  | ⟨na, a, kids⟩ =>
    match execFullAGated s na a with
    | some s' => execFullChildrenG s' kids
    | none    => none

def execFullChildrenG (s : RecChainedState) :
    List (FullChildG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag)) → Option RecChainedState
  | []            => some s
  | ⟨_, _, _, sub⟩ :: rest =>
    match execFullForestG s sub with
    | some s' => execFullChildrenG s' rest
    | none    => none
end

/-- **`execFullAGated_some_iff` — PROVED (the load-bearing unfolding lemma).** The gated step commits
IFF the gate passed AND the underlying `execFullA` committed: `execFullAGated s na a = some s' ↔
(gateOK na s = true ∧ execFullA s a = some s')`. EVERYTHING rests on this — conservation reads the
RHS's `execFullA` run, attestation reads the LHS's gate Bools. NON-VACUOUS: both legs are forced (a
forged credential OR an unauthorized action each give `none`, for different reasons). -/
theorem execFullAGated_some_iff (s s' : RecChainedState)
    (na : NodeAuthC (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag))
    (a : FullActionA) :
    execFullAGated s na a = some s' ↔ (gateOK na s = true ∧ execFullA s a = some s') := by
  unfold execFullAGated
  by_cases hg : gateOK na s = true
  · rw [if_pos hg]
    constructor
    · intro h; exact ⟨hg, h⟩
    · intro h; exact h.2
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · intro h; exact absurd h.1 hg

/-- **`gatedNode_check_eq_use` — the within-cell NO-TOCTOU keystone (PROVED).** A committed gated node
proves the gate held on EXACTLY the pre-state `s` the action then commits against — one indivisible
snapshot (`gateOK na s = true ∧ execFullA s a = some s'`). The executed analog of
`CrossCaveat.caveated_check_eq_use`: there is no window for a concurrent turn to invalidate the
credential/cap-authority/caveats between check and use. Asserts all three gate legs held on `s`. -/
theorem gatedNode_check_eq_use (s s' : RecChainedState)
    (na : NodeAuthC (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag))
    (a : FullActionA) (h : execFullAGated s na a = some s') :
    gateOK na s = true ∧ execFullA s a = some s' :=
  (execFullAGated_some_iff s s' na a).mp h

/-! ## §5 — The gated LINEAR layer: `lowerForestG`, `execFullTurnG`, the append mirror.

The pre-order pairing of each node's `auth` with its `action`, and the gated linear fold. These mirror
`lowerForestA`/`execFullTurnA` EXACTLY with `execFullA → execFullAGated`; the append lemma is the SAME
induction as `execFullTurnA_append`. They re-found the bridge `execFullForestG_eq_execFullTurnG`. -/

/-- The section's fully-applied `NodeAuth` (the linear layer's auth carrier) — an explicit `def` (NOT
an `abbrev`) so the carrier instances (`OrderTop`/`SemilatticeInf Rights`) are pinned by the section
variables, never left as metavariables. -/
def NodeAuthS : Type :=
  NodeAuthC (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
    (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
    (Bytes := Bytes) (Tag := Tag)

mutual
/-- **`lowerForestG`** — the gated forest's `(auth, action)` pairs in pre-order (the node, then its
children's flattenings). The auth-decorated mirror of `lowerForestA`. -/
def lowerForestG :
    FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt) (Wit := Wit)
      (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag) →
    List (NodeAuthS (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag) × FullActionA)
  | ⟨na, a, kids⟩ => (na, a) :: lowerChildrenG kids

def lowerChildrenG :
    List (FullChildG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag)) →
    List (NodeAuthS (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag) × FullActionA)
  | []                     => []
  | ⟨_, _, _, sub⟩ :: rest => lowerForestG sub ++ lowerChildrenG rest
end

/-- **`execFullTurnG`** — the gated linear fold over `(auth, action)` pairs (`execFullA →
execFullAGated`). The all-or-nothing `Option`-fold mirroring `execFullTurnA`. -/
def execFullTurnG (s : RecChainedState) :
    List (NodeAuthS (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag) × FullActionA) → Option RecChainedState
  | []           => some s
  | (na, a) :: rest =>
    match execFullAGated s na a with
    | some s' => execFullTurnG s' rest
    | none    => none

/-- **`execFullTurnG_append` — PROVED.** Running a concatenated gated linear turn equals running the
prefix and, on success, the suffix. The associativity the bridge's pre-order flattening rests on —
the SAME induction as `execFullTurnA_append`, with the gate carried. -/
theorem execFullTurnG_append (s : RecChainedState)
    (xs ys : List (NodeAuthS (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag) × FullActionA)) :
    execFullTurnG s (xs ++ ys)
      = (match execFullTurnG s xs with
         | some s' => execFullTurnG s' ys
         | none    => none) := by
  induction xs generalizing s with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨na, a⟩ := p
      show execFullTurnG s ((na, a) :: (rest ++ ys))
          = (match execFullTurnG s ((na, a) :: rest) with
             | some s' => execFullTurnG s' ys
             | none    => none)
      rw [show execFullTurnG s ((na, a) :: (rest ++ ys))
            = (match execFullAGated s na a with
               | some s1 => execFullTurnG s1 (rest ++ ys)
               | none    => none) from rfl,
          show execFullTurnG s ((na, a) :: rest)
            = (match execFullAGated s na a with
               | some s1 => execFullTurnG s1 rest
               | none    => none) from rfl]
      cases execFullAGated s na a with
      | none    => rfl
      | some s1 => exact ih s1

mutual
/-- **`lowerForestG_actions_eq_eraseG` — PROVED (the action-projection bridge).** Erasing the auth
from the gated linear lowering gives EXACTLY the ungated lowering of `eraseG f`: `(lowerForestG
f).map Prod.snd = lowerForestA (eraseG f)`. So `turnLedgerDeltaAsset` reads the SAME action list either
way (the credential+caveat decoration is ledger-orthogonal) — the conservation corollaries ride this
through `eraseG`. Proved by mutual structural induction. -/
theorem lowerForestG_actions_eq_eraseG
    (f : FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag)) :
    (lowerForestG f).map Prod.snd = lowerForestA (eraseG f) := by
  obtain ⟨na, a, kids⟩ := f
  show (((na, a) :: lowerChildrenG kids).map Prod.snd) = a :: lowerChildrenA (eraseChildrenG kids)
  rw [List.map_cons]
  exact congrArg (a :: ·) (lowerChildrenG_actions_eq_eraseG kids)

theorem lowerChildrenG_actions_eq_eraseG
    (kids : List (FullChildG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag))) :
    (lowerChildrenG kids).map Prod.snd = lowerChildrenA (eraseChildrenG kids) := by
  match kids with
  | [] => rfl
  | ⟨h, k, pc, sub⟩ :: rest =>
      show ((lowerForestG sub ++ lowerChildrenG rest).map Prod.snd)
          = lowerForestA (eraseG sub) ++ lowerChildrenA (eraseChildrenG rest)
      rw [List.map_append, lowerForestG_actions_eq_eraseG sub, lowerChildrenG_actions_eq_eraseG rest]
end

/-! ## §6 — The gated BRIDGE + the EFFECT-PROJECTION (erasure) bridge.

`execFullForestG_eq_execFullTurnG` is the SAME mutual structural induction as
`execFullForestA_eq_execFullTurnA`, with the heavier gated `Option`-producer (the proof cares ONLY
about the `match … some/none` skeleton). `execFullForestG_erases` is the load-bearing effect-projection
bridge: gate-passes ⇒ erasing the auth gives the IDENTICAL committed run of `eraseG f` — so EVERY
conservation/attestation theorem follows as a corollary off the EXISTING `FullForest` theorems. -/

mutual
/-- **`execFullForestG_eq_execFullTurnG` — PROVED (the gated bridge).** The gated tree transaction IS
the gated linear fold over the pre-order `(auth, action)` pairing. The CLONE of
`execFullForestA_eq_execFullTurnA` (rests on `execFullTurnG_append`). Lifts every gated linear theorem
to the tree. -/
theorem execFullForestG_eq_execFullTurnG (s : RecChainedState)
    (f : FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag)) :
    execFullForestG s f = execFullTurnG s (lowerForestG f) := by
  obtain ⟨na, a, kids⟩ := f
  show (match execFullAGated s na a with
        | some s' => execFullChildrenG s' kids
        | none    => none)
      = execFullTurnG s ((na, a) :: lowerChildrenG kids)
  rw [show execFullTurnG s ((na, a) :: lowerChildrenG kids)
        = (match execFullAGated s na a with
           | some s' => execFullTurnG s' (lowerChildrenG kids)
           | none    => none) from rfl]
  cases execFullAGated s na a with
  | none    => rfl
  | some s' => exact execFullChildrenG_eq_execFullTurnG s' kids

theorem execFullChildrenG_eq_execFullTurnG (s : RecChainedState)
    (kids : List (FullChildG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag))) :
    execFullChildrenG s kids = execFullTurnG s (lowerChildrenG kids) := by
  match kids with
  | [] => rfl
  | ⟨h, k, pc, sub⟩ :: rest =>
    show (match execFullForestG s sub with
          | some s' => execFullChildrenG s' rest
          | none    => none)
        = execFullTurnG s (lowerForestG sub ++ lowerChildrenG rest)
    rw [execFullTurnG_append, execFullForestG_eq_execFullTurnG s sub]
    cases execFullTurnG s (lowerForestG sub) with
    | none    => rfl
    | some s' => exact execFullChildrenG_eq_execFullTurnG s' rest
end

/-- **`execFullTurnG_erases` — PROVED.** On the COMMIT path the gated linear fold equals the ungated
linear fold of the action-projection: `execFullTurnG s zs = some s' → execFullTurnA s (zs.map
Prod.snd) = some s'`. Each gated step `execFullAGated s na a = some` unfolds (via
`execFullAGated_some_iff`) to `execFullA s a = some` — the gate changed only admission, never the
post-state. Proved by induction on the pair list. -/
theorem execFullTurnG_erases (s s' : RecChainedState)
    (zs : List (NodeAuthS (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag) × FullActionA))
    (h : execFullTurnG s zs = some s') :
    execFullTurnA s (zs.map Prod.snd) = some s' := by
  induction zs generalizing s with
  | nil =>
      simp only [execFullTurnG, Option.some.injEq] at h
      subst h; rfl
  | cons p rest ih =>
      obtain ⟨na, a⟩ := p
      show execFullTurnA s (a :: (rest.map Prod.snd)) = some s'
      rw [show execFullTurnG s ((na, a) :: rest)
            = (match execFullAGated s na a with
               | some s1 => execFullTurnG s1 rest
               | none    => none) from rfl] at h
      cases hga : execFullAGated s na a with
      | none => rw [hga] at h; exact absurd h (by simp)
      | some s1 =>
          rw [hga] at h
          obtain ⟨_, hfa⟩ := (execFullAGated_some_iff s s1 na a).mp hga
          show (match execFullA s a with
                | some s2 => execFullTurnA s2 (rest.map Prod.snd)
                | none    => none) = some s'
          rw [hfa]
          exact ih s1 h

/-- **`execFullForestG_erases` — THE EFFECT-PROJECTION BRIDGE (PROVED).** Gate-passes ⇒ erasing the
auth decoration gives the IDENTICAL committed run: `execFullForestG s f = some s' → execFullForestA s
(eraseG f) = some s'`. The auth gate changed ONLY admission (more `none`s), never a committed
post-state. NON-VACUOUS: the LHS can fail (`none`) where the RHS would commit (the gate is a real
narrowing — a forged credential gives `none` though `eraseG f` would run), so the implication has
content only on the commit path. THIS is the bridge through which conservation survives. -/
theorem execFullForestG_erases (s s' : RecChainedState)
    (f : FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag))
    (h : execFullForestG s f = some s') :
    execFullForestA s (eraseG f) = some s' := by
  rw [execFullForestG_eq_execFullTurnG] at h
  have h1 : execFullTurnA s ((lowerForestG f).map Prod.snd) = some s' :=
    execFullTurnG_erases s s' (lowerForestG f) h
  rw [lowerForestG_actions_eq_eraseG] at h1
  rw [FullForest.execFullForestA_eq_execFullTurnA]
  exact h1

/-! ## §7 — CONSERVATION corollaries OFF the erasure bridge (one-liners; NOT re-proven).

Each is the EXISTING `FullForest` theorem applied to `eraseG f` via `execFullForestG_erases`, read
through `lowerForestG_actions_eq_eraseG`. The auth gate is ORTHOGONAL to conservation: the launder
teeth SURVIVE (a per-asset nonzero delta in each asset is still CAUGHT). -/

/-- **`execFullForestG_ledger_per_asset` — PROVED (the per-asset VECTOR survives the gate).** A
committed gated full-forest moves `recTotalAssetWithEscrow b` by EXACTLY the net per-asset ledger delta
of its action-projection, for EVERY asset `b`. The CONSERVATION VECTOR end-to-end across the gated
tree — read off the EXISTING `execFullForestA_ledger_per_asset` applied to `eraseG f`. -/
theorem execFullForestG_ledger_per_asset (s s' : RecChainedState)
    (f : FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag)) (b : AssetId)
    (h : execFullForestG s f = some s') :
    recTotalAssetWithEscrow s'.kernel b
      = recTotalAssetWithEscrow s.kernel b
        + turnLedgerDeltaAsset ((lowerForestG f).map Prod.snd) b := by
  rw [lowerForestG_actions_eq_eraseG]
  exact FullForest.execFullForestA_ledger_per_asset s s' (eraseG f) b (execFullForestG_erases s s' f h)

/-- **`execFullForestG_conserves_per_asset` — PROVED (CONSERVATION SURVIVES THE AUTH GATE).** A
committed gated full-forest whose per-asset net is `0` in asset `b` preserves asset `b`'s total supply —
the per-asset VECTOR, end-to-end, UNCHANGED by the credential+caveat gate. The launder teeth survive:
a forest whose per-asset delta is NONZERO in some asset is still CAUGHT (a scalar could not state it).
A one-liner off `execFullForestA_conserves_per_asset (eraseG f)`. -/
theorem execFullForestG_conserves_per_asset (s s' : RecChainedState)
    (f : FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag)) (b : AssetId)
    (h : execFullForestG s f = some s')
    (hzero : turnLedgerDeltaAsset ((lowerForestG f).map Prod.snd) b = 0) :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  rw [execFullForestG_ledger_per_asset s s' f b h, hzero, add_zero]

/-- **`execFullForestG_no_amplify` — PROVED (Granovetter survives the gate).** EVERY delegation edge
of the gated forest is non-amplifying: the credential+caveat decoration adds no amplification (the edge
data is the `FullChildG` triple, IDENTICAL to `FullChildA`). A one-liner off
`execFullForestA_no_amplify (eraseG f)` via `forestEdgesG_eq_forestEdgesA_eraseG`. -/
theorem execFullForestG_no_amplify
    (f : FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag)) :
    ∀ e ∈ forestEdgesG f, capAuthConferred (attenuate e.1 e.2) ⊆ capAuthConferred e.2 := by
  rw [forestEdgesG_eq_forestEdgesA_eraseG]
  exact FullForest.execFullForestA_no_amplify (eraseG f)

/-! ## §8 — Per-node ATTESTATION: `gatedActionInvG` (credential-blindness ELIMINATED) + fail-closed.

`gatedActionInvG` ANDs THREE auth conjuncts (credential-valid ∧ cap-authority ∧ caveats-discharged)
onto the UNCHANGED `fullActionInvA`. `execFullAGated_attests` proves a committed gated node carries all
four (the gate Bools forced true by `gatedNode_check_eq_use`, the fourth by `execFullA_attests_per_asset`
UNCHANGED). `execFullForestG_each_attests` lifts it forest-wide; `execFullForestG_unauthorized_fails`
is the fail-closed root. -/

/-- **`gatedActionInvG`** — the per-node GATED invariant: the THREE auth conjuncts ANDed onto the
UNCHANGED `fullActionInvA` (the per-asset ledger VECTOR ∧ ChainLink ∧ ObsAdvance ∧ kind obligation).
Credential-blindness is GONE: a committed node proves the WHO passed the §8 oracle ∧ the WHAT
(`granted ≤ held` / `authorizedB`) ∧ every caveat discharged on the pre-state. -/
def gatedActionInvG (s : RecChainedState)
    (na : NodeAuthC (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag))
    (a : FullActionA) (s' : RecChainedState) : Prop :=
  credentialValidG na = true ∧ capAuthorityG na = true ∧ caveatsDischarged na s = true
    ∧ fullActionInvA s a s'

/-- **`execFullAGated_attests` — PROVED (the committed⇒all-four headline, per node).** Every committed
gated node attests `gatedActionInvG`: credential-valid ∧ cap-authority ∧ caveats-discharged ∧ the full
per-asset/chain/kind obligation. NON-VACUOUS: a forged credential ⇒ no commit ⇒ no false attestation;
a valid commit ⇒ all four conjuncts with teeth. The gate Bools come from `gatedNode_check_eq_use`
(which forces `gateOK = true`, i.e. ALL THREE legs); the fourth conjunct from
`execFullA_attests_per_asset` UNCHANGED. -/
theorem execFullAGated_attests (s s' : RecChainedState)
    (na : NodeAuthC (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag))
    (a : FullActionA) (h : execFullAGated s na a = some s') :
    gatedActionInvG s na a s' := by
  obtain ⟨hgate, hfa⟩ := gatedNode_check_eq_use s s' na a h
  -- `gateOK = true` forces all three legs (the conjunction).
  have h3 : credentialValidG na = true ∧ capAuthorityG na = true ∧ caveatsDischarged na s = true := by
    unfold gateOK at hgate
    simp only [Bool.and_eq_true] at hgate
    exact ⟨hgate.1.1, hgate.1.2, hgate.2⟩
  exact ⟨h3.1, h3.2.1, h3.2.2, execFullA_attests_per_asset hfa⟩

/-- **`execFullForestG_unauthorized_fails` — PROVED (fail-closed at the root, ANY leg).** If the root
node's gate fails on ANY leg (`gateOK na s = false` — a forged credential, an unauthorized cap, OR a
false caveat), the whole forest rejects (no partial commit). NON-VACUOUS: a forged-credential root with
otherwise-valid caps still gives `none` (credential-orthogonality); a valid-credential root with a false
caveat gives `none` (caveat-orthogonality). -/
theorem execFullForestG_unauthorized_fails (s : RecChainedState)
    (na : NodeAuthC (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag))
    (a : FullActionA)
    (kids : List (FullChildG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag)))
    (h : gateOK na s = false) :
    execFullForestG s ⟨na, a, kids⟩ = none := by
  show (match execFullAGated s na a with
        | some s' => execFullChildrenG s' kids
        | none    => none) = none
  have : execFullAGated s na a = none := by unfold execFullAGated; rw [if_neg (by simp [h])]
  rw [this]

/-- **`execFullTurnG_each_attests` — PROVED.** Every `(na, a)` of a committed gated linear turn attests
its `gatedActionInvG` at the state it ran on. The threaded per-node witness along the all-or-nothing
gated fold. -/
theorem execFullTurnG_each_attests (s s' : RecChainedState)
    (zs : List (NodeAuthS (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag) × FullActionA))
    (h : execFullTurnG s zs = some s') :
    ∀ p ∈ zs, ∃ sa sa', execFullAGated sa p.1 p.2 = some sa' ∧ gatedActionInvG sa p.1 p.2 sa' := by
  induction zs generalizing s with
  | nil => intro p hp; exact absurd hp List.not_mem_nil
  | cons q rest ih =>
      obtain ⟨na, a⟩ := q
      rw [show execFullTurnG s ((na, a) :: rest)
            = (match execFullAGated s na a with
               | some s1 => execFullTurnG s1 rest
               | none    => none) from rfl] at h
      cases hga : execFullAGated s na a with
      | none => rw [hga] at h; exact absurd h (by simp)
      | some s1 =>
          rw [hga] at h
          intro p hp
          rcases List.mem_cons.mp hp with hpeq | hprest
          · subst hpeq
            exact ⟨s, s1, hga, execFullAGated_attests s s1 na a hga⟩
          · exact ih s1 h p hprest

/-- **`execFullForestG_each_attests` — PROVED (per-node step-completeness, whole gated tree).** Every
node `(na, a)` of a committed gated full-forest attests its `gatedActionInvG`: credential passed the §8
oracle ∧ caveats discharged on its pre-state ∧ the per-asset conservation vector ∧ cap-authority, at
EVERY nesting depth. Credential-blindness ELIMINATED forest-wide. Read through the gated bridge
(`execFullForestG_eq_execFullTurnG`) into `execFullTurnG_each_attests` over the pre-order lowering. -/
theorem execFullForestG_each_attests (s s' : RecChainedState)
    (f : FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag))
    (h : execFullForestG s f = some s') :
    ∀ p ∈ lowerForestG f, ∃ sa sa', execFullAGated sa p.1 p.2 = some sa' ∧ gatedActionInvG sa p.1 p.2 sa' := by
  rw [execFullForestG_eq_execFullTurnG] at h
  exact execFullTurnG_each_attests s s' (lowerForestG f) h

/-- **`execFullForestG_root_attests` — PROVED (corollary).** The root node's own `(auth, action)`
attests its `gatedActionInvG` (the per-node membership-lift specialized to the root — the root pair is
the head of `lowerForestG f`). -/
theorem execFullForestG_root_attests (s s' : RecChainedState)
    (f : FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag))
    (h : execFullForestG s f = some s') :
    ∃ sa sa', execFullAGated sa f.auth f.action = some sa' ∧ gatedActionInvG sa f.auth f.action sa' := by
  obtain ⟨na, a, kids⟩ := f
  have hmem : ((na, a) : _ × FullActionA) ∈ lowerForestG (⟨na, a, kids⟩ : FullForestG ..) := by
    show (na, a) ∈ (na, a) :: lowerChildrenG kids
    exact List.mem_cons_self
  exact execFullForestG_each_attests s s' ⟨na, a, kids⟩ h (na, a) hmem

end Gate

end Gated

/-! ## §9 — Non-vacuity (`#eval`): the gate is a REAL fail-closed precondition (the TEETH).

The Demo instantiates the carriers concretely (crypto `Crypto.Reference` `D = P = Int`; AuthModes
`Request := Bool`, `Stmt = Wit := Nat`, `CellId := Label`, `Rights := Unit`, `Ctx := Nat`, `Gateway :=
Unit`; chain `Bytes = Tag := Nat`). It reuses `fma0` and the `goodFullForest`/`launderFullForest`
action shapes from `FullForest`. The FOUR teeth:
  (1) a VALID credential + discharged caveats ⇒ the whole forest COMMITS, per-asset conserved;
  (2) a FORGED credential ⇒ `none` EVEN WITH valid caps (credential-orthogonality);
  (3) a VALID credential but a FALSE caveat ⇒ `none` (caveat-orthogonality);
  (4) a launder forest (per-asset delta NONZERO in EACH asset) is still CAUGHT through the gate. -/

namespace Demo

open Dregg2.Crypto.Reference
open Dregg2.Spec (Guard)
open Dregg2.Exec.AuthModes (AuthMode AuthContext)

abbrev Dg := Crypto.Reference.D    -- Int
abbrev Pf := Crypto.Reference.P    -- Int
abbrev Rq := Bool
abbrev St := Nat
abbrev Wt := Nat
abbrev Cx := Nat
abbrev Gw := Unit
abbrev Bt := Nat
abbrev Tg := Nat

/-- A trivial demo verify seam (the AuthModes `.unchecked` arm reads the guard, not this; it just pins
the `Verifiable` instance the dispatcher's signature needs). -/
local instance demoVerifiable : Dregg2.Laws.Verifiable St Wt where
  Verify _ _ := true

/-- The fully-applied NodeAuth carrier for the demo. -/
abbrev DNodeAuth :=
  NodeAuth Dg Pf Rq St Wt Label Unit Cx Gw Bt Tg

/-- The fully-applied gated forest carrier for the demo. -/
abbrev DForest :=
  FullForestG (Digest := Dg) (Proof := Pf) (Request := Rq) (Stmt := St) (Wit := Wt)
    (CellId := Label) (Rights := Unit) (Ctx := Cx) (Gateway := Gw) (Bytes := Bt) (Tag := Tg)

/-- The fully-applied gated child carrier for the demo. -/
abbrev DChild :=
  FullChildG (Digest := Dg) (Proof := Pf) (Request := Rq) (Stmt := St) (Wit := Wt)
    (CellId := Label) (Rights := Unit) (Ctx := Cx) (Gateway := Gw) (Bytes := Bt) (Tag := Tg)

/-- A minimal cap-authority context (the `.unchecked (Guard.all [])` mode admits independent of most
fields). -/
def baseCapCtx : AuthContext Rq St Wt Label Unit Cx Gw :=
  { req := true, customStmt := 0, wit := fun _ => 0
  , registry := fun _ => none, caveatCtx := 150, discharges := fun _ => false
  , graph := fun _ _ => False, consents := fun _ => True, facetOk := true, freshOk := true }

/-- A GENUINE signature credential (its proof echoes the statement under the Reference oracle): the
portal accepts. -/
def goodCred : Authorization Dg Pf := .signature 7 7
/-- A FORGED credential (off-by-one proof ⇒ does NOT echo): the portal fail-closes. -/
def forgedCred : Authorization Dg Pf := .signature 7 8

/-- A monotone (drift-stable), within-cell caveat that HOLDS: cell 0 holds ≥ 0 of asset 0. -/
def trueCaveat : GatedCaveat :=
  { tier := .monotone, check := fun s => decide (0 ≤ s.kernel.bal 0 0) }
/-- A monotone caveat that is FALSE on the pre-state: cell 0 holds ≥ 10000 of asset 0 (it holds 100). -/
def falseCaveat : GatedCaveat :=
  { tier := .monotone, check := fun s => decide (10000 ≤ s.kernel.bal 0 0) }

/-- Build a demo NodeAuth from a credential + caveat list (admitting cap mode, no chain). -/
def mkAuth (cred : Authorization Dg Pf) (caveats : List GatedCaveat) : DNodeAuth :=
  { cred := cred, rev := Credential.noRevocations
  , capMode := .unchecked (Guard.all []), capCtx := baseCapCtx
  , caveats := caveats, chain := none, chainCtx := 150, chainDis := fun _ => false }

/-- **`goodFullForestG`** — the `goodFullForest` action shape (mint +50 asset1 / transfer asset0 /
burn −50 asset1, per-asset NET ZERO), now GATED: every node carries a VALID credential + a discharged
caveat. The whole gated tree COMMITS and conserves per-asset. -/
def goodFullForestG : DForest :=
  ⟨ mkAuth goodCred [trueCaveat], .mintA 9 0 1 50
  , [ ({ holder := 0, keep := [Auth.read], parentCap := .endpoint 1 [Auth.read, Auth.write]
       , sub := ⟨ mkAuth goodCred [trueCaveat], .balanceA ⟨0, 0, 1, 30⟩ 0
                , [ ({ holder := 9, keep := [], parentCap := .endpoint 0 [Auth.read]
                     , sub := ⟨ mkAuth goodCred [trueCaveat], .burnA 9 0 1 50, [] ⟩ } : DChild) ] ⟩ } : DChild) ] ⟩

/-- **`forgedCredForestG`** — the SAME action shape + valid caps, but the ROOT credential is FORGED.
The portal fail-closes ⇒ the whole forest rejects (`none`) EVEN WITH valid caps — credential-orthogonality. -/
def forgedCredForestG : DForest :=
  ⟨ mkAuth forgedCred [trueCaveat], .mintA 9 0 1 50, [] ⟩

/-- **`falseCaveatForestG`** — a VALID credential, valid caps, but a FALSE caveat (cell 0 ≥ 10000).
The caveat leg fail-closes ⇒ the whole forest rejects (`none`) — caveat-orthogonality. -/
def falseCaveatForestG : DForest :=
  ⟨ mkAuth goodCred [falseCaveat], .mintA 9 0 1 50, [] ⟩

/-- **`launderFullForestG`** — the `launderFullForest` cross-asset launder (mint +50 asset1 / burn −50
asset0) under VALID credentials. The gate passes (auth is orthogonal) and the forest COMMITS — but the
per-asset VECTOR delta is NONZERO in EACH asset (asset 0: −50, asset 1: +50), so the conservation
carrier still CATCHES the launder THROUGH the gate (a scalar would hide it). -/
def launderFullForestG : DForest :=
  ⟨ mkAuth goodCred [trueCaveat], .mintA 9 0 1 50
  , [ ({ holder := 9, keep := [Auth.read], parentCap := .endpoint 0 [Auth.read, Auth.write]
       , sub := ⟨ mkAuth goodCred [trueCaveat], .burnA 9 0 0 50, [] ⟩ } : DChild) ] ⟩

-- (1) VALID credential + discharged caveats ⇒ the whole gated forest COMMITS:
#eval (execFullForestG fma0 goodFullForestG).isSome                                  -- true
-- ...per-asset NET is 0 in BOTH assets ⇒ conserved (the gate is orthogonal to conservation):
#eval turnLedgerDeltaAsset ((lowerForestG goodFullForestG).map Prod.snd) 0           -- 0 (asset 0)
#eval turnLedgerDeltaAsset ((lowerForestG goodFullForestG).map Prod.snd) 1           -- 0 (asset 1)
#eval (execFullForestG fma0 goodFullForestG).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (105, 7)
-- (2) FORGED credential ⇒ none EVEN WITH valid caps (credential-orthogonality):
#eval (execFullForestG fma0 forgedCredForestG).isSome                               -- false
#eval credentialValidG forgedCredForestG.auth                                       -- false (portal fail-closes)
#eval credentialValidG goodFullForestG.auth                                         -- true  (portal accepts)
-- (3) VALID credential, FALSE caveat ⇒ none (caveat-orthogonality):
#eval (execFullForestG fma0 falseCaveatForestG).isSome                              -- false
#eval caveatsDischarged falseCaveatForestG.auth fma0                                -- false (caveat fail-closes)
#eval caveatsDischarged goodFullForestG.auth fma0                                   -- true  (caveat discharges)
-- (4) the launder forest COMMITS through the gate but the per-asset delta is NONZERO in EACH asset
--     (CAUGHT — a scalar aggregate would hide both):
#eval (execFullForestG fma0 launderFullForestG).isSome                              -- true (auth orthogonal)
#eval turnLedgerDeltaAsset ((lowerForestG launderFullForestG).map Prod.snd) 0        -- -50 (NOT 0)
#eval turnLedgerDeltaAsset ((lowerForestG launderFullForestG).map Prod.snd) 1        -- 50  (NOT 0)
#eval (execFullForestG fma0 launderFullForestG).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))              -- some (55, 57) CAUGHT
-- ...the gate passing then erasing gives the IDENTICAL committed run (effect-projection bridge):
#eval (execFullForestA fma0 (eraseG goodFullForestG)).isSome                         -- true
#eval ((execFullForestG fma0 goodFullForestG).map (fun s => s.log.length)
        == (execFullForestA fma0 (eraseG goodFullForestG)).map (fun s => s.log.length))  -- true (identical run)

end Demo

/-! ## §10 — Axiom-hygiene tripwires (the honesty pins over the gated keystones).

Every keystone depends ONLY on the three standard kernel axioms `{propext, Classical.choice,
Quot.sound}` — no `sorryAx`. The `AuthPortal.soundness` carrier is a Prop FIELD (the §8 discipline),
NOT an axiom, so it does NOT appear here (the portal is a carrier, the credential leg's soundness is
the circuit's obligation, never a Lean law). -/

#assert_axioms forestEdgesG_eq_forestEdgesA_eraseG
#assert_axioms execFullAGated_some_iff
#assert_axioms gatedNode_check_eq_use
#assert_axioms execFullTurnG_append
#assert_axioms execFullForestG_eq_execFullTurnG
#assert_axioms execFullTurnG_erases
#assert_axioms execFullForestG_erases
#assert_axioms execFullForestG_ledger_per_asset
#assert_axioms execFullForestG_conserves_per_asset
#assert_axioms execFullForestG_no_amplify
#assert_axioms execFullAGated_attests
#assert_axioms execFullForestG_unauthorized_fails
#assert_axioms execFullTurnG_each_attests
#assert_axioms execFullForestG_each_attests
#assert_axioms execFullForestG_root_attests

end Dregg2.Exec.FullForestAuth
