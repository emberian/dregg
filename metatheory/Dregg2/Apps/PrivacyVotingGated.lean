/-
# Dregg2.Apps.PrivacyVotingGated — a PRIVATE VOTE as a VERIFIED USERSPACE APP on the ONE gated executor.

A private ballot: each ENFRANCHISED voter casts EXACTLY ONE vote, gated by a credential, with the vote
recorded as a NULLIFIER (the vote-as-nullifier anti-replay discipline — a voter's ballot nullifier slot,
once written, can never be silently re-cast). This is the executed, credential-gated dual of two
already-proved keystones:

  * `Dregg2.Apps.MultisigVote` already runs vote-as-nullifier on the REAL kernel: a cast vote inserts
    the voter's id into the kernel's spent-note seen-set, so a double-vote is rejected by the SAME
    fail-closed gate that stops a double-spend (`note_no_double_spend` / `note_spend_inserts`). That is
    the seen-SET discipline. THIS module re-models the SAME anti-replay through the ONE production turn
    entry `Dregg2.Exec.FullForestAuth.execFullForestG` (the `dregg_exec_full_forest_auth` 4-leg gate:
    credential ∧ cap-authority ∧ caveats-discharged ∧ NOT-revoked), recording the vote-nullifier as a
    `WriteOnce` SLOT on the ballot cell — so no-double-vote is enforced BY THE EXECUTOR's caveat gate,
    on the EXECUTED turn the running system runs, not merely by a model-level set.
  * `Dregg2.Exec.PrivacyTheorems` proves the nullifier NO-DOUBLE-SPEND anti-replay (the Zcash
    discipline: a nullifier already in the spent set fail-closes, and a spent nullifier never leaves
    the set — `nullifier_set_monotone` / `seq_no_respend`). A cast-vote IS a nullifier-spend: the
    ballot's per-voter nullifier slot is the on-chain "spent" mark, and the `WriteOnce` caveat is the
    set-membership gate (`old = 0` ⇒ fresh ⇒ admitted; `old ≠ 0 ∧ new ≠ old` ⇒ already-voted ⇒ rejected).

## The vote as a credential-gated op through `execFullForestG`

A cast-vote is a single `SetField` on the ballot cell writing the voter's NULLIFIER mark, modelled as a
GATED leaf node `⟨ mkAuth cred [], .setFieldA actor ballotCell voterNullSlot mark, [] ⟩` run through the
4-leg gate. `mkAuth cred []` supplies an admitting cap-mode (`.unchecked (Guard.all [])`), an empty
within-cell caveat list (so the GATE's caveat leg is vacuously discharged — the SLOT caveats are
enforced separately by `stateStepGuarded` inside `execFullA`), no chain, and (by default) nullifier `0`.

## The ballot cell's SLOT CAVEATS (the executor-enforced ballot invariants)

The ballot cell carries (`s.kernel.slotCaveats ballotCell`):
  * `WriteOnce voterNull A` — voter A's ballot nullifier slot: once A has voted (slot ≠ 0), it can NEVER
    be silently re-cast → **NO DOUBLE-VOTE** (vote-as-nullifier anti-replay, the executed dual of the
    `PrivacyTheorems` nullifier no-double-spend);
  * `WriteOnce voterNull B` — voter B's ballot nullifier slot, identically.

`stateStepGuarded` reads exactly these on EVERY `SetField` to the ballot cell and FAILS CLOSED on a
re-cast — so no-double-vote is enforced BY THE EXECUTOR, not merely carried.

## End-user theorems (general; concrete `#guard` witnesses for non-vacuity)

  1. `pv_forged_credential_rejected` — a FORGED voter credential ⇒ the whole gated turn rejects (`none`),
     ∀ state — nobody can vote without a genuine credential.
  2. `pv_revoked_voter_rejected`     — a REVOKED voter credential (its nullifier in `s.kernel.revoked`)
     ⇒ rejected, ∀ state (via `gateOK_revoked_fails`) — a disenfranchised/revoked voter can never vote
     again (even with a perfectly valid signature: validity and revocation are orthogonal legs).
  3. `pv_no_double_vote`             — a SECOND cast over an already-recorded vote-nullifier slot is
     rejected by the executor's `WriteOnce` caveat (`caveatsAdmit = false`), EVEN with a genuine,
     non-revoked credential — vote-as-nullifier anti-replay, the executed dual of the `PrivacyTheorems`
     nullifier no-double-spend discipline.
  4. `pv_cast_conserves`            — a committed cast-vote moves NO asset's supply (per-asset Δ = 0):
     the ballot write touches metadata, never balance.

Plus a parallel **TOKEN + MACAROON-CHAIN** voter arm (§2b/§5b): `.token` credentials for the WHO leg
and `NodeAuth.chain := some …` for the macaroon `verifiedChainGate` caveat leg — with
`pv_token_forged_rejected`, `pv_chain_forged_rejected`, `pv_chain_caveat_violation_rejected`, and
`pv_token_good_commits` witnessed on `ballot0` alongside the signature arm.

Plus a concrete ballot-cell state (`ballot0`) whose `#guard`s show a GOOD first cast COMMITS, a forged
credential gives `none`, a revoked voter gives `none`, and a double-vote gives `none` — every theorem
witnessed REAL, not vacuous.

Does NOT touch `MultisigVote.lean`, `PrivacyTheorems.lean`,
`FullForestAuth.lean`, nor `Dregg2.lean`. Reuses ONLY the proved gated-executor keystones
(`gateOK_revoked_fails`, `execFullForestG_unauthorized_fails`, `execFullForestG_conserves_per_asset`)
and the proved `stateStepGuarded` fail-closed caveat teeth.
-/
import Dregg2.Exec.GatedForestCfg

namespace Dregg2.Apps.PrivacyVotingGated

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.EffectsState
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.StarbridgeGated
open Dregg2.Exec.StarbridgeGated
open Dregg2.Exec.AuthModes (unchecked_unconstrained_admits)
open Dregg2.Spec (Guard)
open Dregg2.Authority
open Dregg2.Authority.CaveatChain
open Dregg2.Authority.CaveatChain.Demo

/-- Pin the toy `MacKernel` at the starbridge `Tag`/`Bytes` carriers so `#guard`/`decide` can reduce
`chainGateG` (the Demo namespace's instance is not otherwise visible to evaluation here).
DEVACUIFIED in lockstep with `CaveatChain.Demo.honestMacKernel`: `Tagged`/`verifyTag_sound` are the
EUF-CMA carrier shape over the toy recompute-compare oracle, NOT `True`. -/
instance pvMacKernel : MacKernel (Key Tg) Bt Tg where
  mac k m := 31 * k + 7 * m + 1
  Tagged k m t := t = 31 * k + 7 * m + 1
  unforgeable := ∀ k m t, decide (31 * k + 7 * m + 1 = t) = true → t = 31 * k + 7 * m + 1
  verifyTag_sound := by intro hunf k m t h; exact hunf k m t h

/-! ## §1 — The private-vote DOMAIN at the Demo carriers (the ballot cell, the per-voter nullifier slots).

The ballot cell holds, per enfranchised voter, ONE `WriteOnce` nullifier slot. A cast vote writes the
voter's nullifier mark to their slot; `WriteOnce` then permits the FIRST cast (`old = 0`, fresh — not
yet voted) and forbids any later re-cast (`old ≠ 0`, already voted) — the vote-as-nullifier anti-replay.
The slot's freshness/spent state IS the on-chain nullifier set, exactly as in `PrivacyTheorems`. -/

/-- The ballot cell holding the per-voter nullifier marks (the tally cell). Cell `0` so the actor can be
`0` too — `stateAuthB` is then trivially satisfied (`actor == src`), letting the credential gate and the
SLOT CAVEAT be the load-bearing admission conditions (not the cap-list). -/
abbrev ballotCell : CellId := 0

/-- The voting actor (the credential holder submitting the ballot). Equal to `ballotCell` so `stateAuthB`
holds by `actor == src` — the app's authority story rides on the §4 CREDENTIAL gate, not the c-list. -/
abbrev ballotActor : CellId := 0

/-- Voter A's ballot NULLIFIER slot — `WriteOnce`: once A has voted (slot ≠ 0) it is permanent (A cannot
re-cast). The executed dual of A's spent-note nullifier mark in `PrivacyTheorems`. -/
abbrev voterNullA : FieldName := "null_A"
/-- Voter B's ballot NULLIFIER slot — `WriteOnce`: once B has voted it is permanent (no double-vote). -/
abbrev voterNullB : FieldName := "null_B"

/-- The ballot cell's factory-installed SLOT CAVEATS: each enfranchised voter's nullifier slot is
`WriteOnce`. The executor reads these on EVERY cast (`stateStepGuarded`), so a re-cast fail-closes — the
no-double-vote teeth. (Two voters here; the pattern is uniform per voter.) -/
def ballotCaveats : List SlotCaveat :=
  [ .writeOnce voterNullA, .writeOnce voterNullB ]

/-! ## §2 — A cast-vote as a GATED LEAF NODE through the production turn entry `execFullForestG`.

A cast-vote is a single `SetField` on the ballot cell — writing the voter's NULLIFIER mark to their slot —
decorated with a credential (the WHO) and run through the 4-leg gate. `mkAuth cred []` supplies an
admitting cap-mode, an empty within-cell caveat list (the GATE's caveat leg is vacuously discharged — the
SLOT caveat is enforced separately by `stateStepGuarded`), and no chain. So `gateOK` reduces to the
credential leg ∧ the revocation leg. -/

/-- A gated cast-vote node: credential `cred`, a `SetField voterSlot mark` on the ballot cell (recording
the voter's nullifier), no children. The production-entry shape `⟨ mkAuth cred [], action, [] ⟩`. -/
def castNode (cred : Authorization Dg Pf) (voterSlot : FieldName) (mark : Int) : DForest :=
  ⟨ mkAuth cred [], .setFieldA ballotActor ballotCell voterSlot mark, [] ⟩

/-- A gated cast-vote node whose credential carries a specific revocation NULLIFIER `nul` (for the
revocation theorem — the wire-supplied `credNul` the gate checks against `s.kernel.revoked`). Otherwise
identical to `castNode`. -/
def castNodeNul (cred : Authorization Dg Pf) (nul : Nat) (voterSlot : FieldName) (mark : Int) : DForest :=
  ⟨ { mkAuth cred [] with credNul := nul }, .setFieldA ballotActor ballotCell voterSlot mark, [] ⟩

/-! ## §2b — The TOKEN + MACAROON-CHAIN voter arm (parallel to the `.signature` credential arm).

The signature arm supplies the WHO via `portalVerify (.signature stmt sig)`. The token arm supplies
the WHO via `portalVerify (.token key sig)` (the HMAC macaroon tag) AND the macaroon caveat leg via
`NodeAuth.chain := some …` — `chainGateG` requires `verifiedChainGate` = HMAC replay-and-compare ∧
caveat meet. Empty within-cell `caveats` (as in `mkAuth`); the chain IS the attenuation gate. -/

/-- A genuine macaroon TOKEN credential (the tag echoes the issuer key under `Crypto.Reference`). -/
def goodTokenCred : Authorization Dg Pf := .token 7 7
/-- A FORGED macaroon TOKEN credential (wrong tag). -/
def forgedTokenCred : Authorization Dg Pf := .token 7 8

/-- The chain caveat-context for voter authorization (matches `baseCapCtx.caveatCtx = 150`). -/
def pvChainCtx : Cx := 150
/-- No third-party gateway discharges on the voter chain. -/
def pvNoDis : Discharges Gw := fun _ => false

/-- Root macaroon for the voter chain (`Macaroon::new`). -/
def pvChainRoot : Chain Cx Gw (Key Tg) Bt Tg := seed (Ctx := Cx) (Gateway := Gw) 5 9

/-- A GOOD voter macaroon chain: attenuated with `height ≥ 100` then `height ≤ 200` — admits
`pvChainCtx = 150`. -/
def pvGoodChain : Chain Cx Gw (Key Tg) Bt Tg :=
  (pvChainRoot.append { caveat := .opaque (fun h => decide (100 ≤ h)), encoded := 100 }).append
    { caveat := .opaque (fun h => decide (h ≤ 200)), encoded := 200 }

/-- A FORGED voter chain: `windowed`'s tail with the last caveat dropped (the
`test_removed_caveat_fails` attack) — `verify = false`. -/
def pvForgedChain : Chain Cx Gw (Key Tg) Bt Tg :=
  { pvGoodChain with links := pvGoodChain.links.dropLast }

/-- A caveat-VIOLATION voter chain: verifies but does NOT admit `pvChainCtx = 150` (`height ≤ 50` only). -/
def pvCaveatViolationChain : Chain Cx Gw (Key Tg) Bt Tg :=
  pvChainRoot.append { caveat := .opaque (fun h => decide (h ≤ 50)), encoded := 50 }

/-- `NodeAuth` carrying a macaroon chain (the token+chain voter decoration). -/
def mkAuthWithChain (cred : Authorization Dg Pf) (chain : Chain Cx Gw (Key Tg) Bt Tg) : DNodeAuth :=
  { mkAuth cred [] with chain := some chain, chainCtx := pvChainCtx, chainDis := pvNoDis }

/-- A gated cast-vote node with a TOKEN credential and a macaroon chain. -/
def castNodeWithChain (cred : Authorization Dg Pf) (chain : Chain Cx Gw (Key Tg) Bt Tg)
    (voterSlot : FieldName) (mark : Int) : DForest :=
  ⟨ mkAuthWithChain cred chain, .setFieldA ballotActor ballotCell voterSlot mark, [] ⟩

/-! ## §3 — The leaf-collapse bridge: a childless gated forest runs EXACTLY its single gated node. -/

/-- **`execFullForestG_leaf` (the load-bearing collapse).** A gated forest with NO children runs
EXACTLY its root gated node step: `execFullForestG s ⟨na, a, []⟩ = execFullAGated s na a`. (Both branches
of `execFullForestG`'s match collapse because `execFullChildrenG _ s' [] = some s'`.) The bridge through
which every cast-vote's `none`/`some` is read off `execFullAGated` directly. -/
theorem execFullForestG_leaf (s : RecChainedState) (na : DNodeAuth) (a : FullActionA) :
    execFullForestG s (⟨na, a, []⟩ : DForest) = execFullAGated s na a := by
  show (match execFullAGated s na a with
        | some s' => execFullChildrenG (targetOf a) s' ([] : List DChild)
        | none    => none) = execFullAGated s na a
  cases execFullAGated s na a with
  | none   => rfl
  | some _ => rfl

/-- **`execFullForestG_castNode` — the cast-vote collapse.** A childless cast-vote runs
`if gateOK then stateStepGuarded … else none`, and `execFullA (.setFieldA …) = stateStepGuarded`. The
unfolding every theorem below rests on. -/
theorem execFullForestG_castNode (s : RecChainedState) (cred : Authorization Dg Pf)
    (voterSlot : FieldName) (mark : Int) :
    execFullForestG s (castNode cred voterSlot mark)
      = (if gateOK (mkAuth cred []) s = true
         then stateStepDev s voterSlot ballotActor ballotCell mark
         else none) := by
  rw [castNode, execFullForestG_leaf, execFullAGated]
  rfl

/-- **`execFullForestG_castNodeWithChain` — the token+chain cast-vote collapse.** -/
theorem execFullForestG_castNodeWithChain (s : RecChainedState) (cred : Authorization Dg Pf)
    (chain : Chain Cx Gw (Key Tg) Bt Tg) (voterSlot : FieldName) (mark : Int) :
    execFullForestG s (castNodeWithChain cred chain voterSlot mark)
      = (if gateOK (mkAuthWithChain cred chain) s = true
         then stateStepDev s voterSlot ballotActor ballotCell mark
         else none) := by
  rw [castNodeWithChain, execFullForestG_leaf, execFullAGated]
  rfl

/-! ## §4 — The CREDENTIAL gate: a FORGED credential fails-closed (state-independent).

`gateOK (mkAuth cred []) s = credentialValidG (mkAuth cred []) && capAuthorityG (mkAuth cred []) &&
caveatsDischarged (mkAuth cred []) s && revocationGate (mkAuth cred []) s`. For `mkAuth`: the cap mode is
`.unchecked (Guard.all [])` (admits), the within-cell caveat list is `[]` (vacuously discharged, no
chain), the nullifier is `0` (not in an empty revocation registry). So `gateOK` is exactly the credential
leg `credentialValidG (mkAuth cred [])` — `portalVerify cred`. -/

/-- **`gateOK_forged_false`.** The forged credential's gate leg is FALSE
(`portalVerify (.signature 7 8) = decide (7 = 8) = false`) — independent of state, so the whole gate
`gateOK (mkAuth forgedCred []) s = false`. -/
theorem gateOK_forged_false (s : RecChainedState) : gateOK (mkAuth forgedCred []) s = false := by
  have hcred : credentialValidG (mkAuth forgedCred []) = false := by decide
  unfold gateOK
  rw [hcred]
  simp

/-! ## §4b — The TOKEN + MACAROON-CHAIN gate legs (parallel to §4's signature forgery). -/

/-- **`gateOK_token_forged_false`.** A FORGED macaroon token's gate leg is FALSE
(`portalVerify (.token 7 8) = false`) — independent of state and chain. -/
theorem gateOK_token_forged_false (s : RecChainedState) (chain : Chain Cx Gw (Key Tg) Bt Tg) :
    gateOK (mkAuthWithChain forgedTokenCred chain) s = false := by
  have hcred : credentialValidG (mkAuthWithChain forgedTokenCred chain) = false := rfl
  unfold gateOK
  rw [hcred]
  simp

/-- **`gateOK_chain_forged_false`.** A FORGED macaroon chain (HMAC tail mismatch) fails the
`chainGateG` leg — independent of state, even with a genuine token. -/
theorem gateOK_chain_forged_false (s : RecChainedState) :
    gateOK (mkAuthWithChain goodTokenCred pvForgedChain) s = false := by
  have hverify : pvForgedChain.verify = false := by decide
  have hcav : caveatsDischarged (mkAuthWithChain goodTokenCred pvForgedChain) s = false := by
    simp only [caveatsDischarged, mkAuthWithChain, mkAuth, List.all_nil, chainGateG, hverify]
    decide
  unfold gateOK
  rw [hcav]
  simp

/-- **`gateOK_chain_caveat_violation_false`.** A verifying chain whose caveats do NOT admit
`pvChainCtx` fails the `chainGateG` leg — the caveat meet bites. -/
theorem gateOK_chain_caveat_violation_false (s : RecChainedState) :
    gateOK (mkAuthWithChain goodTokenCred pvCaveatViolationChain) s = false := by
  have hverify : pvCaveatViolationChain.verify = true := by decide
  have hadmits : pvCaveatViolationChain.admits pvChainCtx pvNoDis = false := by decide
  have hcav : caveatsDischarged (mkAuthWithChain goodTokenCred pvCaveatViolationChain) s = false := by
    simp only [caveatsDischarged, mkAuthWithChain, mkAuth, List.all_nil, chainGateG, hverify, hadmits]
    decide
  unfold gateOK
  rw [hcav]
  simp

/-! ## §5 — END-USER THEOREM 1: a FORGED voter credential ⇒ the whole gated turn REJECTS. -/

/-- **`pv_forged_credential_rejected`.** A cast-vote (any voter-slot/mark) presented with a
FORGED credential is rejected by the production turn entry: `execFullForestG s (castNode forgedCred …) =
none`, for EVERY pre-state `s`. The credential leg fail-closes ⇒ the whole forest rolls back — nobody
can vote without a genuine credential. -/
theorem pv_forged_credential_rejected (s : RecChainedState) (voterSlot : FieldName) (mark : Int) :
    execFullForestG s (castNode forgedCred voterSlot mark) = none := by
  rw [castNode]
  exact execFullForestG_unauthorized_fails s (mkAuth forgedCred [])
    (.setFieldA ballotActor ballotCell voterSlot mark) [] (gateOK_forged_false s)

/-! ## §5b — TOKEN + MACAROON-CHAIN arm: forgery rejections and a good cast commits. -/

/-- **`pv_token_forged_rejected`.** A cast-vote with a FORGED macaroon token credential is
rejected — `execFullForestG s (castNodeWithChain forgedTokenCred pvGoodChain …) = none`, ∀ state —
even when the macaroon chain is genuine. -/
theorem pv_token_forged_rejected (s : RecChainedState) (voterSlot : FieldName) (mark : Int) :
    execFullForestG s (castNodeWithChain forgedTokenCred pvGoodChain voterSlot mark) = none := by
  rw [castNodeWithChain]
  exact execFullForestG_unauthorized_fails s (mkAuthWithChain forgedTokenCred pvGoodChain)
    (.setFieldA ballotActor ballotCell voterSlot mark) []
    (gateOK_token_forged_false s pvGoodChain)

/-- **`pv_chain_forged_rejected`.** A cast-vote with a FORGED macaroon chain is rejected —
`execFullForestG s (castNodeWithChain goodTokenCred pvForgedChain …) = none`, ∀ state — even with a
genuine token credential. -/
theorem pv_chain_forged_rejected (s : RecChainedState) (voterSlot : FieldName) (mark : Int) :
    execFullForestG s (castNodeWithChain goodTokenCred pvForgedChain voterSlot mark) = none := by
  rw [castNodeWithChain]
  exact execFullForestG_unauthorized_fails s (mkAuthWithChain goodTokenCred pvForgedChain)
    (.setFieldA ballotActor ballotCell voterSlot mark) [] (gateOK_chain_forged_false s)

/-- **`pv_chain_caveat_violation_rejected`.** A cast-vote whose macaroon chain verifies but
does NOT admit `pvChainCtx` is rejected — the chain caveat meet fail-closes. -/
theorem pv_chain_caveat_violation_rejected (s : RecChainedState) (voterSlot : FieldName) (mark : Int) :
    execFullForestG s (castNodeWithChain goodTokenCred pvCaveatViolationChain voterSlot mark) = none := by
  rw [castNodeWithChain]
  exact execFullForestG_unauthorized_fails s
    (mkAuthWithChain goodTokenCred pvCaveatViolationChain)
    (.setFieldA ballotActor ballotCell voterSlot mark) [] (gateOK_chain_caveat_violation_false s)

/-- **`pv_token_good_cast_runs_write` — the gate-passing collapse for `goodTokenCred` + `pvGoodChain`.** -/
theorem pv_token_good_cast_runs_write (s : RecChainedState) (voterSlot : FieldName) (mark : Int)
    (hgate : gateOK (mkAuthWithChain goodTokenCred pvGoodChain) s = true) :
    execFullForestG s (castNodeWithChain goodTokenCred pvGoodChain voterSlot mark)
      = stateStepDev s voterSlot ballotActor ballotCell mark := by
  rw [execFullForestG_castNodeWithChain, if_pos hgate]

/-! ## §6 — END-USER THEOREM 2 (a REVOKED voter): a revoked credential can NEVER vote.

The disenfranchisement headline: if a voter's credential nullifier sits in the COMMITTED revocation
registry `s.kernel.revoked`, EVERY cast presented with it is rejected — at EVERY reachable state. This is
the gate's revocation leg (`gateOK_revoked_fails`, reading adversary-uncontrollable kernel state), the
SAME revocation discipline `IdentityGated` proves permanent. A revoked voter can never re-validate. -/

/-- **`pv_revoked_voter_rejected` (the revoked-voter headline).** If a voter's credential
nullifier `nul` is in the COMMITTED revocation registry `s.kernel.revoked`, then EVERY cast-vote
presented with it is rejected by the production turn entry — `execFullForestG s (castNodeNul cred nul …) =
none` — at EVERY reachable state `s`. The revocation leg fail-closes ⇒ the whole forest rolls back.
NON-VACUOUS: a GENUINE (`portalVerify`-passing) credential is STILL rejected purely because the voter is
revoked — credential-validity and revocation are orthogonal legs. -/
theorem pv_revoked_voter_rejected (s : RecChainedState) (cred : Authorization Dg Pf) (nul : Nat)
    (voterSlot : FieldName) (mark : Int)
    (hrev : s.kernel.revoked.contains nul = true) :
    execFullForestG s (castNodeNul cred nul voterSlot mark) = none := by
  rw [castNodeNul]
  refine execFullForestG_unauthorized_fails s { mkAuth cred [] with credNul := nul }
    (.setFieldA ballotActor ballotCell voterSlot mark) [] ?_
  exact gateOK_revoked_fails { mkAuth cred [] with credNul := nul } s hrev

/-! ## §7 — END-USER THEOREM 3 (NO DOUBLE-VOTE): a re-cast over a recorded nullifier slot is rejected.

The anti-replay headline — the EXECUTED dual of the `PrivacyTheorems` nullifier no-double-spend and the
`MultisigVote` real-kernel double-vote rejection. The gate passes (genuine, non-revoked credential), so
`execFullForestG s (castNode goodCred …) = stateStepGuarded …`; then the `WriteOnce` caveat on the
voter's nullifier slot makes `caveatsAdmit = false` (the slot is already non-zero — the voter has voted),
so `stateStepGuarded = none` (`stateStepGuarded_caveat_violation_fails`). The whole turn rejects —
enforced BY THE EXECUTOR. The first cast (`old = 0`) IS admitted; only the re-cast fails. -/

/-- **`pv_good_cast_runs_write` — the gate-passing collapse for `goodCred`.** When the genuine,
non-revoked credential admits, a cast-vote IS its caveat-gated `SetField` — `execFullForestG s (castNode
goodCred voterSlot mark) = stateStepDev s voterSlot ballotActor ballotCell mark`. The hinge for the
no-double-vote theorem: any caveat-rejection of the WRITE rejects the whole turn. -/
theorem pv_good_cast_runs_write (s : RecChainedState) (voterSlot : FieldName) (mark : Int)
    (hgate : gateOK (mkAuth goodCred []) s = true) :
    execFullForestG s (castNode goodCred voterSlot mark)
      = stateStepDev s voterSlot ballotActor ballotCell mark := by
  rw [execFullForestG_castNode, if_pos hgate]

/-- **`pv_no_double_vote` (END-USER THEOREM 3, the anti-replay headline).** If a voter's ballot
nullifier slot already holds a recorded vote (the `WriteOnce` caveat rejects the re-cast:
`caveatsAdmit … = false`, i.e. `old ≠ 0 ∧ new ≠ old`), then a SECOND cast is rejected by the executor —
`execFullForestG s (castNode goodCred voterSlot mark) = none` — EVEN with a genuine, non-revoked
credential. A voter casts EXACTLY ONE vote; the recorded nullifier is the on-chain spent-mark, and the
`WriteOnce` slot is the membership gate — the executed dual of `PrivacyTheorems.kernel_no_double_spend`
(`nf ∈ nullifiers ⇒ noteSpendNullifier = none`) and `MultisigVote.revote_rejected`. NON-VACUOUS: the
hypothesis `caveatsAdmit … = false` is forced by the `WriteOnce` caveat on an already-voted slot. -/
theorem pv_no_double_vote (s : RecChainedState) (voterSlot : FieldName) (mark : Int)
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (hvoted : caveatsAdmit s.kernel voterSlot ballotActor ballotCell mark = false) :
    execFullForestG s (castNode goodCred voterSlot mark) = none := by
  rw [pv_good_cast_runs_write s voterSlot mark hgate]
  exact stateStepDev_caveat_violation_fails s voterSlot ballotActor ballotCell mark hvoted

/-! ## §8 — END-USER THEOREM 4: a committed cast-vote CONSERVES every asset.

A cast-vote is a single `SetField`, which has `ledgerDeltaAsset = 0` for EVERY asset — so its per-asset
turn delta is `0`, and `execFullForestG_conserves_per_asset` gives supply-preservation for free. The
credential/caveat gate is balance-orthogonal: passing the gate does not move money, and failing it
commits nothing — voting touches the tally, never balances. -/

/-- The per-asset turn delta of any cast-vote is `0` (a `SetField` is balance-neutral) — for EVERY asset
`b`. The conservation hypothesis, discharged once and reused. -/
theorem castNode_delta_zero (cred : Authorization Dg Pf) (voterSlot : FieldName) (mark : Int)
    (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG (castNode cred voterSlot mark)).map Prod.snd) b = 0 := by
  simp [castNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

/-- **`pv_cast_conserves` (END-USER THEOREM 4).** A COMMITTED cast-vote preserves EVERY asset's
total supply: `recTotalAsset s'.kernel b = recTotalAsset s.kernel b`, for every asset
`b`. The ballot write touches the tally/nullifier metadata, never balance — so a vote moves no money. A
one-liner off `execFullForestG_conserves_per_asset` with the `SetField`-is-balance-neutral hypothesis
discharged by `castNode_delta_zero`. -/
theorem pv_cast_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf)
    (voterSlot : FieldName) (mark : Int) (b : AssetId)
    (h : execFullForestG s (castNode cred voterSlot mark) = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  execFullForestG_conserves_per_asset s s' (castNode cred voterSlot mark) b h
    (castNode_delta_zero cred voterSlot mark b)

/-! ## §9 — NON-VACUITY: concrete ballot states with the real WriteOnce slot caveats + `#guard` witnesses.

`ballot0` is the ballot cell `0`, born with the two `WriteOnce` per-voter nullifier caveats, with voter A
having ALREADY VOTED (`null_A = 7`, a recorded nullifier) and voter B FRESH (`null_B = 0`, not yet voted).
Actor `0 == ballotCell`, so `stateAuthB` holds; the cell is Live (default lifecycle `0`); accounts `{0,1}`;
the revocation registry is empty. On `ballot0` we exhibit: (i) B's FIRST cast COMMITS; (ii) a forged
credential ⇒ `none`; (iii) a REVOKED voter ⇒ `none`; (iv) A's SECOND (different) cast ⇒ `none` (the
WriteOnce nullifier slot bites — no double-vote); (v) the committed cast CONSERVES both assets. -/

/-- A ballot-cell pre-state: cell `0` carries the two `WriteOnce` per-voter nullifier caveats; voter A has
ALREADY VOTED (`null_A = 7`, a recorded nullifier — re-cast must fail), voter B is FRESH (`null_B = 0`,
not yet voted — first cast must commit). -/
def ballot0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then
                  .record [("balance", .int 0), (voterNullA, .int 7), (voterNullB, .int 0)]
                else .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0
        slotCaveats := fun c => if c = 0 then ballotCaveats else [] }
    log := [] }

/-- The SAME ballot state but with voter A's credential nullifier (`42`) in the COMMITTED revocation
registry — A is REVOKED. Every cast presented with credential-nullifier `42` must now fail-closed. -/
def ballotRevoked : RecChainedState :=
  { ballot0 with kernel := { ballot0.kernel with revoked := [42] } }

/-- **`pv_ballot0_token_caveats_discharged` — the good token+chain caveat leg passes on `ballot0`. -/
theorem pv_ballot0_token_caveats_discharged :
    caveatsDischarged (mkAuthWithChain goodTokenCred pvGoodChain) ballot0 = true := by
  unfold caveatsDischarged mkAuthWithChain mkAuth chainGateG
  simp only [List.all_nil, Bool.true_and]
  decide

/-- **`pv_ballot0_token_gate_ok` — the good token+chain 4-leg gate passes on `ballot0`. -/
theorem pv_ballot0_token_gate_ok :
    gateOK (mkAuthWithChain goodTokenCred pvGoodChain) ballot0 = true := by
  unfold gateOK
  have hcred : credentialValidG (mkAuthWithChain goodTokenCred pvGoodChain) = true := by decide
  have hcap : capAuthorityG (mkAuthWithChain goodTokenCred pvGoodChain) = true := by
    exact unchecked_unconstrained_admits (Guard.all []) baseCapCtx (fun _ _ => by simp)
  have hrev : revocationGate (mkAuthWithChain goodTokenCred pvGoodChain) ballot0 = true := by
    simp only [revocationGate, mkAuthWithChain, mkAuth, ballot0]
    decide
  rw [hcred, hcap, pv_ballot0_token_caveats_discharged, hrev]
  decide

/-- **`pv_ballot0_token_write_commits` — voter B's fresh-slot write admits under `ballot0`. -/
theorem pv_ballot0_token_write_commits :
    (stateStepGuarded ballot0 voterNullB ballotActor ballotCell 9).isSome := by
  unfold stateStepGuarded ballot0 voterNullB ballotActor ballotCell ballotCaveats
  decide

/-- **`pv_token_good_commits` (concrete non-vacuity).** On `ballot0`, voter B's FIRST cast
with a genuine macaroon token + a verifying, admitting macaroon chain COMMITS over the fresh
`null_B` slot. -/
theorem pv_token_good_commits :
    (execFullForestG ballot0 (castNodeWithChain goodTokenCred pvGoodChain voterNullB 9)).isSome := by
  rw [pv_token_good_cast_runs_write ballot0 voterNullB 9 pv_ballot0_token_gate_ok]
  have hres : reservedField voterNullB = false := by simp [reservedField, voterNullB]
  simpa [stateStepDev, hres] using pv_ballot0_token_write_commits

-- The gate passes for the genuine credential on `ballot0` (credential ∧ revocation legs are the live legs):
#guard (gateOK (mkAuth goodCred []) ballot0)                       --  true  (genuine + not revoked)
#guard (gateOK (mkAuth forgedCred []) ballot0) == false            --  false (forged ⇒ fail-closed)
-- ...and the genuine credential carrying the revoked nullifier `42` fail-closes on `ballotRevoked`:
#guard (gateOK ({ mkAuth goodCred [] with credNul := 42 }) ballotRevoked) == false  --  false (revoked)
#guard (gateOK ({ mkAuth goodCred [] with credNul := 42 }) ballot0)                 --  true  (not yet revoked)

-- (i) voter B's FIRST cast over a FRESH nullifier slot COMMITS (WriteOnce permits the genesis write):
#guard ((execFullForestG ballot0 (castNode goodCred voterNullB 9)).isSome)  --  true (B voted!)
-- ...and the recorded nullifier slot reads back `9`:
#guard ((execFullForestG ballot0 (castNode goodCred voterNullB 9)).map
        (fun s => fieldOf voterNullB (s.kernel.cell 0))) == some 9  --  some 9

-- (ii) a FORGED credential ⇒ none (credential gate fail-closes), even on B's fresh slot:
#guard ((execFullForestG ballot0 (castNode forgedCred voterNullB 9)).isSome) == false  --  false

-- (iii) a REVOKED voter ⇒ none (revocation gate fail-closes), even with a genuine credential + fresh slot:
#guard ((execFullForestG ballotRevoked (castNodeNul goodCred 42 voterNullB 9)).isSome) == false  --  false

-- (iv) NO DOUBLE-VOTE: voter A re-casting a DIFFERENT mark over the recorded `null_A = 7` slot ⇒ none
--      (WriteOnce: old = 7 ≠ 0 and new = 13 ≠ 7 ⇒ caveatsAdmit = false — A already voted):
#guard (caveatsAdmit ballot0.kernel voterNullA ballotActor ballotCell 13) == false  --  false (already voted)
#guard ((execFullForestG ballot0 (castNode goodCred voterNullA 13)).isSome) == false  --  false (re-vote rejected)
-- ...re-writing the SAME recorded nullifier (7) is a WriteOnce no-op and is admitted (idempotent):
#guard (caveatsAdmit ballot0.kernel voterNullA ballotActor ballotCell 7)  --  true (idempotent no-op)

-- (v) CONSERVATION: a committed cast moves NO asset's supply (per-asset Δ = 0):
#guard ((execFullForestG ballot0 (castNode goodCred voterNullB 9)).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)  --  some (105, 7)

-- TOKEN + MACAROON-CHAIN arm witnesses (parallel to the signature arm above):
#guard (portalVerify goodTokenCred)                                              --  true  (genuine macaroon tag)
#guard (portalVerify forgedTokenCred) == false                                   --  false (forged tag)
#guard pvGoodChain.verify                                                        --  true  (good chain)
#guard pvForgedChain.verify == false                                             --  false (forged chain)
#guard pvCaveatViolationChain.verify                                           --  true  (verifies, but narrow)
#guard pvGoodChain.admits pvChainCtx pvNoDis                                     --  true  (150 ∈ [100,200])
#guard pvCaveatViolationChain.admits pvChainCtx pvNoDis == false                   --  false (150 ≰ 50)
#guard (verifiedChainGate pvGoodChain pvNoDis pvChainCtx)                        --  verified ∧ admits
#guard (verifiedChainGate pvCaveatViolationChain pvNoDis pvChainCtx) == false   --  false (caveat violation)
#guard (gateOK (mkAuthWithChain goodTokenCred pvGoodChain) ballot0)              --  true  (token+chain pass)
#guard (gateOK (mkAuthWithChain forgedTokenCred pvGoodChain) ballot0) == false    --  false (forged token)
#guard (gateOK (mkAuthWithChain goodTokenCred pvForgedChain) ballot0) == false    --  false (forged chain)
#guard (gateOK (mkAuthWithChain goodTokenCred pvCaveatViolationChain) ballot0) == false
  --  false (chain caveat violation: 150 ≰ 50)

-- voter B's FIRST cast via token+chain COMMITS:
#guard ((execFullForestG ballot0 (castNodeWithChain goodTokenCred pvGoodChain voterNullB 9)).isSome)
  --  true (B voted via macaroon!)
#guard ((execFullForestG ballot0 (castNodeWithChain goodTokenCred pvGoodChain voterNullB 9)).map
        (fun s => fieldOf voterNullB (s.kernel.cell 0))) == some 9  --  some 9
-- forged token / forged chain / caveat-violation chain ⇒ none:
#guard ((execFullForestG ballot0 (castNodeWithChain forgedTokenCred pvGoodChain voterNullB 9)).isSome) == false
#guard ((execFullForestG ballot0 (castNodeWithChain goodTokenCred pvForgedChain voterNullB 9)).isSome) == false
#guard ((execFullForestG ballot0
          (castNodeWithChain goodTokenCred pvCaveatViolationChain voterNullB 9)).isSome) == false

/-! ## §10 — Axiom-hygiene tripwires (the honesty pins). Every keystone depends ONLY on the three
standard kernel axioms `{propext, Classical.choice, Quot.sound}`. (The
portal soundness is a Prop carrier in `FullForestAuth`, never an axiom, so it does not appear.) -/

#assert_axioms execFullForestG_leaf
#assert_axioms execFullForestG_castNode
#assert_axioms execFullForestG_castNodeWithChain
#assert_axioms gateOK_forged_false
#assert_axioms gateOK_token_forged_false
#assert_axioms gateOK_chain_forged_false
#assert_axioms gateOK_chain_caveat_violation_false
#assert_axioms pv_forged_credential_rejected
#assert_axioms pv_token_forged_rejected
#assert_axioms pv_chain_forged_rejected
#assert_axioms pv_chain_caveat_violation_rejected
#assert_axioms pv_ballot0_token_caveats_discharged
#assert_axioms pv_ballot0_token_gate_ok
#assert_axioms pv_ballot0_token_write_commits
#assert_axioms pv_token_good_cast_runs_write
#assert_axioms pv_token_good_commits
#assert_axioms pv_revoked_voter_rejected
#assert_axioms pv_good_cast_runs_write
#assert_axioms pv_no_double_vote
#assert_axioms castNode_delta_zero
#assert_axioms pv_cast_conserves

end Dregg2.Apps.PrivacyVotingGated
