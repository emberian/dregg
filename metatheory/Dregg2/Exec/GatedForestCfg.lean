/-
# Dregg2.Exec.GatedForestCfg — first-class gated-forest carrier bundle.

Packages the `execFullForestG` carrier parameters as a `GatedForestCarriers` record, with
`starbridgeCarriers` the canonical production instance. Downstream modules `open StarbridgeGated`
instead of a pinned `Demo`/`Production` namespace.

**Production routing for `.coordinated` caveats:** intra-cell `execFullForestG` fail-closes
(see `FullForestAuth.GatedCaveat.holds`); the positive bilateral path is
`CoordinatedForestGLift.execCoordinatedForestG` over a `BilateralForestPairG` of two
`RecChainedState` snapshots (honest — no cross-cell reads on one cell).
-/
import Dregg2.Exec.FullForestAuth

namespace Dregg2.Exec

open FullForestAuth
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Authority
open Dregg2.Spec (Guard)
open Dregg2.Exec.AuthModes (AuthMode AuthContext unchecked_unconstrained_admits)
open Dregg2.Crypto.Reference
open Dregg2.Exec (ExecAuth confRights attenuate)

/-- **Carrier record** for the credential-gated call-forest executor. -/
structure GatedForestCarriers where
  digest : Type
  proof : Type
  request : Type
  stmt : Type
  wit : Type
  cellId : Type
  rights : Type
  ctx : Type
  gateway : Type
  bytes : Type
  tag : Type

/-! ## Starbridge — canonical production carriers + witness forests. -/

namespace StarbridgeGated

open Dregg2.Crypto.Reference

instance starbridgeVerifiable : Dregg2.Laws.Verifiable Nat Nat where
  Verify _ _ := true

def starbridgeCarriers : GatedForestCarriers where
  digest := Crypto.Reference.D
  proof := Crypto.Reference.P
  request := Bool
  stmt := Nat
  wit := Nat
  cellId := Label
  rights := ExecAuth
  ctx := Nat
  gateway := Unit
  bytes := Nat
  tag := Nat

abbrev Dg := Crypto.Reference.D
abbrev Pf := Crypto.Reference.P
abbrev Rq := Bool
abbrev St := Nat
abbrev Wt := Nat
abbrev Cx := Nat
abbrev Gw := Unit
abbrev Bt := Nat
abbrev Tg := Nat
/-- The production rights lattice (the REAL `Finset Auth ⊆` order — `granted ≤ held` is now
non-vacuous, unlike the previous `Unit` collapse). -/
abbrev Rt := ExecAuth
abbrev DNodeAuth := NodeAuth Dg Pf Rq St Wt Label Rt Cx Gw Bt Tg
abbrev DForest :=
  FullForestG (Digest := Dg) (Proof := Pf) (Request := Rq) (Stmt := St) (Wit := Wt)
    (CellId := Label) (Rights := Rt) (Ctx := Cx) (Gateway := Gw) (Bytes := Bt) (Tag := Tg)
abbrev DChild :=
  FullChildG (Digest := Dg) (Proof := Pf) (Request := Rq) (Stmt := St) (Wit := Wt)
    (CellId := Label) (Rights := Rt) (Ctx := Cx) (Gateway := Gw) (Bytes := Bt) (Tag := Tg)

/-- Fully-applied production forest step (`execFullForestG` at the starbridge carriers). -/
noncomputable def execForestG (s : RecChainedState) (f : DForest) : Option RecChainedState :=
  execFullForestG s f

def eraseForestG (f : DForest) : FullForestA :=
  eraseG f

theorem execForestG_erases (s s' : RecChainedState) (f : DForest)
    (h : execForestG s f = some s') :
    execFullForestA s (eraseForestG f) = some s' :=
  execFullForestG_erases s s' f h

/-- Childless gated forest = single gated node step. -/
theorem execFullForestG_leaf (s : RecChainedState) (na : DNodeAuth) (a : FullActionA) :
    execFullForestG s (⟨na, a, []⟩ : DForest) = execFullAGated s na a := by
  show (match execFullAGated s na a with
        | some s' => execFullChildrenG (targetOf a) s' ([] : List DChild)
        | none    => none) = execFullAGated s na a
  cases execFullAGated s na a <;> rfl

def baseCapCtx : AuthContext Rq St Wt Label Rt Cx Gw :=
  { req := true, customStmt := 0, wit := fun _ => 0
  , registry := fun _ => none, caveatCtx := 150, discharges := fun _ => false
  , graph := fun _ _ => False, consents := fun _ => True, facetOk := true, freshOk := true }

def mkAuth (cred : Authorization Dg Pf) (caveats : List GatedCaveat) : DNodeAuth :=
  { cred := cred, rev := Credential.noRevocations
  , capMode := .unchecked (Guard.all []), capCtx := baseCapCtx
  , caveats := caveats, chain := none, chainCtx := 150, chainDis := fun _ => false }

/-! ### A1 — the REAL-RIGHTS cap-authority leg (the WHAT, now load-bearing).

`mkAuth` pins `capMode := .unchecked (Guard.all [])`, which `authModeAdmits` admits for ALL inputs —
so the proved `granted ≤ held` attenuation theory was proved-but-never-exercised over the wire. Here
we route the delegation edge's `keep`/`parentCap` into a `.capTpDelivered` cap mode whose
`granted := keep.toFinset` and `held := confRights parentCap` over the REAL `ExecAuth = Finset Auth`
lattice. `authModeAdmits (.capTpDelivered ⟨_,_,held,granted⟩ _) = decide (granted.rights ≤ held.rights)
&& facetOk && freshOk`, so a delegation edge that AMPLIFIES (`keep ⊄ parentCap.rights`) makes the WHAT
leg FALSE ⇒ the gate fail-closes ⇒ whole-turn rollback. This makes the attenuation theory load-bearing
at the wire. -/

/-- The target label of a positional `Cap` (`null` targets the agent cell `0` by convention; only
the rights matter for the attenuation check). -/
def capTargetOf : Cap → Label
  | .null         => 0
  | .endpoint t _ => t
  | .node t       => t

/-- Build a `.capTpDelivered` cap mode that gates the delegated `keep` rights against the parent
cap's conferred rights over the real `ExecAuth` lattice. `held := confRights parentCap`,
`granted := keep.toFinset`; admits iff `keep.toFinset ≤ confRights parentCap` (the non-amplifying
discipline `is_attenuation(held, granted)`), with facet/freshness already `true` in `baseCapCtx`. -/
def capModeOfEdge (holder : Label) (keep : List Auth) (parentCap : Cap) :
    AuthMode Rq St Wt Label Rt Cx Gw :=
  .capTpDelivered
    { introducer := holder, recipient := holder
    , held := { target := capTargetOf parentCap, rights := confRights parentCap }
    , granted := { target := capTargetOf parentCap, rights := keep.toFinset } }
    True

/-- A node-auth whose WHAT leg gates on the delegation edge's real-rights attenuation. The WHO
(credential) and caveats are the same as `mkAuth`; only `capMode` is the load-bearing
`capModeOfEdge holder keep parentCap`. -/
def mkAuthCap (cred : Authorization Dg Pf) (caveats : List GatedCaveat)
    (holder : Label) (keep : List Auth) (parentCap : Cap) : DNodeAuth :=
  { cred := cred, rev := Credential.noRevocations
  , capMode := capModeOfEdge holder keep parentCap, capCtx := baseCapCtx
  , caveats := caveats, chain := none, chainCtx := 150, chainDis := fun _ => false }

def goodCred : Authorization Dg Pf := .signature 7 7
def forgedCred : Authorization Dg Pf := .signature 7 8

def trueCaveat : GatedCaveat :=
  { tier := .monotone, check := fun s => decide (0 ≤ s.kernel.bal 0 0) }

def falseCaveat : GatedCaveat :=
  { tier := .monotone, check := fun s => decide (10000 ≤ s.kernel.bal 0 0) }

def goodFullForestG : DForest :=
  ⟨ mkAuth goodCred [trueCaveat], .mintA 9 0 1 50
  , [ ({ holder := 0, keep := [Auth.read], parentCap := .endpoint 1 [Auth.read, Auth.write]
       , sub := ⟨ mkAuth goodCred [trueCaveat], .balanceA ⟨0, 0, 1, 30⟩ 0
                , [ ({ holder := 9, keep := [], parentCap := .endpoint 0 [Auth.read]
                     , sub := ⟨ mkAuth goodCred [trueCaveat], .burnA 9 0 1 50, [] ⟩ } : DChild) ] ⟩ } : DChild) ] ⟩

def forgedCredForestG : DForest :=
  ⟨ mkAuth forgedCred [trueCaveat], .mintA 9 0 1 50, [] ⟩

def falseCaveatForestG : DForest :=
  ⟨ mkAuth goodCred [falseCaveat], .mintA 9 0 1 50, [] ⟩

def launderFullForestG : DForest :=
  ⟨ mkAuth goodCred [trueCaveat], .mintA 9 0 1 50
  , [ ({ holder := 9, keep := [Auth.read], parentCap := .endpoint 0 [Auth.read, Auth.write]
       , sub := ⟨ mkAuth goodCred [trueCaveat], .burnA 9 0 0 50, [] ⟩ } : DChild) ] ⟩

/-- Gated forest erasing to the canonical `transferCF` (actor 0, cell 0→1, asset 0). -/
def transferForestG : DForest :=
  ⟨ mkAuth goodCred [trueCaveat], .balanceA ⟨0, 0, 1, 30⟩ 0, [] ⟩

/-- Single-node gated forest for production `◇` witnesses: one `emitEvent`, balance-neutral. -/
def logBumpForestG : DForest :=
  ⟨ mkAuth goodCred [trueCaveat], .emitEventA 0 0 0 0, [] ⟩

theorem transferForestG_turn_delta_zero (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG transferForestG).map Prod.snd) b = 0 := by
  simp only [turnLedgerDeltaAsset, lowerForestG, lowerChildrenG, transferForestG, ledgerDeltaAsset,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

theorem logBumpForestG_turn_delta_zero (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG logBumpForestG).map Prod.snd) b = 0 := by
  simp only [turnLedgerDeltaAsset, lowerForestG, lowerChildrenG, logBumpForestG, ledgerDeltaAsset,
    List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero]

/-- The log-bump forest shares the good-credential root auth with `goodFullForestG`. -/
theorem logBumpForestG_auth_eq : logBumpForestG.auth = goodFullForestG.auth := rfl

theorem logBumpForestG_credential_valid : credentialValidG logBumpForestG.auth = true := by
  unfold logBumpForestG credentialValidG mkAuth goodCred
  decide

theorem logBumpForestG_cap_authority : capAuthorityG logBumpForestG.auth = true := by
  unfold logBumpForestG capAuthorityG mkAuth
  exact unchecked_unconstrained_admits (Guard.all []) baseCapCtx (fun _ _ => by simp)

theorem logBumpForestG_caveats_fma0 : caveatsDischarged logBumpForestG.auth fma0 = true := by
  unfold logBumpForestG caveatsDischarged mkAuth trueCaveat baseCapCtx chainGateG fma0
  simp only [List.all_cons, List.all_nil, Bool.and_true, GatedCaveat.holds, decide_eq_true_eq]
  norm_num

theorem logBumpForestG_revocation_fma0 : revocationGate logBumpForestG.auth fma0 = true := by
  unfold logBumpForestG revocationGate mkAuth fma0
  simp

/-- Gate legs for the log-bump witness forest at `fma0`. -/
theorem logBumpForestG_gateOK : gateOK logBumpForestG.auth fma0 = true := by
  unfold gateOK
  simp only [Bool.and_eq_true, logBumpForestG_credential_valid, logBumpForestG_cap_authority,
             logBumpForestG_caveats_fma0, logBumpForestG_revocation_fma0]
  trivial

theorem transferForestG_auth_eq : transferForestG.auth = logBumpForestG.auth := rfl

theorem transferForestG_gateOK : gateOK transferForestG.auth fma0 = true := by
  rw [transferForestG_auth_eq]
  exact logBumpForestG_gateOK

theorem transferForestG_erase_eq :
    eraseForestG transferForestG = ⟨.balanceA ⟨0, 0, 1, 30⟩ 0, []⟩ := rfl

theorem transferForestG_kernel_commits :
    (execFullForestA fma0 (eraseForestG transferForestG)).isSome := by decide

theorem transferForestG_commits : (execFullForestG fma0 transferForestG).isSome := by
  rcases Option.isSome_iff_exists.mp transferForestG_kernel_commits with ⟨s', hs'⟩
  refine Option.isSome_iff_exists.mpr ⟨s', ?_⟩
  dsimp [execFullForestG, transferForestG, execFullChildrenG]
  have hga := (execFullAGated_some_iff fma0 s' (mkAuth goodCred [trueCaveat]) (.balanceA ⟨0, 0, 1, 30⟩ 0)).mpr
    ⟨transferForestG_gateOK, hs'⟩
  simpa [hga]

/-- **`gatedActionInvG_nonvacuous`** — the non-vacuity witness the `@[load_bearing]` linter requires
for `gatedActionInvG`: it is NEITHER everywhere-true NOR everywhere-false. It ACCEPTS the committed
gated transfer at the production carriers (`mkAuth goodCred [trueCaveat]` over `.balanceA ⟨0,0,1,30⟩ 0`
at `fma0` — credential-valid ∧ cap-authority ∧ caveats-discharged ∧ not-revoked ∧ the full per-asset
`fullActionInvA`, via `execFullAGated_attests`), and REFUTES the SAME node taken to its own pre-state (the
`fullActionInvA` conjunct's ObsAdvance demands `length < length`, impossible). A vacuous accept-all relation could not
carry the refuted half; a vacuous reject-all could not carry the accepted half. -/
theorem gatedActionInvG_nonvacuous :
    (∃ s', execFullAGated fma0 (mkAuth goodCred [trueCaveat]) (.balanceA ⟨0, 0, 1, 30⟩ 0) = some s'
       ∧ gatedActionInvG fma0 (mkAuth goodCred [trueCaveat]) (.balanceA ⟨0, 0, 1, 30⟩ 0) s')
    ∧ ¬ gatedActionInvG fma0 (mkAuth goodCred [trueCaveat]) (.balanceA ⟨0, 0, 1, 30⟩ 0) fma0 := by
  refine ⟨?_, ?_⟩
  · -- ACCEPTED: the gated transfer commits and attests all five conjuncts.
    obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp transferForestG_kernel_commits
    have hga : execFullAGated fma0 (mkAuth goodCred [trueCaveat]) (.balanceA ⟨0, 0, 1, 30⟩ 0) = some s' :=
      (execFullAGated_some_iff fma0 s' (mkAuth goodCred [trueCaveat]) (.balanceA ⟨0, 0, 1, 30⟩ 0)).mpr
        ⟨transferForestG_gateOK, hs'⟩
    exact ⟨s', hga, execFullAGated_attests fma0 s' (mkAuth goodCred [trueCaveat]) (.balanceA ⟨0, 0, 1, 30⟩ 0) hga⟩
  · -- REFUTED: the 5th conjunct `fullActionInvA … fma0` violates ObsAdvance (`length < length`).
    intro hinv
    unfold gatedActionInvG fullActionInvA at hinv
    exact Nat.lt_irrefl _ hinv.2.2.2.2.2.2.1

/-- The erased log-bump action commits at `fma0` (authority-free emit on a live cell). -/
theorem logBump_erase_commits : (execFullForestA fma0 (eraseG logBumpForestG)).isSome := by decide

/-- The production log-bump forest COMMITS at `fma0` (gate + credential + caveat all pass). -/
theorem logBumpForestG_commits : (execFullForestG fma0 logBumpForestG).isSome := by
  rcases Option.isSome_iff_exists.mp logBump_erase_commits with ⟨s', hs'⟩
  refine Option.isSome_iff_exists.mpr ⟨s', ?_⟩
  dsimp [execFullForestG, logBumpForestG, execFullChildrenG]
  have hga := (execFullAGated_some_iff fma0 s' (mkAuth goodCred [trueCaveat]) (.emitEventA 0 0 0 0)).mpr
    ⟨logBumpForestG_gateOK, hs'⟩
  simpa [hga]

/-- The committed post-state lands exactly one receipt. -/
theorem logBumpForestG_log_one {s' : RecChainedState}
    (h : execFullForestG fma0 logBumpForestG = some s') : s'.log.length = 1 := by
  have herase := execFullForestG_erases fma0 s' logBumpForestG h
  have hlen : (execFullForestA fma0 (eraseG logBumpForestG)).map (fun s => s.log.length) = some 1 := by
    decide
  rw [herase] at hlen
  simpa using hlen

#guard ((execFullForestG fma0 logBumpForestG).isSome)
#guard ((execFullForestG fma0 logBumpForestG).map (fun s => s.log.length) == some 1)

#guard ((execFullForestG fmaDeleg goodFullForestG).isSome)
#guard (turnLedgerDeltaAsset ((lowerForestG goodFullForestG).map Prod.snd) 0) == 0
#guard (turnLedgerDeltaAsset ((lowerForestG goodFullForestG).map Prod.snd) 1) == 0
#guard ((execFullForestG fmaDeleg goodFullForestG).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)
#guard ((execFullForestG fmaDeleg forgedCredForestG).isSome) == false
#guard (credentialValidG forgedCredForestG.auth) == false
#guard (credentialValidG goodFullForestG.auth)
#guard ((execFullForestG fmaDeleg falseCaveatForestG).isSome) == false
#guard (caveatsDischarged falseCaveatForestG.auth fmaDeleg) == false
#guard (caveatsDischarged goodFullForestG.auth fmaDeleg)
-- W1: the launder forest's delta family VANISHES (mint/burn are issuer-moves — there is no
-- disclosed non-conservation left to aggregate away), and the forest itself REJECTS: its child
-- `.burnA 9 0 0 50` is a self-burn of the issuer's own well (`cell = a = 0`), refused fail-closed.
#guard ((execFullForestG fmaDeleg launderFullForestG).isSome) == false
#guard (turnLedgerDeltaAsset ((lowerForestG launderFullForestG).map Prod.snd) 0) == 0
#guard (turnLedgerDeltaAsset ((lowerForestG launderFullForestG).map Prod.snd) 1) == 0
#guard ((execFullForestA fmaDeleg (eraseG goodFullForestG)).isSome)
#guard (((execFullForestG fmaDeleg goodFullForestG).map (fun s => s.log.length)
        == (execFullForestA fmaDeleg (eraseG goodFullForestG)).map (fun s => s.log.length)))
#guard ((execFullForestG fmaDeleg goodFullForestG).map
        (fun s' => decide (fmaDeleg.log.length < s'.log.length)) == some true)

/-! ### R2 — the STAGED gated HEAP WRITE at the production carriers (non-vacuity).

`execHeapWriteG` (the gated `write`-verb heap instance the rotation's `FullActionA` arm will route
to) exercised at the SAME starbridge carriers / credential / caveat the forest witnesses use:
a credentialed, kernel-authorized heap write COMMITS (and reads back, balance-neutrally, off the
SPLICED `RecordKernelState.heaps`); a forged credential, an unauthorized actor, and a violated
heap atom each REFUSE (fail-closed at their respective gate legs). -/

section HeapWriteWitness
open Dregg2.Substrate.Heap (refSponge)

-- The full gate stack passes ⇒ the heap write COMMITS:
#guard ((execHeapWriteG refSponge fma0 (mkAuth goodCred [trueCaveat]) [] 0 0 1 2 42).isSome)
-- ...the written (coll 1, key 2) reads back 42 off the SPLICED kernel field:
#guard ((execHeapWriteG refSponge fma0 (mkAuth goodCred [trueCaveat]) [] 0 0 1 2 42).map
        (fun s => Dregg2.Substrate.Heap.hget refSponge (s.kernel.heaps 0) 1 2))
       == some (some 42)
-- ...balance-neutral through the gate (both real assets unmoved):
#guard ((execHeapWriteG refSponge fma0 (mkAuth goodCred [trueCaveat]) [] 0 0 1 2 42).map
        (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 1))) == some (105, 7)
-- A FORGED credential refuses (the WHO leg, in front of a perfectly valid heap write):
#guard ((execHeapWriteG refSponge fma0 (mkAuth forgedCred [trueCaveat]) [] 0 0 1 2 42).isSome)
       == false
-- An UNAUTHORIZED actor (5 holds no cap, not self) refuses (the kernel authority gate UNDER the
-- credential gate — defense in depth):
#guard ((execHeapWriteG refSponge fma0 (mkAuth goodCred [trueCaveat]) [] 5 0 1 2 42).isSome)
       == false
-- A VIOLATED heap atom refuses (the guard-algebra teeth survive the gate):
#guard ((execHeapWriteG refSponge fma0 (mkAuth goodCred [trueCaveat])
          [.heapContains 1 2] 0 0 1 2 42).isSome) == false

end HeapWriteWitness

/-! ### A1 — the WHAT leg (`capAuthorityG`) now has REAL TEETH at the wire.

The two forests below share EVERYTHING — the same genuine credential, the same caveat, the same
`emitEvent` action — differing ONLY in the delegated edge's `keep`/`parentCap`. The non-amplifying
one (`keep = [read]` against a parent cap `.endpoint 0 [read,write]`) COMMITS; the amplifying one
(`keep = [read,write]` against a parent cap `.endpoint 0 [read]`) is REJECTED by `capAuthorityG`
(`granted ⊄ held` over `ExecAuth`) ⇒ the whole forest rolls back. The previous `.unchecked` cap mode
admitted BOTH. This is the same-wire contrast proving the proved `granted ≤ held` attenuation is now
load-bearing — not admit-by-construction. -/

/-- A non-amplifying delegated node: `keep = [read]` ⊆ parent rights `[read, write]`. Its WHAT leg
ADMITS (`[read].toFinset ≤ {read, write}`). Balance-neutral `emitEvent`. -/
def capOkForestG : DForest :=
  ⟨ mkAuthCap goodCred [trueCaveat] 0 [Auth.read] (.endpoint 0 [Auth.read, Auth.write])
  , .emitEventA 0 0 0 0, [] ⟩

/-- An AMPLIFYING delegated node: `keep = [read, write]` ⊄ parent rights `[read]`. Its WHAT leg
REJECTS (`{read, write} ⊄ {read}`). The ONLY difference from `capOkForestG` is the cap data. -/
def capAmplifyForestG : DForest :=
  ⟨ mkAuthCap goodCred [trueCaveat] 0 [Auth.read, Auth.write] (.endpoint 0 [Auth.read])
  , .emitEventA 0 0 0 0, [] ⟩

-- The WHAT leg ADMITS the non-amplifying edge but REJECTS the amplifying one:
#guard (capAuthorityG capOkForestG.auth)                  --  true  (keep ⊆ parent)
#guard (capAuthorityG capAmplifyForestG.auth) == false    --  false (keep ⊄ parent: AMPLIFY)
-- ...and the gate (hence the whole forest) follows the WHAT leg — the amplifying turn ROLLS BACK:
#guard ((execFullForestG fma0 capOkForestG).isSome)               --  true  (commits)
#guard ((execFullForestG fma0 capAmplifyForestG).isSome) == false --  false (gate rejects ⇒ rollback)
-- The two differ ONLY in cap data (same credential ⇒ same WHO leg passes for both):
#guard (credentialValidG capOkForestG.auth)
#guard (credentialValidG capAmplifyForestG.auth)
-- An EXACT-rights (equal, not strict subset) edge also admits (reflexivity of attenuation):
#guard (capAuthorityG (mkAuthCap goodCred [trueCaveat] 0 [Auth.read, Auth.write]
          (.endpoint 0 [Auth.read, Auth.write])))  --  true

theorem capOkForestG_what_admits : capAuthorityG capOkForestG.auth = true := by
  show capAuthorityG (mkAuthCap goodCred [trueCaveat] 0 [Auth.read]
        (.endpoint 0 [Auth.read, Auth.write])) = true
  unfold capAuthorityG mkAuthCap capModeOfEdge baseCapCtx confRights capTargetOf
  simp only [AuthModes.authModeAdmits]
  decide

theorem capAmplifyForestG_what_rejects : capAuthorityG capAmplifyForestG.auth = false := by
  show capAuthorityG (mkAuthCap goodCred [trueCaveat] 0 [Auth.read, Auth.write]
        (.endpoint 0 [Auth.read])) = false
  unfold capAuthorityG mkAuthCap capModeOfEdge baseCapCtx confRights capTargetOf
  simp only [AuthModes.authModeAdmits]
  decide

/-- The amplifying forest is REJECTED by the full gate (the WHAT leg fail-closes the conjunction). -/
theorem capAmplifyForestG_gate_rejects : gateOK capAmplifyForestG.auth fma0 = false := by
  unfold gateOK
  rw [capAmplifyForestG_what_rejects]
  simp

/-- Hence the amplifying forest does NOT commit (`execFullForestG = none`). -/
theorem capAmplifyForestG_rolls_back : execFullForestG fma0 capAmplifyForestG = none := by
  show execFullForestG fma0
    (⟨capAmplifyForestG.auth, .emitEventA 0 0 0 0, []⟩ : DForest) = none
  simp only [execFullForestG_leaf, execFullAGated, capAmplifyForestG_gate_rejects,
    Bool.false_eq_true, ite_false]

#assert_axioms capAmplifyForestG_what_rejects
#assert_axioms capOkForestG_what_admits
#assert_axioms capAmplifyForestG_gate_rejects
#assert_axioms capAmplifyForestG_rolls_back

/-! ### A2 — the AGENT-FACING `Authorization::Token` path (the biscuit credential the Rust
SubAgent / node-MCP surface constructs), now gating the EXECUTOR on the SAME live `execFullForestG`
path — both the WHO (biscuit signature) and the WHAT (the token's attenuation caveats) leg.

The Rust `sdk::SubAgent::execute` / `node::mcp::dispatch_tool` surfaces mint a public-key biscuit
and present it as `Authorization::Token`; the EXECUTOR (`verify_token_for_scope` /
`verify_token_authorization`), not an out-of-band `cap.verify()`, admits or rejects the turn. This
section is the Lean mirror: the gated forest's ROOT credential is the `Authorization.token` arm AND
its cap-authority leg is the REAL `AuthMode.token` (the windowed biscuit's attenuation caveats), NOT
the `.unchecked` admit-by-construction `mkAuth` pins. So the token gates the executor admission on
BOTH legs, witnessed non-vacuously each direction:

  * a VALID, in-scope token (genuine biscuit signature ∧ caveat context inside the granted window)
    is ADMITTED → the forest COMMITS;
  * a FORGED-signature token (the biscuit signature does not verify) is REJECTED by the WHO leg
    (`credentialValidG = false`) → `none`, whole-forest rollback;
  * an OVER-ATTENUATED token (the credential is presented in a context OUTSIDE its granted window —
    the biscuit's own attenuation caveats narrow it out) is REJECTED by the WHAT leg
    (`capAuthorityG = false`) → `none`, whole-forest rollback.

The two negatives are ORTHOGONAL (different gate legs), so neither is laundered by the other. This is
the executable face of "the token gates the executor, not the narration." -/

open Dregg2.Authority (Caveat Token TokenKind)

/-- The agent-facing biscuit credential's WHO arm: an `Authorization.token` whose biscuit signature
verifies under the reference kernel (`sig` echoes the issuer `key`). The Rust SubAgent presents the
encoded `eb2_…` biscuit; here the portal arm is `CryptoKernel.verify key sig` (`Crypto.Reference`:
`decide (key = sig)`), so a genuine credential's signature equals its issuer key. -/
def goodTokenCred : Authorization Dg Pf := .token 11 11

/-- A FORGED biscuit credential: the signature (`12`) does NOT verify against the issuer key (`11`).
The §8 portal WHO leg (`credentialValidG`) fail-closes — exactly the executor's `TokenAuthInvalid`. -/
def forgedTokenCred : Authorization Dg Pf := .token 11 12

/-- The windowed biscuit the agent carries: a root biscuit attenuated to the height window
`[100, 200]` — the Lean mirror of the SubAgent's biscuit scoped (via its Datalog/caveats) to exactly
the verbs/window the worker may invoke. Its `admits` is the meet of both caveats over the context's
`caveatCtx` (height). The starbridge `baseCapCtx.caveatCtx = 150` is INSIDE the window. -/
def agentToken : Token Cx Gw :=
  { kind := .biscuit
  , caveats := [ .opaque (fun h => decide (100 ≤ h)), .opaque (fun h => decide (h ≤ 200)) ] }

/-- The cap-context whose `caveatCtx` (height `150`) lands INSIDE the token's `[100,200]` window —
the in-scope presentation. (Everything else mirrors `baseCapCtx`.) -/
def tokenCtxInWindow : AuthContext Rq St Wt Label Rt Cx Gw := baseCapCtx

/-- The cap-context whose `caveatCtx` (height `50`) lands OUTSIDE the token's `[100,200]` window —
the over-attenuated presentation (the biscuit's own caveat narrows it out). -/
def tokenCtxOutOfWindow : AuthContext Rq St Wt Label Rt Cx Gw := { baseCapCtx with caveatCtx := 50 }

/-- **`mkAuthToken`** — a node-auth on the AGENT-FACING Token path: the WHO leg is the
`Authorization.token` biscuit credential (portal), and the WHAT leg is the REAL `AuthMode.token`
windowed biscuit (`agentToken`) — NOT the `.unchecked (Guard.all [])` that `mkAuth` pins. So the
token's attenuation actually gates the executor admission. The cap-CONTEXT is supplied (in/out of
window) so the same credential admits in-scope and rejects over-attenuated. -/
def mkAuthToken (cred : Authorization Dg Pf) (ctx : AuthContext Rq St Wt Label Rt Cx Gw)
    (caveats : List GatedCaveat) : DNodeAuth :=
  { cred := cred, rev := Credential.noRevocations
  , capMode := .token agentToken, capCtx := ctx
  , caveats := caveats, chain := none, chainCtx := 150, chainDis := fun _ => false }

/-- A VALID agent-token forest: genuine biscuit credential, in-window cap context. Balance-neutral
`emitEvent`, so the only gate that matters is the credential+attenuation. ADMITS. -/
def tokenOkForestG : DForest :=
  ⟨ mkAuthToken goodTokenCred tokenCtxInWindow [trueCaveat], .emitEventA 0 0 0 0, [] ⟩

/-- A FORGED-signature agent-token forest: same in-window context, but the biscuit signature does not
verify. REJECTED by the WHO leg. -/
def tokenForgedForestG : DForest :=
  ⟨ mkAuthToken forgedTokenCred tokenCtxInWindow [trueCaveat], .emitEventA 0 0 0 0, [] ⟩

/-- An OVER-ATTENUATED agent-token forest: genuine biscuit credential, but presented in a context
OUTSIDE the token's `[100,200]` window — the biscuit's own attenuation caveat narrows it out.
REJECTED by the WHAT leg (`capAuthorityG`). -/
def tokenOverAttenForestG : DForest :=
  ⟨ mkAuthToken goodTokenCred tokenCtxOutOfWindow [trueCaveat], .emitEventA 0 0 0 0, [] ⟩

/-- **WHO leg — the genuine biscuit credential VERIFIES.** The `Authorization.token` arm
routes through the §8 portal (`CryptoKernel.verify 11 11` = `decide (11 = 11)` = `true`). -/
theorem tokenOkForestG_credential_valid : credentialValidG tokenOkForestG.auth = true := by
  unfold tokenOkForestG mkAuthToken credentialValidG goodTokenCred
  decide

/-- **WHO leg — the FORGED biscuit credential FAILS (the teeth).** The portal's
`CryptoKernel.verify 11 12` = `decide (11 = 12)` = `false`: a forged biscuit signature fail-closes
exactly as the executor's `TokenAuthInvalid`. NON-VACUOUS against the positive above. -/
theorem tokenForgedForestG_credential_invalid : credentialValidG tokenForgedForestG.auth = false := by
  unfold tokenForgedForestG mkAuthToken credentialValidG forgedTokenCred
  decide

/-- **WHAT leg — the in-window token's attenuation ADMITS.** `AuthMode.token agentToken`
admits iff ALL the biscuit's caveats discharge on `caveatCtx = 150`: `100 ≤ 150 ∧ 150 ≤ 200`. This is
the token's OWN attenuation, gating the executor — not `.unchecked`. -/
theorem tokenOkForestG_what_admits : capAuthorityG tokenOkForestG.auth = true := by
  unfold tokenOkForestG mkAuthToken capAuthorityG agentToken tokenCtxInWindow baseCapCtx
  simp only [AuthModes.authModeAdmits, Dregg2.Authority.Token.admits, Dregg2.Authority.Caveat.ok,
    List.all_cons, List.all_nil]
  decide

/-- **WHAT leg — the OVER-ATTENUATED token's attenuation REJECTS (the teeth).** Presented at
`caveatCtx = 50`, the biscuit's `100 ≤ h` caveat is FALSE, so `agentToken.admits = false` ⇒
`capAuthorityG = false`. The credential's OWN attenuation narrows it out of scope — the executor
rejects, not an out-of-band check. NON-VACUOUS against the in-window admit. -/
theorem tokenOverAttenForestG_what_rejects : capAuthorityG tokenOverAttenForestG.auth = false := by
  unfold tokenOverAttenForestG mkAuthToken capAuthorityG agentToken tokenCtxOutOfWindow baseCapCtx
  simp only [AuthModes.authModeAdmits, Dregg2.Authority.Token.admits, Dregg2.Authority.Caveat.ok,
    List.all_cons, List.all_nil]
  decide

/-- The valid agent-token forest's caveat leg discharges at `fma0` (`trueCaveat`). -/
theorem tokenOkForestG_caveats_fma0 : caveatsDischarged tokenOkForestG.auth fma0 = true := by
  unfold tokenOkForestG mkAuthToken caveatsDischarged trueCaveat chainGateG fma0
  simp only [List.all_cons, List.all_nil, Bool.and_true, GatedCaveat.holds, decide_eq_true_eq]
  norm_num

/-- The valid agent-token forest is not revoked at `fma0`. -/
theorem tokenOkForestG_revocation_fma0 : revocationGate tokenOkForestG.auth fma0 = true := by
  unfold tokenOkForestG mkAuthToken revocationGate fma0
  simp

/-- **`tokenOkForestG_gateOK` — the VALID agent token is ADMITTED by the full 4-leg gate.**
WHO (biscuit verifies) ∧ WHAT (in-window attenuation admits) ∧ caveats ∧ not-revoked. The agent-facing
`Authorization::Token` gates the executor admission positively on the live path. -/
theorem tokenOkForestG_gateOK : gateOK tokenOkForestG.auth fma0 = true := by
  unfold gateOK
  simp only [Bool.and_eq_true, tokenOkForestG_credential_valid, tokenOkForestG_what_admits,
             tokenOkForestG_caveats_fma0, tokenOkForestG_revocation_fma0]
  trivial

/-- **`tokenForgedForestG_gate_rejects` — the FORGED token is REJECTED by the gate.** The WHO
leg fail-closes the conjunction. -/
theorem tokenForgedForestG_gate_rejects : gateOK tokenForgedForestG.auth fma0 = false := by
  unfold gateOK
  rw [tokenForgedForestG_credential_invalid]
  simp

/-- **`tokenOverAttenForestG_gate_rejects` — the OVER-ATTENUATED token is REJECTED by the gate
.** The WHAT leg (the token's own attenuation) fail-closes the conjunction — orthogonal to the
forged case (the credential VERIFIES here; it is the attenuation that narrows it out). -/
theorem tokenOverAttenForestG_gate_rejects : gateOK tokenOverAttenForestG.auth fma0 = false := by
  unfold gateOK
  rw [tokenOverAttenForestG_what_rejects]
  simp [tokenOverAttenForestG_credential_valid_aux]
where
  /-- The over-attenuated forest's credential is the SAME genuine biscuit — it VERIFIES; only the
  attenuation rejects. (Used to show the rejection is the WHAT leg, not the WHO leg.) -/
  tokenOverAttenForestG_credential_valid_aux :
      credentialValidG tokenOverAttenForestG.auth = true := by
    unfold tokenOverAttenForestG mkAuthToken credentialValidG goodTokenCred
    decide

/-- **`tokenOkForestG_commits` — the VALID agent token COMMITS on the live `execFullForestG` path
.** Not just `gateOK`: the whole gated forest runs and produces a post-state. This is the
end-to-end positive: an agent presenting a genuine, in-scope `Authorization::Token` has its turn
admitted by the verified executor. -/
theorem tokenOkForestG_commits : (execFullForestG fma0 tokenOkForestG).isSome := by
  have herase : (execFullForestA fma0 (eraseG tokenOkForestG)).isSome := by decide
  rcases Option.isSome_iff_exists.mp herase with ⟨s', hs'⟩
  refine Option.isSome_iff_exists.mpr ⟨s', ?_⟩
  dsimp [execFullForestG, tokenOkForestG, execFullChildrenG]
  have hga := (execFullAGated_some_iff fma0 s' (mkAuthToken goodTokenCred tokenCtxInWindow [trueCaveat])
    (.emitEventA 0 0 0 0)).mpr ⟨tokenOkForestG_gateOK, hs'⟩
  simpa [hga]

/-- **`tokenForgedForestG_rolls_back` — the FORGED agent token does NOT commit.** The gate
rejects ⇒ `execFullForestG = none` ⇒ whole-forest rollback. -/
theorem tokenForgedForestG_rolls_back : execFullForestG fma0 tokenForgedForestG = none := by
  have hgate : gateOK tokenForgedForestG.auth fma0 = false := tokenForgedForestG_gate_rejects
  unfold tokenForgedForestG at hgate ⊢
  show (match execFullAGated fma0 (mkAuthToken forgedTokenCred tokenCtxInWindow [trueCaveat])
            (.emitEventA 0 0 0 0) with
        | some s' => execFullChildrenG (targetOf (.emitEventA 0 0 0 0)) s' ([] : List DChild)
        | none    => none) = none
  rw [execFullAGated]
  simp only [hgate]
  rfl

/-- **`tokenOverAttenForestG_rolls_back` — the OVER-ATTENUATED agent token does NOT commit.**
The token's own attenuation narrows it out of scope ⇒ `execFullForestG = none` ⇒ rollback. The
credential verified; the EXECUTOR ADMISSION still rejects on the attenuation. -/
theorem tokenOverAttenForestG_rolls_back : execFullForestG fma0 tokenOverAttenForestG = none := by
  have hgate : gateOK tokenOverAttenForestG.auth fma0 = false := tokenOverAttenForestG_gate_rejects
  unfold tokenOverAttenForestG at hgate ⊢
  show (match execFullAGated fma0 (mkAuthToken goodTokenCred tokenCtxOutOfWindow [trueCaveat])
            (.emitEventA 0 0 0 0) with
        | some s' => execFullChildrenG (targetOf (.emitEventA 0 0 0 0)) s' ([] : List DChild)
        | none    => none) = none
  rw [execFullAGated]
  simp only [hgate]
  rfl

-- The agent-facing `Authorization::Token` gates the EXECUTOR on the live path, both legs, both ways:
#guard (credentialValidG tokenOkForestG.auth)                       --  true  (genuine biscuit verifies)
#guard (credentialValidG tokenForgedForestG.auth) == false          --  false (forged signature)
#guard (capAuthorityG tokenOkForestG.auth)                          --  true  (in-window attenuation)
#guard (capAuthorityG tokenOverAttenForestG.auth) == false          --  false (over-attenuated)
#guard ((execFullForestG fma0 tokenOkForestG).isSome)               --  true  (VALID token ⇒ COMMITS)
#guard ((execFullForestG fma0 tokenForgedForestG).isSome) == false  --  false (forged ⇒ rollback)
#guard ((execFullForestG fma0 tokenOverAttenForestG).isSome) == false --  false (over-attenuated ⇒ rollback)

#assert_axioms tokenOkForestG_credential_valid
#assert_axioms tokenForgedForestG_credential_invalid
#assert_axioms tokenOkForestG_what_admits
#assert_axioms tokenOverAttenForestG_what_rejects
#assert_axioms tokenOkForestG_gateOK
#assert_axioms tokenForgedForestG_gate_rejects
#assert_axioms tokenOverAttenForestG_gate_rejects
#assert_axioms tokenOkForestG_commits
#assert_axioms tokenForgedForestG_rolls_back
#assert_axioms tokenOverAttenForestG_rolls_back

/-! ### A3 — the TIER-3 COORDINATED caveat, WELDED into the production gate (executed end-to-end).

`GatedCaveat.holds` on `.coordinated` was a dead fail-closed branch (`FullForestAuth.lean`): a
cross-cell read could never discharge on a single-cell node, so a tier-3 caveat HARD-REJECTED on the
production `caveatsDischarged`/`gateOK`/`execFullForestG` path — the positive coordinated discharge
lived only in the parallel `execCoordinatedForestG` executor. The `cross` field welds the proved
atomic-snapshot equalizer (`CoordinatedCaveat.dischargeCoordinated` / `CrossCaveat.jointApplyCaveated`)
INLINE: on a single machine the companion cell lives in the SAME `RecChainedState`, so the cross-cell
condition is read on the SAME snapshot `s` the node commits against (`gateOK na s` reads exactly the
`s` `execFullA` runs on — `gatedNode_check_eq_use` — so time-of-check = time-of-use, no TOCTOU). The
two forests below share EVERYTHING (same genuine credential, same balance-neutral `emitEvent`, same
companion cell `1`) and differ ONLY in the cross-cell THRESHOLD:

  * the SATISFIED covenant (companion cell `1` holds ≥ `5` of asset `0`, and at `fma0` it holds
    exactly `5`) ⇒ the coordinated caveat DISCHARGES ⇒ `caveatsDischarged = true` ⇒ the gate ADMITS ⇒
    the forest COMMITS;
  * the VIOLATED covenant (companion cell `1` would need ≥ `10`, but holds only `5`) ⇒ the coordinated
    caveat FAILS ⇒ `caveatsDischarged = false` ⇒ the gate REJECTS ⇒ `execFullForestG = none`, rollback.

So the tier-3 cross-cell caveat is EXECUTED end-to-end on the SAME live entry as tier-1/tier-2.
Non-vacuous each direction (witnessed true AND false). -/

/-- A SATISFIED tier-3 coordinated caveat: the cross-cell condition reads the COMPANION cell `1` out of
the same atomic snapshot and gates on it (`companion holds ≥ 5 of asset 0`). At `fma0` cell `1` holds
exactly `5`, so the welded equalizer DISCHARGES. -/
def coordCaveatSat : GatedCaveat :=
  { tier := .coordinated, check := fun _ => false
  , cross := some (fun s => decide (5 ≤ s.kernel.bal 1 0)) }

/-- A VIOLATED tier-3 coordinated caveat: same companion-cell read, but the threshold (`≥ 10`) is NOT
met (cell `1` holds only `5`). The welded equalizer FAIL-CLOSES — the cross-cell covenant
gates. -/
def coordCaveatViolated : GatedCaveat :=
  { tier := .coordinated, check := fun _ => false
  , cross := some (fun s => decide (10 ≤ s.kernel.bal 1 0)) }

/-- A coordinated caveat with NO companion view (`cross = none`) — the dregg1 posture: a cross-cell
read cannot be faked, so it fail-closes. -/
def coordCaveatNoView : GatedCaveat :=
  { tier := .coordinated, check := fun _ => true }

/-- The SATISFIED-coordinated forest: genuine credential, balance-neutral emit, tier-3 caveat whose
cross-cell condition HOLDS at `fma0`. ADMITS. -/
def coordOkForestG : DForest :=
  ⟨ mkAuth goodCred [coordCaveatSat], .emitEventA 0 0 0 0, [] ⟩

/-- The VIOLATED-coordinated forest: identical except the tier-3 caveat's cross-cell condition FAILS at
`fma0`. REJECTED by the caveat leg. -/
def coordViolatedForestG : DForest :=
  ⟨ mkAuth goodCred [coordCaveatViolated], .emitEventA 0 0 0 0, [] ⟩

/-- **`coordCaveatSat_holds` — the welded equalizer DISCHARGES.** The tier-3 caveat's
cross-cell condition (companion cell `1` ≥ 5 of asset 0) holds on the `fma0` snapshot. This is the
positive coordinated discharge routed through `GatedCaveat.holds`'s `.coordinated`/`cross` arm — the
atomic-snapshot read, not a dead `false` branch. -/
theorem coordCaveatSat_holds : coordCaveatSat.holds fma0 = true := by
  unfold coordCaveatSat GatedCaveat.holds fma0
  decide

/-- **`coordCaveatViolated_fails` — the welded equalizer FAIL-CLOSES on a violated covenant (PROVED,
the teeth).** The cross-cell threshold (≥ 10) is not met at `fma0` (cell 1 holds 5), so the coordinated
caveat is rejected — the cross-cell read gates, non-vacuously against the satisfied case. -/
theorem coordCaveatViolated_fails : coordCaveatViolated.holds fma0 = false := by
  unfold coordCaveatViolated GatedCaveat.holds fma0
  decide

/-- **`coordCaveatNoView_fails` — no companion view ⇒ fail-closed (the dregg1 posture).** A
`.coordinated` caveat with `cross = none` cannot discharge on a single node — exactly the old behavior,
recovered as the `none` case. -/
theorem coordCaveatNoView_fails : coordCaveatNoView.holds fma0 = false := by
  unfold coordCaveatNoView GatedCaveat.holds
  rfl

/-- The satisfied-coordinated forest's caveat leg DISCHARGES at `fma0` (the welded tier-3 equalizer). -/
theorem coordOkForestG_caveats_fma0 : caveatsDischarged coordOkForestG.auth fma0 = true := by
  unfold coordOkForestG mkAuth caveatsDischarged chainGateG
  simp only [List.all_cons, List.all_nil, Bool.and_true, coordCaveatSat_holds]

/-- The satisfied-coordinated forest passes the full 4-leg gate at `fma0`. -/
theorem coordOkForestG_gateOK : gateOK coordOkForestG.auth fma0 = true := by
  have hcred : credentialValidG coordOkForestG.auth = true := by
    unfold coordOkForestG mkAuth credentialValidG goodCred; decide
  have hcap : capAuthorityG coordOkForestG.auth = true := by
    unfold coordOkForestG mkAuth capAuthorityG
    exact unchecked_unconstrained_admits (Guard.all []) baseCapCtx (fun _ _ => by simp)
  have hrev : revocationGate coordOkForestG.auth fma0 = true := by
    unfold coordOkForestG mkAuth revocationGate fma0; simp
  unfold gateOK
  simp only [Bool.and_eq_true, hcred, hcap, coordOkForestG_caveats_fma0, hrev]
  trivial

/-- **`coordOkForestG_commits` — the SATISFIED tier-3 coordinated caveat COMMITS end-to-end on the live
`execFullForestG` path.** The whole gated forest runs and produces a post-state — the cross-
cell coordinated condition is DISCHARGED inline by the welded equalizer, on the SAME production entry
as tier-1/tier-2. This is the end-to-end positive the task demands: a tier-3 cross-cell caveat whose
condition holds is admitted, not hard-rejected. -/
theorem coordOkForestG_commits : (execFullForestG fma0 coordOkForestG).isSome := by
  have herase : (execFullForestA fma0 (eraseG coordOkForestG)).isSome := by decide
  rcases Option.isSome_iff_exists.mp herase with ⟨s', hs'⟩
  refine Option.isSome_iff_exists.mpr ⟨s', ?_⟩
  dsimp [execFullForestG, coordOkForestG, execFullChildrenG]
  have hga := (execFullAGated_some_iff fma0 s' (mkAuth goodCred [coordCaveatSat])
    (.emitEventA 0 0 0 0)).mpr ⟨coordOkForestG_gateOK, hs'⟩
  simpa [hga]

/-- The violated-coordinated forest's caveat leg FAIL-CLOSES at `fma0`. -/
theorem coordViolatedForestG_caveats_fma0 : caveatsDischarged coordViolatedForestG.auth fma0 = false := by
  unfold coordViolatedForestG mkAuth caveatsDischarged chainGateG
  simp only [List.all_cons, List.all_nil, Bool.and_true, coordCaveatViolated_fails]

/-- The violated-coordinated forest is REJECTED by the full gate (the caveat leg fail-closes). -/
theorem coordViolatedForestG_gate_rejects : gateOK coordViolatedForestG.auth fma0 = false := by
  unfold gateOK
  rw [coordViolatedForestG_caveats_fma0]
  simp

/-- **`coordViolatedForestG_rolls_back` — the VIOLATED tier-3 coordinated caveat does NOT commit
(the teeth).** The cross-cell covenant fails ⇒ `execFullForestG = none` ⇒ whole-forest
rollback. The cross-cell read gates the EXECUTOR ADMISSION, non-vacuously against
`coordOkForestG_commits`. -/
theorem coordViolatedForestG_rolls_back : execFullForestG fma0 coordViolatedForestG = none := by
  have hgate : gateOK coordViolatedForestG.auth fma0 = false := coordViolatedForestG_gate_rejects
  unfold coordViolatedForestG at hgate ⊢
  show (match execFullAGated fma0 (mkAuth goodCred [coordCaveatViolated]) (.emitEventA 0 0 0 0) with
        | some s' => execFullChildrenG (targetOf (.emitEventA 0 0 0 0)) s' ([] : List DChild)
        | none    => none) = none
  rw [execFullAGated]
  simp only [hgate]
  rfl

-- The tier-3 coordinated caveat is EXECUTED end-to-end on the live gate, both ways:
#guard (coordCaveatSat.holds fma0)                              --  true  (companion cell discharges)
#guard (coordCaveatViolated.holds fma0) == false               --  false (cross-cell covenant violated)
#guard (coordCaveatNoView.holds fma0) == false                 --  false (no companion view ⇒ fail-closed)
#guard (caveatsDischarged coordOkForestG.auth fma0)            --  true  (welded equalizer discharges)
#guard (caveatsDischarged coordViolatedForestG.auth fma0) == false  --  false
#guard ((execFullForestG fma0 coordOkForestG).isSome)               --  true  (tier-3 COMMITS)
#guard ((execFullForestG fma0 coordViolatedForestG).isSome) == false --  false (tier-3 violated ⇒ rollback)

#assert_axioms coordCaveatSat_holds
#assert_axioms coordCaveatViolated_fails
#assert_axioms coordCaveatNoView_fails
#assert_axioms coordOkForestG_caveats_fma0
#assert_axioms coordOkForestG_gateOK
#assert_axioms coordOkForestG_commits
#assert_axioms coordViolatedForestG_caveats_fma0
#assert_axioms coordViolatedForestG_gate_rejects
#assert_axioms coordViolatedForestG_rolls_back

/-! ### A4 — the MACAROON CAVEAT-CHAIN operator, EXECUTED on the live gate (HMAC tail-binding teeth).

Tiers 1-3 (within-cell / cap-authority / coordinated) are witnessed above; the FOURTH authority
operator — the macaroon HMAC caveat-CHAIN (`NodeAuth.chain`) — was, until here, only ever pinned
`chain := none` on the live `execFullForestG` path, so its `chainGateG` leg ran only in its no-op
ABSENT arm. The chain LAWS are proved in `Authority/CaveatChain.lean` (`removal_breaks_tail` /
`chain_unforgeable` consuming `MacKernel.unforgeable`), but a guarantee that never fires on the live
gate is narrated, not executed. This section welds a REAL macaroon chain onto a live gated forest's
root `NodeAuth.chain` and witnesses it BOTH ways on the SAME `execFullForestG` entry:

  * a GENUINE, in-window chain (`CaveatChain.Demo.windowed` — a `seed` then two honest `append`s,
    verifying by `honest_chain_verifies`, admitting at height `150 ∈ [100,200]`) ⇒ `chainGateG = true`
    ⇒ `caveatsDischarged = true` ⇒ the gate ADMITS ⇒ the forest COMMITS;
  * a FORGED chain (`CaveatChain.Demo.forgedDropped` — `windowed`'s tail kept but the last caveat
    DROPPED without re-signing, the `test_removed_caveat_fails` attack) ⇒ `Chain.verify = false`
    (`removal_breaks_tail` is why: the dropped HMAC step is no no-op under a sound `mac`) ⇒
    `chainGateG = false` ⇒ `caveatsDischarged = false` ⇒ the gate REJECTS ⇒ `execFullForestG = none`,
    rollback.

So the HMAC tail-binding is EXECUTED end-to-end on the live gate — caveat-removal is caught at the
executor admission, not in a side theorem. Non-vacuous each direction (verify-true admits AND
verify-false rejects), on the same production entry as tiers 1-3. The macaroon `MacKernel` here is the
honest reference kernel (`CaveatChain.honestMacKernel`), whose `unforgeable` carrier is PROVED
(`honest_unforgeable`) and is provably FALSE for the collapsing kernel (`collapse_not_unforgeable`) —
so the integrity is load-bearing, not a `True` no-op. -/

open Dregg2.Authority.CaveatChain (Chain)
open Dregg2.Authority.CaveatChain.Demo (windowed forgedDropped)

/-- A node-auth carrying a REAL macaroon caveat-chain in `NodeAuth.chain` (the fourth authority
operator, live). The credential (WHO) and cap-authority (WHAT) are the same genuine/`.unchecked` legs
`mkAuth` pins; only `chain` is the load-bearing macaroon. `chainCtx := 150` lands inside the chain's
`[100,200]` window, and `chainDis` supplies no third-party discharges (the chain has none). -/
def mkAuthChain (cred : Authorization Dg Pf) (caveats : List GatedCaveat)
    (chain : Chain Cx Gw (Nat) Bt Tg) : DNodeAuth :=
  { cred := cred, rev := Credential.noRevocations
  , capMode := .unchecked (Guard.all []), capCtx := baseCapCtx
  , caveats := caveats, chain := some chain, chainCtx := 150, chainDis := fun _ => false }

/-- A live gated forest whose root carries the GENUINE in-window macaroon chain. Balance-neutral
`emitEvent`, so the only authority that matters is the chain's verify+admit. ADMITS. -/
def chainOkForestG : DForest :=
  ⟨ mkAuthChain goodCred [trueCaveat] windowed, .emitEventA 0 0 0 0, [] ⟩

/-- A live gated forest whose root carries the FORGED (caveat-dropped) macaroon chain. Identical
except the chain fails `verify`. REJECTED by the chain leg. -/
def chainForgedForestG : DForest :=
  ⟨ mkAuthChain goodCred [trueCaveat] forgedDropped, .emitEventA 0 0 0 0, [] ⟩

/-- **`chainOkForestG_chainGate` — the genuine chain's HMAC gate PASSES.** `chainGateG`
unfolds to `windowed.verify && windowed.admits 150 _`; the honest chain verifies and admits in-window. -/
theorem chainOkForestG_chainGate : chainGateG chainOkForestG.auth = true := by
  unfold chainOkForestG mkAuthChain chainGateG
  decide

/-- **`chainForgedForestG_chainGate` — the forged chain's HMAC gate FAILS (the teeth).**
`forgedDropped.verify = false` (the dropped caveat broke the tail — `removal_breaks_tail`), so the
`&&` short-circuits to `false`. NON-VACUOUS against the genuine chain above. -/
theorem chainForgedForestG_chainGate : chainGateG chainForgedForestG.auth = false := by
  unfold chainForgedForestG mkAuthChain chainGateG
  decide

/-- The genuine-chain forest's caveat leg discharges at `fma0` (`trueCaveat` ∧ the verifying chain). -/
theorem chainOkForestG_caveats_fma0 : caveatsDischarged chainOkForestG.auth fma0 = true := by
  unfold chainOkForestG mkAuthChain caveatsDischarged trueCaveat chainGateG fma0
  decide

/-- The genuine-chain forest passes the full 4-leg gate at `fma0`. -/
theorem chainOkForestG_gateOK : gateOK chainOkForestG.auth fma0 = true := by
  have hcred : credentialValidG chainOkForestG.auth = true := by
    unfold chainOkForestG mkAuthChain credentialValidG goodCred; decide
  have hcap : capAuthorityG chainOkForestG.auth = true := by
    unfold chainOkForestG mkAuthChain capAuthorityG
    exact unchecked_unconstrained_admits (Guard.all []) baseCapCtx (fun _ _ => by simp)
  have hrev : revocationGate chainOkForestG.auth fma0 = true := by
    unfold chainOkForestG mkAuthChain revocationGate fma0; simp
  unfold gateOK
  simp only [Bool.and_eq_true, hcred, hcap, chainOkForestG_caveats_fma0, hrev]
  trivial

/-- **`chainOkForestG_commits` — the GENUINE macaroon chain COMMITS end-to-end on the live
`execFullForestG` path.** The whole gated forest runs and produces a post-state — the HMAC
chain is verified+admitted inline by `chainGateG`, on the SAME production entry as tiers 1-3. -/
theorem chainOkForestG_commits : (execFullForestG fma0 chainOkForestG).isSome := by
  have herase : (execFullForestA fma0 (eraseG chainOkForestG)).isSome := by decide
  rcases Option.isSome_iff_exists.mp herase with ⟨s', hs'⟩
  refine Option.isSome_iff_exists.mpr ⟨s', ?_⟩
  dsimp [execFullForestG, chainOkForestG, execFullChildrenG]
  have hga := (execFullAGated_some_iff fma0 s' (mkAuthChain goodCred [trueCaveat] windowed)
    (.emitEventA 0 0 0 0)).mpr ⟨chainOkForestG_gateOK, hs'⟩
  simpa [hga]

/-- The forged-chain forest's caveat leg FAIL-CLOSES at `fma0` (the chain leg breaks the meet). -/
theorem chainForgedForestG_caveats_fma0 : caveatsDischarged chainForgedForestG.auth fma0 = false := by
  unfold chainForgedForestG mkAuthChain caveatsDischarged trueCaveat chainGateG fma0
  decide

/-- The forged-chain forest is REJECTED by the full gate (the chain leg fail-closes the conjunction). -/
theorem chainForgedForestG_gate_rejects : gateOK chainForgedForestG.auth fma0 = false := by
  unfold gateOK
  rw [chainForgedForestG_caveats_fma0]
  simp

/-- **`chainForgedForestG_rolls_back` — the FORGED macaroon chain does NOT commit (the
teeth).** The dropped caveat broke the HMAC tail ⇒ `execFullForestG = none` ⇒ whole-forest rollback.
Caveat-removal is caught at the EXECUTOR ADMISSION, non-vacuously against `chainOkForestG_commits`. -/
theorem chainForgedForestG_rolls_back : execFullForestG fma0 chainForgedForestG = none := by
  have hgate : gateOK chainForgedForestG.auth fma0 = false := chainForgedForestG_gate_rejects
  unfold chainForgedForestG at hgate ⊢
  show (match execFullAGated fma0 (mkAuthChain goodCred [trueCaveat] forgedDropped)
            (.emitEventA 0 0 0 0) with
        | some s' => execFullChildrenG (targetOf (.emitEventA 0 0 0 0)) s' ([] : List DChild)
        | none    => none) = none
  rw [execFullAGated]
  simp only [hgate]
  rfl

-- The macaroon caveat-chain operator is EXECUTED end-to-end on the live gate, both ways:
#guard (chainGateG chainOkForestG.auth)                          --  true  (honest chain verifies+admits)
#guard (chainGateG chainForgedForestG.auth) == false             --  false (forged: dropped caveat)
#guard (caveatsDischarged chainOkForestG.auth fma0)              --  true
#guard (caveatsDischarged chainForgedForestG.auth fma0) == false --  false
#guard ((execFullForestG fma0 chainOkForestG).isSome)               --  true  (chain COMMITS)
#guard ((execFullForestG fma0 chainForgedForestG).isSome) == false  --  false (forged chain ⇒ rollback)

#assert_axioms chainOkForestG_chainGate
#assert_axioms chainForgedForestG_chainGate
#assert_axioms chainOkForestG_caveats_fma0
#assert_axioms chainOkForestG_gateOK
#assert_axioms chainOkForestG_commits
#assert_axioms chainForgedForestG_caveats_fma0
#assert_axioms chainForgedForestG_gate_rejects
#assert_axioms chainForgedForestG_rolls_back

end StarbridgeGated

end Dregg2.Exec