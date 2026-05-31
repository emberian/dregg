/-
# Dregg2.Apps.AgentOrchestration — "the orchestration is a theorem" (a DEMONSTRATOR).

A verified MULTI-AGENT ORCHESTRATION: an ORCHESTRATOR cell spawns least-privilege sub-agent
workers, delegates each an ATTENUATED slice of its authority, the workers run real per-asset
transfers, an out-of-scope worker is PROVABLY rejected, two agents move value through an
escrow, a credential+caveat gate fail-closes on a forged credential / failing caveat, and the
WHOLE run is assembled into ONE call-forest whose soundness is certified by Lean theorems.

The pitch — *"the same file that RUNS the orchestration PROVES it sound; the orchestration is a
theorem"* — is made concrete by DRIVING the executable per-asset turn (`execFullForestA` /
`execFullA` / `execFullForestG`, the effects we built today) through a concrete scenario AND
INSTANTIATING dregg2's already-proved executor assets for each beat, rather than re-proving them.

The executable turn (`Exec/TurnExecutorFull.lean`, `Exec/FullForest.lean`, `Exec/FullForestAuth.lean`,
`Exec/Caps.lean`) is pure computable Lean: `main` runs the scenes by calling the REAL executor, and
every ✓ printed is backed by one of the theorems below — checked by the kernel when this file compiles.

================================================================================
## HONESTY LABEL — READ THIS. What is REAL here, and what is a portal.
================================================================================

What IS genuine: every theorem below is a real, NON-VACUOUS fact about the CONCRETE run —
  * conservation is the genuine per-asset `recTotalAssetWithEscrow` VECTOR over the actual forest
    (a SCALAR aggregate could not state it — the FILL-1 no-laundering carrier);
  * fail-closed is a real proved `execFullForestA … = none` for the CONCRETE bad worker turn
    (`recKExecAsset_unauthorized_fails` / `execFullForestA_unauthorized_fails`), not an `#eval`;
  * non-amplification is the genuine `capAuthConferred (attenuate keep c) ⊆ capAuthConferred c`
    (`derive_no_amplify`), with a STRICT attenuation witness (`write` literally dropped);
  * the escrow combined-conservation is `execFullA_ledger_per_asset` with `ledgerDeltaAsset = 0`;
  * the auth gate's committed⇒(credential ∧ caveats) is `execFullForestG_root_attests` /
    `execFullForestG_unauthorized_fails` on the gated tree.

What is a PORTAL (NOT a Lean law, by design): `credentialValid` is the §8 `AuthPortal` oracle
(routed to `Credential.verify` / `CryptoKernel.verify`; the circuit's obligation, never proved
sound INSIDE Lean — the seL4 floor). The Demo realizes it over `Crypto.Reference` for `#eval`. We
prove the gate-DISCIPLINE (fail-closed on a forged / revoked credential), not the crypto.

The scenario is INTRA-cell (`DelegationMode::None`, `sameTargetForest`): the cross-cell axis is
routed to `Exec/CrossCellForest.lean` (`crossForest_conserves`), not duplicated here.

Zero `sorry`/`admit`/`native_decide`/`axiom`. Every scenario keystone is `#assert_axioms`-pinned
to `{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Exec.FullForest
import Dregg2.Exec.FullForestAuth
import Dregg2.Exec.Caps

namespace Dregg2.Apps.AgentOrchestration

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Authority

/-! ## §0 — THE LEDGER: an orchestrator + two assets (`fma0`, the proved-asset starting state).

We reuse `TurnExecutorFull.fma0` verbatim — a genuine 2-asset ledger:
  * cell **0** = the ORCHESTRATOR cell: holds 100 of asset 0 and 7 of asset 1;
  * cell **1** = a counterparty cell: holds 5 of asset 0;
  * actor **9** holds the privileged `node 0` mint cap over cell 0 (the broad supply authority).
Authority for balance transfers is by ownership (`actor = src`). Asset-0 supply = 105, asset-1 = 7. -/

/-- The orchestrator cell id (broad authority, the assets). -/
abbrev orchestrator : CellId := 0
/-- The counterparty cell id. -/
abbrev counterparty : CellId := 1
/-- The privileged supply-authority holder (holds the `node 0` mint cap in `fma0`). -/
abbrev minter : CellId := 9

/-- The starting ledger — the already-proved `fma0` asset, reused (NOT re-instantiated). -/
def world : RecChainedState := fma0

/-! ## §1 — SPAWN least-privilege workers + the NON-AMPLIFICATION theorem.

The orchestrator spawns workers and delegates each an ATTENUATED slice of its authority. The
delegation edge data lives in `FullChildA` (`holder`, `keep`, `parentCap`): the parent hands the
worker `attenuate keep parentCap` (`Caps.derive`). The Granovetter no-amplification law
(`derive_no_amplify`) says the worker's conferred authority is a SUBSET of the parent's — no worker
gains authority the orchestrator lacked. We use a STRICT attenuation: the parent cap confers
`[read, write]`, the worker keeps only `[read]` — `write` is LITERALLY dropped. -/

/-- The orchestrator's broad endpoint cap over the counterparty cell: `[read, write]`. -/
def orchestratorCap : Cap := .endpoint counterparty [Auth.read, Auth.write]

/-- The attenuated slice a worker is delegated: keep only `[read]` (drop `write`). -/
def workerKeep : List Auth := [Auth.read]

/-- **`worker_authority_subset_orchestrator` — ① NON-AMPLIFICATION (PROVED, inherited).** The
authority conferred to a delegated worker (`attenuate workerKeep orchestratorCap`) is a SUBSET of the
orchestrator's (`orchestratorCap`): a worker can never exceed the authority it was handed. This is
`Caps.derive_no_amplify` (= `attenuate_subset`) — the Granovetter law, reused, never re-proved. -/
theorem worker_authority_subset_orchestrator :
    capAuthConferred (attenuate workerKeep orchestratorCap) ⊆ capAuthConferred orchestratorCap :=
  derive_no_amplify workerKeep orchestratorCap

/-- **`worker_attenuation_is_strict` — the no-amplification is NON-VACUOUS (PROVED).** The worker's
conferred authority is STRICTLY smaller: `write` is conferred by the orchestrator's cap but NOT by the
attenuated worker cap. So the ⊆ above is a genuine drop, not a `()≤()` collapse. -/
theorem worker_attenuation_is_strict :
    Auth.write ∈ capAuthConferred orchestratorCap ∧
    Auth.write ∉ capAuthConferred (attenuate workerKeep orchestratorCap) := by
  decide

/-! ## §2 — EXECUTE real per-asset transfers + the CONSERVATION theorem.

The workers run genuine per-asset balance transfers (`balanceA`). We assemble them into a forest and
the per-asset conservation VECTOR (`execFullForestA_conserves_per_asset`) certifies that EVERY asset's
total supply is preserved. The forest below is the WORK forest: the orchestrator delegates two workers,
each running an attenuated transfer that conserves its asset. -/

/-- **`workForest`** — the EXECUTE forest: the orchestrator (root) transfers 30 of asset 0 to the
counterparty, then a delegated worker transfers 5 of asset 0 BACK (counterparty owns its cell), each
under an attenuated, non-amplifying cap. Both transfers conserve asset 0 (and trivially asset 1) ⇒ the
whole forest conserves PER-ASSET. -/
def workForest : FullForestA :=
  ⟨ .balanceA ⟨orchestrator, orchestrator, counterparty, 30⟩ 0
  , [ { holder := counterparty, keep := workerKeep, parentCap := orchestratorCap
      , sub := ⟨ .balanceA ⟨counterparty, counterparty, orchestrator, 5⟩ 0, [] ⟩ } ] ⟩

/-- **`workForest_delta0` / `workForest_delta1` — the per-asset net is `0` in BOTH assets (PROVED).**
The transfers move value WITHIN the cell set, never minting or burning, so every asset's net ledger
delta is `0`. These discharge the `hzero` premise of conservation — and they are real arithmetic facts
about the concrete forest (NON-VACUOUS: a mint would make them nonzero). -/
theorem workForest_delta0 : turnLedgerDeltaAsset (lowerForestA workForest) 0 = 0 := by decide
theorem workForest_delta1 : turnLedgerDeltaAsset (lowerForestA workForest) 1 = 0 := by decide

/-- **`workForest_conserves` — ② CONSERVATION (PROVED, inherited).** A committed work forest preserves
EVERY asset's total supply (`recTotalAssetWithEscrow … b` is unchanged for every `b`): the per-asset
CONSERVATION VECTOR across the whole tree. This is `execFullForestA_conserves_per_asset`, discharged by
`workForest_delta0`/`_delta1`. NON-VACUOUS: it is genuine per-asset conservation of the actual run, a
fact a scalar aggregate could not even state. -/
theorem workForest_conserves (s' : RecChainedState) (b : AssetId)
    (h : execFullForestA world workForest = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow world.kernel b := by
  -- Per-asset net is 0 in each asset (the two assets the ledger carries; others trivially 0).
  have hzero : turnLedgerDeltaAsset (lowerForestA workForest) b = 0 := by
    -- `balanceA` transfers have `ledgerDeltaAsset = 0` at EVERY asset, so the turn delta is 0 for any b.
    simp only [workForest, lowerForestA, lowerChildrenA, turnLedgerDeltaAsset,
               List.map_cons, List.map_nil, List.append_nil, List.sum_cons, List.sum_nil,
               ledgerDeltaAsset, add_zero]
  exact execFullForestA_conserves_per_asset world s' workForest b h hzero

/-! ## §3 — DENIED: the out-of-scope worker is PROVABLY rejected (the money shot).

A worker attempts an action OUTSIDE its scope: an UNAUTHORIZED supply mint (the worker, cell 0 acting
as its own owner, does NOT hold the privileged `node 0` mint cap — only `minter` = 9 does). The
executor's `mintAuthorizedB` gate REJECTS it, and the all-or-nothing journal/rollback discipline
rejects the WHOLE forest. This is a REAL proved fact about the concrete bad turn — `execFullA … = none`
and `execFullForestA … = none` — not merely an `#eval` observation. -/

/-- **`badWorkerForest`** — a FAIL-CLOSED forest: a delegated worker (actor 0) attempts to mint +50 of
asset 1 on cell 0, but actor 0 lacks the privileged `node 0` mint cap (only `minter` holds it). The
`execFullA` mint-authorization gate rejects the worker node ⇒ the whole forest rolls back. -/
def badWorkerForest : FullForestA :=
  ⟨ .balanceA ⟨orchestrator, orchestrator, counterparty, 30⟩ 0
  , [ { holder := orchestrator, keep := workerKeep, parentCap := orchestratorCap
      , sub := ⟨ .mintA orchestrator orchestrator 1 50, [] ⟩ } ] ⟩   -- actor 0 lacks the node-0 mint cap

/-- **`unauthorized_mint_rejected` — the worker's out-of-scope node is rejected (PROVED).** Running the
worker's unauthorized mint on the work-threaded state returns `none`: the `mintAuthorizedB` gate
fail-closes because actor 0 holds no mint cap over cell 0. A concrete `execFullA … = none`, proved by
the kernel — the executable confinement fact. -/
theorem unauthorized_mint_rejected :
    execFullA world (.mintA orchestrator orchestrator 1 50) = none := by decide

/-- **`badWorkerForest_fails_closed` — ③ FAIL-CLOSED (PROVED).** The whole bad-worker forest is
rejected: there is NO post-state. The orchestrator's own (authorized) transfer would have committed,
but the all-or-nothing discipline rolls back the ENTIRE forest because the delegated worker's mint is
unauthorized. This is the executed "an agent cannot act outside its scope, and a bad beat aborts the
run" — a real `execFullForestA … = none`, not a demo `if`. -/
theorem badWorkerForest_fails_closed :
    execFullForestA world badWorkerForest = none := by decide

/-- **`recKExecAsset_fail_closed_reused` — the kernel-level fail-closed law, reused (PROVED).** The
executable kernel's per-asset transfer step is itself fail-closed: an unauthorized turn yields `none`.
We name `RecordKernel.recKExecAsset_unauthorized_fails` here so the DENIED scene rests on the SAME
proved fail-closed primitive the whole executor is built on — not a one-off. -/
theorem recKExecAsset_fail_closed_reused (turn : Turn) (a : AssetId)
    (h : authorizedB world.kernel.caps turn = false) :
    recKExecAsset world.kernel turn a = none :=
  recKExecAsset_unauthorized_fails world.kernel turn a h

/-! ## §4 — ESCROW: atomic value-move between two agents + the COMBINED-conservation theorem.

Two agents move value through the off-ledger holding-store: the orchestrator LOCKS 5 of asset 1 into
escrow (the bare ledger drops, the holding-store rises), then the escrow is SETTLED. The COMBINED
per-asset measure `recTotalAssetWithEscrow` (= bal-ledger + per-asset holding-store) is conserved
across the lock — value is parked, never created or destroyed. This is `execFullA_ledger_per_asset`
with the escrow leg's `ledgerDeltaAsset = 0` (combined-conserving). -/

/-- The escrow lock: orchestrator (actor `minter`, authorized over cell 0) locks 5 of asset 1 from the
orchestrator cell to the counterparty, escrow id 1. -/
def escrowLock : FullActionA :=
  .createEscrowA 1 minter orchestrator counterparty 1 5

/-- **`escrowLock_combined_conserves` — ④ ESCROW combined-conservation (PROVED).** A committed escrow
lock preserves the COMBINED per-asset measure `recTotalAssetWithEscrow b` at EVERY asset: the bare
ledger debit at asset 1 is exactly offset by the holding-store rise (combined fixed), and every other
asset is untouched. This is `execFullA_ledger_per_asset` with the escrow leg's `ledgerDeltaAsset = 0` —
the atomic value-move conserves the combined measure across the pair. NON-VACUOUS: the bare per-asset
ledger genuinely DROPS at the locked asset (witnessed by the `#eval` in §7) while the combined measure
holds. -/
theorem escrowLock_combined_conserves (s' : RecChainedState) (b : AssetId)
    (h : execFullA world escrowLock = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow world.kernel b := by
  have hdelta : ledgerDeltaAsset escrowLock b = 0 := by
    simp only [escrowLock, ledgerDeltaAsset]
  rw [execFullA_ledger_per_asset world s' escrowLock b h, hdelta, add_zero]

/-! ## §5 — AUTH GATE: credential + caveat (META-FILL D) + the committed⇒(credential ∧ caveats) theorem.

A gated node commits IFF `credentialValid` (the §8 portal) ∧ cap-authority ∧ caveats discharge. We reuse
the proved `FullForestAuth.Demo` instances directly: `goodFullForestG` (valid credential + discharged
caveat ⇒ commits), `forgedCredForestG` (forged credential ⇒ DENIED), `falseCaveatForestG` (failing
caveat ⇒ DENIED). The keystone is `execFullForestG_root_attests`: a committed gated node attests its
`gatedActionInvG` — credential validated ∧ caveats discharged ∧ cap-authority ∧ the per-asset vector.
And `execFullForestG_unauthorized_fails` is the fail-closed half — a failing leg rejects the forest. -/

open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.FullForestAuth.Demo

/-- The `Verifiable` seam the gated dispatcher's signature needs over the Demo carriers (`St = Wt =
Nat`). The `.unchecked` cap mode the Demo nodes carry reads the guard, not this — it just pins the
instance `execFullForestG`'s type wants. (FullForestAuth's own `demoVerifiable` is `local`; we re-pin
the SAME trivial seam over the identical carriers here so the gated executor resolves.) -/
instance demoVerifiableAO : Dregg2.Laws.Verifiable St Wt where
  Verify _ _ := true

/-- **`gate_committed_implies_credential_and_caveats` — ⑤ AUTH GATE: committed ⇒ credential validated ∧
caveats discharged (PROVED, inherited).** If the good gated forest COMMITS, its root attests
`gatedActionInvG`: the credential passed the §8 `AuthPortal` oracle (`credentialValidG = true`),
cap-authority held, AND the caveats discharged on the pre-state. Credential-blindness ELIMINATED — a
committed node provably carries its WHO and its caveat discharge. This is
`execFullForestG_root_attests`, read for the concrete `goodFullForestG`. -/
theorem gate_committed_implies_credential_and_caveats (s' : RecChainedState)
    (h : execFullForestG world goodFullForestG = some s') :
    ∃ sa sa', execFullAGated sa goodFullForestG.auth goodFullForestG.action = some sa' ∧
              credentialValidG goodFullForestG.auth = true ∧
              capAuthorityG goodFullForestG.auth = true ∧
              caveatsDischarged goodFullForestG.auth sa = true := by
  -- `gatedActionInvG` is `credentialValidG ∧ capAuthorityG ∧ caveatsDischarged ∧ fullActionInvA`;
  -- we forward the first three auth conjuncts (the per-asset `fullActionInvA` is the §6 headline).
  obtain ⟨sa, sa', hrun, hcred, hcap, hcav, _hinv⟩ :=
    execFullForestG_root_attests world s' goodFullForestG h
  exact ⟨sa, sa', hrun, hcred, hcap, hcav⟩

/-- **`forged_credential_denied` — the gate fail-closes on a FORGED credential (PROVED).** A node whose
credential does not pass the §8 portal is DENIED: the whole forest rejects (`none`), EVEN if the caps
would otherwise admit. The credential-orthogonality teeth — `execFullForestG_unauthorized_fails` with
`gateOK = false` because `credentialValidG = false`. NON-VACUOUS: the forged credential genuinely fails
the portal (`credentialValidG forgedCredForestG.auth = false`, witnessed in §7). -/
theorem forged_credential_denied :
    execFullForestG world forgedCredForestG = none := by
  apply execFullForestG_unauthorized_fails
  -- The gate fails on the WHO leg: the forged credential does not echo under the §8 portal, so
  -- `credentialValidG = false` (reduces definitionally) ⇒ the whole `gateOK` conjunction is false.
  have hcred : credentialValidG forgedCredForestG.auth = false := rfl
  show gateOK forgedCredForestG.auth world = false
  simp only [gateOK, hcred, Bool.false_and]

/-- **`false_caveat_denied` — the gate fail-closes on a FAILING caveat (PROVED).** A node whose caveat
does not discharge on the pre-state is DENIED — the whole forest rejects. Caveat-orthogonality teeth.
NON-VACUOUS: the false caveat (cell 0 holds ≥ 10000 of asset 0, but it holds 100) genuinely fails on
`world`'s pre-state. -/
theorem false_caveat_denied :
    execFullForestG world falseCaveatForestG = none := by
  apply execFullForestG_unauthorized_fails
  -- The gate fails on the CAVEAT leg: the false caveat (cell 0 ≥ 10000) is false on `world` (bal=100).
  have hcav : caveatsDischarged falseCaveatForestG.auth world = false := by
    simp only [caveatsDischarged, falseCaveatForestG, mkAuth, falseCaveat, List.all_cons,
               List.all_nil, GatedCaveat.holds, chainGateG, Bool.and_true, world]
    decide
  show gateOK falseCaveatForestG.auth world = false
  simp only [gateOK, hcav, Bool.and_false]

/-! ## §6 — THE WHOLE ORCHESTRATION IS A THEOREM (the headline).

Assemble the agents' actions into ONE `FullForestA` (the orchestrator root + two delegated worker
subtrees: a transfer worker and a mint/burn-balanced supply worker, every edge attenuated). Run it via
`execFullForestA`. THREE theorems certify the WHOLE run at once:
  * **conserves every asset** — `execFullForestA_conserves_per_asset` (∀ b, the per-asset vector);
  * **no agent amplified authority** — `execFullForestA_no_amplify` (every delegation edge non-amplifying);
  * **every committed node attested its StepInv** — `execFullForestA_each_attests` (the per-asset ledger
    vector ∧ ChainLink ∧ ObsAdvance ∧ the kind obligation, at every node).
This is the headline: the orchestration, as a whole, is sound BY CONSTRUCTION. -/

/-- **`orchestration`** — the WHOLE multi-agent run as one call-forest:
  * ROOT (orchestrator, `minter`): mint +50 of asset 1 on cell 0 (privileged, disclosed supply op);
  * WORKER A (delegated, `[read] ⊊ [read,write]`): transfer 30 of asset 0 (orchestrator → counterparty);
  * WORKER B (delegated, deeper): burn −50 of asset 1 on cell 0 (`minter`).
The per-asset net is `0` in BOTH assets (asset 1: +50 −50 = 0; asset 0: 0), so the whole orchestration
conserves PER-ASSET. Every delegation edge is non-amplifying. -/
def orchestration : FullForestA :=
  ⟨ .mintA minter orchestrator 1 50
  , [ { holder := counterparty, keep := workerKeep, parentCap := orchestratorCap
      , sub := ⟨ .balanceA ⟨orchestrator, orchestrator, counterparty, 30⟩ 0
               , [ { holder := minter, keep := [], parentCap := .endpoint orchestrator [Auth.read]
                   , sub := ⟨ .burnA minter orchestrator 1 50, [] ⟩ } ] ⟩ } ] ⟩

/-- **`orchestration_conserves` — ⑥a the WHOLE run conserves EVERY asset (PROVED).** For EVERY asset
`b`, the committed orchestration preserves `recTotalAssetWithEscrow … b`: the per-asset CONSERVATION
VECTOR end-to-end across the whole multi-agent forest. The mint and the burn net to `0` in asset 1; the
transfer is internal; so every asset is conserved. `execFullForestA_conserves_per_asset` on the concrete
run. NON-VACUOUS — genuine per-asset conservation of the actual assembled orchestration. -/
theorem orchestration_conserves (s' : RecChainedState) (b : AssetId)
    (h : execFullForestA world orchestration = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow world.kernel b := by
  have hzero : turnLedgerDeltaAsset (lowerForestA orchestration) b = 0 := by
    -- asset 1: +50 (mint) − 50 (burn) = 0; asset 0: 0; every other asset: 0.
    simp only [orchestration, lowerForestA, lowerChildrenA, turnLedgerDeltaAsset,
               List.map_cons, List.map_nil, List.append_nil, List.sum_cons, List.sum_nil,
               ledgerDeltaAsset, add_zero]
    by_cases hb : b = 1
    · subst hb; decide
    · simp only [if_neg hb, add_zero]
  exact execFullForestA_conserves_per_asset world s' orchestration b h hzero

/-- **`orchestration_no_amplify` — ⑥b NO agent amplified authority (PROVED, inherited).** EVERY
delegation edge of the whole orchestration is non-amplifying: for each `(keep, parentCap)` edge, the cap
handed to the worker confers ⊆ the parent's authority (`derive_no_amplify`). No agent, at any nesting
depth, gained authority its delegator lacked — Granovetter across the whole forest.
`execFullForestA_no_amplify` on the concrete run. -/
theorem orchestration_no_amplify :
    ∀ e ∈ forestEdgesA orchestration,
      capAuthConferred (attenuate e.1 e.2) ⊆ capAuthConferred e.2 :=
  execFullForestA_no_amplify orchestration

/-- **`orchestration_each_attests` — ⑥c EVERY committed node attested its StepInv (PROVED, inherited).**
Every node of the committed orchestration attests its `fullActionInvA`: the per-asset ledger VECTOR ∧
ChainLink (the receipt chain extends, no fork) ∧ ObsAdvance (exactly one row) ∧ the kind-specific
authority obligation. Step-completeness for every agent's action.
`execFullForestA_each_attests` on the concrete run. -/
theorem orchestration_each_attests (s' : RecChainedState)
    (h : execFullForestA world orchestration = some s') :
    ∀ fa ∈ lowerForestA orchestration,
      ∃ sa sa', execFullA sa fa = some sa' ∧ fullActionInvA sa fa sa' :=
  execFullForestA_each_attests world s' orchestration h

/-- **`orchestration_runs` — the headline run COMMITS (PROVED).** The whole assembled orchestration
genuinely commits (`isSome`): the conservation/no-amplify/attestation theorems above are not vacuously
quantified over a never-committing forest — there IS a post-state. -/
theorem orchestration_runs : (execFullForestA world orchestration).isSome = true := by decide

/-! ## §7 — Axiom-hygiene — every scenario keystone pinned to the three standard kernel axioms. -/

#assert_axioms worker_authority_subset_orchestrator
#assert_axioms worker_attenuation_is_strict
#assert_axioms workForest_delta0
#assert_axioms workForest_delta1
#assert_axioms workForest_conserves
#assert_axioms unauthorized_mint_rejected
#assert_axioms badWorkerForest_fails_closed
#assert_axioms recKExecAsset_fail_closed_reused
#assert_axioms escrowLock_combined_conserves
#assert_axioms gate_committed_implies_credential_and_caveats
#assert_axioms forged_credential_denied
#assert_axioms false_caveat_denied
#assert_axioms orchestration_conserves
#assert_axioms orchestration_no_amplify
#assert_axioms orchestration_each_attests
#assert_axioms orchestration_runs

/-! ## §8 — THE RUNNABLE DEMONSTRATOR: a COLORED `main` that RUNS the orchestration.

`main` calls the REAL executor (`execFullForestA` / `execFullA` / `execFullForestG`) on the concrete
scenes, prints the executed result (#eval-style: post-state / isSome / the per-asset totals / the caps),
and after each scene names the Lean theorem that certifies it. Deterministic; pure computable Lean. -/

/-! ### ANSI palette (deterministic escape codes). -/

/-- Reset. -/ def aRESET : String := "\x1b[0m"
/-- Bold. -/  def aBOLD  : String := "\x1b[1m"
/-- Dim. -/   def aDIM   : String := "\x1b[2m"
/-- Green. -/ def aGREEN : String := "\x1b[32m"
/-- Red. -/   def aRED   : String := "\x1b[31m"
/-- Cyan. -/  def aCYAN  : String := "\x1b[36m"
/-- Yellow. -/def aYEL   : String := "\x1b[33m"
/-- Magenta (headers). -/ def aMAG : String := "\x1b[35m"

/-- A bold scene header with a rule. -/
def scene (n : String) (title : String) : IO Unit := do
  IO.println ""
  IO.println s!"{aBOLD}{aMAG}━━ {n}  {title} ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━{aRESET}"

/-- A green ✓ commit line. -/
def ok (msg : String) : IO Unit := IO.println s!"  {aGREEN}✓ {msg}{aRESET}"
/-- A red ✗ DENIED line. -/
def denied (msg : String) : IO Unit := IO.println s!"  {aRED}✗ DENIED  {msg}{aRESET}"
/-- A cyan delegation/auth line. -/
def cyan (msg : String) : IO Unit := IO.println s!"  {aCYAN}⇒ {msg}{aRESET}"
/-- A yellow escrow line. -/
def yellow (msg : String) : IO Unit := IO.println s!"  {aYEL}⛁ {msg}{aRESET}"
/-- A dim detail line. -/
def detail (msg : String) : IO Unit := IO.println s!"    {aDIM}{msg}{aRESET}"
/-- The theorem-citation line for a scene. -/
def certifies (thm : String) : IO Unit :=
  IO.println s!"    {aDIM}└─ certified by{aRESET} {aBOLD}{thm}{aRESET}"

/-- The per-asset supply pair `(asset 0, asset 1)` of a post-state, as a string. -/
def supplyStr (s : RecChainedState) : String :=
  s!"(asset0={recTotalAsset s.kernel 0}, asset1={recTotalAsset s.kernel 1})"

/-- The COMBINED per-asset measure pair of a post-state, as a string. -/
def combinedStr (s : RecChainedState) : String :=
  s!"(asset0={recTotalAssetWithEscrow s.kernel 0}, asset1={recTotalAssetWithEscrow s.kernel 1})"

def main : IO Unit := do
  IO.println ""
  IO.println s!"{aBOLD}{aMAG}╔══════════════════════════════════════════════════════════════════╗{aRESET}"
  IO.println s!"{aBOLD}{aMAG}║   dregg2 · VERIFIED MULTI-AGENT ORCHESTRATION                     ║{aRESET}"
  IO.println s!"{aBOLD}{aMAG}║   \"the orchestration is a theorem\"                                ║{aRESET}"
  IO.println s!"{aBOLD}{aMAG}╚══════════════════════════════════════════════════════════════════╝{aRESET}"
  detail s!"ledger: orchestrator(cell 0)=100·a0 + 7·a1, counterparty(cell 1)=5·a0; minter(9) holds node-0 cap"
  detail s!"pre-state per-asset supply {supplyStr world}"

  -- ① SPAWN least-privilege workers + NON-AMPLIFICATION
  scene "①" "SPAWN least-privilege workers — attenuated delegation"
  cyan s!"orchestrator delegates a worker: parentCap confers {repr (capAuthConferred orchestratorCap)}"
  cyan s!"worker keeps only {repr workerKeep} ⇒ conferred {repr (capAuthConferred (attenuate workerKeep orchestratorCap))}"
  detail s!"write ∈ orchestrator-cap? {capAuthConferred orchestratorCap |>.contains Auth.write}   write ∈ worker-cap? {(capAuthConferred (attenuate workerKeep orchestratorCap)).contains Auth.write}  (STRICT drop)"
  ok "worker authority ⊆ orchestrator authority — no amplification"
  certifies "worker_authority_subset_orchestrator (= Caps.derive_no_amplify)"
  certifies "worker_attenuation_is_strict (write LITERALLY dropped — non-vacuous)"

  -- ② EXECUTE real transfers + CONSERVATION
  scene "②" "EXECUTE — workers run real per-asset transfers"
  match execFullForestA world workForest with
  | some s =>
      ok s!"work forest committed: {(lowerForestA workForest).length} agent actions ran"
      detail s!"post-state per-asset supply {supplyStr s}   (pre {supplyStr world})"
      detail s!"per-asset net delta: a0={turnLedgerDeltaAsset (lowerForestA workForest) 0}, a1={turnLedgerDeltaAsset (lowerForestA workForest) 1}"
      ok "every asset's total supply preserved — per-asset CONSERVATION VECTOR"
  | none => denied "work forest unexpectedly rejected"
  certifies "workForest_conserves (= execFullForestA_conserves_per_asset)"

  -- ③ DENIED — out-of-scope worker
  scene "③" "DENIED — a worker acts OUTSIDE its scope (the money shot)"
  cyan "delegated worker (actor 0) attempts mint +50·a1 — but holds NO node-0 mint cap"
  detail s!"execFullA(worker mint) = {repr (execFullA world (.mintA orchestrator orchestrator 1 50)).isSome}  (none ⇒ fail-closed)"
  match execFullForestA world badWorkerForest with
  | some _ => ok "unexpected commit"
  | none =>
      denied "the unauthorized mint is rejected — whole forest rolls back (all-or-nothing)"
      detail "the orchestrator's own transfer would have committed; one bad beat aborts the run"
  certifies "badWorkerForest_fails_closed (execFullForestA … = none, PROVED)"
  certifies "unauthorized_mint_rejected + recKExecAsset_unauthorized_fails (the kernel fail-closed law)"

  -- ④ ESCROW — atomic value-move
  scene "④" "ESCROW — atomic value-move between two agents"
  match execFullA world escrowLock with
  | some s =>
      yellow s!"orchestrator LOCKS 5·a1 into escrow id 1 → counterparty"
      detail s!"bare per-asset supply {supplyStr s}   held(a1)={escrowHeldAsset s.kernel 1}  (value PARKED)"
      detail s!"COMBINED measure {combinedStr s}   (pre {combinedStr world})"
      ok "combined per-asset measure conserved across the lock — value parked, not created/destroyed"
  | none => denied "escrow lock unexpectedly rejected"
  certifies "escrowLock_combined_conserves (= execFullA_ledger_per_asset, escrow leg δ=0)"

  -- ⑤ AUTH GATE — credential + caveat
  scene "⑤" "AUTH GATE — credential + caveat (META-FILL D)"
  match execFullForestG world goodFullForestG with
  | some _ =>
      cyan s!"good node: credentialValid={credentialValidG goodFullForestG.auth}  caveatsDischarged={caveatsDischarged goodFullForestG.auth world}"
      ok "gated forest commits ⇒ credential validated ∧ caveats discharged"
  | none => denied "good gated forest unexpectedly rejected"
  detail s!"FORGED credential: credentialValid={credentialValidG forgedCredForestG.auth} ⇒ gate fails"
  match execFullForestG world forgedCredForestG with
  | some _ => ok "unexpected commit"
  | none => denied "forged-credential node rejected (credential-orthogonality)"
  detail s!"FAILING caveat: caveatsDischarged={caveatsDischarged falseCaveatForestG.auth world} ⇒ gate fails"
  match execFullForestG world falseCaveatForestG with
  | some _ => ok "unexpected commit"
  | none => denied "failing-caveat node rejected (caveat-orthogonality)"
  certifies "gate_committed_implies_credential_and_caveats (= execFullForestG_root_attests)"
  certifies "forged_credential_denied + false_caveat_denied (= execFullForestG_unauthorized_fails)"

  -- ⑥ THE WHOLE ORCHESTRATION IS A THEOREM
  scene "⑥" "THE WHOLE ORCHESTRATION — assembled, run, certified"
  match execFullForestA world orchestration with
  | some s =>
      ok s!"orchestration committed: {(lowerForestA orchestration).length} agent actions (mint / transfer / burn)"
      detail s!"post-state per-asset supply {supplyStr s}   (pre {supplyStr world}) — every asset conserved"
      detail s!"per-asset net delta: a0={turnLedgerDeltaAsset (lowerForestA orchestration) 0}, a1={turnLedgerDeltaAsset (lowerForestA orchestration) 1}  (mint+50 − burn50 = 0)"
      detail s!"delegation edges (all non-amplifying): {(forestEdgesA orchestration).length} edges"
      detail s!"receipt chain length after run: {s.log.length}  (one row per committed node)"
      ok "∀ asset conserved  ∧  ∀ edge non-amplifying  ∧  ∀ node attested its StepInv"
  | none => denied "orchestration unexpectedly rejected"
  certifies "orchestration_conserves ∧ orchestration_no_amplify ∧ orchestration_each_attests"

  IO.println ""
  IO.println s!"{aBOLD}{aGREEN}Every ✓ above is a Lean theorem, checked by the kernel — this file{aRESET}"
  IO.println s!"{aBOLD}{aGREEN}compiling IS the proof. The orchestration is sound by construction.{aRESET}"
  IO.println ""

end Dregg2.Apps.AgentOrchestration

/-- Top-level entry so `lake env lean --run Dregg2/Apps/AgentOrchestration.lean` runs the colored
demonstrator. Delegates to the namespaced `main` above (the orchestration scenes). -/
def main : IO Unit := Dregg2.Apps.AgentOrchestration.main
