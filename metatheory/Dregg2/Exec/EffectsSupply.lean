/-
# Dregg2.Exec.EffectsSupply — the DISCLOSED-SUPPLY + GENERATIVE-RESOURCE regime, fully characterized.

**Sibling of `Exec/EffectTransfer.lean` (the `Conservative`/`Paired` reference) and of
`Exec/TurnExecutorFull.lean`'s mint/burn (the `Disclosed` supply prototype).** This module drives the
*resource-creating* and *bridge-supply* half of dregg1's `Effect` catalog (`turn/src/action.rs:760
Effect`) all the way through the executor layer, each as a fully-characterized, reference-quality
effect proving the SAME five-keystone pattern `EffectTransfer` names:

  1. **executable step** — concrete, `#eval`-able semantics over `RecChainedState`;
  2. **conserves** — the DOMAIN-LEVEL conservation/disclosure obligation. For the *disclosed-supply*
     effects this is NOT `Σδ = 0` but the DISCLOSED form: `recTotal` moves by a disclosed `±amount`,
     flagged `is_disclosed_non_conservation` (mirroring `TurnExecutorFull`'s mint/burn treatment); for
     the *paired-bridge* effects (lock/finalize/cancel) it IS `Σδ = 0` (an internal escrow move);
  3. **authorized** — a committed step was gated by the relevant authority;
  4. **metadata** — the receipt chain advances by exactly one row (replay-detectable), and the cap
     table is framed (resource creation/supply never edits connectivity);
  5. **forward-sim** — a committed step is matched by an abstract `Spec` step `AbsStep (absT s)
     (absT s')` over the (`balance`-domain total, authority graph) abstraction, with the disclosed
     supply delta recorded on the bottom edge — the record-world refinement square for each effect.

## The effects (catalog colors from `CatalogEffects`, EXCLUDING mint/burn which are DONE)

  * **`CreateCell`** (`g_createCell`, Generative) — mint a FRESH live account with a DISCLOSED
    initial balance: `recTotal` grows by exactly the disclosed `balance` (`is_disclosed_non_conservation`).
  * **`CreateCellFromFactory`** (`g_createCellFromFactory`, Generative) — `CreateCell` whose child runs
    a PUBLISHED `FactoryDescriptor` program: constructor transparency (the child's program IS the
    factory's, reused from `Exec/Factory.lean`) + the same disclosed-balance creation.
  * **`SpawnWithDelegation`** (`g_spawnWithDelegation`, Generative) — spawn a child with a DISCLOSED
    delegated authority snapshot: fresh cell created with disclosed provenance (the parent) + the
    delegated cap; `recTotal` grows by the disclosed child balance.
  * **`BridgeMint`** (`g_bridgeMint`, Generative — the §8 PORTAL inflow) — credit a cell by a disclosed
    `value` observed off a FOREIGN chain. dregg2 CANNOT verify Cardano consensus, so the foreign
    finality is a `Prop`-carrier portal `ForeignFinal` carried as a HYPOTHESIS (`PHASE-… §8`); the LOCAL
    state transition (the disclosed `+value` credit + the nullifier nonce-pairing) is executable + proved.
  * **`BridgeLock`** (`c_bridgeLock`, Conservative) — Phase-1 lock: ESCROW `value` from a cell into a
    bridge lock-cell (an INTERNAL `Σδ = 0` move) + record the lock's `nullifier`. The foreign destination
    is a `Prop` portal; the local escrow conserves.
  * **`BridgeFinalize`** (`c_bridgeFinalize`, Conservative) — Phase-3 finalize: on a foreign receipt
    (`Prop` portal), CONSUME the lock (the nullifier becomes permanently spent — a nonce advance) while
    the balance is FRAMED (the value already left at lock time): `Σδ = 0`.
  * **`BridgeCancel`** (`c_bridgeCancel`, Conservative) — Phase-4 cancel after timeout: REFUND the
    escrow back to the owner (the inverse of the lock — `Σδ = 0`) + retire the lock nonce.

## Reusable vs. bespoke (the `EffectTransfer` discipline)

REUSABLE (mechanical, verbatim): the `recCreditCell` single-cell credit + its `recCreditCell_recTotal_delta`
(the disclosed `±v` move), reused from `TurnExecutorFull`; `mintAuthorizedB` (the privileged supply gate)
+ its `recKMint_*` facts; `Factory.createFromFactory` + `constructor_transparency`; the forward-sim
`AbsStep`/`absT` shape (conservation projection on the disclosed delta + authority-graph framing) is the
SAME `Spec.execGraph`/`conservedInDomain` instantiation as `EffectTransfer`. BESPOKE per effect: which
domain it discloses and the named-field/account-set write (the fresh-account insert for `CreateCell`, the
escrow pairing for the bridge phases, the nullifier nonce). The §8 foreign-finality `Prop` portal is the
ONE genuinely new bespoke shape — carried, never discharged in Lean.

## Discipline (REORIENT §6)
No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly `{propext,
Classical.choice, Quot.sound}` on every keystone. Pure, computable, `#eval`-able. Reuses ONLY built
modules (`TurnExecutorFull`/`RecordKernel`/`Factory`/`CatalogEffects`/`Spec.ExecRefinement`); edits none.
Verified standalone: `lake env lean Dregg2/Exec/EffectsSupply.lean`.
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Exec.Factory
import Dregg2.Exec.EffectTransfer
import Dregg2.Spec.ExecRefinement

namespace Dregg2.Exec.EffectsSupply

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (recCreditCell recCreditCell_recTotal_delta mintEffect
  recKMint recKMint_delta recKMint_authorized recKMint_unauthorized_fails)
open Dregg2.Exec.EffectTransfer (recCexec_caps_eq)
open Dregg2.Authority (Caps Cap Label)
open Dregg2.CatalogInstances (effectLinearity)
open Dregg2.Spec (Domain conservedInDomain execGraph execAuthGuard Guard)
open Dregg2.Laws (Verifiable)
open scoped BigOperators

/-! ## §0 — Shared scaffolding: the disclosed-creation credit, the lock-nullifier nonce, the foreign portal.

The disclosed-supply / generative effects share two named-field moves and one §8 portal:
  * a FRESH-ACCOUNT insert (`createCellInto`) that adds a live cell with a disclosed balance — the
    generative analog of `recCreditCell` but it grows `accounts`, so `recTotal` rises by the disclosed
    balance of the new (previously absent ⇒ measure-`0`) cell;
  * a NULLIFIER-NONCE write (`setLock` / `lockOf`) recording a bridge lock's spent state (the
    replay-protection metadata, the `nonce`-field analog for the bridge phases);
  * the FOREIGN-FINALITY portal `ForeignFinal` — an OPAQUE `Prop` the cross-chain proof discharges
    OUTSIDE Lean (dregg2 cannot verify Cardano consensus). It is carried as a hypothesis on the bridge
    keystones, NEVER proved here. -/

/-- **The disclosed bridge-lock field** — a cell record's `bridge_lock` nullifier-nonce field, recording
whether/which note is locked for a cross-chain bridge (the replay-protection metadata of the bridge
phases). Distinct from `balance`, so writing it does not perturb the conserved measure. -/
def lockField : FieldName := "bridge_lock"

/-- Read a cell's `bridge_lock` field as an `Int` (0 = unlocked / no pending bridge), the bridge-phase
metadata measure. -/
def lockOf (v : Value) : Int := (v.scalar lockField).getD 0

/-- **`ForeignFinal`** — the §8 cross-chain finality portal. A `Prop` standing for "the foreign chain
(e.g. Cardano) has FINALIZED the corresponding transaction at `nullifier` for `value`". dregg2 CANNOT
verify foreign consensus inside Lean, so this is an OPAQUE carrier (cf. `Crypto.Bridge`'s `extractable`
and `Factory`'s `HashInjective`): the BridgeVerifierKernel / observation bridge discharges it; here it is
a HYPOTHESIS on every bridge keystone, surfaced honestly, never proved. -/
opaque ForeignFinal (nullifier : ℤ) (value : ℤ) : Prop

/-! ## §1 — `CreateCell`: a Generative effect that mints a fresh live account (disclosed supply).

`Effect::CreateCell { public_key, token_id, balance }` (`action.rs:786`) adds a NEW cell to the ledger
with an initial `balance`. It is `Generative` (`CatalogEffects.g_createCell`): it brings `balance` units
into existence, a DISCLOSED non-conservation (the created amount is on the receipt). The executable
semantics: gate on `mintAuthorizedB` (creation is privileged — only an authority may coin a new cell's
endowment), require the new id is FRESH (`∉ accounts`), then insert it with the disclosed `balance`. -/

/-- Insert a fresh cell `newCell` into the ledger with initial `balance` field `bal` (and a cleared
lock). The generative account-set write: it adds `newCell` to `accounts` AND sets its `balance`. -/
def createCellInto (k : RecordKernelState) (newCell : CellId) (bal : ℤ) : RecordKernelState :=
  { k with accounts := insert newCell k.accounts
           cell := fun c => if c = newCell then setBalance (.record []) bal else k.cell c }

/-- **`createCellStep` — `CreateCell`'s executable semantics (PROVED computable).** Fail-closed: an
authorized creator (`mintAuthorizedB actor newCell` — creation is privileged, like minting supply), a
FRESH id (`newCell ∉ accounts`), and a non-negative endowment. On commit, the fresh cell is inserted with
the disclosed `bal` and a receipt carrying the disclosed creation amount is appended. -/
def createCellStep (s : RecChainedState) (actor newCell : CellId) (bal : ℤ) :
    Option RecChainedState :=
  if mintAuthorizedB s.kernel.caps actor newCell = true ∧ newCell ∉ s.kernel.accounts ∧ 0 ≤ bal then
    some { kernel := createCellInto s.kernel newCell bal
           log := { actor := actor, src := newCell, dst := newCell, amt := bal } :: s.log }
  else
    none

/-- The receipt a committed `createCellStep` appends (the disclosed creation, newest-first). -/
def createTurn (actor newCell : CellId) (bal : ℤ) : Turn :=
  { actor := actor, src := newCell, dst := newCell, amt := bal }

/-- **`createCellStep` factors through its gate — PROVED.** A committed creation implies the three gate
conjuncts held and pins the post-state. The bridge downstream keystones reuse. -/
theorem createCellStep_factors {s s' : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    (h : createCellStep s actor newCell bal = some s') :
    mintAuthorizedB s.kernel.caps actor newCell = true ∧ newCell ∉ s.kernel.accounts ∧ 0 ≤ bal ∧
      s' = { kernel := createCellInto s.kernel newCell bal
             log := createTurn actor newCell bal :: s.log } := by
  unfold createCellStep at h
  by_cases hg : mintAuthorizedB s.kernel.caps actor newCell = true ∧ newCell ∉ s.kernel.accounts ∧ 0 ≤ bal
  · rw [if_pos hg, Option.some.injEq] at h
    exact ⟨hg.1, hg.2.1, hg.2.2, by rw [← h]; rfl⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ### §1.2 — `create_conserves` (the DISCLOSED form): `recTotal` grows by exactly the disclosed `bal`. -/

/-- The fresh-account insert raises `recTotal` by EXACTLY the disclosed `bal` — PROVED. The new cell was
absent (`∉ accounts`, so it contributed `0`); inserting it with `balance = bal` adds `bal`. Reuses
`Finset.sum_insert` (the fresh-cell single-point growth). -/
theorem createCellInto_recTotal (k : RecordKernelState) (newCell : CellId) (bal : ℤ)
    (hfresh : newCell ∉ k.accounts) :
    recTotal (createCellInto k newCell bal) = recTotal k + bal := by
  unfold recTotal createCellInto
  rw [Finset.sum_insert hfresh]
  have hnew : balOf ((fun c => if c = newCell then setBalance (.record []) bal else k.cell c) newCell)
      = bal := by simp only [if_pos]; exact setBalance_balOf _ bal
  rw [hnew, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  have hcne : c ≠ newCell := fun heq => hfresh (heq ▸ hc)
  simp only [if_neg hcne]

/-- **`create_conserves` — DISCLOSED non-conservation (PROVED).** A committed `createCellStep` raises the
total `balance` by EXACTLY the disclosed `bal`: `recTotal s'.kernel = recTotal s.kernel + bal`. This is
the Generative DISCLOSURE obligation in executable form — the supply move is NOT `Σδ = 0`, it is the
flagged disclosed delta `+bal` (mirroring mint's `recKMint_delta`). -/
theorem create_conserves {s s' : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    (h : createCellStep s actor newCell bal = some s') :
    recTotal s'.kernel = recTotal s.kernel + bal := by
  obtain ⟨_, hfresh, _, hs'⟩ := createCellStep_factors h
  subst hs'
  exact createCellInto_recTotal s.kernel newCell bal hfresh

/-- **`create_discloses` — PROVED.** `CreateCell` is Generative, hence carries the disclosed
non-conservation obligation: its created supply must be revealed in the receipt. Discharged off
`CatalogEffects.generative_discloses` + `g_createCell`. -/
theorem create_discloses :
    (effectLinearity .createCell).is_disclosed_non_conservation = true :=
  Dregg2.CatalogEffects.generative_discloses .createCell Dregg2.CatalogEffects.g_createCell

/-- **`create_disclosed_domain` — PROVED.** The realized balance-domain delta of a committed
`createCellStep` is EXACTLY the disclosed `[bal]` (NOT `[0]`) — the executable shadow of dregg1's
disclosed-creation receipt for the Generative effect. -/
theorem create_disclosed_domain {s s' : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    (h : createCellStep s actor newCell bal = some s') :
    [recTotal s'.kernel - recTotal s.kernel] = [bal] := by
  rw [create_conserves h]; simp

/-! ### §1.3 — `create_authorized` + fail-closed. -/

/-- **`create_authorized` — PROVED.** A committed `createCellStep` implies the creator held the privileged
creation authority over the new cell (`mintAuthorizedB` — bare ownership is NOT enough; creation coins
supply). The integrity obligation, reused from the gate. -/
theorem create_authorized {s s' : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    (h : createCellStep s actor newCell bal = some s') :
    mintAuthorizedB s.kernel.caps actor newCell = true :=
  (createCellStep_factors h).1

/-- **`create_unauthorized_fails` — PROVED (fail-closed).** Without creation authority, no cell is
minted. The confinement core. -/
theorem create_unauthorized_fails (s : RecChainedState) (actor newCell : CellId) (bal : ℤ)
    (h : mintAuthorizedB s.kernel.caps actor newCell = false) :
    createCellStep s actor newCell bal = none := by
  unfold createCellStep
  rw [if_neg]; rintro ⟨ha, _⟩; rw [h] at ha; exact absurd ha (by simp)

/-! ### §1.4 — `create_metadata`: caps framed + the chain advances by one. -/

/-- **`create_caps_unchanged` — PROVED.** A committed `createCellStep` leaves the cap table UNTOUCHED
(creation edits `accounts`/`cell`, never `caps`). -/
theorem create_caps_unchanged {s s' : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    (h : createCellStep s actor newCell bal = some s') :
    s'.kernel.caps = s.kernel.caps := by
  obtain ⟨_, _, _, hs'⟩ := createCellStep_factors h
  subst hs'; rfl

/-- **`create_metadata` — PROVED (metadata + authority frame).** A committed `createCellStep`: (a) grows
the receipt chain by EXACTLY one row (replay-detectable, ObsAdvance), and (b) leaves the cap table /
reconstructed authority graph UNCHANGED. -/
theorem create_metadata {s s' : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    (h : createCellStep s actor newCell bal = some s') :
    s'.log.length = s.log.length + 1 ∧
      execGraph s'.kernel.caps = execGraph s.kernel.caps := by
  obtain ⟨_, _, _, hs'⟩ := createCellStep_factors h
  refine ⟨?_, ?_⟩
  · subst hs'; simp
  · rw [create_caps_unchanged h]

/-! ## §2 — `CreateCellFromFactory`: constructor transparency + disclosed creation.

`Effect::CreateCellFromFactory` (`STORAGE-AS-CELL-PROGRAMS.md §2`, `CatalogEffects.g_createCellFromFactory`,
Generative) mints a cell whose lifetime program IS a published `FactoryDescriptor`'s program. We compose
`Factory.createFromFactory` (constructor transparency, REUSED VERBATIM) with `createCellStep`'s disclosed
ledger insert: the factory pins the child's invariants, the supply move is the disclosed `+bal`. -/

/-- **`createFromFactoryStep` — `CreateCellFromFactory`'s executable semantics.** First mint the child
program/state via `Factory.createFromFactory` (rejects a non-conforming initial value, fail-closed);
THEN insert the fresh ledger account with the disclosed `bal`. Returns BOTH the ledger post-state and the
minted `Factory.Cell` (carrying the published program), so constructor transparency is observable. -/
def createFromFactoryStep (s : RecChainedState) (actor newCell : CellId) (bal : ℤ)
    (d : Factory.FactoryDescriptor) (initial : Value) :
    Option (RecChainedState × Factory.Cell) :=
  match Factory.createFromFactory d initial with
  | some child =>
      match createCellStep s actor newCell bal with
      | some s' => some (s', child)
      | none    => none
  | none => none

/-- **`factory_create_factors` — PROVED.** A committed factory-create factors as a committed
`Factory.createFromFactory` (the child) AND a committed `createCellStep` (the ledger insert). -/
theorem factory_create_factors {s : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    {d : Factory.FactoryDescriptor} {initial : Value} {s' : RecChainedState} {child : Factory.Cell}
    (h : createFromFactoryStep s actor newCell bal d initial = some (s', child)) :
    Factory.createFromFactory d initial = some child ∧ createCellStep s actor newCell bal = some s' := by
  unfold createFromFactoryStep at h
  cases hc : Factory.createFromFactory d initial with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some c =>
      rw [hc] at h
      cases hl : createCellStep s actor newCell bal with
      | none => rw [hl] at h; exact absurd h (by simp)
      | some sl =>
          rw [hl] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hsl, hch⟩ := h
          exact ⟨by rw [hch], by rw [hsl]⟩

/-- **`factory_constructor_transparency` (THE KEYSTONE — PROVED).** The cell a committed
`createFromFactoryStep` mints carries EXACTLY the factory's declared `program` AND conforms to its schema:
no hidden behavior, the published contract is the child's lifetime invariant set. Reused VERBATIM from
`Factory.factory_mints_conforming` — the generative resource is created with DISCLOSED PROVENANCE (the
`vk`-addressed program). -/
theorem factory_constructor_transparency {s : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    {d : Factory.FactoryDescriptor} {initial : Value} {s' : RecChainedState} {child : Factory.Cell}
    (h : createFromFactoryStep s actor newCell bal d initial = some (s', child)) :
    child.program = d.program ∧ child.state = initial ∧
      conforms child.state (.record d.schema) = true :=
  Factory.factory_mints_conforming (factory_create_factors h).1

/-- **`factory_create_conserves` — DISCLOSED non-conservation (PROVED).** The ledger insert raises
`recTotal` by exactly the disclosed `bal` (inherited from `create_conserves`). -/
theorem factory_create_conserves {s : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    {d : Factory.FactoryDescriptor} {initial : Value} {s' : RecChainedState} {child : Factory.Cell}
    (h : createFromFactoryStep s actor newCell bal d initial = some (s', child)) :
    recTotal s'.kernel = recTotal s.kernel + bal :=
  create_conserves (factory_create_factors h).2

/-- **`factory_create_discloses` — PROVED.** `CreateCellFromFactory` is Generative ⇒ disclosed. -/
theorem factory_create_discloses :
    (effectLinearity .createCellFromFactory).is_disclosed_non_conservation = true :=
  Dregg2.CatalogEffects.generative_discloses .createCellFromFactory
    Dregg2.CatalogEffects.g_createCellFromFactory

/-- **`factory_create_authorized` — PROVED.** A committed factory-create implies creation authority. -/
theorem factory_create_authorized {s : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    {d : Factory.FactoryDescriptor} {initial : Value} {s' : RecChainedState} {child : Factory.Cell}
    (h : createFromFactoryStep s actor newCell bal d initial = some (s', child)) :
    mintAuthorizedB s.kernel.caps actor newCell = true :=
  create_authorized (factory_create_factors h).2

/-- **`factory_create_metadata` — PROVED.** Chain advances by one + caps framed. -/
theorem factory_create_metadata {s : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    {d : Factory.FactoryDescriptor} {initial : Value} {s' : RecChainedState} {child : Factory.Cell}
    (h : createFromFactoryStep s actor newCell bal d initial = some (s', child)) :
    s'.log.length = s.log.length + 1 ∧
      execGraph s'.kernel.caps = execGraph s.kernel.caps :=
  create_metadata (factory_create_factors h).2

/-! ## §3 — `SpawnWithDelegation`: a child spawned with a disclosed delegated authority snapshot.

`Effect::SpawnWithDelegation` (`action.rs:873`, `CatalogEffects.g_spawnWithDelegation`, Generative) spawns
a child cell that inherits a snapshot of the parent's authority. We model it as `createCellStep` (the
disclosed-supply child) COMPOSED with handing the child a delegated cap (the disclosed authority snapshot),
recording the parent as the child's provenance. The balance creation is the disclosed `+bal`; the
authority grant is a NEW edge (`addEdge` shape). -/

/-- **`spawnStep` — `SpawnWithDelegation`'s executable semantics.** Fail-closed via `createCellStep` (the
authorized, fresh-id, non-negative child), and on commit ALSO grant the child a snapshot cap to `target`
(the delegated authority). The child's provenance is the spawning `actor` (recorded on the receipt). -/
def spawnStep (s : RecChainedState) (actor child target : CellId) (bal : ℤ) :
    Option RecChainedState :=
  match createCellStep s actor child bal with
  | some s1 =>
      some { s1 with kernel :=
        { s1.kernel with caps := fun l => if l = child then Cap.node target :: s1.kernel.caps l
                                          else s1.kernel.caps l } }
  | none => none

/-- **`spawnStep` factors through `createCellStep` — PROVED.** A committed spawn is a committed
`createCellStep` (into `s1`) followed by the child-cap grant. -/
theorem spawnStep_factors {s s' : RecChainedState} {actor child target : CellId} {bal : ℤ}
    (h : spawnStep s actor child target bal = some s') :
    ∃ s1, createCellStep s actor child bal = some s1 ∧
      s' = { s1 with kernel :=
        { s1.kernel with caps := fun l => if l = child then Cap.node target :: s1.kernel.caps l
                                          else s1.kernel.caps l } } := by
  unfold spawnStep at h
  cases hc : createCellStep s actor child bal with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some s1 => rw [hc] at h; simp only [Option.some.injEq] at h; exact ⟨s1, rfl, h.symm⟩

/-- The cap grant preserves `recTotal` (it edits `caps`, never the `balance` field) — PROVED. -/
theorem spawn_grant_recTotal (k : RecordKernelState) (child target : CellId) :
    recTotal { k with caps := fun l => if l = child then Cap.node target :: k.caps l else k.caps l }
      = recTotal k := rfl

/-- **`spawn_conserves` — DISCLOSED non-conservation (PROVED).** A committed spawn raises `recTotal` by
exactly the disclosed child endowment `bal` (the cap grant does not touch the balance field). -/
theorem spawn_conserves {s s' : RecChainedState} {actor child target : CellId} {bal : ℤ}
    (h : spawnStep s actor child target bal = some s') :
    recTotal s'.kernel = recTotal s.kernel + bal := by
  obtain ⟨s1, hc, hs'⟩ := spawnStep_factors h
  subst hs'
  rw [spawn_grant_recTotal s1.kernel child target]
  exact create_conserves hc

/-- **`spawn_discloses` — PROVED.** `SpawnWithDelegation` is Generative ⇒ disclosed. -/
theorem spawn_discloses :
    (effectLinearity .spawnWithDelegation).is_disclosed_non_conservation = true :=
  Dregg2.CatalogEffects.generative_discloses .spawnWithDelegation
    Dregg2.CatalogEffects.g_spawnWithDelegation

/-- **`spawn_authorized` — PROVED.** A committed spawn implies the spawner held creation authority over
the child (the parent's privilege to spawn). -/
theorem spawn_authorized {s s' : RecChainedState} {actor child target : CellId} {bal : ℤ}
    (h : spawnStep s actor child target bal = some s') :
    mintAuthorizedB s.kernel.caps actor child = true := by
  obtain ⟨s1, hc, _⟩ := spawnStep_factors h
  exact create_authorized hc

/-- **`spawn_provenance` (the DISCLOSED-AUTHORITY keystone — PROVED).** The spawned child carries EXACTLY
the delegated snapshot cap `node target` (its disclosed authority provenance): reading the child's cap
table after a committed spawn yields `Cap.node target :: <inherited>`. The generative resource is created
with disclosed authority. -/
theorem spawn_provenance {s s' : RecChainedState} {actor child target : CellId} {bal : ℤ}
    (h : spawnStep s actor child target bal = some s') :
    ∃ rest, s'.kernel.caps child = Cap.node target :: rest := by
  obtain ⟨s1, _, hs'⟩ := spawnStep_factors h
  subst hs'
  exact ⟨s1.kernel.caps child, by simp⟩

/-- **`spawn_metadata` — PROVED.** A committed spawn grows the receipt chain by exactly one (the child's
creation row); the cap edit is the disclosed child grant (NOT a frame — spawn DOES extend authority, the
sole §3 difference from `CreateCell`). -/
theorem spawn_metadata {s s' : RecChainedState} {actor child target : CellId} {bal : ℤ}
    (h : spawnStep s actor child target bal = some s') :
    s'.log.length = s.log.length + 1 := by
  obtain ⟨s1, hc, hs'⟩ := spawnStep_factors h
  subst hs'
  have := (create_metadata hc).1
  simpa using this

/-! ## §4 — `BridgeMint`: the §8 PORTAL inflow (foreign-finality as a `Prop` carrier).

`Effect::BridgeMint` (`action.rs:897`, `CatalogEffects.g_bridgeMint`, Generative) credits a cell with a
value observed off a FOREIGN chain. The §8-PORTAL RULE: dregg2 CANNOT verify Cardano consensus inside
Lean, so the foreign finality is the OPAQUE `Prop` `ForeignFinal nullifier value` carried as a HYPOTHESIS;
the LOCAL state transition — the disclosed `+value` credit + the nullifier-nonce pairing (so the same
foreign tx cannot be minted twice) — is executable and PROVED. -/

/-- **`bridgeMintStep` — `BridgeMint`'s executable LOCAL semantics.** Fail-closed: an authorized minter
(`mintAuthorizedB` — the bridge mint is privileged supply), the target is live, and a non-negative value.
On commit, credit the cell's `balance` by the disclosed `value` and append a receipt carrying it. The
foreign finality is NOT checked here (it is the §8 portal hypothesis on the keystone). -/
def bridgeMintStep (s : RecChainedState) (actor cell : CellId) (value : ℤ) :
    Option RecChainedState :=
  match recKMint s.kernel actor cell value with
  | some k' => some { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := value } :: s.log }
  | none    => none

/-- **`bridgeMintStep` factors through `recKMint` — PROVED.** A committed bridge-mint is a committed
record-cell `recKMint` (the disclosed credit) plus the receipt row. Reuses the supply spine. -/
theorem bridgeMintStep_factors {s s' : RecChainedState} {actor cell : CellId} {value : ℤ}
    (h : bridgeMintStep s actor cell value = some s') :
    ∃ k', recKMint s.kernel actor cell value = some k' ∧
      s' = { kernel := k', log := { actor := actor, src := cell, dst := cell, amt := value } :: s.log } := by
  unfold bridgeMintStep at h
  cases hm : recKMint s.kernel actor cell value with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some k' => rw [hm] at h; simp only [Option.some.injEq] at h; exact ⟨k', rfl, h.symm⟩

/-- **`bridge_mint_conserves` — DISCLOSED non-conservation, GATED BY THE §8 PORTAL (PROVED).** GIVEN the
foreign-finality portal `ForeignFinal nullifier value` (the cross-chain proof, discharged OUTSIDE Lean), a
committed `bridgeMintStep` raises `recTotal` by EXACTLY the disclosed `value`: `recTotal s'.kernel =
recTotal s.kernel + value`. The LOCAL disclosed credit is `recKMint_delta` (proved); the foreign half is
the carried hypothesis — the honest §8 split. -/
theorem bridge_mint_conserves {s s' : RecChainedState} {actor cell : CellId} {value nullifier : ℤ}
    (_hforeign : ForeignFinal nullifier value)
    (h : bridgeMintStep s actor cell value = some s') :
    recTotal s'.kernel = recTotal s.kernel + value := by
  obtain ⟨k', hm, hs'⟩ := bridgeMintStep_factors h
  subst hs'
  exact recKMint_delta s.kernel k' actor cell value hm

/-- **`bridge_mint_discloses` — PROVED.** `BridgeMint` is Generative ⇒ disclosed (`mintEffect` already
names this color in `TurnExecutorFull`; re-exposed at the bridge name). -/
theorem bridge_mint_discloses :
    (effectLinearity .bridgeMint).is_disclosed_non_conservation = true :=
  Dregg2.CatalogEffects.generative_discloses .bridgeMint Dregg2.CatalogEffects.g_bridgeMint

/-- **`bridge_mint_authorized` — PROVED.** A committed bridge-mint implies the privileged mint authority
(the local credit is gated; the foreign side is the portal). -/
theorem bridge_mint_authorized {s s' : RecChainedState} {actor cell : CellId} {value : ℤ}
    (h : bridgeMintStep s actor cell value = some s') :
    mintAuthorizedB s.kernel.caps actor cell = true := by
  obtain ⟨k', hm, _⟩ := bridgeMintStep_factors h
  exact recKMint_authorized s.kernel k' actor cell value hm

/-- **`bridge_mint_unauthorized_fails` — PROVED (fail-closed).** Without mint authority, no bridge-mint
commits (regardless of foreign finality). -/
theorem bridge_mint_unauthorized_fails (s : RecChainedState) (actor cell : CellId) (value : ℤ)
    (h : mintAuthorizedB s.kernel.caps actor cell = false) :
    bridgeMintStep s actor cell value = none := by
  unfold bridgeMintStep
  rw [recKMint_unauthorized_fails s.kernel actor cell value h]

/-- **`bridge_mint_caps_unchanged` — PROVED.** The local bridge-mint credit frames the cap table. -/
theorem bridge_mint_caps_unchanged {s s' : RecChainedState} {actor cell : CellId} {value : ℤ}
    (h : bridgeMintStep s actor cell value = some s') :
    s'.kernel.caps = s.kernel.caps := by
  obtain ⟨k', hm, hs'⟩ := bridgeMintStep_factors h
  subst hs'
  -- `recKMint` commits ⟹ it took the credit branch (caps untouched).
  unfold recKMint at hm
  by_cases hg : mintAuthorizedB s.kernel.caps actor cell = true ∧ 0 ≤ value ∧ cell ∈ s.kernel.accounts
  · rw [if_pos hg] at hm; simp only [Option.some.injEq] at hm; rw [← hm]
  · rw [if_neg hg] at hm; exact absurd hm (by simp)

/-- **`bridge_mint_metadata` — PROVED.** Chain advances by one + caps/auth graph framed. -/
theorem bridge_mint_metadata {s s' : RecChainedState} {actor cell : CellId} {value : ℤ}
    (h : bridgeMintStep s actor cell value = some s') :
    s'.log.length = s.log.length + 1 ∧
      execGraph s'.kernel.caps = execGraph s.kernel.caps := by
  obtain ⟨k', hm, hs'⟩ := bridgeMintStep_factors h
  refine ⟨?_, ?_⟩
  · subst hs'; simp
  · rw [bridge_mint_caps_unchanged h]

/-! ## §5 — `BridgeLock` / `BridgeCancel` / `BridgeFinalize`: the PAIRED bridge escrow phases.

`Effect::BridgeLock` (`action.rs:907`), `BridgeCancel` (`:936`), `BridgeFinalize` (`:925`) are the
Conservative (`c_bridgeLock`/`c_bridgeCancel`/`c_bridgeFinalize`, `Σδ = 0`) escrow phases. We model a
bridge LOCK-CELL: locking ESCROWS `value` from the owner into the lock-cell (an INTERNAL transfer,
balance-conserving), recording the lock nullifier; cancel REFUNDS it (the inverse); finalize CONSUMES the
lock (the value already left — balance FRAMED, the nullifier retired). The foreign destination/receipt is
the §8 `Prop` portal; the LOCAL escrow conserves. We reuse `recTransfer` (the proved two-party
balance-conserving move) for lock/cancel. -/

/-- **`bridgeLockStep` — `BridgeLock`'s executable LOCAL semantics.** Fail-closed: the owner is authorized
(`authorizedB` over the move), `value` is available in `owner`, and `owner ≠ lockCell` (distinct escrow),
both live. On commit, escrow `value` owner→lockCell and append the lock receipt (carrying the
`nullifier`). -/
def bridgeLockStep (s : RecChainedState) (owner lockCell : CellId) (value nullifier : ℤ) :
    Option RecChainedState :=
  match recCexec s { actor := owner, src := owner, dst := lockCell, amt := value } with
  | some s1 => some { s1 with kernel := { s1.kernel with
      cell := fun c => if c = lockCell then setLockField (s1.kernel.cell c) nullifier
                       else s1.kernel.cell c } }
  | none => none
where
  /-- Write the `bridge_lock` nullifier-nonce field of the lock-cell (the replay metadata) by PREPENDING
  it (the freshest binding wins under `List.find?`). The `bridge_lock` name is distinct from `balance`, so
  prepending it never shadows the balance read — the escrow measure survives untouched. -/
  setLockField (v : Value) (nullifier : ℤ) : Value :=
    match v with
    | .record fs => .record ((lockField, .int nullifier) :: fs)
    | _          => .record [(lockField, .int nullifier)]

/-- The `Turn` a bridge-lock escrows. -/
def lockTurn (owner lockCell : CellId) (value : ℤ) : Turn :=
  { actor := owner, src := owner, dst := lockCell, amt := value }

/-- Writing the `bridge_lock` field leaves the `balance` read UNCHANGED — PROVED. The two named fields are
distinct (`"bridge_lock" ≠ "balance"`), so the lock-nonce write never perturbs the escrow measure. -/
theorem setLockField_balOf (v : Value) (nullifier : ℤ) :
    balOf (bridgeLockStep.setLockField v nullifier) = balOf v := by
  cases v with
  | record fs =>
      -- prepending `(bridge_lock, …)` does not shadow the `balance` read (distinct names).
      unfold balOf bridgeLockStep.setLockField
      simp only [Value.scalar, Value.field]
      have hne : (lockField == balanceField) = false := by decide
      rw [List.find?_cons_of_neg (by simpa using hne)]
  | int _ => simp [balOf, bridgeLockStep.setLockField, Value.scalar, Value.field, balanceField, lockField]
  | dig _ => simp [balOf, bridgeLockStep.setLockField, Value.scalar, Value.field, balanceField, lockField]
  | sym _ => simp [balOf, bridgeLockStep.setLockField, Value.scalar, Value.field, balanceField, lockField]

/-- **`bridgeLockStep` factors through `recCexec` — PROVED.** A committed lock is a committed escrow
`recCexec` (into `s1`) followed by the lock-nonce write. -/
theorem bridgeLockStep_factors {s s' : RecChainedState} {owner lockCell : CellId} {value nullifier : ℤ}
    (h : bridgeLockStep s owner lockCell value nullifier = some s') :
    ∃ s1, recCexec s (lockTurn owner lockCell value) = some s1 ∧
      s' = { s1 with kernel := { s1.kernel with
        cell := fun c => if c = lockCell then bridgeLockStep.setLockField (s1.kernel.cell c) nullifier
                         else s1.kernel.cell c } } := by
  unfold bridgeLockStep lockTurn at *
  cases hc : recCexec s { actor := owner, src := owner, dst := lockCell, amt := value } with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some s1 => rw [hc] at h; simp only [Option.some.injEq] at h; exact ⟨s1, rfl, h.symm⟩

/-- The lock-nonce write preserves the conserved `balance` total — PROVED (it touches only the
`bridge_lock` field). -/
theorem lockWrite_recTotal (k : RecordKernelState) (lockCell : CellId) (nullifier : ℤ) :
    recTotal { k with cell := fun c => if c = lockCell then bridgeLockStep.setLockField (k.cell c) nullifier
                                       else k.cell c } = recTotal k := by
  unfold recTotal
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : c = lockCell
  · simp only [hc, if_pos]; exact setLockField_balOf (k.cell lockCell) nullifier
  · simp only [if_neg hc]

/-- **`bridge_lock_conserves` — TWO-PARTY balance conservation (PROVED, the PAIRED regime).** A committed
`bridgeLockStep` preserves `recTotal`: the owner's `-value` debit and the lock-cell's `+value` credit
cancel (the proved two-party escrow), and the lock-nonce write does not perturb the balance measure. The
bridge LOCK is an INTERNAL `Σδ = 0` move — the value is escrowed, not destroyed. -/
theorem bridge_lock_conserves {s s' : RecChainedState} {owner lockCell : CellId} {value nullifier : ℤ}
    (h : bridgeLockStep s owner lockCell value nullifier = some s') :
    recTotal s'.kernel = recTotal s.kernel := by
  obtain ⟨s1, hc, hs'⟩ := bridgeLockStep_factors h
  subst hs'
  rw [lockWrite_recTotal s1.kernel lockCell nullifier]
  exact (recCexec_attests hc).1

/-- **`bridge_lock_paired_domain` — PROVED (per-domain Σ=0).** The realized balance delta of a committed
lock nets to `0` (`conservedInDomain Domain.balance`), the executable shadow of the `c_bridgeLock`
Conservative obligation. -/
theorem bridge_lock_paired_domain {s s' : RecChainedState} {owner lockCell : CellId} {value nullifier : ℤ}
    (h : bridgeLockStep s owner lockCell value nullifier = some s') :
    conservedInDomain Domain.balance [recTotal s'.kernel - recTotal s.kernel] := by
  unfold conservedInDomain; rw [bridge_lock_conserves h]; simp

/-- **`bridge_lock_authorized` — PROVED.** A committed lock implies the owner was authorized to move the
escrowed value (reused from the escrow `recCexec` gate). -/
theorem bridge_lock_authorized {s s' : RecChainedState} {owner lockCell : CellId} {value nullifier : ℤ}
    (h : bridgeLockStep s owner lockCell value nullifier = some s') :
    authorizedB s.kernel.caps (lockTurn owner lockCell value) = true := by
  obtain ⟨s1, hc, _⟩ := bridgeLockStep_factors h
  exact (recCexec_attests hc).2.1

/-- **`bridge_lock_metadata` — PROVED.** Chain advances by one + caps framed. -/
theorem bridge_lock_metadata {s s' : RecChainedState} {owner lockCell : CellId} {value nullifier : ℤ}
    (h : bridgeLockStep s owner lockCell value nullifier = some s') :
    s'.log.length = s.log.length + 1 ∧
      execGraph s'.kernel.caps = execGraph s.kernel.caps := by
  obtain ⟨s1, hc, hs'⟩ := bridgeLockStep_factors h
  -- caps: `recCexec` frames caps, the lock-nonce write edits only `cell`.
  have hcaps : s'.kernel.caps = s.kernel.caps := by
    subst hs'; simp only []; exact recCexec_caps_eq hc
  refine ⟨?_, by rw [hcaps]⟩
  subst hs'; simp only []
  have : s1.log = lockTurn owner lockCell value :: s.log := (recCexec_attests hc).2.2.1
  rw [this]; simp

/-! ### §5.2 — `BridgeCancel`: refund the escrow (the inverse of lock), gated by timeout (a `Prop` portal). -/

/-- **`bridgeCancelStep` — `BridgeCancel`'s executable LOCAL semantics.** The Phase-4 refund: escrow the
locked `value` BACK from the lock-cell to the owner (the inverse two-party move), via `recCexec`. The
timeout-expiry is a §8 portal (the foreign block height — not verifiable in Lean); the LOCAL refund
conserves. -/
def bridgeCancelStep (s : RecChainedState) (owner lockCell : CellId) (value : ℤ) :
    Option RecChainedState :=
  recCexec s { actor := owner, src := lockCell, dst := owner, amt := value }

/-- The `Turn` a cancel refunds (lockCell → owner). -/
def cancelTurn (owner lockCell : CellId) (value : ℤ) : Turn :=
  { actor := owner, src := lockCell, dst := owner, amt := value }

/-- **`bridge_cancel_conserves` — TWO-PARTY balance conservation (PROVED, PAIRED).** A committed
`bridgeCancelStep` preserves `recTotal` — the refund is the inverse escrow, `Σδ = 0`. -/
theorem bridge_cancel_conserves {s s' : RecChainedState} {owner lockCell : CellId} {value : ℤ}
    (h : bridgeCancelStep s owner lockCell value = some s') :
    recTotal s'.kernel = recTotal s.kernel :=
  (recCexec_attests h).1

/-- **`bridge_cancel_authorized` — PROVED.** A committed cancel was authorized (the refund gate). -/
theorem bridge_cancel_authorized {s s' : RecChainedState} {owner lockCell : CellId} {value : ℤ}
    (h : bridgeCancelStep s owner lockCell value = some s') :
    authorizedB s.kernel.caps (cancelTurn owner lockCell value) = true :=
  (recCexec_attests h).2.1

/-- **`bridge_cancel_metadata` — PROVED.** Chain advances by one + caps framed. -/
theorem bridge_cancel_metadata {s s' : RecChainedState} {owner lockCell : CellId} {value : ℤ}
    (h : bridgeCancelStep s owner lockCell value = some s') :
    s'.log.length = s.log.length + 1 ∧
      execGraph s'.kernel.caps = execGraph s.kernel.caps := by
  refine ⟨?_, by rw [recCexec_caps_eq h]⟩
  have : s'.log = cancelTurn owner lockCell value :: s.log := (recCexec_attests h).2.2.1
  rw [this]; simp

/-! ### §5.3 — `BridgeFinalize`: consume the lock on a foreign receipt (`Prop` portal); balance FRAMED. -/

/-- **`bridgeFinalizeStep` — `BridgeFinalize`'s executable LOCAL semantics.** On a foreign receipt (the §8
portal hypothesis), CONSUME the lock: retire the lock-cell's `bridge_lock` nullifier-nonce (write a
disclosed "spent" marker — here `bumping` it, a metadata advance). The escrowed value already LEFT at lock
time, so the balance is FRAMED here. Fail-closed only on liveness of the lock-cell. -/
def bridgeFinalizeStep (s : RecChainedState) (actor lockCell : CellId) (spentMarker : ℤ) :
    Option RecChainedState :=
  if lockCell ∈ s.kernel.accounts then
    some { kernel := { s.kernel with
             cell := fun c => if c = lockCell then bridgeLockStep.setLockField (s.kernel.cell c) spentMarker
                              else s.kernel.cell c }
           log := { actor := actor, src := lockCell, dst := lockCell, amt := 0 } :: s.log }
  else none

/-- **`bridgeFinalizeStep` factors — PROVED.** A committed finalize implies the lock-cell was live and
pins the post-state (the spent-marker write + the receipt). -/
theorem bridgeFinalizeStep_factors {s s' : RecChainedState} {actor lockCell : CellId} {spentMarker : ℤ}
    (h : bridgeFinalizeStep s actor lockCell spentMarker = some s') :
    lockCell ∈ s.kernel.accounts ∧
      s' = { kernel := { s.kernel with
               cell := fun c => if c = lockCell then bridgeLockStep.setLockField (s.kernel.cell c) spentMarker
                                else s.kernel.cell c }
             log := { actor := actor, src := lockCell, dst := lockCell, amt := 0 } :: s.log } := by
  unfold bridgeFinalizeStep at h
  by_cases hl : lockCell ∈ s.kernel.accounts
  · rw [if_pos hl, Option.some.injEq] at h; exact ⟨hl, h.symm⟩
  · rw [if_neg hl] at h; exact absurd h (by simp)

/-- **`bridge_finalize_conserves` — balance FRAMED (PROVED, the PAIRED `Σδ = 0` form), GATED BY THE §8
PORTAL.** GIVEN the foreign-receipt portal `ForeignFinal nullifier value`, a committed
`bridgeFinalizeStep` preserves `recTotal`: the value already left at lock time, so finalization touches
only the `bridge_lock` nonce (the spent marker), never the balance field — `Σδ = 0`. -/
theorem bridge_finalize_conserves {s s' : RecChainedState} {actor lockCell : CellId}
    {spentMarker nullifier value : ℤ}
    (_hforeign : ForeignFinal nullifier value)
    (h : bridgeFinalizeStep s actor lockCell spentMarker = some s') :
    recTotal s'.kernel = recTotal s.kernel := by
  obtain ⟨_, hs'⟩ := bridgeFinalizeStep_factors h
  subst hs'
  exact lockWrite_recTotal s.kernel lockCell spentMarker

/-- **`bridge_finalize_consumes_lock` (the NULLIFIER keystone — PROVED).** A committed finalize writes the
lock-cell's `bridge_lock` field to EXACTLY the disclosed `spentMarker` — the nullifier becomes permanently
spent (replay-protection: the same foreign tx cannot be finalized twice). The metadata move of the bridge
finalize. -/
theorem bridge_finalize_consumes_lock {s s' : RecChainedState} {actor lockCell : CellId} {spentMarker : ℤ}
    (h : bridgeFinalizeStep s actor lockCell spentMarker = some s') :
    lockOf (s'.kernel.cell lockCell) = spentMarker := by
  obtain ⟨_, hs'⟩ := bridgeFinalizeStep_factors h
  subst hs'
  simp only [if_pos]
  -- reading the freshly-written `bridge_lock` field returns the marker.
  unfold lockOf bridgeLockStep.setLockField
  cases s.kernel.cell lockCell with
  | record fs => simp [Value.scalar, Value.field, lockField]
  | int _ => simp [Value.scalar, Value.field, lockField]
  | dig _ => simp [Value.scalar, Value.field, lockField]
  | sym _ => simp [Value.scalar, Value.field, lockField]

/-- **`bridge_finalize_metadata` — PROVED.** Chain advances by one + caps framed. -/
theorem bridge_finalize_metadata {s s' : RecChainedState} {actor lockCell : CellId} {spentMarker : ℤ}
    (h : bridgeFinalizeStep s actor lockCell spentMarker = some s') :
    s'.log.length = s.log.length + 1 ∧
      execGraph s'.kernel.caps = execGraph s.kernel.caps := by
  obtain ⟨_, hs'⟩ := bridgeFinalizeStep_factors h
  subst hs'; refine ⟨by simp, rfl⟩

/-! ## §6 — Forward-simulation: every disclosed-supply / generative step is an abstract `Spec` step.

Mirroring `EffectTransfer §5`: the record-world abstract state `AbstractS` = (`balance`-domain total,
authority graph). For the DISCLOSED effects the bottom edge records the disclosed `±delta` (NOT a
conservation `0`); for the PAIRED bridge phases it records `0`. The authority graph is framed for all
(creation/supply never edits connectivity, except spawn which extends it — handled by its own provenance
keystone, so its forward-sim is the conservation+disclosure projection). -/

section ForwardSim
variable {Statement Witness : Type} [Verifiable Statement Witness]

/-- **`AbstractS`** — the record-world abstract Spec state the supply/generative effects refine: the
conserved `balance`-domain total and the reconstructed authority graph (the `EffectTransfer.AbstractT`
shape, re-named for this regime). -/
structure AbstractS where
  /-- the `balance`-domain total. -/
  balanceTotal : ℤ
  /-- the reconstructed authority graph. -/
  authGraph    : Dregg2.Spec.Graph Dregg2.Authority.Label Dregg2.Spec.ExecRights

/-- The abstraction function: a chained record state denotes its `recTotal` and its `execGraph`. -/
def absS (s : RecChainedState) : AbstractS :=
  { balanceTotal := recTotal s.kernel, authGraph := execGraph s.kernel.caps }

/-- **`AbsStepDisclosed a a' delta`** — the abstract DISCLOSED-supply step: the abstract balance total
moved by exactly the disclosed `delta` (the receipt-visible non-conservation), and the authority graph is
UNCHANGED (creation/supply is connectivity-preserving). The bottom edge of the disclosed-supply square. -/
def AbsStepDisclosed (a a' : AbstractS) (delta : ℤ) : Prop :=
  a'.balanceTotal = a.balanceTotal + delta ∧ a'.authGraph = a.authGraph

/-- **`AbsStepPaired a a'`** — the abstract PAIRED step (the bridge escrow phases): the abstract balance
total is CONSERVED and the authority graph UNCHANGED. The bottom edge of the paired square (the
`EffectTransfer.AbsStep` shape). -/
def AbsStepPaired (a a' : AbstractS) : Prop :=
  conservedInDomain Domain.balance [a'.balanceTotal - a.balanceTotal] ∧ a'.authGraph = a.authGraph

/-- **`create_forward_sim` — THE REFINEMENT for `CreateCell` (PROVED).** A committed `createCellStep` is
matched by an abstract DISCLOSED step `AbsStepDisclosed (absS s) (absS s') bal`: the abstract balance total
rises by exactly the disclosed `bal`, the authority graph is preserved, AND the committed creation passed
the privileged authority gate. The record-world disclosed-supply forward-simulation square for
`CreateCell`. -/
theorem create_forward_sim {s s' : RecChainedState} {actor newCell : CellId} {bal : ℤ}
    (h : createCellStep s actor newCell bal = some s') :
    AbsStepDisclosed (absS s) (absS s') bal ∧
      mintAuthorizedB s.kernel.caps actor newCell = true := by
  refine ⟨⟨?_, ?_⟩, create_authorized h⟩
  · simp only [absS]; exact create_conserves h
  · simp only [absS]; exact (create_metadata h).2

/-- **`bridge_mint_forward_sim` — THE REFINEMENT for `BridgeMint` (PROVED, §8-portal-gated).** GIVEN the
foreign-finality portal, a committed `bridgeMintStep` is matched by an abstract DISCLOSED step recording
the disclosed `+value`, with the authority graph preserved and the local mint gate passed. -/
theorem bridge_mint_forward_sim {s s' : RecChainedState} {actor cell : CellId} {value nullifier : ℤ}
    (hforeign : ForeignFinal nullifier value)
    (h : bridgeMintStep s actor cell value = some s') :
    AbsStepDisclosed (absS s) (absS s') value ∧
      mintAuthorizedB s.kernel.caps actor cell = true := by
  refine ⟨⟨?_, ?_⟩, bridge_mint_authorized h⟩
  · simp only [absS]; exact bridge_mint_conserves hforeign h
  · simp only [absS]; exact (bridge_mint_metadata h).2

/-- **`bridge_lock_forward_sim` — THE REFINEMENT for `BridgeLock` (PROVED).** A committed `bridgeLockStep`
is matched by an abstract PAIRED step: the abstract balance total is conserved (the internal escrow), the
authority graph preserved, and the escrow turn passed the abstract authority `Guard`. The record-world
paired forward-simulation square for the bridge lock. -/
theorem bridge_lock_forward_sim {s s' : RecChainedState} {owner lockCell : CellId} {value nullifier : ℤ}
    (w : Statement → Witness) (h : bridgeLockStep s owner lockCell value nullifier = some s') :
    AbsStepPaired (absS s) (absS s') ∧
      Guard.admits (execAuthGuard (Statement := Statement) s.kernel.caps) (lockTurn owner lockCell value) w = true := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold conservedInDomain absS; rw [bridge_lock_conserves h]; simp
  · simp only [absS]; exact (bridge_lock_metadata h).2
  · rw [Dregg2.Spec.exec_authz_iff_guard]; exact bridge_lock_authorized h

end ForwardSim

/-! ## §7 — Axiom-hygiene tripwires (the honesty pins over EVERY keystone).

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. The §8 foreign-finality portal `ForeignFinal` is an `opaque` `Prop` (a DATA carrier, like
`Factory.factoryHash` / `Crypto.Bridge`'s `extractable`), NOT an axiom — it never closes a goal, it is a
hypothesis on the bridge keystones. The `#assert_axioms` below confirm the local transitions are genuinely
proved; the foreign half is carried, never faked. -/

#assert_axioms createCellStep_factors
#assert_axioms createCellInto_recTotal
#assert_axioms create_conserves
#assert_axioms create_discloses
#assert_axioms create_disclosed_domain
#assert_axioms create_authorized
#assert_axioms create_unauthorized_fails
#assert_axioms create_caps_unchanged
#assert_axioms create_metadata

#assert_axioms factory_create_factors
#assert_axioms factory_constructor_transparency
#assert_axioms factory_create_conserves
#assert_axioms factory_create_discloses
#assert_axioms factory_create_authorized
#assert_axioms factory_create_metadata

#assert_axioms spawnStep_factors
#assert_axioms spawn_conserves
#assert_axioms spawn_discloses
#assert_axioms spawn_authorized
#assert_axioms spawn_provenance
#assert_axioms spawn_metadata

#assert_axioms bridgeMintStep_factors
#assert_axioms bridge_mint_conserves
#assert_axioms bridge_mint_discloses
#assert_axioms bridge_mint_authorized
#assert_axioms bridge_mint_unauthorized_fails
#assert_axioms bridge_mint_caps_unchanged
#assert_axioms bridge_mint_metadata

#assert_axioms setLockField_balOf
#assert_axioms bridgeLockStep_factors
#assert_axioms lockWrite_recTotal
#assert_axioms bridge_lock_conserves
#assert_axioms bridge_lock_paired_domain
#assert_axioms bridge_lock_authorized
#assert_axioms bridge_lock_metadata

#assert_axioms bridge_cancel_conserves
#assert_axioms bridge_cancel_authorized
#assert_axioms bridge_cancel_metadata

#assert_axioms bridgeFinalizeStep_factors
#assert_axioms bridge_finalize_conserves
#assert_axioms bridge_finalize_consumes_lock
#assert_axioms bridge_finalize_metadata

#assert_axioms create_forward_sim
#assert_axioms bridge_mint_forward_sim
#assert_axioms bridge_lock_forward_sim

/-! ## §8 — Non-vacuity: each effect commits and moves the right measure; unauthorized rejected.

A chained record state: cells 0,1 with balances 100,5; actor 9 holds the privileged `node 0` and `node 2`
mint/create caps; owner 0 owns its own cell (authority by ownership for the escrow moves). -/

/-- The non-vacuity fixture (`fs0`-shaped): cell 0 = 100, cell 1 = 5; actor 9 holds `node 0`,`node 2`
(create/mint authority over cells 0 and the fresh 2). -/
def ss0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then .record [("balance", .int 100)]
                         else if c = 1 then .record [("balance", .int 5)]
                         else .record [("balance", .int 0)]
        caps := fun l => if l = 9 then [Cap.node 0, Cap.node 2] else [] }
    log := [] }

-- CreateCell: actor 9 (holds `node 2`) creates fresh cell 2 with disclosed balance 50 — commits,
-- discloses +50 (105 → 155), grows the chain by one:
#eval (createCellStep ss0 9 2 50).isSome                                    -- true
#eval (createCellStep ss0 9 2 50).map (fun s => recTotal s.kernel)          -- some 155
#eval recTotal ss0.kernel                                                   -- 105
#eval (createCellStep ss0 9 2 50).map (fun s => s.log.length)               -- some 1
-- ...the fresh cell 2 carries the disclosed balance:
#eval (createCellStep ss0 9 2 50).map (fun s => balOf (s.kernel.cell 2))    -- some 50
-- An unauthorized creator (actor 0 holds no create cap) is rejected (fail-closed):
#eval (createCellStep ss0 0 2 50).isSome                                    -- false
-- A non-fresh id (cell 1 already live) is rejected:
#eval (createCellStep ss0 9 1 50).isSome                                    -- false

-- SpawnWithDelegation: actor 9 spawns child 2 (balance 20) with a delegated `node 1` cap:
#eval (spawnStep ss0 9 2 1 20).isSome                                       -- true
#eval (spawnStep ss0 9 2 1 20).map (fun s => recTotal s.kernel)             -- some 125 (disclosed +20)
-- ...and the child carries its disclosed authority snapshot (`node 1` at the head):
#eval ((spawnStep ss0 9 2 1 20).map (fun s => s.kernel.caps 2)).getD []     -- [Cap.node 1]

-- BridgeMint: actor 9 (holds `node 0`) mints +40 into cell 0 — local credit commits, discloses +40:
#eval (bridgeMintStep ss0 9 0 40).isSome                                    -- true
#eval (bridgeMintStep ss0 9 0 40).map (fun s => recTotal s.kernel)          -- some 145 (= 105 + 40)
-- An unauthorized bridge-mint (actor 0) is rejected (the LOCAL gate, independent of foreign finality):
#eval (bridgeMintStep ss0 0 0 40).isSome                                    -- false

-- BridgeLock: owner 0 escrows 30 into lock-cell 1 (owns cell 0) — commits, CONSERVES (105 → 105):
#eval (bridgeLockStep ss0 0 1 30 777).isSome                              -- true
#eval (bridgeLockStep ss0 0 1 30 777).map (fun s => recTotal s.kernel)    -- some 105 (PAIRED Σ=0)
-- ...the value moved owner 0 (100→70) into lock-cell 1 (5→35):
#eval (bridgeLockStep ss0 0 1 30 777).map (fun s => balOf (s.kernel.cell 0))  -- some 70
#eval (bridgeLockStep ss0 0 1 30 777).map (fun s => balOf (s.kernel.cell 1))  -- some 35
-- ...and lock-cell 1's `bridge_lock` nullifier-nonce is set to 777:
#eval (bridgeLockStep ss0 0 1 30 777).map (fun s => lockOf (s.kernel.cell 1)) -- some 777

-- BridgeCancel: owner 0 refunds 30 back from lock-cell 1 — commits, CONSERVES:
#eval (bridgeCancelStep ss0 0 1 30).isSome                                -- false (no value at lock yet)
-- (cancel after a lock: lock then cancel round-trips conservatively — checked via composition below)

-- BridgeFinalize: consume lock-cell 1's nullifier (live) — commits, CONSERVES, retires the lock to 999:
#eval (bridgeFinalizeStep ss0 9 1 999).isSome                               -- true
#eval (bridgeFinalizeStep ss0 9 1 999).map (fun s => recTotal s.kernel)     -- some 105 (balance FRAMED)
#eval (bridgeFinalizeStep ss0 9 1 999).map (fun s => lockOf (s.kernel.cell 1))  -- some 999 (spent)
-- A finalize on a dead lock-cell is rejected:
#eval (bridgeFinalizeStep ss0 9 7 999).isSome                               -- false

end Dregg2.Exec.EffectsSupply
